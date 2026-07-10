/-
  EvmAsm.Stateless.WitnessAuth.TrieWalk

  Batch 2 of obligation #7 (#10141): the decode-on-demand trie walk over the node
  DB, with binding reduced to the batch-1 brick.

  Where `SpecRef.WitnessState.trieLookupAux` walks an already-decoded
  `MutableNode` tree (erroring on unresolved `hashed` nodes), this walk resolves
  each node *at visit time*: `Hash32 → dbLookup → decodeNode → step`, mirroring
  `trieLookupAux`'s step semantics case-for-case. The node decoder is a
  parameter (`decodeNode : Bytes → Option NodeView`) so this batch stays off the
  RLP seam; batch 3 instantiates it with the `EL/RLP` node views.

  **Binding** (`dbTrieLookup_binding`): two walks over two *built* node DBs, from
  the same root hash and key, returning distinct values, yield a concrete Keccak
  collision — by consuming `db_equivocation_collision`: at the first level where
  the walks diverge, the two DBs resolve one hash to distinct entries (the
  collision); at every earlier level the entries agree, so the functional
  decoder forces identical steps.

  Scope fences (ProofTier honesty):
  * children are referenced by `Hash32` only; the spec's sub-32-byte *inline*
    child encodings are a named follow-up (an inline child is structural data
    inside its parent entry, so it cannot equivocate through the DB — the hash
    case is where binding lives);
  * this is the presence/read path; absence-of-key authentication is the
    follow-up scoped in the issue thread.

  No new axioms; no `native_decide`/`bv_decide`.
-/

import EvmAsm.Stateless.WitnessAuth

namespace EvmAsm.Stateless.WitnessAuth

open EvmAsm.Stateless.SpecRef

/-- A shallow (one-level) node view: `MutableNode` with children as `Hash32`
references instead of subtrees. What a single decoded DB entry denotes. -/
inductive NodeView where
  | leaf (restOfKey : Bytes) (value : Bytes)
  | ext (keySegment : Bytes) (childHash : Hash32)
  | branch (children : List (Option Hash32)) (value : Bytes)

/-- Decode-on-demand walk from a root hash: resolve the current node through the
DB, decode it, and step exactly as `SpecRef.WitnessState.trieLookupAux` steps
(leaf: whole remaining key; extension: segment prefix; branch: one nibble, or
the branch value on key exhaustion). -/
def dbTrieLookupAux (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) :
    Nat → Hash32 → Bytes → Nat → Option Bytes
  | 0, _, _, _ => none
  | fuel + 1, h, nibbles, pos =>
    (dbLookup db h).bind fun entry =>
    (decodeNode entry).bind fun view =>
    match view with
    | .leaf restOfKey value =>
      if nibbles.drop pos == restOfKey then some value else none
    | .ext keySegment childHash =>
      if (nibbles.drop pos).take keySegment.length == keySegment then
        dbTrieLookupAux decodeNode db fuel childHash nibbles (pos + keySegment.length)
      else none
    | .branch children value =>
      if nibbles.length ≤ pos then
        if value.isEmpty then none else some value
      else
        (children.getD (nibbles.getD pos 0).toNat none).bind fun childHash =>
          dbTrieLookupAux decodeNode db fuel childHash nibbles (pos + 1)

/-- Authenticated read of `keyHash` from the trie rooted at `root`, resolving
through the node DB (fuel as in `SpecRef.WitnessState.trieLookup`). -/
def dbTrieLookup (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) (root : Hash32) (keyHash : Hash32) : Option Bytes :=
  let nibbles := keyToNibbles keyHash
  dbTrieLookupAux decodeNode db (nibbles.length + 2) root nibbles 0

/-- Binding for the fueled walk: divergent reads from one root over two built
DBs yield a Keccak collision. -/
theorem dbTrieLookupAux_binding (decodeNode : Bytes → Option NodeView)
    {entries₁ entries₂ : List Bytes} {v₁ v₂ : Bytes}
    (fuel : Nat) (h : Hash32) (nibbles : Bytes) (pos : Nat)
    (h₁ : dbTrieLookupAux decodeNode (build_node_db entries₁) fuel h nibbles pos = some v₁)
    (h₂ : dbTrieLookupAux decodeNode (build_node_db entries₂) fuel h nibbles pos = some v₂)
    (hne : v₁ ≠ v₂) :
    ∃ e₁ e₂, KeccakCollision e₁ e₂ := by
  induction fuel generalizing h pos with
  | zero => exact absurd h₁.symm (Option.some_ne_none _)
  | succ fuel ih =>
    rw [dbTrieLookupAux] at h₁ h₂
    cases hd₁ : dbLookup (build_node_db entries₁) h with
    | none =>
      rw [hd₁] at h₁; simp only [Option.bind] at h₁
      exact absurd h₁.symm (Option.some_ne_none _)
    | some e₁ =>
      cases hd₂ : dbLookup (build_node_db entries₂) h with
      | none =>
        rw [hd₂] at h₂; simp only [Option.bind] at h₂
        exact absurd h₂.symm (Option.some_ne_none _)
      | some e₂ =>
        rw [hd₁] at h₁; rw [hd₂] at h₂; simp only [Option.bind] at h₁ h₂
        by_cases he : e₁ = e₂
        · -- same entry: the functional decoder forces identical steps
          subst he
          cases hv : decodeNode e₁ with
          | none =>
            rw [hv] at h₁; simp only [] at h₁
            exact absurd h₁.symm (Option.some_ne_none _)
          | some view =>
            rw [hv] at h₁; rw [hv] at h₂; simp only [] at h₁ h₂
            cases view with
            | leaf restOfKey value =>
              simp only [] at h₁ h₂
              split at h₁
              · rename_i hkey
                rw [if_pos hkey] at h₂
                exact absurd ((Option.some.inj h₁) ▸ (Option.some.inj h₂) ▸ rfl : v₁ = v₂)
                  hne
              · exact absurd h₁.symm (Option.some_ne_none _)
            | ext keySegment childHash =>
              simp only [] at h₁ h₂
              split at h₁
              · rename_i hseg
                rw [if_pos hseg] at h₂
                exact ih childHash (pos + keySegment.length) h₁ h₂
              · exact absurd h₁.symm (Option.some_ne_none _)
            | branch children value =>
              simp only [] at h₁ h₂
              by_cases hpos : nibbles.length ≤ pos
              · rw [if_pos hpos] at h₁ h₂
                split at h₁
                · exact absurd h₁.symm (Option.some_ne_none _)
                · rename_i hval
                  rw [if_neg hval] at h₂
                  exact absurd ((Option.some.inj h₁) ▸ (Option.some.inj h₂) ▸ rfl : v₁ = v₂)
                    hne
              · rw [if_neg hpos] at h₁ h₂
                cases hch : children.getD (nibbles.getD pos 0).toNat none with
                | some childHash =>
                  rw [hch] at h₁ h₂; simp only [] at h₁ h₂
                  exact ih childHash (pos + 1) h₁ h₂
                | none =>
                  rw [hch] at h₁; simp only [] at h₁
                  exact absurd h₁.symm (Option.some_ne_none _)
        · -- distinct entries under one hash: the batch-1 brick
          exact ⟨e₁, e₂, db_equivocation_collision hd₁ hd₂ he⟩

/-- **Trie-read binding.** Two authenticated reads of the same key from the same
state root, over two (possibly different) built witness node DBs, cannot return
distinct values without a concrete Keccak collision. Equivocation about
pre-state contents is impossible without breaking Keccak. -/
theorem dbTrieLookup_binding (decodeNode : Bytes → Option NodeView)
    {entries₁ entries₂ : List Bytes} {v₁ v₂ : Bytes} (root keyHash : Hash32)
    (h₁ : dbTrieLookup decodeNode (build_node_db entries₁) root keyHash = some v₁)
    (h₂ : dbTrieLookup decodeNode (build_node_db entries₂) root keyHash = some v₂)
    (hne : v₁ ≠ v₂) :
    ∃ e₁ e₂, KeccakCollision e₁ e₂ :=
  dbTrieLookupAux_binding decodeNode _ root _ 0 h₁ h₂ hne

end EvmAsm.Stateless.WitnessAuth
