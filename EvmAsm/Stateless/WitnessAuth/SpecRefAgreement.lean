/-
  EvmAsm.Stateless.WitnessAuth.SpecRefAgreement

  Batch 5 of obligation #7 (#10141): authenticated reads agree with SpecRef.

  `Represents decodeNode db h t` says the node DB *represents* the (already-decoded,
  `hashed`-free) `MutableNode` tree `t` at root hash `h`: every node of `t` is the
  decode of the DB entry at its hash, recursively through extension children and all
  sixteen branch slots (`ChildrenRel`, which also pins the slot-list correspondence).

  The agreement theorems tie the batch-2/4 authenticated walk to the SpecRef
  correctness oracle `trieLookupAux` (the line-for-line port of
  `witness_state.py:_trie_lookup` that obligation #8 verifies the guest against):

  * `read_found_agrees`  — an authenticated `.found v` implies SpecRef returns
    `.ok (some v)`;
  * `read_absent_agrees` — an authenticated `.absent` implies SpecRef returns
    `.ok none`.

  Together with batch 2 (found/found binding) and batch 4 (present/absent binding),
  this closes the pure layer: authenticated outcomes are unequivocal (Keccak-bound)
  AND spec-correct. `.fail` outcomes imply nothing — by design (fuel exhaustion and
  malformed witnesses authenticate nothing; note SpecRef's own fuel-0 returns
  `.ok none`, so no implication is stated for `.fail`).

  No new axioms; no `native_decide`/`bv_decide`.
-/

import EvmAsm.Stateless.WitnessAuth.Absence

namespace EvmAsm.Stateless.WitnessAuth

open EvmAsm.Stateless.SpecRef

mutual

/-- The node DB represents tree `t` at hash `h`: `t`'s root is the decode of the DB
entry at `h`, recursively. Trees with `hashed` nodes are unrepresentable (no
constructor), so represented trees never trip `unresolvedHashedNode`. -/
inductive Represents (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) : Hash32 → MutableNode → Prop
  | leaf {h : Hash32} {e restOfKey value : Bytes}
      (he : dbLookup db h = some e)
      (hv : decodeNode e = some (.leaf restOfKey value)) :
      Represents decodeNode db h (.leaf restOfKey value)
  | ext {h : Hash32} {e keySegment : Bytes} {childHash : Hash32} {child : MutableNode}
      (he : dbLookup db h = some e)
      (hv : decodeNode e = some (.ext keySegment childHash))
      (hc : Represents decodeNode db childHash child) :
      Represents decodeNode db h (.extension keySegment child)
  | branch {h : Hash32} {e value : Bytes} {chs : List (Option Hash32)}
      {children : List (Option MutableNode)}
      (he : dbLookup db h = some e)
      (hv : decodeNode e = some (.branch chs value))
      (hch : ChildrenRel decodeNode db chs children) :
      Represents decodeNode db h (.branch children value)

/-- Slotwise correspondence between a view's child-hash list and the tree's child
list (same length; `none` matches `none`; hashes represent subtrees). -/
inductive ChildrenRel (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) : List (Option Hash32) → List (Option MutableNode) → Prop
  | nil : ChildrenRel decodeNode db [] []
  | consNone {t₁ : List (Option Hash32)} {t₂ : List (Option MutableNode)}
      (ht : ChildrenRel decodeNode db t₁ t₂) :
      ChildrenRel decodeNode db (none :: t₁) (none :: t₂)
  | consSome {h : Hash32} {nd : MutableNode}
      {t₁ : List (Option Hash32)} {t₂ : List (Option MutableNode)}
      (hn : Represents decodeNode db h nd) (ht : ChildrenRel decodeNode db t₁ t₂) :
      ChildrenRel decodeNode db (some h :: t₁) (some nd :: t₂)

end

/-- Slot access under `ChildrenRel`: at every index the two `getD`s are `none`
together or a related `some` pair (out-of-range indices are `none/none`). -/
theorem ChildrenRel.getD_rel {decodeNode : Bytes → Option NodeView}
    {db : List (Hash32 × Bytes)} {l₁ : List (Option Hash32)}
    {l₂ : List (Option MutableNode)}
    (hrel : ChildrenRel decodeNode db l₁ l₂) (idx : Nat) :
    (l₁.getD idx none = none ∧ l₂.getD idx none = none) ∨
    (∃ h nd, l₁.getD idx none = some h ∧ l₂.getD idx none = some nd ∧
      Represents decodeNode db h nd) := by
  induction idx generalizing l₁ l₂ with
  | zero =>
    cases hrel with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | consNone ht => exact Or.inl ⟨rfl, rfl⟩
    | consSome hn ht => exact Or.inr ⟨_, _, rfl, rfl, hn⟩
  | succ idx ih =>
    cases hrel with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | consNone ht => exact ih ht
    | consSome hn ht => exact ih ht

/-- **Authenticated presence agrees with SpecRef**: a `.found v` read at a hash
representing `t` implies `trieLookupAux` on `t` returns `.ok (some v)`. -/
theorem read_found_agrees {decodeNode : Bytes → Option NodeView}
    {db : List (Hash32 × Bytes)} {v : Bytes}
    (fuel : Nat) (h : Hash32) (t : MutableNode) (nibbles : Bytes) (pos : Nat)
    (hrep : Represents decodeNode db h t)
    (hread : dbTrieReadAux decodeNode db fuel h nibbles pos = .found v) :
    trieLookupAux fuel (some t) nibbles pos = .ok (some v) := by
  induction fuel generalizing h t pos with
  | zero => exact absurd hread (by simp [dbTrieReadAux])
  | succ fuel ih =>
    rw [dbTrieReadAux] at hread
    cases hrep with
    | leaf he hv =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      split at hread
      · rename_i hkey
        rw [if_pos hkey]
        exact congrArg (Except.ok ∘ some) (ReadResult.found.inj hread)
      · exact absurd hread (by simp)
    | ext he hv hc =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      split at hread
      · rename_i hseg
        rw [if_pos hseg]
        exact ih _ _ _ hc hread
      · exact absurd hread (by simp)
    | branch he hv hch =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      by_cases hpos : nibbles.length ≤ pos
      · rw [if_pos hpos] at hread ⊢
        split at hread
        · exact absurd hread (by simp)
        · rename_i hval
          rw [if_neg hval]
          exact congrArg (Except.ok ∘ some) (ReadResult.found.inj hread)
      · rw [if_neg hpos] at hread ⊢
        simp only [] at hread ⊢
        rcases hch.getD_rel (nibbles.getD pos 0).toNat with ⟨h1, h2⟩ | ⟨ch, nd, h1, h2, hnd⟩
        · rw [h1] at hread; simp only [] at hread
          exact absurd hread (by simp)
        · rw [h1] at hread; simp only [] at hread
          rw [h2]
          exact ih _ _ _ hnd hread

/-- **Authenticated absence agrees with SpecRef**: an `.absent` read at a hash
representing `t` implies `trieLookupAux` on `t` returns `.ok none`. -/
theorem read_absent_agrees {decodeNode : Bytes → Option NodeView}
    {db : List (Hash32 × Bytes)}
    (fuel : Nat) (h : Hash32) (t : MutableNode) (nibbles : Bytes) (pos : Nat)
    (hrep : Represents decodeNode db h t)
    (hread : dbTrieReadAux decodeNode db fuel h nibbles pos = .absent) :
    trieLookupAux fuel (some t) nibbles pos = .ok none := by
  induction fuel generalizing h t pos with
  | zero => exact absurd hread (by simp [dbTrieReadAux])
  | succ fuel ih =>
    rw [dbTrieReadAux] at hread
    cases hrep with
    | leaf he hv =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      split at hread
      · exact absurd hread (by simp)
      · rename_i hkey
        rw [if_neg hkey]
    | ext he hv hc =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      split at hread
      · rename_i hseg
        rw [if_pos hseg]
        exact ih _ _ _ hc hread
      · rename_i hseg
        rw [if_neg hseg]
    | branch he hv hch =>
      rw [he] at hread; simp only [] at hread
      rw [hv] at hread; simp only [] at hread
      rw [trieLookupAux]
      by_cases hpos : nibbles.length ≤ pos
      · rw [if_pos hpos] at hread ⊢
        split at hread
        · rename_i hval
          rw [if_pos hval]
        · exact absurd hread (by simp)
      · rw [if_neg hpos] at hread ⊢
        simp only [] at hread ⊢
        rcases hch.getD_rel (nibbles.getD pos 0).toNat with ⟨h1, h2⟩ | ⟨ch, nd, h1, h2, hnd⟩
        · rw [h2]
          rw [trieLookupAux]
        · rw [h1] at hread; simp only [] at hread
          rw [h2]
          exact ih _ _ _ hnd hread

end EvmAsm.Stateless.WitnessAuth
