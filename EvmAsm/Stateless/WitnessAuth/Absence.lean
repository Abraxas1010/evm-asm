/-
  EvmAsm.Stateless.WitnessAuth.Absence

  Batch 4 of obligation #7 (#10141): authenticated absence.

  `SpecRef.WitnessState.trieLookupAux` (and the batch-2 walk mirroring it) returns
  `none` both when a key is *provably absent* (a visited node positively excludes
  it) and when the witness is merely *malformed* (missing DB entry, undecodable
  entry, fuel exhaustion). A stateless guest needs the two separated: reads of
  empty pre-state slots must be *authenticated* absences, not lookup failures.

  `dbTrieRead` refines the walk into a three-valued result:

  * `.found v` — presence, authenticated to the root;
  * `.absent`  — absence, authenticated to the root: the walk reached a node that
    positively excludes the key (leaf with a different remaining key, extension
    whose segment diverges from the key, branch with an empty child slot at the
    key's nibble, or a valueless branch at key exhaustion);
  * `.fail`    — no authentication either way (unresolvable hash, undecodable
    entry, fuel out).

  Theorems:

  * `dbTrieRead_found_iff` — conservativity: `.found v` holds exactly when the
    batch-2 walk returns `some v` (the refinement does not move presence);
  * `present_absent_collision` — the equivocation theorem this batch exists for:
    one built witness DB showing a key *present* and another showing it *absent*
    (same root, same key) yields a concrete Keccak collision, as data.

  No new axioms; no `native_decide`/`bv_decide`.
-/

import EvmAsm.Stateless.WitnessAuth.TrieWalk

namespace EvmAsm.Stateless.WitnessAuth

open EvmAsm.Stateless.SpecRef

/-- Outcome of an authenticated trie read. -/
inductive ReadResult where
  | found (value : Bytes)
  | absent
  | fail
  deriving DecidableEq

/-- Three-valued decode-on-demand walk: as `dbTrieLookupAux`, but classifying
positively-excluding nodes as `.absent` and non-authentication as `.fail`. -/
def dbTrieReadAux (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) :
    Nat → Hash32 → Bytes → Nat → ReadResult
  | 0, _, _, _ => .fail
  | fuel + 1, h, nibbles, pos =>
    match dbLookup db h with
    | none => .fail
    | some entry =>
      match decodeNode entry with
      | none => .fail
      | some view =>
        match view with
        | .leaf restOfKey value =>
          if nibbles.drop pos == restOfKey then .found value else .absent
        | .ext keySegment childHash =>
          if (nibbles.drop pos).take keySegment.length == keySegment then
            dbTrieReadAux decodeNode db fuel childHash nibbles (pos + keySegment.length)
          else .absent
        | .branch children value =>
          if nibbles.length ≤ pos then
            if value.isEmpty then .absent else .found value
          else
            match children.getD (nibbles.getD pos 0).toNat none with
            | some childHash => dbTrieReadAux decodeNode db fuel childHash nibbles (pos + 1)
            | none => .absent

/-- Authenticated three-valued read (fuel as in `trieLookup`). -/
def dbTrieRead (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) (root : Hash32) (keyHash : Hash32) : ReadResult :=
  let nibbles := keyToNibbles keyHash
  dbTrieReadAux decodeNode db (nibbles.length + 2) root nibbles 0

/-- Conservativity over the batch-2 walk, fueled form: `.found v` exactly when
`dbTrieLookupAux` returns `some v`. -/
theorem dbTrieReadAux_found_iff (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) (fuel : Nat) (h : Hash32) (nibbles : Bytes) (pos : Nat)
    (v : Bytes) :
    dbTrieReadAux decodeNode db fuel h nibbles pos = .found v ↔
      dbTrieLookupAux decodeNode db fuel h nibbles pos = some v := by
  induction fuel generalizing h pos with
  | zero => simp [dbTrieReadAux, dbTrieLookupAux]
  | succ fuel ih =>
    rw [dbTrieReadAux, dbTrieLookupAux]
    cases hd : dbLookup db h with
    | none => simp
    | some entry =>
      simp only [Option.bind]
      cases hv : decodeNode entry with
      | none => simp
      | some view =>
        cases view with
        | leaf restOfKey value =>
          simp only []
          split <;> simp
        | ext keySegment childHash =>
          simp only []
          split
          · exact ih childHash (pos + keySegment.length)
          · simp
        | branch children value =>
          simp only []
          split
          · split <;> simp
          · cases hch : children.getD (nibbles.getD pos 0).toNat none with
            | some childHash => simp only []; exact ih childHash (pos + 1)
            | none => simp

/-- Fueled present/absent equivocation: one built DB reads `.found v`, another
reads `.absent`, same hash/key/position — a Keccak collision. -/
theorem dbTrieReadAux_present_absent (decodeNode : Bytes → Option NodeView)
    {entries₁ entries₂ : List Bytes} {v : Bytes}
    (fuel : Nat) (h : Hash32) (nibbles : Bytes) (pos : Nat)
    (h₁ : dbTrieReadAux decodeNode (build_node_db entries₁) fuel h nibbles pos = .found v)
    (h₂ : dbTrieReadAux decodeNode (build_node_db entries₂) fuel h nibbles pos = .absent) :
    ∃ e₁ e₂, KeccakCollision e₁ e₂ := by
  induction fuel generalizing h pos with
  | zero => exact absurd h₁ (by simp [dbTrieReadAux])
  | succ fuel ih =>
    rw [dbTrieReadAux] at h₁ h₂
    cases hd₁ : dbLookup (build_node_db entries₁) h with
    | none => rw [hd₁] at h₁; simp at h₁
    | some e₁ =>
      cases hd₂ : dbLookup (build_node_db entries₂) h with
      | none => rw [hd₂] at h₂; simp at h₂
      | some e₂ =>
        rw [hd₁] at h₁; rw [hd₂] at h₂
        simp only [] at h₁ h₂
        by_cases he : e₁ = e₂
        · subst he
          cases hv : decodeNode e₁ with
          | none => rw [hv] at h₁; simp at h₁
          | some view =>
            rw [hv] at h₁ h₂
            simp only [] at h₁ h₂
            cases view with
            | leaf restOfKey value =>
              simp only [] at h₁ h₂
              split at h₁
              · rename_i hkey
                rw [if_pos hkey] at h₂
                exact absurd h₂ (by simp)
              · exact absurd h₁ (by simp)
            | ext keySegment childHash =>
              simp only [] at h₁ h₂
              split at h₁
              · rename_i hseg
                rw [if_pos hseg] at h₂
                exact ih childHash (pos + keySegment.length) h₁ h₂
              · exact absurd h₁ (by simp)
            | branch children value =>
              simp only [] at h₁ h₂
              by_cases hpos : nibbles.length ≤ pos
              · rw [if_pos hpos] at h₁ h₂
                split at h₁
                · exact absurd h₁ (by simp)
                · rename_i hval
                  rw [if_neg hval] at h₂
                  exact absurd h₂ (by simp)
              · rw [if_neg hpos] at h₁ h₂
                cases hch : children.getD (nibbles.getD pos 0).toNat none with
                | some childHash =>
                  rw [hch] at h₁ h₂
                  exact ih childHash (pos + 1) h₁ h₂
                | none =>
                  rw [hch] at h₁
                  exact absurd h₁ (by simp)
        · exact ⟨e₁, e₂, db_equivocation_collision hd₁ hd₂ he⟩

/-- **Present/absent equivocation is a Keccak collision.** No pair of built witness
DBs can authenticate a key as present (with any value) to one reader and as absent
to another, against the same state root, without a concrete Keccak collision.
Together with `dbTrieLookup_binding` (found/found) this brackets the read: for a
fixed root and key, all authenticated outcomes agree unless Keccak is broken. -/
theorem present_absent_collision (decodeNode : Bytes → Option NodeView)
    {entries₁ entries₂ : List Bytes} {v : Bytes} (root keyHash : Hash32)
    (h₁ : dbTrieRead decodeNode (build_node_db entries₁) root keyHash = .found v)
    (h₂ : dbTrieRead decodeNode (build_node_db entries₂) root keyHash = .absent) :
    ∃ e₁ e₂, KeccakCollision e₁ e₂ :=
  dbTrieReadAux_present_absent decodeNode _ root _ 0 h₁ h₂

/-- Conservativity at the top level: authenticated presence coincides with the
batch-2 walk. -/
theorem dbTrieRead_found_iff (decodeNode : Bytes → Option NodeView)
    (db : List (Hash32 × Bytes)) (root keyHash : Hash32) (v : Bytes) :
    dbTrieRead decodeNode db root keyHash = .found v ↔
      dbTrieLookup decodeNode db root keyHash = some v :=
  dbTrieReadAux_found_iff decodeNode db _ root _ 0 v

end EvmAsm.Stateless.WitnessAuth
