/-
  EvmAsm.Stateless.WitnessAuth

  Batch 1 of obligation #7 (verified MPT pre-state witness verification; #10141):
  the node-DB authentication kernel, stated over `SpecRef.WitnessState`'s exact
  model (`build_node_db : List Bytes → List (Hash32 × Bytes)`, keying each witness
  entry by `keccak256 entry`).

  Three declarations, consumed by name by the later batches (walk-level binding
  over `MutableNode`, RLP node views, completeness/absence):

  * `dbLookup` — first-match association-list lookup, the read primitive the
    decode step resolves `hashed` references through;
  * `dbLookup_build_sound` — every byte-string resolved from a built node DB is
    keccak-authenticated: the returned entry hashes to the queried key;
  * `db_equivocation_collision` — the atomic binding brick: two *distinct*
    byte-strings resolved under one `Hash32` key (from possibly different
    witness DBs) are a concrete Keccak collision, as data.

  Proof tier: all three are complete over the full input domain (no
  preconditions). No new axioms; no `native_decide`/`bv_decide`.
-/

import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Stateless.WitnessAuth

open EvmAsm.Stateless.SpecRef

/-- First-match lookup in a node DB (`List (Hash32 × Bytes)` in witness order).
Duplicate keys cannot disagree in a *built* DB — a first-match/last-match divergence
under one key is exactly a `db_equivocation_collision` — so first-match is canonical. -/
def dbLookup (db : List (Hash32 × Bytes)) (h : Hash32) : Option Bytes :=
  (db.find? (fun e => e.1 == h)).map (·.2)

/-- **Soundness of node-DB resolution**: a hit in `build_node_db entries` returns an
entry whose keccak hash is the queried key — every resolved byte-string is
keccak-authenticated by construction of the DB. -/
theorem dbLookup_build_sound {entries : List Bytes} {h : Hash32} {e : Bytes}
    (hit : dbLookup (build_node_db entries) h = some e) :
    keccak256 e = h := by
  unfold dbLookup at hit
  cases hfind : (build_node_db entries).find? (fun p => p.1 == h) with
  | none => rw [hfind] at hit; exact absurd hit.symm (Option.some_ne_none _)
  | some p =>
    rw [hfind] at hit
    have hkey : p.1 = h := by
      have := List.find?_some hfind
      exact eq_of_beq this
    have hmem : p ∈ build_node_db entries := List.mem_of_find?_eq_some hfind
    unfold build_node_db at hmem
    obtain ⟨entry, -, hpe⟩ := List.mem_map.mp hmem
    have he : e = p.2 := (Option.some.inj hit).symm
    rw [he, ← hpe]
    simpa [← hpe] using hkey

/-- Two distinct byte-strings with the same keccak hash: a concrete Keccak collision. -/
def KeccakCollision (e₁ e₂ : Bytes) : Prop :=
  e₁ ≠ e₂ ∧ keccak256 e₁ = keccak256 e₂

/-- **Node-DB equivocation is a Keccak collision.** If two witness node DBs (possibly
the same one) resolve the *same* `Hash32` key to *distinct* byte-strings, those two
byte-strings are a Keccak collision, as data. This is the atomic binding brick: every
higher authentication layer (trie-walk binding, account decode, absence proofs)
reduces its equivocation case to this statement. -/
theorem db_equivocation_collision {entries₁ entries₂ : List Bytes} {h : Hash32}
    {e₁ e₂ : Bytes}
    (h₁ : dbLookup (build_node_db entries₁) h = some e₁)
    (h₂ : dbLookup (build_node_db entries₂) h = some e₂)
    (hne : e₁ ≠ e₂) :
    KeccakCollision e₁ e₂ :=
  ⟨hne, (dbLookup_build_sound h₁).trans (dbLookup_build_sound h₂).symm⟩

/-! ## `#guard` examples (house pattern): the kernel evaluates the primitives -/

-- a two-entry DB resolves both keys to their preimages …
#guard dbLookup (build_node_db [[0x01], [0x02, 0x03]]) (keccak256 [0x01]) = some [0x01]
#guard dbLookup (build_node_db [[0x01], [0x02, 0x03]]) (keccak256 [0x02, 0x03])
  = some [0x02, 0x03]
-- … refuses an unknown key …
#guard dbLookup (build_node_db [[0x01], [0x02, 0x03]]) (keccak256 [0x04]) = none
-- … and the empty DB resolves nothing.
#guard dbLookup (build_node_db []) EMPTY_TRIE_ROOT = none

end EvmAsm.Stateless.WitnessAuth
