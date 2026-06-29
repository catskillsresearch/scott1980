import Scott1980.Neighborhood.Definition71
import Scott1980.Neighborhood.Exercise722Decide

/-!
# Exercise 7.22 — computable presentation backbone (`SsysX`)

Enumeration `n ↦ SsysX n` for Scott's positive neighbourhood system `Ssys` (`Exercise722.lean`),
toward Definition 7.1 effective givenness. Indices decode to `SExpr` codes; non-empty denotations
are listed, while junk / empty-syntax indices map to the master neighbourhood `Σ` so every index
still names a member of `S` (`SsysX_mem`). Surjectivity onto `S` uses
`inS_iff_exists_denote` (`Exercise722Regular.lean`).

Sessions C9–C10 will add `RecDecidable₂` consistency and the `ComputablePresentation` structure;
relation (i) `interEq` remains deferred (see `Exercise722Decide.lean`, Session C7a).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open Set Domain.Recursive

/-! ## Gödel codes for `SExpr` -/

private def boolNat (b : Bool) : ℕ := if b then 1 else 0

private def natBool (n : ℕ) : Option Bool :=
  match n with | 0 => some false | 1 => some true | _ => none

private def encodeListBool (σ : List Bool) : ℕ := encodeList (σ.map boolNat)

private def decodeListBool (n : ℕ) : Option (List Bool) :=
  (decodeList n).mapM natBool

private theorem decodeListBool_encodeListBool (σ : List Bool) :
    decodeListBool (encodeListBool σ) = some σ := by
  simp [decodeListBool, encodeListBool, decodeList_encodeList, List.mapM_map, List.map_map]
  induction σ with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [boolNat, natBool, ih]

/-- Subexpression depth (for fuelled decoding). -/
def sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (sexprDepth a) (sexprDepth b)
  | .cap a b => 1 + max (sexprDepth a) (sexprDepth b)

/-- Tag-based Gödel code for an `SExpr` (tags `0..3` for the four constructors). -/
def SExpr.encode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (encode a) (encode b))
  | .cap a b => Nat.pair 3 (Nat.pair (encode a) (encode b))

/-- Fuelled decoder: `fuel` bounds recursive unfoldings. -/
def decodeFuel (fuel : ℕ) (n : ℕ) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match n.unpair.1 with
    | 0 => if n.unpair.2 = 0 then some .sigma else none
    | 1 => (decodeListBool n.unpair.2).map (.single ·)
    | 2 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none

theorem decodeFuel_encode {fuel : ℕ} {e : SExpr} (h : sexprDepth e ≤ fuel) :
    decodeFuel fuel (SExpr.encode e) = some e := by
  induction e generalizing fuel with
  | sigma =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode, sexprDepth]
  | single σ =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode, decodeListBool_encodeListBool σ]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]

/-- Index for the enumeration: code plus depth (fuel for decoding). -/
def SExpr.index (e : SExpr) : ℕ := Nat.pair (encode e) (sexprDepth e)

/-- Decoder: `Nat.unpair n` supplies `(code, fuel)` with `fuel = sexprDepth e` on valid indices. -/
def SExpr.decode (n : ℕ) : Option SExpr := decodeFuel (n.unpair.2 + 1) n.unpair.1

theorem SExpr.decode_index (e : SExpr) : decode (index e) = some e := by
  simp [decode, index]
  exact decodeFuel_encode (Nat.le_succ (sexprDepth e))

/-! ## The enumeration `SsysX` -/

/-- Default neighbourhood for junk / empty-syntax indices: the master `Σ = Set.univ`. -/
private def SsysX_default : Set (List Bool) := Set.univ

/-- **Definition 7.1 enumeration backbone.** Decode `n` to an `SExpr`; if the denotation is
non-empty (`decideNonemptyB`), use it; otherwise (or on junk codes) use `Σ` so every index names a
member of the positive system `S`. -/
def SsysX (n : ℕ) : Set (List Bool) :=
  match SExpr.decode n with
  | none => SsysX_default
  | some e =>
    if decideNonemptyB e then denote e else SsysX_default

theorem SsysX_mem (n : ℕ) : InS (SsysX n) := by
  unfold SsysX
  cases hdec : SExpr.decode n with
  | none => simp; exact InS.univ
  | some e =>
    by_cases h : decideNonemptyB e = true
    · simp [h]
      exact InS_denote_of_nonempty ((decideNonemptyB_iff e).1 h)
    · simp [h]
      exact InS.univ

theorem SsysX_surj {Y : Set (List Bool)} (hY : InS Y) : ∃ n, SsysX n = Y := by
  obtain ⟨e, he, hne⟩ := inS_iff_exists_denote.mp hY
  refine ⟨SExpr.index e, ?_⟩
  unfold SsysX
  rw [SExpr.decode_index e]
  have hne' : (denote e).Nonempty := he ▸ hne
  have hb : decideNonemptyB e = true := (decideNonemptyB_iff e).2 hne'
  simp [hb, he]

/-! ## Definition 7.1 (ii) — recursively decidable consistency (Session C9)

Scott's consistency `∃ k, X_k ⊆ X_n ∩ X_m` on a positive system is equivalent to
`(X_n ∩ X_m).Nonempty` (`Ssys_isPositive`). On the `SsysX` enumeration, inactive indices
(decode failure / empty denotation → `SsysX = Σ`) make consistency automatic; active-active
pairs reduce to `consistentB` on decoded expressions. -/

/-- Inactive index: decode fails or denotes the empty language (mapped to `Σ` in `SsysX`). -/
def ssysActive (n : ℕ) : Bool :=
  match SExpr.decode n with
  | none => false
  | some e => decideNonemptyB e

/-- Canonical representative for `SsysX n` as a fragment expression (junk → `Σ`). -/
def safeDecodeActive (n : ℕ) : SExpr :=
  match SExpr.decode n with
  | none => .sigma
  | some e => if decideNonemptyB e then e else .sigma

theorem SsysX_eq_denote_safe (n : ℕ) : SsysX n = denote (safeDecodeActive n) := by
  unfold SsysX safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => simp [hdec, denote_sigma, SsysX_default]
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hdec, hb]
    · simp [hdec, hb, denote_sigma, SsysX_default]

theorem ssys_inter_nonempty_iff_consistent (n m : ℕ) :
    (SsysX n ∩ SsysX m).Nonempty ↔ consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, ← denote_cap, consistentB_iff]

theorem ssys_cons_positivity (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ (SsysX n ∩ SsysX m).Nonempty := by
  constructor
  · intro ⟨k, hk⟩
    exact Set.Nonempty.mono hk (InS.nonempty (SsysX_mem k))
  · intro hne
    have hIn : InS (SsysX n ∩ SsysX m) :=
      (Ssys_isPositive (Ssys_mem.mpr (SsysX_mem n)) (Ssys_mem.mpr (SsysX_mem m))).2 hne
    obtain ⟨k, hk⟩ := SsysX_surj hIn
    exact ⟨k, hk.subset⟩

theorem ssys_cons_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [ssys_cons_positivity, ssys_inter_nonempty_iff_consistent]

/-- `{0,1}` consistency decider on index pairs (active-active uses `consistentB`). -/
def ssysConsistentB (n m : ℕ) : Bool :=
  if !ssysActive n || !ssysActive m then true
  else
    match SExpr.decode n, SExpr.decode m with
    | some a, some b => consistentB a b
    | _, _ => true

theorem safeDecodeActive_inactive (n : ℕ) (h : ssysActive n = false) : safeDecodeActive n = .sigma := by
  dsimp only [ssysActive, safeDecodeActive] at h ⊢
  cases hdec : SExpr.decode n with
  | none => rfl
  | some e =>
    by_cases hb : decideNonemptyB e
    · exfalso
      simp [hdec, hb] at h
    · simp [hdec, hb]

theorem safeDecodeActive_nonempty (n : ℕ) : (denote (safeDecodeActive n)).Nonempty := by
  unfold safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => exact Set.univ_nonempty
  | some e =>
    by_cases hb : decideNonemptyB e
    · simp [hdec, hb]
      exact (decideNonemptyB_iff e).1 hb
    · simp [hdec, hb, denote_sigma]

theorem consistentB_sigma_safe (m : ℕ) : consistentB .sigma (safeDecodeActive m) = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.univ_inter]
  exact safeDecodeActive_nonempty m

theorem consistentB_safe_sigma (n : ℕ) : consistentB (safeDecodeActive n) .sigma = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.inter_univ]
  exact safeDecodeActive_nonempty n

theorem ssysConsistentB_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  by_cases hn : ssysActive n
  · by_cases hm : ssysActive m
    · cases hdecn : SExpr.decode n with
      | none => exfalso; simp [ssysActive, hdecn] at hn
      | some a =>
        cases hdecm : SExpr.decode m with
        | none => exfalso; simp [ssysActive, hdecm] at hm
        | some b =>
          have ha : decideNonemptyB a := by simpa [ssysActive, hdecn] using hn
          have hb : decideNonemptyB b := by simpa [ssysActive, hdecm] using hm
          have hsa : safeDecodeActive n = a := by simp [safeDecodeActive, hdecn, ha]
          have hsb : safeDecodeActive m = b := by simp [safeDecodeActive, hdecm, hb]
          constructor
          · intro h
            rw [hsa, hsb]
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm, Bool.not_eq_true, Bool.or_false]
            rw [heq] at h
            exact h
          · intro hcons
            rw [hsa, hsb] at hcons
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm, Bool.not_eq_true, Bool.or_false]
            rw [heq]
            exact hcons
    · have hm' : ssysActive m = false := by simpa using hm
      constructor
      · intro _; rw [safeDecodeActive_inactive m hm', consistentB_safe_sigma n]
      · intro _; unfold ssysConsistentB; simp [hn, hm']
  · have hn' : ssysActive n = false := by simpa using hn
    constructor
    · intro _; rw [safeDecodeActive_inactive n hn', consistentB_sigma_safe m]
    · intro _; unfold ssysConsistentB; simp [hn']

theorem ssys_cons_char_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔ ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m := by
  rw [ssysConsistentB_iff, ssys_cons_iff]

/-! ### Session C9 — `RecDecidable₂` (BLOCKED)

Scott's consistency on indices is already equivalent to the **Bool** decider `ssysConsistentB`
(`ssys_cons_char_iff`). What remains is a **`Nat.Primrec` `{0,1}` characteristic function**
`Ssys_consChar` with `Ssys_consChar (pair n m) = 1 ↔ ssysConsistentB n m`, then
`Ssys_cons_computable` via `RecDecidable.of_iff` + `ssys_cons_char_iff` (pattern: `Example78.lean`
`PNpres.cons_computable`).

**Blocker:** `decideNonemptyB` / `consistentB` are computable on `SExpr` but not yet primitive-recursive
on Gödel-coded indices. **`Recursive.lean`** now has **`bExistsFn`**, **`primrec_ite`**, **`primrec_max`**
(engine for bounded search); the failed all-in-one port in `Exercise722Primrec.lean` was removed
(2026-06-29). **Next retry:** small primrec layer importing *this file's* `SExpr.decode` / `ssysActive`
— not a duplicate encode/decode tower. See `HANDOFF.md` checkpoint **2026-06-29**. -/

end Exercise722

end Scott1980.Neighborhood
