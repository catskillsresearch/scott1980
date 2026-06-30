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

theorem boolNat_eq_one_iff (b : Bool) : boolNat b = 1 ↔ b := by
  cases b <;> simp [boolNat]

theorem boolNat_zero_one (b : Bool) : boolNat b = 0 ∨ boolNat b = 1 := by
  cases b <;> simp [boolNat]

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

private theorem natBool_isSome_iff (n : ℕ) :
    (natBool n).isSome = true ↔ n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool]
  | 1 => simp [natBool]
  | n + 2 => simp [natBool]

private theorem natBinDigit_of_natBool_some (n : ℕ) {b : Bool} (h : natBool n = some b) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool] at h; exact Or.inl rfl
  | 1 => simp [natBool] at h; exact Or.inr rfl
  | n + 2 => simp [natBool] at h

private theorem mapM_natBool_isSome_iff (l : List ℕ) :
    (l.mapM natBool).isSome = true ↔ ∀ x ∈ l, x = 0 ∨ x = 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons]
    constructor
    · intro h
      cases hnx : natBool x with
      | none => simp [hnx] at h
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [hnx, htx] at h
        | some ts =>
          have hxs' : (xs.mapM natBool).isSome = true := by simp [htx, h]
          intro y hy
          rcases List.mem_cons.mp hy with hEq | hyTail
          · rw [hEq]
            exact natBinDigit_of_natBool_some x hnx
          · exact ih.mp hxs' y hyTail
    · intro h
      have hx : (natBool x).isSome = true :=
        (natBool_isSome_iff x).2 (h x (List.mem_cons_self ..))
      have hxs : (xs.mapM natBool).isSome = true :=
        ih.mpr fun y hy => h y (List.mem_cons_of_mem x hy)
      cases hnx : natBool x with
      | none =>
        rcases h x (List.mem_cons_self ..) with h0 | h1
        · subst h0; simp [natBool] at hnx
        · subst h1; simp [natBool] at hnx
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [htx] at hxs
        | some ts => simp [hnx, htx, hx, hxs]

/-- **7.22i(b)1(d):** list decode succeeds iff every coded entry is a binary digit. -/
theorem decodeListBool_isSome_iff (n : ℕ) :
    (decodeListBool n).isSome = true ↔ allBinDigitsChar n = 1 := by
  simp only [decodeListBool, mapM_natBool_isSome_iff, allBinDigitsChar_eq_one_iff]

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

private theorem decodeFuel_succ_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 = 0) :
    decodeFuel (fuel + 1) c = some .sigma := by simp [decodeFuel, h, hσ]

private theorem decodeFuel_succ_not_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 ≠ 0) :
    decodeFuel (fuel + 1) c = none := by simp [decodeFuel, h, hσ]

private theorem decodeFuel_succ_single (fuel c : ℕ) (h : c.unpair.1 = 1) :
    decodeFuel (fuel + 1) c = (decodeListBool c.unpair.2).map (.single ·) := by
  simp [decodeFuel, h]

private theorem decodeFuel_succ_cat (fuel c : ℕ) (h : c.unpair.1 = 2) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none := by simp [decodeFuel, h]

private theorem decodeFuel_succ_cap (fuel c : ℕ) (h : c.unpair.1 = 3) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none := by simp [decodeFuel, h]

private theorem decodeFuel_succ_junk (fuel c : ℕ) (h : 4 ≤ c.unpair.1) :
    decodeFuel (fuel + 1) c = none := by
  match tag : c.unpair.1 with
  | 0 | 1 | 2 | 3 => omega
  | t + 4 => simp [decodeFuel, tag]

private theorem decodeFuel_pair_cat_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cat a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp

private theorem decodeFuel_pair_cap_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cap a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp

/-- **7.22i(b)1(e):** shallow link between fuel-bounded char decode and `decodeFuel`. -/
theorem decodeFuelOkChar_eq_one_iff (fuel c : ℕ) :
    decodeFuelOkChar fuel c = 1 ↔ (decodeFuel fuel c).isSome = true := by
  induction fuel generalizing c with
  | zero =>
    simp [decodeFuelOkChar, decodeFuel]
  | succ fuel ih =>
    simp only [decodeFuelOkChar]
    rw [decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      rw [show decodeFuel (fuel + 1) c = if c.unpair.2 = 0 then some .sigma else none from by
        by_cases hσ : c.unpair.2 = 0 <;> simp [decodeFuel, tag, hσ]]
      simp [selectFn_isOne_one_sub_sigma]
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag]
      simp [decodeListBool_isSome_iff, Option.isSome_map]
    | 2 =>
      rw [decodeFuel_succ_cat fuel c tag, mulBit_eq_one_iff, decodeFuel_pair_cat_isSome_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mp h1, ih2.mp h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mpr h1, ih2.mpr h2⟩
    | 3 =>
      rw [decodeFuel_succ_cap fuel c tag, mulBit_eq_one_iff, decodeFuel_pair_cap_isSome_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mp h1, ih2.mp h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mpr h1, ih2.mpr h2⟩
    | t + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)]
      simp [tag]

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
    by_cases hb : decideNonemptyB e = true
    · have hne : (denote e).Nonempty := (decideNonemptyB_iff e).1 hb
      simpa [hdec, hb] using hne
    · simpa [hdec, hb, denote_sigma] using Set.univ_nonempty

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
              simp [hn, hm, hdecn, hdecm]
            rw [heq] at h
            exact h
          · intro hcons
            rw [hsa, hsb] at hcons
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
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

/-- Scott's consistency relation (Definition 7.1 (ii)) on the `SsysX` indices is decidable via
`ssysConsistentB` (choice-free on the `Bool` side; see axiom audit of `decideNonemptyB_iff`). -/
instance decidableSsysCons (n m : ℕ) :
    Decidable (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  decidable_of_iff (ssysConsistentB n m = true) (ssys_cons_char_iff n m)

/-! ### Session C9 — `RecDecidable₂` (primitive-recursive bridge)

The mathematics is finished (`ssys_cons_char_iff`). The generic packaging lemma is
`RecDecidable₂.of_paired_zero_one_char` in `Recursive.lean`: once a `{0,1}`-valued characteristic is
`Nat.Primrec`, `RecDecidable₂` follows immediately.

**Numeric characteristic** for the existing Bool decider (no new algorithm).

Unfolding `ssys_cons_char_iff` (which chains through `ssys_cons_iff` / `consistentB_iff`) can exceed
the default 200000 heartbeat budget; raise the limit for this section only. -/

set_option maxHeartbeats 5000000

/-- `{0,1}` packaging of `ssysConsistentB` on `Nat.pair`-coded index pairs. -/
def ssysConsChar (t : ℕ) : ℕ := boolNat (ssysConsistentB t.unpair.1 t.unpair.2)

theorem ssysConsChar_eq_one_iff (t : ℕ) :
    ssysConsChar t = 1 ↔ ssysConsistentB t.unpair.1 t.unpair.2 = true := by
  simp [ssysConsChar, boolNat_eq_one_iff]

theorem ssysConsChar_zero_one (t : ℕ) : ssysConsChar t = 0 ∨ ssysConsChar t = 1 :=
  boolNat_zero_one _

theorem ssys_cons_char_eq_one_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ ssysConsChar (Nat.pair n m) = 1 := by
  rw [ssysConsChar_eq_one_iff, ssys_cons_char_iff, unpair_pair_fst, unpair_pair_snd]

/-- **Conditional C9 closure.** Instantiated once the sole missing primitive-recursive link below
is proved. -/
theorem Ssys_cons_computable_of_primrec_ssysConsChar (hf : Nat.Primrec ssysConsChar) :
    RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  RecDecidable₂.of_paired_zero_one_char hf ssysConsChar_zero_one ssys_cons_char_eq_one_iff

-- TODO (Scott Exercise 7.22 C9b8): `primrec_ssysConsChar : Nat.Primrec ssysConsChar`
-- TODO (Scott Exercise 7.22 C9b8): `Ssys_cons_computable` via
--   `Ssys_cons_computable_of_primrec_ssysConsChar primrec_ssysConsChar`
--
-- The mathematics is finished (`ssys_cons_char_iff`). The only missing piece is the
-- primitive-recursive realization of `ssysConsChar` (no new algorithm). Slices (C9b / 7.22i(b)):
-- 0. `isBinDigit` / `allBinDigitsChar` in `Recursive.lean` (C9a / 7.22i(a) ☑)
-- 1. C9b1 / 7.22i(b)1 — (a) mulBit ☑ (b) decodeFuelOkChar+primrec ☑;
--    (c) dispatch lemmas ☑ (d) decodeListBool_isSome_iff ☑ (e) decodeFuelOkChar_eq_one_iff ☑
--    See `arxiv.md` rows **7.22i(b)1(a–e)**.
-- 2. `listLenChar` + primrec (C9b2 / 7.22i(b)2) ☑
-- 3. `listEqChar` + primrec (C9b3 / 7.22i(b)3) — Need Advice
-- 4. `appendListCode`, `takeCode`, `dropCode` + primrec (C9b4 / 7.22i(b)4) — Not Yet
-- 5. `autStateCardFuelChar`, `matchesBChar` + primrec (C9b5 / 7.22i(b)5) — Not Yet
-- 6. `decideNonemptyBChar`, `consistentBChar` + primrec (C9b6 / 7.22i(b)6) — Not Yet
-- 7. `ssysConsistentBChar` + shallow Bool `_eq` lemmas (C9b7 / 7.22i(b)7) — Not Yet
-- 8. `primrec_ssysConsChar` → `Ssys_cons_computable` (C9b8 / 7.22i(b)8) — Not Yet
-- See `arxiv.md` rows **7.22i(b)1–8** (one slice per session; avoid monolith).

end Exercise722

end Scott1980.Neighborhood
