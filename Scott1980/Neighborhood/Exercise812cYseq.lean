import Scott1980.Neighborhood.Exercise812c
import Scott1980.Neighborhood.Theorem88

/-!
# Exercise 8.12(c)(vi)(1) (Scott 1981, PRG-19, Lecture VIII) — the abstract `Yseq` closed form

Generalizes `Theorem88.lean`'s core `Yseq` closed-form apparatus (`atomU`, `Yseq`,
`split_fst_eq_inter_Yseq`, `atomU_subset_master`, `atomU_succ_eq`, `atomU_eq_genAtom`) from the
hardcoded target `U : NeighborhoodSystem ℚ` to an **abstract atomless `E : NeighborhoodSystem γ`**,
exactly mirroring how `Exercise812c.lean`'s `exists_split'`/`SplitSpec'`/`splitChoice'` generalized
`exists_split`/`SplitSpec`/`splitChoice`. Once done twice (once with `E := D₀`, once with
`E := D₁`, in 8.12(c)(vi)(5)/(vi)(6)), this is the machinery that recovers a *closed-form*
description of `atomPair`'s two interleaved sub-steps — the two-sided analogue of Scott's `Yₙ`.

## What is reused unchanged from `Theorem88.lean`

`extendTrue`/`restrictFin` (and their agreement lemmas `extendTrue_agree`/
`extendTrue_restrictFin_agree`) and the generic `genAtom` family (`genAtom`, `genAtom_subset`,
`genAtom_congr`, `genAtom_forward`, `genAtom_self`) are **already fully type-generic** in
`Theorem88.lean` — none of them mention `U` at all. They are imported and used *verbatim* below,
with no re-statement needed.

## What is new here

Everything downstream of `atomU` in `Theorem88.lean` (`atomU` itself onward) is hardcoded to
`U.master`/`U.mem`. This file re-proves that whole layer — `atomE` (the `atomU`-analogue),
`atomE_invariant`, `YseqE` (the `Yseq`-analogue), `split_fst_eq_inter_YseqE`, `atomE_subset_master`,
`atomE_succ_eq`, `atomE_eq_genAtom` — against an abstract `E : NeighborhoodSystem γ` and an abstract
`split` satisfying `SplitSpec' E split` (`Exercise812c.lean`), taking `E.master.Nonempty` as an
extra explicit hypothesis (`U.master`'s nonemptiness was previously a hardcoded fact about `[0,1)`;
for the eventual instantiations `E := D₀`/`E := D₁` this is exactly the `hD₀mne`/`hD₁mne` hypothesis
already in scope in `Exercise812c.lean`'s `section AtomPair`). The finite-constraint transfer lemma
(`transfer_empty_iff` and its corollaries) and the nonemptiness facts (`Yseq_empty_or_mem`/
`Yseq_nonempty_of_mem`) are deliberately **not** included here — tracked separately as
8.12(c)(vi)(2)/(vi)(3).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α γ : Type*}

/-! ### The abstract `E`-side atom, generalizing `atomU` -/

variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)

/-- The `E`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` satisfying `SplitSpec' E split`. Generalizes `Theorem88.lean`'s `atomU` from the
hardcoded target `U` to an abstract `E`. -/
noncomputable def atomE (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set γ
  | 0 => E.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2

variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomE_zero (δ : ℕ → Bool) : atomE E split X Δ δ 0 = E.master := rfl

theorem atomE_succ (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 := rfl

/-- Extending/changing `δ` at or beyond position `n` does not change `atomE E split X Δ δ n`
(mirrors `atomU_congr`). -/
theorem atomE_congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomE E split X Δ δ n = atomE E split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomE E split X Δ δ n = atomE E split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [atomE_succ, atomE_succ, hA, hprev, hn]

/-! ### The core invariant: emptiness-matching, `E.mem`-or-empty, and pairwise disjointness -/

variable (hΔ : Δ.Nonempty) (hEmne : E.master.Nonempty) (hsplit : SplitSpec' E split)
include hΔ hEmne hsplit

/-- **The core invariant, generalizing `atomU_invariant`.** At every depth `n` and for every sign
sequence `δ`: (a) the atom-matching invariant (`genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅`),
(b) `atomE E split X Δ δ n` is either empty or a genuine `E`-neighbourhood, and (c) pairwise
disjointness for sign sequences disagreeing somewhere below `n`. -/
theorem atomE_invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅) ∧
      (∀ δ, atomE E split X Δ δ n = ∅ ∨ E.mem (atomE E split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr E.master_mem,
      fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (E.master : Set γ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hEmne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomE_succ]
      by_cases hδ : δ n = true
      · rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ X n from by simp [genAtom, hδ]]
        simp only [hδ, if_true]
        exact hspec.2.2.1
      · rw [Bool.not_eq_true] at hδ
        have hsub := genAtom_subset X Δ δ n
        rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n \ X n from by
          have heq : genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ (Δ \ X n) := by simp [genAtom, hδ]
          rw [heq]
          ext x; constructor
          · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
          · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩]
        simp only [hδ]
        exact hspec.2.2.2.1
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomE_succ]
      by_cases hδ : δ n = true
      · simp only [hδ, if_true]; exact hspec.1
      · simp only [hδ]; exact hspec.2.1
    · by_cases hagree : ∀ j < n, δ j = δ' j
      · have hδn : δ n ≠ δ' n := by
          intro heq
          exact hne (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact hagree i hi'
            · exact heq)
        have hA : genAtom X Δ δ n = genAtom X Δ δ' n := genAtom_congr X Δ hagree
        have hB : atomE E split X Δ δ n = atomE E split X Δ δ' n := atomE_congr E split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [atomE_succ, atomE_succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
          rw [atomE_succ]
          by_cases hδ : δ n = true
          · simp only [hδ, if_true]; exact split_fst_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomE E split X Δ δ' (n + 1) ⊆ atomE E split X Δ δ' n := by
          rw [atomE_succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', if_true]; exact split_fst_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

/-- Corollary of `atomE_invariant`, extracted for reuse: `atomE` only shrinks as `n` grows
(mirrors `atomU_succ_subset`). -/
theorem atomE_succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  rw [atomE_succ]
  by_cases hδ : δ n = true
  · simp only [hδ, if_true]; exact split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset' hsplit (hmatch δ) (hmem δ) (X n)

/-! ### `YseqE`: the abstract analogue of Scott's `Yₙ`

Reuses `Theorem88.lean`'s `extendTrue`/`restrictFin` verbatim (already fully generic, no `U`- or
`E`-specific content). -/

omit hΔ hEmne hsplit in
/-- **The abstract analogue of Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the
"+"-piece chosen when splitting against `X n`. Generalizes `Theorem88.lean`'s `Yseq`. -/
noncomputable def YseqE (n : ℕ) : Set γ :=
  ⋃ δ' : Fin n → Bool, atomE E split X Δ (extendTrue δ') (n + 1)

omit hΔ hEmne hsplit in
theorem subset_YseqE {n : ℕ} (δ' : Fin n → Bool) :
    atomE E split X Δ (extendTrue δ') (n + 1) ⊆ YseqE E split X Δ n :=
  Set.subset_iUnion (fun δ' => atomE E split X Δ (extendTrue δ') (n + 1)) δ'

/-- **The "I-formula", generalizing `split_fst_eq_inter_Yseq`**: the "+"-piece chosen when
splitting the depth-`n` atom for `δ` against `X n` is *exactly* the intersection of that atom with
`YseqE E split X Δ n`. -/
theorem split_fst_eq_inter_YseqE (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 =
      atomE E split X Δ δ n ∩ YseqE E split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomE E split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomE E split X Δ δ2 (n + 1) = I := by
    rw [atomE_succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomE E split X Δ δ2 n = B := by
      apply atomE_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, if_pos rfl, hA2, hB2]
  have hδ3_eq : atomE E split X Δ δ3 (n + 1) = I := (atomE_congr E split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ YseqE E split X Δ n := hδ3_eq ▸ subset_YseqE E split X Δ (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomE E split X Δ (extendTrue δ') n = B := atomE_congr E split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomE E split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomE_succ, hAeq, hBeq, hlast, if_pos rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomE E split X Δ (extendTrue δ') n :=
        atomE_succ_subset E split X Δ hΔ hEmne hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

/-- `atomE E split X Δ δ n` is always a subset of `E.master` (mirrors `atomU_subset_master`). -/
theorem atomE_subset_master (δ : ℕ → Bool) (n : ℕ) : atomE E split X Δ δ n ⊆ E.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomE_succ_subset E split X Δ hΔ hEmne hsplit δ n).trans ih

/-- **Closed form for `atomE`, generalizing `atomU_succ_eq`**: with `YseqE` in hand, `atomE`
satisfies exactly the same recursive description as `genAtom (YseqE E split X Δ) E.master`. -/
theorem atomE_succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      atomE E split X Δ δ n ∩
        (if δ n then YseqE E split X Δ n else E.master \ YseqE E split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := atomE_invariant E split X Δ hΔ hEmne hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_YseqE E split X Δ hΔ hEmne hsplit δ n
  by_cases hδ : δ n = true
  · rw [atomE_succ, if_pos hδ, if_pos hδ]; exact hIeq
  · rw [atomE_succ, if_neg hδ, if_neg hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 =
        atomE E split X Δ δ n \ YseqE E split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomE E split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomE E split X Δ δ n ∩ YseqE E split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := atomE_subset_master E split X Δ hΔ hEmne hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

/-- **`atomE` coincides with the generic atom construction on `YseqE`/`E.master`**, generalizing
`atomU_eq_genAtom`. Lets every later argument treat `atomE` and `genAtom` uniformly (in particular,
`genAtom_forward`/`genAtom_self` — proved once, generically, in `Theorem88.lean` — apply verbatim
to the `E`-side atoms too). -/
theorem atomE_eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomE E split X Δ δ n = genAtom (YseqE E split X Δ) E.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [atomE_succ_eq E split X Δ hΔ hEmne hsplit, atomE_eq_genAtom δ n]; rfl

end Scott1980.Neighborhood
