import Scott1980.Neighborhood.Exercise812c
import Scott1980.Neighborhood.Definition71

/-!
# Exercise 8.12(d) (Scott 1981, PRG-19, Lecture VIII) — effective refinement of 8.12(c)

## 8.12(d)(1): generalizing the core recursion over an abstract split

`Exercise812c.lean`'s `xStep`/`yStep`/`atomPair` are all built directly on top of the
**classical** `splitChoice' D₁ hD₁nomin`/`splitChoice' D₀ hD₀nomin` (defined via `Classical.choice`
over `exists_split'`). To eventually get an *effective* isomorphism we need to re-run the exact same
construction with a **computable** split instead — so the first step is to generalize `xStep`/
`yStep`/`atomPair` (and its core invariant/disjointness/subset facts) over an *abstract* split
satisfying `SplitSpec'`, rather than one hardcoded to come from `NoMinimal` via choice.

This turns out to be a comparatively light abstraction, because `Exercise812c.lean`'s own generic
layer (`xyStep`, `xyStep_disjoint_of_ne`, `SplitSpec'`, `split_fst_subset'`, `split_snd_subset'`) is
**already** split-agnostic — the hardcoding to `splitChoice'` only happens at `xStep`/`yStep`
themselves (`Exercise812c.lean` lines 390/398). So this file's job is: redo *just* `xStep`/`yStep`
through `atomPair`'s subset/disjointness/master-subset facts (`Exercise812c.lean` lines 390–757)
with the `NoMinimal`-witnessed `splitChoice' Dᵢ hDᵢnomin` replaced by an arbitrary
`(splitX, hxSplit : SplitSpec' D₁ splitX)`/`(splitY, hySplit : SplitSpec' D₀ splitY)` pair — every
proof step transcribes essentially verbatim, replacing `splitChoice'_isSplitSpec Dᵢ hDᵢnomin`
(a *term*) with the hypothesis `hxSplit`/`hySplit` directly.

**Scope note (adjustment from the original `arxiv.md` scoping, discovered during execution):** the
original scoping listed `XPseq`/`YPseq`/`combinedX`/`combinedY`/`toD1`/`toD0`/`domainIso812c` as
also needing a parallel classical-abstract-split generalization in this sub-part. On closer
inspection this is unnecessary extra work: those are all downstream consequences of `atomPair`'s
invariant/disjointness/subset facts alone (never touching `splitX`/`splitY`/`hxSplit`/`hySplit`
directly), so `(d)(3)`–`(d)(6)` can build the *code-level* analogues (`atomPairCode`,
`XPseqCode`/`YPseqCode`, computability of `toD1`/`toD0`, final `EffectiveIso` assembly) directly on
top of `atomPairG` below, without first needing a redundant *classical* abstract-split replica of
the whole downstream chain. This keeps `(d)(1)` focused on the genuinely load-bearing recursive
core that every later sub-part depends on.

We also verify, as a sanity check that the abstraction is not vacuous and genuinely subsumes
`Exercise812c.lean`'s construction, that instantiating `splitX := splitChoice' D₁ hD₁nomin`/
`splitY := splitChoice' D₀ hD₀nomin` recovers `atomPair` exactly (`atomPairG_splitChoice_eq`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

/-! ### The two named sub-steps of `atomPair`, generalized over an abstract split

Direct analogues of `Exercise812c.lean`'s `xStep`/`yStep`, taking the split function itself as an
explicit argument instead of deriving it from a `NoMinimal` witness via `splitChoice'`. -/

section StepGen

variable {α β : Type*}

/-- **Generalized `xStep`**: split `D₁`'s side (via the abstract `splitX`) while directly refining
`D₀`'s side. Literally `xyStep splitX`; `xStep D₁ hD₁nomin = xStepG (splitChoice' D₁ hD₁nomin)`. -/
noncomputable def xStepG (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep splitX A B Xn b

/-- **Generalized `yStep`**: split `D₀`'s side (via the abstract `splitY`) while directly refining
`D₁`'s side. Literally `(xyStep splitY _ _ _ _).swap`; `yStep D₀ hD₀nomin = yStepG (splitChoice' D₀
hD₀nomin)`. -/
noncomputable def yStepG (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep splitY B1 A1 Yn b).swap

theorem xStepG_fst_subset (splitX : Set α → Set β → Set α → Set β × Set β)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStepG splitX A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, if_true]; exact Set.inter_subset_left
  · simp only [xStepG, xyStep, hb]; exact Set.diff_subset

theorem xStepG_snd_subset {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStepG splitX A B Xn b).2 ⊆ B := by
  have hspec := hxSplit hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, if_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStepG, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

theorem yStepG_fst_subset {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStepG splitY A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := hySplit hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, if_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStepG, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

theorem yStepG_snd_subset (splitY : Set β → Set α → Set β → Set α × Set α)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStepG splitY A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, if_true]; exact Set.inter_subset_left
  · simp only [yStepG, xyStep, Prod.swap, hb]; exact Set.diff_subset

theorem xStepG_disjoint_of_ne {D₁ : NeighborhoodSystem β}
    {splitX : Set α → Set β → Set α → Set β × Set β} (hxSplit : SplitSpec' D₁ splitX)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStepG splitX A B Xn b).1 ∩ (xStepG splitX A B Xn b').1 = ∅ ∧
      (xStepG splitX A B Xn b).2 ∩ (xStepG splitX A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne hxSplit hAB hBmem Xn hbb'

theorem yStepG_disjoint_of_ne {D₀ : NeighborhoodSystem α}
    {splitY : Set β → Set α → Set β → Set α × Set α} (hySplit : SplitSpec' D₀ splitY)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStepG splitY A1 B1 Yn b).1 ∩ (yStepG splitY A1 B1 Yn b').1 = ∅ ∧
      (yStepG splitY A1 B1 Yn b).2 ∩ (yStepG splitY A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne hySplit hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

end StepGen

/-! ### `atomPair`, generalized over an abstract split pair

Direct analogue of `Exercise812c.lean`'s `section AtomPair` (lines 552–757: the recursive
definition through `atomPair_fst_subset_master`/`atomPair_snd_subset_master`), with `hD₀nomin`/
`hD₁nomin` replaced throughout by `(splitY, hySplit)`/`(splitX, hxSplit)`. `NoMinimal` itself is no
longer needed anywhere in this generalized layer — only `SplitSpec'` is ever used. -/

section AtomPairGen

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hySplit : SplitSpec' D₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hxSplit : SplitSpec' D₁ splitX)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

/-- **Generalized `atomPair`**, taking the split functions directly instead of deriving them from
`NoMinimal` witnesses. -/
noncomputable def atomPairG (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPairG δ n).1
      let B := (atomPairG δ n).2
      let IJ1 := splitX A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitY B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

theorem atomPairG_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPairG D₀ D₁ splitY splitX X Y δ (n + 1) =
      yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne

/-- **The core invariant, generalized.** Direct transcription of `atomPair_invariant`. -/
theorem atomPairG_invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ↔
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).1 = ∅ ∨
        D₀.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).1) ∧
      ((atomPairG D₀ D₁ splitY splitX X Y δ n).2 = ∅ ∨
        D₁.mem (atomPairG D₀ D₁ splitY splitX X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
    set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
    have hspec1 := hxSplit ihAB ihB (X n)
    set I1 := (splitX A B (X n)).1 with hI1def
    set J1 := (splitX A B (X n)).2 with hJ1def
    set A1 := (if (δ n).1 then A ∩ X n else A \ X n) with hA1def
    set B1 := (if (δ n).1 then I1 else J1) with hB1def
    have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hB1def, hδ1, if_true]; exact hspec1.2.2.1
      · simp only [hA1def, hB1def, hδ1]; exact hspec1.2.2.2.1
    have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hA1def, hδ1, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
      · simp only [hA1def, hδ1]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)
    have hB1mem : B1 = ∅ ∨ D₁.mem B1 := by
      by_cases hδ1 : (δ n).1 = true
      · simp only [hB1def, hδ1, if_true]; exact hspec1.1
      · simp only [hB1def, hδ1]; exact hspec1.2.1
    have hspec2 := hySplit hA1B1.symm hA1mem (Y n)
    set I2 := (splitY B1 A1 (Y n)).1 with hI2def
    set J2 := (splitY B1 A1 (Y n)).2 with hJ2def
    set B2 := (if (δ n).2 then B1 ∩ Y n else B1 \ Y n) with hB2def
    set A2 := (if (δ n).2 then I2 else J2) with hA2def
    have hB2A2 : B2 = ∅ ↔ A2 = ∅ := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hA2def, hδ2, if_true]; exact hspec2.2.2.1
      · simp only [hB2def, hA2def, hδ2]; exact hspec2.2.2.2.1
    have hB2mem : B2 = ∅ ∨ D₁.mem B2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hB2def, hδ2, if_true]; exact inter_mem_or_empty hD₁pos hB1mem (hYmem n)
      · simp only [hB2def, hδ2]; exact diff_mem_or_empty hD₁diff hB1mem (hYmem n)
    have hA2mem : A2 = ∅ ∨ D₀.mem A2 := by
      by_cases hδ2 : (δ n).2 = true
      · simp only [hA2def, hδ2, if_true]; exact hspec2.1
      · simp only [hA2def, hδ2]; exact hspec2.2.1
    show (A2 = ∅ ↔ B2 = ∅) ∧ (A2 = ∅ ∨ D₀.mem A2) ∧ (B2 = ∅ ∨ D₁.mem B2)
    exact ⟨hB2A2.symm, hA2mem, hB2mem⟩

omit hD₀pos hD₀diff hySplit hD₁pos hD₁diff hxSplit hXmem hYmem hD₀mne hD₁mne in
/-- Extending/changing `δ` at or beyond position `n` does not change `atomPairG δ n`. -/
theorem atomPairG_congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPairG D₀ D₁ splitY splitX X Y δ n = atomPairG D₀ D₁ splitY splitX X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPairG D₀ D₁ splitY splitX X Y δ n =
        atomPairG D₀ D₁ splitY splitX X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1
       let B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2
       let IJ1 := splitX A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitY B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
         let B := (atomPairG D₀ D₁ splitY splitX X Y δ' n).2
         let IJ1 := splitX A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitY B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

/-- **`xStepG`'s output satisfies the preconditions `yStepG` needs**, generalizing `xStep_spec`. -/
theorem xStepG_spec (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 = ∅ ↔
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅) ∧
      ((xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 = ∅ ∨
        D₀.mem (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX X Y δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX X Y δ n).2 with hBdef
  have hspec1 := hxSplit ihAB ihB (X n)
  refine ⟨?_, ?_⟩
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, if_true]; exact hspec1.2.2.1.symm
    · simp only [xStepG, xyStep, hδ1]; exact hspec1.2.2.2.1.symm
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStepG, xyStep, hδ1, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
    · simp only [xStepG, xyStep, hδ1]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)

/-- **`atomPairG`'s `α`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPairG_fst_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := by
  rw [atomPairG_succ_eq]
  obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG_fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2).trans
    (xStepG_fst_subset splitX _ _ (X n) (δ n).1)

/-- **`atomPairG`'s `β`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPairG_snd_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
      (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := by
  rw [atomPairG_succ_eq]
  obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStepG_snd_subset splitY _ _ (Y n) (δ n).2).trans
    (xStepG_snd_subset hxSplit ihAB ihB (X n) (δ n).1)

/-- **`atomPairG`'s `α`-side is always `⊆ D₀.master`.** -/
theorem atomPairG_fst_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ⊆ D₀.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

/-- **`atomPairG`'s `β`-side is always `⊆ D₁.master`**. -/
theorem atomPairG_snd_subset_master (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ⊆ D₁.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n).trans ih

/-- **Pairwise disjointness of `atomPairG` on both sides at once**, generalizing
`atomPair_disjoint`. -/
theorem atomPairG_disjoint (δ δ' : ℕ → Bool × Bool) :
    ∀ n, (∃ i < n, δ i ≠ δ' i) →
      (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 = ∅ ∧
        (atomPairG D₀ D₁ splitY splitX X Y δ n).2 ∩
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 = ∅ := by
  intro n
  induction n with
  | zero => rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rintro ⟨i, hi, hine⟩
    by_cases hagree : ∀ j < n, δ j = δ' j
    · have hδn : δ n ≠ δ' n := by
        intro heq
        exact hine (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hagree i hi'
          · exact heq)
      have hpairEq : atomPairG D₀ D₁ splitY splitX X Y δ n =
          atomPairG D₀ D₁ splitY splitX X Y δ' n :=
        atomPairG_congr D₀ D₁ splitY splitX X Y hagree
      have hAB' : (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 =
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 ∧
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 =
            (atomPairG D₀ D₁ splitY splitX X Y δ n).2 :=
        ⟨(congrArg Prod.fst hpairEq).symm, (congrArg Prod.snd hpairEq).symm⟩
      by_cases h1 : (δ n).1 = (δ' n).1
      · have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPairG_succ_eq, atomPairG_succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStepG_disjoint_of_ne hySplit hspecAB hspecAmem (Y n) h2
      · obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStepG_disjoint_of_ne hxSplit ihAB ihB (X n) h1
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
        obtain ⟨hspecAB', hspecAmem'⟩ := xStepG_spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
        have h1sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).1 := by
          rw [atomPairG_succ_eq]; exact yStepG_fst_subset hySplit hspecAB hspecAmem (Y n) (δ n).2
        have h2sub : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ n).2 (X n) (δ n).1).2 := by
          rw [atomPairG_succ_eq]; exact yStepG_snd_subset splitY _ _ (Y n) (δ n).2
        have h1sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).1 := by
          rw [atomPairG_succ_eq]; exact yStepG_fst_subset hySplit hspecAB' hspecAmem' (Y n) (δ' n).2
        have h2sub' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
            (xStepG splitX (atomPairG D₀ D₁ splitY splitX X Y δ' n).1
              (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 (X n) (δ' n).1).2 := by
          rw [atomPairG_succ_eq]; exact yStepG_snd_subset splitY _ _ (Y n) (δ' n).2
        rw [hAB'.1, hAB'.2] at h1sub' h2sub'
        exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1sub h1sub') hxdisj.1,
          Set.subset_eq_empty (Set.inter_subset_inter h2sub h2sub') hxdisj.2⟩
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      obtain ⟨hd1, hd2⟩ := ih ⟨j, hj, hjne⟩
      have h1 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).1 := atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h1' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).1 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).1 := atomPairG_fst_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      have h2 : (atomPairG D₀ D₁ splitY splitX X Y δ (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ n).2 := atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h2' : (atomPairG D₀ D₁ splitY splitX X Y δ' (n + 1)).2 ⊆
          (atomPairG D₀ D₁ splitY splitX X Y δ' n).2 := atomPairG_snd_subset D₀ D₁ hD₀pos hD₀diff
        splitY hySplit hD₁pos hD₁diff splitX hxSplit X Y hXmem hYmem hD₀mne hD₁mne δ' n
      exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1 h1') hd1,
        Set.subset_eq_empty (Set.inter_subset_inter h2 h2') hd2⟩

end AtomPairGen

/-! ### Sanity check: instantiating with the classical split recovers `Exercise812c.lean`'s `atomPair`

Confirms the generalization is not vacuous: `atomPair` (from 8.12(c)) is exactly `atomPairG`
instantiated at `splitX := splitChoice' D₁ hD₁nomin`, `splitY := splitChoice' D₀ hD₀nomin`. -/

section Recover

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀nomin : D₀.NoMinimal) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β)

theorem atomPairG_splitChoice_eq (δ : ℕ → Bool × Bool) :
    ∀ n, atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n =
      atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show
      (let A := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).1
       let B := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) = atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)
    rw [atomPair_succ_eq]
    show
      (let A := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).1
       let B := (atomPairG D₀ D₁ (splitChoice' D₀ hD₀nomin) (splitChoice' D₁ hD₁nomin) X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        yStep D₀ hD₀nomin
          (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
          (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
          (Y n) (δ n).2
    rw [ih]
    rfl

end Recover

/-! ## 8.12(d)(2): computable splits relative to two presentations

A split function `split : Set α → Set γ → Set α → Set γ × Set γ` is *computable relative to*
presentations `P` (of the `α`-side) and `Q` (of the `γ`-side) when both of its outputs are given by
a **primitive-recursive** function of the three input indices — mirroring `IsComputableMap`'s
"transport the semantic relation to the integer indices" idea (Definition 7.2), but for a genuine
*function* rather than a relation, so we ask for `Nat.Primrec` index functions with an exact
(rather than merely r.e.) correctness spec, matching `ComputablePresentation.inter`'s own shape
(a primitive-recursive intersection-index function, `inter_spec`).

This one structure serves **both** `splitX : Set α → Set β → Set α → Set β × Set β` (as
`IsComputableSplit P₀ P₁ splitX`) and `splitY : Set β → Set α → Set β → Set α × Set α` (as
`IsComputableSplit P₁ P₀ splitY`, roles swapped) — no separate `X`/`Y`-flavoured structure needed. -/

/-- **A split function is computable relative to two presentations** `P` (`α`-side), `Q` (`γ`-side)
when its two outputs are indexed by primitive-recursive functions of the three input indices
(indices of `A` in `P`, `B` in `Q`, `Xn` in `P`). Only the two index functions are data; primitive-
recursiveness and correctness (`posIdx_spec`/`negIdx_spec`) are `Prop`s, so this is choice-free. -/
structure IsComputableSplit {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
    (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (split : Set α → Set γ → Set α → Set γ × Set γ) where
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).1`, as a function of the three input
  indices `n, m, k`. -/
  posIdx : ℕ → ℕ → ℕ → ℕ
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).2`. -/
  negIdx : ℕ → ℕ → ℕ → ℕ
  /-- `posIdx` is primitive recursive (on the `Nat.pair n (Nat.pair m k)` coding, matching
  `RecDecidable₃`'s convention). -/
  posIdx_primrec : Nat.Primrec (fun t => posIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `negIdx` is primitive recursive. -/
  negIdx_primrec : Nat.Primrec (fun t => negIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `posIdx n m k` genuinely indexes the split's first output. -/
  posIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).1 = Q.X (posIdx n m k)
  /-- `negIdx n m k` genuinely indexes the split's second output. -/
  negIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).2 = Q.X (negIdx n m k)

namespace IsComputableSplit

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}
  {split : Set α → Set γ → Set α → Set γ × Set γ}

/-- The split's first output is always a genuine `W`-neighbourhood (immediate from `posIdx_spec`
and `Q.mem_X`; the "= ∅ ∨ mem" disjunction from `SplitSpec'` is not needed here, since every `Q.X k`
is *already* a genuine neighbourhood — `SplitSpec'`'s "or ∅" only matters when relating back to the
literal set `(split A B Xn).1`, which by `posIdx_spec` is literally *equal to* some `Q.X k`). -/
theorem posIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).1 := by
  rw [h.posIdx_spec]; exact Q.mem_X _

/-- The split's second output is always a genuine `W`-neighbourhood. -/
theorem negIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).2 := by
  rw [h.negIdx_spec]; exact Q.mem_X _

end IsComputableSplit

end Scott1980.Neighborhood
