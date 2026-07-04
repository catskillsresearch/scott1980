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

open NeighborhoodSystem Domain.Recursive

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

/-! ## 8.12(d)(3)(a): `IsComputableDiff` — the missing "diff index" prerequisite

`ComputablePresentation` (Definition 7.1) only makes **intersection** effective (`inter`/
`inter_spec`, guarded by the consistency decider `cons_computable`). `atomPairG`'s recursion
(`xStepG`/`yStepG`) needs the *direct* refinement `A \ Xn` to stay effectively indexed at every
step too (the "split" sub-step is handled by `IsComputableSplit` above), and Definition 7.1 simply
has no such primitive for `\`. `IsComputableDiff` supplies exactly that, mirroring `inter`/
`inter_primrec`/`inter_spec`'s shape — with `cons_computable`'s role (deciding *consistency*,
i.e. whether the operation's output is a genuine neighbourhood) played here by `diff_computable`.

Both `IsComputableSplit`'s clause `A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅` (`SplitSpec'`) and
`NeighborhoodSystem.DiffClosed` (`X \ Y = ∅ ∨ D.mem (X \ Y)`, and no neighbourhood is `∅` under
`NoMinimal`) together mean "`X n \ X m` is a genuine neighbourhood" and "`X n \ X m` is non-empty"
coincide propositionally; `diff_computable` is phrased as the *existence* form (matching
`cons_computable`'s own phrasing) so it stays a direct structural mirror, but every later sub-part
is free to read it as an emptiness decider via that coincidence. One structure serves **both**
`P₀` and `P₁` symmetrically — no separate hypothesis needed per side. -/

/-- **`IsComputableDiff P`**: set-difference relative to the presentation `P` is computable — a
primitive-recursive `diffIdx : ℕ → ℕ → ℕ` indexing `X n \ X m` whenever that difference is a
genuine neighbourhood (`diffIdx_spec`, mirroring `inter_spec` exactly), together with a decider
for that very side-condition (`diff_computable`, mirroring `cons_computable`). Only `diffIdx` is
data; the rest are `Prop`s, so this stays choice-free to *state* (any particular instance may of
course need `Classical.choice` to *construct*, exactly like `inter`/`cons_computable` themselves
would for an arbitrary effectively-given system). -/
structure IsComputableDiff {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V) where
  /-- Index of `X n \ X m`, as a function of the two input indices. -/
  diffIdx : ℕ → ℕ → ℕ
  /-- `diffIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  diffIdx_primrec : Nat.Primrec (fun t => diffIdx t.unpair.1 t.unpair.2)
  /-- `diffIdx n m` genuinely indexes `X n \ X m` whenever that difference is (exactly) some
  `X k` — i.e. whenever it is a genuine neighbourhood. -/
  diffIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n \ P.X m) → P.X (diffIdx n m) = P.X n \ P.X m
  /-- **7.1(i)-for-`\`**: "`X n \ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  diff_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n \ P.X m)

namespace IsComputableDiff

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **The emptiness/genuineness dichotomy**, transported through `DiffClosed` +
`NoMinimal.mem_ne_empty`: for a `DiffClosed`, `NoMinimal` system, "`X n \ X m` is a genuine
neighbourhood" and "`X n \ X m` is non-empty" are the *same* proposition — so `diff_computable`
may equally be read as an emptiness decider. Not needed to *state* `IsComputableDiff` (kept off
the structure itself, matching how `DiffClosed`/`NoMinimal` are separate hypotheses from
`ComputablePresentation` elsewhere in this file), but recorded here once for later sub-parts to
reuse directly instead of re-deriving. -/
theorem diff_exists_iff_ne_empty (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    (∃ k, P.X k = P.X n \ P.X m) ↔ P.X n \ P.X m ≠ ∅ := by
  constructor
  · rintro ⟨k, hk⟩ hempty
    exact NoMinimal.mem_ne_empty hnomin (P.mem_X k) (hk.trans hempty)
  · intro hne
    rcases hdiff (P.mem_X n) (P.mem_X m) with hempty | hmem
    · exact absurd hempty hne
    · exact P.surj hmem

end IsComputableDiff

/-! ## 8.12(d)(3)(b): the `X`-sub-step's code-level state transition

`atomPairG`'s recursion state at depth `n` is a pair `(A_n, B_n) : Set α × Set β`. At the code
level we track it as a triple `(idx0, idx1, junk)`: `idx0`/`idx1` index `A_n`/`B_n` in `P₀`/`P₁`
(meaningful only when `junk = 0`), and `junk` is a **single shared** flag for "`A_n = B_n = ∅`
already". A single flag (rather than "one per side", as originally tentatively scoped) suffices
because `atomPairG_invariant`'s own `ihAB` clause (`(d)(1)`) already proves the two sides go empty
**together** at every depth — so a per-side flag would always just duplicate the other.

The `X`-sub-step (`xStepG`) refines `D₀`'s side **directly** (intersect/diff against `X n = P₀.X n`
— the presentation's own `n`-th neighbourhood; the eventual application enumerates *all* of `P₀`'s
neighbourhoods this way, mirroring `Theorem88d.lean`'s `idxSet (e P) n`) and `D₁`'s side via the
**split** (`(d)(2)`'s `IsComputableSplit`). This sub-part builds that half-step as a single
`Nat.Primrec` function of a packed `(n, bit, state)` argument; `(d)(3)(c)` composes it with the
symmetric `Y`-sub-step into the full `n → n + 1` transition. -/

/-! ### Direct-refinement decidability, extracted from `cons_computable`/`IsComputableDiff`

Two deciders, mirroring `Theorem88d.lean`'s `datomDec` extraction pattern (`Classical.choice` via
`RecDecidable`'s bare existential, then `isOne`-wrapped so the result is *literally* `{0,1}`-valued,
not just "`= 1` iff …"): whether `X n ∩ X m` (resp. `X n \ X m`) is empty. -/

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- **Extracted existence decider for `∩`**: `1` iff `∃ k, X k ⊆ X n ∩ X m` (`cons_computable`'s
own predicate). -/
noncomputable def existsInterDec : ℕ → ℕ := fun t => isOne (P.cons_computable.choose t)

theorem primrec_existsInterDec : Nat.Primrec (existsInterDec P) :=
  (primrec_isOne.comp P.cons_computable.choose_spec.1).of_eq fun _ => rfl

theorem existsInterDec_le_one (t : ℕ) : existsInterDec P t ≤ 1 := isOne_le_one _

theorem existsInterDec_spec (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
  unfold existsInterDec
  rw [isOne_eq_one_iff]
  have h := P.cons_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

/-- **The `∩`-existence decider matches non-emptiness**, given `IsPositive` + `NoMinimal`: any
consistency witness is itself a non-empty neighbourhood (`NoMinimal.mem_ne_empty`), and conversely
a non-empty intersection is a neighbourhood by `IsPositive`, hence indexed by `surj`. -/
theorem existsInterDec_eq_zero_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 0 ↔ P.X n ∩ P.X m = ∅ := by
  have hle := existsInterDec_le_one P (Nat.pair n m)
  constructor
  · intro h0
    by_contra hne
    have hmem : V.mem (P.X n ∩ P.X m) :=
      (hpos (P.mem_X n) (P.mem_X m)).mpr (Set.nonempty_iff_ne_empty.mpr hne)
    obtain ⟨k, hk⟩ := P.surj hmem
    have h1 : existsInterDec P (Nat.pair n m) = 1 :=
      (existsInterDec_spec P n m).mpr ⟨k, by rw [hk]⟩
    omega
  · intro hempty
    by_contra hne1
    have h1 : existsInterDec P (Nat.pair n m) = 1 := by omega
    obtain ⟨k, hk⟩ := (existsInterDec_spec P n m).mp h1
    exact absurd (Set.subset_eq_empty hk hempty) (hnomin.mem_ne_empty (P.mem_X k))

/-- **The `∩`-emptiness decider** (`1` iff `X n ∩ X m = ∅`): the complementary flag to
`existsInterDec`. -/
noncomputable def emptyInterDec : ℕ → ℕ := fun t => 1 - existsInterDec P t

theorem primrec_emptyInterDec : Nat.Primrec (emptyInterDec P) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec_existsInterDec P)

theorem emptyInterDec_le_one (t : ℕ) : emptyInterDec P t ≤ 1 := by
  unfold emptyInterDec; have := existsInterDec_le_one P t; omega

theorem emptyInterDec_eq_one_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyInterDec P (Nat.pair n m) = 1 ↔ P.X n ∩ P.X m = ∅ := by
  unfold emptyInterDec
  have hle := existsInterDec_le_one P (Nat.pair n m)
  have h0 := existsInterDec_eq_zero_iff P hpos hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

variable (hDiff : IsComputableDiff P)

/-- **Extracted existence decider for `\`**: `1` iff `∃ k, X k = X n \ X m`
(`IsComputableDiff.diff_computable`'s own predicate). -/
noncomputable def existsDiffDec : ℕ → ℕ := fun t => isOne (hDiff.diff_computable.choose t)

theorem primrec_existsDiffDec : Nat.Primrec (existsDiffDec P hDiff) :=
  (primrec_isOne.comp hDiff.diff_computable.choose_spec.1).of_eq fun _ => rfl

theorem existsDiffDec_le_one (t : ℕ) : existsDiffDec P hDiff t ≤ 1 := isOne_le_one _

theorem existsDiffDec_spec (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 1 ↔ ∃ k, P.X k = P.X n \ P.X m := by
  unfold existsDiffDec
  rw [isOne_eq_one_iff]
  have h := hDiff.diff_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

/-- **The `\`-existence decider matches non-emptiness**, via `IsComputableDiff.diff_exists_iff_ne_empty`. -/
theorem existsDiffDec_eq_zero_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 0 ↔ P.X n \ P.X m = ∅ := by
  have hle := existsDiffDec_le_one P hDiff (Nat.pair n m)
  have h1 := existsDiffDec_spec P hDiff n m
  have h2 := IsComputableDiff.diff_exists_iff_ne_empty (P := P) hdiff hnomin n m
  constructor
  · intro h0
    by_contra hne
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := h1.mpr (h2.mpr hne)
    omega
  · intro hempty
    by_contra hne0
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := by omega
    exact (h2.mp (h1.mp h1')) hempty

/-- **The `\`-emptiness decider** (`1` iff `X n \ X m = ∅`). -/
noncomputable def emptyDiffDec : ℕ → ℕ := fun t => 1 - existsDiffDec P hDiff t

theorem primrec_emptyDiffDec : Nat.Primrec (emptyDiffDec P hDiff) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec_existsDiffDec P hDiff)

theorem emptyDiffDec_le_one (t : ℕ) : emptyDiffDec P hDiff t ≤ 1 := by
  unfold emptyDiffDec; have := existsDiffDec_le_one P hDiff t; omega

theorem emptyDiffDec_eq_one_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyDiffDec P hDiff (Nat.pair n m) = 1 ↔ P.X n \ P.X m = ∅ := by
  unfold emptyDiffDec
  have hle := existsDiffDec_le_one P hDiff (Nat.pair n m)
  have h0 := existsDiffDec_eq_zero_iff P hDiff hdiff hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

end DirectDec

/-! ### The two-sided packed state `(idx0, idx1, junk)` -/

/-- Pack a two-sided code state: `idx0` (`P₀`-index of `A_n`), `idx1` (`P₁`-index of `B_n`),
`junk` (`1` iff `A_n = B_n = ∅` already). -/
def packState2 (idx0 idx1 junk : ℕ) : ℕ := Nat.pair idx0 (Nat.pair idx1 junk)

def stateIdx0 (s : ℕ) : ℕ := s.unpair.1
def stateIdx1 (s : ℕ) : ℕ := s.unpair.2.unpair.1
def stateJunk (s : ℕ) : ℕ := s.unpair.2.unpair.2

@[simp] theorem stateIdx0_packState2 (a b c : ℕ) : stateIdx0 (packState2 a b c) = a := by
  unfold stateIdx0 packState2; simp only [unpair_pair_fst]
@[simp] theorem stateIdx1_packState2 (a b c : ℕ) : stateIdx1 (packState2 a b c) = b := by
  unfold stateIdx1 packState2; simp only [unpair_pair_fst, unpair_pair_snd]
@[simp] theorem stateJunk_packState2 (a b c : ℕ) : stateJunk (packState2 a b c) = c := by
  unfold stateJunk packState2; simp only [unpair_pair_snd]

theorem primrec_stateIdx0 : Nat.Primrec stateIdx0 := Nat.Primrec.left
theorem primrec_stateIdx1 : Nat.Primrec stateIdx1 := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_stateJunk : Nat.Primrec stateJunk := Nat.Primrec.right.comp Nat.Primrec.right

/-- The base (depth-`0`) state: `A₀ = D₀.master`, `B₀ = D₁.master`, never junk. -/
def stateBase2 (masterIdx0 masterIdx1 : ℕ) : ℕ := packState2 masterIdx0 masterIdx1 0

/-! ### The `X`-sub-step

Packed-argument convention `w = pair n (pair b1 s)` (mirroring `Theorem88d.lean`'s `atomStep`
convention `w = pair k (pair y state)`): `n` is the current depth, `b1` is `(δ n).1` coded as
`0`/`1`, `s` is the incoming two-sided state. -/

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwN (w : ℕ) : ℕ := w.unpair.1
def xwB1 (w : ℕ) : ℕ := w.unpair.2.unpair.1
def xwS (w : ℕ) : ℕ := w.unpair.2.unpair.2

theorem primrec_xwN : Nat.Primrec xwN := Nat.Primrec.left
theorem primrec_xwB1 : Nat.Primrec xwB1 := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_xwS : Nat.Primrec xwS := Nat.Primrec.right.comp Nat.Primrec.right

/-- **The `X`-sub-step.** Refines `D₀`'s side (`idx0`) directly against `P₀.X n` (intersect if
`b1 = 1`, diff if `b1 = 0`, via `P₀.inter`/`hDiff0.diffIdx`), and `D₁`'s side (`idx1`) via the
matching branch of the split `hSplitX` — freezing both at the junk sentinel `0` the moment either
the incoming state was already junk, or this step's direct refinement is found empty. -/
noncomputable def xSubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b1 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b1 (P₀.inter idx0 n) (hDiff0.diffIdx idx0 n)
  let directEmpty := selectFn b1 (emptyInterDec P₀ (Nat.pair idx0 n))
    (emptyDiffDec P₀ hDiff0 (Nat.pair idx0 n))
  let splitIdx := selectFn b1 (hSplitX.posIdx idx0 idx1 n) (hSplitX.negIdx idx0 idx1 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 directIdx) (selectFn newJunk 0 splitIdx) newJunk

theorem primrec_xSubStep : Nat.Primrec (xSubStep P₀ P₁ hDiff0 splitX hSplitX) := by
  have hn : Nat.Primrec xwN := primrec_xwN
  have hb1 : Nat.Primrec xwB1 := primrec_xwB1
  have hs : Nat.Primrec xwS := primrec_xwS
  have hidx0 : Nat.Primrec (fun w => stateIdx0 (xwS w)) := primrec_stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => stateIdx1 (xwS w)) := primrec_stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => stateJunk (xwS w)) := primrec_stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₀.inter (stateIdx0 (xwS w)) (xwN w)) :=
    (P₀.inter_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)) :=
    (hDiff0.diffIdx_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyInterDec P₀).comp (hidx0.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))) :=
    (primrec_emptyDiffDec P₀ hDiff0).comp (hidx0.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.posIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)) :=
    (hSplitX.negIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (P₀.inter (stateIdx0 (xwS w)) (xwN w)) (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hb1 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (xwB1 w)
      (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
      (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))) :=
    primrec_selectFn hb1 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (P₀.inter (stateIdx0 (xwS w)) (xwN w))
        (hDiff0.diffIdx (stateIdx0 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (stateJunk (xwS w)) 1 (selectFn (xwB1 w)
      (emptyInterDec P₀ (Nat.pair (stateIdx0 (xwS w)) (xwN w)))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (xwS w)) (xwN w))))) 0
      (selectFn (xwB1 w) (hSplitX.posIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w))
        (hSplitX.negIdx (stateIdx0 (xwS w)) (stateIdx1 (xwS w)) (xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold xSubStep packState2
    simp only []

end XSubStep
