import Scott1980.Neighborhood.Exercise812
import Scott1980.Neighborhood.IntervalPrimrec
import Scott1980.Neighborhood.Theorem88

/-!
# Exercise 8.12(c) (Scott 1981, PRG-19, Lecture VIII) — a general two-sided back-and-forth lemma

Following the 7-part plan recorded in `arxiv.md`/`HANDOFF.md`, this file works towards **Exercise
8.12(c)**: a new, general (non-effective) lemma that two countable, atomless neighbourhood systems,
each satisfying a mutual one-step extension property relative to the other, are order-isomorphic.

## A structural shortcut over `Theorem88.lean`'s one-sided embedding

`Theorem88.lean`'s back-and-forth (`exists_split`/`atomU`/`Yseq`) embeds an *arbitrary* countable
`D` into `U` by tracking a matching pair `(A, B)` where only the `U`-side `B` is kept a genuine
`U`-neighbourhood-or-∅ at every step (via `U_no_minimal`); the `D`-side atom `A` is *never* required
to be a `D`-neighbourhood — it is an uninterpreted Boolean combination of `D`'s own sets and their
*complements* (`Δ \ Xᵢ`), which need not lie in `D` at all. This asymmetry is exactly what makes a
one-sided *embedding* enough, but is also exactly what breaks for a genuine two-sided
*isomorphism*: to alternately refine **both** sides (sometimes splitting `D₀`'s atom via `D₀`'s own
no-minimal property, sometimes `D₁`'s), the side not currently being split still needs to remain a
genuine neighbourhood-or-∅ at every step, including right after being intersected/subtracted by an
enumerated neighbourhood from the *other* side.

**Key discovery**: both `U` and `V` are already *Boolean-closed* — closed not just under
consistent intersection (Definition 1.1(ii)) but under **set-difference** of any two of their own
neighbourhoods (`U_diff_mem`, `V_diff_mem` below), on top of their already-known closure under
finite union (`U_union_mem`/`V_union_mem`) and unconditional/positive intersection
(`U`'s `combineIntervals`, `V`'s `levelSet_inter`, both witness-free). `U`'s case is nearly free:
`IntervalPrimrec.lean`'s `diffLists`/`presentedIntervals_diffLists` (built for the *computable*
presentation, Exercise 7.22-style) already witnesses this unconditionally, so `U_diff_mem` is a
two-line corollary. `V`'s case is the bitmask arithmetic identity `a ^^^ (a &&& b)` = "`a` and not
`b`", mirroring `levelSet_inter`'s own `upsample`-then-`&&&` formula.

Boolean-closure means a **complement-relative-to-master is always mem-or-∅** (`X \ D.master`, or
rather `D.master \ X`, is a special case with `Y := D.master`), and hence *every finite Boolean
combination* of enumerated neighbourhoods and their complements (`genAtom`, `Theorem88.lean`'s own
notion) is *automatically* mem-or-∅ by a direct induction — no `Classical.choice`-driven splitting
needed to keep either side "in the family". This is the structural fact that will let the two-sided
construction alternate which side is intersected/subtracted (a free computation) against which side
is split via the *other* system's no-minimal property (the one place non-constructive choice
genuinely enters, exactly as in `Theorem88.lean`), symmetrically.

## Status

This file establishes:

1. The Boolean-closure prerequisites `U_diff_mem`/`V_diff_mem` (and `U_isPositive`/`V_isPositive`,
 `U_noMinimal`/`V_noMinimal` repackaging the existing `U_no_minimal`/`V_no_minimal`).
2. The generic definitions (`NeighborhoodSystem.NoMinimal`, `.DiffClosed`) the back-and-forth is
 stated over, plus `genAtom_mem_or_empty` (Boolean atoms are automatically mem-or-∅ — no choice
 needed) and its one-step building blocks `inter_mem_or_empty`/`diff_mem_or_empty`.
3. `exists_split'`/`SplitSpec'`/`splitChoice'`: `Theorem88.lean`'s `exists_split`/`SplitSpec`/
 `splitChoice`, generalized from the hardcoded target `U` to an abstract atomless `E`.
4. **`atomPair`/`atomPair_invariant`**: the interleaved two-sided atom construction and its core
 invariant (matched emptiness, mem-or-∅ on both sides at every depth). This is the technical heart
 of the two-sided back-and-forth — see the section docstring above `atomPair` for the construction.

**Not yet done** (tracked as 8.12(c)'s remaining work): pairwise disjointness of `atomPair` across
disagreeing sign sequences (needed for a `Yseq`-style closed form on *both* sides at once), the
resulting `Xseq`/`Yseq`-analogue transfer lemmas (subset/inter-empty/inter-eq, mirroring
`Theorem88.lean`'s `transfer_subset_iff`/`transfer_inter_eq_iff` but bidirectionally), and the final
assembly into `DomainIso D₀ D₁`. This remaining work is comparable in size to the rest of
`Theorem88.lean` (`Yseq` onward) plus `Theorem88a.lean`'s assembly, done twice (once per direction)
plus the interleaving glue — a substantial next increment, tracked in `HANDOFF.md`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

/-! ### `U` is difference-closed -/

/-- **`U` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty): `IntervalPrimrec.lean`'s `diffLists`/`presentedIntervals_diffLists`, built unconditionally
from `Ico_diff_Ico`, already witnesses presentability of the raw difference; only non-emptiness can
fail. -/
theorem U_diff_mem {X Y : Set ℚ} (hX : U.mem X) (hY : U.mem Y) : X \ Y = ∅ ∨ U.mem (X \ Y) := by
  obtain ⟨⟨L1, rfl⟩, -, hXsub⟩ := hX
  obtain ⟨⟨L2, rfl⟩, -, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (presentedIntervals L1 \ presentedIntervals L2) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨diffLists L1 L2, (presentedIntervals_diffLists L1 L2).symm⟩, h,
      Set.diff_subset.trans hXsub⟩

/-! ### `V` is difference-closed -/

/-- **The bitwise "and-not" identity**: `a ^^^ (a &&& b) = a` on bits where `b`'s bit is `0`, and
`= 0` on bits where `b`'s bit is `1` (whether or not `a`'s bit is set) — i.e. exactly "`a`'s bits
with `b`'s bits cleared". Mirrors `levelSet_inter`'s own `&&&`-formula; here `^^^` combines with
`&&&` instead, since `a &&& b` is always a "submask" of `a` (every set bit of `a &&& b` is already a
set bit of `a`), so XOR-ing it out just clears exactly those shared bits. -/
theorem testBit_xor_and_self (a b : ℕ) (i : ℕ) :
    (a ^^^ (a &&& b)).testBit i = (a.testBit i && !b.testBit i) := by
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

/-- **`levelSet` is closed under set-difference, unconditionally** — mirrors `levelSet_inter`
exactly, combining `upsample`-to-a-common-level with the "and-not" bit identity
`testBit_xor_and_self` in place of plain `&&&`. -/
theorem levelSet_diff (k₁ m₁ k₂ m₂ : ℕ) :
    levelSet k₁ m₁ \ levelSet k₂ m₂
      = levelSet (max k₁ k₂)
          (let a := upsample k₁ (max k₁ k₂) m₁
           let b := upsample k₂ (max k₁ k₂) m₂
           a ^^^ (a &&& b)) := by
  rw [← levelSet_upsample (le_max_left k₁ k₂) (m := m₁),
    ← levelSet_upsample (le_max_right k₁ k₂) (m := m₂)]
  ext n
  simp only [mem_levelSet, Set.mem_diff, testBit_xor_and_self, Bool.and_eq_true, Bool.not_eq_true,
    Bool.not_eq_true']

/-- **`V` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty). -/
theorem V_diff_mem {X Y : Set ℕ} (hX : V.mem X) (hY : V.mem Y) : X \ Y = ∅ ∨ V.mem (X \ Y) := by
  obtain ⟨k₁, m₁, rfl, -⟩ := hX
  obtain ⟨k₂, m₂, rfl, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (levelSet k₁ m₁ \ levelSet k₂ m₂) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨max k₁ k₂, _, levelSet_diff k₁ m₁ k₂ m₂, h⟩

/-! ### Generic hypotheses for the back-and-forth lemma -/

/-- **Atomlessness** ("no minimal neighbourhoods"), generalizing `U_no_minimal`/`V_no_minimal`:
every non-empty neighbourhood splits into two disjoint, non-empty neighbourhood pieces whose union
recovers it. (Phrased with explicit `Nonempty` clauses, equivalent given `Y ∩ Z = ∅`/`Y ∪ Z = X` to
`U_no_minimal`/`V_no_minimal`'s own `Y ≠ X`/`Z ≠ X` phrasing, but directly what `exists_split'`
needs — an *abstract* `D.mem` need not itself carry nonemptiness the way `U.mem`/`V.mem` do.) -/
def NeighborhoodSystem.NoMinimal {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X : Set α}, D.mem X →
    ∃ Y Z : Set α, D.mem Y ∧ D.mem Z ∧ Y.Nonempty ∧ Z.Nonempty ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X

/-- **Difference-closure**, generalizing `U_diff_mem`/`V_diff_mem`: the set-difference of two
neighbourhoods is again a neighbourhood, or empty. -/
def NeighborhoodSystem.DiffClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → X \ Y = ∅ ∨ D.mem (X \ Y)

theorem U_noMinimal : U.NoMinimal := by
  intro X hX
  obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U_no_minimal hX
  exact ⟨Y, Z, hY, hZ, hY.2.1, hZ.2.1, hYZinter, hYZunion⟩

theorem V_mem_nonempty {X : Set ℕ} (hX : V.mem X) : X.Nonempty := by
  obtain ⟨k, m, -, hne⟩ := hX; exact hne

theorem V_noMinimal : V.NoMinimal := by
  intro X hX
  obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := V_no_minimal hX
  exact ⟨Y, Z, hY, hZ, V_mem_nonempty hY, V_mem_nonempty hZ, hYZinter, hYZunion⟩

theorem U_diffClosed : U.DiffClosed := fun hX hY => U_diff_mem hX hY

theorem V_diffClosed : V.DiffClosed := fun hX hY => V_diff_mem hX hY

/-! ### `U` and `V` are Positive (Exercise 1.19) -/

/-- **`U` is Positive**: since `combineIntervals` presents *any* raw intersection of two presented
lists unconditionally, and `X ∩ Y ⊆ [0,1)` is automatic whenever `X ⊆ [0,1)`, only non-emptiness
can ever obstruct `U.mem (X ∩ Y)`. -/
theorem U_isPositive : U.IsPositive := by
  rintro X Y ⟨⟨L1, rfl⟩, -, hXsub⟩ ⟨⟨L2, rfl⟩, -, -⟩
  refine ⟨fun h => h.2.1, fun hne => ⟨⟨combineIntervals L1 L2, presentedIntervals_inter L1 L2⟩,
    hne, Set.inter_subset_left.trans hXsub⟩⟩

/-- **`V` is Positive**: `levelSet_inter` presents *any* raw intersection unconditionally, so only
non-emptiness can obstruct `V.mem (X ∩ Y)`. -/
theorem V_isPositive : V.IsPositive := by
  rintro X Y ⟨k₁, m₁, rfl, -⟩ ⟨k₂, m₂, rfl, -⟩
  refine ⟨fun ⟨k, m, heq, hne⟩ => hne, fun hne => ⟨max k₁ k₂, _, levelSet_inter k₁ m₁ k₂ m₂, hne⟩⟩

/-! ### Boolean atoms are automatically mem-or-empty

The key structural payoff of Positivity + difference-closure: `Theorem88.lean`'s `genAtom`
(a finite Boolean combination of an enumerated family `Z 0, …, Z (n-1)` and their complements
relative to `M`) is *automatically* `D.mem`-or-`∅`, by a direct induction — no
`Classical.choice`-driven splitting is needed to keep it "in the family". This is what will let the
eventual two-sided back-and-forth alternate which side is refined by plain intersection/difference
(free) against which side is refined by the *other* system's `NoMinimal` property (the one place
genuine choice enters, exactly as in `Theorem88.lean`). -/
theorem genAtom_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {Z : ℕ → Set γ} (hZ : ∀ n, D.mem (Z n)) (δ : ℕ → Bool) :
    ∀ n, genAtom Z D.master δ n = ∅ ∨ D.mem (genAtom Z D.master δ n) := by
  intro n
  induction n with
  | zero => exact Or.inr D.master_mem
  | succ n ih =>
    have hbranch : (if δ n then Z n else D.master \ Z n) = ∅ ∨
        D.mem (if δ n then Z n else D.master \ Z n) := by
      by_cases hδ : δ n = true
      · simp only [hδ, if_true]; exact Or.inr (hZ n)
      · simp only [hδ]; exact hdiff D.master_mem (hZ n)
    show genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n) = ∅ ∨
      D.mem (genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n))
    rcases ih with ihA | ihA
    · exact Or.inl (by rw [ihA, Set.empty_inter])
    rcases hbranch with hb | hb
    · exact Or.inl (by rw [hb, Set.inter_empty])
    rcases Set.eq_empty_or_nonempty (genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n))
      with he | hne
    · exact Or.inl he
    · exact Or.inr ((hpos ihA hb).mpr hne)

/-! ### Generalizing `Theorem88.lean`'s `exists_split`/`SplitSpec`/`splitChoice` to an abstract
atomless target `E`

`Theorem88.lean`'s versions are hardcoded to `E := U`. The proofs below are verbatim transcriptions
with `U`/`U.mem`/`U_no_minimal` replaced by an abstract `E`/`E.mem`/`hEnomin : E.NoMinimal`; nothing
else changes. This is the piece that lets the eventual two-sided construction invoke the *same*
splitting lemma with `E := D₁` (when refining `D₁`'s side against a `D₀`-side target) and `E := D₀`
(symmetrically), rather than only ever `E := U`. -/

/-- **Generalization of `Theorem88.lean`'s `exists_split`** to an abstract atomless `E`. -/
theorem exists_split' {α γ : Type*} {E : NeighborhoodSystem γ} (hEnomin : E.NoMinimal)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    ∃ I J : Set γ, (I = ∅ ∨ E.mem I) ∧ (J = ∅ ∨ E.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBE, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_diff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBE, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
      have hAeq : A ∩ Xn = A := by
        ext x
        simp only [Set.mem_inter_iff]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hxn
        exact Set.eq_empty_iff_forall_notMem.mp h2 x ⟨hx, hxn⟩
      rw [hAeq, hAB]
    · have hAne : A ≠ ∅ := by
        intro hA
        apply h1
        rw [hA]
        exact Set.empty_inter Xn
      have hBne : B ≠ ∅ := fun hB => hAne (hAB.mpr hB)
      have hBE' : E.mem B := hBE.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYne', hZne', hYZinter, hYZunion⟩ := hEnomin hBE'
      have hYne : Y ≠ ∅ := hYne'.ne_empty
      have hZne : Z ≠ ∅ := hZne'.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

/-- **Generalization of `Theorem88.lean`'s `SplitSpec`.** -/
def SplitSpec' {α γ : Type*} (E : NeighborhoodSystem γ)
    (split : Set α → Set γ → Set α → Set γ × Set γ) : Prop :=
  ∀ {A : Set α} {B : Set γ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ E.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ E.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ E.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

open Classical in
/-- **Generalization of `Theorem88.lean`'s `splitChoice`.** -/
noncomputable def splitChoice' {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal)
    (A : Set α) (B : Set γ) (Xn : Set α) : Set γ × Set γ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ E.mem B) then
    ⟨(exists_split' hEnomin h.1 h.2 Xn).choose, (exists_split' hEnomin h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

theorem splitChoice'_isSplitSpec {α γ : Type*} (E : NeighborhoodSystem γ) (hEnomin : E.NoMinimal) :
    SplitSpec' (α := α) E (splitChoice' E hEnomin) := by
  intro A B hAB hBE Xn
  classical
  unfold splitChoice'
  rw [dif_pos ⟨hAB, hBE⟩]
  exact (exists_split' hEnomin hAB hBE Xn).choose_spec.choose_spec

/-! ### One-step Boolean-closure helpers

The two facts that let a mem-or-∅ set stay mem-or-∅ after being intersected/subtracted by a
*genuine* neighbourhood — the local, one-step content of `genAtom_mem_or_empty`'s induction,
extracted for reuse in the two-sided construction (where the "tested" side alternates, so the same
one-step fact is needed twice, once per side, rather than as a single long induction). -/

theorem inter_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A ∩ B = ∅ ∨ D.mem (A ∩ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_inter B)
  · rcases Set.eq_empty_or_nonempty (A ∩ B) with h | h
    · exact Or.inl h
    · exact Or.inr ((hpos hA hB).mpr h)

theorem diff_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hdiff : D.DiffClosed)
    {A B : Set γ} (hA : A = ∅ ∨ D.mem A) (hB : D.mem B) : A \ B = ∅ ∨ D.mem (A \ B) := by
  rcases hA with rfl | hA
  · exact Or.inl (Set.empty_diff B)
  · exact hdiff hA hB

/-! ### The interleaved two-sided atom construction

Fix `D₀ : NeighborhoodSystem α`, `D₁ : NeighborhoodSystem β`, each Positive, difference-closed and
atomless (`NoMinimal`), with enumerations `X : ℕ → Set α`, `Y : ℕ → Set β` covering `D₀.mem`/`D₁.mem`
respectively. `atomPair` tracks a matched pair `(A, B) : Set α × Set β`, refined by *two* sub-steps
per index `n`: an **`X`-step** (test `A` against `X n` directly — free by Boolean-closure — and
correspondingly split `B` via `D₁`'s `NoMinimal`, exactly `Theorem88.lean`'s `exists_split` with
`E := D₁`), followed by a **`Y`-step** (symmetrically: test the *new* `B` against `Y n` directly,
and split the *new* `A` via `D₀`'s `NoMinimal`, `E := D₀`). A sign sequence `δ : ℕ → Bool × Bool`
selects the `+`/`-` branch at each of the two sub-steps. -/

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))

open Classical in
/-- **The interleaved two-sided atom pair**, depth `n`, sign sequence `δ`. See the section
docstring for the two sub-steps making up each `n → n + 1` transition. -/
noncomputable def atomPair (δ : ℕ → Bool × Bool) : ℕ → Set α × Set β
  | 0 => (D₀.master, D₁.master)
  | (n + 1) =>
      let A := (atomPair δ n).1
      let B := (atomPair δ n).2
      let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
      let A1 := if (δ n).1 then A ∩ X n else A \ X n
      let B1 := if (δ n).1 then IJ1.1 else IJ1.2
      let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
      let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
      let A2 := if (δ n).2 then IJ2.1 else IJ2.2
      (A2, B2)

variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne

/-- **The core invariant of the two-sided back-and-forth construction**: at every depth `n` and for
every sign sequence `δ`, the matched pair `atomPair δ n` (a) has matching emptiness
(`= ∅ ↔ = ∅`) and (b)/(c) is mem-or-∅ on each respective side. Proved by a single induction,
alternating the two Boolean-closure/`exists_split'` steps described in the section docstring. -/
theorem atomPair_invariant (δ : ℕ → Bool × Bool) :
    ∀ n, ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 = ∅ ↔
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 = ∅) ∧
      ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 = ∅ ∨
        D₀.mem (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1) ∧
      ((atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 = ∅ ∨
        D₁.mem (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, Or.inr D₀.master_mem, Or.inr D₁.master_mem⟩
    show (D₀.master = ∅ ↔ D₁.master = ∅)
    exact ⟨fun h => absurd h hD₀mne.ne_empty, fun h => absurd h hD₁mne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihAB, ihA, ihB⟩ := ih
    set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
    set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
    have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin ihAB ihB (X n)
    set I1 := (splitChoice' D₁ hD₁nomin A B (X n)).1 with hI1def
    set J1 := (splitChoice' D₁ hD₁nomin A B (X n)).2 with hJ1def
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
    have hspec2 := splitChoice'_isSplitSpec D₀ hD₀nomin hA1B1.symm hA1mem (Y n)
    set I2 := (splitChoice' D₀ hD₀nomin B1 A1 (Y n)).1 with hI2def
    set J2 := (splitChoice' D₀ hD₀nomin B1 A1 (Y n)).2 with hJ2def
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

end AtomPair

end Scott1980.Neighborhood
