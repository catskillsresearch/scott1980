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

/-- **Generalization of `Theorem88.lean`'s `split_fst_subset`**: a splitting operation's first
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_fst_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-- **Generalization of `Theorem88.lean`'s `split_snd_subset`**: a splitting operation's second
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_snd_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-! ### A single generic sub-step, used for both the `X`-sub-step and the `Y`-sub-step

`xyStep split A B Xn b` packages "intersect/subtract `A` by `Xn` directly (per the sign `b`), and
correspondingly split `B` via `split`" as a single ordinary (non-recursive) function. `atomPair`'s
two sub-steps per depth (the `X`-sub-step, splitting `D₁`'s side while directly refining `D₀`'s;
the `Y`-sub-step, splitting `D₀`'s side while directly refining `D₁`'s) are both literally
instances of this one function (`xStep`/`yStep` below) — exposing this lets the disjointness proof
manipulate one sub-step algebraically, rather than re-deriving `atomPair`'s definitional unfolding
by hand each time. -/

def xyStep {α γ : Type*} (split : Set α → Set γ → Set α → Set γ × Set γ)
    (A : Set α) (B : Set γ) (Xn : Set α) (b : Bool) : Set α × Set γ :=
  (if b then A ∩ Xn else A \ Xn, if b then (split A B Xn).1 else (split A B Xn).2)

/-- **Generic "swap-if" disjointness helper**: if `P` and `Q` are disjoint, then choosing `P` for
one Boolean and `Q` for a *different* Boolean always lands in disjoint sets, regardless of which
Boolean is `true`. -/
theorem if_swap_disjoint {γ : Type*} {P Q : Set γ} (hPQ : P ∩ Q = ∅) {b b' : Bool} (hbb' : b ≠ b') :
    (if b then P else Q) ∩ (if b' then P else Q) = ∅ := by
  rcases Bool.eq_false_or_eq_true b with hb | hb <;> rcases Bool.eq_false_or_eq_true b' with hb' | hb' <;>
    simp_all [Set.inter_comm]

theorem inter_diff_self_eq_empty {γ : Type*} (P Q : Set γ) : (P ∩ Q) ∩ (P \ Q) = ∅ := by
  ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false]; tauto

/-- **`xyStep`'s two outputs, at two *different* sign bits, are pairwise disjoint** — the local,
one-step content behind `atomPair`'s eventual pairwise-disjointness invariant. -/
theorem xyStep_disjoint_of_ne {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xyStep split A B Xn b).1 ∩ (xyStep split A B Xn b').1 = ∅ ∧
      (xyStep split A B Xn b).2 ∩ (xyStep split A B Xn b').2 = ∅ :=
  ⟨if_swap_disjoint (inter_diff_self_eq_empty A Xn) hbb',
    if_swap_disjoint (hsplit hAB hBE Xn).2.2.2.2.2 hbb'⟩

/-! ### Padding/restricting `ℕ → Bool × Bool` sign sequences

The two-sided analogues of `Theorem88.lean`'s `extendTrue`/`restrictFin`, built by applying them
componentwise to each half of the pair. Needed for 8.12(c)(vi)(4)'s `XPseq`/`YPseq`. -/

/-- Pad `δ' : Fin n → Bool × Bool` to a total `ℕ → Bool × Bool`, filling positions `≥ n` with
`(true, true)`. -/
def extendTruePair {n : ℕ} (δ' : Fin n → Bool × Bool) : ℕ → Bool × Bool :=
  fun i => (extendTrue (Prod.fst ∘ δ') i, extendTrue (Prod.snd ∘ δ') i)

/-- Restrict `δ : ℕ → Bool × Bool` to `Fin n → Bool × Bool`. -/
def restrictFinPair (δ : ℕ → Bool × Bool) (n : ℕ) : Fin n → Bool × Bool := fun i => δ i.val

theorem extendTruePair_restrictFinPair_agree (δ : ℕ → Bool × Bool) (n i : ℕ) (hi : i < n) :
    extendTruePair (restrictFinPair δ n) i = δ i := by
  have h1 : extendTrue (Prod.fst ∘ restrictFinPair δ n) i = (δ i).1 :=
    extendTrue_restrictFin_agree (Prod.fst ∘ δ) n i hi
  have h2 : extendTrue (Prod.snd ∘ restrictFinPair δ n) i = (δ i).2 :=
    extendTrue_restrictFin_agree (Prod.snd ∘ δ) n i hi
  show (extendTrue (Prod.fst ∘ restrictFinPair δ n) i, extendTrue (Prod.snd ∘ restrictFinPair δ n) i)
      = δ i
  rw [h1, h2]

/-! ### The two named sub-steps of `atomPair`, as instances of `xyStep`

These, and their basic subset/disjointness properties, are stated fully generically (independent
of any particular `D₀`/`D₁`/`X`/`Y`) and placed here, *before* `section AtomPair` below, so that
they do not pick up that section's `include`d hypotheses (`hD₀pos`, `hXmem`, etc.) as spurious
extra arguments — `xStep`/`yStep` only ever need a *single* system's data (`D₁`/`hD₁nomin` for
`xStep`, `D₀`/`hD₀nomin` for `yStep`), never the full two-sided context. -/

/-- **The `X`-sub-step**, as an instance of `xyStep`: split `D₁`'s side while directly refining
`D₀`'s side. -/
noncomputable def xStep {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : Set α × Set β :=
  xyStep (splitChoice' D₁ hD₁nomin) A B Xn b

/-- **The `Y`-sub-step**, symmetric to `xStep`: split `D₀`'s side while directly refining `D₁`'s
side. The `.swap` puts the output back into `(α-side, β-side)` order, matching `atomPair`'s own
`(A2, B2)` convention (`xyStep`'s first component is always the *direct* side, which for the
`Y`-sub-step is the `β`-side). -/
noncomputable def yStep {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : Set α × Set β :=
  (xyStep (splitChoice' D₀ hD₀nomin) B1 A1 Yn b).swap

/-- **`xStep`'s `α`-side output is always a subset of `A`** (unconditional: `A ∩ Xn` and `A \ Xn`
are both `⊆ A`). -/
theorem xStep_fst_subset {α β : Type*} (D₁ : NeighborhoodSystem β) (hD₁nomin : D₁.NoMinimal)
    (A : Set α) (B : Set β) (Xn : Set α) (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).1 ⊆ A := by
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, if_true]; exact Set.inter_subset_left
  · simp only [xStep, xyStep, hb]; exact Set.diff_subset

/-- **`xStep`'s `β`-side output is a subset of `B`**, given the `SplitSpec'` preconditions
(`I ∪ J = B`, so both `I ⊆ B` and `J ⊆ B`). -/
theorem xStep_snd_subset {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    (b : Bool) : (xStep D₁ hD₁nomin A B Xn b).2 ⊆ B := by
  have hspec := splitChoice'_isSplitSpec D₁ hD₁nomin hAB hBmem Xn
  by_cases hb : b = true
  · simp only [xStep, xyStep, hb, if_true]; exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [xStep, xyStep, hb]; exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

/-- **`yStep`'s `α`-side output is a subset of `A1`**, given the `SplitSpec'` preconditions. -/
theorem yStep_fst_subset {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).1 ⊆ A1 := by
  have hspec := splitChoice'_isSplitSpec D₀ hD₀nomin hBA hAmem Yn
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, if_true]
    exact Set.subset_union_left.trans_eq hspec.2.2.2.2.1
  · simp only [yStep, xyStep, Prod.swap, hb]
    exact Set.subset_union_right.trans_eq hspec.2.2.2.2.1

/-- **`yStep`'s `β`-side output is always a subset of `B1`** (unconditional). -/
theorem yStep_snd_subset {α β : Type*} (D₀ : NeighborhoodSystem α) (hD₀nomin : D₀.NoMinimal)
    (A1 : Set α) (B1 : Set β) (Yn : Set β) (b : Bool) : (yStep D₀ hD₀nomin A1 B1 Yn b).2 ⊆ B1 := by
  by_cases hb : b = true
  · simp only [yStep, xyStep, Prod.swap, hb, if_true]; exact Set.inter_subset_left
  · simp only [yStep, xyStep, Prod.swap, hb]; exact Set.diff_subset

/-- **`xStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem xStep_disjoint_of_ne {α β : Type*} {D₁ : NeighborhoodSystem β} (hD₁nomin : D₁.NoMinimal)
    {A : Set α} {B : Set β} (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (Xn : Set α)
    {b b' : Bool} (hbb' : b ≠ b') :
    (xStep D₁ hD₁nomin A B Xn b).1 ∩ (xStep D₁ hD₁nomin A B Xn b').1 = ∅ ∧
      (xStep D₁ hD₁nomin A B Xn b).2 ∩ (xStep D₁ hD₁nomin A B Xn b').2 = ∅ :=
  xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₁ hD₁nomin) hAB hBmem Xn hbb'

/-- **`yStep`'s two outputs, at two different sign bits, are pairwise disjoint.** -/
theorem yStep_disjoint_of_ne {α β : Type*} {D₀ : NeighborhoodSystem α} (hD₀nomin : D₀.NoMinimal)
    {A1 : Set α} {B1 : Set β} (hBA : B1 = ∅ ↔ A1 = ∅) (hAmem : A1 = ∅ ∨ D₀.mem A1) (Yn : Set β)
    {b b' : Bool} (hbb' : b ≠ b') :
    (yStep D₀ hD₀nomin A1 B1 Yn b).1 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').1 = ∅ ∧
      (yStep D₀ hD₀nomin A1 B1 Yn b).2 ∩ (yStep D₀ hD₀nomin A1 B1 Yn b').2 = ∅ := by
  have h := xyStep_disjoint_of_ne (splitChoice'_isSplitSpec D₀ hD₀nomin) hBA hAmem Yn hbb'
  exact ⟨h.2, h.1⟩

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

/-! ### A generic union-closure fact for `IsPositive` + `DiffClosed` systems

Needed by 8.12(c)(vi)(3)'s `YseqE_empty_or_mem`: `Theorem88.lean`'s own `U_union_mem`/
`U_iUnion_mem` (`Definition87.lean`) are proved directly from `U`'s presented-interval structure
(list `++`), which an abstract `E` does not have access to. But `IsPositive` + `DiffClosed` +
`sub_master`, entirely on their own, already force closure under finite union via the De Morgan
identity `X ∪ Y = M \ ((M \ X) ∩ (M \ Y))` (valid whenever `X, Y ⊆ M`) — `M \ X`/`M \ Y` are
mem-or-∅ by `DiffClosed`, their intersection is mem-or-∅ by `IsPositive`, and one more `DiffClosed`
application finishes it. This is genuinely new generic content (`U`/`V`'s own union-closure lemmas
never needed to be derived this way), not a transcription of anything in `Theorem88.lean`. -/

theorem union_eq_master_diff_inter_compl {γ : Type*} (M X Y : Set γ) (hX : X ⊆ M) (hY : Y ⊆ M) :
    X ∪ Y = M \ ((M \ X) ∩ (M \ Y)) := by
  ext x
  have hXx : x ∈ X → x ∈ M := @hX x
  have hYx : x ∈ Y → x ∈ M := @hY x
  simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
  tauto

/-- **Union-closure from `IsPositive` + `DiffClosed` alone**: if `X` and `Y` are each mem-or-∅ in a
Positive, difference-closed `D`, so is `X ∪ Y`. -/
theorem union_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {X Y : Set γ} (hX : X = ∅ ∨ D.mem X) (hY : Y = ∅ ∨ D.mem Y) :
    X ∪ Y = ∅ ∨ D.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · simpa using hY
  · rcases hY with rfl | hY
    · simpa using Or.inr hX
    · set M := D.master with hMdef
      have hXM : X ⊆ M := D.sub_master hX
      have hYM : Y ⊆ M := D.sub_master hY
      rcases hdiff D.master_mem hX with hMX0 | hMXm
      · refine Or.inr ?_
        have hXeqM : X = M := Set.Subset.antisymm hXM (Set.diff_eq_empty.mp hMX0)
        rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hXeqM ▸ Set.subset_union_left)]
        exact D.master_mem
      · rcases hdiff D.master_mem hY with hMY0 | hMYm
        · refine Or.inr ?_
          have hYeqM : Y = M := Set.Subset.antisymm hYM (Set.diff_eq_empty.mp hMY0)
          rw [Set.Subset.antisymm (Set.union_subset hXM hYM) (hYeqM ▸ Set.subset_union_right)]
          exact D.master_mem
        · rw [union_eq_master_diff_inter_compl M X Y hXM hYM]
          rcases Set.eq_empty_or_nonempty ((M \ X) ∩ (M \ Y)) with hcap0 | hcapne
          · rw [hcap0, Set.diff_empty]; exact Or.inr D.master_mem
          · exact hdiff D.master_mem ((hpos hMXm hMYm).mpr hcapne)

/-- **`Fintype`-indexed union-closure from `IsPositive` + `DiffClosed` alone**, generalizing
`Definition87.lean`'s `U_iUnion_mem`/`Exercise812.lean`'s `V_iUnion_mem` to an abstract `D`. Proved
identically (fold `union_mem_or_empty` over `Finset.univ`), just with the generic one-step lemma in
place of `U`/`V`'s hardcoded binary-union facts. -/
theorem iUnion_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {ι : Type*} [Fintype ι] {f : ι → Set γ}
    (hf : ∀ i, f i = ∅ ∨ D.mem (f i)) : (⋃ i, f i) = ∅ ∨ D.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ D.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact union_mem_or_empty hpos hdiff (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall]
  exact hstep Finset.univ

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

/-- **`atomPair`'s recursive step, rephrased as `yStep ∘ xStep`.** Definitionally equal to
`atomPair`'s own `let`-chain (both sides unfold to the identical `(A2, B2)` pair), but stated in
terms of the two named sub-steps so later lemmas can manipulate them algebraically instead of
re-deriving the unfolding by hand. -/
theorem atomPair_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ) :
    atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1) =
      yStep D₀ hD₀nomin
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1
        (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2
        (Y n) (δ n).2 := rfl

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

/-! ### Pairwise disjointness of `atomPair` (Exercise 8.12(c)(v))

Mirrors `Theorem88.lean`'s `atomU_invariant`'s third clause, but proved on **both** sides at once.
Two supporting facts are needed first: `atomPair_congr` (agreeing sign sequences below `n` give the
identical depth-`n` pair — no invariant needed, purely definitional) and `atomPair_fst_subset`/
`atomPair_snd_subset` (each side only shrinks from depth `n` to `n+1` — *does* need the invariant,
since the shrinking is via `split_fst_subset'`/`split_snd_subset'`, which only fire once the
`SplitSpec'` preconditions are known to hold). -/

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
/-- Extending/changing `δ` at or beyond position `n` does not change `atomPair δ n` (mirrors
`Theorem88.lean`'s `atomU_congr`/`genAtom_congr`; needs no invariant, since every step is an
ordinary function of its inputs). -/
theorem atomPair_congr {δ δ' : ℕ → Bool × Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n = atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n =
        atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn : δ n = δ' n := h n (Nat.lt_succ_self n)
    show
      (let A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
       let B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2
       let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
       let A1 := if (δ n).1 then A ∩ X n else A \ X n
       let B1 := if (δ n).1 then IJ1.1 else IJ1.2
       let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
       let B2 := if (δ n).2 then B1 ∩ Y n else B1 \ Y n
       let A2 := if (δ n).2 then IJ2.1 else IJ2.2
       (A2, B2)) =
        (let A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
         let B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2
         let IJ1 := splitChoice' D₁ hD₁nomin A B (X n)
         let A1 := if (δ' n).1 then A ∩ X n else A \ X n
         let B1 := if (δ' n).1 then IJ1.1 else IJ1.2
         let IJ2 := splitChoice' D₀ hD₀nomin B1 A1 (Y n)
         let B2 := if (δ' n).2 then B1 ∩ Y n else B1 \ Y n
         let A2 := if (δ' n).2 then IJ2.1 else IJ2.2
         (A2, B2))
    rw [hprev, hn]

/-- **`xStep`'s output satisfies the preconditions `yStep` needs** (the `SplitSpec'` hypotheses,
transported across the `X`-sub-step): the `β`-side output is empty iff the `α`-side output is, and
the `α`-side output is mem-or-∅ for `D₀`. Proved exactly as the corresponding step inside
`atomPair_invariant`'s induction (Boolean-closure for the *direct* side, `SplitSpec'` for the
*split* side). -/
theorem xStep_spec (δ : ℕ → Bool × Bool) (n : ℕ) :
    ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 = ∅ ↔
      (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 = ∅) ∧
      ((xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 = ∅ ∨
        D₀.mem (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  have hspec1 := splitChoice'_isSplitSpec D₁ hD₁nomin ihAB ihB (X n)
  refine ⟨?_, ?_⟩
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStep, xyStep, hδ1, if_true]; exact hspec1.2.2.1.symm
    · simp only [xStep, xyStep, hδ1]; exact hspec1.2.2.2.1.symm
  · by_cases hδ1 : (δ n).1 = true
    · simp only [xStep, xyStep, hδ1, if_true]; exact inter_mem_or_empty hD₀pos ihA (hXmem n)
    · simp only [xStep, xyStep, hδ1]; exact diff_mem_or_empty hD₀diff ihA (hXmem n)

/-- **`atomPair`'s `α`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPair_fst_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 := by
  rw [atomPair_succ_eq]
  obtain ⟨hspecAB, hspecAmem⟩ := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
    X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStep_fst_subset hD₀nomin hspecAB hspecAmem (Y n) (δ n).2).trans
    (xStep_fst_subset D₁ hD₁nomin _ _ (X n) (δ n).1)

/-- **`atomPair`'s `β`-side only shrinks from depth `n` to `n + 1`.** -/
theorem atomPair_snd_subset (δ : ℕ → Bool × Bool) (n : ℕ) :
    (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 := by
  rw [atomPair_succ_eq]
  obtain ⟨ihAB, -, ihB⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  exact (yStep_snd_subset D₀ hD₀nomin _ _ (Y n) (δ n).2).trans
    (xStep_snd_subset hD₁nomin ihAB ihB (X n) (δ n).1)

/-- **Pairwise disjointness of `atomPair` on both sides at once** (Exercise 8.12(c)(v)): for sign
sequences `δ`, `δ'` disagreeing somewhere below depth `n`, the two matched pairs are disjoint on
*both* the `α`-side and the `β`-side. Proved by induction on `n`, mirroring `Theorem88.lean`'s
`atomU_invariant`'s disjointness clause: the "disagree below `n`" case shrinks via
`atomPair_fst_subset`/`atomPair_snd_subset`; the "agree below `n`, disagree at `n`" case splits on
*which* sub-step first disagrees — the `X`-sub-step (`xStep_disjoint_of_ne` directly, then
`yStep_fst_subset`/`yStep_snd_subset` carry the disjointness through the following `Y`-sub-step),
or the `Y`-sub-step (`atomPair_succ_eq` unifies both `xStep` applications via `hpairEq`/`h1`, then
`yStep_disjoint_of_ne` finishes directly). -/
theorem atomPair_disjoint (δ δ' : ℕ → Bool × Bool) :
    ∀ n, (∃ i < n, δ i ≠ δ' i) →
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ∩
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 = ∅ ∧
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 = ∅ := by
  intro n
  induction n with
  | zero => rintro ⟨i, hi, -⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rintro ⟨i, hi, hine⟩
    by_cases hagree : ∀ j < n, δ j = δ' j
    · -- Disagreement is exactly at position `n`: both depth-`n` pairs coincide.
      have hδn : δ n ≠ δ' n := by
        intro heq
        exact hine (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact hagree i hi'
          · exact heq)
      have hpairEq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n :=
        atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      have hAB' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 =
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 ∧
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 =
            (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 :=
        ⟨(congrArg Prod.fst hpairEq).symm, (congrArg Prod.snd hpairEq).symm⟩
      by_cases h1 : (δ n).1 = (δ' n).1
      · -- Agree on the `X`-sub-step: the `xStep` application is *literally the same* for `δ`,
        -- `δ'`, so disjointness comes purely from the `Y`-sub-step (which must then disagree).
        have h2 : (δ n).2 ≠ (δ' n).2 := fun h2eq => hδn (Prod.ext_iff.mpr ⟨h1, h2eq⟩)
        rw [atomPair_succ_eq, atomPair_succ_eq, hAB'.1, hAB'.2, h1]
        obtain ⟨hspecAB, hspecAmem⟩ := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        rw [h1] at hspecAB hspecAmem
        exact yStep_disjoint_of_ne hD₀nomin hspecAB hspecAmem (Y n) h2
      · -- Disagree already at the `X`-sub-step: the two `xStep` applications are disjoint
        -- outright, and both `yStep` outputs shrink into their respective `xStep` halves.
        obtain ⟨ihAB, ihA, ihB⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        have hxdisj := xStep_disjoint_of_ne hD₁nomin ihAB ihB (X n) h1
        obtain ⟨hspecAB, hspecAmem⟩ := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
        obtain ⟨hspecAB', hspecAmem'⟩ := xStep_spec D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
          hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
        have h1sub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).1 := by
          rw [atomPair_succ_eq]; exact yStep_fst_subset hD₀nomin hspecAB hspecAmem (Y n) (δ n).2
        have h2sub : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) (δ n).1).2 := by
          rw [atomPair_succ_eq]; exact yStep_snd_subset D₀ hD₀nomin _ _ (Y n) (δ n).2
        have h1sub' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).1 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 (X n) (δ' n).1).1 := by
          rw [atomPair_succ_eq]; exact yStep_fst_subset hD₀nomin hspecAB' hspecAmem' (Y n) (δ' n).2
        have h2sub' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).2 ⊆
            (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1
              (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 (X n) (δ' n).1).2 := by
          rw [atomPair_succ_eq]; exact yStep_snd_subset D₀ hD₀nomin _ _ (Y n) (δ' n).2
        rw [hAB'.1, hAB'.2] at h1sub' h2sub'
        exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1sub h1sub') hxdisj.1,
          Set.subset_eq_empty (Set.inter_subset_inter h2sub h2sub') hxdisj.2⟩
    · -- Disagreement is somewhere below `n`: shrink via `atomPair_fst_subset`/`atomPair_snd_subset`.
      push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      obtain ⟨hd1, hd2⟩ := ih ⟨j, hj, hjne⟩
      have h1 : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).1 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 := atomPair_fst_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h1' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).1 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).1 := atomPair_fst_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
      have h2 : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ (n + 1)).2 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 := atomPair_snd_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
      have h2' : (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' (n + 1)).2 ⊆
          (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ' n).2 := atomPair_snd_subset D₀ D₁ hD₀pos hD₀diff
        hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ' n
      exact ⟨Set.subset_eq_empty (Set.inter_subset_inter h1 h1') hd1,
        Set.subset_eq_empty (Set.inter_subset_inter h2 h2') hd2⟩

/-! ### Exercise 8.12(c)(vi)(4): recovering `X n` on `D₁`'s side directly from `atomPair`

**Correcting the original pre-plan.** The plan (`arxiv.md`/`HANDOFF.md`, written before any code)
anticipated a *bridge* identifying `atomPair`'s per-side trajectory with an instance of
`Exercise812cYseq.lean`'s single-family `atomE` (`E := D₁` for the `X`-sub-step, `E := D₀` for the
`Y`-sub-step). **This turns out to be false**, not just difficult: `atomE`'s testing family
`genAtom X Δ δ n` is a *free* Boolean combination (only ever intersected/subtracted directly,
never split), whereas `atomPair`'s `A`-component is *itself* choice-split at every `Y`-sub-step
(via `D₀.NoMinimal`) — so whenever `exists_split'`'s genuine-split case fires (generically), the
actual `A_n` is a *proper* subset of `genAtom X Δ δ₁ n` (`δ₁ k := (δ k).1`), with different
emptiness. Concretely: both `atomPair` components are "`atomE`-like" (choice-driven), so *neither*
is "`genAtom`-like" (free) — unlike `Theorem88.lean`'s one-sided case, where `D`'s side stayed free
by construction. `Exercise812cYseq.lean`'s apparatus therefore is **not** reused here (it remains
valid, reusable general theory for any genuinely one-sided abstract `E`, just not what this specific
bridge needs).

**The actual fix**, found by re-deriving `Yseq`'s "I-formula" argument directly against `atomPair`,
reusing only `atomPair_invariant`/`atomPair_congr`/`atomPair_disjoint` (already `Pass`, (iv)/(v))
and `xStep_snd_subset` (already `Pass`, (v)(2)) — no `atomE` involved: `XPseq n` unions, over all
depth-`n` histories, the `D₁`-piece obtained by the `X`-sub-step's "+" branch (the *half-step*
value, strictly before the following `Y`-sub-step further refines it). This is *simpler* than
`Yseq`'s own proof in one respect: since the branch is a literal argument (`true`) rather than
`δ n`'s own value, there is no need for `Theorem88.lean`'s `Function.update`-based "`δ2`" detour —
agreement below `n` alone suffices. -/

open Classical in
/-- **`XPseq`**: the union, over all depth-`n` histories, of the `D₁`-piece chosen by the
`X`-sub-step's "+" branch against `X n`. Recovers `X n`'s correspondent on `D₁`'s side (the
two-sided, half-step analogue of `Theorem88.lean`'s `Yseq`). -/
noncomputable def XPseq (n : ℕ) : Set β :=
  ⋃ δ' : Fin n → Bool × Bool,
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2

omit hD₀pos hD₀diff hD₁pos hD₁diff hXmem hYmem hD₀mne hD₁mne in
theorem subset_XPseq {n : ℕ} (δ' : Fin n → Bool × Bool) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2 ⊆
      XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n :=
  Set.subset_iUnion
    (fun δ' => (xStep D₁ hD₁nomin
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).1
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 (X n) true).2) δ'

/-- **The "I-formula" for `XPseq`**: the `D₁`-piece chosen by the depth-`n` `X`-sub-step's "+"
branch (for *any* history `δ`) is exactly the intersection of `atomPair δ n`'s `D₁`-side with
`XPseq n`. Mirrors `Theorem88.lean`'s `split_fst_eq_inter_Yseq`, but proved directly against
`atomPair`'s own invariants (no `atomE`/`genAtom` involved — see the section docstring above). -/
theorem xStep_snd_eq_inter_XPseq (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStep D₁ hD₁nomin (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1
        (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 (X n) true).2 =
      (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 ∩ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
  obtain ⟨hAB, -, hBmem⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
    hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne δ n
  set A := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).1 with hAdef
  set B := (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n).2 with hBdef
  set I := (xStep D₁ hD₁nomin A B (X n) true).2 with hIdef
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := xStep_snd_subset hD₁nomin hAB hBmem (X n) true
    have hIsubX : I ⊆ XPseq D₀ D₁ hD₀nomin hD₁nomin X Y n := by
      have hcongr : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y
          (extendTruePair (restrictFinPair δ n)) n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y
          (fun i hi => extendTruePair_restrictFinPair_agree δ n i hi)
      have hmem := subset_XPseq D₀ D₁ hD₀nomin hD₁nomin X Y (restrictFinPair δ n)
      rwa [hcongr] at hmem
    exact Set.subset_inter hIsubB hIsubX
  · rintro z ⟨hzB, hzX⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzX
    by_cases hagree : ∀ i < n, extendTruePair δ' i = δ i
    · have hABeq : atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n =
          atomPair D₀ D₁ hD₀nomin hD₁nomin X Y δ n :=
        atomPair_congr D₀ D₁ hD₀nomin hD₁nomin X Y hagree
      rwa [hABeq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hdisjBB := (atomPair_disjoint D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin
        X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') δ n ⟨j, hj, hjne⟩).2
      obtain ⟨hAB', -, hBmem'⟩ := atomPair_invariant D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff
        hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne (extendTruePair δ') n
      have hzB' : z ∈ (atomPair D₀ D₁ hD₀nomin hD₁nomin X Y (extendTruePair δ') n).2 :=
        xStep_snd_subset hD₁nomin hAB' hBmem' (X n) true hz'
      exact absurd (Set.mem_inter hzB' hzB) (by rw [hdisjBB]; simp)

end AtomPair

end Scott1980.Neighborhood
