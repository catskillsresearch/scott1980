import Scott1980.Neighborhood.Theorem85

/-!
# Lecture VIII — Theorem 8.6 (Scott 1981, PRG-19): the `sub` combinator

**Theorem 8.6.** For any domain `E` define `sub : (E → E) → (E → E)` by the formula

`X sub(f) Z` iff `∃Y ∈ E. X ⊆ Y, f Y ⊆ Z`,

for all `X, Z ∈ E` and all `f : E → E`. Then the range of `sub` consists exactly of the finitary
projections on `E`, and moreover `sub` itself is a finitary projection on `(E → E)`. If `E` is
effectively given, then `sub` is computable.

## What is formalized here

Scott's formula for `sub(f)` is *literally* Proposition 8.2's `retractionOfSubsystem`, applied to
Theorem 8.5's subdomain `D = fixedNbhd f = {Y ∈ E ∣ Y f Y}` (which, recall, is a genuine subsystem
`D ◁ E` for *any* `f`, no hypotheses needed). This module formalizes the per-token map
`sub : ApproximableMap E E → ApproximableMap E E` (`Sub8_6.sub`) and its order-theoretic content at
that level:

* **`sub f ≤ f`** (`sub_le`) — Scott's "`X ⊆ Y, f Y ⊆ Z` always implies `X f Z`", a bare
  monotonicity calculation, valid for *any* `f`.
* **`sub` is idempotent, exactly: `sub (sub f) = sub f`** (`sub_sub`) — sharper than Scott's stated
  inclusion `sub(f) ⊆ sub(sub(f))`: unwinding `fixedNbhd (sub f)` shows it has *the same*
  neighbourhoods as `fixedNbhd f` (`Y ⊆ Y' ⊆ Y` forces `Y = Y'`), so `sub (sub f)` and `sub f` are
  built from literally the same subsystem and hence are equal, not just related by `≤`.
* **`sub` is monotone** (`sub_mono`) — immediate from `fixedNbhd`'s definition.
* **The easy half of "range(sub) = finitary projections":** `sub f = f → IsFinitaryProjection f`
  (`isFinitaryProjection_of_sub_eq_self`) — immediate substitution into
  `Subsystem.isFinitaryProjection_retractionOfSubsystem`, since `sub f = f` says exactly that `f`
  *is* `retractionOfSubsystem (fixedNbhd_subsystem f)`.

**Not formalized (deferred, matching `Theorem85.lean`'s scope note):**

* The converse containment `IsFinitaryProjection f → sub f = f` needs Theorem 8.5's `(i) ⟹ (ii)`
  direction (the compactness-reflection argument flagged there as future work).
* Packaging `sub` as a genuine `ApproximableMap (funSpace E E) (funSpace E E)` (Scott's remark that
  "the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub` is itself
  approximable") and the finitary-projection/computability clauses about *that* map. This requires
  extending `ofMono`/`curry`-style machinery to the step-neighbourhoods of `funSpace E E`, a
  standalone effort comparable in size to `Theorem75.lean`; see `HANDOFF.md`.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}

/-- **Theorem 8.6's combinator `sub(f)` (Scott 1981, PRG-19), per token `f`.** Scott's formula
`X sub(f) Z ↔ ∃Y ∈ E, X⊆Y ∧ f.rel Y Y ∧ Y⊆Z` is literally `retractionOfSubsystem` applied to
`fixedNbhd f = {Y ∈ E ∣ Y f Y}` (Theorem 8.5's subsystem, built for *any* `f`). -/
def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)

@[simp] theorem sub_rel {f : ApproximableMap E E} {X Z : Set α} :
    (sub f).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, (E.mem Y ∧ f.rel Y Y) ∧ X ⊆ Y ∧ Y ⊆ Z :=
  Subsystem.retractionOfSubsystem_rel (fixedNbhd_subsystem f)

/-- `fixedNbhd (sub f) = fixedNbhd f`: `Y (sub f) Y ↔ Y f Y`, since a witness `Y ⊆ Y' ⊆ Y` forces
`Y' = Y`. This is the key computation behind `sub`'s idempotency (`sub_sub`). -/
theorem fixedNbhd_sub (f : ApproximableMap E E) : fixedNbhd (sub f) = fixedNbhd f := by
  apply NeighborhoodSystem.ext
  · intro Y
    constructor
    · intro hmem
      have hr : (sub f).rel Y Y := hmem.2
      obtain ⟨hYE, -, Y', hY', hYY', hY'Y⟩ := sub_rel.mp hr
      obtain ⟨hY'E, hY'f⟩ := hY'
      have hYY'eq : Y' = Y := Set.Subset.antisymm hY'Y hYY'
      exact ⟨hYE, hYY'eq ▸ hY'f⟩
    · intro hmem
      obtain ⟨hYE, hYf⟩ := hmem
      refine ⟨hYE, sub_rel.mpr ⟨hYE, hYE, Y, ⟨hYE, hYf⟩, subset_rfl, subset_rfl⟩⟩
  · rfl

/-- **`sub f ≤ f`, unconditionally (Scott 1981, PRG-19).** "`X ⊆ Y, f Y ⊆ Z` always implies
`X f Z`" — a bare narrow-input/widen-output monotonicity calculation, needing nothing about `f`. -/
theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ

/-- **`sub` is monotone.** `f ≤ g → sub f ≤ sub g`: immediate from `fixedNbhd`'s definition, since
`f.rel Y Y → g.rel Y Y` whenever `f ≤ g`. -/
theorem sub_mono {f g : ApproximableMap E E} (h : f ≤ g) : sub f ≤ sub g := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  exact sub_rel.mpr ⟨hX, hZ, Y, ⟨hYE, h Y Y hYf⟩, hXY, hYZ⟩

/-- **`sub` is idempotent: `sub (sub f) = sub f`** (sharper than Scott's stated `sub(f) ⊆
sub(sub(f))`, Theorem 8.6's projection clause for `sub` itself). Both sides are
`retractionOfSubsystem` of the *same* subsystem `fixedNbhd f` (`fixedNbhd_sub`), so they coincide
as maps, not merely as an inclusion. -/
theorem sub_sub (f : ApproximableMap E E) : sub (sub f) = sub f := by
  unfold sub
  congr 1
  exact fixedNbhd_sub f

/-- **The easy half of Theorem 8.6's range characterization.** If `f` is a fixed point of `sub`,
then `f` is a finitary projection: `sub f = f` says exactly that `f` *is*
`retractionOfSubsystem (fixedNbhd_subsystem f)`, and Definition 8.3's corollary of Proposition 8.2
finishes immediately. (The converse — every finitary projection is a fixed point of `sub` — is
Theorem 8.5's harder direction; see the module docstring.) -/
theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    IsFinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)

end Scott1980.Neighborhood
