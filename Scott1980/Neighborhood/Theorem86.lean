import Scott1980.Neighborhood.Theorem85
import Scott1980.Neighborhood.FunctionSpace
import Scott1980.Neighborhood.Exercise213

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
`sub : ApproximableMap E E → ApproximableMap E E` and its order-theoretic content at that level,
**Theorem 8.6's clause 1 in full**:

* **`sub f ≤ f`** (`sub_le`) — Scott's "`X ⊆ Y, f Y ⊆ Z` always implies `X f Z`", a bare
  monotonicity calculation, valid for *any* `f`.
* **`sub` is idempotent, exactly: `sub (sub f) = sub f`** (`sub_sub`) — sharper than Scott's stated
  inclusion `sub(f) ⊆ sub(sub(f))`: unwinding `fixedNbhd (sub f)` shows it has *the same*
  neighbourhoods as `fixedNbhd f` (`Y ⊆ Y' ⊆ Y` forces `Y = Y'`), so `sub (sub f)` and `sub f` are
  built from literally the same subsystem and hence are equal, not just related by `≤`.
* **`sub` is monotone** (`sub_mono`) — immediate from `fixedNbhd`'s definition.
* **`range(sub) = finitary projections`, both directions** (`sub_eq_self_iff_isFinitaryProjection`):
  the easy half `sub f = f → IsFinitaryProjection f` (`isFinitaryProjection_of_sub_eq_self`) is
  immediate substitution into `Subsystem.isFinitaryProjection_retractionOfSubsystem`; the converse
  `IsFinitaryProjection f → sub f = f` (`sub_eq_self_of_isFinitaryProjection`) is now unblocked by
  Theorem 8.5's hard direction (`formula_of_isFinitaryProjection`): `sub_le` gives `⊇` for free, and
  `⊆` unwinds `X f Z` via `rel_iff_mem_principal` into `Z ∈ f(↑X)`, then rewrites via Theorem 8.5's
  formula into exactly `sub_rel`'s defining shape.
* **`sub f` is *always* a finitary projection**, for any `f` (`isFinitaryProjection_sub`) —
  `sub (sub f) = sub f` plus the above.

**Theorem 8.6's clause 2, half done (in `namespace Sub8_6`):** `sub` packaged as a genuine
`ApproximableMap (funSpace E E) (funSpace E E)` (`subApprox`), realizing Scott's remark that
"the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub` is itself
approximable", and shown to be a **projection** on `(E → E)` (`isProjection_subApprox`):
`subApprox` is built via Exercise 2.13's `ofContinuous`, using a new general domain-theory bridge
`continuous_of_monotone_iSupDirected` (`Exercise213.lean`: monotone + directed-sup-preserving ⟹
topologically continuous, proved directly from algebraicity) applied to `subFilter`, `sub`
transported along `funSpaceEquiv`. `subFilter`'s directed-sup-preservation
(`subFilter_iSupDirected`) needs no consistency argument at all: directed unions of *filters*
correspond, under `toApproxMap`, to the raw union of the underlying maps' *relations*
(`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), and `sub`'s formula is a
*positive* existential in `f`'s relation, hence commutes with such unions by pure logic
(`sub_toApproxMap_iSupDirected`). `IsRetraction subApprox`/`subApprox ≤ idMap` then drop out of
`sub_sub`/`sub_le` respectively.

**Not formalized (deferred):**

* **`IsFinitary subApprox`** — the remaining half of clause 2 (that `Fix(subApprox)`, the finitary
  projections on `E`, is itself isomorphic to a domain). Every other `IsFinitary` witness in this
  file was built by exhibiting the retraction as `retractionOfSubsystem` of an *explicit* subsystem,
  but that route is circular here (it would need Theorem 8.5's hard direction applied to
  `subApprox` itself). The natural honest witness needs a fresh domain of "subsystems of `E`",
  which looks to require the not-yet-formalized universal-domain machinery (Def 8.7 onward); see
  `HANDOFF.md`.
* **Clause 3 (computability)** — needs clause 2 complete plus `E` effectively given (Def 7.1
  machinery); out of reach until the above lands.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

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

/-- **The hard half of Theorem 8.6's range characterization, now unblocked by Theorem 8.5.** Every
finitary projection is a fixed point of `sub`: `⊇` is `sub_le`; `⊆` unwinds `X f Z` via
`rel_iff_mem_principal` into `Z ∈ f(↑X)`, and Theorem 8.5's formula
(`formula_of_isFinitaryProjection`) rewrites this as exactly `sub_rel`'s defining formula. -/
theorem sub_eq_self_of_isFinitaryProjection {f : ApproximableMap E E}
    (h : IsFinitaryProjection f) : sub f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · exact sub_le f X Z
  · intro hXZ
    have hX : E.mem X := f.rel_dom hXZ
    have hZ : E.mem Z := f.rel_cod hXZ
    have hmem : (f.toElementMap (E.principal hX)).mem Z := (f.rel_iff_mem_principal hX).mp hXZ
    obtain ⟨-, W, hW, hWZ, hWf⟩ := (formula_of_isFinitaryProjection h (E.principal hX)).mp hmem
    obtain ⟨hWE, hXW⟩ := (E.mem_principal hX).mp hW
    exact sub_rel.mpr ⟨hX, hZ, W, ⟨hWE, hWf⟩, hXW, hWZ⟩

/-- **Theorem 8.6's range characterization, in full.** `sub f = f ↔ f` is a finitary projection. -/
theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ IsFinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩

/-- **`sub` is itself a finitary projection on `E → E`'s range** (Theorem 8.6's remark that `sub`
restricted to its own range is the identity, i.e. `sub` "is" a projection onto the finitary
projections): applying `sub` twice is the same as once (`sub_sub`), and every `sub f` is already a
fixed point of `sub` (feed `isFinitaryProjection_of_sub_eq_self (sub_sub f)` back through
`sub_eq_self_iff_isFinitaryProjection`) — i.e. `sub f` is *always* a finitary projection, for any
`f`, needing no hypothesis on `f` at all. -/
theorem isFinitaryProjection_sub (f : ApproximableMap E E) : IsFinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)

/-! ## Theorem 8.6, clause 2 (partial): `sub` is itself approximable, and a projection, on
`(E → E)`

Scott's remark: "the correspondence `f ↦ sub(f)` preserves directed unions of `f`'s, thus `sub`
is itself approximable". We realize this via Exercise 2.13 (`ofContinuous`): transported along
`funSpaceEquiv` to `subFilter : (funSpace E E).Element → (funSpace E E).Element`, `sub` is monotone
(`subFilter_mono`, from `sub_mono`) and preserves directed unions (`subFilter_iSupDirected`) — the
latter because `sub`'s defining formula (`sub_rel`) is a *positive* existential in `f`'s relation,
so it commutes with the raw union of relations that `toApproxMap` assigns to a directed union of
filters (`toApproxMap_rel_iSupDirected`, immediate from `mem_iSupDirected`), with no extra
consistency argument needed. `continuous_of_monotone_iSupDirected` then upgrades this to genuine
topological continuity, giving `subApprox := ofContinuous subFilter hc`.

**Not yet formalized:** `IsFinitary subApprox` (that `Fix(subApprox)` — the finitary projections on
`E` — is itself isomorphic to a domain) and the computability clause. Every other `IsFinitary`
witness in this file was built by exhibiting the retraction as `retractionOfSubsystem` of an
*explicit* subsystem, but that route is circular here (it would need Theorem 8.5's hard direction
applied to `subApprox` itself). The natural honest witness needs a fresh domain of "subsystems of
`E`", which looks to require the not-yet-formalized universal-domain machinery (Def 8.7 onward);
see `HANDOFF.md`. -/

namespace Sub8_6

theorem toFilter_toApproxMap (φ : (funSpace E E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv E E).left_inv φ

theorem toApproxMap_toFilter (f : ApproximableMap E E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv E E).right_inv f

theorem toApproxMap_injective {φ ψ : (funSpace E E).Element} (h : toApproxMap φ = toApproxMap ψ) :
    φ = ψ := by
  rw [← toFilter_toApproxMap φ, ← toFilter_toApproxMap ψ, h]

theorem toApproxMap_monotone {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) :
    toApproxMap φ ≤ toApproxMap ψ := by
  have := (funSpaceEquiv E E).monotone h
  simpa using this

/-- **`sub`, transported to the function space's own `Element` type via `funSpaceEquiv`.** -/
def subFilter (φ : (funSpace E E).Element) : (funSpace E E).Element :=
  toFilter (sub (toApproxMap φ))

theorem toApproxMap_subFilter (φ : (funSpace E E).Element) :
    toApproxMap (subFilter φ) = sub (toApproxMap φ) :=
  toApproxMap_toFilter _

theorem subFilter_mono {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) : subFilter φ ≤ subFilter ψ :=
  toFilter_le_iff.mpr (sub_mono (toApproxMap_monotone h))

/-- Directed unions of filters correspond, under `toApproxMap`, to the raw (pointwise) union of the
underlying maps' relations — immediate from `mem_iSupDirected` unfolded through `toApproxMap_rel`.
No consistency/directedness argument is needed for this direction. -/
theorem toApproxMap_rel_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (toApproxMap (iSupDirected φ hdir)).rel X Z ↔ ∃ i, (toApproxMap (φ i)).rel X Z := by
  simp only [toApproxMap_rel, mem_iSupDirected]

/-- **`sub` commutes with directed unions of relations.** `sub`'s formula (`sub_rel`) is a positive
existential in `f`'s relation (`∃Y, ... ∧ f.rel Y Y ∧ ...`), so it commutes with an arbitrary union
of relations by pure logic (swapping the order of two existentials) — no directedness needed here
either, only for `iSupDirected` to be well-formed in the first place. -/
theorem sub_toApproxMap_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (sub (toApproxMap (iSupDirected φ hdir))).rel X Z ↔
      ∃ i, (sub (toApproxMap (φ i))).rel X Z := by
  simp only [sub_rel, toApproxMap_rel_iSupDirected]
  constructor
  · rintro ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩
    exact ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
  · rintro ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
    exact ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩

/-- **`subFilter` preserves directed unions.** Assembled from `sub_toApproxMap_iSupDirected` and
`toApproxMap_rel_iSupDirected` via `toApproxMap`'s injectivity. -/
theorem subFilter_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k)
    (hdir' : ∀ i j, ∃ k, subFilter (φ i) ≤ subFilter (φ k) ∧ subFilter (φ j) ≤ subFilter (φ k)) :
    subFilter (iSupDirected φ hdir) = iSupDirected (fun i => subFilter (φ i)) hdir' := by
  apply toApproxMap_injective
  rw [toApproxMap_subFilter]
  apply ApproximableMap.ext
  intro X Z
  rw [sub_toApproxMap_iSupDirected, toApproxMap_rel_iSupDirected]
  simp only [toApproxMap_subFilter]

theorem subFilter_monotone : Monotone (subFilter (E := E)) := fun _ _ h => subFilter_mono h

/-- **`subFilter` is (topologically) continuous**, via the domain-theoretic bridge
`continuous_of_monotone_iSupDirected` (monotone + preserves directed unions). -/
theorem continuous_subFilter : Continuous (subFilter (E := E)) :=
  continuous_of_monotone_iSupDirected subFilter_monotone subFilter_iSupDirected

/-- **`sub`, packaged as a genuine approximable map on the function space `(E → E)`** (Scott's
remark that `f ↦ sub(f)` is itself approximable), via Exercise 2.13's `ofContinuous`. -/
def subApprox : ApproximableMap (funSpace E E) (funSpace E E) :=
  ofContinuous subFilter continuous_subFilter

theorem toElementMap_subApprox (φ : (funSpace E E).Element) :
    subApprox.toElementMap φ = subFilter φ :=
  toElementMap_ofContinuous subFilter continuous_subFilter φ

theorem subFilter_subFilter (φ : (funSpace E E).Element) :
    subFilter (subFilter φ) = subFilter φ := by
  unfold subFilter
  rw [toApproxMap_toFilter, sub_sub]

theorem toElementMap_subApprox_comp (φ : (funSpace E E).Element) :
    (subApprox.comp subApprox).toElementMap φ = subApprox.toElementMap φ := by
  rw [toElementMap_comp]
  simp only [toElementMap_subApprox]
  exact subFilter_subFilter φ

/-- **`subApprox` is a retraction**: `subApprox ∘ subApprox = subApprox`, from `subFilter`'s own
idempotency (`subFilter_subFilter`), itself inherited from `sub_sub`. Proved via `le_antisymm` on
`le_iff_toElementMap_le` (choice-free), rather than the classical `ext_of_toElementMap`. -/
theorem isRetraction_subApprox : IsRetraction (subApprox (E := E)) :=
  le_antisymm (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).le)
    (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).ge)

/-- **`subApprox` is a projection**: `subApprox ≤ idMap`, from `subFilter φ ≤ φ`, itself
inherited from `sub_le`. -/
theorem subApprox_le_idMap : subApprox ≤ idMap (funSpace E E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_subApprox, toElementMap_idMap]
  calc subFilter φ = toFilter (sub (toApproxMap φ)) := rfl
    _ ≤ toFilter (toApproxMap φ) := toFilter_le_iff.mpr (sub_le _)
    _ = φ := toFilter_toApproxMap φ

/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause — the remaining `IsFinitary` half needs the not-yet-formalized universal-domain
machinery, see the section docstring above). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

end Sub8_6

end Scott1980.Neighborhood
