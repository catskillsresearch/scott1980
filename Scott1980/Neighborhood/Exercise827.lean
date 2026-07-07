import Scott1980.Neighborhood.Exercise826
import Scott1980.Neighborhood.Exercise821

/-!
# Exercise 8.27 (Scott 1981, PRG-19) — Donahue's polymorphic/infinite products over `𝒰`

> **Exercise 8.27.** (Suggested by James Donahue.) Finite cartesian products of domains are formed
> by the `D₀ × D₁`-construct we have used so often. The problem is to define — computably — some
> *infinite* cartesian products. In particular, as applied to the universal domain `𝒰`, the
> combinator `sub` is to be regarded as a finitary projection of `𝒰` whose fixed points are
> exactly *all* the finitary projections. A map `d = sub∘d∘sub` can be regarded as a *polymorphic
> type* (because, whenever `t` is a finitary projection (`=` type), then so is `d(t)`). The
> *continuous product* of *all* these types would be the domain of all approximable functions `x`
> such that `x(t) = d(t)(x(t))` for all types `t`. (Why does this equation mean that `x` is in the
> product?) Define `Π` as a combinator by `Π = λd λx λt. sub(d(sub(t)))(x(sub(t)))`. Show that for
> `d` a polymorphic type, `Π(d)` is a type. (Hint: it is easy to check that `Π(d)` is a projection;
> the problem is to show it is finitary.)

This is the **last exercise in the entire book**.

## What this file formalizes

**Step 1 — `sub` regarded as a combinator on `𝒰` itself.** Theorem 8.6's `sub : (E→E)→(E→E)`
(`Theorem86.lean`) is a per-map operation; Theorem 8.6(b) packages it as a genuine approximable
self-map `subApprox : (𝒰→𝒰) → (𝒰→𝒰)`. To get "`sub` regarded as a finitary projection *of* `𝒰`"
(the exercise's own phrasing), we conjugate `subApprox` through the fixed pair `i_→ : (𝒰→𝒰)→𝒰`,
`j_→ : 𝒰→(𝒰→𝒰)` (Definition 8.9) exactly as `Definition 8.9` itself builds `a→b` from `λf.b∘f∘a` —
`subU := i_→ ∘ subApprox ∘ j_→ : 𝒰 → 𝒰`. We show `subU` is a genuine finitary projection
(`isFinitaryProjection_subU`) whose fixed points are exactly the finitary projections of `𝒰`
(`subUFixIso`, composed with Theorem 8.6(a)'s own `{f ∣ sub f=f} = ` finitary projections
characterization) — a direct formalization of the exercise's opening sentence.

**Step 2 — polymorphic types.** `IsPolymorphicType d := subU∘d∘subU = d`, Scott's `d = sub∘d∘sub`.
The exercise's own justification ("whenever `t` is a finitary projection, then so is `d(t)`") is
`polymorphicType_apply_mem_fix`: for `d` polymorphic and *any* `z` (not just a "type" `t`),
`d(z) ∈ Fix(subU)`.

**Step 3 — the `Π` combinator.** Built by direct transcription of Scott's formula
`Π(d)(x)(t) = sub(d(sub(t)))(x(sub(t)))` via `curry`/`evalMap`/`paired` (mirroring
`Exercise825FixedPoint.lean`'s `RMap` recipe), giving `piD d : (𝒰→𝒰) → (𝒰→𝒰)`, then conjugated
through `i_→, j_→` exactly as in Step 1 to land `piU d : 𝒰 → 𝒰` — "`Π(d)`, regarded as living in
`𝒰`," matching that "type" means a self-map *of `𝒰`* (not of `𝒰→𝒰`).

**Step 4 — "it is easy to check that `Π(d)` is a projection" (Scott's own hint).** Proved here
**unconditionally for every `d : 𝒰 → 𝒰`** (not just polymorphic `d`!) — a genuinely easier and
stronger fact than what Scott's theorem statement asks for, made possible because `Π`'s own
formula *already* re-projects through `sub` at every occurrence of the bound type variable `t`
(`sub(d(sub(t)))`, not bare `d(sub(t))`): this makes the "type" fed to the application step
*automatically* a genuine finitary projection regardless of whether `d` itself is polymorphic
(`isFinitaryProjection_decode_subU`), which is exactly what both halves of the projection proof
need.

**Step 5 (Exercise 8.27(b)(0)) — reduce "`piU d` is finitary" to "`piD d` is finitary."**
`piUFixIso : Fix(piU d) ≃o Fix(piD d)`, built by literally copying Step 1's `subUFixIso` recipe
(`piU d = i_→∘(piD d)∘j_→` has the same shape as `subU = i_→∘subApprox∘j_→`). Packaged as
`isFinitary_piU_of_isFinitary_piD`, so the remaining work (Exercise 8.27(b)(1)–(b)(4), **not**
attempted here) is exactly to prove `IsFinitary (piD d)` for `d` polymorphic.

**"The problem is to show it is finitary" (Scott's own hint) — the core content, deliberately NOT
attempted.** See the discussion at the bottom of this file for why, and `HANDOFF.md`'s 2026-07-07
checkpoint for the planned proof route (Exercise 8.27(b)(1)–(b)(5), pivoting on Theorem 8.5's
step-closure formula rather than an ad hoc dependent-product construction).

Axiom audit: everything here mentions `𝒰`, hence inherits `𝒰`'s own `Classical.choice` footprint
(`⊆ {propext, Classical.choice, Quot.sound}`, not new).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

/-! ## Step 1: `subU`, `sub` regarded as a combinator on `𝒰` itself -/

/-- **`sub`, regarded as a finitary projection of `𝒰` itself** (the exercise's opening sentence):
conjugate Theorem 8.6(b)'s `subApprox : (𝒰→𝒰)→(𝒰→𝒰)` through the fixed pair `i_→, j_→`
(Definition 8.9), exactly as `a→b` is built from `λf.b∘f∘a` in `Definition89.lean`. -/
noncomputable def subU : ApproximableMap U U :=
  iArrow.comp (Sub8_6.subApprox.comp jArrow)

/-! ### A reusable gadget: conjugating a projection of `(𝒰→𝒰)` through `i_→, j_→` gives a
projection of `𝒰`. Used for both `subU` (from `subApprox`) and, later, `piU d` (from `piD d`). -/

/-- **Conjugating a retraction of `(𝒰→𝒰)` through `i_→, j_→` gives a retraction of `𝒰`.** Pure
associativity plus `j_→∘i_→ = I` (`jArrow_comp_iArrow`) and `H∘H=H`. -/
theorem isRetraction_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsRetraction H) : IsRetraction (iArrow.comp (H.comp jArrow)) := by
  show (iArrow.comp (H.comp jArrow)).comp (iArrow.comp (H.comp jArrow)) =
    iArrow.comp (H.comp jArrow)
  rw [comp_assoc iArrow (H.comp jArrow) (iArrow.comp (H.comp jArrow)),
    comp_assoc H jArrow (iArrow.comp (H.comp jArrow)),
    ← comp_assoc jArrow iArrow (H.comp jArrow), jArrow_comp_iArrow, idMap_comp,
    ← comp_assoc H H jArrow, hH]

/-- **Conjugating a `≤ I`-map of `(𝒰→𝒰)` through `i_→, j_→` gives a `≤ I`-map of `𝒰`.** Chains
`comp_mono_gen` with `i_→∘j_→ ≤ I` (`iArrow_comp_jArrow_le`, Definition 8.9). -/
theorem le_idMap_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : H ≤ idMap (funSpace U U)) : iArrow.comp (H.comp jArrow) ≤ idMap U :=
  calc iArrow.comp (H.comp jArrow)
      ≤ iArrow.comp ((idMap (funSpace U U)).comp jArrow) :=
        comp_mono_gen le_rfl (comp_mono_gen hH le_rfl)
    _ = iArrow.comp jArrow := by rw [idMap_comp]
    _ ≤ idMap U := iArrow_comp_jArrow_le

/-- **Conjugating a projection of `(𝒰→𝒰)` through `i_→, j_→` gives a projection of `𝒰`.** -/
theorem isProjection_conjArrow {H : ApproximableMap (funSpace U U) (funSpace U U)}
    (hH : IsProjection H) : IsProjection (iArrow.comp (H.comp jArrow)) :=
  ⟨isRetraction_conjArrow hH.1, le_idMap_conjArrow hH.2⟩

/-- **`subU` is a projection.** -/
theorem isProjection_subU : IsProjection subU :=
  isProjection_conjArrow Sub8_6.isProjection_subApprox

/-- `subU`'s defining formula unfolded at the element level. -/
theorem toElementMap_subU (w : U.Element) :
    subU.toElementMap w = iArrow.toElementMap (Sub8_6.subApprox.toElementMap
      (jArrow.toElementMap w)) := by
  unfold subU
  rw [toElementMap_comp, toElementMap_comp]

theorem jArrow_comp_iArrow_apply (v : (funSpace U U).Element) :
    jArrow.toElementMap (iArrow.toElementMap v) = v := by
  rw [show jArrow.toElementMap (iArrow.toElementMap v) = (jArrow.comp iArrow).toElementMap v from
    (toElementMap_comp jArrow iArrow v).symm, jArrow_comp_iArrow, toElementMap_idMap]

/-- Unfolds `subU.toElementMap w = w` (via `jArrow_comp_iArrow`) into the statement that
`j_→(w)` is already a fixed point of `subApprox`. Used for both `subUFixIso.toFun`'s well-typing
and its `left_inv`. -/
theorem subApprox_fix_of_subU_fix {w : U.Element} (hw : subU.toElementMap w = w) :
    Sub8_6.subApprox.toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_subU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

theorem subU_fix_of_subApprox_fix {φ : (funSpace U U).Element}
    (hφ : Sub8_6.subApprox.toElementMap φ = φ) :
    subU.toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_subU, jArrow_comp_iArrow_apply, hφ]

/-- **`Fix(subU) ≃o Fix(subApprox)`.** Forward: `w ↦ j_→(w)`; backward: `φ ↦ i_→(φ)`. Needs only
`j_→∘i_→ = I` (no inequality on `i_→∘j_→`). -/
noncomputable def subUFixIso :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // Sub8_6.subApprox.toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, subApprox_fix_of_subU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, subU_fix_of_subApprox_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_subU w.1
    rw [w.2] at hw
    rw [subApprox_fix_of_subU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap_subU w.1
        rw [w.2, subApprox_fix_of_subU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_subU w'.1
        rw [w'.2, subApprox_fix_of_subU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle

/-- **`subU` is finitary.** Composes `subUFixIso` with Theorem 8.6(b)(ii)'s `isFinitary_subApprox`. -/
theorem isFinitary_subU : IsFinitary subU := by
  obtain ⟨β, F, ⟨iso⟩⟩ := Sub8_6.isFinitary_subApprox (E := U)
  exact ⟨β, F, ⟨subUFixIso.trans iso⟩⟩

/-- **`sub`, regarded as a combinator on `𝒰` itself, is a finitary projection** (Exercise 8.27's
opening sentence, in full). -/
theorem isFinitaryProjection_subU : IsFinitaryProjection subU :=
  ⟨isProjection_subU, isFinitary_subU⟩

/-- **`subU`'s fixed points are exactly the finitary projections of `𝒰`** (Exercise 8.27's
opening sentence, precisely): composing `subUFixIso` with Theorem 8.6(b)(ii)'s `subApproxFixIso`
identifies `Fix(subU)` with `{f : 𝒰→𝒰 ∣ sub f = f}`, which by Theorem 8.6(a)'s
`sub_eq_self_iff_isFinitaryProjection` is exactly `{f ∣ IsFinitaryProjection f}`. -/
noncomputable def subUFixIsoSubFixed :
    {w : U.Element // subU.toElementMap w = w} ≃o
      {f : ApproximableMap U U // sub f = f} :=
  subUFixIso.trans Sub8_6.subApproxFixIso

/-! ## Step 2: polymorphic types -/

/-- **A polymorphic type** (Scott 1981, PRG-19, Exercise 8.27): `d = sub∘d∘sub`, `sub` here being
`subU` (Step 1's "`sub` regarded as a combinator on `𝒰`"). -/
def IsPolymorphicType (d : ApproximableMap U U) : Prop :=
  subU.comp (d.comp subU) = d

/-- If `a` is idempotent and `f = a∘g∘a` for *some* `g`, then `a(f(z)) = f(z)` for *every* `z` —
i.e. any map "sandwiched" between two copies of an idempotent `a` always lands in `Fix(a)`,
regardless of what `g` is. (General form of the pattern behind Exercise 8.26's
`translateApp_hasType`, but derived automatically rather than assumed as a hypothesis.) -/
theorem toElementMap_mem_fix_of_isRetraction_sandwich {a g : ApproximableMap U U}
    (ha : IsRetraction a) (z : U.Element) :
    a.toElementMap ((a.comp (g.comp a)).toElementMap z) = (a.comp (g.comp a)).toElementMap z := by
  rw [toElementMap_comp, ← toElementMap_comp a a, ha]

/-- **The exercise's own justification, formalized**: "whenever `t` is a finitary projection, then
so is `d(t)`" — in fact, for `d` a polymorphic type, `d(z) ∈ Fix(subU)` for *every* `z`, not just
for `z` a "type". -/
theorem polymorphicType_apply_mem_fix {d : ApproximableMap U U} (hd : IsPolymorphicType d)
    (z : U.Element) : subU.toElementMap (d.toElementMap z) = d.toElementMap z := by
  have h := toElementMap_mem_fix_of_isRetraction_sandwich isProjection_subU.1 (g := d) z
  rwa [hd] at h

/-! ## Step 4 (prerequisite): decoding `Fix(subU)` always yields a genuine finitary projection

The key fact behind "it is easy to check that `Π(d)` is a projection" (Scott's own hint): because
`subU` is idempotent, `subU(z) ∈ Fix(subU)` for *any* `z` — and `Fix(subU)` decodes, via `j_→`, to
exactly the finitary projections of `𝒰` (Step 1). Chaining these: `j_→(subU(z))`, viewed as a map
of `𝒰`, is *always* a genuine finitary projection, for *any* `z` at all, with no hypothesis on `z`
or on how it arose. This is exactly what makes `Π`'s formula `sub(d(sub(t)))(-)` well-behaved
regardless of whether `d` itself is a polymorphic type. -/

/-- **Any `j_→`-decoded fixed point of `subU` is a finitary projection of `𝒰`.** -/
theorem isFinitaryProjection_toApproxMap_jArrow_of_fix {w : U.Element}
    (hw : subU.toElementMap w = w) :
    IsFinitaryProjection (toApproxMap (jArrow.toElementMap w)) := by
  apply isFinitaryProjection_of_sub_eq_self
  have hfix := subApprox_fix_of_subU_fix hw
  have hstep := congrArg toApproxMap hfix
  rwa [Sub8_6.toElementMap_subApprox, Sub8_6.toApproxMap_subFilter] at hstep

/-- **The key lemma: `j_→(subU(z))` is always a finitary projection of `𝒰`, for any `z`.** -/
theorem isFinitaryProjection_decode_subU (z : U.Element) :
    IsFinitaryProjection (toApproxMap (jArrow.toElementMap (subU.toElementMap z))) :=
  isFinitaryProjection_toApproxMap_jArrow_of_fix
    (toElementMap_idem_of_isRetraction isProjection_subU.1 z)

/-! ## Step 3: the `Π` combinator

Scott's formula: `Π(d)(x)(t) = sub(d(sub(t)))(x(sub(t)))`. Built exactly as
`Exercise825FixedPoint.lean`'s `RMap` — a raw composite of `evalMap`/`proj`/`paired`, uncurried,
then curried. -/

/-- **`Π(d)(x)(t)`, uncurried**: an `ApproximableMap ((𝒰→𝒰) × 𝒰) 𝒰`, jointly continuous in
`(x, t)` for `d` fixed. -/
noncomputable def piDUncurried (d : ApproximableMap U U) : ApproximableMap (prod (funSpace U U) U) U :=
  (evalMap U U).comp
    (paired
      (jArrow.comp (subU.comp (d.comp (subU.comp (proj₁ (funSpace U U) U)))))
      ((evalMap U U).comp
        (paired (proj₀ (funSpace U U) U) (subU.comp (proj₁ (funSpace U U) U)))))

theorem toElementMap_piDUncurried (d : ApproximableMap U U) (φ : (funSpace U U).Element)
    (t : U.Element) :
    (piDUncurried d).toElementMap (pair φ t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t)) := by
  simp only [piDUncurried, toElementMap_comp, toElementMap_paired, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

/-- **`Π(d)`, as a self-map of `(𝒰→𝒰)`** (currying `piDUncurried d` in `x`, leaving `t` bound). -/
noncomputable def piD (d : ApproximableMap U U) : ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (piDUncurried d)

/-- **`Π(d)(x)`, for `x` a plain map `𝒰 → 𝒰`** (not yet an element of the function space) — the
formula's "closed form" as a composite `ApproximableMap`, matching Scott's
`λt. sub(d(sub(t)))(x(sub(t)))` literally. -/
noncomputable def piDApply (d f : ApproximableMap U U) : ApproximableMap U U :=
  (evalMap U U).comp (paired (jArrow.comp (subU.comp (d.comp subU))) (f.comp subU))

theorem toElementMap_piDApply (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  simp only [piDApply, toElementMap_comp, toElementMap_paired, evalMap_apply]

/-- **`piD d`, transported through `funSpaceEquiv`, is exactly `piDApply d`.** Mirrors
`toApproxMap_toElementMap_lamComb`/`toApproxMap_toElementMap_expMap`. -/
theorem toApproxMap_toElementMap_piD (d : ApproximableMap U U) (φ : (funSpace U U).Element) :
    toApproxMap ((piD d).toElementMap φ) = piDApply d (toApproxMap φ) := by
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [piD, toElementMap_curry_apply, toElementMap_piDUncurried, toElementMap_piDApply]

/-- **`Π(d)`, regarded as a combinator living in `𝒰` itself** — conjugating `piD d` through
`i_→, j_→` (Definition 8.9), exactly as `subU` was built from `subApprox` in Step 1. This is what
Scott's "type" means: a self-map *of `𝒰`*, not of `(𝒰→𝒰)`. -/
noncomputable def piU (d : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((piD d).comp jArrow)

/-! ## Step 4: "it is easy to check that `Π(d)` is a projection" — Scott's own hint

Proved **unconditionally**, for *every* `d : 𝒰 → 𝒰`, not only for `d` a polymorphic type: the
outer `sub(-)` wrapper already appearing in Scott's own formula guarantees, via
`isFinitaryProjection_decode_subU`, that the "type at `t`" fed to the application step is always a
genuine finitary projection — and that alone is exactly what both halves of the projection
property need. -/

/-- Evaluating `piDApply d f` at an already-`subU`-projected point simplifies (via `subU`'s
idempotency) exactly to `toElementMap_piDApply`'s formula with `t` replaced by `subU.toElementMap
t` throughout. The key computational step behind `isRetraction_piD`. -/
theorem piDApply_toElementMap_eq (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap (subU.toElementMap t) =
      (toApproxMap (jArrow.toElementMap (subU.toElementMap (d.toElementMap
          (subU.toElementMap t))))).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, toElementMap_idem_of_isRetraction isProjection_subU.1 t]

/-- **`Π(d)` is a retraction, for any `d`.** -/
theorem isRetraction_piD (d : ApproximableMap U U) : IsRetraction (piD d) := by
  apply ApproximableMap.ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_piD d ((piD d).toElementMap φ),
    toApproxMap_toElementMap_piD d φ]
  apply ApproximableMap.ext_of_toElementMap
  intro t
  rw [toElementMap_piDApply d (piDApply d (toApproxMap φ)) t,
    piDApply_toElementMap_eq d (toApproxMap φ) t,
    toElementMap_piDApply d (toApproxMap φ) t]
  exact toElementMap_idem_of_isRetraction
    (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).1.1 _

/-- **`Π(d) ≤ I`, for any `d`.** Chains: `subU(t) ⊑ t` (`subU`'s own projection property) with
`f`'s monotonicity to get `f(subU(t)) ⊑ f(t)`, then the "type at `t`"'s own `≤ I` (from
`isFinitaryProjection_decode_subU`) to get `(type at t)(f(subU(t))) ⊑ f(subU(t))`. -/
theorem le_idMap_piD (d : ApproximableMap U U) : piD d ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_piD, le_iff_toElementMap_le]
  intro t
  rw [toElementMap_piDApply]
  have hP := (isFinitaryProjection_decode_subU (d.toElementMap (subU.toElementMap t))).1.2
  calc (toApproxMap (jArrow.toElementMap (subU.toElementMap
        (d.toElementMap (subU.toElementMap t))))).toElementMap
        ((toApproxMap φ).toElementMap (subU.toElementMap t))
      ≤ (toApproxMap φ).toElementMap (subU.toElementMap t) :=
        toElementMap_le_self_of_le_idMap hP _
    _ ≤ (toApproxMap φ).toElementMap t :=
        (toApproxMap φ).toElementMap_mono
          (toElementMap_le_self_of_le_idMap isProjection_subU.2 t)

/-- **Scott's own hint, in full: `Π(d)` is a projection, for every `d`.** -/
theorem isProjection_piD (d : ApproximableMap U U) : IsProjection (piD d) :=
  ⟨isRetraction_piD d, le_idMap_piD d⟩

/-- **`Π(d)`, regarded as living in `𝒰` (`piU d`), is a projection, for every `d`.** Half of "for
`d` a polymorphic type, `Π(d)` is a type" (Definition 8.3's `IsProjection` clause) — Scott's own
"it is easy to check" — obtained "for free" from `isProjection_piD` via the same conjugation
gadget (`isProjection_conjArrow`) used for `subU` in Step 1. Note this does not even need `d` to
be a polymorphic type. -/
theorem isProjection_piU (d : ApproximableMap U U) : IsProjection (piU d) :=
  isProjection_conjArrow (isProjection_piD d)

/-! ## Exercise 8.27(b)(0): `Fix(piU d) ≃o Fix(piD d)`

Mirrors Step 1's `subUFixIso` verbatim, substituting `piD d`/`piU d` for `subApprox`/`subU`
(both are built by the identical `i_→∘(-)∘j_→` conjugation recipe, so every step transfers
unchanged). Reduces "`piU d` is finitary" to "`piD d` is finitary" — the target of Exercise
8.27(b)(1) onward — exactly as `isFinitary_subU` was obtained from `isFinitary_subApprox`. -/

/-- `piU d`'s defining formula unfolded at the element level (mirrors `toElementMap_subU`). -/
theorem toElementMap_piU (d : ApproximableMap U U) (w : U.Element) :
    (piU d).toElementMap w =
      iArrow.toElementMap ((piD d).toElementMap (jArrow.toElementMap w)) := by
  unfold piU
  rw [toElementMap_comp, toElementMap_comp]

/-- Unfolds `(piU d).toElementMap w = w` into the statement that `j_→(w)` is already a fixed
point of `piD d` (mirrors `subApprox_fix_of_subU_fix`). -/
theorem piD_fix_of_piU_fix {d : ApproximableMap U U} {w : U.Element}
    (hw : (piU d).toElementMap w = w) :
    (piD d).toElementMap (jArrow.toElementMap w) = jArrow.toElementMap w := by
  rw [toElementMap_piU] at hw
  have hstep := congrArg jArrow.toElementMap hw
  rwa [jArrow_comp_iArrow_apply] at hstep

/-- Mirrors `subU_fix_of_subApprox_fix`. -/
theorem piU_fix_of_piD_fix {d : ApproximableMap U U} {φ : (funSpace U U).Element}
    (hφ : (piD d).toElementMap φ = φ) :
    (piU d).toElementMap (iArrow.toElementMap φ) = iArrow.toElementMap φ := by
  rw [toElementMap_piU, jArrow_comp_iArrow_apply, hφ]

/-- **Exercise 8.27(b)(0): `Fix(piU d) ≃o Fix(piD d)`.** Forward: `w ↦ j_→(w)`; backward:
`φ ↦ i_→(φ)`. Needs only `j_→∘i_→ = I` (no inequality on `i_→∘j_→`) — mirrors `subUFixIso`
verbatim, with `piD d`/`piU d` in place of `subApprox`/`subU`. -/
noncomputable def piUFixIso (d : ApproximableMap U U) :
    {w : U.Element // (piU d).toElementMap w = w} ≃o
      {φ : (funSpace U U).Element // (piD d).toElementMap φ = φ} where
  toFun w := ⟨jArrow.toElementMap w.1, piD_fix_of_piU_fix w.2⟩
  invFun φ := ⟨iArrow.toElementMap φ.1, piU_fix_of_piD_fix φ.2⟩
  left_inv w := by
    apply Subtype.ext
    show iArrow.toElementMap (jArrow.toElementMap w.1) = w.1
    have hw := toElementMap_piU d w.1
    rw [w.2] at hw
    rw [piD_fix_of_piU_fix w.2] at hw
    exact hw.symm
  right_inv φ := by
    apply Subtype.ext
    exact jArrow_comp_iArrow_apply φ.1
  map_rel_iff' := by
    intro w w'
    show jArrow.toElementMap w.1 ≤ jArrow.toElementMap w'.1 ↔ w.1 ≤ w'.1
    constructor
    · intro hle
      have h2 := iArrow.toElementMap_mono hle
      have e1 : iArrow.toElementMap (jArrow.toElementMap w.1) = w.1 := by
        have hw := toElementMap_piU d w.1
        rw [w.2, piD_fix_of_piU_fix w.2] at hw
        exact hw.symm
      have e2 : iArrow.toElementMap (jArrow.toElementMap w'.1) = w'.1 := by
        have hw' := toElementMap_piU d w'.1
        rw [w'.2, piD_fix_of_piU_fix w'.2] at hw'
        exact hw'.symm
      rwa [e1, e2] at h2
    · intro hle
      exact jArrow.toElementMap_mono hle

/-- **Exercise 8.27(b)(0), corollary: if `piD d` is finitary then so is `piU d`.** Mirrors
`isFinitary_subU`'s use of `subUFixIso`. This is the reduction Exercise 8.27(b)(1)–(b)(4) will
target: it suffices to prove `IsFinitary (piD d)` for `d` polymorphic. -/
theorem isFinitary_piU_of_isFinitary_piD {d : ApproximableMap U U} (h : IsFinitary (piD d)) :
    IsFinitary (piU d) := by
  obtain ⟨β, F, ⟨iso⟩⟩ := h
  exact ⟨β, F, ⟨(piUFixIso d).trans iso⟩⟩

/-! ## Exercise 8.27(b)(1): reduce finitariness of `piD d` to Theorem 8.5's step-closure formula

`Theorem85.lean`'s `isFinitaryProjection_of_formula` proves, for *any* approximable map `a : E → E`
on *any* neighbourhood system `E`, that Scott's step-closure formula (ii) —

  `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ X a X}`, for every `x ∈ |E|`

— by itself (no other hypothesis on `a`) implies `IsFinitaryProjection a`, with the witness domain
`fixedNbhd a` built automatically from `a`'s own relation. Specializing `E := funSpace U U`,
`a := piD d` turns "prove `piD d` is finitary" into "prove `piD d` satisfies formula (ii)" — no
external witness system to invent. This is exactly the reduction Exercise 8.27(b)(2)–(b)(3) target;
what remains here is only to record the specialization and its corollary via Exercise 8.27(b)(0). -/

/-- **Exercise 8.27(b)(1).** If `piD d` satisfies Scott's step-closure formula (ii), it is a
finitary projection — a direct specialization of `Theorem85.lean`'s general
`isFinitaryProjection_of_formula`, no new proof needed beyond the specialization itself. -/
theorem isFinitaryProjection_piD_of_formula (d : ApproximableMap U U)
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitaryProjection (piD d) :=
  isFinitaryProjection_of_formula (piD d) hii

/-- **Exercise 8.27(b)(1), assembled with (b)(0):** formula (ii) for `piD d` alone gives
`IsFinitary (piU d)`, i.e. (combined with the already-Pass 8.27(a)) the *entire* exercise for `d`
polymorphic. This pins down exactly what Exercise 8.27(b)(2)–(b)(3) need to supply: `hii`. -/
theorem isFinitary_piU_of_formula {d : ApproximableMap U U}
    (hii : ∀ (x : (funSpace U U).Element) {Y}, ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X) :
    IsFinitary (piU d) :=
  isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD_of_formula d hii).2

/-! ## Exercise 8.27(b)(2): unwind `piD d`'s neighbourhood relation

`piD d = curry (piDUncurried d)` uses `FunctionSpace.lean`'s *abstract* `curry` (not the Ex 7.16/
Table 5.5 recursion-theoretic coded layer). Its general relation lemma **`curry_rel`** already
exists there:

  `(curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W`

reducing `(piD d).rel X W` to a literal *set membership* test `gSection (piDUncurried d) hX ∈ W`
of an actual map into the funSpace-nbhd `W` (no new proof needed — `piD_rel_iff` below is the
direct specialization). The remaining unwinding is `gSection (piDUncurried d) hX`'s own relation:
`gSection_rel` reduces it to `(piDUncurried d).rel (prodNbhd X Y) Z`, and **`rel_iff_mem_principal`**
(`Approximable.lean`) plus **`pair_principal_eq_principal_prodNbhd`** (`Exercise821.lean`, general —
pairing two principal elements is the principal element of the product nbhd) convert *that* into an
*element*-level statement, which the already-proven **`toElementMap_piDUncurried`** evaluates in
closed form purely in terms of `subU`'s and `d`'s own `toElementMap` actions (built, in its own
proof, from `evalMap_apply`, `FunctionSpace.lean`'s abstract defining relation for `eval`). This is
`gSection_piDUncurried_rel_iff` below — the genuine content of this subgoal. -/

/-- **Exercise 8.27(b)(2)(a).** `(piD d).rel X W` reduces to a literal membership test — the direct
specialization of `curry_rel` (`FunctionSpace.lean`), no new proof needed. -/
theorem piD_rel_iff (d : ApproximableMap U U) {X W : Set (ApproximableMap U U)} :
    (piD d).rel X W ↔ ∃ hX : (funSpace U U).mem X, (funSpace U U).mem W ∧
      gSection (piDUncurried d) hX ∈ W :=
  curry_rel

/-- **Exercise 8.27(b)(2)(b).** `gSection (piDUncurried d) hX`'s own relation, fully unwound to a
closed elementwise formula in terms of the already-proven closed form `piDApply` (built, in its
own proof, purely from `subU`'s and `d`'s `toElementMap` actions plus `evalMap_apply`): reduce via
`gSection_rel` to `(piDUncurried d).rel (prodNbhd X Y) Z`, then via `rel_iff_mem_principal` +
`pair_principal_eq_principal_prodNbhd` to the element pair `pair (principal hX) (principal hY)`,
then read off `toElementMap_piDUncurried`/`toElementMap_piDApply`. This is the "unwind `piD d`'s
neighbourhood relation" content of Exercise 8.27(b)(2). -/
theorem gSection_piDUncurried_rel_iff (d : ApproximableMap U U)
    {X : Set (ApproximableMap U U)} (hX : (funSpace U U).mem X) {Y Z : Set ℚ} (hY : U.mem Y) :
    (gSection (piDUncurried d) hX).rel Y Z ↔
      ((piDApply d (toApproxMap ((funSpace U U).principal hX))).toElementMap
        (U.principal hY)).mem Z := by
  rw [gSection_rel, rel_iff_mem_principal (piDUncurried d) (prod_mem_prodNbhd hX hY),
    ← pair_principal_eq_principal_prodNbhd hX hY, toElementMap_piDUncurried,
    ← toElementMap_piDApply]

/-- **Exercise 8.27(b)(2), specialized to self-relation** (the shape Theorem 8.5's formula (ii)
actually tests, `a.rel X X`): combines (a) and (b) into the single membership-test formula that
Exercise 8.27(b)(3) will chain through `subU`'s and each `D'_s`'s own formula (ii). -/
theorem piD_rel_self_iff (d : ApproximableMap U U) {X : Set (ApproximableMap U U)} :
    (piD d).rel X X ↔ ∃ hX : (funSpace U U).mem X, gSection (piDUncurried d) hX ∈ X := by
  rw [piD_rel_iff]
  exact ⟨fun ⟨hX, _, hmem⟩ => ⟨hX, hmem⟩, fun ⟨hX, hmem⟩ => ⟨hX, hX, hmem⟩⟩

/-! ## Exercise 8.27(b)(3): formula (ii) for `piD d` — substantial partial progress, not closed

**The reduction is complete and clean.** Via `Sub8_6.toFilter_toApproxMap`/`mem_toFilter`
(`mem_iff_mem_toApproxMap`) plus the already-proven `toApproxMap_toElementMap_piD`, `hii`'s LHS
`((piD d).toElementMap x).mem Y` reduces *exactly* to a literal membership test
`piDApply d (toApproxMap x) ∈ Y` (`piD_toElementMap_mem_iff`) — no abstract "element" reasoning
left, purely a statement about the actual map `piDApply d (toApproxMap x) : ApproximableMap U U`
and the actual set `Y`.

**The `⟸` half closes unconditionally**, via `Theorem85.lean`'s newly-extracted
`mem_of_exists_rel_self` (isolated from `isFinitaryProjection_of_formula`'s own proof, valid for
*any* `a : E → E` with no hypothesis) — `hii_easy_direction` below.

**The `⟹` half (the genuine mathematical content) is *not* closed here.** Attempting it exposed a
precise, previously-undocumented obstruction, recorded in full in `HANDOFF.md`'s 2026-07-07
checkpoint: given `f := piDApply d (toApproxMap x) ∈ Y` (`Y = stepFun [(Y_i,Z_i)]_i`), unwinding
each `f.rel Y_i Z_i` via `gSection_piDUncurried_rel_iff`/`toElementMap_piDApply` and Theorem 8.5's
*already-proven* formula (ii) for `subU` (Exercise 8.27(a)) and for each per-`i` "type" projection
`P_i := toApproxMap(jArrow.toElementMap(subU.toElementMap(d.toElementMap t_i)))`
(`isFinitaryProjection_decode_subU`, `t_i := subU.toElementMap (U.principal hY_i)`) produces
per-component witnesses `W_i` (`W_i ⊆ Z_i`, `P_i.rel W_i W_i`) — the natural next step is to
assemble `X := stepFun [(T_i,W_i)]_i` for domain-side nbhds `T_i ⊇ Y_i` with `t_i.mem T_i`
(continuity), to get `x.mem X` and `X ⊆ Y`. But testing `(piD d).rel X X` itself re-runs the same
unwinding *at `X`'s own `T_i`*, which feeds `s_i := subU.toElementMap (U.principal hT_i)` — **not**
`t_i` — into `d`, landing on a *different* type-projection `P_i' := toApproxMap(jArrow.toElementMap
(subU.toElementMap (d.toElementMap s_i)))`. Since `T_i ⊇ Y_i` is unavoidable (needed for `X ⊆ Y`
by `mono`), `s_i ≤ t_i` is forced (monotonicity), so `P_i' ≤ P_i` is generally a *strictly weaker*
map, and `P_i.rel W_i W_i` does not transfer to `P_i'.rel W_i W_i` for free — the self-relation
witness and the continuity witness pull `T_i` in incompatible directions with a single round of
formula (ii). The likely resolution (not attempted) mirrors `Theorem85.lean`'s *own* `(i) ⟹ (ii)`
hard direction (`exists_principal_eq_of_isRetraction_le_idMap`'s compactness-reflection argument,
~200 lines) rather than a single formula(ii)-chase: an iterative/compactness "descent" building
`T_i` as a directed limit that becomes self-consistent *in the limit*, using algebraicity
(`eq_iSupDirected_principal`) to show the descent stabilizes at a genuine finite/principal nbhd —
a comparably-sized undertaking to Theorem 8.5's hard direction, not a quick corollary of it. `d`'s
polymorphism (`IsPolymorphicType`, unused so far) is expected to enter here, but exactly how is not
yet worked out. -/

/-- **Exercise 8.27(b)(3)(a).** `hii`'s LHS, reduced to a literal membership test: no abstract
"funSpace element" reasoning left, purely `piDApply d (toApproxMap x) ∈ Y` as an actual map/set. -/
theorem piD_toElementMap_mem_iff (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ piDApply d (toApproxMap x) ∈ Y := by
  conv_lhs => rw [← Sub8_6.toFilter_toApproxMap ((piD d).toElementMap x)]
  rw [mem_toFilter, toApproxMap_toElementMap_piD]

/-- **Exercise 8.27(b)(3), the `⟸` half — closes unconditionally, for any `d` at all.** Direct
specialization of `Theorem85.lean`'s newly-extracted `mem_of_exists_rel_self` (no hypothesis on
`a` needed) to `a := piD d`. The remaining, genuinely hard direction is documented above and in
`HANDOFF.md`; **not** attempted here. -/
theorem hii_easy_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    {X : Set (ApproximableMap U U)} (hXx : x.mem X) (hXY : X ⊆ Y) (hXX : (piD d).rel X X) :
    ((piD d).toElementMap x).mem Y :=
  mem_of_exists_rel_self x hYE hXx hXY hXX

/-! ## Exercise 8.27(b)(3)(b): the `⟹` half of formula (ii), closed

**Resolution of the obstruction documented above.** The fix: instead of chasing a *single* domain
witness `T_i ⊇ Y_i` (which forces the wrong type-projection `P_i'` via `s_i ≤ t_i`), observe that
`t_i` is *itself* the directed sup of its own `subU`-self-consistent approximants
(`eq_iSupDirected_scPrincipal`) — a family on which `principal T = subU(principal T)` *exactly*
(`subU_principal_eq_of_rel_self`, by antisymmetry: `≤` from `subU`'s projection property, `≥` from
self-consistency). Since `d`, `subU`, `jArrow` are all continuous, the "type at `t_i`" `P_i` is
*itself* the directed sup (in the `ApproximableMap` order) of the "type at `T`" `P_T` over this same
family, so `P_i.rel W W` (already established) is, by directed-sup compactness
(`toApproxMap_rel_iSupDirected`/`mem_iSupDirected`), *already* witnessed at some single
self-consistent `T ∈ 𝒮(t_i)`. A second application of the same compactness fact (this time to the
continuity witness for `x`) and one directed-family common refinement (`scFamily_directed`) then
finds a *single* `T` simultaneously self-consistent, `x`-continuous, and `P_T`-self-relating — the
correct `T_i`. Notably, this argument uses only `subU`'s algebraicity/continuity and
`isFinitaryProjection_decode_subU` (Step 4, unconditional); **`d`'s polymorphism is never used**, so
the result below holds for *every* `d`, polymorphic or not — a strictly stronger and more uniform
fact than Scott's exercise statement requires. -/

/-- **`subU`'s self-relating neighbourhoods are exactly fixed under `principal`.** If `subU.rel T T`,
the "witnessing element" `↑T` is *exactly* fixed by `subU` (not merely approximated): `≤` is
`subU`'s projection property (`subU ≤ I`), `≥` is `principal_le_of_mem` applied to the membership
`subU.rel T T` gives via `rel_iff_mem_principal`. -/
theorem subU_principal_eq_of_rel_self {T : Set ℚ} (hT : U.mem T) (hTT : subU.rel T T) :
    subU.toElementMap (U.principal hT) = U.principal hT := by
  apply le_antisymm
  · exact toElementMap_le_self_of_le_idMap isProjection_subU.2 _
  · exact principal_le_of_mem ((subU.rel_iff_mem_principal hT).mp hTT)

/-- **Descending to a self-consistent approximant.** For `t` already `subU`-fixed, formula (ii) for
`subU` (Exercise 8.27(a)) applied at `t` and any target `T₀ ∈ t` produces a *self-consistent*
`T ⊆ T₀` still in `t`'s filter — the cofinality fact that makes the self-consistent nbhds a directed
family sup-ing to `t` itself (`eq_iSupDirected_scPrincipal` below). -/
theorem exists_rel_self_subset_of_mem {t : U.Element} (ht : subU.toElementMap t = t)
    {T₀ : Set ℚ} (hT₀ : t.mem T₀) : ∃ T, subU.rel T T ∧ t.mem T ∧ T ⊆ T₀ := by
  have hmem : (subU.toElementMap t).mem T₀ := by rw [ht]; exact hT₀
  obtain ⟨_, T, hTt, hTT₀, hTT⟩ :=
    (formula_of_isFinitaryProjection isFinitaryProjection_subU t).mp hmem
  exact ⟨T, hTT, hTt, hTT₀⟩

/-- The family of `subU`-self-consistent nbhds already in `t`'s filter. -/
def scFamily (t : U.Element) : Type := {T : Set ℚ // subU.rel T T ∧ t.mem T}

instance instNonemptyScFamily (t : U.Element) : Nonempty (scFamily t) :=
  ⟨⟨U.master, subU.master_rel, t.master_mem⟩⟩

/-- The principal element witnessed by a member of `scFamily t`. -/
def scPrincipal {t : U.Element} (i : scFamily t) : U.Element :=
  U.principal (t.sub i.2.2)

/-- **`scFamily t`'s principals form a directed family.** Given `i, j`, apply
`exists_rel_self_subset_of_mem` at the common refinement `i.1 ∩ j.1` (valid via `t.inter_mem`). -/
theorem scFamily_directed {t : U.Element} (ht : subU.toElementMap t = t) :
    ∀ i j : scFamily t, ∃ k : scFamily t, scPrincipal i ≤ scPrincipal k ∧ scPrincipal j ≤ scPrincipal k :=
  fun i j => by
    obtain ⟨T, hTT, htT, hTsub⟩ := exists_rel_self_subset_of_mem ht (t.inter_mem i.2.2 j.2.2)
    refine ⟨⟨T, hTT, htT⟩, ?_, ?_⟩
    · exact (U.principal_le_iff (t.sub i.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_left)
    · exact (U.principal_le_iff (t.sub j.2.2) (t.sub htT)).mpr (hTsub.trans Set.inter_subset_right)

/-- **`t` is the directed sup of its own self-consistent approximants.** Cofinality
(`exists_rel_self_subset_of_mem`) shows the self-consistent sub-family already has the same sup as
the full principal-approximant family (`eq_iSupDirected_principal`), namely `t` itself. -/
theorem eq_iSupDirected_scPrincipal {t : U.Element} (ht : subU.toElementMap t = t) :
    t = NeighborhoodSystem.iSupDirected scPrincipal (scFamily_directed ht) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ
    obtain ⟨T, hTT, htT, hTZ⟩ := exists_rel_self_subset_of_mem ht hZ
    exact ⟨⟨T, hTT, htT⟩, (U.mem_principal _).mpr ⟨t.sub hZ, hTZ⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨hZmem, hTZ⟩ := (U.mem_principal _).mp hi
    exact t.up_mem i.2.2 hZmem hTZ

/-- **The "type at `s`" map**, `decode(subU(d(s)))`, as a function of the *element* `s` (not just
`s = subU(principal Y)` for some `Y`). Packaging `piDApply`'s inner formula this way is what lets
continuity/monotonicity in `s` be stated directly. -/
noncomputable def piDTypeMap (d : ApproximableMap U U) : ApproximableMap U (funSpace U U) :=
  jArrow.comp (subU.comp d)

theorem toElementMap_piDTypeMap (d : ApproximableMap U U) (s : U.Element) :
    (piDTypeMap d).toElementMap s = jArrow.toElementMap (subU.toElementMap (d.toElementMap s)) := by
  unfold piDTypeMap
  rw [toElementMap_comp, toElementMap_comp]

/-- The "type at `s`" itself, as an `ApproximableMap U U`. Always a finitary projection
(`isFinitaryProjection_piDType`, Step 4), for *any* `d` and `s`. -/
noncomputable def piDType (d : ApproximableMap U U) (s : U.Element) : ApproximableMap U U :=
  toApproxMap ((piDTypeMap d).toElementMap s)

theorem isFinitaryProjection_piDType (d : ApproximableMap U U) (s : U.Element) :
    IsFinitaryProjection (piDType d s) := by
  unfold piDType
  rw [toElementMap_piDTypeMap]
  exact isFinitaryProjection_decode_subU (d.toElementMap s)

/-- **`piDType d` is monotone in `s`.** Composite of monotone `toElementMap`s (`d`, `subU`,
`jArrow`) followed by monotone `toApproxMap` (`Sub8_6.toApproxMap_monotone`). -/
theorem piDType_monotone (d : ApproximableMap U U) {s s' : U.Element} (h : s ≤ s') :
    piDType d s ≤ piDType d s' :=
  Sub8_6.toApproxMap_monotone ((piDTypeMap d).toElementMap_mono h)

/-- `piDApply`'s defining formula, restated via `piDType`/`piDTypeMap`. -/
theorem toElementMap_piDApply' (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (piDType d (subU.toElementMap t)).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, piDType, toElementMap_piDTypeMap]

/-- **Exercise 8.27(b)(3)(b), single-pair case — the genuine mathematical content.** Given
`f := piDApply d (toApproxMap x)` relates `Y₀` to `Z₀`, produce `X` (a single `step`) with
`x.mem X`, `X ⊆ step Y₀ Z₀`, `(piD d).rel X X`.

The compactness-descent argument, in outline (`t := subU(↑Y₀)`):
1. Formula (ii) for the finitary projection `piDType d t` (at `t`'s own image of `x`) gives `W ⊆ Z₀`
   with `piDType d t` self-relating `W`.
2. Both `(toApproxMap x).rel _ W`'s witness and `(piDType d t).rel W W` are pushed down, via
   `t = ⨆ scPrincipal` and directed-sup compactness, to *some* self-consistent approximants
   `i₀, i₁ ∈ scFamily t`.
3. A common refinement `k` (directedness of `scFamily t`) makes *both* facts hold simultaneously at
   `T := k.1`: `(toApproxMap x).rel T W` (monotonicity) and `(piDType d (scPrincipal k)).rel W W`
   (monotonicity of `piDType d`, since bigger domain element ⟹ bigger map).
4. `scPrincipal k` is *exactly* `subU`-fixed (self-consistency), so `piDType d (scPrincipal k))` is
   *exactly* the type-projection `X`'s own self-test uses at `T` — no mismatch. -/
theorem exists_X_of_mem_step (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y₀ Z₀ : Set ℚ} (hmem : piDApply d (toApproxMap x) ∈ step Y₀ Z₀) :
    ∃ X, x.mem X ∧ X ⊆ (step Y₀ Z₀ : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  have hrelY0Z0 : (piDApply d (toApproxMap x)).rel Y₀ Z₀ := hmem
  have hY₀ : U.mem Y₀ := (piDApply d (toApproxMap x)).rel_dom hrelY0Z0
  have hZ₀ : U.mem Z₀ := (piDApply d (toApproxMap x)).rel_cod hrelY0Z0
  set t : U.Element := subU.toElementMap (U.principal hY₀) with ht_def
  have ht : subU.toElementMap t = t := toElementMap_idem_of_isRetraction isProjection_subU.1 _
  have hmem' : ((piDType d t).toElementMap ((toApproxMap x).toElementMap t)).mem Z₀ := by
    have h := ((piDApply d (toApproxMap x)).rel_iff_mem_principal hY₀).mp hrelY0Z0
    rwa [toElementMap_piDApply'] at h
  obtain ⟨_, W, hW_mem, hWZ₀, hWW⟩ :=
    (formula_of_isFinitaryProjection (isFinitaryProjection_piDType d t)
      ((toApproxMap x).toElementMap t)).mp hmem'
  have hw_sup := eq_iSupDirected_scPrincipal ht
  -- Push the continuity witness `W` for `x` down to a single self-consistent approximant `i₀`.
  rw [hw_sup, toElementMap_iSupDirected, mem_iSupDirected] at hW_mem
  obtain ⟨i₀, hi₀⟩ := hW_mem
  have hrelT0 : (toApproxMap x).rel i₀.1 W :=
    (rel_iff_mem_principal (toApproxMap x) (t.sub i₀.2.2)).mpr hi₀
  -- Push the self-relation witness `W` for `piDType d t` down to a single self-consistent `i₁`.
  have hWW2 : ∃ i : scFamily t, (piDType d (scPrincipal i)).rel W W := by
    have h2 : (piDType d t).rel W W := hWW
    unfold piDType at h2
    rw [hw_sup, toElementMap_iSupDirected, Sub8_6.toApproxMap_rel_iSupDirected] at h2
    exact h2
  obtain ⟨i₁, hi₁⟩ := hWW2
  -- Common refinement `k` of `i₀, i₁` makes both facts hold simultaneously.
  obtain ⟨k, hik0, hik1⟩ := scFamily_directed ht i₀ i₁
  have hksub0 : k.1 ⊆ i₀.1 := (U.principal_le_iff (t.sub i₀.2.2) (t.sub k.2.2)).mp hik0
  have hTfinal : U.mem k.1 := subU.rel_dom k.2.1
  have hWmem : U.mem W := (piDType d t).rel_dom hWW
  have hrelTfinal : (toApproxMap x).rel k.1 W :=
    (toApproxMap x).mono hrelT0 hksub0 subset_rfl hTfinal hWmem
  have hPfinal : (piDType d (scPrincipal k)).rel W W := piDType_monotone d hik1 W W hi₁
  -- `k.1` is `subU`-self-consistent, so `scPrincipal k = subU(↑k.1)` exactly.
  have hTfinal_fix : subU.toElementMap (U.principal hTfinal) = U.principal hTfinal :=
    subU_principal_eq_of_rel_self hTfinal k.2.1
  set X : Set (ApproximableMap U U) := step k.1 W with hX_def
  have hXvalid : (funSpace U U).mem X := step_mem hTfinal hWmem
  refine ⟨X, ?_, ?_, ?_⟩
  · -- `x.mem X`
    exact toApproxMap_rel.mp hrelTfinal
  · -- `X ⊆ step Y₀ Z₀`
    have hle : t ≤ U.principal hY₀ := toElementMap_le_self_of_le_idMap isProjection_subU.2 _
    have hY0sub : Y₀ ⊆ k.1 := ((U.mem_principal hY₀).mp (hle k.1 k.2.2)).2
    exact step_subset hY₀ hZ₀ hY0sub hWZ₀
  · -- `(piD d).rel X X`
    rw [piD_rel_self_iff]
    refine ⟨hXvalid, ?_⟩
    show (gSection (piDUncurried d) hXvalid).rel k.1 W
    rw [gSection_piDUncurried_rel_iff d hXvalid hTfinal]
    set g : ApproximableMap U U := toApproxMap ((funSpace U U).principal hXvalid) with hg_def
    show ((piDApply d g).toElementMap (U.principal hTfinal)).mem W
    rw [toElementMap_piDApply', hTfinal_fix]
    have hg : g.rel k.1 W := by
      rw [hg_def, toApproxMap_rel]
      exact ((funSpace U U).mem_principal hXvalid).mpr ⟨hXvalid, subset_rfl⟩
    have hgmem : (g.toElementMap (U.principal hTfinal)).mem W :=
      (rel_iff_mem_principal g hTfinal).mp hg
    exact mem_of_exists_rel_self (g.toElementMap (U.principal hTfinal))
      ((piDType d (U.principal hTfinal)).rel_dom hPfinal) hgmem subset_rfl hPfinal

/-- **Exercise 8.27(b)(3)(b), assembled over a whole `stepFun` list.** Induction on the list `L`
using `exists_X_of_mem_step` for the head pair and the inductive hypothesis for the tail, combined
via `x.inter_mem` (giving the ambient validity of the intersection "for free", `x.sub`) and
`(piD d).mono`/`.inter_right` (self-relation of an intersection of two self-related nbhds). -/
theorem exists_X_of_mem_stepFun (d : ApproximableMap U U) (x : (funSpace U U).Element)
    (L : List (Set ℚ × Set ℚ)) (hmem : piDApply d (toApproxMap x) ∈ stepFun L) :
    ∃ X, x.mem X ∧ X ⊆ (stepFun L : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  induction L with
  | nil =>
    refine ⟨(funSpace U U).master, x.master_mem, ?_, (piD d).master_rel⟩
    simp
  | cons p L ih =>
    rw [stepFun_cons] at hmem
    obtain ⟨hmemP, hmemL⟩ := hmem
    obtain ⟨Xp, hXpx, hXpsub, hXpXp⟩ := exists_X_of_mem_step d x hmemP
    obtain ⟨XL, hXLx, hXLsub, hXLXL⟩ := ih hmemL
    refine ⟨Xp ∩ XL, x.inter_mem hXpx hXLx, ?_, ?_⟩
    · rw [stepFun_cons]
      exact Set.inter_subset_inter hXpsub hXLsub
    · have hvalidP : (funSpace U U).mem Xp := x.sub hXpx
      have hvalidL : (funSpace U U).mem XL := x.sub hXLx
      have hvalidInter : (funSpace U U).mem (Xp ∩ XL) := x.sub (x.inter_mem hXpx hXLx)
      have h1 : (piD d).rel (Xp ∩ XL) Xp :=
        (piD d).mono hXpXp Set.inter_subset_left subset_rfl hvalidInter hvalidP
      have h2 : (piD d).rel (Xp ∩ XL) XL :=
        (piD d).mono hXLXL Set.inter_subset_right subset_rfl hvalidInter hvalidL
      exact (piD d).inter_right h1 h2

/-- **Exercise 8.27(b)(3), the `⟹` half, closed for any `d` at all.** Destructure the general
`Y : Set (ApproximableMap U U)` via `funSpace_mem_iff` into `Y = stepFun L`, then apply
`exists_X_of_mem_stepFun`. -/
theorem hii_hard_direction (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} (hYE : (funSpace U U).mem Y)
    (hmem : piDApply d (toApproxMap x) ∈ Y) :
    ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hYE
  exact exists_X_of_mem_stepFun d x L hmem

/-- **Exercise 8.27(b)(3), in full: `piD d` satisfies Scott's step-closure formula (ii), for *any*
`d` at all** (`d`'s polymorphism is not needed). Combines the reduction (b)(3)(a) with the easy
(`hii_easy_direction`) and now-closed hard (`hii_hard_direction`) halves. -/
theorem hii_piD (d : ApproximableMap U U) (x : (funSpace U U).Element)
    {Y : Set (ApproximableMap U U)} :
    ((piD d).toElementMap x).mem Y ↔
      (funSpace U U).mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ (piD d).rel X X := by
  rw [piD_toElementMap_mem_iff]
  constructor
  · rintro ⟨hYE, hmem⟩
    exact ⟨hYE, hii_hard_direction d x hYE hmem⟩
  · rintro ⟨hYE, X, hXx, hXY, hXX⟩
    have := hii_easy_direction d x hYE hXx hXY hXX
    rwa [piD_toElementMap_mem_iff] at this

/-- **Exercise 8.27(b)(4): `piD d` is a finitary projection, for every `d`** (Exercise 8.27(b)(1)
specialized to `hii_piD`). Combined with Exercise 8.27(b)(0) (`isFinitary_piU_of_isFinitary_piD`),
this closes "`Π(d)` is a type" — Scott's own hint, in full, and *without even needing `d` to be a
polymorphic type* (a strictly stronger statement than the exercise asks for). -/
theorem isFinitaryProjection_piD (d : ApproximableMap U U) : IsFinitaryProjection (piD d) :=
  isFinitaryProjection_piD_of_formula d (fun x => hii_piD d x)

/-- **Exercise 8.27, in full: for `d` a polymorphic type, `Π(d)` is a type.** (In fact for *any*
`d` at all — see `isFinitaryProjection_piD`.) This is the exercise's own statement, the last exercise
in the book, closed. -/
theorem isFinitaryProjection_piU (d : ApproximableMap U U) : IsFinitaryProjection (piU d) :=
  ⟨isProjection_piU d, isFinitary_piU_of_isFinitary_piD (isFinitaryProjection_piD d).2⟩

/-! ## Discussion: "why does this equation mean that `x` is in the product?"

Scott's parenthetical question, about `x(t) = d(t)(x(t))` (all `t`): unwind the right-hand side
using Exercise 8.26's `Uapply`/`Ulam` (the self-hosted application of an element of `𝒰` regarded
as a "type"): `d(t)(x(t))` means `Uapply (d.toElementMap t) (x.toElementMap t)`, i.e. *decode*
`d(t)` via `j_→` into an actual map `D_{d(t)} : 𝒰 → 𝒰` and apply it to `x(t)`. Since `d` is a
polymorphic type, `d(t) ∈ Fix(subU)` for every `t` (`polymorphicType_apply_mem_fix`), hence
`D_{d(t)}` is *always* a genuine finitary projection — "the type at `t`" in the informal reading.
The equation `x(t) = D_{d(t)}(x(t))` is then exactly the defining property of being a **fixed
point** of that projection, i.e. `x(t) ∈ Fix(D_{d(t)})`. Since `Fix` of a finitary projection is
(order-isomorphic to) a genuine domain, this says precisely: *`x(t)` is a legitimate element of
the domain named by the type `t`*, for *every* type `t` simultaneously — i.e. `x` is a dependent
family `x : Π_{t : Type} D_{d(t)}`, a bona fide element of the "continuous product." Nothing about
this needs a separate Lean lemma beyond what is already proved above; it is genuinely just Scott
inviting the reader to notice that his equation *is* the universal-domain encoding of dependent
products (a form of impredicative/parametric polymorphism, à la System F).

## Why "the problem is to show it is finitary" is left unattempted here

Scott's own hint stops at "it is easy to check that `Π(d)` is a projection" — established above,
in fact unconditionally, for *every* `d`. For the finitary half he gives **no technique at all**,
unlike literally every other exercise/theorem in this book (which come with a concrete "(Hint:
...)" naming a specific construction or reduction). This is deliberate: Exercise 8.27 is the
**last exercise in the book**, credited to a named correspondent (James Donahue), and is posed as
a genuinely open-ended research problem about a *dependent*/*polymorphic* product — Scott is
asking the reader to discover a construction, not recalling one.

Concretely, every "finitary-closure" result proved elsewhere in this project
(`finitaryProjection_arrowComb`, `_prodComb`, `_sumComb` in `Proposition810b.lean`; Theorem 8.6(b)'s
own `isFinitary_subApprox`) works by exhibiting `Fix` of the projection in question as
order-isomorphic to an *already available* domain (a product/sum/function-space/subsystem-space
built from *fixed*, finitely many ingredient domains). `Fix(piD d)` has no such ready-made
candidate: it is the dependent product `Π_{t : 𝒰} Fix(D_{d(t)})` ranging over a *continuum* of
"index" values `t`, indexed by a domain (`𝒰`) rather than a finite/discrete set, with the fibers
`Fix(D_{d(t)})` themselves varying (dependently, via `d`) rather than staying fixed. Constructing a
"domain of dependent-continuous-sections" and proving `Fix(piD d)` is isomorphic to it is a
genuinely new piece of domain theory (closer to a logical-relations/realizability argument for
System-F-style parametric polymorphism than to any single-step algebraic closure fact), with no
template anywhere in Lectures I–VIII. It is intentionally left as the natural terminus of this
formalization project, matching Scott's own framing of it as "the problem."
-/

end Scott1980.Neighborhood
