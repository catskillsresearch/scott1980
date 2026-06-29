import Scott1980.Neighborhood.Theorem41

/-!
# Exercise 4.9 (Scott 1981, PRG-19, Lecture IV) — the operator `Ψ` and `fix = fix(Ψ)`

Scott asks for an *approximable* operator

  `Ψ : ((𝒟 → 𝒟) → 𝒟) → ((𝒟 → 𝒟) → 𝒟)`     with     `Ψ(θ)(f) = f(θ(f))`,

and then to prove that `fix : (𝒟 → 𝒟) → 𝒟` is the **least fixed point** of `Ψ` — the true equation
`fix = fix(λF λf. f(F(f)))` (cf. the text following Exercise 4.9).

**Construction.** Writing `G = (𝒟 → 𝒟)` and `E = (G → 𝒟)`, the term `λF λf. f(F(f))` is built from the
cartesian-closed combinators: `Ψ = curry Φ` where `Φ : E × G → 𝒟` is
`Φ = eval_{𝒟,𝒟} ∘ ⟨π_G, eval_{G,𝒟}⟩`, sending `⟨F, f⟩ ↦ f(F(f))`. Approximability is automatic
(`bigPsi`); the defining equation `Ψ(θ)(f) = f(θ(f))` is `bigPsi_apply` (Theorem 3.12's `curry` β-rule
plus the `eval`/projection laws).

**`fix = fix(Ψ)`.** Representing `fix` as the element `toFilter (fixMap V) ∈ |E|`:

* `bigPsi_fix` — `Ψ(fix) = fix`: indeed `Ψ(fix)(f) = f(fix(f)) = f(fix f) = fix f = fix(f)` since
  `fix(f) = fix f` is a fixed point of `f` (Theorem 4.1);
* `bigPsi_least` — if `Ψ(θ) ⊑ θ` then `fix ⊑ θ`: pointwise, `Ψ(θ)(f) = f(θ(f)) ⊑ θ(f)` makes `θ(f)`
  a pre-fixed point of `f`, so `fix f ⊑ θ(f)` (Theorem 4.1's minimality), i.e. `fix(f) ⊑ θ(f)`;
* `fix_eq_fixElement_bigPsi` — combining the two, `fix = fix(Ψ)` (`= fixElement Ψ`, Theorem 4.1's
  canonical least fixed point).

The operator data `bigPsi` is **choice-free**; equalities of elements/operators go through the
project's permitted `Element.ext` / `ext_of_toElementMap`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** The approximable operator `Ψ = λF λf. f(F(f))` on the
higher-order domain `E = ((𝒟 → 𝒟) → 𝒟)`, built as `curry (eval ∘ ⟨π_G, eval⟩)`. -/
def bigPsi (V : NeighborhoodSystem α) :
    ApproximableMap (funSpace (funSpace V V) V) (funSpace (funSpace V V) V) :=
  curry ((evalMap V V).comp
    (paired (proj₁ (funSpace (funSpace V V) V) (funSpace V V)) (evalMap (funSpace V V) V)))

/-- **Exercise 4.9 (Scott 1981, PRG-19).** The defining equation `Ψ(θ)(f) = f(θ(f))`. -/
theorem bigPsi_apply (V : NeighborhoodSystem α)
    (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element) :
    (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
      = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f) := by
  rw [bigPsi, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply, evalMap_apply]

/-- `fix`, as the element of `E = ((𝒟 → 𝒟) → 𝒟)` corresponding to the operator `fixMap`, unfolds
under `toApproxMap` back to `fixMap` (the `funSpace` round-trip). -/
theorem toApproxMap_toFilter_fixMap (V : NeighborhoodSystem α) :
    toApproxMap (toFilter (fixMap V)) = fixMap V := by
  have he := (funSpaceEquiv (funSpace V V) V).apply_symm_apply (fixMap V)
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix` is a *fixed point* of `Ψ`: `Ψ(fix) = fix`. -/
theorem bigPsi_fix (V : NeighborhoodSystem α) :
    (bigPsi V).toElementMap (toFilter (fixMap V)) = toFilter (fixMap V) := by
  apply (funSpaceEquiv (funSpace V V) V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro f
  rw [bigPsi_apply, toApproxMap_toFilter_fixMap, fixMap_toElementMap, toElementMap_fixElement]

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix` is the *least* pre-fixed point of `Ψ`: any `θ` with
`Ψ(θ) ⊑ θ` satisfies `fix ⊑ θ`. -/
theorem bigPsi_least (V : NeighborhoodSystem α) (θ : (funSpace (funSpace V V) V).Element)
    (hθ : (bigPsi V).toElementMap θ ≤ θ) : toFilter (fixMap V) ≤ θ := by
  -- transport `Ψ(θ) ⊑ θ` to the pointwise pre-fixed-point inequality on maps.
  have hθ' : toApproxMap ((bigPsi V).toElementMap θ) ≤ toApproxMap θ := by
    rw [← funSpaceEquiv_apply, ← funSpaceEquiv_apply]
    exact (funSpaceEquiv (funSpace V V) V).monotone hθ
  have hpre : ∀ f, (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f)
      ≤ (toApproxMap θ).toElementMap f := by
    intro f
    have h := (le_iff_toElementMap_le.mp hθ') f
    rwa [bigPsi_apply] at h
  -- conclude `fix ⊑ θ` pointwise via Theorem 4.1's minimality.
  apply (funSpaceEquiv (funSpace V V) V).le_iff_le.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toFilter_fixMap, le_iff_toElementMap_le]
  intro f
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap f) (hpre f)

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix = fix(Ψ)`: `fix` is the least fixed point of `Ψ`,
i.e. coincides with Theorem 4.1's canonical least fixed point `fixElement Ψ`. -/
theorem fix_eq_fixElement_bigPsi (V : NeighborhoodSystem α) :
    toFilter (fixMap V) = (bigPsi V).fixElement := by
  apply le_antisymm
  · exact bigPsi_least V _ (le_of_eq (toElementMap_fixElement (bigPsi V)))
  · exact fixElement_le_of_toElementMap_le (bigPsi V) (le_of_eq (bigPsi_fix V))

end Scott1980.Neighborhood
