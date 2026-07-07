import Scott1980.Neighborhood.Proposition810b
import Scott1980.Neighborhood.Exercise324
import Scott1980.Neighborhood.Table55

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), toolkit — function-space congruence and currying

Two small general-purpose isomorphism-manipulation tools, needed to assemble the final closing
argument of Exercise 8.25 (`D ≅ D → V`, `V × V ≅ V` `⟹` `D × D ≅ D`, `D ≅ D → D`):

* **`funSpace_congr`**: `𝒟₀ ≅ 𝒟₀'`, `𝒟₁ ≅ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ (𝒟₀' → 𝒟₁')`, built from
  `Proposition810b.lean`'s Hom-bifunctor `expMap` (`f ↦ k∘f∘h`) applied to the two `ApproximableMap`s
  `ofIso e₀.symm`/`ofIso e₁` coming from the given order-isomorphisms, using `expMap`'s functor laws
  (`expMap_comp`/`expMap_id`) to see that the two induced maps are *exact* mutual inverses
  (`orderIsoOfMutualInverse`, a small standalone gadget: two approximable maps composing to the
  identity *on the nose* in both directions give an order-isomorphism of element types — arguably
  missing general infrastructure, provided here).
* **`curry_isomorphic`**: `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`, Theorem 3.12's `curryIso`
  (`Table55.lean`) restated as a domain isomorphism.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-! ### A standalone gadget: exact mutual inverses give an order-isomorphism -/

/-- **Two approximable maps that are *exact* (not merely `≤`) mutual inverses give an
order-isomorphism of element types.** The generic upgrade behind `elementIsoOfProjectionPair`
(`Proposition810b.lean`) when the projection-pair equation holds in *both* directions: then the
fixed-point subtype on the codomain side is *everything*, collapsing to a genuine bijection. -/
def orderIsoOfMutualInverse {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) (hij : i.comp j = idMap E) : D.Element ≃o E.Element where
  toFun := i.toElementMap
  invFun := j.toElementMap
  left_inv x := by rw [← toElementMap_comp, hji, toElementMap_idMap]
  right_inv y := by rw [← toElementMap_comp, hij, toElementMap_idMap]
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro h
      have hm := j.toElementMap_mono h
      rwa [← toElementMap_comp, ← toElementMap_comp, hji, toElementMap_idMap,
        toElementMap_idMap] at hm
    · intro h
      exact i.toElementMap_mono h

/-! ### `ofIso e` and `ofIso e.symm` are exact mutual inverses -/

theorem ofIso_symm_comp_ofIso (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e.symm).comp (ofIso e) = idMap V₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.symm_apply_apply]

theorem ofIso_comp_ofIso_symm (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e).comp (ofIso e.symm) = idMap V₀' := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

/-! ### `funSpace` congruence -/

theorem funSpaceCongr_hji (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0) (ofIso e1.symm)).comp (expMap (ofIso e0.symm) (ofIso e1)) =
      idMap (funSpace V₀ V₁) := by
  rw [← expMap_comp, ofIso_symm_comp_ofIso, ofIso_symm_comp_ofIso, expMap_id]

theorem funSpaceCongr_hij (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0.symm) (ofIso e1)).comp (expMap (ofIso e0) (ofIso e1.symm)) =
      idMap (funSpace V₀' V₁') := by
  rw [← expMap_comp, ofIso_comp_ofIso_symm, ofIso_comp_ofIso_symm, expMap_id]

/-- **`funSpace` is a congruence for `≃o`.** `𝒟₀ ≃o 𝒟₀'`, `𝒟₁ ≃o 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≃o (𝒟₀' → 𝒟₁')`. -/
noncomputable def funSpaceCongrOrderIso (e0 : V₀.Element ≃o V₀'.Element)
    (e1 : V₁.Element ≃o V₁'.Element) :
    (funSpace V₀ V₁).Element ≃o (funSpace V₀' V₁').Element :=
  orderIsoOfMutualInverse (expMap (ofIso e0.symm) (ofIso e1)) (expMap (ofIso e0) (ofIso e1.symm))
    (funSpaceCongr_hji e0 e1) (funSpaceCongr_hij e0 e1)

/-- **`funSpace` is a congruence for `≅ᴰ`.** `𝒟₀ ≅ᴰ 𝒟₀'`, `𝒟₁ ≅ᴰ 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁')`. -/
theorem funSpace_congr (h0 : V₀ ≅ᴰ V₀') (h1 : V₁ ≅ᴰ V₁') :
    funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁' :=
  h0.elim fun e0 => h1.elim fun e1 => ⟨funSpaceCongrOrderIso e0 e1⟩

/-- **`funSpace` congruence, domain slot.** `𝒟₀ ≅ᴰ 𝒟₀'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁)`. -/
theorem funSpace_congr_left (h0 : V₀ ≅ᴰ V₀') : funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁ :=
  funSpace_congr h0 (Isomorphic.refl V₁)

/-- **`funSpace` congruence, codomain slot.** `𝒟₁ ≅ᴰ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀ → 𝒟₁')`. -/
theorem funSpace_congr_right (h1 : V₁ ≅ᴰ V₁') : funSpace V₀ V₁ ≅ᴰ funSpace V₀ V₁' :=
  funSpace_congr (Isomorphic.refl V₀) h1

/-! ### Currying, as a domain isomorphism -/

/-- **Currying (Theorem 3.12), as a domain isomorphism.** `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
theorem curry_isomorphic (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    funSpace (prod V₀ V₁) V₂ ≅ᴰ funSpace V₀ (funSpace V₁ V₂) :=
  ⟨curryIso V₀ V₁ V₂⟩

end Scott1980.Neighborhood
