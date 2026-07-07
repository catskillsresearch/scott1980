import Scott1980.Neighborhood.Exercise817
import Scott1980.Neighborhood.Proposition810b
import Scott1980.Neighborhood.Exercise326Sum
import Scott1980.Neighborhood.Exercise315

/-!
# Exercise 8.19 (Scott 1981, PRG-19)

> **Exercise 8.19.** Suppose we know both `T` and `E→E ⊴ E`. Does it follow that `E+E` and
> `E×E ⊴ E`?

Here `T` is the truth-value domain of Example 1.2 (`Example23.T`/`Exercise326.TD`, the same
two-point-plus-bottom domain used throughout §3 for `cond`). Reading "we know `T`" as "we know
`T ⊴ E`" (the natural companion hypothesis to `E→E ⊴ E`, and exactly what is needed to make the
argument below go through), the answer is **yes**, both follow, via two general-purpose `⊴`
constructions:

* **Products.** `T ⊴ E` gives an embedding `E × E ⊴ (T → E)` (pair `(x, y)` up as the function
  `t ↦ cond(t, x, y)`, using Exercise 3.26's `cond`), and `T ⊴ E` gives `(T → E) ⊴ (E → E)`
  (precompose with the retraction `E → T`, contravariant functoriality of `expMap`,
  `Proposition810b.lean`). Chaining with the hypothesis `E → E ⊴ E` and `⊴`'s transitivity
  (Exercise 8.17) gives `E × E ⊴ E`.
* **Sums.** `T ⊴ E` similarly gives `E + E ⊴ T × (E × E)` (tag a summand by `which : E+E → T`
  together with the two projections `out₀, out₁ : E + E → E`, Exercise 3.26's `which`/`cond`
  machinery) and `T × (E × E) ⊴ E × (E × E)` (the *covariant* functoriality of `prod` in `T ⊴ E`).
  Composing with `E × E ⊴ E` (just proved, applied twice to peel off the nested product) and
  transitivity gives `E + E ⊴ E`.

Both directions reuse only pre-existing combinators (`cond`, `which`, `curry`, `evalMap`,
`expMap`, `paired`/`proj₀`/`proj₁`) — the only genuinely new general-purpose facts are `expMap`'s
monotonicity in its contravariant argument (`expMap_mono_left`), the analogous covariant
monotonicity of pairing (`prod_left_trianglelefteq`/`prod_right_trianglelefteq`), and two small
"cross" round-trip facts for the sum injections (`outMap₁_comp_inMap₀`/`outMap₀_comp_inMap₁`, the
natural companions of Exercise 3.18's `outMap₀_comp_inMap₀`/`outMap₁_comp_inMap₁`).

Everything here inherits `Classical.choice` only from `ext_of_toElementMap` calls already baked
into `expMap`'s own defining lemmas (`Proposition810b.lean`) and from `T`'s concrete presentation
(`Example12.lean`) — the same pre-existing footprint as every other `T`/`cond`-mentioning theorem
in the project, not something new introduced here.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u

/-! ## General-purpose lemmas -/

section General

variable {α β γ δ : Type*}

/-- **`expMap` is monotone in its contravariant argument** (`k` fixed): `h ≤ h' ⟹ expMap h k ≤
expMap h' k`. Proved choice-freely from `comp_mono_gen` and the order-isomorphism `funSpaceEquiv`,
transported through the elementwise formula `toApproxMap_toElementMap_expMap`. -/
theorem expMap_mono_left {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β}
    {V0' : NeighborhoodSystem γ} {V1' : NeighborhoodSystem δ}
    {h h' : ApproximableMap V0' V0} (hh : h ≤ h') (k : ApproximableMap V1 V1') :
    expMap h k ≤ expMap h' k := by
  rw [le_iff_toElementMap_le]
  intro φ
  apply (funSpaceEquiv V0' V1').map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap,
    toApproxMap_toElementMap_expMap]
  exact comp_mono_gen le_rfl (comp_mono_gen le_rfl hh)

/-- **Contravariant functoriality of `⊴` in the function-space's domain argument.** `A ⊴ B ⟹
(A → C) ⊴ (B → C)` for any `C`: precompose/postcompose with the given projection pair via
`expMap`. -/
theorem funSpace_dom_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : funSpace A C ⊴ funSpace B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (expMap p.proj (idMap C)) (expMap p.inj (idMap C))
    ?_ ?_
  · have hcomp := (expMap_comp p.proj (idMap C) p.inj (idMap C)).symm
    rw [hcomp, p.proj_comp_inj, idMap_comp]
    exact expMap_id
  · calc (expMap p.proj (idMap C)).comp (expMap p.inj (idMap C))
        = expMap (p.inj.comp p.proj) ((idMap C).comp (idMap C)) :=
          (expMap_comp p.inj (idMap C) p.proj (idMap C)).symm
      _ ≤ expMap (idMap B) ((idMap C).comp (idMap C)) :=
          expMap_mono_left p.inj_comp_proj_le _
      _ = expMap (idMap B) (idMap C) := by rw [idMap_comp]
      _ = idMap (funSpace B C) := expMap_id

/-- **Covariant functoriality of `⊴` in `prod`'s left argument.** `A ⊴ B ⟹ prod A C ⊴ prod B C`
for any `C`: pair the given projection pair with the identity on `C`. -/
theorem prod_left_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod A C ⊴ prod B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (paired (p.inj.comp (proj₀ A C)) (proj₁ A C))
    (paired (p.proj.comp (proj₀ B C)) (proj₁ B C)) ?_ ?_
  · apply ext_of_toElementMap
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    have hxx : (p.proj.comp p.inj).toElementMap x = (idMap A).toElementMap x := by
      rw [p.proj_comp_inj]
    rw [toElementMap_comp, toElementMap_idMap] at hxx
    rw [hxx]
  · rw [le_iff_toElementMap_le]
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    apply pair_le_pair_iff.mpr
    refine ⟨?_, le_refl y⟩
    have hxx : (p.inj.comp p.proj).toElementMap x ≤ (idMap B).toElementMap x :=
      le_iff_toElementMap_le.mp p.inj_comp_proj_le x
    rwa [toElementMap_comp, toElementMap_idMap] at hxx

/-- **Covariant functoriality of `⊴` in `prod`'s right argument.** `A ⊴ B ⟹ prod C A ⊴ prod C B`,
obtained from `prod_left_trianglelefteq` by conjugating with `prod`'s commutativity
(`Exercise315.prod_comm_isomorphic`). -/
theorem prod_right_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod C A ⊴ prod C B := by
  have h1 : prod C A ⊴ prod A C :=
    (prod_comm_isomorphic (V₀ := C) (V₁ := A)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  have h2 : prod A C ⊴ prod B C := prod_left_trianglelefteq C h
  have h3 : prod B C ⊴ prod C B :=
    (prod_comm_isomorphic (V₀ := B) (V₁ := C)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  exact trianglelefteq_trans (trianglelefteq_trans h1 h2) h3

/-- If `f` sends the master input to only the master output, then `f` sends `⊥` to `⊥`
(more precisely, `≤ ⊥`, i.e. `= ⊥` by `bot_le`). The elementwise membership at `⊥` is read off the
relation at `V₀.master` via `rel_iff_mem_principal` (`⊥ = ↑Δ`). -/
theorem toElementMap_bot_le {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) (h : ∀ {Y}, f.rel V₀.master Y → Y = V₁.master) :
    f.toElementMap V₀.bot ≤ V₁.bot := by
  intro Y hY
  rw [mem_bot]
  exact h ((rel_iff_mem_principal f V₀.master_mem).mpr hY)

/-- The pairing of two bottoms is the bottom of the product. -/
theorem pair_bot {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β} :
    pair V0.bot V1.bot = (prod V0 V1).bot := by
  apply le_antisymm
  · intro W hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    rw [mem_bot] at hX hY
    subst hX; subst hY
    rw [mem_bot]
    exact prod_master.symm
  · exact NeighborhoodSystem.bot_le _ _

/-- **`TD.bot = Example23.botElt`.** These are the *same* element (`TD` and `Example23.T` are both
`Example12.neighborhoodSystem`), but not syntactically unifiable by `rfl` (the `abbrev`s don't
delta-reduce transparently through `NeighborhoodSystem.bot`'s field projection), so we prove it by
antisymmetry instead. -/
theorem TD_bot_eq_botElt : TD.bot = Example23.botElt :=
  le_antisymm (NeighborhoodSystem.bot_le _ _) (Example23.botElt_le _)

end General

/-! ## Cross round-trips for the sum injections (companions of Exercise 3.18) -/

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₁ ∘ in₀ = const ⊥`.** A left-injected element carries no right-hand information. -/
theorem outMap₁_comp_inMap₀ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁)) = constMap V₀ V₁.bot := by
  apply ApproximableMap.ext
  intro X Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hX, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, ?_⟩
    obtain ⟨a, ha⟩ := h₀ X hX
    have hmaster : rightPart V₁ (inj₀ X) ⊆ rightPart V₁ W := rightPart_mono V₁ hinj
    rw [rightPart_inj₀ V₁ ⟨a, ha⟩] at hmaster
    exact Set.Subset.antisymm (V₁.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hX, rfl⟩
    exact ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), V₁.master_mem, (rightPart_inj₀ V₁ (h₀ X hX)).subset⟩

/-- **`out₀ ∘ in₁ = const ⊥`.** A right-injected element carries no left-hand information. -/
theorem outMap₀_comp_inMap₁ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁)) = constMap V₁ V₀.bot := by
  apply ApproximableMap.ext
  intro Y Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hY, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, ?_⟩
    obtain ⟨b, hb⟩ := h₁ Y hY
    have hmaster : leftPart V₀ (inj₁ Y) ⊆ leftPart V₀ W := leftPart_mono V₀ hinj
    rw [leftPart_inj₁ V₀ ⟨b, hb⟩] at hmaster
    exact Set.Subset.antisymm (V₀.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hY, rfl⟩
    exact ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), V₀.master_mem, (leftPart_inj₁ V₀ (h₁ Y hY)).subset⟩

/-- `which(in₀ x) ≤ true`: a left-injected element's tag never reaches `false`. -/
theorem which_inMap₀_le_trueElt (x : V₀.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
      ≤ Example23.trueElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)).sub hZ) with rfl | rfl | rfl
  · exact Example23.trueElt.master_mem
  · show Example23.trueElt.mem Example12.zero
    exact Or.inr rfl
  · exfalso
    obtain ⟨Y, hY, hmem⟩ := which_mem_one.mp hZ
    obtain ⟨X, _, hX0, _, hsub⟩ := hmem
    exact not_inj₀_subset_inj₁ (h₀ X hX0) hsub

/-- `which(⊥) ≤ ⊥`: the basepoint carries no tag information. Only the third `whichGuard` disjunct
applies at `W = (sum V₀ V₁ h₀ h₁).master`, forcing the output to `master`. -/
theorem which_bot_le :
    (whichMap V₀ V₁ h₀ h₁).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ Example23.botElt := by
  rw [← TD_bot_eq_botElt]
  refine toElementMap_bot_le _ ?_
  intro Y hg
  exact whichGuard_masterC hg.2.2 rfl

/-- `out₀(⊥) ≤ ⊥`: the basepoint carries no left-hand information. -/
theorem outMap₀_bot_le :
    (outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₀.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₀.sub_master hg.2.1) ?_
  have h2 : leftPart V₀ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [leftPart_sumMaster] at h2

/-- `out₁(⊥) ≤ ⊥`: the basepoint carries no right-hand information. -/
theorem outMap₁_bot_le :
    (outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₁.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₁.sub_master hg.2.1) ?_
  have h2 : rightPart V₁ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [rightPart_sumMaster] at h2

/-- `which(in₁ y) ≤ false`: a right-injected element's tag never reaches `true`. -/
theorem which_inMap₁_le_falseElt (y : V₁.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)
      ≤ Example23.falseElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)).sub hZ) with rfl | rfl | rfl
  · exact Example23.falseElt.master_mem
  · exfalso
    obtain ⟨X, hX, hmem⟩ := which_mem_zero.mp hZ
    obtain ⟨Y, _, hY0, _, hsub⟩ := hmem
    exact not_inj₁_subset_inj₀ (h₁ Y hY0) hsub
  · show Example23.falseElt.mem Example12.one
    exact Or.inr rfl

end SumHelpers

/-- **`T`'s elements, named via `Example23`.** The three-way classification of `Example12`,
restated with `Example23`'s `⊥`/`true`/`false` names (they are the *same* terms by `rfl`). -/
theorem TD_trichotomy (t : TD.Element) :
    t = Example23.botElt ∨ t = Example23.trueElt ∨ t = Example23.falseElt :=
  Example12.neighborhoodSystem.element_classification t

/-! ## Goal 1: `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E` -/

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- The "swap" map `(E×E)×T → T×(E×E)`, used to feed `cond`'s `T×E×E`-shaped domain from a
`(E×E)×T`-shaped one so it can be curried away from the `T`-argument. -/
noncomputable def swapProdT : ApproximableMap (prod (prod E E) TD) (prod TD (prod E E)) :=
  paired (proj₁ (prod E E) TD) (proj₀ (prod E E) TD)

theorem toElementMap_swapProdT (x y : E.Element) (t : TD.Element) :
    (swapProdT (E := E)).toElementMap (pair (pair x y) t) = pair t (pair x y) := by
  simp only [swapProdT, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁, fst_pair,
    snd_pair]

/-- **Pairing up, as a function out of `T`.** `pairToFun(x, y) : T → E` sends `t ↦ cond(t, x,
y)`; in particular `true ↦ x`, `false ↦ y`, `⊥ ↦ ⊥` (Exercise 3.26). -/
noncomputable def pairToFun : ApproximableMap (prod E E) (funSpace TD E) :=
  curry ((cond E).comp swapProdT)

theorem toApproxMap_pairToFun (x y : E.Element) (t : TD.Element) :
    (toApproxMap ((pairToFun (E := E)).toElementMap (pair x y))).toElementMap t
      = (cond E).toElementMap (pair t (pair x y)) := by
  rw [pairToFun, toElementMap_curry_apply, toElementMap_comp, toElementMap_swapProdT]

/-- **Reading off the pair from a function `T → E`.** `funToPair(φ) = (φ(true), φ(false))`. -/
noncomputable def funToPair : ApproximableMap (funSpace TD E) (prod E E) :=
  paired
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.trueElt)))
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.falseElt)))

theorem toElementMap_funToPair (φ : (funSpace TD E).Element) :
    (funToPair (E := E)).toElementMap φ
      = pair ((toApproxMap φ).toElementMap Example23.trueElt)
          ((toApproxMap φ).toElementMap Example23.falseElt) := by
  simp only [funToPair, toElementMap_paired, toElementMap_comp, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

/-- **`funToPair ∘ pairToFun = I`.** `(x, y) ↦ (λt. cond(t,x,y)) ↦ (cond(true,x,y),
cond(false,x,y)) = (x, y)`. -/
theorem funToPair_comp_pairToFun : (funToPair (E := E)).comp pairToFun = idMap (prod E E) := by
  apply ext_of_toElementMap
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair, toApproxMap_pairToFun,
    toApproxMap_pairToFun, Exercise326.cond_true, Exercise326.cond_false]

/-- **`pairToFun ∘ funToPair ≤ I`.** For every `φ : T → E`, feeding `(φ(true), φ(false))` back
through `cond` gives a map agreeing with `φ` at `true`/`false` and `≤ φ` at `⊥` (`E.bot ≤`
anything). Case split on `T`'s three elements (`TD_trichotomy`). -/
theorem pairToFun_comp_funToPair_le :
    (pairToFun (E := E)).comp funToPair ≤ idMap (funSpace TD E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair]
  apply (funSpaceEquiv TD E).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro t
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [toApproxMap_pairToFun, Exercise326.cond_bot]; exact E.bot_le _
  · rw [toApproxMap_pairToFun, Exercise326.cond_true]
  · rw [toApproxMap_pairToFun, Exercise326.cond_false]

/-- **`E × E ⊴ (T → E)`.** -/
theorem prod_trianglelefteq_funSpace_TD : prod E E ⊴ funSpace TD E :=
  trianglelefteq_of_projectionPair pairToFun funToPair funToPair_comp_pairToFun
    pairToFun_comp_funToPair_le

/-- **Exercise 8.19, Goal 1.** `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E`: chain `E×E ⊴ (T→E) ⊴
(E→E) ⊴ E`. -/
theorem prod_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    prod E E ⊴ E :=
  trianglelefteq_trans
    (trianglelefteq_trans prod_trianglelefteq_funSpace_TD (funSpace_dom_trianglelefteq E hT))
    hArrow

end Prod

/-! ## Goal 2: `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E` -/

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)

/-- **The tagging embedding `E + E → T × (E × E)`.** `w ↦ (which w, out₀ w, out₁ w)`. -/
noncomputable def sumToProdT : ApproximableMap (sum E E hE hE) (prod TD (prod E E)) :=
  paired (whichMap E E hE hE)
    (paired (outMap₀ (h₀ := hE) (h₁ := hE)) (outMap₁ (h₀ := hE) (h₁ := hE)))

theorem toElementMap_sumToProdT (w : (sum E E hE hE).Element) :
    (sumToProdT hE).toElementMap w
      = pair ((whichMap E E hE hE).toElementMap w)
          (pair ((outMap₀ (h₀ := hE) (h₁ := hE)).toElementMap w)
            ((outMap₁ (h₀ := hE) (h₁ := hE)).toElementMap w)) := by
  simp only [sumToProdT, toElementMap_paired]

/-- **`condSum ∘ sumToProdT = I`.** Scott's identity `cond_which`, transported through
`condSumEmb`. -/
theorem condSum_comp_sumToProdT :
    (condSum E E hE hE).comp (sumToProdT hE) = idMap (sum E E hE hE) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_sumToProdT, condSum, toElementMap_comp,
    condSumEmb_toElementMap]
  exact cond_which w

/-- **`sumToProdT ∘ condSum ≤ I`.** Case-split `t : T` into `⊥ / true / false`
(`TD_trichotomy`); `condSum(t,x,y)` reduces to a concrete sum element (`⊥`, `in₀ x`, or `in₁ y`)
whose image under `sumToProdT` is read off via the round-trips
`outMap₀_comp_inMap₀`/`outMap₁_comp_inMap₀` (and their mirror images) together with the tag bounds
`which_inMap₀_le_trueElt`/`which_inMap₁_le_falseElt`. -/
theorem sumToProdT_comp_condSum_le :
    (sumToProdT hE).comp (condSum E E hE hE) ≤ idMap (prod TD (prod E E)) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z, ← pair_fst_snd z.snd]
  set t := z.fst; set x := z.snd.fst; set y := z.snd.snd
  clear_value t x y
  rw [toElementMap_comp, toElementMap_idMap]
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [condSum_bot, toElementMap_sumToProdT]
    exact pair_le_pair_iff.mpr ⟨which_bot_le,
      pair_le_pair_iff.mpr ⟨outMap₀_bot_le.trans (E.bot_le x), outMap₁_bot_le.trans (E.bot_le y)⟩⟩
  · rw [condSum_true, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₀_le_trueElt x, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₀_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₁_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
  · rw [condSum_false, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₁_le_falseElt y, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₀_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₁_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le

/-- **`E + E ⊴ T × (E × E)`.** -/
theorem sum_trianglelefteq_prodT : sum E E hE hE ⊴ prod TD (prod E E) :=
  trianglelefteq_of_projectionPair (sumToProdT hE) (condSum E E hE hE) (condSum_comp_sumToProdT hE)
    (sumToProdT_comp_condSum_le hE)

/-- **Exercise 8.19, Goal 2.** `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E`: chain
`E+E ⊴ T×(E×E) ⊴ E×(E×E) ⊴ E×E ⊴ E`, using Goal 1 (applied twice, to peel off each product layer)
for the last two links. -/
theorem sum_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E := by
  have hPE : prod E E ⊴ E := prod_trianglelefteq_of hT hArrow
  exact trianglelefteq_trans
    (trianglelefteq_trans (sum_trianglelefteq_prodT hE) (prod_left_trianglelefteq (prod E E) hT))
    (trianglelefteq_trans (prod_right_trianglelefteq E hPE) hPE)

end Sum

/-! ## Exercise 8.19, assembled -/

/-- **Exercise 8.19.** If `T ⊴ E` and `E → E ⊴ E`, then `E + E ⊴ E` and `E × E ⊴ E`. -/
theorem exercise_8_19 {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  ⟨sum_trianglelefteq_of hE hT hArrow, prod_trianglelefteq_of hT hArrow⟩

end Scott1980.Neighborhood
