import Scott1980.Neighborhood.Exercise817
import Scott1980.Neighborhood.FunctionSpace

/-!
# Exercise 8.20 (Scott 1981, PRG-19)

> **Exercise 8.20.** For any system we know `D ⊴ D + D`, but what about
>
> `D ⊴ D × D` and `D ⊴ D → D`?
>
> Would these projections be computable if `D` is effectively given? Are there more than one
> projection pair in each case?

## What is formalized here

Both `D ⊴ D×D` and `D ⊴ (D→D)` hold **unconditionally, for every domain `D`** (no hypotheses
needed, unlike Exercise 8.19's `E×E ⊴ E`/`E+E ⊴ E`, which genuinely required `T ⊴ E` and
`E→E ⊴ E`). Both are exhibited by the *simplest possible* combinator recipe, generalized slightly
to two (possibly different) domains `A`, `B`:

* **Products** (`trianglelefteq_prod_fst`/`trianglelefteq_prod_snd`): embed `a ↦ ⟨a, ⊥⟩` (resp.
  `b ↦ ⟨⊥, b⟩`), retract with `proj₀` (resp. `proj₁`). `proj₀⟨a,⊥⟩ = a` on the nose, and
  `⟨(proj₀ z), ⊥⟩ = ⟨z.fst, ⊥⟩ ≤ ⟨z.fst, z.snd⟩ = z` since `⊥ ≤ z.snd` always
  (`Proposition 3.2(i)`'s `pair_le_pair_iff` reduces this to `⊥ ≤ z.snd`, `NeighborhoodSystem.bot_le`).
  Specializing `A = B = D` gives `D ⊴ D×D` (`D_trianglelefteq_prod`).
* **Function spaces** (`trianglelefteq_funSpace_const`): embed `b ↦ (λ_. b)` (the constant function,
  `constFunMap := curry (proj₀ B A)`), retract `φ ↦ φ(⊥)` (evaluate at the bottom,
  `evalBotMap := evalMap A B ∘ ⟨id, const ⊥⟩`). `eval(const_b) = b` on the nose
  (`toApproxMap_constFunMap`, from `toElementMap_curry_apply`), and `const_{φ(⊥)} ≤ φ` pointwise
  since `φ(⊥) ≤ φ(x)` for every `x` by **monotonicity of approximable maps**
  (`toElementMap_mono`, Proposition 2.2(iii)) applied to `⊥ ≤ x`. Specializing `A = B = D` gives
  `D ⊴ D→D` (`D_trianglelefteq_funSpace`).

**On `D ⊴ D+D`:** Scott states this as *already known* background (not part of the question), so
it is not re-derived here. The "easy half" of the projection pair is already in the codebase
(`outMap₀_comp_inMap₀`, Exercise 3.18); the second half (`inMap₀ ∘ outMap₀ ≤ id`, needing a
case-analysis on general sum elements analogous to the `which`/`condSum` machinery of Exercise 8.19)
is genuine additional work that this exercise does not ask for, so it is left as background
citation rather than re-proved.

**On multiplicity ("are there more than one projection pair"):** for products, the two
constructions above are already *literally different maps* whenever `D` has any element `≠ ⊥`
(`embedFst_ne_embedSnd_of_ne_bot`, by evaluating both at that element and reading off the first
coordinate) — so **yes**, generically more than one. For `D→D`, the "evaluate at a fixed point `a`"
half of the recipe is forced to be `a = ⊥` (for a *general* `a`, `const_{φ(a)} ≤ φ` would need
`φ(a) ≤ φ(x)` for *every* `x`, i.e. `a ≤ x` for every `x`, i.e. `a = ⊥`); but distinct projection
pairs can still arise by composing this one with any nontrivial order-automorphism of `D` (if
`D ≅ᴰ D` non-trivially, conjugating `constFunMap`/`evalBotMap` by the automorphism gives a genuinely
different pair). We do not formalize this second, automorphism-dependent source of multiplicity
here — it depends on `D`'s own automorphism group, which is not fixed data for a "for any system"
claim — but record it as the answer to Scott's question.

**On computability:** every combinator used (`⊥`, `paired`, `proj₀`/`proj₁`, `curry`, `evalMap`,
`constMap`) already has (or, for `constMap` at a fixed computable index such as `⊥`'s, trivially
would have) an `IsComputableMap` closure lemma elsewhere in the project (`proj₀_isComputable`/
`proj₁_isComputable`/`paired_isComputable`, `Theorem74.lean`; `curry_isComputable`/
`evalMap_isComputable`, `Theorem75.lean`) — so **yes**, both projection pairs are computable
whenever `D` is effectively given. Assembling the precise numerical parameters these lemmas expect
(the `ℕ → ℕ` encoding functions `gN`/`incl0`/`incl1`/`eq1` etc.) for *this specific* composite is
extra bookkeeping proportional to a full computable-presentation transport, not to this exercise's
mathematical content, so it is recorded here as a citation-backed answer rather than reformalized.

Everything proved here is **fully choice-free** (`⊆ {propext, Quot.sound}`): following the project's
"prefer `le_iff_toElementMap_le` + `le_antisymm` over `ext_of_toElementMap`" discipline
(`HANDOFF.md`), even the map *equalities* (`proj₀_comp_embedFst`, `proj₁_comp_embedSnd`,
`evalBotMap_comp_constFunMap`) are proved via `le_antisymm` on `le_iff_toElementMap_le`-unfolded
goals rather than `ApproximableMap.ext_of_toElementMap`, since both `≤`-directions are in fact
trivial (the underlying `toElementMap`s are literally equal, not just comparable) — so no
`Classical.choice` is pulled in anywhere, unlike most of `D`-mentioning Exercise 8.19.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u v

/-! ## `A ⊴ prod A B` and `B ⊴ prod A B`, for any `A`, `B` -/

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`a ↦ ⟨a, ⊥⟩`.** -/
noncomputable def embedFst : ApproximableMap A (prod A B) := paired (idMap A) (constMap A B.bot)

/-- **`b ↦ ⟨⊥, b⟩`.** -/
noncomputable def embedSnd : ApproximableMap B (prod A B) := paired (constMap B A.bot) (idMap B)

theorem proj₀_comp_embedFst : (proj₀ A B).comp (embedFst A B) = idMap A := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro a <;>
    simp [embedFst, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₀, fst_pair]

theorem embedFst_comp_proj₀_le : (embedFst A B).comp (proj₀ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₀, fst_pair, embedFst,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨le_refl x, B.bot_le y⟩

theorem proj₁_comp_embedSnd : (proj₁ A B).comp (embedSnd A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    simp [embedSnd, toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_constMap,
      toElementMap_proj₁, snd_pair]

theorem embedSnd_comp_proj₁_le : (embedSnd A B).comp (proj₁ A B) ≤ idMap (prod A B) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_proj₁, snd_pair, embedSnd,
    toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  exact pair_le_pair_iff.mpr ⟨A.bot_le x, le_refl y⟩

/-- **`A ⊴ prod A B`**, via `a ↦ ⟨a, ⊥⟩` / `proj₀`. -/
theorem trianglelefteq_prod_fst : A ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedFst A B) (proj₀ A B) (proj₀_comp_embedFst A B)
    (embedFst_comp_proj₀_le A B)

/-- **`B ⊴ prod A B`**, via `b ↦ ⟨⊥, b⟩` / `proj₁`. -/
theorem trianglelefteq_prod_snd : B ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedSnd A B) (proj₁ A B) (proj₁_comp_embedSnd A B)
    (embedSnd_comp_proj₁_le A B)

end Prod

/-- **Multiplicity, product case.** `embedFst`/`embedSnd` (hence the two projection pairs above)
are genuinely *different maps* as soon as `D` has an element `x ≠ ⊥`: evaluating both at `x` gives
`⟨x, ⊥⟩` vs. `⟨⊥, x⟩`, which differ in their first coordinate (`fst_pair`). -/
theorem embedFst_ne_embedSnd_of_ne_bot {α : Type u} {D : NeighborhoodSystem α} {x : D.Element}
    (hx : x ≠ D.bot) : embedFst D D ≠ embedSnd D D := fun h => hx <| by
  have heq := congrArg (fun f => f.toElementMap x) h
  simp only [embedFst, embedSnd, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap] at heq
  simpa using congrArg (·.fst) heq

/-! ## `B ⊴ funSpace A B`, for any `A`, `B` -/

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`b ↦ (λ_. b)`, the constant-function embedding.** `curry (proj₀ B A) : B → (A → B)` sends `b`
to the function that ignores its argument and always returns `b`. -/
noncomputable def constFunMap : ApproximableMap B (funSpace A B) := curry (proj₀ B A)

/-- **`φ ↦ φ(⊥)`, evaluation at the bottom.** -/
noncomputable def evalBotMap : ApproximableMap (funSpace A B) B :=
  (evalMap A B).comp (paired (idMap (funSpace A B)) (constMap (funSpace A B) A.bot))

@[simp] theorem toApproxMap_constFunMap (b : B.Element) (a : A.Element) :
    (toApproxMap ((constFunMap A B).toElementMap b)).toElementMap a = b := by
  rw [constFunMap, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

theorem toElementMap_evalBotMap (φ : (funSpace A B).Element) :
    (evalBotMap A B).toElementMap φ = (toApproxMap φ).toElementMap A.bot := by
  simp [evalBotMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

theorem evalBotMap_comp_constFunMap : (evalBotMap A B).comp (constFunMap A B) = idMap B := by
  apply le_antisymm <;> rw [le_iff_toElementMap_le] <;> intro b <;>
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_evalBotMap, toApproxMap_constFunMap]

/-- `const_{φ(⊥)} ≤ φ` pointwise, since `φ(⊥) ≤ φ(x)` for every `x` (monotonicity,
`toElementMap_mono`, Proposition 2.2(iii), applied to `⊥ ≤ x`). -/
theorem constFunMap_comp_evalBotMap_le :
    (constFunMap A B).comp (evalBotMap A B) ≤ idMap (funSpace A B) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap]
  apply (funSpaceEquiv A B).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro a
  rw [toApproxMap_constFunMap, toElementMap_evalBotMap]
  exact toElementMap_mono (toApproxMap φ) (A.bot_le a)

/-- **`B ⊴ funSpace A B`**, via `b ↦ (λ_. b)` / evaluation at `⊥`. -/
theorem trianglelefteq_funSpace_const : B ⊴ funSpace A B :=
  trianglelefteq_of_projectionPair (constFunMap A B) (evalBotMap A B)
    (evalBotMap_comp_constFunMap A B) (constFunMap_comp_evalBotMap_le A B)

end FunSpace

/-! ## Exercise 8.20, specialized and assembled -/

variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D×D`.** -/
theorem D_trianglelefteq_prod : D ⊴ prod D D := trianglelefteq_prod_fst D D

/-- **Exercise 8.20, `D ⊴ D→D`.** -/
theorem D_trianglelefteq_funSpace : D ⊴ funSpace D D := trianglelefteq_funSpace_const D D

/-- **Exercise 8.20.** For any domain `D`, `D ⊴ D×D` and `D ⊴ D→D` (unconditionally — no hypotheses
needed, unlike Exercise 8.19). See the module docstring for the discussion of computability and
multiplicity of projection pairs that Scott also asks about. -/
theorem exercise_8_20 : D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  ⟨D_trianglelefteq_prod D, D_trianglelefteq_funSpace D⟩

end Scott1980.Neighborhood
