import Scott1980.Neighborhood.Exercise511
import Scott1980.Neighborhood.Exercise618
import Scott1980.Neighborhood.Lemma615

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), step 3 — `𝒟 ⊴ 𝒟^∞`

Scott's hint remarks that (after solving `D ≅ D → 𝒰^∞`) "`𝒰 ◁ D`", i.e. the universal domain `𝒰`
embeds as a subdomain of the solution `D`, which is what makes the eventual `D` non-trivial and
universal. The link runs through `𝒰 ⊴ 𝒰^∞`: any domain `V` embeds into its own infinite power
`V^∞ = iterSys V` as the "singleton stack" `x ↦ ⟨x, ⊥, ⊥, …⟩`, with `head` as a retraction.

This file proves `V ⊴ iterSys V` for **every** `V` (Lemma 6.15 applied to the projection pair
`embedIntoPow ⊣ head`), reusing the stack combinators `head`/`push`/`pair` from Exercise 5.11 and
the bottom-sequence computation `component_bot` from Exercise 6.18. Specializing `V := 𝒰` gives
Scott's `𝒰 ⊴ 𝒰^∞`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The "singleton stack" embedding `D → D^∞`: `x ↦ ⟨x, ⊥, ⊥, …⟩`, i.e. `x` prepended to the all-`⊥`
stack. -/
def embedIntoPow : ApproximableMap V (iterSys V) :=
  (push V).comp (paired (idMap V) (constMap V (iterSys V).bot))

theorem toElementMap_embedIntoPow (x : V.Element) :
    (embedIntoPow V).toElementMap x = (push V).toElementMap (pair x (iterSys V).bot) := by
  rw [embedIntoPow, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

/-- The head of the singleton stack `⟨x, ⊥, ⊥, …⟩` is `x`. -/
theorem component_embedIntoPow_zero (x : V.Element) :
    component ((embedIntoPow V).toElementMap x) 0 = x := by
  rw [toElementMap_embedIntoPow, ← head_apply, head_push]

/-- Every coordinate past the head of `⟨x, ⊥, ⊥, …⟩` is `⊥`. -/
theorem component_embedIntoPow_succ (x : V.Element) (n : ℕ) :
    component ((embedIntoPow V).toElementMap x) (n + 1) = V.bot := by
  rw [toElementMap_embedIntoPow, ← component_tail, tail_push, Exercise618.component_bot]

/-- **`head` retracts `embedIntoPow`.** -/
theorem head_comp_embedIntoPow : (head V).comp (embedIntoPow V) = idMap V :=
  ApproximableMap.ext_of_toElementMap fun x => by
    rw [toElementMap_comp, toElementMap_idMap, head_apply, component_embedIntoPow_zero]

/-- **`embedIntoPow ∘ head ≤ id`**: re-stacking after reading only the head can only forget
information (all coordinates past the head collapse to `⊥`). -/
theorem embedIntoPow_comp_head_le : (embedIntoPow V).comp (head V) ≤ idMap (iterSys V) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_comp, toElementMap_idMap]
  apply le_of_component_le
  intro n
  cases n with
  | zero => rw [component_embedIntoPow_zero, head_apply]
  | succ m => rw [component_embedIntoPow_succ]; exact NeighborhoodSystem.bot_le V _

/-- **Exercise 8.25 (Scott 1981, PRG-19): `𝒟 ⊴ 𝒟^∞`**, for every `𝒟`. Specialized to `𝒟 = 𝒰` this is
Scott's remark `𝒰 ⊴ 𝒰^∞`. -/
theorem trianglelefteq_iterSys : V ⊴ iterSys V :=
  trianglelefteq_of_projectionPair (embedIntoPow V) (head V)
    (head_comp_embedIntoPow V) (embedIntoPow_comp_head_le V)

end Scott1980.Neighborhood
