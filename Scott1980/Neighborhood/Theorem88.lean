import Scott1980.Neighborhood.Definition87

/-!
# Theorem 8.8 (Scott 1981, PRG-19, Lecture VIII) — `U` is universal

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Theorem 8.8:

> The system `U` is universal in the sense that, for every countable neighbourhood system `D`, we
> have `D ⊴ U`. Moreover, if `D` is effectively given, then the projection pair making the
> embedding can be taken as computable. Indeed there is a correspondence between effectively
> presented domains and the computable, finitary projections of `U`.

This file works towards **Theorem 8.8(a)**, the general (non-effective) half of the theorem: every
*countable* `D` embeds as a subsystem of `U`, up to isomorphism.

## Scott's construction

Enumerate `D = {Xₙ ∣ n ∈ ℕ}` (with `X₀ = Δ = D.master`). Scott builds `Yₙ ∈ U` recursively so
that, for every `n` and every `δ ∈ {+,-}ⁿ`, writing `δX := X` if `δ = +` and `Δ \ X` if `δ = -`,
the **atom** `⋂_{i<n} δᵢXᵢ` is empty iff the corresponding atom `⋂_{i<n} δᵢYᵢ` is empty — call this
invariant `(■)`. Once built, matching `Xᵢ ↦ Yᵢ` realizes the embedding.

## This file's encoding

Rather than track the atoms via dependent `Fin n → Bool` tuples, we track them as a `List (Set α ×
Set ℚ)` of matching *pairs* `(A, B)` (the `D`-side atom and its paired `U`-side atom), which
doubles in length at each step — this is exactly `(■)` unpacked into `List` bookkeeping (matching
this codebase's usual idiom for finite combinatorial data, e.g. `presentedIntervals`'s own `List`
representation), avoiding `Fin`-indexed dependent recursion entirely.

**The key local step (`exists_split`)**: given one matching pair `(A, B)` and a new target `Xₙ`,
produce the two refined pairs for `A ∩ Xₙ` and `A \ Xₙ`. Remarkably, all three of Scott's cases are
handled *without* ever needing a general "`U`-neighbourhoods are closed under set difference"
lemma:

* `A ∩ Xₙ = ∅`: the new pairs are `(∅, ∅)` and `(A, B)` (unchanged) — no computation needed.
* `A \ Xₙ = ∅` (i.e. `A ⊆ Xₙ`): the new pairs are `(A, B)` (unchanged) and `(∅, ∅)`.
* otherwise (`A` is genuinely split by `Xₙ`): both `A ∩ Xₙ` and `A \ Xₙ` are non-empty, so (by the
  matching invariant on the old pair) `B` is a genuine, non-empty `U`-neighbourhood — split it via
  **Definition 8.7's `U_no_minimal`** into disjoint proper non-empty pieces `Y, Z` with `Y ∪ Z = B`;
  take `I := Y`, and `B \ I = Z` comes *for free* from `U_no_minimal`'s own conclusion, again with
  no separate set-difference-closure lemma required.

**Remaining work** (tracked in `arxiv.md`, not yet in this file): package `exists_split` into the
`List`-of-pairs recursive construction of the full sequence `Y : ℕ → Set ℚ`, derive the inclusion
correspondence `Xᵢ ⊆ Xⱼ ↔ Yᵢ ⊆ Yⱼ` from the atom invariant, and assemble the final `∃ D' : Neighbo
rhoodSystem ℚ, D ≅ᴰ D' ∧ D' ◁ U` statement. `Classical.choice` is expected and acceptable throughout
this file's `Theorem 8.8(a)` development: it is a genuinely non-constructive `Prop`-level existence
statement for an *arbitrary* countable `D` (Scott's own remark that the effective case needs the
*additional* `𝒟 ≅ 𝒟†` preparation, absent here, to make the case-splits decidable rather than merely
classical, is the substance of the follow-up Theorem 8.8(b)).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

/-- **The key local splitting step behind Theorem 8.8(a)'s back-and-forth construction.** Given a
`D`-side atom `A` matched with a `U`-side atom `B` (`A = ∅ ↔ B = ∅`, and `B` is either empty or a
genuine `U`-neighbourhood), and a new target set `Xₙ` (morally the next `D`-neighbourhood `Xₙ`),
produce matching refinements `I` (for `A ∩ Xₙ`) and `J` (for `A \ Xₙ`). -/
theorem exists_split {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) :
    ∃ I J : Set ℚ, (I = ∅ ∨ U.mem I) ∧ (J = ∅ ∨ U.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBU, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_diff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBU, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
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
      have hBU' : U.mem B := hBU.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U_no_minimal hBU'
      have hYne : Y ≠ ∅ := hY.2.1.ne_empty
      have hZne : Z ≠ ∅ := hZ.2.1.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩

end Scott1980.Neighborhood
