import Scott1980.Neighborhood.Exercise124
import Scott1980.Neighborhood.Exercise413

/-!
# Exercise 4.15 (Scott 1981, PRG-19, Lecture IV) — a maximal (and a least) fixed point

(For set theorists.) Let `f : |𝒟| → |𝒟|` be a *monotone* function on the elements of a domain. Then
`f` has a **maximal** fixed point — a fixed point that cannot be extended to a larger one — and
(consequently) a **least** fixed point.

**Maximal fixed point (Zorn).** Consider the set `S = {x ∣ x ⊑ f(x)}` of *post*-fixed points. It is
non-empty (`⊥ ∈ S`) and every chain `C ⊆ S` has an upper bound in `S`: its union `⊔C`
(Exercise 1.24's `chainUnion`, Scott's "use 2.11 to remark `⊔C ∈ |𝒟|`") is again post-fixed, since
each `x ∈ C` has `x ⊑ f(x) ⊑ f(⊔C)`. By Zorn's Lemma (`zorn_le₀`) `S` has a maximal element `m`.
Then `m` is a fixed point: `m ⊑ f(m)` (it is in `S`) and `f(m) ⊑ m` (because `f(m) ∈ S` too, by
monotonicity, and `m` is maximal). It is *maximal among fixed points*
(`exists_maximal_fixedPoint`).

**Least fixed point.** Having produced *some* fixed point `m`, we have `f(m) ⊑ m`, so Exercise
4.13(1) (the monotone-only intersection construction `monoFix`) applies and yields the *least* fixed
point `fix(f) = ⋂{x ∣ f(x) ⊑ x} ⊑ m` (`exists_least_fixedPoint`).

This is the explicitly **classical** exercise (Zorn ⟹ `Classical.choice`), exactly like Exercise
1.24; the `chainUnion` construction itself is choice-free.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- `chainUnion C` is the least upper bound of the chain: an upper bound `y` of every member
dominates it. -/
theorem chainUnion_le (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {y : V.Element} (hy : ∀ x ∈ C, x ≤ y) : V.chainUnion C hne hchain ≤ y := by
  rintro Z ⟨x, hxC, hxZ⟩
  exact hy x hxC Z hxZ

/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *maximal* fixed point:
some `m` with `f(m) = m` that admits no strictly larger fixed point. -/
theorem exists_maximal_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ m, f m = m ∧ ∀ y, f y = y → m ≤ y → y ≤ m := by
  -- Zorn on the set of post-fixed points.
  set S : Set V.Element := {x | x ≤ f x} with hS
  have ih : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ?_, fun z hz => ((Set.mem_empty_iff_false z).mp hz).elim⟩
      show (⊥ : V.Element) ≤ f ⊥
      exact _root_.bot_le
    · refine ⟨V.chainUnion c hne hchain, ?_, fun z hz => V.le_chainUnion c hne hchain hz⟩
      -- `⊔c` is post-fixed: each `x ∈ c` has `x ⊑ f x ⊑ f(⊔c)`.
      show V.chainUnion c hne hchain ≤ f (V.chainUnion c hne hchain)
      intro Z hZ
      obtain ⟨x, hxc, hxZ⟩ := hZ
      have hxle : x ≤ V.chainUnion c hne hchain := V.le_chainUnion c hne hchain hxc
      exact (le_trans (hcS hxc) (hf hxle)) Z hxZ
  obtain ⟨m, hm⟩ := zorn_le₀ S ih
  have hms : m ≤ f m := hm.1
  have hfm_le_m : f m ≤ m := hm.2 (hf hms) hms
  refine ⟨m, le_antisymm hfm_le_m hms, fun y hy hmy => hm.2 ?_ hmy⟩
  exact le_of_eq hy.symm

/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *least* fixed point.
(Having a maximal fixed point `m` gives a pre-fixed point `f(m) ⊑ m`; Exercise 4.13(1)'s `monoFix`
then constructs the least fixed point `⋂{x ∣ f(x) ⊑ x}`.) -/
theorem exists_least_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ b, f b = b ∧ ∀ y, f y = y → b ≤ y := by
  obtain ⟨m, hfm, _⟩ := exists_maximal_fixedPoint f hf
  exact ⟨monoFix f (le_of_eq hfm), monoFix_isFixed f hf (le_of_eq hfm),
    fun y hy => monoFix_least f (le_of_eq hfm) hy⟩

end NeighborhoodSystem

end Scott1980.Neighborhood
