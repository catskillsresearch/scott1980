import Scott1980.Neighborhood.Basic
import Scott1980.Neighborhood.Exercise315
import Scott1980.Neighborhood.Recursive

/-!
# Definition 7.1 (Scott 1981, PRG-19, §7) — computable presentations / effectively given domains

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII,
*Computability in effectively given domains*.

Scott's idea: the *finite elements* of `|𝒟|` are the ones initially known, and to know a finite
element is to know how it is **related** to the other finite elements. As finite elements are in
one-one correspondence with neighbourhoods (Definition 1.7), the data reduces to *recursive
calculations with neighbourhoods*. This forces at most a countable infinity of neighbourhoods.

> **Definition 7.1.** A neighbourhood system `𝒟` has a *computable presentation* provided we can
> write `𝒟 = {Xₙ ∣ n ∈ ℕ}`, where the two relations
>
> * (i)  `Xₙ ∩ Xₘ = X_k`, and
> * (ii) `∃ k. X_k ⊆ Xₙ and X_k ⊆ Xₘ`
>
> are recursively decidable (in `n, m, k` and in `n, m` respectively).

**Recursion theory: we roll our own and reject Mathlib here.** "Recursively decidable" is modelled by
`Domain.Recursive.RecDecidable` — the existence of a primitive-recursive `{0,1}`-valued
characteristic function, with tuples coded by `Nat.pair`. We deliberately do **not** use Mathlib's
recursion theory (`ComputablePred` / `Primrec` / `Partrec`): in Mathlib `v4.30.0` essentially all of
its *correctness lemmas* are proved with `grind`/`lia` or the `@[simp]` lemma `Nat.unpair_pair`,
which **open `Classical`**, so they audit with `Classical.choice`. This project's discipline is to
keep constructions choice-free (`⊆ {propext, Quot.sound}`), so we rebuilt the slice of recursion
theory we need (choice-free `Nat.sqrt` correctness, the `Nat.pair`/`unpair` round-trips, and
primitive-recursive `id`/`+`/`*`) in `Domain/Neighborhood/Recursive.lean`. Relation (i) is the
ternary `interEq` predicate (`RecDecidable₃`); relation (ii) is the binary consistency predicate
(`RecDecidable₂`). The enumeration `X` is the only *data* the structure carries (a plain
`ℕ → Set α`), so building a presentation stays choice-free.

The intuitive content (Scott's prose): (i) lets us *locate* the intersection of two neighbourhoods
in the standard list, and (ii) is the *consistency condition* — the necessary and sufficient
condition for the intersection to exist in `𝒟`. Scott immediately remarks the biconditional
`Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`, which makes the **inclusion** relation decidable from (i); we record this
as `ComputablePresentation.incl_computable`, and equality of neighbourhoods as `eq_computable`.

A neighbourhood system is *effectively given* when it admits such a presentation
(`NeighborhoodSystem.IsEffectivelyGiven`). The one-point system `𝟙` is the sanity inhabitant
(`unitSys_isEffectivelyGiven`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

/-- **Definition 7.1 (Scott 1981, PRG-19).** A *computable presentation* of a neighbourhood system
`V` over a token type `α`: an enumeration `X : ℕ → Set α` whose range is exactly `𝒟` (`mem_X` and
`surj`), such that Scott's two relations on the integer indices are recursively decidable:

* `interEq_computable` is (i): the ternary relation `Xₙ ∩ Xₘ = X_k`;
* `cons_computable` is (ii): the binary consistency relation `∃ k. X_k ⊆ Xₙ ∩ Xₘ`
  (Scott's `X_k ⊆ Xₙ and X_k ⊆ Xₘ`).

Only the enumeration `X` is data; the remaining fields are `Prop`s, so a presentation is built
choice-free. -/
structure ComputablePresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`: every neighbourhood appears as some `Xₙ`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(i)** — `Xₙ ∩ Xₘ = X_k` is recursively decidable in `n, m, k`. -/
  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)
  /-- A **primitive-recursive intersection function**: an index of `Xₙ ∩ Xₘ` whenever that
  intersection is a neighbourhood (i.e. consistent). This makes explicit the operation that 7.1(i)
  is *about*: in Scott's general-recursive reading of "recursively decidable" the index can be
  recovered from `interEq_computable` by an (unbounded) search `μk. Xₙ ∩ Xₘ = X_k`, but that search
  is not *primitive* recursive; for the function-space presentation (Theorem 7.5) we need to
  *form* component intersections primitively, so we carry the function as part of the data of an
  ("acceptable") computable presentation. Off the consistent domain `inter n m` may be junk. -/
  inter : ℕ → ℕ → ℕ
  /-- The intersection function is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  inter_primrec : Nat.Primrec (fun t => inter t.unpair.1 t.unpair.2)
  /-- `inter n m` indexes `Xₙ ∩ Xₘ` whenever that intersection is consistent. -/
  inter_spec : ∀ {n m : ℕ}, (∃ k, X k ⊆ X n ∩ X m) → X (inter n m) = X n ∩ X m
  /-- A fixed index of the master neighbourhood `Δ` (used to seed finite intersections). -/
  masterIdx : ℕ
  /-- `X masterIdx = Δ`. -/
  masterIdx_spec : X masterIdx = V.master

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- Reindexing `(n, m) ↦ (n, m, n)` on `Nat.pair` codes: `t ↦ pair n (pair m n)`. -/
private def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

private theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)

/-- Swap the two components of a `Nat.pair` code: `t ↦ pair m n`. -/
private def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

/-- **Scott's biconditional after 7.1.** "The inclusion relation between neighbourhoods is itself
decidable in terms of the indices", because `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. We obtain the decision by
reindexing `(n, m) ↦ (n, m, n)` into relation (i). -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

/-- **Equality of neighbourhoods is decidable** from the indices: `Xₙ = Xₘ ↔ Xₙ ⊆ Xₘ ∧ Xₘ ⊆ Xₙ`,
so equality is the conjunction of `incl_computable` with its swap. -/
theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff

end ComputablePresentation

/-- **Definition 7.1 (Scott 1981, PRG-19) — effectively given.** A neighbourhood system is
*effectively given* when it admits a computable presentation. -/
def NeighborhoodSystem.IsEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ComputablePresentation V)

/-! ### Sanity inhabitant: the one-point domain `𝟙` is effectively given. -/

/-- The trivial presentation of the one-point system `𝟙 = unitSys`: the constant enumeration
`Xₙ = Δ = univ`. Both of Scott's relations are *always true* here (any two neighbourhoods are equal
and consistent), hence trivially recursively decidable via the constant `1` decider. -/
def unitPresentation : ComputablePresentation unitSys where
  X _ := Set.univ
  mem_X _ := rfl
  surj := by rintro Y rfl; exact ⟨0, rfl⟩
  interEq_computable := recDecidable_of_forall fun _ => Set.inter_self Set.univ
  cons_computable := recDecidable_of_forall fun _ =>
    ⟨0, by rw [Set.inter_self]⟩
  inter _ _ := 0
  inter_primrec := Nat.Primrec.zero
  inter_spec _ := by rw [Set.inter_self]
  masterIdx := 0
  masterIdx_spec := rfl

/-- **The one-point domain `𝟙` is effectively given.** -/
theorem unitSys_isEffectivelyGiven : unitSys.IsEffectivelyGiven :=
  ⟨unitPresentation⟩

end Scott1980.Neighborhood
