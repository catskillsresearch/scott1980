import Mathlib.Computability.MyhillNerode

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — eventually-periodic trees and regular events

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI,
*Introduction to domain equations*. After exhibiting the generalised domain equation `A ≅ Aⁿ + Aⁿ`
(formalised in `Example62A.lean`), Scott closes Example 6.2 with a *casual aside* connecting his
infinite `±`-labelled `n`-ary trees to automata theory:

> "We say that a (total) tree `a` is *eventually periodic* iff the set `{aσ ∣ σ ∈ Σ*}` is finite.
> The result is that the 'language' `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` corresponding to an eventually
> periodic tree is always a *regular event* of automata theory, and every such language has this form.
> In fact, `a` just represents the initial state of an automaton, and `aσ` represents the state after
> 'reading' a tape `σ`."

This file makes that remark precise and *proves* it. Scott's total trees over `Σ = {0, …, n-1}` are
exactly the functions `a : Σ* → Bool` assigning a `±` label (`pos`) to every node, addressed by a
finite selector `σ ∈ Σ*`. The **subtree** operation `σ ↦ aσ` is Scott's selector recursion
`aΛ = a`, `a(iσ) = (aᵢ)σ`; its *language* `L_a` is the set of selectors landing on a `+` node.

The two halves of Scott's claim are exactly the two halves of the **Myhill–Nerode theorem**: a tree
is eventually periodic (finitely many distinct subtrees) iff its language has finitely many *left
quotients* iff (Myhill–Nerode, `Language.isRegular_iff_finite_range_leftQuotient`) the language is
regular. The bridge is that the subtree `aσ` *is* the left quotient `σ⁻¹ L_a`: reading the tape `σ`
moves the automaton to the residual language, which is precisely the subtree at `σ`.

This is a `Prop`-level result (about regularity), so `Classical.choice` is unobjectionable here; the
content is entirely the combinatorics-on-words / automata correspondence, orthogonal to the
neighbourhood-system machinery.
-/

namespace Scott1980.Neighborhood

namespace Example62Regular

open Language

variable {n : ℕ}

/-- A **total tree** over the alphabet `Σ = Fin n` (Scott's `n`-ary `±` tree): an assignment of a
`±` label (`Bool`, `true = +`) to every node, addressed by a finite selector `σ ∈ Σ*`. A tree is
*total* in Scott's sense (every node carries a genuine label), as opposed to the partial elements of
the domain `A` of `Example62A.lean` where labels may be `⊥`. -/
abbrev Tree (n : ℕ) : Type := List (Fin n) → Bool

/-- Scott's `pos : A → T`: the `±` label at the **root** of the tree (`pos(±⟨…⟩) = true/false`). -/
def pos (a : Tree n) : Bool := a []

/-- Scott's subtree selector `σ ↦ aσ`: the subtree of `a` reached by the selector `σ`. Defined so
that `(aσ)τ = a(στ)`; the `pos`-label at node `τ` of `aσ` is the label at node `στ` of `a`. -/
def select (a : Tree n) (σ : List (Fin n)) : Tree n := fun τ => a (σ ++ τ)

@[simp] theorem select_apply (a : Tree n) (σ τ : List (Fin n)) : select a σ τ = a (σ ++ τ) := rfl

/-- The `i`-th immediate subtree `aᵢ = a i` (Scott's children of the root node). -/
def child (a : Tree n) (i : Fin n) : Tree n := select a [i]

/-- **Scott's selector recursion, base case `aΛ = a`.** -/
@[simp] theorem select_nil (a : Tree n) : select a [] = a := by
  funext τ; simp

/-- **Scott's selector recursion, step `a(iσ) = (aᵢ)σ`.** Reading the digit `i` then `σ` is the same
as descending to the `i`-th child `aᵢ` and reading `σ` there. -/
theorem select_cons (a : Tree n) (i : Fin n) (σ : List (Fin n)) :
    select a (i :: σ) = select (child a i) σ := by
  funext τ; simp [child]

/-- `pos(aσ) = a σ`: the root label of the subtree at `σ` is the label `a` assigns to node `σ`. -/
@[simp] theorem pos_select (a : Tree n) (σ : List (Fin n)) : pos (select a σ) = a σ := by
  simp [pos]

/-- Composing selectors: `a(στ) = (aσ)τ`. -/
theorem select_append (a : Tree n) (σ τ : List (Fin n)) :
    select a (σ ++ τ) = select (select a σ) τ := by
  funext ρ; simp [List.append_assoc]

/-- **Scott's language of a tree.** `L_a = {σ ∈ Σ* ∣ pos(aσ) = true}` — the selectors that land on a
`+` node. Equivalently (by `pos_select`) the set of `σ` with `a σ = true`. A `Language (Fin n)` is
just a set of words over the alphabet, exactly Scott's "language". -/
def treeLang (a : Tree n) : Language (Fin n) := {σ | a σ = true}

@[simp] theorem mem_treeLang {a : Tree n} {σ : List (Fin n)} : σ ∈ treeLang a ↔ a σ = true := Iff.rfl

/-- `L_a` is genuinely `{σ ∣ pos(aσ) = true}` as Scott writes it. -/
theorem treeLang_eq_pos (a : Tree n) : treeLang a = {σ | pos (select a σ) = true} := by
  simp only [pos_select]; rfl

/-- **The subtree is the left quotient.** `L_{aσ} = σ⁻¹ L_a`: the language of the subtree reached by
reading `σ` is exactly the *left quotient* of `L_a` by `σ` (the residual / "state after reading
`σ`"). This is the heart of Scott's "`a` is the initial state, `aσ` the state after reading `σ`". -/
theorem treeLang_select (a : Tree n) (σ : List (Fin n)) :
    treeLang (select a σ) = (treeLang a).leftQuotient σ := by
  ext τ
  simp only [mem_treeLang, select_apply, Language.mem_leftQuotient]

/-- The label function recovers the tree from its language, so `treeLang` is **one-one**: two trees
with the same language are the same tree (a node's `±` label is recorded by whether its selector is
in the language). -/
theorem treeLang_injective : Function.Injective (treeLang (n := n)) := by
  intro a a' h
  funext σ
  have hmem : (σ ∈ treeLang a) ↔ (σ ∈ treeLang a') := by rw [h]
  simp only [mem_treeLang] at hmem
  cases ha : a σ <;> cases ha' : a' σ <;> simp_all

/-- **Eventual periodicity (Scott).** A tree `a` is *eventually periodic* iff the set of its subtrees
`{aσ ∣ σ ∈ Σ*}` is finite. (Equivalently — by the picture — the tree is built from finitely many
distinct subtrees, so it is "ultimately periodic" along every branch.) -/
def EventuallyPeriodic (a : Tree n) : Prop := (Set.range (select a)).Finite

/-- **Scott's closing claim, made precise (Example 6.2).** A tree's language `L_a` is a *regular
event* of automata theory **iff** the tree is eventually periodic. This is the Myhill–Nerode theorem
in disguise: the subtrees `aσ` are the left quotients `σ⁻¹ L_a` (`treeLang_select`), so "finitely many
subtrees" is "finitely many left quotients", which Myhill–Nerode equates with regularity. -/
theorem eventuallyPeriodic_iff_isRegular (a : Tree n) :
    EventuallyPeriodic a ↔ (treeLang a).IsRegular := by
  have hcomp : (treeLang a).leftQuotient = treeLang ∘ select a :=
    funext fun σ => (treeLang_select a σ).symm
  rw [Language.isRegular_iff_finite_range_leftQuotient, hcomp, Set.range_comp]
  exact (Set.finite_image_iff (treeLang_injective.injOn)).symm

/-- The inverse half of Scott's claim: **every regular event arises** as the language of an eventually
periodic tree. Concretely, take the tree whose root labels record membership in `L`; reading a tape
`σ` lands on the residual language `σ⁻¹ L`, of which there are finitely many exactly when `L` is
regular. -/
theorem isRegular_iff_exists_eventuallyPeriodic (L : Language (Fin n)) :
    L.IsRegular ↔ ∃ a : Tree n, EventuallyPeriodic a ∧ treeLang a = L := by
  classical
  constructor
  · intro hL
    refine ⟨fun σ => decide (σ ∈ L), ?_, ?_⟩
    · have hlang : treeLang (fun σ => decide (σ ∈ L)) = L := by
        ext σ; simp only [mem_treeLang, decide_eq_true_eq]
      rw [eventuallyPeriodic_iff_isRegular, hlang]; exact hL
    · ext σ; simp only [mem_treeLang, decide_eq_true_eq]
  · rintro ⟨a, hEP, rfl⟩
    exact (eventuallyPeriodic_iff_isRegular a).mp hEP

end Example62Regular

end Scott1980.Neighborhood
