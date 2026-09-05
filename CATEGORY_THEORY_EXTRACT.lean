/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980

Self-contained extract of the category-theory spine of this formalization
(Scott Defs 6.3–6.5, Props 6.6–6.7, Defs 6.8/6.13, Thms 6.9/6.14/6.16,
cartesian closed structure, and the concrete initial-algebra examples).
Only Mathlib is imported; every Scott1980 dependency is inlined below.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Set
import Mathlib.Data.Set.Image
import Mathlib.Tactic
import Mathlib.Data.List.Infix
import Mathlib.Topology.Inseparable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Directed
import Mathlib.Data.Set.Insert


/-! ### Inlined from Scott1980/Neighborhood/Basic.lean -/

/-!
# Neighborhood systems (Scott 1981, PRG-19, §1) — foundations

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, Technical
Monograph PRG-19, Oxford (May 1981), Lecture I, *Domains given by neighbourhoods*.

Scott fixes a non-empty set `Δ` of *tokens* and considers a family `𝒟` of subsets of `Δ`
(the *neighbourhoods*). The order is *reversed* relative to information: a **smaller**
neighbourhood carries **more** information. A finite sequence of neighbourhoods is
*consistent* when it has a common lower bound inside `𝒟` (a `Z ∈ 𝒟` contained in all of
them); a neighbourhood system is closed under intersections of consistent finite sequences.

This file formalizes the very first page of §1:

* **Definition 1.1** — `NeighborhoodSystem`: a family with `Δ ∈ 𝒟` (condition (i)) and
  closure under consistent binary intersections (condition (ii)).
* **Factoid 1.1a / 1.1b** — Scott's recursive *convention* for the finite intersection
  `⋂_{i < n} Xᵢ` (`interUpTo`): the empty intersection is `Δ`, and the `(n+1)`-fold
  intersection peels off the last factor.
* **Theorem 1.1c** — "from (ii) we can extend the intersection property to any finite
  sequence", and *consequently* a finite sequence is consistent **iff** its intersection
  lies in `𝒟`.

The §1 core is deliberately **constructive**: Scott uses *partial* filters so that the
basic theory avoids maximal-filter existence (Zorn/choice). Every theorem here depends only
on `propext`/`Quot.sound` (no `Classical.choice`).
-/

namespace Scott1980.Neighborhood

/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a token type
`α`. `mem X` means "`X` is a neighbourhood" (`X ∈ 𝒟`), and `master` is Scott's least
informative neighbourhood `Δ` (the whole token set, "ask me no questions").

The two conditions are exactly Scott's:

* (i)  `Δ ∈ 𝒟`                                        — `master_mem`;
* (ii) whenever `X, Y, Z ∈ 𝒟` and `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟` — `inter_mem`.

We keep `master` as a field (rather than hard-wiring `Set.univ`) to stay faithful to
Scott's `Δ` notation, and record Scott's standing assumption `𝒟 ⊆ 𝒫(Δ)` as the field
`sub_master` (every neighbourhood is a subset of `Δ`). Scott also assumes from the outset
that the token set `Δ` is non-empty; `master_nonempty` records this standing assumption
explicitly. The subset condition is what makes the principal filter `↑X` (Definition 1.7)
contain `Δ`, and underlies the least element `⊥ = ↑Δ`. -/
structure NeighborhoodSystem (α : Type*) where
  /-- `mem X` holds iff `X` is a neighbourhood of the system (`X ∈ 𝒟`). -/
  mem : Set α → Prop
  /-- Scott's distinguished least-informative neighbourhood `Δ`. -/
  master : Set α
  /-- Scott's standing assumption that the token set `Δ` is non-empty. -/
  master_nonempty : master.Nonempty
  /-- (i) `Δ ∈ 𝒟`. -/
  master_mem : mem master
  /-- (ii) Closure under intersection of a *consistent* pair: if `X, Y, Z ∈ 𝒟` with the
  witness `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟`. -/
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  /-- Scott's `𝒟 ⊆ 𝒫(Δ)`: every neighbourhood is a subset of the master neighbourhood `Δ`. -/
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

/-- Scott's *"very special circumstance"* (the prose after Examples 1.2–1.4): a family `𝒟`
is **nested-or-disjoint** when any two of its members are either nested (one included in the
other) or disjoint. -/
def NestedOrDisjoint {α : Type*} (mem : Set α → Prop) : Prop :=
  ∀ ⦃X Y : Set α⦄, mem X → mem Y → X ⊆ Y ∨ Y ⊆ X ∨ X ∩ Y = ∅

/-- **Factoid 1.4a (Scott 1981, PRG-19).** "In these systems two neighbourhoods are either
disjoint or one is included in the other": a family containing `Δ` whose members are pairwise
nested-or-disjoint **is** a neighbourhood system. This uniformly explains why Examples 1.2,
1.3 and 1.4 satisfy Definition 1.1.

The verification of condition (ii) needs no choice: if `X, Y` are nested then `X ∩ Y` is the
smaller (already in `𝒟`); if they are disjoint then the consistency witness `Z ⊆ X ∩ Y = ∅`
forces `Z = ∅`, whence `X ∩ Y = ∅ = Z ∈ 𝒟`. The caller supplies `master_nonempty`
(Scott's standing `Δ ≠ ∅` assumption) and `sub_master` (`𝒟 ⊆ 𝒫(Δ)`) directly. -/
def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases hnd hX hY with h | h | h
    · rwa [Set.inter_eq_left.mpr h]
    · rwa [Set.inter_eq_right.mpr h]
    · rw [h]
      rw [h] at hZsub
      rwa [← Set.subset_empty_iff.mp hZsub]

/-- **Exercise 1.19 (Scott 1981, PRG-19) — positivity, condition (ii′).** A neighbourhood
system is *positive* when Scott's (ii) is strengthened to the biconditional **(ii′)**: for
`X, Y ∈ 𝒟`, the intersection `X ∩ Y` is a neighbourhood **iff** it is non-empty. -/
def NeighborhoodSystem.IsPositive {α : Type*} (V : NeighborhoodSystem α) : Prop :=
  ∀ ⦃X Y : Set α⦄, V.mem X → V.mem Y → (V.mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)

/-- **Exercise 1.19 — a positive system is a neighbourhood system.** Scott: "*prove that a
positive neighbourhood system is indeed a neighbourhood system*". From the raw data — (i)
`Δ ∈ 𝒟`, `𝒟 ⊆ 𝒫(Δ)`, and the positivity axiom (ii′) — condition (ii) follows: a consistency
witness `Z ⊆ X ∩ Y` with `Z ∈ 𝒟` is itself non-empty (apply (ii′) to `Z ∩ Z = Z`), so
`X ∩ Y ⊇ Z` is non-empty, whence `X ∩ Y ∈ 𝒟` by (ii′). Choice-free. -/
def NeighborhoodSystem.ofPositive {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hZZ : mem (Z ∩ Z) := by rwa [Set.inter_self]
    have hZne : (Z ∩ Z).Nonempty := (pos hZ hZ).mp hZZ
    rw [Set.inter_self] at hZne
    exact (pos hX hY).mpr (hZne.mono hZsub)

/-- The system built by `ofPositive` is indeed positive. -/
theorem NeighborhoodSystem.ofPositive_isPositive {α : Type*} (mem : Set α → Prop)
    (master : Set α) (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_nonempty master_mem sub_master pos).IsPositive :=
  pos

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection `⋂_{i < n} Xᵢ` of the first `n` terms of a sequence of
neighbourhoods, defined by Scott's recursive convention (**Factoid 1.1a / 1.1b**):

* `n = 0` : the empty intersection is `Δ` (`master`);
* `n + 1` : `(⋂_{i < n} Xᵢ) ∩ Xₙ`.

(See `interUpTo_zero` and `interUpTo_succ` for the two defining equations as lemmas.) -/
def interUpTo (V : NeighborhoodSystem α) (X : ℕ → Set α) : ℕ → Set α
  | 0 => V.master
  | (n + 1) => interUpTo V X n ∩ X n

/-- **Factoid 1.1a.** The intersection of the empty sequence of neighbourhoods is `Δ`:
`⋂_{i < 0} Xᵢ = Δ`. -/
@[simp] theorem interUpTo_zero (X : ℕ → Set α) : V.interUpTo X 0 = V.master := rfl

/-- **Factoid 1.1b.** The intersection of the first `n + 1` neighbourhoods peels off the
last factor: `⋂_{i < n+1} Xᵢ = (⋂_{i < n} Xᵢ) ∩ Xₙ`. -/
@[simp] theorem interUpTo_succ (X : ℕ → Set α) (n : ℕ) :
    V.interUpTo X (n + 1) = V.interUpTo X n ∩ X n := rfl

/-- The finite intersection is contained in each of its factors: `⋂_{i < n} Xᵢ ⊆ Xⱼ` for
`j < n`. (Supporting lemma: this is what makes `⋂_{i < n} Xᵢ` a common lower bound of the
sequence, the intuition behind consistency.) -/
theorem interUpTo_subset (X : ℕ → Set α) :
    ∀ {n j : ℕ}, j < n → V.interUpTo X n ⊆ X j := by
  intro n
  induction n with
  | zero => intro j h; exact absurd h (Nat.not_lt_zero j)
  | succ n ih =>
    intro j h
    rw [interUpTo_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · subst h'; exact Set.inter_subset_right
    · exact Set.inter_subset_left.trans (ih h')

/-- A finite sequence `X₀, …, Xₙ₋₁` of neighbourhoods is *consistent in* `𝒟` when it has a
common lower bound inside `𝒟`: some `Z ∈ 𝒟` contained in the intersection `⋂_{i < n} Xᵢ`
(equivalently, contained in every `Xⱼ`, `j < n`). This is Scott's notion of consistency,
generalized from pairs to finite sequences. -/
def Consistent (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∃ Z, V.mem Z ∧ Z ⊆ V.interUpTo X n

/-- **Theorem 1.1c (extension of the intersection property).** Scott: "from (ii), we can
extend the intersection property to any finite sequence." If `Xᵢ ∈ 𝒟` for every `i < n`
and the sequence is consistent, then the finite intersection `⋂_{i < n} Xᵢ` is again a
neighbourhood (`∈ 𝒟`). Proved by induction on `n`; the inductive step is one application of
condition (ii). -/
theorem interUpTo_mem (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → V.mem (X i)) → V.Consistent X n →
      V.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _ _; exact V.master_mem
  | succ n ih =>
    intro hX hcons
    obtain ⟨Z, hZmem, hZsub⟩ := hcons
    have hZsub' : Z ⊆ V.interUpTo X n ∩ X n := by rwa [interUpTo_succ] at hZsub
    -- The same witness `Z` shows the length-`n` prefix is consistent.
    have hconsn : V.Consistent X n :=
      ⟨Z, hZmem, hZsub'.trans Set.inter_subset_left⟩
    have hmemn : V.mem (V.interUpTo X n) :=
      ih (fun i hi => hX i (Nat.lt_succ_of_lt hi)) hconsn
    have hXn : V.mem (X n) := hX n (Nat.lt_succ_self n)
    rw [interUpTo_succ]
    exact V.inter_mem hmemn hXn hZmem hZsub'

/-- **Theorem 1.1c (consistency characterization).** "Consequently, `X₀, …, Xₙ₋₁` is
consistent in `𝒟` iff `⋂_{i < n} Xᵢ ∈ 𝒟`." (Given `Xᵢ ∈ 𝒟` for all `i < n`.)

* `→` is the extension property `interUpTo_mem`;
* `←` is immediate: the intersection is its own common lower bound. -/
theorem consistent_iff_interUpTo_mem (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ V.mem (V.interUpTo X n) := by
  constructor
  · exact V.interUpTo_mem X hX
  · intro h; exact ⟨V.interUpTo X n, h, Set.Subset.refl _⟩

/-- **Definition 1.6 (Scott 1981, PRG-19).** An (ideal) *element* of a neighbourhood system:
a subfamily `x ⊆ 𝒟` that is a *filter* — (i) `Δ ∈ x`, (ii) closed under intersection, (iii)
upward closed within `𝒟`. The domain is the type `Element` of all such filters, ordered by
inclusion. -/
structure Element where
  /-- `mem X` holds iff the neighbourhood `X` belongs to the filter `x`. -/
  mem : Set α → Prop
  /-- `x` is a subfamily of `𝒟`. -/
  sub : ∀ {X}, mem X → V.mem X
  /-- (i) `Δ ∈ x`. -/
  master_mem : mem V.master
  /-- (ii) `X, Y ∈ x ⟹ X ∩ Y ∈ x`. -/
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  /-- (iii) `X ∈ x` and `X ⊆ Y ∈ 𝒟 ⟹ Y ∈ x`. -/
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

/-- Two elements with the same membership predicate are equal (the remaining fields are `Prop`s). -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

/-- A filter (`Element`) is closed under the finite intersection `⋂_{i<n} Xᵢ`: if every factor
`Xᵢ` (`i < n`) lies in the filter `x`, so does `interUpTo X n`. Used in Exercises 1.18 and 1.21.
Base case `x.master_mem`; inductive step one `x.inter_mem`. -/
theorem Element.mem_interUpTo {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → x.mem (X i)) → x.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _; exact x.master_mem
  | succ n ih =>
    intro h
    rw [interUpTo_succ]
    exact x.inter_mem (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- Membership of the finite intersection in a filter, as a biconditional (given all factors
are neighbourhoods). `→` is upward closure along `interUpTo X n ⊆ Xᵢ` (`interUpTo_subset`); `←`
is `Element.mem_interUpTo`. -/
theorem Element.mem_interUpTo_iff {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) {n : ℕ} (hX : ∀ i, i < n → V.mem (X i)) :
    x.mem (V.interUpTo X n) ↔ ∀ i, i < n → x.mem (X i) := by
  constructor
  · intro h i hi
    exact x.up_mem h (hX i hi) (V.interUpTo_subset X hi)
  · exact x.mem_interUpTo X

/-- Filter-inclusion order on elements (Scott's approximation order, Definition 1.8).
Named so Palomar can lock the `PartialOrder` relation without inlining it. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

/-- Reflexivity of the filter-inclusion order. Named so Palomar can lock the
`PartialOrder` instance without a generated `._proof_N`. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

/-- The **limit family** of a sequence of neighbourhoods (Scott, the prose before Definition
1.6): `x = {Z ∈ 𝒟 ∣ Xₙ ⊆ Z for some n}` — the family of all neighbourhoods eventually reached
by `⟨Xₙ⟩`. This is the construction Scott uses to motivate the (ideal) elements of `|𝒟|`. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}

/-- Two sequences of neighbourhoods are **equivalent** ("each goes equally deep as the other"):
for every `Yₘ` some `Xₙ ⊆ Yₘ`, and for every `Xₙ` some `Yₘ ⊆ Xₙ`. -/
def SeqEquiv (X Y : ℕ → Set α) : Prop :=
  (∀ m, ∃ n, X n ⊆ Y m) ∧ (∀ n, ∃ m, Y m ⊆ X n)

/-- **Factoid 1.5b (Scott 1981, PRG-19).** "It is easy to prove that … the two families are
*equal* if and only if the sequences are *equivalent*." Given that every term of each sequence
is a neighbourhood, the limit families coincide exactly when the sequences are equivalent. -/
theorem limitFamily_eq_iff (X Y : ℕ → Set α)
    (hX : ∀ n, V.mem (X n)) (hY : ∀ m, V.mem (Y m)) :
    V.limitFamily X = V.limitFamily Y ↔ SeqEquiv X Y := by
  constructor
  · intro hEq
    refine ⟨fun m => ?_, fun n => ?_⟩
    · have hmem : Y m ∈ V.limitFamily Y := ⟨hY m, m, subset_rfl⟩
      rw [← hEq] at hmem
      obtain ⟨_, n, hn⟩ := hmem
      exact ⟨n, hn⟩
    · have hmem : X n ∈ V.limitFamily X := ⟨hX n, n, subset_rfl⟩
      rw [hEq] at hmem
      obtain ⟨_, m, hm⟩ := hmem
      exact ⟨m, hm⟩
  · rintro ⟨h1, h2⟩
    apply Set.ext
    intro Z
    constructor
    · rintro ⟨hZ, n, hn⟩
      obtain ⟨m, hm⟩ := h2 n
      exact ⟨hZ, m, hm.trans hn⟩
    · rintro ⟨hZ, m, hm⟩
      obtain ⟨n, hn⟩ := h1 m
      exact ⟨hZ, n, hn.trans hm⟩

/-- **Definition 1.7 (Scott 1981, PRG-19).** The *principal filter* `↑X` determined by a
neighbourhood `X ∈ 𝒟`:

`↑X = {Y ∈ 𝒟 ∣ X ⊆ Y}`.

These are Scott's *finite elements* of `|𝒟|`. The four filter conditions:

* `sub` is the first projection (`Y ∈ ↑X ⟹ Y ∈ 𝒟`);
* `master_mem` needs `X ⊆ Δ`, supplied by `V.sub_master` (Scott's `𝒟 ⊆ 𝒫(Δ)`);
* `inter_mem` uses `Set.subset_inter` (from `X ⊆ Y₁`, `X ⊆ Y₂`) with `X` itself as the
  consistency witness for `V.inter_mem`;
* `up_mem` is transitivity of `⊆`. -/
def principal {X : Set α} (hX : V.mem X) : V.Element where
  mem Y := V.mem Y ∧ X ⊆ Y
  sub h := h.1
  master_mem := ⟨V.master_mem, V.sub_master hX⟩
  inter_mem h1 h2 :=
    ⟨V.inter_mem h1.1 h2.1 hX (Set.subset_inter h1.2 h2.2), Set.subset_inter h1.2 h2.2⟩
  up_mem h hY hsub := ⟨hY, h.2.trans hsub⟩

@[simp] theorem mem_principal {X Y : Set α} (hX : V.mem X) :
    (V.principal hX).mem Y ↔ V.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **Factoid 1.7a (Scott 1981, PRG-19) — inclusion-*reversing*.** "It is obvious that the
correspondence between `X` and `↑X` is one-one and inclusion *reversing*." The order on `↑`:
`↑X ⊑ ↑Y ↔ Y ⊆ X` (equivalently Scott's `X ⊆ Y ↔ ↑Y ⊑ ↑X`).

`→` tests at `Z = X` (`X ∈ ↑X` since `X ⊆ X`), reading off `Y ⊆ X` from `X ∈ ↑Y`; `←` chains
`Y ⊆ X ⊆ Z`. -/
theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

/-- **Factoid 1.7a (Scott 1981, PRG-19) — one-one.** The correspondence `X ↦ ↑X` is injective:
`↑X = ↑Y ⟹ X = Y`. Antisymmetry applied to `principal_le_iff` in both directions. -/
theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

/-- **Factoid 1.7b (Scott 1981, PRG-19).** "It is also obvious from the definitions that for each
`x ∈ |𝒟|`, `x = ⋃ {↑X ∣ X ∈ x}`." In membership form (the union over a `Set (Set α)` made
concrete): a neighbourhood `Z` is in `x` iff `Z` lies in the principal filter `↑X` of *some*
member `X` of `x`.

`→` uses `X = Z` (`Z ∈ ↑Z` as `Z ⊆ Z`); `←` is upward closure `up_mem` (`X ⊆ Z`, `Z ∈ 𝒟`). -/
theorem eq_iUnion_principal (x : V.Element) {Z : Set α} :
    x.mem Z ↔ ∃ X, ∃ hX : x.mem X, (V.principal (x.sub hX)).mem Z := by
  constructor
  · intro hZ
    exact ⟨Z, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨X, hX, hVZ, hXZ⟩
    exact x.up_mem hX hVZ hXZ

/-- **Definition 1.8 (Scott 1981, PRG-19) — `⊥`.** The least defined element `⊥ = {Δ}`,
"read: *bottom*". It is the principal filter of the master neighbourhood `Δ`: `⊥ = ↑Δ`. -/
def bot : V.Element := V.principal V.master_mem

/-- **Definition 1.8 — `⊥ = {Δ}` literally.** Scott's `⊥` is the *singleton* `{Δ}`: a
neighbourhood `Y` belongs to `⊥` iff `Y = Δ`.

`→`: `Y ∈ ⊥ = ↑Δ` gives `Y ∈ 𝒟` and `Δ ⊆ Y`; `V.sub_master` gives the reverse `Y ⊆ Δ`, so
`Y = Δ` by antisymmetry. `←`: `Δ ∈ 𝒟` and `Δ ⊆ Δ`. -/
@[simp] theorem mem_bot {Y : Set α} : V.bot.mem Y ↔ Y = V.master := by
  constructor
  · rintro ⟨hY, hΔY⟩
    exact Set.Subset.antisymm (V.sub_master hY) hΔY
  · rintro rfl
    exact ⟨V.master_mem, subset_rfl⟩

/-- **Factoid 1.8a (Scott 1981, PRG-19).** "The element that approximates all others, `{Δ}`,
is called `⊥`": `⊥` is the least element of `|𝒟|`, `⊥ ⊑ x` for every `x`.

Given `Y ∈ ⊥`, i.e. `Y = Δ`, membership `Δ ∈ x` is filter condition (i) (`x.master_mem`). -/
theorem bot_le (x : V.Element) : V.bot ≤ x := by
  intro Y hY
  rw [mem_bot] at hY
  subst hY
  exact x.master_mem

/-- **Factoid 1.8a, packaged.** `⊥` is an `OrderBot` for the approximation order, so the `⊥`
notation refers to `{Δ}`. Constructive (`bot_le` is `[propext, Quot.sound]`). -/
instance : OrderBot V.Element where
  bot := V.bot
  bot_le := V.bot_le

/-- **Definition 1.8 (Scott 1981, PRG-19) — *total* elements.** "Elements maximal with respect
to the approximation relation are called *total elements*." `x` is total iff it is maximal: any
`y` it approximates approximates it back. This is the *predicate* only; the *existence* of total
elements above a given `x` (Exercise 1.24) is choice-dependent and out of scope here. -/
def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x

/-- **Factoid 1.8b (Scott 1981, PRG-19) — "Examples 1.2–1.5 revisited".** "Any explicitly given
filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." Stated honestly: if
the filter `x` has a `⊆`-minimum member `X` (one contained in every member of `x`), then `x` is
exactly the principal filter `↑X`. In a *finite* system every filter has such a minimum (the
intersection of its finitely many members, itself in `x` by closure), so every element is
principal; that finiteness step is the only classical ingredient and is left implicit here — this
constructive core captures the content.

`⊆`: any `Z ∈ x` satisfies `X ⊆ Z` by minimality, so `Z ∈ ↑X`. `⊇`: `Z ∈ ↑X` means `Z ∈ 𝒟` and
`X ⊆ Z`, so `Z ∈ x` by upward closure from `X ∈ x`. -/
theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem

/-- **Definition 1.9 (Scott 1981, PRG-19).** Two neighbourhood systems `𝒟₀` and `𝒟₁` (over possibly
*different* token types) *determine isomorphic domains* iff there is a one-one, inclusion-preserving
correspondence between `|𝒟₀|` and `|𝒟₁|`. We package "one-one + preserves inclusion (both ways)" as
mathlib's order-isomorphism `≃o`: an `OrderIso` is automatically a bijection that *reflects* as well
as preserves `⊑` (`map_rel_iff`), which is exactly Scott's requirement. -/
abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

/-- Scott's `𝒟₀ ≅ 𝒟₁`: the domains are isomorphic (there *exists* a `DomainIso`). -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

/-- `≅ᴰ` is reflexive (`OrderIso.refl`). -/
theorem Isomorphic.refl {α : Type*} (V : NeighborhoodSystem α) : V ≅ᴰ V :=
  ⟨OrderIso.refl _⟩

/-- `≅ᴰ` is symmetric (`OrderIso.symm`). -/
theorem Isomorphic.symm {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h : V₀ ≅ᴰ V₁) : V₁ ≅ᴰ V₀ :=
  h.elim fun e => ⟨e.symm⟩

/-- `≅ᴰ` is transitive (`OrderIso.trans`). -/
theorem Isomorphic.trans {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} (h₀ : V₀ ≅ᴰ V₁) (h₁ : V₁ ≅ᴰ V₂) : V₀ ≅ᴰ V₂ :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨e₀.trans e₁⟩

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Approximable.lean -/

/-!
# Lecture II (§2) — approximable mappings: Definitions 2.1, 2.2 and Theorems 2.5–2.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture II,
*Approximable mappings*. A mapping of domains that "preserves the spirit of approximation" is given
not by a function on ideal elements but by a **relation between neighbourhoods**: `X f Y` reads "if
the input is approximated at least as well as by `X`, then the output is approximated at least as
well as by `Y`."

This file formalizes the §2 core:

* **Definition 2.1** — `ApproximableMap V₀ V₁`: a relation `f ⊆ 𝒟₀ × 𝒟₁` with
  (i) `Δ₀ f Δ₁` (`master_rel`),
  (ii) `X f Y → X f Y' → X f (Y ∩ Y')` (`inter_right`, the consistency/intersectivity condition),
  (iii) `X f Y → X' ⊆ X → Y ⊆ Y' → X' f Y'` (`mono`, monotonicity: sharper input, blunter output).
  We carry `rel_dom`/`rel_cod` recording `f ⊆ 𝒟₀ × 𝒟₁`.
* **Proposition 2.2** — every approximable mapping determines an elementwise function
  `toElementMap f : |𝒟₀| → |𝒟₁|`, `f(x) = {Y ∣ ∃ X ∈ x, X f Y}`, which is a filter (i)–(iii) are
  *all* used); the relation is recovered by `rel_iff_mem_principal` (`X f Y ↔ Y ∈ f(↑X)`); the map
  is monotone (`toElementMap_mono`); and two approximable maps are equal iff they induce the same
  elementwise map (`ext_of_toElementMap`).
* **Theorem 2.5** — neighbourhood systems and approximable maps form a **category**: identity
  `idMap` (`X I_D Y ↔ X ⊆ Y`), composition `comp g f` (`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`), with the
  identity laws `idMap_comp`/`comp_idMap` and associativity `comp_assoc`.
* **Proposition 2.6** — the elementwise action is a **functor** to sets and functions:
  `toElementMap_idMap` (`I_D(x) = x`) and `toElementMap_comp` (`(g∘f)(x) = g(f(x))`).
* **Theorem 2.7** — every domain **isomorphism** `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9) comes from an
  approximable map: `ofIso e` with `toElementMap_ofIso` (`(ofIso e)(x) = e(x)`), packaged as
  `exists_approximable_of_iso`; moreover `e` carries finite (principal) elements to finite elements
  (`exists_principal_eq_apply_principal`), via the directed-union construction `sSupDirected`.

Everything in this file is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the only
classical lemma is `ext_of_toElementMap`, which decides neighbourhood membership by `by_cases`
(`Classical.em`). -/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem

/-- **Directed union of filters.** The union `⋃ S = {Z ∣ ∃ s ∈ S, Z ∈ s}` of a *non-empty directed*
family `S` of elements (any two members have an upper bound in `S`) is again an element. The only
non-trivial law is `inter_mem`: given `Z ∈ a` and `Z' ∈ b`, an upper bound `c ⊇ a, b` contains both,
hence `Z ∩ Z' ∈ c`. (Generalizes `chainUnion` of Exercise 1.24 from chains to directed sets; this is
the construction behind Exercise 2.11 and Scott's finiteness argument in Theorem 2.7.) -/
def sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) : V.Element where
  mem Z := ∃ s ∈ S, s.mem Z
  sub := fun ⟨s, _, hs⟩ => s.sub hs
  master_mem := by obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, s.master_mem⟩
  inter_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ ⟨b, hbS, hbZ⟩
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a haS b hbS
    exact ⟨c, hcS, c.inter_mem (hac Z haZ) (hbc Z' hbZ)⟩
  up_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ hZ' hZZ'
    exact ⟨a, haS, a.up_mem haZ hZ' hZZ'⟩

/-- Each member of a directed family approximates the directed union. -/
theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

/-- The directed union is the least upper bound: an upper bound of every member dominates it. -/
theorem sSupDirected_le (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {y : V.Element}
    (hy : ∀ s ∈ S, s ≤ y) : V.sSupDirected S hne hdir ≤ y := by
  rintro Z ⟨s, hs, hsZ⟩
  exact hy s hs Z hsZ

end NeighborhoodSystem

/-- **Definition 2.1 (Scott 1981, PRG-19).** An *approximable mapping* `f : 𝒟₀ → 𝒟₁` is a relation
`rel` between neighbourhoods (`rel X Y`, Scott's `X f Y`) confined to `𝒟₀ × 𝒟₁` and satisfying
Scott's three conditions:

* (i)   `Δ₀ f Δ₁`                                   — `master_rel`;
* (ii)  `X f Y` and `X f Y'` imply `X f (Y ∩ Y')`   — `inter_right`;
* (iii) `X f Y`, `X' ⊆ X`, `Y ⊆ Y'` imply `X' f Y'` — `mono` (the targets `X'`, `Y'` must be
  neighbourhoods, as Scott's relation lives on `𝒟₀ × 𝒟₁`). -/
structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where
  /-- The underlying neighbourhood relation `X f Y`. -/
  rel : Set α → Set β → Prop
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (domain side): related inputs are neighbourhoods. -/
  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (codomain side): related outputs are neighbourhoods. -/
  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y
  /-- (i) `Δ₀ f Δ₁`. -/
  master_rel : rel V₀.master V₁.master
  /-- (ii) intersectivity on the output: `X f Y → X f Y' → X f (Y ∩ Y')`. -/
  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')
  /-- (iii) monotonicity: a sharper input `X' ⊆ X` with a blunter output `Y ⊆ Y'` is still related,
  provided `X'`, `Y'` are neighbourhoods. -/
  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Extensionality for the relation.** Two approximable maps with the same neighbourhood relation
are equal (the remaining fields are propositions). -/
theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

/-- **Proposition 2.2(i) (Scott 1981, PRG-19).** The elementwise function determined by an
approximable mapping: `f(x) = {Y ∈ 𝒟₁ ∣ ∃ X ∈ x, X f Y}`. The four filter laws use *all* of
Definition 2.1: `master_mem` uses (i); `inter_mem` uses (ii) together with (iii) (to pull both
outputs back along the common input `X ∩ X'`); `up_mem` uses (iii). -/
def toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) : V₁.Element where
  mem Y := ∃ X, x.mem X ∧ f.rel X Y
  sub := fun ⟨_, _, hXY⟩ => f.rel_cod hXY
  master_mem := ⟨V₀.master, x.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ ⟨X', hX', hX'Y'⟩
    have hXX'mem : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hXX'mem
    refine ⟨X ∩ X', hXX'mem, ?_⟩
    have h1 : f.rel (X ∩ X') Y :=
      f.mono hXY Set.inter_subset_left subset_rfl hXX' (f.rel_cod hXY)
    have h2 : f.rel (X ∩ X') Y' :=
      f.mono hX'Y' Set.inter_subset_right subset_rfl hXX' (f.rel_cod hX'Y')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ hY' hYY'
    exact ⟨X, hX, f.mono hXY subset_rfl hYY' (x.sub hX) hY'⟩

@[simp] theorem mem_toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y := Iff.rfl

/-- **Proposition 2.2(ii) (Scott 1981, PRG-19).** The relation is recovered from the elementwise
map: for `X ∈ 𝒟₀`, `X f Y ↔ Y ∈ f(↑X)`. (`→` since `X ∈ ↑X`; `←` since any `Z ∈ ↑X` has `X ⊆ Z`,
so `Z f Y` monotonically yields `X f Y`.) -/
theorem rel_iff_mem_principal (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y := by
  constructor
  · intro hXY
    exact ⟨X, ⟨hX, subset_rfl⟩, hXY⟩
  · rintro ⟨Z, ⟨_, hXZ⟩, hZY⟩
    exact f.mono hZY hXZ subset_rfl hX (f.rel_cod hZY)

/-- **Proposition 2.2(iii) (Scott 1981, PRG-19).** Approximable maps are monotone on elements:
`x ⊑ y ⟹ f(x) ⊑ f(y)`. -/
theorem toElementMap_mono (f : ApproximableMap V₀ V₁) {x y : V₀.Element} (hxy : x ≤ y) :
    f.toElementMap x ≤ f.toElementMap y := by
  rintro Y ⟨X, hX, hXY⟩
  exact ⟨X, hxy X hX, hXY⟩

/-- **Proposition 2.2(iv) (Scott 1981, PRG-19).** Two approximable maps are *identical as relations*
iff they induce the same elementwise function: `(∀ x, f(x) = g(x)) ⟹ f = g`. For neighbourhoods `X`
the relation is read off `f(↑X)` (`rel_iff_mem_principal`); off `𝒟₀` both relations are empty. -/
theorem ext_of_toElementMap {f g : ApproximableMap V₀ V₁}
    (h : ∀ x, f.toElementMap x = g.toElementMap x) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

/-! ### Theorem 2.5 — the category of neighbourhood systems and approximable mappings. -/

/-- **Theorem 2.5(i) (Scott 1981, PRG-19) — the identity mapping `I_D`.** `X I_D Y ↔ X ⊆ Y`
(confined to `𝒟 × 𝒟`). It is approximable: (i) `Δ ⊆ Δ`; (ii) `X ⊆ Y`, `X ⊆ Y'` give `X ⊆ Y ∩ Y'`
with witness `X`; (iii) is transitivity `X' ⊆ X ⊆ Y ⊆ Y'`. -/
def idMap (V : NeighborhoodSystem α) : ApproximableMap V V where
  rel X Y := V.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, V.inter_mem hY hY' hX (Set.subset_inter hXY hXY'), Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

@[simp] theorem idMap_rel {V : NeighborhoodSystem α} {X Y : Set α} :
    (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **Theorem 2.5(ii) (Scott 1981, PRG-19) — composition `g ∘ f`.** `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`.
Approximability is Scott's verification: (i) use `Y = Δ₁`; (ii) intersect both witnesses via
`f.inter_right` then `g.inter_right` (narrowing the inner neighbourhood with `g.mono`); (iii) narrow
the input with `f.mono` and widen the output with `g.mono`, keeping the same witness. -/
def comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₂ where
  rel X Z := ∃ Y, f.rel X Y ∧ g.rel Y Z
  rel_dom := fun ⟨_, hXY, _⟩ => f.rel_dom hXY
  rel_cod := fun ⟨_, _, hYZ⟩ => g.rel_cod hYZ
  master_rel := ⟨V₁.master, f.master_rel, g.master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨Y, hXY, hYZ⟩ ⟨Y', hXY', hY'Z'⟩
    refine ⟨Y ∩ Y', f.inter_right hXY hXY', ?_⟩
    have hYY'mem : V₁.mem (Y ∩ Y') := f.rel_cod (f.inter_right hXY hXY')
    have h1 : g.rel (Y ∩ Y') Z :=
      g.mono hYZ Set.inter_subset_left subset_rfl hYY'mem (g.rel_cod hYZ)
    have h2 : g.rel (Y ∩ Y') Z' :=
      g.mono hY'Z' Set.inter_subset_right subset_rfl hYY'mem (g.rel_cod hY'Z')
    exact g.inter_right h1 h2
  mono := by
    rintro X X' Z Z' ⟨Y, hXY, hYZ⟩ hX'X hZZ' hX' hZ'
    refine ⟨Y, f.mono hXY hX'X subset_rfl hX' (f.rel_cod hXY), ?_⟩
    exact g.mono hYZ subset_rfl hZZ' (g.rel_dom hYZ) hZ'

@[simp] theorem comp_rel {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁} {X : Set α}
    {Z : Set γ} : (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z := Iff.rfl

/-- **Theorem 2.5 — left identity law.** `I_{D₁} ∘ f = f`. (`→`: a witness `Y ⊆ Z` widens the output
of `f` by `f.mono`; `←`: take `Y = Z`.) -/
theorem idMap_comp (f : ApproximableMap V₀ V₁) : (idMap V₁).comp f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, hXY, _, hZ, hYZ⟩
    exact f.mono hXY subset_rfl hYZ (f.rel_dom hXY) hZ
  · intro hXZ
    exact ⟨Z, hXZ, f.rel_cod hXZ, f.rel_cod hXZ, subset_rfl⟩

/-- **Theorem 2.5 — right identity law.** `f ∘ I_{D₀} = f`. (`→`: a witness `X ⊆ Y` sharpens the
input of `f` by `f.mono`; `←`: take `Y = X`.) -/
theorem comp_idMap (f : ApproximableMap V₀ V₁) : f.comp (idMap V₀) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, hYZ⟩
    exact f.mono hYZ hXY subset_rfl hX (f.rel_cod hYZ)
  · intro hXZ
    exact ⟨X, ⟨f.rel_dom hXZ, f.rel_dom hXZ, subset_rfl⟩, hXZ⟩

/-- **Theorem 2.5 — associativity.** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`. Pure reassociation of the
existential witnesses. -/
theorem comp_assoc {V₃ : NeighborhoodSystem δ} (h : ApproximableMap V₂ V₃)
    (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨Y, hXY, Z, hYZ, hZW⟩
    exact ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
  · rintro ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
    exact ⟨Y, hXY, Z, hYZ, hZW⟩

/-! ### Proposition 2.6 — the functor to sets and functions. -/

/-- **Proposition 2.6(i) (Scott 1981, PRG-19).** The identity mapping acts as the identity on
elements: `I_D(x) = x`. (`→`: `X ∈ x`, `X ⊆ Y ∈ 𝒟` gives `Y ∈ x` by `up_mem`; `←`: take `X = Y`.) -/
@[simp] theorem toElementMap_idMap (x : V₀.Element) : (idMap V₀).toElementMap x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXx, _, hY, hXY⟩
    exact x.up_mem hXx hY hXY
  · intro hY
    exact ⟨Y, hY, x.sub hY, x.sub hY, subset_rfl⟩

/-- **Proposition 2.6(ii) (Scott 1981, PRG-19).** Composition of approximable mappings becomes
composition of the elementwise functions: `(g ∘ f)(x) = g(f(x))`. Both sides unfold to
`∃ Y X, x.mem X ∧ X f Y ∧ Y g Z`; the proof is a reassociation of existentials. -/
theorem toElementMap_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) (x : V₀.Element) :
    (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, hXx, Y, hXY, hYZ⟩
    exact ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
  · rintro ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
    exact ⟨X, hXx, Y, hXY, hYZ⟩

/-! ### Theorem 2.7 — every domain isomorphism comes from an approximable mapping. -/

/-- **Theorem 2.7 (Scott 1981, PRG-19) — the approximable map of an isomorphism.** Given a domain
isomorphism `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9), Scott's "only way to define a neighbourhood
mapping" is the relation `X f Y ↔ Y ∈ e(↑X)`. The conditions of 2.1 hold because `e` is monotone:
(i) `Δ₁ ∈ e(⊥₀)` is `master_mem`; (ii) is `inter_mem` of the filter `e(↑X)`; (iii) sharpening `X' ⊆ X`
means `↑X ⊑ ↑X'`, so `e(↑X) ⊑ e(↑X')` and the output transports along, then widens by `up_mem`. -/
def ofIso (e : V₀.Element ≃o V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ _ : V₀.mem X, (e (V₀.principal ‹V₀.mem X›)).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hY⟩ => (e _).sub hY
  master_rel := ⟨V₀.master_mem, (e _).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (e (V₀.principal hX)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    have hle : V₀.principal hX ≤ V₀.principal hX' := (V₀.principal_le_iff hX hX').mpr hX'X
    have hmem : (e (V₀.principal hX')).mem Y := (e.monotone hle) Y hY
    exact (e (V₀.principal hX')).up_mem hmem hY' hYY'

/-- **Theorem 2.7 — the relation re-defines the function.** The elementwise map of `ofIso e` is `e`
itself: `(ofIso e)(x) = e(x)` for every `x`. The forward inclusion uses that `X ∈ x` implies
`↑X ⊑ x`, hence `e(↑X) ⊑ e(x)`; the reverse uses surjectivity of `e` (via `e.symm`) exactly as in
Scott's proof — one shows `x = e⁻¹((ofIso e)(x))` by antisymmetry. -/
theorem toElementMap_ofIso (e : V₀.Element ≃o V₁.Element) (x : V₀.Element) :
    (ofIso e).toElementMap x = e x := by
  have hgxle : (ofIso e).toElementMap x ≤ e x := by
    rintro Y ⟨X, hXx, hX, hY⟩
    have hpx : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hXx hZ.1 hZ.2
    exact (e.monotone hpx) Y hY
  have key : x = e.symm ((ofIso e).toElementMap x) := by
    apply le_antisymm
    · intro X hXx
      have hX : V₀.mem X := x.sub hXx
      have hsub : e (V₀.principal hX) ≤ (ofIso e).toElementMap x :=
        fun Y hY => ⟨X, hXx, hX, hY⟩
      have hple : V₀.principal hX ≤ e.symm ((ofIso e).toElementMap x) := by
        have h := e.symm.monotone hsub
        rwa [e.symm_apply_apply] at h
      exact hple X ⟨hX, subset_rfl⟩
    · have h := e.symm.monotone hgxle
      rwa [e.symm_apply_apply] at h
  have h1 : e x = e (e.symm ((ofIso e).toElementMap x)) := congrArg e key
  rw [e.apply_symm_apply] at h1
  exact h1.symm

/-- **Theorem 2.7 (statement) (Scott 1981, PRG-19).** "Every isomorphism between domains results from
an approximable mapping." For any domain isomorphism `e`, there is an approximable mapping whose
elementwise action is exactly `e`. -/
theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩

/-- **Theorem 2.7 (Scott 1981, PRG-19) — finite elements go to finite elements.** A domain
isomorphism `e` carries the finite (principal) element `↑X` to a finite element `↑Y` of the other
domain. Following Scott: with `w = e(↑X)`, the set `S = {e⁻¹(↑Y) ∣ Y ∈ w}` is directed (intersections
of members of `w` give upper bounds), so its union `z = ⋃ S` is an element (`sSupDirected`). One shows
`z = ↑X` (each `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`, and conversely `w ⊑ e(z)` forces `↑X = e⁻¹(w) ⊑ z`); then
`X ∈ z` lands in some `e⁻¹(↑Y)`, giving `w ⊑ ↑Y`, while `↑Y ⊑ w` is automatic — so `w = ↑Y`. -/
theorem exists_principal_eq_apply_principal (e : V₀.Element ≃o V₁.Element)
    {X : Set α} (hX : V₀.mem X) :
    ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY := by
  -- `w = e(↑X)`, and the directed family `S` of inverse images of principals of members of `w`.
  set w : V₁.Element := e (V₀.principal hX) with hw
  set S : Set V₀.Element :=
    {z | ∃ (Y : Set β) (hY : V₁.mem Y), w.mem Y ∧ z = e.symm (V₁.principal hY)} with hS
  -- `e⁻¹(w) = ↑X`.
  have hsymm_w : e.symm w = V₀.principal hX := by rw [hw, e.symm_apply_apply]
  -- For `Y ∈ w`, `↑Y ⊑ w`.
  have hprin_le_w : ∀ {Y : Set β} (hY : V₁.mem Y), w.mem Y → V₁.principal hY ≤ w :=
    fun hY hYw Z hZ => w.up_mem hYw hZ.1 hZ.2
  -- `S` is non-empty (use `Y = Δ₁`).
  have hne : S.Nonempty :=
    ⟨e.symm (V₁.principal V₁.master_mem), V₁.master, V₁.master_mem, w.master_mem, rfl⟩
  -- `S` is directed: intersect the two members of `w`.
  have hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c := by
    rintro a ⟨Y, hY, hYw, rfl⟩ b ⟨Y', hY', hY'w, rfl⟩
    have hYY'w : w.mem (Y ∩ Y') := w.inter_mem hYw hY'w
    have hYY' : V₁.mem (Y ∩ Y') := w.sub hYY'w
    refine ⟨e.symm (V₁.principal hYY'), ⟨Y ∩ Y', hYY', hYY'w, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone ((V₁.principal_le_iff hY hYY').mpr Set.inter_subset_left)
    · exact e.symm.monotone ((V₁.principal_le_iff hY' hYY').mpr Set.inter_subset_right)
  -- The directed union `z = ⋃ S`.
  set z : V₀.Element := V₀.sSupDirected S hne hdir with hz
  -- `z ⊑ ↑X`: every member `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`.
  have hz_le : z ≤ V₀.principal hX := by
    apply V₀.sSupDirected_le
    rintro s ⟨Y, hY, hYw, rfl⟩
    have : e.symm (V₁.principal hY) ≤ e.symm w := e.symm.monotone (hprin_le_w hY hYw)
    rwa [hsymm_w] at this
  -- `↑X ⊑ z`: show `w ⊑ e(z)`, then `↑X = e⁻¹(w) ⊑ z`.
  have hw_le_ez : w ≤ e z := by
    intro Y hYw
    have hY : V₁.mem Y := w.sub hYw
    have hmem_S : e.symm (V₁.principal hY) ∈ S := ⟨Y, hY, hYw, rfl⟩
    have h1 : e.symm (V₁.principal hY) ≤ z := V₀.le_sSupDirected S hne hdir hmem_S
    have h2 : V₁.principal hY ≤ e z := by
      have := e.monotone h1
      rwa [e.apply_symm_apply] at this
    exact h2 Y ⟨hY, subset_rfl⟩
  have hX_le_z : V₀.principal hX ≤ z := by
    have : e.symm w ≤ e.symm (e z) := e.symm.monotone hw_le_ez
    rwa [hsymm_w, e.symm_apply_apply] at this
  -- Hence `z = ↑X`, so `X ∈ z` lands in some member `e⁻¹(↑Y)`.
  have hz_eq : z = V₀.principal hX := le_antisymm hz_le hX_le_z
  have hXz : z.mem X := hz_eq ▸ ⟨hX, subset_rfl⟩
  obtain ⟨s, ⟨Y, hY, hYw, rfl⟩, hXs⟩ := hXz
  -- `↑X ⊑ e⁻¹(↑Y)` (it contains `X`), so `w = e(↑X) ⊑ ↑Y`; with `↑Y ⊑ w` we get `w = ↑Y`.
  refine ⟨Y, hY, ?_⟩
  have hprinX_le : V₀.principal hX ≤ e.symm (V₁.principal hY) :=
    fun Z hZ => (e.symm (V₁.principal hY)).up_mem hXs hZ.1 hZ.2
  have hw_le_prinY : w ≤ V₁.principal hY := by
    have := e.monotone hprinX_le
    rw [e.apply_symm_apply] at this
    rwa [← hw] at this
  exact le_antisymm hw_le_prinY (hprin_le_w hY hYw)

end ApproximableMap

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/ApproximableExercises.lean -/

/-!
# Lecture II (§2) — Exercises 2.8–2.12 and 2.19 (the algebra of approximable mappings)

Following Dana Scott, PRG-19 (1981), Lecture II. This file collects the *structural* exercises about
approximable mappings, all built on `Approximable.lean`:

* **Exercise 2.8** — an approximable map is determined by its action on finite (principal) elements
  (`eq_of_toElementMap_principal`); and **any** monotone function on finite elements extends to an
  approximable map (`ofMono`, `toElementMap_ofMono_principal`).
* **Exercise 2.9** — Scott's formula `f(x) = ⋃ {f(↑X) ∣ X ∈ x}` (`toElementMap_mem_iff_principal`).
* **Exercise 2.10** — the pointwise **meet** of two maps: `h(x) = f(x) ∩ g(x)` (`interMap`).
* **Exercise 2.11** — `|𝒟|` is closed under **directed unions** (`iSupDirected`, with
  `mem_iSupDirected`/`le_iSupDirected`/`iSupDirected_le`), and approximable maps **preserve** them
  (`toElementMap_iSupDirected`).
* **Exercise 2.12** — a directed family of approximable maps has a **pointwise union** that is again
  approximable (`iSupMap`, `mem_toElementMap_iSupMap`).
* **Exercise 2.19** — **two-variable** approximable maps `f : 𝒟₀ × 𝒟₁ → 𝒟₂` as ternary relations
  (`ApproximableMap₂`), with the Proposition 2.2 analogue (`toElementMap₂`, `rel₂_iff_mem_principal`).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the two
`eq_of_…`/uniqueness lemmas decide membership by `by_cases` and are therefore classical, exactly like
`ext_of_toElementMap`. -/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem

/-- **Exercise 2.11 — directed union (indexed form).** For a directed family `a : I → |𝒟|` (any two
`a i, a j` have a common upper bound `a k`), the union `⋃ᵢ a i` is again an element of `|𝒟|`. Built
on `sSupDirected` over the range. -/
def iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) : V.Element :=
  V.sSupDirected (Set.range a) (Set.range_nonempty a) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨a k, ⟨k, rfl⟩, hik, hjk⟩)

theorem mem_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α} :
    (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z := by
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hsZ⟩; exact ⟨i, hsZ⟩
  · rintro ⟨i, hi⟩; exact ⟨a i, ⟨i, rfl⟩, hi⟩

theorem le_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) (i : I) :
    a i ≤ iSupDirected a hdir :=
  fun _ hZ => (mem_iSupDirected a hdir).mpr ⟨i, hZ⟩

theorem iSupDirected_le {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {y : V.Element}
    (hy : ∀ i, a i ≤ y) : iSupDirected a hdir ≤ y := by
  intro Z hZ
  obtain ⟨i, hi⟩ := (mem_iSupDirected a hdir).mp hZ
  exact hy i Z hi

end NeighborhoodSystem

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### Exercise 2.8 — determination by, and extension from, finite elements. -/

/-- **Exercise 2.8 (uniqueness).** An approximable mapping is *uniquely determined by its elementwise
effect on finite elements*: if `f(↑X) = g(↑X)` for every neighbourhood `X`, then `f = g`. (Off `𝒟₀`
both relations are empty; on `𝒟₀` use `rel_iff_mem_principal`.) -/
theorem eq_of_toElementMap_principal {f g : ApproximableMap V₀ V₁}
    (h : ∀ (X : Set α) (hX : V₀.mem X),
      f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h X hX]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

/-- **Exercise 2.8 (extension).** *Any* monotone function on finite elements comes from an
approximable map. Here a "monotone function on finite elements" is a map `m` sending each
neighbourhood `X` (a finite element `↑X`) to an element `m X hX : |𝒟₁|`, monotone in the sense
`X' ⊆ X → m X hX ≤ m X' hX'` (i.e. `↑X ⊑ ↑X' ⟹ m(↑X) ⊑ m(↑X')`). The induced relation is
`X f Y ↔ Y ∈ m(↑X)`. -/
def ofMono (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX') :
    ApproximableMap V₀ V₁ where
  rel X Y := ∃ hX : V₀.mem X, (m X hX).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨hX, hY⟩ => (m _ hX).sub hY
  master_rel := ⟨V₀.master_mem, (m _ V₀.master_mem).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (m X hX).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    have hle : m X hX ≤ m X' hX' := hmono X X' hX hX' hX'X
    exact ⟨hX', (m X' hX').up_mem (hle Y hY) hY' hYY'⟩

/-- **Exercise 2.8 (extension, computed).** The map `ofMono m` realizes `m` on finite elements:
`(ofMono m)(↑X) = m(↑X)`. -/
theorem toElementMap_ofMono_principal
    (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX')
    (X : Set α) (hX : V₀.mem X) :
    (ofMono m hmono).toElementMap (V₀.principal hX) = m X hX := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨Z, ⟨hZmem, hXZ⟩, hZ', hmY⟩
    have hle : m Z hZ' ≤ m X hX := hmono Z X hZ' hX hXZ
    exact hle Y hmY
  · intro hmY
    exact ⟨X, ⟨hX, subset_rfl⟩, hX, hmY⟩

/-! ### Exercise 2.9 — the elementwise map as a union over finite approximants. -/

/-- **Exercise 2.9 (Scott 1981, PRG-19).** `f(x) = ⋃ {f(↑X) ∣ X ∈ x}`: a neighbourhood `Y` lies in
`f(x)` iff it lies in `f(↑X)` for some `X ∈ x`. (Immediate from `rel_iff_mem_principal`.) -/
theorem toElementMap_mem_iff_principal (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔
      ∃ (X : Set α) (hx : x.mem X), (f.toElementMap (V₀.principal (x.sub hx))).mem Y := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mp hrel⟩
  · rintro ⟨X, hxX, hmem⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mpr hmem⟩

/-! ### Exercise 2.10 — the pointwise meet of two approximable maps. -/

/-- **Exercise 2.10 (Scott 1981, PRG-19).** The pointwise **intersection** `h` of two approximable
maps: `X h Z ↔ X f Z ∧ X g Z`. It is approximable, and (`mem_toElementMap_interMap`)
`h(x) = f(x) ∩ g(x)`. -/
def interMap (f g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Z := f.rel X Z ∧ g.rel X Z
  rel_dom h := f.rel_dom h.1
  rel_cod h := f.rel_cod h.1
  master_rel := ⟨f.master_rel, g.master_rel⟩
  inter_right := fun ⟨hf, hg⟩ ⟨hf', hg'⟩ => ⟨f.inter_right hf hf', g.inter_right hg hg'⟩
  mono := fun ⟨hf, hg⟩ hX'X hZZ' hX' hZ' =>
    ⟨f.mono hf hX'X hZZ' hX' hZ', g.mono hg hX'X hZZ' hX' hZ'⟩

/-- **Exercise 2.10.** `h(x) = f(x) ∩ g(x)` (the meet in `|𝒟₁|`). The non-trivial direction combines
witnesses `X ∈ x` (for `f`) and `X' ∈ x` (for `g`) through `X ∩ X' ∈ x` using `mono`. -/
theorem mem_toElementMap_interMap (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β} :
    ((interMap f g).toElementMap x).mem Z ↔
      (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z := by
  constructor
  · rintro ⟨X, hxX, hf, hg⟩
    exact ⟨⟨X, hxX, hf⟩, ⟨X, hxX, hg⟩⟩
  · rintro ⟨⟨X, hxX, hf⟩, ⟨X', hxX', hg⟩⟩
    have hxXX' : x.mem (X ∩ X') := x.inter_mem hxX hxX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hxXX'
    refine ⟨X ∩ X', hxXX', ?_, ?_⟩
    · exact f.mono hf Set.inter_subset_left subset_rfl hXX' (f.rel_cod hf)
    · exact g.mono hg Set.inter_subset_right subset_rfl hXX' (g.rel_cod hg)

/-! ### Exercise 2.11 — approximable maps preserve directed unions. -/

/-- **Exercise 2.11 (Scott 1981, PRG-19).** Approximable mappings *preserve directed unions*:
`f(⋃ᵢ a i) = ⋃ᵢ f(a i)`. Both sides have member `Y` iff `∃ i X, X ∈ a i ∧ X f Y`. -/
theorem toElementMap_iSupDirected (f : ApproximableMap V₀ V₁) {I : Type*} [Nonempty I]
    (a : I → V₀.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) :
    f.toElementMap (NeighborhoodSystem.iSupDirected a hdir) =
      NeighborhoodSystem.iSupDirected (fun i => f.toElementMap (a i))
        (fun i j => by
          obtain ⟨k, hik, hjk⟩ := hdir i j
          exact ⟨k, f.toElementMap_mono hik, f.toElementMap_mono hjk⟩) := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap, NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨i, hi⟩ := (NeighborhoodSystem.mem_iSupDirected a hdir).mp hX
    exact ⟨i, X, hi, hrel⟩
  · rintro ⟨i, X, hi, hrel⟩
    exact ⟨X, (NeighborhoodSystem.mem_iSupDirected a hdir).mpr ⟨i, hi⟩, hrel⟩

/-! ### Exercise 2.12 — the pointwise union of a directed family of maps. -/

/-- **Exercise 2.12 (Scott 1981, PRG-19).** The pointwise union of a *directed* family of approximable
maps is approximable. Directedness is stated on the relations: any two `f i, f j` are dominated by
some `f k`. The union relation is `X g Z ↔ ∃ i, X (f i) Z`. -/
def iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) : ApproximableMap V₀ V₁ where
  rel X Z := ∃ i, (f i).rel X Z
  rel_dom := fun ⟨i, h⟩ => (f i).rel_dom h
  rel_cod := fun ⟨i, h⟩ => (f i).rel_cod h
  master_rel := by obtain ⟨i⟩ := (inferInstance : Nonempty I); exact ⟨i, (f i).master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (f k).inter_right (hik X Z hi) (hjk X Z' hj)⟩
  mono := by
    rintro X X' Z Z' ⟨i, hi⟩ hX'X hZZ' hX' hZ'
    exact ⟨i, (f i).mono hi hX'X hZZ' hX' hZ'⟩

/-- **Exercise 2.12.** The induced elementwise map is the pointwise union: `g(x) = ⋃ᵢ f i (x)`. -/
theorem mem_toElementMap_iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) (x : V₀.Element) {Y : Set β} :
    ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y := by
  constructor
  · rintro ⟨X, hxX, i, hrel⟩
    exact ⟨i, X, hxX, hrel⟩
  · rintro ⟨i, X, hxX, hrel⟩
    exact ⟨X, hxX, i, hrel⟩

end ApproximableMap

/-! ### Exercise 2.19 — approximable mappings of two variables. -/

/-- **Exercise 2.19 (Scott 1981, PRG-19).** An *approximable mapping of two variables*
`f : 𝒟₀ × 𝒟₁ → 𝒟₂` is a ternary relation `X, Y f Z` confined to `𝒟₀ × 𝒟₁ × 𝒟₂` with the natural
generalization of Definition 2.1: (i) `Δ₀, Δ₁ f Δ₂`; (ii) intersectivity on the output; (iii)
monotonicity jointly in both inputs (sharper) and the output (blunter). -/
structure ApproximableMap₂ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) where
  /-- The underlying ternary relation `X, Y f Z`. -/
  rel : Set α → Set β → Set γ → Prop
  rel_dom₀ : ∀ {X Y Z}, rel X Y Z → V₀.mem X
  rel_dom₁ : ∀ {X Y Z}, rel X Y Z → V₁.mem Y
  rel_cod : ∀ {X Y Z}, rel X Y Z → V₂.mem Z
  /-- (i) `Δ₀, Δ₁ f Δ₂`. -/
  master_rel : rel V₀.master V₁.master V₂.master
  /-- (ii) intersectivity on the output. -/
  inter_right : ∀ {X Y Z Z'}, rel X Y Z → rel X Y Z' → rel X Y (Z ∩ Z')
  /-- (iii) joint monotonicity: sharper inputs `X' ⊆ X`, `Y' ⊆ Y`; blunter output `Z ⊆ Z'`. -/
  mono : ∀ {X X' Y Y' Z Z'}, rel X Y Z → X' ⊆ X → Y' ⊆ Y → Z ⊆ Z' →
    V₀.mem X' → V₁.mem Y' → V₂.mem Z' → rel X' Y' Z'

namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.19 (Proposition 2.2 analogue).** A two-variable approximable mapping determines an
elementwise function of two arguments: `f(x, y) = {Z ∣ ∃ X ∈ x, ∃ Y ∈ y, X, Y f Z}`. The filter
laws use all three conditions: `inter_mem` pulls both outputs back to `(X ∩ X', Y ∩ Y')` via `mono`
then `inter_right`. -/
def toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element) : V₂.Element where
  mem Z := ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z
  sub := fun ⟨_, _, _, _, hrel⟩ => f.rel_cod hrel
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ ⟨X', Y', hX', hY', hrel'⟩
    have hXX' : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hYY' : y.mem (Y ∩ Y') := y.inter_mem hY hY'
    have hXX'm : V₀.mem (X ∩ X') := x.sub hXX'
    have hYY'm : V₁.mem (Y ∩ Y') := y.sub hYY'
    refine ⟨X ∩ X', Y ∩ Y', hXX', hYY', ?_⟩
    have h1 : f.rel (X ∩ X') (Y ∩ Y') Z :=
      f.mono hrel Set.inter_subset_left Set.inter_subset_left subset_rfl hXX'm hYY'm (f.rel_cod hrel)
    have h2 : f.rel (X ∩ X') (Y ∩ Y') Z' :=
      f.mono hrel' Set.inter_subset_right Set.inter_subset_right subset_rfl hXX'm hYY'm
        (f.rel_cod hrel')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ hZ' hZZ'
    exact ⟨X, Y, hX, hY, f.mono hrel subset_rfl subset_rfl hZZ' (x.sub hX) (y.sub hY) hZ'⟩

@[simp] theorem mem_toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element)
    {Z : Set γ} : (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z := Iff.rfl

/-- **Exercise 2.19 (recovery of the relation).** `X, Y f Z ↔ Z ∈ f(↑X, ↑Y)`, the two-variable
analogue of Proposition 2.2(ii). -/
theorem rel₂_iff_mem_principal (f : ApproximableMap₂ V₀ V₁ V₂) {X : Set α} (hX : V₀.mem X)
    {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z := by
  constructor
  · intro hrel
    exact ⟨X, Y, ⟨hX, subset_rfl⟩, ⟨hY, subset_rfl⟩, hrel⟩
  · rintro ⟨X', Y', ⟨_, hXX'⟩, ⟨_, hYY'⟩, hrel⟩
    exact f.mono hrel hXX' hYY' subset_rfl hX hY (f.rel_cod hrel)

/-- **Exercise 2.19 (monotonicity).** The two-variable elementwise map is monotone in each argument
jointly: `x ⊑ x'`, `y ⊑ y'` imply `f(x, y) ⊑ f(x', y')`. -/
theorem toElementMap₂_mono (f : ApproximableMap₂ V₀ V₁ V₂) {x x' : V₀.Element} {y y' : V₁.Element}
    (hx : x ≤ x') (hy : y ≤ y') : f.toElementMap₂ x y ≤ f.toElementMap₂ x' y' := by
  rintro Z ⟨X, Y, hX, hY, hrel⟩
  exact ⟨X, Y, hx X hX, hy Y hY, hrel⟩

end ApproximableMap₂

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Definition610.lean -/

/-!
# Lecture VI — Definition 6.10 (Scott 1981, PRG-19): the subsystem relation `D ◁ E`

To explain why the *minimal* solutions of a domain equation exist, Scott introduces a notion of
"subdomain". The functors `T` he has in mind are not merely continuous on maps (Definition 6.8) but
also possess continuity properties *on domains*, and those are phrased in terms of this relation.

**Definition 6.10.** For two neighbourhood systems `D` and `E` over the *same* set of tokens `Δ`,
we write `D ◁ E` to mean that
* `D ⊆ E` (every neighbourhood of `D` is a neighbourhood of `E`), **and**
* whenever `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`.

The second clause is the crucial one: it says the notion of *consistency* in `D` is the **same** as
in `E`. A subdomain is a smaller family of neighbourhoods, but it must agree with `E` about which
pairs are consistent.

This module formalizes the relation together with the elementary facts Scott records in the prose:

* it is reflexive (`Subsystem.refl`) and transitive (`Subsystem.trans`);
* it is antisymmetric (`Subsystem.antisymm`): `D ◁ E` and `E ◁ D` force `D = E`;
* **Scott's remark.** If `D₀ ◁ E` and `D₁ ◁ E`, then `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`
  (`Subsystem.subsystem_iff_subset_of_common`) — once both sit inside a common `E`, the
  subdomain relation collapses to plain inclusion of neighbourhood families.

Everything here is at the `Prop` level and **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
Propositions 6.11 (the subsystems of `E` form a domain) and 6.12 (a `D ◁ E` yields a projection
pair `i, j`) build on this relation and are formalized separately.
-/

namespace Scott1980.Neighborhood

variable {α : Type*}

/-- **Definition 6.10 (Scott 1981, PRG-19).** The *subsystem* (subdomain) relation `D ◁ E` for two
neighbourhood systems over the same token type. It records that `D` and `E` are systems over the
same `Δ` (`master_eq`), that `D` is a subfamily of `E` (`sub`), and — the essential clause — that
consistency is inherited from `E`: an intersection of two `D`-neighbourhoods that happens to be an
`E`-neighbourhood is already a `D`-neighbourhood (`inter_closed`). -/
structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  /-- `D` and `E` are systems over the same set of tokens `Δ`. -/
  master_eq : D.master = E.master
  /-- `D ⊆ E`: every neighbourhood of `D` is a neighbourhood of `E`. -/
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  /-- Consistency in `D` is the same as in `E`: if `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`. -/
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

namespace Subsystem

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

/-- The subsystem relation is **transitive**: `D ◁ E` and `E ◁ F` give `D ◁ F`.

The `inter_closed` clause threads through `E`: from `X, Y ∈ D ⊆ E` and `X ∩ Y ∈ F`, the relation
`E ◁ F` puts `X ∩ Y ∈ E`, and then `D ◁ E` puts `X ∩ Y ∈ D`. -/
theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

/-- Two neighbourhood systems with the same `mem` and the same `master` are equal (the remaining
fields of `NeighborhoodSystem` are `Prop`s). -/
theorem _root_.Scott1980.Neighborhood.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D = E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

/-- **Scott's remark (the prose after Definition 6.10).** Once `D₀` and `D₁` both sit inside a
common system `E` as subdomains, the subdomain relation between them is just inclusion of
neighbourhood families: `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`.

* `→` is the `sub` clause of `D₀ ◁ D₁`.
* `←` builds `D₀ ◁ D₁` from `D₀ ⊆ D₁`: the masters agree because both equal `E`'s master, and
  the `inter_closed` clause routes through `E` — an intersection `X ∩ Y` of `D₀`-neighbourhoods
  lying in `D₁` lies in `E` (since `D₁ ⊆ E`), and `D₀ ◁ E` then returns it to `D₀`. -/
theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Definition63.lean -/

/-!
# Lecture VI — Definitions 6.3–6.5 (Scott 1981, PRG-19): functors, `T`-algebras, initial algebras

To state domain equations `D ≅ T(D)` and single out their *canonical* solutions, Scott introduces
"a small amount of the terminology of category theory" and stresses that the next few definitions
"could be given for any category". This module sets up a small, self-contained category abstraction
and formalises that vocabulary:

* **Definition 6.3** — a *functor* `T` on a category into itself (an *endofunctor*), preserving
  identities and composition.
* **Definition 6.4** — a *`T`-algebra* `k : T(E) → E` and a *homomorphism* of `T`-algebras.
* **Definition 6.5** — an *initial* `T`-algebra: one with a unique homomorphism into every algebra.

Everything is generic over an arbitrary `Category`, exactly as Scott emphasises. As Scott also notes
in the prose preceding Definition 6.3 ("[the systems] form quite an interesting category with respect
to the approximable maps"), the neighbourhood systems and approximable maps of the project *are* a
category; that instance (`DomainObj`) is provided here as a witness that the abstract definitions are
not vacuous.

Auxiliary categorical lemmas (identity and composition of algebra homomorphisms, `Iso`) needed for
Propositions 6.6 and 6.7 are developed here as well.

All definitions and lemmas are constructive and **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the underlying composition laws are the project's
`idMap_comp`/`comp_idMap`/`comp_assoc` (Theorem 2.5).

## Why a bespoke `Category` rather than Mathlib's `CategoryTheory.Category`?

Mathlib *does* have a fully developed category theory: `CategoryTheory.Category` (structurally
identical to the class below — separate object/morphism universes, `Hom`, `id`, `comp`, and the three
laws), functors `C ⥤ D`, `Iso`, `CategoryTheory.Endofunctor.Algebra`/`Algebra.Hom` with the category
of algebras, `Limits.IsInitial`, and even Lambek's lemma as `Endofunctor.Algebra.Initial.strInv` /
`left_inv` / `right_inv`. So Mathlib is *expressive enough* to state every one of Definitions 6.3–6.5
(and Propositions 6.6–6.7) verbatim — it is not a question of missing vocabulary.

It is nonetheless the wrong tool *here*, and the reason is this project's headline invariant, not
taste. The trade-off was checked empirically:

* The bare instance is fine: a `Category DomainObj` built on `ApproximableMap` (Theorem 2.5 laws)
  is **choice-free**, `#print axioms = [propext, Quot.sound]`.
* But the *only reason* to import Mathlib's hierarchy is to reuse its downstream content — functor
  algebras and the initial-algebra fixed-point theorem — and that content is **choice-bound**:
  `Mathlib.CategoryTheory.Endofunctor.Algebra.Initial.left_inv` (the inverse half of Lambek's lemma,
  i.e. Scott's Proposition 6.7) reports `[propext, Classical.choice, Quot.sound]`, because Mathlib's
  `IsInitial` rides on the `Limits` framework.
* By contrast, the project's own `initialIso` (Proposition 6.6) and `lambek` (Proposition 6.7), built
  on the class below, depend on **no axioms whatsoever** (`#print axioms` reports *"does not depend on
  any axioms"*).

So adopting Mathlib would force one of two losing choices: (a) consume its initial-algebra API and
thereby inject `Classical.choice` into the project's flagship Lecture VI results, breaking the
`#print axioms ⊆ {propext, Quot.sound}` discipline that is the whole point; or (b) take only the bare
class and re-prove 6.6–6.7 by hand anyway — paying a heavy transitive import and the `≫`
(diagrammatic, "`f` then `g`") vs `⊚` (Scott's "`g` after `f`") convention clash for no reusable
content. Since Scott asks only for "a small amount of the terminology of category theory", the
~50-line self-contained class below supplies exactly that vocabulary while keeping every proof
constructive and choice-free. The Mathlib `Category` is therefore *usable but counterproductive* for
this development, and is deliberately not used.
-/

namespace Scott1980.Neighborhood

universe u v w

/-- A category: objects (a type `Obj`), hom-sets `Hom X Y`, identities, composition, and the three
category laws. We bundle it as a class so a fixed object type can carry its categorical structure.
The composition `comp g f` reads "`g` after `f`" (the same convention as `ApproximableMap.comp`). -/
class Category (Obj : Type u) where
  /-- The morphisms from `X` to `Y`. -/
  Hom : Obj → Obj → Type v
  /-- The identity morphism on each object. -/
  id : (X : Obj) → Hom X X
  /-- Composition: `comp g f` is "`g` after `f`". -/
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  /-- Left identity law `I ∘ f = f`. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  /-- Right identity law `f ∘ I = f`. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  /-- Associativity `(h ∘ g) ∘ f = h ∘ (g ∘ f)`. -/
  assoc : ∀ {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp (comp h g) f = comp h (comp g f)

@[inherit_doc] infixr:80 " ⊚ " => Category.comp

/-! ### The category of neighbourhood systems and approximable maps

Scott's running category (prose before Definition 6.3). Objects bundle a token type with a system;
morphisms are approximable maps; the laws are Theorem 2.5. -/

/-- An object of the category of domains: a token type together with a neighbourhood system on it. -/
structure DomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system (the "domain"). -/
  sys : NeighborhoodSystem carrier

/-- **The category of domains and approximable maps** (Scott's prose preceding Definition 6.3):
identities and associative composition come from Theorem 2.5 (`idMap_comp`, `comp_idMap`,
`comp_assoc`). -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := ApproximableMap.idMap D.sys
  comp g f := g.comp f
  id_comp f := ApproximableMap.idMap_comp f
  comp_id f := ApproximableMap.comp_idMap f
  assoc h g f := ApproximableMap.comp_assoc h g f

variable {Obj : Type u} [Category Obj]

/-! ### Definition 6.3 — functors -/

/-- **Definition 6.3 (Scott 1981, PRG-19).** A *functor* on a category into itself (an
*endofunctor*): an assignment `obj` on objects and `map` on morphisms preserving identities
(`map_id`) and composition (`map_comp`). -/
structure Endofunctor (Obj : Type u) [Category Obj] where
  /-- The action on objects. -/
  obj : Obj → Obj
  /-- The action on morphisms. -/
  map : {X Y : Obj} → Category.Hom X Y → Category.Hom (obj X) (obj Y)
  /-- `T(I_X) = I_{T(X)}`. -/
  map_id : ∀ (X : Obj), map (Category.id X) = Category.id (obj X)
  /-- `T(g ∘ f) = T(g) ∘ T(f)`. -/
  map_comp : ∀ {X Y Z : Obj} (g : Category.Hom Y Z) (f : Category.Hom X Y),
    map (g ⊚ f) = (map g) ⊚ (map f)

/-! ### Definition 6.4 — `T`-algebras and their homomorphisms -/

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *`T`-algebra*: a domain `carrier` together with a
structure map `str : T(carrier) → carrier`. -/
structure TAlgebra (T : Endofunctor Obj) where
  /-- The underlying object `E`. -/
  carrier : Obj
  /-- The structure map `k : T(E) → E`. -/
  str : Category.Hom (T.obj carrier) carrier

variable {T : Endofunctor Obj}

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *homomorphism* of `T`-algebras `(E,k) → (F,m)`: a map
`hom : E → F` making the square commute, i.e. `hom ∘ k = m ∘ T(hom)`. -/
structure AlgHom (A B : TAlgebra T) where
  /-- The underlying morphism `h : E → F`. -/
  hom : Category.Hom A.carrier B.carrier
  /-- The homomorphism square `h ∘ k = m ∘ T(h)`. -/
  comm : hom ⊚ A.str = B.str ⊚ T.map hom

namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := Category.id A.carrier
  comm := by rw [Category.id_comp, T.map_id, Category.comp_id]

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    rw [Category.assoc, α.comm, ← Category.assoc, β.comm, Category.assoc, ← T.map_comp]

@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = Category.id A.carrier := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

/-! ### Definition 6.5 — initial `T`-algebras -/

/-- **Definition 6.5 (Scott 1981, PRG-19).** A `T`-algebra `A` is *initial* iff there is a (unique)
homomorphism from `A` into every `T`-algebra. We package the homomorphism as the data `desc` and its
uniqueness as `uniq`. -/
structure IsInitial (A : TAlgebra T) where
  /-- The chosen homomorphism into any algebra `B`. -/
  desc : (B : TAlgebra T) → AlgHom A B
  /-- It is the only homomorphism `A → B`. -/
  uniq : ∀ (B : TAlgebra T) (h : AlgHom A B), h = desc B

/-- An isomorphism in the category: a pair of mutually inverse morphisms. -/
structure Iso (X Y : Obj) where
  /-- The forward morphism. -/
  hom : Category.Hom X Y
  /-- The inverse morphism. -/
  inv : Category.Hom Y X
  /-- `inv ∘ hom = I_X`. -/
  hom_inv_id : inv ⊚ hom = Category.id X
  /-- `hom ∘ inv = I_Y`. -/
  inv_hom_id : hom ⊚ inv = Category.id Y

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Example12.lean -/

/-!
# Example 1.2 (Scott 1981, PRG-19, §1)

Scott's first worked example: tokens `Δ = {0, 1}` and neighbourhoods
`𝒟 = {{0, 1}, {0}, {1}}`.

We construct the neighbourhood system, prove it satisfies Definition 1.1, and classify
its domain elements (Definition 1.6): there are exactly three filters, and exactly one
partial element — the bottom filter `{Δ}`.
-/

namespace Scott1980.Neighborhood.Example12

/-- Tokens for Example 1.2: `Δ = {0, 1}`. -/
abbrev Token := Fin 2

/-- The master neighbourhood `Δ = {0, 1}`. -/
def master : Set Token := Set.univ

/-- The neighbourhood `{0}`. -/
def zero : Set Token := {0}

/-- The neighbourhood `{1}`. -/
def one : Set Token := {1}

/-- The three neighbourhoods of Example 1.2. -/
def memSet : Set (Set Token) := {master, zero, one}

/-- Membership in the neighbourhood system `𝒟` of Example 1.2. -/
def mem (X : Set Token) : Prop := X ∈ memSet

theorem mem_master : mem master := by simp [mem, memSet, master, zero, one]
theorem mem_zero : mem zero := by simp [mem, memSet, master, zero, one]
theorem mem_one : mem one := by simp [mem, memSet, master, zero, one]

/-- A neighbourhood of Example 1.2 is exactly one of `Δ`, `{0}`, or `{1}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = zero ∨ X = one := by
  constructor
  · intro h
    simp [mem, memSet, master, zero, one] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_zero
    · exact mem_one

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h
  · rw [master] at h; exact Set.empty_ne_univ h
  · simp [zero] at h
  · simp [one] at h

private theorem zero_ne_master : zero ≠ master := by
  intro h
  have : (1 : Token) ∈ zero := h ▸ (by simp [master])
  simp [zero] at this

private theorem one_ne_master : one ≠ master := by
  intro h
  have : (0 : Token) ∈ one := h ▸ (by simp [master])
  simp [one] at this

private theorem master_not_subset_zero : ¬master ⊆ zero := by
  intro h
  have : (1 : Token) ∈ zero := h (by simp [master])
  simp [zero] at this

private theorem master_not_subset_one : ¬master ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [master])
  simp [one] at this

private theorem one_not_subset_zero : ¬one ⊆ zero := by
  intro h
  have : (1 : Token) ∈ zero := h (by simp [one])
  simp [zero] at this

private theorem zero_not_subset_one : ¬zero ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [zero])
  simp [one] at this

private theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | hzero | hone
  · rfl
  · exact absurd hzero (fun h' => master_not_subset_zero (h' ▸ hsub))
  · exact absurd hone (fun h' => master_not_subset_one (h' ▸ hsub))

private theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

private theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

private theorem zero_inter_one : zero ∩ one = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

private theorem one_inter_zero : one ∩ zero = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

private theorem inter_eq (X Y : Set Token) (h : mem X) (h' : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = zero ∨ X ∩ Y = one ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp h with rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp h' with rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (Or.inl (master_inter _)))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (Or.inr zero_inter_one))
  · exact Or.inr (Or.inr (Or.inl (inter_master _)))
  · exact Or.inr (Or.inr (Or.inr one_inter_zero))
  · exact Or.inr (Or.inr (Or.inl (Set.inter_self _)))

/-- **Example 1.2.** The neighbourhood system on `Δ = {0, 1}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_zero
    · rw [h]; exact mem_one
    · rw [h] at hZsub
      have hz : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst hz
      exact absurd hZ not_mem_empty

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}`. -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

/-- The total element determined by `{0}`. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = zero
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_zero
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY zero_not_subset_one

/-- The total element determined by `{1}`. -/
def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = one
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_one
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hXY one_not_subset_zero
      · exact Or.inr rfl

private theorem mem_zero_of_mem (x : neighborhoodSystem.Element) (h : x.mem zero) :
    x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · exact Or.inr hzero
    · have hxone : x.mem one := hone ▸ hx
      have := x.inter_mem h hxone
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

private theorem mem_one_of_mem (x : neighborhoodSystem.Element) (h : x.mem one) :
    x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · have hxzero : x.mem zero := hzero ▸ hx
      have := x.inter_mem hxzero h
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
    · exact Or.inr hone
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

/-- Every element of Example 1.2 is one of the three filters `⊥`, `{0}`-total, `{1}`-total. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne := by
  by_cases h0 : x.mem zero
  · exact Or.inr (Or.inl (mem_zero_of_mem x h0))
  by_cases h1 : x.mem one
  · exact Or.inr (Or.inr (mem_one_of_mem x h1))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · rfl
    · exact absurd (hzero ▸ hx) h0
    · exact absurd (hone ▸ hx) h1
  · intro hx
    rw [hx]
    exact x.master_mem

/-- The bottom filter is the only partial element: it is strictly below both total elements. -/
theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem zero := h zero (Or.inr rfl)
    have hm : zero = master := this
    exact zero_ne_master hm

theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem one := h one (Or.inr rfl)
    have hm : one = master := this
    exact one_ne_master hm

theorem bot_is_unique_partial (x : neighborhoodSystem.Element) :
    x ≠ elemZero → x ≠ elemOne → x = bot := by
  intro hne0 hne1
  rcases element_classification x with hx | hx | hx
  · exact hx
  · exact (hne0 hx).elim
  · exact (hne1 hx).elim

private theorem zero_ne_one : zero ≠ (one : Set Token) := by
  intro h
  have h0 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h0
  simp [one] at h0

/-- **`elemZero` and `elemOne` are incomparable.** Neither total element approximates the other:
if it did, its finite neighbourhood `{i}` would have to belong to the other's filter too, which
is neither `Δ` nor its own singleton `{1-i}`. Used to show `⊥` is the *only* common lower bound
of `elemZero` and `elemOne` (Exercise 2.16's uniqueness argument for the parity map). -/
theorem not_elemZero_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h zero (Or.inr rfl) with h' | h'
  · exact zero_ne_master h'
  · exact zero_ne_one h'

theorem not_elemOne_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h one (Or.inr rfl) with h' | h'
  · exact one_ne_master h'
  · exact zero_ne_one h'.symm

/-- **`⊥` is the unique common lower bound of `elemZero` and `elemOne`.** Any element approximated
by *both* total elements is exactly `⊥`: `element_classification` puts it at `bot`, `elemZero`, or
`elemOne`, and the latter two are excluded by incomparability. This is the order-theoretic
ingredient (continuity/flatness of `𝒯`) behind the uniqueness half of Exercise 2.16. -/
theorem eq_bot_of_le_elemZero_of_le_elemOne {a : neighborhoodSystem.Element}
    (h0 : a ≤ elemZero) (h1 : a ≤ elemOne) : a = bot := by
  rcases element_classification a with rfl | rfl | rfl
  · rfl
  · exact absurd h1 not_elemZero_le_elemOne
  · exact absurd h0 not_elemOne_le_elemZero

end neighborhoodSystem

end Scott1980.Neighborhood.Example12

/-! ### Inlined from Scott1980/Neighborhood/ExampleB.lean -/

/-!
# Example 1.B (Scott 1981, PRG-19, §1) — binary sequences

Scott's recurring **binary** example, generalizing the finite binary tree of Example 1.4 to
*infinite* sequences. Take `Δ = Σ*` with `Σ = {0,1}` (the finite binary strings, `Λ` = the empty
string), and for `σ ∈ Σ*` let `σΣ*` be the set of all *extensions* of `σ`. The neighbourhoods are

`B = {σΣ* ∣ σ ∈ Σ*}`,

a neighbourhood being "all extensions of a fixed prefix `σ`". We encode `Σ* = List Bool`, the
empty sequence `Λ = []`, concatenation `στ = σ ++ τ`, and the *initial-segment* relation
`σ ⪯ τ` by mathlib's list-prefix order `σ <+: τ`. The cone `σΣ*` is `cone σ = {w ∣ σ <+: w}`.

Deliverables (all of the Example-1.B paragraph, lines 281–315 of the source):

* **Example 1.B / Exercise (`B` is a system).** `B : NeighborhoodSystem Str`, built from the
  prefix *trichotomy* via `ofNestedOrDisjoint` — any two cones are nested or disjoint.
* **`σ⊥` (the finite elements).** `sigmaBot σ = ↑(cone σ)`, the principal filter of `σΣ*`; its
  minimal neighbourhood is `σΔ = cone σ`.
* **Factoid `σ₀⊥ ⊆ σ₁⊥ ⟺ σ₀` initial segment of `σ₁`.** `sigmaBot_le_iff`.
* **Exercise (`σx ∈ |B|`).** `sigmaElt σ x`, and `sigmaElt σ ⊥ = σ⊥` (`sigmaElt_bot`) justifying
  the `σ⊥` notation.
* **Factoid `x = ⋃ₙ σₙ⊥`.** `mem_iff_exists_sigmaBot`: every `x ∈ |B|` is the union of the finite
  elements `σ⊥` with `σΣ* ∈ x` — the concrete "limit of finite approximations" in `|B|`. (The
  countable *chain* form, with `σₙ ⪯ σₙ₊₁` enumerated, needs choice and is left to the prose.)

Everything is **constructive** (`#print axioms ⊆ {propext, Quot.sound}`): list-prefix is decidable,
so the trichotomy is choice-free.
-/

namespace Scott1980.Neighborhood.ExampleB

open Scott1980.Neighborhood NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`). -/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity of `<+:`.) -/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

/-- **Cones are one-one in the prefix.** `cone σ = cone τ ⟹ σ = τ`: from the two inclusions we get
`τ <+: σ` and `σ <+: τ`, and a prefix-antisymmetry (equal lengths) finishes. Used by the approximable
maps `B → T` / `B → B` (Examples 2.3, 2.4) to read off the unique generating prefix of a cone. -/
theorem cone_injective {σ τ : Str} (h : cone σ = cone τ) : σ = τ := by
  have h1 : τ <+: σ := cone_subset_cone.mp (le_of_eq h)
  have h2 : σ <+: τ := cone_subset_cone.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either one contains the
other, or they are disjoint (incomparable prefixes have no common extension). Choice-free: the
prefix relation on `List Bool` is decidable. -/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*` for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

/-- **Exercise ("`B` is a neighbourhood system").** The family `B = {σΣ* ∣ σ ∈ Σ*}` is pairwise
nested-or-disjoint, by `cone_trichotomy`. -/
theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

/-- **Example 1.B (Scott 1981, PRG-19).** The binary neighbourhood system `B` on `Δ = Σ*`. -/
def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

@[simp] theorem B_master : B.master = Set.univ := rfl

/-- Every cone is a neighbourhood of `B`. -/
theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

/-! ### Prepending a prefix: `σX = {στ ∣ τ ∈ X}`. -/

/-- Scott's `σX = {στ ∣ τ ∈ X}` (prepend the prefix `σ` to every member of `X`). -/
def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element. -/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

/-- **Prepending is monotone.** `X' ⊆ X → σX' ⊆ σX` (Exercise 2.16's `sigmaMap` uses this for
its `mono` clause; `sigmaElt_append` uses it to transport the up-closure through composition). -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

/-- `σΣ* = σ·Σ*`: prepending `σ` to the whole space recovers the cone of `σ`. -/
theorem prepend_univ (σ : Str) : prepend σ Set.univ = cone σ := by
  ext w
  simp only [mem_prepend, Set.mem_univ, true_and, mem_cone]
  constructor
  · rintro ⟨τ, rfl⟩
    exact List.prefix_append σ τ
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

/-- Prepending preserves membership in `B` (`σ` applied to a cone is a cone). -/
theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

/-- Prepending the empty prefix does nothing: `ΛX = X`. -/
@[simp] theorem prepend_nil (X : Set Str) : prepend [] X = X := by
  ext w; simp [mem_prepend]

/-- **Prepending is associative.** `σ(τX) = (στ)X`: prepending `σ` after `τ` is the same as
prepending the concatenation `σ ++ τ` in one step (used to compose `sigmaElt`, `Exercise216`). -/
theorem prepend_append (σ τ : Str) (X : Set Str) :
    prepend σ (prepend τ X) = prepend (σ ++ τ) X := by
  ext w
  simp only [mem_prepend]
  constructor
  · rintro ⟨ρ, ⟨ρ', hρ', rfl⟩, rfl⟩
    exact ⟨ρ', hρ', by rw [List.append_assoc]⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨τ ++ ρ, ⟨ρ, hρ, rfl⟩, by rw [List.append_assoc]⟩

/-! ### The finite elements `σ⊥` and the initial-segment factoid. -/

/-- **`σ⊥`, a finite element of `|B|`.** The principal filter `↑(σΣ*)` of the cone of `σ`; its
minimal neighbourhood is `σΔ = σΣ*` (Scott). These are exactly the finite elements of `|B|`. -/
def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

/-- **Factoid (Scott 1981, PRG-19).** "`σ₀⊥ ⊆ σ₁⊥` if and only if `σ₀` is an *initial segment* of
the sequence `σ₁`." The approximation order on finite elements is exactly the prefix order:
`σ₀⊥ ⊑ σ₁⊥ ↔ σ₀ <+: σ₁`. (Via `principal_le_iff` — reversal — composed with `cone_subset_cone` —
reversal again — which cancel to give the prefix order directly.) -/
theorem sigmaBot_le_iff (σ₀ σ₁ : Str) :
    sigmaBot σ₀ ≤ sigmaBot σ₁ ↔ σ₀ <+: σ₁ := by
  rw [sigmaBot, sigmaBot, B.principal_le_iff, cone_subset_cone]

/-- **`⊥` sits only in the cone of the empty prefix.** `⊥.mem(σΣ*) ↔ σ = Λ`: `⊥`'s only
neighbourhood is `Δ = ΛΣ*` (`cone_nil`), and a cone determines its prefix (`cone_injective`).
(Used by Exercise 2.17's base case, where `g(1)=⊥` is stated only at the input `⊥`.) -/
theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone_nil]
  constructor
  · exact cone_injective
  · intro h; rw [h]

/-! ### The operation `σx` (Scott's left-multiplication on elements). -/

/-- **Exercise (`σx ∈ |B|`).** For `x ∈ |B|` and `σ ∈ Σ*`, Scott's
`σx = {Y ∣ σX ⊆ Y for some X ∈ x}` is again an element of `|B|`.

The filter laws: `master` uses `X = Δ ∈ x` (`σΔ ⊆ Δ` trivially); `inter` takes `X₁ ∩ X₂ ∈ x` and
the consistency witness `σ(X₁∩X₂)`, which is a *cone* (hence in `B`, by `memB_prepend`) contained in
both `Y₁` and `Y₂`; `up` reuses the same `X`. -/
def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

/-- **`σ⊥` really is `σ` applied to `⊥`.** `sigmaElt σ ⊥ = sigmaBot σ`, justifying the `σ⊥`
notation: applying `σ` to the least element produces the finite element `↑(σΣ*)`. -/
theorem sigmaElt_bot (σ : Str) : sigmaElt σ B.bot = sigmaBot σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [B.mem_bot] at hX
    subst hX
    rw [B_master, prepend_univ] at hsub
    exact ⟨hY, hsub⟩
  · rintro ⟨hY, hcone⟩
    refine ⟨hY, B.master, B.mem_bot.mpr rfl, ?_⟩
    rw [B_master, prepend_univ]
    exact hcone

/-- **Prepending the empty prefix fixes every element.** `Λx = x` — the identity case of
`sigmaElt`, matching `prepend_nil` on neighbourhoods. -/
theorem sigmaElt_nil (x : B.Element) : sigmaElt [] x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [prepend_nil] at hsub
    exact x.up_mem hX hY hsub
  · intro hY
    exact ⟨x.sub hY, Y, hY, by rw [prepend_nil]⟩

/-- **`σ` and `τ` prepend in sequence, like concatenation.** `(στ)x = σ(τx)`: applying the
prefix `σ ++ τ` in one step agrees with applying `τ` first and then `σ`. (Used in Exercise 2.16's
second half — the uniqueness of the parity map — to unfold `f(σ₁σ₂ … σₙx)` one token at a time.) -/
theorem sigmaElt_append (σ τ : Str) (x : B.Element) :
    sigmaElt (σ ++ τ) x = sigmaElt σ (sigmaElt τ x) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    refine ⟨hY, prepend τ X, ⟨memB_prepend τ (x.sub hX), X, hX, subset_rfl⟩, ?_⟩
    rw [prepend_append]; exact hsub
  · rintro ⟨hY, X, ⟨_, X', hX', hsub'⟩, hsub⟩
    refine ⟨hY, X', hX', ?_⟩
    rw [← prepend_append]
    exact (prepend_mono σ hsub').trans hsub

/-! ### Every element is a union of its finite approximations `σ⊥`. -/

/-- **Factoid (Scott 1981, PRG-19).** "`x = ⋃ₙ σₙ⊥`": every `x ∈ |B|` is the union of the finite
elements `σ⊥` whose generating cone `σΣ*` lies in `x`. In membership form, a neighbourhood `Z`
belongs to `x` iff `Z` lies in some `σ⊥ = ↑(σΣ*)` with `σΣ* ∈ x`.

This is the concrete "an element is uniquely determined by its finite approximations" in `|B|`
(`Basic.eq_iUnion_principal` specialized to `B`, where every neighbourhood is a cone). The further
arrangement of the `σ` into a single increasing chain `σ₀ ⪯ σ₁ ⪯ …` requires choice/enumeration and
is left to Scott's prose. -/
theorem mem_iff_exists_sigmaBot (x : B.Element) {Z : Set Str} :
    x.mem Z ↔ ∃ σ, x.mem (cone σ) ∧ (sigmaBot σ).mem Z := by
  constructor
  · intro hZ
    obtain ⟨σ, rfl⟩ := x.sub hZ
    exact ⟨σ, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨σ, hcone, hZmem, hsub⟩
    exact x.up_mem hcone hZmem hsub

end Scott1980.Neighborhood.ExampleB

/-! ### Inlined from Scott1980/Neighborhood/Example23.lean -/

/-!
# Example 2.3 (Scott 1981, PRG-19, §2) — the parity map `f : B → T`

Scott's first approximable mapping. Reading a binary sequence left to right, count the number `n`
of `0`'s seen *before the first* `1`; the output is `true` if `n` is even, `false` if `n` is odd,
and `⊥` while the input is still an unbroken string of `0`'s (which has consistent extensions of
both parities). Concretely

`f(0ⁿ1⊥) = true` if `n` even, `false` if `n` odd; `f(0^∞) = ⊥`.

Here `B` is the binary system (`ExampleB`) and `T` is the two-token domain of Example 1.2, whose two
total elements we use as `true`/`false` and whose unique partial element is `⊥`.

We model the relation by a parity scanner `scan : Σ* → Option Bool`:
`scan` returns `none` while no `1` has appeared and `some b` (with `b` the parity-of-leading-zeros)
once the first `1` is found. The neighbourhood relation is

`X f Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ valElt (scan σ)`,

where `valElt none = ⊥`, `valElt (some true) = true`, `valElt (some false) = false`. The cone `σΣ*`
has a unique generating prefix (`cone_injective`), so this is well defined, and `scan` is *stable*
under extension (`scan_append`), which is exactly the monotonicity (Def 2.1(iii)).

Definition 2.1(i)–(iii) all check out, giving `parityMap : ApproximableMap B T`. (The `B`-side
reasoning is choice-free; `parityMap` nonetheless pulls `Classical.choice` through the concrete
codomain `T` of Example 1.2, whose `simp`/`fin_cases` proofs already do — pre-existing and harmless.)
-/

namespace Scott1980.Neighborhood.Example23

open Scott1980.Neighborhood NeighborhoodSystem ExampleB

/-- The two-token codomain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- Scott's `true`: the total element `{Δ, {0}}` of `T`. -/
def trueElt : T.Element := Example12.neighborhoodSystem.elemZero

/-- Scott's `false`: the total element `{Δ, {1}}` of `T`. -/
def falseElt : T.Element := Example12.neighborhoodSystem.elemOne

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

/-- The codomain element selected by a parity reading: `none ↦ ⊥`, `some true ↦ true`,
`some false ↦ false`. -/
def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

/-- `⊥` approximates every element of `T` (the local `{Δ}` form, proved directly). -/
theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem

/-- **`⊥` is the unique common lower bound of `true` and `false`.** Any `a : |𝒯|` approximated by
*both* total elements is `⊥` — `𝒯`'s flatness. (Exercise 2.16's uniqueness argument: reading no
tokens yet is the only state consistent with committing to either verdict.) -/
theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  Example12.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1

/-- **The parity scanner.** `scan σ = none` while `σ` is an unbroken run of `0`'s; once a `1`
appears, `scan σ = some b` with `b = true` iff an even number of `0`'s preceded it. A leading `0`
flips the parity of the rest; a leading `1` fixes parity `true` (zero preceding zeros). -/
def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

@[simp] theorem scan_nil : scan [] = none := rfl
@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl
@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl

/-- **A leading `1` always commits to `true`, whatever follows.** `scan([1]++τ) = true`, for
*every* tail `τ`. (Exercise 2.16's first equation, at the token level.) -/
theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

/-- **A leading `01` always commits to `false`, whatever follows.** `scan([0,1]++τ) = false`, for
*every* tail `τ`. (Exercise 2.16's second equation, at the token level.) -/
theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]

/-- **Two leading `0`'s cancel.** `scan([0,0]++τ) = scan τ`: reading two extra zeros flips the
parity twice, i.e. not at all (`Bool.not_not`). (Exercise 2.16's third equation, at the token
level — the recursive step behind the uniqueness argument for the parity map.) -/
theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]

/-- **Stability of the scan under extension.** Once `scan σ` has committed to a parity `some b`,
every extension `σ ++ t` keeps that value. This is the engine of monotonicity for `parityMap`. -/
theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl

/-- **Monotonicity of the parity value.** A longer prefix `σ <+: σ'` yields a (weakly) more defined
value: `valElt (scan σ) ⊑ valElt (scan σ')`. If `scan σ = none` then `valElt = ⊥ ⊑ _`; otherwise the
value is fixed by `scan_append`. -/
theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

/-- **Example 2.3 — the parity mapping `f : B → T`.** `X f Y` iff `X` is the cone `σΣ*` of some
prefix `σ` and `Y` is approximated by the parity verdict `valElt (scan σ)`. Definition 2.1:
(i) the empty prefix scans to `none = ⊥`, and `⊥` contains `Δ_T`; (ii) for a fixed cone the verdict
is a *single* filter (cones have a unique prefix), closed under `∩`; (iii) extending the prefix only
sharpens the verdict (`valElt_scan_mono`). -/
def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    show (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

/-- **`parityMap`'s relation on a cone, read off.** `cone σ f Y ↔ Y ∈ valElt(scan σ)` — the
defining existential collapses since a cone has a *unique* generating prefix (`cone_injective`).
(Used throughout Exercise 2.16's uniqueness argument.) -/
theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

/-- **`parityMap`'s elementwise value, read off cone-by-cone.** `f(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ valElt(scan σ)` — every neighbourhood of `x` is a cone
(`Element.sub`), and `parityMap`'s relation is exactly `parityMap_rel_cone`. -/
theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

/-- **The "shift formula" for `parityMap`.** Reading off the parity of `σx` depends on `x` only
through *some* cone `cone τ ∈ x`, via the scan of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`valElt_scan_mono`), so the longest
one — `σ ++ τ` itself — already witnesses the answer. This is the key computation behind Exercise
2.16's second half: `parityMap` genuinely satisfies its own defining equations. -/
theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

end Scott1980.Neighborhood.Example23

/-! ### Inlined from Scott1980/Neighborhood/Exercise118.lean -/

/-!
# Exercise 1.18 (Scott 1981, PRG-19, §1) — consistent subsets and filter intersections

Scott calls a subset `C ⊆ 𝒟` *consistent* iff every finite subset of `C` is consistent in `𝒟`.
This file formalizes (representing finite subsets as finite sequences drawn from `C`):

* `FinitelyConsistent C` — every finite sequence from `C` is `Consistent`;
* a concrete `C = {A, B, Cc}` (over `Δ = {0,1,2}`, all-non-empty-subsets system) with three
  members, pairwise consistent (`family_pairwise_nonempty`) but **not** consistent
  (`not_finitelyConsistent`) — `A ∩ B ∩ Cc = ∅`;
* `sInf F hF` — the intersection of a non-empty family `F` of filters is a filter, the greatest
  lower bound (`sInf_le`, `le_sInf`);
* `leastFilter C hCsub hC` — the **least** filter containing a consistent `C`, with
  `subset_leastFilter` (`C ⊆` it) and `leastFilter_le` (it is least). The intersection law uses
  the *append* of two finite sequences (`interUpTo_appendSeq`).

Constructive (`[propext, Quot.sound]`) except the counterexample's finite case-analysis.
-/

set_option linter.unusedSimpArgs false

namespace Scott1980.Neighborhood

/-- Concatenation of two finite sequences: the first `n1` entries are `X1 0, …, X1 (n1-1)`,
then `X2 0, X2 1, …`. -/
def appendSeq {α : Type*} (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) : ℕ → Set α :=
  fun i => if i < n1 then X1 i else X2 (i - n1)

/-- Each entry of `appendSeq X1 n1 X2` below `n1 + n2` is drawn from `C`. -/
theorem appendSeq_mem {α : Type*} {C : Set (Set α)} {X1 : ℕ → Set α} {n1 : ℕ}
    {X2 : ℕ → Set α} {n2 : ℕ} (h1 : ∀ i, i < n1 → X1 i ∈ C) (h2 : ∀ i, i < n2 → X2 i ∈ C) :
    ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := by
  intro i hi
  simp only [appendSeq]
  by_cases h : i < n1
  · rw [if_pos h]; exact h1 i h
  · rw [if_neg h]; exact h2 (i - n1) (by omega)

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is contained in the master neighbourhood (its first factor). -/
theorem interUpTo_subset_master (X : ℕ → Set α) : ∀ n, V.interUpTo X n ⊆ V.master := by
  intro n
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact Set.inter_subset_left.trans ih

/-- For a prefix length `k ≤ n1`, `interUpTo` of the appended sequence agrees with `interUpTo`
of the first sequence. -/
theorem interUpTo_appendSeq_left (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {k : ℕ}, k ≤ n1 → V.interUpTo (appendSeq X1 n1 X2) k = V.interUpTo X1 k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [interUpTo_succ, interUpTo_succ, ih (Nat.le_of_succ_le hk)]
    have happ : appendSeq X1 n1 X2 k = X1 k := by
      simp only [appendSeq, if_pos (Nat.lt_of_succ_le hk)]
    rw [happ]

/-- The key identity: `⋂_{i<n1+n2} (X1 ⧺ X2)ᵢ = (⋂_{i<n1} X1ᵢ) ∩ (⋂_{i<n2} X2ᵢ)`. -/
theorem interUpTo_appendSeq (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {j : ℕ}, V.interUpTo (appendSeq X1 n1 X2) (n1 + j)
      = V.interUpTo X1 n1 ∩ V.interUpTo X2 j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, V.interUpTo_appendSeq_left X1 n1 X2 (le_refl n1), interUpTo_zero]
    exact (Set.inter_eq_left.mpr (V.interUpTo_subset_master X1 n1)).symm
  | succ j ih =>
    rw [Nat.add_succ, interUpTo_succ, ih]
    have happ : appendSeq X1 n1 X2 (n1 + j) = X2 j := by
      simp only [appendSeq, if_neg (by omega : ¬ n1 + j < n1)]
      congr 1
      omega
    rw [happ, interUpTo_succ, Set.inter_assoc]

/-! ### Finite consistency. -/

/-- **Exercise 1.18 — consistent subset.** `C ⊆ 𝒟` is *finitely consistent* iff every finite
sequence drawn from `C` is `Consistent` in `𝒟`. -/
def FinitelyConsistent (C : Set (Set α)) : Prop :=
  ∀ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) → V.Consistent X n

/-! ### Intersection of a non-empty family of filters (Scott's last claim). -/

/-- **Exercise 1.18 — the intersection of a non-empty family of filters is a filter.**
`sInf F = {X ∣ ∀ x ∈ F, X ∈ x}`. -/
def sInf (F : Set V.Element) (hF : F.Nonempty) : V.Element where
  mem X := ∀ x ∈ F, x.mem X
  sub h := hF.elim (fun x hx => x.sub (h x hx))
  master_mem := fun x _ => x.master_mem
  inter_mem h1 h2 := fun x hx => x.inter_mem (h1 x hx) (h2 x hx)
  up_mem h hY hXY := fun x hx => x.up_mem (h x hx) hY hXY

/-- `sInf F ⊑ x` for every `x ∈ F`. -/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

/-- `sInf F` is the **greatest** lower bound of `F`. -/
theorem le_sInf (F : Set V.Element) (hF : F.Nonempty) (y : V.Element) (h : ∀ x ∈ F, y ≤ x) :
    y ≤ V.sInf F hF :=
  fun _ hX x hx => h x hx _ hX

/-! ### The least filter containing a consistent `C`. -/

/-- **Exercise 1.18 — the least filter containing a consistent `C`.**
`leastFilter C = {Y ∈ 𝒟 ∣ ⋂_{i<n} Xᵢ ⊆ Y for some finite sequence ⟨Xᵢ⟩ from C}`. The
intersection law concatenates two finite sequences (`interUpTo_appendSeq`) and uses finite
consistency to keep their combined intersection in `𝒟`. -/
def leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) : V.Element where
  mem Y := V.mem Y ∧ ∃ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) ∧ V.interUpTo X n ⊆ Y
  sub h := h.1
  master_mem :=
    ⟨V.master_mem, 0, (fun _ => V.master), (fun i hi => absurd hi (Nat.not_lt_zero i)),
      V.interUpTo_subset_master _ 0⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n1, X1, hX1C, hX1sub⟩ ⟨hYmem, n2, X2, hX2C, hX2sub⟩
    have hmemC : ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := appendSeq_mem hX1C hX2C
    have hintermem : V.mem (V.interUpTo (appendSeq X1 n1 X2) (n1 + n2)) :=
      (V.consistent_iff_interUpTo_mem _ (fun i hi => hCsub _ (hmemC i hi))).mp
        (hC _ _ hmemC)
    have hsub : V.interUpTo (appendSeq X1 n1 X2) (n1 + n2) ⊆ X ∩ Y := by
      rw [V.interUpTo_appendSeq X1 n1 X2]
      exact Set.inter_subset_inter hX1sub hX2sub
    exact ⟨V.inter_mem hXmem hYmem hintermem hsub, n1 + n2, appendSeq X1 n1 X2, hmemC, hsub⟩
  up_mem := by
    rintro X Y ⟨_, n, Xs, hXC, hsub⟩ hY hXY
    exact ⟨hY, n, Xs, hXC, hsub.trans hXY⟩

/-- `C ⊆ leastFilter C`: every member of `C` is in the least filter. -/
theorem subset_leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) {W : Set α} (hW : W ∈ C) :
    (V.leastFilter C hCsub hC).mem W := by
  refine ⟨hCsub W hW, 1, (fun _ => W), (fun _ _ => hW), ?_⟩
  rw [interUpTo_succ, interUpTo_zero]
  exact Set.inter_subset_right

/-- **Exercise 1.18 — `leastFilter` is least.** Any filter `z` with `C ⊆ z` contains
`leastFilter C`. -/
theorem leastFilter_le (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) (z : V.Element) (hz : ∀ W ∈ C, z.mem W) :
    V.leastFilter C hCsub hC ≤ z := by
  rintro Y ⟨hYmem, n, X, hXC, hsub⟩
  exact z.up_mem (z.mem_interUpTo X (fun i hi => hz (X i) (hXC i hi))) hYmem hsub

end NeighborhoodSystem

/-! ### A 3-element pairwise-consistent but not consistent set. -/

/-- All non-empty subsets of `Δ = {0,1,2}` (a positive neighbourhood system). -/
def triSys : NeighborhoodSystem (Fin 3) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (⟨0, Set.mem_univ 0⟩) (⟨0, Set.mem_univ 0⟩)
    (fun {_} _ => Set.subset_univ _) (fun _ _ _ _ => Iff.rfl)

theorem triSys_master : triSys.master = (Set.univ : Set (Fin 3)) := rfl

namespace triSys

/-- `A = {0,1}`. -/
def A : Set (Fin 3) := {0, 1}
/-- `B = {1,2}`. -/
def B : Set (Fin 3) := {1, 2}
/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

/-- The three-member family `C = {A, B, Cc}`. -/
def family : Set (Set (Fin 3)) := {A, B, Cc}

/-- Every pair of members of `family` has non-empty intersection, hence (in the all-non-empty
system `triSys`) every pair is consistent. -/
theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩

/-- The triple `A, B, Cc` as a finite sequence. -/
def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

theorem triple_mem : ∀ i, i < 3 → triple i ∈ family := by
  intro i hi
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem triple_interUpTo_empty : triSys.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo_succ, NeighborhoodSystem.interUpTo_zero, triSys_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

/-- **Exercise 1.18 — `family` is pairwise consistent but not consistent.** Its full triple has
empty intersection, so no `Z ∈ 𝒟` (i.e. no non-empty `Z`) lies below it. -/
theorem not_finitelyConsistent : ¬ triSys.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  rw [hZsub] at hZne
  exact Set.not_nonempty_empty hZne

end triSys

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise122.lean -/

/-!
# Exercise 1.22 (Scott 1981, PRG-19, §1) — the topology on `|𝒟|`

> **EXERCISE 1.22.** (For topologists). Show that the neighbourhoods `[X]` for `X ∈ 𝒟` make
> `|𝒟|` into a topological space where the open subsets `𝒰 ⊆ |𝒟|` can be characterized by the
> following two conditions:
>
> (i)  whenever `x ∈ 𝒰` and `x ⊑ y ∈ |𝒟|`, then `y ∈ 𝒰`; and
> (ii) whenever `x ∈ 𝒰`, then `[X] ⊆ 𝒰` for some `X ∈ x`.
>
> Prove also that the inclusion relation on `|𝒟|` can be defined topologically as:
>
> (iii) `x ⊑ y` iff for all open `𝒰 ⊆ |𝒟|`, if `x ∈ 𝒰` then `y ∈ 𝒰`.

Here `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Scott's notation from Theorem 1.10): the set of elements
(filters) of which `X` is a member. We call it `basicOpen X`.

## What is proved

* `basicOpen` — Scott's `[X]`, with `mem_basicOpen` the membership unfolding.
* `instTopologicalSpaceElement` — the topology on `V.Element`: `𝒰` is open iff every point of
  `𝒰` has a basic neighbourhood `[X]` (`X ∈ x`) contained in `𝒰`. This is condition (ii); the
  three topology axioms are verified directly (the basic opens are closed under finite `∩`, with
  `[Δ] = |𝒟|` the whole space, so they form a base).
* `isOpen_basicOpen` — each `[X]` is open.
* `isOpen_iff_upper_basic` — the characterization: `IsOpen 𝒰 ↔ (i) ∧ (ii)`. Note (ii) already
  pins down openness; (i) (upward closure under `⊑`) is a *consequence* of (ii), recorded
  separately as `isOpen_isUpperSet`. We keep both to match Scott's statement.
* `le_iff_isOpen_imp` — condition (iii): `x ⊑ y ↔ ∀ 𝒰 open, x ∈ 𝒰 → y ∈ 𝒰`. This says `⊑` is
  the (opposite of the) specialization preorder; `specializes_iff_le` makes the bridge to
  Mathlib's `⤳` explicit.

The space is **T₀** but not in general **T₁**/Hausdorff (the specialization order `⊑` is a genuine
partial order, recoverable from the topology by (iii)); the open-ended limit-point questions of the
exercise need Definition 1.7 (`↑X`) and are deferred.
-/

namespace Scott1980.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Theorem 1.10 notation): the set of elements of the domain
`|𝒟|` that contain the neighbourhood `X`. These sets are the basic opens of the topology of
Exercise 1.22. -/
def basicOpen (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_basicOpen {X : Set α} {x : V.Element} :
    x ∈ V.basicOpen X ↔ x.mem X := Iff.rfl

/-- `[X ∩ Y] ⊆ [X]` whenever `X ∈ 𝒟`: a filter containing `X ∩ Y` contains `X` (upward closure).
This (with the symmetric version) is the closure of the basic opens under finite intersection,
i.e. `[X] ∩ [Y] = [X ∩ Y]`, the base condition behind the topology. -/
theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

/-- `[X ∩ Y] ⊆ [Y]` whenever `Y ∈ 𝒟`. -/
theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right

/-- A set `𝒰 ⊆ |𝒟|` is *open* (Exercise 1.22, condition (ii)) when every point `x ∈ 𝒰` has a
basic neighbourhood `[X]` with `X ∈ x` contained in `𝒰`. -/
def IsOpenFilter (U : Set V.Element) : Prop :=
  ∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U

/-- **Exercise 1.22 (the space).** The basic opens `[X]` (`X ∈ 𝒟`) generate a topology on `|𝒟|`:
`𝒰` is open iff it is a union of basic opens (condition (ii)). The three axioms hold because the
base is closed under finite intersection (`basicOpen_inter_subset_left/right`, using that filters
are `∩`-closed and upward closed) with `[Δ] = |𝒟|` covering the space. -/
instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.IsOpenFilter
  isOpen_univ := fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩
  isOpen_inter := by
    intro U W hU hW x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU x hxU
    obtain ⟨Y, hY, hYW⟩ := hW x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := hS t htS x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩

/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.IsOpenFilter U := Iff.rfl

/-- **Exercise 1.22.** Each basic neighbourhood `[X]` is open. -/
theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  fun _ hx => ⟨X, hx, subset_rfl⟩

/-- **Exercise 1.22, condition (i).** Every open set is upward closed under the approximation order
`⊑`: if `x ∈ 𝒰` and `x ⊑ y` then `y ∈ 𝒰`. (This is a *consequence* of (ii): the basic
neighbourhood `[X] ⊆ 𝒰` witnessing `x ∈ 𝒰` also contains every `y ⊒ x`.) -/
theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU x hxU
  exact hXU (hxy X hX)

/-- **Exercise 1.22 (characterization of open sets).** A subset `𝒰 ⊆ |𝒟|` is open iff
(i) it is upward closed under `⊑`, and (ii) every point of `𝒰` has a basic neighbourhood `[X]`
(`X ∈ x`) contained in `𝒰`. -/
theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU⟩
  · rintro ⟨_, h2⟩
    exact h2

/-- **Exercise 1.22, condition (iii).** The approximation order is recovered from the topology:
`x ⊑ y` iff every open set containing `x` also contains `y`.

* `→` is upward closure of opens (`isOpen_isUpperSet`);
* `←` tests against the open basic neighbourhood `[X]` for each `X ∈ x`. -/
theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

/-- The approximation order `⊑` is the opposite of Mathlib's specialization preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm

end NeighborhoodSystem

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise127.lean -/

/-!
# Exercise 1.27 (Scott 1981, PRG-19, §1) — bounded sets and least upper bounds

Scott introduces *bounded* sets of elements as the analogue, for `|𝒟|`, of *consistent*
sequences of neighbourhoods. A set `X ⊆ |𝒟|` is **bounded** iff it has an upper bound
`y ∈ |𝒟|` (`x ⊑ y` for all `x ∈ X`), and then

`⊔X = ⋂ {y ∣ x ⊑ y for all x ∈ X}`

is its **least upper bound**. This file formalizes:

* `Bounded X` and `sSup X hX := sInf (upper bounds of X)` — the upper-bound family is non-empty
  exactly because `X` is bounded, so we reuse `sInf` from Exercise 1.18; the lub laws
  `le_sSup` / `sSup_le` are then immediate from `le_sInf` / `sInf_le`;
* `consistent_pair_iff_bounded` — for `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is `Consistent` iff
  `{↑U, ↑W}` is bounded ("boundedness is for elements what consistency is for neighbourhoods");
* `bounded_iff_finite_bounded` — **with the aid of Exercise 1.18**, `X` is bounded iff every
  *finite* subset of `X` is bounded; the hard direction builds the bound as the `leastFilter`
  of `C = ⋃_{x∈X} x`, whose finite consistency comes from the finite bounds.

The constructions (`sSup`) are `[propext, Quot.sound]`. The hard direction of
`bounded_iff_finite_bounded` selects a finite witness set via `Classical.choice`; this is a
*proof*, so the construction stays choice-free.
-/

namespace Scott1980.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.27 — bounded set of elements.** `X ⊆ |𝒟|` is *bounded* iff it has an upper
bound `y ∈ |𝒟|`: `x ⊑ y` for all `x ∈ X`. -/
def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

/-- If `X` is bounded then its upper-bound family is non-empty (it contains the witness). -/
theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

/-- **Exercise 1.27 — `⊔X`.** The least upper bound of a bounded `X`, defined à la Scott as the
intersection of all upper bounds: `⊔X = ⋂ {y ∣ x ⊑ y all x∈X}`. Reusing `sInf` from Exercise
1.18 on the (non-empty, because bounded) family of upper bounds. -/
def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

/-- **Exercise 1.27 — `⊔X` is an upper bound.** Each `x ∈ X` satisfies `x ⊑ ⊔X`. -/
theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

/-- **Exercise 1.27 — `⊔X` is least.** Any upper bound `z` of `X` satisfies `⊔X ⊑ z`. -/
theorem sSup_le (X : Set V.Element) (hX : V.Bounded X) {z : V.Element}
    (hz : ∀ x ∈ X, x ≤ z) : V.sSup X hX ≤ z :=
  V.sInf_le (V.upperBounds X) (V.upperBounds_nonempty hX) hz

/-! ### Boundedness of `{↑U, ↑W}` ⟺ consistency of `⟨U, W⟩`. -/

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase `Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

theorem interUpTo_pairSeq (U W : Set α) :
    V.interUpTo (pairSeq U W) 2 = V.master ∩ U ∩ W := by
  simp only [interUpTo_succ, interUpTo_zero, pairSeq]
  norm_num

/-- **Exercise 1.27 — "boundedness is for elements what consistency is for neighbourhoods".**
For `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is consistent in `𝒟` iff `{↑U, ↑W}` is bounded in `|𝒟|`.

`→` packages the consistency witness `Z` into the principal filter `↑Z`, which lies above both
`↑U` and `↑W` (via `principal_le_iff`). `←` uses that any bound `y` contains both `U` and `W`,
hence `U ∩ W ∈ y ⊆ 𝒟`, giving `U ∩ W` as the consistency witness. -/
theorem consistent_pair_iff_bounded {U W : Set α} (hU : V.mem U) (hW : V.mem W) :
    V.Consistent (pairSeq U W) 2 ↔ V.Bounded {V.principal hU, V.principal hW} := by
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩
    rw [V.interUpTo_pairSeq] at hZsub
    have hZU : Z ⊆ U := hZsub.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    have hZW : Z ⊆ W := hZsub.trans Set.inter_subset_right
    refine ⟨V.principal hZmem, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact (V.principal_le_iff hU hZmem).mpr hZU
    · exact (V.principal_le_iff hW hZmem).mpr hZW
  · rintro ⟨y, hy⟩
    have hyU : y.mem U :=
      hy _ (Or.inl rfl) U ⟨hU, subset_rfl⟩
    have hyW : y.mem W :=
      hy _ (Or.inr rfl) W ⟨hW, subset_rfl⟩
    have hyUW : y.mem (U ∩ W) := y.inter_mem hyU hyW
    refine ⟨U ∩ W, y.sub hyUW, ?_⟩
    rw [V.interUpTo_pairSeq]
    intro z hz
    exact ⟨⟨V.sub_master hU hz.1, hz.1⟩, hz.2⟩

/-! ### Boundedness is finitary (with the aid of Exercise 1.18). -/

/-- **Exercise 1.27 — boundedness is finitary.** `X ⊆ |𝒟|` is bounded iff every *finite* subset
of `X` is bounded. The forward direction reuses any global bound. The reverse direction is the
content: assemble `C = ⋃_{x∈X} x` (the neighbourhoods of all members of `X`); `C` is finitely
consistent because any finite sequence drawn from `C` comes from finitely many members of `X`,
which form a finite subset, hence bounded — that bound's filter contains the whole finite
sequence, so its intersection lies in `𝒟`. The least filter `leastFilter C` (Exercise 1.18) is
then an upper bound of `X`. -/
theorem bounded_iff_finite_bounded (X : Set V.Element) :
    V.Bounded X ↔ ∀ S : Set V.Element, S ⊆ X → S.Finite → V.Bounded S := by
  constructor
  · rintro ⟨y, hy⟩ S hS _
    exact ⟨y, fun x hx => hy x (hS hx)⟩
  · intro hfin
    set C : Set (Set α) := {Z | ∃ x : V.Element, x ∈ X ∧ x.mem Z} with hCdef
    have hCsub : ∀ Z ∈ C, V.mem Z := by rintro Z ⟨x, _, hxZ⟩; exact x.sub hxZ
    have hCcons : V.FinitelyConsistent C := by
      intro n seq hseqC
      choose g hgX hgmem using hseqC
      set S : Set V.Element := Set.range (fun i : Fin n => g i.1 i.2) with hSdef
      have hSfin : S.Finite := Set.finite_range _
      have hSsub : S ⊆ X := by
        rintro _ ⟨i, rfl⟩
        exact hgX i.1 i.2
      obtain ⟨y, hy⟩ := hfin S hSsub hSfin
      have hseqy : ∀ i, i < n → y.mem (seq i) := by
        intro i hi
        have hle : g i hi ≤ y := hy _ ⟨⟨i, hi⟩, rfl⟩
        exact hle (seq i) (hgmem i hi)
      have hmem : y.mem (V.interUpTo seq n) := y.mem_interUpTo seq hseqy
      exact ⟨V.interUpTo seq n, y.sub hmem, subset_rfl⟩
    refine ⟨V.leastFilter C hCsub hCcons, ?_⟩
    intro x hx Z hZ
    exact V.subset_leastFilter C hCsub hCcons ⟨x, hx, hZ⟩

end NeighborhoodSystem

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise213.lean -/

/-!
# Exercise 2.13 (Scott 1981, PRG-19, §2) — approximable maps **are** the continuous functions

> **EXERCISE 2.13.** (For topologists.) Recall Exercise 1.22 where it was shown that any domain
> `|𝒟|` is a topological space. Prove from Exercise 2.9 that the functions `f : |𝒟₀| → |𝒟₁|`
> determined by approximable mappings are exactly *the continuous functions between these spaces.*

This file closes the loop between the §2 theory of approximable mappings (`Approximable.lean`,
`ApproximableExercises.lean`) and the Exercise 1.22 topology on `|𝒟|` (`Exercise122.lean`):

* **`continuous_toElementMap`** — every approximable mapping `f` induces a *continuous* function
  `x ↦ f(x)`. Scott's hint: by Exercise 2.9, `f⁻¹[Y] = ⋃ {[X] ∣ Y ∈ f(↑X)}`, so the inverse image
  of a basic open is a union of basic opens, hence open.
* **`continuous_monotone`** — a continuous `c : |𝒟₀| → |𝒟₁|` is monotone for `⊑` (the order is the
  specialization order, `le_iff_isOpen_imp`).
* **`mem_iff_principal_of_continuous`** — Scott's union formula for a *continuous* `c`:
  `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`. (Forward: `c⁻¹[X]` open ∋ `x`; reverse: `↑X ⊑ x` + monotone.)
* **`ofContinuous`** — the approximable mapping of a continuous function, built from `ofMono` on the
  finite elements `↑X ↦ c(↑X)` (monotone by `continuous_monotone`).
* **`toElementMap_ofContinuous`** — the round trip: `ofContinuous c hc` induces exactly `c`
  (`(ofContinuous c hc)(x) = c(x)`), combining Exercise 2.9 with the union formula.

Together: `f ↦ toElementMap f` and `c ↦ ofContinuous c` exhibit approximable mappings `𝒟₀ → 𝒟₁`
and continuous functions `|𝒟₀| → |𝒟₁|` as the same thing.

Choice-free apart from the `ofMono`/Exercise-2.9 ingredients (whose uniqueness companions are the
only classical pieces). -/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- **Exercise 2.13 (forward).** The elementwise function of an approximable mapping is continuous.
For an open `U` and `x` with `f(x) ∈ U`, openness gives `Y` with `Y ∈ f(x)` and `[Y] ⊆ U`; unfolding
`Y ∈ f(x)` produces `X ∈ x` with `X f Y`; then `[X] ⊆ f⁻¹U`, since any `x' ∈ [X]` has `Y ∈ f(x')`
(via `X f Y`). -/
theorem continuous_toElementMap (f : ApproximableMap V₀ V₁) :
    Continuous (fun x => f.toElementMap x) := by
  rw [continuous_def]
  intro U hU
  show V₀.IsOpenFilter _
  intro x hx
  obtain ⟨Y, hY, hYU⟩ := hU (f.toElementMap x) hx
  obtain ⟨X, hxX, hrel⟩ := hY
  exact ⟨X, hxX, fun x' hx' => hYU ⟨X, hx', hrel⟩⟩

end ApproximableMap

namespace NeighborhoodSystem

/-- A continuous function between domains is monotone for the approximation order `⊑`: this is
because `⊑` is recoverable from the topology (`le_iff_isOpen_imp`) and continuous preimages of opens
are open and upward closed (`isOpen_isUpperSet`). -/
theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

/-- **Exercise 2.13 — Scott's union formula for a continuous map.** For continuous `c` and any
`x ∈ |𝒟₀|`: `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`.

* `→` : `c⁻¹[[Y]]` is open and contains `x`, so it contains a basic neighbourhood `[X]` with `X ∈ x`;
  since `↑X ∈ [X]`, `Y ∈ c(↑X)`.
* `←` : `↑X ⊑ x` and `c` monotone (`continuous_monotone`) give `c(↑X) ⊑ c(x)`, transporting `Y`. -/
theorem mem_iff_principal_of_continuous {c : V₀.Element → V₁.Element} (hc : Continuous c)
    (x : V₀.Element) {Y : Set β} :
    (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y := by
  constructor
  · intro hY
    have hxpre : x ∈ c ⁻¹' V₁.basicOpen Y := hY
    have hopen : IsOpen (c ⁻¹' V₁.basicOpen Y) := (V₁.isOpen_basicOpen Y).preimage hc
    obtain ⟨X, hxX, hXU⟩ := hopen x hxpre
    refine ⟨X, hxX, ?_⟩
    exact hXU (show V₀.principal (x.sub hxX) ∈ V₀.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
  · rintro ⟨X, hxX, hY⟩
    have hple : V₀.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact (continuous_monotone hc hple) Y hY

/-- **Algebraicity.** Every element `x` is the directed union of its own principal
("finite"/compact) approximants: `x = ⋃ {↑X ∣ X ∈ x}`, literally as an `iSupDirected`. (Used below
to reduce continuity checks to principal elements; a duplicate of `Theorem85.lean`'s own copy,
kept local here to avoid a heavy import for this early file.) -/
instance instNonemptyMemSubtype (x : V₀.Element) : Nonempty {X : Set α // x.mem X} :=
  ⟨⟨V₀.master, x.master_mem⟩⟩

theorem principalFamily_directed (x : V₀.Element) :
    ∀ i j : {X : Set α // x.mem X}, ∃ k : {X : Set α // x.mem X},
      V₀.principal (x.sub i.2) ≤ V₀.principal (x.sub k.2) ∧
        V₀.principal (x.sub j.2) ≤ V₀.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V₀.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V₀.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

theorem eq_iSupDirected_principal (x : V₀.Element) :
    x = iSupDirected (fun i : {X : Set α // x.mem X} => V₀.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V₀.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V₀.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

/-- **The converse of `continuous_toElementMap`/`continuous_monotone`, in domain-theoretic form.**
A monotone function that also preserves directed unions is topologically continuous — the standard
"Scott continuity ⟺ order-theoretic continuity" bridge, proved directly from algebraicity rather
than through a general topological-basis argument: given `x ∈ c⁻¹U`, decompose `x` as the directed
union of its principal approximants (`eq_iSupDirected_principal`); `c` preserving the union puts
`c x` there too, so openness of `U` finds a witness `Y` in *some* `c(↑X)` (`X ∈ x`); monotonicity of
`c` then transfers `Y ∈ c(↑X)` up to every `x' ∈ [X]`, giving `[X] ⊆ c⁻¹U`. -/
theorem continuous_of_monotone_iSupDirected {c : V₀.Element → V₁.Element} (hmono : Monotone c)
    (hsup : ∀ {I : Type u} [Nonempty I] (d : I → V₀.Element)
      (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
      (hdir' : ∀ i j, ∃ k, c (d i) ≤ c (d k) ∧ c (d j) ≤ c (d k)),
      c (iSupDirected d hdir) = iSupDirected (fun i => c (d i)) hdir') :
    Continuous c := by
  rw [continuous_def]
  intro U hU x hx
  rw [Set.mem_preimage] at hx
  set fam : {X : Set α // x.mem X} → V₀.Element := fun i => V₀.principal (x.sub i.2) with hfam
  have hdir : ∀ i j : {X : Set α // x.mem X}, ∃ k, fam i ≤ fam k ∧ fam j ≤ fam k :=
    principalFamily_directed x
  have hdir' : ∀ i j : {X : Set α // x.mem X}, ∃ k, c (fam i) ≤ c (fam k) ∧ c (fam j) ≤ c (fam k) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hdir i j; exact ⟨k, hmono hik, hmono hjk⟩
  have hxeq : c x = iSupDirected (fun i => c (fam i)) hdir' :=
    (congrArg c (eq_iSupDirected_principal x)).trans
      (hsup (I := {X : Set α // x.mem X}) fam hdir hdir')
  rw [hxeq] at hx
  obtain ⟨Y, hY, hYU⟩ := hU _ hx
  obtain ⟨i, hi⟩ := (mem_iSupDirected _ hdir').mp hY
  refine ⟨i.1, i.2, fun x' hx' => hYU ?_⟩
  have hple : fam i ≤ x' := fun Z hZ => x'.up_mem hx' hZ.1 hZ.2
  exact (hmono hple) Y hi

end NeighborhoodSystem

namespace ApproximableMap

/-- **Exercise 2.13 (reverse).** The approximable mapping determined by a continuous function `c`:
its action on the finite element `↑X` is the value `c(↑X)`, extended to all of `𝒟₀` via `ofMono`.
Monotonicity of `X ↦ c(↑X)` is `continuous_monotone` together with the inclusion-reversal
`X' ⊆ X ↔ ↑X ⊑ ↑X'`. -/
def ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c) : ApproximableMap V₀ V₁ :=
  ofMono (fun _X hX => c (V₀.principal hX))
    (fun _X _X' hX hX' hX'X =>
      NeighborhoodSystem.continuous_monotone hc ((V₀.principal_le_iff hX hX').mpr hX'X))

/-- **Exercise 2.13 — the round trip.** `ofContinuous c hc` induces exactly `c`:
`(ofContinuous c hc)(x) = c(x)` for all `x`. Exercise 2.9 reduces `f(x)` to a union over finite
approximants `↑X` (`X ∈ x`), where `ofMono` evaluates to `c(↑X)`; the union formula
`mem_iff_principal_of_continuous` then re-assembles `c(x)`. -/
theorem toElementMap_ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c)
    (x : V₀.Element) : (ofContinuous c hc).toElementMap x = c x := by
  apply Element.ext
  intro Y
  rw [toElementMap_mem_iff_principal, NeighborhoodSystem.mem_iff_principal_of_continuous hc]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal] at hmem
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal]

end ApproximableMap

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise222.lean -/

/-!
# Exercise 2.22 (Scott 1981, PRG-19) — the abstract representation theorem

(*For set theorists.*) Exercises 1.18 and 2.11 noted that any domain `|𝒟|`, viewed as a family of
sets, is closed under (i) the intersection of an arbitrary **non-empty** subfamily and (ii) the union
of any **directed** subfamily. This exercise proves the converse: *any* family `C` of sets with these
two closure properties is inclusion-isomorphic to a domain.

We follow Scott's hint. Fix `C : Set (Set τ)` (non-empty) closed under non-empty intersections
(`hInter`) and directed unions (`hDir`).

* `Δ` = the **finite** sets `F` included in some member of `C` (here the subtype `Tok C`).
* The **closure** of `F` is `F̄ = ⋂ {X ∈ C ∣ F ⊆ X}` (`Cl C F`); since `F` lies in some member of
  `C`, this intersection is over a non-empty family, so `F̄ ∈ C` (`Cl_mem`). The `F̄` are the "finite"
  elements.
* The neighbourhood system `reprSystem` over `Δ` has neighbourhoods `C(F) = {G ∈ Δ ∣ F ⊆ Ḡ}`
  (`nbhd C F`).

The representation isomorphism `reprIso : reprSystem.Element ≃o C` (under `⊆`) sends an ideal element
`x` to `⋃ {F̄ ∣ C(F) ∈ x}` and a set `X ∈ C` to the element generated by `{C(F) ∣ F ⊆ X}`. The key
identity (Scott) is `X = ⋃ {F̄ ∣ F ⊆ X, F ∈ Δ}`, realized by `toC_ofC`/`mem_nbhd_iff`.

**Axioms.** This is the genuinely set-theoretic exercise: it uses `Classical.choice` (picking witnesses
of `C.Nonempty`, finite-set induction). This is documented and expected per the exercise's framing
("for set theorists").
-/

namespace Scott1980.Neighborhood.Exercise222

open Scott1980.Neighborhood NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-! ### Closure and tokens. -/

/-- The **closure** `F̄ = ⋂ {X ∈ C ∣ F ⊆ X}` of a set `F` relative to the family `C`. -/
def Cl (F : Set τ) : Set τ := ⋂₀ {X | X ∈ C ∧ F ⊆ X}

/-- `F ⊆ F̄`: a set is contained in its closure. -/
theorem subset_Cl (F : Set τ) : F ⊆ Cl C F := by
  intro t ht
  rw [Cl, Set.mem_sInter]
  intro X hX
  exact hX.2 ht

/-- `F̄ ⊆ X` whenever `X ∈ C` contains `F`: the closure is the *smallest* member of `C` over `F`. -/
theorem Cl_subset {F X : Set τ} (hX : X ∈ C) (hFX : F ⊆ X) : Cl C F ⊆ X := by
  intro t ht
  exact (Set.mem_sInter.mp ht) X ⟨hX, hFX⟩

/-- A token: a finite set included in some member of `C`. -/
def IsTok (F : Set τ) : Prop := F.Finite ∧ ∃ X ∈ C, F ⊆ X

/-- Scott's `Δ`: the type of tokens (finite sets included in members of `C`). -/
abbrev Tok := {F : Set τ // IsTok C F}

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- Every closure `F̄` of a token lies in `C` (closure under non-empty intersection). -/
theorem Cl_mem {F : Set τ} (h : ∃ X ∈ C, F ⊆ X) : Cl C F ∈ C := by
  show ⋂₀ {X | X ∈ C ∧ F ⊆ X} ∈ C
  apply hInter
  · obtain ⟨X, hX, hFX⟩ := h
    exact ⟨X, hX, hFX⟩
  · intro X hX
    exact hX.1

/-! ### The neighbourhood system `reprSystem`. -/

/-- Scott's neighbourhood `C(F) = {G ∈ Δ ∣ F ⊆ Ḡ}`. -/
def nbhd (F : Set τ) : Set (Tok C) := {G | F ⊆ Cl C G.1}

@[simp] theorem mem_nbhd {F : Set τ} {G : Tok C} : G ∈ nbhd C F ↔ F ⊆ Cl C G.1 := Iff.rfl

include hInter in
/-- `C(F) ⊆ C(G) ↔ G ⊆ F̄`: comparison of neighbourhoods reduces to inclusion against closures. -/
theorem nbhd_subset_iff {F G : Set τ} (hF : IsTok C F) :
    nbhd C F ⊆ nbhd C G ↔ G ⊆ Cl C F := by
  constructor
  · intro h
    have hmem : (⟨F, hF⟩ : Tok C) ∈ nbhd C F := subset_Cl C F
    exact h hmem
  · intro hG H hH
    exact hG.trans (Cl_subset C (Cl_mem C hInter H.2.2) hH)

/-- `C(∅) = Δ`: the empty token's neighbourhood is everything (the master). -/
theorem nbhd_empty : nbhd C (∅ : Set τ) = Set.univ := by
  ext G
  simp [nbhd]

variable (hne : C.Nonempty)

include hne in
/-- The empty token `∅ ∈ Δ` (needs `C` non-empty for `∅` to lie in some member). -/
def botTok : Tok C := ⟨∅, Set.finite_empty, hne.choose, hne.choose_spec, Set.empty_subset _⟩

include hInter hne in
/-- **The representation neighbourhood system** `reprSystem` over `Δ = Tok C`: neighbourhoods are
exactly the `C(F)` for tokens `F`, the master is all of `Δ = C(∅)`. -/
def reprSystem : NeighborhoodSystem (Tok C) where
  mem N := ∃ F : Tok C, N = nbhd C F.1
  master := Set.univ
  master_nonempty := ⟨botTok C hne, Set.mem_univ _⟩
  master_mem := ⟨botTok C hne, (nbhd_empty C).symm⟩
  inter_mem := by
    rintro X Y Z ⟨F, rfl⟩ ⟨F', rfl⟩ ⟨F'', rfl⟩ hZsub
    have hF''mem : (F'' : Tok C) ∈ nbhd C F''.1 := subset_Cl C F''.1
    have h := hZsub hF''mem
    have hClF'' : Cl C F''.1 ∈ C := Cl_mem C hInter F''.2.2
    have hunionsub : F.1 ∪ F'.1 ⊆ Cl C F''.1 := Set.union_subset h.1 h.2
    refine ⟨⟨F.1 ∪ F'.1, F.2.1.union F'.2.1, Cl C F''.1, hClF'', hunionsub⟩, ?_⟩
    ext G
    simp only [mem_nbhd, Set.mem_inter_iff, Set.union_subset_iff]
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem mem_reprSystem {N : Set (Tok C)} :
    (reprSystem C hInter hne).mem N ↔ ∃ F : Tok C, N = nbhd C F.1 := Iff.rfl

@[simp] theorem reprSystem_master : (reprSystem C hInter hne).master = Set.univ := rfl

/-! ### From an element to a set of `C`: `x ↦ ⋃ {F̄ ∣ C(F) ∈ x}`. -/

/-- The family `{F̄ ∣ C(F) ∈ x}` of finite-element closures present in the ideal element `x`. -/
def famC (x : (reprSystem C hInter hne).Element) : Set (Set τ) :=
  {Y | ∃ F : Tok C, x.mem (nbhd C F.1) ∧ Y = Cl C F.1}

/-- Scott's `⋃ {F̄ ∣ C(F) ∈ x}`: the set of `C` represented by the ideal element `x`. -/
def toC (x : (reprSystem C hInter hne).Element) : Set τ := ⋃₀ famC C hInter hne x

theorem mem_toC (x : (reprSystem C hInter hne).Element) {t : τ} :
    t ∈ toC C hInter hne x ↔ ∃ F : Tok C, x.mem (nbhd C F.1) ∧ t ∈ Cl C F.1 := by
  simp only [toC, famC, Set.mem_sUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Y, ⟨F, hF, rfl⟩, ht⟩
    exact ⟨F, hF, ht⟩
  · rintro ⟨F, hF, ht⟩
    exact ⟨Cl C F.1, ⟨F, hF, rfl⟩, ht⟩

/-- **Directedness step.** If `C(F), C(F') ∈ x` then there is a token `F₃` with `C(F₃) ∈ x` whose
closure dominates both `F̄` and `F̄'`. (From the filter intersection `C(F) ∩ C(F') ∈ x`, which is
some `C(F₃)`.) -/
theorem directed_step (x : (reprSystem C hInter hne).Element) {F F' : Tok C}
    (hF : x.mem (nbhd C F.1)) (hF' : x.mem (nbhd C F'.1)) :
    ∃ F₃ : Tok C, x.mem (nbhd C F₃.1) ∧ Cl C F.1 ⊆ Cl C F₃.1 ∧ Cl C F'.1 ⊆ Cl C F₃.1 := by
  have hinter : x.mem (nbhd C F.1 ∩ nbhd C F'.1) := x.inter_mem hF hF'
  have hmemD : (reprSystem C hInter hne).mem (nbhd C F.1 ∩ nbhd C F'.1) := x.sub hinter
  obtain ⟨F₃, hF₃eq⟩ := hmemD
  rw [hF₃eq] at hinter
  have hF₃self : (F₃ : Tok C) ∈ nbhd C F₃.1 := subset_Cl C F₃.1
  rw [← hF₃eq] at hF₃self
  refine ⟨F₃, hinter, ?_, ?_⟩
  · exact Cl_subset C (Cl_mem C hInter F₃.2.2) hF₃self.1
  · exact Cl_subset C (Cl_mem C hInter F₃.2.2) hF₃self.2

/-- The empty token's neighbourhood `C(∅) = Δ` is in every element (it is the master). -/
theorem mem_nbhd_bot (x : (reprSystem C hInter hne).Element) :
    x.mem (nbhd C (botTok C hne).1) := by
  have h : (botTok C hne).1 = (∅ : Set τ) := rfl
  rw [h, nbhd_empty C]
  exact x.master_mem

/-- **Finite sets are captured by a single token.** A finite `s ⊆ toC x` is contained in some `F̄`
with `C(F) ∈ x` — the finite-subcover property of the directed union `toC x`. -/
theorem exists_tok_of_finite_subset (x : (reprSystem C hInter hne).Element) {s : Set τ}
    (hs : s.Finite) (hsub : s ⊆ toC C hInter hne x) :
    ∃ F : Tok C, x.mem (nbhd C F.1) ∧ s ⊆ Cl C F.1 := by
  revert hsub
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨botTok C hne, mem_nbhd_bot C hInter hne x, Set.empty_subset _⟩
  | @insert a s _ha _hsfin ih =>
    intro hsub
    have ha' : a ∈ toC C hInter hne x := hsub (Set.mem_insert a s)
    rw [mem_toC] at ha'
    obtain ⟨Fa, hFa, haCl⟩ := ha'
    obtain ⟨Fs, hFs, hsCl⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem a hy))
    obtain ⟨F₃, hF₃, hFaF₃, hFsF₃⟩ := directed_step C hInter hne x hFa hFs
    refine ⟨F₃, hF₃, ?_⟩
    rw [Set.insert_subset_iff]
    exact ⟨hFaF₃ haCl, hsCl.trans hFsF₃⟩

/-- **Key membership identity.** `C(G) ∈ x ↔ G ⊆ toC x`. Forward: `G ⊆ Ḡ ⊆ toC x`. Reverse: `G` is
finite, so the finite-subcover lemma gives `F` with `C(F) ∈ x` and `G ⊆ F̄`, whence `C(F) ⊆ C(G)`
and upward closure gives `C(G) ∈ x`. -/
theorem mem_nbhd_iff (x : (reprSystem C hInter hne).Element) (G : Tok C) :
    x.mem (nbhd C G.1) ↔ G.1 ⊆ toC C hInter hne x := by
  constructor
  · intro hx t ht
    rw [mem_toC]
    exact ⟨G, hx, subset_Cl C G.1 ht⟩
  · intro hsub
    obtain ⟨F, hF, hGF⟩ := exists_tok_of_finite_subset C hInter hne x G.2.1 hsub
    have hnsub : nbhd C F.1 ⊆ nbhd C G.1 := (nbhd_subset_iff C hInter F.2).mpr hGF
    exact x.up_mem hF ⟨G, rfl⟩ hnsub

/-! ### From a set of `C` to an element: `X ↦ {C(F) ∣ F ⊆ X}`. -/

/-- The ideal element generated by `X ∈ C`: it contains the neighbourhoods above some `C(F)` with
`F ⊆ X`. -/
def ofC (X : Set τ) (hX : X ∈ C) : (reprSystem C hInter hne).Element where
  mem N := (reprSystem C hInter hne).mem N ∧ ∃ F : Tok C, F.1 ⊆ X ∧ nbhd C F.1 ⊆ N
  sub h := h.1
  master_mem :=
    ⟨(reprSystem C hInter hne).master_mem, botTok C hne, Set.empty_subset X, Set.subset_univ _⟩
  inter_mem := by
    rintro N M ⟨hN, F, hFX, hFN⟩ ⟨hM, F', hF'X, hF'M⟩
    have htok : IsTok C (F.1 ∪ F'.1) := ⟨F.2.1.union F'.2.1, X, hX, Set.union_subset hFX hF'X⟩
    have hsub : nbhd C (F.1 ∪ F'.1) ⊆ N ∩ M := by
      intro G hG
      rw [mem_nbhd, Set.union_subset_iff] at hG
      exact ⟨hFN hG.1, hF'M hG.2⟩
    exact ⟨(reprSystem C hInter hne).inter_mem hN hM ⟨⟨_, htok⟩, rfl⟩ hsub,
      ⟨F.1 ∪ F'.1, htok⟩, Set.union_subset hFX hF'X, hsub⟩
  up_mem := by
    rintro N M ⟨_, F, hFX, hFN⟩ hM hNM
    exact ⟨hM, F, hFX, hFN.trans hNM⟩

/-- **Scott's identity** `X = ⋃ {F̄ ∣ F ⊆ X, F ∈ Δ}` in round-trip form: `toC (ofC X) = X`. -/
theorem toC_ofC (X : Set τ) (hX : X ∈ C) : toC C hInter hne (ofC C hInter hne X hX) = X := by
  apply Set.Subset.antisymm
  · intro t ht
    rw [mem_toC] at ht
    obtain ⟨F, hF, htCl⟩ := ht
    obtain ⟨_, F', hF'X, hF'F⟩ := hF
    have h1 : F.1 ⊆ Cl C F'.1 := (nbhd_subset_iff C hInter F'.2).mp hF'F
    have hFX : F.1 ⊆ X := h1.trans (Cl_subset C hX hF'X)
    exact Cl_subset C hX hFX htCl
  · intro t ht
    have hst : IsTok C {t} := ⟨Set.finite_singleton t, X, hX, Set.singleton_subset_iff.mpr ht⟩
    rw [mem_toC]
    refine ⟨⟨{t}, hst⟩, ?_, subset_Cl C {t} rfl⟩
    exact ⟨⟨⟨{t}, hst⟩, rfl⟩, ⟨{t}, hst⟩, Set.singleton_subset_iff.mpr ht, subset_rfl⟩

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- `toC x ∈ C`: the represented set lies in the family (closure under directed unions). -/
theorem toC_mem (x : (reprSystem C hInter hne).Element) : toC C hInter hne x ∈ C := by
  show ⋃₀ famC C hInter hne x ∈ C
  apply hDir (famC C hInter hne x)
  · exact ⟨Cl C (botTok C hne).1, botTok C hne, mem_nbhd_bot C hInter hne x, rfl⟩
  · rintro Y ⟨F, _, rfl⟩
    exact Cl_mem C hInter F.2.2
  · rintro Y ⟨F, hF, rfl⟩ Y' ⟨F', hF', rfl⟩
    obtain ⟨F₃, hF₃, hFF₃, hF'F₃⟩ := directed_step C hInter hne x hF hF'
    exact ⟨Cl C F₃.1, ⟨F₃, hF₃, rfl⟩, hFF₃, hF'F₃⟩

/-- The other round-trip `ofC (toC x) = x`. -/
theorem ofC_toC (x : (reprSystem C hInter hne).Element) :
    ofC C hInter hne (toC C hInter hne x) (toC_mem C hInter hne hDir x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨hN, F, hFtoC, hFN⟩
    have hxF : x.mem (nbhd C F.1) := (mem_nbhd_iff C hInter hne x F).mpr hFtoC
    exact x.up_mem hxF hN hFN
  · intro hxN
    have hN : (reprSystem C hInter hne).mem N := x.sub hxN
    obtain ⟨G, rfl⟩ := hN
    have hGtoC : G.1 ⊆ toC C hInter hne x := (mem_nbhd_iff C hInter hne x G).mp hxN
    exact ⟨⟨G, rfl⟩, G, hGtoC, subset_rfl⟩

/-! ### The representation isomorphism. -/

include hDir in
/-- **Exercise 2.22 — the representation theorem.** `C`, ordered by inclusion, is order-isomorphic
to the domain `|reprSystem|`. The isomorphism sends `x ↦ ⋃ {F̄ ∣ C(F) ∈ x}` (`toC`) and
`X ↦ {C(F) ∣ F ⊆ X}` (`ofC`). -/
def reprIso : (reprSystem C hInter hne).Element ≃o {X : Set τ // X ∈ C} where
  toFun x := ⟨toC C hInter hne x, toC_mem C hInter hne hDir x⟩
  invFun X := ofC C hInter hne X.1 X.2
  left_inv x := ofC_toC C hInter hne hDir x
  right_inv X := Subtype.ext (toC_ofC C hInter hne X.1 X.2)
  map_rel_iff' := by
    intro a b
    show toC C hInter hne a ⊆ toC C hInter hne b ↔ a ≤ b
    constructor
    · intro hsub N hN
      have hmemD : (reprSystem C hInter hne).mem N := a.sub hN
      obtain ⟨G, rfl⟩ := hmemD
      have hGa : G.1 ⊆ toC C hInter hne a := (mem_nbhd_iff C hInter hne a G).mp hN
      exact (mem_nbhd_iff C hInter hne b G).mpr (hGa.trans hsub)
    · intro hab t ht
      rw [mem_toC] at ht ⊢
      obtain ⟨F, hF, htCl⟩ := ht
      exact ⟨F, hab _ hF, htCl⟩

end Scott1980.Neighborhood.Exercise222

/-! ### Inlined from Scott1980/Neighborhood/Exercise318.lean -/

/-!
# Exercise 3.18 (Scott 1981, PRG-19, §3) — the sum (coproduct) system

Scott's sum of `𝒟₀` (over `Δ₀`) and `𝒟₁` (over `Δ₁`), assuming *no neighbourhood is empty*:

`𝒟₀ + 𝒟₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`,

a neighbourhood system over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. We model the tokens as `Option (α ⊕ β)`: `Λ = none`,
`0a = some (inl a)`, `1b = some (inr b)`; then `0X = il '' X` and `1Y = ir '' Y`.

The non-emptiness assumption (`h₀`, `h₁`) is exactly what makes the system closed under intersection:
the two tagged copies are disjoint (`inj₀ X ∩ inj₁ Y = ∅`), so a cross pair `0X, 1Y` is *inconsistent*
(no non-empty neighbourhood lies in `∅`), and same-tag intersections reduce to those of the factors.

We then build the injections `inMapᵢ : 𝒟ᵢ → 𝒟₀ + 𝒟₁` and projections `outMapᵢ : 𝒟₀ + 𝒟₁ → 𝒟ᵢ`,
and prove `outMapᵢ ∘ inMapᵢ = I_{𝒟ᵢ}`. (The non-emptiness assumption is what makes the system a
neighbourhood system; the section/retraction identities hold for the resulting maps.)

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

/-- Left tag `0a = some (inl a)`. -/
def il (a : α) : Option (α ⊕ β) := some (Sum.inl a)

/-- Right tag `1b = some (inr b)`. -/
def ir (b : β) : Option (α ⊕ β) := some (Sum.inr b)

/-- The tagged left copy `0X = {some (inl a) ∣ a ∈ X}`. -/
def inj₀ (X : Set α) : Set (Option (α ⊕ β)) := il '' X

/-- The tagged right copy `1Y = {some (inr b) ∣ b ∈ Y}`. -/
def inj₁ (Y : Set β) : Set (Option (α ⊕ β)) := ir '' Y

@[simp] theorem il_mem_inj₀ {X : Set α} {a : α} : (il a : Option (α ⊕ β)) ∈ inj₀ X ↔ a ∈ X := by
  simp only [inj₀, Set.mem_image, il]
  constructor
  · rintro ⟨a', ha', hb⟩; simp only [Option.some.injEq, Sum.inl.injEq] at hb; exact hb ▸ ha'
  · intro ha; exact ⟨a, ha, rfl⟩

@[simp] theorem ir_mem_inj₀ {X : Set α} {b : β} : (ir b : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il, ir])

@[simp] theorem none_mem_inj₀ {X : Set α} : (none : Option (α ⊕ β)) ∉ inj₀ X := by
  rintro ⟨a, _, hb⟩; exact absurd hb (by simp [il])

@[simp] theorem ir_mem_inj₁ {Y : Set β} {b : β} : (ir b : Option (α ⊕ β)) ∈ inj₁ Y ↔ b ∈ Y := by
  simp only [inj₁, Set.mem_image, ir]
  constructor
  · rintro ⟨b', hb', hb⟩; simp only [Option.some.injEq, Sum.inr.injEq] at hb; exact hb ▸ hb'
  · intro hb; exact ⟨b, hb, rfl⟩

@[simp] theorem il_mem_inj₁ {Y : Set β} {a : α} : (il a : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [il, ir])

@[simp] theorem none_mem_inj₁ {Y : Set β} : (none : Option (α ⊕ β)) ∉ inj₁ Y := by
  rintro ⟨b, _, hb⟩; exact absurd hb (by simp [ir])

theorem inj₀_inter (X X' : Set α) :
    (inj₀ X ∩ inj₀ X' : Set (Option (α ⊕ β))) = inj₀ (X ∩ X') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, il, inj₀]

theorem inj₁_inter (Y Y' : Set β) :
    (inj₁ Y ∩ inj₁ Y' : Set (Option (α ⊕ β))) = inj₁ (Y ∩ Y') := by
  ext t; rcases t with _ | (a | b) <;>
    simp [Set.mem_inter_iff, ir, inj₁]

theorem inj₀_inter_inj₁ (X : Set α) (Y : Set β) :
    (inj₀ X ∩ inj₁ Y : Set (Option (α ⊕ β))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro t ⟨ht0, ht1⟩
  rcases t with _ | (a | b)
  · exact none_mem_inj₀ ht0
  · exact il_mem_inj₁ ht1
  · exact ir_mem_inj₀ ht0

theorem inj₀_nonempty {X : Set α} (hX : X.Nonempty) : (inj₀ X : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image il hX

theorem inj₁_nonempty {Y : Set β} (hY : Y.Nonempty) : (inj₁ Y : Set (Option (α ⊕ β))).Nonempty :=
  Set.Nonempty.image ir hY

theorem inj₀_subset_inj₀ {X X' : Set α} :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₀ X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact il_mem_inj₀.mp (h (il_mem_inj₀.mpr ha))
  · intro h t ht
    rw [inj₀, Set.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact il_mem_inj₀.mpr (h ha)

theorem inj₁_subset_inj₁ {Y Y' : Set β} :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₁ Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact ir_mem_inj₁.mp (h (ir_mem_inj₁.mpr hb))
  · intro h t ht
    rw [inj₁, Set.mem_image] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact ir_mem_inj₁.mpr (h hb)

theorem inj₀_injective {X X' : Set α} (h : (inj₀ X : Set (Option (α ⊕ β))) = inj₀ X') : X = X' :=
  Set.Subset.antisymm (inj₀_subset_inj₀.mp h.subset) (inj₀_subset_inj₀.mp h.symm.subset)

theorem inj₁_injective {Y Y' : Set β} (h : (inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y') : Y = Y' :=
  Set.Subset.antisymm (inj₁_subset_inj₁.mp h.subset) (inj₁_subset_inj₁.mp h.symm.subset)

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

/-- The master neighbourhood of the sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
def sumMaster : Set (Option (α ⊕ β)) := insert none (inj₀ V₀.master ∪ inj₁ V₁.master)

variable {V₀ V₁}

@[simp] theorem none_mem_sumMaster : (none : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ :=
  Set.mem_insert _ _

theorem inj₀_subset_sumMaster {X : Set α} (hX : V₀.mem X) :
    (inj₀ X : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _ ?_))
  exact (inj₀_subset_inj₀.mpr (V₀.sub_master hX)) ht

theorem inj₁_subset_sumMaster {Y : Set β} (hY : V₁.mem Y) :
    (inj₁ Y : Set (Option (α ⊕ β))) ⊆ sumMaster V₀ V₁ := by
  intro t ht
  refine Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ ?_))
  exact (inj₁_subset_inj₁.mpr (V₁.sub_master hY)) ht

theorem sumMaster_inter_inj₀ {X : Set α} (hX : V₀.mem X) :
    (sumMaster V₀ V₁ ∩ inj₀ X : Set (Option (α ⊕ β))) = inj₀ X :=
  Set.inter_eq_right.mpr (inj₀_subset_sumMaster hX)

theorem sumMaster_inter_inj₁ {Y : Set β} (hY : V₁.mem Y) :
    (sumMaster V₀ V₁ ∩ inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y :=
  Set.inter_eq_right.mpr (inj₁_subset_sumMaster hY)

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The *sum system* `𝒟₀ + 𝒟₁` over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`,
under the standing assumption that no neighbourhood of `𝒟₀` or `𝒟₁` is empty. -/
def sum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem (Option (α ⊕ β)) where
  mem W := W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨ (∃ Y, V₁.mem Y ∧ W = inj₁ Y)
  master := sumMaster V₀ V₁
  master_nonempty := ⟨none, none_mem_sumMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact subset_rfl
    · exact inj₀_subset_sumMaster hX
    · exact inj₁_subset_sumMaster hY
  inter_mem := by
    -- every neighbourhood is non-empty, hence so is any consistency witness `Z`
    have hne : ∀ W, (W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ W = inj₀ X) ∨
        (∃ Y, V₁.mem Y ∧ W = inj₁ Y)) → (W : Set (Option (α ⊕ β))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨none, none_mem_sumMaster⟩
      · exact inj₀_nonempty (h₀ X hX)
      · exact inj₁_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumMaster_inter_inj₀ hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [sumMaster_inter_inj₁ hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₀ hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [inj₀_inter] at hZsub ⊢
        -- witness `Z ⊆ inj₀ (X ∩ X')`; `Z` non-empty forces it to be a left copy `inj₀ Z₀`
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₀
        · refine Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ₀ (inj₀_subset_inj₀.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          exact absurd (hZsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · rw [inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₁ hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
      · rw [Set.inter_comm, inj₀_inter_inj₁] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [inj₁_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₁
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          exact absurd (hZsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
        · refine Or.inr (Or.inr ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ₁ (inj₁_subset_inj₁.mp hZsub), rfl⟩)

/-! ### The injections `inᵢ` and projections `outᵢ`. -/

theorem il_injective : Function.Injective (il : α → Option (α ⊕ β)) := by
  intro a a' h; simpa [il] using h

theorem ir_injective : Function.Injective (ir : β → Option (α ⊕ β)) := by
  intro b b' h; simpa [ir] using h

@[simp] theorem il_preimage_inj₀ (X : Set α) :
    ((il : α → Option (α ⊕ β)) ⁻¹' inj₀ X) = X :=
  Set.preimage_image_eq X il_injective

@[simp] theorem ir_preimage_inj₁ (Y : Set β) :
    ((ir : β → Option (α ⊕ β)) ⁻¹' inj₁ Y) = Y :=
  Set.preimage_image_eq Y ir_injective

/-- The left content `leftPart W ⊆ Δ₀` of a sum-neighbourhood `W`: the `0`-tagged tokens of `W`,
*plus* all of `Δ₀` whenever `W` reaches into the right copy or the basepoint (so non-left
neighbourhoods contribute only `Δ₀`, i.e. project to `⊥`). This is a genuine (choice-free) function
of `W`. -/
def leftPart (V₀ : NeighborhoodSystem α) (W : Set (Option (α ⊕ β))) : Set α :=
  il ⁻¹' W ∪ {a | a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

/-- The right content `rightPart W ⊆ Δ₁`, symmetric to `leftPart`. -/
def rightPart (V₁ : NeighborhoodSystem β) (W : Set (Option (α ⊕ β))) : Set β :=
  ir ⁻¹' W ∪ {b | b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ (none : Option (α ⊕ β)) ∈ W)}

@[simp] theorem mem_leftPart {V₀ : NeighborhoodSystem α} {W : Set (Option (α ⊕ β))} {a : α} :
    a ∈ leftPart V₀ W ↔ il a ∈ W ∨ (a ∈ V₀.master ∧ ((∃ b : β, ir b ∈ W) ∨ none ∈ W)) := by
  simp only [leftPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

@[simp] theorem mem_rightPart {V₁ : NeighborhoodSystem β} {W : Set (Option (α ⊕ β))} {b : β} :
    b ∈ rightPart V₁ W ↔ ir b ∈ W ∨ (b ∈ V₁.master ∧ ((∃ a : α, il a ∈ W) ∨ none ∈ W)) := by
  simp only [rightPart, Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq]

theorem leftPart_mono (V₀ : NeighborhoodSystem α) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    leftPart V₀ W ⊆ leftPart V₀ W' := by
  intro a ha
  rw [mem_leftPart] at ha ⊢
  exact ha.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨b, hb⟩ => ⟨b, h hb⟩) (fun hn => h hn)⟩)

theorem rightPart_mono (V₁ : NeighborhoodSystem β) {W W' : Set (Option (α ⊕ β))} (h : W ⊆ W') :
    rightPart V₁ W ⊆ rightPart V₁ W' := by
  intro b hb
  rw [mem_rightPart] at hb ⊢
  exact hb.imp (fun h' => h h') (fun ⟨hm, hc⟩ => ⟨hm, hc.imp (fun ⟨a, ha⟩ => ⟨a, h ha⟩) (fun hn => h hn)⟩)

@[simp] theorem leftPart_inj₀ (V₀ : NeighborhoodSystem α) (X : Set α) :
    leftPart V₀ (inj₀ X : Set (Option (α ⊕ β))) = X := by
  ext a
  simp only [mem_leftPart, il_mem_inj₀, ir_mem_inj₀, none_mem_inj₀, exists_false, or_self,
    and_false]
  exact ⟨fun h => h.resolve_right (by simp), fun h => Or.inl h⟩

@[simp] theorem rightPart_inj₁ (V₁ : NeighborhoodSystem β) (Y : Set β) :
    rightPart V₁ (inj₁ Y : Set (Option (α ⊕ β))) = Y := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₁, il_mem_inj₁, none_mem_inj₁, exists_false, or_self,
    and_false]
  exact ⟨fun h => h.resolve_right (by simp), fun h => Or.inl h⟩

theorem leftPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    leftPart V₀ (sumMaster V₀ V₁) = V₀.master := by
  ext a
  simp only [mem_leftPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (il a : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [il])
      · rcases h' with h'' | h''
        · exact (il_mem_inj₀).mp h''
        · exact absurd h'' (by simp)
    · exact h
  · intro ha; exact Or.inr ha

theorem leftPart_inj₁ (V₀ : NeighborhoodSystem α) {Y : Set β} (hY : Y.Nonempty) :
    leftPart V₀ (inj₁ Y : Set (Option (α ⊕ β))) = V₀.master := by
  ext a
  simp only [mem_leftPart, il_mem_inj₁, none_mem_inj₁, or_false, false_or]
  constructor
  · rintro ⟨ha, _⟩; exact ha
  · intro ha; obtain ⟨b, hb⟩ := hY; exact ⟨ha, ⟨b, ir_mem_inj₁.mpr hb⟩⟩

theorem rightPart_sumMaster (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    rightPart V₁ (sumMaster V₀ V₁) = V₁.master := by
  ext b
  simp only [mem_rightPart, none_mem_sumMaster, or_true, and_true]
  constructor
  · rintro (h | h)
    · have : (ir b : Option (α ⊕ β)) ∈ sumMaster V₀ V₁ := h
      rcases Set.mem_insert_iff.mp this with h' | h'
      · exact absurd h' (by simp [ir])
      · rcases h' with h'' | h''
        · exact absurd h'' (by simp)
        · exact (ir_mem_inj₁).mp h''
    · exact h
  · intro hb; exact Or.inr hb

theorem rightPart_inj₀ (V₁ : NeighborhoodSystem β) {X : Set α} (hX : X.Nonempty) :
    rightPart V₁ (inj₀ X : Set (Option (α ⊕ β))) = V₁.master := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₀, none_mem_inj₀, or_false, false_or]
  constructor
  · rintro ⟨hb, _⟩; exact hb
  · intro hb; obtain ⟨a, ha⟩ := hX; exact ⟨hb, ⟨a, il_mem_inj₀.mpr ha⟩⟩

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem leftPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₀.mem (leftPart V₀ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [leftPart_sumMaster]; exact V₀.master_mem
  · rw [leftPart_inj₀]; exact hX
  · rw [leftPart_inj₁ V₀ (h₁ Y hY)]; exact V₀.master_mem

theorem rightPart_mem {W : Set (Option (α ⊕ β))} (hW : (sum V₀ V₁ h₀ h₁).mem W) :
    V₁.mem (rightPart V₁ W) := by
  rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rw [rightPart_sumMaster]; exact V₁.master_mem
  · rw [rightPart_inj₀ V₁ (h₀ X hX)]; exact V₁.master_mem
  · rw [rightPart_inj₁]; exact hY

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left injection `in₀ : 𝒟₀ → 𝒟₀ + 𝒟₁`,
`X (in₀) W ↔ 0X ⊆ W`. -/
def inMap₀ : ApproximableMap V₀ (sum V₀ V₁ h₀ h₁) where
  rel X W := V₀.mem X ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right injection `in₁ : 𝒟₁ → 𝒟₀ + 𝒟₁`. -/
def inMap₁ : ApproximableMap V₁ (sum V₀ V₁ h₀ h₁) where
  rel Y W := V₁.mem Y ∧ (sum V₀ V₁ h₀ h₁).mem W ∧ inj₁ Y ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₁.master_mem, (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
  inter_right := by
    rintro Y W W' ⟨hY, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hY, (sum V₀ V₁ h₀ h₁).inter_mem hW hW' (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro Y Y' W W' ⟨_, _, hsub⟩ hY'Y hWW' hY' hW'
    exact ⟨hY', hW', (inj₁_subset_inj₁.mpr hY'Y).trans (hsub.trans hWW')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The left projection `out₀ : 𝒟₀ + 𝒟₁ → 𝒟₀`,
`W (out₀) X ↔ leftPart W ⊆ X` (right/basepoint neighbourhoods relate only to `Δ₀`). -/
def outMap₀ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₀ where
  rel W X := (sum V₀ V₁ h₀ h₁).mem W ∧ V₀.mem X ∧ leftPart V₀ W ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V₀.inter_mem hX hX' (leftPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', (leftPart_mono V₀ hW'W).trans (hsub.trans hXX')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** The right projection `out₁ : 𝒟₀ + 𝒟₁ → 𝒟₁`. -/
def outMap₁ : ApproximableMap (sum V₀ V₁ h₀ h₁) V₁ where
  rel W Y := (sum V₀ V₁ h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hW, V₁.inter_mem hY hY' (rightPart_mem hW) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₀ ∘ in₀ = I_{𝒟₀}`. -/
theorem outMap₀_comp_inMap₀ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₀ = idMap V₀ := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, hZ, ?_⟩
    have hXW : X ⊆ leftPart V₀ W := by
      intro a ha
      rw [mem_leftPart]; exact Or.inl (hinj (il_mem_inj₀.mpr ha))
    exact hXW.trans hsub
  · rintro ⟨hX, hZ, hXZ⟩
    refine ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), hZ, ?_⟩
    rw [leftPart_inj₀]; exact hXZ

/-- **Exercise 3.18 (Scott 1981, PRG-19).** `out₁ ∘ in₁ = I_{𝒟₁}`. -/
theorem outMap₁_comp_inMap₁ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₁ = idMap V₁ := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, hZ, ?_⟩
    have hYW : Y ⊆ rightPart V₁ W := by
      intro b hb
      rw [mem_rightPart]; exact Or.inl (hinj (ir_mem_inj₁.mpr hb))
    exact hYW.trans hsub
  · rintro ⟨hY, hZ, hYZ⟩
    refine ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), hZ, ?_⟩
    rw [rightPart_inj₁]; exact hYZ

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise319Sum.lean -/

/-!
# Exercise 3.19 (Scott 1981, PRG-19, §3) — the sum functor `f + g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise 3.19 also asks for the
*sum* mapping `f + g : 𝒟₀ + 𝒟₁ → 𝒟₀' + 𝒟₁'`, characterized (equations (iii), (iv)) by

* `out₀ ∘ (f + g) ∘ in₀ = f`, and
* `out₁ ∘ (f + g) ∘ in₁ = g`.

We build `f + g` (`sumMap`) directly as a relation between sum-neighbourhoods: it routes the left copy
`0X` through `f` (to `0Y'`), the right copy `1Y` through `g` (to `1Y'`), and sends everything to the
master neighbourhood `{Λ} ∪ 0Δ₀' ∪ 1Δ₁'`. The disjointness of the two tagged copies (Exercise 3.18) is
exactly what makes this a well-defined approximable mapping — a left input can never produce a
right-tagged output, so there is no cross-contamination through `g(⊥)`.

Scott also asks whether (iii), (iv) *uniquely* determine `f + g`: they do **not**, because the behaviour
on the basepoint `Λ` (i.e. `(f + g)(⊥)`) is unconstrained; our choice sends `Λ` to `Λ`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-! ### Structural extraction lemmas for sum-neighbourhoods. -/

/-- A sum-neighbourhood contained in a *left* copy `0X` is itself a left copy `0X₂` (the basepoint and
the right copy are excluded, using non-emptiness). -/
theorem mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

/-- A sum-neighbourhood contained in a *right* copy `1Y` is itself a right copy `1Y₂`. -/
theorem mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, rfl⟩

/-- A sum-neighbourhood that *contains* the master is the master. -/
theorem eq_sumMaster_of_subset {W : Set (Option (α ⊕ β))}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : sumMaster V₀ V₁ ⊆ W) :
    W = sumMaster V₀ V₁ :=
  Set.Subset.antisymm ((sum V₀ V₁ h₀ h₁).sub_master hW) hsub

/-- A nonempty left copy is never contained in a right copy. -/
theorem not_inj₀_subset_inj₁ {X : Set α} {Y : Set β} (hX : X.Nonempty)
    (hsub : (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₁ Y) : False := by
  obtain ⟨a, ha⟩ := hX
  exact il_mem_inj₁ (hsub (il_mem_inj₀.mpr ha))

/-- A nonempty right copy is never contained in a left copy. -/
theorem not_inj₁_subset_inj₀ {X : Set α} {Y : Set β} (hY : Y.Nonempty)
    (hsub : (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₀ X) : False := by
  obtain ⟨b, hb⟩ := hY
  exact ir_mem_inj₀ (hsub (ir_mem_inj₁.mpr hb))

/-! ### The sum mapping `f + g`. -/

/-- **Exercise 3.19 (Scott 1981, PRG-19).** The *sum mapping* `f + g : 𝒟₀ + 𝒟₁ → 𝒟₀' + 𝒟₁'`. As a
relation between sum-neighbourhoods, `W (f+g) W'` holds iff `W'` is the codomain master, or `W = 0X`
with `W' = 0Y'` and `X f Y'`, or `W = 1Y` with `W' = 1Y'` and `Y g Y'`. -/
def sumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (sum V₀ V₁ h₀ h₁) (sum V₀' V₁' h₀' h₁') where
  rel W W' := (sum V₀ V₁ h₀ h₁).mem W ∧ (sum V₀' V₁' h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, (sum V₀' V₁' h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    -- membership of any disjunction-satisfying set
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ g.rel Y Y')) →
          (sum V₀' V₁' h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hg⟩)
      · exact (sum V₀' V₁' h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, rfl⟩)
    -- the disjunction is preserved by intersection
    have key : (W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ g.rel Y Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩
      · rw [Set.inter_eq_right.mpr
          (show W'₂ ⊆ sumMaster V₀' V₁' from (sum V₀' V₁' h₀' h₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f.inter_right hf₁ hf₂⟩)
        · exact absurd ((hWX₁.symm.trans hWY₂)) (fun h =>
            not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩)
        · exact absurd ((hWY₁.symm.trans hWX₂)) (fun h =>
            not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hg⟩
    · -- W' = master; W'₂ ⊇ master so W'₂ = master
      left; exact eq_sumMaster_of_subset hW'₂mem hW'W'₂
    · -- left copy: W₂ ⊆ 0X, W'₂ ⊇ 0Y'
      obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Z'₂, hZ'₂, rfl⟩
      · left; rfl
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₀_subset_inj₀.mp hW'W'₂
        exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f.mono hf hXX₂ hY'Y'₂ hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · -- right copy: W₂ ⊆ 1Y, W'₂ ⊇ 1Y'
      obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₁_subset_inj₁.mp hW'W'₂
        exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl,
          g.mono hg hYY₂ hY'Y'₂ hY₂ hY'₂⟩)

/-! ### The defining identities (iii) and (iv). -/

/-- **Exercise 3.19(iii) (Scott 1981, PRG-19).** `out₀ ∘ (f + g) ∘ in₀ = f`. -/
theorem outMap₀_comp_sumMap_comp_inMap₀ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hX, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hleft⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · -- output master: leftPart = Δ₀', and Z ⊇ Δ₀' so Z = Δ₀'
      rw [leftPart_sumMaster] at hleft
      have : Z = V₀'.master := Set.Subset.antisymm (V₀'.sub_master hZ) hleft
      subst this
      exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₀'.master_mem
    · -- output 0Y': X ⊆ X₀ and Y' ⊆ Z
      rw [leftPart_inj₀] at hleft
      have hXX₀ : X ⊆ X₀ := inj₀_subset_inj₀.mp (hWX₀ ▸ hinj)
      exact f.mono hf hXX₀ hleft hX hZ
    · -- impossible: in₀ forces 0X ⊆ W = 1Y₀
      exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY₀ ▸ hinj)).elim
  · intro hf
    refine ⟨inj₀ Z, ⟨inj₀ X, ⟨f.rel_dom hf, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, f.rel_cod hf, ?_⟩
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Z, rfl, rfl, hf⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact (leftPart_inj₀ V₀' Z).subset

/-- **Exercise 3.19(iv) (Scott 1981, PRG-19).** `out₁ ∘ (f + g) ∘ in₁ = g`. -/
theorem outMap₁_comp_sumMap_comp_inMap₁ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hY, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hright⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · rw [rightPart_sumMaster] at hright
      have : Z = V₁'.master := Set.Subset.antisymm (V₁'.sub_master hZ) hright
      subst this
      exact g.mono g.master_rel (V₁.sub_master hY) subset_rfl hY V₁'.master_mem
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX₀ ▸ hinj)).elim
    · rw [rightPart_inj₁] at hright
      have hYY₀ : Y ⊆ Y₀ := inj₁_subset_inj₁.mp (hWY₀ ▸ hinj)
      exact g.mono hg hYY₀ hright hY hZ
  · intro hg
    refine ⟨inj₁ Z, ⟨inj₁ Y, ⟨g.rel_dom hg, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, g.rel_cod hg, ?_⟩
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, Z, rfl, rfl, hg⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact (rightPart_inj₁ V₁' Z).subset

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Example62.lean -/

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — `B` and `C` as solutions of domain equations

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI,
*Introduction to domain equations*. Scott observes that the staple examples `B` (binary sequences,
Example 1.B) and `C` (finite-or-infinite binary sequences, Example 4.4) satisfy *domain equations*:

`B ≅ B + B`,    `C ≅ {{Λ}} + C + C`,

where, "if we liked", both systems can be presented over `{0,1}*` as the least families

`B = {Σ*} ∪ {0X ∣ X ∈ B} ∪ {1X ∣ X ∈ B}`,
`C = {Σ*} ∪ {{Λ}} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`.

This module formalizes the **`B ≅ B + B`** half. (See `Example62C.lean` for `C`'s three-way
equation `C ≅ 𝟙 + C + C`.)

The point of the equation is that a neighbourhood of `B` is either the master `Σ*` (`= cone []`), a
`0`-prefixed copy `0X` (`= embBit false X`), or a `1`-prefixed copy `1X` (`= embBit true X`) — exactly
the three shapes that build the sum `B + B` (Exercise 3.18): the fresh basepoint, the left copy `0X`,
and the right copy `1Y`. We exhibit the order-isomorphism `bbEquiv : |B| ≃o |B + B|` directly from the
filter maps `toBB` (forward) / `fromBB` (inverse), mirroring `Example61.dsharpEquiv`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-! ### Prepending a single bit: `bX = {bw' ∣ w' ∈ X}`. -/

/-- `bX = {b :: w' ∣ w' ∈ X}`: the `b`-prefixed copy of a neighbourhood `X` (Scott's `0X` for
`b = false` and `1X` for `b = true`). -/
def embBit (b : Bool) (X : Set Str) : Set Str := {w | ∃ w', w = b :: w' ∧ w' ∈ X}

@[simp] theorem mem_embBit {b : Bool} {X : Set Str} {w : Str} :
    w ∈ embBit b X ↔ ∃ w', w = b :: w' ∧ w' ∈ X := Iff.rfl

/-- `bX = b·X` is exactly the single-bit prepend of Example 1.B. -/
theorem embBit_eq_prepend (b : Bool) (X : Set Str) : embBit b X = prepend [b] X := by
  ext w
  simp only [mem_embBit, mem_prepend]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨τ, hX, rfl⟩; exact ⟨τ, rfl, hX⟩

/-- `b(σΣ*) = (bσ)Σ*`: prepending a bit to a cone gives the cone of the longer prefix. -/
theorem embBit_cone (b : Bool) (σ : Str) : embBit b (cone σ) = cone (b :: σ) := by
  rw [embBit_eq_prepend, prepend_cone]; rfl

/-- Prepending a bit lands back in `B`. -/
theorem memB_embBit (b : Bool) {X : Set Str} (hX : B.mem X) : B.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact memB_prepend [b] hX

theorem nil_not_mem_embBit {b : Bool} {X : Set Str} : ([] : Str) ∉ embBit b X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

theorem embBit_ne_univ (b : Bool) (X : Set Str) : embBit b X ≠ Set.univ := by
  intro h; exact nil_not_mem_embBit (X := X) (b := b) (by rw [h]; trivial)

theorem embBit_inter (b : Bool) (X X' : Set Str) :
    embBit b X ∩ embBit b X' = embBit b (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩
    exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

theorem embBit_inter_ne {b b' : Bool} (h : b ≠ b') (X Y : Set Str) :
    embBit b X ∩ embBit b' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq
  exact h heq.1

theorem embBit_subset {b : Bool} {X X' : Set Str} :
    embBit b X ⊆ embBit b X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact hX'
  · rintro h w ⟨w', rfl, hX⟩
    exact ⟨w', rfl, h hX⟩

theorem embBit_injective {b : Bool} {X X' : Set Str} (h : embBit b X = embBit b X') : X = X' :=
  Set.Subset.antisymm (embBit_subset.mp h.subset) (embBit_subset.mp h.symm.subset)

theorem embBit_nonempty {b : Bool} {X : Set Str} (hX : X.Nonempty) : (embBit b X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨b :: w', w', rfl, hw'⟩

/-- If `bW ∈ B` then `W ∈ B`: a `b`-prefixed neighbourhood that lands in `B` must be `b·(cone w')`,
so `W = cone w'`. -/
theorem memB_embBit_inv {b : Bool} {W : Set Str} (h : B.mem (embBit b W)) : B.mem W := by
  obtain ⟨σ, hσ⟩ := h
  have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
  obtain ⟨w', rfl, -⟩ := hmem
  rw [← embBit_cone] at hσ
  rw [embBit_injective hσ]
  exact memB_cone w'

theorem embBit_ne {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty) :
    embBit b X ≠ embBit b' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (b :: w') ∈ embBit b' Y := heq ▸ (⟨w', rfl, hw'⟩ : (b :: w') ∈ embBit b X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he
  exact h he.1

/-! ### `B` is positive (no empty neighbourhood) and its neighbourhood-shape classification. -/

/-- Scott's standing assumption `∅ ∉ B`: every neighbourhood of `B` is nonempty (cones contain their
generating prefix). -/
theorem B_nonempty : ∀ X, B.mem X → X.Nonempty := by
  rintro X ⟨σ, rfl⟩; exact ⟨σ, List.prefix_rfl⟩

/-- **Example 6.2 — the shape of a `B`-neighbourhood.** Every neighbourhood of `B` is either the
master `Σ* = cone []`, a `0`-copy `0X` with `X ∈ B`, or a `1`-copy `1X` with `X ∈ B`. -/
theorem memB_cases {W : Set Str} (hW : B.mem W) :
    W = Set.univ ∨ (∃ X, B.mem X ∧ W = embBit false X) ∨ (∃ Y, B.mem Y ∧ W = embBit true Y) := by
  obtain ⟨σ, rfl⟩ := hW
  cases σ with
  | nil => exact Or.inl cone_nil
  | cons b σ' =>
    cases b with
    | false => exact Or.inr (Or.inl ⟨cone σ', memB_cone σ', (embBit_cone false σ').symm⟩)
    | true => exact Or.inr (Or.inr ⟨cone σ', memB_cone σ', (embBit_cone true σ').symm⟩)

/-! ### The sum target `B + B` and its inversion lemmas. -/

/-- The right-hand side of Scott's domain equation: the sum system `B + B` (Exercise 3.18). -/
abbrev BB : NeighborhoodSystem (Option (Str ⊕ Str)) := sum B B B_nonempty B_nonempty

theorem sum_mem_inj₀_inv {X : Set Str} (h : BB.mem (inj₀ X)) : B.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := B_nonempty Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

theorem sum_mem_inj₁_inv {Y : Set Str} (h : BB.mem (inj₁ Y)) : B.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := B_nonempty X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : BB.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (B_nonempty X hX)
  · exact inj₁_nonempty (B_nonempty Y hY)

/-! ### The forward half `toBB : |B| → |B + B|`. -/

/-- **Example 6.2 — forward half of `B ≅ B + B`.** An element `x` of `B` is sent to the sum element
recording, for each branch, whether `x` reaches the `0`-copy `0X` (left summand) or the `1`-copy `1Y`
(right summand). -/
def toBB (x : B.Element) : BB.Element where
  mem W := W = sumMaster B B
    ∨ (∃ X, B.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, B.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := B_nonempty _ (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact memB_embBit_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (memB_embBit false hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (memB_embBit true hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

@[simp] theorem toBB_mem_inj₀ {x : B.Element} {X : Set Str} (hX : B.mem X) :
    (toBB x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := B_nonempty X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toBB_mem_inj₁ {x : B.Element} {Y : Set Str} (hY : B.mem Y) :
    (toBB x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := B_nonempty X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-! ### The inverse half `fromBB : |B + B| → |B|`. -/

/-- **Example 6.2 — inverse half of `B ≅ B + B`.** -/
def fromBB (s : BB.Element) : B.Element where
  mem W := W = Set.univ
    ∨ (∃ X, B.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, B.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact ⟨[], cone_nil.symm⟩
    · exact memB_embBit false hX
    · exact memB_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

@[simp] theorem fromBB_mem_embF {s : BB.Element} {X : Set Str} (hX : B.mem X) :
    (fromBB s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromBB_mem_embT {s : BB.Element} {Y : Set Str} (hY : B.mem Y) :
    (fromBB s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (B_nonempty X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

/-! ### The two halves are mutually inverse. -/

theorem fromBB_toBB (x : B.Element) : fromBB (toBB x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toBB_mem_inj₀ hX).mp hs
    · exact (toBB_mem_inj₁ hY).mp hs
  · intro hW
    rcases memB_cases (x.sub hW) with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toBB_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toBB_mem_inj₁ hY).mpr hW⟩)

theorem toBB_fromBB (s : BB.Element) : toBB (fromBB s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromBB_mem_embF hX).mp hs
    · exact (fromBB_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromBB_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromBB_mem_embT hY).mpr hW⟩)

/-! ### The domain equation `B ≅ B + B`. -/

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|B| ≃o |B + B|`.** -/
def bbEquiv : B.Element ≃o BB.Element where
  toFun := toBB
  invFun := fromBB
  left_inv := fromBB_toBB
  right_inv := toBB_fromBB
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases memB_cases (x.sub hX) with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toBB_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toBB_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `B ≅ B + B`.** Scott's binary-sequence
domain `B` is, as a domain, isomorphic to `B + B`: a sequence is bottom, or begins with `0`, or begins
with `1`, the two non-bottom cases giving the two summands. -/
theorem B_domain_equation : B ≅ᴰ sum B B B_nonempty B_nonempty :=
  ⟨bbEquiv⟩

end Example62

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Product.lean -/

/-!
# Lecture III (§3) — the product system: Definitions 3.1, 3.3, Propositions 3.2, 3.4,
Lemma 3.6, Theorems 3.5, 3.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture III,
*Constructions on domains*. Given two neighbourhood systems over **disjoint** token sets `Δ₀`, `Δ₁`,
the **product system** `𝒟₀ × 𝒟₁` has neighbourhoods `X ∪ Y` (`X ∈ 𝒟₀`, `Y ∈ 𝒟₁`) over `Δ₀ ∪ Δ₁`.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, and the product
neighbourhood `X ∪ Y` by `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`. Because `Sum.inl` and
`Sum.inr` have disjoint ranges, the cleanest facts of Scott's proof become transparent:

* `prodNbhd_inter` — `(X ∪ Y) ∩ (X' ∪ Y') = (X ∩ X') ∪ (Y ∩ Y')` (Scott's (2));
* `prodNbhd_subset_iff` — `X ∪ Y ⊆ X' ∪ Y' ↔ X ⊆ X' ∧ Y ⊆ Y'` (Scott's (1));
* `prodNbhd_injective` — the representation `X ∪ Y` is unique.

This file formalizes:

* **Definition 3.1 / Proposition 3.2** — the product system `prod V₀ V₁`, the element pairing
  `pair x y = ⟨x, y⟩`, the order law `pair_le_pair_iff` (3.2(i)), and the order-isomorphism
  `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`.
* **Definition 3.3 / Proposition 3.4** — projections `proj₀`, `proj₁`, the paired mapping `paired f g`,
  and `proj₀_comp_paired`, `proj₁_comp_paired`, `paired_proj` (`⟨p₀∘h, p₁∘h⟩ = h`),
  `toElementMap_paired` (`⟨f, g⟩(w) = ⟨f(w), g(w)⟩`).
* **Lemma 3.6** — constant maps `constMap b` (`X b Y ↔ Y ∈ b`) with `toElementMap_constMap`.
* **Theorem 3.5** — joint vs. separate approximability, via the bridge `ApproximableMap (prod V₀ V₁) V₂
  ≃ ApproximableMap₂ V₀ V₁ V₂` (`ofMap₂` / `toMap₂` and round-trips).
* **Proposition 3.7** — multivariate approximable functions are closed under substitution
  (`comp`/`paired`/`proj` bookkeeping).

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- The product neighbourhood `X ∪ Y` over the disjoint union `Δ₀ ∪ Δ₁`, modelled on `α ⊕ β` as
`Sum.inl '' X ∪ Sum.inr '' Y`. -/
def prodNbhd (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

@[simp] theorem mem_prodNbhd_inl {X : Set α} {Y : Set β} {a : α} :
    (Sum.inl a : α ⊕ β) ∈ prodNbhd X Y ↔ a ∈ X := by
  simp [prodNbhd]

@[simp] theorem mem_prodNbhd_inr {X : Set α} {Y : Set β} {b : β} :
    (Sum.inr b : α ⊕ β) ∈ prodNbhd X Y ↔ b ∈ Y := by
  simp [prodNbhd]

@[simp] theorem inl_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inl ⁻¹' prodNbhd X Y = X := by ext a; simp

@[simp] theorem inr_preimage_prodNbhd (X : Set α) (Y : Set β) :
    Sum.inr ⁻¹' prodNbhd X Y = Y := by ext b; simp

/-- Scott's (2): the product nbhds intersect componentwise. -/
theorem prodNbhd_inter (X X' : Set α) (Y Y' : Set β) :
    prodNbhd X Y ∩ prodNbhd X' Y' = prodNbhd (X ∩ X') (Y ∩ Y') := by
  ext (a | b) <;> simp [Set.mem_inter_iff]

/-- Scott's (1): inclusion of product nbhds is componentwise (uses disjointness of `Δ₀`, `Δ₁`). -/
theorem prodNbhd_subset_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y ⊆ prodNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have : (Sum.inl a : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using ha)
      simpa using this
    · have : (Sum.inr b : α ⊕ β) ∈ prodNbhd X' Y' := h (by simpa using hb)
      simpa using this
  · rintro ⟨hX, hY⟩ (a | b) hs
    · simp only [mem_prodNbhd_inl] at hs ⊢; exact hX hs
    · simp only [mem_prodNbhd_inr] at hs ⊢; exact hY hs

/-- The representation `X ∪ Y` is unique (choice-free, via the preimage projections). -/
theorem prodNbhd_injective {X X' : Set α} {Y Y' : Set β}
    (h : prodNbhd X Y = prodNbhd X' Y') : X = X' ∧ Y = Y' := by
  refine ⟨?_, ?_⟩
  · rw [← inl_preimage_prodNbhd X Y, ← inl_preimage_prodNbhd X' Y', h]
  · rw [← inr_preimage_prodNbhd X Y, ← inr_preimage_prodNbhd X' Y', h]

/-- **Definition 3.1 (Scott 1981, PRG-19).** The *product system* `𝒟₀ × 𝒟₁`: neighbourhoods are
`X ∪ Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closure under consistent intersection is Scott's (2)
(`prodNbhd_inter`) together with the factors' closure; the consistency witness `Z ⊆ (X∪Y) ∩ (X'∪Y')`
splits into witnesses `Z₀ ⊆ X ∩ X'`, `Z₁ ⊆ Y ∩ Y'` by `prodNbhd_subset_iff`. -/
def prod (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := ⟨V₀.master, V₁.master, V₀.master_mem, V₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', V₀.inter_mem hX hX' hZ₀ hsub₀, V₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prod_mem_iff {W : Set (α ⊕ β)} :
    (prod V₀ V₁).mem W ↔ ∃ X Y, V₀.mem X ∧ V₁.mem Y ∧ W = prodNbhd X Y := Iff.rfl

theorem prod_mem_prodNbhd {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (prod V₀ V₁).mem (prodNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

@[simp] theorem prod_master : (prod V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

/-! ### Projections of an element (Scott's `z₀`, `z₁`). -/

/-- Scott's `z₀ = {X ∈ 𝒟₀ ∣ X ∪ Δ₁ ∈ z}`: the first component of a product element. -/
def NeighborhoodSystem.Element.fst (z : (prod V₀ V₁).Element) : V₀.Element where
  mem X := V₀.mem X ∧ z.mem (prodNbhd X V₁.master)
  sub h := h.1
  master_mem := ⟨V₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    refine ⟨hX', z.up_mem hzX (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩

/-- Scott's `z₁ = {Y ∈ 𝒟₁ ∣ Δ₀ ∪ Y ∈ z}`: the second component of a product element. -/
def NeighborhoodSystem.Element.snd (z : (prod V₀ V₁).Element) : V₁.Element where
  mem Y := V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y)
  sub h := h.1
  master_mem := ⟨V₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    refine ⟨hY', z.up_mem hzY (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩

@[simp] theorem mem_fst {z : (prod V₀ V₁).Element} {X : Set α} :
    z.fst.mem X ↔ V₀.mem X ∧ z.mem (prodNbhd X V₁.master) := Iff.rfl

@[simp] theorem mem_snd {z : (prod V₀ V₁).Element} {Y : Set β} :
    z.snd.mem Y ↔ V₁.mem Y ∧ z.mem (prodNbhd V₀.master Y) := Iff.rfl

/-- The key splitting (Scott's (3)): for a product element `z` and neighbourhoods `X ∈ 𝒟₀`,
`Y ∈ 𝒟₁`, membership of `X ∪ Y` in `z` is equivalent to membership of its two "slices". -/
theorem prod_mem_split {z : (prod V₀ V₁).Element} {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    z.mem (prodNbhd X Y) ↔ z.mem (prodNbhd X V₁.master) ∧ z.mem (prodNbhd V₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prod_mem_prodNbhd hX V₁.master_mem) ?_,
            z.up_mem h (prod_mem_prodNbhd V₀.master_mem hY) ?_⟩
    · exact prodNbhd_subset_iff.mpr ⟨subset_rfl, V₁.sub_master hY⟩
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
      Set.inter_eq_right.mpr (V₁.sub_master hY)] at this

/-! ### Definition 3.1 — the element pairing `⟨x, y⟩`. -/

/-- **Definition 3.1 (Scott 1981, PRG-19).** The element pairing `⟨x, y⟩ = {X ∪ Y ∣ X ∈ x, Y ∈ y}`. -/
def pair (x : V₀.Element) (y : V₁.Element) : (prod V₀ V₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prod_mem_prodNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

@[simp] theorem mem_pair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (pair x y).mem W ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodNbhd X Y := Iff.rfl

theorem mem_pair_prodNbhd {x : V₀.Element} {y : V₁.Element} {X : Set α} {Y : Set β} :
    (pair x y).mem (prodNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

/-- **Proposition 3.2(i) (Scott 1981, PRG-19).** `⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pair_le_pair_iff {x x' : V₀.Element} {y y' : V₁.Element} :
    pair x y ≤ pair x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd X V₁.master) ⟨X, V₁.master, hX, y.master_mem, rfl⟩
      obtain ⟨rfl, _⟩ := prodNbhd_injective heq
      exact hX'
    · obtain ⟨X', Y', hX', hY', heq⟩ :=
        h (prodNbhd V₀.master Y) ⟨V₀.master, Y, x.master_mem, hY, rfl⟩
      obtain ⟨_, rfl⟩ := prodNbhd_injective heq
      exact hY'
  · rintro ⟨hx, hy⟩ W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, hx X hX, hy Y hY, rfl⟩

/-- `z = ⟨z₀, z₁⟩`: every product element is the pairing of its two components. -/
theorem pair_fst_snd (z : (prod V₀ V₁).Element) : pair z.fst z.snd = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prod_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prod_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

@[simp] theorem fst_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).fst = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).1
  · intro hX
    exact ⟨x.sub hX, mem_pair_prodNbhd.mpr ⟨hX, y.master_mem⟩⟩

@[simp] theorem snd_pair (x : V₀.Element) (y : V₁.Element) : (pair x y).snd = y := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩
    exact (mem_pair_prodNbhd.mp hmem).2
  · intro hY
    exact ⟨y.sub hY, mem_pair_prodNbhd.mpr ⟨x.master_mem, hY⟩⟩

/-- **Proposition 3.2 (Scott 1981, PRG-19).** The order-isomorphism `|𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`. -/
def prodEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o V₀.Element × V₁.Element where
  toFun z := (z.fst, z.snd)
  invFun p := pair p.1 p.2
  left_inv z := pair_fst_snd z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prod_mem_split hX hY).mp hW
      have hX' : z'.fst.mem X := h1 X ⟨hX, ha⟩
      have hY' : z'.snd.mem Y := h2 Y ⟨hY, hb⟩
      exact (prod_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

@[simp] theorem prodEquiv_apply (z : (prod V₀ V₁).Element) :
    prodEquiv V₀ V₁ z = (z.fst, z.snd) := rfl

@[simp] theorem prodEquiv_symm_apply (p : V₀.Element × V₁.Element) :
    (prodEquiv V₀ V₁).symm p = pair p.1 p.2 := rfl

/-! ### Definition 3.3 / Proposition 3.4 — projections and pairing of maps. -/

variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap

/-- Every product neighbourhood is `(inl⁻¹ W) ∪ (inr⁻¹ W)`. -/
theorem prodNbhd_preimage {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) :
    W = prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, _, rfl⟩ := hW
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]

/-- An approximable map relates any input neighbourhood to the master output `Δ₁`. -/
theorem ApproximableMap.rel_master (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) :
    f.rel X V₁.master :=
  f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₀ : 𝒟₀ × 𝒟₁ → 𝒟₀`,
`(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def proj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₀ where
  rel W X' := (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨_, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, hA, ‹_›, rfl⟩, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

/-- **Definition 3.3 (Scott 1981, PRG-19).** The projection `p₁ : 𝒟₀ × 𝒟₁ → 𝒟₁`,
`(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def proj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) V₁ where
  rel W Y' := (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨_, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨⟨A, B, ‹_›, hB, rfl⟩, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

/-- **Definition 3.3 (Scott 1981, PRG-19).** The paired mapping `⟨f, g⟩ : 𝒟₂ → 𝒟₀ × 𝒟₁`,
`Z ⟨f, g⟩ (X ∪ Y) ↔ Z f X ∧ Z g Y`. -/
def paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    ApproximableMap V₂ (prod V₀ V₁) where
  rel Z P := (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P)
  rel_dom h := f.rel_dom h.2.1
  rel_cod h := h.1
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_, ?_⟩
    · simpa using f.master_rel
    · simpa using g.master_rel
  inter_right := by
    rintro Z P P' ⟨hP, hfP, hgP⟩ ⟨hP', hfP', hgP'⟩
    have hfX := f.inter_right hfP hfP'
    have hgY := g.inter_right hgP hgP'
    refine ⟨?_, ?_, ?_⟩
    · rw [prodNbhd_preimage hP, prodNbhd_preimage hP', prodNbhd_inter]
      exact prod_mem_prodNbhd (f.rel_cod hfX) (g.rel_cod hgY)
    · rw [Set.preimage_inter]; exact hfX
    · rw [Set.preimage_inter]; exact hgY
  mono := by
    rintro Z Z₂ P P₂ ⟨_, hfP, hgP⟩ hZ₂Z hPP₂ hZ₂ hP₂
    obtain ⟨A, B, hA, hB, rfl⟩ := hP₂
    have hinl : Sum.inl ⁻¹' P ⊆ A := by
      have := Set.preimage_mono (f := Sum.inl) hPP₂; rwa [inl_preimage_prodNbhd] at this
    have hinr : Sum.inr ⁻¹' P ⊆ B := by
      have := Set.preimage_mono (f := Sum.inr) hPP₂; rwa [inr_preimage_prodNbhd] at this
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]; exact f.mono hfP hZ₂Z hinl hZ₂ hA
    · rw [inr_preimage_prodNbhd]; exact g.mono hgP hZ₂Z hinr hZ₂ hB

@[simp] theorem proj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (proj₀ V₀ V₁).rel W X' ↔ (prod V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

@[simp] theorem proj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (proj₁ V₀ V₁).rel W Y' ↔ (prod V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

@[simp] theorem paired_rel {f : ApproximableMap V₂ V₀} {g : ApproximableMap V₂ V₁}
    {Z : Set γ} {P : Set (α ⊕ β)} :
    (paired f g).rel Z P ↔
      (prod V₀ V₁).mem P ∧ f.rel Z (Sum.inl ⁻¹' P) ∧ g.rel Z (Sum.inr ⁻¹' P) := Iff.rfl

/-- **Proposition 3.4(ii) (Scott 1981, PRG-19).** `p₀(z) = z₀`. -/
@[simp] theorem toElementMap_proj₀ (z : (prod V₀ V₁).Element) :
    (proj₀ V₀ V₁).toElementMap z = z.fst := by
  apply Element.ext
  intro X'
  constructor
  · rintro ⟨W, hzW, hW, hX', hsub⟩
    obtain ⟨A, B, _, hB, rfl⟩ := hW
    rw [inl_preimage_prodNbhd] at hsub
    refine ⟨hX', z.up_mem hzW (prod_mem_prodNbhd hX' V₁.master_mem) ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨hsub, V₁.sub_master hB⟩
  · rintro ⟨hX', hz⟩
    exact ⟨prodNbhd X' V₁.master, hz, prod_mem_prodNbhd hX' V₁.master_mem, hX', by simp⟩

/-- **Proposition 3.4(ii) (Scott 1981, PRG-19).** `p₁(z) = z₁`. -/
@[simp] theorem toElementMap_proj₁ (z : (prod V₀ V₁).Element) :
    (proj₁ V₀ V₁).toElementMap z = z.snd := by
  apply Element.ext
  intro Y'
  constructor
  · rintro ⟨W, hzW, hW, hY', hsub⟩
    obtain ⟨A, B, hA, _, rfl⟩ := hW
    rw [inr_preimage_prodNbhd] at hsub
    refine ⟨hY', z.up_mem hzW (prod_mem_prodNbhd V₀.master_mem hY') ?_⟩
    exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hA, hsub⟩
  · rintro ⟨hY', hz⟩
    exact ⟨prodNbhd V₀.master Y', hz, prod_mem_prodNbhd V₀.master_mem hY', hY', by simp⟩

/-- **Proposition 3.4(iv) (Scott 1981, PRG-19).** `⟨f, g⟩(w) = ⟨f(w), g(w)⟩`. -/
theorem toElementMap_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁)
    (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) := by
  apply Element.ext
  intro P
  constructor
  · rintro ⟨Z, hwZ, hP, hfZ, hgZ⟩
    exact ⟨Sum.inl ⁻¹' P, Sum.inr ⁻¹' P, ⟨Z, hwZ, hfZ⟩, ⟨Z, hwZ, hgZ⟩, prodNbhd_preimage hP⟩
  · rintro ⟨X, Y, ⟨Z₁, hwZ₁, hfZ₁⟩, ⟨Z₂, hwZ₂, hgZ₂⟩, rfl⟩
    refine ⟨Z₁ ∩ Z₂, w.inter_mem hwZ₁ hwZ₂, prod_mem_prodNbhd (f.rel_cod hfZ₁) (g.rel_cod hgZ₂),
      ?_, ?_⟩
    · rw [inl_preimage_prodNbhd]
      exact f.mono hfZ₁ Set.inter_subset_left subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (f.rel_cod hfZ₁)
    · rw [inr_preimage_prodNbhd]
      exact g.mono hgZ₂ Set.inter_subset_right subset_rfl (w.sub (w.inter_mem hwZ₁ hwZ₂))
        (g.rel_cod hgZ₂)

/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₀ ∘ ⟨f, g⟩ = f`. -/
theorem proj₀_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired f g) = f := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, fst_pair]

/-- **Proposition 3.4(i) (Scott 1981, PRG-19).** `p₁ ∘ ⟨f, g⟩ = g`. -/
theorem proj₁_comp_paired (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) :
    (proj₁ V₀ V₁).comp (paired f g) = g := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_proj₁, snd_pair]

/-- **Proposition 3.4(iii) (Scott 1981, PRG-19).** `h = ⟨p₀ ∘ h, p₁ ∘ h⟩`. -/
theorem paired_proj (h : ApproximableMap V₂ (prod V₀ V₁)) :
    paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, pair_fst_snd]

theorem prod_mem_prodNbhd_iff {X : Set α} {Y : Set β} :
    (prod V₀ V₁).mem (prodNbhd X Y) ↔ V₀.mem X ∧ V₁.mem Y := by
  constructor
  · rintro ⟨A, B, hA, hB, heq⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hA, hB⟩
  · rintro ⟨hX, hY⟩; exact prod_mem_prodNbhd hX hY

/-! ### Lemma 3.6 — constant maps. -/

/-- **Lemma 3.6 (Scott 1981, PRG-19).** The constant map at `b : |𝒟₁|`: `X b Y ↔ Y ∈ b`. -/
def constMap (V₀ : NeighborhoodSystem α) (b : V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ b.mem Y
  rel_dom h := h.1
  rel_cod h := b.sub h.2
  master_rel := ⟨V₀.master_mem, b.master_mem⟩
  inter_right := by rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩; exact ⟨hX, b.inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hY⟩ _ hYY' hX' hY'
    exact ⟨hX', b.up_mem hY hY' hYY'⟩

@[simp] theorem constMap_rel {b : V₁.Element} {X : Set α} {Y : Set β} :
    (constMap V₀ b).rel X Y ↔ V₀.mem X ∧ b.mem Y := Iff.rfl

/-- **Lemma 3.6 (Scott 1981, PRG-19).** The constant map sends every element to `b`. -/
@[simp] theorem toElementMap_constMap (b : V₁.Element) (x : V₀.Element) :
    (constMap V₀ b).toElementMap x = b := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, _, _, hbY⟩; exact hbY
  · intro hbY; exact ⟨V₀.master, x.master_mem, V₀.master_mem, hbY⟩

/-! ### Theorem 3.5 — joint vs. separate approximability. -/

/-- Extensionality for two-variable approximable mappings. -/
theorem ApproximableMap₂.ext {f g : ApproximableMap₂ V₀ V₁ V₂}
    (h : ∀ X Y Z, f.rel X Y Z ↔ g.rel X Y Z) : f = g := by
  obtain ⟨rf, _, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y Z; exact propext (h X Y Z)
  subst this; rfl

/-- **Theorem 3.5 (→) (Scott 1981, PRG-19).** A joint approximable mapping `𝒟₀ × 𝒟₁ → 𝒟₂`
restricts to a two-variable mapping `X, Y f Z ↔ (X ∪ Y) f Z`. -/
def toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap₂ V₀ V₁ V₂ where
  rel X Y Z := f.rel (prodNbhd X Y) Z
  rel_dom₀ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).1
  rel_dom₁ h := (prod_mem_prodNbhd_iff.mp (f.rel_dom h)).2
  rel_cod h := f.rel_cod h
  master_rel := f.master_rel
  inter_right h h' := f.inter_right h h'
  mono := by
    rintro X X' Y Y' Z Z' hrel hX'X hY'Y hZZ' hX' hY' hZ'
    exact f.mono hrel (prodNbhd_subset_iff.mpr ⟨hX'X, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX' hY') hZ'

/-- **Theorem 3.5 (←) (Scott 1981, PRG-19).** A two-variable mapping induces a joint mapping. -/
def ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ f.rel (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W) Z
  rel_dom h := h.1
  rel_cod h := f.rel_cod h.2
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    simpa using f.master_rel
  inter_right := by rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩; exact ⟨hW, f.inter_right hrel hrel'⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl
    rw [inr_preimage_prodNbhd] at hinr
    refine ⟨⟨A, B, hA, hB, rfl⟩, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact f.mono hrel hinl hinr hZZ' hA hB hZ'

theorem toMap₂_ofMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) : toMap₂ (ofMap₂ f) = f := by
  apply ApproximableMap₂.ext
  intro X Y Z
  show (prod V₀ V₁).mem (prodNbhd X Y) ∧ f.rel _ _ Z ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, hrel⟩; exact hrel
  · intro hrel
    exact ⟨prod_mem_prodNbhd (f.rel_dom₀ hrel) (f.rel_dom₁ hrel), hrel⟩

theorem ofMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) : ofMap₂ (toMap₂ f) = f := by
  apply ApproximableMap.ext
  intro W Z
  show (prod V₀ V₁).mem W ∧ f.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z ↔ _
  constructor
  · rintro ⟨hW, hrel⟩; rwa [← prodNbhd_preimage hW] at hrel
  · intro hrel
    exact ⟨f.rel_dom hrel, by rwa [← prodNbhd_preimage (f.rel_dom hrel)]⟩

/-- **Theorem 3.5 (Scott 1981, PRG-19).** The bijection between joint approximable mappings
`𝒟₀ × 𝒟₁ → 𝒟₂` and two-variable mappings `𝒟₀, 𝒟₁ → 𝒟₂`: a function of two arguments comes from
an approximable mapping iff it is separately approximable. -/
def map₂Equiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃ ApproximableMap₂ V₀ V₁ V₂ where
  toFun := toMap₂
  invFun := ofMap₂
  left_inv := ofMap₂_toMap₂
  right_inv := toMap₂_ofMap₂

/-- **Theorem 3.5 (elementwise) (Scott 1981, PRG-19).** The two-variable elementwise map of
`toMap₂ f` is `f` evaluated at the pairing: `(toMap₂ f)(x, y) = f(⟨x, y⟩)`. -/
theorem toElementMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, hX, hY, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
    exact ⟨X, Y, hX, hY, hrel⟩

/-! ### Proposition 3.7 — closure under substitution. -/

variable {V₃ : NeighborhoodSystem δ}

/-- **Proposition 3.7 (Scott 1981, PRG-19).** Multivariate approximable functions are closed under
substitution: substituting approximable maps `a, b : 𝒟₃ → 𝒟ᵢ` into a two-variable approximable map
`F : 𝒟₀ × 𝒟₁ → 𝒟₂` yields the approximable map `F ∘ ⟨a, b⟩`, whose value is `F(a(w), b(w))`. The
building blocks are exactly Definition 3.3's `paired` and Theorem 2.5's `comp`. -/
theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise315.lean -/

/-!
# Exercise 3.15 (Scott 1981, PRG-19, §3) — the usual product isomorphisms

Scott asks for the standard isomorphisms of the product construction. Because Proposition 3.2 gives
the order-isomorphism `prodEquiv : |𝒟₀ × 𝒟₁| ≃o |𝒟₀| × |𝒟₁|`, every isomorphism reduces to the
corresponding fact about cartesian products of *ordered sets*: mathlib's `OrderIso.prodComm` and
`OrderIso.prodAssoc`, together with the two product congruences `prodCongrOrderIso` /
`prodUniqueOrderIso` we record here.

* **(i)** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀` — `prodCommD`.
* **(ii)** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂` — `prodAssocD`.
* **The product of no factors** is the one-point (terminal) domain `𝟙 = unitSys`; it is a two-sided
  unit for `×`: `𝒟 × 𝟙 ≅ 𝒟 ≅ 𝟙 × 𝒟` (`prodUnitD`, `unitProdD`).
* **(iii)** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'` — `prodCongrD` /
  `Isomorphic.prod`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-! ### Order-iso helpers for cartesian products. -/

/-- The product of two order isomorphisms, as an order isomorphism. -/
def prodCongrOrderIso {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e₀ : A ≃o B) (e₁ : C ≃o D) : A × C ≃o B × D where
  toFun p := (e₀ p.1, e₁ p.2)
  invFun q := (e₀.symm q.1, e₁.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    show (e₀ a, e₁ c) ≤ (e₀ a', e₁ c') ↔ (a, c) ≤ (a', c')
    rw [Prod.mk_le_mk, Prod.mk_le_mk, e₀.le_iff_le, e₁.le_iff_le]

/-- For a `Unique` second factor, `A × C ≃o A` (forget the constant component). -/
def prodUniqueOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : A × C ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := by
    have : (default : C) = p.2 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨a, c⟩ ⟨a', c'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨h, le_of_eq (Subsingleton.elim c c')⟩, And.left⟩

/-- For a `Unique` first factor, `C × A ≃o A` (forget the constant component). -/
def uniqueProdOrderIso (A C : Type*) [Preorder A] [Preorder C] [Unique C] : C × A ≃o A where
  toFun p := p.2
  invFun a := (default, a)
  left_inv p := by
    have : (default : C) = p.1 := Subsingleton.elim _ _
    simp [this]
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨c, a⟩ ⟨c', a'⟩
    simp only [Prod.mk_le_mk]
    exact ⟨fun h => ⟨le_of_eq (Subsingleton.elim c c'), h⟩, And.right⟩

/-! ### (i) Commutativity. -/

/-- **Exercise 3.15(i) (Scott 1981, PRG-19).** The commutativity order-isomorphism
`|𝒟₀ × 𝒟₁| ≃o |𝒟₁ × 𝒟₀|`, factored through Proposition 3.2 and the cartesian swap. -/
def prodCommD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (prod V₀ V₁).Element ≃o (prod V₁ V₀).Element :=
  (prodEquiv V₀ V₁).trans (OrderIso.prodComm.trans (prodEquiv V₁ V₀).symm)

/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩

/-! ### (ii) Associativity. -/

/-- **Exercise 3.15(ii) (Scott 1981, PRG-19).** The associativity order-isomorphism
`|𝒟₀ × (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ × 𝒟₁) × 𝒟₂|`. -/
def prodAssocD (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (prod V₀ (prod V₁ V₂)).Element ≃o (prod (prod V₀ V₁) V₂).Element :=
  (prodEquiv V₀ (prod V₁ V₂)).trans <|
    (prodCongrOrderIso (OrderIso.refl V₀.Element) (prodEquiv V₁ V₂)).trans <|
      (OrderIso.prodAssoc V₀.Element V₁.Element V₂.Element).symm.trans <|
        (prodCongrOrderIso (prodEquiv V₀ V₁).symm (OrderIso.refl V₂.Element)).trans
          (prodEquiv (prod V₀ V₁) V₂).symm

/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

/-! ### The product of no factors — the terminal (one-point) domain. -/

/-- The **terminal domain** `𝟙`: the neighbourhood system over `Unit` with the single
neighbourhood `Δ = univ`. Its domain `|𝟙|` has exactly one element (`⊥ = {Δ}`), so `𝟙` is the
*product of no factors*. -/
def unitSys : NeighborhoodSystem Unit where
  mem X := X = Set.univ
  master := Set.univ
  master_nonempty := ⟨(), Set.mem_univ _⟩
  master_mem := rfl
  inter_mem := by rintro X Y Z rfl rfl _ _; simp
  sub_master := by rintro X rfl; exact subset_rfl

/-- `|𝟙|` is a subsingleton: every element is `⊥`. -/
theorem unitSys_element_eq (x : unitSys.Element) : x = unitSys.bot := by
  apply Element.ext
  intro Y
  constructor
  · intro hY; rw [mem_bot]; exact x.sub hY
  · intro hY; rw [mem_bot] at hY; subst hY; exact x.master_mem

instance : Unique unitSys.Element where
  default := unitSys.bot
  uniq := unitSys_element_eq

/-- **Exercise 3.15 (empty product).** `𝟙` is a right unit: `𝒟 × 𝟙 ≅ 𝒟`. -/
def prodUnitD (V₀ : NeighborhoodSystem α) :
    (prod V₀ unitSys).Element ≃o V₀.Element :=
  (prodEquiv V₀ unitSys).trans (prodUniqueOrderIso _ _)

theorem prod_unit_isomorphic : prod V₀ unitSys ≅ᴰ V₀ := ⟨prodUnitD V₀⟩

/-- **Exercise 3.15 (empty product).** `𝟙` is a left unit: `𝟙 × 𝒟 ≅ 𝒟`. -/
def unitProdD (V₀ : NeighborhoodSystem α) :
    (prod unitSys V₀).Element ≃o V₀.Element :=
  (prodEquiv unitSys V₀).trans (uniqueProdOrderIso _ _)

theorem unit_prod_isomorphic : prod unitSys V₀ ≅ᴰ V₀ := ⟨unitProdD V₀⟩

/-! ### (iii) Functoriality of `≅`. -/

/-- **Exercise 3.15(iii) (Scott 1981, PRG-19).** Two domain isomorphisms induce one on the products:
`|𝒟₀ × 𝒟₁| ≃o |𝒟₀' × 𝒟₁'|`. -/
def prodCongrD (e₀ : V₀.Element ≃o V₀'.Element) (e₁ : V₁.Element ≃o V₁'.Element) :
    (prod V₀ V₁).Element ≃o (prod V₀' V₁').Element :=
  (prodEquiv V₀ V₁).trans ((prodCongrOrderIso e₀ e₁).trans (prodEquiv V₀' V₁').symm)

/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise316.lean -/

/-!
# Exercise 3.16 (Scott 1981, PRG-19, §3) — the infinite iterate `𝒟^∞`

Scott: for a neighbourhood system `𝒟` over `Δ`, let `Δ^∞ = ⋃ₙ 1ⁿ0Δ` be infinitely many disjoint
copies of `Δ`, and let `𝒟^∞` be the *least* family of subsets with

1. `Δ^∞ ∈ 𝒟^∞`, and
2. `X ∈ 𝒟`, `Y ∈ 𝒟^∞` ⟹ `0X ∪ 1Y ∈ 𝒟^∞`.

He asks to show `𝒟^∞` is a neighbourhood system over `Δ^∞`, that `𝒟^∞ ≅ 𝒟 × 𝒟^∞`, and that the
elements of `|𝒟^∞|` are in one-one correspondence with arbitrary infinite sequences `⟨xₙ⟩` of
elements `xₙ ∈ |𝒟|`, via the combinations of neighbourhoods

`0X₀ ∪ 10X₁ ∪ ⋯ ∪ 1ⁿ0Xₙ ∪ ⋯`   (with all but finitely many `Xₘ = Δ`).

**Model.** We take the token type to be `ℕ × α`, where `(n, a)` is "the token `a ∈ Δ` sitting in
the `n`-th copy" (i.e. Scott's `1ⁿ0a`). A neighbourhood `0X₀ ∪ 1ⁿ0Xₙ ∪ ⋯` is then exactly the set
`{(i, a) ∣ a ∈ Xᵢ}`, recovered from `W` by its **fibers** `fiber W i = {a ∣ (i, a) ∈ W}`. The
"least family" description is equivalent to: `W ∈ 𝒟^∞` iff every fiber is a neighbourhood and all
but finitely many fibers equal `Δ`. (Closure under (2) and the base (1) generate exactly these, and
no fewer, because (2) is the one-step "cons" and the cofinite-`Δ` condition is its iterate.)

The element-level payoff is the clean order-isomorphism

`iterSeqEquiv : |𝒟^∞| ≃o (ℕ → |𝒟|)`

(Scott's "one-one correspondence with infinite sequences"), from which `𝒟^∞ ≅ 𝒟 × 𝒟^∞` falls out by
the shift `(ℕ → E) ≃o E × (ℕ → E)`.

Everything is **choice-free in spirit**; the classical content is only what is inherited from the
project's `Element.ext`/`prodEquiv` machinery, as elsewhere in §3.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

/-! ### Fibers of a set of `(copy index, token)` pairs. -/

/-- The `i`-th *fiber* of a set `W ⊆ ℕ × α`: the tokens appearing in copy `i`. -/
def fiber (W : Set (ℕ × α)) (i : ℕ) : Set α := {a | (i, a) ∈ W}

@[simp] theorem mem_fiber {W : Set (ℕ × α)} {i : ℕ} {a : α} : a ∈ fiber W i ↔ (i, a) ∈ W := Iff.rfl

theorem fiber_mono {W W' : Set (ℕ × α)} (h : W ⊆ W') (i : ℕ) : fiber W i ⊆ fiber W' i :=
  fun _ ha => h ha

theorem fiber_inter (W W' : Set (ℕ × α)) (i : ℕ) :
    fiber (W ∩ W') i = fiber W i ∩ fiber W' i := rfl

theorem eq_of_fiber_eq {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i = fiber W' i) : W = W' := by
  ext ⟨i, a⟩
  exact Set.ext_iff.mp (h i) a

theorem subset_of_fiber_subset {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i ⊆ fiber W' i) :
    W ⊆ W' := fun ⟨i, _⟩ ha => h i ha

/-! ### The pinning neighbourhood `single n X` (Scott's `1ⁿ0X`, rest `Δ`). -/

variable (V : NeighborhoodSystem α)

/-- The `𝒟^∞`-neighbourhood pinning copy `n` to `X` and leaving all other copies at `Δ`: Scott's
`Δ^∞ ∩ (1ⁿ0X)`, i.e. the combination with `Xₙ = X` and `Xₘ = Δ` for `m ≠ n`. -/
def single (n : ℕ) (X : Set α) : Set (ℕ × α) :=
  {p | if p.1 = n then p.2 ∈ X else p.2 ∈ V.master}

variable {V}

@[simp] theorem fiber_single_self (n : ℕ) (X : Set α) : fiber (single V n X) n = X := by
  ext a; simp [fiber, single]

theorem fiber_single_ne {n i : ℕ} (h : i ≠ n) (X : Set α) : fiber (single V n X) i = V.master := by
  ext a; simp [fiber, single, h]

theorem single_mono {n : ℕ} {X X' : Set α} (h : X ⊆ X') : single V n X ⊆ single V n X' := by
  intro p hp
  simp only [single, Set.mem_ofPred_eq] at hp ⊢
  by_cases hc : p.1 = n
  · rw [if_pos hc] at hp ⊢; exact h hp
  · rw [if_neg hc] at hp ⊢; exact hp

theorem single_inter {n : ℕ} (X X' : Set α) :
    single V n X ∩ single V n X' = single V n (X ∩ X') := by
  apply eq_of_fiber_eq
  intro i
  by_cases h : i = n
  · subst h; rw [fiber_inter, fiber_single_self, fiber_single_self, fiber_single_self]
  · rw [fiber_inter, fiber_single_ne h, fiber_single_ne h, fiber_single_ne h, Set.inter_self]

/-! ### The system `𝒟^∞`. -/

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The infinite iterate `𝒟^∞` over `Δ^∞ = ℕ × Δ`:
`W ∈ 𝒟^∞` iff every fiber is a neighbourhood of `𝒟` and all but finitely many fibers equal `Δ`. -/
def iterSys (V : NeighborhoodSystem α) : NeighborhoodSystem (ℕ × α) where
  mem W := (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master
  master := {p | p.2 ∈ V.master}
  master_nonempty := by
    obtain ⟨a, ha⟩ := V.master_nonempty
    exact ⟨(0, a), ha⟩
  master_mem := ⟨fun _ => V.master_mem, 0, fun _ _ => rfl⟩
  inter_mem := by
    rintro W W' Z ⟨hWf, NW, hNW⟩ ⟨hW'f, NW', hNW'⟩ ⟨hZf, _⟩ hsub
    refine ⟨fun i => ?_, max NW NW', fun i hi => ?_⟩
    · rw [fiber_inter]
      exact V.inter_mem (hWf i) (hW'f i) (hZf i) (fiber_mono hsub i)
    · rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  sub_master := by
    rintro W ⟨hWf, _⟩ ⟨i, a⟩ ha
    exact V.sub_master (hWf i) ha

@[simp] theorem iterSys_master : (iterSys V).master = {p : ℕ × α | p.2 ∈ V.master} := rfl

theorem fiber_iterSys_master (i : ℕ) : fiber ((iterSys V).master) i = V.master := rfl

@[simp] theorem mem_iterSys {W : Set (ℕ × α)} :
    (iterSys V).mem W ↔ (∀ i, V.mem (fiber W i)) ∧ ∃ N, ∀ i, N ≤ i → fiber W i = V.master := Iff.rfl

/-- `single V n X` is a `𝒟^∞`-neighbourhood whenever `X ∈ 𝒟`. -/
theorem single_mem {n : ℕ} {X : Set α} (hX : V.mem X) : (iterSys V).mem (single V n X) := by
  refine ⟨fun i => ?_, n + 1, fun i hi => ?_⟩
  · by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact V.master_mem
  · exact fiber_single_ne (by omega : i ≠ n) X

theorem single_master (n : ℕ) : single V n V.master = (iterSys V).master := by
  apply eq_of_fiber_eq
  intro i
  rw [fiber_iterSys_master]
  by_cases h : i = n
  · subst h; rw [fiber_single_self]
  · rw [fiber_single_ne h]

/-- Every `𝒟^∞`-neighbourhood is contained in the pinning of its own `i`-th fiber. -/
theorem subset_single {W : Set (ℕ × α)} (hW : (iterSys V).mem W) (i : ℕ) :
    W ⊆ single V i (fiber W i) := by
  rintro ⟨j, a⟩ ha
  simp only [single, Set.mem_ofPred_eq]
  by_cases h : j = i
  · rw [if_pos h]; subst h; exact ha
  · rw [if_neg h]; exact V.sub_master (hW.1 j) ha

theorem interUpTo_subset_master (F : ℕ → Set (ℕ × α)) (N : ℕ) :
    (iterSys V).interUpTo F N ⊆ (iterSys V).master := by
  induction N with
  | zero => exact subset_rfl
  | succ n ih => rw [NeighborhoodSystem.interUpTo_succ]; exact Set.inter_subset_left.trans ih

/-- The finite intersection `⋂_{i<N} single i (fiber W i)` reconstructs `W` from below, once `N`
exceeds the cofinite-`Δ` bound of `W`. -/
theorem reconstruct_subset {W : Set (ℕ × α)} (_hW : (iterSys V).mem W) {N : ℕ}
    (hN : ∀ i, N ≤ i → fiber W i = V.master) :
    (iterSys V).interUpTo (fun i => single V i (fiber W i)) N ⊆ W := by
  rintro ⟨j, a⟩ ha
  by_cases h : j < N
  · have hsub := (iterSys V).interUpTo_subset (fun i => single V i (fiber W i)) h
    have hmem : (j, a) ∈ single V j (fiber W j) := hsub ha
    simpa [single] using hmem
  · have haM : a ∈ V.master := interUpTo_subset_master (fun i => single V i (fiber W i)) N ha
    have : a ∈ fiber W j := by rw [hN j (not_lt.mp h)]; exact haM
    exact this

/-! ### Components and sequences. -/

/-- The `n`-th component `xₙ ∈ |𝒟|` of a `𝒟^∞`-element `z` (Scott's coordinate at copy `n`). -/
def component (z : (iterSys V).Element) (n : ℕ) : V.Element where
  mem X := V.mem X ∧ z.mem (single V n X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [single_master]; exact z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz : z.mem (single V n (X ∩ X')) := by rw [← single_inter]; exact z.inter_mem hzX hzX'
    have hmem : V.mem (X ∩ X') := by
      have := (z.sub hz).1 n; rwa [fiber_single_self] at this
    exact ⟨hmem, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (single_mem hX') (single_mono hXX')⟩

@[simp] theorem mem_component {z : (iterSys V).Element} {n : ℕ} {X : Set α} :
    (component z n).mem X ↔ V.mem X ∧ z.mem (single V n X) := Iff.rfl

/-- The `𝒟^∞`-element determined by an infinite sequence `⟨xₙ⟩` of `𝒟`-elements: the neighbourhoods
`W` whose every fiber lies in the corresponding `xᵢ`. -/
def ofSeq (seq : ℕ → V.Element) : (iterSys V).Element where
  mem W := (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i)
  sub h := h.1
  master_mem := ⟨(iterSys V).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (seq i).master_mem⟩
  inter_mem := by
    rintro W W' ⟨hW, hWf⟩ ⟨hW', hW'f⟩
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [fiber_inter]; exact (seq i).sub ((seq i).inter_mem (hWf i) (hW'f i))
    · obtain ⟨NW, hNW⟩ := hW.2
      obtain ⟨NW', hNW'⟩ := hW'.2
      refine ⟨max NW NW', fun i hi => ?_⟩
      rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
        hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
    · rw [fiber_inter]; exact (seq i).inter_mem (hWf i) (hW'f i)
  up_mem := by
    rintro W W' ⟨_, hWf⟩ hW' hWW'
    exact ⟨hW', fun i => (seq i).up_mem (hWf i) (hW'.1 i) (fiber_mono hWW' i)⟩

@[simp] theorem mem_ofSeq {seq : ℕ → V.Element} {W : Set (ℕ × α)} :
    (ofSeq seq).mem W ↔ (iterSys V).mem W ∧ ∀ i, (seq i).mem (fiber W i) := Iff.rfl

theorem ofSeq_mono {seq seq' : ℕ → V.Element} (h : ∀ n, seq n ≤ seq' n) :
    ofSeq seq ≤ ofSeq seq' := by
  rintro W ⟨hW, hf⟩
  exact ⟨hW, fun i => h i _ (hf i)⟩

/-! ### The two round-trips. -/

@[simp] theorem component_ofSeq (seq : ℕ → V.Element) (n : ℕ) :
    component (ofSeq seq) n = seq n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨_, _, hfib⟩
    have := hfib n; rwa [fiber_single_self] at this
  · intro hX
    refine ⟨(seq n).sub hX, single_mem ((seq n).sub hX), fun i => ?_⟩
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hX
    · rw [fiber_single_ne h]; exact (seq i).master_mem

@[simp] theorem ofSeq_component (z : (iterSys V).Element) :
    ofSeq (fun n => component z n) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hW, hfib⟩
    obtain ⟨N, hN⟩ := hW.2
    exact z.up_mem (z.mem_interUpTo _ (n := N) (fun i _ => (hfib i).2)) hW
      (reconstruct_subset hW hN)
  · intro hzW
    refine ⟨z.sub hzW, fun i => ?_⟩
    exact ⟨(z.sub hzW).1 i, z.up_mem hzW (single_mem ((z.sub hzW).1 i)) (subset_single (z.sub hzW) i)⟩

/-- `z ⊑ z'` is detected component-wise. -/
theorem le_of_component_le {z z' : (iterSys V).Element}
    (h : ∀ n, component z n ≤ component z' n) : z ≤ z' := by
  have hmono := ofSeq_mono h
  rwa [ofSeq_component, ofSeq_component] at hmono

/-! ### Scott's two conclusions. -/

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The elements of `|𝒟^∞|` are in one-one,
order-preserving correspondence with infinite sequences `⟨xₙ⟩` of elements of `|𝒟|`. -/
def iterSeqEquiv (V : NeighborhoodSystem α) : (iterSys V).Element ≃o (∀ _ : ℕ, V.Element) where
  toFun z := fun n => component z n
  invFun seq := ofSeq seq
  left_inv z := ofSeq_component z
  right_inv seq := by funext n; exact component_ofSeq seq n
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h
      exact le_of_component_le (fun n => h n)
    · intro h n X hX
      exact ⟨hX.1, h (single V n X) hX.2⟩

/-- The shift order-isomorphism `(ℕ → E) ≃o E × (ℕ → E)`, `f ↦ (f 0, f ∘ succ)`. -/
def natShiftEquiv (E : Type*) [Preorder E] : (ℕ → E) ≃o E × (ℕ → E) where
  toFun f := (f 0, fun n => f (n + 1))
  invFun p := fun n => Nat.casesOn n p.1 (fun m => p.2 m)
  left_inv f := by funext n; cases n <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h0, hs⟩
      intro n
      cases n with
      | zero => exact h0
      | succ m => exact hs m
    · intro h
      exact ⟨h 0, fun m => h (m + 1)⟩

/-- **Exercise 3.16 (Scott 1981, PRG-19).** The isomorphism `|𝒟^∞| ≃o |𝒟 × 𝒟^∞|`, obtained from the
sequence correspondence and the shift. -/
def iterProdIso (V : NeighborhoodSystem α) :
    (iterSys V).Element ≃o (prod V (iterSys V)).Element :=
  (iterSeqEquiv V).trans <|
    (natShiftEquiv V.Element).trans <|
      (prodCongrOrderIso (OrderIso.refl V.Element) (iterSeqEquiv V).symm).trans
        (prodEquiv V (iterSys V)).symm

/-- **Exercise 3.16 (Scott 1981, PRG-19).** `𝒟^∞ ≅ 𝒟 × 𝒟^∞`. -/
theorem iter_isomorphic (V : NeighborhoodSystem α) : iterSys V ≅ᴰ prod V (iterSys V) :=
  ⟨iterProdIso V⟩

/-! ### The coordinate projections `𝒟^∞ → 𝒟` (used in Exercise 3.24(ii)). -/

open ApproximableMap

/-- The `n`-th coordinate projection `projN n : 𝒟^∞ → 𝒟`, `W (projN n) X ↔ fiber W n ⊆ X`. -/
def projN (V : NeighborhoodSystem α) (n : ℕ) : ApproximableMap (iterSys V) V where
  rel W X := (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, V.master_mem, by rw [fiber_iterSys_master]⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    exact ⟨hW, V.inter_mem hX hX' (hW.1 n) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, _, hsub⟩ hW₂W hXX₂ hW₂ hX₂
    exact ⟨hW₂, hX₂, (fiber_mono hW₂W n).trans (hsub.trans hXX₂)⟩

@[simp] theorem projN_rel {n : ℕ} {W : Set (ℕ × α)} {X : Set α} :
    (projN V n).rel W X ↔ (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X := Iff.rfl

/-- `projN n` extracts the `n`-th component: `projN n (z) = component z n`. -/
@[simp] theorem toElementMap_projN (z : (iterSys V).Element) (n : ℕ) :
    (projN V n).toElementMap z = component z n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨W, hzW, hW, hX, hsub⟩
    refine ⟨hX, z.up_mem hzW (single_mem hX) ?_⟩
    refine subset_of_fiber_subset (fun i => ?_)
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hsub
    · rw [fiber_single_ne h]; exact V.sub_master (hW.1 i)
  · rintro ⟨hX, hz⟩
    exact ⟨single V n X, hz, single_mem hX, hX, by rw [fiber_single_self]⟩

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise319.lean -/

/-!
# Exercise 3.19 / 3.20 (Scott 1981, PRG-19, §3) — the product functor `f × g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise 3.19 constructs
the product mapping `f × g : 𝒟₀ × 𝒟₁ → 𝒟₀' × 𝒟₁'` with

* **(i)** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, and
* **(ii)** `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`.

We take (ii) as the definition (`prodMap`, built from Definition 3.3's `paired`/`proj`), and prove
(i) — indeed the more general `toElementMap_prodMap` (`(f × g)(w) = ⟨f(w₀), g(w₁)⟩`).

Exercise 3.20 (for category theorists) then follows: `×` is a **functor** (`prodMap_id`,
`prodMap_comp`), and `prod` with its projections is the **categorical product** — the universal
property `paired`/`proj` with uniqueness `paired_unique`.

The sum functor `f + g` is treated in `Exercise318.lean`/`Exercise319Sum.lean` after the sum system
is built. Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.19(ii) (Scott 1981, PRG-19).** The product mapping `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`. -/
def prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (prod V₀ V₁) (prod V₀' V₁') :=
  paired (f.comp (proj₀ V₀ V₁)) (g.comp (proj₁ V₀ V₁))

/-- **Exercise 3.19 (Scott 1981, PRG-19).** `(f × g)(w) = ⟨f(w₀), g(w₁)⟩` for every product element
`w` (so in particular `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, equation (i)). -/
theorem toElementMap_prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (w : (prod V₀ V₁).Element) :
    (prodMap f g).toElementMap w = pair (f.toElementMap w.fst) (g.toElementMap w.snd) := by
  rw [prodMap, toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁]

/-- **Exercise 3.19(i) (Scott 1981, PRG-19).** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`. -/
theorem toElementMap_prodMap_pair (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (x : V₀.Element) (y : V₁.Element) :
    (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y) := by
  rw [toElementMap_prodMap, fst_pair, snd_pair]

/-! ### Exercise 3.20 — `×` is a functor. -/

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves composition:
`(f' ∘ f) × (g' ∘ g) = (f' × g') ∘ (f × g)`. -/
theorem prodMap_comp {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

/-! ### Exercise 3.20 — `prod` is the categorical product. -/

/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (existence):
`p₀ ∘ ⟨h₀, h₁⟩ = h₀` and `p₁ ∘ ⟨h₀, h₁⟩ = h₁` (these are Proposition 3.4(i)). -/
theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (uniqueness):
any `k` with `p₀ ∘ k = h₀` and `p₁ ∘ k = h₁` equals the pairing `⟨h₀, h₁⟩`. Hence `prod` with
`proj₀`, `proj₁` is the categorical product of `𝒟₀` and `𝒟₁`. -/
theorem paired_unique (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
    (k : ApproximableMap V₂ (prod V₀ V₁)) (hk₀ : (proj₀ V₀ V₁).comp k = h₀)
    (hk₁ : (proj₁ V₀ V₁).comp k = h₁) : k = paired h₀ h₁ := by
  rw [← hk₀, ← hk₁, paired_proj]

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise326.lean -/

/-!
# Exercise 3.26 (Scott 1981, PRG-19, §3) — the conditional operator `cond`

Scott asks: for every domain `D` there is an approximable mapping

`cond : T × D × D → D`

(the *conditional operator*) satisfying

* `cond(true,  x, y) = x`,
* `cond(false, x, y) = y`,
* `cond(⊥,     x, y) = ⊥`.

Here `T` is the truth domain of Example 1.2 (`Example12.neighborhoodSystem`), whose neighbourhoods
are `{Δ, {0}, {1}}` with `true = ↑{0}` (`Example23.trueElt`), `false = ↑{1}` (`falseElt`) and
`⊥ = {Δ}` (`botElt`). The product `T × D × D` is the tagged product of Exercise 3.14, modelled here
as `prod T (prod V V)` over the token type `T.Token ⊕ (α ⊕ α)`; a neighbourhood is
`0C ∪ 10X ∪ 110Y`, recovered from `W` by the projections `C = inl⁻¹ W`, `X = inl⁻¹ inr⁻¹ W`,
`Y = inr⁻¹ inr⁻¹ W`.

Scott's hint gives the relation directly:

```
0C ∪ 10X ∪ 110Y  cond  Z   iff   0 ∈ C and X ⊆ Z,  or
                                  1 ∈ C and Y ⊆ Z,  or
                                  0, 1 ∈ C and Δ ⊆ Z.
```

Since `T = {Δ, {0}, {1}}`, the three guards on `C` are *mutually exclusive and exhaustive*:
`0 ∈ C` (alone) means `C = {0}`, `1 ∈ C` (alone) means `C = {1}`, and `0, 1 ∈ C` means `C = Δ`. We
therefore phrase the relation with explicit equalities `C = {0} / {1} / Δ` (`condGuard`), which is
mathematically identical to Scott's membership form but makes the case analysis transparent and the
three identities clean.

Everything is **choice-free** in spirit; the only classical input is inherited from `T` (Example 1.2)
and from the project's `ext_of_toElementMap`/`Element.ext` machinery, as elsewhere in §3.
-/

namespace Scott1980.Neighborhood.Exercise326

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- The truth domain `T` of Example 1.2 (neighbourhoods `{Δ, {0}, {1}}`). -/
abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-! ### Token-level facts about `T`'s three neighbourhoods `{0}`, `{1}`, `Δ`. -/

theorem zero_ne_one : (Example12.zero : Set Example12.Token) ≠ Example12.one := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.zero, Example12.one] at h0

theorem zero_ne_master : (Example12.zero : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h1 := Set.ext_iff.mp h 1
  simp [Example12.zero, Example12.master] at h1

theorem one_ne_master : (Example12.one : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.one, Example12.master] at h0

/-- A `T`-neighbourhood contained in `{0}` is `{0}` (the other two, `Δ` and `{1}`, are not). -/
theorem Tmem_eq_zero {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.zero) :
    C = Example12.zero := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 1)) (by simp [Example12.zero])
  · rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])

/-- A `T`-neighbourhood contained in `{1}` is `{1}`. -/
theorem Tmem_eq_one {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.one) :
    C = Example12.one := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 0)) (by simp [Example12.one])
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])
  · rfl

/-! ### The conditional relation. -/

/-- Scott's guard for `cond`, phrased with explicit equalities on the truth component
`C = inl⁻¹ W`. With `X = inl⁻¹ inr⁻¹ W` and `Y = inr⁻¹ inr⁻¹ W`:

* `C = {0}` (`true`):  `X ⊆ Z`;
* `C = {1}` (`false`): `Y ⊆ Z`;
* `C = Δ` (`⊥`):       `Δ_D ⊆ Z`. -/
def condGuard (V : NeighborhoodSystem α) (W : Set (Example12.Token ⊕ (α ⊕ α))) (Z : Set α) : Prop :=
  (Sum.inl ⁻¹' W = Example12.zero ∧ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.one ∧ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.master ∧ V.master ⊆ Z)

variable (V : NeighborhoodSystem α)

theorem condGuard_zero {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.zero) : Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨_, h⟩ | ⟨hC', _⟩ | ⟨hC', _⟩
  · exact h
  · exact absurd (hC.symm.trans hC') zero_ne_one
  · exact absurd (hC.symm.trans hC') zero_ne_master

theorem condGuard_one {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.one) : Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨_, h⟩ | ⟨hC', _⟩
  · exact absurd (hC.symm.trans hC') zero_ne_one.symm
  · exact h
  · exact absurd (hC.symm.trans hC') one_ne_master

theorem condGuard_master {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.master) : V.master ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨hC', _⟩ | ⟨_, h⟩
  · exact absurd (hC.symm.trans hC') zero_ne_master.symm
  · exact absurd (hC.symm.trans hC') one_ne_master.symm
  · exact h

/-- The three components `C, X, Y` of an input neighbourhood are themselves neighbourhoods. -/
theorem cond_components {W : Set (Example12.Token ⊕ (α ⊕ α))}
    (hW : (prod TD (prod V V)).mem W) :
    Example12.mem (Sum.inl ⁻¹' W) ∧
      V.mem (Sum.inl ⁻¹' (Sum.inr ⁻¹' W)) ∧ V.mem (Sum.inr ⁻¹' (Sum.inr ⁻¹' W)) := by
  obtain ⟨C, P, hC, hP, rfl⟩ := hW
  obtain ⟨X, Y, hX, hY, rfl⟩ := hP
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨hC, hX, hY⟩

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The conditional operator `cond : T × D × D → D`. -/
def cond (V : NeighborhoodSystem α) : ApproximableMap (prod TD (prod V V)) V where
  rel W Z := (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨(prod TD (prod V V)).master_mem, V.master_mem, Or.inr (Or.inr ⟨?_, subset_rfl⟩)⟩
    show Sum.inl ⁻¹' (prod TD (prod V V)).master = Example12.master
    rw [prod_master, inl_preimage_prodNbhd]; rfl
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hg⟩ ⟨_, hZ', hg'⟩
    obtain ⟨_, hX, hY⟩ := cond_components V hW
    refine ⟨hW, ?_, ?_⟩
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact V.inter_mem hZ hZ' hX (Set.subset_inter hXZ (condGuard_zero V hg' hCz))
      · exact V.inter_mem hZ hZ' hY (Set.subset_inter hYZ (condGuard_one V hg' hCo))
      · exact V.inter_mem hZ hZ' V.master_mem (Set.subset_inter hmZ (condGuard_master V hg' hCm))
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact Or.inl ⟨hCz, Set.subset_inter hXZ (condGuard_zero V hg' hCz)⟩
      · exact Or.inr (Or.inl ⟨hCo, Set.subset_inter hYZ (condGuard_one V hg' hCo)⟩)
      · exact Or.inr (Or.inr ⟨hCm, Set.subset_inter hmZ (condGuard_master V hg' hCm)⟩)
  mono := by
    rintro W W₂ Z Z₂ ⟨hW, hZ, hg⟩ hW₂W hZZ₂ hW₂ hZ₂
    obtain ⟨hC₂, hX₂, hY₂⟩ := cond_components V hW₂
    refine ⟨hW₂, hZ₂, ?_⟩
    have hCsub : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hXsub : Sum.inl ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    have hYsub : Sum.inr ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
    · exact Or.inl ⟨Tmem_eq_zero hC₂ (hCsub.trans hCz.subset), (hXsub.trans hXZ).trans hZZ₂⟩
    · exact Or.inr (Or.inl ⟨Tmem_eq_one hC₂ (hCsub.trans hCo.subset),
        (hYsub.trans hYZ).trans hZZ₂⟩)
    · have hmZ₂ : V.master ⊆ Z₂ := hmZ.trans hZZ₂
      rcases (Example12.mem_iff (Sum.inl ⁻¹' W₂)).mp hC₂ with hC₂m | hC₂z | hC₂o
      · exact Or.inr (Or.inr ⟨hC₂m, hmZ₂⟩)
      · exact Or.inl ⟨hC₂z, (V.sub_master hX₂).trans hmZ₂⟩
      · exact Or.inr (Or.inl ⟨hC₂o, (V.sub_master hY₂).trans hmZ₂⟩)

@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

/-! ### Elementwise characterization, and the three defining identities. -/

/-- The elementwise action of `cond`, computed at a paired argument `⟨t, ⟨x, y⟩⟩`: a neighbourhood
`Z` lies in `cond(t, x, y)` iff `t` selects `true` (`{0} ∈ t`) and `Z ∈ x`, or `t` selects `false`
(`{1} ∈ t`) and `Z ∈ y`, or `Z = Δ_D` (the always-present master). The three defining identities are
immediate corollaries. -/
theorem cond_toElementMap_mem (t : TD.Element) (x y : V.Element) {Z : Set α} :
    ((cond V).toElementMap (pair t (pair x y))).mem Z ↔
      (t.mem Example12.zero ∧ x.mem Z) ∨ (t.mem Example12.one ∧ y.mem Z) ∨ Z = V.master := by
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCt, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨_, hmZ⟩
    · exact Or.inl ⟨hCz ▸ hCt, x.up_mem hXx hZ hXZ⟩
    · exact Or.inr (Or.inl ⟨hCo ▸ hCt, y.up_mem hYy hZ hYZ⟩)
    · exact Or.inr (Or.inr (Set.Subset.antisymm (V.sub_master hZ) hmZ))
  · intro h
    rcases h with ⟨ht0, hxZ⟩ | ⟨ht1, hyZ⟩ | rfl
    · have hZ : V.mem Z := x.sub hxZ
      refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
        ht0, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
      refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
      rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
    · have hZ : V.mem Z := y.sub hyZ
      refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
        ht1, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
      refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
      rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]
    · refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
        ⟨Example12.master, prodNbhd V.master V.master, t.master_mem,
          ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
        V.master_mem, ?_⟩
      exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

/-- **Exercise 3.26(i) (Scott 1981, PRG-19).** `cond(true, x, y) = x`. -/
theorem cond_true (x y : V.Element) :
    (cond V).toElementMap (pair Example23.trueElt (pair x y)) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCtrue, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨_, hXZ⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact x.up_mem hXx hZ hXZ
    · rcases hCtrue with hCm | hCz
      · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
      · exact absurd (hCz.symm.trans hCo) zero_ne_one
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact x.master_mem
  · intro hxZ
    have hZ : V.mem Z := x.sub hxZ
    refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
      Or.inr rfl, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
    refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
    rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]

/-- **Exercise 3.26(ii) (Scott 1981, PRG-19).** `cond(false, x, y) = y`. -/
theorem cond_false (x y : V.Element) :
    (cond V).toElementMap (pair Example23.falseElt (pair x y)) = y := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCfalse, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, _⟩ | ⟨_, hYZ⟩ | ⟨_, hmZ⟩
    · rcases hCfalse with hCm | hCo
      · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
      · exact absurd (hCo.symm.trans hCz) zero_ne_one.symm
    · exact y.up_mem hYy hZ hYZ
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact y.master_mem
  · intro hyZ
    have hZ : V.mem Z := y.sub hyZ
    refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
      Or.inr rfl, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
    refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
    rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]

/-- **Exercise 3.26(iii) (Scott 1981, PRG-19).** `cond(⊥, x, y) = ⊥`. -/
theorem cond_bot (x y : V.Element) :
    (cond V).toElementMap (pair Example23.botElt (pair x y)) = V.bot := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCbot, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    have hCm : C = Example12.master := hCbot
    rcases hg with ⟨hCz, _⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
    · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
    · rw [mem_bot, Set.Subset.antisymm (V.sub_master hZ) hmZ]
  · intro hbZ
    rw [mem_bot] at hbZ
    subst hbZ
    refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
      ⟨Example12.master, prodNbhd V.master V.master, rfl,
        ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
      V.master_mem, ?_⟩
    exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end Scott1980.Neighborhood.Exercise326

/-! ### Inlined from Scott1980/Neighborhood/Exercise619.lean -/

/-!
# Exercise 6.19 (Scott 1981, PRG-19, §6) — sum and product on the category of strict maps

> **EXERCISE 6.19.** For the sake of uniformity restrict attention to systems `𝒟` on sets
> `Δ ⊆ {0,1}*`, where `Λ ∈ Δ` and `∅ ∉ 𝒟`, and to the category of strict maps. Define sum and
> product by
> `𝒟₀ + 𝒟₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`,
> `𝒟₀ × 𝒟₁ = {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀ and Y ∈ 𝒟₁}`.
> Are these correct up to isomorphism? …

This module formalizes **Part A** of the exercise: Scott's *uniform* token-level presentations of
sum and product over `{0,1}*` (so that the constructions are genuine *endo*-operations on a single
category, unlike the abstract separated sum `𝒟₀ + 𝒟₁` of Exercise 3.18 over `Option (α ⊕ β)` or the
product `𝒟₀ × 𝒟₁` of Definition 3.1 over `α ⊕ β`), and the answer to *"Are these correct up to
isomorphism?"* — **yes**:

* `sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁`, and
* `prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁`.

We reuse the single-bit prefix `embBit b X = bX` of Example 6.2 (so `0X = embBit false X`,
`1Y = embBit true Y`), whose disjointness/intersection algebra (`embBit_inter`, `embBit_inter_ne`,
`embBit_subset`, `embBit_injective`, `embBit_nonempty`) is exactly what makes the concrete sum a
neighbourhood system and drives the isomorphism (a token-level analogue of `Example62.bbEquiv`,
generalised from `B` to arbitrary `∅`-free `D₀, D₁`).

The functor-algebra closure (all `T(X)` generated by constants/identity/sum/product are functors,
continuous on maps, monotone and continuous on domains) is **Part B**, deferred.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## The concrete sum `D₀ + D₁` over `{0,1}*`

`D₀ + D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ 𝒟₀} ∪ {1Y ∣ Y ∈ 𝒟₁}`, with `Λ = []`, `0X = embBit false X`,
`1Y = embBit true Y`. -/

/-- The master neighbourhood `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` of the concrete sum. -/
def sumTokMaster (D₀ D₁ : NeighborhoodSystem Str) : Set Str :=
  insert [] (embBit false D₀.master ∪ embBit true D₁.master)

theorem nil_mem_sumTokMaster : ([] : Str) ∈ sumTokMaster D₀ D₁ := Set.mem_insert _ _

theorem embF_subset_sumTokMaster {X : Set Str} (hX : D₀.mem X) :
    embBit false X ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₀.sub_master hX)).trans (Set.subset_union_left.trans (Set.subset_insert _ _))

theorem embT_subset_sumTokMaster {Y : Set Str} (hY : D₁.mem Y) :
    embBit true Y ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₁.sub_master hY)).trans (Set.subset_union_right.trans (Set.subset_insert _ _))

theorem sumTokMaster_inter_embF {X : Set Str} (hX : D₀.mem X) :
    sumTokMaster D₀ D₁ ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_sumTokMaster hX)

theorem sumTokMaster_inter_embT {Y : Set Str} (hY : D₁.mem Y) :
    sumTokMaster D₀ D₁ ∩ embBit true Y = embBit true Y :=
  Set.inter_eq_right.mpr (embT_subset_sumTokMaster hY)

theorem embF_ne_sumTokMaster {X : Set Str} : embBit false X ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

theorem embT_ne_sumTokMaster {Y : Set Str} : embBit true Y ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

/-- **Exercise 6.19 — the concrete sum system `𝒟₀ + 𝒟₁` over `{0,1}*`.** A neighbourhood is the
master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`, a left copy `0X` (`X ∈ 𝒟₀`), or a right copy `1Y` (`Y ∈ 𝒟₁`). The standing
assumption `∅ ∉ 𝒟ᵢ` (`h₀`, `h₁`) makes the two tagged copies disjoint, so the system is closed under
consistent intersection. -/
def sumTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, rfl⟩ | ⟨Z₁, hZ₁, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub), rfl⟩)

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_master : (sumTok D₀ D₁ h₀ h₁).mem (sumTokMaster D₀ D₁) := Or.inl rfl

theorem sumTok_mem_embF {X : Set Str} (hX : D₀.mem X) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, rfl⟩)

theorem sumTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) :
    (sumTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, rfl⟩)

theorem sumTok_mem_embF_inv {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem (embBit false W)) :
    D₀.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩ | ⟨Y, hY, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX
  · exact absurd heq.symm (embBit_ne (show (true : Bool) ≠ false by decide) (h₁ Y hY))

theorem sumTok_mem_embT_inv {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩ | ⟨Y, hY, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

theorem sumTok_mem_nonempty {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

/-- The concrete sum is again `∅`-free (an object of Scott's category). -/
theorem sumTok_nonempty : ∀ W, (sumTok D₀ D₁ h₀ h₁).mem W → W.Nonempty :=
  fun _ h => sumTok_mem_nonempty h

/-! ### Generic inversion lemmas for the abstract separated sum `sum D₀ D₁` -/

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : (sum D₀ D₁ h₀ h₁).mem W) :
    W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (h₀ X hX)
  · exact inj₁_nonempty (h₁ Y hY)

theorem sum_mem_inj₀_inv {X : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₀ X)) : D₀.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := h₁ Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

theorem sum_mem_inj₁_inv {Y : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₁ Y)) : D₁.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

/-! ### The forward half `toSum : |D₀ + D₁|ₜₒₖ → |D₀ + D₁|` -/

/-- The forward half of the isomorphism, a token-level analogue of `Example62.toBB`. -/
def toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : (sum D₀ D₁ h₀ h₁).Element where
  mem W := W = sumMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = inj₀ X ∧ x.mem (embBit false X))
    ∨ (∃ Y, D₁.mem Y ∧ W = inj₁ Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := x.inter_mem hzX hzX'; rw [embBit_inter] at hz; exact sumTok_mem_embF_inv (x.sub hz)
      · have hz := x.inter_mem hzX hzX'; rwa [embBit_inter] at hz
    · exfalso
      have hz := x.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumMaster_inter_inj₁ hY], hzY⟩)
    · exfalso
      have hz := x.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (x.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [inj₁_inter], ?_⟩)
      · have hz := x.inter_mem hzY hzY'; rw [embBit_inter] at hz; exact sumTok_mem_embT_inv (x.sub hz)
      · have hz := x.inter_mem hzY hzY'; rwa [embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact x.up_mem hzX (sumTok_mem_embF hX') (embBit_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact x.up_mem hzY (sumTok_mem_embT hY') (embBit_subset.mpr (inj₁_subset_inj₁.mp hsub))

@[simp] theorem toSum_mem_inj₀ {x : (sumTok D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (toSum x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := h₀ X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toSum_mem_inj₁ {x : (sumTok D₀ D₁ h₀ h₁).Element} {Y : Set Str} (hY : D₁.mem Y) :
    (toSum x).mem (inj₁ Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := h₀ X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rwa [inj₁_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-! ### The inverse half `fromSum : |D₀ + D₁| → |D₀ + D₁|ₜₒₖ` -/

/-- The inverse half of the isomorphism, a token-level analogue of `Example62.fromBB`. -/
def fromSum (s : (sum D₀ D₁ h₀ h₁).Element) : (sumTok D₀ D₁ h₀ h₁).Element where
  mem W := W = sumTokMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, D₁.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((sumTok D₀ D₁ h₀ h₁).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

@[simp] theorem fromSum_mem_embF {s : (sum D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (fromSum s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromSum_mem_embT {s : (sum D₀ D₁ h₀ h₁).Element} {Y : Set Str} (hY : D₁.mem Y) :
    (fromSum s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

/-! ### The two halves are mutually inverse, giving the isomorphism. -/

theorem fromSum_toSum (x : (sumTok D₀ D₁ h₀ h₁).Element) : fromSum (toSum x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toSum_mem_inj₀ hX).mp hs
    · exact (toSum_mem_inj₁ hY).mp hs
  · intro hW
    rcases x.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toSum_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toSum_mem_inj₁ hY).mpr hW⟩)

theorem toSum_fromSum (s : (sum D₀ D₁ h₀ h₁).Element) : toSum (fromSum s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromSum_mem_embF hX).mp hs
    · exact (fromSum_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromSum_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromSum_mem_embT hY).mpr hW⟩)

/-- **Exercise 6.19 — the concrete sum is correct up to isomorphism.** The order-isomorphism
`|D₀ + D₁|ₜₒₖ ≃o |D₀ + D₁|` between Scott's `{0,1}*`-presentation and the abstract separated sum. -/
def sumTokEquiv : (sumTok D₀ D₁ h₀ h₁).Element ≃o (sum D₀ D₁ h₀ h₁).Element where
  toFun := toSum
  invFun := fromSum
  left_inv := fromSum_toSum
  right_inv := toSum_fromSum
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases x.sub hX with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toSum_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toSum_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (sum).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ + 𝒟₁` is isomorphic, as a domain, to the abstract separated sum of
Exercise 3.18. -/
theorem sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁ := ⟨sumTokEquiv⟩

/-! ## The concrete product `D₀ × D₁` over `{0,1}*`

`D₀ × D₁ = {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀ and Y ∈ 𝒟₁}`. Every neighbourhood carries *both* coordinates and
the basepoint, in contrast to the sum (where a proper neighbourhood refines exactly one summand). -/

/-- A product neighbourhood `{Λ} ∪ 0X ∪ 1Y` over `{0,1}*`. -/
def prodTokNbhd (X Y : Set Str) : Set Str := insert [] (embBit false X ∪ embBit true Y)

@[simp] theorem mem_prodTokNbhd_nil {X Y : Set Str} : ([] : Str) ∈ prodTokNbhd X Y :=
  Set.mem_insert _ _

@[simp] theorem mem_prodTokNbhd_false {X Y : Set Str} {w' : Str} :
    (false :: w') ∈ prodTokNbhd X Y ↔ w' ∈ X := by
  simp only [prodTokNbhd, Set.mem_insert_iff, Set.mem_union, mem_embBit]
  constructor
  · rintro (h | ⟨u, hu, hX⟩ | ⟨u, hu, hY⟩)
    · exact absurd h (by simp)
    · rw [List.cons.injEq] at hu; rw [hu.2]; exact hX
    · rw [List.cons.injEq] at hu; exact absurd hu.1 (by decide)
  · intro h; exact Or.inr (Or.inl ⟨w', rfl, h⟩)

@[simp] theorem mem_prodTokNbhd_true {X Y : Set Str} {w' : Str} :
    (true :: w') ∈ prodTokNbhd X Y ↔ w' ∈ Y := by
  simp only [prodTokNbhd, Set.mem_insert_iff, Set.mem_union, mem_embBit]
  constructor
  · rintro (h | ⟨u, hu, hX⟩ | ⟨u, hu, hY⟩)
    · exact absurd h (by simp)
    · rw [List.cons.injEq] at hu; exact absurd hu.1 (by decide)
    · rw [List.cons.injEq] at hu; rw [hu.2]; exact hY
  · intro h; exact Or.inr (Or.inr ⟨w', rfl, h⟩)

/-- `prodTokNbhd D₀.master D₁.master` is exactly the sum master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
theorem prodTokNbhd_master_eq : prodTokNbhd D₀.master D₁.master = sumTokMaster D₀ D₁ := rfl

/-- Scott's (2) for the product: product neighbourhoods intersect componentwise. -/
theorem prodTokNbhd_inter (X X' Y Y' : Set Str) :
    prodTokNbhd X Y ∩ prodTokNbhd X' Y' = prodTokNbhd (X ∩ X') (Y ∩ Y') := by
  ext w
  cases w with
  | nil => simp [Set.mem_inter_iff]
  | cons b w' => cases b <;> simp [Set.mem_inter_iff]

/-- Scott's (1) for the product: inclusion of product neighbourhoods is componentwise. -/
theorem prodTokNbhd_subset_iff {X X' Y Y' : Set Str} :
    prodTokNbhd X Y ⊆ prodTokNbhd X' Y' ↔ X ⊆ X' ∧ Y ⊆ Y' := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · exact mem_prodTokNbhd_false.mp (h (mem_prodTokNbhd_false.mpr ha))
    · exact mem_prodTokNbhd_true.mp (h (mem_prodTokNbhd_true.mpr hb))
  · rintro ⟨hX, hY⟩ w hw
    cases w with
    | nil => exact mem_prodTokNbhd_nil
    | cons b w' =>
      cases b with
      | false => exact mem_prodTokNbhd_false.mpr (hX (mem_prodTokNbhd_false.mp hw))
      | true => exact mem_prodTokNbhd_true.mpr (hY (mem_prodTokNbhd_true.mp hw))

theorem prodTokNbhd_injective {X X' Y Y' : Set Str} (h : prodTokNbhd X Y = prodTokNbhd X' Y') :
    X = X' ∧ Y = Y' :=
  ⟨Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).1
      (prodTokNbhd_subset_iff.mp h.symm.subset).1,
   Set.Subset.antisymm (prodTokNbhd_subset_iff.mp h.subset).2
      (prodTokNbhd_subset_iff.mp h.symm.subset).2⟩

/-- **Exercise 6.19 — the concrete product system `𝒟₀ × 𝒟₁` over `{0,1}*`.** Neighbourhoods are
`{Λ} ∪ 0X ∪ 1Y` with `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. Closed under consistent intersection by Scott's (1)/(2)
together with the factors' closure. -/
def prodTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ ⟨Z₀, Z₁, hZ₀, hZ₁, rfl⟩ hsub
    rw [prodTokNbhd_inter] at hsub ⊢
    obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀, D₁.inter_mem hY hY' hZ₁ hsub₁, rfl⟩
  sub_master := by
    rintro W ⟨X, Y, hX, hY, rfl⟩
    exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩

@[simp] theorem prodTok_mem_iff {W : Set Str} :
    (prodTok D₀ D₁).mem W ↔ ∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ W = prodTokNbhd X Y := Iff.rfl

theorem prodTok_mem_prodTokNbhd {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y) :
    (prodTok D₀ D₁).mem (prodTokNbhd X Y) := ⟨X, Y, hX, hY, rfl⟩

@[simp] theorem prodTok_master : (prodTok D₀ D₁).master = prodTokNbhd D₀.master D₁.master := rfl

/-- The concrete product is again `∅`-free (every neighbourhood contains `Λ`). -/
theorem prodTok_nonempty : ∀ W, (prodTok D₀ D₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, _, _, rfl⟩; exact ⟨[], mem_prodTokNbhd_nil⟩

/-! ### Components of a product element and the splitting lemma -/

/-- Scott's `z₀`: the first component of a `prodTok`-element. -/
def fstTok (z : (prodTok D₀ D₁).Element) : D₀.Element where
  mem X := D₀.mem X ∧ z.mem (prodTokNbhd X D₁.master)
  sub h := h.1
  master_mem := ⟨D₀.master_mem, z.master_mem⟩
  inter_mem := by
    rintro X X' ⟨_, hzX⟩ ⟨_, hzX'⟩
    have hz := z.inter_mem hzX hzX'
    rw [prodTokNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, hA, _, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hA, hz⟩
  up_mem := by
    rintro X X' ⟨_, hzX⟩ hX' hXX'
    exact ⟨hX', z.up_mem hzX (prodTok_mem_prodTokNbhd hX' D₁.master_mem)
      (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩)⟩

/-- Scott's `z₁`: the second component of a `prodTok`-element. -/
def sndTok (z : (prodTok D₀ D₁).Element) : D₁.Element where
  mem Y := D₁.mem Y ∧ z.mem (prodTokNbhd D₀.master Y)
  sub h := h.1
  master_mem := ⟨D₁.master_mem, z.master_mem⟩
  inter_mem := by
    rintro Y Y' ⟨_, hzY⟩ ⟨_, hzY'⟩
    have hz := z.inter_mem hzY hzY'
    rw [prodTokNbhd_inter, Set.inter_self] at hz
    obtain ⟨A, B, _, hB, heq⟩ := z.sub hz
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hB, hz⟩
  up_mem := by
    rintro Y Y' ⟨_, hzY⟩ hY' hYY'
    exact ⟨hY', z.up_mem hzY (prodTok_mem_prodTokNbhd D₀.master_mem hY')
      (prodTokNbhd_subset_iff.mpr ⟨subset_rfl, hYY'⟩)⟩

@[simp] theorem mem_fstTok {z : (prodTok D₀ D₁).Element} {X : Set Str} :
    (fstTok z).mem X ↔ D₀.mem X ∧ z.mem (prodTokNbhd X D₁.master) := Iff.rfl

@[simp] theorem mem_sndTok {z : (prodTok D₀ D₁).Element} {Y : Set Str} :
    (sndTok z).mem Y ↔ D₁.mem Y ∧ z.mem (prodTokNbhd D₀.master Y) := Iff.rfl

/-- Scott's (3) for the product: membership of `X ∪ Y` splits into its two slices. -/
theorem prodTok_mem_split {z : (prodTok D₀ D₁).Element} {X Y : Set Str}
    (hX : D₀.mem X) (hY : D₁.mem Y) :
    z.mem (prodTokNbhd X Y) ↔
      z.mem (prodTokNbhd X D₁.master) ∧ z.mem (prodTokNbhd D₀.master Y) := by
  constructor
  · intro h
    refine ⟨z.up_mem h (prodTok_mem_prodTokNbhd hX D₁.master_mem) ?_,
            z.up_mem h (prodTok_mem_prodTokNbhd D₀.master_mem hY) ?_⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨subset_rfl, D₁.sub_master hY⟩
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, subset_rfl⟩
  · rintro ⟨h1, h2⟩
    have := z.inter_mem h1 h2
    rwa [prodTokNbhd_inter, Set.inter_eq_left.mpr (D₀.sub_master hX),
      Set.inter_eq_right.mpr (D₁.sub_master hY)] at this

/-! ### The element pairing and the isomorphism `|D₀ × D₁|ₜₒₖ ≃o |D₀| × |D₁|`. -/

/-- The element pairing `⟨x, y⟩` for the concrete product. -/
def pairTok (x : D₀.Element) (y : D₁.Element) : (prodTok D₀ D₁).Element where
  mem W := ∃ X Y, x.mem X ∧ y.mem Y ∧ W = prodTokNbhd X Y
  sub := by rintro W ⟨X, Y, hX, hY, rfl⟩; exact prodTok_mem_prodTokNbhd (x.sub hX) (y.sub hY)
  master_mem := ⟨D₀.master, D₁.master, x.master_mem, y.master_mem, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩
    exact ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', y.inter_mem hY hY', prodTokNbhd_inter X X' Y Y'⟩
  up_mem := by
    rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hsub
    obtain ⟨hXX', hYY'⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X', Y', x.up_mem hX hX' hXX', y.up_mem hY hY' hYY', rfl⟩

theorem mem_pairTok_prodTokNbhd {x : D₀.Element} {y : D₁.Element} {X Y : Set Str} :
    (pairTok x y).mem (prodTokNbhd X Y) ↔ x.mem X ∧ y.mem Y := by
  constructor
  · rintro ⟨X', Y', hX', hY', heq⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨hX', hY'⟩
  · rintro ⟨hx, hy⟩; exact ⟨X, Y, hx, hy, rfl⟩

theorem pairTok_fstTok_sndTok (z : (prodTok D₀ D₁).Element) : pairTok (fstTok z) (sndTok z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨X, Y, ⟨hX, hzX⟩, ⟨hY, hzY⟩, rfl⟩
    exact (prodTok_mem_split hX hY).mpr ⟨hzX, hzY⟩
  · intro hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
    obtain ⟨h1, h2⟩ := (prodTok_mem_split hX hY).mp hW
    exact ⟨X, Y, ⟨hX, h1⟩, ⟨hY, h2⟩, rfl⟩

@[simp] theorem fstTok_pairTok (x : D₀.Element) (y : D₁.Element) : fstTok (pairTok x y) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).1
  · intro hX; exact ⟨x.sub hX, mem_pairTok_prodTokNbhd.mpr ⟨hX, y.master_mem⟩⟩

@[simp] theorem sndTok_pairTok (x : D₀.Element) (y : D₁.Element) : sndTok (pairTok x y) = y := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨hY, hmem⟩; exact (mem_pairTok_prodTokNbhd.mp hmem).2
  · intro hY; exact ⟨y.sub hY, mem_pairTok_prodTokNbhd.mpr ⟨x.master_mem, hY⟩⟩

/-- The order-isomorphism `|D₀ × D₁|ₜₒₖ ≃o |D₀| × |D₁|` (Scott's Proposition 3.2, token-level). -/
def prodTokEquiv : (prodTok D₀ D₁).Element ≃o D₀.Element × D₁.Element where
  toFun z := (fstTok z, sndTok z)
  invFun p := pairTok p.1 p.2
  left_inv z := pairTok_fstTok_sndTok z
  right_inv p := by simp
  map_rel_iff' := by
    intro z z'
    constructor
    · rintro ⟨h1, h2⟩ W hW
      obtain ⟨X, Y, hX, hY, rfl⟩ := z.sub hW
      obtain ⟨ha, hb⟩ := (prodTok_mem_split hX hY).mp hW
      have hX' : (fstTok z').mem X := h1 X ⟨hX, ha⟩
      have hY' : (sndTok z').mem Y := h2 Y ⟨hY, hb⟩
      exact (prodTok_mem_split hX hY).mpr ⟨hX'.2, hY'.2⟩
    · intro h
      exact ⟨fun X ⟨hX, hzX⟩ => ⟨hX, h _ hzX⟩, fun Y ⟨hY, hzY⟩ => ⟨hY, h _ hzY⟩⟩

/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (product).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ × 𝒟₁` is isomorphic, as a domain, to the abstract product of Definition 3.1.
Both compute the same domain `|D₀| × |D₁|` (via `prodTokEquiv` and Scott's `prodEquiv`). -/
theorem prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁ :=
  ⟨prodTokEquiv.trans (prodEquiv D₀ D₁).symm⟩

end Exercise619

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/FunctionSpace.lean -/

/-!
# Lecture III (§3) — the function space `(𝒟₀ → 𝒟₁)`: Definitions 3.8, Propositions 3.9,
Theorems 3.10, 3.11, 3.12, 3.13

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture III.
The **function space** `(𝒟₀ → 𝒟₁)` is the neighbourhood system whose *tokens* are the approximable
maps `𝒟₀ → 𝒟₁` (Definition 2.1), and whose neighbourhoods are the non-empty finite intersections of
the *step sets*

`[X, Y] = {f ∣ X f Y}`   (`step X Y`),

for `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. We model a finite intersection by a `List` of `(X, Y)` pairs, with
`stepFun L = {f ∣ ∀ (X, Y) ∈ L, X f Y}`; the empty list gives the master `Δ = |𝒟₀ → 𝒟₁|`
(`Set.univ`). The system is **positive**: a neighbourhood is required non-empty, which is exactly
what makes a filter's induced relation *intersective* (Theorem 3.10).

This file formalizes:

* **Definition 3.8** — `step`, `stepFun`, the system `funSpace V₀ V₁`, with the basic algebra
  `step_inter_right` (`[X,Y] ∩ [X,Y'] = [X,Y∩Y']`), `step_subset` (antitone/monotone),
  `step_master_eq` (`[Δ₀,Δ₁] = univ`), and membership `step_mem`.
* **Theorem 3.10** (the crux) — `funSpaceEquiv : |𝒟₀ → 𝒟₁| ≃o ApproximableMap V₀ V₁`: every filter
  is fixed by a unique approximable map (`toApproxMap`/`toFilter`), inclusion-preservingly.
* **Proposition 3.9** — `leastMap` (the least map `f₀` of a consistent neighbourhood, condition
  (ii) `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`), `leastMap_mem_stepFun` and `leastMap_le` (it is the minimal
  element of `⋂[Xᵢ,Yᵢ]`), and `stepFun_subset_step_iff` (the remark after 3.9). The consistency
  hypothesis `hcons` is Scott's condition (i) in operational form.
* **Theorem 3.13** — `le_iff_toElementMap_le` (i); `mapsBounded_iff_pointwiseBounded` (ii);
  `sSupMaps` with `toElementMap_sSupMaps` (iii).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The order on approximable maps (rel-inclusion). -/

/-- Approximable maps are ordered by inclusion of their relations (Scott's approximation order on
`|𝒟₀ → 𝒟₁|`). Antisymmetry is `ApproximableMap.ext`. -/
instance : PartialOrder (ApproximableMap V₀ V₁) where
  le f g := ∀ X Y, f.rel X Y → g.rel X Y
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 X Y h := h2 X Y (h1 X Y h)
  le_antisymm f g h1 h2 := ApproximableMap.ext fun X Y => ⟨h1 X Y, h2 X Y⟩

theorem ApproximableMap.le_iff {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ X Y, f.rel X Y → g.rel X Y := Iff.rfl

/-! ### Definition 3.8 — step sets and the function space. -/

/-- Scott's step set `[X, Y] = {f ∣ X f Y}`. -/
def step (X : Set α) (Y : Set β) : Set (ApproximableMap V₀ V₁) := {f | f.rel X Y}

@[simp] theorem mem_step {X : Set α} {Y : Set β} {f : ApproximableMap V₀ V₁} :
    f ∈ step X Y ↔ f.rel X Y := Iff.rfl

/-- A finite intersection of step sets, indexed by a list of `(X, Y)` pairs. -/
def stepFun (L : List (Set α × Set β)) : Set (ApproximableMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.rel p.1 p.2}

@[simp] theorem mem_stepFun {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} :
    f ∈ stepFun L ↔ ∀ p ∈ L, f.rel p.1 p.2 := Iff.rfl

@[simp] theorem stepFun_nil : (stepFun [] : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simp

theorem stepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (stepFun (p :: L) : Set (ApproximableMap V₀ V₁)) = step p.1 p.2 ∩ stepFun L := by
  ext f
  simp only [mem_stepFun, List.mem_cons, Set.mem_inter_iff, mem_step]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

theorem stepFun_append (L L' : List (Set α × Set β)) :
    (stepFun (L ++ L') : Set (ApproximableMap V₀ V₁)) = stepFun L ∩ stepFun L' := by
  ext f
  simp only [mem_stepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

theorem stepFun_singleton (X : Set α) (Y : Set β) :
    (stepFun [(X, Y)] : Set (ApproximableMap V₀ V₁)) = step X Y := by
  rw [stepFun_cons, stepFun_nil, Set.inter_univ]

/-- `[Δ₀, Δ₁] = |𝒟₀ → 𝒟₁|`: every map relates the masters. -/
@[simp] theorem step_master_eq : (step V₀.master V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.master_rel

/-- `[X, Y] ∩ [X, Y'] = [X, Y ∩ Y']` (intersectivity in the output). -/
theorem step_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (step X Y ∩ step X Y' : Set (ApproximableMap V₀ V₁)) = step X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_step]
  constructor
  · rintro ⟨h, h'⟩; exact f.inter_right h h'
  · intro h
    exact ⟨f.mono h subset_rfl Set.inter_subset_left (f.rel_dom h) hY,
           f.mono h subset_rfl Set.inter_subset_right (f.rel_dom h) hY'⟩

/-- `X' ⊆ X` and `Y ⊆ Y'` imply `[X, Y] ⊆ [X', Y']`. -/
theorem step_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (step X Y : Set (ApproximableMap V₀ V₁)) ⊆ step X' Y' := by
  intro f hf
  exact f.mono hf hX'X hYY' hX' hY'

/-- **Definition 3.8 (Scott 1981, PRG-19).** The *function space* `(𝒟₀ → 𝒟₁)`: tokens are
approximable maps, neighbourhoods are non-empty finite intersections of step sets. -/
def funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (ApproximableMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, stepFun_nil.symm⟩, ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem funSpace_master : (funSpace V₀ V₁).master = Set.univ := rfl

theorem funSpace_mem_iff {W : Set (ApproximableMap V₀ V₁)} :
    (funSpace V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
        ∧ W.Nonempty := Iff.rfl

/-- A step neighbourhood `[X, Y]` is a neighbourhood of the function space (non-empty: it contains
the constant map `constMap V₀ (↑Y)`). -/
theorem step_mem {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (funSpace V₀ V₁).mem (step X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (stepFun_singleton X Y).symm⟩,
    ⟨constMap V₀ (V₁.principal hY), ?_⟩⟩
  · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hX, hY⟩
  · show (constMap V₀ (V₁.principal hY)).rel X Y
    exact ⟨hX, hY, subset_rfl⟩

/-- The "generation" lemma: a filter contains the intersection `stepFun L` iff it contains each
step `[Xᵢ, Yᵢ]`. (The step sets `[X, Y] ∈ φ` generate the filter `φ`.) -/
theorem mem_stepFun_iff (φ : (funSpace V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (stepFun L) ↔ ∀ p ∈ L, φ.mem (step p.1 p.2) := by
  induction L with
  | nil => simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hstep : φ.mem (step p.1 p.2) :=
        φ.up_mem hmem (step_mem hp.1 hp.2) Set.inter_subset_left
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (stepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

/-! ### Theorem 3.10 — the function space is complete. -/

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The relation `X φ̂ Y ↔ [X, Y] ∈ φ` of a filter `φ`.
Intersectivity is the payoff of positivity (`[X,Y]∩[X,Y'] = [X,Y∩Y']` is non-empty, so `Y∩Y' ∈ 𝒟₁`). -/
def toApproxMap (φ : (funSpace V₀ V₁).Element) : ApproximableMap V₀ V₁ where
  rel X Y := φ.mem (step X Y)
  rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_dom hf
  rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_cod hf
  master_rel := by show φ.mem (step V₀.master V₁.master); rw [step_master_eq]; exact φ.master_mem
  inter_right := by
    intro X Y Y' h h'
    obtain ⟨f, hf⟩ := (φ.sub h).2
    obtain ⟨f', hf'⟩ := (φ.sub h').2
    have hY : V₁.mem Y := f.rel_cod hf
    have hY' : V₁.mem Y' := f'.rel_cod hf'
    show φ.mem (step X (Y ∩ Y'))
    rw [← step_inter_right hY hY']
    exact φ.inter_mem h h'
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY'
    show φ.mem (step X' Y')
    exact φ.up_mem h (step_mem hX' hY') (step_subset hX' hY' hX'X hYY')

@[simp] theorem toApproxMap_rel {φ : (funSpace V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toApproxMap φ).rel X Y ↔ φ.mem (step X Y) := Iff.rfl

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The filter `f̂ = {F ∣ f ∈ F}` of an approximable map. -/
def toFilter (f : ApproximableMap V₀ V₁) : (funSpace V₀ V₁).Element where
  mem W := (funSpace V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(funSpace V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
    refine ⟨⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, ⟨f, ?_⟩⟩, ?_⟩
    · intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hL p h
      · exact hL' p h
    · exact Set.mem_inter hfW hfW'
    · exact Set.mem_inter hfW hfW'
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

@[simp] theorem mem_toFilter {f : ApproximableMap V₀ V₁} {W : Set (ApproximableMap V₀ V₁)} :
    (toFilter f).mem W ↔ (funSpace V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The function space is *complete*: every filter is fixed
by a unique approximable mapping, inclusion-preservingly. -/
def funSpaceEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁ where
  toFun := toApproxMap
  invFun := toFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_stepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_stepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨step_mem (f.rel_dom hf) (f.rel_cod hf), hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_stepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_stepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

@[simp] theorem funSpaceEquiv_apply (φ : (funSpace V₀ V₁).Element) :
    funSpaceEquiv V₀ V₁ φ = toApproxMap φ := rfl

@[simp] theorem funSpaceEquiv_symm_apply (f : ApproximableMap V₀ V₁) :
    (funSpaceEquiv V₀ V₁).symm f = toFilter f := rfl

/-- Intersection of two function-space neighbourhoods, when non-empty, is again one. -/
theorem funSpace_mem_inter {W W' : Set (ApproximableMap V₀ V₁)}
    (hW : (funSpace V₀ V₁).mem W) (hW' : (funSpace V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (funSpace V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

/-- Step neighbourhoods are *up-closed* under the map order: if `f ∈ stepFun L` and `f ⊑ f'`, then
`f' ∈ stepFun L`. -/
theorem stepFun_up_closed {L : List (Set α × Set β)} {f f' : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) (hff' : f ≤ f') : f' ∈ stepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)

/-- A function-space neighbourhood is up-closed under the map order. -/
theorem funSpace_mem_up_closed {W : Set (ApproximableMap V₀ V₁)} (hW : (funSpace V₀ V₁).mem W)
    {f f' : ApproximableMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact stepFun_up_closed hf hff'

/-! ### Proposition 3.9 — the least map of a consistent neighbourhood. -/

/-- Scott's intersection `⋂ {Yᵢ ∣ X ⊆ Xᵢ}` of the outputs whose input is coarser than `X`, taken
inside the master neighbourhood `Δ₁` (so the empty intersection is `Δ₁`, per the convention 1.1a).
Indexed by the list `L` of `(Xᵢ, Yᵢ)` pairs. -/
def interYs (m : Set β) : List (Set α × Set β) → Set α → Set β
  | [], _ => m
  | p :: L, X => {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X

@[simp] theorem interYs_nil (m : Set β) (X : Set α) : interYs m [] X = m := rfl

theorem interYs_cons (m : Set β) (p : Set α × Set β) (L : List (Set α × Set β)) (X : Set α) :
    interYs m (p :: L) X = {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X := rfl

/-- Membership in `interYs`: `z ∈ ⋂{Yᵢ ∣ X ⊆ Xᵢ}` iff `z ∈ Δ₁` and `z ∈ Yᵢ` for every `i` with
`X ⊆ Xᵢ`. -/
theorem mem_interYs {m : Set β} {L : List (Set α × Set β)} {X : Set α} {z : β} :
    z ∈ interYs m L X ↔ z ∈ m ∧ ∀ p ∈ L, X ⊆ p.1 → z ∈ p.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [interYs_cons]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hp, hm, hL⟩
      refine ⟨hm, ?_⟩
      rintro q (rfl | hq) hXq
      · exact hp hXq
      · exact hL q hq hXq
    · rintro ⟨hm, hall⟩
      exact ⟨fun hXp => hall p (Or.inl rfl) hXp, hm,
        fun q hq hXq => hall q (Or.inr hq) hXq⟩

/-- `interYs` is contained in the master neighbourhood. -/
theorem interYs_subset_master {m : Set β} {L : List (Set α × Set β)} {X : Set α} :
    interYs m L X ⊆ m := fun _ hz => (mem_interYs.mp hz).1

/-- `interYs` is antitone in the input `X`: a sharper input intersects over more outputs. -/
theorem interYs_antitone {m : Set β} {L : List (Set α × Set β)} {X X' : Set α} (h : X' ⊆ X) :
    interYs m L X' ⊆ interYs m L X := by
  intro z hz
  rw [mem_interYs] at hz ⊢
  exact ⟨hz.1, fun p hp hXp => hz.2 p hp (h.trans hXp)⟩

/-- `interYs` contains `Yⱼ` whenever `Xⱼ ⊆ X`-indexed: in particular `interYs m L Xⱼ ⊆ Yⱼ` for
`(Xⱼ, Yⱼ) ∈ L`. -/
theorem interYs_subset_of_mem {m : Set β} {L : List (Set α × Set β)} {p : Set α × Set β}
    (hp : p ∈ L) : interYs m L p.1 ⊆ p.2 :=
  fun _ hz => (mem_interYs.mp hz).2 p hp subset_rfl

/-- **Proposition 3.9(ii) (Scott 1981, PRG-19).** The *least* approximable mapping `f₀` belonging to
the neighbourhood `⋂ [Xᵢ, Yᵢ]`, defined by `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. Well-definedness uses
Scott's condition (i) in the operational form `hcons`: for every neighbourhood `X`, the outputs
`{Yᵢ ∣ X ⊆ Xᵢ}` (consistent in `𝒟₁`, witnessed by `X` being a common lower bound of their inputs)
have their intersection again a neighbourhood. -/
def leastMap (L : List (Set α × Set β)) (_hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, V₁.master_mem, interYs_subset_master⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, V₁.inter_mem hY hY' (hcons hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (interYs_antitone hX'X).trans (hsub.trans hYY')⟩

@[simp] theorem leastMap_rel {L : List (Set α × Set β)}
    {hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2}
    {hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)} {X : Set α} {Y : Set β} :
    (leastMap L hL hcons).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y := Iff.rfl

/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

/-- The relation `X f Y` holds for `f` in the neighbourhood `stepFun L` at the master output, and
more importantly `f` relates `X` to the whole intersection `interYs Δ₁ L X` (finite intersectivity
over the relevant outputs). The case split deciding `X ⊆ Xᵢ` is a documented classical step. -/
theorem rel_interYs {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} (hf : f ∈ stepFun L)
    {X : Set α} (hX : V₀.mem X) : f.rel X (interYs V₁.master L X) := by
  induction L with
  | nil =>
    rw [interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem
  | cons p L ih =>
    have hftail : f ∈ stepFun L := fun q hq => hf q (List.mem_cons.mpr (Or.inr hq))
    have htail := ih hftail
    by_cases hXp : X ⊆ p.1
    · have hp : f.rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel X p.2 := f.mono hp hXp subset_rfl hX (f.rel_cod hp)
      have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]; exact htail

/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

/-- **Remark after Proposition 3.9 (Scott 1981, PRG-19).** When the neighbourhood is consistent,
`⋂ [Xᵢ, Yᵢ] ⊆ [X, Y]` iff `⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. This is the form used to check that `curry` is
monotone (and hence approximable). -/
theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

/-! ### Theorem 3.13(i) — the pointwise order. -/

/-- **Theorem 3.13(i) (Scott 1981, PRG-19).** `f ⊑ g ↔ ∀ x, f(x) ⊑ g(x)`. -/
theorem le_iff_toElementMap_le {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ x, f.toElementMap x ≤ g.toElementMap x := by
  constructor
  · intro h x Y ⟨X, hXx, hrel⟩
    exact ⟨X, hXx, h X Y hrel⟩
  · intro h X Y hrel
    have hX : V₀.mem X := f.rel_dom hrel
    rw [f.rel_iff_mem_principal hX] at hrel
    rw [g.rel_iff_mem_principal hX]
    exact h (V₀.principal hX) Y hrel

/-! ### Theorem 3.13(ii)(iii) — pointwise boundedness and sups. -/

/-- A set `F` of approximable maps is *bounded* when it has an upper bound in the map order. -/
def MapsBounded (F : Set (ApproximableMap V₀ V₁)) : Prop := ∃ h, ∀ f ∈ F, f ≤ h

/-- `F` is *pointwise bounded* when `{f(x) ∣ f ∈ F}` is bounded in `|𝒟₁|` for every `x`. -/
def PointwiseBounded (F : Set (ApproximableMap V₀ V₁)) : Prop :=
  ∀ x : V₀.Element, V₁.Bounded (Set.image (fun f => f.toElementMap x) F)

theorem toFilter_le_iff {f g : ApproximableMap V₀ V₁} : toFilter f ≤ toFilter g ↔ f ≤ g :=
  (funSpaceEquiv V₀ V₁).symm.map_rel_iff'

theorem mapsBounded_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    V₁.Bounded (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) :=
  hF (V₀.principal hX)

/-- The sup of `{f(↑X) ∣ f ∈ F}` on principal inputs, used to build `sSupMaps`. -/
def supOnPrincipal (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X : Set α) (hX : V₀.mem X) : V₁.Element :=
  V₁.sSup (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) (mapsBounded_principal hF hX)

theorem supOnPrincipal_mono (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    supOnPrincipal F hF X hX ≤ supOnPrincipal F hF X' hX' :=
  V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
    obtain ⟨f, hf, rfl⟩ := hs
    exact (toElementMap_mono f ((V₀.principal_le_iff hX hX').mpr hX'X)).trans
      (V₁.le_sSup _ (mapsBounded_principal hF hX') ⟨f, hf, rfl⟩)

theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** The least upper bound of a pointwise-bounded set
`F`, defined on principal inputs by `supOnPrincipal` and extended via Exercise 2.8 (`ofMono`). -/
def sSupMaps (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) : ApproximableMap V₀ V₁ :=
  ofMono (fun X hX => supOnPrincipal F hF X hX) (supOnPrincipal_mono F hF)

theorem toElementMap_sSupMaps_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    (sSupMaps F hF).toElementMap (V₀.principal hX) = supOnPrincipal F hF X hX :=
  toElementMap_ofMono_principal _ (supOnPrincipal_mono F hF) X hX

/-- **Theorem 3.13(ii) (Scott 1981, PRG-19).** `F` is bounded in `|𝒟₀ → 𝒟₁|` iff `{f(x) ∣ f ∈ F}` is
bounded in `|𝒟₁|` for each `x ∈ |𝒟₀|`. The forward direction is `le_iff_toElementMap_le` (3.13(i))
applied pointwise; the backward direction builds the bound `sSupMaps F`. -/
theorem mapsBounded_iff_pointwiseBounded {F : Set (ApproximableMap V₀ V₁)} :
    MapsBounded F ↔ PointwiseBounded F := by
  constructor
  · intro ⟨h, hh⟩ x
    refine ⟨h.toElementMap x, fun z hz => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hz
    exact (le_iff_toElementMap_le.mp (hh f hf)) x
  · intro hpb
    refine ⟨sSupMaps F hpb, fun f hf X Y hrel => ?_⟩
    have hX : V₀.mem X := f.rel_dom hrel
    have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
    exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hpb hX) ⟨f, hf, rfl⟩) Y hmem⟩

theorem le_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ F) : f ≤ sSupMaps F hF := by
  intro X Y hrel
  have hX : V₀.mem X := f.rel_dom hrel
  have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
  exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hF hX) ⟨f, hf, rfl⟩) Y hmem⟩

theorem sSupMaps_le {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {h : ApproximableMap V₀ V₁} (hh : ∀ f ∈ F, f ≤ h) : sSupMaps F hF ≤ h := by
  intro X Y hrel
  obtain ⟨hX, hYmem⟩ := hrel
  have hle : supOnPrincipal F hF X hX ≤ h.toElementMap (V₀.principal hX) :=
    V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
      obtain ⟨f, hf, rfl⟩ := hs
      exact (le_iff_toElementMap_le.mp (hh f hf)) (V₀.principal hX)
  exact (h.rel_iff_mem_principal hX).mpr (hle Y hYmem)

theorem toElementMap_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    (x : V₀.Element) :
    (sSupMaps F hF).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) := by
  apply le_antisymm
  · -- `(⊔F)(x) ⊑ ⊔{f(x)}`: read `(⊔F)(x)` off some principal `↑X` (Ex 2.9), where the
    -- principal value `(⊔F)(↑X) = ⊔{f(↑X)}` is bounded above by `⊔{f(x)}` (monotonicity, `↑X ⊑ x`).
    intro Y hY
    rw [toElementMap_mem_iff_principal (sSupMaps F hF) x] at hY
    obtain ⟨X, hxX, hY'⟩ := hY
    have hX : V₀.mem X := x.sub hxX
    rw [toElementMap_sSupMaps_principal hF] at hY'
    have hprinc : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    have hsub : supOnPrincipal F hF X hX ≤ V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) :=
      V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
        obtain ⟨f, hf, rfl⟩ := hs
        exact (toElementMap_mono f hprinc).trans (V₁.le_sSup _ (hF x) ⟨f, hf, rfl⟩)
    exact hsub Y hY'
  · -- `⊔{f(x)} ⊑ (⊔F)(x)`: `(⊔F)(x)` is an upper bound of every `f(x)` since `f ⊑ ⊔F` (3.13(i)).
    refine V₁.sSup_le _ (hF x) fun s hs => ?_
    obtain ⟨f, hf, rfl⟩ := hs
    exact le_iff_toElementMap_le.mp (le_sSupMaps hF hf) x

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** When `F` is bounded, `(⊔F)(x) = ⊔{f(x) ∣ f ∈ F}`
(stated with the boundedness hypothesis in Scott's `MapsBounded` form). -/
theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F) (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

/-! ### Theorem 3.11 — evaluation. -/

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.11 (Scott 1981, PRG-19).** The two-variable evaluation map
`eval : (𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`, `F, X eval Y ↔ X f Y for all f ∈ F`. -/
def eval (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap₂ (funSpace V₁ V₂) V₁ V₂ where
  rel F X Y := (funSpace V₁ V₂).mem F ∧ V₁.mem X ∧ V₂.mem Y ∧ ∀ f ∈ F, f.rel X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨(funSpace V₁ V₂).master_mem, V₁.master_mem, V₂.master_mem,
    fun f _ => f.master_rel⟩
  inter_right := by
    rintro F X Y Y' ⟨hF, hX, hY, hrel⟩ ⟨_, _, hY', hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hF).2
    refine ⟨hF, hX, ?_, fun g hg => g.inter_right (hrel g hg) (hrel' g hg)⟩
    exact f.rel_cod (f.inter_right (hrel f hf) (hrel' f hf))
  mono := by
    rintro F F' X X' Y Y' ⟨hF, hX, hY, hrel⟩ hF'F hX'X hYY' hF' hX' hY'
    exact ⟨hF', hX', hY', fun f hf => f.mono (hrel f (hF'F hf)) hX'X hYY' hX' hY'⟩

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter `φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    show φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

/-- **Theorem 3.11 (Scott 1981, PRG-19).** Evaluation as a single approximable map out of the
product `(𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`. -/
def evalMap (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) V₁) V₂ := ofMap₂ (eval V₁ V₂)

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(⟨f, x⟩) = f(x)`. -/
theorem evalMap_apply (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalMap, ← toElementMap₂_toMap₂, toMap₂_ofMap₂, toElementMap₂_eval]

/-! ### Theorem 3.12 — currying. -/

/-- The `X`-section of a two-variable map `g : 𝒟₀ × 𝒟₁ → 𝒟₂`: the map `𝒟₁ → 𝒟₂` with
`Y (gSection g X) Z ↔ X ∪ Y g Z`. -/
def gSection (g : ApproximableMap (prod V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ where
  rel Y Z := g.rel (prodNbhd X Y) Z
  rel_dom h := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  rel_cod h := g.rel_cod h
  master_rel := g.rel_master (prod_mem_prodNbhd hX V₁.master_mem)
  inter_right h h' := g.inter_right h h'
  mono := by
    intro Y Y' Z Z' h hY'Y hZZ' hY' hZ'
    exact g.mono h (prodNbhd_subset_iff.mpr ⟨subset_rfl, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX hY') hZ'

@[simp] theorem gSection_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} : (gSection g hX).rel Y Z ↔ g.rel (prodNbhd X Y) Z := Iff.rfl

theorem gSection_le {g : ApproximableMap (prod V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) : gSection g hX ≤ gSection g hX' := by
  intro Y Z h
  have hY := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  exact g.mono h (prodNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩) subset_rfl
    (prod_mem_prodNbhd hX' hY) (g.rel_cod h)

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry(g) : 𝒟₀ → (𝒟₁ → 𝒟₂)`, where
`X curry(g) W ↔ (the X-section of g) ∈ W` (for `W = [Y, Z]` this is `X ∪ Y g Z`). -/
def curry (g : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap V₀ (funSpace V₁ V₂) where
  rel X W := ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hW, _⟩ => hW
  master_rel := ⟨V₀.master_mem, (funSpace V₁ V₂).master_mem, Set.mem_univ _⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hmem⟩ ⟨_, hW', hmem'⟩
    exact ⟨hX, funSpace_mem_inter hW hW' ⟨gSection g hX, hmem, hmem'⟩,
      Set.mem_inter hmem hmem'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hmem⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', funSpace_mem_up_closed hW' (hWW' hmem) (gSection_le hX hX' hX'X)⟩

@[simp] theorem curry_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α}
    {W : Set (ApproximableMap V₁ V₂)} :
    (curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W := Iff.rfl

/-- **Theorem 3.12(i) (Scott 1981, PRG-19).** `curry(g)(x)(y) = g(x, y)`. -/
theorem toElementMap_curry_apply (g : ApproximableMap (prod V₀ V₁) V₂)
    (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hyY, X, hxX, hX, _, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
    exact ⟨Y, hyY, X, hxX, x.sub hxX, step_mem (y.sub hyY) (g.rel_cod hrel), hrel⟩

/-- The relational generation lemma for maps `h : 𝒟₀ → (𝒟₁ → 𝒟₂)`: `X h (⋂ᵢ [Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_stepFun_iff (h : ApproximableMap V₀ (funSpace V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (stepFun L) ↔ ∀ p ∈ L, h.rel X (step p.1 p.2) := by
  induction L with
  | nil =>
    simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (funSpace V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (h.rel_cod hmem).2
      have hstep : h.rel X (step p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (step_mem hp.1 hp.2)
      have htail : h.rel X (stepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

theorem prod_mem_inl {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₀.mem (Sum.inl ⁻¹' W) := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW; rwa [inl_preimage_prodNbhd]

theorem prod_mem_inr {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₁.mem (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, hY, rfl⟩ := hW; rwa [inr_preimage_prodNbhd]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** Uncurrying `h : 𝒟₀ → (𝒟₁ → 𝒟₂)` to `𝒟₀ × 𝒟₁ → 𝒟₂`:
`X ∪ Y (uncurry h) Z ↔ X h [Y, Z]`. -/
def uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z)
  rel_dom h' := h'.1
  rel_cod := by
    rintro W Z ⟨_, hrel⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    exact f.rel_cod hf
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    rw [show (prod V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
      inl_preimage_prodNbhd, inr_preimage_prodNbhd, step_master_eq]
    exact h.master_rel
  inter_right := by
    rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    obtain ⟨f', hf'⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel')).2
    refine ⟨hW, ?_⟩
    rw [← step_inter_right (f.rel_cod hf) (f'.rel_cod hf')]
    exact h.inter_right hrel hrel'
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl ⊢
    rw [inr_preimage_prodNbhd] at hinr ⊢
    refine ⟨prod_mem_prodNbhd hA hB, ?_⟩
    exact h.mono hrel hinl (step_subset hB hZ' hinr hZZ') hA (step_mem hB hZ')

@[simp] theorem uncurry_rel {h : ApproximableMap V₀ (funSpace V₁ V₂)}
    {W : Set (α ⊕ β)} {Z : Set γ} :
    (uncurry h).rel W Z ↔
      (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := Iff.rfl

/-- `uncurry` is the composition `eval ∘ ⟨h ∘ p₀, p₁⟩`. -/
theorem uncurry_eq (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    uncurry h = (evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, evalMap_apply]
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W₀, hwW₀, hW₀, hrel⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW₀
    rw [inl_preimage_prodNbhd] at hrel
    rw [inr_preimage_prodNbhd] at hrel
    obtain ⟨hwX, hwY⟩ := (prod_mem_split hX hY).mp hwW₀
    exact ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
  · rintro ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
    refine ⟨prodNbhd X Y, (prod_mem_split hX hY).mpr ⟨hwX, hwY⟩, prod_mem_prodNbhd hX hY, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact hrel

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `uncurry (curry g) = g`. -/
theorem uncurry_curry (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g := by
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, _, _, hmem⟩
    rw [prodNbhd_preimage hW]; exact hmem
  · intro hrel
    have hW := g.rel_dom hrel
    refine ⟨hW, prod_mem_inl hW, step_mem (prod_mem_inr hW) (g.rel_cod hrel), ?_⟩
    show g.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z
    rwa [← prodNbhd_preimage hW]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry (uncurry h) = h`. -/
theorem curry_uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : curry (uncurry h) = h := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨hX, hW, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    refine (rel_stepFun_iff h hX hL).mpr (fun p hp => ?_)
    have := hmem p hp
    -- `gSection (uncurry h) hX ∈ step p.1 p.2` means `(uncurry h).rel (prodNbhd X p.1) p.2`
    have hrel : (uncurry h).rel (prodNbhd X p.1) p.2 := this
    obtain ⟨_, hrel'⟩ := hrel
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel'
    exact hrel'
  · intro hrel
    have hX : V₀.mem X := h.rel_dom hrel
    have hW : (funSpace V₁ V₂).mem W := h.rel_cod hrel
    refine ⟨hX, hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    intro p hp
    show (uncurry h).rel (prodNbhd X p.1) p.2
    refine ⟨prod_mem_prodNbhd hX (hL p hp).1, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact (rel_stepFun_iff h hX hL).mp hrel p hp

/-- **Theorem 3.12(ii) (Scott 1981, PRG-19).** `eval ∘ ⟨curry(g) ∘ p₀, p₁⟩ = g`. -/
theorem eval_comp_curry (g : ApproximableMap (prod V₀ V₁) V₂) :
    (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g := by
  rw [← uncurry_eq]; exact uncurry_curry g

/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry` is an order-isomorphism between
`|𝒟₀ × 𝒟₁ → 𝒟₂|` and `|𝒟₀ → (𝒟₁ → 𝒟₂)|`. -/
def curryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (curry g).rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := by
        have hu : (uncurry (curry g)).rel W Z := by rw [uncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (uncurry (curry g')).rel W Z := ⟨g.rel_dom hrel, h2⟩
      rw [uncurry_curry] at hu'
      exact hu'
    · intro hg X W hrel
      obtain ⟨hX, hW, hmem⟩ := hrel
      refine ⟨hX, hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
      intro p hp
      have hgrel : g.rel (prodNbhd X p.1) p.2 := hmem p hp
      exact hg _ _ hgrel

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise323.lean -/

/-!
# Exercise 3.23 (Scott 1981, PRG-19, §3) — the category of domains is cartesian closed

Exercise 3.23 asks (for category theorists) to read off from Theorems 3.11 and 3.12 that the category
of domains and approximable mappings is *cartesian closed*, to identify its terminal object, and to
say what sort of functor `(𝒟₀ → 𝒟₁)` is.

The three ingredients are already in the development; this file packages them and supplies the
missing terminal object:

* **Terminal object.** The one-point domain `𝟙 = unitSys` (Exercise 3.15) is *terminal*: there is a
  unique approximable mapping `𝒟 → 𝟙` (`Unique (ApproximableMap V unitSys)`), because `|𝟙|` is a
  subsingleton.
* **Finite products.** `prod` with `proj₀`, `proj₁` is the categorical product (Exercise 3.20).
* **Exponentials.** `curryEquiv` (Theorem 3.12) is the natural adjunction
  `Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential `𝒟₂^𝒟₁`.

So `𝟙`, `×`, and `→` make the category cartesian closed, and `(𝒟₀ → -)` is a (covariant) functor
right adjoint to `- × 𝒟₀`. Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### The terminal domain. -/

/-- There is at most one approximable mapping into the terminal domain `𝟙`: the codomain `|𝟙|`
is a subsingleton, so any two maps have the same elementwise action. -/
instance : Subsingleton (ApproximableMap V unitSys) :=
  ⟨fun _ _ => ext_of_toElementMap fun _ => Subsingleton.elim _ _⟩

/-- **Exercise 3.23 (Scott 1981, PRG-19).** `𝟙 = unitSys` is the *terminal object*: for every domain
`𝒟` there is a unique approximable mapping `𝒟 → 𝟙` (the constant map at `⊥`). -/
instance : Unique (ApproximableMap V unitSys) where
  default := constMap V (default : unitSys.Element)
  uniq _ := Subsingleton.elim _ _

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The unique map to the terminal object, named. -/
def toUnit : ApproximableMap V unitSys := default

theorem toUnit_unique (f : ApproximableMap V unitSys) : f = toUnit V := Subsingleton.elim _ _

/-! ### The exponential adjunction (cartesian closure). -/

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The cartesian-closed adjunction
`Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential object. This
is exactly `curryEquiv` of Theorem 3.12. -/
def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise510.lean -/

/-!
# Exercise 5.10 (Scott 1981, PRG-19, §5) — the smash product and the strict function space

> Suppose `𝒟₀` and `𝒟₁` are neighbourhood systems over disjoint sets `Δ₀` and `Δ₁`. Define the
> *smash product* `𝒟₀ ⊗ 𝒟₁` with neighbourhoods
> `{Δ₀ ∪ Δ₁} ∪ {X ∪ Y ∣ X ∈ 𝒟₀ ∖ {Δ₀} and Y ∈ 𝒟₁ ∖ {Δ₁}}`.
> Show that this *is* a neighbourhood system. Define `(𝒟₀ →⊥ 𝒟₁)` so that `|𝒟₀ →⊥ 𝒟₁|` consists
> exactly of the *strict functions*. By introducing appropriate combinators, show that
> `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))` and `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)` are isomorphic.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, exactly as for the ordinary
product (`Domain/Neighborhood/Product.lean`), reusing `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`
and its algebra (`prodNbhd_inter`, `prodNbhd_subset_iff`, `prodNbhd_injective`).

This file is organised as follows.

* **The smash product** `smash V₀ V₁` (`§ smash`): a genuine neighbourhood system. The neighbourhoods
  are the master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` whose factors are
  both *proper* (`X ≠ Δ₀`, `Y ≠ Δ₁`). Closure under consistent intersection is the new content: the
  consistency witness rules out the degenerate cases, and a proper factor stays proper under
  intersection.
* **The smash collapses bottoms** (`§ elements`): the element `smashPair x y` (the strict pairing) and
  the order-isomorphism showing `|𝒟₀ ⊗ 𝒟₁|` is the *smash* of the pointed domains — every element is
  either `⊥` or a pair `⟨x, y⟩` of *non-`⊥`* elements.
* **The strict function space** `strictFun V₀ V₁` (`§ strict`): a neighbourhood system whose elements
  are exactly the *strict* approximable maps (`IsStrict f`, i.e. `f(⊥) = ⊥`). We realise it as the
  function space generated only by step neighbourhoods `[X, Y]` with *proper* input `X`, and prove the
  representation `strictFunEquiv : |𝒟₀ →⊥ 𝒟₁| ≃o {f ∣ IsStrict f}`.
* **The adjunction** (`§ iso`): the "appropriate combinators" Scott asks for — a strict curry
  `smashCurryMap` and strict uncurry `smashUncurryMap` — assembled into the order-isomorphism
  `smashCurryEquiv : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃o (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`. The decisive computation is
  `section_uncurry_rel`: `g(⟨x, y⟩⊗) = curry⊥(g)(x)(y)`, with the boundary (a master factor) handled
  by strictness — exactly the bottom-gluing the smash performs.

The *data* (`smash`, `strictFun`, `smashCurryMap`, `smashUncurryMap`) and the representation
`strictFunEquiv` are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); `Classical.choice`
enters only the `smashCurryEquiv` *proof*, through the genuinely-classical `X = Δ₀?` / `Y = Δ₁?`
boundary case analysis.
-/

namespace Scott1980.Neighborhood.Exercise510

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

/-! ### The smash product `𝒟₀ ⊗ 𝒟₁`. -/

/-- A *proper* product neighbourhood of the smash: `X ∪ Y` with `X ∈ 𝒟₀ ∖ {Δ₀}` and
`Y ∈ 𝒟₁ ∖ {Δ₁}` (both factors strictly below their masters). -/
def SmashProper (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (W : Set (α ⊕ β)) : Prop :=
  ∃ X Y, V₀.mem X ∧ X ≠ V₀.master ∧ V₁.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A neighbourhood that is `⊆ Δ₀` and equals `Δ₀` exactly when it contains `Δ₀`. A proper factor
`X ≠ Δ₀` stays proper after intersecting with anything: `X ∩ X' ≠ Δ₀`. -/
theorem inter_ne_master_left {X X' : Set α} (hX : V₀.mem X) (hXne : X ≠ V₀.master) :
    X ∩ X' ≠ V₀.master := by
  intro h
  apply hXne
  refine Set.Subset.antisymm (V₀.sub_master hX) ?_
  rw [← h]; exact Set.inter_subset_left

theorem inter_ne_master_right {Y Y' : Set β} (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) :
    Y ∩ Y' ≠ V₁.master :=
  inter_ne_master_left (V₀ := V₁) hY hYne

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁`.** Neighbourhoods are the
master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` (both factors proper).

*This is a neighbourhood system.* Condition (i) is the master clause. Condition (ii) is the new
content: given two smash neighbourhoods with a consistency witness `Z`,

* if either is the master, the intersection collapses to the other (since `X ⊆ Δ₀`, `Y ⊆ Δ₁`);
* if both are proper, `Z` cannot be the master (that would force a factor to be `Δ₀`/`Δ₁`), so `Z` is
  a *proper* `U ∪ V`; `U ⊆ X ∩ X'` and `V ⊆ Y ∩ Y'` then witness `X ∩ X' ∈ 𝒟₀`, `Y ∩ Y' ∈ 𝒟₁`, both
  still proper (`inter_ne_master_*`). -/
def smash (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W
  master := prodNbhd V₀.master V₁.master
  master_nonempty := by
    obtain ⟨a, ha⟩ := V₀.master_nonempty
    exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hZ hZsub
    · -- W = master
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master hX'),
          Set.inter_eq_right.mpr (V₁.sub_master hY')]
    · -- W = X ∪ Y proper
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
          Set.inter_eq_left.mpr (V₁.sub_master hY)]
      · -- both proper: use the witness Z
        right
        rw [prodNbhd_inter] at hZsub ⊢
        rcases hZ with hZeq | ⟨U, V, hU, _, hV, _, rfl⟩
        · -- Z = master is impossible
          exfalso
          rw [hZeq] at hZsub
          obtain ⟨hΔ₀, _⟩ := prodNbhd_subset_iff.mp hZsub
          exact hXne (Set.Subset.antisymm (V₀.sub_master hX) (hΔ₀.trans Set.inter_subset_left))
        · obtain ⟨hUsub, hVsub⟩ := prodNbhd_subset_iff.mp hZsub
          refine ⟨X ∩ X', Y ∩ Y', ?_, ?_, ?_, ?_, rfl⟩
          · exact V₀.inter_mem hX hX' hU hUsub
          · exact inter_ne_master_left hX hXne
          · exact V₁.inter_mem hY hY' hV hVsub
          · exact inter_ne_master_right hY hYne
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, _, hY, _, rfl⟩)
    · exact subset_rfl
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

@[simp] theorem smash_master :
    (smash V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

theorem smash_mem_iff {W : Set (α ⊕ β)} :
    (smash V₀ V₁).mem W ↔
      W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W := Iff.rfl

/-- A proper product neighbourhood is a neighbourhood of the smash. -/
theorem smash_mem_proper {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) : (smash V₀ V₁).mem (prodNbhd X Y) :=
  Or.inr ⟨X, Y, hX, hXne, hY, hYne, rfl⟩

/-- `⊥` of the smash is exactly `{Δ₀ ∪ Δ₁}`. -/
@[simp] theorem smash_mem_bot {W : Set (α ⊕ β)} :
    (smash V₀ V₁).bot.mem W ↔ W = prodNbhd V₀.master V₁.master := by
  rw [NeighborhoodSystem.mem_bot, smash_master]

/-! ### The smash collapses bottoms: the strict pairing `⟨x, y⟩⊗`.

The smash identifies all elements that have a `⊥` in either coordinate. We realise this by the *strict
pairing* `smashPair x y`: when both `x, y` are non-`⊥` it is the genuine pair `⟨x, y⟩`, and when either
is `⊥` it collapses to `⊥` (`smashPair_eq_bot_iff`). Every element of `|𝒟₀ ⊗ 𝒟₁|` arises this way. -/

/-- The *strict pairing* `⟨x, y⟩⊗`: the filter generated by the proper product neighbourhoods
`X ∪ Y` with `X ∈ x ∖ {Δ₀}`, `Y ∈ y ∖ {Δ₁}` (plus the master). When either `x` or `y` is `⊥` (i.e.
contains only its master), this collapses to `⊥`. -/
def smashPair (x : V₀.Element) (y : V₁.Element) : (smash V₀ V₁).Element where
  mem W := W = prodNbhd V₀.master V₁.master ∨
    ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩)
    · exact (smash V₀ V₁).master_mem
    · exact smash_mem_proper (x.sub hX) hXne (y.sub hY) hYne
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW'
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        exact ⟨X', Y', hX', hX'ne, hY', hY'ne, by
          rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master (x.sub hX')),
            Set.inter_eq_right.mpr (V₁.sub_master (y.sub hY'))]⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        exact ⟨X, Y, hX, hXne, hY, hYne, by
          rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master (x.sub hX)),
            Set.inter_eq_left.mpr (V₁.sub_master (y.sub hY))]⟩
      · right
        refine ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', inter_ne_master_left (x.sub hX) hXne,
          y.inter_mem hY hY', inter_ne_master_right (y.sub hY) hYne, ?_⟩
        rw [prodNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hsub
    · left
      exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW') hsub
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rfl
      · obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
        right
        exact ⟨X', Y', x.up_mem hX hX' hXX', hX'ne, y.up_mem hY hY' hYY', hY'ne, rfl⟩

@[simp] theorem mem_smashPair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (smashPair x y).mem W ↔ W = prodNbhd V₀.master V₁.master ∨
      ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y := Iff.rfl

/-- An element is `⊥` iff every neighbourhood it contains is the master: `x ≠ ⊥` exactly when `x`
contains a *proper* neighbourhood. -/
theorem exists_proper_of_ne_bot {x : V₀.Element} (hx : x ≠ V₀.bot) :
    ∃ X, x.mem X ∧ X ≠ V₀.master := by
  by_contra hc
  refine hx (le_antisymm (fun W hW => ?_) (V₀.bot_le x))
  rw [NeighborhoodSystem.mem_bot]
  by_contra hWne
  exact hc ⟨W, hW, hWne⟩

theorem eq_bot_of_no_proper {x : V₀.Element} (hx : ∀ X, x.mem X → X = V₀.master) :
    x = V₀.bot :=
  le_antisymm (fun W hW => by rw [NeighborhoodSystem.mem_bot]; exact hx W hW)
    (V₀.bot_le x)

/-- The strict pairing is `⊥` iff one of the components is `⊥`: the smash glues `(⊥, y)` and `(x, ⊥)`
to a single bottom. -/
theorem smashPair_eq_bot_iff {x : V₀.Element} {y : V₁.Element} :
    smashPair x y = (smash V₀ V₁).bot ↔ x = V₀.bot ∨ y = V₁.bot := by
  constructor
  · intro h
    by_contra hcon
    obtain ⟨hx, hy⟩ := not_or.mp hcon
    obtain ⟨X, hxX, hXne⟩ := exists_proper_of_ne_bot hx
    obtain ⟨Y, hyY, hYne⟩ := exists_proper_of_ne_bot hy
    -- `prodNbhd X Y` is a proper member of `smashPair x y`, but `⊥` contains only the master.
    have hmem : (smashPair x y).mem (prodNbhd X Y) :=
      Or.inr ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩
    rw [h, smash_mem_bot] at hmem
    obtain ⟨hX, _⟩ := prodNbhd_injective hmem
    exact hXne hX
  · intro h
    apply eq_bot_of_no_proper
    rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
    · rfl
    · exfalso
      rcases h with hx | hy
      · rw [hx, NeighborhoodSystem.mem_bot] at hxX; exact hXne hxX
      · rw [hy, NeighborhoodSystem.mem_bot] at hyY; exact hYne hyY

/-- The strict pairing is monotone in both arguments. -/
theorem smashPair_mono {x x' : V₀.Element} {y y' : V₁.Element} (hx : x ≤ x') (hy : y ≤ y') :
    smashPair x y ≤ smashPair x' y' := by
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, Y, hx X hxX, hXne, hy Y hyY, hYne, rfl⟩

/-- The principal filter of the master is `⊥`. -/
theorem principal_master_eq_bot {X : Set α} (hX : V₀.mem X) (hXm : X = V₀.master) :
    V₀.principal hX = V₀.bot := by
  subst hXm; rfl

/-- A `⊥` left factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_left (y : V₁.Element) : smashPair V₀.bot y = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hxX; exact absurd hxX hXne

/-- A `⊥` right factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_right (x : V₀.Element) : smashPair x V₁.bot = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hyY; exact absurd hyY hYne

/-! ### The strict function space `(𝒟₀ →⊥ 𝒟₁)`.

A map `f : 𝒟₀ → 𝒟₁` is **strict** when `f(⊥) = ⊥`. In relational terms (since `f(⊥)` is the filter
`{Y ∣ Δ₀ f Y}`), this says `f` relates the master input `Δ₀` only to the master output `Δ₁`:
`Δ₀ f Y ⟹ Y = Δ₁`.

We realise `(𝒟₀ →⊥ 𝒟₁)` as the function space whose *tokens* are the **strict** approximable maps and
whose neighbourhoods are the non-empty finite intersections of step sets `[X, Y] = {f ∣ X f Y}`. The
crucial point — making `|𝒟₀ →⊥ 𝒟₁|` consist *exactly* of the strict functions — is automatic: a step
`[Δ₀, Y]` with `Y ≠ Δ₁` contains *no* strict map, so it is empty, hence never a neighbourhood; thus no
filter can force a non-strict value at `⊥`. The representation `strictFunEquiv` then mirrors
Theorem 3.10. -/

/-- **A map is *strict* when `f(⊥) = ⊥`.** Relationally: `f` sends the master input only to the master
output. -/
def IsStrict (f : ApproximableMap V₀ V₁) : Prop :=
  ∀ ⦃Y⦄, f.rel V₀.master Y → Y = V₁.master

/-- Strictness is exactly `f(⊥) = ⊥`. -/
theorem isStrict_iff_apply_bot {f : ApproximableMap V₀ V₁} :
    IsStrict f ↔ f.toElementMap V₀.bot = V₁.bot := by
  constructor
  · intro h
    apply Element.ext
    intro Y
    rw [NeighborhoodSystem.mem_bot]
    constructor
    · rintro ⟨X, hX, hrel⟩
      rw [NeighborhoodSystem.mem_bot] at hX; subst hX
      exact h hrel
    · rintro rfl
      exact ⟨V₀.master, V₀.bot.master_mem, f.master_rel⟩
  · intro h Y hrel
    have : (f.toElementMap V₀.bot).mem Y := ⟨V₀.master, V₀.bot.master_mem, hrel⟩
    rw [h, NeighborhoodSystem.mem_bot] at this
    exact this

/-- Strictness is downward closed: a map below a strict map is strict. -/
theorem IsStrict.mono {f g : ApproximableMap V₀ V₁} (hf : IsStrict f) (hgf : g ≤ f) : IsStrict g :=
  fun _ hrel => hf (hgf _ _ hrel)

/-- The constant map at `⊥` is strict. -/
theorem isStrict_constBot : IsStrict (constMap V₀ (V₁.bot)) := by
  rintro Y ⟨_, hY⟩
  rwa [NeighborhoodSystem.mem_bot] at hY

/-- The identity is strict. -/
theorem isStrict_idMap : IsStrict (idMap V₀) := by
  rintro Y ⟨_, hY, hsub⟩
  exact Set.Subset.antisymm (V₀.sub_master hY) hsub

/-- The strict maps `𝒟₀ →⊥ 𝒟₁`, as a subtype carrying the inherited approximation order. -/
abbrev StrictMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :=
  {f : ApproximableMap V₀ V₁ // IsStrict f}

/-- A step set among strict maps: `[X, Y] = {f strict ∣ X f Y}`. -/
def sstep (X : Set α) (Y : Set β) : Set (StrictMap V₀ V₁) := {f | f.1.rel X Y}

@[simp] theorem mem_sstep {X : Set α} {Y : Set β} {f : StrictMap V₀ V₁} :
    f ∈ sstep X Y ↔ f.1.rel X Y := Iff.rfl

/-- A finite intersection of strict step sets. -/
def sstepFun (L : List (Set α × Set β)) : Set (StrictMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.1.rel p.1 p.2}

@[simp] theorem mem_sstepFun {L : List (Set α × Set β)} {f : StrictMap V₀ V₁} :
    f ∈ sstepFun L ↔ ∀ p ∈ L, f.1.rel p.1 p.2 := Iff.rfl

@[simp] theorem sstepFun_nil : (sstepFun [] : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simp

theorem sstepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (sstepFun (p :: L) : Set (StrictMap V₀ V₁)) = sstep p.1 p.2 ∩ sstepFun L := by
  ext f
  simp only [mem_sstepFun, List.mem_cons, Set.mem_inter_iff, mem_sstep]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

theorem sstepFun_append (L L' : List (Set α × Set β)) :
    (sstepFun (L ++ L') : Set (StrictMap V₀ V₁)) = sstepFun L ∩ sstepFun L' := by
  ext f
  simp only [mem_sstepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

theorem sstepFun_singleton (X : Set α) (Y : Set β) :
    (sstepFun [(X, Y)] : Set (StrictMap V₀ V₁)) = sstep X Y := by
  rw [sstepFun_cons, sstepFun_nil, Set.inter_univ]

/-- `[Δ₀, Δ₁] = |𝒟₀ →⊥ 𝒟₁|`: every (strict) map relates the masters. -/
@[simp] theorem sstep_master_eq :
    (sstep V₀.master V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.1.master_rel

theorem sstep_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (sstep X Y ∩ sstep X Y' : Set (StrictMap V₀ V₁)) = sstep X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_sstep]
  constructor
  · rintro ⟨h, h'⟩; exact f.1.inter_right h h'
  · intro h
    exact ⟨f.1.mono h subset_rfl Set.inter_subset_left (f.1.rel_dom h) hY,
           f.1.mono h subset_rfl Set.inter_subset_right (f.1.rel_dom h) hY'⟩

theorem sstep_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (sstep X Y : Set (StrictMap V₀ V₁)) ⊆ sstep X' Y' := by
  intro f hf
  exact f.1.mono hf hX'X hYY' hX' hY'

/-- **Exercise 5.10 — the strict function space `(𝒟₀ →⊥ 𝒟₁)`.** Tokens are the strict approximable
maps; neighbourhoods are non-empty finite intersections of step sets. -/
def strictFun (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (StrictMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨⟨constMap V₀ V₁.bot, isStrict_constBot⟩, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, sstepFun_nil.symm⟩,
    ⟨⟨constMap V₀ V₁.bot, isStrict_constBot⟩, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem strictFun_master : (strictFun V₀ V₁).master = Set.univ := rfl

theorem strictFun_mem_iff {W : Set (StrictMap V₀ V₁)} :
    (strictFun V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
        ∧ W.Nonempty := Iff.rfl

/-- A step set is a neighbourhood as soon as it has a (strict) witness. -/
theorem sstep_mem_of_mem {g : StrictMap V₀ V₁} {X : Set α} {Y : Set β} (h : g.1.rel X Y) :
    (strictFun V₀ V₁).mem (sstep X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (sstepFun_singleton X Y).symm⟩, ⟨g, h⟩⟩
  intro p hp; rw [List.mem_singleton] at hp; subst hp
  exact ⟨g.1.rel_dom h, g.1.rel_cod h⟩

/-- Intersection of two neighbourhoods, when non-empty, is again one. -/
theorem strictFun_mem_inter {W W' : Set (StrictMap V₀ V₁)}
    (hW : (strictFun V₀ V₁).mem W) (hW' : (strictFun V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (strictFun V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

theorem sstepFun_up_closed {L : List (Set α × Set β)} {f f' : StrictMap V₀ V₁}
    (hf : f ∈ sstepFun L) (hff' : f ≤ f') : f' ∈ sstepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)

theorem strictFun_mem_up_closed {W : Set (StrictMap V₀ V₁)} (hW : (strictFun V₀ V₁).mem W)
    {f f' : StrictMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact sstepFun_up_closed hf hff'

/-- The generation lemma: a filter contains `sstepFun L` iff it contains each step `[Xᵢ, Yᵢ]`. -/
theorem mem_sstepFun_iff (φ : (strictFun V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (sstepFun L) ↔ ∀ p ∈ L, φ.mem (sstep p.1 p.2) := by
  induction L with
  | nil => simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [sstepFun_cons]
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨g, hg⟩ := (φ.sub hmem).2
      have hstep : φ.mem (sstep p.1 p.2) :=
        φ.up_mem hmem (sstep_mem_of_mem (g := g) (hg.1)) Set.inter_subset_left
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (sstepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

/-- **The strict map represented by a filter.** `X (toStrictMap φ) Y ↔ [X, Y] ∈ φ`. It is *strict*
because the step `[Δ₀, Y]` with `Y ≠ Δ₁` is empty (no strict map relates `Δ₀` to a proper output),
hence not a neighbourhood, so it cannot belong to `φ`. -/
def toStrictMap (φ : (strictFun V₀ V₁).Element) : StrictMap V₀ V₁ :=
  ⟨{ rel := fun X Y => φ.mem (sstep X Y)
     rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_dom hf
     rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_cod hf
     master_rel := by
       show φ.mem (sstep V₀.master V₁.master); rw [sstep_master_eq]; exact φ.master_mem
     inter_right := by
       intro X Y Y' h h'
       obtain ⟨f, hf⟩ := (φ.sub h).2
       obtain ⟨f', hf'⟩ := (φ.sub h').2
       have hY : V₁.mem Y := f.1.rel_cod hf
       have hY' : V₁.mem Y' := f'.1.rel_cod hf'
       show φ.mem (sstep X (Y ∩ Y'))
       rw [← sstep_inter_right hY hY']
       exact φ.inter_mem h h'
     mono := by
       intro X X' Y Y' h hX'X hYY' hX' hY'
       obtain ⟨g, hg⟩ := (φ.sub h).2
       have hg' : g.1.rel X' Y' := g.1.mono hg hX'X hYY' hX' hY'
       show φ.mem (sstep X' Y')
       exact φ.up_mem h (sstep_mem_of_mem (g := g) hg') (sstep_subset hX' hY' hX'X hYY') },
   by
     intro Y h
     obtain ⟨g, hg⟩ := (φ.sub h).2
     exact g.2 hg⟩

@[simp] theorem toStrictMap_rel {φ : (strictFun V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toStrictMap φ).1.rel X Y ↔ φ.mem (sstep X Y) := Iff.rfl

/-- **The filter `f̂ = {F ∣ f ∈ F}` of a strict map.** -/
def toStrictFilter (f : StrictMap V₀ V₁) : (strictFun V₀ V₁).Element where
  mem W := (strictFun V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(strictFun V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    exact ⟨strictFun_mem_inter hW hW' ⟨f, Set.mem_inter hfW hfW'⟩, Set.mem_inter hfW hfW'⟩
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

@[simp] theorem mem_toStrictFilter {f : StrictMap V₀ V₁} {W : Set (StrictMap V₀ V₁)} :
    (toStrictFilter f).mem W ↔ (strictFun V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

/-- **Exercise 5.10 — the strict function space is complete.** `|𝒟₀ →⊥ 𝒟₁|` is order-isomorphic to
the strict approximable maps `𝒟₀ → 𝒟₁`. -/
def strictFunEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (strictFun V₀ V₁).Element ≃o StrictMap V₀ V₁ where
  toFun := toStrictMap
  invFun := toStrictFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_sstepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨sstep_mem_of_mem (g := f) hf, hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_sstepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_sstepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

/-! ### The adjunction `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) ≅ ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`.

The smash product is *left adjoint* to the strict function space: strict maps out of a smash product
are the same as strict maps into a strict function space. We realise the iso with the "appropriate
combinators" Scott asks for — a *strict curry* and *strict uncurry* — connected by the computation
`g(⟨x, y⟩⊗) = (curry g)(x)(y)`.

The decisive computation is `smashPair_principal_apply`: for *proper* `X, Y`, applying `g` to the
strict pairing of the principal elements is the same as `g` relating the proper neighbourhood
`X ∪ Y`. At the bottom (a master factor) the strict pairing collapses to `⊥`, where strictness forces
the master output — exactly the gluing the smash performs. -/

variable {V₂ : NeighborhoodSystem γ}

/-- Every smash neighbourhood is a product neighbourhood `A ∪ B` (the master is `Δ₀ ∪ Δ₁`). -/
theorem smash_mem_prodNbhd_form {W : Set (α ⊕ β)} (hW : (smash V₀ V₁).mem W) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ W = prodNbhd A B := by
  rcases hW with rfl | ⟨X, Y, hX, _, hY, _, rfl⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, rfl⟩
  · exact ⟨X, Y, hX, hY, rfl⟩

/-- **The key computation.** For *proper* `X, Y`, `g(⟨↑X, ↑Y⟩⊗)` contains `Z` iff `g` relates the
proper neighbourhood `X ∪ Y` to `Z`. (Coarser members of the strict pairing are absorbed by
monotonicity; the master member needs only that `X ∪ Y ⊆ Δ₀ ∪ Δ₁`.) -/
theorem smashPair_principal_apply (g : ApproximableMap (smash V₀ V₁) V₂)
    {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) {Z : Set γ} :
    (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z
      ↔ g.rel (prodNbhd X Y) Z := by
  constructor
  · rintro ⟨W, hW, hrel⟩
    rcases hW with rfl | ⟨A, B, ⟨_, hXA⟩, _, ⟨_, hYB⟩, _, rfl⟩
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨hXA, hYB⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
  · intro hrel
    exact ⟨prodNbhd X Y, Or.inr ⟨X, Y, ⟨hX, subset_rfl⟩, hXne, ⟨hY, subset_rfl⟩, hYne, rfl⟩, hrel⟩

/-- The `X`-section of `g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₂`, as a map `𝒟₁ → 𝒟₂`: `y ↦ g(⟨↑X, y⟩⊗)`. Built with
Exercise 2.8's `ofMono` from its values on principal inputs. -/
def smashSection (g : ApproximableMap (smash V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ :=
  ofMono (fun Y hY => g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY)))
    (by
      intro Y Y' hY hY' hY'Y
      exact toElementMap_mono g (smashPair_mono le_rfl ((V₁.principal_le_iff hY hY').mpr hY'Y)))

theorem smashSection_rel {g : ApproximableMap (smash V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} :
    (smashSection g hX).rel Y Z ↔
      ∃ hY : V₁.mem Y, (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z :=
  Iff.rfl

/-- The section is monotone in the neighbourhood `X` (a smaller input gives a larger section). -/
theorem smashSection_mono {g : ApproximableMap (smash V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    smashSection g hX ≤ smashSection g hX' := by
  intro Y Z hrel
  obtain ⟨hY, hmem⟩ := hrel
  exact ⟨hY, toElementMap_mono g
    (smashPair_mono ((V₀.principal_le_iff hX hX').mpr hX'X) le_rfl) Z hmem⟩

/-- The section of a *strict* `g` is itself strict: `g(⟨↑X, ⊥⟩⊗) = g(⊥) = ⊥`. -/
theorem isStrict_smashSection {g : ApproximableMap (smash V₀ V₁) V₂} (hg : IsStrict g)
    {X : Set α} (hX : V₀.mem X) : IsStrict (smashSection g hX) := by
  rw [isStrict_iff_apply_bot, smashSection,
    show (V₁.bot) = V₁.principal V₁.master_mem from rfl, toElementMap_ofMono_principal,
    show smashPair (V₀.principal hX) (V₁.principal V₁.master_mem) = (smash V₀ V₁).bot from
      smashPair_bot_right _]
  exact isStrict_iff_apply_bot.mp hg

/-- The generation lemma for maps into the strict function space: `X h (⋂ᵢ[Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_sstepFun_iff (h : ApproximableMap V₀ (strictFun V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (sstepFun L) ↔ ∀ p ∈ L, h.rel X (sstep p.1 p.2) := by
  induction L with
  | nil =>
    simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    show h.rel X (strictFun V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [sstepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.rel_cod hmem)).2
      have hstep : h.rel X (sstep p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (sstep_mem_of_mem (g := f) (hf.1))
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (h.rel_cod hmem).2
      have htail : h.rel X (sstepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

/-- **Strict curry combinator.** `curry⊥ : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) → (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`, sending `g`
to `x ↦ (y ↦ g(⟨x, y⟩⊗))`. -/
def smashCurryMap (g : StrictMap (smash V₀ V₁) V₂) : StrictMap V₀ (strictFun V₁ V₂) :=
  ⟨{ rel := fun X N => ∃ hX : V₀.mem X, (strictFun V₁ V₂).mem N ∧
       (⟨smashSection g.1 hX, isStrict_smashSection g.2 hX⟩ : StrictMap V₁ V₂) ∈ N
     rel_dom := fun ⟨hX, _⟩ => hX
     rel_cod := fun ⟨_, hN, _⟩ => hN
     master_rel := ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
     inter_right := by
       rintro X N N' ⟨hX, hN, hmem⟩ ⟨_, hN', hmem'⟩
       exact ⟨hX, strictFun_mem_inter hN hN' ⟨_, hmem, hmem'⟩, Set.mem_inter hmem hmem'⟩
     mono := by
       rintro X X' N N' ⟨hX, hN, hmem⟩ hX'X hNN' hX' hN'
       refine ⟨hX', hN', strictFun_mem_up_closed hN' (hNN' hmem) ?_⟩
       exact Subtype.coe_le_coe.mp (smashSection_mono hX hX' hX'X) },
  by
    rintro N ⟨hΔ₀, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    have hall : ∀ p ∈ L, p.2 = V₂.master := by
      intro p hp
      have hpr : (smashSection g.1 hΔ₀).rel p.1 p.2 := hmem p hp
      rw [smashSection_rel] at hpr
      obtain ⟨hp1, hpmem⟩ := hpr
      have hbot : smashPair (V₀.principal hΔ₀) (V₁.principal hp1) = (smash V₀ V₁).bot := by
        rw [principal_master_eq_bot hΔ₀ rfl]; exact smashPair_bot_left _
      rw [hbot, isStrict_iff_apply_bot.mp g.2, NeighborhoodSystem.mem_bot] at hpmem
      exact hpmem
    apply Set.eq_univ_of_forall
    intro f q hq
    rw [hall q hq]
    exact (f.1).rel_master (hL q hq).1⟩

/-- **Strict uncurry combinator.** `uncurry⊥ : (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) → ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`,
`X ∪ Y (uncurry⊥ h) Z ↔ X h [Y, Z]`. -/
def smashUncurryMap (h : StrictMap V₀ (strictFun V₁ V₂)) : StrictMap (smash V₀ V₁) V₂ :=
  ⟨{ rel := fun W Z => (smash V₀ V₁).mem W ∧ h.1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z)
     rel_dom := fun hh => hh.1
     rel_cod := by
       rintro W Z ⟨_, hrel⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       exact f.1.rel_cod hf
     master_rel := by
       refine ⟨(smash V₀ V₁).master_mem, ?_⟩
       rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
         inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
       exact h.1.master_rel
     inter_right := by
       rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       obtain ⟨f', hf'⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel')).2
       refine ⟨hW, ?_⟩
       rw [← sstep_inter_right (f.1.rel_cod hf) (f'.1.rel_cod hf')]
       exact h.1.inter_right hrel hrel'
     mono := by
       rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
       have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
       have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
       obtain ⟨A, B, hA, hB, rfl⟩ := smash_mem_prodNbhd_form hW₂
       refine ⟨hW₂, ?_⟩
       rw [inl_preimage_prodNbhd] at hinl
       rw [inr_preimage_prodNbhd] at hinr
       rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       have hfB : f.1.rel B Z' := f.1.mono hf hinr hZZ' hB hZ'
       exact h.1.mono hrel hinl (sstep_subset hB hZ' hinr hZZ') hA
         (sstep_mem_of_mem (g := f) hfB) },
   by
     rintro Z ⟨_, hrel⟩
     rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
       inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel
     have huniv : sstep V₁.master Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
     have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep V₁.master Z := by
       rw [huniv]; exact Set.mem_univ _
     obtain ⟨_, hZ⟩ := hcb
     rwa [NeighborhoodSystem.mem_bot] at hZ⟩

/-! ### The roundtrip identities and the adjunction isomorphism. -/

/-- A step with master codomain is everything: every strict map relates `Y` to `Δ₁`. -/
theorem sstep_cod_master {Y : Set α} (hY : V₀.mem Y) :
    (sstep Y V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_sstep, Set.mem_univ, iff_true]
  exact f.1.mono f.1.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

/-- **The decisive computation for the adjunction.** The `X`-section of `uncurry⊥ h` evaluated on a
neighbourhood `Y` is exactly the strict-function value `X h [Y, Z]`. At the boundary (a master
factor) both sides collapse via strictness; off the boundary it is `smashPair_principal_apply`. -/
theorem section_uncurry_rel (h : StrictMap V₀ (strictFun V₁ V₂))
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    (smashSection (smashUncurryMap h).1 hX).rel Y Z ↔ h.1.rel X (sstep Y Z) := by
  rw [smashSection_rel]
  by_cases hXm : X = V₀.master
  · subst hXm
    constructor
    · rintro ⟨hY', hmem⟩
      rw [principal_master_eq_bot hX rfl,
        show smashPair V₀.bot (V₁.principal hY') = (smash V₀ V₁).bot from
          smashPair_eq_bot_iff.mpr (Or.inl rfl),
        isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
      subst hmem
      rw [sstep_cod_master hY]
      exact h.1.rel_master hX
    · intro hrel
      have huniv : sstep Y Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
      have hZ : Z = V₂.master := by
        have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep Y Z := by
          rw [huniv]; exact Set.mem_univ _
        obtain ⟨_, hbz⟩ := hcb
        rwa [NeighborhoodSystem.mem_bot] at hbz
      subst hZ
      exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
  · by_cases hYm : Y = V₁.master
    · subst hYm
      constructor
      · rintro ⟨hY', hmem⟩
        rw [principal_master_eq_bot hY' rfl,
          show smashPair (V₀.principal hX) V₁.bot = (smash V₀ V₁).bot from
            smashPair_eq_bot_iff.mpr (Or.inr rfl),
          isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
        subst hmem
        rw [sstep_master_eq]
        exact h.1.rel_master hX
      · intro hrel
        obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
        have hZ : Z = V₂.master := f.2 hf
        subst hZ
        exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
    · constructor
      · rintro ⟨hY', hmem⟩
        obtain ⟨_, hrel⟩ :=
          (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mp hmem
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel
      · intro hrel
        refine ⟨hY, (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mpr ?_⟩
        refine ⟨smash_mem_proper hX hXm hY hYm, ?_⟩
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel

/-- **Roundtrip (i): `uncurry⊥ ∘ curry⊥ = id`.** -/
theorem smashUncurry_curry (g : StrictMap (smash V₀ V₁) V₂) :
    smashUncurryMap (smashCurryMap g) = g := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, hcurry⟩
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hXm, _, hsec⟩ := hcurry
      have hZ : Z = V₂.master := isStrict_smashSection g.2 hXm hsec
      rw [hZ]; exact g.1.master_rel
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hX, _, hY, hmem⟩ := hcurry
      exact (smashPair_principal_apply g.1 hXp hXne hYp hYne).mp hmem
  · intro hrel
    have hW : (smash V₀ V₁).mem W := g.1.rel_dom hrel
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · have hZ : Z = V₂.master := g.2 hrel
      subst hZ
      refine ⟨Or.inl rfl, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
      exact ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
    · refine ⟨smash_mem_proper hXp hXne hYp hYne, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      have hsec : (smashSection g.1 hXp).rel Y Z :=
        ⟨hYp, (smashPair_principal_apply g.1 hXp hXne hYp hYne).mpr hrel⟩
      exact ⟨hXp, sstep_mem_of_mem
        (g := ⟨smashSection g.1 hXp, isStrict_smashSection g.2 hXp⟩) hsec, hsec⟩

/-- **Roundtrip (ii): `curry⊥ ∘ uncurry⊥ = id`.** -/
theorem smashCurry_uncurry (h : StrictMap V₀ (strictFun V₁ V₂)) :
    smashCurryMap (smashUncurryMap h) = h := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro X N
  constructor
  · rintro ⟨hX, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    refine (rel_sstepFun_iff h.1 hX hL).mpr (fun p hp => ?_)
    exact (section_uncurry_rel h hX (hL p hp).1).mp (hmem p hp)
  · intro hrel
    have hX : V₀.mem X := h.1.rel_dom hrel
    have hN : (strictFun V₁ V₂).mem N := h.1.rel_cod hrel
    refine ⟨hX, hN, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    intro p hp
    exact (section_uncurry_rel h hX (hL p hp).1).mpr
      ((rel_sstepFun_iff h.1 hX hL).mp hrel p hp)

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the adjunction.** The strict currying combinator is an
order isomorphism `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃ (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`: the smash product is left adjoint to
the strict function space. -/
def smashCurryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂) where
  toFun := smashCurryMap
  invFun := smashUncurryMap
  left_inv := smashUncurry_curry
  right_inv := smashCurry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (smashCurryMap g).1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z) := by
        have hu : (smashUncurryMap (smashCurryMap g)).1.rel W Z := by
          rw [smashUncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (smashUncurryMap (smashCurryMap g')).1.rel W Z := ⟨g.1.rel_dom hrel, h2⟩
      rw [smashUncurry_curry] at hu'
      exact hu'
    · intro hg X N hrel
      obtain ⟨hX, hN, hmem⟩ := hrel
      refine ⟨hX, hN, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
      intro p hp
      obtain ⟨hY, hmm⟩ := hmem p hp
      obtain ⟨W, hWmem, hWrel⟩ := hmm
      exact ⟨hY, W, hWmem, hg W p.2 hWrel⟩

end Scott1980.Neighborhood.Exercise510

/-! ### Inlined from Scott1980/Neighborhood/Definition68.lean -/

/-!
# Lecture VI — Definition 6.8 (Scott 1981, PRG-19): functors *continuous on maps*

> **DEFINITION 6.8.** On the category of domains and strict approximable maps a functor `T` is
> *continuous on maps* if for any systems `D` and `E` the induced mapping
> `λf. T(f) : (D →⊥ E) → (T(D) →⊥ T(E))` is approximable.

This is the continuity condition that powers Theorem 6.9 (existence of homomorphisms out of a fixed
point `D ≅ T(D)`): the homomorphism equation `h = k ∘ T(h) ∘ j` is a fixed-point equation for the map
`λh. k ∘ T(h) ∘ j`, and it has a solution precisely because `λh. T(h)` — hence the whole operator — is
itself an approximable (so continuous) self-map of a function-space domain.

## What the formalization uses

* **The category and the functor.** `T` is an `Endofunctor DomainObj` (Definition 6.3): an action
  `T.obj` on domains and `T.map` on the morphisms (here approximable maps, Theorem 2.5 laws).
* **The strict function space `(D →⊥ E)`.** This is *exactly* Scott's domain on the left of the
  induced map. The project already constructs it in `Exercise510.lean`: `strictFun D E` is the
  neighbourhood system whose elements are the **strict** approximable maps (`IsStrict f`, i.e.
  `f(⊥) = ⊥`), with the representation `strictFunEquiv : |D →⊥ E| ≃o StrictMap D E` mirroring
  Theorem 3.10. So this Definition is stated over Scott's strict maps verbatim, **not** the full
  function space.
* **"is approximable".** In this framework a function between domains is *approximable* exactly when
  it is the elementwise action (`toElementMap`) of an approximable map (Proposition 2.2 / Theorem
  3.10). So `λf. T(f)` being approximable is rendered as the existence of a witnessing
  `Φ : (D →⊥ E) → (T(D) →⊥ T(E))` (an `ApproximableMap` between the two strict function-space
  *domains*) whose action reproduces `T` on the underlying maps — transported across the
  representation `strictFunEquiv` via `toStrictFilter`/`toStrictMap`.

Because the witnessing equation reads off the underlying map of a `StrictMap`, it automatically forces
`T.map f` to be strict whenever `f` is (lemma `ContinuousOnMaps.isStrict_map`): a `T` continuous on
maps does restrict to Scott's subcategory of strict maps, as required.

## A design note on the category (strict maps vs. all maps)

Scott states 6.8 on the category of domains and *strict* maps, whereas the project's abstract spine
(Definitions 6.3–6.7) is built on the all-maps `DomainObj` category (its `Hom` is the full
`ApproximableMap`). We bridge the two faithfully without introducing a second, strict-map category
abstraction: the functor here is still `T : Endofunctor DomainObj` (acting on *all* maps), but the
continuity condition is stated over the *strict* function spaces `(D →⊥ E)`, and strictness-preservation
is then *derived* (`ContinuousOnMaps.isStrict_map`) rather than assumed. So `T` lives on the all-maps
category, yet "continuous on maps" pins down exactly the behaviour Scott asks for on the strict
subcategory — keeping Definition 6.8 coherent with the rest of the Lecture VI spine while remaining
literally about Scott's strict maps.

The identity functor is continuous on maps (`continuousOnMaps_id`), witnessing non-vacuity; its
representing `Φ` is the identity on the function space. Everything here is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe u

/-- The **identity endofunctor** on any category: it fixes objects and morphisms. (A convenient
witness that `Endofunctor` is inhabited; used to show Definition 6.8 is non-vacuous.) -/
def idEndofunctor (Obj : Type u) [Category Obj] : Endofunctor Obj where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem idEndofunctor_obj {Obj : Type u} [Category Obj] (X : Obj) :
    (idEndofunctor Obj).obj X = X := rfl

@[simp] theorem idEndofunctor_map {Obj : Type u} [Category Obj] {X Y : Obj}
    (f : Category.Hom X Y) : (idEndofunctor Obj).map f = f := rfl

/-- **Definition 6.8 (Scott 1981, PRG-19).** An endofunctor `T` on the category of domains is
*continuous on maps* when, for every pair of domains `D` and `E`, the induced action `λf. T(f)` on the
**strict** function space `(D →⊥ E)` is approximable: there is an approximable map `Φ` from
`(D →⊥ E)` to `(T(D) →⊥ T(E))` whose elementwise action (read through the representation
`strictFunEquiv`) sends each strict map `f` to `T(f)`. -/
def ContinuousOnMaps (T : Endofunctor DomainObj) : Prop :=
  ∀ D E : DomainObj,
    ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
      ∀ f : StrictMap D.sys E.sys,
        (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1

/-- A functor continuous on maps **preserves strictness** (so it genuinely lives on Scott's category
of domains and strict maps): if `f` is strict then so is `T(f)`. This is automatic from the witnessing
equation, whose left-hand side is the underlying map of a `StrictMap`. -/
theorem ContinuousOnMaps.isStrict_map {T : Endofunctor DomainObj} (h : ContinuousOnMaps T)
    {D E : DomainObj} (f : StrictMap D.sys E.sys) :
    IsStrict (T.map (X := D) (Y := E) f.1) := by
  obtain ⟨Φ, hΦ⟩ := h D E
  rw [← hΦ f]
  exact (toStrictMap (Φ.toElementMap (toStrictFilter f))).2

/-- `toStrictMap ∘ toStrictFilter = id` (the right inverse of the strict-function-space
representation, Exercise 5.10). -/
theorem toStrictMap_toStrictFilter {α β : Type*} {V₀ : NeighborhoodSystem α}
    {V₁ : NeighborhoodSystem β} (f : StrictMap V₀ V₁) :
    toStrictMap (toStrictFilter f) = f :=
  (strictFunEquiv V₀ V₁).right_inv f

/-- **The identity functor is continuous on maps** — the basic witness that Definition 6.8 is
satisfiable. The representing approximable map is the identity on `(D →⊥ E)`. -/
theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  show (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Lemma615.lean -/

/-!
# Lecture VI — Lemma 6.15 (Scott 1981, PRG-19): the converse of Proposition 6.12

Proposition 6.12 says a subdomain relation `D ◁ E` yields a *projection pair* `i : D → E`,
`j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. **Lemma 6.15** is the converse: *any* projection
pair — between two neighbourhood systems `D` and `E` over possibly **different** token types —
exhibits `D` as (isomorphic to) a subdomain of `E`. Scott writes `D ⊴ E` as short for "`D ≅ D'`
for some `D' ◁ E`."

**Lemma 6.15.** If there exist approximable maps `i : D → E` and `j : E → D` with `j ∘ i = I_D`
and `i ∘ j ⊆ I_E`, then `D ⊴ E`.

## The construction (cleaner than Scott's, fully relational)

Scott's proof works with the ideal elements (filters) and shows that `i` carries finite (principal)
elements to finite elements. We avoid the filter-by-filter argument by isolating one relational
predicate:

`IsGen i j X Y := X i Y ∧ Y j X`   ("`Y` generates `i(↑X)`").

Everything follows from three relational facts:

* **`isGen_exists`** (uses `j ∘ i = I_D`): every `X ∈ D` has a generator `Y` (apply `j∘i = I` to the
  identity relation `X I_D X`).
* **`isGen_mono`** (uses `j ∘ i = I_D`) and **`isGen_mono'`** (uses `i ∘ j ⊆ I_E`): the generator
  correspondence is inclusion-monotone in both directions — `Y ⊆ Y' ↔ X ⊆ X'`. Their two-way use
  gives that generators are unique in each argument (`isGen_fst_unique`/`isGen_snd_unique`).
* **`isGen_inter`** (just `mono`/`inter_right` of `i, j`): if `Y, Y'` are generators and `Y ∩ Y' ∈ E`,
  then `Y ∩ Y'` generates `X ∩ X'`.

The image system `Dprime i j` has `Y` as a neighbourhood iff `Y` generates some `X ∈ D`; its master
is `E`'s master. `isGen_inter` makes it a neighbourhood system **and** gives the crucial
`inter_closed` clause of `◁` (consistency inherited from `E`), so `Dprime i j ◁ E`. The
order-isomorphism `D ≅ Dprime i j` is `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` with inverse
`y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`, the inverse laws and order-reflection coming from generator
uniqueness.

Everything is built at the level of Definition 2.1 relations, so the whole development is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Scott's `⊴` (the prose before Lemma 6.15).** `D ⊴ E` means `D ≅ D'` for some subdomain
`D' ◁ E`: `D` *embeds as a subdomain* of `E`. -/
def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The generator predicate: `Y` generates `i(↑X)`. Relationally, `X i Y` and `Y j X`. -/
def IsGen (X : Set α) (Y : Set β) : Prop := i.rel X Y ∧ j.rel Y X

/-- The masters generate each other: `IsGen Δ_D Δ_E` (from `i.master_rel`, `j.master_rel`). -/
theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

/-- **Generators exist** (uses `j ∘ i = I_D`). Every `D`-neighbourhood `X` has a generator: apply
`j ∘ i = I_D` to the identity relation `X I_D X`. -/
theorem isGen_exists (hji : j.comp i = idMap D) {X : Set α} (hX : D.mem X) :
    ∃ Y, IsGen i j X Y := by
  have hrel : (j.comp i).rel X X := by rw [hji]; exact ⟨hX, hX, subset_rfl⟩
  obtain ⟨Y, hiXY, hjYX⟩ := hrel
  exact ⟨Y, hiXY, hjYX⟩

/-- **The generator correspondence is monotone** (uses `j ∘ i = I_D`): if `Y, Y'` generate `X, X'`
and `Y ⊆ Y'`, then `X ⊆ X'`. (Widen `X i Y` to `X i Y'` by `mono`, compose with `Y' j X'`, and read
off `X ⊆ X'` from `j ∘ i = I_D`.) -/
theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

/-- **The generator correspondence is monotone, other direction** (uses `i ∘ j ⊆ I_E`): if `Z, W`
generate `X, X'` and `X ⊆ X'`, then `Z ⊆ W`. (Widen `Z j X` to `Z j X'` by `mono`, compose with
`X' i W`, and read off `Z ⊆ W` from `i ∘ j ⊆ I_E`.) -/
theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

/-- Generators are unique in the first argument (`isGen_mono` both ways). -/
theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

/-- Generators are unique in the second argument (`isGen_mono'` both ways). -/
theorem isGen_snd_unique (hij : i.comp j ≤ idMap E) {X : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X Y') : Y = Y' :=
  Set.Subset.antisymm (isGen_mono' i j hij h h' subset_rfl)
    (isGen_mono' i j hij h' h subset_rfl)

/-- **Generators are closed under intersection.** If `Y, Y'` generate `X, X'` and `Y ∩ Y' ∈ E`, then
`Y ∩ Y'` generates `X ∩ X'`. Needs only `mono`/`inter_right` of `i` and `j` (the hypothesis
`E.mem (Y ∩ Y')` is what licenses the `j.mono` steps). -/
theorem isGen_inter {X X' : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y') (hE : E.mem (Y ∩ Y')) :
    IsGen i j (X ∩ X') (Y ∩ Y') := by
  obtain ⟨hiXY, hjYX⟩ := h
  obtain ⟨hiX'Y', hjY'X'⟩ := h'
  have hj1 : j.rel (Y ∩ Y') X :=
    j.mono hjYX Set.inter_subset_left subset_rfl hE (j.rel_cod hjYX)
  have hj2 : j.rel (Y ∩ Y') X' :=
    j.mono hjY'X' Set.inter_subset_right subset_rfl hE (j.rel_cod hjY'X')
  have hjInter : j.rel (Y ∩ Y') (X ∩ X') := j.inter_right hj1 hj2
  have hDXX' : D.mem (X ∩ X') := j.rel_cod hjInter
  have hi1 : i.rel (X ∩ X') Y :=
    i.mono hiXY Set.inter_subset_left subset_rfl hDXX' (i.rel_cod hiXY)
  have hi2 : i.rel (X ∩ X') Y' :=
    i.mono hiX'Y' Set.inter_subset_right subset_rfl hDXX' (i.rel_cod hiX'Y')
  exact ⟨i.inter_right hi1 hi2, hjInter⟩

/-- **The image subdomain `D'`.** A `β`-set `Y` is a neighbourhood iff it generates some
`D`-neighbourhood; the master is `E`'s master. `isGen_inter` supplies condition (ii). -/
def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

/-- **`D' ◁ E`.** Same master (`rfl`); `D' ⊆ E` since a generator's `Y` is an `E`-neighbourhood; and
the consistency clause `inter_closed` is exactly `isGen_inter`. -/
theorem Dprime_subsystem : Dprime i j ◁ E where
  master_eq := rfl
  sub := by rintro Y ⟨X, hg⟩; exact i.rel_cod hg.1
  inter_closed := by
    rintro Y₁ Y₂ ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ hE
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hE⟩

/-- **Forward map of the isomorphism `D ≅ D'`.** `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` — the
generators of the members of `x`. (Needs `j ∘ i = I_D` for upward closure, via `isGen_mono`.) -/
def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

/-- **Inverse map of the isomorphism `D ≅ D'`.** `y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`. (Needs both
laws: `j ∘ i = I_D` for generator existence and `i ∘ j ⊆ I_E` for `isGen_mono'`.) -/
def ofEl (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E)
    (y : (Dprime i j).Element) : D.Element where
  mem X := ∃ Y, y.mem Y ∧ IsGen i j X Y
  sub := by rintro X ⟨Y, _, hg⟩; exact i.rel_dom hg.1
  master_mem := ⟨E.master, y.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁y, hg₁⟩ ⟨Y₂, hY₂y, hg₂⟩
    have hyInter : y.mem (Y₁ ∩ Y₂) := y.inter_mem hY₁y hY₂y
    have hEInter : E.mem (Y₁ ∩ Y₂) := (Dprime_subsystem i j).sub (y.sub hyInter)
    exact ⟨Y₁ ∩ Y₂, hyInter, isGen_inter i j hg₁ hg₂ hEInter⟩
  up_mem := by
    rintro X X' ⟨Y, hYy, hg⟩ hDX' hXX'
    obtain ⟨Y', hg'⟩ := isGen_exists i j hji hDX'
    have hYY' : Y ⊆ Y' := isGen_mono' i j hij hg hg' hXX'
    exact ⟨Y', y.up_mem hYy ⟨X', hg'⟩ hYY', hg'⟩

/-- **The domain isomorphism `D ≅ D'`** (Scott's "inclusion-preserving one-one correspondence").
Built from `toEl`/`ofEl`; the inverse laws and order-reflection come from generator uniqueness. -/
def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E → D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair

/-- **Proposition 6.12 + Lemma 6.15 packaged.** A subdomain relation `D ◁ E` is in particular a
witness of `D ⊴ E` (take `D' = D`). Together with `trianglelefteq_of_projectionPair`, this shows
`D ⊴ E` holds **iff** there is a projection pair `D ⇄ E`. -/
theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Proposition611.lean -/

/-!
# Lecture VI — Proposition 6.11 (Scott 1981, PRG-19): the subsystems of `E` form a domain

**Proposition 6.11.** For a given neighbourhood system `E`, the set of subsystems

`{D ∣ D ◁ E}`

forms a domain in its own right.

Scott derives this as a one-line corollary of the remark preceding it: *the union of a directed
family of subdomains of `E` is again a subdomain*. We make this precise using the project's
**abstract representation theorem** (Exercise 2.22, `Exercise222.reprIso`): a family `C` of sets
that is closed under (i) non-empty intersection and (ii) directed union is order-isomorphic to a
domain `|reprSystem C|` — exactly the route used for "the open sets form a domain" (Exercise 3.25)
and "the function space is a domain" (Exercise 3.27).

The faithful translation runs as follows. A subsystem `D ◁ E` is, by `NeighborhoodSystem.ext` and
the standing `D.master = E.master`, completely determined by its **family of neighbourhoods**
`{X ∣ D.mem X}`. So we represent the poset `({D ∣ D ◁ E}, ◁)` by the family

`subFam E = { {X ∣ D.mem X} ∣ D ◁ E } ⊆ 𝒫(𝒫(Δ))`,

ordered by `⊆`. By Scott's remark (`Subsystem.subsystem_iff_subset_of_common`) the subdomain
relation `◁` between two subsystems of `E` is just inclusion of their neighbourhood families, so
`({D ∣ D ◁ E}, ◁) ≃o (subFam E, ⊆)` (`subIso`). The two closure properties hold:

* **non-empty intersections** (`subFam_sInter_mem`): the intersection of a non-empty family of
  subdomains is the subdomain `interSys` whose neighbourhoods are the common neighbourhoods;
* **directed unions** (`subFam_sUnion_mem`): the union of a directed family of subdomains is the
  subdomain `unionSys` (Scott's remark) — directedness is used exactly to verify closure under
  consistent intersection.

The capstone `subsystemReprIso : {D ∣ D ◁ E} ≃o |reprSystem (subFam E) …|` composes `subIso` with
`Exercise222.reprIso`, witnessing that the subsystems of `E` *are* (isomorphic to) a domain.

**Axioms.** The combinatorial heart — `subFam` and its closure under intersection/union, the
subsystem constructions `interSys`/`unionSys`, and `subIso` — is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`). The final `subsystemReprIso` inherits `Classical.choice`
solely through Exercise 2.22's representation isomorphism (the "for set theorists" exercise, which
picks witnesses of non-emptiness and uses finite-set induction), exactly as Exercise 3.27 does.
-/

namespace Scott1980.Neighborhood.Proposition611

open Scott1980.Neighborhood NeighborhoodSystem Set Scott1980.Neighborhood.Exercise222

variable {α : Type*}

/-! ### The representing family of neighbourhood-sets. -/

/-- The family of **neighbourhood-sets of subdomains of `E`**: a set of subsets of `Δ` lies in
`subFam E` exactly when it is `{X ∣ D.mem X}` for some subsystem `D ◁ E`. This is the concrete
family of sets that, by Exercise 2.22, represents `{D ∣ D ◁ E}` as a domain. -/
def subFam (E : NeighborhoodSystem α) : Set (Set (Set α)) :=
  {𝒮 | ∃ D : NeighborhoodSystem α, D ◁ E ∧ 𝒮 = {X | D.mem X}}

/-- The master `Δ = E.master` belongs to the neighbourhood-set of any subdomain (a subsystem shares
`E`'s master and contains it). -/
theorem subFam_master_mem (E : NeighborhoodSystem α) {𝒮 : Set (Set α)}
    (h : 𝒮 ∈ subFam E) : E.master ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  rw [← hD.master_eq]
  exact D.master_mem

/-- Every member of a subdomain's neighbourhood-set is an `E`-neighbourhood (`D ⊆ E`). -/
theorem subFam_mem_E (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) : E.mem X := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.sub hX

/-- Consistency is inherited from `E` (Definition 6.10's essential clause): if `X, Y` lie in a
subdomain's neighbourhood-set and `X ∩ Y ∈ E`, then `X ∩ Y` lies in it too. -/
theorem subFam_inter_closed (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X Y : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : E.mem (X ∩ Y)) : X ∩ Y ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.inter_closed hX hY hXY

/-- `subFam E` is non-empty: `E` itself is a subsystem (`Subsystem.refl`), so its own
neighbourhood-set `{X ∣ E.mem X}` is a member. -/
theorem subFam_nonempty (E : NeighborhoodSystem α) : (subFam E).Nonempty :=
  ⟨{X | E.mem X}, E, Subsystem.refl E, rfl⟩

/-! ### Closure under non-empty intersection. -/

/-- The **intersection subdomain** of a non-empty family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are the sets common to *every* member of `ℱ`. -/
def interSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : NeighborhoodSystem α where
  mem X := ∀ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := fun 𝒮 h𝒮 => subFam_master_mem E (hℱ h𝒮)
  inter_mem := by
    intro X Y Z hX hY hZ hsub 𝒮 h𝒮
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮) (hY 𝒮 h𝒮)
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮) (hZ 𝒮 h𝒮)
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) (E.inter_mem hEX hEY hEZ hsub)
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮))

/-- The intersection subdomain is a subsystem of `E`. -/
theorem interSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : interSys E ℱ hne hℱ ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
  inter_closed := by
    intro X Y hX hY hEXY 𝒮 h𝒮
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) hEXY

/-- The neighbourhood-set of the intersection subdomain is exactly `⋂₀ ℱ`. -/
theorem interSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) :
    {X | (interSys E ℱ hne hℱ).mem X} = ⋂₀ ℱ := by
  ext X
  exact Set.mem_sInter.symm

/-- **Closure under non-empty intersection** (Exercise 2.22's hypothesis (i)). -/
theorem subFam_sInter_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : ⋂₀ ℱ ∈ subFam E :=
  ⟨interSys E ℱ hne hℱ, interSys_subsystem E ℱ hne hℱ, (interSys_nbset E ℱ hne hℱ).symm⟩

/-! ### Closure under directed union (Scott's remark). -/

/-- The **union subdomain** of a directed family `ℱ` of subdomain neighbourhood-sets: its
neighbourhoods are those lying in *some* member of `ℱ`. Directedness is what makes this closed
under consistent intersection. -/
def unionSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    NeighborhoodSystem α where
  mem X := ∃ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := by
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact ⟨𝒮, h𝒮, subFam_master_mem E (hℱ h𝒮)⟩
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮z, h𝒮z, hZz⟩ := hZ
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    have hXs : X ∈ 𝒮s := hxs hXx
    have hYs : Y ∈ 𝒮s := hys hYy
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮s) hXs
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮s) hYs
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮z) hZz
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) hXs hYs (E.inter_mem hEX hEY hEZ hsub)⟩
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) hX𝒮)

/-- The union subdomain is a subsystem of `E` (Scott's remark: the directed union of subdomains is
again a subdomain). -/
theorem unionSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    unionSys E ℱ hne hℱ hdir ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact subFam_mem_E E (hℱ h𝒮) hX𝒮
  inter_closed := by
    intro X Y hX hY hEXY
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) (hxs hXx) (hys hYy) hEXY⟩

/-- The neighbourhood-set of the union subdomain is exactly `⋃₀ ℱ`. -/
theorem unionSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    {X | (unionSys E ℱ hne hℱ hdir).mem X} = ⋃₀ ℱ := by
  ext X
  exact Set.mem_sUnion.symm

/-- **Closure under directed union** (Exercise 2.22's hypothesis (ii)) — Scott's remark. -/
theorem subFam_sUnion_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    ⋃₀ ℱ ∈ subFam E :=
  ⟨unionSys E ℱ hne hℱ hdir, unionSys_subsystem E ℱ hne hℱ hdir,
    (unionSys_nbset E ℱ hne hℱ hdir).symm⟩

/-! ### The poset of subsystems and its representation. -/

/-- The subsystems of `E`, ordered by the **subdomain relation** `◁`, form a partial order
(reflexive, transitive, antisymmetric — Definition 6.10's API). -/
instance subPartialOrder (E : NeighborhoodSystem α) :
    PartialOrder {D : NeighborhoodSystem α // D ◁ E} where
  le D₀ D₁ := D₀.1 ◁ D₁.1
  le_refl D := Subsystem.refl D.1
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := Subtype.ext (h₁.antisymm h₂)

/-- Rebuild a subsystem of `E` from its neighbourhood-set `𝒮 ∈ subFam E`. The data (the `mem`
predicate `· ∈ 𝒮` and the master `E.master`) depends only on `𝒮`; the proof obligations are
discharged from `subFam` membership. -/
def ofMem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    NeighborhoodSystem α where
  mem X := X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := subFam_master_mem E h
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    exact subFam_inter_closed E h hX hY
      (E.inter_mem (subFam_mem_E E h hX) (subFam_mem_E E h hY) (subFam_mem_E E h hZ) hsub)
  sub_master := fun hX => E.sub_master (subFam_mem_E E h hX)

/-- `ofMem` lands in the subsystems of `E`. -/
theorem ofMem_subsystem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    ofMem E 𝒮 h ◁ E where
  master_eq := rfl
  sub := subFam_mem_E E h
  inter_closed := subFam_inter_closed E h

/-- **The poset of subsystems is the family `subFam E`.** The subsystems of `E`, ordered by `◁`,
are order-isomorphic to `subFam E` ordered by `⊆`. A subsystem is sent to its family of
neighbourhoods `{X ∣ D.mem X}`, and recovered by `ofMem`; order is preserved and reflected by
Scott's remark `Subsystem.subsystem_iff_subset_of_common`. -/
def subIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o {𝒮 : Set (Set α) // 𝒮 ∈ subFam E} where
  toFun D := ⟨{X | D.1.mem X}, ⟨D.1, D.2, rfl⟩⟩
  invFun 𝒮 := ⟨ofMem E 𝒮.1 𝒮.2, ofMem_subsystem E 𝒮.1 𝒮.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    apply NeighborhoodSystem.ext
    · intro X; exact Iff.rfl
    · exact D.2.master_eq.symm
  right_inv := by
    intro 𝒮
    apply Subtype.ext
    ext X
    exact Iff.rfl
  map_rel_iff' := by
    intro a b
    show ({X | a.1.mem X} : Set (Set α)) ⊆ {X | b.1.mem X} ↔ a.1 ◁ b.1
    constructor
    · intro hsub
      refine (Subsystem.subsystem_iff_subset_of_common a.2 b.2).mpr ?_
      intro X hX
      exact hsub hX
    · intro hsub X hX
      exact hsub.sub hX

/-- **Proposition 6.11 (Scott 1981, PRG-19).** For a neighbourhood system `E`, the set of
subsystems `{D ∣ D ◁ E}`, ordered by the subdomain relation `◁`, *forms a domain in its own
right*: it is order-isomorphic to the domain `|reprSystem (subFam E) …|` produced by the abstract
representation theorem (Exercise 2.22), using that `subFam E` is closed under non-empty
intersections (`subFam_sInter_mem`) and directed unions (Scott's remark, `subFam_sUnion_mem`). -/
def subsystemReprIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element :=
  (subIso E).trans
    (reprIso (subFam E) (subFam_sInter_mem E) (subFam_nonempty E) (subFam_sUnion_mem E)).symm

end Scott1980.Neighborhood.Proposition611

/-! ### Inlined from Scott1980/Neighborhood/Proposition612.lean -/

/-!
# Lecture VI — Proposition 6.12 (Scott 1981, PRG-19): a subdomain yields a projection pair

**Proposition 6.12.** If `D ◁ E`, then there exists a *projection pair* of approximable mappings

`i : D → E` and `j : E → D`

with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`, determined as element-wise functions by

`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}` and `j(y) = y ∩ D`.

Scott leaves the proof "for the exercises". We give it directly at the level of the neighbourhood
relations (Definition 2.1), which keeps everything **choice-free**.

* The injection `i` (`Subsystem.inj`) is the relation `X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y` — it sends a
  `D`-neighbourhood to all the `E`-neighbourhoods it refines.
* The projection `j` (`Subsystem.proj`) is the relation `Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X` — it
  intersects an `E`-element with `D`.

The two laws are then short relational calculations:

* `Subsystem.proj_comp_inj : j ∘ i = I_D`. Both round trips factor as `X ⊆ Y ⊆ Z`, giving exactly
  the identity relation `X ⊆ Z` on `D`. (Proved with the **choice-free** relational extensionality
  `ApproximableMap.ext`.)
* `Subsystem.inj_comp_proj_le : i ∘ j ⊆ I_E`. A round trip `Y ⊆ X ⊆ Y'` through a common
  `D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E` — but not conversely, so this direction is
  only an inclusion. The crucial clause of `D ◁ E` (consistency inherited from `E`) is what makes
  `j`'s output-intersection law hold (`inter_right`).

The element-wise descriptions Scott records are `Subsystem.toElementMap_inj` and
`Subsystem.toElementMap_proj`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The injection `i : D → E` of Proposition 6.12.** As a neighbourhood relation,
`X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y`. Element-wise (see `toElementMap_inj`) it is Scott's
`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
def inj (h : D ◁ E) : ApproximableMap D E where
  rel X Y := D.mem X ∧ E.mem Y ∧ X ⊆ Y
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨D.master_mem, E.master_mem, h.master_eq.subset⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, E.inter_mem hY hY' (h.sub hX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **The projection `j : E → D` of Proposition 6.12.** As a neighbourhood relation,
`Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X`. Element-wise (see `toElementMap_proj`) it is Scott's
`j(y) = y ∩ D`. The `inter_right` law is exactly where Definition 6.10's consistency clause
(`inter_closed`) is used. -/
def proj (h : D ◁ E) : ApproximableMap E D where
  rel Y X := E.mem Y ∧ D.mem X ∧ Y ⊆ X
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨E.master_mem, D.master_mem, h.master_eq.symm.subset⟩
  inter_right := by
    rintro Y X X' ⟨hY, hX, hYX⟩ ⟨_, hX', hYX'⟩
    have hEinter : E.mem (X ∩ X') :=
      E.inter_mem (h.sub hX) (h.sub hX') hY (Set.subset_inter hYX hYX')
    exact ⟨hY, h.inter_closed hX hX' hEinter, Set.subset_inter hYX hYX'⟩
  mono := by
    rintro Y Y' X X' ⟨_, _, hYX⟩ hY'Y hXX' hY' hX'
    exact ⟨hY', hX', (hY'Y.trans hYX).trans hXX'⟩

@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

/-- **Element-wise description of `i` (Scott's equation).** `i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`. -/
theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

/-- **Proposition 6.12, first law: `j ∘ i = I_D`.** Each side relates `X` and `Z` exactly when
`X, Z ∈ D` and `X ⊆ Z`: a round trip `X ⊆ Y ⊆ Z` through an `E`-neighbourhood `Y` collapses to
`X ⊆ Z` (forward), and `X ⊆ Z` factors through `Y = Z` (backward). Proved relationally, so
**choice-free**. -/
theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

/-- **Proposition 6.12, second law: `i ∘ j ⊆ I_E`.** A round trip `Y ⊆ X ⊆ Y'` through a common
`D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`. The reverse inclusion fails (not every
consistent `E`-pair factors through `D`), so this is an inclusion of relations, not an equality. -/
theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

/-- **A projection pair (Definition 6.13 vocabulary).** Bundles Scott's `i, j` together with the two
laws, ready for reuse in monotone/continuous-on-domains functors and the existence Theorem 6.14. -/
structure ProjectionPair (D E : NeighborhoodSystem α) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

/-- **Proposition 6.12 (Scott 1981, PRG-19).** Every subdomain relation `D ◁ E` gives rise to a
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. -/
def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Definition613.lean -/

/-!
# Lecture VI — Definition 6.13 (Scott 1981, PRG-19): functors *monotone / continuous on domains*

> **DEFINITION 6.13.** A functor `T` is *monotone on domains* iff whenever `D ◁ E`, then not only do
> we have `T(D) ◁ T(E)` but the projection pair `i, j` of 6.12 is mapped to the same kind of
> projection pair `T(i), T(j)`. A monotone functor is *continuous on domains* iff whenever `E` is a
> domain, then the mapping `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is approximable.

This is the second of Scott's two continuity conditions on a functor (the first being Definition 6.8,
*continuous on maps*). Together with a generating set `Γ` they power the existence Theorem 6.14
(initial `T`-algebras as iterated-functor colimits `𝒟 = ⋃ₙ Tⁿ({Γ})`).

## What the formalization uses

* **The functor.** `T` is an `Endofunctor DomainObj` (Definition 6.3), acting on objects (`T.obj`)
  and on the approximable maps between them (`T.map`).
* **The subdomain relation `◁`.** Definition 6.10 (`Subsystem`), between two systems over the *same*
  token type, with the projection pair `i = Subsystem.inj`, `j = Subsystem.proj` of Proposition 6.12.
* **The domain of subsystems `{D ∣ D ◁ E}`.** Proposition 6.11 shows this *is* a domain; here it is
  the subtype `{D // D ◁ E}` and the directed-union sups are the union subsystems `unionSys`.

### The carrier-type subtlety, and how it is handled

`D ◁ E` requires `D, E` to be systems over a *common* token type `α`. The abstract functor `T` need
not preserve token types: `T.obj ⟨α, D⟩` and `T.obj ⟨α, E⟩` may have different carriers. So
"`T(D) ◁ T(E)`" only makes sense once we *assert* that `T` preserves the token type along `◁`, i.e.
once the carriers of the two images agree. **Monotone on domains** therefore packages, for each
`h : D ◁ E`:

* `carrier_eq`: the two image carriers coincide;
* `sub`: the transported subdomain relation `T(D) ◁ T(E)`;
* `inj_heq`/`proj_heq`: Scott's "the projection pair `i, j` is mapped to `T(i), T(j)`", i.e. the
  canonical 6.12 pair of `T(D) ◁ T(E)` is exactly `(T.map i, T.map j)` (stated up to the carrier
  transport, hence `HEq`).

**Continuous on domains** then adds Scott's approximability of `λD. T(D)`, rendered in the concrete
neighbourhood framework as *preservation of directed unions of subsystems*: for any directed family
`ℱ` of subsystems of `E` whose union is the subsystem `U`, the (target-side) neighbourhood family of
`T(U)` is the union of those of the `T(D)`. This is exactly the continuity Scott invokes in the proof
of 6.14 (`T(⋃ₙ Tⁿ{Γ}) = ⋃ₙ T(Tⁿ⁺¹{Γ})`).

The identity functor is monotone and continuous on domains (`monotoneOnDomains_id`,
`continuousOnDomains_id`), witnessing non-vacuity. Everything is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

universe w

/-! ### Monotone on domains -/

/-- **Definition 6.13, monotone part (pointwise).** Given a subdomain relation `h : D ◁ E`, the data
witnessing that the functor `T` carries it to `T(D) ◁ T(E)` *and* carries the projection pair `i, j`
of 6.12 to the projection pair of `T(D) ◁ T(E)`.

Because `T` may change the token type, the two image systems live a priori over different carriers;
`carrier_eq` records that they coincide, `sub` is the resulting subdomain relation (with `T(E)`'s
system transported into `T(D)`'s carrier), and `inj_heq`/`proj_heq` say the canonical 6.12 maps of
`sub` are `T(i)` and `T(j)` (up to that transport, hence `HEq`). -/
structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  /-- The two image carriers coincide, so `T(D) ◁ T(E)` can be stated. -/
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  /-- The image subdomain relation `T(D) ◁ T(E)` (with `T(E)`'s system carried into `T(D)`'s
  carrier). -/
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  /-- The injection of `T(D) ◁ T(E)` is `T(i)` (Scott: the pair is mapped to `T(i), T(j)`). -/
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  /-- The projection of `T(D) ◁ T(E)` is `T(j)`. -/
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

/-- **Definition 6.13 (Scott 1981, PRG-19), monotone on domains.** A functor `T` is *monotone on
domains* iff every subdomain relation `D ◁ E` is carried to a subdomain relation `T(D) ◁ T(E)` whose
projection pair is `(T(i), T(j))` — see `MonotoneAt`. -/
def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h

/-- The **identity functor is monotone on domains**: it fixes objects and maps, so `T(D) ◁ T(E)` is
just `D ◁ E` and the projection pair is unchanged. -/
theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩

/-! ### Continuous on domains -/

/-- The **target-side neighbourhood family** of the image `T(D)` of a subsystem `h : D ◁ E`, viewed
over `T(E)`'s carrier (using `MonotoneAt.carrier_eq` to transport neighbourhoods of `T(D)` to that
carrier). This is the data on which "`λD. T(D)` is approximable" is expressed. -/
def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}

/-- **Definition 6.13 (Scott 1981, PRG-19), continuous on domains.** A monotone functor `T` is
*continuous on domains* iff `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is approximable. In the
neighbourhood framework this is *preservation of directed unions of subsystems*: for any non-empty
directed family `ℱ` of subsystems of `E` whose union is the subsystem `U` (`hU`), the target-side
neighbourhood family of `T(U)` is the union of those of the `T(D)` for `D ∈ ℱ`. -/
def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)

/-- The **identity functor is continuous on domains**: `targetFam` reduces to the plain neighbourhood
family, so directed-union preservation is exactly the hypothesis `hU` that `U` is the union. -/
theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise619PartB.lean -/

/-!
# Exercise 6.19 (Scott 1981, PRG-19, §6) — Part B: the functor algebra

> … Now generate all constructs `T(X)` formed by the constants (that is, `T(X) = 𝒟` for a fixed `𝒟`),
> by the identity (`T(X) = X`), and by sums and products (`T₀(X) + T₁(X)`, etc.). Show that these are
> all functors, continuous on maps, and monotone and continuous on domains.

This module formalizes **Part B**: the closed family of constructs `T(X)` over Scott's *uniform*
category of Exercise 6.19 — neighbourhood systems on `Δ ⊆ {0,1}*` with `∅ ∉ 𝒟` (the standing
hypothesis that makes the token-level sum `sumTok`/product `prodTok` of Part A genuine
*endo*-operations) and **strict** approximable maps.

## Contents

* `ScottSys` — an object of Scott's category: an `∅`-free neighbourhood system over `Str = {0,1}*`.
* The object actions `ScottSys.sum`/`ScottSys.prod` (Part A's `sumTok`/`prodTok`, repackaged so they
  stay inside the category) and the constant/identity objects.
* The **functorial action on maps**: `sumMapTok f₀ f₁ : (𝒟₀+𝒟₁) → (ℰ₀+ℰ₁)` and
  `prodMapTok f₀ f₁ : (𝒟₀×𝒟₁) → (ℰ₀×ℰ₁)`, each an approximable map, with strictness preservation
  (`sumMapTok` is *always* strict; `prodMapTok` is strict when both factors are).
* The **bifunctor laws**: both actions preserve identities and composition
  (`sumMapTok_id`/`sumMapTok_comp`, `prodMapTok_id`/`prodMapTok_comp`).
* The functor-expression algebra `FExpr` (constants, identity, sum, product), its object action
  `FExpr.obj`, its action on maps `FExpr.map`.

Scott asks to show these constructs are **all functors, continuous on maps, and monotone and
continuous on domains**; each is established here:

* **functors** — `FExpr.map_id` (`T(I)=I`) and `FExpr.map_comp` (`T(g∘f)=T(g)∘T(f)`), by induction;
  plus `FExpr.map_isStrict` (so `T` restricts to Scott's strict-map category).
* **continuous on maps** — `FExpr.map_mono` (a sharper map gives a sharper image) and
  `FExpr.map_continuous` (`λf. T(f)` preserves directed unions of maps); together these are exactly
  approximability of `λf. T(f)` (Exercise 2.13).
* **monotone on domains** — `FExpr.obj_subsystem` (`D ◁ E ⟹ T(D) ◁ T(E)`).
* **continuous on domains** — `FExpr.obj_continuous` (`λD. T(D)` preserves directed unions of
  subsystems, the form Scott uses in Theorem 6.14).

Because every construct stays over the single token type `{0,1}*`, the subdomain relation `◁` is
between systems on a common carrier, so the domain conditions need no carrier transport (unlike the
universe-polymorphic `Endofunctor DomainObj` form of Definitions 6.8/6.13).

This module also formalizes **Exercise 6.20**: writing `tok(𝒟) = 𝒟.master` for the underlying token
set and `{Γ}` for the one-neighbourhood system `singletonSys Γ`, the function `λΓ. tok(T({Γ}))` is
computed by the token-level recursion `mFun T` (`mFun_eq_master`), shown monotone (`mFun_mono`) and
continuous (`mFun_continuous`) on the domain `{Γ ∣ Λ ∈ Γ}`. Its least fixed point — the explicit
Kleene union `⋃ₙ mFunⁿ({Λ})` — gives a `Γ = tok(T({Γ}))` (`exists_tok_fixedPoint`), whence
`{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the hypothesis Theorem 6.14 needs.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise619
open Scott1980.Neighborhood.Example62 Scott1980.Neighborhood.ExampleB
open Scott1980.Neighborhood.Exercise510

namespace Exercise619

/-! ## Objects of Scott's category: `∅`-free systems over `{0,1}*` -/

/-- **An object of the Exercise 6.19 category.** An `∅`-free neighbourhood system over
`Str = {0,1}*` (`ne`: every neighbourhood is non-empty, Scott's `∅ ∉ 𝒟`). -/
structure ScottSys where
  /-- The underlying neighbourhood system on `{0,1}*`. -/
  sys : NeighborhoodSystem Str
  /-- `∅ ∉ 𝒟`: every neighbourhood is non-empty. -/
  ne : ∀ X, sys.mem X → X.Nonempty

/-- The **sum object** `𝒟₀ + 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.sum (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨sumTok A₀.sys A₁.sys A₀.ne A₁.ne, sumTok_nonempty⟩

/-- The **product object** `𝒟₀ × 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.prod (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨prodTok A₀.sys A₁.sys, prodTok_nonempty⟩

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- A non-empty `b`-tagged copy can never sit inside a `b'`-tagged copy for `b ≠ b'`. -/
theorem embBit_not_subset_cross {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty)
    (hsub : embBit b X ⊆ embBit b' Y) : False := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨w', he, -⟩ := hsub ⟨t, rfl, ht⟩
  simp only [List.cons.injEq] at he
  exact h he.1

/-! ## The functorial action of sum on maps -/

/-- **`f₀ + f₁`, the action of the sum functor on (approximable) maps.** It carries the master to the
master (so it is strict), a left copy `0X` to `0X'` whenever `X f₀ X'`, and a right copy `1Y` to
`1Y'` whenever `Y f₁ Y'`. -/
def sumMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.sum A₁).sys (B₀.sum B₁).sys where
  rel W W' :=
    ((sumTok A₀.sys A₁.sys A₀.ne A₁.ne).mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩ | ⟨Y, Y', hrel, rfl, -⟩)
    · exact hW
    · exact Or.inr (Or.inl ⟨X, f₀.rel_dom hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, f₁.rel_dom hrel, rfl⟩)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩ | ⟨Y, Y', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X', f₀.rel_cod hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y', f₁.rel_cod hrel, rfl⟩)
  master_rel := Or.inl ⟨(A₀.sum A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩ | ⟨Y, Y', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hWeq, by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hWeq, by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, rfl, embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · -- output was the master; a blunter neighbourhood must again be the master.
      exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.sum B₁).sys.sub_master hZ') hZZ'⟩
    · -- input `0X`, output `0X'`. The sharper input `W''` and blunter output `Z'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · -- input `1Y`, output `1Y'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃, rfl, rfl⟩)

/-- **`sumMapTok` is strict** for *any* component maps: the master input `Λ` (the only neighbourhood
containing the empty string) relates only to the output master. -/
theorem sumMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (sumMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y0, Y', -, heq, -⟩)
  · rfl
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit false X := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit true Y0 := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit

/-! ## The functorial action of product on maps -/

/-- **`f₀ × f₁`, the action of the product functor on (approximable) maps.** A product
neighbourhood `{Λ} ∪ 0X ∪ 1Y` is sent to `{Λ} ∪ 0X' ∪ 1Y'` whenever `X f₀ X'` and `Y f₁ Y'`. -/
def prodMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.prod A₁).sys (B₀.prod B₁).sys where
  rel W W' := ∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧
    W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y'
  rel_dom := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, rfl, -⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_dom h0) (f₁.rel_dom h1)
  rel_cod := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, -, rfl⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_cod h0) (f₁.rel_cod h1)
  master_rel :=
    ⟨A₀.sys.master, A₁.sys.master, B₀.sys.master, B₁.sys.master,
      f₀.master_rel, f₁.master_rel, rfl, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ ⟨X₂, Y₂, X'₂, Y'₂, h0₂, h1₂, hWeq, rfl⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right h0 h0₂, f₁.inter_right h1 h1₂, rfl,
      prodTokNbhd_inter X' X'₂ Y' Y'₂⟩
  mono := by
    rintro W W'' Z Z' ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ hWW hZZ' hW'' hZ'
    obtain ⟨X₂, Y₂, hX₂, hY₂, rfl⟩ := hW''
    obtain ⟨X'₃, Y'₃, hX'₃, hY'₃, rfl⟩ := hZ'
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hWW
    obtain ⟨hsX', hsY'⟩ := prodTokNbhd_subset_iff.mp hZZ'
    exact ⟨X₂, Y₂, X'₃, Y'₃, f₀.mono h0 hsX hsX' hX₂ hX'₃, f₁.mono h1 hsY hsY' hY₂ hY'₃, rfl, rfl⟩

/-- **`prodMapTok` is strict** exactly when both components are strict. -/
theorem prodMapTok_isStrict {f₀ : ApproximableMap A₀.sys B₀.sys}
    {f₁ : ApproximableMap A₁.sys B₁.sys} (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) :
    IsStrict (prodMapTok f₀ f₁) := by
  rintro Y ⟨X, Y0, X', Y', h0, h1, hWeq, rfl⟩
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
  rw [hf₀ h0, hf₁ h1]
  rfl

/-! ## The bifunctor laws: identities and composition are preserved -/

/-- **`(I_{𝒟₀} + I_{𝒟₁}) = I_{𝒟₀+𝒟₁}`.** -/
theorem sumMapTok_id :
    sumMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.sum A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, (A₀.sum A₁).sys.sub_master hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

/-- **`(g₀ ∘ f₀) + (g₁ ∘ f₁) = (g₀ + g₁) ∘ (f₀ + f₁)`.** -/
theorem sumMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    sumMapTok (g₀.comp f₀) (g₁.comp f₁) = (sumMapTok g₀ g₁).comp (sumMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩ | ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.sum B₁).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, rfl, rfl⟩)⟩
    · exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩ | ⟨Y, Y', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩ | ⟨Y, Y', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩ | ⟨Y₂, Y'', hg, heq, -⟩
      · exact Or.inl ⟨Or.inr (Or.inl ⟨X, f₀.rel_dom hf, rfl⟩), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, -⟩ | ⟨Y₂, Y'', hg, heq, rfl⟩
      · exact Or.inl ⟨Or.inr (Or.inr ⟨Y, f₁.rel_dom hf, rfl⟩), rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, rfl, rfl⟩)

/-- **`(I_{𝒟₀} × I_{𝒟₁}) = I_{𝒟₀×𝒟₁}`.** -/
theorem prodMapTok_id :
    prodMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.prod A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩, rfl, rfl⟩

/-- **`(g₀ ∘ f₀) × (g₁ ∘ f₁) = (g₀ × g₁) ∘ (f₀ × f₁)`.** -/
theorem prodMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    (g₀ : ApproximableMap B₀.sys C₀.sys) (g₁ : ApproximableMap B₁.sys C₁.sys) :
    prodMapTok (g₀.comp f₀) (g₁.comp f₁) = (prodMapTok g₀ g₁).comp (prodMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩
    exact ⟨prodTokNbhd X' Y', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩,
      ⟨X', Y', X'', Y'', hg0, hg1, rfl, rfl⟩⟩
  · rintro ⟨W', ⟨X, Y, X', Y', hf0, hf1, rfl, rfl⟩, ⟨X₂, Y₂, X'', Y'', hg0, hg1, hWeq, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩, rfl, rfl⟩

/-! ## The functor-expression algebra `T(X)` and the functor laws

*"Generate all constructs `T(X)` formed by the constants (`T(X) = 𝒟`), by the identity (`T(X) = X`),
and by sums and products."* -/

/-- **The functor-expression algebra.** A `T(X)` built from constants, the identity, and binary sums
and products — Scott's closed family of constructs. -/
inductive FExpr where
  /-- The constant functor `T(X) = 𝒟` at a fixed object `𝒟`. -/
  | const : ScottSys → FExpr
  /-- The identity functor `T(X) = X`. -/
  | var : FExpr
  /-- The sum `T₀(X) + T₁(X)`. -/
  | sum : FExpr → FExpr → FExpr
  /-- The product `T₀(X) × T₁(X)`. -/
  | prod : FExpr → FExpr → FExpr

/-- **The action of `T` on objects.** -/
def FExpr.obj : FExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum T₀ T₁, X => (T₀.obj X).sum (T₁.obj X)
  | .prod T₀ T₁, X => (T₀.obj X).prod (T₁.obj X)

/-- **The action of `T` on (approximable) maps.** Constants act by the identity, the identity functor
acts by `f` itself, and sums/products act by the bifunctorial combinators `sumMapTok`/`prodMapTok`. -/
def FExpr.map : (T : FExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum T₀ T₁, _, _, f => sumMapTok (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f => prodMapTok (T₀.map f) (T₁.map f)

/-- **Every `T` preserves strictness** (so it restricts to Scott's category of strict maps): `T(f)`
is strict whenever `f` is (and constants/sums are strict unconditionally). -/
theorem FExpr.map_isStrict : (T : FExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum T₀ T₁, _, _, f, _ => sumMapTok_isStrict (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f, hf =>
      prodMapTok_isStrict (T₀.map_isStrict f hf) (T₁.map_isStrict f hf)

/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** Every construct `T` preserves identities. -/
theorem FExpr.map_id : (T : FExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const D, _ => rfl
  | .var, _ => rfl
  | .sum T₀ T₁, X => by
      show sumMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).sum (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, sumMapTok_id]
  | .prod T₀ T₁, X => by
      show prodMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).prod (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, prodMapTok_id]

/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)`.** Every construct `T` preserves composition; together
with `map_id` this shows *these are all functors*. -/
theorem FExpr.map_comp : (T : FExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    (g : ApproximableMap Y.sys Z.sys) → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _ => rfl
  | .sum T₀ T₁, _, _, _, f, g => by
      show sumMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (sumMapTok (T₀.map g) (T₁.map g)).comp (sumMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, sumMapTok_comp]
  | .prod T₀ T₁, _, _, _, f, g => by
      show prodMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (prodMapTok (T₀.map g) (T₁.map g)).comp (prodMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, prodMapTok_comp]

/-! ## Continuous on maps — the monotone half

Scott's *continuous on maps* (Definition 6.8) requires `λf. T(f)` to be approximable on the strict
function space; here we record its **monotonicity** (the order half of approximability — a sharper map
yields a sharper image), proved compositionally from the bifunctor combinators. -/

/-- `sumMapTok` is monotone in both arguments. -/
theorem sumMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    sumMapTok f₀ f₁ ≤ sumMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, rfl, rfl⟩)

/-- `prodMapTok` is monotone in both arguments. -/
theorem prodMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    prodMapTok f₀ f₁ ≤ prodMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' ⟨X, Y, X', Y', hr0, hr1, rfl, rfl⟩
  exact ⟨X, Y, X', Y', h0 X X' hr0, h1 Y Y' hr1, rfl, rfl⟩

/-- **`λf. T(f)` is monotone.** A sharper map `f ≤ f'` is sent to a sharper image `T(f) ≤ T(f')` —
the monotonicity half of *continuous on maps*. -/
theorem FExpr.map_mono : (T : FExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum T₀ T₁, _, _, _, _, h => sumMapTok_mono (T₀.map_mono h) (T₁.map_mono h)
  | .prod T₀ T₁, _, _, _, _, h => prodMapTok_mono (T₀.map_mono h) (T₁.map_mono h)

/-! ## Monotone on domains

Scott's *monotone on domains* (Definition 6.13): a subdomain relation `D ◁ E` is carried to
`T(D) ◁ T(E)`. Because every construct here stays over the single token type `{0,1}*`, the relation is
between systems on a common carrier (no transport needed), and the bifunctor combinators carry `◁`
componentwise. -/

/-- The sum carries the subsystem relation componentwise: `𝒟₀ ◁ ℰ₀` and `𝒟₁ ◁ ℰ₁` give
`𝒟₀+𝒟₁ ◁ ℰ₀+ℰ₁`. -/
theorem sumTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.sum A₁).sys ◁ (B₀.sum B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩) (rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (sumTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.sum B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (sumTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt), rfl⟩)

/-- The product carries the subsystem relation componentwise. -/
theorem prodTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.prod A₁).sys ◁ (B₀.prod B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W ⟨X, Y, hX, hY, rfl⟩
    exact ⟨X, Y, h0.sub hX, h1.sub hY, rfl⟩
  · rintro W W' ⟨X, Y, hX, hY, rfl⟩ ⟨X', Y', hX', hY', rfl⟩ hInt
    rw [prodTokNbhd_inter] at hInt ⊢
    obtain ⟨X'', Y'', hX'', hY'', heq⟩ := hInt
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
    exact ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hX'', h1.inter_closed hY hY' hY'', rfl⟩

/-- **`λX. T(X)` is monotone on domains.** Whenever `X ◁ Y` we have `T(X) ◁ T(Y)`. -/
theorem FExpr.obj_subsystem : (T : FExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum T₀ T₁, _, _, h => sumTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)
  | .prod T₀ T₁, _, _, h => prodTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)

/-! ## Continuous on domains

Scott's *continuous on domains* (Definition 6.13): `λD. T(D)` preserves directed unions of
subsystems. Concretely, if `U` is the union of a non-empty `◁`-directed family `ℱ` of subsystems of
`U`, then every neighbourhood of `T(U)` already appears in some `T(D)` with `D ∈ ℱ` (and conversely).
The forward direction is by induction; the products use directedness to merge the two component
witnesses into a single `D`. -/

/-- Forward direction of continuity on domains: a neighbourhood of `T(U)` is a neighbourhood of some
`T(D)` with `D ∈ ℱ`. -/
theorem FExpr.obj_continuous_mp : (T : FExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((FExpr.sum T₀ T₁).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod T₀ T₁, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := T₀.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := T₁.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (T₀.obj_subsystem hr1).sub hXD, (T₁.obj_subsystem hr2).sub hYD, rfl⟩

/-- **`λD. T(D)` is continuous on domains.** For a non-empty `◁`-directed family `ℱ` of subsystems of
`U` whose union is `U`, the neighbourhood family of `T(U)` is the union of those of the `T(D)`. -/
theorem FExpr.obj_continuous (T : FExpr) {ℱ : Set ScottSys} {U : ScottSys}
    (hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ) (hne : ℱ.Nonempty)
    (hsub : ∀ D ∈ ℱ, D.sys ◁ U.sys) (hU : ∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X)
    (W : Set Str) : (T.obj U).sys.mem W ↔ ∃ D ∈ ℱ, (T.obj D).sys.mem W := by
  refine ⟨T.obj_continuous_mp hdir hne hsub hU, ?_⟩
  rintro ⟨D, hD, hmem⟩
  exact (T.obj_subsystem (hsub D hD)).sub hmem

/-! ## Continuous on maps — full directed-sup preservation

Scott's *continuous on maps* (Definition 6.8): `λf. T(f)` is approximable, equivalently (Exercise
2.13) it is continuous — monotone (`map_mono`) and preserving directed unions of maps. If `f` is the
pointwise union of a non-empty directed family `gᵢ`, then `T(f)` is the pointwise union of the
`T(gᵢ)`. The products use directedness to merge the two component witnesses. -/

/-- Forward direction of continuity on maps: a related pair of `T(f)` is already related by some
`T(gᵢ)`. -/
theorem FExpr.map_continuous_mp : (T : FExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := T₁.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod T₀ T₁, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := T₀.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := T₁.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (T₀.map_mono hik) P P' hi, (T₁.map_mono hjk) Q Q' hj, rfl, rfl⟩

/-- **`λf. T(f)` is continuous on maps.** For a non-empty directed family `gᵢ` with pointwise union
`f`, the relation of `T(f)` is the union of those of the `T(gᵢ)` — `T(f)` is approximable. -/
theorem FExpr.map_continuous (T : FExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

/-! ## Exercise 6.20 — `λΓ. tok(T({Γ}))` is continuous, hence a fixed point exists

> For any system `𝒟` let `tok(𝒟)` be the underlying set of tokens, so that `𝒟` is a system over
> `tok(𝒟)`. For the category of Exercise 6.19 show that the function `λΓ. tok(T({Γ}))` is continuous
> on the domain `{Γ ⊆ {0,1}* ∣ Λ ∈ Γ}`, where `T` is any of the functors generated in 6.19. Conclude
> that there must exist a set `Γ = tok(T({Γ}))`, so that `{Γ} ◁ T({Γ})`, and so 6.14 applies.

Here `tok(𝒟) = 𝒟.master` (the master neighbourhood *is* the token set `Δ`, since `𝒟 ⊆ 𝒫(Δ)`), and
`{Γ}` is the one-neighbourhood system `singletonSys Γ` with master `Γ`. The key simplification is
that the *master* of `T({Γ})` is computed by a tiny token-level recursion `mFun T` that needs no
`NeighborhoodSystem` data at all: constants are constant, the identity returns `Γ`, and **both** sum
and product return `{Λ} ∪ 0·(…) ∪ 1·(…)` (`sumTokMaster = prodTokNbhd` on masters). `mFun_eq_master`
identifies `mFun T Γ` with `tok(T({Γ}))`. The function `mFun T` is monotone (`mFun_mono`) and
continuous — in fact fully additive — on the powerset of `{0,1}*` (`mFun_continuous`), so its
restriction to `{Γ ∣ Λ ∈ Γ}` is continuous on that domain. The least fixed point above the bottom
`{Λ}` is the explicit Kleene union `⋃ₙ mFunⁿ({Λ})` (`mIter`), giving `Γ = tok(T({Γ}))`
(`exists_tok_fixedPoint`) and hence `{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the
hypothesis Theorem 6.14 needs. (For the bottom to stay in the domain we need `Λ ∈ tok(C)` for the
constant systems `C`; this is recorded by `FExpr.RootedConst`, and holds automatically for sums and
products since their masters contain `Λ`.) -/

/-- **`tok(𝒟)`** — the underlying set of tokens of a system, i.e. its master neighbourhood `Δ`. -/
def ScottSys.tok (D : ScottSys) : Set Str := D.sys.master

/-- **The one-neighbourhood system `{Γ}`** over `{0,1}*`: its only neighbourhood is `Γ` itself, and
its master (token set) is `Γ`. It is `∅`-free precisely because `Γ` is non-empty. -/
def singletonSys (Γ : Set Str) (h : Γ.Nonempty) : ScottSys where
  sys :=
    { mem := fun X => X = Γ
      master := Γ
      master_nonempty := h
      master_mem := rfl
      inter_mem := by
        intro X Y Z hX hY _ _
        show X ∩ Y = Γ
        rw [hX, hY, Set.inter_self]
      sub_master := by intro X hX; rw [show X = Γ from hX] }
  ne := by intro X hX; rw [show X = Γ from hX]; exact h

/-- **The token-level master recursion.** `mFun T Γ` computes `tok(T({Γ}))` purely from `Γ`, without
touching the neighbourhood data of `{Γ}` (`mFun_eq_master`): constants are constant, the identity
returns `Γ`, and both sum and product wrap the two component token sets with the tags `0,1` under a
common root `Λ` (`sumTokMaster = prodTokNbhd` agree on masters). -/
def mFun : FExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
  | .prod T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))

/-- `mFun T Γ` is exactly the token set `tok(T({Γ})) = (T.obj {Γ}).sys.master`. -/
theorem mFun_eq_master : (T : FExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    mFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]
  | .prod T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]

/-! ### Monotone on the domain -/

/-- Monotonicity of the tagged-union shape shared by sum and product. -/
theorem insertTag_mono {p q p' q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') :
    insert ([] : Str) (embBit false p ∪ embBit true q)
      ⊆ insert ([] : Str) (embBit false p' ∪ embBit true q') := by
  rintro w (rfl | hw | hw)
  · exact Or.inl rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

/-- **`λΓ. tok(T({Γ}))` is monotone on the domain.** -/
theorem mFun_mono (T : FExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : mFun T Γ ⊆ mFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-! ### Continuous on the domain -/

/-- Continuity (full additivity) of the tagged-union shape shared by sum and product. -/
theorem insertTag_continuous {ℱ : Set (Set Str)} {U : Set Str} (hne : ℱ.Nonempty)
    {p q : Set Str → Set Str}
    (hp : ∀ w, w ∈ p U ↔ ∃ Γ ∈ ℱ, w ∈ p Γ)
    (hq : ∀ w, w ∈ q U ↔ ∃ Γ ∈ ℱ, w ∈ q Γ) (w : Str) :
    (w ∈ insert ([] : Str) (embBit false (p U) ∪ embBit true (q U)))
      ↔ ∃ Γ ∈ ℱ, w ∈ insert ([] : Str) (embBit false (p Γ) ∪ embBit true (q Γ)) := by
  simp only [Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro (rfl | hw | hw)
    · obtain ⟨Γ, hΓ⟩ := hne; exact ⟨Γ, hΓ, Or.inl rfl⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hpΓ⟩ := (hp w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inl ⟨w', rfl, hpΓ⟩)⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hqΓ⟩ := (hq w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inr ⟨w', rfl, hqΓ⟩)⟩
  · rintro ⟨Γ, hΓ, (rfl | hw | hw)⟩
    · exact Or.inl rfl
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inl ⟨w', rfl, (hp w').mpr ⟨Γ, hΓ, hw'⟩⟩)
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inr ⟨w', rfl, (hq w').mpr ⟨Γ, hΓ, hw'⟩⟩)

/-- **`λΓ. tok(T({Γ}))` is continuous on the domain `{Γ ∣ Λ ∈ Γ}`.** For a non-empty `⊆`-directed
family `ℱ` with union `U`, the token set of `T({U})` is the union of those of the `T({Γ})`. (The
proof in fact establishes full additivity — directedness is not needed for the master level — but the
statement is the directed-sup form Scott calls *continuous*.) -/
theorem mFun_continuous (T : FExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ mFun T U ↔ ∃ Γ ∈ ℱ, w ∈ mFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

/-! ### A fixed point `Γ = tok(T({Γ}))` — so `{Γ} ◁ T({Γ})` and 6.14 applies -/

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** This is what keeps the bottom `{Λ}` and
the whole Kleene chain inside the domain `{Γ ∣ Λ ∈ Γ}`; sums and products satisfy it for free. -/
def FExpr.RootedConst : FExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst

/-- If `Λ ∈ Γ` then `Λ ∈ tok(T({Γ}))` — so `λΓ. tok(T({Γ}))` is an endofunction of the domain. -/
theorem mFun_nil_mem : ∀ (T : FExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ mFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _

/-- The **Kleene iteration** `mFunⁿ({Λ})` whose union is the least fixed point above `{Λ}`. -/
def mIter (T : FExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => mFun T (mIter T n)

theorem nil_mem_mIter (T : FExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ mIter T n
  | 0 => rfl
  | n + 1 => mFun_nil_mem T hT (nil_mem_mIter T hT n)

theorem mIter_mono_step (T : FExpr) (hT : T.RootedConst) :
    ∀ n, mIter T n ⊆ mIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact mFun_nil_mem T hT rfl
  | n + 1 => mFun_mono T (mIter_mono_step T hT n)

theorem mIter_mono (T : FExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    mIter T m ⊆ mIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact mIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem mFun_iter_fixed (T : FExpr) (hT : T.RootedConst) :
    mFun T (⋃ n, mIter T n) = ⋃ n, mIter T n := by
  have hstep := mIter_mono_step T hT
  have hne : (Set.range (mIter T)).Nonempty := ⟨mIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (mIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨mIter T (max i j), ⟨max i j, rfl⟩,
      mIter_mono T hT (le_max_left i j), mIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, mIter T n) ↔ ∃ S ∈ Set.range (mIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨mIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [mFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨mIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **The conclusion of Exercise 6.20 (token level).** For any construct `T` whose constants contain
`Λ`, there is a set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem exists_tok_fixedPoint (T : FExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ mFun T Γ = Γ :=
  ⟨⋃ n, mIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_mIter T hT 0⟩, mFun_iter_fixed T hT⟩

/-- **The conclusion of Exercise 6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies.**
From the fixed point `Γ = tok(T({Γ}))`, the one-neighbourhood system `{Γ}` is a subsystem of
`T({Γ})`: they share the master `Γ`, and `Γ` is a (the master) neighbourhood of `T({Γ})`. -/
theorem exists_singleton_subsystem (T : FExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := exists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  -- `tok(T({Γ})) = Γ` (note `tok` is definitionally `.sys.master`).
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (mFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · -- master_eq: `Γ = tok(T({Γ}))`
    exact hmaster.symm
  · -- sub: the only neighbourhood `Γ` of `{Γ}` is the master of `T({Γ})`
    intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · -- inter_closed: trivial, both neighbourhoods are `Γ`
    intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]

end Exercise619

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise621.lean -/

/-!
# Exercise 6.21 (Scott 1981, PRG-19, §6) — the *separated* sum `⊕` and product `⊗`

> **EXERCISE 6.21.** Do the same as 6.19 and 6.20 when the functors are also allowed to be generated
> by the operations
> `D₀ ⊕ D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {0X ∣ X ∈ D₀ ∖ {Δ₀}} ∪ {1Y ∣ Y ∈ D₁ ∖ {Δ₁}}`,
> `D₀ ⊗ D₁ = {{Λ} ∪ 0Δ₀ ∪ 1Δ₁} ∪ {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ D₀ ∖ {Δ₀} and Y ∈ D₁ ∖ {Δ₁}}`.
> Generalize all of `+`, `×`, `⊕`, `⊗` to combinations of several terms, not just the binary sums and
> products.

This module extends Exercise 6.19 Part B (`Exercise619PartB.lean`) with the two *coalesced*
operations. The difference from the *separated* sum `+`/product `×` of 6.19 is that `⊕`/`⊗` **delete
the improper tagged copies** `0Δ₀` and `1Δ₁`: in domain terms this **identifies the two bottoms**
(`⊕` is the coalesced sum, `⊗` the smash product), whereas `+`/`×` keep them apart. Both share the
*same master* `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` as `+`/`×`.

## Contents (this stage: objects)

* `oplusTok`/`otimesTok` — the two token-level systems over `Str = {0,1}*`, each `∅`-free.
* `ScottSys.oplus`/`ScottSys.otimes` — the same, repackaged as objects of Scott's category.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise619
open Scott1980.Neighborhood.Example62 Scott1980.Neighborhood.ExampleB
open Scott1980.Neighborhood.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## The coalesced sum `D₀ ⊕ D₁` over `{0,1}*`

`D₀ ⊕ D₁ = {M} ∪ {0X ∣ X ∈ 𝒟₀, X ≠ Δ₀} ∪ {1Y ∣ Y ∈ 𝒟₁, Y ≠ Δ₁}`, where `M = {Λ} ∪ 0Δ₀ ∪ 1Δ₁` is
the shared `sumTokMaster`. -/

/-- If `X ⊆ Δ` and `X ≠ Δ`, then any intersection `X ∩ X'` is still `≠ Δ` (it is `⊆ X ⊊ Δ`). -/
theorem inter_ne_of_ne_left {X X' Δ : Set Str} (hX : X ⊆ Δ) (hne : X ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX (by rw [← h]; exact Set.inter_subset_left))

theorem inter_ne_of_ne_right {X X' Δ : Set Str} (hX' : X' ⊆ Δ) (hne : X' ≠ Δ) : X ∩ X' ≠ Δ := by
  intro h
  exact hne (Set.Subset.antisymm hX' (by rw [← h]; exact Set.inter_subset_right))

/-- **Exercise 6.21 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁` over `{0,1}*`.** As `sumTok`, but the
improper copies `0Δ₀`, `1Δ₁` are removed (`X ≠ Δ₀`, `Y ≠ Δ₁`), so the two bottoms are identified. -/
def oplusTok (D₀ D₁ : NeighborhoodSystem Str)
    (h₀ : ∀ X, D₀.mem X → X.Nonempty) (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
    (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)
  master := sumTokMaster D₀ D₁
  master_nonempty := ⟨[], nil_mem_sumTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_sumTokMaster hX
    · exact embT_subset_sumTokMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumTokMaster D₀ D₁ ∨ (∃ X, D₀.mem X ∧ X ≠ D₀.master ∧ W = embBit false X) ∨
        (∃ Y, D₁.mem Y ∧ Y ≠ D₁.master ∧ W = embBit true Y)) → (W : Set Str).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨[], nil_mem_sumTokMaster⟩
      · exact embBit_nonempty (h₀ X hX)
      · exact embBit_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embF hX]
        exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X ∩ X', D₀.inter_mem hX hX' hZ₀ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₀.sub_master hX) hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          obtain ⟨w', he, -⟩ := hZsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Z₁)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumTokMaster_inter_embT hY]
        exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub nil_mem_sumTokMaster) nil_not_mem_embBit
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          obtain ⟨w', he, -⟩ := hZsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false Z₀)
          simp only [List.cons.injEq] at he; exact absurd he.1 (by decide)
        · exact Or.inr (Or.inr ⟨Y ∩ Y', D₁.inter_mem hY hY' hZ₁ (embBit_subset.mp hZsub),
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩)

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_nonempty : ∀ W, (oplusTok D₀ D₁ h₀ h₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

/-! ## The smash product `D₀ ⊗ D₁` over `{0,1}*`

`D₀ ⊗ D₁ = {M} ∪ {{Λ} ∪ 0X ∪ 1Y ∣ X ∈ 𝒟₀, X ≠ Δ₀, Y ∈ 𝒟₁, Y ≠ Δ₁}`, where again
`M = {Λ} ∪ 0Δ₀ ∪ 1Δ₁ = prodTokNbhd Δ₀ Δ₁`. The improper rectangles touching a top coordinate (other
than the full top `M`) are removed. -/

/-- **Exercise 6.21 — the smash product system `𝒟₀ ⊗ 𝒟₁` over `{0,1}*`.** As `prodTok`, but proper
rectangles must avoid both top coordinates (`X ≠ Δ₀`, `Y ≠ Δ₁`); the full top `M = prodTokNbhd Δ₀ Δ₁`
is kept as the master. -/
def otimesTok (D₀ D₁ : NeighborhoodSystem Str) : NeighborhoodSystem Str where
  mem W := W = prodTokNbhd D₀.master D₁.master ∨
    (∃ X Y, D₀.mem X ∧ D₁.mem Y ∧ X ≠ D₀.master ∧ Y ≠ D₁.master ∧ W = prodTokNbhd X Y)
  master := prodTokNbhd D₀.master D₁.master
  master_nonempty := ⟨[], mem_prodTokNbhd_nil⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact subset_rfl
    · exact prodTokNbhd_subset_iff.mpr ⟨D₀.sub_master hX, D₁.sub_master hY⟩
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
          Set.inter_eq_right.mpr (D₁.sub_master hY')]
        exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
      · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
          Set.inter_eq_right.mpr (D₁.sub_master hY)]
        exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · rw [prodTokNbhd_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, Z₁, hZ₀, hZ₁, -, -, rfl⟩
        · obtain ⟨hsub₀, -⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact absurd (Set.Subset.antisymm (D₀.sub_master hX)
            (hsub₀.trans Set.inter_subset_left)) hXne
        · obtain ⟨hsub₀, hsub₁⟩ := prodTokNbhd_subset_iff.mp hZsub
          exact Or.inr ⟨X ∩ X', Y ∩ Y', D₀.inter_mem hX hX' hZ₀ hsub₀,
            D₁.inter_mem hY hY' hZ₁ hsub₁, inter_ne_of_ne_left (D₀.sub_master hX) hXne,
            inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

theorem otimesTok_nonempty : ∀ W, (otimesTok D₀ D₁).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, Y, -, -, -, -, rfl⟩) <;> exact ⟨[], mem_prodTokNbhd_nil⟩

/-! ## Repackaged as objects of Scott's category -/

/-- The **coalesced sum object** `𝒟₀ ⊕ 𝒟₁`. -/
def ScottSys.oplus (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨oplusTok A₀.sys A₁.sys A₀.ne A₁.ne, oplusTok_nonempty⟩

/-- The **smash product object** `𝒟₀ ⊗ 𝒟₁`. -/
def ScottSys.otimes (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨otimesTok A₀.sys A₁.sys, otimesTok_nonempty⟩

/-! ## Membership inversions -/

theorem oplusTok_mem_master : (oplusTok D₀ D₁ h₀ h₁).mem (sumTokMaster D₀ D₁) := Or.inl rfl

theorem oplusTok_mem_embF {X : Set Str} (hX : D₀.mem X) (hXne : X ≠ D₀.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit false X) := Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)

theorem oplusTok_mem_embT {Y : Set Str} (hY : D₁.mem Y) (hYne : Y ≠ D₁.master) :
    (oplusTok D₀ D₁ h₀ h₁).mem (embBit true Y) := Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)

theorem oplusTok_mem_embF_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit false W)) :
    D₀.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX
  · exact absurd heq.symm (embBit_ne (show (true : Bool) ≠ false by decide) (h₁ Y hY))

theorem oplusTok_mem_embT_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

theorem otimesTok_mem_master : (otimesTok D₀ D₁).mem (prodTokNbhd D₀.master D₁.master) := Or.inl rfl

theorem otimesTok_mem_prod {X Y : Set Str} (hX : D₀.mem X) (hY : D₁.mem Y)
    (hXne : X ≠ D₀.master) (hYne : Y ≠ D₁.master) :
    (otimesTok D₀ D₁).mem (prodTokNbhd X Y) := Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩

theorem otimesTok_mem_prod_inv {X Y : Set Str} (h : (otimesTok D₀ D₁).mem (prodTokNbhd X Y))
    (hX : X ≠ D₀.master) : D₀.mem X ∧ D₁.mem Y := by
  rcases h with heq | ⟨X', Y', hX', hY', -, -, heq⟩
  · obtain ⟨rfl, -⟩ := prodTokNbhd_injective heq; exact absurd rfl hX
  · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq; exact ⟨hX', hY'⟩

/-! ## Monotone on domains: `◁` is carried componentwise -/

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The coalesced sum carries the subsystem relation componentwise. -/
theorem oplusTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.oplus A₁).sys ◁ (B₀.oplus B₁).sys := by
  have heqm : sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys := by
    unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr (Or.inl ⟨X, h0.sub hX, h0.master_eq ▸ hXne, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, h1.sub hY, h1.master_eq ▸ hYne, rfl⟩)
  · rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
    · rw [sumTokMaster_inter_embT hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inl ⟨X ∩ X',
        h0.inter_closed hX hX' (oplusTok_mem_embF_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne, rfl⟩)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd ((B₀.oplus B₁).ne _ hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact Or.inr (Or.inr ⟨Y ∩ Y',
        h1.inter_closed hY hY' (oplusTok_mem_embT_inv (h₀ := B₀.ne) (h₁ := B₁.ne) hInt),
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩)

/-- The smash product carries the subsystem relation componentwise. -/
theorem otimesTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.otimes A₁).sys ◁ (B₀.otimes B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr ⟨X, Y, h0.sub hX, h1.sub hY, h0.master_eq ▸ hXne, h1.master_eq ▸ hYne, rfl⟩
  · rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX'),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      have hXne' : X ∩ X' ≠ B₀.sys.master := by
        rw [← h0.master_eq]; exact inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne
      obtain ⟨hmemX, hmemY⟩ := otimesTok_mem_prod_inv hInt hXne'
      exact Or.inr ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hmemX, h1.inter_closed hY hY' hmemY,
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne,
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩

/-! ## The functorial action of the coalesced sum on (strict) maps

The relation has the same shape as `sumMapTok` but with two changes forced by *coalescence*: proper
tagged copies require the components to be proper (`X ≠ Δ₀`, `X' ≠ Δ₀'`), and the **master/collapse
row** `(W ∈ 𝒟₀⊕𝒟₁ ∧ W' = M)` sends *every* neighbourhood to the top `M` (which is always valid, the
top being the least informative output, and is exactly what handles `f₀(X) = Δ₀'` collapsing back to
the shared bottom). -/

variable {C₀ C₁ : ScottSys}

/-- **`f₀ ⊕ f₁`, the action of the coalesced sum on maps.** -/
def oplusMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.oplus A₁).sys (B₀.oplus B₁).sys where
  rel W W' :=
    ((A₀.oplus A₁).sys.mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ X ≠ A₀.sys.master ∧ X' ≠ B₀.sys.master ∧
      W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ Y ≠ A₁.sys.master ∧ Y' ≠ B₁.sys.master ∧
      W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, hXne, -, rfl, -⟩ | ⟨Y, Y', hrel, hYne, -, rfl, -⟩)
    · exact hW
    · exact oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hrel) hXne
    · exact oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hrel) hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, hX'ne, -, rfl⟩ | ⟨Y, Y', hrel, -, hY'ne, -, rfl⟩)
    · exact Or.inl rfl
    · exact oplusTok_mem_embF (h₀ := B₀.ne) (h₁ := B₁.ne) (f₀.rel_cod hrel) hX'ne
    · exact oplusTok_mem_embT (h₀ := B₀.ne) (h₁ := B₁.ne) (f₁.rel_cod hrel) hY'ne
  master_rel := Or.inl ⟨(A₀.oplus A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, hWeq, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, hWeq,
          by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, hWeq,
          by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hX₂ne, hX'₂ne, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, -, -, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, hXne, hX'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, hXne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hrel)) hX'ne, rfl,
          embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, -, -, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hY₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, hYne, hY'ne, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, hYne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hrel)) hY'ne, rfl,
          embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.oplus B₁).sys.sub_master hZ') hZZ'⟩
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃,
            hX₂ne, hX₃ne, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · rcases hZ' with rfl | ⟨X₃, hX₃, hX₃ne, rfl⟩ | ⟨Y₃, hY₃, hY₃ne, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, hX₂ne, rfl⟩ | ⟨Y₂, hY₂, hY₂ne, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃,
            hY₂ne, hY₃ne, rfl, rfl⟩)

/-- **`oplusMapTok` is always strict.** -/
theorem oplusMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (oplusMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, -, -, heq, -⟩ | ⟨Y0, Y', -, -, -, heq, -⟩)
  · rfl
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit false X := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · have heq' : sumTokMaster A₀.sys A₁.sys = embBit true Y0 := heq
    exact absurd (heq' ▸ nil_mem_sumTokMaster) nil_not_mem_embBit

/-- **`(I ⊕ I) = I`.** -/
theorem oplusMapTok_id :
    oplusMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.oplus A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hsub⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, (A₀.oplus A₁).sys.sub_master hW⟩
    · exact ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX hXne,
        oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX' hX'ne, embBit_subset.mpr hsub⟩
    · exact ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY hYne,
        oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY' hY'ne, embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

/-- **`(g₀ ∘ f₀) ⊕ (g₁ ∘ f₁) = (g₀ ⊕ g₁) ∘ (f₀ ⊕ f₁)`** for **strict** `g₀, g₁`. (Strictness of the
outer maps is exactly what prevents an intermediate top `f₀(X) = Δ₀'` from being re-expanded — that
is the categorical reason `⊕` is a functor only on the strict-map category Scott restricts to.) -/
theorem oplusMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    oplusMapTok (g₀.comp f₀) (g₁.comp f₁) = (oplusMapTok g₀ g₁).comp (oplusMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩ |
      ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)
    · exact ⟨sumTokMaster B₀.sys B₁.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.oplus B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg))
      exact ⟨embBit false X', Or.inr (Or.inl ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩),
        Or.inr (Or.inl ⟨X', X'', hg, hX'ne, hX''ne, rfl, rfl⟩)⟩
    · have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg))
      exact ⟨embBit true Y', Or.inr (Or.inr ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩),
        Or.inr (Or.inr ⟨Y', Y'', hg, hY'ne, hY''ne, rfl, rfl⟩)⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, hXne, hX'ne, rfl, rfl⟩ | ⟨Y, Y', hf, hYne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, -, -, heq, -⟩ | ⟨Y, Y', -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd (heq ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, hX''ne, heq, rfl⟩ | ⟨Y₂, Y'', hg, -, -, heq, -⟩
      · exact Or.inl ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) (f₀.rel_dom hf) hXne, rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inl ⟨X, X'', ⟨X', hf, hg⟩, hXne, hX''ne, rfl, rfl⟩)
      · exact absurd heq (embBit_ne (by decide) (B₀.ne X' (f₀.rel_cod hf)))
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, -, -, heq, -⟩ | ⟨Y₂, Y'', hg, -, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) (f₁.rel_dom hf) hYne, rfl⟩
      · exact absurd heq (embBit_ne (by decide) (B₁.ne Y' (f₁.rel_cod hf)))
      · obtain rfl := embBit_injective heq
        exact Or.inr (Or.inr ⟨Y, Y'', ⟨Y', hf, hg⟩, hYne, hY''ne, rfl, rfl⟩)

/-- `oplusMapTok` is monotone in both arguments. -/
theorem oplusMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    oplusMapTok f₀ f₁ ≤ oplusMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, X', hrel, hXne, hX'ne, rfl, rfl⟩ |
    ⟨Y, Y', hrel, hYne, hY'ne, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr (Or.inl ⟨X, X', h0 X X' hrel, hXne, hX'ne, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨Y, Y', h1 Y Y' hrel, hYne, hY'ne, rfl, rfl⟩)

/-! ## The functorial action of the smash product on (strict) maps

As `prodMapTok`, but proper rectangles require both components proper, and a **master/collapse row**
absorbs a boundary hit `f₀(X) = Δ₀'` (or `f₁(Y) = Δ₁'`) into the top `M`. -/

/-- **`f₀ ⊗ f₁`, the action of the smash product on maps.** -/
def otimesMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.otimes A₁).sys (B₀.otimes B₁).sys where
  rel W W' :=
    ((A₀.otimes A₁).sys.mem W ∧ W' = prodTokNbhd B₀.sys.master B₁.sys.master) ∨
    (∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧ X ≠ A₀.sys.master ∧ Y ≠ A₁.sys.master ∧
      X' ≠ B₀.sys.master ∧ Y' ≠ B₁.sys.master ∧ W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, Y, X', Y', h0, h1, hXne, hYne, -, -, rfl, -⟩)
    · exact hW
    · exact otimesTok_mem_prod (f₀.rel_dom h0) (f₁.rel_dom h1) hXne hYne
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, Y, X', Y', h0, h1, -, -, hX'ne, hY'ne, -, rfl⟩)
    · exact otimesTok_mem_master
    · exact otimesTok_mem_prod (f₀.rel_cod h0) (f₁.rel_cod h1) hX'ne hY'ne
  master_rel := Or.inl ⟨(A₀.otimes A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, hWeq, ?_⟩
        rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, Y₂, X'₂, Y'₂, hr0₂, hr1₂, hX₂ne, hY₂ne, hX'₂ne, hY'₂ne, hWeq, rfl⟩
      · refine Or.inr ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, ?_⟩
        rw [Set.inter_comm, prodTokNbhd_inter,
          Set.inter_eq_right.mpr (B₀.sys.sub_master (f₀.rel_cod hr0)),
          Set.inter_eq_right.mpr (B₁.sys.sub_master (f₁.rel_cod hr1))]
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
        refine Or.inr ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right hr0 hr0₂,
          f₁.inter_right hr1 hr1₂, hXne, hYne,
          inter_ne_of_ne_left (B₀.sys.sub_master (f₀.rel_cod hr0)) hX'ne,
          inter_ne_of_ne_left (B₁.sys.sub_master (f₁.rel_cod hr1)) hY'ne, rfl, ?_⟩
        rw [prodTokNbhd_inter]
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((B₀.otimes B₁).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZmem with rfl | ⟨Xz, Yz, hXz, hYz, hXzne, hYzne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hWW
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master (f₀.rel_dom hr0)) hsubX) hXne
      · rcases hZ'mem with rfl | ⟨Xz', Yz', hXz', hYz', hXz'ne, hYz'ne, rfl⟩
        · exact Or.inl ⟨otimesTok_mem_prod hXz hYz hXzne hYzne, rfl⟩
        · obtain ⟨hXzX, hYzY⟩ := prodTokNbhd_subset_iff.mp hWW
          obtain ⟨hX'Xz', hY'Yz'⟩ := prodTokNbhd_subset_iff.mp hZZ'
          exact Or.inr ⟨Xz, Yz, Xz', Yz', f₀.mono hr0 hXzX hX'Xz' hXz hXz',
            f₁.mono hr1 hYzY hY'Yz' hYz hYz', hXzne, hYzne, hXz'ne, hYz'ne, rfl, rfl⟩

/-- **`otimesMapTok` is always strict.** -/
theorem otimesMapTok_isStrict (f₀ : ApproximableMap A₀.sys B₀.sys)
    (f₁ : ApproximableMap A₁.sys B₁.sys) : IsStrict (otimesMapTok f₀ f₁) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, Y0, X', Y', -, -, hXne, -, -, -, heq, -⟩)
  · rfl
  · have heq' : prodTokNbhd A₀.sys.master A₁.sys.master = prodTokNbhd X Y0 := heq
    obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
    exact absurd h.symm hXne

/-- **`(I ⊗ I) = I`.** -/
theorem otimesMapTok_id :
    otimesMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.otimes A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X', Y', ⟨hX, hX', hsubX⟩, ⟨hY, hY', hsubY⟩,
      hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.otimes A₁).sys.master_mem, (A₀.otimes A₁).sys.sub_master hW⟩
    · exact ⟨otimesTok_mem_prod hX hY hXne hYne, otimesTok_mem_prod hX' hY' hX'ne hY'ne,
        prodTokNbhd_subset_iff.mpr ⟨hsubX, hsubY⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX') hsubX) hX'ne
      · obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-- **`(g₀ ∘ f₀) ⊗ (g₁ ∘ f₁) = (g₀ ⊗ g₁) ∘ (f₀ ⊗ f₁)`** for **strict** `g₀, g₁`. -/
theorem otimesMapTok_comp (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys)
    {g₀ : ApproximableMap B₀.sys C₀.sys} {g₁ : ApproximableMap B₁.sys C₁.sys}
    (hg₀ : IsStrict g₀) (hg₁ : IsStrict g₁) :
    otimesMapTok (g₀.comp f₀) (g₁.comp f₁) = (otimesMapTok g₀ g₁).comp (otimesMapTok f₀ f₁) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
      hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩)
    · exact ⟨prodTokNbhd B₀.sys.master B₁.sys.master, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(B₀.otimes B₁).sys.master_mem, rfl⟩⟩
    · have hX'ne : X' ≠ B₀.sys.master := fun h => hX''ne (hg₀ (h ▸ hg0))
      have hY'ne : Y' ≠ B₁.sys.master := fun h => hY''ne (hg₁ (h ▸ hg1))
      exact ⟨prodTokNbhd X' Y',
        Or.inr ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩,
        Or.inr ⟨X', Y', X'', Y'', hg0, hg1, hX'ne, hY'ne, hX''ne, hY''ne, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, Y, X', Y', hf0, hf1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨Xg, Yg, X'', Y'', -, -, hXgne, -, -, -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · have heq' : prodTokNbhd B₀.sys.master B₁.sys.master = prodTokNbhd Xg Yg := heq
        obtain ⟨h, -⟩ := prodTokNbhd_injective heq'
        exact absurd h.symm hXgne
    · rcases hW'W'' with ⟨-, rfl⟩ |
        ⟨Xg, Yg, X'', Y'', hg0, hg1, hXgne, hYgne, hX''ne, hY''ne, heq, rfl⟩
      · exact Or.inl ⟨otimesTok_mem_prod (f₀.rel_dom hf0) (f₁.rel_dom hf1) hXne hYne, rfl⟩
      · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
        exact Or.inr ⟨X, Y, X'', Y'', ⟨X', hf0, hg0⟩, ⟨Y', hf1, hg1⟩,
          hXne, hYne, hX''ne, hY''ne, rfl, rfl⟩

/-- `otimesMapTok` is monotone in both arguments. -/
theorem otimesMapTok_mono {f₀ f₀' : ApproximableMap A₀.sys B₀.sys}
    {f₁ f₁' : ApproximableMap A₁.sys B₁.sys} (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    otimesMapTok f₀ f₁ ≤ otimesMapTok f₀' f₁' := by
  rw [ApproximableMap.le_iff]
  rintro W W' (⟨hW, rfl⟩ | ⟨X, Y, X', Y', hr0, hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
  · exact Or.inl ⟨hW, rfl⟩
  · exact Or.inr ⟨X, Y, X', Y', h0 X X' hr0, h1 Y Y' hr1, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-! ## The extended functor-expression algebra `GExpr`

Scott's *"do the same as 6.19 and 6.20 when the functors are also allowed to be generated by the
operations `⊕`, `⊗`"*: the closed family of constructs is enlarged from `FExpr` (constants,
identity, `+`, `×`) to also include the coalesced `⊕` and the smash `⊗`. The functor laws and the
on-maps/on-domains continuity properties are re-established by induction; the `⊕`/`⊗` composition
law carries the strictness hypothesis (Scott's category is the **strict-map** category, and that is
exactly what makes `⊕`/`⊗` functorial). -/

/-- **The extended functor-expression algebra** (constants, identity, `+`, `×`, `⊕`, `⊗`). -/
inductive GExpr where
  /-- The constant functor `T(X) = 𝒟`. -/
  | const : ScottSys → GExpr
  /-- The identity functor `T(X) = X`. -/
  | var : GExpr
  /-- The separated sum `T₀(X) + T₁(X)`. -/
  | sum : GExpr → GExpr → GExpr
  /-- The separated product `T₀(X) × T₁(X)`. -/
  | prod : GExpr → GExpr → GExpr
  /-- The coalesced sum `T₀(X) ⊕ T₁(X)`. -/
  | oplus : GExpr → GExpr → GExpr
  /-- The smash product `T₀(X) ⊗ T₁(X)`. -/
  | otimes : GExpr → GExpr → GExpr

/-- **The action of `T` on objects.** -/
def GExpr.obj : GExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum a b, X => (a.obj X).sum (b.obj X)
  | .prod a b, X => (a.obj X).prod (b.obj X)
  | .oplus a b, X => (a.obj X).oplus (b.obj X)
  | .otimes a b, X => (a.obj X).otimes (b.obj X)

/-- **The action of `T` on maps.** -/
def GExpr.map : (T : GExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum a b, _, _, f => sumMapTok (a.map f) (b.map f)
  | .prod a b, _, _, f => prodMapTok (a.map f) (b.map f)
  | .oplus a b, _, _, f => oplusMapTok (a.map f) (b.map f)
  | .otimes a b, _, _, f => otimesMapTok (a.map f) (b.map f)

/-- **Every `T` preserves strictness.** -/
theorem GExpr.map_isStrict : (T : GExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum a b, _, _, f, _ => sumMapTok_isStrict (a.map f) (b.map f)
  | .prod a b, _, _, f, hf => prodMapTok_isStrict (a.map_isStrict f hf) (b.map_isStrict f hf)
  | .oplus a b, _, _, f, _ => oplusMapTok_isStrict (a.map f) (b.map f)
  | .otimes a b, _, _, f, _ => otimesMapTok_isStrict (a.map f) (b.map f)

/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** -/
theorem GExpr.map_id : (T : GExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const _, _ => rfl
  | .var, _ => rfl
  | .sum a b, X => by
      show sumMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).sum (b.obj X)).sys
      rw [a.map_id X, b.map_id X, sumMapTok_id]
  | .prod a b, X => by
      show prodMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys)) = idMap ((a.obj X).prod (b.obj X)).sys
      rw [a.map_id X, b.map_id X, prodMapTok_id]
  | .oplus a b, X => by
      show oplusMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).oplus (b.obj X)).sys
      rw [a.map_id X, b.map_id X, oplusMapTok_id]
  | .otimes a b, X => by
      show otimesMapTok (a.map (idMap X.sys)) (b.map (idMap X.sys))
          = idMap ((a.obj X).otimes (b.obj X)).sys
      rw [a.map_id X, b.map_id X, otimesMapTok_id]

/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)` for strict `g`.** Together with `map_id`, *these are
all functors* of the strict-map category. The strictness of `g` is needed (and only) for the
coalesced `⊕`/`⊗`, whose composition law `oplusMapTok_comp`/`otimesMapTok_comp` requires it. -/
theorem GExpr.map_comp : (T : GExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    {g : ApproximableMap Y.sys Z.sys} → IsStrict g → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _, _ => rfl
  | .sum a b, _, _, _, f, g, hg => by
      show sumMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (sumMapTok (a.map g) (b.map g)).comp (sumMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact sumMapTok_comp _ _ _ _
  | .prod a b, _, _, _, f, g, hg => by
      show prodMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (prodMapTok (a.map g) (b.map g)).comp (prodMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact prodMapTok_comp _ _ _ _
  | .oplus a b, _, _, _, f, g, hg => by
      show oplusMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (oplusMapTok (a.map g) (b.map g)).comp (oplusMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact oplusMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)
  | .otimes a b, _, _, _, f, g, hg => by
      show otimesMapTok (a.map (g.comp f)) (b.map (g.comp f))
          = (otimesMapTok (a.map g) (b.map g)).comp (otimesMapTok (a.map f) (b.map f))
      rw [a.map_comp f hg, b.map_comp f hg]
      · exact otimesMapTok_comp _ _ (a.map_isStrict g hg) (b.map_isStrict g hg)

/-- **`λf. T(f)` is monotone** (the order half of *continuous on maps*). -/
theorem GExpr.map_mono : (T : GExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum a b, _, _, _, _, h => sumMapTok_mono (a.map_mono h) (b.map_mono h)
  | .prod a b, _, _, _, _, h => prodMapTok_mono (a.map_mono h) (b.map_mono h)
  | .oplus a b, _, _, _, _, h => oplusMapTok_mono (a.map_mono h) (b.map_mono h)
  | .otimes a b, _, _, _, _, h => otimesMapTok_mono (a.map_mono h) (b.map_mono h)

/-- **`λX. T(X)` is monotone on domains.** -/
theorem GExpr.obj_subsystem : (T : GExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum a b, _, _, h => sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .prod a b, _, _, h => prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .oplus a b, _, _, h => oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)
  | .otimes a b, _, _, h => otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)

/-! ### Continuous on domains -/

/-- Forward direction of continuity on domains for `GExpr`. -/
theorem GExpr.obj_continuous_mp : (T : GExpr) → {ℱ : Set ScottSys} → {U : ScottSys} →
    DirectedOn (fun a b => a.sys ◁ b.sys) ℱ → ℱ.Nonempty →
    (∀ D ∈ ℱ, D.sys ◁ U.sys) → (∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X) →
    {W : Set Str} → (T.obj U).sys.mem W → ∃ D ∈ ℱ, (T.obj D).sys.mem W
  | .const _, _, _, _, hne, _, _, _, hmem => by
      obtain ⟨D, hD⟩ := hne; exact ⟨D, hD, hmem⟩
  | .var, _, _, _, _, _, hU, W, hmem => (hU W).mp hmem
  | .sum a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.sum a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        exact ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, rfl⟩)⟩
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        exact ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, rfl⟩)⟩
  | .prod a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      obtain ⟨X, Y, hX, hY, rfl⟩ := hmem
      obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
      obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
      obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
      exact ⟨D₃, hD₃, X, Y, (a.obj_subsystem hr1).sub hXD, (b.obj_subsystem hr2).sub hYD, rfl⟩
  | .oplus a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.oplus a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D, hD, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        refine ⟨D, hD, Or.inr (Or.inl ⟨X, hXD, ?_, rfl⟩)⟩
        exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D hD)).master_eq)
      · obtain ⟨D, hD, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        refine ⟨D, hD, Or.inr (Or.inr ⟨Y, hYD, ?_, rfl⟩)⟩
        exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D hD)).master_eq)
  | .otimes a b, _, _, hdir, hne, hsub, hU, _, hmem => by
      rcases hmem with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨D, hD⟩ := hne
        exact ⟨D, hD, Or.inl ((GExpr.otimes a b).obj_subsystem (hsub D hD)).master_eq.symm⟩
      · obtain ⟨D₁, hD₁, hXD⟩ := a.obj_continuous_mp hdir hne hsub hU hX
        obtain ⟨D₂, hD₂, hYD⟩ := b.obj_continuous_mp hdir hne hsub hU hY
        obtain ⟨D₃, hD₃, hr1, hr2⟩ := hdir D₁ hD₁ D₂ hD₂
        refine ⟨D₃, hD₃, Or.inr ⟨X, Y, (a.obj_subsystem hr1).sub hXD,
          (b.obj_subsystem hr2).sub hYD, ?_, ?_, rfl⟩⟩
        · exact fun heq => hXne (heq.trans (a.obj_subsystem (hsub D₃ hD₃)).master_eq)
        · exact fun heq => hYne (heq.trans (b.obj_subsystem (hsub D₃ hD₃)).master_eq)

/-- **`λD. T(D)` is continuous on domains.** -/
theorem GExpr.obj_continuous (T : GExpr) {ℱ : Set ScottSys} {U : ScottSys}
    (hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ) (hne : ℱ.Nonempty)
    (hsub : ∀ D ∈ ℱ, D.sys ◁ U.sys) (hU : ∀ X, U.sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X)
    (W : Set Str) : (T.obj U).sys.mem W ↔ ∃ D ∈ ℱ, (T.obj D).sys.mem W := by
  refine ⟨T.obj_continuous_mp hdir hne hsub hU, ?_⟩
  rintro ⟨D, hD, hmem⟩
  exact (T.obj_subsystem (hsub D hD)).sub hmem

/-! ### Continuous on maps -/

/-- Forward direction of continuity on maps for `GExpr`. -/
theorem GExpr.map_continuous_mp : (T : GExpr) → {I : Type} → {X Y : ScottSys} →
    {g : I → ApproximableMap X.sys Y.sys} → {f : ApproximableMap X.sys Y.sys} →
    [Nonempty I] → (∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k) →
    (∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) →
    {A B : Set Str} → (T.map f).rel A B → ∃ i, (T.map (g i)).rel A B
  | .const _, _, _, _, _, _, _, _, _, _, _, hrel => by
      obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, hrel⟩
  | .var, _, _, _, _, _, _, _, hf, A, B, hrel => (hf A B).mp hrel
  | .sum a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, rfl, rfl⟩ | ⟨Q, Q', hr, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, rfl, rfl⟩)⟩
  | .prod a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      obtain ⟨P, Q, P', Q', hr0, hr1, rfl, rfl⟩ := hrel
      obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
      obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj, rfl, rfl⟩
  | .oplus a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, P', hr, hPne, hP'ne, rfl, rfl⟩ |
        ⟨Q, Q', hr, hQne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inl ⟨P, P', hi, hPne, hP'ne, rfl, rfl⟩)⟩
      · obtain ⟨i, hi⟩ := b.map_continuous_mp hdir hf hr
        exact ⟨i, Or.inr (Or.inr ⟨Q, Q', hi, hQne, hQ'ne, rfl, rfl⟩)⟩
  | .otimes a b, _, _, _, _, _, _, hdir, hf, _, _, hrel => by
      rcases hrel with ⟨hA, rfl⟩ | ⟨P, Q, P', Q', hr0, hr1, hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩
      · obtain ⟨i⟩ := ‹Nonempty _›; exact ⟨i, Or.inl ⟨hA, rfl⟩⟩
      · obtain ⟨i, hi⟩ := a.map_continuous_mp hdir hf hr0
        obtain ⟨j, hj⟩ := b.map_continuous_mp hdir hf hr1
        obtain ⟨k, hik, hjk⟩ := hdir i j
        exact ⟨k, Or.inr ⟨P, Q, P', Q', (a.map_mono hik) P P' hi, (b.map_mono hjk) Q Q' hj,
          hPne, hQne, hP'ne, hQ'ne, rfl, rfl⟩⟩

/-- **`λf. T(f)` is continuous on maps.** -/
theorem GExpr.map_continuous (T : GExpr) {I : Type} [Nonempty I] {X Y : ScottSys}
    (g : I → ApproximableMap X.sys Y.sys) (f : ApproximableMap X.sys Y.sys)
    (hdir : ∀ i j, ∃ k, g i ≤ g k ∧ g j ≤ g k)
    (hf : ∀ A B, f.rel A B ↔ ∃ i, (g i).rel A B) (A B : Set Str) :
    (T.map f).rel A B ↔ ∃ i, (T.map (g i)).rel A B := by
  refine ⟨T.map_continuous_mp hdir hf, ?_⟩
  rintro ⟨i, hi⟩
  have hgif : g i ≤ f := by
    rw [ApproximableMap.le_iff]; intro A' B' h; exact (hf A' B').mpr ⟨i, h⟩
  exact (T.map_mono hgif) A B hi

/-! ## Exercise 6.20 for the extended algebra — `λΓ. tok(T({Γ}))` is continuous, so a fixed point
exists

The masters of `⊕`/`⊗` coincide with those of `+`/`×` (all four equal `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`), so the
token-level recursion `gFun` has the **same** tagged-union body in all four binary cases. The 6.20
argument (continuity of `λΓ. tok(T({Γ}))` and existence of `Γ = tok(T({Γ}))`, whence
`{Γ} ◁ T({Γ})` and Theorem 6.14 applies) goes through verbatim, reusing the generic helpers
`singletonSys`, `insertTag_mono`, `insertTag_continuous` of Exercise 6.19 Part B. -/

/-- **The token-level master recursion for `GExpr`.** All four binary operations share the same body
(`sumTokMaster = prodTokNbhd` on masters). -/
def gFun : GExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .prod a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .oplus a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .otimes a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))

/-- `gFun T Γ = tok(T({Γ}))`. -/
theorem gFun_eq_master : (T : GExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    gFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .prod a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .oplus a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]
  | .otimes a b, Γ, h => by
      show insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
        = insert ([] : Str) (embBit false ((a.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((b.obj (singletonSys Γ h)).sys.master))
      rw [gFun_eq_master a h, gFun_eq_master b h]

/-- **`λΓ. tok(T({Γ}))` is monotone.** -/
theorem gFun_mono (T : GExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : gFun T Γ ⊆ gFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | oplus a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | otimes a b ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-- **`λΓ. tok(T({Γ}))` is continuous on `{Γ ∣ Λ ∈ Γ}`.** -/
theorem gFun_continuous (T : GExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ gFun T U ↔ ∃ Γ ∈ ℱ, w ∈ gFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | oplus a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | otimes a b ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** -/
def GExpr.RootedConst : GExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst
  | .oplus a b => a.RootedConst ∧ b.RootedConst
  | .otimes a b => a.RootedConst ∧ b.RootedConst

theorem gFun_nil_mem : ∀ (T : GExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ gFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _
  | .oplus _ _, _, _, _ => Set.mem_insert _ _
  | .otimes _ _, _, _, _ => Set.mem_insert _ _

/-- The **Kleene iteration** `gFunⁿ({Λ})`. -/
def gIter (T : GExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => gFun T (gIter T n)

theorem nil_mem_gIter (T : GExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ gIter T n
  | 0 => rfl
  | n + 1 => gFun_nil_mem T hT (nil_mem_gIter T hT n)

theorem gIter_mono_step (T : GExpr) (hT : T.RootedConst) :
    ∀ n, gIter T n ⊆ gIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact gFun_nil_mem T hT rfl
  | n + 1 => gFun_mono T (gIter_mono_step T hT n)

theorem gIter_mono (T : GExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    gIter T m ⊆ gIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact gIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem gFun_iter_fixed (T : GExpr) (hT : T.RootedConst) :
    gFun T (⋃ n, gIter T n) = ⋃ n, gIter T n := by
  have hstep := gIter_mono_step T hT
  have hne : (Set.range (gIter T)).Nonempty := ⟨gIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (gIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨gIter T (max i j), ⟨max i j, rfl⟩,
      gIter_mono T hT (le_max_left i j), gIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, gIter T n) ↔ ∃ S ∈ Set.range (gIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨gIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [gFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨gIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **Exercise 6.21/6.20 (token level).** For any `GExpr` `T` whose constants contain `Λ`, there is a
set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem gExists_tok_fixedPoint (T : GExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ gFun T Γ = Γ :=
  ⟨⋃ n, gIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_gIter T hT 0⟩, gFun_iter_fixed T hT⟩

/-- **Exercise 6.21/6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies** for any construct
`T` built from constants, identity, `+`, `×`, `⊕`, `⊗`. -/
theorem gExists_singleton_subsystem (T : GExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := gExists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (gFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · exact hmaster.symm
  · intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]

/-! ## Generalizing `+`, `×`, `⊕`, `⊗` to combinations of several terms

> Generalize all of `+`, `×`, `⊕`, `⊗` to combinations of several terms, not just the binary sums
> and products.

Because `GExpr` is **closed** under the binary operations, every finite combination of several terms
`T₀ ⋆ T₁ ⋆ ⋯ ⋆ Tₙ` (for any `⋆ ∈ {+, ×, ⊕, ⊗}`, in any nesting) is itself a `GExpr` — so the
results already proved (`map_id`, `map_comp`, `map_mono`, `map_continuous`, `obj_subsystem`,
`obj_continuous`, and the 6.20 fixed point `gExists_singleton_subsystem`) apply to *all* of them with
no further work. The `naryOp` fold below packages the common right-nested n-ary constructs
`⋆(a, [b, c, …]) = a ⋆ (b ⋆ (c ⋆ ⋯))` explicitly, and `naryOp_rootedConst` shows the `Λ ∈ tok`
side-condition (needed for the 6.20 fixed point) is preserved, so every n-ary construct also has a
solution `Γ = tok(T({Γ}))`. -/

/-- **Right-nested n-ary fold** of a binary construct-operation `op` over a non-empty list `a, l…`.
With `op = .sum`/`.prod`/`.oplus`/`.otimes` this is the n-ary `+`/`×`/`⊕`/`⊗`. -/
def GExpr.naryOp (op : GExpr → GExpr → GExpr) (a : GExpr) : List GExpr → GExpr
  | [] => a
  | b :: l => op a (GExpr.naryOp op b l)

/-- n-ary separated sum `T₀ + T₁ + ⋯ + Tₙ`. -/
def GExpr.narySum : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.sum

/-- n-ary separated product `T₀ × T₁ × ⋯ × Tₙ`. -/
def GExpr.naryProd : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.prod

/-- n-ary coalesced sum `T₀ ⊕ T₁ ⊕ ⋯ ⊕ Tₙ`. -/
def GExpr.naryOplus : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.oplus

/-- n-ary smash product `T₀ ⊗ T₁ ⊗ ⋯ ⊗ Tₙ`. -/
def GExpr.naryOtimes : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.otimes

/-- The `Λ ∈ tok` side-condition is preserved by any n-ary fold whose binary operation preserves it
(all four of `+`, `×`, `⊕`, `⊗` do, definitionally). -/
theorem GExpr.naryOp_rootedConst {op : GExpr → GExpr → GExpr}
    (hop : ∀ x y, (op x y).RootedConst ↔ x.RootedConst ∧ y.RootedConst) :
    ∀ (a : GExpr) (l : List GExpr), a.RootedConst → (∀ b ∈ l, b.RootedConst) →
      (GExpr.naryOp op a l).RootedConst
  | a, [], ha, _ => ha
  | a, b :: l, ha, hl => by
      rw [GExpr.naryOp, hop]
      exact ⟨ha, GExpr.naryOp_rootedConst hop b l (hl b (List.mem_cons_self ..))
        (fun c hc => hl c (List.mem_cons_of_mem _ hc))⟩

/-- **Every n-ary construct has a solution `Γ = tok(T({Γ}))`** (so `{Γ} ◁ T({Γ})` and 6.14 applies),
illustrated for the n-ary separated sum; identical for `naryProd`/`naryOplus`/`naryOtimes`. -/
theorem narySum_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.narySum a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

theorem naryOplus_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryOplus a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

theorem naryProd_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryProd a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

theorem naryOtimes_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryOtimes a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise626.lean -/

/-!
# Exercise 6.26 (Scott 1981, PRG-19, §6) — the lifting `𝒟_⊥` over `{0,1}*`

> **EXERCISE 6.26.** For systems `𝒟` as in 6.19 define
> `𝒟_⊥ = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ 𝒟}`.
> Describe the construct in terms of elements. Is this a suitable functor? Prove that
> `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`. What is `𝒟_⊥ ⊗ ℰ_⊥ ≅ ??`

The **lifting** `𝒟_⊥` adds a *new bottom* below a `0`-tagged copy of `𝒟`. Its master is
`{Λ} ∪ 0Δ` and its proper neighbourhoods are the `0X` for `X ∈ 𝒟` (including `0Δ`, which sits
strictly above the new bottom `{{Λ} ∪ 0Δ}`). It is the one-summand analogue of Exercise 6.19's sum.

## Contents

* `liftTok`/`ScottSys.lift` — the lifted system over `Str = {0,1}*`, again `∅`-free.
* **Elements** (`liftBot`, `liftUp`, `unlift`): `|𝒟_⊥| ≅ |𝒟|_⊥`. The bottom `liftBot` is the fresh
  least element; `liftUp x` embeds `|𝒟|` order-isomorphically *above* it (`liftBot_lt_liftUp`,
  `liftUp_le_liftUp_iff`); every element is one or the other (`eq_liftBot_or_exists_liftUp`).
* **Functor** (`liftMapTok`, `liftMapTok_isStrict`, `liftMapTok_id`, `liftMapTok_comp`): *yes*, `(·)_⊥`
  is a (strict) functor on Scott's category — the action on maps preserves identities and composition.
* **`𝒟_⊥ ⊕ ℰ_⊥ ≅ᴰ 𝒟 + ℰ`** (`lift_oplus_lift_iso_sum`): coalescing the two fresh bottoms of the
  lifts reproduces exactly the separated sum.
* **`𝒟_⊥ ⊗ ℰ_⊥ ≅ᴰ (𝒟 × ℰ)_⊥`** (`lift_otimes_lift_iso_lift_prod`): the answer to Scott's `??` — the
  smash of two lifts is the lift of the product.

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the lone exception
is `eq_liftBot_or_exists_liftUp`, a `Prop`-level case split that uses excluded middle (`Classical`)
to decide whether an element lies above the fresh bottom — unavoidable and called out there.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise619
open Scott1980.Neighborhood.Example62 Scott1980.Neighborhood.ExampleB
open Scott1980.Neighborhood.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-! ## The lifted system `𝒟_⊥` over `{0,1}*` -/

/-- The master neighbourhood `{Λ} ∪ 0Δ` of the lift. -/
def liftTokMaster (D : NeighborhoodSystem Str) : Set Str := insert [] (embBit false D.master)

theorem nil_mem_liftTokMaster : ([] : Str) ∈ liftTokMaster D := Set.mem_insert _ _

theorem embF_subset_liftTokMaster {X : Set Str} (hX : D.mem X) :
    embBit false X ⊆ liftTokMaster D :=
  (embBit_subset.mpr (D.sub_master hX)).trans (Set.subset_insert _ _)

theorem liftTokMaster_inter_embF {X : Set Str} (hX : D.mem X) :
    liftTokMaster D ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_liftTokMaster hX)

theorem embF_ne_liftTokMaster {X : Set Str} : embBit false X ≠ liftTokMaster D := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_liftTokMaster)

/-- **Exercise 6.26 — the lifted system `𝒟_⊥` over `{0,1}*`.** A neighbourhood is the master
`{Λ} ∪ 0Δ` or a tagged copy `0X` (`X ∈ 𝒟`). `∅`-freeness of `𝒟` (`hD`) keeps it `∅`-free. -/
def liftTok (D : NeighborhoodSystem Str) (_hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem Str where
  mem W := W = liftTokMaster D ∨ ∃ X, D.mem X ∧ W = embBit false X
  master := liftTokMaster D
  master_nonempty := ⟨[], nil_mem_liftTokMaster⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact subset_rfl
    · exact embF_subset_liftTokMaster hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [liftTokMaster_inter_embF hX']; exact Or.inr ⟨X', hX', rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · rw [Set.inter_comm, liftTokMaster_inter_embF hX]; exact Or.inr ⟨X, hX, rfl⟩
      · rw [embBit_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z', hZ', rfl⟩
        · exact absurd (hZsub nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X ∩ X', D.inter_mem hX hX' hZ' (embBit_subset.mp hZsub), rfl⟩

theorem liftTok_nonempty (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ W, (liftTok D hD).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩)
  · exact ⟨[], nil_mem_liftTokMaster⟩
  · exact embBit_nonempty (hD X hX)

/-- The **lift object** `𝒟_⊥` of Scott's category. -/
def ScottSys.lift (A : ScottSys) : ScottSys := ⟨liftTok A.sys A.ne, liftTok_nonempty A.ne⟩

variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_master : (liftTok D hD).mem (liftTokMaster D) := Or.inl rfl

theorem liftTok_mem_embF {X : Set Str} (hX : D.mem X) :
    (liftTok D hD).mem (embBit false X) := Or.inr ⟨X, hX, rfl⟩

theorem liftTok_mem_embF_inv {W : Set Str} (h : (liftTok D hD).mem (embBit false W)) : D.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX

/-! ## Elements: `|𝒟_⊥| ≅ |𝒟|_⊥` -/

/-- The **fresh bottom** of `𝒟_⊥`: the element whose only neighbourhood is the master `{Λ} ∪ 0Δ`. -/
def liftBot (D : NeighborhoodSystem Str) (hD : ∀ X, D.mem X → X.Nonempty) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D
  sub := by rintro W rfl; exact Or.inl rfl
  master_mem := rfl
  inter_mem := by rintro W W' rfl rfl; rw [Set.inter_self]
  up_mem := by
    rintro W W' rfl hW' hsub
    exact Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub

/-- The **embedding** `|𝒟| ↪ |𝒟_⊥|`: `liftUp x = {{Λ} ∪ 0Δ} ∪ {0X ∣ X ∈ x}`, the image of `x`
sitting above the fresh bottom. -/
def liftUp {D : NeighborhoodSystem Str} {hD : ∀ X, D.mem X → X.Nonempty} (x : D.Element) :
    (liftTok D hD).Element where
  mem W := W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, x.sub hX, rfl⟩
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [liftTokMaster_inter_embF (x.sub hX')]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, liftTokMaster_inter_embF (x.sub hX)]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embBit_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((liftTok D hD).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', x.up_mem hX hX' (embBit_subset.mp hsub), rfl⟩

@[simp] theorem mem_liftBot {W : Set Str} : (liftBot D hD).mem W ↔ W = liftTokMaster D := Iff.rfl

@[simp] theorem mem_liftUp {x : D.Element} {W : Set Str} :
    (liftUp (hD := hD) x).mem W ↔ W = liftTokMaster D ∨ ∃ X, x.mem X ∧ W = embBit false X := Iff.rfl

/-- `liftBot` is the least element of `𝒟_⊥`. -/
theorem liftBot_le (z : (liftTok D hD).Element) : liftBot D hD ≤ z := by
  rintro W rfl; exact z.master_mem

/-- `liftUp` is an order embedding: `liftUp x ⊑ liftUp y ↔ x ⊑ y`. -/
theorem liftUp_le_liftUp_iff {x y : D.Element} :
    liftUp (hD := hD) x ≤ liftUp (hD := hD) y ↔ x ≤ y := by
  constructor
  · intro h X hX
    have hmem := h (embBit false X) (Or.inr ⟨X, hX, rfl⟩)
    rcases hmem with h0 | ⟨X', hX', heq⟩
    · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rw [embBit_injective heq]; exact hX'
  · rintro h W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h X hX, rfl⟩

/-- The fresh bottom is *strictly* below every lifted element. -/
theorem liftBot_lt_liftUp (x : D.Element) : liftBot D hD < liftUp (hD := hD) x := by
  refine lt_of_le_of_ne (liftBot_le _) (fun heq => ?_)
  have hmem : (liftBot D hD).mem (embBit false D.master) := by
    rw [heq]; exact Or.inr ⟨D.master, x.master_mem, rfl⟩
  exact embF_ne_liftTokMaster hmem

/-- The **unlift** of an element that lies above the fresh bottom (i.e. contains `0Δ`): the
`𝒟`-element `{X ∣ 0X ∈ z}`. -/
def unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) : D.Element where
  mem X := z.mem (embBit false X)
  sub := fun hX => liftTok_mem_embF_inv (z.sub hX)
  master_mem := hz
  inter_mem := by
    intro X X' hX hX'
    have hz' := z.inter_mem hX hX'
    rwa [embBit_inter] at hz'
  up_mem := by
    intro X Y hX hY hXY
    exact z.up_mem hX (liftTok_mem_embF hY) (embBit_subset.mpr hXY)

theorem liftUp_unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) :
    liftUp (hD := hD) (unlift z hz) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl⟩)
    · exact z.master_mem
    · exact hX
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, hW, rfl⟩

/-- **Exercise 6.26 — "describe in terms of elements".** Every element of `𝒟_⊥` is either the fresh
bottom or a lifted `𝒟`-element: `|𝒟_⊥| ≅ |𝒟|_⊥`. (`Prop`-level; the case split on "does `z` contain
`0Δ`?" uses excluded middle — the only non-constructive step in this module.) -/
theorem eq_liftBot_or_exists_liftUp (z : (liftTok D hD).Element) :
    z = liftBot D hD ∨ ∃ x : D.Element, z = liftUp (hD := hD) x := by
  by_cases hz : z.mem (embBit false D.master)
  · exact Or.inr ⟨unlift z hz, (liftUp_unlift z hz).symm⟩
  · refine Or.inl ?_
    apply NeighborhoodSystem.Element.ext
    intro W
    constructor
    · intro hW
      rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
      · rfl
      · exact absurd
          (z.up_mem hW (liftTok_mem_embF D.master_mem) (embBit_subset.mpr (D.sub_master hX))) hz
    · rintro rfl; exact z.master_mem

/-! ## Functoriality: `(·)_⊥` is a strict functor -/

variable {A B C : ScottSys}

/-- **`f_⊥`, the action of lifting on (approximable) maps.** It carries the master to the master (so
it is strict) and a copy `0X` to `0X'` whenever `X f X'`. -/
def liftMapTok (f : ApproximableMap A.sys B.sys) :
    ApproximableMap (ScottSys.lift A).sys (ScottSys.lift B).sys where
  rel W W' :=
    ((liftTok A.sys A.ne).mem W ∧ W' = liftTokMaster B.sys) ∨
    (∃ X X', f.rel X X' ∧ W = embBit false X ∧ W' = embBit false X')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩)
    · exact hW
    · exact liftTok_mem_embF (hD := A.ne) (f.rel_dom hrel)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact liftTok_mem_embF (hD := B.ne) (f.rel_cod hrel)
  master_rel := Or.inl ⟨(ScottSys.lift A).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr ⟨X, X', hrel, hWeq, by rw [liftTokMaster_inter_embF (f.rel_cod hrel)]⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr ⟨X, X', hrel, rfl, ?_⟩
        rw [Set.inter_comm, liftTokMaster_inter_embF (f.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr ⟨X, X' ∩ X'₂, f.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hZmem hZ'mem
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩
    · exact Or.inl ⟨hZmem, Set.Subset.antisymm ((ScottSys.lift B).sys.sub_master hZ'mem) hZZ'⟩
    · rcases hZ'mem with rfl | ⟨X₃, hX₃, rfl⟩
      · exact Or.inl ⟨hZmem, rfl⟩
      · rcases hZmem with rfl | ⟨X₂, hX₂, rfl⟩
        · exact absurd (hWW nil_mem_liftTokMaster) nil_not_mem_embBit
        · exact Or.inr ⟨X₂, X₃,
            f.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩

/-- **`f_⊥` is strict** for *any* `f`: the master `Λ`-bearing input relates only to the master. -/
theorem liftMapTok_isStrict (f : ApproximableMap A.sys B.sys) : IsStrict (liftMapTok f) := by
  rintro Y (⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩)
  · rfl
  · have hnil : ([] : Str) ∈ embBit false X := by
      rw [← heq]; exact nil_mem_liftTokMaster
    exact absurd hnil nil_not_mem_embBit

/-- **`(I_𝒟)_⊥ = I_{𝒟_⊥}`.** -/
theorem liftMapTok_id : liftMapTok (idMap A.sys) = idMap (ScottSys.lift A).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (ScottSys.lift A).sys.master_mem, (ScottSys.lift A).sys.sub_master hW⟩
    · exact ⟨liftTok_mem_embF (hD := A.ne) hX, liftTok_mem_embF (hD := A.ne) hX',
        embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩
      · exact absurd (hsub nil_mem_liftTokMaster) nil_not_mem_embBit
      · exact Or.inr ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩

/-- **`(g ∘ f)_⊥ = g_⊥ ∘ f_⊥`.** -/
theorem liftMapTok_comp (f : ApproximableMap A.sys B.sys) (g : ApproximableMap B.sys C.sys) :
    liftMapTok (g.comp f) = (liftMapTok g).comp (liftMapTok f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩)
    · exact ⟨liftTokMaster B.sys, Or.inl ⟨hW, rfl⟩,
        Or.inl ⟨(ScottSys.lift B).sys.master_mem, rfl⟩⟩
    · exact ⟨embBit false X', Or.inr ⟨X, X', hf, rfl, rfl⟩, Or.inr ⟨X', X'', hg, rfl, rfl⟩⟩
  · rintro ⟨W', hWW', hW'W''⟩
    rcases hWW' with ⟨hW, rfl⟩ | ⟨X, X', hf, rfl, rfl⟩
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X, X', -, heq, -⟩
      · exact Or.inl ⟨hW, rfl⟩
      · exact absurd (heq ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rcases hW'W'' with ⟨-, rfl⟩ | ⟨X₂, X'', hg, heq, rfl⟩
      · exact Or.inl ⟨liftTok_mem_embF (hD := A.ne) (f.rel_dom hf), rfl⟩
      · obtain rfl := embBit_injective heq
        exact Or.inr ⟨X, X'', ⟨X', hf, hg⟩, rfl, rfl⟩

/-! ## `𝒟_⊥ ⊕ ℰ_⊥ ≅ᴰ 𝒟 + ℰ`

The coalesced sum of the two lifts has tokens `0·0·X'` (`X' ∈ 𝒟`) and `1·0·Y'` (`Y' ∈ ℰ`), with the
shared bottom `{Λ} ∪ 0(liftTokMaster 𝒟) ∪ 1(liftTokMaster ℰ)`. The separated sum `𝒟 + ℰ` has tokens
`0X'`, `1Y'`. The element iso simply *deletes the inner `0`*. The cross-tag intersections vanish
(`∅`-freeness), exactly as in Exercise 6.19's `toSum`/`fromSum`. -/

variable {D E : ScottSys}

theorem o_mem_embFF {X' : Set Str} (hX' : D.sys.mem X') :
    (D.lift.oplus E.lift).sys.mem (embBit false (embBit false X')) :=
  oplusTok_mem_embF (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := D.ne) hX') (embF_ne_liftTokMaster (D := D.sys))

theorem o_mem_embTF {Y' : Set Str} (hY' : E.sys.mem Y') :
    (D.lift.oplus E.lift).sys.mem (embBit true (embBit false Y')) :=
  oplusTok_mem_embT (h₀ := D.lift.ne) (h₁ := E.lift.ne)
    (liftTok_mem_embF (hD := E.ne) hY') (embF_ne_liftTokMaster (D := E.sys))

theorem o_embFF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit false (embBit false W))) : D.sys.mem W :=
  liftTok_mem_embF_inv (hD := D.ne)
    (oplusTok_mem_embF_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

theorem o_embTF_inv {W : Set Str}
    (h : (D.lift.oplus E.lift).sys.mem (embBit true (embBit false W))) : E.sys.mem W :=
  liftTok_mem_embF_inv (hD := E.ne)
    (oplusTok_mem_embT_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys)
      (h₀ := D.lift.ne) (h₁ := E.lift.ne) h)

/-- The forward half `|𝒟_⊥ ⊕ ℰ_⊥| → |𝒟 + ℰ|`: delete the inner `0`. -/
def toSumLift (z : (D.lift.oplus E.lift).sys.Element) : (D.sum E).sys.Element where
  mem W := W = sumTokMaster D.sys E.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false X ∧ z.mem (embBit false (embBit false X)))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true Y ∧ z.mem (embBit true (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX
    · exact sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embBit_inter, embBit_inter] at hz
        exact o_embFF_inv (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embBit_inter, embBit_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hz
      obtain ⟨t, ht⟩ := (D.lift.oplus E.lift).ne _ (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embBit_inter, embBit_inter] at hz
        exact o_embTF_inv (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embBit_inter, embBit_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.sum E).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X'', hX'', rfl, ?_⟩)
        exact z.up_mem hzX (o_mem_embFF hX'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide) (D.ne X hX) hs)
    · rcases hW' with rfl | ⟨X'', hX'', rfl⟩ | ⟨Y'', hY'', rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide) (E.ne Y hY) hs)
      · refine Or.inr (Or.inr ⟨Y'', hY'', rfl, ?_⟩)
        exact z.up_mem hzY (o_mem_embTF hY'')
          (embBit_subset.mpr (embBit_subset.mpr (embBit_subset.mp hsub)))

@[simp] theorem toSumLift_mem_embF {z : (D.lift.oplus E.lift).sys.Element} {X : Set Str}
    (hX : D.sys.mem X) :
    (toSumLift z).mem (embBit false X) ↔ z.mem (embBit false (embBit false X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (D.ne X hX))
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toSumLift_mem_embT {z : (D.lift.oplus E.lift).sys.Element} {Y : Set Str}
    (hY : E.sys.mem Y) :
    (toSumLift z).mem (embBit true Y) ↔ z.mem (embBit true (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide) (E.ne Y hY))
    · rwa [embBit_injective heq]
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-- The inverse half `|𝒟 + ℰ| → |𝒟_⊥ ⊕ ℰ_⊥|`: reinstate the inner `0`. -/
def fromSumLift (s : (D.sum E).sys.Element) : (D.lift.oplus E.lift).sys.Element where
  mem W := W = sumTokMaster D.lift.sys E.lift.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false (embBit false X) ∧ s.mem (embBit false X))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true (embBit false Y) ∧ s.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact o_mem_embFF hX
    · exact o_mem_embTF hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr (Or.inl ⟨X', hX', ?_, hsX'⟩)
      rw [sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX')]
    · refine Or.inr (Or.inr ⟨Y', hY', ?_, hsY'⟩)
      rw [sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY')]
    · refine Or.inr (Or.inl ⟨X, hX, ?_, hsX⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX)]
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [embBit_inter] at hs
        exact sumTok_mem_embF_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [embBit_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y, hY, ?_, hsY⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY)]
    · exfalso
      have hs := s.inter_mem hsY hsX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [embBit_inter] at hs
        exact sumTok_mem_embT_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [embBit_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.oplus E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hV with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inl ⟨X'', hX''D, rfl, ?_⟩)
          exact s.up_mem hsX (sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX''D)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide)
            (embBit_nonempty (D.ne X hX)) hs)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide)
            (embBit_nonempty (E.ne Y hY)) hs)
      · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inr ⟨Y'', hY''E, rfl, ?_⟩)
          exact s.up_mem hsY (sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY''E)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))

@[simp] theorem fromSumLift_mem_embFF {s : (D.sum E).sys.Element} {X : Set Str} (hX : D.sys.mem X) :
    (fromSumLift s).mem (embBit false (embBit false X)) ↔ s.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective (embBit_injective heq)]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide)
        (embBit_nonempty (D.ne X hX)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromSumLift_mem_embTF {s : (D.sum E).sys.Element} {Y : Set Str} (hY : E.sys.mem Y) :
    (fromSumLift s).mem (embBit true (embBit false Y)) ↔ s.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide)
        (embBit_nonempty (E.ne Y hY)))
    · rwa [embBit_injective (embBit_injective heq)]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

theorem fromSumLift_toSumLift (z : (D.lift.oplus E.lift).sys.Element) :
    fromSumLift (toSumLift z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toSumLift_mem_embF hX).mp hs
    · exact (toSumLift_mem_embT hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X', hX'D, rfl⟩
      · exact absurd rfl hXne
      · exact Or.inr (Or.inl ⟨X', hX'D, rfl, (toSumLift_mem_embF hX'D).mpr hW⟩)
    · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
      · exact absurd rfl hYne
      · exact Or.inr (Or.inr ⟨Y', hY'E, rfl, (toSumLift_mem_embT hY'E).mpr hW⟩)

theorem toSumLift_fromSumLift (s : (D.sum E).sys.Element) :
    toSumLift (fromSumLift s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromSumLift_mem_embFF hX).mp hs
    · exact (fromSumLift_mem_embTF hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromSumLift_mem_embFF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromSumLift_mem_embTF hY).mpr hW⟩)

/-- The order-isomorphism `|𝒟_⊥ ⊕ ℰ_⊥| ≃o |𝒟 + ℰ|`. -/
def sumLiftEquiv : (D.lift.oplus E.lift).sys.Element ≃o (D.sum E).sys.Element where
  toFun := toSumLift
  invFun := fromSumLift
  left_inv := fromSumLift_toSumLift
  right_inv := toSumLift_fromSumLift
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X', hX'D, rfl⟩
        · exact absurd rfl hXne
        · exact (toSumLift_mem_embF hX'D).mp (h _ ((toSumLift_mem_embF hX'D).mpr hW))
      · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
        · exact absurd rfl hYne
        · exact (toSumLift_mem_embT hY'E).mp (h _ ((toSumLift_mem_embT hY'E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Exercise 6.26 — `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`.** Coalescing the fresh bottoms of the two lifts
reproduces the separated sum. -/
theorem lift_oplus_lift_iso_sum :
    (D.lift.oplus E.lift).sys ≅ᴰ (D.sum E).sys := ⟨sumLiftEquiv⟩

/-! ## `𝒟_⊥ ⊗ ℰ_⊥ ≅ᴰ (𝒟 × ℰ)_⊥` — the answer to Scott's `??`

The smash of the two lifts has proper neighbourhoods `{Λ} ∪ 0(0X') ∪ 1(0Y')` (i.e.
`prodTokNbhd (0X') (0Y')`, with `X' ∈ 𝒟`, `Y' ∈ ℰ`). The lift of the product has proper
neighbourhoods `0(prodTokNbhd X' Y')`. The element iso transports one rectangle presentation to the
other. Unlike the sum there are *no* cross-tag intersections, so the proof is purely "rectangular". -/

theorem ot_mem_prod {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y')) :=
  otimesTok_mem_prod (liftTok_mem_embF (hD := D.ne) hX') (liftTok_mem_embF (hD := E.ne) hY')
    (embF_ne_liftTokMaster (D := D.sys)) (embF_ne_liftTokMaster (D := E.sys))

theorem ot_mem_prod_inv {X' Y' : Set Str}
    (h : (D.lift.otimes E.lift).sys.mem (prodTokNbhd (embBit false X') (embBit false Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨h1, h2⟩ := otimesTok_mem_prod_inv (D₀ := D.lift.sys) (D₁ := E.lift.sys) h
    (embF_ne_liftTokMaster (D := D.sys))
  exact ⟨liftTok_mem_embF_inv (hD := D.ne) h1, liftTok_mem_embF_inv (hD := E.ne) h2⟩

theorem lp_mem_embF {X' Y' : Set Str} (hX' : D.sys.mem X') (hY' : E.sys.mem Y') :
    (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y')) :=
  liftTok_mem_embF (hD := (D.prod E).ne) (prodTok_mem_prodTokNbhd hX' hY')

theorem lp_prod_inv {X' Y' : Set Str}
    (h : (D.prod E).lift.sys.mem (embBit false (prodTokNbhd X' Y'))) :
    D.sys.mem X' ∧ E.sys.mem Y' := by
  obtain ⟨A, B, hA, hB, heq⟩ := liftTok_mem_embF_inv (hD := (D.prod E).ne) h
  obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
  exact ⟨hA, hB⟩

/-- The forward half `|𝒟_⊥ ⊗ ℰ_⊥| → |(𝒟 × ℰ)_⊥|`. -/
def toLiftProd (z : (D.lift.otimes E.lift).sys.Element) : (D.prod E).lift.sys.Element where
  mem W := W = liftTokMaster (prodTok D.sys E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = embBit false (prodTokNbhd X Y) ∧
        z.mem (prodTokNbhd (embBit false X) (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact lp_mem_embF hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hzXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hzXY'⟩
      rw [liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX' hY')]
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hzXY⟩
      rw [Set.inter_comm, liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX hY)]
    · have hz := z.inter_mem hzXY hzXY'
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter] at hz
      obtain ⟨hXi, hYi⟩ := ot_mem_prod_inv (z.sub hz)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hz⟩
      rw [embBit_inter, prodTokNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.prod E).lift.sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨Z, hZ, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X'', Y'', hX'', hY'', rfl⟩ := hZ
        refine Or.inr ⟨X'', Y'', hX'', hY'', rfl, ?_⟩
        obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp (embBit_subset.mp hsub)
        exact z.up_mem hzXY (ot_mem_prod hX'' hY'')
          (prodTokNbhd_subset_iff.mpr ⟨embBit_subset.mpr hsX, embBit_subset.mpr hsY⟩)

@[simp] theorem toLiftProd_mem_embF {z : (D.lift.otimes E.lift).sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (toLiftProd z).mem (embBit false (prodTokNbhd X Y)) ↔
      z.mem (prodTokNbhd (embBit false X) (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hz⟩)
    · exact absurd h0 (embF_ne_liftTokMaster (D := prodTok D.sys E.sys))
    · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective (embBit_injective heq); exact hz
  · intro hz; exact Or.inr ⟨X, Y, hX, hY, rfl, hz⟩

/-- The inverse half `|(𝒟 × ℰ)_⊥| → |𝒟_⊥ ⊗ ℰ_⊥|`. -/
def fromLiftProd (s : (D.prod E).lift.sys.Element) : (D.lift.otimes E.lift).sys.Element where
  mem W := W = prodTokNbhd (liftTokMaster D.sys) (liftTokMaster E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = prodTokNbhd (embBit false X) (embBit false Y) ∧
        s.mem (embBit false (prodTokNbhd X Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact ot_mem_prod hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hsXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hsXY'⟩
      rw [prodTokNbhd_inter, liftTokMaster_inter_embF hX', liftTokMaster_inter_embF hY']
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hsXY⟩
      rw [Set.inter_comm, prodTokNbhd_inter, liftTokMaster_inter_embF hX,
        liftTokMaster_inter_embF hY]
    · have hs := s.inter_mem hsXY hsXY'
      rw [embBit_inter, prodTokNbhd_inter] at hs
      obtain ⟨hXi, hYi⟩ := lp_prod_inv (s.sub hs)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hs⟩
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.otimes E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨U, V, hU, hV, hUne, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hU with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hUne
        · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hVne
          · refine Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, ?_⟩
            obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
            exact s.up_mem hsXY (lp_mem_embF hX''D hY''E)
              (embBit_subset.mpr (prodTokNbhd_subset_iff.mpr
                ⟨embBit_subset.mp hsX, embBit_subset.mp hsY⟩))

@[simp] theorem fromLiftProd_mem_prod {s : (D.prod E).lift.sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (fromLiftProd s).mem (prodTokNbhd (embBit false X) (embBit false Y)) ↔
      s.mem (embBit false (prodTokNbhd X Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hs⟩)
    · obtain ⟨hX0, -⟩ := prodTokNbhd_injective h0
      exact absurd hX0 (embF_ne_liftTokMaster (D := D.sys))
    · obtain ⟨hXe, hYe⟩ := prodTokNbhd_injective heq
      rw [embBit_injective hXe, embBit_injective hYe]; exact hs
  · intro hs; exact Or.inr ⟨X, Y, hX, hY, rfl, hs⟩

theorem fromLiftProd_toLiftProd (z : (D.lift.otimes E.lift).sys.Element) :
    fromLiftProd (toLiftProd z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toLiftProd_mem_embF hX hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
      · exact absurd rfl hXne
      · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hYne
        · exact Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, (toLiftProd_mem_embF hX''D hY''E).mpr hW⟩

theorem toLiftProd_fromLiftProd (s : (D.prod E).lift.sys.Element) :
    toLiftProd (fromLiftProd s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromLiftProd_mem_prod hX hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨Z, hZ, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, Y, hX, hY, rfl⟩ := hZ
      exact Or.inr ⟨X, Y, hX, hY, rfl, (fromLiftProd_mem_prod hX hY).mpr hW⟩

/-- The order-isomorphism `|𝒟_⊥ ⊗ ℰ_⊥| ≃o |(𝒟 × ℰ)_⊥|`. -/
def liftProdEquiv : (D.lift.otimes E.lift).sys.Element ≃o (D.prod E).lift.sys.Element where
  toFun := toLiftProd
  invFun := fromLiftProd
  left_inv := fromLiftProd_toLiftProd
  right_inv := toLiftProd_fromLiftProd
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hXne
        · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hYne
          · exact (toLiftProd_mem_embF hX''D hY''E).mp
              (h _ ((toLiftProd_mem_embF hX''D hY''E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, Y, hX, hY, rfl, h _ hzXY⟩

/-- **Exercise 6.26 — `𝒟_⊥ ⊗ ℰ_⊥ ≅ (𝒟 × ℰ)_⊥`** (the answer to Scott's `??`). The smash product of
two lifts is the lift of the product. -/
theorem lift_otimes_lift_iso_lift_prod :
    (D.lift.otimes E.lift).sys ≅ᴰ (D.prod E).lift.sys := ⟨liftProdEquiv⟩

end Exercise619

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Proposition66.lean -/

/-!
# Lecture VI — Proposition 6.6 (Scott 1981, PRG-19): initial algebras are uniquely isomorphic

**Proposition 6.6.** Any two initial `T`-algebras are uniquely isomorphic.

The proof is the standard diagram chase. If `A` and `B` are both initial, initiality gives unique
homomorphisms `f : A → B` and `g : B → A`. Their composites `g ∘ f : A → A` and `f ∘ g : B → B` are
homomorphisms, and by uniqueness of homomorphisms out of an initial algebra they must equal the
identity homomorphisms. Hence the underlying morphisms of `f` and `g` are mutually inverse, giving an
isomorphism `A.carrier ≅ B.carrier`. The isomorphism is *unique* in that the homomorphism `A → B`
realising it is the only one (`iso_hom_unique`).

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/-- Composing the two unique homomorphisms `A → B → A` gives the identity homomorphism on the initial
algebra `A`. -/
theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]

/-- **Proposition 6.6 (Scott 1981, PRG-19).** Any two initial `T`-algebras have isomorphic carriers;
the isomorphism is built from the unique homomorphisms in both directions. -/
def initialIso (hA : IsInitial A) (hB : IsInitial B) : Iso A.carrier B.carrier where
  hom := (hA.desc B).hom
  inv := (hB.desc A).hom
  hom_inv_id := by
    have h := comp_desc_eq_id hA hB
    have := congrArg AlgHom.hom h
    simpa using this
  inv_hom_id := by
    have h := comp_desc_eq_id hB hA
    have := congrArg AlgHom.hom h
    simpa using this

/-- The isomorphism of Proposition 6.6 is **unique**: the homomorphism `A → B` realising it is the
only homomorphism between the two initial algebras. -/
theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Proposition67.lean -/

/-!
# Lecture VI — Proposition 6.7 (Scott 1981, PRG-19): Lambek's lemma

**Proposition 6.7.** If `i : T(D) → D` is an initial `T`-algebra, then so is `T(i) : T²(D) → T(D)`
and `i` is the isomorphism from `T(D)` to `D`.

We formalise the second (and decisive) half: the structure map of an initial algebra is an
isomorphism. Writing `A = (D, i)`, the functor turns `i` into a new algebra `(T(D), T(i))` (`tStr`),
and `i` itself is a homomorphism `(T(D), T(i)) → (D, i)` (`strHom`). Initiality supplies a
homomorphism `j : (D,i) → (T(D),T(i))`, and the composite `i ∘ j : (D,i) → (D,i)` must be the
identity (`str_comp_desc`). Functoriality then gives `T(i) ∘ T(j) = T(i ∘ j) = I`, and the
homomorphism square for `j` yields `j ∘ i = I`. Hence `i` and `j` are mutually inverse: `i` is an
isomorphism (`lambek`).

This is exactly Scott's remark that "if we are going to have initial algebras at all we have to
satisfy the domain equation `D ≅ T(D)`".

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new `T`-algebra
`(T(D), T(i))`. -/
abbrev tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str

/-- The structure map `i : T(D) → D` is itself a homomorphism `(T(D), T(i)) → (D, i)`: the square
`i ∘ T(i) = i ∘ T(i)` commutes trivially. -/
def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl

/-- The composite `i ∘ j` of `i` with the descent homomorphism `j : (D,i) → (T(D),T(i))` is the
identity on `D`. -/
theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = Category.id A.carrier := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  exact congrArg AlgHom.hom h

/-- **Proposition 6.7 (Lambek's lemma; Scott 1981, PRG-19).** The structure map `i : T(D) → D` of an
initial `T`-algebra is an isomorphism `T(D) ≅ D`, with inverse the descent homomorphism `j`. -/
def lambek (A : TAlgebra T) (hA : IsInitial A) : Iso (T.obj A.carrier) A.carrier where
  hom := A.str
  inv := (hA.desc (tStr A)).hom
  inv_hom_id := str_comp_desc A hA
  hom_inv_id :=
    calc (hA.desc (tStr A)).hom ⊚ A.str
        = (tStr A).str ⊚ T.map (hA.desc (tStr A)).hom := (hA.desc (tStr A)).comm
      _ = T.map A.str ⊚ T.map (hA.desc (tStr A)).hom := rfl
      _ = T.map (A.str ⊚ (hA.desc (tStr A)).hom) := (T.map_comp _ _).symm
      _ = T.map (Category.id A.carrier) := by rw [str_comp_desc A hA]
      _ = Category.id (T.obj A.carrier) := T.map_id _

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Theorem41.lean -/

/-!
# Lecture IV (§4) — fixed points and recursion: Theorems 4.1 and 4.2

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture IV,
*Fixed points and recursion*. The heart of the matter is the **Fixed-point Theorem**:

* **Theorem 4.1** — every approximable mapping `f : 𝒟 → 𝒟` has a *least* element `x ∈ |𝒟|` with
  `f(x) = x`. Scott constructs `x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`, the family of neighbourhoods
  reachable from the master `Δ` along finitely many `f`-steps. We model the `n`-fold composition
  `fⁿ` by `iterMap f n` (`f⁰ = I_𝒟`, `f^{n+1} = f ∘ fⁿ`) and the fixed point by `fixElement f`.
  The fixed-point equation is `toElementMap_fixElement`; minimality among *pre-fixed* points
  (`f(z) ⊆ z ⟹ x ⊆ z`) is `fixElement_le_of_toElementMap_le`.

* **Theorem 4.2** — the operator `fix : (𝒟 → 𝒟) → 𝒟` is itself approximable. We build it as
  `fixMap V : ApproximableMap (funSpace V V) V` via the extension-from-finite-elements principle
  (Exercise 2.8, `ofMono`), sending the finite element `↑F` to `fix(↑F)` where `↑F = leastMap` is
  the least map of the neighbourhood `F` (here `toApproxMap (↑F)`). The defining computation
  `fixMap.toElementMap φ = fix(toApproxMap φ)` is Scott's equation (∗)
  `fix(f) = ⋃ {fix(↑F) ∣ f ∈ [F]}` (`fixMap_toElementMap`), whose non-trivial half — every
  finite `f`-chain factors through one finite approximant `F ∈ φ` — is `exists_principal_iterMap`.
  Then (i) `fix(f) = f(fix(f))` (`fixMap_fixed`); (ii) `f(x) ⊆ x ⟹ fix(f) ⊆ x` (`fixMap_least`);
  (iii) `fix(f) = ⊔ₙ fⁿ(⊥)` (`fixMap_eq_iSup`, with `iterElem_eq_iterate` giving the faithful
  `⊔ₙ fⁿ(⊥)` form); and uniqueness (`fixMap_unique`).

All *data* constructions (`iterMap`, `fixElement`, `iterElem`, `fixMap`) are **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the uniqueness lemma `fixMap_unique` pulls
`Classical.choice` only through the project's `ext_of_toElementMap`, as permitted.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The iterated map `fⁿ`. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The `n`-fold composition `fⁿ` of an endomap with itself:
`f⁰ = I_𝒟` and `f^{n+1} = f ∘ fⁿ`. -/
def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

@[simp] theorem iterMap_zero (f : ApproximableMap V V) : f.iterMap 0 = idMap V := rfl

@[simp] theorem iterMap_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterMap (n + 1) = f.comp (f.iterMap n) := rfl

/-- Composition is monotone in both arguments. -/
theorem comp_mono {f g a b : ApproximableMap V V} (hfg : f ≤ g) (hab : a ≤ b) :
    f.comp a ≤ g.comp b := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hab X Y hXY, hfg Y Z hYZ⟩

/-- The iterate is monotone in the map: `f ⊑ g ⟹ fⁿ ⊑ gⁿ` (Scott's "`fⁿ ⊆ gⁿ`"). -/
theorem iterMap_mono_map {f g : ApproximableMap V V} (hfg : f ≤ g) (n : ℕ) :
    f.iterMap n ≤ g.iterMap n := by
  induction n with
  | zero => show (idMap V) ≤ (idMap V); exact le_refl _
  | succ k ih => exact comp_mono hfg ih

/-- `f` commutes with its own iterate: `f ∘ fⁿ = fⁿ ∘ f`. Proved by induction using associativity
and the identity laws. -/
theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

/-- Scott's "a sequence for an `X ∈ x` can always be extended": if `Δ fⁿ X`, then `Δ f^{n+1} X`
(prepend a `Δ`-step, using `Δ f Δ`). -/
theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

/-- Monotonicity of the reachability relation in the number of steps: `n ≤ m` and `Δ fⁿ X` imply
`Δ fᵐ X`. -/
theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

/-! ### Theorem 4.1 — the least fixed point. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The least fixed point of `f`, Scott's
`x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`. The three filter conditions are exactly Scott's: `Δ ∈ x` (the
`n = 0` witness `I_𝒟`); closure under intersection follows from intersectivity (`inter_right`) of
the single iterate `f^{max n m}` reached by extending the shorter chain; upward closure is `mono`. -/
def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

@[simp] theorem mem_fixElement (f : ApproximableMap V V) {X : Set α} :
    f.fixElement.mem X ↔ ∃ n, (f.iterMap n).rel V.master X := Iff.rfl

/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is a *fixed point*: `f(x) = x`.
`f(x) ⊆ x` appends an `f`-step (`Δ f^{n+1} X` from `Δ fⁿ X' f X`); `x ⊆ f(x)` reads off the last
step of the chain (the empty chain forces `X = Δ`, handled by `master_mem`/`master_rel`). -/
theorem toElementMap_fixElement (f : ApproximableMap V V) :
    f.toElementMap f.fixElement = f.fixElement := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨n, hn⟩, hXY⟩
    exact ⟨n + 1, ⟨X, hn, hXY⟩⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      obtain ⟨_, hYmem, hmY⟩ := hn
      have hYmaster : Y = V.master := Set.Subset.antisymm (V.sub_master hYmem) hmY
      subst hYmaster
      exact ⟨V.master, f.fixElement.master_mem, f.master_rel⟩
    | succ k =>
      obtain ⟨Z, hZ, hZY⟩ := hn
      exact ⟨Z, ⟨k, hZ⟩, hZY⟩

/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is the *least pre-fixed point*: if
`f(z) ⊆ z`, then `x ⊆ z`. (Scott's induction: `Δ ∈ z`, and `X ∈ z`, `X f Y` give `Y ∈ f(z) ⊆ z`,
so `Δ fⁿ X` implies `X ∈ z`.) In particular `x` is the least element with `f(x) = x`. -/
theorem fixElement_le_of_toElementMap_le (f : ApproximableMap V V) {z : V.Element}
    (hz : f.toElementMap z ≤ z) : f.fixElement ≤ z := by
  have key : ∀ n X, (f.iterMap n).rel V.master X → z.mem X := by
    intro n
    induction n with
    | zero =>
      intro X hn
      obtain ⟨_, hXmem, hmX⟩ := hn
      have hXmaster : X = V.master := Set.Subset.antisymm (V.sub_master hXmem) hmX
      subst hXmaster
      exact z.master_mem
    | succ k ih =>
      intro X hn
      obtain ⟨W, hW, hWX⟩ := hn
      exact hz X ⟨W, ih W hW, hWX⟩
  rintro X ⟨n, hn⟩
  exact key n X hn

/-- The least fixed point is monotone in the map: `f ⊑ g ⟹ fix(f) ⊑ fix(g)` (immediate from
`iterMap_mono_map`; underlies the approximability of `fix` in 4.2). -/
theorem fixElement_mono {f g : ApproximableMap V V} (hfg : f ≤ g) :
    f.fixElement ≤ g.fixElement := by
  rintro X ⟨n, hn⟩
  exact ⟨n, iterMap_mono_map hfg n V.master X hn⟩

/-! ### Theorem 4.2(iii) — the iterates `fⁿ(⊥)`. -/

/-- The `n`-th approximant `fⁿ(⊥)` of the least fixed point. -/
def iterElem (f : ApproximableMap V V) (n : ℕ) : V.Element := (f.iterMap n).toElementMap V.bot

/-- `Y ∈ fⁿ(⊥) ↔ Δ fⁿ Y`: the `n`-th approximant is the family of neighbourhoods reachable from
`Δ` in exactly the `n` steps recorded by `fⁿ`. -/
theorem mem_iterElem (f : ApproximableMap V V) (n : ℕ) {X : Set α} :
    (f.iterElem n).mem X ↔ (f.iterMap n).rel V.master X := by
  constructor
  · rintro ⟨W, hW, hWX⟩
    rw [mem_bot] at hW; subst hW; exact hWX
  · intro h; exact ⟨V.master, by rw [mem_bot], h⟩

/-- The approximants form an increasing chain: `n ≤ m ⟹ fⁿ(⊥) ⊑ fᵐ(⊥)`. -/
theorem iterElem_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) :
    f.iterElem n ≤ f.iterElem m := by
  intro X hX
  rw [mem_iterElem] at hX ⊢
  exact rel_master_mono f hnm hX

/-- `fⁿ(⊥)` agrees with the iterated elementwise function `(f(·))^[n] ⊥` — Scott's `fⁿ(⊥)`. -/
theorem iterElem_eq_iterate (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n = (f.toElementMap)^[n] V.bot := by
  induction n with
  | zero =>
    show (f.iterMap 0).toElementMap V.bot = V.bot
    exact toElementMap_idMap V.bot
  | succ k ih =>
    have hstep : f.iterElem (k + 1) = f.toElementMap (f.iterElem k) := by
      show (f.comp (f.iterMap k)).toElementMap V.bot
          = f.toElementMap ((f.iterMap k).toElementMap V.bot)
      rw [toElementMap_comp]
    rw [hstep, ih, Function.iterate_succ', Function.comp_apply]

/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)`, here as the directed union of
the increasing chain of approximants. -/
theorem fixElement_eq_iSupDirected (f : ApproximableMap V V) :
    f.fixElement =
      NeighborhoodSystem.iSupDirected (f.iterElem)
        (fun i j => ⟨max i j, iterElem_mono f (le_max_left i j),
          iterElem_mono f (le_max_right i j)⟩) := by
  apply Element.ext
  intro X
  rw [NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap

/-! ### Theorem 4.2 — the approximable fixed-point operator `fix`. -/

open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19).** The fixed-point operator `fix : (𝒟 → 𝒟) → 𝒟` as an
approximable mapping. Built by the extension principle (Exercise 2.8, `ofMono`): on the finite
element `↑F` it returns `fix(↑F)`, where `↑F = toApproxMap (principal hF)` is the least map of the
neighbourhood `F` (Proposition 3.9). Monotonicity of `↑F ↦ fix(↑F)` is `fixElement_mono` composed
with the order-iso `funSpaceEquiv`. -/
def fixMap (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V :=
  ofMono (fun W hW => (toApproxMap ((funSpace V V).principal hW)).fixElement)
    (fun W W' hW hW' hW'W => by
      apply fixElement_mono
      exact (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff hW hW').mpr hW'W))

/-- On a finite element `↑F`, `fix` returns `fix(↑F)` (the least fixed point of the least map of
`F`). -/
theorem fixMap_toElementMap_principal (V : NeighborhoodSystem α)
    {W : Set (ApproximableMap V V)} (hW : (funSpace V V).mem W) :
    (fixMap V).toElementMap ((funSpace V V).principal hW) =
      (toApproxMap ((funSpace V V).principal hW)).fixElement :=
  toElementMap_ofMono_principal _ _ W hW

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗), hard half.** A finite `f`-chain
`Δ (toApproxMap φ)ⁿ X` factors through a *single* finite approximant `F ∈ φ`: there is a
neighbourhood `W ∈ φ` whose least map already realizes the same chain `Δ (↑W)ⁿ X`. The witness `W`
is accumulated as the intersection of the (finitely many) step-neighbourhoods used by the chain,
which lies in `φ` because `φ` is a filter. -/
theorem exists_principal_iterMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    ∀ (n : ℕ) (X : Set α), ((toApproxMap φ).iterMap n).rel V.master X →
      ∃ (W : Set (ApproximableMap V V)) (hw : φ.mem W),
        ((toApproxMap ((funSpace V V).principal (φ.sub hw))).iterMap n).rel V.master X := by
  intro n
  induction n with
  | zero =>
    intro X hX
    exact ⟨(funSpace V V).master, φ.master_mem, hX⟩
  | succ k ih =>
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hX
    obtain ⟨W₁, hw₁, hW₁⟩ := ih Y hY
    have hVY : V.mem Y := ((toApproxMap φ).iterMap k).rel_cod hY
    have hVX : V.mem X := (toApproxMap φ).rel_cod hYX
    have hw₂ : φ.mem (step Y X) := toApproxMap_rel.mp hYX
    have hwInter : φ.mem (W₁ ∩ step Y X) := φ.inter_mem hw₁ hw₂
    refine ⟨W₁ ∩ step Y X, hwInter, ?_⟩
    have hg₁g : toApproxMap ((funSpace V V).principal (φ.sub hw₁))
        ≤ toApproxMap ((funSpace V V).principal (φ.sub hwInter)) :=
      (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff (φ.sub hw₁) (φ.sub hwInter)).mpr Set.inter_subset_left)
    have hYg : ((toApproxMap ((funSpace V V).principal (φ.sub hwInter))).iterMap k).rel V.master Y :=
      iterMap_mono_map hg₁g k V.master Y hW₁
    have hgYX : (toApproxMap ((funSpace V V).principal (φ.sub hwInter))).rel Y X := by
      show ((funSpace V V).principal (φ.sub hwInter)).mem (step Y X)
      exact ⟨step_mem hVY hVX, Set.inter_subset_right⟩
    exact ⟨Y, hYg, hgYX⟩

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗).** The elementwise action of `fix` is
the least fixed point of the corresponding map: `fix.toElementMap φ = fix(toApproxMap φ)`. The
forward inclusion (`⊆ x`) is `exists_principal_iterMap`; the reverse is monotonicity of `fix` along
`↑W ⊑ toApproxMap φ`. -/
theorem fixMap_toElementMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ = (toApproxMap φ).fixElement := by
  apply Element.ext
  intro X
  rw [toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨W, hw, hmem⟩
    rw [fixMap_toElementMap_principal] at hmem
    have hle : (funSpace V V).principal (φ.sub hw) ≤ φ :=
      fun Z hZ => φ.up_mem hw hZ.1 hZ.2
    exact fixElement_mono ((funSpaceEquiv V V).monotone hle) X hmem
  · rintro ⟨n, hn⟩
    obtain ⟨W, hw, hWn⟩ := exists_principal_iterMap V φ n X hn
    refine ⟨W, hw, ?_⟩
    rw [fixMap_toElementMap_principal]
    exact ⟨n, hWn⟩

/-- **Theorem 4.2(i) (Scott 1981, PRG-19).** `fix(f) = f(fix(f))`: the value of `fix` is a fixed
point of the argument. (Equivalently `eval(f, fix(f)) = fix(f)` by `evalMap_apply`.) -/
theorem fixMap_fixed (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ := by
  rw [fixMap_toElementMap]
  exact toElementMap_fixElement (toApproxMap φ)

/-- **Theorem 4.2(ii) (Scott 1981, PRG-19).** `f(x) ⊆ x ⟹ fix(f) ⊆ x`: `fix` lands in the least
pre-fixed point. -/
theorem fixMap_least (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element}
    (hz : (toApproxMap φ).toElementMap z ≤ z) : (fixMap V).toElementMap φ ≤ z := by
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap φ) hz

/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)` (as a directed union). -/
theorem fixMap_eq_iSup (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ =
      NeighborhoodSystem.iSupDirected ((toApproxMap φ).iterElem)
        (fun i j => ⟨max i j, iterElem_mono _ (le_max_left i j),
          iterElem_mono _ (le_max_right i j)⟩) := by
  rw [fixMap_toElementMap]
  exact fixElement_eq_iSupDirected (toApproxMap φ)

/-- `fix` applied to (the filter of) an approximable map `f` returns the least fixed point of `f`.
This is the bridge to the "for any `f : 𝒟 → 𝒟`" form of Theorem 4.2, using the Theorem 3.10
isomorphism `toApproxMap (toFilter f) = f`. -/
theorem fixMap_toElementMap_toFilter (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    (fixMap V).toElementMap (toFilter f) = f.fixElement := by
  rw [fixMap_toElementMap]
  have h : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv V V).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  rw [h]

/-- **Theorem 4.2 (Scott 1981, PRG-19) — uniqueness.** Any approximable operator `fax` satisfying
(i) and (ii) coincides with `fix`. (Scott: from (i)(ii) one proves `fix(f) ⊆ fax(f)` and
`fax(f) ⊆ fix(f)`.) -/
theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Example44.lean -/

/-!
# Example 4.4 (Scott 1981, PRG-19, §4) — the domain `C` of binary sequences

Scott's domain `C` of *finite or infinite binary sequences* (pages 61–64), a generalization of the
natural-number domain `N` of Example 4.3. Over the tokens `Σ* = List Bool` (Scott's `Σ = {0,1}`,
`Λ = []`), recall the cones `cone σ = σΣ*` of Example 1.B. The system `C` adds the *singletons*:

`C = {σΣ* ∣ σ ∈ Σ*} ∪ {{σ} ∣ σ ∈ Σ*}`.

The total elements correspond to finite or infinite sequences: `σ = ↑{σ}` (`strElem σ`, the finite
sequence `σ` *completed*) and `σ⊥ = ↑σΣ*` (`strBot σ`, the partial element "starts with `σ`"). `C`
is again nested-or-disjoint, so it is a neighbourhood system (`ofNestedOrDisjoint`).

We equip `C` with the two **successors** `x ↦ 0x` and `x ↦ 1x` (`consMap false`, `consMap true`),
prepending a bit, with their action on the finite/partial elements (`consMap_strElem`,
`consMap_strBot`). As Scott's illustration that recursion now lives inside `|C|`, we then define the
alternating sequence `a = 01a` as the least fixed point of `x ↦ 0(1x)` (`altElt`, `altElt_eq`),
using the Fixed-point Theorem 4.1.

The remaining structure maps Scott lists for `⟨C, Λ, 0, 1, tail, empty, zero, one⟩` — the
predecessor analogue `tail` (`tail(0x) = tail(1x) = x`, `tail(Λ) = ⊥`) and the three tests
`empty, zero, one : C → T` — are exactly the parts Scott leaves as exercises ("It is left to the
reader to show that **tail** exists as an approximable mapping"; "it is an exercise to show these
are approximable", Exercise 4.19); they are out of scope for this module.

The data constructions (`C`, `consMap`) are **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`).
-/

namespace Scott1980.Neighborhood.Example44

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap ExampleB

/-! ### Prepending a bit: set-level lemmas (reused from Example 1.B). -/

/-- `σ{τ} = {στ}`: prepending `σ` to a singleton is the singleton of the concatenation. -/
theorem prepend_singleton (σ τ : Str) : prepend σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩

/-- Prepending is monotone in its set argument. -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

/-! ### The neighbourhood system `C`. -/

/-- Membership in `C`: a neighbourhood is a cone `σΣ*` or a singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})

theorem memC_cone (σ : Str) : memC (cone σ) := Or.inl ⟨σ, rfl⟩

theorem memC_singleton (σ : Str) : memC ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

/-- `{τ} ⊆ σΣ*` iff `σ` is an initial segment of `τ`. -/
theorem singleton_subset_cone {σ τ : Str} : ({τ} : Set Str) ⊆ cone σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_cone]

/-- A singleton and a cone are nested-or-disjoint. -/
theorem singleton_cone_nd (σ τ : Str) :
    ({τ} : Set Str) ⊆ cone σ ∨ cone σ ⊆ {τ} ∨ ({τ} : Set Str) ∩ cone σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_cone.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ

/-- Any two neighbourhoods of `C` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone_trichotomy σ τ
  · rcases singleton_cone_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_cone_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2

/-- **Example 4.4 (Scott 1981, PRG-19).** The neighbourhood system `C` of finite or infinite binary
sequences on `Δ = Σ*`. -/
abbrev C : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memC Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

@[simp] theorem C_master : C.master = (Set.univ : Set Str) := rfl

/-! ### Elements of `C`: `σ` (total) and `σ⊥` (partial). -/

/-- Scott's partial element `σ⊥ = ↑σΣ*` ("the sequence starts with `σ`"). -/
def strBot (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_cone σ))

/-- Scott's total element `σ = ↑{σ}` (the finite sequence `σ`, completed). -/
def strElem (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_singleton σ))

/-! ### The successor maps `x ↦ bx`. -/

/-- Prepending the bit `b` (or, generally, a prefix `σ`) to a neighbourhood of `C` lands back in
`C`: `σ(τΣ*) = (στ)Σ*` and `σ{τ} = {στ}`. -/
theorem memC_prepend (σ : Str) {X : Set Str} (hX : memC X) : memC (prepend σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prepend_cone σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prepend_singleton σ ρ⟩

/-- `σX ⊆ X` along the prefix order: a prepended neighbourhood is contained in any neighbourhood it
refines. (Used only via `prepend_mono`; kept implicit.) -/
theorem prepend_subset_self : True := trivial

/-- **Example 4.4 — the successors `x ↦ bx`.** The approximable map prepending the bit `b`:
`X (bx) Y ↔ bX ⊆ Y`. Approximable because `bX` is again a neighbourhood (`memC_prepend`) and
prepending is monotone. -/
def consMap (b : Bool) : ApproximableMap C C where
  rel X Y := memC X ∧ memC Y ∧ prepend [b] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨Or.inl ⟨[], cone_nil.symm⟩, Or.inl ⟨[], cone_nil.symm⟩, ?_⟩
    exact Set.subset_univ _
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : prepend [b] X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    have hZ : memC (prepend [b] X) := memC_prepend [b] hX
    exact ⟨hX, C.inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prepend_mono [b] hX'X).trans (hsub.trans hYY')⟩

/-- `bx` on a partial element: `b(σ⊥) = (bσ)⊥`. -/
theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub

/-- `bx` on a total element: `b(σ) = (bσ)` (prepend the bit to a finite sequence). -/
theorem consMap_strElem (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strElem σ) = strElem (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] {σ} ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, memC_singleton σ, hY, ?_⟩
    rw [prepend_singleton]; exact hsub

/-! ### A fixed-point element: the alternating sequence `a = 01a`. -/

/-- **Example 4.4 — an element defined by a fixed-point equation.** Scott's `a = 01a`, the infinite
sequence that alternates `0`s and `1`s. We take the least fixed point of `x ↦ 0(1x)`
(`= consMap 0 ∘ consMap 1`), which exists by the Fixed-point Theorem 4.1. -/
def altElt : C.Element := ((consMap false).comp (consMap true)).fixElement

/-- `a = 0(1a)`: `altElt` satisfies Scott's defining equation. -/
theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h

end Scott1980.Neighborhood.Example44

/-! ### Inlined from Scott1980/Neighborhood/Example62C.lean -/

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — `C ≅ {{Λ}} + C + C`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture VI.
This module formalizes the second domain equation of Example 6.2, for the system `C` of finite or
infinite binary sequences (Example 4.4):

`C ≅ {{Λ}} + C + C`,

where `{{Λ}} = 𝟙` is the one-point (unit) domain (Exercise 3.15). Presented over `{0,1}*`,

`C = {Σ*} ∪ {{Λ}} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`,

so a neighbourhood of `C` is the master `Σ*` (`= cone []`), the terminator `{Λ} = {[]}`, a `0`-copy
`0X = embBit false X`, or a `1`-copy `1X = embBit true X`. These four shapes are exactly those of a
**three-way separated sum** `𝟙 + C + C`: a fresh basepoint, plus one `𝟙`-copy (the lone `{Λ}`), plus
two `C`-copies.

Crucially this is a genuine *three-way* sum: nesting the binary sum (`𝟙 + (C + C)`) would introduce a
spurious extra bottom element (the inner sum's basepoint) with no counterpart in `C`. So we first build
the three-way separated sum `sum3` (mirroring Exercise 3.18), then exhibit the order-isomorphism
`ccEquiv : |C| ≃o |𝟙 + C + C|`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-! ## The three-way separated sum `D₀ + D₁ + D₂`.

Tokens are `Option (α ⊕ β ⊕ γ)`: a fresh basepoint `Λ = none` below three disjoint tagged copies. -/

/-- Left tag `0a = some (inl a)`. -/
def t0 {α β γ : Type*} (a : α) : Option (α ⊕ β ⊕ γ) := some (Sum.inl a)

/-- Middle tag `1b = some (inr (inl b))`. -/
def t1 {α β γ : Type*} (b : β) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inl b))

/-- Right tag `2c = some (inr (inr c))`. -/
def t2 {α β γ : Type*} (c : γ) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inr c))

/-- The tagged left copy `0X`. -/
def j0 {α β γ : Type*} (X : Set α) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ a, w = t0 a ∧ a ∈ X}

/-- The tagged middle copy `1Y`. -/
def j1 {α β γ : Type*} (Y : Set β) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ b, w = t1 b ∧ b ∈ Y}

/-- The tagged right copy `2Z`. -/
def j2 {α β γ : Type*} (Z : Set γ) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ c, w = t2 c ∧ c ∈ Z}

variable {α β γ : Type*}

@[simp] theorem t0_mem_j0 {X : Set α} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∈ j0 X ↔ a ∈ X := by
  constructor
  · rintro ⟨a', heq, ha'⟩; simp only [t0, Option.some.injEq, Sum.inl.injEq] at heq; exact heq ▸ ha'
  · intro ha; exact ⟨a, rfl, ha⟩

@[simp] theorem t1_mem_j1 {Y : Set β} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∈ j1 Y ↔ b ∈ Y := by
  constructor
  · rintro ⟨b', heq, hb'⟩
    simp only [t1, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at heq; exact heq ▸ hb'
  · intro hb; exact ⟨b, rfl, hb⟩

@[simp] theorem t2_mem_j2 {Z : Set γ} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∈ j2 Z ↔ c ∈ Z := by
  constructor
  · rintro ⟨c', heq, hc'⟩
    simp only [t2, Option.some.injEq, Sum.inr.injEq] at heq; exact heq ▸ hc'
  · intro hc; exact ⟨c, rfl, hc⟩

@[simp] theorem none_not_mem_j0 {X : Set α} : (none : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0])

@[simp] theorem none_not_mem_j1 {Y : Set β} : (none : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1])

@[simp] theorem none_not_mem_j2 {Z : Set γ} : (none : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t2])

@[simp] theorem t1_not_mem_j0 {X : Set α} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j0 {X : Set α} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t0_not_mem_j1 {Y : Set β} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j1 {Y : Set β} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1, t2])

@[simp] theorem t0_not_mem_j2 {Z : Set γ} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t1_not_mem_j2 {Z : Set γ} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t1, t2])

theorem j0_inter_j0 (X X' : Set α) :
    (j0 X ∩ j0 X' : Set (Option (α ⊕ β ⊕ γ))) = j0 (X ∩ X') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, t0, Set.mem_inter_iff]

theorem j1_inter_j1 (Y Y' : Set β) :
    (j1 Y ∩ j1 Y' : Set (Option (α ⊕ β ⊕ γ))) = j1 (Y ∩ Y') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, t1, Set.mem_inter_iff]

theorem j2_inter_j2 (Z Z' : Set γ) :
    (j2 Z ∩ j2 Z' : Set (Option (α ⊕ β ⊕ γ))) = j2 (Z ∩ Z') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j2, t2, Set.mem_inter_iff]

theorem j0_inter_j1 (X : Set α) (Y : Set β) :
    (j0 X ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j1, t0, t1, Set.mem_inter_iff]

theorem j0_inter_j2 (X : Set α) (Z : Set γ) :
    (j0 X ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j2, t0, t2, Set.mem_inter_iff]

theorem j1_inter_j2 (Y : Set β) (Z : Set γ) :
    (j1 Y ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, j2, t1, t2, Set.mem_inter_iff]

theorem j0_nonempty {X : Set α} (hX : X.Nonempty) : (j0 X : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨t0 a, a, rfl, ha⟩

theorem j1_nonempty {Y : Set β} (hY : Y.Nonempty) : (j1 Y : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨b, hb⟩ := hY; exact ⟨t1 b, b, rfl, hb⟩

theorem j2_nonempty {Z : Set γ} (hZ : Z.Nonempty) : (j2 Z : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨c, hc⟩ := hZ; exact ⟨t2 c, c, rfl, hc⟩

theorem j0_subset_j0 {X X' : Set α} :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ j0 X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact t0_mem_j0.mp (h (t0_mem_j0.mpr ha))
  · rintro h w ⟨a, rfl, ha⟩; exact t0_mem_j0.mpr (h ha)

theorem j1_subset_j1 {Y Y' : Set β} :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ j1 Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact t1_mem_j1.mp (h (t1_mem_j1.mpr hb))
  · rintro h w ⟨b, rfl, hb⟩; exact t1_mem_j1.mpr (h hb)

theorem j2_subset_j2 {Z Z' : Set γ} :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ j2 Z' ↔ Z ⊆ Z' := by
  constructor
  · intro h c hc; exact t2_mem_j2.mp (h (t2_mem_j2.mpr hc))
  · rintro h w ⟨c, rfl, hc⟩; exact t2_mem_j2.mpr (h hc)

theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)

theorem j1_injective {Y Y' : Set β}
    (h : (j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y') : Y = Y' :=
  Set.Subset.antisymm (j1_subset_j1.mp h.subset) (j1_subset_j1.mp h.symm.subset)

theorem j2_injective {Z Z' : Set γ}
    (h : (j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z') : Z = Z' :=
  Set.Subset.antisymm (j2_subset_j2.mp h.subset) (j2_subset_j2.mp h.symm.subset)

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

/-- The master neighbourhood of the three-way sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`. -/
def master3 : Set (Option (α ⊕ β ⊕ γ)) :=
  insert none (j0 V₀.master ∪ j1 V₁.master ∪ j2 V₂.master)

variable {V₀ V₁ V₂}

@[simp] theorem none_mem_master3 : (none : Option (α ⊕ β ⊕ γ)) ∈ master3 V₀ V₁ V₂ :=
  Set.mem_insert _ _

theorem j0_subset_master3 {X : Set α} (hX : V₀.mem X) :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨a, rfl, ha⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_left _ (t0_mem_j0.mpr (V₀.sub_master hX ha)))))

theorem j1_subset_master3 {Y : Set β} (hY : V₁.mem Y) :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨b, rfl, hb⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_right _ (t1_mem_j1.mpr (V₁.sub_master hY hb)))))

theorem j2_subset_master3 {Z : Set γ} (hZ : V₂.mem Z) :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨c, rfl, hc⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_right _ (t2_mem_j2.mpr (V₂.sub_master hZ hc))))

theorem master3_inter_j0 {X : Set α} (hX : V₀.mem X) :
    (master3 V₀ V₁ V₂ ∩ j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X :=
  Set.inter_eq_right.mpr (j0_subset_master3 hX)

theorem master3_inter_j1 {Y : Set β} (hY : V₁.mem Y) :
    (master3 V₀ V₁ V₂ ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y :=
  Set.inter_eq_right.mpr (j1_subset_master3 hY)

theorem master3_inter_j2 {Z : Set γ} (hZ : V₂.mem Z) :
    (master3 V₀ V₁ V₂ ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z :=
  Set.inter_eq_right.mpr (j2_subset_master3 hZ)

theorem eq_master3_of_subset {W : Set (Option (α ⊕ β ⊕ γ))}
    (hsub : master3 V₀ V₁ V₂ ⊆ W) (hsub' : W ⊆ master3 V₀ V₁ V₂) : W = master3 V₀ V₁ V₂ :=
  Set.Subset.antisymm hsub' hsub

/-- **Example 6.2 — the three-way separated sum `D₀ + D₁ + D₂`** over `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`,
under the standing assumption that no neighbourhood of any factor is empty. -/
def sum3 (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (h₂ : ∀ Z, V₂.mem Z → Z.Nonempty) : NeighborhoodSystem (Option (α ⊕ β ⊕ γ)) where
  mem W := W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
    ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)
  master := master3 V₀ V₁ V₂
  master_nonempty := ⟨none, none_mem_master3⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
    · exact subset_rfl
    · exact j0_subset_master3 hX
    · exact j1_subset_master3 hY
    · exact j2_subset_master3 hZ
  inter_mem := by
    have hne : ∀ W, (W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
        ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)) →
        (W : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
      · exact ⟨none, none_mem_master3⟩
      · exact j0_nonempty (h₀ X hX)
      · exact j1_nonempty (h₁ Y hY)
      · exact j2_nonempty (h₂ Z hZ)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Zc, hZc, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [master3_inter_j0 hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [master3_inter_j1 hY']; exact Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl⟩))
      · rw [master3_inter_j2 hZ']; exact Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl⟩))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j0 hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [j0_inter_j0] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ0 (j0_subset_j0.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j1 hY]; exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j1_inter_j1] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · exact Or.inr (Or.inr (Or.inl ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ1 (j1_subset_j1.mp hZsub), rfl⟩))
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j2 hZc]; exact Or.inr (Or.inr (Or.inr ⟨Zc, hZc, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [Set.inter_comm, j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j2_inter_j2] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · exact Or.inr (Or.inr (Or.inr ⟨Zc ∩ Z', V₂.inter_mem hZc hZ' hZ2 (j2_subset_j2.mp hZsub), rfl⟩))

/-! ## The domain equation `C ≅ 𝟙 + C + C`. -/

namespace Example62C

/-- `𝟙` is positive: its single neighbourhood `univ` (over the inhabited `Unit`) is nonempty. -/
theorem unitSys_nonempty : ∀ X, unitSys.mem X → X.Nonempty := by
  rintro X rfl; exact Set.univ_nonempty

/-- Scott's standing assumption `∅ ∉ C`: every neighbourhood of `C` is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- `b{σ} = {bσ}`: prepending a bit to a singleton. -/
theorem embBit_singleton (b : Bool) (σ : Str) : embBit b ({σ} : Set Str) = {(b :: σ : Str)} := by
  rw [embBit_eq_prepend, Example44.prepend_singleton]; rfl

/-- Prepending a bit lands back in `C`. -/
theorem memC_embBit (b : Bool) {X : Set Str} (hX : C.mem X) : C.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact Example44.memC_prepend [b] hX

/-- **Example 6.2 — the shape of a `C`-neighbourhood.** Every neighbourhood of `C` is the master
`Σ* = cone []`, the terminator `{Λ} = {[]}`, a `0`-copy `0X` with `X ∈ C`, or a `1`-copy `1X`. -/
theorem memC_cases {W : Set Str} (hW : C.mem W) :
    W = Set.univ ∨ W = ({[]} : Set Str)
      ∨ (∃ X, C.mem X ∧ W = embBit false X) ∨ (∃ Y, C.mem Y ∧ W = embBit true Y) := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl cone_nil
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨cone σ', memC_cone σ', (embBit_cone false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨cone σ', memC_cone σ', (embBit_cone true σ').symm⟩))
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨{σ'}, memC_singleton σ', (embBit_singleton false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨{σ'}, memC_singleton σ', (embBit_singleton true σ').symm⟩))

/-- If `bW ∈ C` then `W ∈ C`. -/
theorem memC_embBit_inv {b : Bool} {W : Set Str} (h : C.mem (embBit b W)) : C.mem W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_cone] at hσ; rw [embBit_injective hσ]; exact memC_cone w'
  · have hmem : σ ∈ embBit b W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set Str))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_singleton] at hσ; rw [embBit_injective hσ]; exact memC_singleton w'

theorem singleton_nil_inter_embBit (b : Bool) (X : Set Str) :
    (({[]} : Set Str) ∩ embBit b X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embBit, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩
  exact absurd heq (by simp)

theorem singleton_nil_ne_univ : ({[]} : Set Str) ≠ Set.univ := by
  intro h
  have hmem : ([true] : Str) ∈ ({[]} : Set Str) := h ▸ Set.mem_univ _
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

theorem singleton_nil_ne_embBit (b : Bool) (X : Set Str) : ({[]} : Set Str) ≠ embBit b X := by
  intro h
  exact nil_not_mem_embBit (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Str) ∈ ({[]} : Set Str)))

/-- The right-hand side of the domain equation: the three-way sum `𝟙 + C + C`. -/
abbrev CC : NeighborhoodSystem (Option (Unit ⊕ Str ⊕ Str)) :=
  sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty

theorem sum3_mem_j1_inv {X : Set Str} (h : CC.mem (j1 X)) : C.mem X := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Y, hY, heq⟩ | ⟨Z, hZ, heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · rw [j1_injective heq]; exact hY
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1

theorem sum3_mem_j2_inv {Y : Set Str} (h : CC.mem (j2 Y)) : C.mem Y := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Z, hZ, heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t1_mem_j1.mpr hc)) t1_not_mem_j2
  · rw [j2_injective heq]; exact hY'

theorem sum3_mem_nonempty {W : Set (Option (Unit ⊕ Str ⊕ Str))} (h : CC.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨U, hU, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (unitSys_nonempty U hU)
  · exact j1_nonempty (C_nonempty Y hY)
  · exact j2_nonempty (C_nonempty Z hZ)

/-! ### The forward half `toCC : |C| → |𝟙 + C + C|`. -/

/-- **Example 6.2 — forward half of `C ≅ 𝟙 + C + C`.** -/
def toCC (x : C.Element) : CC.Element where
  mem W := W = master3 unitSys C C
    ∨ (W = j0 (Set.univ : Set Unit) ∧ x.mem ({[]} : Set Str))
    ∨ (∃ X, C.mem X ∧ W = j1 X ∧ x.mem (embBit false X))
    ∨ (∃ Y, C.mem Y ∧ W = j2 Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Set.univ, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨X', hX', rfl, hzF'⟩ | ⟨Y', hY', rfl, hzT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨master3_inter_j0 rfl, hzU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', master3_inter_j1 hX', hzF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', master3_inter_j2 hY', hzT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, master3_inter_j0 rfl], hzU⟩)
    · refine Or.inr (Or.inl ⟨?_, hzU⟩)
      rw [j0_inter_j0, Set.inter_self]
    · exfalso
      have hx := x.inter_mem hzU hzF'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzU hzT'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, master3_inter_j1 hX], hzF⟩))
    · exfalso
      have hx := x.inter_mem hzF hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, j1_inter_j1 X X', ?_⟩))
      · have hx := x.inter_mem hzF hzF'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzF hzF'; rwa [embBit_inter] at hx
    · exfalso
      have hx := x.inter_mem hzF hzT'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j2 hY], hzT⟩))
    · exfalso
      have hx := x.inter_mem hzT hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzT hzF'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, j2_inter_j2 Y Y', ?_⟩))
      · have hx := x.inter_mem hzT hzT'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzT hzT'; rwa [embBit_inter] at hx
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub (CC.sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain rfl := hX'; exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · refine Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl, ?_⟩))
        exact x.up_mem hzF (memC_embBit false hY') (embBit_subset.mpr (j1_subset_j1.mp hsub))
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · refine Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl, ?_⟩))
        exact x.up_mem hzT (memC_embBit true hZ') (embBit_subset.mpr (j2_subset_j2.mp hsub))

@[simp] theorem toCC_mem_j0 {x : C.Element} :
    (toCC x).mem (j0 (Set.univ : Set Unit)) ↔ x.mem ({[]} : Set Str) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · exact hz
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

@[simp] theorem toCC_mem_j1 {x : C.Element} {X : Set Str} (hX : C.mem X) :
    (toCC x).mem (j1 X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heq ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j0
    · rw [j1_injective heqj]; exact hz
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heqj ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · intro hz; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hz⟩))

@[simp] theorem toCC_mem_j2 {x : C.Element} {Y : Set Str} (hY : C.mem Y) :
    (toCC x).mem (j2 Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j0
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heqj ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1
    · rw [j2_injective heqj]; exact hz
  · intro hz; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩))

/-! ### The inverse half `fromCC : |𝟙 + C + C| → |C|`. -/

/-- **Example 6.2 — inverse half of `C ≅ 𝟙 + C + C`.** -/
def fromCC (s : CC.Element) : C.Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set Str) ∧ s.mem (j0 (Set.univ : Set Unit)))
    ∨ (∃ X, C.mem X ∧ W = embBit false X ∧ s.mem (j1 X))
    ∨ (∃ Y, C.mem Y ∧ W = embBit true Y ∧ s.mem (j2 Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl ⟨[], cone_nil.symm⟩
    · exact memC_singleton []
    · exact memC_embBit false hX
    · exact memC_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨X', hX', rfl, hsF'⟩ | ⟨Y', hY', rfl, hsT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsU hsT'; rw [j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsF⟩))
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, embBit_inter false X X', ?_⟩))
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs
        exact sum3_mem_j1_inv (s.sub hs)
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs; exact hs
    · exfalso
      have hs := s.inter_mem hsF hsT'; rw [j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsT⟩))
    · exfalso
      have hs := s.inter_mem hsT hsU'; rw [Set.inter_comm, j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsT hsF'; rw [Set.inter_comm, j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, embBit_inter true Y Y', ?_⟩))
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs
        exact sum3_mem_j2_inv (s.sub hs)
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        have hm := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · refine Or.inr (Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩))
        exact s.up_mem hsF (Or.inr (Or.inr (Or.inl ⟨X', hX', rfl⟩)))
          (j1_subset_j1.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        have hm := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩))
        exact s.up_mem hsT (Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl⟩)))
          (j2_subset_j2.mpr (embBit_subset.mp hsub))

@[simp] theorem fromCC_mem_nil {s : CC.Element} :
    (fromCC s).mem ({[]} : Set Str) ↔ s.mem (j0 (Set.univ : Set Unit)) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embBit false X')
    · exact absurd heq (singleton_nil_ne_embBit true Y')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

@[simp] theorem fromCC_mem_embF {s : CC.Element} {X : Set Str} (hX : C.mem X) :
    (fromCC s).mem (embBit false X) ↔ s.mem (j1 X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · exact absurd heq.symm (singleton_nil_ne_embBit false X)
    · rw [embBit_injective heqj]; exact hs
    · exact absurd heqj (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X hX))
  · intro hs; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hs⟩))

@[simp] theorem fromCC_mem_embT {s : CC.Element} {Y : Set Str} (hY : C.mem Y) :
    (fromCC s).mem (embBit true Y) ↔ s.mem (j2 Y) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (singleton_nil_ne_embBit true Y)
    · exact absurd heqj.symm (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X' hX'))
    · rw [embBit_injective heqj]; exact hs
  · intro hs; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩))

/-! ### The two halves are mutually inverse. -/

theorem fromCC_toCC (x : C.Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_j0.mp hs
    · exact (toCC_mem_j1 hX).mp hs
    · exact (toCC_mem_j2 hY).mp hs
  · intro hW
    rcases memC_cases (x.sub hW) with rfl | rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_j0.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (toCC_mem_j1 hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (toCC_mem_j2 hY).mpr hW⟩))

theorem toCC_fromCC (s : CC.Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embF hX).mp hs
    · exact (fromCC_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨U, hU, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · obtain rfl := hU
      exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (fromCC_mem_embF hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (fromCC_mem_embT hY).mpr hW⟩))

/-! ### The domain equation `C ≅ 𝟙 + C + C`. -/

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|C| ≃o |𝟙 + C + C|`.** -/
def ccEquiv : C.Element ≃o CC.Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hW
      rcases memC_cases (x.sub hW) with rfl | rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_j0.mp (h _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_j1 hA).mp (h _ (Or.inr (Or.inr (Or.inl ⟨A, hA, rfl, hW⟩))))
      · exact (toCC_mem_j2 hA).mp (h _ (Or.inr (Or.inr (Or.inr ⟨A, hA, rfl, hW⟩))))
    · intro h W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h _ hz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, h _ hz⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, h _ hz⟩))

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `C ≅ {{Λ}} + C + C`.** Scott's domain
`C` of finite-or-infinite binary sequences is, as a domain, isomorphic to the three-way separated sum
`𝟙 + C + C`: a sequence is bottom, the finished empty sequence `Λ` (the `𝟙` summand), or begins with
`0` or `1` (the two `C` summands). -/
theorem C_domain_equation :
    C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty :=
  ⟨ccEquiv⟩

end Example62C

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise408.lean -/

/-!
# Exercise 4.8 (Scott 1981, PRG-19, Lecture IV) — the principle of fixed-point induction

Suppose `f : 𝒟 → 𝒟` and a predicate `S ⊆ |𝒟|` satisfy

  (i)   `⊥ ∈ S`;
  (ii)  `x ∈ S ⟹ f(x) ∈ S`;
  (iii) `S` is closed under sups of increasing sequences.

Then `fix(f) ∈ S`. Since `fix(f) = ⊔ₙ fⁿ(⊥)` (Theorem 4.2(iii)), and `f⁰(⊥) = ⊥ ∈ S` with the
inductive step `fⁿ(⊥) ∈ S ⟹ fⁿ⁺¹(⊥) ∈ S` from (i)/(ii), every approximant lies in `S`; the
directed union then lies in `S` by (iii). This is **fixed-point induction** (`fix_induction`).

As Scott suggests, we apply it to `S = {x ∣ a(x) = b(x)}` (`fix_induction_eq`): if `a, b : 𝒟 → 𝒟`
are approximable with `a(⊥) = b(⊥)`, `f ∘ a = a ∘ f` and `f ∘ b = b ∘ f`, then
`a(fix f) = b(fix f)`. (i) is `a(⊥) = b(⊥)`; (ii) uses the commutation `a(f x) = f(a x)`,
`b(f x) = f(b x)`; (iii) is continuity (`a`, `b` preserve directed unions, `toElementMap_iSupDirected`).

The induction principle is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the equality
corollary inherits `Classical.choice` only through the `Element` extensionality used to compare the
two directed unions.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The sup of a monotone `ω`-chain, realized as a directed union (`max`-directedness). -/
def supChain (s : ℕ → V.Element) (hmono : Monotone s) : V.Element :=
  NeighborhoodSystem.iSupDirected s
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)

theorem mem_supChain (s : ℕ → V.Element) (hmono : Monotone s) {Z : Set α} :
    (supChain s hmono).mem Z ↔ ∃ n, (s n).mem Z :=
  NeighborhoodSystem.mem_iSupDirected s _

/-- `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  show (f.comp (f.iterMap n)).toElementMap V.bot
      = f.toElementMap ((f.iterMap n).toElementMap V.bot)
  rw [toElementMap_comp]

theorem iterElem_zero (f : ApproximableMap V V) : f.iterElem 0 = V.bot :=
  toElementMap_idMap V.bot

/-- The approximants form a monotone `ω`-chain (the `Monotone` packaging of `iterElem_mono`). -/
theorem iterElem_monotone (f : ApproximableMap V V) : Monotone f.iterElem :=
  fun _ _ hab => iterElem_mono f hab

/-- The approximants `fⁿ(⊥)` form a monotone chain whose sup is `fix(f)`. -/
theorem fixElement_eq_supChain (f : ApproximableMap V V) :
    f.fixElement = supChain f.iterElem (iterElem_monotone f) := by
  apply Element.ext
  intro X
  rw [mem_supChain, mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

/-- **Exercise 4.8 (Scott 1981, PRG-19) — fixed-point induction.** If a predicate `P` holds at `⊥`,
is preserved by `f`, and is closed under sups of monotone chains, then it holds at `fix(f)`. -/
theorem fix_induction (f : ApproximableMap V V) (P : V.Element → Prop)
    (hbot : P V.bot)
    (hstep : ∀ x, P x → P (f.toElementMap x))
    (hsup : ∀ (s : ℕ → V.Element) (hmono : Monotone s), (∀ n, P (s n)) → P (supChain s hmono)) :
    P f.fixElement := by
  have hmono : Monotone f.iterElem := iterElem_monotone f
  have hP : ∀ n, P (f.iterElem n) := by
    intro n
    induction n with
    | zero => rw [iterElem_zero]; exact hbot
    | succ k ih => rw [iterElem_succ]; exact hstep _ ih
  rw [fixElement_eq_supChain f]
  exact hsup f.iterElem hmono hP

/-- **Exercise 4.8 (Scott 1981, PRG-19) — application to `S = {x ∣ a(x) = b(x)}`.** If `a(⊥) = b(⊥)`
and `f` commutes with both `a` and `b` (`f ∘ a = a ∘ f`, `f ∘ b = b ∘ f`), then `a` and `b` agree at
the least fixed point: `a(fix f) = b(fix f)`. -/
theorem fix_induction_eq (f a b : ApproximableMap V V)
    (hbot : a.toElementMap V.bot = b.toElementMap V.bot)
    (hfa : f.comp a = a.comp f) (hfb : f.comp b = b.comp f) :
    a.toElementMap f.fixElement = b.toElementMap f.fixElement := by
  -- commutation, elementwise: `a(f x) = f(a x)` and `b(f x) = f(b x)`.
  have hca : ∀ x, a.toElementMap (f.toElementMap x) = f.toElementMap (a.toElementMap x) := by
    intro x
    have h1 : (a.comp f).toElementMap x = (f.comp a).toElementMap x := by rw [hfa]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  have hcb : ∀ x, b.toElementMap (f.toElementMap x) = f.toElementMap (b.toElementMap x) := by
    intro x
    have h1 : (b.comp f).toElementMap x = (f.comp b).toElementMap x := by rw [hfb]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  refine fix_induction f (fun x => a.toElementMap x = b.toElementMap x) hbot ?_ ?_
  · intro x hx
    rw [hca, hcb, hx]
  · intro s hmono hs
    -- both sides are directed unions of equal families.
    show a.toElementMap (supChain s hmono) = b.toElementMap (supChain s hmono)
    rw [supChain, toElementMap_iSupDirected, toElementMap_iSupDirected]
    apply Element.ext
    intro Z
    rw [NeighborhoodSystem.mem_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [← hs n]; exact hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hs n]; exact hn⟩

end ApproximableMap

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise419.lean -/

/-!
# Exercise 4.19 (Scott 1981, PRG-19, Lecture IV) — verifying Example 4.4

Example 4.4 leaves many assertions to the reader. This module discharges the two explicitly
requested ones:

* **"Peano's Axioms" for `{0,1}*`.** The structured set `⟨Σ*, Λ, 0·, 1·⟩` (here `Σ* = List Bool`,
  `Λ = []`, and the two successors `b ↦ b :: ·`) satisfies the natural two-successor analogue of
  Definition 4.5: `Λ` is not a successor (`peano_nil_ne_cons`), each successor is injective
  (`peano_cons_injective`), the two successor ranges are disjoint (`peano_cons_disjoint`), and the
  *induction* principle holds (`peano_induction`). So `Σ*` is the free monoid on two generators —
  the binary-tree analogue of `⟨ℕ, 0, ⁺⟩`.

* **`one : C → T` is definable from the rest of the structure by a fixed-point equation.** We first
  build the three tests `empty, zero, one : C → T` as honest approximable maps (Scott: "it is an
  exercise to show these are approximable"), via a uniform *head-test* combinator `liftC`. We then
  show

  `one(x) = cond(empty(x), false, cond(zero(x), false, true))`

  on every generator of `|C|` (`one_def_strElem`, `one_def_strBot`), exhibiting `one` as the
  solution of a fixed-point/recursion equation in the remaining structure `⟨C, Λ, 0, 1, empty,
  zero, cond⟩` (the right-hand side does not mention `one`, so this is the trivial fixed point —
  Scott's point that the tests are not independent).

The `liftC` combinator (a map `C → V` determined by its values on the partial elements `σ⊥` and the
total elements `σ`, subject to two monotonicity conditions) is reusable; with it one likewise gets
Scott's `tail : C → C` (`tail(bx) = x`, `tail(Λ) = ⊥`), here noted but not needed for `one`.

The `liftC` *data* is **choice-free**; the truth-domain tests inherit `Classical.choice`
structurally from `T` (Example 1.2), exactly as `Example23.parityMap` and `Example43.zeroMap` do.
-/

namespace Scott1980.Neighborhood.Exercise419

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44

/-! ### "Peano's Axioms" for `{0,1}* = List Bool`. -/

/-- **Exercise 4.19 — Peano (i) for `{0,1}*`.** `Λ` is not a successor: `[] ≠ b :: σ`. -/
theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp

/-- **Exercise 4.19 — Peano (ii) for `{0,1}*`.** Each successor `b ::·` is injective. -/
theorem peano_cons_injective {b : Bool} {σ τ : Str} (h : b :: σ = b :: τ) : σ = τ :=
  (List.cons.injEq b σ b τ).mp h |>.2

/-- **Exercise 4.19 — Peano (ii′) for `{0,1}*`.** The two successor ranges are disjoint:
`0σ ≠ 1τ`. -/
theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp

/-- **Exercise 4.19 — Peano (iii) for `{0,1}*`.** Induction: a predicate holding at `Λ` and closed
under both successors holds everywhere. (This is `List.rec`; it is the two-successor analogue of
Definition 4.5(iii) and the recursion engine behind `tail`/`empty`/`zero`/`one`.) -/
theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih

/-! ### Disjointness facts for `C`'s neighbourhoods (cones vs singletons). -/

/-- A cone is never contained in a singleton (it has at least two elements). -/
theorem not_cone_subset_singleton (τ σ : Str) : ¬ cone τ ⊆ ({σ} : Set Str) := by
  intro h
  have h1 : τ ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  have h2 : (τ ++ [true]) ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [true] := h1.trans h2.symm
  simp at this

/-- A cone is never equal to a singleton. -/
theorem cone_ne_singleton (τ σ : Str) : cone τ ≠ ({σ} : Set Str) := by
  intro h
  exact not_cone_subset_singleton τ σ (h ▸ subset_rfl)

/-! ### The head-test value functions. -/

variable {β : Type*}

/-- The codomain value chosen by inspecting the head of a sequence: `[] ↦ z`, `0σ ↦ a₀`, `1σ ↦ a₁`.
With `z = ⊥` this is the value at the *partial* element `σ⊥`; with `z = vΛ` the value at the
*total* element `σ`. -/
def headValC (V : NeighborhoodSystem β) (z a0 a1 : V.Element) : Str → V.Element
  | [] => z
  | false :: _ => a0
  | true :: _ => a1

@[simp] theorem headValC_nil (V : NeighborhoodSystem β) (z a0 a1 : V.Element) :
    headValC V z a0 a1 [] = z := rfl
@[simp] theorem headValC_false (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (false :: σ) = a0 := rfl
@[simp] theorem headValC_true (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (true :: σ) = a1 := rfl

/-- Monotonicity of the head value: along a prefix `σ <+: τ`, the *partial* value (`z = ⊥`) at `σ`
is below *any* head value at `τ` with the same head constants. Covers both required conditions
(cone→cone with `z' = ⊥`, cone→singleton with `z' = vΛ`). -/
theorem headValC_bot_le (V : NeighborhoodSystem β) (z' a0 a1 : V.Element) {σ τ : Str}
    (h : σ <+: τ) : headValC V V.bot a0 a1 σ ≤ headValC V z' a0 a1 τ := by
  cases σ with
  | nil => exact bot_le
  | cons b σ0 =>
    obtain ⟨s, rfl⟩ := h
    cases b
    · rw [List.cons_append]; exact le_of_eq rfl
    · rw [List.cons_append]; exact le_of_eq rfl

/-! ### The combinator `liftC`: an approximable map out of `C`. -/

/-- A map `C → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`, provided (a) the partial values are monotone along prefixes and (b) a
partial value sits below the total value of any extending prefix. The relation says: a cone `σΣ*`
relates to the neighbourhoods of `coneVal σ`, and a singleton `{σ}` to those of `singVal σ`. -/
def liftC (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap C V where
  rel X Y := (∃ σ, X = cone σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [C_master]; exact cone_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have : σ = σ' := cone_injective hX'
      subst this
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (cone_ne_singleton σ σ')
    · exact absurd hX'.symm (cone_ne_singleton σ' σ)
    · have : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst this
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · -- input is the cone `σΣ*`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · -- `X' = cone τ ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := cone_subset_cone.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · -- `X' = {τ} ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := singleton_subset_cone.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · -- input is the singleton `{σ}`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_cone_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at this
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

/-- `liftC` on a partial element: `f(σ⊥) = coneVal σ`. -/
theorem liftC_strBot (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strBot σ) = coneVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := cone_subset_cone.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_cone_subset_singleton σ σ')
  · intro hY
    exact ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

/-- `liftC` on a total element: `f(σ) = singVal σ`. -/
theorem liftC_strElem (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strElem σ) = singVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_cone.mp
        rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at this
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

/-! ### The three tests `empty, zero, one : C → T`. -/

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T

local notation "𝕥" => Example23.trueElt
local notation "𝕗" => Example23.falseElt

/-- **Example 4.4 — `empty`.** `empty(Λ) = true`, `empty(0x) = empty(1x) = false`, strict. -/
def emptyMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗)

/-- **Example 4.4 — `zero`.** `zero(Λ) = false`, `zero(0x) = true`, `zero(1x) = false`, strict. -/
def zeroMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗)

/-- **Example 4.4 — `one`.** `one(Λ) = false`, `one(0x) = false`, `one(1x) = true`, strict. -/
def oneMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥)

/-! Value equations on total elements `σ` and partial elements `σ⊥`. -/

@[simp] theorem emptyMap_strElem (σ : Str) :
    emptyMap.toElementMap (strElem σ) = headValC T 𝕥 𝕗 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
@[simp] theorem emptyMap_strBot (σ : Str) :
    emptyMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
@[simp] theorem zeroMap_strElem (σ : Str) :
    zeroMap.toElementMap (strElem σ) = headValC T 𝕗 𝕥 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
@[simp] theorem zeroMap_strBot (σ : Str) :
    zeroMap.toElementMap (strBot σ) = headValC T T.bot 𝕥 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
@[simp] theorem oneMap_strElem (σ : Str) :
    oneMap.toElementMap (strElem σ) = headValC T 𝕗 𝕗 𝕥 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ
@[simp] theorem oneMap_strBot (σ : Str) :
    oneMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕥 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ

/-! ### `one` is defined from `empty`, `zero` and `cond` by a fixed-point equation. -/

/-- `cond(⊥, x, y) = ⊥` in `T`, phrased with `T.bot` (which the head-test `empty(⊥)` produces)
rather than the syntactically distinct `Example23.botElt` of `Exercise326.cond_bot`. -/
theorem condT_bot (x y : T.Element) :
    (Exercise326.cond T).toElementMap (pair T.bot (pair x y)) = T.bot := by
  apply Element.ext
  intro Z
  rw [Exercise326.cond_toElementMap_mem]
  constructor
  · rintro (⟨h0, _⟩ | ⟨h1, _⟩ | rfl)
    · rw [NeighborhoodSystem.mem_bot] at h0; exact absurd h0 Exercise326.zero_ne_master
    · rw [NeighborhoodSystem.mem_bot] at h1; exact absurd h1 Exercise326.one_ne_master
    · exact T.bot.master_mem
  · intro h
    rw [NeighborhoodSystem.mem_bot] at h
    exact Or.inr (Or.inr h)

/-- The defining right-hand side: `cond(empty(x), false, cond(zero(x), false, true))`. It uses only
`empty`, `zero` and the conditional `cond` (Exercise 3.26) — not `one`. -/
def oneDef (x : C.Element) : T.Element :=
  (Exercise326.cond T).toElementMap
    (pair (emptyMap.toElementMap x)
      (pair 𝕗
        ((Exercise326.cond T).toElementMap (pair (zeroMap.toElementMap x) (pair 𝕗 𝕥)))))

/-- **Exercise 4.19 (Scott 1981, PRG-19).** `one` is definable from `empty`, `zero`, `cond`: the
equation `one(x) = cond(empty(x), false, cond(zero(x), false, true))` holds on every total element
`σ`. -/
theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>
    -- empty(Λ)=true ⟹ cond picks `false`
    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      -- empty=false ⟹ inner cond; zero(0σ)=true ⟹ inner cond picks `false`
      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]

/-- **Exercise 4.19 (Scott 1981, PRG-19).** The same defining equation holds on every partial
element `σ⊥` — including `⊥ = []⊥` where `empty(⊥) = ⊥` forces `cond(⊥, …) = ⊥`. -/
theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]

end Scott1980.Neighborhood.Exercise419

/-! ### Inlined from Scott1980/Neighborhood/Exercise516.lean -/

/-!
# Exercise 5.16 (Scott 1981, PRG-19, Lecture V) — `neg`, `merge` and `d` on `C`

Returning to Example 4.4 (the domain `C` of finite or infinite binary sequences), this module gives
fixed-point/recursive definitions of three maps and verifies their characterizing equations:

* **`tail : C → C`** (`tail(bx) = x`, `tail(Λ) = ⊥`) — Scott's predecessor analogue, the item left to
  the reader in Example 4.4, built here with the head-test combinator `Exercise419.liftC`.
* **`neg : C → C`** with `neg(0x) = 1·neg(x)`, `neg(1x) = 0·neg(x)` — bit-complement. We solve the
  recursion in closed form via `liftC` (`neg(σ) = (flip σ)`, `flip = List.map not`), prove the
  recursion equations `neg_cons_false`/`neg_cons_true` (so it is *the* solution), and prove Scott's
  involution law **`neg(neg x) = x` for all `x ∈ |C|`** (`negMap_negMap`) — using that an approximable
  map is determined by its values on the finite elements `σ⊥`, `σ` (Exercise 2.8,
  `eq_of_toElementMap_principal`), so it suffices to check the two-fold complement on those, where it
  is `flip ∘ flip = id`.
* **`d : C → C`** (`d(Λ) = Λ`, `d(0x) = 00·d(x)`, `d(1x) = 11·d(x)`) — the bit-doubling map of
  Example 4.4, again via `liftC` (`d(σ) = double σ`).
* **`merge : C × C → C`** with `merge(εx, δy) = ε·δ·merge(x, y)` — bit-interleaving. Built directly as
  an approximable map out of `prod C C` from an explicit interleave value function `mergeVal`. The
  boundary that Scott flags (`merge(Λ, y)` etc.) is resolved by the unique *monotone* convention
  (`merge(Λ, y) = Λ`, `merge(εx, y) = ε⊥` once `y` runs out), the only choice compatible with
  approximability. We prove the recursion equation and **`merge(x, x) = d(x)`** (`mergeMap_diag`).

All *data* (`tail`, `negMap`, `dMap`, `mergeMap`) is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`); equalities of maps go through `eq_of_toElementMap_principal` (classical, exactly like
the project's `ext_of_toElementMap`).

The Thue–Morse properties of `t = 0·merge(neg t, tail t)` (its digit-sum-mod-2 description and
overlap-freeness) are real combinatorics-on-words and are left as a separate follow-up.
-/

namespace Scott1980.Neighborhood.Exercise516

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-! ### List helpers: bit-complement `flip` and bit-doubling `double`. -/

/-- Complement every bit of a finite string. -/
abbrev flip (σ : Str) : Str := σ.map not

@[simp] theorem flip_nil : flip [] = [] := rfl
@[simp] theorem flip_cons (b : Bool) (σ : Str) : flip (b :: σ) = (!b) :: flip σ := rfl

/-- `flip` is an involution. -/
@[simp] theorem flip_flip (σ : Str) : flip (flip σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

/-- `flip` preserves the prefix order. -/
theorem flip_prefix {σ τ : Str} (h : σ <+: τ) : flip σ <+: flip τ := h.map _

/-- Double every bit of a finite string: `double (b :: σ) = b :: b :: double σ`. -/
def double : Str → Str
  | [] => []
  | b :: σ => b :: b :: double σ

@[simp] theorem double_nil : double [] = [] := rfl
@[simp] theorem double_cons (b : Bool) (σ : Str) : double (b :: σ) = b :: b :: double σ := rfl

/-- `double` distributes over append. -/
theorem double_append (σ τ : Str) : double (σ ++ τ) = double σ ++ double τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [double, ih]

/-- `double` preserves the prefix order. -/
theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩

/-! ### The approximation order on the finite elements `σ⊥` and `σ`. -/

theorem strBot_le_strBot_iff {σ τ : Str} : strBot σ ≤ strBot τ ↔ σ <+: τ := by
  rw [strBot, strBot, C.principal_le_iff, cone_subset_cone]

theorem strBot_le_strElem_iff {σ τ : Str} : strBot σ ≤ strElem τ ↔ σ <+: τ := by
  rw [strBot, strElem, C.principal_le_iff]
  exact singleton_subset_cone

theorem strElem_le_strElem_iff {σ τ : Str} : strElem σ ≤ strElem τ ↔ σ = τ := by
  rw [strElem, strElem, C.principal_le_iff, Set.singleton_subset_iff, Set.mem_singleton_iff,
    eq_comm]

theorem not_strElem_le_strBot {σ τ : Str} : ¬ strElem σ ≤ strBot τ := by
  rw [strElem, strBot, C.principal_le_iff]
  exact not_cone_subset_singleton τ σ

/-- A prefix relation descends to tails. -/
theorem tail_prefix {σ τ : Str} (h : σ <+: τ) : σ.tail <+: τ.tail := by
  obtain ⟨ρ, rfl⟩ := h
  cases σ with
  | nil => simp
  | cons a σ' => exact List.prefix_append σ' ρ

/-! ### Determination by finite elements: an equality criterion for maps `C → V`. -/

variable {β : Type*}

/-- Two approximable maps out of `C` agree as soon as they agree on every finite element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below. -/
theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ

/-! ### `tail : C → C` — Scott's predecessor analogue (Example 4.4). -/

/-- The value of `tail` on a total element `σ`: `tail(Λ) = ⊥`, `tail(bσ') = σ'`. -/
def tailSing : Str → C.Element
  | [] => strBot []
  | _ :: σ' => strElem σ'

theorem tail_hcone {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ strBot τ.tail :=
  strBot_le_strBot_iff.mpr (tail_prefix h)

theorem tail_hsing {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ tailSing τ := by
  cases τ with
  | nil => obtain rfl := List.prefix_nil.mp h; exact le_refl _
  | cons a τ' =>
    refine strBot_le_strElem_iff.mpr ?_
    cases σ with
    | nil => exact List.nil_prefix
    | cons b σ' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact h'

/-- **Exercise 5.16 / Example 4.4 — `tail : C → C`.** Built with the head-test combinator `liftC`:
on `σ⊥` it returns `(tail σ)⊥`, on `σ` the total `tail σ` (with `tail Λ = ⊥`). -/
def tailMap : ApproximableMap C C :=
  liftC C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing

@[simp] theorem tailMap_strBot (σ : Str) :
    tailMap.toElementMap (strBot σ) = strBot σ.tail :=
  liftC_strBot C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

@[simp] theorem tailMap_strElem (σ : Str) :
    tailMap.toElementMap (strElem σ) = tailSing σ :=
  liftC_strElem C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

/-- `tail(b(σ⊥)) = σ⊥`. -/
theorem tailMap_consMap_strBot (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strBot σ)) = strBot σ := by
  rw [consMap_strBot, tailMap_strBot]; rfl

/-- `tail(b(σ)) = σ`. -/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

/-! ### `neg : C → C` — bit complement, `neg(0x)=1·neg(x)`, `neg(1x)=0·neg(x)`. -/

theorem neg_hcone {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strBot (flip τ) :=
  strBot_le_strBot_iff.mpr (flip_prefix h)

theorem neg_hsing {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strElem (flip τ) :=
  strBot_le_strElem_iff.mpr (flip_prefix h)

/-- **Exercise 5.16 — `neg : C → C`.** The closed-form solution of Scott's recursion, built with
`liftC`: `neg(σ⊥) = (flip σ)⊥` and `neg(σ) = flip σ`. -/
def negMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing

@[simp] theorem negMap_strBot (σ : Str) :
    negMap.toElementMap (strBot σ) = strBot (flip σ) :=
  liftC_strBot C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

@[simp] theorem negMap_strElem (σ : Str) :
    negMap.toElementMap (strElem σ) = strElem (flip σ) :=
  liftC_strElem C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

/-- **Exercise 5.16 — the recursion for `neg`, case `0`.** `neg(0·x) = 1·neg(x)` as a map identity. -/
theorem neg_cons_false : negMap.comp (consMap false) = (consMap true).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

/-- **Exercise 5.16 — the recursion for `neg`, case `1`.** `neg(1·x) = 0·neg(x)` as a map identity. -/
theorem neg_cons_true : negMap.comp (consMap true) = (consMap false).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg ∘ neg = id` as approximable maps: it suffices to
check on the finite elements `σ⊥`, `σ`, where it is `flip ∘ flip = id`. -/
theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg(neg(x)) = x` for all `x ∈ |C|`. -/
theorem negMap_negMap (x : C.Element) : negMap.toElementMap (negMap.toElementMap x) = x := by
  have h := negMap_comp_negMap
  rw [← toElementMap_comp, h, toElementMap_idMap]

/-! ### `d : C → C` — bit-doubling, `d(Λ)=Λ`, `d(0x)=00·d(x)`, `d(1x)=11·d(x)`. -/

theorem d_hcone {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strBot (double τ) :=
  strBot_le_strBot_iff.mpr (double_prefix h)

theorem d_hsing {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strElem (double τ) :=
  strBot_le_strElem_iff.mpr (double_prefix h)

/-- **Exercise 5.16 / Example 4.4 — `d : C → C`.** The doubling map, closed form via `liftC`:
`d(σ⊥) = (double σ)⊥`, `d(σ) = double σ`. -/
def dMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing

@[simp] theorem dMap_strBot (σ : Str) :
    dMap.toElementMap (strBot σ) = strBot (double σ) :=
  liftC_strBot C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

@[simp] theorem dMap_strElem (σ : Str) :
    dMap.toElementMap (strElem σ) = strElem (double σ) :=
  liftC_strElem C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

/-! ### `merge : C × C → C` — bit interleaving.

The principal elements of `C` are tagged strings `(b, σ)`: `b = true` is the *total* `σ`, `b = false`
the *partial* `σ⊥`. We encode the corresponding neighbourhood (`shape`) and element (`shapeElem`),
the partial order between them (`SLe`), and the interleaving value function `mergeVal`. -/

/-- The neighbourhood of the tagged string `(b, σ)`: `{σ}` if total, `cone σ` if partial. -/
def shape : Bool → Str → Set Str
  | true, σ => {σ}
  | false, σ => cone σ

theorem memC_shape : ∀ (b : Bool) (σ : Str), memC (shape b σ)
  | true, σ => memC_singleton σ
  | false, σ => memC_cone σ

/-- The element of the tagged string `(b, σ)`: total `σ` if `b`, partial `σ⊥` otherwise. -/
def shapeElem (b : Bool) (σ : Str) : C.Element := C.principal (memC_shape b σ)

@[simp] theorem shapeElem_true (σ : Str) : shapeElem true σ = strElem σ := rfl
@[simp] theorem shapeElem_false (σ : Str) : shapeElem false σ = strBot σ := rfl

theorem shape_injective : ∀ {b b' : Bool} {σ σ' : Str}, shape b σ = shape b' σ' → b = b' ∧ σ = σ'
  | true, true, σ, σ', h => ⟨rfl, by rwa [shape, shape, Set.singleton_eq_singleton_iff] at h⟩
  | true, false, σ, σ', h => absurd h.symm (cone_ne_singleton σ' σ)
  | false, true, σ, σ', h => absurd h (cone_ne_singleton σ σ')
  | false, false, σ, σ', h => ⟨rfl, cone_injective h⟩

/-- The approximation order between tagged strings: `(b, σ) ⊑ (b', σ')`. A total string is maximal
(only `⊑` itself); a partial string `σ⊥` is `⊑` anything extending `σ`. -/
def SLe : Bool → Str → Bool → Str → Prop
  | true, σ, b', σ' => b' = true ∧ σ = σ'
  | false, σ, _, σ' => σ <+: σ'

/-- `SLe` characterizes the element order on `shapeElem`. -/
theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩

/-- The interleave value function: `mergeVal σ b₀ τ b₁` returns the interleaving of the tagged
strings `(b₀, σ)` and `(b₁, τ)` as a tagged string. Boundary convention (the only monotone one):
`merge(Λ, y) = Λ`, `merge(⊥, y) = ⊥`, and `merge(εx, y) = ε⊥` once `y` runs out. -/
def mergeVal : Str → Bool → Str → Bool → Str × Bool
  | [], b₀, _, _ => ([], b₀)
  | a :: _, _, [], _ => ([a], false)
  | a :: σ, b₀, b :: τ, b₁ => (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2)

@[simp] theorem mergeVal_nil (b₀ : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal [] b₀ τ b₁ = ([], b₀) := rfl
@[simp] theorem mergeVal_cons_nil (a : Bool) (σ : Str) (b₀ b₁ : Bool) :
    mergeVal (a :: σ) b₀ [] b₁ = ([a], false) := rfl
@[simp] theorem mergeVal_cons_cons (a : Bool) (σ : Str) (b₀ b : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal (a :: σ) b₀ (b :: τ) b₁ =
      (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2) := rfl

/-- The element produced by interleaving `(b₀, σ)` and `(b₁, τ)`. -/
def mergeElem (σ : Str) (b₀ : Bool) (τ : Str) (b₁ : Bool) : C.Element :=
  shapeElem (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1

/-! #### The monotonicity of `mergeVal` (the crux of approximability). -/

/-- Two equal head bits prepended preserve `SLe`. -/
theorem SLe_cons2 {p p' : Bool} {ρ ρ' : Str} (c d : Bool) (h : SLe p ρ p' ρ') :
    SLe p (c :: d :: ρ) p' (c :: d :: ρ') := by
  cases p with
  | true => obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | false =>
    exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, h⟩⟩

/-- Invert `SLe` on a cons in the first string: the second string starts with the same head. -/
theorem SLe_cons_inv {b₀ b₀' : Bool} {a : Bool} {σ₀ σ' : Str} (h : SLe b₀ (a :: σ₀) b₀' σ') :
    ∃ σ₀', σ' = a :: σ₀' ∧ SLe b₀ σ₀ b₀' σ₀' := by
  cases b₀ with
  | true =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨σ₀, rfl, rfl, rfl⟩
  | false =>
    cases σ' with
    | nil => exact absurd h (by simp [SLe])
    | cons a' σ₀' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact ⟨σ₀', rfl, h'⟩

/-- **The monotonicity of interleaving.** If `(b₀, σ) ⊑ (b₀', σ')` and `(b₁, τ) ⊑ (b₁', τ')` then the
interleavings are `⊑`-ordered. The crux that makes `merge` approximable. -/
theorem mergeVal_SLe : ∀ (σ : Str) (b₀ : Bool) (σ' : Str) (b₀' : Bool)
    (τ : Str) (b₁ : Bool) (τ' : Str) (b₁' : Bool),
    SLe b₀ σ b₀' σ' → SLe b₁ τ b₁' τ' →
    SLe (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1
      (mergeVal σ' b₀' τ' b₁').2 (mergeVal σ' b₀' τ' b₁').1
  | [], b₀, σ', b₀', τ, b₁, τ', b₁', h0, _ => by
    cases b₀ with
    | true =>
      obtain ⟨rfl, rfl⟩ := h0
      simp only [mergeVal_nil]; exact ⟨rfl, rfl⟩
    | false =>
      simp only [mergeVal_nil]; exact List.nil_prefix
  | a :: σ₀, b₀, σ', b₀', [], b₁, τ', b₁', h0, _ => by
    obtain ⟨σ₀', rfl, _⟩ := SLe_cons_inv h0
    simp only [mergeVal_cons_nil]
    cases τ' with
    | nil => simp only [mergeVal_cons_nil]; exact List.prefix_rfl
    | cons c τ₀' => simp only [mergeVal_cons_cons]; exact ⟨c :: _, rfl⟩
  | a :: σ₀, b₀, σ', b₀', b :: τ₀, b₁, τ', b₁', h0, h1 => by
    obtain ⟨σ₀', rfl, h0'⟩ := SLe_cons_inv h0
    obtain ⟨τ₀', rfl, h1'⟩ := SLe_cons_inv h1
    simp only [mergeVal_cons_cons]
    exact SLe_cons2 a b (mergeVal_SLe σ₀ b₀ σ₀' b₀' τ₀ b₁ τ₀' b₁' h0' h1')

/-- The element-order form of `mergeVal_SLe`. -/
theorem mergeElem_mono {σ σ' τ τ' : Str} {b₀ b₀' b₁ b₁' : Bool}
    (h0 : shapeElem b₀ σ ≤ shapeElem b₀' σ') (h1 : shapeElem b₁ τ ≤ shapeElem b₁' τ') :
    mergeElem σ b₀ τ b₁ ≤ mergeElem σ' b₀' τ' b₁' :=
  shapeElem_le_iff.mpr
    (mergeVal_SLe σ b₀ σ' b₀' τ b₁ τ' b₁' (shapeElem_le_iff.mp h0) (shapeElem_le_iff.mp h1))

/-- The diagonal value: interleaving `(s, σ)` with itself doubles. -/
theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]

/-- On the diagonal `merge(⟨(s, σ), (s, σ)⟩)` doubles `σ`. -/
theorem mergeElem_diag (s : Bool) (σ : Str) : mergeElem σ s σ s = shapeElem s (double σ) := by
  simp [mergeElem, mergeVal_diag]

/-! #### A refinement lemma packaging both the representation and the order. -/

theorem shape_refine {b : Bool} {σ : Str} {P : Set Str} (hP : memC P) (hsub : P ⊆ shape b σ) :
    ∃ (b' : Bool) (σ' : Str), P = shape b' σ' ∧ shapeElem b σ ≤ shapeElem b' σ' := by
  rcases hP with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact ⟨false, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape false ρ)).mpr hsub⟩
  · exact ⟨true, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape true ρ)).mpr hsub⟩

/-! #### The map `merge`. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The interleaving map `merge : C × C → C` with
`merge(εx, δy) = ε·δ·merge(x, y)`. Built directly as an approximable map: an input neighbourhood
`shape b₀ σ ∪ shape b₁ τ` relates to the neighbourhoods of `mergeElem σ b₀ τ b₁`. -/
def mergeMap : ApproximableMap (prod C C) C where
  rel W Z := ∃ (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str),
    W = prodNbhd (shape b₀ σ) (shape b₁ τ) ∧ (mergeElem σ b₀ τ b₁).mem Z
  rel_dom := by
    rintro W Z ⟨b₀, σ, b₁, τ, rfl, _⟩
    exact prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ)
  rel_cod := by
    rintro W Z ⟨b₀, σ, b₁, τ, _, hZ⟩
    exact (mergeElem σ b₀ τ b₁).sub hZ
  master_rel := by
    refine ⟨false, [], false, [], ?_, (mergeElem [] false [] false).master_mem⟩
    show (prod C C).master = prodNbhd (shape false []) (shape false [])
    simp only [prod_master, shape, C_master, cone_nil]
  inter_right := by
    rintro W Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ ⟨b₀', σ', b₁', τ', heq, hZ'⟩
    obtain ⟨hX, hY⟩ := prodNbhd_injective heq
    obtain ⟨rfl, rfl⟩ := shape_injective hX
    obtain ⟨rfl, rfl⟩ := shape_injective hY
    exact ⟨b₀, σ, b₁, τ, rfl, (mergeElem σ b₀ τ b₁).inter_mem hZ hZ'⟩
  mono := by
    rintro W W₂ Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ hW₂W hZZ' hW₂ hZ'
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hW₂
    obtain ⟨hPsub, hQsub⟩ := prodNbhd_subset_iff.mp hW₂W
    obtain ⟨b₀', σ', hPeq, hle0⟩ := shape_refine hP hPsub
    obtain ⟨b₁', τ', hQeq, hle1⟩ := shape_refine hQ hQsub
    subst hPeq; subst hQeq
    refine ⟨b₀', σ', b₁', τ', rfl, ?_⟩
    have hmono := mergeElem_mono hle0 hle1
    exact (mergeElem σ' b₀' τ' b₁').up_mem (hmono Z hZ) hZ' hZZ'

/-- `consMap b` shifts a tagged string: `b·(c, σ) = (c, b :: σ)`. -/
@[simp] theorem consMap_shapeElem (b c : Bool) (σ : Str) :
    (consMap b).toElementMap (shapeElem c σ) = shapeElem c (b :: σ) := by
  cases c with
  | false => rw [shapeElem_false, consMap_strBot]; rfl
  | true => rw [shapeElem_true, consMap_strElem]; rfl

/-- **The value of `merge` on a pair of finite elements.** `merge(⟨(b₀, σ), (b₁, τ)⟩) =
mergeElem σ b₀ τ b₁`. The analogue of `liftC_strBot`/`liftC_strElem` for the product. -/
theorem mergeMap_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    mergeMap.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ)) = mergeElem σ b₀ τ b₁ := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, c₀, ρ, c₁, π, rfl, hZ⟩
    rw [mem_pair_prodNbhd] at hWmem
    obtain ⟨hmσ, hmτ⟩ := hWmem
    have hle0 : shapeElem c₀ ρ ≤ shapeElem b₀ σ :=
      (C.principal_le_iff (memC_shape c₀ ρ) (memC_shape b₀ σ)).mpr hmσ.2
    have hle1 : shapeElem c₁ π ≤ shapeElem b₁ τ :=
      (C.principal_le_iff (memC_shape c₁ π) (memC_shape b₁ τ)).mpr hmτ.2
    exact mergeElem_mono hle0 hle1 Z hZ
  · intro hZ
    refine ⟨prodNbhd (shape b₀ σ) (shape b₁ τ), ?_, b₀, σ, b₁, τ, rfl, hZ⟩
    exact mem_pair_prodNbhd.mpr ⟨⟨memC_shape b₀ σ, subset_rfl⟩, ⟨memC_shape b₁ τ, subset_rfl⟩⟩

/-! #### Extensionality for maps `C × C → C` via finite element pairs. -/

theorem memC_eq_shape {X : Set Str} (hX : memC X) : ∃ (b : Bool) (σ : Str), X = shape b σ := by
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨false, σ, rfl⟩
  · exact ⟨true, σ, rfl⟩

theorem prod_principal_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    (prod C C).principal (prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ))
      = pair (shapeElem b₀ σ) (shapeElem b₁ τ) := by
  apply Element.ext
  intro P
  rw [mem_principal]
  constructor
  · rintro ⟨hP, hsub⟩
    obtain ⟨X', Y', hX', hY', rfl⟩ := hP
    obtain ⟨hsX, hsY⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
  · rintro ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
    exact ⟨prod_mem_prodNbhd hX' hY', prodNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩

/-- Two maps `C × C → C` agree as soon as they agree on every pair of finite elements. -/
theorem prodMap_ext {f g : ApproximableMap (prod C C) C}
    (h : ∀ b₀ σ b₁ τ, f.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))
      = g.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))) : f = g := by
  apply eq_of_toElementMap_principal
  intro W hW
  obtain ⟨b₀, σ, b₁, τ, rfl⟩ :
      ∃ b₀ σ b₁ τ, W = prodNbhd (shape b₀ σ) (shape b₁ τ) := by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    obtain ⟨b₀, σ, rfl⟩ := memC_eq_shape hX
    obtain ⟨b₁, τ, rfl⟩ := memC_eq_shape hY
    exact ⟨b₀, σ, b₁, τ, rfl⟩
  have heq : (prod C C).principal hW = pair (shapeElem b₀ σ) (shapeElem b₁ τ) :=
    prod_principal_pair b₀ σ b₁ τ
  rw [heq]; exact h b₀ σ b₁ τ

/-! #### The recursion equation and `merge(x, x) = d(x)`. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The defining recursion of `merge`:
`merge(εx, δy) = ε·δ·merge(x, y)` for all `x, y ∈ |C|` and bits `ε, δ`. -/
theorem mergeMap_cons (ε δ : Bool) (x y : C.Element) :
    mergeMap.toElementMap
        (pair ((consMap ε).toElementMap x) ((consMap δ).toElementMap y))
      = (consMap ε).toElementMap
          ((consMap δ).toElementMap (mergeMap.toElementMap (pair x y))) := by
  have key :
      mergeMap.comp (paired ((consMap ε).comp (proj₀ C C)) ((consMap δ).comp (proj₁ C C)))
        = ((consMap ε).comp (consMap δ)).comp mergeMap := by
    apply prodMap_ext
    intro b₀ σ b₁ τ
    simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
      fst_pair, snd_pair, consMap_shapeElem, mergeMap_pair, mergeElem, mergeVal_cons_cons]
  have hx := congrArg (fun m : ApproximableMap (prod C C) C => m.toElementMap (pair x y)) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair] at hx
  exact hx

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `merge(x, x) = d(x)` for all `x ∈ |C|` (the doubling map
of Example 4.4). -/
theorem mergeMap_diag (x : C.Element) :
    mergeMap.toElementMap (pair x x) = dMap.toElementMap x := by
  have key : mergeMap.comp (paired (idMap C) (idMap C)) = dMap := by
    apply map_ext_C
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strBot σ) (strBot σ) = pair (shapeElem false σ) (shapeElem false σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_false, dMap_strBot]
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strElem σ) (strElem σ) = pair (shapeElem true σ) (shapeElem true σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_true, dMap_strElem]
  have hx := congrArg (fun m : ApproximableMap C C => m.toElementMap x) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_idMap] at hx
  exact hx

end Scott1980.Neighborhood.Exercise516

/-! ### Inlined from Scott1980/Neighborhood/Theorem69.lean -/

/-!
# Lecture VI — Theorem 6.9 (Scott 1981, PRG-19): homomorphisms out of a fixed point

> **THEOREM 6.9.** If the functor `T` is *continuous on maps* (Definition 6.8) and if `D ≅ T(D)`, so
> in particular `D` is a `T`-algebra, then for any `T`-algebra `k : T(E) → E` there is a homomorphism
> `h : D → E`.

Scott's proof. Let `i : T(D) → D` be the isomorphism making `D` a `T`-algebra and `j : D → T(D)` its
inverse. A homomorphism `h : D → E` must satisfy `h ∘ i = k ∘ T(h)`, equivalently the **fixed-point
equation**

`h = k ∘ T(h) ∘ j`.

The operator `λh. k ∘ T(h) ∘ j` on the **strict** function space `(D →⊥ E)` is approximable: the
inner `λh. T(h)` is approximable *precisely by Definition 6.8* (`ContinuousOnMaps`), and post- and
pre-composition with the fixed maps `k`, `j` is approximable too. Hence by the Lecture IV fixed-point
theory (Theorem 4.1, `fixElement`) it has a least fixed point `h`, the desired homomorphism.

## What the formalization does

We work over Scott's **strict** function space `(D →⊥ E) = strictFun D.sys E.sys` (Exercise 5.10),
exactly matching Definition 6.8.

* **`homOpComp`** — the strict composite `g ↦ k ∘ g ∘ j` as a `StrictMap`. Strictness of the composite
  uses that `j` is strict (any isomorphism of domains preserves `⊥`, `isStrict_of_comp_eq_id`) and `k`
  is strict (a morphism of Scott's *strict* category; carried as a hypothesis), so `T(h) ∘ j` and then
  `k ∘ (T(h) ∘ j)` stay strict.
* **`homOp`** — the post/pre-composition map `(T(D) →⊥ T(E)) → (D →⊥ E)`, `g ↦ k ∘ g ∘ j`, built by
  Exercise 2.8's `ofMono`. Its decisive **action lemma** `homOp_apply_filter` says
  `homOp(f̂) = (k ∘ f ∘ j)^` for every strict `f`; it is proved by reducing (through the strict
  representation `strictFunEquiv`) to single step neighbourhoods `[X, Z]`, where the "finite factoring"
  is just `N := [Y₁, Y₂]`.
* The operator is `Op = homOp ∘ Φ`, where `Φ` is Definition 6.8's witness that `λf. T(f)` is
  approximable. Its `fixElement` represents the strict map `h`; the fixed-point equation
  (`toElementMap_fixElement`) unwinds — via `Φ`'s defining property and `homOp_apply_filter` — to
  `h = k ∘ T(h) ∘ j`, which rearranges (using `j ∘ i = I`) to the homomorphism square
  `h ∘ i = k ∘ T(h)`.

The conclusion is `Nonempty {g : AlgHom ⟨D, i⟩ B // IsStrict g.hom}` — Scott's *existence* statement,
recording that the homomorphism is itself a strict map (it is `toStrictMap` of the fixed point), which
the uniqueness half of Theorem 6.14 consumes. Extracting `Φ` from the `Prop`-valued `ContinuousOnMaps`
is done by `Exists.elim` while proving a `Prop`, so it stays **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### General helper lemmas (strictness and monotonicity of composition). -/

/-- The composite of strict maps is strict: `(a ∘ b)(⊥) = a(b(⊥)) = a(⊥) = ⊥`. -/
theorem isStrict_comp {a : ApproximableMap V₁ V₂} {b : ApproximableMap V₀ V₁}
    (ha : IsStrict a) (hb : IsStrict b) : IsStrict (a.comp b) := by
  rw [isStrict_iff_apply_bot, toElementMap_comp, isStrict_iff_apply_bot.mp hb,
    isStrict_iff_apply_bot.mp ha]

/-- If `a ∘ b = I` then `a` is strict: any (split) iso preserves `⊥`. -/
theorem isStrict_of_comp_eq_id {a : ApproximableMap V₁ V₀} {b : ApproximableMap V₀ V₁}
    (h : a.comp b = idMap V₀) : IsStrict a := by
  rw [isStrict_iff_apply_bot]
  refine le_antisymm ?_ (V₀.bot_le _)
  calc a.toElementMap V₁.bot
      ≤ a.toElementMap (b.toElementMap V₀.bot) := toElementMap_mono a (V₁.bot_le _)
    _ = (a.comp b).toElementMap V₀.bot := (toElementMap_comp a b V₀.bot).symm
    _ = V₀.bot := by rw [h, toElementMap_idMap]

/-- Composition is monotone in both arguments (general arities). -/
theorem comp_mono_gen {a a' : ApproximableMap V₁ V₂} {b b' : ApproximableMap V₀ V₁}
    (ha : a ≤ a') (hb : b ≤ b') : a.comp b ≤ a'.comp b' := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hb _ _ hXY, ha _ _ hYZ⟩

/-- `toStrictMap` is monotone. -/
theorem toStrictMap_mono {φ φ' : (strictFun V₀ V₁).Element} (h : φ ≤ φ') :
    toStrictMap φ ≤ toStrictMap φ' := by
  intro X Y hrel
  rw [toStrictMap_rel] at hrel ⊢
  exact h _ hrel

/-- `toStrictFilter` is monotone. -/
theorem toStrictFilter_mono {f f' : StrictMap V₀ V₁} (h : f ≤ f') :
    toStrictFilter f ≤ toStrictFilter f' := by
  intro W hW
  rw [mem_toStrictFilter] at hW ⊢
  exact ⟨hW.1, strictFun_mem_up_closed hW.1 hW.2 h⟩

/-- `toStrictFilter ∘ toStrictMap = id` (the left inverse of the strict-function-space
representation; the mirror of `toStrictMap_toStrictFilter`). -/
theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hWmem, hfW⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
    exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
  · intro hW
    refine ⟨φ.sub hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
    intro p hp
    exact (mem_sstepFun_iff φ hL).mp hW p hp

/-! ### The post/pre-composition operator on strict function spaces. -/

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- The strict composite `g ↦ k ∘ g ∘ j : (T(D) →⊥ T(E)) → (D →⊥ E)`. -/
def homOpComp (g : StrictMap (T.obj D).sys (T.obj E).sys) : StrictMap D.sys E.sys :=
  ⟨k.comp (g.1.comp j), isStrict_comp hk (isStrict_comp g.2 hj)⟩

theorem homOpComp_mono {g g' : StrictMap (T.obj D).sys (T.obj E).sys} (hgg : g ≤ g') :
    homOpComp T D E j k hj hk g ≤ homOpComp T D E j k hj hk g' := by
  show k.comp (g.1.comp j) ≤ k.comp (g'.1.comp j)
  exact comp_mono_gen le_rfl (comp_mono_gen (Subtype.coe_le_coe.mpr hgg) le_rfl)

/-- **The operator `λg. k ∘ g ∘ j`** as an approximable map between the strict function spaces, built
by Exercise 2.8 (`ofMono`) from its values on finite elements. -/
def homOp : ApproximableMap (strictFun (T.obj D).sys (T.obj E).sys) (strictFun D.sys E.sys) :=
  ofMono
    (fun N hN => toStrictFilter (homOpComp T D E j k hj hk
      (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN))))
    (by
      intro N N' hN hN' hN'N
      apply toStrictFilter_mono
      apply homOpComp_mono
      apply toStrictMap_mono
      exact ((strictFun (T.obj D).sys (T.obj E).sys).principal_le_iff hN hN').mpr hN'N)

theorem homOp_rel {N : Set (StrictMap (T.obj D).sys (T.obj E).sys)}
    {M : Set (StrictMap D.sys E.sys)} :
    (homOp T D E j k hj hk).rel N M ↔
      ∃ hN : (strictFun (T.obj D).sys (T.obj E).sys).mem N,
        (toStrictFilter (homOpComp T D E j k hj hk
          (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN)))).mem M :=
  Iff.rfl

/-- **Action lemma.** `homOp` realizes the composite `g ↦ k ∘ g ∘ j` on filters of strict maps:
`homOp(ĝ) = (k ∘ g ∘ j)^`. Proved by reducing to single step neighbourhoods through the strict
representation. -/
theorem homOp_apply_filter (g : StrictMap (T.obj D).sys (T.obj E).sys) :
    (homOp T D E j k hj hk).toElementMap (toStrictFilter g)
      = toStrictFilter (homOpComp T D E j k hj hk g) := by
  have key : ∀ X Z,
      ((homOp T D E j k hj hk).toElementMap (toStrictFilter g)).mem (sstep X Z)
        ↔ (homOpComp T D E j k hj hk g).1.rel X Z := by
    intro X Z
    constructor
    · rintro ⟨N, hgN, hrel⟩
      rw [homOp_rel] at hrel
      obtain ⟨hN, hmem⟩ := hrel
      rw [mem_toStrictFilter] at hmem
      obtain ⟨_, hsstep⟩ := hmem
      rw [mem_sstep] at hsstep
      obtain ⟨Y2, ⟨Y1, hXY1, hY1Y2⟩, hY2Z⟩ := hsstep
      rw [toStrictMap_rel, mem_principal] at hY1Y2
      obtain ⟨_, hNsub⟩ := hY1Y2
      exact ⟨Y2, ⟨Y1, hXY1, hNsub (mem_toStrictFilter.mp hgN).2⟩, hY2Z⟩
    · intro hrel
      obtain ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩ := hrel
      refine ⟨sstep Y1 Y2, ?_, ?_⟩
      · rw [mem_toStrictFilter]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, hgY1Y2⟩
      · rw [homOp_rel]
        refine ⟨sstep_mem_of_mem (g := g) hgY1Y2, ?_⟩
        rw [mem_toStrictFilter]
        refine ⟨sstep_mem_of_mem (g := homOpComp T D E j k hj hk g)
          ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩, ?_⟩
        rw [mem_sstep]
        refine ⟨Y2, ⟨Y1, hXY1, ?_⟩, hY2Z⟩
        rw [toStrictMap_rel, mem_principal]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, subset_rfl⟩
  have hmap : toStrictMap ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
      = homOpComp T D E j k hj hk g := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Z
    rw [toStrictMap_rel]
    exact key X Z
  have hL := toStrictFilter_toStrictMap
    ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
  rw [hmap] at hL
  exact hL.symm

end HomOp

/-! ### Theorem 6.9. -/

/-- **Theorem 6.9 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D ≅ T(D)` (so `D` is a
`T`-algebra via `i : T(D) → D`), then for any `T`-algebra `B = (E, k)` with `k` strict there is a
homomorphism `D → E`. The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘ j`. -/
theorem nonempty_algHom_of_continuousOnMaps
    (T : Endofunctor DomainObj) (hT : ContinuousOnMaps T)
    {D : DomainObj} (iso : Iso (T.obj D) D)
    (B : TAlgebra T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} := by
  -- `j = i⁻¹` is strict (it is an isomorphism of domains).
  have hji : iso.inv.comp iso.hom = idMap (T.obj D).sys := iso.hom_inv_id
  have hj : IsStrict iso.inv := isStrict_of_comp_eq_id hji
  -- Definition 6.8's witness that `λf. T(f)` is approximable.
  obtain ⟨Φ, hΦ⟩ := hT D B.carrier
  -- the operator `Op = (k ∘ · ∘ j) ∘ T` and its least fixed point.
  set Op := (homOp T D B.carrier iso.inv B.str hj hk).comp Φ with hOp
  set x := Op.fixElement with hx
  set h := toStrictMap x with hh
  let Tg : StrictMap (T.obj D).sys (T.obj B.carrier).sys :=
    ⟨T.map (X := D) (Y := B.carrier) h.1, hT.isStrict_map (D := D) (E := B.carrier) h⟩
  have hfix : Op.toElementMap x = x := toElementMap_fixElement Op
  have hxh : toStrictFilter h = x := toStrictFilter_toStrictMap x
  -- `Φ` sends `h` to the filter of `T(h)`.
  have hTg : toStrictMap (Φ.toElementMap (toStrictFilter h)) = Tg := Subtype.ext (hΦ h)
  have hφ : Φ.toElementMap (toStrictFilter h) = toStrictFilter Tg := by
    rw [← hTg]; exact (toStrictFilter_toStrictMap _).symm
  -- evaluate the operator at the fixed point.
  have hOpx : Op.toElementMap x
      = toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg) := by
    rw [hOp, toElementMap_comp, ← hxh, hφ, homOp_apply_filter]
  have hcompeq : toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg)
      = toStrictFilter h := by
    rw [← hOpx, hfix, hxh]
  have hh' : homOpComp T D B.carrier iso.inv B.str hj hk Tg = h := by
    have h2 := congrArg toStrictMap hcompeq
    rwa [toStrictMap_toStrictFilter, toStrictMap_toStrictFilter] at h2
  -- the fixed-point equation `h = k ∘ T(h) ∘ j`.
  have hcore : B.str.comp ((T.map (X := D) (Y := B.carrier) h.1).comp iso.inv) = h.1 :=
    congrArg Subtype.val hh'
  -- rearrange to the homomorphism square `h ∘ i = k ∘ T(h)`.
  refine ⟨⟨{ hom := h.1, comm := ?_ }, h.2⟩⟩
  show h.1.comp iso.hom = B.str.comp (T.map (X := D) (Y := B.carrier) h.1)
  conv_lhs => rw [← hcore]
  rw [comp_assoc, comp_assoc, hji, comp_idMap]

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise617.lean -/

/-!
# Exercise 6.17 (Scott 1981, PRG-19, §6) — the algebras for which `C` is initial

> **EXERCISE 6.17.** What are the algebras for which `C` is initial? If `A` of 6.2 is a generalization
> of `B`, what is the corresponding generalization of `C`? Prove that it exists and explain what are
> the algebras involved.

`C` (Example 4.4: finite-or-infinite binary sequences) satisfies the domain equation
`C ≅ {{Λ}} + C + C` (Example 6.2, `Example62C.lean`). So `C` is a solution of the domain equation for
the functor

`T(X) = 𝟙 + X + X`   (one terminator + two successor copies).

This module proves that **`C` is the *initial* `T`-algebra**: for every `T`-algebra `(E, k)` there is a
*unique* homomorphism `C → E`. Concretely a `T`-algebra is a strict map `k : 𝟙 + E + E → E`, which by
the universal property of the separated sum is the same data as

* a distinguished element `e ∈ |E|` (the image of the terminator `𝟙`), and
* two strict endomaps `f₀, f₁ : E → E` (the two successor branches);

so **the algebras for which `C` is initial are the domains carrying a point and two strict unary
operations**, and the unique homomorphism `C → E` interprets a finite-or-infinite binary sequence
`b₀b₁b₂…` as `f_{b₀}(f_{b₁}(… e …))`.

## Why a bespoke category of `∅`-free domains

Scott's separated sum `𝒟₀ + 𝒟₁` (Exercise 3.18) is a neighbourhood system **only** under the standing
assumption `∅ ∉ 𝒟` (an empty neighbourhood of one summand would become a spurious consistency witness
for the other tag, breaking `inter_mem`). Consequently the functor `T(X) = 𝟙 + X + X` does **not**
extend to a total endofunctor of the all-systems category `DomainObj`, and the existence Theorem 6.14
(stated over `DomainObj`) cannot be instantiated directly.

Following Scott — who restricts to the category of `∅`-free systems and *strict* maps in Exercise 6.19
— we instantiate the abstract categorical vocabulary (Definitions 6.3–6.5) on the bespoke object type
`StrictDomainObj` of neighbourhood systems with **no empty neighbourhood**, with **strict approximable
maps** as morphisms. The functor `T` then reuses the existing `sum3` (Example 6.2, the genuine
three-way separated sum) and a three-way sum map, and initiality of `C` is proved **directly** (we
construct the homomorphism and prove its uniqueness by the finite-approximant argument), rather than
routing through the colimit construction of Theorem 6.14.

Everything is choice-free where it is data; the homomorphism/uniqueness layer reuses the project's
established machinery.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe w

/-! ## The category of `∅`-free domains and strict maps -/

/-- An object of Scott's category (Exercise 6.19): a token type, a neighbourhood system on it, and the
standing assumption `∅ ∉ 𝒟` (every neighbourhood is non-empty). -/
structure StrictDomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system. -/
  sys : NeighborhoodSystem carrier
  /-- Scott's standing assumption `∅ ∉ 𝒟`. -/
  nonempty : ∀ X, sys.mem X → X.Nonempty

/-- **The category of `∅`-free domains and strict maps.** Morphisms are strict approximable maps
(`StrictMap`, Exercise 5.10); identities and associative composition come from Theorem 2.5, and
strictness is preserved by `isStrict_idMap` / `isStrict_comp`. -/
instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp g f := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  comp_id f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  assoc h g f := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1)

@[simp] theorem StrictDomainObj.id_val (D : StrictDomainObj) :
    (Category.id D : StrictMap D.sys D.sys).1 = ApproximableMap.idMap D.sys := rfl

@[simp] theorem StrictDomainObj.comp_val {D E F : StrictDomainObj}
    (g : Category.Hom E F) (f : Category.Hom D E) :
    ((g ⊚ f : StrictMap D.sys F.sys)).1 = g.1.comp f.1 := rfl

/-! ## The functor `T(X) = 𝟙 + X + X` on objects -/

open Example62C in
/-- Every neighbourhood of the three-way separated sum `sum3` is non-empty (so `sum3` is again an
object of the `∅`-free category). -/
theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)

/-- **The functor `T(X) = 𝟙 + X + X` on objects.** Over `D`, the system is the genuine three-way
separated sum `𝟙 + D + D` (Example 6.2's `sum3`, with `𝟙 = unitSys`), again `∅`-free by
`sum3_nonempty`. -/
abbrev tcObj (D : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Option (Unit ⊕ D.carrier ⊕ D.carrier)
  sys := sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty
  nonempty := sum3_nonempty

@[simp] theorem tcObj_sys (D : StrictDomainObj.{w}) :
    (tcObj D).sys = sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty := rfl

/-! ### Membership-shape lemmas for `sum3` (no nesting through the wrong tag) -/

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `0`-copy `0X` is itself a `0`-copy. -/
theorem mem_subset_j0_inv {W : Set (Option (α ⊕ β ⊕ γ))} {X : Set α}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j0 X) :
    ∃ X₂, V₀.mem X₂ ∧ W = j0 X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j0
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0

/-- A `sum3`-neighbourhood contained in a `1`-copy `1Y` is itself a `1`-copy. -/
theorem mem_subset_j1_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Y : Set β}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j1 Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = j1 Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · exact ⟨Y₂, hY₂, rfl⟩
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1

/-- A `sum3`-neighbourhood contained in a `2`-copy `2Z` is itself a `2`-copy. -/
theorem mem_subset_j2_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Z : Set γ}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j2 Z) :
    ∃ Z₂, V₂.mem Z₂ ∧ W = j2 Z₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · exact ⟨Z₂, hZ₂, rfl⟩

end ShapeLemmas

/-! ### The three-way sum map `f₀ + f₁ + f₂` -/

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- **The three-way sum map `f₀ + f₁ + f₂ : 𝒟₀+𝒟₁+𝒟₂ → 𝒟₀'+𝒟₁'+𝒟₂'`.** Routes each tagged copy `iX`
through `fᵢ` (to `iYᵢ'`), and sends everything to the codomain master. (The three-way analogue of
Exercise 3.19's `sumMap`.) -/
def sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    ApproximableMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) (sum3 V₀' V₁' V₂' h₀' h₁' h₂') where
  rel W W' := (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W ∧ (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W' ∧
    (W' = master3 V₀' V₁' V₂' ∨
      (∃ X Y', W = j0 X ∧ W' = j0 Y' ∧ f₀.rel X Y') ∨
      (∃ X Y', W = j1 X ∧ W' = j1 Y' ∧ f₁.rel X Y') ∨
      (∃ X Y', W = j2 X ∧ W' = j2 Y' ∧ f₂.rel X Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem,
    Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β' ⊕ γ')),
        (W'' = master3 V₀' V₁' V₂' ∨
          (∃ X Y', W = j0 X ∧ W'' = j0 Y' ∧ f₀.rel X Y') ∨
          (∃ X Y', W = j1 X ∧ W'' = j1 Y' ∧ f₁.rel X Y') ∨
          (∃ X Y', W = j2 X ∧ W'' = j2 Y' ∧ f₂.rel X Y')) →
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩)
      · exact (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem
      · exact Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩))
    have key : (W'₁ ∩ W'₂ = master3 V₀' V₁' V₂' ∨
        (∃ X Y', W = j0 X ∧ W'₁ ∩ W'₂ = j0 Y' ∧ f₀.rel X Y') ∨
        (∃ X Y', W = j1 X ∧ W'₁ ∩ W'₂ = j1 Y' ∧ f₁.rel X Y') ∨
        (∃ X Y', W = j2 X ∧ W'₁ ∩ W'₂ = j2 Y' ∧ f₂.rel X Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩
        | ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ master3 V₀' V₁' V₂' from
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j0_subset_master3 (f₀.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := j0_injective (hWX₁.symm.trans hWX₂)
          rw [j0_inter_j0]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f₀.inter_right hf₁ hf₂⟩)
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWY₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWZ₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j1_subset_master3 (f₁.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWX₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
        · obtain rfl : Y = Y' := j1_injective (hWY₁.symm.trans hWY₂)
          rw [j1_inter_j1]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, f₁.inter_right hf₁ hf₂⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWZ₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j2_subset_master3 (f₂.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩))
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWX₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWY₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
        · obtain rfl : Z = Z' := j2_injective (hWZ₁.symm.trans hWZ₂)
          rw [j2_inter_j2]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁ ∩ Y'₂, hWZ₁, rfl, f₂.inter_right hf₁ hf₂⟩))
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hf⟩ | ⟨Z, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_master3_of_subset hW'W'₂ ((sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂mem))
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_j0_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := j0_subset_j0.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f₀.mono hf hX₂X (j0_subset_j0.mp hW'W'₂) hX₂ hY'₂⟩)
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_j1_inv hW₂mem hW₂W
      have hY₂Y : Y₂ ⊆ Y := j1_subset_j1.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y₂, Y'₂, rfl, rfl,
          f₁.mono hf hY₂Y (j1_subset_j1.mp hW'W'₂) hY₂ hY'₂⟩))
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · obtain ⟨Z₂, hZ₂, rfl⟩ := mem_subset_j2_inv hW₂mem hW₂W
      have hZ₂Z : Z₂ ⊆ Z := j2_subset_j2.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z₂, Y'₂, rfl, rfl,
          f₂.mono hf hZ₂Z (j2_subset_j2.mp hW'W'₂) hZ₂ hY'₂⟩))

/-- The three-way sum map is always strict: `(f₀+f₁+f₂)(⊥) = ⊥`. (The master only relates to the
master, since `master3` is not any tagged copy.) -/
theorem isStrict_sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    IsStrict (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
      f₀ f₁ f₂) := by
  rintro Y ⟨-, -, hd⟩
  have h0 : (none : Option (α ⊕ β ⊕ γ)) ∈ (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master := none_mem_master3
  rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWX ▸ h0) none_not_mem_j0
  · exact absurd (hWX ▸ h0) none_not_mem_j1
  · exact absurd (hWX ▸ h0) none_not_mem_j2

/-- **Functoriality (identities): `I + I + I = I`.** -/
theorem sumMap3_id :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀) (h₁' := h₁) (h₂' := h₂)
      (idMap V₀) (idMap V₁) (idMap V₂) = idMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, _, _, hXY⟩ | ⟨Y, Y', rfl, rfl, _, _, hXY⟩
      | ⟨Z, Y', rfl, rfl, _, _, hXY⟩
    · exact (sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW
    · exact j0_subset_j0.mpr hXY
    · exact j1_subset_j1.mpr hXY
    · exact j2_subset_j2.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
    · left; exact eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW')
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, X', rfl, rfl, hX, hX', j0_subset_j0.mp hsub⟩)
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hY, hY', j1_subset_j1.mp hsub⟩))
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z, Z', rfl, rfl, hZ, hZ', j2_subset_j2.mp hsub⟩))

/-- **Functoriality (composition): `(g₀∘f₀) + (g₁∘f₁) + (g₂∘f₂) = (g₀+g₁+g₂) ∘ (f₀+f₁+f₂)`.** -/
theorem sumMap3_comp {α'' β'' γ'' : Type*} {V₀'' : NeighborhoodSystem α''}
    {V₁'' : NeighborhoodSystem β''} {V₂'' : NeighborhoodSystem γ''}
    {h₀'' : ∀ X, V₀''.mem X → X.Nonempty} {h₁'' : ∀ Y, V₁''.mem Y → Y.Nonempty}
    {h₂'' : ∀ Z, V₂''.mem Z → Z.Nonempty}
    (g₀ : ApproximableMap V₀' V₀'') (g₁ : ApproximableMap V₁' V₁'') (g₂ : ApproximableMap V₂' V₂'')
    (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁') (f₂ : ApproximableMap V₂ V₂') :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
        (g₀.comp f₀) (g₁.comp f₁) (g₂.comp f₂)
      = (sumMap3 (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
          g₀ g₁ g₂).comp
        (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
          f₀ f₁ f₂) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨X, Z'', rfl, rfl, Y', hf, hg⟩ | ⟨Y, Z'', rfl, rfl, Y', hf, hg⟩
      | ⟨Z, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨master3 V₀' V₁' V₂', ⟨hW, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, hW'', Or.inl rfl⟩
    · exact ⟨j0 Y', ⟨hW, Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩),
        Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), hW'', Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩)⟩
    · exact ⟨j1 Y', ⟨hW, Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩))⟩
    · exact ⟨j2 Y', ⟨hW, Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Z, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inr ⟨Y', Z'', rfl, rfl, hg⟩))⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, _, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨X', Z'', hW'X', rfl, hg⟩ | ⟨Y', Z'', hW'Y', rfl, hg⟩
      | ⟨Z', Z'', hW'Z', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'X'.symm) ▸ none_mem_master3) none_not_mem_j0
      · obtain rfl : Y'₀ = X' := j0_injective (hW'eq.symm.trans hW'X')
        exact Or.inr (Or.inl ⟨X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
      · obtain rfl : Y'₀ = Y' := j1_injective (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr (Or.inl ⟨Y, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Z'.symm) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · obtain rfl : Y'₀ = Z' := j2_injective (hW'eq.symm.trans hW'Z')
        exact Or.inr (Or.inr (Or.inr ⟨Z, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))

end SumMap3

/-! ### The canonical injections `D_i ↪ D₀+D₁+D₂` -/

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `0`-injection `D₀ ↪ D₀+D₁+D₂`: send `x₀∈|D₀|` to the sum element whose only proper
neighbourhoods are the `0`-copies `0X` with `X∈x₀`. -/
def sinj0 (x₀ : V₀.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ X, V₀.mem X ∧ W = j0 X ∧ x₀.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [master3_inter_j0 hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, master3_inter_j0 hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x₀.sub (x₀.inter_mem hx hx'), j0_inter_j0 X X', x₀.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', hX', rfl, x₀.up_mem hx hX' (j0_subset_j0.mp hsub)⟩
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2

/-- The `1`-injection `D₁ ↪ D₀+D₁+D₂`. -/
def sinj1 (x₁ : V₁.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Y, V₁.mem Y ∧ W = j1 Y ∧ x₁.mem Y
  sub := by
    rintro W (rfl | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) (rfl | ⟨Y', hY', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Y', hY', by rw [master3_inter_j1 hY'], hx'⟩
    · exact Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j1 hY], hx⟩
    · exact Or.inr ⟨Y ∩ Y', x₁.sub (x₁.inter_mem hx hx'), j1_inter_j1 Y Y', x₁.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr ⟨Y', hY', rfl, x₁.up_mem hx hY' (j1_subset_j1.mp hsub)⟩
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2

/-- The `2`-injection `D₂ ↪ D₀+D₁+D₂`. -/
def sinj2 (x₂ : V₂.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Z, V₂.mem Z ∧ W = j2 Z ∧ x₂.mem Z
  sub := by
    rintro W (rfl | ⟨Z, hZ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) (rfl | ⟨Z', hZ', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Z', hZ', by rw [master3_inter_j2 hZ'], hx'⟩
    · exact Or.inr ⟨Z, hZ, by rw [Set.inter_comm, master3_inter_j2 hZ], hx⟩
    · exact Or.inr ⟨Z ∩ Z', x₂.sub (x₂.inter_mem hx hx'), j2_inter_j2 Z Z', x₂.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr ⟨Z', hZ', rfl, x₂.up_mem hx hZ' (j2_subset_j2.mp hsub)⟩

@[simp] theorem sinj0_mem_j0 {x₀ : V₀.Element} {X : Set α} (hX : V₀.mem X) :
    (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀).mem (j0 X) ↔ x₀.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · rw [j0_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

@[simp] theorem sinj1_mem_j1 {x₁ : V₁.Element} {Y : Set β} (hY : V₁.mem Y) :
    (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁).mem (j1 Y) ↔ x₁.mem Y := by
  constructor
  · rintro (h0 | ⟨Y', hY', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · rw [j1_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Y, hY, rfl, hx⟩

@[simp] theorem sinj2_mem_j2 {x₂ : V₂.Element} {Z : Set γ} (hZ : V₂.mem Z) :
    (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂).mem (j2 Z) ↔ x₂.mem Z := by
  constructor
  · rintro (h0 | ⟨Z', hZ', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · rw [j2_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Z, hZ, rfl, hx⟩

end SumInj

/-! ### Monotonicity of the injections, and the action of `f₀+f₁+f₂` on them -/

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sinj1_mono {x x' : V₁.Element} (hx : x ≤ x') :
    sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj1 x' := by
  rintro W (rfl | ⟨Y, hY, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Y, hY, rfl, hx Y hm⟩

theorem sinj2_mono {x x' : V₂.Element} (hx : x ≤ x') :
    sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj2 x' := by
  rintro W (rfl | ⟨Z, hZ, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Z, hZ, rfl, hx Z hm⟩

/-- `(f₀+f₁+f₂)(inj₀ x) = inj₀(f₀ x)`. -/
theorem sumMap3_sinj0 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₀ : V₀.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀)
      = sinj0 (V₁ := V₁') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₀.toElementMap x₀) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · have hXX : X = X₀ := j0_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₀.rel_cod hf, rfl, ⟨X₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j0 X, Or.inr ⟨X, x₀.sub hx, rfl, hx⟩, Or.inr (Or.inl ⟨X, x₀.sub hx, rfl⟩),
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩

/-- `(f₀+f₁+f₂)(inj₁ x) = inj₁(f₁ x)`. -/
theorem sumMap3_sinj1 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₁ : V₁.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁)
      = sinj1 (V₀ := V₀') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₁.toElementMap x₁) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · have hXX : X = Y₀ := j1_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₁.rel_cod hf, rfl, ⟨Y₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j1 X, Or.inr ⟨X, x₁.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inl ⟨X, x₁.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩))⟩

/-- `(f₀+f₁+f₂)(inj₂ x) = inj₂(f₂ x)`. -/
theorem sumMap3_sinj2 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₂ : V₂.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂)
      = sinj2 (V₀ := V₀') (V₁ := V₁') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₂.toElementMap x₂) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨c, hc⟩ := h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · have hXX : X = Z₀ := j2_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₂.rel_cod hf, rfl, ⟨Z₀, hx, hXX ▸ hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j2 X, Or.inr ⟨X, x₂.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inr ⟨X, x₂.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨X, Y', rfl, rfl, hf⟩))⟩

end SumInjMap

/-! ## The functor `T(X) = 𝟙 + X + X` -/

open Example62C in
/-- The morphism action of `T`: `T(f) = I_𝟙 + f + f` (identity on the terminator, `f` on each
successor copy). Always strict (`isStrict_sumMap3`). -/
def tcMapHom {D E : StrictDomainObj.{w}} (f : Category.Hom D E) :
    Category.Hom (tcObj D) (tcObj E) :=
  ⟨sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1, isStrict_sumMap3 _ _ _⟩

open Example62C in
/-- **Exercise 6.17 — the functor `T(X) = 𝟙 + X + X`** on the category of `∅`-free domains and strict
maps. On objects, `T(D) = 𝟙 + D + D` (Example 6.2's three-way sum); on maps, `T(f) = I_𝟙 + f + f`. -/
abbrev Tc : Endofunctor StrictDomainObj.{w} where
  obj := tcObj
  map := tcMapHom
  map_id D := Subtype.ext (by
    show sumMap3 (idMap unitSys) (idMap D.sys) (idMap D.sys) = idMap (tcObj D).sys
    exact sumMap3_id)
  map_comp {D E F} g f := Subtype.ext (by
    show sumMap3 (idMap unitSys) (g.1.comp f.1) (g.1.comp f.1)
      = (sumMap3 (idMap unitSys) g.1 g.1).comp (sumMap3 (idMap unitSys) f.1 f.1)
    have h := sumMap3_comp (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (h₀'' := Example62C.unitSys_nonempty) (h₁'' := F.nonempty) (h₂'' := F.nonempty)
      (idMap unitSys) g.1 g.1 (idMap unitSys) f.1 f.1
    rw [idMap_comp] at h
    exact h)

@[simp] theorem Tc_obj (D : StrictDomainObj.{w}) : Tc.obj D = tcObj D := rfl

@[simp] theorem Tc_map_val {D E : StrictDomainObj.{w}} (f : Category.Hom D E) :
    (Tc.map f).1 = sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1 := rfl

/-! ## `C` as a `T`-algebra -/

/-- The map of an order-isomorphism is strict (an iso of domains preserves `⊥`). -/
theorem isStrict_ofIso {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (e : V₀.Element ≃o V₁.Element) : IsStrict (ofIso e) := by
  rw [isStrict_iff_apply_bot, toElementMap_ofIso]
  exact e.map_bot

open Example44 Example62C ExampleB in
/-- `C` (Example 4.4: finite-or-infinite binary sequences) as an object of the `∅`-free category. -/
abbrev Cobj : StrictDomainObj.{0} := ⟨Str, C, C_nonempty⟩

open Example44 Example62C in
/-- **The `T`-algebra structure on `C`.** `(tcObj Cobj).sys = 𝟙 + C + C` (definitionally Example 6.2's
`CC`), and the structure map `i : 𝟙 + C + C → C` is the inverse of the domain-equation isomorphism
`ccEquiv` (Example 6.2), realised as an approximable map by `ofIso`; it is strict by `isStrict_ofIso`.
Concretely `i` sends the terminator to `Λ̂` and each `b`-copy of `x` to `b·x`. -/
abbrev cStr : Category.Hom (Tc.obj Cobj) Cobj :=
  ⟨ofIso (by exact ccEquiv.symm), isStrict_ofIso _⟩

open Example44 Example62C in
/-- **`C` is a `T`-algebra**, `(C, i)` with `T(X) = 𝟙 + X + X`. -/
abbrev Calg : TAlgebra Tc := ⟨Cobj, cStr⟩

/-! ## Initiality of `(C, i)`: the unique homomorphism into any `T`-algebra

We first relate the domain-equation isomorphism `toCC = ccEquiv` to the separated-sum injections:
the terminator `Λ̂` lands on the `𝟙`-copy, and prepending a bit (`consMap b`) lands on the `b`-th
`C`-copy. -/

namespace Example62C

open Example44 ExampleB Example62

@[simp] theorem ccEquiv_apply (x : C.Element) : ccEquiv x = toCC x := rfl

/-- `(b·z).mem (bX) ↔ z.mem X`: the `b`-successor's filter restricted to the `b`-copy is `z`. -/
theorem consMap_mem_embBit {b : Bool} {z : C.Element} {X : Set Str} (hX : C.mem X) :
    ((consMap b).toElementMap z).mem (embBit b X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', _, _, hsub⟩
    rw [← embBit_eq_prepend] at hsub
    exact z.up_mem hzX' hX (embBit_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memC_embBit b hX, ?_⟩
    rw [← embBit_eq_prepend]

/-- `(b·z)` never meets the `(¬b)`-copy: `0z` avoids the `1`-copies and vice versa (used to discharge
the cross-tag cases in `toCC_consMap`). -/
theorem consMap_not_mem_embBit_ne {b c : Bool} (hbc : b ≠ c) {z : C.Element} {X : Set Str} :
    ¬ ((consMap b).toElementMap z).mem (embBit c X) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  obtain ⟨w, hw, heq⟩ := hsub ⟨a, rfl, ha⟩
  rw [List.cons.injEq] at hw; exact hbc hw.1

/-- `(b·z)` avoids the terminator `{Λ}` (since `bσ ≠ Λ`). -/
theorem consMap_not_mem_nil {b : Bool} {z : C.Element} :
    ¬ ((consMap b).toElementMap z).mem ({[]} : Set Str) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  have := hsub ⟨a, rfl, ha⟩
  rw [Set.mem_singleton_iff] at this; exact absurd this (by simp)

/-- **`toCC ∘ (0·) = inj₁` and `toCC ∘ (1·) = inj₂`.** Prepending the bit `b` to `z` is, across the
isomorphism `C ≅ 𝟙+C+C`, the injection of `z` into the `b`-th `C`-summand. -/
theorem toCC_consMap (b : Bool) (z : C.Element) :
    toCC ((consMap b).toElementMap z)
      = cond b
          (sinj2 (V₀ := unitSys) (V₁ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z)
          (sinj1 (V₀ := unitSys) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  cases b
  · simp only [cond_false]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact Or.inr ⟨X, hX, rfl, (consMap_mem_embBit hX).mp hz⟩
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))
  · simp only [cond_true]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
      · exact Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mp hz⟩
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))

/-- **`toCC Λ̂ = inj₀`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElem_nil :
    toCC (strElem []) = sinj0 (V₁ := C) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
      (h₂ := C_nonempty) unitSys.bot := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.univ, rfl, rfl, unitSys.bot.master_mem⟩
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
  · rintro (rfl | ⟨X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · obtain rfl : X = Set.univ := hX
      exact Or.inr (Or.inl ⟨rfl, memC_singleton [], subset_rfl⟩)

end Example62C

/-! ### The homomorphism `desc : C → E` for a `T`-algebra `B = (E, k)` -/

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The distinguished point `e = k(Λ)`: the image under `k` of the terminator (`𝟙`-injection). -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinj0 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty)
    (h₂ := B.carrier.nonempty) unitSys.bot)

/-- The `b`-th successor operation `f_b = k ∘ inj_b`: `f₀` via the `0`-copy (`inj₁`), `f₁` via the
`1`-copy (`inj₂`). -/
def descF (b : Bool) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (cond b
    (sinj2 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y)
    (sinj1 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (h₂ := B.carrier.nonempty) y))

/-- The recursion `φ(Λ)=z`, `φ(b·σ)=f_b(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Str → B.carrier.sys.Element
  | [] => z
  | b :: σ => descF B b (descVal z σ)

theorem descF_mono (b : Bool) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B b y ≤ descF B b y' := by
  cases b
  · exact B.str.1.toElementMap_mono (sinj1_mono h)
  · exact B.str.1.toElementMap_mono (sinj2_mono h)

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Str) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => exact congrArg (descF B b) ih

theorem descMap_hcone {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

theorem descMap_hsing {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

/-- **The homomorphism `C → E`.** Built by `liftC` from the head-recursion: `φ(σ⊥) = f_{σ}(⊥)` and
`φ(σ) = f_{σ}(e)`, interpreting `b₀b₁… ↦ f_{b₀}(f_{b₁}(…))`. -/
def descMap : ApproximableMap C B.carrier.sys :=
  liftC B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

@[simp] theorem descMap_strBot (σ : Str) :
    (descMap B).toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ :=
  liftC_strBot _ _ _ _ _ σ

@[simp] theorem descMap_strElem (σ : Str) :
    (descMap B).toElementMap (strElem σ) = descVal B (descE B) σ :=
  liftC_strElem _ _ _ _ _ σ

theorem C_bot_eq_strBot_nil : C.bot = strBot [] := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show (C.mem Y ∧ C.master ⊆ Y) ↔ (C.mem Y ∧ cone [] ⊆ Y)
  rw [C_master, cone_nil]

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, C_bot_eq_strBot_nil, descMap_strBot]
  rfl

/-- The bundled strict homomorphism `C → E`. -/
def descStrict : Category.Hom Cobj B.carrier := ⟨descMap B, descMap_strict B⟩

/-! ### The homomorphism square and uniqueness -/

/-- The composite `inj₀∘(...)` of `T(g)` applied to a successor reduces to the operation `f_b`. The
single computational step behind both existence and uniqueness, for an *arbitrary* `g`. -/
theorem genKey (g : ApproximableMap C B.carrier.sys) (b : Bool) (w : C.Element) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap
      (toCC ((consMap b).toElementMap w)))
      = descF B b (g.toElementMap w) := by
  rw [toCC_consMap]
  cases b
  · simp only [cond_false]; rw [sumMap3_sinj1]; rfl
  · simp only [cond_true]; rw [sumMap3_sinj2]; rfl

/-- `T(g)` on the terminator is the terminator; precomposed with `k` it is `e`. -/
theorem genKey0 (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strElem [])))
      = descE B := by
  rw [toCC_strElem_nil, sumMap3_sinj0, toElementMap_idMap]
  rfl

/-- `T(g)` on `⊥` is `⊥`; precomposed with `k` it is `⊥` (both maps are strict). -/
theorem genKeyBot (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strBot [])))
      = B.carrier.sys.bot := by
  have hb : toCC (strBot []) = (sum3 unitSys C C Example62C.unitSys_nonempty Example62C.C_nonempty
      Example62C.C_nonempty).bot := by
    rw [← C_bot_eq_strBot_nil, ← Example62C.ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMap3 (h₀ := Example62C.unitSys_nonempty)
    (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (idMap unitSys) g g)]
  exact isStrict_iff_apply_bot.mp B.str.2

theorem ccEquiv_symm_comp : (ofIso ccEquiv.symm).comp (ofIso ccEquiv) = idMap C := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

theorem ccEquiv_comp_symm :
    (ofIso ccEquiv).comp (ofIso ccEquiv.symm) = idMap (sum3 unitSys C C Example62C.unitSys_nonempty
      Example62C.C_nonempty Example62C.C_nonempty) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** This is *both* the existence
witness (`descMap` satisfies it) and the uniqueness driver. -/
theorem rec_determines (g : ApproximableMap C B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKeyBot B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strBot]
      have h := genKey B g b (strBot σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElem σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKey0 B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strElem]
      have h := genKey B g b (strElem σ)
      rw [ih] at h
      exact h
  apply map_ext_C
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

/-- `C`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty)
        (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty) (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strBot]
      have h := genKey B (descMap B) b (strBot σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strElem]
      have h := genKey B (descMap B) b (strElem σ)
      rw [descMap_strElem] at h
      exact h.symm

/-- **The homomorphism square**, read off at the level of underlying approximable maps:
`desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B) (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

/-- **The descent homomorphism `(C, i) → (E, k)`** as a `T`-algebra homomorphism. -/
def descAlgHom : AlgHom Calg B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

/-- **Uniqueness.** Any `T`-algebra homomorphism out of `(C, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom Calg B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
          (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (h₁' := B.carrier.nonempty)
          (h₂' := B.carrier.nonempty) (idMap unitSys) hom.1 hom.1) :=
      congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial

/-- **Exercise 6.17 (existence half) — `(C, i)` is an initial `T`-algebra for `T(X) = 𝟙 + X + X`.**
The descent map `φ : C → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(b·x) = f_b(φ x)`
(`f_b = k ∘ inj_b`), built choice-free via `liftC`; it is the unique `T`-algebra homomorphism, so `C`
is determined (up to iso, Proposition 6.6) as the initial algebra of `X ↦ 𝟙 + X + X`. -/
def CisInitial : IsInitial Calg where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise617Gen.lean -/

/-!
# Exercise 6.17 part 2 (Scott 1981, PRG-19) — the generalization `Cₐ ≅ 𝟙 + Σₐ Cₐ`

Example 6.2 / Exercise 6.17 ask for the generalization of `C` corresponding to Scott's `A ≅ Aⁿ + Aⁿ`:
replace the two-letter alphabet `{0,1}` of `C` (`C ≅ 𝟙 + C + C`) by an arbitrary alphabet `A`. The
domain `Cₐ` of *finite or infinite `A`-sequences* then satisfies the domain equation
`Cₐ ≅ 𝟙 + Σ_{a:A} Cₐ` (the `A`-indexed separated sum of copies of `Cₐ`). Instantiating `A := Fin n`
gives **`Cₙ ≅ 𝟙 + n·Cₙ`**; `A := Bool` recovers Example 6.2's `C`.

This module mirrors, generically over an alphabet `A` with decidable equality, the binary development
of `Example44` (the domain), `Example62`/`Example62C` (the sum and the isomorphism) and `Exercise617`
(initiality).

## Stage 1 (this section): the generic domain `Cₐ`

`Strn A = List A`; cones `coneN σ = σA*`; the neighbourhood system `Cn = {σA*} ∪ {{σ}}`; the total
elements `strElemN σ` and partial elements `strBotN σ`; and the successors `consMapN a : Cₐ → Cₐ`
prepending the letter `a`. Everything is the alphabet-generic copy of `Example44`, and the data
(`Cn`, `consMapN`) stays choice-free.
-/

namespace Scott1980.Neighborhood.Exercise617Gen

set_option linter.unusedSectionVars false

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

variable {A : Type} [DecidableEq A]

/-- The token type `A*` of finite `A`-strings. -/
abbrev Strn (A : Type) := List A

/-- The cone `σA*`: all extensions of `σ`. -/
def coneN (σ : Strn A) : Set (Strn A) := {w | σ <+: w}

@[simp] theorem mem_coneN {σ w : Strn A} : w ∈ coneN σ ↔ σ <+: w := Iff.rfl

theorem coneN_nil : coneN ([] : Strn A) = Set.univ := by ext w; simp [coneN]

theorem coneN_subset_coneN {σ τ : Strn A} : coneN σ ⊆ coneN τ ↔ τ <+: σ := by
  constructor
  · intro h; exact h (show σ ∈ coneN σ from List.prefix_rfl)
  · intro hτσ w hw; exact hτσ.trans hw

theorem coneN_injective {σ τ : Strn A} (h : coneN σ = coneN τ) : σ = τ := by
  have h1 : τ <+: σ := coneN_subset_coneN.mp (le_of_eq h)
  have h2 : σ <+: τ := coneN_subset_coneN.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

theorem coneN_trichotomy (σ τ : Strn A) :
    coneN σ ⊆ coneN τ ∨ coneN τ ⊆ coneN σ ∨ coneN σ ∩ coneN τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (coneN_subset_coneN.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (coneN_subset_coneN.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_coneN, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

/-- Membership in `Cₐ`: a cone `σA*` or a singleton `{σ}`. -/
def memCn (X : Set (Strn A)) : Prop := (∃ σ, X = coneN σ) ∨ (∃ σ, X = {σ})

theorem memCn_coneN (σ : Strn A) : memCn (coneN σ) := Or.inl ⟨σ, rfl⟩

theorem memCn_singleton (σ : Strn A) : memCn ({σ} : Set (Strn A)) := Or.inr ⟨σ, rfl⟩

theorem singleton_subset_coneN {σ τ : Strn A} : ({τ} : Set (Strn A)) ⊆ coneN σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_coneN]

theorem singleton_coneN_nd (σ τ : Strn A) :
    ({τ} : Set (Strn A)) ⊆ coneN σ ∨ coneN σ ⊆ {τ} ∨ ({τ} : Set (Strn A)) ∩ coneN σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_coneN.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_coneN, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ

theorem nestedOrDisjointN : NestedOrDisjoint (memCn (A := A)) := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact coneN_trichotomy σ τ
  · rcases singleton_coneN_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_coneN_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2

/-- **The generic domain `Cₐ`** of finite-or-infinite `A`-sequences. -/
abbrev Cn (A : Type) [DecidableEq A] : NeighborhoodSystem (Strn A) :=
  NeighborhoodSystem.ofNestedOrDisjoint memCn Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], coneN_nil.symm⟩) nestedOrDisjointN
    (fun _ => Set.subset_univ _)

@[simp] theorem Cn_mem {X : Set (Strn A)} : (Cn A).mem X ↔ memCn X := Iff.rfl

@[simp] theorem Cn_master : (Cn A).master = (Set.univ : Set (Strn A)) := rfl

/-- `Cₐ` is `∅`-free: every neighbourhood is non-empty (cones and singletons are inhabited). -/
theorem Cn_nonempty : ∀ X, (Cn A).mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- The partial element `σ⊥ = ↑σA*`. -/
def strBotN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_coneN σ))

/-- The total element `σ = ↑{σ}`. -/
def strElemN (σ : Strn A) : (Cn A).Element := (Cn A).principal (Cn_mem.mpr (memCn_singleton σ))

/-! ### Prepending a letter: the successors `x ↦ a·x`. -/

/-- `σX = {στ ∣ τ ∈ X}`. -/
def prependN (σ : Strn A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prependN {σ : Strn A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ prependN σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

theorem prependN_coneN (σ ρ : Strn A) : prependN σ (coneN ρ) = coneN (σ ++ ρ) := by
  ext w
  simp only [mem_prependN, mem_coneN]
  constructor
  · rintro ⟨τ, hτ, rfl⟩; exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

theorem prependN_singleton (σ τ : Strn A) : prependN σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prependN, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩

theorem prependN_mono (σ : Strn A) {X X' : Set (Strn A)} (h : X' ⊆ X) :
    prependN σ X' ⊆ prependN σ X := by
  rintro w ⟨τ, hτ, rfl⟩; exact ⟨τ, h hτ, rfl⟩

theorem memCn_prependN (σ : Strn A) {X : Set (Strn A)} (hX : memCn X) : memCn (prependN σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prependN_coneN σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prependN_singleton σ ρ⟩

/-- **The successor `x ↦ a·x`** prepending the letter `a`: `X (a·x) Y ↔ aX ⊆ Y`. -/
def consMapN (a : A) : ApproximableMap (Cn A) (Cn A) where
  rel X Y := memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Or.inl ⟨[], coneN_nil.symm⟩, Or.inl ⟨[], coneN_nil.symm⟩,
    fun _ _ => trivial⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    have hsubInter : prependN [a] X ⊆ Y ∩ Y' := Set.subset_inter hXY hXY'
    have hZ : memCn (prependN [a] X) := memCn_prependN [a] hX
    exact ⟨hX, (Cn A).inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prependN_mono [a] hX'X).trans (hXY.trans hYY')⟩

@[simp] theorem consMapN_rel {a : A} {X Y : Set (Strn A)} :
    (consMapN a).rel X Y ↔ memCn X ∧ memCn Y ∧ prependN [a] X ⊆ Y := Iff.rfl

theorem consMapN_strBot (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strBotN σ) = strBotN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXcone⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc coneN (a :: σ) = prependN [a] (coneN σ) := by rw [prependN_coneN]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXcone
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, memCn_coneN σ, hY, ?_⟩
    rw [show prependN [a] (coneN σ) = coneN (a :: σ) by rw [prependN_coneN]; rfl]
    exact hsub

theorem consMapN_strElem (a : A) (σ : Strn A) :
    (consMapN a).toElementMap (strElemN σ) = strElemN (a :: σ) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hXsing⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    calc ({a :: σ} : Set (Strn A)) = prependN [a] {σ} := by rw [prependN_singleton]; rfl
      _ ⊆ prependN [a] X := prependN_mono [a] hXsing
      _ ⊆ Y := hsub
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, memCn_singleton σ, hY, ?_⟩
    rw [show prependN [a] ({σ} : Set (Strn A)) = {a :: σ} by rw [prependN_singleton]; rfl]
    exact hsub

/-! ## Stage 2: the `A`-indexed separated sum `Tsig(X) = 𝟙 + Σ_{a:A} X`

The right-hand side of the generalized domain equation. Tokens are `Option (Unit ⊕ (A × β))`: a
fresh basepoint `Λ = none`, the lone `𝟙`-token `tu = some (inl ())`, and the `A`-indexed family of
tagged copies `tc a t = some (inr (a, t))`. This is the alphabet-generic analogue of `Example62C`'s
three-way `sum3 unitSys C C` (`= 𝟙 + C + C`), the index `Bool` being replaced by `A`. -/

section SumSig

universe v

variable {β : Type v} {γ : Type v}

/-- Tokens of the indexed sum `𝟙 + Σ_a β`. -/
abbrev SigTok (A : Type) (β : Type v) := Option (Unit ⊕ (A × β))

/-- The lone `𝟙`-token. -/
def tu : SigTok A β := some (Sum.inl ())

/-- The token `t` in the `a`-indexed copy. -/
def tc (a : A) (t : β) : SigTok A β := some (Sum.inr (a, t))

/-- The `𝟙`-copy neighbourhood (the image of `univ : Set Unit`). -/
def jU : Set (SigTok A β) := {tu}

/-- The `a`-indexed tagged copy `aX`. -/
def jc (a : A) (X : Set β) : Set (SigTok A β) := {w | ∃ t, w = tc a t ∧ t ∈ X}

theorem tc_injective {a a' : A} {t t' : β} (h : (tc a t : SigTok A β) = tc a' t') :
    a = a' ∧ t = t' := by
  simp only [tc, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h; exact h

@[simp] theorem tc_mem_jc {a : A} {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∈ jc a X ↔ t ∈ X := by
  constructor
  · rintro ⟨t', heq, ht'⟩; obtain ⟨-, rfl⟩ := tc_injective heq; exact ht'
  · intro ht; exact ⟨t, rfl, ht⟩

@[simp] theorem mem_jU {w : SigTok A β} : w ∈ (jU : Set (SigTok A β)) ↔ w = tu := Iff.rfl

@[simp] theorem none_not_mem_jU : (none : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu]

@[simp] theorem none_not_mem_jc {a : A} {X : Set β} : (none : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tc])

@[simp] theorem tu_not_mem_jc {a : A} {X : Set β} : (tu : SigTok A β) ∉ jc a X := by
  rintro ⟨t, heq, -⟩; exact absurd heq (by simp [tu, tc])

@[simp] theorem tc_not_mem_jU {a : A} {t : β} : (tc a t : SigTok A β) ∉ (jU : Set (SigTok A β)) := by
  simp [jU, tu, tc]

theorem tc_mem_jc_ne {a a' : A} (h : a ≠ a') {X : Set β} {t : β} :
    (tc a t : SigTok A β) ∉ jc a' X := by
  rintro ⟨t', heq, -⟩; exact h (tc_injective heq).1

theorem jc_inter_jc_same (a : A) (X X' : Set β) :
    (jc a X ∩ jc a X' : Set (SigTok A β)) = jc a (X ∩ X') := by
  ext w
  constructor
  · rintro ⟨⟨t, rfl, ht⟩, ⟨t', heq, ht'⟩⟩
    obtain ⟨-, rfl⟩ := tc_injective heq; exact ⟨t, rfl, ht, ht'⟩
  · rintro ⟨t, rfl, ht, ht'⟩; exact ⟨⟨t, rfl, ht⟩, ⟨t, rfl, ht'⟩⟩

theorem jc_inter_jc_ne {a a' : A} (h : a ≠ a') (X X' : Set β) :
    (jc a X ∩ jc a' X' : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl, -⟩ ⟨t', heq, -⟩
  exact h (tc_injective heq).1

theorem jU_inter_jc (a : A) (X : Set β) : (jU ∩ jc a X : Set (SigTok A β)) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_jU, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl; exact tu_not_mem_jc

theorem jU_nonempty : (jU : Set (SigTok A β)).Nonempty := ⟨tu, rfl⟩

theorem jc_nonempty {a : A} {X : Set β} (hX : X.Nonempty) : (jc a X : Set (SigTok A β)).Nonempty := by
  obtain ⟨t, ht⟩ := hX; exact ⟨tc a t, t, rfl, ht⟩

theorem jc_subset_jc {a : A} {X X' : Set β} :
    (jc a X : Set (SigTok A β)) ⊆ jc a X' ↔ X ⊆ X' := by
  constructor
  · intro h t ht; exact tc_mem_jc.mp (h (tc_mem_jc.mpr ht))
  · rintro h w ⟨t, rfl, ht⟩; exact tc_mem_jc.mpr (h ht)

theorem jc_injective {a : A} {X X' : Set β} (h : (jc a X : Set (SigTok A β)) = jc a X') : X = X' :=
  Set.Subset.antisymm (jc_subset_jc.mp h.subset) (jc_subset_jc.mp h.symm.subset)

/-- Tagged copies determine both index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`,
`X=X'`. -/
theorem jc_eq_jc {a a' : A} {X X' : Set β} (hXne : X.Nonempty)
    (heq : (jc a X : Set (SigTok A β)) = jc a' X') : a = a' ∧ X = X' := by
  obtain ⟨t, ht⟩ := hXne
  obtain ⟨t', he, -⟩ := heq ▸ (tc_mem_jc.mpr ht)
  obtain ⟨rfl, -⟩ := tc_injective he
  exact ⟨rfl, jc_injective heq⟩

variable (V : NeighborhoodSystem β)

/-- The master neighbourhood `{Λ} ∪ {tu} ∪ ⋃_a aΔ`. -/
def masterSig : Set (SigTok A β) :=
  {w | w = none ∨ w = tu ∨ ∃ a t, t ∈ V.master ∧ w = tc a t}

variable {V}

@[simp] theorem none_mem_masterSig : (none : SigTok A β) ∈ masterSig V := Or.inl rfl

@[simp] theorem tu_mem_masterSig : (tu : SigTok A β) ∈ masterSig V := Or.inr (Or.inl rfl)

theorem jU_subset_masterSig : (jU : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w rfl; exact tu_mem_masterSig

theorem jc_subset_masterSig {a : A} {X : Set β} (hX : V.mem X) :
    (jc a X : Set (SigTok A β)) ⊆ masterSig V := by
  rintro w ⟨t, rfl, ht⟩; exact Or.inr (Or.inr ⟨a, t, V.sub_master hX ht, rfl⟩)

theorem masterSig_inter_jU : (masterSig V ∩ jU : Set (SigTok A β)) = jU :=
  Set.inter_eq_right.mpr jU_subset_masterSig

theorem masterSig_inter_jc {a : A} {X : Set β} (hX : V.mem X) :
    (masterSig V ∩ jc a X : Set (SigTok A β)) = jc a X :=
  Set.inter_eq_right.mpr (jc_subset_masterSig hX)

theorem eq_masterSig_of_subset {W : Set (SigTok A β)}
    (hsub : masterSig V ⊆ W) (hsub' : W ⊆ masterSig V) : W = masterSig V :=
  Set.Subset.antisymm hsub' hsub

/-- **The `A`-indexed separated sum `𝟙 + Σ_a V`** over `{Λ} ∪ {tu} ∪ ⋃_a aΔ`, under the standing
assumption that no neighbourhood of `V` is empty. The alphabet-generic analogue of `sum3 unitSys V V`
(Example 6.2). -/
def sumSig (A : Type) [DecidableEq A] (V : NeighborhoodSystem β)
    (h : ∀ X, V.mem X → X.Nonempty) :
    NeighborhoodSystem (SigTok A β) where
  mem W := W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X
  master := masterSig V
  master_nonempty := ⟨none, none_mem_masterSig⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
    · exact subset_rfl
    · exact jU_subset_masterSig
    · exact jc_subset_masterSig hX
  inter_mem := by
    have hne : ∀ W, (W = masterSig V ∨ W = jU ∨ ∃ a X, V.mem X ∧ W = jc a X) →
        (W : Set (SigTok A β)).Nonempty := by
      rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
      · exact ⟨none, none_mem_masterSig⟩
      · exact jU_nonempty
      · exact jc_nonempty (h X hX)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [masterSig_inter_jc hX']; exact Or.inr (Or.inr ⟨a', X', hX', rfl⟩)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jU]; exact Or.inr (Or.inl rfl)
      · rw [Set.inter_self]; exact Or.inr (Or.inl rfl)
      · rw [jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · rw [Set.inter_comm, masterSig_inter_jc hX]; exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
      · rw [Set.inter_comm, jU_inter_jc] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · by_cases haa : a = a'
        · subst haa
          rw [jc_inter_jc_same] at hZsub ⊢
          rcases hZ with rfl | rfl | ⟨a₂, Z₂, hZ₂, rfl⟩
          · exact absurd (hZsub none_mem_masterSig) (by simp)
          · exact absurd (hZsub (show tu ∈ jU from rfl)) tu_not_mem_jc
          · by_cases ha₂ : a = a₂
            · subst ha₂
              exact Or.inr (Or.inr ⟨a, X ∩ X', V.inter_mem hX hX' hZ₂ (jc_subset_jc.mp hZsub), rfl⟩)
            · obtain ⟨t, ht⟩ := h Z₂ hZ₂
              exact absurd (hZsub (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm ha₂))
        · rw [jc_inter_jc_ne haa] at hZsub ⊢
          obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)

@[simp] theorem sumSig_master {h : ∀ X, V.mem X → X.Nonempty} :
    (sumSig A V h).master = masterSig V := rfl

theorem sumSig_nonempty {h : ∀ X, V.mem X → X.Nonempty} :
    ∀ W, (sumSig A V h).mem W → W.Nonempty := by
  rintro W (rfl | rfl | ⟨a, X, hX, rfl⟩)
  · exact ⟨none, none_mem_masterSig⟩
  · exact jU_nonempty
  · exact jc_nonempty (h X hX)

/-! ### Shape lemmas: no nesting through the wrong tag. -/

variable {h : ∀ X, V.mem X → X.Nonempty}

/-- A `sumSig`-neighbourhood contained in an `a`-copy `aX` is itself an `a`-copy. -/
theorem mem_subset_jc_inv {W : Set (SigTok A β)} {a : A} {X : Set β}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jc a X) : ∃ X₂, V.mem X₂ ∧ W = jc a X₂ := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jc
  · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
    obtain ⟨rfl, -⟩ := tc_injective heq
    exact ⟨X₂, hX₂, rfl⟩

/-- A `sumSig`-neighbourhood contained in the `𝟙`-copy `jU` is `jU`. -/
theorem mem_subset_jU_inv {W : Set (SigTok A β)}
    (hW : (sumSig A V h).mem W) (hsub : W ⊆ jU) : W = jU := by
  rcases hW with rfl | rfl | ⟨a', X₂, hX₂, rfl⟩
  · exact absurd (hsub none_mem_masterSig) none_not_mem_jU
  · rfl
  · obtain ⟨t, ht⟩ := h X₂ hX₂
    exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU

/-! ### The canonical injections `𝟙 ↪ 𝟙+Σ_a V` and `V ↪ 𝟙+Σ_a V` (the `a`-th copy). -/

/-- The basepoint/`𝟙`-injection: the image of the unique point of `𝟙`. Its proper neighbourhood is
the `𝟙`-copy `jU`. -/
def sinjU : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ W = jU
  sub := by
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | rfl) (rfl | rfl)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (by rw [masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_comm, masterSig_inter_jU])
    · exact Or.inr (by rw [Set.inter_self])
  up_mem := by
    rintro W W' (rfl | rfl) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc

/-- The `a`-th copy injection `V ↪ 𝟙+Σ_a V`: send `x∈|V|` to the sum element whose proper
neighbourhoods are the `a`-copies `aX` with `X∈x`. -/
def sinjC (a : A) (x : V.Element) : (sumSig A V h).Element where
  mem W := W = masterSig V ∨ ∃ X, V.mem X ∧ W = jc a X ∧ x.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [masterSig_inter_jc hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x.sub (x.inter_mem hx hx'), jc_inter_jc_same a X X', x.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V h).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h X (x.sub hx)
        obtain ⟨t', heq, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective heq
        exact Or.inr ⟨X', hX', rfl, x.up_mem hx hX' (jc_subset_jc.mp hsub)⟩

@[simp] theorem sinjU_mem_jU : (sinjU (h := h)).mem (jU : Set (SigTok A β)) := Or.inr rfl

@[simp] theorem sinjC_mem_jc {a : A} {x : V.Element} {X : Set β} (hX : V.mem X) :
    (sinjC (h := h) a x).mem (jc a X) ↔ x.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · rw [jc_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

theorem sinjC_mono {a : A} {x x' : V.Element} (hxle : x ≤ x') :
    sinjC (h := h) a x ≤ sinjC a x' := by
  rintro W (rfl | ⟨X, hX, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, hX, rfl, hxle X hm⟩

end SumSig

/-! ### The sum map `Σ f = I_𝟙 + Σ_a f` and its functoriality. -/

section SumMapSig

universe v

variable {β₀ β₁ β₂ : Type v}
  {V₀ : NeighborhoodSystem β₀} {V₁ : NeighborhoodSystem β₁} {V₂ : NeighborhoodSystem β₂}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- **The indexed sum map `Σf = I_𝟙 + Σ_a f`** acting as the identity on the `𝟙`-summand and as `f`
on each `a`-copy. The generic analogue of `sumMap3 (idMap unitSys) f f`. -/
def sumMapSig (f : ApproximableMap V₀ V₁) :
    ApproximableMap (sumSig A V₀ h₀) (sumSig A V₁ h₁) where
  rel W W' := (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
    (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
      ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y')
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨(sumSig A V₀ h₀).master_mem, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (SigTok A β₁),
        (W'' = masterSig V₁ ∨ (W = jU ∧ W'' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W'' = jc a Y' ∧ f.rel X Y') → (sumSig A V₁ h₁).mem W'' := by
      rintro W'' (rfl | ⟨-, rfl⟩ | ⟨a, X, Y', -, rfl, hf⟩)
      · exact (sumSig A V₁ h₁).master_mem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩)
    have key : (W'₁ ∩ W'₂ = masterSig V₁ ∨ (W = jU ∧ W'₁ ∩ W'₂ = jU) ∨
        ∃ a X Y', W = jc a X ∧ W'₁ ∩ W'₂ = jc a Y' ∧ f.rel X Y') := by
      rcases hd₁ with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Y'₁, hWX, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ masterSig V₁ from
          (sumSig A V₁ h₁).sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hWX, rfl, hf⟩
        · rw [Set.inter_eq_left.mpr jU_subset_masterSig]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · rw [Set.inter_self]; exact Or.inr (Or.inl ⟨hWU, rfl⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf)
          exact absurd ((hWX.symm.trans hWU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · rcases hd₂ with rfl | ⟨hWU2, rfl⟩ | ⟨a', X', Y'₂, hWX', rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (jc_subset_masterSig (f.rel_cod hf₁))]
          exact Or.inr (Or.inr ⟨a, X, Y'₁, hWX, rfl, hf₁⟩)
        · obtain ⟨t, ht⟩ := h₀ X (f.rel_dom hf₁)
          exact absurd ((hWX.symm.trans hWU2) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
        · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X (f.rel_dom hf₁)) (hWX.symm.trans hWX')
          rw [jc_inter_jc_same]
          exact Or.inr (Or.inr ⟨a, X, Y'₁ ∩ Y'₂, hWX, rfl, f.inter_right hf₁ hf₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_masterSig_of_subset hW'W'₂ ((sumSig A V₁ h₁).sub_master hW'₂mem))
    · have hW₂jU : W₂ = jU := mem_subset_jU_inv hW₂mem hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hW₂jU, rfl⟩)
      · exact absurd (hW'W'₂ (show tu ∈ jU from rfl)) tu_not_mem_jc
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_jc_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := jc_subset_jc.mp hW₂W
      rcases hW'₂mem with rfl | rfl | ⟨a', Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        exact absurd (hW'W'₂ (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₁ Y' (f.rel_cod hf)
        obtain ⟨t', he, -⟩ := hW'W'₂ (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X₂, Y'₂, rfl, rfl,
          f.mono hf hX₂X (jc_subset_jc.mp hW'W'₂) hX₂ hY'₂⟩)

/-- The sum map is strict: it sends `⊥ = master` only to `master`. -/
theorem isStrict_sumMapSig (f : ApproximableMap V₀ V₁) :
    IsStrict (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  rintro W' ⟨-, -, hd⟩
  rcases hd with rfl | ⟨hWU, -⟩ | ⟨a, X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWU ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jU
  · exact absurd (hWX ▸ (show (none : SigTok A β₀) ∈ (sumSig A V₀ h₀).master from
      none_mem_masterSig)) none_not_mem_jc

@[simp] theorem sumMapSig_rel {f : ApproximableMap V₀ V₁} {W W'} :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).rel W W' ↔
      (sumSig A V₀ h₀).mem W ∧ (sumSig A V₁ h₁).mem W' ∧
        (W' = masterSig V₁ ∨ (W = jU ∧ W' = jU) ∨
          ∃ a X Y', W = jc a X ∧ W' = jc a Y' ∧ f.rel X Y') := Iff.rfl

/-- `Σf` fixes the basepoint injection. -/
theorem sumMapSig_sinjU (f : ApproximableMap V₀ V₁) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjU (h := h₀))
      = sinjU (h := h₁) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨-, rfl⟩ | ⟨a, X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hU with hUm | rfl
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · exact absurd (hUj ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · rintro (rfl | rfl)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · exact ⟨jU, Or.inr rfl, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl),
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- `Σf` on the `a`-copy injection: `(Σf)(inj_a x) = inj_a (f x)`. -/
theorem sumMapSig_sinjC (f : ApproximableMap V₀ V₁) (a : A) (x : V₀.Element) :
    (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f).toElementMap (sinjC (h := h₀) a x)
      = sinjC (h := h₁) a (f.toElementMap x) := by
  apply NeighborhoodSystem.Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, -, -, hd⟩
    rcases hd with rfl | ⟨hUjU, rfl⟩ | ⟨a', X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUjU) ▸ none_mem_masterSig) none_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X₀ hX₀
        exact absurd ((hUeq.symm.trans hUjU) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₀ X₀ hX₀) (hUeq.symm.trans hUj)
        exact Or.inr ⟨Y', f.rel_cod hf, rfl, ⟨X₀, hx, hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨masterSig V₀, Or.inl rfl, (sumSig A V₀ h₀).master_mem,
        (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨jc a X, Or.inr ⟨X, x.sub hx, rfl, hx⟩, Or.inr (Or.inr ⟨a, X, x.sub hx, rfl⟩),
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩

/-- **Functoriality (identities): `Σ(I) = I`.** -/
theorem sumMapSig_id :
    sumMapSig (A := A) (V₀ := V₀) (V₁ := V₀) (h₀ := h₀) (h₁ := h₀) (idMap V₀)
      = idMap (sumSig A V₀ h₀) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨rfl, rfl⟩ | ⟨a, X, Y', rfl, rfl, -, -, hXY⟩
    · exact (sumSig A V₀ h₀).sub_master hW
    · exact subset_rfl
    · exact jc_subset_jc.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl (eq_masterSig_of_subset hsub ((sumSig A V₀ h₀).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := h₀ X hX; exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := h₀ X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X, X', rfl, rfl, hX, hX', jc_subset_jc.mp hsub⟩)

/-- **Functoriality (composition): `Σ(g∘f) = Σg ∘ Σf`.** -/
theorem sumMapSig_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    sumMapSig (A := A) (h₀ := h₀) (h₁ := h₂) (g.comp f)
      = (sumMapSig (A := A) (h₀ := h₁) (h₁ := h₂) g).comp
          (sumMapSig (A := A) (h₀ := h₀) (h₁ := h₁) f) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨hWU, rfl⟩ | ⟨a, X, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨masterSig V₁, ⟨hW, (sumSig A V₁ h₁).master_mem, Or.inl rfl⟩,
        (sumSig A V₁ h₁).master_mem, hW'', Or.inl rfl⟩
    · exact ⟨jU, ⟨hW, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨hWU, rfl⟩)⟩,
        Or.inr (Or.inl rfl), hW'', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨jc a Y', ⟨hW, Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩),
        Or.inr (Or.inr ⟨a, X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inr ⟨a, Y', f.rel_cod hf, rfl⟩), hW'',
        Or.inr (Or.inr ⟨a, Y', Z'', rfl, rfl, hg⟩)⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, -, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨hW'U, rfl⟩ | ⟨a, Y', Z'', hW'Y', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨hWU, -⟩ | ⟨a, X, Y'₀, -, hW'eq, hf⟩
      · exact absurd ((hW'U.symm) ▸ none_mem_masterSig) none_not_mem_jU
      · exact Or.inr (Or.inl ⟨hWU, rfl⟩)
      · obtain ⟨t, ht⟩ := h₁ Y'₀ (f.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'U) ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
    · rcases hdf with rfl | ⟨-, hW'U⟩ | ⟨a', X, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_masterSig) none_not_mem_jc
      · obtain ⟨t, ht⟩ := h₁ Y' (g.rel_dom hg)
        exact absurd ((hW'U.symm.trans hW'Y') ▸ tc_mem_jc.mpr ht) tc_not_mem_jU
      · obtain ⟨rfl, rfl⟩ := jc_eq_jc (h₁ Y'₀ (f.rel_cod hf)) (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr ⟨a', X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)

end SumMapSig

/-! ## The endofunctor `Tsig(X) = 𝟙 + Σ_a X` on the `∅`-free category. -/

/-- `Tsig` on objects: `Tsig(D) = 𝟙 + Σ_a D`, again `∅`-free (`sumSig_nonempty`). -/
abbrev tsigObj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) : StrictDomainObj.{0} where
  carrier := SigTok A D.carrier
  sys := sumSig A D.sys D.nonempty
  nonempty := sumSig_nonempty

@[simp] theorem tsigObj_sys (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (tsigObj A D).sys = sumSig A D.sys D.nonempty := rfl

/-- `Tsig` on maps: `Tsig(f) = I_𝟙 + Σ_a f`, strict by `isStrict_sumMapSig`. -/
def tsigMapHom (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}} (f : Category.Hom D E) :
    Category.Hom (tsigObj A D) (tsigObj A E) :=
  ⟨sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1, isStrict_sumMapSig _⟩

@[simp] theorem tsigMapHom_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : Category.Hom D E) :
    (tsigMapHom A f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

/-- **The functor `Tsig(X) = 𝟙 + Σ_{a:A} X`** on the category of `∅`-free domains and strict maps. -/
abbrev Tsig (A : Type) [DecidableEq A] : Endofunctor StrictDomainObj.{0} where
  obj := tsigObj A
  map := tsigMapHom A
  map_id _ := Subtype.ext sumMapSig_id
  map_comp {_ _ _} g f := Subtype.ext (sumMapSig_comp g.1 f.1)

@[simp] theorem Tsig_obj (A : Type) [DecidableEq A] (D : StrictDomainObj.{0}) :
    (Tsig A).obj D = tsigObj A D := rfl

@[simp] theorem Tsig_map_val (A : Type) [DecidableEq A] {D E : StrictDomainObj.{0}}
    (f : Category.Hom D E) :
    ((Tsig A).map f).1 = sumMapSig (A := A) (h₀ := D.nonempty) (h₁ := E.nonempty) f.1 := rfl

/-! ## Stage 3: the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.

The alphabet-generic analogue of `Example62C` (`C ≅ 𝟙 + C + C`). Prepending the letter `a` to a
neighbourhood gives `embA a X`; a `Cₐ`-neighbourhood is the master, the terminator `{Λ}`, or some
`a`-copy `aX`, exactly the shapes of the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/

section Iso

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `aX = {a :: w' ∣ w' ∈ X}`: the `a`-prefixed copy of a neighbourhood. -/
def embA (a : A) (X : Set (Strn A)) : Set (Strn A) := {w | ∃ w', w = a :: w' ∧ w' ∈ X}

@[simp] theorem mem_embA {a : A} {X : Set (Strn A)} {w : Strn A} :
    w ∈ embA a X ↔ ∃ w', w = a :: w' ∧ w' ∈ X := Iff.rfl

theorem embA_eq_prependN (a : A) (X : Set (Strn A)) : embA a X = prependN [a] X := by
  ext w
  simp only [mem_embA, mem_prependN]
  constructor
  · rintro ⟨w', rfl, hX⟩; exact ⟨w', hX, rfl⟩
  · rintro ⟨t, hX, rfl⟩; exact ⟨t, rfl, hX⟩

theorem embA_coneN (a : A) (σ : Strn A) : embA a (coneN σ) = coneN (a :: σ) := by
  rw [embA_eq_prependN, prependN_coneN]; rfl

theorem embA_singleton (a : A) (σ : Strn A) : embA a ({σ} : Set (Strn A)) = {a :: σ} := by
  rw [embA_eq_prependN, prependN_singleton]; rfl

theorem memCn_embA (a : A) {X : Set (Strn A)} (hX : memCn X) : memCn (embA a X) := by
  rw [embA_eq_prependN]; exact memCn_prependN [a] hX

theorem nil_not_mem_embA {a : A} {X : Set (Strn A)} : ([] : Strn A) ∉ embA a X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

theorem embA_ne_univ (a : A) (X : Set (Strn A)) : embA a X ≠ Set.univ := by
  intro h; exact nil_not_mem_embA (X := X) (a := a) (by rw [h]; trivial)

theorem embA_inter (a : A) (X X' : Set (Strn A)) : embA a X ∩ embA a X' = embA a (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩; exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

theorem embA_inter_ne {a a' : A} (h : a ≠ a') (X Y : Set (Strn A)) :
    embA a X ∩ embA a' Y = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embA, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨w', rfl, -⟩ ⟨w'', heq, -⟩
  rw [List.cons.injEq] at heq; exact h heq.1

theorem embA_subset {a : A} {X X' : Set (Strn A)} : embA a X ⊆ embA a X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq; obtain ⟨-, rfl⟩ := heq; exact hX'
  · rintro h w ⟨w', rfl, hX⟩; exact ⟨w', rfl, h hX⟩

theorem embA_injective {a : A} {X X' : Set (Strn A)} (h : embA a X = embA a X') : X = X' :=
  Set.Subset.antisymm (embA_subset.mp h.subset) (embA_subset.mp h.symm.subset)

theorem embA_nonempty {a : A} {X : Set (Strn A)} (hX : X.Nonempty) : (embA a X).Nonempty := by
  obtain ⟨w', hw'⟩ := hX; exact ⟨a :: w', w', rfl, hw'⟩

theorem memCn_embA_inv {a : A} {W : Set (Strn A)} (h : memCn (embA a W)) : memCn W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embA a W := hσ ▸ (show σ ∈ coneN σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_coneN] at hσ; rw [embA_injective hσ]; exact memCn_coneN w'
  · have hmem : σ ∈ embA a W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set (Strn A)))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embA_singleton] at hσ; rw [embA_injective hσ]; exact memCn_singleton w'

theorem embA_ne {a a' : A} (h : a ≠ a') {X Y : Set (Strn A)} (hX : X.Nonempty) :
    embA a X ≠ embA a' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (a :: w') ∈ embA a' Y := heq ▸ (⟨w', rfl, hw'⟩ : (a :: w') ∈ embA a X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he; exact h he.1

theorem singleton_nil_inter_embA (a : A) (X : Set (Strn A)) :
    (({[]} : Set (Strn A)) ∩ embA a X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embA, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩; exact absurd heq (by simp)

theorem singleton_nil_ne_univ : ({[]} : Set (Strn A)) ≠ Set.univ := by
  intro h
  have hmem : ([default] : Strn A) ∈ ({[]} : Set (Strn A)) := by rw [h]; trivial
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

theorem singleton_nil_ne_embA (a : A) (X : Set (Strn A)) :
    ({[]} : Set (Strn A)) ≠ embA a X := by
  intro h
  exact nil_not_mem_embA (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Strn A) ∈ ({[]} : Set (Strn A))))

/-- **The shape of a `Cₐ`-neighbourhood.** Every neighbourhood is the master `Σ*`, the terminator
`{Λ}`, or an `a`-copy `aX` with `X ∈ Cₐ`. -/
theorem memCn_cases {W : Set (Strn A)} (hW : memCn W) :
    W = Set.univ ∨ W = ({[]} : Set (Strn A)) ∨ ∃ a X, memCn X ∧ W = embA a X := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl coneN_nil
    | cons a σ' => exact Or.inr (Or.inr ⟨a, coneN σ', memCn_coneN σ', (embA_coneN a σ').symm⟩)
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons a σ' => exact Or.inr (Or.inr ⟨a, {σ'}, memCn_singleton σ', (embA_singleton a σ').symm⟩)

/-! ### The sum target `𝟙 + Σ_a Cₐ` and its inversion lemmas. -/

/-- The right-hand side of the domain equation: the `A`-indexed sum `𝟙 + Σ_a Cₐ`. -/
abbrev CCn (A : Type) [DecidableEq A] : NeighborhoodSystem (SigTok A (Strn A)) :=
  sumSig A (Cn A) Cn_nonempty

theorem sumSig_mem_jc_inv {a : A} {X : Set (Strn A)} (h : (CCn A).mem (jc a X)) :
    (Cn A).mem X := by
  rcases h with h0 | hU | ⟨a', X', hX', heq⟩
  · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
  · have : (tu : SigTok A (Strn A)) ∈ jc a X := by rw [hU]; rfl
    exact absurd this tu_not_mem_jc
  · by_cases haa : a = a'
    · subst haa; rw [jc_injective heq]; exact hX'
    · obtain ⟨t, ht⟩ := Cn_nonempty X' hX'
      exact absurd (heq.symm ▸ (tc_mem_jc.mpr ht)) (tc_mem_jc_ne (Ne.symm haa))

/-! ### The forward half `toCC : |Cₐ| → |𝟙 + Σ_a Cₐ|`. -/

/-- **Forward half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** Records, for each branch, whether `x` finishes at `Λ`
(the `𝟙`-summand) or reaches the `a`-copy `aX` (the `a`-th summand). -/
def toCC (x : (Cn A).Element) : (CCn A).Element where
  mem W := W = masterSig (Cn A)
    ∨ (W = jU ∧ x.mem ({[]} : Set (Strn A)))
    ∨ (∃ a X, (Cn A).mem X ∧ W = jc a X ∧ x.mem (embA a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨a', X', hX', rfl, hzF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [masterSig_inter_jU], hzU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [masterSig_inter_jc hX'], hzF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, masterSig_inter_jU], hzU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hzU⟩)
    · exfalso
      have hx := x.inter_mem hzU hzF'; rw [singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_comm, masterSig_inter_jc hX], hzF⟩)
    · exfalso
      have hx := x.inter_mem hzF hzU'; rw [Set.inter_comm, singleton_nil_inter_embA] at hx
      obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hx := x.inter_mem hzF hzF'; rw [embA_inter] at hx
        exact Or.inr (Or.inr ⟨a, X ∩ X', memCn_embA_inv (x.sub hx), jc_inter_jc_same a X X', hx⟩)
      · exfalso
        have hx := x.inter_mem hzF hzF'; rw [embA_inter_ne haa] at hx
        obtain ⟨t, ht⟩ := Cn_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨a, X, hX, rfl, hzF⟩) hW' hsub
    · exact Or.inl (eq_masterSig_of_subset hsub ((CCn A).sub_master hW'))
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (show tu ∈ jU from rfl)) tu_not_mem_jc
    · rcases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        exact absurd (hsub (tc_mem_jc.mpr ht)) tc_not_mem_jU
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨t', he, -⟩ := hsub (tc_mem_jc.mpr ht)
        obtain ⟨rfl, -⟩ := tc_injective he
        exact Or.inr (Or.inr ⟨a, X', hX', rfl,
          x.up_mem hzF (memCn_embA a hX') (embA_subset.mpr (jc_subset_jc.mp hsub))⟩)

@[simp] theorem toCC_mem_jU {x : (Cn A).Element} :
    (toCC x).mem (jU : Set (SigTok A (Strn A))) ↔ x.mem ({[]} : Set (Strn A)) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨a', X', hX', heq, hz⟩)
    · exact absurd (h0.symm ▸ none_mem_masterSig) none_not_mem_jU
    · exact hz
    · exact absurd (heq ▸ (show tu ∈ jU from rfl)) tu_not_mem_jc
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

@[simp] theorem toCC_mem_jc {x : (Cn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (toCC x).mem (jc a X) ↔ x.mem (embA a X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨a', X', hX', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_masterSig) none_not_mem_jc
    · obtain ⟨t, ht⟩ := Cn_nonempty X hX
      exact absurd (heq ▸ (tc_mem_jc.mpr ht)) tc_not_mem_jU
    · obtain ⟨rfl, rfl⟩ := jc_eq_jc (Cn_nonempty X hX) heqj
      exact hz
  · intro hz; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hz⟩)

/-- Prefixed copies determine index and set: `aX = a'X'` (with `X` non-empty) forces `a=a'`, `X=X'`. -/
theorem embA_eq_embA {a a' : A} {X X' : Set (Strn A)} (hXne : X.Nonempty)
    (h : embA a X = embA a' X') : a = a' ∧ X = X' := by
  obtain ⟨w', hw'⟩ := hXne
  have hmem : (a :: w') ∈ embA a X := ⟨w', rfl, hw'⟩
  rw [h] at hmem
  obtain ⟨u, he, -⟩ := hmem
  rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
  exact ⟨rfl, embA_injective h⟩

/-! ### The inverse half `fromCC : |𝟙 + Σ_a Cₐ| → |Cₐ|`. -/

/-- **Inverse half of `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
def fromCC (s : (CCn A).Element) : (Cn A).Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set (Strn A)) ∧ s.mem jU)
    ∨ (∃ a X, (Cn A).mem X ∧ W = embA a X ∧ s.mem (jc a X))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨a, X, hX, rfl, -⟩)
    · exact Or.inl ⟨[], coneN_nil.symm⟩
    · exact memCn_singleton []
    · exact memCn_embA a hX
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨a', X', hX', rfl, hsF'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr ⟨a', X', hX', by rw [Set.univ_inter], hsF'⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨a, X, hX, by rw [Set.inter_univ], hsF⟩)
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, jU_inter_jc] at hs
      obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
    · by_cases haa : a = a'
      · subst haa
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_same] at hs
        exact Or.inr (Or.inr ⟨a, X ∩ X', sumSig_mem_jc_inv (s.sub hs), embA_inter a X X', hs⟩)
      · exfalso
        have hs := s.inter_mem hsF hsF'; rw [jc_inter_jc_ne haa] at hs
        obtain ⟨t, ht⟩ := sumSig_nonempty _ (s.sub hs); exact Set.notMem_empty t ht
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨a, X, hX, rfl, hsF⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
    · rcases memCn_cases hW' with rfl | rfl | ⟨a', X', hX', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        have hm := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · obtain ⟨t, ht⟩ := Cn_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨t, rfl, ht⟩ : (a :: t) ∈ embA a X)
        rw [List.cons.injEq] at he; obtain ⟨rfl, -⟩ := he
        refine Or.inr (Or.inr ⟨a, X', hX', rfl, ?_⟩)
        exact s.up_mem hsF (Or.inr (Or.inr ⟨a, X', hX', rfl⟩))
          (jc_subset_jc.mpr (embA_subset.mp hsub))

@[simp] theorem fromCC_mem_nil {s : (CCn A).Element} :
    (fromCC s).mem ({[]} : Set (Strn A)) ↔ s.mem (jU : Set (SigTok A (Strn A))) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨a', X', hX', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embA a' X')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

@[simp] theorem fromCC_mem_embA {s : (CCn A).Element} {a : A} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    (fromCC s).mem (embA a X) ↔ s.mem (jc a X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨a', X', hX', heqj, hs⟩)
    · exact absurd h0 (embA_ne_univ a X)
    · exact absurd heq.symm (singleton_nil_ne_embA a X)
    · obtain ⟨rfl, rfl⟩ := embA_eq_embA (Cn_nonempty X hX) heqj
      exact hs
  · intro hs; exact Or.inr (Or.inr ⟨a, X, hX, rfl, hs⟩)

/-! ### The two halves are mutually inverse. -/

theorem fromCC_toCC (x : (Cn A).Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_jU.mp hs
    · exact (toCC_mem_jc hX).mp hs
  · intro hW
    rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_jU.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (toCC_mem_jc hX).mpr hW⟩)

theorem toCC_fromCC (s : (CCn A).Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨a, X, hX, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embA hX).mp hs
  · intro hW
    rcases s.sub hW with rfl | rfl | ⟨a, X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (fromCC_mem_embA hX).mpr hW⟩)

/-- **The isomorphism `|Cₐ| ≃o |𝟙 + Σ_a Cₐ|`.** -/
def ccEquiv : (Cn A).Element ≃o (CCn A).Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro hle W hW
      rcases memCn_cases (x.sub hW) with rfl | rfl | ⟨a, X, hX, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_jU.mp (hle _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_jc hX).mp (hle _ (Or.inr (Or.inr ⟨a, X, hX, rfl, hW⟩)))
    · intro hle W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hle _ hz⟩)
      · exact Or.inr (Or.inr ⟨a, X, hX, rfl, hle _ hz⟩)

@[simp] theorem ccEquiv_apply (x : (Cn A).Element) : ccEquiv x = toCC x := rfl

/-! ### Bridging the isomorphism to the successors `consMapN`. -/

theorem consMapN_mem_embA {a : A} {z : (Cn A).Element} {X : Set (Strn A)} (hX : (Cn A).mem X) :
    ((consMapN a).toElementMap z).mem (embA a X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', -, -, hsub⟩
    rw [← embA_eq_prependN] at hsub
    exact z.up_mem hzX' hX (embA_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memCn_embA a hX, ?_⟩
    rw [← embA_eq_prependN]

theorem consMapN_not_mem_embA_ne {a c : A} (hac : a ≠ c) {z : (Cn A).Element} {X : Set (Strn A)} :
    ¬ ((consMapN a).toElementMap z).mem (embA c X) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  obtain ⟨w, hw, -⟩ := hsub ⟨t, rfl, ht⟩
  rw [List.cons.injEq] at hw; exact hac hw.1

theorem consMapN_not_mem_nil {a : A} {z : (Cn A).Element} :
    ¬ ((consMapN a).toElementMap z).mem ({[]} : Set (Strn A)) := by
  rintro ⟨X', hzX', hX'mem, -, hsub⟩
  obtain ⟨t, ht⟩ := Cn_nonempty X' hX'mem
  rw [← embA_eq_prependN] at hsub
  have hmem := hsub ⟨t, rfl, ht⟩
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

/-- **`toCC ∘ (a·) = inj_a`.** Prepending the letter `a` to `z` is, across `Cₐ ≅ 𝟙+Σ_a Cₐ`, the
injection of `z` into the `a`-th summand. -/
theorem toCC_consMapN (a : A) (z : (Cn A).Element) :
    toCC ((consMapN a).toElementMap z) = sinjC (h := Cn_nonempty) a z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨c, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact absurd hz consMapN_not_mem_nil
    · by_cases hac : a = c
      · subst hac; exact Or.inr ⟨X, hX, rfl, (consMapN_mem_embA hX).mp hz⟩
      · exact absurd hz (consMapN_not_mem_embA_ne hac)
  · rintro (rfl | ⟨X, hX, rfl, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨a, X, hX, rfl, (consMapN_mem_embA hX).mpr hm⟩)

/-- **`toCC Λ̂ = inj_𝟙`.** The finished empty sequence is the terminator (the `𝟙`-summand). -/
theorem toCC_strElemN_nil :
    toCC (strElemN ([] : Strn A)) = sinjU (h := Cn_nonempty) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨a, X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embA
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, memCn_singleton [], subset_rfl⟩)

end Iso

/-! ## `Cₐ` as a `Tsig`-algebra. -/

section Algebra

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `Cₐ` as an object of the `∅`-free category. -/
abbrev Cnobj (A : Type) [DecidableEq A] : StrictDomainObj.{0} := ⟨Strn A, Cn A, Cn_nonempty⟩

@[simp] theorem Cnobj_sys (A : Type) [DecidableEq A] : (Cnobj A).sys = Cn A := rfl

/-- **The `Tsig`-algebra structure on `Cₐ`.** The structure map `i : 𝟙+Σ_a Cₐ → Cₐ` is the inverse of
the domain-equation isomorphism `ccEquiv`, strict by `isStrict_ofIso`. -/
abbrev cnStr : Category.Hom ((Tsig A).obj (Cnobj A)) (Cnobj A) :=
  ⟨ofIso ccEquiv.symm, isStrict_ofIso _⟩

/-- **`Cₐ` is a `Tsig`-algebra** for `Tsig(X) = 𝟙 + Σ_a X`. -/
abbrev Cnalg (A : Type) [DecidableEq A] [Inhabited A] : TAlgebra (Tsig A) := ⟨Cnobj A, cnStr⟩

end Algebra

/-! ## The `liftCn` combinator: an approximable map out of `Cₐ` (generic `Exercise419.liftC`). -/

section Lift

variable {A : Type} [DecidableEq A] [Inhabited A] {β : Type}

/-- A cone is never contained in a singleton: it has the two distinct elements `τ` and `τ·default`. -/
theorem not_coneN_subset_singleton (τ σ : Strn A) : ¬ coneN τ ⊆ ({σ} : Set (Strn A)) := by
  intro h
  have h1 : τ ∈ ({σ} : Set (Strn A)) := h (show τ ∈ coneN τ from List.prefix_rfl)
  have h2 : (τ ++ [default]) ∈ ({σ} : Set (Strn A)) := h (List.prefix_append τ [default])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [default] := h1.trans h2.symm
  simp at this

theorem coneN_ne_singleton (τ σ : Strn A) : coneN τ ≠ ({σ} : Set (Strn A)) := fun h =>
  not_coneN_subset_singleton τ σ (h ▸ subset_rfl)

/-- A map `Cₐ → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`. (The alphabet-generic copy of `Exercise419.liftC`.) -/
def liftCn (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap (Cn A) V where
  rel X Y := (∃ σ, X = coneN σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memCn_coneN σ
    · exact memCn_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [Cn_master]; exact coneN_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have hσσ : σ = σ' := coneN_injective hX'
      subst hσσ
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (coneN_ne_singleton σ σ')
    · exact absurd hX'.symm (coneN_ne_singleton σ' σ)
    · have hσσ : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst hσσ
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · have hpre : σ <+: τ := coneN_subset_coneN.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · have hpre : σ <+: τ := singleton_subset_coneN.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_coneN_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have hmem := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at hmem
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

theorem liftCn_strBot (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strBotN σ) = coneVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := coneN_subset_coneN.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_coneN_subset_singleton σ σ')
  · intro hY
    exact ⟨coneN σ, ⟨memCn_coneN σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

theorem liftCn_strElem (V : NeighborhoodSystem β) (coneVal singVal : Strn A → V.Element)
    (hcone : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Strn A}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Strn A) :
    (liftCn V coneVal singVal hcone hsing).toElementMap (strElemN σ) = singVal σ := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_coneN.mp; rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have hmem := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at hmem
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memCn_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

/-- Two maps out of `Cₐ` agree once they agree on every `σ⊥` and `σ` (generic `Exercise516.map_ext_C`). -/
theorem map_ext_Cn {V : NeighborhoodSystem β} {f g : ApproximableMap (Cn A) V}
    (hbot : ∀ σ, f.toElementMap (strBotN σ) = g.toElementMap (strBotN σ))
    (helem : ∀ σ, f.toElementMap (strElemN σ) = g.toElementMap (strElemN σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (Cn_mem.mp hX)
  · exact hbot σ
  · exact helem σ

end Lift

/-! ## Initiality of `(Cₐ, i)`: the unique homomorphism into any `Tsig`-algebra. -/

section Initial

variable {A : Type} [DecidableEq A] [Inhabited A] (B : TAlgebra (Tsig A))

/-- The distinguished point `e = k(inj_𝟙)`: the image under `k` of the terminator. -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjU (h := B.carrier.nonempty))

/-- The `a`-th successor operation `f_a = k ∘ inj_a`. -/
def descF (a : A) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinjC (h := B.carrier.nonempty) a y)

/-- The recursion `φ(Λ)=z`, `φ(a·σ)=f_a(φ(σ))` on a finite string, with base value `z`. -/
def descVal (z : B.carrier.sys.Element) : Strn A → B.carrier.sys.Element
  | [] => z
  | a :: σ => descF B a (descVal z σ)

theorem descF_mono (a : A) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B a y ≤ descF B a y' :=
  B.str.1.toElementMap_mono (sinjC_mono h)

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Strn A) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons a σ ih => exact congrArg (descF B a) ih

theorem descMap_hcone {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

theorem descMap_hsing {σ τ : Strn A} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

/-- **The homomorphism `Cₐ → E`**, built by `liftCn` from the head-recursion. -/
def descMap : ApproximableMap (Cn A) B.carrier.sys :=
  liftCn B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

@[simp] theorem descMap_strBot (σ : Strn A) :
    (descMap B).toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ :=
  liftCn_strBot _ _ _ _ _ σ

@[simp] theorem descMap_strElem (σ : Strn A) :
    (descMap B).toElementMap (strElemN σ) = descVal B (descE B) σ :=
  liftCn_strElem _ _ _ _ _ σ

theorem Cn_bot_eq_strBotN_nil : (Cn A).bot = strBotN ([] : Strn A) := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  show ((Cn A).mem Y ∧ (Cn A).master ⊆ Y) ↔ ((Cn A).mem Y ∧ coneN [] ⊆ Y)
  rw [Cn_master, coneN_nil]

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, Cn_bot_eq_strBotN_nil, descMap_strBot]
  rfl

/-- The bundled strict homomorphism `Cₐ → E`. -/
def descStrict : Category.Hom (Cnobj A) B.carrier := ⟨descMap B, descMap_strict B⟩

/-! ### The homomorphism square and uniqueness. -/

theorem genKey (g : ApproximableMap (Cn A) B.carrier.sys) (a : A) (w : (Cn A).Element) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC ((consMapN a).toElementMap w)))
      = descF B a (g.toElementMap w) := by
  rw [toCC_consMapN, sumMapSig_sinjC]; rfl

theorem genKey0 (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strElemN ([] : Strn A))))
      = descE B := by
  rw [toCC_strElemN_nil, sumMapSig_sinjU]; rfl

theorem genKeyBot (g : ApproximableMap (Cn A) B.carrier.sys) :
    B.str.1.toElementMap ((sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g).toElementMap (toCC (strBotN ([] : Strn A))))
      = B.carrier.sys.bot := by
  have hb : toCC (strBotN ([] : Strn A)) = (CCn A).bot := by
    rw [← Cn_bot_eq_strBotN_nil, ← ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMapSig (A := A) (h₀ := Cn_nonempty)
    (h₁ := B.carrier.nonempty) g)]
  exact isStrict_iff_apply_bot.mp B.str.2

theorem ccEquiv_symm_comp :
    (ofIso (ccEquiv (A := A)).symm).comp (ofIso ccEquiv) = idMap (Cn A) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

theorem ccEquiv_comp_symm :
    (ofIso (ccEquiv (A := A))).comp (ofIso ccEquiv.symm) = idMap (CCn A) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** -/
theorem rec_determines (g : ApproximableMap (Cn A) B.carrier.sys)
    (hg : g = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBotN σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKeyBot B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strBot]
      have h := genKey B g a (strBotN σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElemN σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply]
      exact genKey0 B g
    | cons a σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, ccEquiv_apply,
        ← consMapN_strElem]
      have h := genKey B g a (strElemN σ)
      rw [ih] at h
      exact h
  apply map_ext_Cn
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

/-- `Cₐ`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_Cn
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strBot]
      have h := genKey B (descMap B) a (strBotN σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons a σ =>
      rw [ccEquiv_apply, ← consMapN_strElem]
      have h := genKey B (descMap B) a (strElemN σ)
      rw [descMap_strElem] at h
      exact h.symm

/-- **The homomorphism square** `desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty)
        (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

/-- **The descent homomorphism `(Cₐ, i) → (E, k)`** as a `Tsig`-algebra homomorphism. -/
def descAlgHom : AlgHom (Cnalg A) B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val]
    exact descComm B

/-- **Uniqueness.** Any `Tsig`-algebra homomorphism out of `(Cₐ, i)` equals `descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom (Cnalg A) B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMapSig (A := A) (h₀ := Cn_nonempty) (h₁ := B.carrier.nonempty) hom.1) := by
      exact congrArg Subtype.val comm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    simp only at h2
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial

/-- **Exercise 6.17 part 2 — `(Cₐ, i)` is an initial `Tsig`-algebra for `Tsig(X) = 𝟙 + Σ_a X`.**
The descent map `φ : Cₐ → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(a·x) = f_a(φ x)`
(`f_a = k ∘ inj_a`), built choice-free via `liftCn`; it is the unique `Tsig`-algebra homomorphism, so
`Cₐ` is the initial algebra of `X ↦ 𝟙 + Σ_a X`. -/
def CnisInitial (A : Type) [DecidableEq A] [Inhabited A] : IsInitial (Cnalg A) where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

/-- **Exercise 6.17 part 2 — the domain equation `Cₐ ≅ 𝟙 + Σ_a Cₐ`.** -/
theorem Cn_domain_equation (A : Type) [DecidableEq A] [Inhabited A] :
    Cn A ≅ᴰ CCn A := ⟨ccEquiv⟩

/-! ## Instantiation: `Cₙ ≅ 𝟙 + n·Cₙ` over the `n`-letter alphabet `Fin (n+1)`.

Taking `A := Fin (n+1)` recovers Scott's `Cₙ`: the domain of finite-or-infinite sequences over an
`(n+1)`-letter alphabet, satisfying `Cₙ ≅ 𝟙 + (n+1)·Cₙ`. (For `n = 1`, `Fin 2 ≃ Bool` recovers
Example 6.2's `C ≅ 𝟙 + C + C`.) -/

/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))

/-- **`Cₙ` is the initial algebra** of `X ↦ 𝟙 + Σ_{Fin (n+1)} X`. -/
def CfinIsInitial (n : ℕ) : IsInitial (Cnalg (Fin (n + 1))) := CnisInitial (Fin (n + 1))

end Scott1980.Neighborhood.Exercise617Gen

/-! ### Inlined from Scott1980/Neighborhood/Exercise618.lean -/

/-!
# Exercise 6.18 (Scott 1981, PRG-19, §6) — `𝒟^∞` as an initial algebra

> **EXERCISE 6.18.** With reference back to Exercise 3.16 discuss the construction of `𝒟^∞` as an
> initial algebra and as a solution to the domain equation `𝒟^∞ ≅ 𝒟 × 𝒟^∞`.

Exercise 3.16 already constructs the infinite iterate `𝒟^∞` (`iterSys`, over `ℕ × Δ`) and proves the
**domain-equation** half, `𝒟^∞ ≅ 𝒟 × 𝒟^∞` (`iter_isomorphic`, with the explicit element iso
`iterProdIso`). This module supplies the **initial-algebra** half.

For a fixed `∅`-free domain `𝒟` consider the (product) endofunctor
`T(X) = 𝒟 × X`. The domain equation `𝒟^∞ ≅ T(𝒟^∞)` makes `𝒟^∞` a `T`-algebra, with structure map
`i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" isomorphism (Exercise 3.16's `iterProdIso⁻¹`). We prove **`𝒟^∞` is the
initial `T`-algebra**: for every `T`-algebra `(E, k)` there is a *unique* (strict) homomorphism
`𝒟^∞ → E`, namely `h(⟨x₀,x₁,…⟩) = k(x₀, k(x₁, k(x₂, …)))`, the least fixed point of
`λh. k ∘ T(h) ∘ j`.

## Architecture

The genuine analysis is done at the level of plain approximable maps (over `iterSys V`,
`prod V (iterSys V)`, and a target `E`), then packaged into the bespoke category `StrictDomainObj`
of `∅`-free domains and strict maps (Exercise 6.17), where `IsInitial` directly expresses Scott's
universal property among strict algebras (cf. Theorem 6.14, which is initiality *among strict
algebras* — the product functor grows the token set, so Theorem 6.14's same-carrier colimit tower
does **not** apply, and `𝒟^∞` must be built directly as in Exercise 3.16).

* **Existence.** `descMap = ⋃ₙ hₙ`, `h₀ = ⊥`, `hₙ₊₁ = k ∘ T(hₙ) ∘ j`. It is strict and satisfies the
  fixed-point equation `descMap = k ∘ T(descMap) ∘ j`, hence the homomorphism square
  `descMap ∘ i = k ∘ T(descMap)` (since `j ∘ i = I`).
* **Uniqueness.** The truncation chain `ρₙ : 𝒟^∞ → 𝒟^∞`, `ρ₀ = ⊥`, `ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`,
  computes to `ρₙ(⟨xᵢ⟩) = ⟨x₀,…,x_{n-1},⊥,⊥,…⟩` (`rho_apply`) and satisfies `⋃ₙ ρₙ = I` (`iSupRho_eq_id`,
  the cofinite-`Δ` structure of `iterSys`). For any strict homomorphism `g`, the sequence `g ∘ ρₙ` is
  `g`-independent (the recursion `g∘ρₙ₊₁ = k∘T(g∘ρₙ)∘j`), so `g = ⋃ₙ g∘ρₙ` is forced.

Everything is choice-free where it is data.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe w

namespace Exercise618

/-! ## `∅`-freeness is preserved by `prod` and `iterSys` -/

/-- The product of two `∅`-free systems is `∅`-free. -/
theorem prod_nonempty {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (_h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ∀ W, (prod V₀ V₁).mem W → W.Nonempty := by
  rintro W ⟨X, Y, hX, _, rfl⟩
  obtain ⟨a, ha⟩ := h₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

/-- The infinite iterate of an `∅`-free system is `∅`-free (each fibre is a non-empty neighbourhood). -/
theorem iterSys_nonempty {α : Type*} {V : NeighborhoodSystem α}
    (h : ∀ X, V.mem X → X.Nonempty) :
    ∀ W, (iterSys V).mem W → W.Nonempty := by
  rintro W ⟨hfib, _⟩
  obtain ⟨a, ha⟩ := h (fiber W 0) (hfib 0)
  exact ⟨(0, a), ha⟩

/-! ## The "cons" description of the Exercise 3.16 isomorphism -/

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The forward iso reads off head and tail.** `iterProdIso z = ⟨z₀, ⟨z₁,z₂,…⟩⟩`: the first
component is the `0`-coordinate `component z 0`, the second is the shifted sequence. -/
theorem iterProdIso_apply (z : (iterSys V).Element) :
    iterProdIso V z = pair (component z 0) (ofSeq (fun n => component z (n + 1))) := rfl

/-- The "cons" of a head `a : |𝒟|` and a tail `b : |𝒟^∞|`, as a sequence `⟨a, b₀, b₁, …⟩`. -/
def consSeq (a : V.Element) (b : (iterSys V).Element) : ℕ → V.Element :=
  fun i => Nat.casesOn i a (fun k => component b k)

@[simp] theorem consSeq_zero (a : V.Element) (b : (iterSys V).Element) : consSeq a b 0 = a := rfl

@[simp] theorem consSeq_succ (a : V.Element) (b : (iterSys V).Element) (k : ℕ) :
    consSeq a b (k + 1) = component b k := rfl

/-- **The inverse iso is "cons".** `iterProdIso⁻¹ ⟨a, b⟩ = ⟨a, b₀, b₁, …⟩`. -/
theorem iterProdIso_symm_pair (a : V.Element) (b : (iterSys V).Element) :
    (iterProdIso V).symm (pair a b) = ofSeq (consSeq a b) := by
  have hkey : iterProdIso V (ofSeq (consSeq a b)) = pair a b := by
    rw [iterProdIso_apply]
    congr 1
    · rw [component_ofSeq, consSeq_zero]
    · have : (fun n => component (ofSeq (consSeq a b)) (n + 1)) = fun n => component b n := by
        funext n; rw [component_ofSeq, consSeq_succ]
      rw [this, ofSeq_component]
  rw [← hkey, OrderIso.symm_apply_apply]

/-! ## Bottom-element computations -/

/-- `⊥` of `𝒟^∞` is the all-`⊥` sequence. -/
theorem iterBot_eq : (iterSys V).bot = ofSeq (fun _ : ℕ => V.bot) := by
  apply Element.ext
  intro W
  rw [mem_bot, mem_ofSeq]
  constructor
  · rintro rfl
    refine ⟨(iterSys V).master_mem, fun i => ?_⟩
    rw [fiber_iterSys_master, mem_bot]
  · rintro ⟨_, hfib⟩
    apply eq_of_fiber_eq
    intro i
    have hi := hfib i
    rw [fiber_iterSys_master]
    rwa [mem_bot] at hi

/-- The `n`-th coordinate of `⊥` is `⊥`. -/
@[simp] theorem component_bot (n : ℕ) : component (iterSys V).bot n = V.bot := by
  rw [iterBot_eq, component_ofSeq]

/-- `⊥` of a product is the pair of `⊥`s. -/
theorem pair_bot {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} :
    pair V₀.bot V₁.bot = (prod V₀ V₁).bot := by
  apply Element.ext
  intro W
  rw [mem_bot, prod_master]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY; subst hX; subst hY; rfl
  · rintro rfl
    exact ⟨V₀.master, V₁.master, V₀.bot.master_mem, V₁.bot.master_mem, rfl⟩

/-! ## The structure isomorphism `i, j` as approximable maps -/

/-- `j : 𝒟^∞ → 𝒟 × 𝒟^∞`, the splitting iso (`iterProdIso`). -/
def jmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (prod V (iterSys V)) :=
  ofIso (iterProdIso V)

/-- `i : 𝒟 × 𝒟^∞ → 𝒟^∞`, the "cons" iso (`iterProdIso⁻¹`); the `T`-algebra structure map. -/
def imap (V : NeighborhoodSystem α) : ApproximableMap (prod V (iterSys V)) (iterSys V) :=
  ofIso (iterProdIso V).symm

theorem isStrict_imap : IsStrict (imap V) := isStrict_ofIso _

/-- `j ∘ i = I` on `𝒟 × 𝒟^∞`. -/
theorem jmap_comp_imap : (jmap V).comp (imap V) = idMap (prod V (iterSys V)) := by
  apply ext_of_toElementMap
  intro w
  simp only [jmap, imap]
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

/-! ## Monotonicity of the product action -/

/-- `T(·) = (id_𝒟 × ·)` is monotone. -/
theorem prodMap_idMap_mono {γ : Type*} {E : NeighborhoodSystem γ}
    {f f' : ApproximableMap (iterSys V) E} (h : f ≤ f') :
    prodMap (idMap V) f ≤ prodMap (idMap V) f' := by
  intro W P hrel
  simp only [prodMap, paired_rel] at hrel ⊢
  exact ⟨hrel.1, hrel.2.1, comp_mono_gen h le_rfl _ _ hrel.2.2⟩

/-- Approximable maps are monotone in the map argument: `f ≤ g ⟹ f(x) ≤ g(x)`. -/
theorem toElementMap_le_of_le {β₀ β₁ : Type*} {W₀ : NeighborhoodSystem β₀}
    {W₁ : NeighborhoodSystem β₁} {f g : ApproximableMap W₀ W₁} (h : f ≤ g) (x : W₀.Element) :
    f.toElementMap x ≤ g.toElementMap x := by
  rintro Y ⟨X, hX, hrel⟩
  exact ⟨X, hX, h _ _ hrel⟩

/-! ## The homomorphism operator and the descent chain -/

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The homomorphism operator `Op(f) = k ∘ T(f) ∘ j`. -/
def descOp (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E) :
    ApproximableMap (iterSys V) E :=
  k.comp ((prodMap (idMap V) f).comp (jmap V))

/-- The defining action of the operator: `Op(f)(z) = k(z₀, f(⟨z₁,z₂,…⟩))`. -/
theorem descOp_apply (k : ApproximableMap (prod V E) E) (f : ApproximableMap (iterSys V) E)
    (z : (iterSys V).Element) :
    (descOp k f).toElementMap z
      = k.toElementMap (pair (component z 0)
          (f.toElementMap (ofSeq (fun n => component z (n + 1))))) := by
  simp only [descOp, jmap]
  rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, iterProdIso_apply,
    toElementMap_prodMap_pair, toElementMap_idMap]

theorem descOp_mono (k : ApproximableMap (prod V E) E) {f f' : ApproximableMap (iterSys V) E}
    (h : f ≤ f') : descOp k f ≤ descOp k f' :=
  comp_mono_gen le_rfl (comp_mono_gen (prodMap_idMap_mono h) le_rfl)

/-- The descent chain `h₀ = ⊥`, `hₙ₊₁ = Op(hₙ)`. -/
def descSeq (k : ApproximableMap (prod V E) E) : ℕ → ApproximableMap (iterSys V) E
  | 0 => constMap (iterSys V) E.bot
  | (n + 1) => descOp k (descSeq k n)

/-- The bottom map is below everything. -/
theorem constBot_le (f : ApproximableMap (iterSys V) E) :
    constMap (iterSys V) E.bot ≤ f := by
  intro X Y hrel
  obtain ⟨hX, hY⟩ := hrel
  rw [mem_bot] at hY; subst hY
  exact f.rel_master hX

theorem descSeq_mono_succ (k : ApproximableMap (prod V E) E) (n : ℕ) :
    descSeq k n ≤ descSeq k (n + 1) := by
  induction n with
  | zero => exact constBot_le _
  | succ m ih => exact descOp_mono k ih

theorem descSeq_mono (k : ApproximableMap (prod V E) E) {n m : ℕ} (h : n ≤ m) :
    descSeq k n ≤ descSeq k m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descSeq_mono_succ k _)

theorem descSeq_dir (k : ApproximableMap (prod V E) E) :
    ∀ i j, ∃ l, (∀ X Y, (descSeq k i).rel X Y → (descSeq k l).rel X Y) ∧
      (∀ X Y, (descSeq k j).rel X Y → (descSeq k l).rel X Y) :=
  fun i j => ⟨max i j, fun _ _ => descSeq_mono k (le_max_left i j) _ _,
    fun _ _ => descSeq_mono k (le_max_right i j) _ _⟩

/-- **The descent map `h = ⋃ₙ hₙ : 𝒟^∞ → E`.** -/
def descMap (k : ApproximableMap (prod V E) E) : ApproximableMap (iterSys V) E :=
  iSupMap (descSeq k) (descSeq_dir k)

theorem descMap_toElementMap (k : ApproximableMap (prod V E) E) (z : (iterSys V).Element)
    {Y : Set γ} :
    ((descMap k).toElementMap z).mem Y ↔ ∃ n, ((descSeq k n).toElementMap z).mem Y :=
  mem_toElementMap_iSupMap (descSeq k) (descSeq_dir k) z

end Target

/-! ## Generic chain helpers -/

/-- A successor-increasing chain is increasing. -/
theorem chain_le_of_succ {β : Type*} {W : NeighborhoodSystem β} {a : ℕ → W.Element}
    (h : ∀ n, a n ≤ a (n + 1)) {i j : ℕ} (hij : i ≤ j) : a i ≤ a j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (h _)

/-- Directedness of a successor-increasing chain. -/
theorem succChainDir {β : Type*} {W : NeighborhoodSystem β} (a : ℕ → W.Element)
    (h : ∀ n, a n ≤ a (n + 1)) : ∀ i j, ∃ l, a i ≤ a l ∧ a j ≤ a l :=
  fun i j => ⟨max i j, chain_le_of_succ h (le_max_left i j), chain_le_of_succ h (le_max_right i j)⟩

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain is increasing element-wise. -/
theorem descSeqEltMono (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    ∀ n, (descSeq k n).toElementMap x ≤ (descSeq k (n + 1)).toElementMap x :=
  fun n => toElementMap_le_of_le (descSeq_mono_succ k n) x

/-- **The descent map as a directed union.** `h(x) = ⋃ₙ hₙ(x)`. -/
theorem descMap_eq (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    (descMap k).toElementMap x
      = iSupDirected (fun n => (descSeq k n).toElementMap x)
          (succChainDir _ (descSeqEltMono k x)) := by
  apply Element.ext
  intro Y
  rw [descMap_toElementMap, mem_iSupDirected]

/-- The continuity helper `k(a, ·) : E → E` as an approximable map. -/
def kHead (k : ApproximableMap (prod V E) E) (a : V.Element) :
    ApproximableMap E E :=
  k.comp (paired (constMap E a) (idMap E))

theorem kHead_apply (k : ApproximableMap (prod V E) E) (a : V.Element) (u : E.Element) :
    (kHead k a).toElementMap u = k.toElementMap (pair a u) := by
  rw [kHead, toElementMap_comp, toElementMap_paired, toElementMap_constMap, toElementMap_idMap]

/-! ## The fixed-point equation `h = k ∘ T(h) ∘ j` -/

/-- **The descent map is a fixed point** of `Op = k ∘ T(·) ∘ j`. -/
theorem descMap_fix (k : ApproximableMap (prod V E) E) : descMap k = descOp k (descMap k) := by
  apply ext_of_toElementMap
  intro z
  rw [descOp_apply, descMap_eq k (ofSeq (fun n => component z (n + 1))),
    ← kHead_apply k (component z 0), toElementMap_iSupDirected, descMap_eq k z]
  -- both sides are directed unions; compare the (reindexed) families term-wise
  apply Element.ext
  intro Y
  rw [mem_iSupDirected, mem_iSupDirected]
  have hstep : ∀ m, (kHead k (component z 0)).toElementMap
        ((descSeq k m).toElementMap (ofSeq (fun n => component z (n + 1))))
      = (descSeq k (m + 1)).toElementMap z := by
    intro m
    rw [kHead_apply, show descSeq k (m + 1) = descOp k (descSeq k m) from rfl, descOp_apply]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact ⟨0, by rw [hstep 0]; exact descSeqEltMono k z 0 _ hn⟩
    | succ m => exact ⟨m, by rw [hstep m]; exact hn⟩
  · rintro ⟨m, hm⟩
    rw [hstep m] at hm
    exact ⟨m + 1, hm⟩

/-! ## Strictness of the descent map -/

theorem descSeq_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    ∀ n, IsStrict (descSeq k n)
  | 0 => isStrict_constBot
  | (n + 1) => by
      have ih := descSeq_strict k hk n
      rw [isStrict_iff_apply_bot] at ih ⊢
      rw [show descSeq k (n + 1) = descOp k (descSeq k n) from rfl, descOp_apply]
      have htl : ofSeq (fun m => component (iterSys V).bot (m + 1)) = (iterSys V).bot := by
        have hconst : (fun m => component (iterSys V).bot (m + 1)) = (fun _ => V.bot) := by
          funext m; rw [component_bot]
        rw [hconst, ← iterBot_eq]
      rw [component_bot, htl, ih, pair_bot]
      exact isStrict_iff_apply_bot.mp hk

theorem descMap_strict (k : ApproximableMap (prod V E) E) (hk : IsStrict k) :
    IsStrict (descMap k) := by
  rw [isStrict_iff_apply_bot]
  apply Element.ext
  intro Y
  rw [mem_bot, descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hs := descSeq_strict k hk n
    rw [isStrict_iff_apply_bot] at hs
    rw [hs, mem_bot] at hn
    exact hn
  · rintro rfl
    have hs := descSeq_strict k hk 0
    rw [isStrict_iff_apply_bot] at hs
    exact ⟨0, by rw [hs]; exact E.bot.master_mem⟩

/-! ## The homomorphism square `h ∘ i = k ∘ T(h)` -/

/-- **Existence of the algebra homomorphism.** The descent map makes the square commute:
`descMap ∘ i = k ∘ T(descMap)` (using `j ∘ i = I` and the fixed-point equation). -/
theorem descMap_comm (k : ApproximableMap (prod V E) E) :
    (descMap k).comp (imap V) = k.comp (prodMap (idMap V) (descMap k)) := by
  conv_lhs => rw [descMap_fix k]
  show (k.comp ((prodMap (idMap V) (descMap k)).comp (jmap V))).comp (imap V)
     = k.comp (prodMap (idMap V) (descMap k))
  rw [comp_assoc, comp_assoc, jmap_comp_imap, comp_idMap]

end Target

/-! ## The truncation chain `ρₙ` and `⋃ₙ ρₙ = I`

The descent chain for the structure map `i` itself, `ρₙ = (descSeq i)ₙ : 𝒟^∞ → 𝒟^∞`, truncates a
sequence to its first `n` coordinates. Its supremum is the identity (`iSupRho_eq_id`), the key fact
behind uniqueness: every strict homomorphism is determined on the finite truncations. -/

/-- **The truncation formula** `ρₙ(⟨x₀,x₁,…⟩) = ⟨x₀,…,x_{n-1},⊥,⊥,…⟩`. -/
theorem rho_apply (n : ℕ) (z : (iterSys V).Element) :
    (descSeq (imap V) n).toElementMap z
      = ofSeq (fun i => if i < n then component z i else V.bot) := by
  induction n generalizing z with
  | zero =>
    show (constMap (iterSys V) (iterSys V).bot).toElementMap z = _
    rw [toElementMap_constMap, iterBot_eq]
    congr 1
  | succ n ih =>
    rw [show descSeq (imap V) (n + 1) = descOp (imap V) (descSeq (imap V) n) from rfl,
      descOp_apply, ih]
    simp only [imap]
    rw [toElementMap_ofIso, iterProdIso_symm_pair]
    congr 1
    funext j
    cases j with
    | zero =>
      show component z 0 = if (0 : ℕ) < n + 1 then component z 0 else V.bot
      rw [if_pos (Nat.zero_lt_succ n)]
    | succ k =>
      rw [consSeq_succ, component_ofSeq, component_ofSeq]
      show (if k < n then component z (k + 1) else V.bot)
         = if k + 1 < n + 1 then component z (k + 1) else V.bot
      by_cases h : k < n
      · rw [if_pos h, if_pos (Nat.succ_lt_succ h)]
      · rw [if_neg h, if_neg (fun hc => h (Nat.lt_of_succ_lt_succ hc))]

/-- **`⋃ₙ ρₙ = I`.** Every `z` is the directed union of its truncations: the cofinite-`Δ` structure
of `𝒟^∞` means each neighbourhood of `z` is already realised by a finite truncation. -/
theorem iSupRho_eq_id : descMap (imap V) = idMap (iterSys V) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_idMap]
  apply Element.ext
  intro Y
  rw [descMap_toElementMap]
  constructor
  · rintro ⟨n, hn⟩
    have hle : (descSeq (imap V) n).toElementMap z ≤ z := by
      rw [rho_apply]
      have hz : z = ofSeq (fun i => component z i) := (ofSeq_component z).symm
      conv_rhs => rw [hz]
      apply ofSeq_mono
      intro i
      show (if i < n then component z i else V.bot) ≤ component z i
      split
      · exact le_rfl
      · exact V.bot_le _
    exact hle Y hn
  · intro hzY
    have hY : (iterSys V).mem Y := z.sub hzY
    obtain ⟨N, hN⟩ := hY.2
    have hcomp : ∀ i, (component z i).mem (fiber Y i) := by
      have h := hzY
      rw [← ofSeq_component z] at h
      rw [mem_ofSeq] at h
      exact h.2
    refine ⟨N, ?_⟩
    rw [rho_apply, mem_ofSeq]
    refine ⟨hY, fun i => ?_⟩
    show (if i < N then component z i else V.bot).mem (fiber Y i)
    by_cases h : i < N
    · rw [if_pos h]; exact hcomp i
    · rw [if_neg h, hN i (not_lt.mp h)]; exact V.bot.master_mem

/-! ## Uniqueness of strict homomorphisms -/

section Uniq

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- The descent chain for any strict `g` starts at the constant `⊥`: `g ∘ ρ₀ = ⊥`. -/
theorem gcomp_rho_zero (g : ApproximableMap (iterSys V) E) (hg : IsStrict g) :
    g.comp (descSeq (imap V) 0) = constMap (iterSys V) E.bot := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_constMap,
    show descSeq (imap V) 0 = constMap (iterSys V) (iterSys V).bot from rfl,
    toElementMap_constMap, isStrict_iff_apply_bot.mp hg]

/-- **`g`-independence step.** If `g` is a homomorphism (`g ∘ i = k ∘ T(g)`) then
`g ∘ ρₙ₊₁ = k ∘ T(g ∘ ρₙ) ∘ j = Op_k(g ∘ ρₙ)`: the composite depends only on `g ∘ ρₙ`. -/
theorem gcomp_rho_succ (k : ApproximableMap (prod V E) E) (g : ApproximableMap (iterSys V) E)
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g)) (n : ℕ) :
    g.comp (descSeq (imap V) (n + 1)) = descOp k (g.comp (descSeq (imap V) n)) := by
  show g.comp ((imap V).comp ((prodMap (idMap V) (descSeq (imap V) n)).comp (jmap V)))
     = k.comp ((prodMap (idMap V) (g.comp (descSeq (imap V) n))).comp (jmap V))
  rw [← comp_assoc, hc, comp_assoc]
  congr 1
  rw [← comp_assoc, ← prodMap_comp, idMap_comp]

/-- **Uniqueness.** Any two strict homomorphisms `g, g' : 𝒟^∞ → E` into a `T`-algebra `(E,k)` are
equal. By `g`-independence they agree on every truncation (`g ∘ ρₙ = g' ∘ ρₙ`), and `⋃ₙ ρₙ = I`
forces `g = g'`. -/
theorem comm_unique (k : ApproximableMap (prod V E) E)
    {g g' : ApproximableMap (iterSys V) E} (hg : IsStrict g) (hg' : IsStrict g')
    (hc : g.comp (imap V) = k.comp (prodMap (idMap V) g))
    (hc' : g'.comp (imap V) = k.comp (prodMap (idMap V) g')) : g = g' := by
  have hindep : ∀ n, g.comp (descSeq (imap V) n) = g'.comp (descSeq (imap V) n) := by
    intro n
    induction n with
    | zero => rw [gcomp_rho_zero g hg, gcomp_rho_zero g' hg']
    | succ m ih => rw [gcomp_rho_succ k g hc m, gcomp_rho_succ k g' hc' m, ih]
  have key : g.comp (descMap (imap V)) = g'.comp (descMap (imap V)) := by
    apply ApproximableMap.ext
    intro X Z
    simp only [descMap, comp_rel]
    constructor
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg : (g.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [hindep i] at hg
      obtain ⟨Y', hXY', hYZ'⟩ := hg
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
    · rintro ⟨Y, ⟨i, hXY⟩, hYZ⟩
      have hg' : (g'.comp (descSeq (imap V) i)).rel X Z := ⟨Y, hXY, hYZ⟩
      rw [← hindep i] at hg'
      obtain ⟨Y', hXY', hYZ'⟩ := hg'
      exact ⟨Y', ⟨i, hXY'⟩, hYZ'⟩
  rw [iSupRho_eq_id] at key
  rwa [comp_idMap, comp_idMap] at key

end Uniq

/-! ## The endofunctor `T(X) = 𝒟 × X` and `𝒟^∞` as its initial algebra

We package the analysis into the bespoke category `StrictDomainObj` of `∅`-free domains and strict
maps (Exercise 6.17), exactly the setting in which `IsInitial` expresses Scott's universal property.
The fixed domain `𝒟` is an arbitrary `StrictDomainObj`. -/

/-- `T(f₀ × f₁)` is strict when both factors are: `(f₀ × f₁)(⊥,⊥) = (f₀ ⊥, f₁ ⊥) = (⊥,⊥)`. -/
theorem isStrict_prodMap {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {f₀ : ApproximableMap V₀ V₀'} {f₁ : ApproximableMap V₁ V₁'}
    (hf₀ : IsStrict f₀) (hf₁ : IsStrict f₁) : IsStrict (prodMap f₀ f₁) := by
  rw [isStrict_iff_apply_bot, show (prod V₀ V₁).bot = pair V₀.bot V₁.bot from pair_bot.symm,
    toElementMap_prodMap_pair, isStrict_iff_apply_bot.mp hf₀, isStrict_iff_apply_bot.mp hf₁]
  exact pair_bot

/-- The fixed domain `𝒟` times an object `X`, again an `∅`-free domain. -/
def prodObj (Dom X : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Dom.carrier ⊕ X.carrier
  sys := prod Dom.sys X.sys
  nonempty := prod_nonempty Dom.nonempty X.nonempty

/-- The morphism action `T(f) = id_𝒟 × f`, strict by `isStrict_prodMap`. -/
def prodMapHom (Dom : StrictDomainObj.{w}) {X Y : StrictDomainObj.{w}} (f : Category.Hom X Y) :
    Category.Hom (prodObj Dom X) (prodObj Dom Y) :=
  ⟨prodMap (idMap Dom.sys) f.1, isStrict_prodMap isStrict_idMap f.2⟩

/-- **The product endofunctor `T(X) = 𝒟 × X`** on `∅`-free domains and strict maps, for a fixed
domain `𝒟`. On objects `T(X) = 𝒟 × X`; on maps `T(f) = id_𝒟 × f`. -/
def prodFunctor (Dom : StrictDomainObj.{w}) : Endofunctor StrictDomainObj.{w} where
  obj := prodObj Dom
  map := prodMapHom Dom
  map_id X := Subtype.ext (by
    show prodMap (idMap Dom.sys) (idMap X.sys) = idMap (prod Dom.sys X.sys)
    exact prodMap_id)
  map_comp {X Y Z} g f := Subtype.ext (by
    show prodMap (idMap Dom.sys) (g.1.comp f.1)
       = (prodMap (idMap Dom.sys) g.1).comp (prodMap (idMap Dom.sys) f.1)
    have h := prodMap_comp (idMap Dom.sys) (idMap Dom.sys) g.1 f.1
    rw [idMap_comp] at h
    exact h)

/-- `𝒟^∞` (Exercise 3.16's `iterSys`) as an `∅`-free object. -/
def iterObj (Dom : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := ℕ × Dom.carrier
  sys := iterSys Dom.sys
  nonempty := iterSys_nonempty Dom.nonempty

/-- **`𝒟^∞` as a `T`-algebra**, `(𝒟^∞, i)` with `i : 𝒟 × 𝒟^∞ → 𝒟^∞` the "cons" iso (`imap`,
Exercise 3.16's `iterProdIso⁻¹`), strict by `isStrict_imap`. -/
def iterAlg (Dom : StrictDomainObj.{w}) : TAlgebra (prodFunctor Dom) where
  carrier := iterObj Dom
  str := ⟨imap Dom.sys, isStrict_imap⟩

/-- **The descent homomorphism `(𝒟^∞, i) → (E, k)`**: the strict map `descMap k` (existence half),
with the homomorphism square supplied by `descMap_comm`. -/
def descAlgHom (Dom : StrictDomainObj.{w}) (B : TAlgebra (prodFunctor Dom)) :
    AlgHom (iterAlg Dom) B where
  hom := ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩
  comm := by
    apply Subtype.ext
    show (descMap B.str.1).comp (imap Dom.sys)
       = B.str.1.comp (prodMap (idMap Dom.sys) (descMap B.str.1))
    exact descMap_comm B.str.1

/-- **Exercise 6.18 (initial-algebra half) — `𝒟^∞` is the initial `T`-algebra for `T(X) = 𝒟 × X`.**
For every `T`-algebra `(E, k)` the descent map `h(⟨x₀,x₁,…⟩) = k(x₀, k(x₁, …))` is the *unique*
strict homomorphism `𝒟^∞ → E`. Together with Exercise 3.16's `𝒟^∞ ≅ 𝒟 × 𝒟^∞` (the domain-equation
half), this exhibits `𝒟^∞` both as the canonical solution of the domain equation and as the initial
algebra (determined up to iso by Proposition 6.6). -/
def iterIsInitial (Dom : StrictDomainObj.{w}) : IsInitial (iterAlg Dom) where
  desc := descAlgHom Dom
  uniq B h := by
    obtain ⟨hom, comm⟩ := h
    have hcomm : hom.1.comp (imap Dom.sys)
        = B.str.1.comp (prodMap (idMap Dom.sys) hom.1) := congrArg Subtype.val comm
    have hg : hom.1 = descMap B.str.1 :=
      comm_unique B.str.1 hom.2 (descMap_strict B.str.1 B.str.2) hcomm (descMap_comm B.str.1)
    have hhom : hom = ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩ := Subtype.ext hg
    subst hhom
    rfl

end Exercise618

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Exercise623.lean -/

/-!
# Exercise 6.23 (Scott 1981, PRG-19, §6) — the syntactic domain of expressions

> **EXERCISE 6.23.** Construe the initial solution to
> `Exp ≅ N ⊕ ((Exp × Exp) + (Exp × Exp))`
> as a "syntactical domain" of expressions generated from infinitely many "variables" by means of two
> binary "operation symbols". Given an algebra `D` with two operations `u : D×D → D` and
> `v : D×D → D`, show how any strict map `s : N → D` determines a unique map `val(s) : Exp → D` that
> can be regarded as the "evaluation of an expression".

The right-hand functor is `T(X) = N ⊕ ((X×X) + (X×X))`, i.e. in the algebra `GExpr` of Exercise 6.21,
`Texp N = .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))`. Reading the structure map
`k : T(Exp) → Exp` of an algebra through the universal properties of `⊕`, `+`, `×`:

* the `⊕ N` summand gives a strict **variable map** `s : N → Exp` (the "infinitely many variables"
  are the tokens / points of `N`);
* the two `(Exp × Exp)` summands, combined by `+`, give two binary **operation symbols**
  `u, v : Exp × Exp → Exp`.

So an algebra of this functor is exactly *a domain `D` with a strict `s : N → D` and two binary
operations `u, v : D×D → D`*, and the unique homomorphism `val(s) : Exp → D` is Scott's "evaluation
of an expression": it sends a variable to its value under `s`, and an `u`/`v`-node to the `u`/`v` of
the values of its two subexpressions.

## This module (Phase 1 — the domain `Exp` itself)

Following Scott's standing restriction in Exercises 6.19–6.23 to `∅`-free systems over `{0,1}*` and
*strict* maps (`ScottSys`), and following the structure of **Theorem 6.14** (the initial solution is
the iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`), we build the concrete solution domain **for any rooted
`GExpr` functor** `T`:

* `gFix T = ⋃ₙ gFunⁿ({Λ})` — the token set (Exercise 6.20/6.21 fixed point `Γ = tok(T({Γ}))`);
* `gTower T n = Tⁿ({Γ})` — the iterated-functor tower of `∅`-free systems over `Str`;
* `gColim T = ⋃ₙ Tⁿ({Γ})` — the colimit system, with `gColim_obj_eq : T(gColim) = gColim` (the
  structure map is the **identity**, since the two systems are literally equal — no carrier transport
  is needed because `ScottSys` keeps the token type fixed at `Str`).

Instantiating at `Texp N` gives `Exp N := gColim (Texp N)` together with the domain-equation
**isomorphism** `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))` (`Exp_structure_eq`). The algebra decomposition
(`s`, `u`, `v`) and the unique evaluation homomorphism `val(s)` (initiality) are developed in later
phases.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the colimit is genuine data
built without `Classical.choice` (the generator `Γ` is the *explicit* Kleene union, not an
existential witness).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise619
open Scott1980.Neighborhood.Example62 Scott1980.Neighborhood.ExampleB Scott1980.Neighborhood.Exercise510

namespace Exercise619

/-! ## The generator `Γ = ⋃ₙ gFunⁿ({Λ})` (the Exercise 6.20/6.21 fixed point, as data) -/

/-- **The fixed-point token set `Γ = tok(T({Γ}))`**, as the explicit Kleene union `⋃ₙ gIter T n`
(no `Classical.choice`). -/
def gFix (T : GExpr) : Set Str := ⋃ n, gIter T n

theorem gFix_nil_mem (T : GExpr) : ([] : Str) ∈ gFix T :=
  Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem gFix_nonempty (T : GExpr) : (gFix T).Nonempty := ⟨[], gFix_nil_mem T⟩

/-- `Γ = tok(T({Γ}))` at the token level: `gFun T Γ = Γ`. -/
theorem gFix_fixed (T : GExpr) (hT : T.RootedConst) : gFun T (gFix T) = gFix T :=
  gFun_iter_fixed T hT

/-! ## The iterated-functor tower `Tⁿ({Γ})` -/

/-- **The one-point generator `{Γ}`** as an object of the category. -/
def gGen (T : GExpr) : ScottSys := singletonSys (gFix T) (gFix_nonempty T)

@[simp] theorem gGen_master (T : GExpr) : (gGen T).sys.master = gFix T := rfl

/-- **`{Γ} ◁ T({Γ})`** — Scott's hypothesis for Theorem 6.14, the base of the tower. (This is the
content of `gExists_singleton_subsystem`, here at the *explicit* generator `Γ = gFix T`.) -/
theorem gBase (T : GExpr) (hT : T.RootedConst) : (gGen T).sys ◁ (T.obj (gGen T)).sys := by
  have hmaster : (T.obj (gGen T)).sys.master = gFix T :=
    (gFun_eq_master T (gFix_nonempty T)).symm.trans (gFix_fixed T hT)
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have heq : X = (T.obj (gGen T)).sys.master := (hX : X = gFix T).trans hmaster.symm
    rw [heq]; exact (T.obj (gGen T)).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = gFix T
    rw [show X = gFix T from hX, show Y = gFix T from hY, Set.inter_self]

/-- **The tower `Tⁿ({Γ})`** of `∅`-free systems over `Str`: `T⁰({Γ}) = {Γ}`, `Tⁿ⁺¹({Γ}) =
T(Tⁿ({Γ}))`. -/
def gTower (T : GExpr) : ℕ → ScottSys
  | 0 => gGen T
  | n + 1 => T.obj (gTower T n)

@[simp] theorem gTower_zero (T : GExpr) : gTower T 0 = gGen T := rfl

@[simp] theorem gTower_succ (T : GExpr) (n : ℕ) : gTower T (n + 1) = T.obj (gTower T n) := rfl

/-- **The basic chain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`.** Base: `gBase`. Step: `T` is monotone on domains
(`obj_subsystem`). -/
theorem gChain (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys ◁ (gTower T (n + 1)).sys
  | 0 => gBase T hT
  | n + 1 => T.obj_subsystem (gChain T hT n)

/-- Every level of the tower has the same master `Δ = Γ`. -/
theorem gTower_master (T : GExpr) (hT : T.RootedConst) :
    ∀ n, (gTower T n).sys.master = gFix T
  | 0 => rfl
  | n + 1 => ((gChain T hT n).master_eq).symm.trans (gTower_master T hT n)

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem gTower_le (T : GExpr) (hT : T.RootedConst) {n m : ℕ} (h : n ≤ m) :
    (gTower T n).sys ◁ (gTower T m).sys := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (gChain T hT _)

/-! ## The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/

/-- **The colimit system `𝒟 = ⋃ₙ Tⁿ({Γ})`** as an `∅`-free system over `Str`. A set is a
neighbourhood exactly when it is a neighbourhood of some level; closure under consistent intersection
uses that the tower is a chain (any finite collection sits inside one level). -/
def gColim (T : GExpr) (hT : T.RootedConst) : ScottSys where
  sys :=
    { mem := fun X => ∃ n, (gTower T n).sys.mem X
      master := gFix T
      master_nonempty := (gTower T 0).sys.master_nonempty
      master_mem := ⟨0, (gTower T 0).sys.master_mem⟩
      inter_mem := by
        rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
        set N := max n (max m p) with hN
        have hXN : (gTower T N).sys.mem X := (gTower_le T hT (le_max_left n _)).sub hX
        have hYN : (gTower T N).sys.mem Y :=
          (gTower_le T hT ((le_max_left m p).trans (le_max_right n _))).sub hY
        have hZN : (gTower T N).sys.mem Z :=
          (gTower_le T hT ((le_max_right m p).trans (le_max_right n _))).sub hZ
        exact ⟨N, (gTower T N).sys.inter_mem hXN hYN hZN hsub⟩
      sub_master := by
        rintro X ⟨n, hX⟩
        rw [← gTower_master T hT n]
        exact (gTower T n).sys.sub_master hX }
  ne := by rintro X ⟨n, hX⟩; exact (gTower T n).ne X hX

@[simp] theorem mem_gColim (T : GExpr) (hT : T.RootedConst) {X : Set Str} :
    (gColim T hT).sys.mem X ↔ ∃ n, (gTower T n).sys.mem X := Iff.rfl

@[simp] theorem gColim_master (T : GExpr) (hT : T.RootedConst) :
    (gColim T hT).sys.master = gFix T := rfl

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem gTower_sub_colim (T : GExpr) (hT : T.RootedConst) (n : ℕ) :
    (gTower T n).sys ◁ (gColim T hT).sys where
  master_eq := by rw [gColim_master, gTower_master T hT]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (gTower T (max n m)).sys.mem (X ∩ Y) :=
      (gTower_le T hT (le_max_right n m)).sub hXY
    exact (gTower_le T hT (le_max_left n m)).inter_closed hX hY hN

/-! ## The structure isomorphism `T(𝒟) = 𝒟` -/

/-- Two objects of the category with the same underlying system are equal (the `∅`-freeness field is
a `Prop`). -/
theorem ScottSys.ext {A B : ScottSys} (h : A.sys = B.sys) : A = B := by
  cases A; cases B; cases h; rfl

/-- **`T(𝒟) = 𝒟` at the level of neighbourhood systems.** Membership: continuity on domains
(`obj_continuous`) along the directed tower turns `T(⋃ₙ Tⁿ({Γ}))` into `⋃ₙ Tⁿ⁺¹({Γ})`, which has the
same neighbourhoods as `⋃ₙ Tⁿ({Γ})` (the extra `n=0` level `T⁰({Γ})` is absorbed by the chain step).
Master: both are `Γ` (`gTower_master` through `obj_subsystem` of `Tⁿ({Γ}) ◁ 𝒟`). -/
theorem gColim_obj_sys_eq (T : GExpr) (hT : T.RootedConst) :
    (T.obj (gColim T hT)).sys = (gColim T hT).sys := by
  set ℱ : Set ScottSys := Set.range (gTower T) with hℱ
  have hne : ℱ.Nonempty := ⟨gTower T 0, 0, rfl⟩
  have hsub : ∀ D ∈ ℱ, D.sys ◁ (gColim T hT).sys := by
    rintro D ⟨n, rfl⟩; exact gTower_sub_colim T hT n
  have hdir : DirectedOn (fun a b => a.sys ◁ b.sys) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨gTower T (max n m), ⟨max n m, rfl⟩,
      gTower_le T hT (le_max_left n m), gTower_le T hT (le_max_right n m)⟩
  have hU : ∀ X, (gColim T hT).sys.mem X ↔ ∃ D ∈ ℱ, D.sys.mem X := by
    intro X; constructor
    · rintro ⟨n, hn⟩; exact ⟨gTower T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  apply NeighborhoodSystem.ext
  · intro W
    rw [T.obj_continuous hdir hne hsub hU W]
    constructor
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩
      -- `T(Tⁿ({Γ})) = Tⁿ⁺¹({Γ})`, a level of the colimit.
      exact ⟨n + 1, hn⟩
    · rintro ⟨n, hn⟩
      -- a colimit neighbourhood at level `n` is, after one chain step, at `T(Tⁿ({Γ}))`.
      exact ⟨gTower T n, ⟨n, rfl⟩, (gChain T hT n).sub hn⟩
  · -- masters: `(T 𝒟).master = (Tⁿ⁺¹({Γ})).master = Γ = 𝒟.master`, via `obj_subsystem` at `n=0`.
    have h := (T.obj_subsystem (gTower_sub_colim T hT 0)).master_eq
    rw [gColim_master]
    rw [show (T.obj (gTower T 0)) = gTower T 1 from rfl] at h
    rw [← h, gTower_master T hT]

/-- **The structure isomorphism `T(𝒟) ≅ 𝒟` is the identity** (the two objects are literally equal). -/
theorem gColim_obj_eq (T : GExpr) (hT : T.RootedConst) : T.obj (gColim T hT) = gColim T hT :=
  ScottSys.ext (gColim_obj_sys_eq T hT)

/-! ## The functor of Exercise 6.23 and the syntactic domain `Exp` -/

/-- **The functor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23, as a `GExpr` over the variable
domain `N`. The `⊕ N` carries the variables, and the two `(X×X)` summands (combined by `+`) carry the
two binary operation symbols. -/
def Texp (N : ScottSys) : GExpr :=
  .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))

/-- `Texp N` is rooted iff the variable domain `N` is (`Λ ∈ tok(N)`, automatic for the fixed-point
solutions of 6.19–6.22). -/
theorem Texp_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) : (Texp N).RootedConst :=
  ⟨hN, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **The syntactic domain of expressions** `Exp = ⋃ₙ Texpⁿ({Γ})`, the initial solution of
`Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`. -/
def Exp (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : ScottSys :=
  gColim (Texp N) (Texp_rooted hN)

/-- **The domain equation `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`**, realised as an equality of systems
(the structure map is the identity). This is the "construe the initial solution" half of
Exercise 6.23. -/
theorem Exp_structure_eq (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (Texp N).obj (Exp N hN) = Exp N hN :=
  gColim_obj_eq (Texp N) (Texp_rooted hN)

/-! ## Phase 2 — the strict-map category, the endofunctor `T`, and the algebra `Exp`

Following Scott (and Exercise 6.17's `StrictDomainObj`), but over the *fixed* token type `Str`: the
objects are `ScottSys` (∅-free systems over `Str`), the morphisms are **strict** approximable maps.
Because every object lives over `Str`, all carrier equalities are `rfl` and there is no `HEq`
transport (the obstruction that made the abstract Theorem 6.14 unusable). The functor `Texp N` then
becomes a genuine `Endofunctor` of this category, and the colimit `Exp` of Phase 1 — together with the
structure equality `T(Exp) = Exp` — is a `T`-algebra. -/

/-- **The category of `∅`-free domains over `Str` and strict maps.** Morphisms are strict approximable
maps (`StrictMap`); identities and associative composition are Theorem 2.5, with strictness preserved
by `isStrict_idMap`/`isStrict_comp`. The fixed carrier `Str` is what removes all the carrier-transport
`HEq` that burdens the abstract `Endofunctor DomainObj`. -/
instance : Category ScottSys where
  Hom A B := StrictMap A.sys B.sys
  id A := ⟨idMap A.sys, isStrict_idMap⟩
  comp g f := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (idMap_comp f.1)
  comp_id f := Subtype.ext (comp_idMap f.1)
  assoc h g f := Subtype.ext (comp_assoc h.1 g.1 f.1)

@[simp] theorem ScottSys.id_val (A : ScottSys) :
    (Category.id A : StrictMap A.sys A.sys).1 = idMap A.sys := rfl

@[simp] theorem ScottSys.comp_val {A B C : ScottSys} (g : Category.Hom B C) (f : Category.Hom A B) :
    ((g ⊚ f : StrictMap A.sys C.sys)).1 = g.1.comp f.1 := rfl

/-- The morphism action of `gFunctor T`: a strict `f` is sent to the strict map `T(f)`. (Typed via
`StrictMap`, which is defeq to the category's `Hom`; this avoids the class-projection that blocks the
anonymous `.1` on `Category.Hom`.) -/
def gFunctorMap (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    StrictMap (T.obj X).sys (T.obj Y).sys :=
  ⟨T.map f.1, T.map_isStrict f.1 f.2⟩

/-- **Every `GExpr` is an `Endofunctor` of the strict-map category.** On objects it is `GExpr.obj`;
on a strict map `f` it is the strict map `T(f)` (`GExpr.map_isStrict`). Functoriality is
`GExpr.map_id` and `GExpr.map_comp` (the latter needs `g` strict — automatic here, since every
morphism of this category is strict). -/
abbrev gFunctor (T : GExpr) : Endofunctor ScottSys where
  obj := T.obj
  map := gFunctorMap T
  map_id X := Subtype.ext (T.map_id X)
  map_comp {_ _ _} g f :=
    Subtype.ext (T.map_comp (f : StrictMap _ _).1 (g : StrictMap _ _).2)

@[simp] theorem gFunctor_obj (T : GExpr) (X : ScottSys) : (gFunctor T).obj X = T.obj X := rfl

@[simp] theorem gFunctorMap_val (T : GExpr) {X Y : ScottSys} (f : StrictMap X.sys Y.sys) :
    (gFunctorMap T f).1 = T.map f.1 := rfl

/-- **The endofunctor `T(X) = N ⊕ ((X×X) + (X×X))`** of Exercise 6.23. -/
abbrev TexpF (N : ScottSys) : Endofunctor ScottSys := gFunctor (Texp N)

/-- The identity isomorphism in any category induced by an object equality. -/
def isoOfObjEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨Category.id X, Category.id X, Category.id_comp _, Category.id_comp _⟩

/-- **The structure isomorphism `T(Exp) ≅ Exp`.** Since Phase 1 proved `T(Exp) = Exp` as objects
(`Exp_structure_eq`), this is the identity isomorphism. -/
def ExpIso (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    Iso ((TexpF N).obj (Exp N hN)) (Exp N hN) :=
  isoOfObjEq (Exp_structure_eq N hN)

/-- **`Exp` as a `T`-algebra** with structure map the isomorphism `T(Exp) ≅ Exp` (the identity, since
`T(Exp) = Exp`). This realises Scott's "construe the initial solution as a syntactic domain of
expressions": `Exp` is an algebra of `T(X) = N ⊕ ((X×X)+(X×X))`. -/
abbrev ExpAlg (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : TAlgebra (TexpF N) where
  carrier := Exp N hN
  str := (ExpIso N hN).hom

/-! ## Phase 3 — the evaluation homomorphism `val(s)` (existence)

Given any algebra `B = (D, k)` of `T(X) = N ⊕ ((X×X)+(X×X))` — i.e. a domain `D` carrying (through the
universal properties of `⊕`,`+`,`×`) a strict variable map `s : N → D` and two binary operations
`u, v : D×D → D` — we build a `T`-algebra homomorphism `val : Exp → D`. This is Scott's *"evaluation
of an expression"*.

Since Phase 1's structure map `i : T(Exp) → Exp` is the **identity** (`Exp_structure_eq`), the
homomorphism equation `val ∘ i = k ∘ T(val)` is the fixed-point equation `val = k ∘ T(val) ∘ j`
(`j = i⁻¹`). We solve it directly by the Kleene iteration `valₙ` (`val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`) and take `val = ⋃ₙ valₙ`. The fixed-point property uses *continuity on
maps* (`GExpr.map_continuous`: `T(⋃ valₙ) = ⋃ T(valₙ)`); no projection machinery is needed for
existence. (Uniqueness — initiality — is the remaining Phase 4.) -/

/-- The structure map of an algebra `B`, as a raw approximable map (its strictness is `algStr_strict`).
The ascription to `StrictMap` forces the categorical `Hom` to its underlying subtype. -/
def algStr (B : TAlgebra (TexpF N)) :
    ApproximableMap ((TexpF N).obj B.carrier).sys B.carrier.sys :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).1

theorem algStr_strict (B : TAlgebra (TexpF N)) : IsStrict (algStr B) :=
  (B.str : StrictMap ((TexpF N).obj B.carrier).sys B.carrier.sys).2

/-- The inverse `j = i⁻¹ : Exp → T(Exp)` of the structure isomorphism, as a raw map. -/
def expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).1

theorem expInv_strict (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) : IsStrict (expInv N hN) :=
  ((ExpIso N hN).inv : StrictMap (Exp N hN).sys ((TexpF N).obj (Exp N hN)).sys).2

/-- The structure map `i : T(Exp) → Exp` as a raw map (the identity, since `T(Exp) = Exp`). -/
def expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ApproximableMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys :=
  ((ExpIso N hN).hom : StrictMap ((TexpF N).obj (Exp N hN)).sys (Exp N hN).sys).1

/-- `j ∘ i = I_{T(Exp)}` at the raw level (from the iso's `hom_inv_id`). -/
theorem expInv_comp_expHom (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expInv N hN).comp (expHom N hN) = idMap ((TexpF N).obj (Exp N hN)).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).hom_inv_id
  exact h

/-- `i ∘ j = I_Exp` at the raw level (from the iso's `inv_hom_id`). -/
theorem expHom_comp_expInv (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    (expHom N hN).comp (expInv N hN) = idMap (Exp N hN).sys := by
  have h := congrArg (Subtype.val) (ExpIso N hN).inv_hom_id
  exact h

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- **The Kleene iterates `valₙ : Exp → D`** of the operator `λh. k ∘ T(h) ∘ j`. `val₀ = ⊥`,
`valₙ₊₁ = k ∘ T(valₙ) ∘ j`. -/
def descRel : ℕ → ApproximableMap (Exp N hN).sys B.carrier.sys
  | 0 => constMap (Exp N hN).sys B.carrier.sys.bot
  | n + 1 => (algStr B).comp (((Texp N).map (descRel n)).comp (expInv N hN))

@[simp] theorem descRel_succ (n : ℕ) :
    descRel hN B (n + 1) = (algStr B).comp (((Texp N).map (descRel hN B n)).comp (expInv N hN)) :=
  rfl

/-- Every iterate is strict. -/
theorem descRel_isStrict : ∀ n, IsStrict (descRel hN B n)
  | 0 => isStrict_constBot
  | n + 1 => by
      rw [descRel_succ]
      exact isStrict_comp (algStr_strict B)
        (isStrict_comp ((Texp N).map_isStrict _ (descRel_isStrict n)) (expInv_strict N hN))

/-- The constant `⊥` map is below every approximable map (it relates each domain neighbourhood only
to the codomain master, which every map produces by monotonicity from `master_rel`). -/
theorem constBot_le {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (g : ApproximableMap V₀ V₁) : constMap V₀ V₁.bot ≤ g := by
  intro X Y hr
  obtain ⟨hX, hY⟩ := hr
  rw [NeighborhoodSystem.mem_bot] at hY
  subst hY
  exact g.mono g.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

/-- The iterates increase: `valₙ ≤ valₙ₊₁`. -/
theorem descRel_le_succ : ∀ n, descRel hN B n ≤ descRel hN B (n + 1)
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, descRel_succ]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_succ n)) le_rfl)

/-- The iterates form a `≤`-chain. -/
theorem descRel_mono {i j : ℕ} (h : i ≤ j) : descRel hN B i ≤ descRel hN B j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (descRel_le_succ hN B _)

/-- Directedness witness for the union (any two iterates are dominated by the later one). -/
theorem descDir (i j : ℕ) : ∃ k, (∀ X Y, (descRel hN B i).rel X Y → (descRel hN B k).rel X Y) ∧
    (∀ X Y, (descRel hN B j).rel X Y → (descRel hN B k).rel X Y) :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

/-- **The evaluation map `val = ⋃ₙ valₙ`** as an approximable map. -/
def descMap : ApproximableMap (Exp N hN).sys B.carrier.sys :=
  iSupMap (descRel hN B) (descDir hN B)

theorem descMap_rel {A E : Set Str} :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

/-- `val` is strict (a union of strict maps). -/
theorem descMap_isStrict : IsStrict (descMap hN B) := by
  rintro Y ⟨n, hn⟩
  exact descRel_isStrict hN B n hn

/-- Directedness of the iterates in `≤`-form (for `map_continuous`). -/
theorem descDirLe (i j : ℕ) :
    ∃ k, descRel hN B i ≤ descRel hN B k ∧ descRel hN B j ≤ descRel hN B k :=
  ⟨max i j, descRel_mono hN B (le_max_left i j), descRel_mono hN B (le_max_right i j)⟩

/-- `val` is the relational union of the iterates (the hypothesis for `map_continuous`). -/
theorem descMap_is_sup (A E : Set Str) :
    (descMap hN B).rel A E ↔ ∃ n, (descRel hN B n).rel A E := Iff.rfl

/-- **The fixed-point equation `val = k ∘ T(val) ∘ j`.** Forward: an iterate `valₙ` is, after the
recursion, `k ∘ T(valₙ₋₁) ∘ j`, and `T(valₙ₋₁) ⊆ T(val)` by continuity on maps. Backward: a witness
factoring through `T(valₙ)` lands in `valₙ₊₁`. -/
theorem descMap_fix :
    descMap hN B = (algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN)) := by
  have hmc : ∀ Y C, ((Texp N).map (descMap hN B)).rel Y C
      ↔ ∃ n, ((Texp N).map (descRel hN B n)).rel Y C :=
    fun Y C => (Texp N).map_continuous (descRel hN B) (descMap hN B) (descDirLe hN B)
      (descMap_is_sup hN B) Y C
  apply ApproximableMap.ext
  intro A E
  rw [comp_rel]
  constructor
  · rintro ⟨n, hn⟩
    have hn1 : (descRel hN B (n + 1)).rel A E := descRel_le_succ hN B n A E hn
    rw [descRel_succ, comp_rel] at hn1
    obtain ⟨C, hAC, hCE⟩ := hn1
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    exact ⟨C, ⟨Y, hAY, (hmc Y C).mpr ⟨n, hYC⟩⟩, hCE⟩
  · rintro ⟨C, hAC, hCE⟩
    rw [comp_rel] at hAC
    obtain ⟨Y, hAY, hYC⟩ := hAC
    obtain ⟨n, hn⟩ := (hmc Y C).mp hYC
    refine ⟨n + 1, ?_⟩
    rw [descRel_succ, comp_rel]
    exact ⟨C, by rw [comp_rel]; exact ⟨Y, hAY, hn⟩, hCE⟩

/-- **The homomorphism square `val ∘ i = k ∘ T(val)`** at the raw level (conjugating the fixed-point
equation by `i`, using `j ∘ i = I`). -/
theorem descComm :
    (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B)) := by
  calc (descMap hN B).comp (expHom N hN)
      = ((algStr B).comp (((Texp N).map (descMap hN B)).comp (expInv N hN))).comp (expHom N hN) := by
        rw [← descMap_fix]
    _ = (algStr B).comp ((((Texp N).map (descMap hN B)).comp (expInv N hN)).comp (expHom N hN)) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp ((expInv N hN).comp (expHom N hN))) := by
        rw [comp_assoc]
    _ = (algStr B).comp (((Texp N).map (descMap hN B)).comp (idMap _)) := by
        rw [expInv_comp_expHom]
    _ = (algStr B).comp ((Texp N).map (descMap hN B)) := by rw [comp_idMap]

/-- **The evaluation homomorphism `val(s) : Exp → D`** as a `T`-algebra homomorphism — Scott's
existence of the evaluation map. -/
def descAlgHom : AlgHom (ExpAlg N hN) B where
  hom := ⟨descMap hN B, descMap_isStrict hN B⟩
  comm := by
    apply Subtype.ext
    show (descMap hN B).comp (expHom N hN) = (algStr B).comp ((Texp N).map (descMap hN B))
    exact descComm hN B

/-- **Every homomorphism `g : Exp → D` is a fixed point** of the operator `λh. k ∘ T(h) ∘ j`. This is
the homomorphism square `g ∘ i = k ∘ T(g)` (`g.comm`) rearranged by `i ∘ j = I`. -/
theorem algHom_fix (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1 = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1
      = (g.hom.1).comp (idMap (Exp N hN).sys) := (comp_idMap _).symm
    _ = (g.hom.1).comp ((expHom N hN).comp (expInv N hN)) := by rw [expHom_comp_expInv]
    _ = ((g.hom.1).comp (expHom N hN)).comp (expInv N hN) := (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp (expInv N hN) :=
          congrArg (fun m => m.comp (expInv N hN)) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp (expInv N hN)) := comp_assoc _ _ _

/-- **`descAlgHom` is the least homomorphism**: `val ≤ g` for every homomorphism `g : Exp → D`. The
Kleene iterates `valₙ` lie below any fixed point `g` (induction: `val₀ = ⊥ ≤ g`, and the operator is
monotone with `g` its own fixed point), so their union `val` does too. This is the easy half of
initiality; the matching `g ≤ val` (so `g = val`) is the projection-chain argument of Phase 4. -/
theorem descRel_le_algHom (g : AlgHom (ExpAlg N hN) B) : ∀ n, descRel hN B n ≤ g.hom.1
  | 0 => constBot_le _
  | n + 1 => by
      rw [descRel_succ, algHom_fix hN B g]
      exact comp_mono_gen le_rfl
        (comp_mono_gen ((Texp N).map_mono (descRel_le_algHom g n)) le_rfl)

theorem descMap_le_algHom (g : AlgHom (ExpAlg N hN) B) : descMap hN B ≤ g.hom.1 := by
  intro X Y hr
  obtain ⟨n, hn⟩ := hr
  exact descRel_le_algHom hN B g n X Y hn

end Existence

/-! ## Phase 4 — uniqueness of `val(s)` and initiality of `Exp`

Scott proves homomorphisms out of the iterated colimit are unique by showing they are *determined on
the finite elements*: the projection chain `ρₙ = iₙ ∘ jₙ` (Proposition 6.12's pair for
`Texpⁿ({Γ}) ◁ Exp`) satisfies `T(ρₙ) = ρₙ₊₁` and `⋃ₙ ρₙ = I_Exp`, so any homomorphism `g` equals
`⋃ₙ g ∘ ρₙ`, a sequence that is forced by the recursion (independent of `g`). The crux is the
*concrete* "monotone on domains" content (Definition 6.13): the functor `Texp` carries the canonical
6.12 projection pair of `D ◁ E` to that of `T(D) ◁ T(E)` — here a genuine **equality** of maps over
`Str` (no `HEq` carrier transport, the whole point of staying in `ScottSys`).

This section establishes that crux as `GExpr.map_inj`/`GExpr.map_proj` (by induction over the six
functor constructors), then mirrors Theorem 6.14's uniqueness argument concretely. -/

/-! ### Proposition 6.12 helpers: the projection pair is strict, and trivial on `D ◁ D` -/

/-- The injection `i : D → E` of a subsystem is **strict**: `i` sends `Δ_D` only to `Δ_E`. -/
theorem Subsystem.inj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.inj := by
  intro Y hrel
  rw [Subsystem.inj_rel] at hrel
  obtain ⟨_, hYE, hsub⟩ := hrel
  exact Set.Subset.antisymm (E.sub_master hYE) (by rw [← h.master_eq]; exact hsub)

/-- The projection `j : E → D` of a subsystem is **strict**. -/
theorem Subsystem.proj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.proj := by
  intro X hrel
  rw [Subsystem.proj_rel] at hrel
  obtain ⟨_, hXD, hsub⟩ := hrel
  exact Set.Subset.antisymm (D.sub_master hXD) (by rw [h.master_eq]; exact hsub)

/-- On `D ◁ D` (e.g. `Subsystem.refl`), the injection is the identity (both relations are
`X ∈ D ∧ Y ∈ D ∧ X ⊆ Y`). -/
theorem Subsystem.self_inj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.inj_rel, idMap_rel]

/-- On `D ◁ D`, the projection is the identity. -/
theorem Subsystem.self_proj {α : Type*} {D : NeighborhoodSystem α} (h : D ◁ D) :
    h.proj = idMap D := by
  apply ApproximableMap.ext
  intro X Y
  rw [Subsystem.proj_rel, idMap_rel]

/-! ### The functor carries projection pairs: the token-level lemmas -/

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Sum carries the injection.** `(i₀ + i₁) = i` for the sum subsystem: both relate `W ↦ W'` iff
`W ∈ 𝒟₀+𝒟₁`, `W' ∈ ℰ₀+ℰ₁`, `W ⊆ W'`. -/
theorem sumMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.inj h1.inj = (sumTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.sum A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (B₀.sum B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

/-- **Sum carries the projection.** -/
theorem sumMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.proj h1.proj = (sumTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.sum B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (A₀.sum A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

/-- **Product carries the injection.** -/
theorem prodMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.inj h1.inj = (prodTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

/-- **Product carries the projection.** -/
theorem prodMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.proj h1.proj = (prodTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

/-- **Coalesced sum carries the injection.** -/
theorem oplusMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.inj h1.inj = (oplusTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.oplus A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (B₀.oplus B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

/-- **Coalesced sum carries the projection.** -/
theorem oplusMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    oplusMapTok h0.proj h1.proj = (oplusTok_subsystem h0 h1).proj := by
  have hsubM : ∀ {W : Set Str}, (B₀.oplus B₁).sys.mem W → W ⊆ sumTokMaster A₀.sys A₁.sys := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · exact (show sumTokMaster B₀.sys B₁.sys = sumTokMaster A₀.sys A₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact (embBit_subset.mpr (by rw [h0.master_eq]; exact B₀.sys.sub_master hX)).trans
        (embF_subset_sumTokMaster A₀.sys.master_mem)
    · exact (embBit_subset.mpr (by rw [h1.master_eq]; exact B₁.sys.sub_master hY)).trans
        (embT_subset_sumTokMaster A₁.sys.master_mem)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXs⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hYs⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩), Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩),
        embBit_subset.mpr hXs⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩), Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩),
        embBit_subset.mpr hYs⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (B₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

/-- **Smash product carries the injection.** -/
theorem otimesMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.inj h1.inj = (otimesTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (B₀.otimes B₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd A₀.sys.master A₁.sys.master
            = prodTokNbhd B₀.sys.master B₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨B₀.sys.sub_master (h0.sub hP),
          B₁.sys.sub_master (h1.sub hQ)⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (B₀.sys.sub_master hX')
          (by rw [← h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-- **Smash product carries the projection.** -/
theorem otimesMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.proj h1.proj = (otimesTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (A₀.otimes A₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd B₀.sys.master B₁.sys.master
            = prodTokNbhd A₀.sys.master A₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨by rw [h0.master_eq]; exact B₀.sys.sub_master hP,
          by rw [h1.master_eq]; exact B₁.sys.sub_master hQ⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX')
          (by rw [h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

/-! ### The crux (Definition 6.13, concrete): `T` carries the 6.12 projection pair

This is the *monotone on domains* content of Definition 6.13, but here a genuine **equality** of maps
over the single token type `Str` (no `HEq` carrier transport): the functor `T = GExpr` sends the
injection/projection of `D ◁ E` to the injection/projection of `T(D) ◁ T(E)`. Proved by induction
over the six constructors using the token-level lemmas just established. -/

/-- **`T(i) = i'`** — the functor carries the injection of `D ◁ E` to that of `T(D) ◁ T(E)`. -/
theorem GExpr.map_inj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.inj = (T.obj_subsystem h).inj
  | .const D, _, _, _ => (Subsystem.self_inj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.inj) (b.map h.inj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, sumMapTok_inj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.inj) (b.map h.inj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, prodMapTok_inj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.inj) (b.map h.inj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, oplusMapTok_inj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.inj) (b.map h.inj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).inj
      rw [a.map_inj h, b.map_inj h, otimesMapTok_inj]

/-- **`T(j) = j'`** — the functor carries the projection of `D ◁ E` to that of `T(D) ◁ T(E)`. -/
theorem GExpr.map_proj : (T : GExpr) → {X Y : ScottSys} → (h : X.sys ◁ Y.sys) →
    T.map h.proj = (T.obj_subsystem h).proj
  | .const D, _, _, _ => (Subsystem.self_proj (Subsystem.refl D.sys)).symm
  | .var, _, _, _ => rfl
  | .sum a b, _, _, h => by
      show sumMapTok (a.map h.proj) (b.map h.proj)
          = (sumTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, sumMapTok_proj]
  | .prod a b, _, _, h => by
      show prodMapTok (a.map h.proj) (b.map h.proj)
          = (prodTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, prodMapTok_proj]
  | .oplus a b, _, _, h => by
      show oplusMapTok (a.map h.proj) (b.map h.proj)
          = (oplusTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, oplusMapTok_proj]
  | .otimes a b, _, _, h => by
      show otimesMapTok (a.map h.proj) (b.map h.proj)
          = (otimesTok_subsystem (a.obj_subsystem h) (b.obj_subsystem h)).proj
      rw [a.map_proj h, b.map_proj h, otimesMapTok_proj]

/-! ### The identity structure isomorphism, relationally -/

/-- The forward map of the identity iso `isoOfObjEq e` is the inclusion `X ↪ Y` (= `idMap` across the
object equality `e`). -/
theorem isoOfObjEq_hom_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).hom).1.rel A E ↔ X.sys.mem A ∧ Y.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

/-- The inverse map of the identity iso `isoOfObjEq e`. -/
theorem isoOfObjEq_inv_rel {X Y : ScottSys} (e : X = Y) {A E : Set Str} :
    ((isoOfObjEq e).inv).1.rel A E ↔ Y.sys.mem A ∧ X.sys.mem E ∧ A ⊆ E := by
  cases e; exact idMap_rel

/-- **Relational description of the structure map `i = expHom`** (the identity `T(Exp) = Exp`). -/
theorem expHom_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expHom N hN).rel A E ↔
      ((Texp N).obj (Exp N hN)).sys.mem A ∧ (Exp N hN).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_hom_rel (Exp_structure_eq N hN)

/-- **Relational description of the inverse structure map `j = expInv`**. -/
theorem expInv_rel {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) {A E : Set Str} :
    (expInv N hN).rel A E ↔
      (Exp N hN).sys.mem A ∧ ((Texp N).obj (Exp N hN)).sys.mem E ∧ A ⊆ E :=
  isoOfObjEq_inv_rel (Exp_structure_eq N hN)

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_Exp` -/

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- The subdomain `Texpⁿ({Γ}) ◁ Exp` (Proposition 6.12's pair lives here). -/
theorem expSub (n : ℕ) : (gTower (Texp N) n).sys ◁ (Exp N hN).sys :=
  gTower_sub_colim (Texp N) (Texp_rooted hN) n

/-- **`ρₙ = iₙ ∘ jₙ : Exp → Exp`**, the retraction onto `Texpⁿ({Γ})`. -/
def rho (n : ℕ) : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  (expSub hN n).inj.comp (expSub hN n).proj

/-- Scott's relational description `A ρₙ E ↔ ∃ z ∈ Texpⁿ({Γ}), A ⊆ z ⊆ E`. -/
theorem rho_rel (n : ℕ) {A E : Set Str} :
    (rho hN n).rel A E ↔ (Exp N hN).sys.mem A ∧ (Exp N hN).sys.mem E ∧
      ∃ z, (gTower (Texp N) n).sys.mem z ∧ A ⊆ z ∧ z ⊆ E := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, hproj, hinj⟩
    rw [Subsystem.proj_rel] at hproj
    rw [Subsystem.inj_rel] at hinj
    obtain ⟨hcA, hTz, hAz⟩ := hproj
    obtain ⟨_, hcE, hzE⟩ := hinj
    exact ⟨hcA, hcE, z, hTz, hAz, hzE⟩
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨z, by rw [Subsystem.proj_rel]; exact ⟨hcA, hTz, hAz⟩,
      by rw [Subsystem.inj_rel]; exact ⟨hTz, hcE, hzE⟩⟩

/-- `ρₙ ⊆ ρₘ` for `n ≤ m`. -/
theorem rho_mono {n m : ℕ} (h : n ≤ m) {A E : Set Str} (hr : (rho hN n).rel A E) :
    (rho hN m).rel A E := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcA, hcE, z, hTz, hAz, hzE⟩ := hr
  exact ⟨hcA, hcE, z, (gTower_le (Texp N) (Texp_rooted hN) h).sub hTz, hAz, hzE⟩

/-- The pointwise union `⋃ₙ ρₙ`. -/
def iSupRho : ApproximableMap (Exp N hN).sys (Exp N hN).sys :=
  iSupMap (rho hN) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono hN (le_max_left i j) h,
    fun _ _ h => rho_mono hN (le_max_right i j) h⟩)

/-- **`⋃ₙ ρₙ = I_Exp`** (Scott's key identity). -/
theorem iSupRho_eq_id : iSupRho hN = idMap (Exp N hN).sys := by
  apply ApproximableMap.ext
  intro A E
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcA, hcE, z, _, hAz, hzE⟩ := hr
    exact ⟨hcA, hcE, hAz.trans hzE⟩
  · rintro ⟨hcA, hcE, hAE⟩
    obtain ⟨n, hA⟩ := hcA
    exact ⟨n, (rho_rel hN n).mpr ⟨⟨n, hA⟩, hcE, A, hA, subset_rfl, hAE⟩⟩

/-- **`ρ₀ = ⊥`** (the generator `{Γ}` is one-point): `ρ₀` relates `A` only to the master. -/
theorem rho_zero_rel {A E : Set Str} :
    (rho hN 0).rel A E ↔ (Exp N hN).sys.mem A ∧ E = (Exp N hN).sys.master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcA, hcE, z, hz, _, hzE⟩
    have hzm : z = (Exp N hN).sys.master :=
      (hz : z = gFix (Texp N)).trans (gColim_master (Texp N) (Texp_rooted hN)).symm
    subst hzm
    exact ⟨hcA, Set.Subset.antisymm ((Exp N hN).sys.sub_master hcE) hzE⟩
  · rintro ⟨hcA, rfl⟩
    exact ⟨hcA, (Exp N hN).sys.master_mem, (Exp N hN).sys.master,
      gColim_master (Texp N) (Texp_rooted hN), (Exp N hN).sys.sub_master hcA, subset_rfl⟩

/-! ### The crux equation `ρₙ₊₁ = i ∘ T(ρₙ) ∘ j` -/

/-- `T(ρₙ) = T(iₙ) ∘ T(jₙ) = i'ₙ ∘ j'ₙ`, the projection pair of `T(Texpⁿ{Γ}) ◁ T(Exp)`. -/
theorem map_rho_eq (n : ℕ) :
    (Texp N).map (rho hN n)
      = ((Texp N).obj_subsystem (expSub hN n)).inj.comp
        ((Texp N).obj_subsystem (expSub hN n)).proj := by
  unfold rho
  rw [(Texp N).map_comp (expSub hN n).proj (Subsystem.inj_isStrict (expSub hN n)),
      (Texp N).map_inj, (Texp N).map_proj]

/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). -/
theorem key_rho (n : ℕ) :
    rho hN (n + 1)
      = (expHom N hN).comp (((Texp N).map (rho hN n)).comp (expInv N hN)) := by
  have hsyseq : ((Texp N).obj (Exp N hN)).sys = (Exp N hN).sys :=
    gColim_obj_sys_eq (Texp N) (Texp_rooted hN)
  apply ApproximableMap.ext
  intro A E
  rw [map_rho_eq]
  simp only [comp_rel, rho_rel, expInv_rel, expHom_rel, Subsystem.proj_rel,
    Subsystem.inj_rel, hsyseq]
  constructor
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨E, ⟨A, ⟨hcA, hcA, subset_rfl⟩, z, ⟨hcA, hTz, hAz⟩, hTz, hcE, hzE⟩,
      hcE, hcE, subset_rfl⟩
  · rintro ⟨Y, ⟨C, ⟨hcA, _, hAC⟩, z, ⟨_, hTz, hCz⟩, _, _, hzY⟩, _, hcE, hYE⟩
    exact ⟨hcA, hcE, z, hTz, hAC.trans hCz, hzY.trans hYE⟩

/-! ### `g`-independence of `g ∘ ρₙ` and uniqueness -/

variable (B : TAlgebra (TexpF N))

/-- The base of the recursion: `g ∘ ρ₀ = ⊥ = val₀`, independent of `g`. -/
theorem gcomp_rho_zero (g : AlgHom (ExpAlg N hN) B) :
    g.hom.1.comp (rho hN 0) = descRel hN B 0 := by
  apply ApproximableMap.ext
  intro A Z
  rw [comp_rel]
  constructor
  · rintro ⟨E, hrho, hg⟩
    rw [rho_zero_rel] at hrho
    obtain ⟨hcA, rfl⟩ := hrho
    have hZ : Z = B.carrier.sys.master := g.hom.2 hg
    exact ⟨hcA, by rw [NeighborhoodSystem.mem_bot]; exact hZ⟩
  · rintro ⟨hcA, hZ⟩
    rw [NeighborhoodSystem.mem_bot] at hZ
    subst hZ
    exact ⟨(Exp N hN).sys.master, (rho_zero_rel hN).mpr ⟨hcA, rfl⟩, g.hom.1.master_rel⟩

/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`** (`key_rho` + the homomorphism square). -/
theorem gcomp_rho_succ (g : AlgHom (ExpAlg N hN) B) (n : ℕ) :
    g.hom.1.comp (rho hN (n + 1))
      = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) := by
  have hcomm : (g.hom.1).comp (expHom N hN) = (algStr B).comp ((Texp N).map g.hom.1) :=
    congrArg Subtype.val g.comm
  calc g.hom.1.comp (rho hN (n + 1))
      = g.hom.1.comp ((expHom N hN).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := by rw [key_rho]
    _ = (g.hom.1.comp (expHom N hN)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        (comp_assoc _ _ _).symm
    _ = ((algStr B).comp ((Texp N).map g.hom.1)).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN)) :=
        congrArg (fun m => m.comp (((Texp N).map (rho hN n)).comp (expInv N hN))) hcomm
    _ = (algStr B).comp (((Texp N).map g.hom.1).comp
          (((Texp N).map (rho hN n)).comp (expInv N hN))) := comp_assoc _ _ _
    _ = (algStr B).comp ((((Texp N).map g.hom.1).comp ((Texp N).map (rho hN n))).comp
          (expInv N hN)) :=
        congrArg ((algStr B).comp ·)
          (comp_assoc ((Texp N).map g.hom.1) ((Texp N).map (rho hN n)) (expInv N hN)).symm
    _ = (algStr B).comp (((Texp N).map (g.hom.1.comp (rho hN n))).comp (expInv N hN)) :=
        congrArg (fun m => (algStr B).comp (m.comp (expInv N hN)))
          ((Texp N).map_comp (rho hN n) g.hom.2).symm

/-- **`g ∘ ρₙ = val₀ₙ`**: every homomorphism `g` agrees with the canonical Kleene iterate after the
`n`-th projection — the sequence is forced by the recursion, independent of `g`. -/
theorem gcomp_rho_eq (g : AlgHom (ExpAlg N hN) B) :
    ∀ n, g.hom.1.comp (rho hN n) = descRel hN B n
  | 0 => gcomp_rho_zero hN B g
  | n + 1 => by rw [gcomp_rho_succ hN B g n, gcomp_rho_eq g n, ← descRel_succ]

/-- **The underlying map of any homomorphism `g : Exp → D` is `val = descMap`.** Hence `descAlgHom`
is the *unique* homomorphism. -/
theorem descMap_eq_algHom (g : AlgHom (ExpAlg N hN) B) : g.hom.1 = descMap hN B := by
  have hcomp : g.hom.1.comp (iSupRho hN) = descMap hN B := by
    apply ApproximableMap.ext
    intro A E
    rw [comp_rel, descMap_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hg⟩
      refine ⟨n, ?_⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel]
      exact ⟨Y, hrho, hg⟩
    · rintro ⟨n, hn⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel] at hn
      obtain ⟨Y, hrho, hg⟩ := hn
      exact ⟨Y, ⟨n, hrho⟩, hg⟩
  calc g.hom.1 = g.hom.1.comp (iSupRho hN) := by
        rw [iSupRho_eq_id hN]; exact (comp_idMap g.hom.1).symm
    _ = descMap hN B := hcomp

/-- Two algebra homomorphisms with equal underlying maps are equal. -/
theorem algHom_ext {A C : TAlgebra (TexpF N)} {g g' : AlgHom A C} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

/-- **Exercise 6.23 (Scott 1981, PRG-19) — `Exp` is the initial `T`-algebra.** For every algebra
`B = (D, s, u, v)` there is a *unique* homomorphism `val(s) : Exp → D` — Scott's evaluation of an
expression. Existence is `descAlgHom` (Phase 3); uniqueness is the projection-chain argument. -/
def ExpInitial : IsInitial (ExpAlg N hN) where
  desc B := descAlgHom hN B
  uniq B g := algHom_ext (Subtype.ext (descMap_eq_algHom hN B g))

end Uniqueness

end Exercise619

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Theorem614.lean -/

/-!
# Lecture VI — Theorem 6.14 (Scott 1981, PRG-19): existence of initial `T`-algebras

> **THEOREM 6.14.** If the functor `T` is continuous on maps and monotone and continuous on domains,
> and if there is a set `Γ` such that `{Γ} ◁ T({Γ})`, then there exists an initial `T`-algebra.

Scott's proof iterates the functor from the generating system `{Γ}`. The assumption
`{Γ} ◁ T({Γ})` means `T({Γ})` is a system over the same token set `Γ`; iterating, every
`Tⁿ({Γ})` is over `Γ` and `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. The colimit

`𝒟 = ⋃ₙ Tⁿ({Γ})`

is then a system over `Γ` with `Tⁿ({Γ}) ◁ 𝒟`, whence `𝒟 ◁ T(𝒟)`, and *continuity on domains*
gives `T(𝒟) = 𝒟` — the isomorphism `𝒟 ≅ T(𝒟)` is the **identity**. So `𝒟` is a `T`-algebra, and:

* **existence** of homomorphisms out of `𝒟` is Theorem 6.9 (`nonempty_algHom_of_continuousOnMaps`);
* **uniqueness** is the `ρₙ = iₙ ∘ jₙ` projection-chain argument: `T(ρₙ) = ρₙ₊₁` (monotone on
  domains), `⋃ₙ ρₙ = I_𝒟`, and any homomorphism `h` is `⋃ₙ h∘ρₙ`, the least fixed point of
  `λh. k ∘ T(h)`.

## The carrier-type subtlety

The abstract `T : Endofunctor DomainObj` need not preserve token types, so `Tⁿ({Γ})` a priori live
over different carriers. The hypothesis `{Γ} ◁ T({Γ})` already pins `T({Γ})` to `Γ`'s carrier, and
*monotone on domains* (Definition 6.13, `MonotoneAt.carrier_eq`) propagates the identification up the
tower. We carry the carrier equalities explicitly and transport along them; the transport of the
subdomain relation is the choice-free `subsystem_cast`.

## Lean note: `rw` fragility on defeq-but-not-syntactic implicits

Throughout the uniqueness half, `rw` with explicit arguments at the `ApproximableMap` /
`NeighborhoodSystem` level repeatedly failed with "did not find an occurrence of the pattern" even
when the pattern was visibly present — because the implicit carriers/systems were **defeq but not
syntactically equal** (`colim s` vs `(colimAlg s).carrier.sys` vs `(objColim s).sys`; the abbrev
`objColim` vs the literal `⟨Tok, colim s⟩`). Three fixes, used throughout `gcomp_rho_succ`/`gcomp_eq`:
* work at the categorical `⊚` / `Category.assoc` level, where the implicits are concrete `DomainObj`s
  rather than systems, so unification has nothing to get stuck on;
* prefer `congrArg` / `calc` **term-mode** proofs (e.g. `congrArg (fun x => g.hom ⊚ x) (key_rho s n)`),
  since `calc` bridges adjacent steps by defeq rather than by syntactic match;
* to rewrite with a lemma whose implicit is pinned to the "wrong" representation (e.g. `comp_idMap`,
  whose `idMap` arg is tied to `g.hom`'s domain `(colimAlg s).carrier.sys`), first bind the fact via a
  `have` stated in the *desired* form (`have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap
  g.hom` — the `have` unifies by defeq), then `rw [← e]`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe w

namespace Theorem614

/-! ### Carrier-transport helpers -/

variable {α : Type w}

/-- Transport a subsystem relation `D ◁ E` along a carrier-type equality `β = α`. Choice-free. -/
theorem subsystem_cast {β : Type w} (e : β = α) {D E : NeighborhoodSystem β} (h : D ◁ E) :
    (e ▸ D : NeighborhoodSystem α) ◁ (e ▸ E : NeighborhoodSystem α) := by
  cases e; exact h

/-- Transport composition for neighbourhood systems: `e' ▸ (e ▸ x) = (e.trans e') ▸ x`. -/
theorem rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (x : NeighborhoodSystem β) :
    (e' ▸ (e ▸ x : NeighborhoodSystem γ) : NeighborhoodSystem α) = (e.trans e') ▸ x := by
  cases e; cases e'; rfl

/-- Membership in a transported system: `(e ▸ V).mem X ↔ V.mem (e.symm ▸ X)`. -/
theorem mem_cast {β : Type w} (e : β = α) (V : NeighborhoodSystem β) (X : Set α) :
    (e ▸ V : NeighborhoodSystem α).mem X ↔ V.mem (e.symm ▸ X : Set β) := by
  cases e; rfl

/-- Transport composition for sets: `e' ▸ (e ▸ X) = (e.trans e') ▸ X`. -/
theorem set_rec_trans {β γ : Type w} (e : β = γ) (e' : γ = α) (X : Set β) :
    (e' ▸ (e ▸ X : Set γ) : Set α) = (e.trans e') ▸ X := by
  cases e; cases e'; rfl

/-! ### The setup bundle (hypotheses of Theorem 6.14) -/

/-- The hypotheses of Theorem 6.14, bundled: a functor `T` that is continuous on maps, monotone and
continuous on domains, together with a generating system `Γ` over a token type `Tok` such that
`{Γ} ◁ T({Γ})` (the carrier of `T({Γ})` is identified with `Tok` by `ceq`, and `hsub` is Scott's
`{Γ} ◁ T({Γ})`). -/
structure Setup where
  /-- The functor. -/
  T : Endofunctor DomainObj.{w}
  /-- `T` is continuous on maps (Definition 6.8). -/
  hmaps : ContinuousOnMaps T
  /-- `T` is monotone on domains (Definition 6.13). -/
  hmono : MonotoneOnDomains T
  /-- `T` is continuous on domains (Definition 6.13). -/
  hcont : ContinuousOnDomains T
  /-- The token type of the generating system. -/
  {Tok : Type w}
  /-- The generating system `{Γ}`. -/
  Γ : NeighborhoodSystem Tok
  /-- `T({Γ})` is a system over the same token type. -/
  ceq : (T.obj ⟨Tok, Γ⟩).carrier = Tok
  /-- Scott's hypothesis `{Γ} ◁ T({Γ})`. -/
  hsub : Γ ◁ (ceq ▸ (T.obj ⟨Tok, Γ⟩).sys : NeighborhoodSystem Tok)

/-! ### The iterated functor tower `Tⁿ({Γ})` -/

/-- The iterated tower, as data: at level `n`, the system `Tⁿ({Γ})` over `Tok`, the carrier
identification `(T.obj Tⁿ({Γ})).carrier = Tok`, and the subdomain relation `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`
(where `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`). The successor step uses
*monotone on domains* (`MonotoneAt`) to obtain the next carrier identification and subdomain
relation. Choice-free. -/
def iter (s : Setup.{w}) : (n : ℕ) →
    Σ' (S : NeighborhoodSystem s.Tok), Σ' (ceq : (s.T.obj ⟨s.Tok, S⟩).carrier = s.Tok),
      S ◁ (ceq ▸ (s.T.obj ⟨s.Tok, S⟩).sys : NeighborhoodSystem s.Tok)
  | 0 => ⟨s.Γ, s.ceq, s.hsub⟩
  | (n + 1) =>
      let p := iter s n
      ⟨p.2.1 ▸ (s.T.obj ⟨s.Tok, p.1⟩).sys,
        (s.hmono p.2.2).carrier_eq.trans p.2.1,
        by
          have hsub := subsystem_cast p.2.1 (s.hmono p.2.2).sub
          rwa [rec_trans] at hsub⟩

/-- `Tⁿ({Γ})`, the `n`-th system in the tower (over `Tok`). -/
def Dsys (s : Setup.{w}) (n : ℕ) : NeighborhoodSystem s.Tok := (iter s n).1

/-- The carrier identification `(T.obj Tⁿ({Γ})).carrier = Tok`. -/
theorem Dceq (s : Setup.{w}) (n : ℕ) : (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier = s.Tok := (iter s n).2.1

/-- `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`. -/
theorem Dsys_succ (s : Setup.{w}) (n : ℕ) :
    Dsys s (n + 1) = (Dceq s n ▸ (s.T.obj ⟨s.Tok, Dsys s n⟩).sys : NeighborhoodSystem s.Tok) :=
  rfl

/-- The basic subdomain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. -/
theorem Dchain (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ Dsys s (n + 1) := (iter s n).2.2

/-- Every system in the tower has the same master `Δ = Γ`. -/
theorem Dsys_master (s : Setup.{w}) (n : ℕ) : (Dsys s n).master = s.Γ.master := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← (Dchain s k).master_eq]; exact ih

/-- The tower is a `◁`-chain: `Tⁿ({Γ}) ◁ Tᵐ({Γ})` whenever `n ≤ m`. -/
theorem chain_le (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) : Dsys s n ◁ Dsys s m := by
  induction h with
  | refl => exact Subsystem.refl _
  | step _ ih => exact ih.trans (Dchain s _)

/-! ### The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` -/

/-- **The colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`** as a neighbourhood system over `Tok`: a set is a neighbourhood
of `𝒟` exactly when it is a neighbourhood of some `Tⁿ({Γ})`. Closure under consistent intersection
uses that the tower is a chain (`chain_le`): any finite collection of neighbourhoods sits inside one
level `Tᴺ({Γ})`, whose own `inter_mem` finishes the job. -/
def colim (s : Setup.{w}) : NeighborhoodSystem s.Tok where
  mem X := ∃ n, (Dsys s n).mem X
  master := s.Γ.master
  master_nonempty := s.Γ.master_nonempty
  master_mem := ⟨0, s.Γ.master_mem⟩
  inter_mem := by
    rintro X Y Z ⟨n, hX⟩ ⟨m, hY⟩ ⟨p, hZ⟩ hsub
    set N := max n (max m p) with hN
    have hXN : (Dsys s N).mem X := (chain_le s (le_max_left n _)).sub hX
    have hYN : (Dsys s N).mem Y :=
      (chain_le s ((le_max_left m p).trans (le_max_right n _))).sub hY
    have hZN : (Dsys s N).mem Z :=
      (chain_le s ((le_max_right m p).trans (le_max_right n _))).sub hZ
    exact ⟨N, (Dsys s N).inter_mem hXN hYN hZN hsub⟩
  sub_master := by
    rintro X ⟨n, hX⟩
    rw [← Dsys_master s n]
    exact (Dsys s n).sub_master hX

@[simp] theorem mem_colim (s : Setup.{w}) {X : Set s.Tok} :
    (colim s).mem X ↔ ∃ n, (Dsys s n).mem X := Iff.rfl

@[simp] theorem colim_master (s : Setup.{w}) : (colim s).master = s.Γ.master := rfl

/-- Each level of the tower is a subdomain of the colimit: `Tⁿ({Γ}) ◁ 𝒟`. -/
theorem Dsys_sub_colim (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ colim s where
  master_eq := by rw [colim_master, Dsys_master]
  sub hX := ⟨n, hX⟩
  inter_closed := by
    rintro X Y hX hY ⟨m, hXY⟩
    have hN : (Dsys s (max n m)).mem (X ∩ Y) := by
      have hle : (Dsys s m) ◁ (Dsys s (max n m)) := chain_le s (le_max_right n m)
      exact hle.sub hXY
    -- pull `X ∩ Y` back into `Tⁿ({Γ})` using consistency-in-the-bigger-level
    exact (chain_le s (le_max_left n m)).inter_closed hX hY hN

/-! ### `T(𝒟)` and the relation `𝒟 ◁ T(𝒟)` -/

/-- The carrier identification `(T.obj 𝒟).carrier = Tok`, from `MonotoneAt` of `T⁰({Γ}) ◁ 𝒟`. -/
theorem colimCeq (s : Setup.{w}) : (s.T.obj ⟨s.Tok, colim s⟩).carrier = s.Tok :=
  (s.hmono (Dsys_sub_colim s 0)).carrier_eq.trans (Dceq s 0)

/-- `T(𝒟)`, the image of the colimit, as a system over `Tok` (via `colimCeq`). -/
def Tcolim (s : Setup.{w}) : NeighborhoodSystem s.Tok :=
  colimCeq s ▸ (s.T.obj ⟨s.Tok, colim s⟩).sys

/-- `Tⁿ⁺¹({Γ}) ◁ T(𝒟)`: applying *monotone on domains* to `Tⁿ({Γ}) ◁ 𝒟` and transporting. -/
theorem Dsys_sub_Tcolim (s : Setup.{w}) (n : ℕ) : Dsys s (n + 1) ◁ Tcolim s := by
  have h := subsystem_cast (Dceq s n) (s.hmono (Dsys_sub_colim s n)).sub
  rw [rec_trans] at h
  exact h

/-- `T(𝒟)` and `𝒟` share the master `Δ = Γ`. -/
theorem Tcolim_master (s : Setup.{w}) : (Tcolim s).master = s.Γ.master := by
  rw [← (Dsys_sub_Tcolim s 0).master_eq, Dsys_master]

/-- The easy half of `T(𝒟) = 𝒟`: every neighbourhood of `𝒟` is a neighbourhood of `T(𝒟)`
(`𝒟 ⊆ T(𝒟)`), since `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ}) ◁ T(𝒟)`. -/
theorem colim_sub_Tcolim (s : Setup.{w}) {X : Set s.Tok} (hX : (colim s).mem X) :
    (Tcolim s).mem X := by
  obtain ⟨n, hn⟩ := hX
  exact (Dsys_sub_Tcolim s n).sub ((Dchain s n).sub hn)

/-- **The continuity step (the hard half of `T(𝒟) = 𝒟`).** Every neighbourhood of `T(𝒟)` is a
neighbourhood of `𝒟`. This is exactly Scott's `T(𝒟) = T(⋃ₙ Tⁿ({Γ})) = ⋃ₙ Tⁿ⁺¹({Γ}) = 𝒟`,
obtained from *continuity on domains* applied to the directed family `{Tⁿ({Γ})}`. -/
theorem Tcolim_sub_colim (s : Setup.{w}) {X : Set s.Tok} (hX : (Tcolim s).mem X) :
    (colim s).mem X := by
  obtain ⟨hmono', hC⟩ := s.hcont
  set ℱ : Set (NeighborhoodSystem s.Tok) := Set.range (Dsys s) with hℱdef
  have hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ colim s := by rintro D ⟨n, rfl⟩; exact Dsys_sub_colim s n
  have hne : ℱ.Nonempty := ⟨Dsys s 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ◁ ·) ℱ := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨Dsys s (max n m), ⟨max n m, rfl⟩,
      chain_le s (le_max_left n m), chain_le s (le_max_right n m)⟩
  have hU : ∀ Y, (colim s).mem Y ↔ ∃ D ∈ ℱ, D.mem Y := by
    intro Y; constructor
    · rintro ⟨n, hn⟩; exact ⟨Dsys s n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨D, ⟨n, rfl⟩, hn⟩; exact ⟨n, hn⟩
  have heq := hC ℱ hℱ hne hdir (Subsystem.refl (colim s)) hU
  set Y₀ : Set (s.T.obj ⟨s.Tok, colim s⟩).carrier := (colimCeq s).symm ▸ X with hY₀
  -- `X ∈ T(𝒟)` says `Y₀ ∈ targetFam (refl 𝒟)` = the neighbourhood family of `T(𝒟)`.
  have hmem : Y₀ ∈ targetFam s.T hmono' (Subsystem.refl (colim s)) :=
    (mem_cast (colimCeq s) _ X).mp hX
  rw [heq, Set.mem_iUnion] at hmem
  obtain ⟨D, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨hD, hmemD⟩ := hmem
  obtain ⟨n, rfl⟩ := hD
  simp only [targetFam, Set.mem_ofPred_eq] at hmemD
  -- conclude `X ∈ Tⁿ⁺¹({Γ}) ⊆ 𝒟`.
  refine ⟨n + 1, ?_⟩
  rw [Dsys_succ s n, mem_cast (Dceq s n)]
  have key : ((Dceq s n).symm ▸ X : Set (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier)
      = (s.hmono (hℱ ⟨n, rfl⟩)).carrier_eq ▸ Y₀ := by
    rw [hY₀, set_rec_trans]
  rw [key]
  exact hmemD

/-- **`T(𝒟) = 𝒟`** (Scott's `𝒟 = T(𝒟)`): the two systems have the same neighbourhoods (mutual
inclusion via `colim_sub_Tcolim`/`Tcolim_sub_colim`) and the same master. -/
theorem Tcolim_eq_colim (s : Setup.{w}) : Tcolim s = colim s :=
  NeighborhoodSystem.ext
    (fun _ => ⟨fun h => Tcolim_sub_colim s h, fun h => colim_sub_Tcolim s h⟩)
    (by rw [Tcolim_master, colim_master])

/-! ### `𝒟` is a `T`-algebra: the iso `𝒟 ≅ T(𝒟)` is the identity -/

/-- A `DomainObj` equality from a carrier equality and a transported-system equality. -/
theorem domainObj_ext {c : Type w} (σ : NeighborhoodSystem c) (e : c = α)
    {V : NeighborhoodSystem α} (h : (e ▸ σ : NeighborhoodSystem α) = V) :
    (⟨c, σ⟩ : DomainObj) = ⟨α, V⟩ := by
  cases e; cases h; rfl

/-- The identity isomorphism induced by an object equality in any category. -/
def isoOfEq {Obj : Type*} [Category Obj] {X Y : Obj} (h : X = Y) : Iso X Y := by
  cases h
  exact ⟨Category.id X, Category.id X, Category.id_comp _, Category.id_comp _⟩

/-- **`T(𝒟) ≅ 𝒟` is the identity**, packaged as a `DomainObj` equality `T(𝒟) = 𝒟`. -/
theorem colimObj_eq (s : Setup.{w}) :
    s.T.obj ⟨s.Tok, colim s⟩ = (⟨s.Tok, colim s⟩ : DomainObj) :=
  domainObj_ext (s.T.obj ⟨s.Tok, colim s⟩).sys (colimCeq s) (Tcolim_eq_colim s)

/-- The isomorphism `T(𝒟) ≅ 𝒟` making `𝒟` a `T`-algebra (the identity, since `T(𝒟) = 𝒟`). -/
def colimIso (s : Setup.{w}) : Iso (s.T.obj ⟨s.Tok, colim s⟩) (⟨s.Tok, colim s⟩ : DomainObj) :=
  isoOfEq (colimObj_eq s)

/-- The colimit `𝒟` as a `T`-algebra, with structure map the iso `T(𝒟) → 𝒟`. -/
abbrev colimAlg (s : Setup.{w}) : TAlgebra s.T :=
  ⟨⟨s.Tok, colim s⟩, (colimIso s).hom⟩

/-! ### Existence of homomorphisms (Theorem 6.9) -/

/-- **Existence (Theorem 6.9 applied to `𝒟 ≅ T(𝒟)`).** For any `T`-algebra `B` with a strict
structure map, there is a *strict* homomorphism `𝒟 → B`. -/
theorem nonempty_strict_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (colimAlg s) B // IsStrict g.hom} :=
  nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk

/-- **Existence (Theorem 6.9 applied to `𝒟 ≅ T(𝒟)`).** For any `T`-algebra `B` with a strict
structure map, there is a homomorphism `𝒟 → B`. -/
theorem nonempty_algHom (s : Setup.{w}) (B : TAlgebra s.T) (hk : IsStrict B.str) :
    Nonempty (AlgHom (colimAlg s) B) :=
  (nonempty_strict_algHom s B hk).map (·.1)

/-! ### The projection chain `ρₙ = iₙ ∘ jₙ` and `⋃ₙ ρₙ = I_𝒟` -/

/-- `ρₙ = iₙ ∘ jₙ : 𝒟 → 𝒟`, the retraction onto `Tⁿ({Γ})` (Proposition 6.12's projection pair for
`Tⁿ({Γ}) ◁ 𝒟`). -/
def rho (s : Setup.{w}) (n : ℕ) : ApproximableMap (colim s) (colim s) :=
  (Dsys_sub_colim s n).inj.comp (Dsys_sub_colim s n).proj

/-- Scott's relational description `X ρₙ Y ↔ ∃ z ∈ Tⁿ({Γ}), X ⊆ z ⊆ Y`. -/
theorem rho_rel (s : Setup.{w}) (n : ℕ) {X Y : Set s.Tok} :
    (rho s n).rel X Y ↔
      (colim s).mem X ∧ (colim s).mem Y ∧ ∃ z, (Dsys s n).mem z ∧ X ⊆ z ∧ z ⊆ Y := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, ⟨hcX, hDz, hXz⟩, _, hcY, hzY⟩
    exact ⟨hcX, hcY, z, hDz, hXz, hzY⟩
  · rintro ⟨hcX, hcY, z, hDz, hXz, hzY⟩
    exact ⟨z, ⟨hcX, hDz, hXz⟩, hDz, hcY, hzY⟩

/-- `ρₙ ⊆ ρₘ` for `n ≤ m` (the projection chain is increasing). -/
theorem rho_mono (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) {X Y : Set s.Tok}
    (hr : (rho s n).rel X Y) : (rho s m).rel X Y := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcX, hcY, z, hDz, hXz, hzY⟩ := hr
  exact ⟨hcX, hcY, z, (chain_le s h).sub hDz, hXz, hzY⟩

/-- The pointwise union `⋃ₙ ρₙ` (directed, since the chain is increasing). -/
def iSupRho (s : Setup.{w}) : ApproximableMap (colim s) (colim s) :=
  iSupMap (rho s) (fun i j => ⟨max i j,
    fun _ _ h => rho_mono s (le_max_left i j) h,
    fun _ _ h => rho_mono s (le_max_right i j) h⟩)

/-- **`⋃ₙ ρₙ = I_𝒟`** (Scott's key identity for uniqueness). The forward inclusion uses
`X ⊆ z ⊆ Y ⟹ X ⊆ Y`; the reverse factors the identity step `X ⊆ X ⊆ Y` through the level
witnessing `X ∈ 𝒟`. -/
theorem iSupRho_eq_id (s : Setup.{w}) : iSupRho s = idMap (colim s) := by
  apply ApproximableMap.ext
  intro X Y
  rw [idMap_rel]
  constructor
  · rintro ⟨n, hr⟩
    rw [rho_rel] at hr
    obtain ⟨hcX, hcY, z, _, hXz, hzY⟩ := hr
    exact ⟨hcX, hcY, hXz.trans hzY⟩
  · rintro ⟨hcX, hcY, hXY⟩
    obtain ⟨n, hX⟩ := hcX
    exact ⟨n, (rho_rel s n).mpr ⟨⟨n, hX⟩, hcY, X, hX, subset_rfl, hXY⟩⟩

/-! ### Theorem 6.14 — the existence half (the canonical solution and its homomorphisms) -/

/-- **Theorem 6.14 (Scott 1981, PRG-19) — the canonical fixed point.** Under the hypotheses
(continuous on maps, monotone and continuous on domains, with a generating set `{Γ} ◁ T({Γ})`), the
iterated colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra whose structure map is an isomorphism
`T(𝒟) ≅ 𝒟` (the identity, since `T(𝒟) = 𝒟`), and there is a homomorphism from `𝒟` into every
`T`-algebra with a strict structure map (Theorem 6.9). This is Scott's *existence* of the initial
`T`-algebra. -/
theorem exists_algebra_with_hom (s : Setup.{w}) :
    ∃ A : TAlgebra s.T, Nonempty (Iso (s.T.obj A.carrier) A.carrier) ∧
      ∀ B : TAlgebra s.T, IsStrict B.str → Nonempty (AlgHom A B) :=
  ⟨colimAlg s, ⟨colimIso s⟩, fun B hk => nonempty_algHom s B hk⟩

/-! ### Theorem 6.14 — the uniqueness half (`T(ρₙ) = ρₙ₊₁`, then `g = ⋃ₙ g∘ρₙ`)

Scott shows homomorphisms out of `𝒟` are unique by showing they are determined on the finite
elements. Concretely, the projection chain `ρₙ = iₙ ∘ jₙ` satisfies `T(ρₙ) = ρₙ₊₁` (because `T` is
monotone on domains, so it carries the projection pair `iₙ, jₙ` to `iₙ₊₁, jₙ₊₁`) and
`⋃ₙ ρₙ = I_𝒟`. For any homomorphism `g : 𝒟 → E`, the sequence `gₙ = g ∘ ρₙ` is then **independent
of `g`**: `g₀ = ⊥` (because `g` is strict and `ρ₀ = ⊥`), and `gₙ₊₁ = k ∘ T(gₙ) ∘ j` by the
homomorphism square; so `g = ⋃ₙ gₙ` is forced. -/

/-- In the category of domains, `⊚` (categorical composition) is `ApproximableMap.comp`. -/
theorem cat_comp_eq {X Y Z : DomainObj} (g : Category.Hom Y Z) (f : Category.Hom X Y) :
    g ⊚ f = g.comp f := rfl

/-- The colimit `𝒟` as a category object `⟨Tok, 𝒟⟩`. -/
abbrev objColim (s : Setup.{w}) : DomainObj := ⟨s.Tok, colim s⟩

/-- The `n`-th tower system `Tⁿ({Γ})` as a category object `⟨Tok, Tⁿ({Γ})⟩`. -/
abbrev objDsys (s : Setup.{w}) (n : ℕ) : DomainObj := ⟨s.Tok, Dsys s n⟩

/-- `T(ρₙ)` as an endomorphism of `T(𝒟)`, with the category objects pinned (they cannot be inferred
from `rho s n`'s `ApproximableMap` type alone). -/
abbrev Tmap_rho (s : Setup.{w}) (n : ℕ) :
    ApproximableMap (s.T.obj (objColim s)).sys (s.T.obj (objColim s)).sys :=
  s.T.map (X := objColim s) (Y := objColim s) (rho s n)

/-- Transport of a `Hom X X` along an object equality is heterogeneously equal to itself. -/
theorem transport_heq {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : Category.Hom X X) : HEq (e ▸ f : Category.Hom Y Y) f := by
  cases e; rfl

/-- Conjugation by the identity isomorphism `isoOfEq e` is the object-transport along `e`. -/
theorem isoOfEq_conj {Obj : Type*} [Category Obj] {X Y : Obj} (e : X = Y)
    (f : Category.Hom X X) :
    (isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = (e ▸ f : Category.Hom Y Y) := by
  cases e
  change Category.id X ⊚ f ⊚ Category.id X = f
  rw [Category.id_comp, Category.comp_id]

/-- **The carrier-transport core of `T(ρₙ) = ρₙ₊₁`.** Given the *monotone-on-domains* data for a
subsystem (its injection `Tmi`/projection `Tmj` are heterogeneously equal to the canonical 6.12 pair
`sub.inj`/`sub.proj` of the image subsystem `sub : Ps ◁ ce ▸ Qs`), the composite `Tmi ∘ Tmj` is —
after carrying the functor-image carriers `Pc, Qc` down to `Tok` — exactly the projection
`iₙ₊₁ ∘ jₙ₊₁` of the next subsystem `hsub' : Dn1 ◁ Col`. Proved by `subst`ing the carrier equalities,
after which proof-irrelevance identifies the two subsystem proofs. -/
theorem map_comp_proj_heq {Tok : Type w} {Pc Qc : Type w} (cn : Pc = Tok) (cc : Qc = Tok)
    {Ps : NeighborhoodSystem Pc} {Qs : NeighborhoodSystem Qc} (ce : Qc = Pc)
    (sub : Ps ◁ (ce ▸ Qs : NeighborhoodSystem Pc))
    {Dn1 Col : NeighborhoodSystem Tok}
    (hDn1 : (cn ▸ Ps : NeighborhoodSystem Tok) = Dn1)
    (hCol : (cc ▸ Qs : NeighborhoodSystem Tok) = Col)
    (hsub' : Dn1 ◁ Col)
    (Tmi : ApproximableMap Ps Qs) (Tmj : ApproximableMap Qs Ps)
    (hi : HEq Tmi sub.inj) (hj : HEq Tmj sub.proj) :
    HEq (Tmi.comp Tmj) (hsub'.inj.comp hsub'.proj) := by
  subst cn
  subst cc
  obtain rfl := hDn1
  obtain rfl := hCol
  have e1 : Tmi = sub.inj := eq_of_heq hi
  have e2 : Tmj = sub.proj := eq_of_heq hj
  rw [e1, e2]

/-- **`T(ρₙ) = ρₙ₊₁`, heterogeneously.** The image `T(ρₙ)` of the `n`-th projection, living over
`T(𝒟)`'s carrier, is heterogeneously equal to the `(n+1)`-st projection `ρₙ₊₁` over `Tok`. -/
theorem map_rho_heq (s : Setup.{w}) (n : ℕ) :
    HEq (Tmap_rho s n) (rho s (n + 1)) := by
  have hcomp : Tmap_rho s n
      = (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj).comp
          (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj) :=
    s.T.map_comp (X := objColim s) (Y := objDsys s n) (Z := objColim s)
      (Dsys_sub_colim s n).inj (Dsys_sub_colim s n).proj
  rw [hcomp]
  exact map_comp_proj_heq (Dceq s n) (colimCeq s) (s.hmono (Dsys_sub_colim s n)).carrier_eq
    (s.hmono (Dsys_sub_colim s n)).sub (Dsys_succ s n).symm (Tcolim_eq_colim s)
    (Dsys_sub_colim s (n + 1)) (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj)
    (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj)
    (s.hmono (Dsys_sub_colim s n)).inj_heq (s.hmono (Dsys_sub_colim s n)).proj_heq

/-- **`ρₙ₊₁ = i ∘ T(ρₙ) ∘ j`** (Scott's `T(ρₙ) = ρₙ₊₁`, conjugated by the structure iso). Since the
iso `𝒟 ≅ T(𝒟)` is the identity, this is the carrier transport of `T(ρₙ)`; combined with
`map_rho_heq` it pins `ρₙ₊₁`. -/
theorem key_rho (s : Setup.{w}) (n : ℕ) :
    rho s (n + 1) = (colimIso s).hom ⊚ Tmap_rho s n ⊚ (colimIso s).inv := by
  rw [show (colimIso s).hom = (isoOfEq (colimObj_eq s)).hom from rfl,
      show (colimIso s).inv = (isoOfEq (colimObj_eq s)).inv from rfl,
      isoOfEq_conj (colimObj_eq s) (Tmap_rho s n)]
  apply eq_of_heq
  exact HEq.trans (map_rho_heq s n).symm
    (transport_heq (colimObj_eq s) (Tmap_rho s n)).symm

/-! ### The `g`-independent fixed-point recursion -/

/-- For a strict map `g`, `g(⊥) = ⊥` relationally: `g` sends `Δ` only to `Δ`. -/
theorem strict_rel_master {β₀ β₁ : Type w} {V₀ : NeighborhoodSystem β₀}
    {V₁ : NeighborhoodSystem β₁} {g : ApproximableMap V₀ V₁} (hg : IsStrict g) {Z : Set β₁} :
    g.rel V₀.master Z ↔ Z = V₁.master :=
  ⟨fun h => hg h, fun h => h ▸ g.master_rel⟩

/-- `Dsys s 0 = Γ` (the base of the tower). -/
@[simp] theorem Dsys_zero (s : Setup.{w}) : Dsys s 0 = s.Γ := rfl

/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

/-- For a strict homomorphism `g`, the base `g ∘ ρ₀` is the least map: it relates `X` only to the
master of `E`, independent of `g`. -/
theorem gcomp_rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g : ApproximableMap (colim s) B.carrier.sys} (hg : IsStrict g)
    {X : Set s.Tok} {Z : Set B.carrier.carrier} :
    (g.comp (rho s 0)).rel X Z ↔ (colim s).mem X ∧ Z = B.carrier.sys.master := by
  rw [comp_rel]
  constructor
  · rintro ⟨Y, hrho, hgYZ⟩
    rw [rho_zero_rel s hΓ] at hrho
    obtain ⟨hcX, rfl⟩ := hrho
    exact ⟨hcX, (strict_rel_master hg).mp hgYZ⟩
  · rintro ⟨hcX, rfl⟩
    exact ⟨(colim s).master, (rho_zero_rel s hΓ).mpr ⟨hcX, rfl⟩, g.master_rel⟩

/-- The base case of `g`-independence: any two strict maps agree after `∘ ρ₀`. -/
theorem gcomp_rho_zero_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g g' : ApproximableMap (colim s) B.carrier.sys}
    (hg : IsStrict g) (hg' : IsStrict g') :
    g.comp (rho s 0) = g'.comp (rho s 0) := by
  apply ApproximableMap.ext
  intro X Z
  rw [gcomp_rho_zero_rel s hΓ B hg, gcomp_rho_zero_rel s hΓ B hg']

/-- **The fixed-point recursion `gₙ₊₁ = k ∘ T(gₙ) ∘ j`.** Using `key_rho` (`ρₙ₊₁ = i∘T(ρₙ)∘j`) and the
homomorphism square `g ∘ i = k ∘ T(g)`. -/
theorem gcomp_rho_succ (s : Setup.{w}) (B : TAlgebra s.T) (g : AlgHom (colimAlg s) B) (n : ℕ) :
    g.hom.comp (rho s (n + 1))
      = B.str.comp ((s.T.map (X := objColim s) (Y := B.carrier)
          (g.hom.comp (rho s n))).comp (colimIso s).inv) := by
  have hcomm : g.hom ⊚ (colimIso s).hom
      = B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom := g.comm
  show g.hom ⊚ rho s (n + 1)
      = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)) ⊚ (colimIso s).inv
  calc g.hom ⊚ rho s (n + 1)
      = g.hom ⊚ ((colimIso s).hom ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          congrArg (fun x => g.hom ⊚ x) (key_rho s n)
    _ = (g.hom ⊚ (colimIso s).hom) ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) :=
          (Category.assoc g.hom (colimIso s).hom (Tmap_rho s n ⊚ (colimIso s).inv)).symm
    _ = (B.str ⊚ s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv) := by rw [hcomm]
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) g.hom
            ⊚ (Tmap_rho s n ⊚ (colimIso s).inv)) :=
          Category.assoc B.str (s.T.map (X := objColim s) (Y := B.carrier) g.hom)
            (Tmap_rho s n ⊚ (colimIso s).inv)
    _ = B.str ⊚ ((s.T.map (X := objColim s) (Y := B.carrier) g.hom ⊚ Tmap_rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (B.str ⊚ ·)
            (Category.assoc (s.T.map (X := objColim s) (Y := B.carrier) g.hom) (Tmap_rho s n)
              (colimIso s).inv).symm
    _ = B.str ⊚ (s.T.map (X := objColim s) (Y := B.carrier) (g.hom ⊚ rho s n)
            ⊚ (colimIso s).inv) :=
          congrArg (fun m => B.str ⊚ (m ⊚ (colimIso s).inv))
            (s.T.map_comp (X := objColim s) (Y := objColim s) (Z := B.carrier) g.hom
              (rho s n)).symm

/-- **`g`-independence of `gₙ = g ∘ ρₙ`.** For any two strict homomorphisms into the same algebra,
`g ∘ ρₙ = g' ∘ ρₙ` for all `n` — the sequence is determined by the recursion, not by `g`. -/
theorem gcomp_rho_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) (n : ℕ) :
    g.hom.comp (rho s n) = g'.hom.comp (rho s n) := by
  induction n with
  | zero => exact gcomp_rho_zero_indep s hΓ B hg hg'
  | succ k ih => rw [gcomp_rho_succ s B g k, gcomp_rho_succ s B g' k, ih]

/-! ### Uniqueness and initiality (among strict algebras) -/

/-- Two algebra homomorphisms with equal underlying maps are equal (the commuting square is a
`Prop`). -/
theorem algHom_ext {Obj : Type*} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}
    {g g' : AlgHom A B} (h : g.hom = g'.hom) : g = g' := by
  cases g; cases g'; cases h; rfl

/-- **The underlying maps of two strict homomorphisms coincide**: `g = g ∘ I = g ∘ ⋃ₙ ρₙ =
⋃ₙ (g ∘ ρₙ)`, and the latter is `g`-independent. -/
theorem gcomp_eq (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) :
    g.hom = g'.hom := by
  have key : g.hom.comp (iSupRho s) = g'.hom.comp (iSupRho s) := by
    apply ApproximableMap.ext
    intro X Z
    rw [comp_rel, comp_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g'.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [← gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
  have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap g.hom
  have e' : g'.hom.comp (idMap (colim s)) = g'.hom := comp_idMap g'.hom
  rw [← e, ← e', ← iSupRho_eq_id]
  exact key

/-- **Uniqueness of strict homomorphisms out of `𝒟`.** Any two strict `T`-algebra homomorphisms from
the canonical solution into the same algebra are equal. -/
theorem algHom_unique (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) : g = g' :=
  algHom_ext (gcomp_eq s hΓ B g g' hg hg')

/-- **Theorem 6.14 (Scott 1981, PRG-19) — initial `T`-algebra.** When `{Γ}` is the one-point
generating system, the canonical solution `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among the
strict algebras: for every `T`-algebra `B` with a strict structure map there is a *unique* strict
homomorphism `𝒟 → B`. (Existence is Theorem 6.9; uniqueness is the `ρₙ` projection-chain argument.) -/
theorem exists_unique_strict_algHom (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (hk : IsStrict B.str) :
    ∃ g : AlgHom (colimAlg s) B, IsStrict g.hom ∧
      ∀ g' : AlgHom (colimAlg s) B, IsStrict g'.hom → g' = g := by
  obtain ⟨⟨g, hg⟩⟩ := nonempty_strict_algHom s B hk
  exact ⟨g, hg, fun g' hg' => algHom_unique s hΓ B g' g hg' hg⟩

end Theorem614

end Scott1980.Neighborhood

/-! ### Inlined from Scott1980/Neighborhood/Theorem616.lean -/

/-!
# Lecture VI — Theorem 6.16 (Scott 1981, PRG-19): an initial algebra embeds in every solution

> **THEOREM 6.16.** If on the category of domains and strict approximable maps the functor `T` is
> continuous on maps, and if `D` is an initial `T`-algebra, then for any system `E ≅ T(E)` we have
> `D ⊴ E`.

Scott's proof. By Theorem 6.9 there is a homomorphism `h : D → E` and (running 6.9 the other way) a
homomorphism `g : E → D`. The composite `g ∘ h : D → D` is a homomorphism of the *initial* algebra
`D`, hence equals `I_D` by uniqueness. By Lemma 6.15 it remains to show `h ∘ g ⊑ I_E`.

Writing `i : T(D) → D`, `j : D → T(D)` for `D`'s isomorphism (Lambek, Proposition 6.7) and
`u : T(E) → E`, `v : E → T(E)` for `E`'s, the proof of 6.9 produces `h` and `g` as the least fixed
points of
`h = u ∘ T(h) ∘ j` and `g = i ∘ T(g) ∘ v`.
Setting `h₀ = ⊥`, `g₀ = ⊥` and `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, `gₙ₊₁ = i ∘ T(gₙ) ∘ v`, one computes
`hₙ₊₁ ∘ gₙ₊₁ = u ∘ T(hₙ ∘ gₙ) ∘ v` (using `j ∘ i = I_{T(D)}`), so `kₙ := hₙ ∘ gₙ` is the approximant
chain of the operator `k ↦ u ∘ T(k) ∘ v`. Therefore `h ∘ g = ⊔ₙ (hₙ ∘ gₙ)` is its *least* fixed
point, and since `I_E` is a fixed point of that operator, `h ∘ g ⊑ I_E`.

## What the formalization does

Everything reuses Theorem 6.9's operator `(homOp T D E j k) ∘ Φ` on Scott's **strict** function
space `(D →⊥ E)` (Exercise 5.10). The per-step computation is isolated as `opStep`. The three
approximant chains `H`, `G`, `K` (for `h`, `g`, `k`) and the ladder identity `H n ∘ G n = K n` give
`h ∘ g = k` (the least fixed point of `u ∘ T(·) ∘ v`), which is `⊑ I_E` because `I_E` is a fixed
point. Lemma 6.15 (`trianglelefteq_of_projectionPair`) then closes `D ⊴ E`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Scott1980.Neighborhood.Exercise510

universe w

/-! ### General helpers. -/

/-- **The per-step computation of Theorem 6.9's operator.** For the operator `Op = (k ∘ · ∘ j) ∘ Φ`
on the strict function space, `Op(x)` is the strict map `k ∘ T(toStrictMap x) ∘ j`. This is the
content of `homOp_apply_filter` plus the defining property `hΦ` of the Definition 6.8 witness `Φ`. -/
theorem opStep (T : Endofunctor DomainObj.{w}) (D E : DomainObj.{w})
    (j : ApproximableMap D.sys (T.obj D).sys) (k : ApproximableMap (T.obj E).sys E.sys)
    (hj : IsStrict j) (hk : IsStrict k)
    (Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys))
    (hΦ : ∀ f : StrictMap D.sys E.sys,
      (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1)
    (x : (strictFun D.sys E.sys).Element) :
    (toStrictMap (((homOp T D E j k hj hk).comp Φ).toElementMap x)).1
      = k.comp ((T.map (X := D) (Y := E) (toStrictMap x).1).comp j) := by
  set h := toStrictMap x with hh
  have hx : toStrictFilter h = x := toStrictFilter_toStrictMap x
  have hφ : Φ.toElementMap x
      = toStrictFilter (toStrictMap (Φ.toElementMap (toStrictFilter h))) := by
    rw [← hx]; exact (toStrictFilter_toStrictMap _).symm
  rw [toElementMap_comp, hφ, homOp_apply_filter, toStrictMap_toStrictFilter]
  show k.comp ((toStrictMap (Φ.toElementMap (toStrictFilter h))).1.comp j)
      = k.comp ((T.map (X := D) (Y := E) h.1).comp j)
  rw [hΦ h]

/-- The strict map represented by `⊥` of the strict function space relates `X` to `Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥` (least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX

/-! ### Theorem 6.16. -/

/-- **Theorem 6.16 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D` is an initial
`T`-algebra, then for any system `E ≅ T(E)` we have `D ⊴ E`: the initial algebra embeds as a
subdomain of every solution of the domain equation. -/
theorem trianglelefteq_of_isInitial
    (T : Endofunctor DomainObj.{w}) (hT : ContinuousOnMaps T)
    (Dalg : TAlgebra T) (hinit : IsInitial Dalg)
    (E : DomainObj.{w}) (isoE : Iso (T.obj E) E) :
    Dalg.carrier.sys ⊴ E.sys := by
  -- Lambek (Proposition 6.7): the structure map of `D` is an isomorphism `i : T(D) ≅ D`.
  let isoD : Iso (T.obj Dalg.carrier) Dalg.carrier := lambek Dalg hinit
  -- strictness of the four structure maps (each is a split iso, hence preserves `⊥`).
  have hi : IsStrict isoD.hom := isStrict_of_comp_eq_id isoD.inv_hom_id
  have hj : IsStrict isoD.inv := isStrict_of_comp_eq_id isoD.hom_inv_id
  have hu : IsStrict isoE.hom := isStrict_of_comp_eq_id isoE.inv_hom_id
  have hv : IsStrict isoE.inv := isStrict_of_comp_eq_id isoE.hom_inv_id
  -- the iso laws in `.comp` form.
  have hji : isoD.inv.comp isoD.hom = idMap (T.obj Dalg.carrier).sys := isoD.hom_inv_id
  have hvu : isoE.inv.comp isoE.hom = idMap (T.obj E).sys := isoE.hom_inv_id
  have huv : isoE.hom.comp isoE.inv = idMap E.sys := isoE.inv_hom_id
  -- Definition 6.8 witnesses that `λf. T(f)` is approximable on each strict function space.
  obtain ⟨ΦDE, hΦDE⟩ := hT Dalg.carrier E
  obtain ⟨ΦED, hΦED⟩ := hT E Dalg.carrier
  obtain ⟨ΦEE, hΦEE⟩ := hT E E
  -- the three operators (Theorem 6.9's `λf. k ∘ T(f) ∘ j`) for `h`, `g`, `k`.
  let Oph := (homOp T Dalg.carrier E isoD.inv isoE.hom hj hu).comp ΦDE
  let Opg := (homOp T E Dalg.carrier isoE.inv isoD.hom hv hi).comp ΦED
  let Opk := (homOp T E E isoE.inv isoE.hom hv hu).comp ΦEE
  -- the approximant chains.
  let H : ℕ → ApproximableMap Dalg.carrier.sys E.sys := fun n => (toStrictMap (Oph.iterElem n)).1
  let G : ℕ → ApproximableMap E.sys Dalg.carrier.sys := fun n => (toStrictMap (Opg.iterElem n)).1
  let K : ℕ → ApproximableMap E.sys E.sys := fun n => (toStrictMap (Opk.iterElem n)).1
  -- `iterElem 0 = ⊥`.
  have iterElem_zero : ∀ {γ : Type w} {V : NeighborhoodSystem γ} (f : ApproximableMap V V),
      f.iterElem 0 = V.bot := by
    intro γ V f
    show (f.iterMap 0).toElementMap V.bot = V.bot
    rw [iterMap_zero, toElementMap_idMap]
  -- the recursion equations `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, etc.
  have H_succ : ∀ n, H (n + 1)
      = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) (H n)).comp isoD.inv) := by
    intro n
    show (toStrictMap (Oph.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE (Oph.iterElem n)
  have G_succ : ∀ n, G (n + 1)
      = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) (G n)).comp isoE.inv) := by
    intro n
    show (toStrictMap (Opg.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED (Opg.iterElem n)
  have K_succ : ∀ n, K (n + 1)
      = isoE.hom.comp ((T.map (X := E) (Y := E) (K n)).comp isoE.inv) := by
    intro n
    show (toStrictMap (Opk.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE (Opk.iterElem n)
  -- monotonicity of the chains.
  have H_mono : ∀ {n m : ℕ}, n ≤ m → H n ≤ H m := fun hnm =>
    toStrictMap_mono (iterElem_mono Oph hnm)
  have G_mono : ∀ {n m : ℕ}, n ≤ m → G n ≤ G m := fun hnm =>
    toStrictMap_mono (iterElem_mono Opg hnm)
  -- the algebraic core: `(u ∘ a ∘ j) ∘ (i ∘ b ∘ v) = u ∘ (a ∘ b) ∘ v` (uses `j ∘ i = I`).
  have key : ∀ (a : ApproximableMap (T.obj Dalg.carrier).sys (T.obj E).sys)
      (b : ApproximableMap (T.obj E).sys (T.obj Dalg.carrier).sys),
      (isoE.hom.comp (a.comp isoD.inv)).comp (isoD.hom.comp (b.comp isoE.inv))
        = isoE.hom.comp ((a.comp b).comp isoE.inv) := by
    intro a b
    rw [comp_assoc isoE.hom (a.comp isoD.inv) (isoD.hom.comp (b.comp isoE.inv)),
        comp_assoc a isoD.inv (isoD.hom.comp (b.comp isoE.inv)),
        ← comp_assoc isoD.inv isoD.hom (b.comp isoE.inv), hji, idMap_comp,
        ← comp_assoc a b isoE.inv]
  -- functoriality `T(p) ∘ T(q) = T(p ∘ q)` in `.comp` form.
  have hTcomp : ∀ (p : ApproximableMap Dalg.carrier.sys E.sys)
      (q : ApproximableMap E.sys Dalg.carrier.sys),
      (T.map (X := Dalg.carrier) (Y := E) p).comp (T.map (X := E) (Y := Dalg.carrier) q)
        = T.map (X := E) (Y := E) (p.comp q) :=
    fun p q => (T.map_comp (X := E) (Y := Dalg.carrier) (Z := E) p q).symm
  -- **the ladder**: `hₙ ∘ gₙ = kₙ`.
  have ladder : ∀ n, (H n).comp (G n) = K n := by
    intro n
    induction n with
    | zero =>
      apply ApproximableMap.ext
      intro X Z
      have hH0 : ∀ {P Q}, (H 0).rel P Q ↔ Dalg.carrier.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        show (toStrictMap (Oph.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hG0 : ∀ {P Q}, (G 0).rel P Q ↔ E.sys.mem P ∧ Q = Dalg.carrier.sys.master := by
        intro P Q
        show (toStrictMap (Opg.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hK0 : ∀ {P Q}, (K 0).rel P Q ↔ E.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        show (toStrictMap (Opk.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      constructor
      · rintro ⟨Y, hG, hHr⟩
        rw [hG0] at hG; rw [hH0] at hHr
        obtain ⟨hEX, rfl⟩ := hG
        obtain ⟨_, rfl⟩ := hHr
        rw [hK0]; exact ⟨hEX, rfl⟩
      · intro hK
        rw [hK0] at hK
        obtain ⟨hEX, rfl⟩ := hK
        exact ⟨Dalg.carrier.sys.master,
          (hG0).mpr ⟨hEX, rfl⟩, (hH0).mpr ⟨Dalg.carrier.sys.master_mem, rfl⟩⟩
    | succ n ih =>
      rw [H_succ n, G_succ n, key, K_succ n, hTcomp (H n) (G n), ih]
  -- the fixed-point maps and their `⊔`-decomposition.
  let hh := (toStrictMap Oph.fixElement).1
  let gg := (toStrictMap Opg.fixElement).1
  let kk := (toStrictMap Opk.fixElement).1
  have H_fix_rel : ∀ X Y, hh.rel X Y ↔ ∃ n, (H n).rel X Y := by
    intro X Y
    show (toStrictMap Oph.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Oph.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have G_fix_rel : ∀ X Y, gg.rel X Y ↔ ∃ n, (G n).rel X Y := by
    intro X Y
    show (toStrictMap Opg.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opg.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have K_fix_rel : ∀ X Y, kk.rel X Y ↔ ∃ n, (K n).rel X Y := by
    intro X Y
    show (toStrictMap Opk.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opk.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  -- `h ∘ g = k` (the diagonal of the doubly-indexed directed family, via the ladder).
  have hgk : hh.comp gg = kk := by
    apply ApproximableMap.ext
    intro X Z
    constructor
    · rintro ⟨Y, hgXY, hhYZ⟩
      rw [G_fix_rel] at hgXY
      rw [H_fix_rel] at hhYZ
      obtain ⟨m, hm⟩ := hgXY
      obtain ⟨n, hn⟩ := hhYZ
      rw [K_fix_rel]
      refine ⟨max m n, ?_⟩
      rw [← ladder (max m n)]
      exact ⟨Y, G_mono (le_max_left m n) X Y hm, H_mono (le_max_right m n) Y Z hn⟩
    · intro hk
      rw [K_fix_rel] at hk
      obtain ⟨p, hp⟩ := hk
      rw [← ladder p] at hp
      obtain ⟨Y, hG, hHr⟩ := hp
      exact ⟨Y, (G_fix_rel X Y).mpr ⟨p, hG⟩, (H_fix_rel Y Z).mpr ⟨p, hHr⟩⟩
  -- `k ⊑ I_E`, because `I_E` is a fixed point of `k ↦ u ∘ T(k) ∘ v`.
  have hk_le : kk ≤ idMap E.sys := by
    have hstepeq : (toStrictMap (Opk.toElementMap
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys)))).1
          = idMap E.sys := by
      have hs := opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))
      have hmapid : T.map (X := E) (Y := E) (idMap E.sys) = idMap (T.obj E).sys := T.map_id E
      rw [hs, show (toStrictMap (toStrictFilter
          (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))).1 = idMap E.sys from
          congrArg Subtype.val (toStrictMap_toStrictFilter _),
        hmapid, idMap_comp, huv]
    have hfp : Opk.toElementMap (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))
        = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
      calc Opk.toElementMap (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩)
          = toStrictFilter (toStrictMap (Opk.toElementMap
              (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩))) :=
            (toStrictFilter_toStrictMap _).symm
        _ = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
            congr 1
            apply Subtype.ext
            rw [hstepeq]
        _ = toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩ := rfl
    have hle : Opk.fixElement ≤ toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) :=
      fixElement_le_of_toElementMap_le Opk (le_of_eq hfp)
    have hmono := toStrictMap_mono hle
    show (toStrictMap Opk.fixElement).1 ≤ idMap E.sys
    refine le_of_le_of_eq hmono ?_
    exact congrArg Subtype.val (toStrictMap_toStrictFilter _)
  -- `h` and `g` are algebra homomorphisms.
  let Balg : TAlgebra T := ⟨E, isoE.hom⟩
  have h_fixeq : hh = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) hh).comp isoD.inv) := by
    have hs := opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE Oph.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have h_comm : hh.comp isoD.hom = isoE.hom.comp (T.map (X := Dalg.carrier) (Y := E) hh) := by
    conv_lhs => rw [h_fixeq]
    rw [comp_assoc, comp_assoc, hji, comp_idMap]
  let h_alg : AlgHom Dalg Balg := { hom := hh, comm := h_comm }
  have g_fixeq : gg = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) gg).comp isoE.inv) := by
    have hs := opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED Opg.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have g_comm : gg.comp isoE.hom = isoD.hom.comp (T.map (X := E) (Y := Dalg.carrier) gg) := by
    conv_lhs => rw [g_fixeq]
    rw [comp_assoc, comp_assoc, hvu, comp_idMap]
  let g_alg : AlgHom Balg Dalg := { hom := gg, comm := g_comm }
  -- `g ∘ h = I_D` by initiality of `D`.
  have hgh_id : gg.comp hh = idMap Dalg.carrier.sys := by
    have huniq : g_alg.comp h_alg = AlgHom.id Dalg := by
      rw [hinit.uniq Dalg (g_alg.comp h_alg), hinit.uniq Dalg (AlgHom.id Dalg)]
    exact congrArg AlgHom.hom huniq
  -- conclude via Lemma 6.15.
  exact trianglelefteq_of_projectionPair hh gg hgh_id (le_of_eq_of_le hgk hk_le)

end Scott1980.Neighborhood
