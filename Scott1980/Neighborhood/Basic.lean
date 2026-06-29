import Mathlib.Data.Set.Basic
import Mathlib.Order.Hom.Basic

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
`sub_master` (every neighbourhood is a subset of `Δ`). The latter is what makes the principal
filter `↑X` (Definition 1.7) contain `Δ`, and underlies the least element `⊥ = ↑Δ`. -/
structure NeighborhoodSystem (α : Type*) where
  /-- `mem X` holds iff `X` is a neighbourhood of the system (`X ∈ 𝒟`). -/
  mem : Set α → Prop
  /-- Scott's distinguished least-informative neighbourhood `Δ`. -/
  master : Set α
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
forces `Z = ∅`, whence `X ∩ Y = ∅ = Z ∈ 𝒟`. The caller supplies `sub_master` (Scott's
`𝒟 ⊆ 𝒫(Δ)`) directly. -/
def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem := mem
  master := master
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
    (master_mem : mem master) (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    NeighborhoodSystem α where
  mem := mem
  master := master
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
    (master : Set α) (master_mem : mem master) (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_mem sub_master pos).IsPositive :=
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

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance : PartialOrder V.Element where
  le x y := ∀ X, x.mem X → y.mem X
  le_refl x X h := h
  le_trans x y z h1 h2 X h := h2 X (h1 X h)
  le_antisymm x y h1 h2 :=
    @Element.ext α V x y fun X => ⟨h1 X, h2 X⟩

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
