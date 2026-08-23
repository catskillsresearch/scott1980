/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Scott 1981, Theorem 8.8 (Palomar statement of record)

Ground truth for the wording is `sources/PRG19.md`. Theorem 8.8 there is:

> The system \(\mathcal{U}\) is universal in the sense that, for every countable
> neighbourhood system \(\mathcal{D}\), we have
> \(\mathcal{D} \trianglelefteq \mathcal{U}\).

`𝒰` is Definition 8.7's neighbourhood system over `[0,1) ⊆ ℚ`: the non-empty
finite unions of rational intervals `[r,s)`. Scott's `⊴` (the prose before
Lemma 6.15) means *embeds as a subdomain*: `D ⊴ U` iff there is a `D'` with
`D ≅ D'` and `D' ◁ U`. The compared theorem is that statement; the library
proves it as `theorem_8_8` by assembling `theorem_8_8_a`.

This file imports only Mathlib. The proofs live in
`Scott1980/Neighborhood/*` and are compared against this file by Comparator
via `Solution.lean`.

## How to read this file

The definitions below are the vocabulary of the claim. A reader who wants to
check *what* has been proved should read this file and need not read the proof
development. `Solution.lean` imports the sorry-free library.
-/

namespace Scott1980.Neighborhood

/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a
token type `α`. -/
structure NeighborhoodSystem (α : Type*) where
  mem : Set α → Prop
  master : Set α
  master_mem : mem master
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.6.** An (ideal) *element*: a filter of neighbourhoods. -/
structure Element where
  mem : Set α → Prop
  sub : ∀ {X}, mem X → V.mem X
  master_mem : mem V.master
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

/-- Extensional equality of elements. -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  sorry

/-- Reflexivity of the filter-inclusion order. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X := by
  sorry

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X := by
  sorry

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y := by
  sorry

/-- Elements are ordered by inclusion of their membership predicates
(Definition 1.8). -/
instance : PartialOrder V.Element where
  le x y := ∀ X, x.mem X → y.mem X
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

end NeighborhoodSystem

/-- **Definition 1.9.** An order-isomorphism of the element domains. -/
abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

/-- Scott's `𝒟₀ ≅ 𝒟₁`. -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

/-- **Definition 6.10.** The subsystem (subdomain) relation `D ◁ E`. -/
structure Subsystem {α : Type*} (D E : NeighborhoodSystem α) : Prop where
  master_eq : D.master = E.master
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

/-- **Scott's `⊴` (prose before Lemma 6.15).** `D` embeds as a subdomain of `E`. -/
def Trianglelefteq {α β : Type*} (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

/-- The set presented by a list of interval endpoint-pairs. -/
def presentedIntervals (L : List (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ L, Set.Ico p.1 p.2

/-- Membership in Scott's universal family. -/
def UMem (X : Set ℚ) : Prop :=
  (∃ L : List (ℚ × ℚ), X = presentedIntervals L) ∧ X.Nonempty ∧ X ⊆ Set.Ico (0 : ℚ) 1

/-- Scott's master neighbourhood `Δ = [0,1)` for `𝒰`. -/
abbrev UMaster : Set ℚ := Set.Ico (0 : ℚ) 1

/-- `[0,1)` is a neighbourhood of `𝒰`. -/
theorem U_master_mem : UMem UMaster := by
  sorry

/-- Intersection of two presentable sets is presentable. -/
theorem U_inter_mem {X Y Z : Set ℚ} (hX : UMem X) (hY : UMem Y) (hZ : UMem Z)
    (hZsub : Z ⊆ X ∩ Y) : UMem (X ∩ Y) := by
  sorry

/-- Every `UMem` set is contained in `[0,1)`. -/
theorem U_sub_master {X : Set ℚ} (hX : UMem X) : X ⊆ UMaster := by
  sorry

/-- **Definition 8.7.** The universal neighbourhood system `𝒰` over `[0,1) ⊆ ℚ`. -/
def U : NeighborhoodSystem ℚ where
  mem := UMem
  master := UMaster
  master_mem := U_master_mem
  inter_mem := U_inter_mem
  sub_master := U_sub_master

/-- **Theorem 8.8 (Scott 1981, PRG-19), general half** (`sources/PRG19.md`):
*The system \(\mathcal{U}\) is universal in the sense that, for every countable
neighbourhood system \(\mathcal{D}\), we have \(\mathcal{D} \trianglelefteq \mathcal{U}\).* -/
theorem theorem_8_8.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  sorry

end Scott1980.Neighborhood
