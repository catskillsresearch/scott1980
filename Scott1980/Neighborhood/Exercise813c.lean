import Scott1980.Neighborhood.Exercise813a
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen

/-!
# Exercise 8.13(c) (Scott 1981, PRG-19, Lecture VIII) — connecting to Cantor space

> (For topologists.) Connect this representation of `𝒰` with the collection of non-empty open
> subsets of the product space `2^ℕ` (= Cantor space).

Per the scoping in `arxiv.md`, the literal "proper filters `≃o` non-empty opens" reading is
**false** (every filter contains `master`, so the naive map is constant); the mathematically
correct route lands on "opens" via the *dual* notion (**ideals**), decomposed into four subgoals
`8.13(c1)`–`(c4)`. This file carries `8.13(c1)`.

## `8.13(c1)`: Cantor space's clopen algebra is `GeneratedBy genPoint`

`genPoint i := {x : ℕ → Bool | x i = true}` is the literal transcription, on carrier `ℕ → Bool`,
of `8.13(a)`'s `generator i` (on carrier `ℕ`). The headline, `isClopen_iff_generatedBy_genPoint`,
identifies Cantor space's clopen algebra with `GeneratedBy genPoint` exactly:

* `⟸` (`generatedBy_genPoint_isClopen`) is easy structural induction: each `genPoint i` is clopen
  (preimage of a clopen singleton in discrete `Bool` under the continuous projection), and clopens
  are closed under the Boolean operations `GeneratedBy` builds with.
* `⟹` is the substantive direction, via compactness: every open `Y` is covered by `box`es
  (`box I f := {x | ∀ i ∈ I, x i = f i}`, one finite-support box per point of `Y`, from
  `isOpen_pi_iff` — Bool's discreteness lets us shrink to a singleton box at each coordinate) each
  contained in `Y`; each `box` is itself `GeneratedBy genPoint` (`generatedBy_genPoint_box`, by
  `Finset.induction_on`); `Y` clopen (hence compact, as Cantor space is a `CompactSpace`) extracts
  a **finite** subcover, so `Y` is a finite union of `box`es, hence `GeneratedBy genPoint` by
  `generatedBy_genPoint_biUnion`.

`isOpen_iff_iUnion_genPoint` records the immediate corollary that opens (not just clopens) are
exactly unions of `GeneratedBy genPoint` sets — the "topological basis" fact `8.13(c)`'s scoping
row anticipated, now free from the clopen identification.
-/

namespace Scott1980.Neighborhood

/-! ### `genPoint`: the coordinate-projection clopens of Cantor space -/

/-- The `i`-th coordinate-projection basic clopen of Cantor space `ℕ → Bool`: the literal
transcription, on this carrier, of `8.13(a)`'s `generator i`. -/
def genPoint (i : ℕ) : Set (ℕ → Bool) := (fun x : ℕ → Bool => x i) ⁻¹' {true}

@[simp] theorem mem_genPoint {i : ℕ} {x : ℕ → Bool} : x ∈ genPoint i ↔ x i = true := Iff.rfl

theorem isClopen_genPoint (i : ℕ) : IsClopen (genPoint i) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply i)

/-- `GeneratedBy genPoint ∅` — recorded separately since `GeneratedBy`'s only route to `∅` is via
`compl` of `univ`. -/
theorem generatedBy_genPoint_empty : GeneratedBy genPoint (∅ : Set (ℕ → Bool)) := by
  simpa using GeneratedBy.univ.compl

/-- **Easy direction**: everything `GeneratedBy genPoint` is clopen. -/
theorem generatedBy_genPoint_isClopen {Y : Set (ℕ → Bool)} (h : GeneratedBy genPoint Y) :
    IsClopen Y := by
  induction h with
  | of i => exact isClopen_genPoint i
  | univ => exact isClopen_univ
  | inter _ _ ih1 ih2 => exact ih1.inter ih2
  | union _ _ ih1 ih2 => exact ih1.union ih2
  | compl _ ih => exact ih.compl

theorem isOpen_genPoint (i : ℕ) : IsOpen (genPoint i) := (isClopen_genPoint i).isOpen

/-! ### `box`: finite-support basic clopens -/

/-- The basic clopen pinning every coordinate in `I` to match `f`, and leaving the rest free —
the standard basis element of the product topology on `ℕ → Bool`. -/
def box (I : Finset ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) := {x | ∀ i ∈ I, x i = f i}

@[simp] theorem mem_box {I : Finset ℕ} {f x : ℕ → Bool} :
    x ∈ box I f ↔ ∀ i ∈ I, x i = f i := Iff.rfl

theorem self_mem_box (I : Finset ℕ) (f : ℕ → Bool) : f ∈ box I f := fun _ _ => rfl

theorem generatedBy_genPoint_box (I : Finset ℕ) (f : ℕ → Bool) :
    GeneratedBy genPoint (box I f) := by
  induction I using Finset.induction_on with
  | empty => simpa [box] using GeneratedBy.univ
  | insert a s ha ih =>
    have hstep : box (insert a s) f =
        (if f a = true then genPoint a else (genPoint a)ᶜ) ∩ box s f := by
      ext x
      by_cases hfa : f a = true
      · simp [hfa]
      · have hfa' : f a = false := by simpa using hfa
        simp [hfa]
    rw [hstep]
    split_ifs with hfa
    · exact (GeneratedBy.of a).inter ih
    · exact (GeneratedBy.of a).compl.inter ih

theorem isOpen_box (I : Finset ℕ) (f : ℕ → Bool) : IsOpen (box I f) :=
  (generatedBy_genPoint_isClopen (generatedBy_genPoint_box I f)).isOpen

/-- Finite unions of `box`es (over any index type) are `GeneratedBy genPoint` — the same
`Finset.induction_on`/`Finset.set_biUnion_insert` idiom as `8.13(a)`'s `generatedBy_biUnion_affine`. -/
theorem generatedBy_genPoint_biUnion {β : Type*} (t : Finset β) (I : β → Finset ℕ)
    (f : β → ℕ → Bool) : GeneratedBy genPoint (⋃ b ∈ t, box (I b) (f b)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using generatedBy_genPoint_empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (generatedBy_genPoint_box _ _).union ih

/-! ### The headline: clopens are exactly `GeneratedBy genPoint` -/

/-- **`8.13(c1)`.** Cantor space's clopen algebra is exactly `GeneratedBy genPoint` — the free
Boolean algebra on `ℵ₀` generators (`8.13(a)`), transported to carrier `ℕ → Bool`. -/
theorem isClopen_iff_generatedBy_genPoint {Y : Set (ℕ → Bool)} :
    IsClopen Y ↔ GeneratedBy genPoint Y := by
  refine ⟨fun hY => ?_, generatedBy_genPoint_isClopen⟩
  classical
  have hbox : ∀ f ∈ Y, ∃ I : Finset ℕ, box I f ⊆ Y := by
    intro f hf
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hY.isOpen f hf
    refine ⟨I, fun x hx => hIu fun i hi => ?_⟩
    rw [hx i hi]
    exact (hu i hi).2
  choose Ifn hIfn using hbox
  set Ig : Y → Finset ℕ := fun f => Ifn (f : ℕ → Bool) f.2
  set fg : Y → ℕ → Bool := fun f => (f : ℕ → Bool)
  have hcover : Y ⊆ ⋃ f : Y, box (Ig f) (fg f) :=
    fun f hf => Set.mem_iUnion.mpr ⟨⟨f, hf⟩, self_mem_box _ _⟩
  have hcompact : IsCompact Y := hY.isClosed.isCompact
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun f : Y => box (Ig f) (fg f))
    (fun f => isOpen_box _ _) hcover
  have heq : Y = ⋃ f ∈ t, box (Ig f) (fg f) := by
    refine Set.Subset.antisymm ht (Set.iUnion₂_subset fun f _ => hIfn (f : ℕ → Bool) f.2)
  rw [heq]
  exact generatedBy_genPoint_biUnion t Ig fg

/-- Immediate corollary: **opens** (not just clopens) of Cantor space are exactly unions of
`GeneratedBy genPoint` clopens — the "topological basis" fact underlying the scoping row's
candidate `(ii)`. -/
theorem isOpen_iff_exists_iUnion_generatedBy {O : Set (ℕ → Bool)} :
    IsOpen O ↔ ∃ (S : Set (Set (ℕ → Bool))), (∀ Y ∈ S, GeneratedBy genPoint Y) ∧ O = ⋃ Y ∈ S, Y := by
  constructor
  · intro hO
    refine ⟨{Y | GeneratedBy genPoint Y ∧ Y ⊆ O}, fun Y hY => hY.1, ?_⟩
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hO x hx
      have hxbox : x ∈ box I x := self_mem_box I x
      exact ⟨box I x, ⟨generatedBy_genPoint_box I x,
        fun y hy => hIu fun i hi => by rw [hy i hi]; exact (hu i hi).2⟩, hxbox⟩
    · rintro ⟨Y, ⟨_, hYO⟩, hxY⟩
      exact hYO hxY
  · rintro ⟨S, hS, rfl⟩
    exact isOpen_biUnion fun Y hY => (generatedBy_genPoint_isClopen (hS Y hY)).isOpen

end Scott1980.Neighborhood
