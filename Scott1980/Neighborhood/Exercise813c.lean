import Scott1980.Neighborhood.Exercise813b
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

/-!
## `8.13(c2)`: `generator`/`genPoint` realize the same free Boolean algebra

`8.13(b)`'s `Formula`/`evalV` already has one evaluation, `evalSet : Formula → Set ℕ`
(`var i ↦ generator i`). A *second* evaluation, `evalSet' : Formula → Set (ℕ → Bool)`
(`var i ↦ genPoint i`), is even simpler than the first: since Cantor space's own points
`x : ℕ → Bool` already *are* valuations, `mem_evalSet'_iff` needs no bit-encoding step (unlike
`8.13(b)`'s `mem_evalSet_iff`, which had to translate `n : ℕ` into a valuation via its bits) —
and consequently `semanticEquiv_iff_evalSet'_eq` needs no finitary agreement argument either.

`Corresponds X Y := ∃ φ, evalSet φ = X ∧ evalSet' φ = Y` witnesses, via a common `Formula`, that
`generator`'s algebra `{X | GeneratedBy generator X}` and `genPoint`'s algebra
`{Y | GeneratedBy genPoint Y}` are "the same" abstract Boolean algebra: `Corresponds` relates them
functionally in both directions (`exists_corresponds_of_generatedBy_generator/genPoint`,
`Corresponds.unique_left/right`) and respects `⊆` (`Corresponds.subset_iff`) — i.e. it is exactly
an order-isomorphism between the two concrete algebras, without needing any (nonexistent) bijection
of the wildly different underlying carriers `ℕ`/`ℕ → Bool`.
-/

/-- The *same* recursion as `evalSet`, but interpreted via `genPoint` instead of `generator`. -/
def evalSet' : Formula → Set (ℕ → Bool)
  | .var i => genPoint i
  | .bot => ∅
  | .top => Set.univ
  | .neg φ => (evalSet' φ)ᶜ
  | .and φ ψ => evalSet' φ ∩ evalSet' ψ
  | .or φ ψ => evalSet' φ ∪ evalSet' ψ

/-- Cantor space's own points already *are* valuations, so this bridge is definitional-level
simple: no bit-encoding step is needed (contrast `8.13(b)`'s `mem_evalSet_iff`). -/
theorem mem_evalSet'_iff (x : ℕ → Bool) (φ : Formula) :
    x ∈ evalSet' φ ↔ evalV x φ = true := by
  induction φ with
  | var i => simp [evalSet', evalV]
  | bot => simp [evalSet', evalV]
  | top => simp [evalSet', evalV]
  | neg φ ih => simp [evalSet', evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]

theorem generatedBy_iff_exists_evalSet' {Y : Set (ℕ → Bool)} :
    GeneratedBy genPoint Y ↔ ∃ φ : Formula, evalSet' φ = Y := by
  constructor
  · intro h
    induction h with
    | of i => exact ⟨.var i, rfl⟩
    | univ => exact ⟨.top, rfl⟩
    | @inter X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.and φ ψ, rfl⟩
    | @union X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.or φ ψ, rfl⟩
    | @compl X _ ih =>
      obtain ⟨φ, rfl⟩ := ih
      exact ⟨.neg φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    induction φ with
    | var i => exact GeneratedBy.of i
    | bot => simpa using GeneratedBy.univ.compl
    | top => exact GeneratedBy.univ
    | neg φ ih => exact ih.compl
    | and φ ψ ihφ ihψ => exact ihφ.inter ihψ
    | or φ ψ ihφ ihψ => exact ihφ.union ihψ

/-- No finitary agreement argument is needed here (contrast `8.13(b)`'s `semanticEquiv_iff_
evalSet_eq`): `evalV`'s own domain `ℕ → Bool` already *is* Cantor space's points. -/
theorem semanticEquiv_iff_evalSet'_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet' φ = evalSet' ψ := by
  constructor
  · intro h
    ext x
    rw [mem_evalSet'_iff, mem_evalSet'_iff, h]
  · intro h v
    have hmem : v ∈ evalSet' φ ↔ v ∈ evalSet' ψ := by rw [h]
    rw [mem_evalSet'_iff, mem_evalSet'_iff] at hmem
    rcases hφ : evalV v φ with - | - <;> rcases hψ : evalV v ψ with - | - <;> simp_all

/-- The same finitary-free argument as `semanticEquiv_iff_evalSet'_eq`, for entailment. -/
theorem entails_iff_evalSet'_subset {φ ψ : Formula} :
    Entails φ ψ ↔ evalSet' φ ⊆ evalSet' ψ := by
  constructor
  · intro h x hx
    rw [mem_evalSet'_iff] at hx ⊢
    exact h _ hx
  · intro h v hv
    exact (mem_evalSet'_iff v ψ).mp (h ((mem_evalSet'_iff v φ).mpr hv))

/-- `Lindenbaum`'s canonical map to Cantor-space clopens, the counterpart of `8.13(b)`'s
`Lindenbaum.toSet`. -/
def Lindenbaum.toSet' : Lindenbaum → Set (ℕ → Bool) :=
  Quotient.lift evalSet' fun _ _ h => semanticEquiv_iff_evalSet'_eq.mp h

@[simp] theorem Lindenbaum.toSet'_mk (φ : Formula) :
    Lindenbaum.toSet' ⟦φ⟧ = evalSet' φ := rfl

theorem Lindenbaum.toSet'_injective : Function.Injective Lindenbaum.toSet' := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet'_eq.mpr h)

theorem Lindenbaum.range_toSet' :
    Set.range Lindenbaum.toSet' = {Y | GeneratedBy genPoint Y} := by
  ext Y
  simp only [Set.mem_range, Set.mem_setOf_eq, generatedBy_iff_exists_evalSet']
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.ind with
    | _ φ => exact ⟨φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨⟦φ⟧, rfl⟩

/-- **`8.13(c2)`, the headline.** `X` and `Y` are the `evalSet`/`evalSet'` images of a *common*
`Formula` — i.e. the same node of the (unique, up to `SemanticEquiv`) Lindenbaum algebra. -/
def Corresponds (X : Set ℕ) (Y : Set (ℕ → Bool)) : Prop :=
  ∃ φ : Formula, evalSet φ = X ∧ evalSet' φ = Y

theorem exists_corresponds_of_generatedBy_generator {X : Set ℕ} (hX : GeneratedBy generator X) :
    ∃ Y, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet.mp hX
  exact ⟨evalSet' φ, φ, hφ, rfl⟩

theorem exists_corresponds_of_generatedBy_genPoint {Y : Set (ℕ → Bool)}
    (hY : GeneratedBy genPoint Y) : ∃ X, Corresponds X Y := by
  obtain ⟨φ, hφ⟩ := generatedBy_iff_exists_evalSet'.mp hY
  exact ⟨evalSet φ, φ, rfl, hφ⟩

theorem Corresponds.unique_right {X : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X Y₁) (h2 : Corresponds X Y₂) : Y₁ = Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet_eq.mpr (hφX.trans hψX.symm)
  rw [← hφY, ← hψY, semanticEquiv_iff_evalSet'_eq.mp hse]

theorem Corresponds.unique_left {X₁ X₂ : Set ℕ} {Y : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y) (h2 : Corresponds X₂ Y) : X₁ = X₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  have hse : SemanticEquiv φ ψ := semanticEquiv_iff_evalSet'_eq.mpr (hφY.trans hψY.symm)
  rw [← hφX, ← hψX, semanticEquiv_iff_evalSet_eq.mp hse]

/-- `Corresponds` also matches `⊆` — i.e. it is an order-isomorphism between the two concrete
algebras, not just a bijection. -/
theorem Corresponds.subset_iff {X₁ X₂ : Set ℕ} {Y₁ Y₂ : Set (ℕ → Bool)}
    (h1 : Corresponds X₁ Y₁) (h2 : Corresponds X₂ Y₂) : X₁ ⊆ X₂ ↔ Y₁ ⊆ Y₂ := by
  obtain ⟨φ, hφX, hφY⟩ := h1
  obtain ⟨ψ, hψX, hψY⟩ := h2
  subst hφX; subst hφY; subst hψX; subst hψY
  exact ⟨fun hsub => entails_iff_evalSet'_subset.mp (entails_iff_evalSet_subset.mpr hsub),
    fun hsub => entails_iff_evalSet_subset.mp (entails_iff_evalSet'_subset.mpr hsub)⟩

end Scott1980.Neighborhood
