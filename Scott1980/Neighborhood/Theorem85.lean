import Scott1980.Neighborhood.Definition83

/-!
# Lecture VIII — Theorem 8.5 (Scott 1981, PRG-19): finitary projections via a step-closure formula

**Theorem 8.5.** For an approximable mapping `a : E → E` the following are equivalent:

(i) `a` is a finitary projection;

(ii) `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ X a X}`, for all `x ∈ |E|`.

## What is formalized here

The **`(ii) ⟹ (i)` direction** (`isFinitaryProjection_of_formula`) is proved in full, and is what
Theorem 8.6 actually needs: `sub`'s fixed points are *by definition* exactly the maps `a`
satisfying formula (ii), so characterising the range of `sub` only ever needs this direction.

The construction: from `a`, build `D := {X ∈ E ∣ X a X}` directly (`fixedNbhd`) — this is a genuine
subsystem `D ◁ E` **for any approximable map `a`** (`fixedNbhd_subsystem`), no hypothesis on `a`
needed for the neighbourhood-system axioms themselves. Formula (ii), unwound at principal elements
via `rel_iff_mem_principal`, says exactly that `a`'s relation matches Proposition 8.2's formula for
`D`: `a = retractionOfSubsystem (fixedNbhd_subsystem a)`. Proposition 8.2 (via Definition 8.3's
corollaries) then hands us `IsFinitaryProjection a` for free.

**The `(i) ⟹ (ii)` direction is *not* formalized in this file.** Scott's own proof needs a fact not
yet in the codebase: a section/retraction pair `i ⊣ j` (`j∘i = I_D`) built from the abstract
"isomorphic to a domain" witness of `IsFinitary` *reflects compactness* — if `i(w)` is a principal
(finite) element of `E` then `w` is already principal in `D`. (Scott's own remark: "`i(j(↑X)) = ↑X`
means `j(↑X)` is a finite element of `D`".) This is provable from existing machinery (`iSupDirected`/
`toElementMap_iSupDirected` give continuity of `i`, and `D`'s general algebraicity gives that every
element is a directed union of its principal approximants — a compact element equalling a directed
sup must already equal one of the sup's members), but assembling it is a standalone, comparably
sized effort to the rest of this file and is left as a documented follow-up; see `HANDOFF.md`.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}

/-- **The candidate subdomain of Theorem 8.5's proof, `D = {X ∈ E ∣ X a X}`.** Built for *any*
approximable map `a : E → E` — the neighbourhood-system axioms need only `mono`/`inter_right` of
`a`, no projection or finitary hypothesis. (This is also exactly Theorem 8.6's `Fix(sub)` predicate
`X sub(f) X`, restated for a single map `a` in place of the function-space token `f`.) -/
def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl

/-- **`fixedNbhd a ◁ E`, unconditionally.** The consistency clause is the same monotonicity +
intersectivity calculation as `fixedNbhd`'s own `inter_mem`, just without needing the extra
consistency witness `Z`. -/
theorem fixedNbhd_subsystem (a : ApproximableMap E E) : fixedNbhd a ◁ E where
  master_eq := rfl
  sub := fun h => h.1
  inter_closed := by
    rintro X Y ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ hEXY
    have h1 : a.rel (X ∩ Y) X := a.mono hXa Set.inter_subset_left subset_rfl hEXY hXE
    have h2 : a.rel (X ∩ Y) Y := a.mono hYa Set.inter_subset_right subset_rfl hEXY hYE
    exact ⟨hEXY, a.inter_right h1 h2⟩

/-- **Theorem 8.5, `(ii) ⟹ (i)` (Scott 1981, PRG-19).** If `a` satisfies Scott's step-closure
formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`, then `a` is a finitary projection.

The proof shows `a` literally *is* `retractionOfSubsystem` for `D = fixedNbhd a`: unwinding formula
(ii) at a principal `x = ↑X` via `rel_iff_mem_principal` reproduces exactly
`retractionOfSubsystem_rel`'s formula. Definition 8.3's corollaries of Proposition 8.2 then finish
the proof — no further work needed. -/
theorem isFinitaryProjection_of_formula (a : ApproximableMap E E)
    (hii : ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) :
    IsFinitaryProjection a := by
  have heq : a = Subsystem.retractionOfSubsystem (fixedNbhd_subsystem a) := by
    apply ApproximableMap.ext
    intro X Z
    rw [Subsystem.retractionOfSubsystem_rel]
    constructor
    · intro hr
      have hX : E.mem X := a.rel_dom hr
      have hmem : (a.toElementMap (E.principal hX)).mem Z := (a.rel_iff_mem_principal hX).mp hr
      obtain ⟨hZE, Y, hXY, hYZ, hYa⟩ := hii (E.principal hX) |>.mp hmem
      exact ⟨hX, hZE, Y, ⟨a.rel_dom hYa, hYa⟩, (E.mem_principal hX).mp hXY |>.2, hYZ⟩
    · rintro ⟨hX, hZ, Y, ⟨_, hYa⟩, hXY, hYZ⟩
      have hmem : (a.toElementMap (E.principal hX)).mem Z :=
        hii (E.principal hX) |>.mpr ⟨hZ, Y, (E.mem_principal hX).mpr ⟨a.rel_dom hYa, hXY⟩, hYZ, hYa⟩
      exact (a.rel_iff_mem_principal hX).mpr hmem
  rw [heq]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem a)

end Scott1980.Neighborhood
