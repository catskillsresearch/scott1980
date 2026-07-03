import Scott1980.Neighborhood.Theorem88b
import Scott1980.Neighborhood.RecursiveCross

/-!
# Theorem 8.8(b), Part 7 — a genuinely computable back-and-forth construction

Part 6 (`Theorem88c.lean`) showed Theorem 8.8(a)'s *classical* subsystem `D' = DprimeU` (built via
`splitChoice`) is effectively given as an abstract domain in its own right. That is **not** enough
for Part 7: `IsComputableMap` needs the *cross*-relation between `D'` and `U` — concretely,
`Yidx e n ⊆ UX m` — to be recursively enumerable, and `Yidx e n`'s actual position among `U`'s
rational intervals is, by construction, whatever `Classical.choice` happened to pick. There is no
effective handle on it at all, so no relation mentioning it can be shown r.e.

This file therefore builds a **fresh, genuinely computable** back-and-forth construction,
replacing Theorem 8.8(a)'s abstract, `Set`-valued splitting recursion (`Theorem88.lean`'s
`atomU`/`split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ`) with one that works **natively on `U`-codes**
throughout, so that at every step there is an actual `ℕ`-code in hand — never a `Set ℚ` value
conjured by choice.

## Why the original `atomUCode`/`splitEff` plan failed, and how this one differs

The design pitfall recorded in `HANDOFF.md` (2026-07-02) was: to reuse `Theorem88.lean`'s *generic*
apparatus, `split` must be a **total function of `Set`s** (`Set α → Set ℚ → Set α → Set ℚ × Set ℚ`).
Given only a *set* `B`, there is no way to effectively recover "the" code for it (`canonCode` is not
unique-per-set, so `splitULeft`/`splitURight` — which key off a code's specific first interval — can
give different answers for different codes of the same set). Any attempt to define `splitEff` as a
function of `B : Set ℚ` alone (e.g. via `Classical.choice`/`Nat.find` to pick a representative code)
is therefore not provably the same split an independently-built code tracker would compute.

**This file sidesteps the problem instead of solving it**: it never builds a `Set`-valued `split`
function at all, and does not reuse `Theorem88.lean`'s generic `atomU`/`Yseq`/`transfer_*` machinery.
Instead, the entire back-and-forth recursion is defined **natively as a `Nat.Primrec` function of
`(depth, sign-sequence-code)`**, carrying an explicit `U`-code as part of its state from the very
first step — so "which code represents `B`" is never a question, only ever "the code my own
recursion already computed". The three ingredients, all already built:

* Part 4 (`SplitU.lean`): `splitULeft`/`splitURight`, a deterministic, `Nat.Primrec` midpoint split
  of *any* `U`-code, with `UX_splitULeft`/`UX_splitURight` holding **unconditionally** (no side
  conditions on the input code) — this is what makes composing it across recursion steps trivial.
* Part 5 (`DAtomDecidable.lean`): `DAtom_recDecidable (P0 P)`, deciding whether a finite Boolean
  atom-constraint on `D`'s neighbourhoods is empty, extracted as a genuine `Nat.Primrec` function.
* `DAtom`'s monotonicity under adding constraints (`DAtom (i :: pos) neg ⊆ DAtom pos neg`, via
  `IPos_cons`): once a `(pos, neg)`-atom is detected empty, every further extension of it is
  automatically detected empty too, by the *same* decider, with **no extra "already empty" flag
  needed** in the recursion state.

## Status

This file lays the **foundational recursion** (`atomUCode`, `Nat.Primrec`), its **per-step `D`-side
correctness** (`genAtom_atomUCode`), and now **Theorem 8.8(b)(vii)(1), the full `atomUCode`
invariant**: `atomUCode_mem` (validity, unconditional — `UX` is a total surjection onto `U`'s
neighbourhoods, so this needs no emptiness hypothesis at all, unlike `Theorem88.lean`'s `atomU`) and
`atomUCode_disjoint` (atoms for bit-sources disagreeing below depth `n`, and *both* still `D`-side
non-empty, are `U`-side disjoint). The restriction to non-empty atoms is unavoidable and harmless:
`atomUCode_eq_zero_of_empty` shows a once-empty atom's code freezes at the junk value `0` forever, so
every junk atom aliases to the same `UX 0` — disjointness genuinely fails there, but `(vii)(2)`'s
`YseqCode` filters junk `k`'s out of its union, so this restricted invariant is exactly what is
needed downstream.

The remaining assembly (Part 7b: a `Yseq`-analogue as a *union* over `2ⁿ` such atoms, disjointness,
subset/intersection transfer, `D''`'s `NeighborhoodSystem`/`ComputablePresentation`,
`D ≅ᴰ D''`/`D'' ◁ U`; Part 7c: `IsComputableMap` itself) is **not yet done** — see `HANDOFF.md` for
the detailed continuation plan. Nothing in this file is a placeholder or `sorry`; everything proved
here is a real, checked, reusable building block for that continuation.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## Union of two `U`-codes via `appendCode` (list concatenation, up to order) -/

theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

theorem presentedIntervals_decodeQPairList_appendCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (appendCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∪ presentedIntervals (decodeQPairList c2) := by
  ext x
  simp only [mem_presentedIntervals, Set.mem_union]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rcases (mem_decodeQPairList_appendCode c1 c2 p).mp hp with hp' | hp'
    · exact Or.inl ⟨p, hp', h1, h2⟩
    · exact Or.inr ⟨p, hp', h1, h2⟩
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inl hp), h1, h2⟩
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inr hp), h1, h2⟩

/-- **`unionUX n m` codes `UX n ∪ UX m`.** Canonicalizes both inputs first (mirroring `Uinter`),
then concatenates; the result is always a genuine `U`-neighbourhood since a union of two such is
again presentable, non-empty, and `⊆ [0,1)`. -/
def unionUX (n m : ℕ) : ℕ := appendCode (canonCode n) (canonCode m)

theorem primrec_unionUX : Nat.Primrec (fun t : ℕ => unionUX t.unpair.1 t.unpair.2) := by
  unfold unionUX
  exact (primrec_appendCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem U_mem_union_UX (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨-, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨-, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨decodeQPairList (canonCode n) ++ decodeQPairList (canonCode m),
      (presentedIntervals_append _ _).symm⟩, hne1.mono Set.subset_union_left,
    Set.union_subset hsub1 hsub2⟩

theorem UX_unionUX (n m : ℕ) : UX (unionUX n m) = UX n ∪ UX m := by
  have hmem : U.mem (presentedIntervals (decodeQPairList (appendCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_appendCode]; exact U_mem_union_UX n m
  show presentedIntervals (decodeQPairList (canonCode (unionUX n m))) = UX n ∪ UX m
  unfold unionUX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hmem,
    presentedIntervals_decodeQPairList_appendCode]
  rfl

/-! ## The code-native atom recursion

Fix `P : ComputablePresentation D` and work relative to `P0 P` (Part 6b's re-pointed presentation,
`(P0 P).X 0 = D.master`). The recursion state at depth `n`, for a fixed bit-source `k` (`k`'s bit
`y` records the sign `δ y ∈ {true, false}` of the depth-`y` step), is packed as

`pair remK (pair posC (pair negC uCode))`

where `remK` is the *unconsumed* suffix of `k` (peeled one bit at a time via `/2`, avoiding the need
for a general `Nat.Primrec` division-by-`2^y`), `posC`/`negC` are `encodeList`-style codes for the
accumulated positive/negative index lists (Part 6c's `posnegList`, built by **prepending** instead
of appending — harmless, since `DAtom`/`IPos` only ever care about list *membership*), and `uCode`
is the `U`-code of the matching `U`-side atom (meaningful only when the `D`-side atom is
non-empty). -/

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

/-- Extract the current depth `y` from a packed step-input `w = pair k (pair y state)`. -/
def wY (w : ℕ) : ℕ := w.unpair.2.unpair.1

/-- Extract the packed `(remK, posC, negC, uCode)` state from `w = pair k (pair y state)`. -/
def wState (w : ℕ) : ℕ := w.unpair.2.unpair.2

def stateRem (s : ℕ) : ℕ := s.unpair.1
def statePos (s : ℕ) : ℕ := s.unpair.2.unpair.1
def stateNeg (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.1
def stateCode (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.2

theorem primrec_wY : Nat.Primrec wY := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_wState : Nat.Primrec wState := Nat.Primrec.right.comp Nat.Primrec.right
theorem primrec_stateRem : Nat.Primrec stateRem := Nat.Primrec.left
theorem primrec_statePos : Nat.Primrec statePos := Nat.Primrec.left.comp Nat.Primrec.right
theorem primrec_stateNeg : Nat.Primrec stateNeg :=
  Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
theorem primrec_stateCode : Nat.Primrec stateCode :=
  Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)

/-- Pack `(remK, posC, negC, uCode)` into a single state code. -/
def packState (remK posC negC uCode : ℕ) : ℕ := Nat.pair remK (Nat.pair posC (Nat.pair negC uCode))

@[simp] theorem stateRem_packState (a b c d : ℕ) : stateRem (packState a b c d) = a := by
  unfold stateRem packState; simp only [unpair_pair_fst]
@[simp] theorem statePos_packState (a b c d : ℕ) : statePos (packState a b c d) = b := by
  unfold statePos packState; simp only [unpair_pair_fst, unpair_pair_snd]
@[simp] theorem stateNeg_packState (a b c d : ℕ) : stateNeg (packState a b c d) = c := by
  unfold stateNeg packState; simp only [unpair_pair_fst, unpair_pair_snd]
@[simp] theorem stateCode_packState (a b c d : ℕ) : stateCode (packState a b c d) = d := by
  unfold stateCode packState; simp only [unpair_pair_fst, unpair_pair_snd]

/-- The initial state at depth `0`: no constraints yet (`posC = negC = 0`, the empty-list code),
`U`-side code is `U.master`'s (`UmasterIdx`), and the unconsumed bit-source is the whole of `k`. -/
def atomBase (k : ℕ) : ℕ := packState k 0 0 UmasterIdx

theorem primrec_atomBase : Nat.Primrec atomBase :=
  ((Nat.Primrec.id).pair ((Nat.Primrec.const 0).pair
    ((Nat.Primrec.const 0).pair (Nat.Primrec.const UmasterIdx)))).of_eq fun k => by
    unfold atomBase packState; simp only [id_eq]

/-- **The per-step state transition.** `datomDec` should be `DAtom_recDecidable (P0 P)`'s extracted
decider (`datomDec (pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅`);
kept abstract here so `Nat.Primrec`-ness can be proved once and reused. `bit := remK % 2`, then:
`posC' := pair y posC + 1` / `negC' := pair y negC + 1` are the candidate accumulators with the
current index `y` prepended; `emptyI`/`emptyJ` decide whether the "+"/"-"-refinements are already
`D`-side empty; the new `U`-code either stays `0` (junk, `D`-side empty), is carried over unchanged
(the refinement equals the old atom outright), or is `splitULeft`/`splitURight` of the old code
(a genuine split). -/
def atomStep (datomDec : ℕ → ℕ) (w : ℕ) : ℕ :=
  let y := wY w
  let s := wState w
  let bit := stateRem s % 2
  let posC' := Nat.pair y (statePos s) + 1
  let negC' := Nat.pair y (stateNeg s) + 1
  let emptyI := datomDec (Nat.pair posC' (stateNeg s))
  let emptyJ := datomDec (Nat.pair (statePos s) negC')
  packState (stateRem s / 2) (selectFn bit posC' (statePos s)) (selectFn bit (stateNeg s) negC')
    (selectFn bit
      (selectFn emptyI 0 (selectFn emptyJ (stateCode s) (splitULeft (stateCode s))))
      (selectFn emptyJ 0 (selectFn emptyI (stateCode s) (splitURight (stateCode s)))))

theorem primrec_atomStep {datomDec : ℕ → ℕ} (hd : Nat.Primrec datomDec) :
    Nat.Primrec (atomStep datomDec) := by
  have hy : Nat.Primrec wY := primrec_wY
  have hs : Nat.Primrec wState := primrec_wState
  have hrem : Nat.Primrec (fun w => stateRem (wState w)) := primrec_stateRem.comp hs
  have hpos : Nat.Primrec (fun w => statePos (wState w)) := primrec_statePos.comp hs
  have hneg : Nat.Primrec (fun w => stateNeg (wState w)) := primrec_stateNeg.comp hs
  have hcode : Nat.Primrec (fun w => stateCode (wState w)) := primrec_stateCode.comp hs
  have hbit : Nat.Primrec (fun w => stateRem (wState w) % 2) := primrec_mod2.comp hrem
  have hposC' : Nat.Primrec (fun w => Nat.pair (wY w) (statePos (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hpos)
  have hnegC' : Nat.Primrec (fun w => Nat.pair (wY w) (stateNeg (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hneg)
  have hemptyI : Nat.Primrec (fun w => datomDec (Nat.pair
      (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w)))) :=
    hd.comp (hposC'.pair hneg)
  have hemptyJ : Nat.Primrec (fun w => datomDec (Nat.pair (statePos (wState w))
      (Nat.pair (wY w) (stateNeg (wState w)) + 1))) :=
    hd.comp (hpos.pair hnegC')
  have hsplitL : Nat.Primrec (fun w => splitULeft (stateCode (wState w))) :=
    primrec_splitULeft.comp hcode
  have hsplitR : Nat.Primrec (fun w => splitURight (stateCode (wState w))) :=
    primrec_splitURight.comp hcode
  have hcodeBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
        0 (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) (stateCode (wState w)) (splitULeft (stateCode (wState w)))))
      (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) 0
        (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
          (stateCode (wState w)) (splitURight (stateCode (wState w)))))) :=
    primrec_selectFn hbit
      (primrec_selectFn hemptyI (Nat.Primrec.const 0) (primrec_selectFn hemptyJ hcode hsplitL))
      (primrec_selectFn hemptyJ (Nat.Primrec.const 0) (primrec_selectFn hemptyI hcode hsplitR))
  have hrem' : Nat.Primrec (fun w => stateRem (wState w) / 2) := primrec_div2.comp hrem
  have hposBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (Nat.pair (wY w) (statePos (wState w)) + 1) (statePos (wState w))) :=
    primrec_selectFn hbit hposC' hpos
  have hnegBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (stateNeg (wState w)) (Nat.pair (wY w) (stateNeg (wState w)) + 1)) :=
    primrec_selectFn hbit hneg hnegC'
  exact (hrem'.pair (hposBranch.pair (hnegBranch.pair hcodeBranch))).of_eq fun w => by
    unfold atomStep packState
    simp only []

end AtomCode

/-! ## Instantiating at `datomDec := DAtom_recDecidable (P0 P)`'s extracted decider -/

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The extracted `D`-atom-emptiness decider for `P0 P`.** Obtained non-constructively
(`Classical.choice`, via `RecDecidable`'s bare existential) from `DAtom_recDecidable (P0 P)`; the
resulting *function* is exactly as computable as any other `Nat.Primrec` function in this
codebase — only *naming* it needs choice, mirroring `DprimeUPresentation`'s own `noncomputable`.
Wrapped in `isOne` so the result is *literally* `{0,1}`-valued (not just "`= 1` iff ..."): `(vii)(1)`'s
`selectFn`-based case analysis on `emptyI`/`emptyJ` needs the *exact* value `0` on the false side, not
merely `≠ 1` (`selectFn`, unlike a genuine `if`, is only well-behaved on a literal `0`/`1` condition). -/
noncomputable def datomDec : ℕ → ℕ := fun n => isOne ((DAtom_recDecidable (P0 P)).choose n)

theorem primrec_datomDec : Nat.Primrec (datomDec P) :=
  (primrec_isOne.comp (DAtom_recDecidable (P0 P)).choose_spec.1).of_eq fun _ => rfl

theorem datomDec_spec (posC negC : ℕ) :
    datomDec P (Nat.pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅ := by
  unfold datomDec
  rw [isOne_eq_one_iff]
  have h := (DAtom_recDecidable (P0 P)).choose_spec.2 (Nat.pair posC negC)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem datomDec_le_one (n : ℕ) : datomDec P n ≤ 1 := by unfold datomDec; exact isOne_le_one _

/-- The complementary fact to `datomDec_spec`: whenever the `D`-side atom is *non*-empty,
`datomDec` reads out exactly `0` (not just "`≠ 1`") — needed so `selectFn`'s zero-branch actually
fires in the per-step unfoldings below. -/
theorem datomDec_eq_zero (posC negC : ℕ) (h : DAtom (P0 P) (decodeList posC) (decodeList negC) ≠ ∅) :
    datomDec P (Nat.pair posC negC) = 0 := by
  have hle := datomDec_le_one P (Nat.pair posC negC)
  have hne : datomDec P (Nat.pair posC negC) ≠ 1 := fun he => h ((datomDec_spec P posC negC).mp he)
  omega

/-- **The full state recursion**, packing `atomBase`/`atomStep (datomDec P)` via `Nat.Primrec.prec`:
`atomUCodeState P (pair k n)` is the depth-`n` state for bit-source `k`. -/
noncomputable def atomUCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomBase t.unpair.1) (fun y IH => atomStep (datomDec P) (Nat.pair t.unpair.1 (Nat.pair y IH)))

theorem primrec_atomUCodeState : Nat.Primrec (atomUCodeState P) :=
  (Nat.Primrec.prec primrec_atomBase (primrec_atomStep (primrec_datomDec P))).of_eq fun t => rfl

/-- **The depth-`n` accumulated positive-index code**, for bit-source `k`. -/
noncomputable def atomUPos (n k : ℕ) : ℕ := statePos (atomUCodeState P (Nat.pair k n))
/-- **The depth-`n` accumulated negative-index code**, for bit-source `k`. -/
noncomputable def atomUNeg (n k : ℕ) : ℕ := stateNeg (atomUCodeState P (Nat.pair k n))
/-- **The depth-`n` `U`-side code**, for bit-source `k` (meaningful exactly when the matching
`D`-side atom, `DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))`, is
non-empty — see `genAtom_atomUCode` below). -/
noncomputable def atomUCode (n k : ℕ) : ℕ := stateCode (atomUCodeState P (Nat.pair k n))

theorem primrec_atomUPos : Nat.Primrec (fun t : ℕ => atomUPos P t.unpair.1 t.unpair.2) :=
  (primrec_statePos.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUNeg : Nat.Primrec (fun t : ℕ => atomUNeg P t.unpair.1 t.unpair.2) :=
  (primrec_stateNeg.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUCode : Nat.Primrec (fun t : ℕ => atomUCode P t.unpair.1 t.unpair.2) :=
  (primrec_stateCode.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

/-! ## Per-step correctness: the `D`-side atom is tracked exactly -/

/-- `DAtom` gains a positive constraint by intersecting with `idxSet`, prepended. -/
theorem DAtom_cons_pos (Q : ComputablePresentation D) (i : ℕ) (pos neg : List ℕ) :
    DAtom Q (i :: pos) neg = idxSet Q.X i ∩ DAtom Q pos neg := by
  unfold DAtom; rw [IPos_cons, Set.inter_assoc]

/-- `DAtom` gains a negative constraint by intersecting with the complement of `idxSet`, prepended. -/
theorem DAtom_cons_neg (Q : ComputablePresentation D) (j : ℕ) (pos neg : List ℕ) :
    DAtom Q pos (j :: neg) = (Set.univ \ idxSet Q.X j) ∩ DAtom Q pos neg := by
  ext m
  simp only [mem_DAtom, List.mem_cons, Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, true_and,
    mem_idxSet]
  constructor
  · rintro ⟨hpos, hneg⟩
    exact ⟨hneg j (Or.inl rfl), hpos, fun i hi => hneg i (Or.inr hi)⟩
  · rintro ⟨hj, hpos, hneg⟩
    exact ⟨hpos, fun i hi => hi.elim (fun h => h ▸ hj) (hneg i)⟩

/-- **The bit-sequence associated to a bit-source `k`**: `deltaOf k i = true` iff bit `i` of `k`
(read low-bit-first, matching `atomStep`'s `remK % 2`/`remK / 2` peeling) is `1`. -/
def deltaOf (k : ℕ) : ℕ → Bool := fun i => decide ((k / 2 ^ i) % 2 = 1)

/-- **Unfolding `atomUCodeState` one step.** -/
theorem atomUCodeState_succ (k n : ℕ) :
    atomUCodeState P (Nat.pair k (n + 1)) =
      atomStep (datomDec P) (Nat.pair k (Nat.pair n (atomUCodeState P (Nat.pair k n)))) := by
  unfold atomUCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- The unconsumed bit-source at depth `n` is exactly `k / 2 ^ n` (peeled one bit at a time). -/
theorem stateRem_atomUCodeState (k n : ℕ) : stateRem (atomUCodeState P (Nat.pair k n)) = k / 2 ^ n := by
  induction n with
  | zero => simp [atomUCodeState, atomBase]
  | succ n ih =>
    rw [atomUCodeState_succ]
    unfold atomStep
    simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateRem_packState, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

theorem deltaOf_eq_true_iff (k i : ℕ) : deltaOf k i = true ↔ (k / 2 ^ i) % 2 = 1 := by
  unfold deltaOf; simp

/-- `atomUPos`/`atomUNeg` step by prepending the new index `n` on whichever side `deltaOf k n`
selects, exactly mirroring `genAtom`'s own step. -/
theorem atomUPos_succ (k n : ℕ) :
    atomUPos P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (Nat.pair n (atomUPos P n k) + 1) (atomUPos P n k) := by
  unfold atomUPos
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, statePos_packState,
    stateRem_atomUCodeState]

theorem atomUNeg_succ (k n : ℕ) :
    atomUNeg P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (atomUNeg P n k) (Nat.pair n (atomUNeg P n k) + 1) := by
  unfold atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateNeg_packState,
    stateRem_atomUCodeState]

/-- **Per-step `D`-side correctness.** The accumulated `(pos, neg)` code pair at depth `n`, for
bit-source `k`, tracks exactly the same atom as `genAtom (idxSet (e P)) Set.univ (deltaOf k) n`. -/
theorem genAtom_atomUCode (k : ℕ) :
    ∀ n, genAtom (idxSet (e P)) Set.univ (deltaOf k) n
      = DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
  intro n
  induction n with
  | zero =>
    simp [genAtom, atomUPos, atomUNeg, atomUCodeState, atomBase, DAtom, decodeList_zero, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hbit1 : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp hδ
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit1, selectFn_one, selectFn_one,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos, Set.inter_comm]
    · have hbit0 : (k / 2 ^ n) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos ((k / 2 ^ n) % 2) with h | h
        · exact h
        · exact absurd ((deltaOf_eq_true_iff k n).mpr (by omega)) (by simp [hδ])
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit0, selectFn_zero, selectFn_zero,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg, Set.inter_comm]

/-! ## Theorem 8.8(b)(vii)(1) — the `atomUCode` invariant

Unlike `Theorem88.lean`'s `atomU` (valued in genuine `Set ℚ`, where `∅` is an honest value),
`UX : ℕ → Set ℚ` is a **total surjection onto `U`'s neighbourhoods** (`U_mem_UX`, unconditional:
`canonCode`'s degenerate-input fallback is `U.master`, never `∅`) — no code represents the empty
set. So the right invariant here is *not* `atomU_invariant`'s emptiness-matching clause "(■)"
verbatim; instead:

* **validity** holds completely for free, for *every* code (`U_mem_UX`), empty match or not;
* **disjointness** only holds, and only needs to hold, between two atoms that are *both* still
  `D`-side non-empty (`atomUEmpty = 0`) — once a bit-source's atom goes empty its code is frozen at
  the junk value `0` forever (`atomUCode_eq_zero_of_empty` below), and *all* junk atoms alias to the
  same `UX 0`, so disjointness genuinely fails between two junk atoms (or junk vs. non-junk) and must
  be excluded; `(vii)(2)`'s `YseqCode` filters junk `k`'s out of its union, so this restricted
  disjointness is exactly what is needed downstream. -/

/-- **`D`-side atom emptiness at depth `n`, for bit-source `k`** — `1` iff the accumulated
`(pos, neg)` constraint pair already denotes the empty `D`-index atom. -/
noncomputable def atomUEmpty (n k : ℕ) : ℕ := datomDec P (Nat.pair (atomUPos P n k) (atomUNeg P n k))

theorem atomUEmpty_eq_one_iff (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
  datomDec_spec P _ _

/-- **`atomUEmpty` reads off `genAtom`'s own emptiness**, via `genAtom_atomUCode`. -/
theorem atomUEmpty_eq_one_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n = ∅ := by
  rw [atomUEmpty_eq_one_iff, ← genAtom_atomUCode]

theorem atomUEmpty_eq_zero_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 0 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n ≠ ∅ := by
  have hle : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
  have h1 := atomUEmpty_eq_one_iff_genAtom P n k
  constructor
  · intro h0 hempty; exact absurd (h1.mpr hempty) (by omega)
  · intro hne; by_contra h0; exact hne (h1.mp (by omega))

/-! ### The zero-depth base case, unconditionally (no dependence on `k`) -/

theorem atomUPos_zero (k : ℕ) : atomUPos P 0 k = 0 := by
  simp [atomUPos, atomUCodeState, atomBase]

theorem atomUNeg_zero (k : ℕ) : atomUNeg P 0 k = 0 := by
  simp [atomUNeg, atomUCodeState, atomBase]

theorem atomUCode_zero (k : ℕ) : atomUCode P 0 k = UmasterIdx := by
  simp [atomUCode, atomUCodeState, atomBase]

/-! ### Unfolding the `U`-side code one step

Mirrors `atomUPos_succ`/`atomUNeg_succ`: `atomUCode P (n+1) k` is a nested `selectFn` on the actual
bit `(k / 2^n) % 2` and the *two* hypothetical extension-emptiness checks (whichever the actual bit
picks decides `0`-vs-carry-vs-split; the *other* is exactly the sibling's own `atomUEmpty` at depth
`n+1`, which is what powers the disjointness argument below). -/
theorem atomUCode_succ (k n : ℕ) :
    atomUCode P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))) 0
          (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)))
            (atomUCode P n k) (splitULeft (atomUCode P n k))))
        (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) 0
          (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
            (atomUCode P n k) (splitURight (atomUCode P n k)))) := by
  unfold atomUCode atomUPos atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateCode_packState,
    stateRem_atomUCodeState]

/-- The two hypothetical checks appearing in `atomUCode_succ` are exactly `atomUEmpty` at depth
`n + 1`, evaluated at whichever of the two bit-sources through `n` realizes each hypothesis. In
particular, for the *actual* bit-source `k` itself: whichever branch `(k/2^n)%2` selects reproduces
`atomUEmpty P (n+1) k` verbatim. -/
theorem atomUEmpty_succ (k n : ℕ) :
    atomUEmpty P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
        (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) := by
  unfold atomUEmpty
  rw [atomUPos_succ, atomUNeg_succ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp only [hbit, selectFn_zero, selectFn_one]

/-! ### Congruence: the recursion depends only on `deltaOf k`'s first `n` bits -/

/-- **Congruence for the whole packed triple**: bit-sources agreeing on `deltaOf` below `n` produce
identical `(pos, neg, code)` triples at depth `n` — the code-level analogue of `genAtom_congr`/
`atomU_congr`, proved jointly (the three components interact through `atomUCode_succ`'s two
`datomDec` checks, which read `atomUPos`/`atomUNeg` at depth `n`). -/
theorem atomUCodeState_congr {n : ℕ} :
    ∀ {k k' : ℕ}, (∀ i < n, deltaOf k i = deltaOf k' i) →
      atomUPos P n k = atomUPos P n k' ∧ atomUNeg P n k = atomUNeg P n k' ∧
        atomUCode P n k = atomUCode P n k' := by
  induction n with
  | zero =>
    intro k k' _
    exact ⟨(atomUPos_zero P k).trans (atomUPos_zero P k').symm,
      (atomUNeg_zero P k).trans (atomUNeg_zero P k').symm,
      (atomUCode_zero P k).trans (atomUCode_zero P k').symm⟩
  | succ n ih =>
    intro k k' h
    obtain ⟨ihpos, ihneg, ihcode⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hbit : (k / 2 ^ n) % 2 = (k' / 2 ^ n) % 2 := by
      have hh := h n (Nat.lt_succ_self n)
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with h2 | h2 <;>
          simp_all [deltaOf]
    refine ⟨?_, ?_, ?_⟩
    · rw [atomUPos_succ, atomUPos_succ, ihpos, hbit]
    · rw [atomUNeg_succ, atomUNeg_succ, ihneg, hbit]
    · rw [atomUCode_succ, atomUCode_succ, ihpos, ihneg, ihcode, hbit]

theorem atomUEmpty_congr {n k k' : ℕ} (h : ∀ i < n, deltaOf k i = deltaOf k' i) :
    atomUEmpty P n k = atomUEmpty P n k' := by
  obtain ⟨hpos, hneg, -⟩ := atomUCodeState_congr P h
  unfold atomUEmpty
  rw [hpos, hneg]

/-! ### Validity: every code is a genuine `U`-neighbourhood, unconditionally -/

/-- **Validity**, the free half of the invariant: `UX` never needs an emptiness hypothesis at all. -/
theorem atomUCode_mem (n k : ℕ) : U.mem (UX (atomUCode P n k)) := U_mem_UX _

/-! ### Junk propagates: once empty, `atomUCode` is frozen at `0` forever -/

theorem genAtom_succ_subset (k n : ℕ) :
    genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) ⊆
      genAtom (idxSet (e P)) Set.univ (deltaOf k) n :=
  Set.inter_subset_left

theorem atomUEmpty_mono {n k : ℕ} (h : atomUEmpty P n k = 1) : atomUEmpty P (n + 1) k = 1 := by
  rw [atomUEmpty_eq_one_iff_genAtom] at h ⊢
  exact Set.subset_eq_empty (genAtom_succ_subset P k n) h

theorem atomUEmpty_zero_of_succ {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) : atomUEmpty P n k = 0 := by
  by_contra hne
  have hle := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  have h1 : atomUEmpty P n k = 1 := by unfold atomUEmpty at hne hle ⊢; omega
  exact absurd (atomUEmpty_mono P h1) (by omega)

/-- **Junk is frozen at `0`.** Once a bit-source's `D`-side atom is empty, its `U`-code stays `0`
forever after (both hypothetical continuations of an already-empty atom are themselves empty, so
`atomUCode_succ`'s outer `selectFn` always lands on its `0` branch). -/
theorem atomUCode_eq_zero_of_empty {n k : ℕ} (h : atomUEmpty P n k = 1) :
    atomUCode P (n + 1) k = 0 := by
  have hemp : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
    (atomUEmpty_eq_one_iff P n k).mp h
  have hI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  have hJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  rw [atomUCode_succ, hI, hJ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp [hbit, selectFn_zero, selectFn_one]

/-- **Monotonicity**: as long as the depth-`(n+1)` atom is still non-empty, its `U`-code's
neighbourhood shrinks from (or coincides with) the depth-`n` one — either the "carry unchanged"
branch fires (equality) or a genuine `splitULeft`/`splitURight` fires (strict `⊆`, `UX_splitULeft`/
`UX_splitURight`). Mirrors `split_fst_subset`/`split_snd_subset` from the abstract `Theorem88.lean`
account, but unconditionally true here since `splitULeft`/`splitURight` need no side hypotheses. -/
theorem atomUCode_subset {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) :
    UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := by
  have hemp := h
  rw [atomUEmpty_succ] at hemp
  rw [atomUCode_succ]
  set posC := atomUPos P n k
  set negC := atomUNeg P n k
  set c := atomUCode P n k
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit
  · simp only [hbit, selectFn_zero] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair (Nat.pair n posC + 1) negC)
    rcases (by omega : datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 0 ∨
        datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitURight]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]
  · simp only [hbit, selectFn_one] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair posC (Nat.pair n negC + 1))
    rcases (by omega : datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 0 ∨
        datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitULeft]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]

/-! ### Disjointness -/

/-- **The core `(vii)(1)` result**: at every depth `n`, atoms for bit-sources disagreeing somewhere
below `n` are disjoint on the `U`-side, *provided both are still `D`-side non-empty*. Proved by
induction on `n`, mirroring `atomU_invariant`'s disjointness clause: either the disagreement is
already below `n - 1` (recurse, then shrink both sides via `atomUCode_subset`), or it is exactly at
the last bit (use `atomUCodeState_congr` to identify the shared depth-`(n-1)` ancestor, then
`splitU_disjoint`, since both survive to depth `n` iff that step was a genuine split). -/
theorem atomUCode_disjoint :
    ∀ n k k', atomUEmpty P n k = 0 → atomUEmpty P n k' = 0 → (∃ i < n, deltaOf k i ≠ deltaOf k' i) →
      UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ := by
  intro n
  induction n with
  | zero => intro k k' _ _ ⟨i, hi, _⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k k' hk hk' ⟨i, hi, hne⟩
    by_cases hagree : ∀ j < n, deltaOf k j = deltaOf k' j
    · have hδn : deltaOf k n ≠ deltaOf k' n := by
        intro heq
        apply hne
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact hagree i hi'
        · exact heq
      obtain ⟨hpos, hneg, hcode⟩ := atomUCodeState_congr P hagree
      rw [atomUCode_succ, atomUCode_succ, hpos, hneg, hcode]
      -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
      rcases Bool.eq_false_or_eq_true (deltaOf k n) with h1 | h1
      · -- `deltaOf k n = true`: `k` takes bit `1`, so `deltaOf k' n` must be `false`.
        have hbitk : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp h1
        have h2 : deltaOf k' n = false := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact absurd (h1.trans h2.symm) hδn
          · exact h2
        have hbitk' : (k' / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k' n).mpr hh) (by simp [h2])
        have hkI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_one] at h; exact h
        have hk'J : datomDec P (Nat.pair (atomUPos P n k') (Nat.pair n (atomUNeg P n k') + 1)) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_zero] at h; exact h
        rw [hpos, hneg] at hkI
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkI, hk'J]
        exact splitU_disjoint (atomUCode P n k')
      · -- `deltaOf k n = false`: `k` takes bit `0`, so `deltaOf k' n` must be `true`.
        have hbitk : (k / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [h1])
        have h2 : deltaOf k' n = true := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact h2
          · exact absurd (h1.trans h2.symm) hδn
        have hbitk' : (k' / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k' n).mp h2
        have hkJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_zero] at h; exact h
        have hk'I : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k') + 1) (atomUNeg P n k')) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_one] at h; exact h
        rw [hpos, hneg] at hkJ
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkJ, hk'I]
        exact (Set.inter_comm _ _).trans (splitU_disjoint (atomUCode P n k'))
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hd : UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ :=
        ih k k' (atomUEmpty_zero_of_succ P hk) (atomUEmpty_zero_of_succ P hk') ⟨j, hj, hjne⟩
      exact Set.subset_eq_empty
        (Set.inter_subset_inter (atomUCode_subset P hk) (atomUCode_subset P hk')) hd

/-! ## Theorem 8.8(b)(vii)(2) — `YseqCode`, Scott's `Yₙ` coded

Scott's `Yₙ` (`Theorem88.lean`'s `Yseq`) is the union, over the `2ⁿ` depth-`(n+1)` atoms with bit
`n` forced `1`, of the "+"-piece chosen at that step. Here that union is built **as a `Nat.Primrec`
fold over `U`-codes** (`yFold`/`YseqCode`), skipping any bit-source whose `D`-side atom is already
junk (`atomUEmpty = 1`) — since a junk atom's code is *frozen at the aliasing value `0`*
(`atomUCode_eq_zero_of_empty`), and `UX 0 = U.master` (`canonCode`'s degenerate-input fallback), a
naive unfiltered union would corrupt every depth's result to `U.master` outright. -/

/-! ### Bit-level arithmetic for `deltaOf`, via `Nat.testBit`

`deltaOf` is definitionally `Nat.testBit` in disguise (`Nat.testBit_eq_decide_div_mod_eq`), so every
fact below is a direct transcription of a core `Nat.testBit` lemma about `2ⁿ`-shifted/masked
naturals — no bespoke bit-manipulation induction is needed. -/

theorem deltaOf_eq_testBit (k i : ℕ) : deltaOf k i = k.testBit i :=
  Nat.testBit_eq_decide_div_mod_eq.symm

/-- Adding `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_add_two_pow_of_lt {n : ℕ} (m : ℕ) {i : ℕ} (hi : i < n) :
    deltaOf (m + 2 ^ n) i = deltaOf m i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_gt hi]

/-- Adding `2ⁿ` to an `m < 2ⁿ` sets exactly bit `n` (no carry beyond it). -/
theorem deltaOf_two_pow_add_self {n m : ℕ} (hm : m < 2 ^ n) : deltaOf (m + 2 ^ n) n = true := by
  rw [deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
  rfl

/-- Reducing modulo `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

/-! ### `encodeBits`: realizing a prescribed finite bit-prefix as an explicit `ℕ`

Purely a `Prop`-level existence tool (never claimed `Nat.Primrec`): given *any* `δ : ℕ → Bool`,
`encodeBits δ n < 2ⁿ` is a bit-source whose first `n` bits match `δ`'s. Used once, below, to turn
the *abstract* nonemptiness fact "every index's own atom is nonempty" into a concrete witness
bit-source for `yFold`'s search range. -/

private def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => encodeBits δ n + (if δ n then 2 ^ n else 0)

private theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | n + 1 => by
      have ih := encodeBits_lt δ n
      have hp := Nat.two_pow_pos n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn <;> simp [hδn] <;> omega

private theorem deltaOf_encodeBits (δ : ℕ → Bool) :
    ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i
  | n + 1, i, hi => by
      have hlt := encodeBits_lt δ n
      show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n + 2 ^ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [deltaOf_add_two_pow_of_lt _ hi']; exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_two_pow_add_self hlt, hδn]
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_eq_testBit, Nat.testBit_lt_two_pow hlt, hδn]

/-! ### Existence: some bit-source among `{i + 2ⁿ ∣ i < 2ⁿ}` is always `D`-side non-empty

Mirrors `Theorem88a.lean`'s `Yidx_nonempty` (every index `n` witnesses its own `idxSet e n`'s
self-membership, `self_mem_idxSet`), transported to the bit-source encoding via `encodeBits`. -/

theorem exists_atomUEmpty_zero (n : ℕ) : ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  classical
  set δ0 : ℕ → Bool := fun j => decide (n ∈ idxSet (e P) j) with hδ0def
  have hδ0n : δ0 n = true := by
    show decide (n ∈ idxSet (e P) n) = true
    rw [decide_eq_true_iff]; exact self_mem_idxSet (e P) n
  have hstep : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) =
      genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n := by
    show genAtom (idxSet (e P)) Set.univ δ0 n ∩
      (if δ0 n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
    simp [hδ0n]
  have hxn : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n :=
    genAtom_self (idxSet (e P)) Set.univ (Set.mem_univ n) n
  have hmem : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n :=
    ⟨hxn, self_mem_idxSet (e P) n⟩
  have hAne : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) ≠ ∅ := by
    rw [hstep]; exact Set.Nonempty.ne_empty ⟨n, hmem⟩
  set m0 := encodeBits δ0 n with hm0def
  have hm0lt : m0 < 2 ^ n := encodeBits_lt δ0 n
  refine ⟨m0, hm0lt, ?_⟩
  rw [atomUEmpty_eq_zero_iff_genAtom]
  have hagree : ∀ j < n + 1, deltaOf (m0 + 2 ^ n) j = δ0 j := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hj']; exact deltaOf_encodeBits δ0 n j hj'
    · rw [deltaOf_two_pow_add_self hm0lt, hδ0n]
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree]
  exact hAne

/-! ### `atomUEmpty` is `Nat.Primrec` -/

theorem primrec_atomUEmpty : Nat.Primrec (fun t : ℕ => atomUEmpty P t.unpair.1 t.unpair.2) :=
  ((primrec_datomDec P).comp ((primrec_atomUPos P).pair (primrec_atomUNeg P))).of_eq
    fun _ => rfl

/-! ### The union fold: `yFoldStep`/`yFold`

`yFoldStep` is written as a function of a **single** packed argument `w = pair n (pair i acc)`
(mirroring `atomStep`'s own convention), so that feeding it directly into `Nat.Primrec.prec` needs
no further unpair/pair bookkeeping. -/

/-- One step of the depth-`n` union fold over bit-sources `i + 2ⁿ` (bit `n` forced `1`): silently
skip over `D`-side-empty ("junk") atoms — whose code is frozen at the aliasing value `0`
(`atomUCode_eq_zero_of_empty`) and would otherwise contribute the spurious `UX 0 = U.master` to the
union — and union in every genuine (non-junk) atom's code via `unionUX`. The accumulator is packed
as `(found, code)`: `found = 0` means "no genuine atom seen among the earlier `i' < i` yet" (`code`
is junk and unused in that case); `found = 1` means `code` already holds the union of all genuine
atoms seen so far. -/
noncomputable def yFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  let k := i + 2 ^ n
  selectFn (atomUEmpty P (n + 1) k) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) k)))
      (Nat.pair 1 (atomUCode P (n + 1) k)))

theorem primrec_yFoldStep : Nat.Primrec (yFoldStep P) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h2n : Nat.Primrec (fun w : ℕ => 2 ^ w.unpair.1) := primrec_two_pow hn
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 2 ^ w.unpair.1) :=
    primrec_add₂ hi h2n
  have hn1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) := Nat.Primrec.succ.comp hn
  have hempty : Nat.Primrec (fun w : ℕ =>
      atomUEmpty P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUEmpty P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcode : Nat.Primrec (fun w : ℕ =>
      atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUCode P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => unionUX w.unpair.2.unpair.2.unpair.2
      (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))) :=
    (primrec_unionUX.comp (hval.pair hcode)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (unionUX w.unpair.2.unpair.2.unpair.2
        (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))))
      (Nat.pair 1 (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)))) :=
    primrec_selectFn hfound
      ((Nat.Primrec.const 1).pair hunion)
      ((Nat.Primrec.const 1).pair hcode)
  exact (primrec_selectFn hempty hacc hinner).of_eq fun w => by unfold yFoldStep; simp only []

/-- The depth-`n` union fold over `i < N`, starting from the "nothing found yet" accumulator
`(0, 0)`. -/
noncomputable def yFold (n N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => yFoldStep P (Nat.pair n (Nat.pair i acc)))

theorem yFold_zero (n : ℕ) : yFold P n 0 = Nat.pair 0 0 := rfl

theorem yFold_succ (n N : ℕ) :
    yFold P n (N + 1) = yFoldStep P (Nat.pair n (Nat.pair N (yFold P n N))) := rfl

theorem primrec_yFold : Nat.Primrec (fun t : ℕ => yFold P t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0)) (primrec_yFoldStep P)).of_eq fun _ => rfl

/-! ### Correctness: `yFold`'s "found" flag and running union, by induction on `N` -/

theorem atomUEmpty_zero_or_one (n k : ℕ) : atomUEmpty P n k = 0 ∨ atomUEmpty P n k = 1 := by
  have h := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  unfold atomUEmpty
  omega

/-- Unfolding `yFoldStep` at an explicit `(n, i, acc)` triple. -/
theorem yFoldStep_eq (n i acc : ℕ) :
    yFoldStep P (Nat.pair n (Nat.pair i acc)) =
      selectFn (atomUEmpty P (n + 1) (i + 2 ^ n)) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) (i + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (i + 2 ^ n)))) := by
  unfold yFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem yFold_found_le_one (n : ℕ) : ∀ N, (yFold P n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

/-- **The "found" flag exactly tracks existence of a non-junk bit-source below `N`.** -/
theorem yFold_found_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 ↔ ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn (yFold P n N).unpair.1
          (Nat.pair 1 (unionUX (yFold P n N).unpair.2 (atomUCode P (n + 1) (N + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (N + 2 ^ n)))).unpair.1 = 1 := by
        have hle := yFold_found_le_one P n N
        rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf | hf
        · rw [show (yFold P n N).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

/-- **The membership form of `yFold`'s correctness**: once a non-junk bit-source has been found
below `N`, the running code's `UX`-image is exactly the union of the genuine (non-junk) atoms
seen so far. -/
theorem yFold_mem_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 →
      ∀ z : ℚ, z ∈ UX (yFold P n N).unpair.2 ↔
        ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) := by
  intro N
  induction N with
  | zero => intro h; simp [yFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [yFold_succ, yFoldStep_eq] at hfound1 ⊢
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((yFold_found_iff P n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (yFold P n N).unpair.1 = 1 := by
          have := yFold_found_le_one P n N; omega
        rw [hf1, selectFn_one, unpair_pair_snd, UX_unionUX, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

/-! ### `YseqCode`: assembling the fold at `N = 2ⁿ` -/

theorem yFold_two_pow_found (n : ℕ) : (yFold P n (2 ^ n)).unpair.1 = 1 :=
  (yFold_found_iff P n (2 ^ n)).mpr (exists_atomUEmpty_zero P n)

/-- **`YseqCode`, Scott's `Yₙ` coded.** The `Nat.Primrec` union, over the `2ⁿ` bit-sources
`i < 2ⁿ` (bit `n` forced `1`, i.e. `i + 2ⁿ`), of the genuine (non-junk) atoms `atomUCode P (n+1)
(i + 2ⁿ)`. -/
noncomputable def YseqCode (n : ℕ) : ℕ := (yFold P n (2 ^ n)).unpair.2

theorem primrec_YseqCode : Nat.Primrec (YseqCode P) := by
  have h2n : Nat.Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow Nat.Primrec.id
  refine (Nat.Primrec.right.comp ((primrec_yFold P).comp (Nat.Primrec.id.pair h2n))).of_eq
    fun n => ?_
  show ((yFold P (Nat.pair n (2 ^ n)).unpair.1 (Nat.pair n (2 ^ n)).unpair.2)).unpair.2 = YseqCode P n
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

/-- **The closed-form membership characterization of `YseqCode`** — the "Set-level closed form"
this part exists to supply: a point lies in `UX (YseqCode P n)` iff it lies in some genuine
(non-junk) depth-`(n+1)` atom with bit `n` forced `1`. -/
theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

/-! ### The closed form: `YseqCode` recovers the "+"-piece of the atom recursion

Mirrors `Theorem88.lean`'s `split_fst_eq_inter_Yseq`: the "+"-branch chosen at depth `n` by the
atom recursion is exactly the intersection of the depth-`n` atom with `YseqCode`. Pairwise
disjointness (`atomUCode_disjoint`) is what rules out any *other* atom leaking a point into
`UX (YseqCode P n)` that isn't already forced into this one. -/

theorem atomUCode_succ_true {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = true) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) ∩ UX (YseqCode P n) := by
  set j := k % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  have hagree : ∀ i < n + 1, deltaOf k i = deltaOf (j + 2 ^ n) i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hi', hjdef, deltaOf_mod_two_pow_of_lt hi']
    · rw [deltaOf_two_pow_add_self hjlt, hδ]
  obtain ⟨hpos_eq, hneg_eq, hcode_eq⟩ := atomUCodeState_congr P hagree
  have hempty_eq : atomUEmpty P (n + 1) (j + 2 ^ n) = 0 := by
    have heq : atomUEmpty P (n + 1) (j + 2 ^ n) = atomUEmpty P (n + 1) k := by
      unfold atomUEmpty; rw [hpos_eq, hneg_eq]
    rw [heq]; exact hne
  apply Set.Subset.antisymm
  · have hsub1 : UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := atomUCode_subset P hne
    have hsub2 : UX (atomUCode P (n + 1) k) ⊆ UX (YseqCode P n) := by
      rw [hcode_eq]
      intro z hz
      exact (mem_UX_YseqCode_iff P n z).mpr ⟨j, hjlt, hempty_eq, hz⟩
    exact Set.subset_inter hsub1 hsub2
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
    by_cases hagree' : ∀ p < n, deltaOf (i + 2 ^ n) p = deltaOf k p
    · have hagreeFull : ∀ l < n + 1, deltaOf (i + 2 ^ n) l = deltaOf k l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
        · exact hagree' l hl'
        · rw [deltaOf_two_pow_add_self hilt, hδ]
      have hcode_eq'' : atomUCode P (n + 1) (i + 2 ^ n) = atomUCode P (n + 1) k :=
        (atomUCodeState_congr P hagreeFull).2.2
      rw [← hcode_eq'']; exact hz
    · push_neg at hagree'
      obtain ⟨l, hl, hlne⟩ := hagree'
      have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) = ∅ :=
        atomUCode_disjoint P n (i + 2 ^ n) k (atomUEmpty_zero_of_succ P hie)
          (atomUEmpty_zero_of_succ P hne) ⟨l, hl, hlne⟩
      have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode_subset P hie hz
      have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) := ⟨hzB', hzB⟩
      rw [hd] at hzmem
      exact absurd hzmem (Set.mem_empty_iff_false z).mp

end Scott1980.Neighborhood
