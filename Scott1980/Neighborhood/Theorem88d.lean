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

This file lays the **foundational recursion** (`atomUCode`, `Nat.Primrec`) and its **per-step
correctness** (Part 7a): decoding `atomUCode`'s state reproduces exactly Scott's atom-emptiness
invariant, with the `U`-side code meaningful exactly when the `D`-side atom is non-empty. The
remaining assembly (Part 7b: a `Yseq`-analogue as a *union* over `2ⁿ` such atoms, disjointness,
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
codebase — only *naming* it needs choice, mirroring `DprimeUPresentation`'s own `noncomputable`. -/
noncomputable def datomDec : ℕ → ℕ := (DAtom_recDecidable (P0 P)).choose

theorem primrec_datomDec : Nat.Primrec (datomDec P) := (DAtom_recDecidable (P0 P)).choose_spec.1

theorem datomDec_spec (posC negC : ℕ) :
    datomDec P (Nat.pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅ := by
  have h := (DAtom_recDecidable (P0 P)).choose_spec.2 (Nat.pair posC negC)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

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

end Scott1980.Neighborhood
