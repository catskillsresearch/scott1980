import Scott1980.Neighborhood.Example78
import Scott1980.Neighborhood.Theorem74

/-!
# Exercise 7.23 (Scott 1981, PRG-19, §7) — completing the discussion of `PN`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.23.** Complete the discussion of `PN` of Example 7.8. Show that the combinators
> `fun` and `graph` of Exercise 5.14 are computable. Also do the same for `λx,y. x∩y`,
> `λx,y. x∪y`, and `λx,y. x+y`, where for `x,y ∈ PN` we define `x+y = {n+m ∣ n∈x and m∈y}`.
> What are the computable elements of `PN`?

**The key structural fact.** Write `E n := ℕ \ Example78.nbhd n = {k ∣ n.testBit k}` for the finite
set Scott's `nbhd n` excludes. `Example78.nbhd n ⊆ Example78.nbhd k ↔ E k ⊆ E n` (containment of
neighbourhoods *reverses* into containment of the excluded finite sets — this is exactly
`ComputablePresentation.incl_computable`, already proven generically for any
`ComputablePresentation`, applied to `Example78.PNpres`). Every binary combinator `λx,y. h(x,y)`
this exercise asks about turns out to test a *containment of finite sets* `E k ⊆ h(E n, E m)`, which
is exactly `nbhd n ⊆ nbhd k` (and/or `nbhd m ⊆ nbhd k`) reindexed — so **`∩`/`∪` are computable
reusing `incl_computable` directly, with no new bitwise/primitive-recursive machinery**: `∩` is the
conjunction of two containments (`Eₖ⊆Eₙ∩Eₘ ↔ Eₖ⊆Eₙ ∧ Eₖ⊆Eₘ`), and `∪` reduces to a single
containment against `myLor n m` (`Eₖ⊆Eₙ∪Eₘ ↔ Eₖ⊆E_{myLor n m} ↔ nbhd(myLor n m) ⊆ nbhd k`).
-/

namespace Scott1980.Neighborhood.Exercise723

open Scott1980.Neighborhood Example78 NeighborhoodSystem Domain.Recursive

/-! ## `nbhd`-containment reverses into excluded-set containment -/

/-- **The reversal fact.** `nbhd n ⊆ nbhd k ↔ myLor n k = n`: `nbhd n ⊆ nbhd k` iff
`nbhd n ∩ nbhd k = nbhd n` iff (by `nbhd_inter` + injectivity) `nbhd (myLor n k) = nbhd n`. -/
theorem nbhd_subset_iff_myLor_eq (n k : ℕ) : nbhd n ⊆ nbhd k ↔ myLor n k = n := by
  constructor
  · intro h
    apply nbhd_injective
    rw [← nbhd_inter]
    exact (Set.inter_eq_left.mpr h)
  · intro h
    rw [← h, ← nbhd_inter]
    exact Set.inter_subset_right

/-! ## `λx,y. x∩y` -/

/-- **`λx,y. x∩y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `X ⊆ Z` and `Y ⊆ Z` (the "test at the minimal witness" idiom: `X`, `Y` are themselves the
tightest possible arguments consistent with the input information). -/
def capMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ⊆ Z ∧ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.subset_univ _, Set.subset_univ _⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ ⟨X', Y', heq, _, _, hZ', hXZ', hYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩,
      Set.subset_inter hXZ hXZ', Set.subset_inter hYZ hYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXZ, hYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ', hXX'.trans (hXZ.trans hZZ'), hYY'.trans (hYZ.trans hZZ')⟩

/-- `capMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff both
`nbhd n ⊆ nbhd k` and `nbhd m ⊆ nbhd k`. -/
theorem capMap_rel_iff (n m k : ℕ) :
    capMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd n ⊆ nbhd k ∧ nbhd m ⊆ nbhd k := by
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXZ, hYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hXZ, hYZ⟩
  · rintro ⟨hXZ, hYZ⟩
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, hXZ, hYZ⟩

/-- **`λx,y. x∩y` is computable.** Reduces to `PNpres.incl_computable`, tested twice and
conjoined. -/
theorem capMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres capMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hr0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hr1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) ((hincl.comp hr0).and (hincl.comp hr1))).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact capMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## Bit-level utilities: `Nat.testBit` is primitive recursively decidable

Needed for `λx,y.x+y` (Minkowski sum) and for `fun`/`graph`, both of which test membership of a
*bit position* `k` of the excluded set `E_k` against a target condition. -/

/-- **Every set bit lies below the number itself.** If `n.testBit i = true` then `i < n` (since
`n ≥ 2^i > i`). -/
theorem lt_of_testBit_true {n i : ℕ} (h : n.testBit i = true) : i < n := by
  by_contra hle
  have hle' : n ≤ i := by omega
  have hlt : n < 2 ^ i := lt_of_le_of_lt hle' Nat.lt_two_pow_self
  rw [Nat.testBit_eq_false_of_lt hlt] at h
  exact absurd h (by decide)

/-- Iterated halving `(·/2)^[k] n`, the primitive-recursive core of `Nat.testBit`. -/
def halfIter (n k : ℕ) : ℕ := (fun x : ℕ => x / 2)^[k] n

@[simp] theorem halfIter_zero (n : ℕ) : halfIter n 0 = n := rfl

theorem halfIter_succ (n k : ℕ) : halfIter n (k + 1) = halfIter (n / 2) k := by
  unfold halfIter; rw [Function.iterate_succ_apply]

theorem primrec_halfIter : Nat.Primrec (fun t => halfIter t.unpair.1 t.unpair.2) := by
  have hstep : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec primrec_id hstep).of_eq (fun t => ?_)
  simp only [Nat.unpaired, unpair_pair_snd]
  exact rec_const_iterate (fun x => x / 2) t.unpair.1 t.unpair.2

/-- The `{0,1}`-valued primitive-recursive proxy for `Nat.testBit`. -/
def bitAt (n k : ℕ) : ℕ := halfIter n k % 2

theorem primrec_bitAt : Nat.Primrec (fun t => bitAt t.unpair.1 t.unpair.2) :=
  primrec_mod2.comp primrec_halfIter

theorem bitAt_le_one (n k : ℕ) : bitAt n k ≤ 1 := by unfold bitAt; omega

/-- **Correctness of `bitAt`.** `bitAt n k = 1 ↔ n.testBit k = true`. -/
theorem bitAt_eq_one_iff (n k : ℕ) : bitAt n k = 1 ↔ n.testBit k = true := by
  induction k generalizing n with
  | zero =>
    show n % 2 = 1 ↔ n.testBit 0 = true
    rw [Nat.testBit_zero, decide_eq_true_iff]
  | succ k ih =>
    show halfIter n (k + 1) % 2 = 1 ↔ n.testBit (k + 1) = true
    rw [halfIter_succ, Nat.testBit_add_one]
    exact ih (n / 2)

/-! ## `λx,y. x∪y` -/

/-- **`λx,y. x∪y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to
`Z` iff `nbhd(myLor n m) ⊆ Z` — the excluded set of `Z` must fit inside the *union* `Eₙ ∪ Eₘ`, i.e.
`nbhd n ∩ nbhd m ⊆ Z` (`Eₙ ∪ Eₘ = E_{myLor n m}`, `nbhd_inter`). -/
def cupMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    Set.inter_subset_left.trans (Set.subset_univ _)⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ ⟨X', Y', heq, _, _, hZ', hXYZ'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    exact ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, Set.subset_inter hXYZ hXYZ'⟩
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hXYZ⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    exact ⟨X', Y', rfl, hX', hY', hZ',
      (Set.inter_subset_inter hXX' hYY').trans (hXYZ.trans hZZ')⟩

/-- `cupMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (myLor n m) ⊆ nbhd k`. -/
theorem cupMap_rel_iff (n m k : ℕ) :
    cupMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (myLor n m) ⊆ nbhd k := by
  rw [← nbhd_inter n m]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hXYZ
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

/-- **`λx,y. x∪y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `myLor`. -/
theorem cupMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres cupMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hlor : Nat.Primrec (fun t : ℕ => myLor t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_myLor.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
      (Nat.Primrec.right.comp Nat.Primrec.left))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (myLor t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hlor.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact cupMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## `λx,y. x+y` (Minkowski sum)

Scott's `x + y = {n + m ∣ n ∈ x, m ∈ y}`. Written on excluded sets, `Eₙ + Eₘ` (Minkowski sum of two
*finite* sets) is again finite, and — since `a + b` ranges over `Eₙ + Eₘ` exactly when `a` ranges
over `Eₙ` and `b` over `Eₘ` — `Eₙ + Eₘ = ⋃ {a + Eₘ ∣ a ∈ Eₙ}`, a union of shifted copies of `Eₘ`, one
per set bit of `n`. This is computed by `plusIdx`, an iterative bitwise-OR fold (mirroring `myLor`)
of `m <<< a` over the set bits `a` of `n`. -/

/-- Scott's `x + y = {n+m ∣ n ∈ x, m ∈ y}` (Minkowski sum) for `x, y ⊆ ℕ`. -/
def sumSet (X Y : Set ℕ) : Set ℕ := {k | ∃ a ∈ X, ∃ b ∈ Y, a + b = k}

@[inherit_doc] infixl:65 " +ˢ " => sumSet

theorem mem_sumSet {X Y : Set ℕ} {k : ℕ} : k ∈ X +ˢ Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a + b = k := Iff.rfl

theorem sumSet_mono {X X' Y Y' : Set ℕ} (hX : X ⊆ X') (hY : Y ⊆ Y') : X +ˢ Y ⊆ X' +ˢ Y' := by
  rintro k ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hX ha, b, hY hb, rfl⟩

/-- **Choice-free antitone `compl`** (only the direction needed here): unlike the general
`Set.compl_subset_compl` (a `BooleanAlgebra` lemma whose `↔` proof is classical), this direction is
constructive contraposition and needs no excluded middle. -/
theorem compl_subset_compl_of_subset {X Y : Set ℕ} (h : X ⊆ Y) : Yᶜ ⊆ Xᶜ :=
  fun _ hx hxX => hx (h hxX)

/-- The excluded set of `nbhd n`, as a set of naturals: `(nbhd n)ᶜ = {k ∣ n.testBit k}`. -/
theorem compl_nbhd (n : ℕ) : (nbhd n)ᶜ = {k | n.testBit k = true} := by
  ext k; simp [nbhd]

/-- Pointwise form of `compl_nbhd`, convenient for `rw`/case-splitting on the (decidable) bit. -/
theorem mem_compl_nbhd {n x : ℕ} : x ∈ (nbhd n)ᶜ ↔ n.testBit x = true := by
  rw [compl_nbhd]; rfl

/-- **Choice-free De Morgan for `nbhd`'s excluded sets.** The general `Set.compl_inter` needs
excluded middle; here, since membership in `nbhd a`/`nbhd b` is decided by `Nat.testBit`, a case
split on the two (concrete) bits suffices. -/
theorem compl_inter_nbhd (a b : ℕ) : (nbhd a ∩ nbhd b)ᶜ = (nbhd a)ᶜ ∪ (nbhd b)ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, mem_nbhd]
  cases a.testBit x <;> cases b.testBit x <;> decide

/-- **Reference spec for `plusIdx`.** The running bitwise-OR of `m <<< a` over set bits `a < N` of
`n`, built by ordinary (non-primitive-recursive) structural recursion — used only to state and prove
correctness of the primitive-recursive `plusIdx` below. -/
def orUpTo (n m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => myLor (orUpTo n m k) (selectFn (bitAt n k) (m <<< k) 0)

/-- **`orUpTo`'s bit-by-bit characterization.** Bit `k` of `orUpTo n m N` is set exactly when some
`a < N` is a set bit of `n` with `a ≤ k` and `k - a` a set bit of `m`. -/
theorem testBit_orUpTo (n m : ℕ) : ∀ N k,
    (orUpTo n m N).testBit k = true ↔ ∃ a, a < N ∧ n.testBit a = true ∧ a ≤ k ∧ m.testBit (k - a) = true
  | 0, k => by simp [orUpTo]
  | N + 1, k => by
    show (myLor (orUpTo n m N) (selectFn (bitAt n N) (m <<< N) 0)).testBit k = true ↔ _
    rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true, testBit_orUpTo n m N]
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, Nat.testBit_shiftLeft]
      constructor
      · rintro (⟨a, haN, ha, hak, hb⟩ | h)
        · exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
        · rw [Bool.and_eq_true, decide_eq_true_iff] at h
          exact ⟨N, Nat.lt_succ_self N, hbit, h.1, h.2⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact Or.inl ⟨a, haN, ha, hak, hb⟩
        · subst haN
          exact Or.inr (by rw [Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hak, hb⟩)
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨a, haN, ha, hak, hb⟩; exact ⟨a, Nat.lt_succ_of_lt haN, ha, hak, hb⟩
      · rintro ⟨a, haN1, ha, hak, hb⟩
        rcases (show a < N ∨ a = N by omega) with haN | haN
        · exact ⟨a, haN, ha, hak, hb⟩
        · subst haN; exact absurd ha hbit

/-- **`orUpTo n m n` computes the Minkowski sum `Eₙ + Eₘ` exactly.** Every set bit `a` of `n`
satisfies `a < n` (`lt_of_testBit_true`), so ranging `a` over `N = n` sees every set bit of `n`. -/
theorem testBit_orUpTo_self (n m k : ℕ) :
    (orUpTo n m n).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true := by
  rw [testBit_orUpTo]
  constructor
  · rintro ⟨a, _, ha, hak, hb⟩; exact ⟨a, hak, ha, hb⟩
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, lt_of_testBit_true ha, ha, hak, hb⟩

/-- **`plusIdx n m`: the primitive-recursive index of `Eₙ + Eₘ`.** -/
def plusIdx (n m : ℕ) : ℕ := orUpTo n m n

theorem plusIdx_testBit (n m k : ℕ) :
    (plusIdx n m).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true :=
  testBit_orUpTo_self n m k

/-- **`plusIdx`'s excluded set is the Minkowski sum `Eₙ + Eₘ`.** -/
theorem compl_nbhd_plusIdx (n m : ℕ) : (nbhd (plusIdx n m))ᶜ = (nbhd n)ᶜ +ˢ (nbhd m)ᶜ := by
  rw [compl_nbhd, compl_nbhd, compl_nbhd]
  ext k
  simp only [mem_sumSet, Set.mem_setOf_eq, plusIdx_testBit]
  constructor
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, ha, k - a, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, by omega, ha, by rw [Nat.add_sub_cancel_left]; exact hb⟩

/-- The primitive-recursive step function for `orUpTo`'s bitwise-OR fold: `(n, m, a, acc) ↦
(n, m, a+1, acc ||| (if testBit n a then m<<<a else 0))`. -/
def plusStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair s.unpair.1.unpair.1 s.unpair.1.unpair.2)
    (Nat.pair (s.unpair.2.unpair.1 + 1)
      (myLor s.unpair.2.unpair.2
        (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
          (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0)))

theorem primrec_plusStep : Nat.Primrec plusStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hm : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have ha : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair ha)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hshift : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) := by
    have := primrec_mul₂ hm (primrec_two_pow ha)
    exact this.of_eq fun s => by rw [Nat.shiftLeft_eq]
  have hsel := primrec_selectFn hbit hshift (Nat.Primrec.const 0)
  have hlor : Nat.Primrec (fun s : ℕ => myLor s.unpair.2.unpair.2
      (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
        (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0)) :=
    (primrec_myLor.comp (hacc.pair hsel)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((hn.pair hm).pair ((primrec_add₂ ha (Nat.Primrec.const 1)).pair hlor)).of_eq fun _ => rfl

theorem plusStep_unpair11 (s : ℕ) : (plusStep s).unpair.1.unpair.1 = s.unpair.1.unpair.1 := by
  unfold plusStep; rw [unpair_pair_fst, unpair_pair_fst]

theorem plusStep_unpair12 (s : ℕ) : (plusStep s).unpair.1.unpair.2 = s.unpair.1.unpair.2 := by
  unfold plusStep; rw [unpair_pair_fst, unpair_pair_snd]

theorem plusStep_unpair21 (s : ℕ) : (plusStep s).unpair.2.unpair.1 = s.unpair.2.unpair.1 + 1 := by
  unfold plusStep; rw [unpair_pair_snd, unpair_pair_fst]

theorem plusStep_unpair22 (s : ℕ) : (plusStep s).unpair.2.unpair.2 =
    myLor s.unpair.2.unpair.2 (selectFn (bitAt s.unpair.1.unpair.1 s.unpair.2.unpair.1)
      (s.unpair.1.unpair.2 <<< s.unpair.2.unpair.1) 0) := by
  unfold plusStep; rw [unpair_pair_snd, unpair_pair_snd]

theorem plusStep_iter_spec (n m : ℕ) (k : ℕ) :
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.1 = n ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.2 = m ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.2 = orUpTo n m k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, orUpTo]
  | succ k ih =>
    obtain ⟨hn, hm, ha, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [plusStep_unpair11, hn]
    · rw [plusStep_unpair12, hm]
    · rw [plusStep_unpair21, ha]
    · rw [plusStep_unpair22, hn, hm, ha, hacc]; rfl

theorem primrec_plusIdx : Nat.Primrec (fun t => plusIdx t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 0 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => plusStep w.unpair.2.unpair.2) :=
    primrec_plusStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.left))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (plusStep_iter_spec t.unpair.1 t.unpair.2 t.unpair.1).2.2.2

/-- **`λx,y. x+y` as an approximable map** `PN × PN → PN`. On neighbourhoods: `X ∪ Y` relates to `Z`
iff `Zᶜ ⊆ Xᶜ +ˢ Yᶜ` — the excluded set of the output must fit inside the *Minkowski sum* of the
inputs' excluded sets, the most that is guaranteed knowing only `Eₙ ⊆ Sx` and `Eₘ ⊆ Sy`. -/
def plusMap : ApproximableMap (prod PN PN) PN where
  rel W Z := ∃ X Y, W = prodNbhd X Y ∧ PN.mem X ∧ PN.mem Y ∧ PN.mem Z ∧ Zᶜ ⊆ Xᶜ +ˢ Yᶜ
  rel_dom := by rintro W Z ⟨X, Y, rfl, hX, hY, _, _⟩; exact prod_mem_prodNbhd hX hY
  rel_cod := by rintro W Z ⟨X, Y, rfl, _, _, hZ, _⟩; exact hZ
  master_rel := ⟨Set.univ, Set.univ, rfl, PN.master_mem, PN.master_mem, PN.master_mem,
    fun x hx => absurd (Set.mem_univ x) hx⟩
  inter_right := by
    rintro W Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ ⟨X', Y', heq, _, _, hZ', hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    obtain ⟨k, hk⟩ := hZ; obtain ⟨k', hk'⟩ := hZ'; subst hk; subst hk'
    refine ⟨X, Y, rfl, hX, hY, ⟨myLor k k', nbhd_inter k k'⟩, ?_⟩
    rw [compl_inter_nbhd]
    exact Set.union_subset hsub hsub'
  mono := by
    rintro W W' Z Z' ⟨X, Y, rfl, hX, hY, hZ, hsub⟩ hW'W hZZ' hW' hZ'
    obtain ⟨X', Y', hX', hY', rfl⟩ := hW'
    obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hW'W
    refine ⟨X', Y', rfl, hX', hY', hZ', ?_⟩
    calc Z'ᶜ ⊆ Zᶜ := compl_subset_compl_of_subset hZZ'
      _ ⊆ Xᶜ +ˢ Yᶜ := hsub
      _ ⊆ X'ᶜ +ˢ Y'ᶜ :=
        sumSet_mono (compl_subset_compl_of_subset hXX') (compl_subset_compl_of_subset hYY')

/-- **Choice-free converse of `compl_subset_compl_of_subset`, specialized to `nbhd`.** For cofinite
neighbourhoods the excluded sets have decidable membership (`Nat.testBit`), so unlike the general
`Set.compl_subset_compl` this direction needs only a case split on a `Bool`, not excluded middle. -/
theorem nbhd_subset_iff_compl_subset_compl (a b : ℕ) :
    nbhd a ⊆ nbhd b ↔ (nbhd b)ᶜ ⊆ (nbhd a)ᶜ := by
  constructor
  · exact compl_subset_compl_of_subset
  · intro h x hxa
    rw [mem_nbhd] at hxa ⊢
    cases hbit : b.testBit x with
    | false => rfl
    | true => exact absurd (mem_compl_nbhd.mp (h (mem_compl_nbhd.mpr hbit))) (by rw [hxa]; decide)

/-- `plusMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (plusIdx n m) ⊆ nbhd k`. -/
theorem plusMap_rel_iff (n m k : ℕ) :
    plusMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (plusIdx n m) ⊆ nbhd k := by
  rw [nbhd_subset_iff_compl_subset_compl, compl_nbhd_plusIdx]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hsub
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

/-- **`λx,y. x+y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `plusIdx`. -/
theorem plusMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres plusMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have hplus : Nat.Primrec (fun t : ℕ => plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_plusIdx.comp hpair).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hplus.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact plusMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

/-! ## What are the computable elements of `PN`?

Every element `x` of `PN` is a downward-directed filter of the cofinite neighbourhoods `nbhd n`.
Write `elemSet x := ⋃ {Eₙ ∣ x.mem (nbhd n)}` for the (arbitrary) subset of `ℕ` it "positively
describes". Since `PN`'s neighbourhoods carry only *negative* information and any two are consistent
(`PN_consistent`), each single fact `x.mem (nbhd n)` is *generated* by finitely many of the positive
facts `k ∈ elemSet x` (`k ∈ Eₙ`) — combine their witnesses with `myLor` (`exists_combined_witness`) —
so `x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x` (`nbhd_mem_iff_subset_elemSet`). This exhibits `PN` as
(isomorphic to) the classical powerset domain `(Set ℕ, ⊆)`, `x ↦ elemSet x`, and:

> **Theorem.** `x` is a computable element of `PN` iff `elemSet x` is a recursively enumerable
> subset of `ℕ` (`isComputableElement_iff_elemSet_re`).

I.e. **the computable elements of `PN` are exactly the recursively enumerable sets** — Scott's
headline fact about the powerset domain. -/

/-- The subset of `ℕ` "positively described" by a `PN`-element `x`: the union of the excluded finite
sets of every neighbourhood it contains. -/
def elemSet (x : PN.Element) : Set ℕ := {k | ∃ n, x.mem (nbhd n) ∧ n.testBit k = true}

@[simp] theorem mem_elemSet {x : PN.Element} {k : ℕ} :
    k ∈ elemSet x ↔ ∃ n, x.mem (nbhd n) ∧ n.testBit k = true := Iff.rfl

/-- **Finite covering (choice-free, structural induction on the witness list).** If every `k` in a
list `L` has *some* neighbourhood `nbhd m` of `x` with `m.testBit k`, a single `nbhd m₀ ∈ x` works for
all of `L` at once: combine the per-entry witnesses with `myLor` via `x.inter_mem`, one list entry at
a time. -/
theorem exists_combined_witness (x : PN.Element) :
    ∀ L : List ℕ, (∀ k ∈ L, ∃ m, x.mem (nbhd m) ∧ m.testBit k = true) →
      ∃ m₀, x.mem (nbhd m₀) ∧ ∀ k ∈ L, m₀.testBit k = true
  | [] => fun _ => ⟨0, nbhd_zero ▸ x.master_mem, by simp⟩
  | k :: L => by
    intro hL
    obtain ⟨mk, hmk, hbk⟩ := hL k List.mem_cons_self
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x L (fun j hj => hL j (List.mem_cons_of_mem k hj))
    refine ⟨myLor mk m₀, ?_, ?_⟩
    · rw [← nbhd_inter]; exact x.inter_mem hmk hm₀
    · intro j hj
      rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl hbk
      · exact Or.inr (hall j hj)

/-- The (non-primitive-recursive) list of set-bit positions of `n`: every set bit `k` of `n`
satisfies `k < n` (`lt_of_testBit_true`), so ranging over `List.range n` catches them all. Used only
to state/prove the pure covering fact `nbhd_mem_iff_subset_elemSet`; see `bitsCode` below for the
primitive-recursive analogue used in the computability direction. -/
def bitsList (n : ℕ) : List ℕ := (List.range n).filter (fun k => n.testBit k)

theorem mem_bitsList {n k : ℕ} : k ∈ bitsList n ↔ n.testBit k = true := by
  unfold bitsList
  rw [List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_testBit_true h, h⟩⟩

/-- **`x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x`.** Neighbourhood-membership reduces to positive-information
containment: `n`'s excluded set must already be covered by `x`'s recorded information. -/
theorem nbhd_mem_iff_subset_elemSet (x : PN.Element) (n : ℕ) :
    x.mem (nbhd n) ↔ (nbhd n)ᶜ ⊆ elemSet x := by
  rw [compl_nbhd]
  constructor
  · intro hn k hk
    exact ⟨n, hn, hk⟩
  · intro hsub
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x (bitsList n) (fun k hk => hsub (mem_bitsList.mp hk))
    have hincl : nbhd m₀ ⊆ nbhd n := by
      intro k hk
      simp only [mem_nbhd] at hk ⊢
      cases hn2 : n.testBit k with
      | false => rfl
      | true =>
        have hcontra := hall k (mem_bitsList.mpr hn2)
        rw [hk] at hcontra
        exact absurd hcontra (by decide)
    exact x.up_mem hm₀ ⟨n, rfl⟩ hincl

/-- **`elemSet x` is r.e. when `x` is a computable element.** Direct: `k ∈ elemSet x ↔ ∃ n,
x.mem (nbhd n) ∧ n.testBit k`, an r.e. projection of the conjunction of an r.e. predicate and a
(`bitAt`-)decidable one. -/
theorem elemSet_re_of_isComputableElement {x : PN.Element} (hx : IsComputableElement PNpres x) :
    REPred (fun k => k ∈ elemSet x) := by
  have hx' : REPred (fun n => x.mem (nbhd n)) := hx
  have hbit : RecDecidable (fun t : ℕ => t.unpair.1.testBit t.unpair.2 = true) :=
    ⟨fun t => bitAt t.unpair.1 t.unpair.2, primrec_bitAt, fun t => (bitAt_eq_one_iff _ _).symm⟩
  have hand : REPred (fun t : ℕ => x.mem (nbhd t.unpair.1) ∧ t.unpair.1.testBit t.unpair.2 = true) :=
    (hx'.comp Nat.Primrec.left).and hbit.re
  refine REPred.of_iff (fun k => ?_) hand.proj
  simp only [mem_elemSet, unpair_pair_fst, unpair_pair_snd]

/-! ### `bitsCode`: a primitive-recursive coding of "the list of set bits below `N`"

Needed for the converse computability direction: to invoke the generic closure
`REPred.forall_mem_decodeList`, the bounded conjunction `∀ k ∈ Eₙ, k ∈ A` must be phrased over a
*coded* list (`decodeList`), built by primitive recursion — not the plain `List.filter` form
`bitsList` above (which lives in `List ℕ`, outside the `Nat.Primrec` universe). `bitsCode` mirrors the
`plusStep`/`plusIdx` iteration pattern: it walks `k = 0, …, N-1`, consing `k` onto the running coded
list (`Nat.pair k acc + 1`, matching `decodeList`'s own `c + 1 ↦ c.unpair.1 :: decodeList c.unpair.2`)
exactly when `n.testBit k`. -/

/-- `bitsCode n N` codes the list of `k < N` with `n.testBit k = true`. -/
def bitsCode : ℕ → ℕ → ℕ
  | _, 0 => 0
  | n, N + 1 => selectFn (bitAt n N) (Nat.pair N (bitsCode n N) + 1) (bitsCode n N)

theorem mem_decodeList_bitsCode (n : ℕ) :
    ∀ N k, k ∈ decodeList (bitsCode n N) ↔ k < N ∧ n.testBit k = true
  | 0, k => by simp [bitsCode, decodeList_zero]
  | N + 1, k => by
    show k ∈ decodeList (selectFn (bitAt n N) (Nat.pair N (bitsCode n N) + 1) (bitsCode n N)) ↔ _
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, decodeList_succ, unpair_pair_fst,
        unpair_pair_snd, List.mem_cons, mem_decodeList_bitsCode n N k]
      constructor
      · rintro (rfl | ⟨hkN, hk⟩)
        · exact ⟨by omega, hbit⟩
        · exact ⟨by omega, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact Or.inr ⟨hkN, hk⟩
        · exact Or.inl hkN
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero, mem_decodeList_bitsCode n N k]
      constructor
      · rintro ⟨hkN, hk⟩
        exact ⟨Nat.lt_succ_of_lt hkN, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact ⟨hkN, hk⟩
        · subst hkN; exact absurd hk hbit

/-- The primitive-recursive step function for `bitsCode`'s iteration: `(n, N, acc) ↦
(n, N+1, if n.testBit N then pair N acc + 1 else acc)`. -/
def bitsStep (s : ℕ) : ℕ :=
  Nat.pair s.unpair.1
    (Nat.pair (s.unpair.2.unpair.1 + 1)
      (selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
        (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2))

theorem primrec_bitsStep : Nat.Primrec bitsStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1) := Nat.Primrec.left
  have hN : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair hN)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcons : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hN.pair hacc).of_eq fun _ => rfl)
  have hsel := primrec_selectFn hbit hcons hacc
  exact (hn.pair ((primrec_add₂ hN (Nat.Primrec.const 1)).pair hsel)).of_eq fun _ => rfl

theorem bitsStep_unpair11 (s : ℕ) : (bitsStep s).unpair.1 = s.unpair.1 := by
  unfold bitsStep; rw [unpair_pair_fst]

theorem bitsStep_unpair21 (s : ℕ) : (bitsStep s).unpair.2.unpair.1 = s.unpair.2.unpair.1 + 1 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_fst]

theorem bitsStep_unpair22 (s : ℕ) : (bitsStep s).unpair.2.unpair.2 =
    selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
      (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_snd]

theorem bitsStep_iter_spec (n : ℕ) (k : ℕ) :
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.1 = n ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.2 = bitsCode n k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, bitsCode]
  | succ k ih =>
    obtain ⟨hn, hN, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := bitsStep^[k] (Nat.pair n (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_⟩
    · rw [bitsStep_unpair11, hn]
    · rw [bitsStep_unpair21, hN]
    · rw [bitsStep_unpair22, hn, hN, hacc]; rfl

theorem primrec_bitsCode : Nat.Primrec (fun t => bitsCode t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec (fun z : ℕ => Nat.pair z.unpair.1 (Nat.pair 0 0)) :=
    Nat.Primrec.left.pair ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w : ℕ => bitsStep w.unpair.2.unpair.2) :=
    primrec_bitsStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.right))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (bitsStep_iter_spec t.unpair.1 t.unpair.2).2.2

/-- **`x` is a computable element when `elemSet x` is r.e.** The bounded conjunction `Eₙ ⊆ elemSet x`,
phrased over the coded list `bitsCode n n`, is r.e. by `REPred.forall_mem_decodeList`; by
`nbhd_mem_iff_subset_elemSet` this containment is exactly `x.mem (nbhd n)`. -/
theorem isComputableElement_of_elemSet_re {x : PN.Element} (hA : REPred (fun k => k ∈ elemSet x)) :
    IsComputableElement PNpres x := by
  have hforall : REPred (fun c => ∀ e ∈ decodeList c, e ∈ elemSet x) := hA.forall_mem_decodeList
  have hcode : Nat.Primrec (fun n : ℕ => bitsCode n n) :=
    (primrec_bitsCode.comp (primrec_id.pair primrec_id)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd, id_eq]
  refine REPred.of_iff (fun n => ?_) (hforall.comp hcode)
  show x.mem (nbhd n) ↔ _
  rw [nbhd_mem_iff_subset_elemSet, compl_nbhd]
  constructor
  · intro hsub e he
    exact hsub ((mem_decodeList_bitsCode n n e).mp he).2
  · intro hall k hk
    exact hall k ((mem_decodeList_bitsCode n n k).mpr ⟨lt_of_testBit_true hk, hk⟩)

/-- **What are the computable elements of `PN`? — Exercise 7.23 (Scott 1981, PRG-19).** Exactly the
recursively enumerable subsets of `ℕ`, via the identification `x ↦ elemSet x` of `PN` with the
classical powerset domain `(Set ℕ, ⊆)`. -/
theorem isComputableElement_iff_elemSet_re (x : PN.Element) :
    IsComputableElement PNpres x ↔ REPred (fun k => k ∈ elemSet x) :=
  ⟨elemSet_re_of_isComputableElement, isComputableElement_of_elemSet_re⟩

end Scott1980.Neighborhood.Exercise723
