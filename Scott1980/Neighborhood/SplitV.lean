import Scott1980.Neighborhood.LevelSetPrimrec

/-!
# Exercise 8.12(e)(b) (Scott 1981, PRG-19, Lecture VIII) — a computable canonical bisection for `V`

## 8.12(e)(b)(i): `myFirstBit`, the least-set-bit search combinator

`V_no_minimal`'s classical proof (`Exercise812.lean`) picks its splitting bit `ℓ₀` via a bare
existential (`levelSet_nonempty_iff.mp hne`). `LevelSetPrimrec.lean`'s existing `bExistsFn`
combinator only *decides* whether such a witness exists ({0,1}-valued); it never *produces* one.
`myFirstBit m N` fills that gap: the smallest `ℓ < N` with `m.testBit ℓ = true`, computed by the
same bounded `Nat.rec`-fold idiom `bExistsFn`/`bForallFn` use, but threading the witnessing index
itself through the recursion instead of a `{0,1}` flag — a sentinel value of `N` (never itself a
valid index `< N`) marks "no witness found among the indices scanned so far", exactly mirroring
`bExistsFn`'s own `0`-sentinel for "not yet found".
-/

namespace Scott1980.Neighborhood

open Domain.Recursive

/-! ### `myFirstBit`: definition -/

/-- **The least-set-bit search combinator.** `myFirstBit m N` is the smallest `ℓ < N` with
`m.testBit ℓ = true`, or `N` itself (a sentinel, since a genuine witness is always `< N`) if no
such `ℓ` exists. Folds over `i = 0, 1, …, N - 1` in increasing order (via `Nat.rec` on `N`,
mirroring `bExistsFn`'s recursion exactly): once a witness has been found (the running value is
`< i`), it is carried forward unchanged; otherwise (`ih = i`, nothing found yet) bit `i` itself is
tested, becoming the new witness if set, or `i + 1` (the new sentinel) if not. -/
def myFirstBit (m N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i ih => selectFn (isZero (i - ih)) (selectFn (myTestBit m i) i (i + 1)) ih) N

/-! ### `myFirstBit`: primitive recursiveness -/

theorem primrec_myFirstBit : Nat.Primrec (fun t => myFirstBit t.unpair.1 t.unpair.2) := by
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hsub : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 - w.unpair.2.unpair.2) :=
    primrec_sub₂ hi hih
  have htb : Nat.Primrec (fun w : ℕ => myTestBit w.unpair.1 w.unpair.2.unpair.1) :=
    (primrec_myTestBit.comp (hm.pair hi)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hsucc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 1) := Nat.Primrec.succ.comp hi
  have hGfn : Nat.Primrec (fun w =>
      selectFn (isZero (w.unpair.2.unpair.1 - w.unpair.2.unpair.2))
        (selectFn (myTestBit w.unpair.1 w.unpair.2.unpair.1) w.unpair.2.unpair.1
          (w.unpair.2.unpair.1 + 1))
        w.unpair.2.unpair.2) :=
    primrec_selectFn (primrec_isZero.comp hsub) (primrec_selectFn htb hi hsucc) hih
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-! ### `myFirstBit`: correctness -/

/-- **Unfolding equation** for `myFirstBit` at a successor argument, stated so `rw` fires cleanly
on the outer application (mirrors `LevelSetPrimrec.lean`'s `myUpsampleJointStep_eq`). -/
theorem myFirstBit_succ (m i : ℕ) :
    myFirstBit m (i + 1) =
      selectFn (isZero (i - myFirstBit m i)) (selectFn (myTestBit m i) i (i + 1))
        (myFirstBit m i) := rfl

/-- **The core invariant, by induction on `N`.** Either `myFirstBit m N` is a genuine witness
below `N` (`< N`, `testBit` true there, and no smaller index witnesses), or nothing witnesses
below `N` at all and `myFirstBit m N` sits exactly at the sentinel `N`. -/
theorem myFirstBit_spec (m N : ℕ) :
    (myFirstBit m N < N ∧ m.testBit (myFirstBit m N) = true ∧
        ∀ j < myFirstBit m N, m.testBit j = false) ∨
      (myFirstBit m N = N ∧ ∀ j < N, m.testBit j = false) := by
  induction N with
  | zero => exact Or.inr ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ i ih =>
    rw [myFirstBit_succ]
    rcases ih with ⟨hlt, htrue, hmin⟩ | ⟨heq, hall⟩
    · have hne : i - myFirstBit m i ≠ 0 := by omega
      have hz : isZero (i - myFirstBit m i) = 0 := by
        have hle := isZero_le_one (i - myFirstBit m i)
        rcases (show isZero (i - myFirstBit m i) = 0 ∨ isZero (i - myFirstBit m i) = 1 by omega)
          with h | h
        · exact h
        · exact absurd ((isZero_eq_one_iff _).mp h) hne
      rw [hz, selectFn_zero]
      exact Or.inl ⟨by omega, htrue, hmin⟩
    · have hz : isZero (i - myFirstBit m i) = 1 :=
        (isZero_eq_one_iff _).mpr (by omega)
      rw [hz, selectFn_one]
      have hle : myTestBit m i ≤ 1 := myTestBit_le_one m i
      rcases (show myTestBit m i = 0 ∨ myTestBit m i = 1 by omega) with hbit | hbit
      · rw [hbit, selectFn_zero]
        have hfalse : m.testBit i = false := by
          by_contra hcontra
          have := (myTestBit_eq_one_iff m i).mpr (by simpa using hcontra)
          omega
        refine Or.inr ⟨by omega, fun j hj => ?_⟩
        rcases (show j < i ∨ j = i by omega) with hlt' | heq'
        · exact hall j hlt'
        · subst heq'; exact hfalse
      · rw [hbit, selectFn_one]
        have htrue : m.testBit i = true := (myTestBit_eq_one_iff m i).mp hbit
        exact Or.inl ⟨by omega, htrue, fun j hj => hall j (by omega)⟩

/-- **`myFirstBit` never overshoots its bound.** -/
theorem myFirstBit_le (m N : ℕ) : myFirstBit m N ≤ N := by
  rcases myFirstBit_spec m N with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega

/-- **`myFirstBit` finds a genuine witness whenever one exists below `N`.** -/
theorem myFirstBit_lt {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) : myFirstBit m N < N := by
  rcases myFirstBit_spec m N with ⟨hlt, -, -⟩ | ⟨heq, hall⟩
  · exact hlt
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)

/-- **`myFirstBit m N` is genuinely a set bit of `m`, whenever a witness exists below `N`.** -/
theorem myFirstBit_testBit {m N : ℕ} (h : ∃ ℓ < N, m.testBit ℓ = true) :
    m.testBit (myFirstBit m N) = true := by
  rcases myFirstBit_spec m N with ⟨-, htrue, -⟩ | ⟨heq, hall⟩
  · exact htrue
  · obtain ⟨ℓ, hℓN, hℓtrue⟩ := h
    exact absurd hℓtrue (by simpa using hall ℓ hℓN)

end Scott1980.Neighborhood
