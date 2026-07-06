import Scott1980.Neighborhood.Exercise812d

/-!
# Exercise 8.12(e) (Scott 1981, PRG-19, Lecture VIII) — `U` satisfies the extension property
relative to `V`

## 8.12(e)(a): the split's contract, as Lean declarations

`(d)`'s `IsComputableSplit P Q split` structure only ever gets *consumed*, downstream, through its
two index functions `posIdx`/`negIdx : ℕ → ℕ → ℕ → ℕ` (`xSubStep`/`ySubStep`, `Exercise812d.lean`).
This section fixes the *design* for those two functions concretely, as genuine `Nat`-valued `def`s
(no proof obligations yet — those are `(e)(c)`'s job): given a prober presentation `P` (with an
`IsComputableDiff` witness) and a target presentation `Q` equipped with a computable canonical
bisection (`ComputableBisection`, below), decide via the prober's own `emptyInterDec`/`emptyDiffDec`
deciders ((d)(2)) whether the "chosen branch" is (as far as these two deciders can tell) forced
empty, and fall back to the bisection only when neither decider fires.

Both `posIdxFromBisection`/`negIdxFromBisection` share the same outer shape and, not entirely
obviously, the same "either decider fires" branch value `m` (i.e. literally `B` itself) — one of the
two decider branches is the *genuinely correct* value in that case (`A ⊆ Xn` resp. `Xn ∩ A = ∅`
forces the corresponding piece to be exactly `B`), the other is a harmless placeholder that later
gets junk-masked (`xSubStep`'s `newJunk`) before ever being read — see the `(e)(a)` row of
`arxiv.md` for the case-by-case argument. Only the "both deciders silent" branch genuinely bisects
`B`, via the supplied `ComputableBisection`. -/

namespace Scott1980.Neighborhood

open Domain.Recursive

/-- **A computable canonical bisection of a `ComputablePresentation`'s own neighbourhoods**: two
`Nat.Primrec` index functions `left`/`right` such that `Q.X (left k)`/`Q.X (right k)` are always
disjoint and reunite to `Q.X k`. (Nonemptiness of both pieces is *not* required here — for the
concrete `U`/`V` instances this file eventually builds (`(e)(b)`/`SplitU.lean`), it is automatic
from `mem → Set.Nonempty`, so is proved separately rather than carried as a field.)

**`left_congr`/`right_congr`** are a well-definedness requirement discovered while scoping `(e)(c)`
(2026-07-05), *not* present in the earlier `arxiv.md` draft of this structure: `ComputablePresentation.X`
is generally many-to-one (distinct raw indices `k`, `k'` can present the *same* set `Q.X k = Q.X k'`),
so building a genuine classical `split : Set α → Set γ → Set α → Set γ × Set γ` *function of sets*
out of an index-level `left`/`right` needs `left`/`right`'s *output sets* — not necessarily the raw
output indices themselves — to only depend on `Q.X k` as a set, or `(e)(c)`'s `posIdx_spec`/
`negIdx_spec` obligations (stated `∀ n m k`, not just for one fixed representative) would not be
provable. Satisfied by any canonicalizing construction (e.g. `SplitU.lean`'s `splitULeft`/
`splitURight`, built via `canonCode`, which already collapses every representative of a given set to
one canonical index) — expected free for both `(e)(b)`'s `SplitV.lean` and `(f)(a)`'s reuse of
`SplitU.lean`, but must be checked (or reduced to an existing `canonCode`/`canonIdx`-invariance lemma)
when those are actually built, not merely assumed. -/
structure ComputableBisection {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W) where
  /-- Index of the "left" half of `Q.X k`. -/
  left : ℕ → ℕ
  /-- Index of the "right" half of `Q.X k`. -/
  right : ℕ → ℕ
  /-- `left` is primitive recursive. -/
  left_primrec : Nat.Primrec left
  /-- `right` is primitive recursive. -/
  right_primrec : Nat.Primrec right
  /-- The two halves are disjoint. -/
  disjoint : ∀ k, Q.X (left k) ∩ Q.X (right k) = ∅
  /-- The two halves reunite to the whole. -/
  union : ∀ k, Q.X (left k) ∪ Q.X (right k) = Q.X k
  /-- `left`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  left_congr : ∀ k k', Q.X k = Q.X k' → Q.X (left k) = Q.X (left k')
  /-- `right`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  right_congr : ∀ k k', Q.X k = Q.X k' → Q.X (right k) = Q.X (right k')

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q)

/-- **The split's "positive" (`∩`-branch) index**, as a genuine `Nat`-valued function of the three
raw indices `n` (of `A` in `P`), `m` (of `B` in `Q`), `k` (of `Xn` in `P`): fall back to `m` (i.e.
literally `B`) the moment either prober-side decider fires, and to the bisection's left half
otherwise. -/
noncomputable def posIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.left m))

/-- **The split's "negative" (`\`-branch) index.** Same outer shape as `posIdxFromBisection`,
falling back to the bisection's *right* half instead of its left. -/
noncomputable def negIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.right m))

/-! ### 8.12(e)(c)(i): decider congruence and index-function well-definedness

`emptyInterDec`/`emptyDiffDec` depend only on the *sets* `P.X n ∩ P.X k`/`P.X n \ P.X k` (via
`(d)(2)`'s `_eq_one_iff` characterizations), not on which raw index presents them — and, combined
with `left_congr`/`right_congr` above, this transports all the way up to `posIdxFromBisection`/
`negIdxFromBisection` being well-defined functions of sets, exactly what `(e)(c)(ii)`'s
`posIdx_spec`/`negIdx_spec` will need. -/

section Congr

variable {n n' k k' m m' : ℕ}

/-- `emptyInterDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. -/
theorem emptyInterDec_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyInterDec P (Nat.pair n k) = emptyInterDec P (Nat.pair n' k') := by
  have h1 := emptyInterDec_eq_one_iff P hpos hnomin n k
  have h2 := emptyInterDec_eq_one_iff P hpos hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyInterDec P (Nat.pair n k) = 1 ↔ emptyInterDec P (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyInterDec_le_one P (Nat.pair n k)
  have hle2 := emptyInterDec_le_one P (Nat.pair n' k')
  omega

/-- `emptyDiffDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. Needs `V.DiffClosed`, not just
`IsComputableDiff P` — a hypothesis gap found while scoping `(e)(c)` (2026-07-05), absent from
`(e)(c)`'s original draft signature. -/
theorem emptyDiffDec_congr (hdiffClosed : V.DiffClosed) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyDiffDec P hDiff (Nat.pair n k) = emptyDiffDec P hDiff (Nat.pair n' k') := by
  have h1 := emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n k
  have h2 := emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyDiffDec P hDiff (Nat.pair n k) = 1 ↔ emptyDiffDec P hDiff (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyDiffDec_le_one P hDiff (Nat.pair n k)
  have hle2 := emptyDiffDec_le_one P hDiff (Nat.pair n' k')
  omega

/-- **`posIdxFromBisection` is a well-defined function of sets**: its *output set*
`Q.X (posIdxFromBisection …)` depends only on `P.X n`, `Q.X m`, `P.X k` as sets, not on the raw
indices `n, m, k` chosen to present them. Four-way case split on the two `{0,1}`-valued deciders:
three of the four cases collapse to the shared fallback value `m`/`m'` (needing only `hm`); only the
"both deciders silent" case needs `B.left_congr`. -/
theorem posIdxFromBisection_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hn : P.X n = P.X n') (hk : P.X k = P.X k')
    (hm : Q.X m = Q.X m') :
    Q.X (posIdxFromBisection P hDiff B n m k) = Q.X (posIdxFromBisection P hDiff B n' m' k') := by
  unfold posIdxFromBisection
  rw [emptyInterDec_congr P hpos hnomin hn hk, emptyDiffDec_congr P hDiff hdiffClosed hnomin hn hk]
  have hle1 := emptyInterDec_le_one P (Nat.pair n' k')
  have hle2 := emptyDiffDec_le_one P hDiff (Nat.pair n' k')
  have h1 : emptyInterDec P (Nat.pair n' k') = 0 ∨ emptyInterDec P (Nat.pair n' k') = 1 := by omega
  have h2 : emptyDiffDec P hDiff (Nat.pair n' k') = 0 ∨
      emptyDiffDec P hDiff (Nat.pair n' k') = 1 := by omega
  rcases h1 with h1 | h1
  · simp only [h1, selectFn_zero]
    rcases h2 with h2 | h2
    · simp only [h2, selectFn_zero]; exact B.left_congr m m' hm
    · simp only [h2, selectFn_one]; exact hm
  · simp only [h1, selectFn_one]; exact hm

/-- **`negIdxFromBisection` is a well-defined function of sets**, the same argument as
`posIdxFromBisection_congr` with `B.right_congr` in place of `B.left_congr`. -/
theorem negIdxFromBisection_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hn : P.X n = P.X n') (hk : P.X k = P.X k')
    (hm : Q.X m = Q.X m') :
    Q.X (negIdxFromBisection P hDiff B n m k) = Q.X (negIdxFromBisection P hDiff B n' m' k') := by
  unfold negIdxFromBisection
  rw [emptyInterDec_congr P hpos hnomin hn hk, emptyDiffDec_congr P hDiff hdiffClosed hnomin hn hk]
  have hle1 := emptyInterDec_le_one P (Nat.pair n' k')
  have hle2 := emptyDiffDec_le_one P hDiff (Nat.pair n' k')
  have h1 : emptyInterDec P (Nat.pair n' k') = 0 ∨ emptyInterDec P (Nat.pair n' k') = 1 := by omega
  have h2 : emptyDiffDec P hDiff (Nat.pair n' k') = 0 ∨
      emptyDiffDec P hDiff (Nat.pair n' k') = 1 := by omega
  rcases h1 with h1 | h1
  · simp only [h1, selectFn_zero]
    rcases h2 with h2 | h2
    · simp only [h2, selectFn_zero]; exact B.right_congr m m' hm
    · simp only [h2, selectFn_one]; exact hm
  · simp only [h1, selectFn_one]; exact hm

end Congr

end ComputableBisection

end Scott1980.Neighborhood
