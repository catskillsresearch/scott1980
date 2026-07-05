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

end ComputableBisection

end Scott1980.Neighborhood
