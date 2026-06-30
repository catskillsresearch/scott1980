import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring

/-!
# A choice-free recursion theory for Lecture VII (Scott 1981, PRG-19)

**Why this file exists — we roll our own and reject mathlib's recursion theory here.**
Lecture VII ("Computability in effectively given domains") needs the notions *recursively
decidable* and *recursively enumerable*. mathlib *has* these (`Computable`, `ComputablePred`,
`REPred`, `Primrec`, `Partrec`), but in mathlib `v4.30.0` essentially every *correctness lemma* of
that development is proved with tactics (`grind`, `lia`) or wrapper lemmas that **open
`Classical`** — e.g. `Computable.const`, `Primrec.const`, `Nat.unpair_pair`, `Nat.sqrt_le`, and
`Nat.Primrec.add`/`mul` all audit with `Classical.choice` in their axiom set. This project's
discipline is to keep *data* (and as much as possible) **choice-free** (`⊆ {propext, Quot.sound}`),
so we deliberately decline mathlib's classical recursion theory and instead build the slice we need
on the genuinely choice-free foundations: the raw inductives `Nat.Primrec` / `Nat.Partrec` (whose
*constructors* are choice-free) and `Nat.sqrt` / `Nat.pair` / `Nat.unpair` (whose *definitions* are
choice-free). The only tactic we lean on for arithmetic is `omega`, which is choice-free here
(unlike `grind`/`lia`).

The pattern: a relation on integer indices is *recursive* (decidable) when it has a
**primitive-recursive characteristic function** (`Nat.Primrec`, lifted to `Nat.Partrec` for the
recursive/`REPred` analogues). Tuples are encoded with `Nat.pair` (choice-free), and we reprove the
pairing round-trips (`unpair_pair'`, `pair_unpair'`) choice-free here.

Everything in this file is `⊆ {propext, Quot.sound}`.
-/

namespace Domain.Recursive

/-! ## Choice-free `Nat.sqrt` correctness

mathlib's `Nat.sqrt.iter_sq_le` / `Nat.sqrt.lt_iter_succ_sq` are the heart of `Nat.sqrt`'s
correctness, but they use `grind` / `lia` (classical). We reprove them with `omega`. -/

/-- **AM–GM for naturals (choice-free).** `4 a b ≤ (a+b)²`. Faithful port of mathlib's `private`
`Nat.AM_GM` (no classical tactics). -/
theorem amGM : ∀ {a b : ℕ}, 4 * a * b ≤ (a + b) * (a + b)
  | 0, _ => by rw [Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
  | _, 0 => by rw [Nat.mul_zero]; exact Nat.zero_le _
  | a + 1, b + 1 => by
    simpa only [Nat.mul_add, Nat.add_mul, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, Nat.one_mul,
      Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_le_add_iff_left]
      using Nat.add_le_add_right (@amGM a b) 4

/-- **Choice-free `sqrt.iter` lower bound.** `iter n guess ² ≤ n`. Faithful port of
`Nat.sqrt.iter_sq_le`, with `grind` replaced by `omega`. -/
theorem iter_sq_le (n guess : ℕ) : Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dif_pos h]
    exact iter_sq_le n ((guess + n / guess) / 2)
  else
    rw [dif_neg h]
    apply Nat.mul_le_of_le_div
    omega
  termination_by guess
  decreasing_by exact h

/-- Choice-free left-cancellation for `<` under `*` (mathlib's `Nat.lt_of_mul_lt_mul_left` is
classical). From `a*b < a*c` deduce `b < c`, by the contrapositive `c ≤ b → a*c ≤ a*b`. -/
theorem lt_of_mul_lt_mul_left' {a b c : ℕ} (h : a * b < a * c) : b < c := by
  rcases Nat.lt_or_ge b c with hbc | hbc
  · exact hbc
  · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_left a hbc))

/-- **Choice-free `sqrt.iter` upper bound.** If `n < (guess+1)²` then `n < (iter n guess + 1)²`.
Faithful port of `Nat.sqrt.lt_iter_succ_sq`, with `lia` replaced by `omega`. -/
theorem lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dif_pos h]
    suffices hsuff : n < ((guess + n / guess) / 2 + 1) * ((guess + n / guess) / 2 + 1) from
      lt_iter_succ_sq n ((guess + n / guess) / 2) hsuff
    refine lt_of_mul_lt_mul_left' (a := 4 * (guess * guess)) ?_
    apply Nat.lt_of_le_of_lt amGM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← Nat.add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux : (guess + n / guess + 1) ≤ 2 * ((guess + n / guess + 1 + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left
      (Nat.lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le _) h)) _
  else
    rw [dif_neg h]
    exact hn
  termination_by guess
  decreasing_by exact h

/-- `sqrt n` squared is `≤ n` (choice-free; mathlib's `Nat.sqrt_le` is classical). -/
theorem sqrt_le (n : ℕ) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, if_neg (Nat.not_le.mpr h)]
    exact iter_sq_le _ _
  · rw [Nat.sqrt, if_pos h]
    calc n * n ≤ 1 * n := Nat.mul_le_mul_right n h
      _ = n := Nat.one_mul n

/-- `n < (sqrt n + 1)²` (choice-free; mathlib's `Nat.lt_succ_sqrt` is classical). The initial guess
`2 ^ (log₂ n / 2 + 1)` over-shoots `√n`, which feeds `lt_iter_succ_sq`. -/
theorem lt_succ_sqrt (n : ℕ) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, if_neg (Nat.not_le.mpr h)]
    refine lt_iter_succ_sq _ _ ?_
    set g := 1 <<< (n.log2 / 2 + 1) with hg
    have hshift : g = 2 ^ (n.log2 / 2 + 1) := by rw [hg, Nat.shiftLeft_eq, Nat.one_mul]
    have hgg : g * g = 2 ^ (2 * (n.log2 / 2 + 1)) := by
      rw [hshift, ← pow_add]; congr 1; omega
    calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ (2 * (n.log2 / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = g * g := hgg.symm
      _ ≤ (g + 1) * (g + 1) := Nat.mul_le_mul (Nat.le_succ g) (Nat.le_succ g)
  · rw [Nat.sqrt, if_pos h]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n))

/-- **The square-root characterization (choice-free).** If `q² ≤ m < (q+1)²` then `sqrt m = q`. The
uniqueness step is `omega` from the two bounds plus `sqrt_le`/`lt_succ_sqrt`. -/
theorem sqrt_eq_of {m q : ℕ} (h1 : q * q ≤ m) (h2 : m < (q + 1) * (q + 1)) : Nat.sqrt m = q := by
  have hle := sqrt_le m
  have hlt := lt_succ_sqrt m
  have hq_le : q ≤ Nat.sqrt m := by
    rcases Nat.lt_or_ge (Nat.sqrt m) q with hh | hh
    · exfalso
      have ha : Nat.sqrt m + 1 ≤ q := hh
      have hmul : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ q * q := Nat.mul_le_mul ha ha
      omega
    · exact hh
  have hle_q : Nat.sqrt m ≤ q := by
    rcases Nat.lt_or_ge q (Nat.sqrt m) with hh | hh
    · exfalso
      have ha : q + 1 ≤ Nat.sqrt m := hh
      have hmul : (q + 1) * (q + 1) ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul ha ha
      omega
    · exact hh
  omega

/-- `sqrt (q² + a) = q` whenever `a ≤ 2q` (choice-free; mathlib's `Nat.sqrt_add_eq` is classical). -/
theorem sqrt_add_eq (q a : ℕ) (h : a ≤ q + q) : Nat.sqrt (q * q + a) = q := by
  refine sqrt_eq_of (Nat.le_add_right _ _) ?_
  have expand : (q + 1) * (q + 1) = q * q + q + q + 1 := Nat.succ_mul_succ q q
  omega

/-! ## Choice-free pairing round-trip

`Nat.pair`/`Nat.unpair` are themselves choice-free *definitions*; only mathlib's `unpair_pair`
*lemma* (via `sqrt_add_eq`) is classical. We reprove the round-trip on our choice-free `sqrt`. -/

/-- **`unpair ∘ pair = id` (choice-free).** Mirrors `Nat.unpair_pair`. -/
theorem unpair_pair (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b) := by
  rw [Nat.pair]
  if h : a < b then
    rw [if_pos h]
    show Nat.unpair (b * b + a) = (a, b)
    have be : Nat.sqrt (b * b + a) = b := sqrt_add_eq b a (by omega)
    simp only [Nat.unpair, be, Nat.add_sub_cancel_left, if_pos h]
  else
    rw [if_neg h]
    show Nat.unpair (a * a + a + b) = (a, b)
    have ae : Nat.sqrt (a * a + a + b) = a := by
      have e : a * a + a + b = a * a + (a + b) := by omega
      rw [e]; exact sqrt_add_eq a (a + b) (by omega)
    have e1 : a * a + a + b - a * a = a + b := by omega
    have e2 : ¬ a + b < a := by omega
    have e3 : a + b - a = b := by omega
    simp only [Nat.unpair, ae, e1, if_neg e2, e3]

/-- First projection of the pairing round-trip. -/
@[simp] theorem unpair_pair_fst (a b : ℕ) : (Nat.pair a b).unpair.1 = a := by rw [unpair_pair]

/-- Second projection of the pairing round-trip. -/
@[simp] theorem unpair_pair_snd (a b : ℕ) : (Nat.pair a b).unpair.2 = b := by rw [unpair_pair]

/-- `n ≤ (sqrt n)² + 2·sqrt n` (choice-free; needed for `pair_unpair`). -/
theorem sqrt_le_add (n : ℕ) : n ≤ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n := by
  have h := lt_succ_sqrt n
  have e : (Nat.sqrt n + 1) * (Nat.sqrt n + 1)
      = Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n + 1 := Nat.succ_mul_succ _ _
  omega

/-- **`pair ∘ unpair = id` (choice-free).** Mirrors `Nat.pair_unpair`. -/
theorem pair_unpair (n : ℕ) : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := by
  have sm : Nat.sqrt n * Nat.sqrt n + (n - Nat.sqrt n * Nat.sqrt n) = n :=
    Nat.add_sub_cancel' (sqrt_le _)
  have hadd := sqrt_le_add n
  rw [Nat.unpair]
  if h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then
    rw [if_pos h]
    show Nat.pair (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n) = n
    rw [Nat.pair, if_pos h]
    omega
  else
    rw [if_neg h]
    have hge : Nat.sqrt n ≤ n - Nat.sqrt n * Nat.sqrt n := Nat.le_of_not_lt h
    have hlt : ¬ Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by omega
    show Nat.pair (Nat.sqrt n) (n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n) = n
    rw [Nat.pair, if_neg hlt]
    omega

/-! ## Choice-free primitive-recursive arithmetic

mathlib's `Nat.Primrec.id/add/mul` are proved with `by simp`, which silently applies the *classical*
`@[simp] Nat.unpair_pair`; so they audit with `Classical.choice`. We reprove the few we need using
the choice-free round-trips above. The *constructors* of `Nat.Primrec`
(`zero/succ/left/right/pair/comp/prec`) are choice-free and used directly. -/

/-- `id` is primitive recursive (choice-free). -/
theorem primrec_id : Nat.Primrec id :=
  (Nat.Primrec.left.pair Nat.Primrec.right).of_eq fun n => pair_unpair n

/-- The `prec` recursor for addition computes the sum. -/
private theorem rec_add (a b : ℕ) : Nat.rec a (fun _ IH => IH + 1) b = a + b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH + 1) k + 1 = a + (k + 1); omega

/-- The `prec` recursor for multiplication computes the product. -/
private theorem rec_mul (a b : ℕ) : Nat.rec 0 (fun _ IH => a + IH) b = a * b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    show a + Nat.rec 0 (fun _ IH => a + IH) k = a * (k + 1)
    rw [Nat.mul_succ]; omega

/-- Addition is primitive recursive (choice-free). -/
theorem primrec_add : Nat.Primrec (Nat.unpaired (· + ·)) :=
  (Nat.Primrec.prec primrec_id
      ((Nat.Primrec.succ.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_add _ _

/-- Multiplication is primitive recursive (choice-free). -/
theorem primrec_mul : Nat.Primrec (Nat.unpaired (· * ·)) :=
  (Nat.Primrec.prec Nat.Primrec.zero
      (primrec_add.comp (Nat.Primrec.pair Nat.Primrec.left
        (Nat.Primrec.right.comp Nat.Primrec.right)))).of_eq fun p => by
    simp only [unpair_pair_fst, unpair_pair_snd, Nat.unpaired]
    exact rec_mul _ _

/-- The `prec` recursor for predecessor computes `n - 1`. -/
private theorem rec_pred (n : ℕ) : Nat.rec 0 (fun y _ => y) n = n - 1 := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- Predecessor `n ↦ n - 1` is primitive recursive (choice-free; mathlib's `Nat.Primrec.pred` is
classical). -/
theorem primrec_pred : Nat.Primrec (fun n => n - 1) :=
  ((Nat.Primrec.prec Nat.Primrec.zero (Nat.Primrec.left.comp Nat.Primrec.right)).comp
    (primrec_id.pair primrec_id)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    exact rec_pred n

/-- The `prec` recursor for truncated subtraction computes `a - b`. -/
private theorem rec_sub (a b : ℕ) : Nat.rec a (fun _ IH => IH - 1) b = a - b := by
  induction b with
  | zero => rfl
  | succ k ih => show Nat.rec a (fun _ IH => IH - 1) k - 1 = a - (k + 1); rw [ih]; omega

/-- Truncated subtraction is primitive recursive (choice-free; mathlib's `Nat.Primrec.sub` is
classical). -/
theorem primrec_sub : Nat.Primrec (Nat.unpaired (· - ·)) :=
  (Nat.Primrec.prec primrec_id
    ((primrec_pred.comp Nat.Primrec.right).comp Nat.Primrec.right)).of_eq fun p => by
    simp only [unpair_pair_snd, id_eq]
    exact rec_sub _ _

/-- `a * b = 1 ↔ a = 1 ∧ b = 1` over `ℕ` (choice-free; avoids the classical generic `mul_eq_one`). -/
theorem nat_mul_eq_one {a b : ℕ} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h => ⟨Nat.dvd_one.mp ⟨b, h.symm⟩, Nat.dvd_one.mp ⟨a, ?_⟩⟩, fun h => by rw [h.1, h.2]⟩
  rw [Nat.mul_comm] at h; exact h.symm

/-! ## Pointwise primitive-recursive arithmetic combinators

`primrec_add`/`mul`/`sub` are `Nat.unpaired` forms; the `₂` variants below take two primitive
recursive functions `f, g` and build `fun n => f n ⋆ g n` directly (composing through `Nat.pair`).
These cut the `Nat.pair`/`unpair` plumbing in larger constructions (sum's intersection function and
the list-fold engine). All choice-free. -/

/-- `fun n => f n + g n` is primitive recursive. -/
theorem primrec_add₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n + g n) :=
  (primrec_add.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n * g n` is primitive recursive. -/
theorem primrec_mul₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n * g n) :=
  (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- `fun n => f n - g n` (truncated) is primitive recursive. -/
theorem primrec_sub₂ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => f n - g n) :=
  (primrec_sub.comp (hf.pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-- Choice-free primitive-recursive **selection**: `selectFn c a b = a` if `c = 1`, `= b` if `c = 0`
(for a `{0,1}`-valued `c`), via `c * a + (1 - c) * b`. -/
def selectFn (c a b : ℕ) : ℕ := c * a + (1 - c) * b

@[simp] theorem selectFn_one (a b : ℕ) : selectFn 1 a b = a := by simp [selectFn]

@[simp] theorem selectFn_zero (a b : ℕ) : selectFn 0 a b = b := by simp [selectFn]

/-- `selectFn` of primitive-recursive `c, a, b` is primitive recursive. -/
theorem primrec_selectFn {c a b : ℕ → ℕ} (hc : Nat.Primrec c) (ha : Nat.Primrec a)
    (hb : Nat.Primrec b) : Nat.Primrec (fun n => selectFn (c n) (a n) (b n)) :=
  primrec_add₂ (primrec_mul₂ hc ha) (primrec_mul₂ (primrec_sub₂ (Nat.Primrec.const 1) hc) hb)

/-- `selectFn` driven by a decidable test through its `{0,1}` indicator is an `if`-then-else. -/
@[simp] theorem selectFn_ite {c : Prop} [Decidable c] (a b : ℕ) :
    selectFn (if c then 1 else 0) a b = if c then a else b := by
  split <;> simp [selectFn]

/-- The `{0,1}` indicator of `2 ≤ a`, written via truncated subtraction. -/
theorem geTwo_bit (a : ℕ) : 1 - (2 - a) = if 2 ≤ a then 1 else 0 := by split <;> omega

/-- The `{0,1}` indicator of `a = 0`, written via truncated subtraction. -/
theorem eqZero_bit (a : ℕ) : 1 - a = if a = 0 then 1 else 0 := by split <;> omega

/-! ## "Recursively decidable" predicates (Scott's notion, Definition 7.1)

A predicate is recursively decidable when it has a primitive-recursive `{0,1}`-valued characteristic
function. Tuples are coded by `Nat.pair`. These are the building blocks Scott's Definition 7.1 needs
(relations on indices), and the closure lemmas (`of_iff`, `comp` = reindex, `and`) let us derive the
inclusion- and equality-deciders. All choice-free. -/

/-- A unary predicate `p : ℕ → Prop` is **recursively decidable**. -/
def RecDecidable (p : ℕ → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Nat.Primrec f ∧ ∀ n, p n ↔ f n = 1

/-- A binary relation is recursively decidable when its `Nat.pair`-coding is. -/
def RecDecidable₂ (r : ℕ → ℕ → Prop) : Prop :=
  RecDecidable fun t => r t.unpair.1 t.unpair.2

/-- A ternary relation is recursively decidable when its `Nat.pair`-coding (`pair n (pair m k)`) is. -/
def RecDecidable₃ (r : ℕ → ℕ → ℕ → Prop) : Prop :=
  RecDecidable fun t => r t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

/-- Recursive decidability transfers across a pointwise logical equivalence. -/
theorem RecDecidable.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : RecDecidable p) :
    RecDecidable q := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨f, hf, fun n => (h n).trans (hfe n)⟩

/-- **Reindexing.** If `p` is recursively decidable and `g` is primitive recursive, then
`fun n => p (g n)` is recursively decidable. -/
theorem RecDecidable.comp {p : ℕ → Prop} (hp : RecDecidable p) {g : ℕ → ℕ}
    (hg : Nat.Primrec g) : RecDecidable (fun n => p (g n)) := by
  obtain ⟨f, hf, hfe⟩ := hp
  exact ⟨fun n => f (g n), hf.comp hg, fun n => hfe (g n)⟩

/-- **Conjunction.** Recursive decidability is closed under `∧` (multiply the `{0,1}` deciders). -/
theorem RecDecidable.and {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∧ q n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  obtain ⟨g, hg, hge⟩ := hq
  refine ⟨fun n => f n * g n, ?_, fun n => ?_⟩
  · exact (primrec_mul.comp (hf.pair hg)).of_eq fun n => by
      simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  · rw [nat_mul_eq_one]; exact and_congr (hfe n) (hge n)

/-- An always-true predicate is recursively decidable (constant decider `1`). -/
theorem recDecidable_of_forall {p : ℕ → Prop} (h : ∀ n, p n) : RecDecidable p :=
  ⟨fun _ => 1, Nat.Primrec.const 1, fun n => ⟨fun _ => rfl, fun _ => h n⟩⟩

/-- **From a primitive-recursive `{0,1}` characteristic to `RecDecidable`.** This is the standard
bridge when an executable Bool decider has already been realized as a numeric `{0,1}` function; the
logical equivalence is supplied separately (do not reprove the mathematics). -/
theorem RecDecidable.of_zero_one_char {p : ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (hfe : ∀ n, p n ↔ f n = 1) : RecDecidable p :=
  ⟨f, hf, hfe⟩

/-- **Paired `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n m`, reindex to `RecDecidable₂`. -/
theorem RecDecidable₂.of_paired_zero_one_char {r : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (h01 : ∀ t, f t = 0 ∨ f t = 1) (hfe : ∀ n m, r n m ↔ f (Nat.pair n m) = 1) :
    RecDecidable₂ r := by
  unfold RecDecidable₂
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair]

/-- An always-true binary relation is recursively decidable (constant decider `1`). -/
theorem recDecidable₂_of_forall {r : ℕ → ℕ → Prop} (h : ∀ n m, r n m) : RecDecidable₂ r :=
  recDecidable_of_forall (fun t => h t.unpair.1 t.unpair.2)

/-- **Equality of two primitive-recursive functions is recursively decidable.** The `{0,1}`-valued
characteristic function is `1 - ((a t - b t) + (b t - a t))` (truncated subtraction), which is `1`
exactly when `a t = b t`; primitive recursive via `primrec_sub`/`primrec_add`, and the biconditional
is `omega` (which understands truncated subtraction). -/
theorem RecDecidable.natEq {a b : ℕ → ℕ} (ha : Nat.Primrec a) (hb : Nat.Primrec b) :
    RecDecidable (fun t => a t = b t) := by
  refine ⟨fun t => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· + ·)
      (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (a t) (b t)))
        (Nat.unpaired (· - ·) (Nat.pair (b t) (a t)))))), ?_, fun t => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_add.comp
      ((primrec_sub.comp (ha.pair hb)).pair (primrec_sub.comp (hb.pair ha)))))
  · simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- **Negation.** Recursive decidability is closed under `¬` (negate the `{0,1}` decider). -/
theorem RecDecidable.not {p : ℕ → Prop} (hp : RecDecidable p) : RecDecidable (fun n => ¬ p n) := by
  obtain ⟨f, hf, hfe⟩ := hp
  refine ⟨fun n => Nat.unpaired (· - ·) (Nat.pair 1 (Nat.unpaired (· - ·) (Nat.pair 1
      (Nat.unpaired (· + ·) (Nat.pair (Nat.unpaired (· - ·) (Nat.pair (f n) 1))
        (Nat.unpaired (· - ·) (Nat.pair 1 (f n)))))))), ?_, fun n => ?_⟩
  · exact primrec_sub.comp ((Nat.Primrec.const 1).pair (primrec_sub.comp
      ((Nat.Primrec.const 1).pair (primrec_add.comp
        ((primrec_sub.comp (hf.pair (Nat.Primrec.const 1))).pair
          (primrec_sub.comp ((Nat.Primrec.const 1).pair hf)))))))
  · show ¬ p n ↔ _
    rw [hfe n]
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
    constructor <;> intro h <;> omega

/-- Every recursively decidable predicate is **decidable** (the decider is `f n = 1`, decidable
equality on `ℕ`); useful for choice-free De Morgan. -/
theorem RecDecidable.em {p : ℕ → Prop} (hp : RecDecidable p) (n : ℕ) : p n ∨ ¬ p n := by
  obtain ⟨f, _, hfe⟩ := hp
  rcases Nat.decEq (f n) 1 with h | h
  · exact Or.inr (fun hp => h ((hfe n).mp hp))
  · exact Or.inl ((hfe n).mpr h)

/-- **Disjunction.** Recursive decidability is closed under `∨`, via choice-free De Morgan
`p ∨ q ↔ ¬(¬p ∧ ¬q)` (the non-constructive direction uses `RecDecidable.em`). -/
theorem RecDecidable.or {p q : ℕ → Prop} (hp : RecDecidable p) (hq : RecDecidable q) :
    RecDecidable (fun n => p n ∨ q n) := by
  refine RecDecidable.of_iff (fun n => ?_) (hp.not.and hq.not).not
  constructor
  · rintro (h | h) ⟨hnp, hnq⟩
    · exact hnp h
    · exact hnq h
  · intro h
    rcases hp.em n with hp' | hp'
    · exact Or.inl hp'
    · rcases hq.em n with hq' | hq'
      · exact Or.inr hq'
      · exact absurd ⟨hp', hq'⟩ h

/-! ## "Recursively enumerable" predicates (Scott's notion, Definition 7.2)

Scott's Definition 7.2 asks for the neighbourhood relation `Xₙ f Yₘ` to be *recursively
enumerable*. We model "recursively enumerable" choice-free as a **projection of a recursively
decidable relation**: `p` is r.e. iff there is a recursively decidable `q` with
`p n ↔ ∃ i, q ⟨i, n⟩` (the search variable `i` is paired with `n` via `Nat.pair`). This is the
standard equivalent of Scott's prose description — "there is a primitive recursive `r` with
`y = {Y_{r(i)} ∣ i ∈ ℕ}`": the projection form additionally represents the empty set (take `q`
identically false), exactly as r.e. sets require. Every recursively decidable predicate is r.e.
(`RecDecidable.re`, dropping the search variable), and r.e.-ness transfers across pointwise
equivalence (`REPred.of_iff`). All choice-free. -/

/-- A unary predicate `p : ℕ → Prop` is **recursively enumerable**: it is the projection of a
recursively decidable relation, `p n ↔ ∃ i, q (Nat.pair i n)`. -/
def REPred (p : ℕ → Prop) : Prop :=
  ∃ q : ℕ → Prop, RecDecidable q ∧ ∀ n, p n ↔ ∃ i, q (Nat.pair i n)

/-- A binary relation is recursively enumerable when its `Nat.pair`-coding is. -/
def REPred₂ (r : ℕ → ℕ → Prop) : Prop :=
  REPred fun t => r t.unpair.1 t.unpair.2

/-- **Every recursively decidable predicate is recursively enumerable.** Use the decider as the
relation `q ⟨i, n⟩ := p n` (a reindex of `p` along `unpair.2`, dropping the search variable `i`); the
witness `i = 0` makes the projection trivial. -/
theorem RecDecidable.re {p : ℕ → Prop} (hp : RecDecidable p) : REPred p := by
  refine ⟨fun t => p t.unpair.2, hp.comp Nat.Primrec.right, fun n => ?_⟩
  simp only [unpair_pair_snd]
  exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩

/-- A recursively decidable binary relation is recursively enumerable. -/
theorem RecDecidable₂.re {r : ℕ → ℕ → Prop} (hr : RecDecidable₂ r) : REPred₂ r :=
  RecDecidable.re hr

/-- Recursive enumerability transfers across a pointwise logical equivalence. -/
theorem REPred.of_iff {p q : ℕ → Prop} (h : ∀ n, q n ↔ p n) (hp : REPred p) : REPred q := by
  obtain ⟨r, hr, hre⟩ := hp
  exact ⟨r, hr, fun n => (h n).trans (hre n)⟩

/-- An always-true predicate is recursively enumerable. -/
theorem rePred_of_forall {p : ℕ → Prop} (h : ∀ n, p n) : REPred p :=
  (recDecidable_of_forall h).re

/-! ### Closure properties of r.e. predicates (for Proposition 7.3 and Theorem 7.4)

The projection-of-decidable form makes r.e.-ness closed under primitive-recursive **reindexing**
(`REPred.comp`), **conjunction** (`REPred.and`, pairing the two search variables), and
**existential projection** over `ℕ` (`REPred.proj`, absorbing the projected variable into the search
variable). These are exactly the moves Scott's `g ∘ f` needs: `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`. -/

/-- **Reindexing.** If `p` is r.e. and `g` is primitive recursive, then `fun n => p (g n)` is r.e.
(absorb `g` into the decidable relation along `unpair.2`). -/
theorem REPred.comp {p : ℕ → Prop} (hp : REPred p) {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    REPred (fun n => p (g n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun t => q (Nat.pair t.unpair.1 (g t.unpair.2)),
    hq.comp (Nat.Primrec.left.pair (hg.comp Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact hqe (g n)

/-- **Conjunction.** Recursive enumerability is closed under `∧`: combine the two decidable relations
and run the two searches in parallel (pairing the search variables `i, j` into a single `w`). -/
theorem REPred.and {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∧ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => a (Nat.pair u.unpair.1.unpair.1 u.unpair.2)
      ∧ b (Nat.pair u.unpair.1.unpair.2 u.unpair.2),
    (ha.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)).and
      (hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hae n, hbe n]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨Nat.pair i j, by simp only [unpair_pair_fst, unpair_pair_snd]; exact ⟨hi, hj⟩⟩
  · rintro ⟨w, hw1, hw2⟩
    exact ⟨⟨w.unpair.1, hw1⟩, ⟨w.unpair.2, hw2⟩⟩

/-- **Existential projection.** If `p` is r.e. then so is `fun n => ∃ i, p ⟨i, n⟩`: fold the new
existential variable `i` into the search variable (pairing it with the decidable relation's own
search variable `j`). -/
theorem REPred.proj {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun n => ∃ i, p (Nat.pair i n)) := by
  obtain ⟨q, hq, hqe⟩ := hp
  refine ⟨fun u => q (Nat.pair u.unpair.1.unpair.2 (Nat.pair u.unpair.1.unpair.1 u.unpair.2)),
    hq.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
      ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right)), fun n => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨i, hi⟩
    rw [hqe (Nat.pair i n)] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨Nat.pair i j, by simpa only [unpair_pair_fst, unpair_pair_snd] using hj⟩
  · rintro ⟨w, hw⟩
    refine ⟨w.unpair.1, ?_⟩
    rw [hqe (Nat.pair w.unpair.1 n)]
    exact ⟨w.unpair.2, hw⟩

/-- **Disjunction of r.e. predicates is r.e.** A witness `w` carries a tag `w.1 ∈ {0,1}` selecting
which disjunct's search index `w.2` to use; the underlying relation is recursively decidable by
`RecDecidable.or`/`.and`/`.natEq`. (Used for the sum-mapping `f + g` of Theorem 7.4.) -/
theorem REPred.or {p q : ℕ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun n => p n ∨ q n) := by
  obtain ⟨a, ha, hae⟩ := hp
  obtain ⟨b, hb, hbe⟩ := hq
  refine ⟨fun u => (a (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 0)
      ∨ (b (Nat.pair u.unpair.1.unpair.2 u.unpair.2) ∧ u.unpair.1.unpair.1 = 1), ?_, fun n => ?_⟩
  · refine RecDecidable.or (RecDecidable.and ?_ ?_) (RecDecidable.and ?_ ?_)
    · exact ha.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
    · exact hb.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
    · exact RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  · show p n ∨ q n ↔ _
    rw [hae n, hbe n]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · refine ⟨Nat.pair 0 i, Or.inl ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
      · refine ⟨Nat.pair 1 i, Or.inr ⟨?_, ?_⟩⟩
        · simpa only [unpair_pair_fst, unpair_pair_snd] using hi
        · simp only [unpair_pair_fst]
    · rintro ⟨w, hw⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hw
      rcases hw with ⟨hi, _⟩ | ⟨hi, _⟩
      · exact Or.inl ⟨w.unpair.2, hi⟩
      · exact Or.inr ⟨w.unpair.2, hi⟩

/-! ## A choice-free primitive-recursive fold engine over `Nat`-coded lists

Scott's function-space deciders (Theorem 7.5) range over *finite lists* of neighborhood indices.
To stay choice-free we encode such a list as a single natural via `encodeList` and process it with a
genuinely primitive-recursive `foldCode`. The key results are:

* `encodeList`            — `List ℕ → ℕ`, with `l.length ≤ encodeList l` (`encodeList_length_le`);
* `foldCode stp p z c`    — folds the list coded by `c`, threading an accumulator and a fixed
                            parameter `p`, with `stp` the (coded) step function;
* `foldCode_eq`           — `foldCode` on `encodeList l` equals the corresponding `List.foldl`;
* `primrec_foldCode`      — `foldCode` is primitive recursive in all of its (primrec) inputs.

`foldStep` walks one entry: the state is `pair remainingCode accumulator`; an empty remaining code
(`= 0`) is a fixed point, otherwise it pops the head and applies `stp`. -/

/-- `b ≤ pair a b` (choice-free; avoids mathlib's `Nat.right_le_pair` to keep the axiom set clean). -/
theorem le_pair_right (a b : ℕ) : b ≤ Nat.pair a b := by
  have hbb : b ≤ b * b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left b h
  unfold Nat.pair
  split <;> omega

/-- `a ≤ pair a b` (choice-free). -/
theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair
  split <;> omega

/-- Encode a list of naturals as a single natural: `[] ↦ 0`, `a :: l ↦ pair a (encodeList l) + 1`.
The `+1` keeps the empty list (code `0`) distinguishable from any nonempty list. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (encodeList l) + 1

/-- The length of a list is bounded by its code; this is the fuel bound that lets a `c`-fold iterate
enough times to consume the whole list coded by `c`. -/
theorem encodeList_length_le : ∀ l : List ℕ, l.length ≤ encodeList l
  | [] => Nat.le_refl 0
  | a :: l => by
    simp only [encodeList, List.length_cons]
    have hrec := encodeList_length_le l
    have hle : encodeList l ≤ Nat.pair a (encodeList l) := le_pair_right a (encodeList l)
    omega

/-- One step of the code-walking fold. The state `s = pair rc acc` carries the remaining code `rc`
and accumulator `acc`. If `rc = 0` the state is a fixed point; otherwise `rc - 1 = pair head tail`,
and the step pops `head`, recurses on `tail`, and updates `acc := stp (pair head (pair acc params))`. -/
def foldStep (stp : ℕ → ℕ) (params s : ℕ) : ℕ :=
  selectFn (1 - s.unpair.1) s
    (Nat.pair (s.unpair.1 - 1).unpair.2
      (stp (Nat.pair (s.unpair.1 - 1).unpair.1 (Nat.pair s.unpair.2 params))))

/-- Empty remaining code: the fold state is unchanged. -/
theorem foldStep_zero (stp : ℕ → ℕ) (params acc : ℕ) :
    foldStep stp params (Nat.pair 0 acc) = Nat.pair 0 acc := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

/-- Nonempty remaining code `pair a t + 1`: pop `a`, recurse on `t`, update the accumulator. -/
theorem foldStep_pos (stp : ℕ → ℕ) (params a t acc : ℕ) :
    foldStep stp params (Nat.pair (Nat.pair a t + 1) acc)
      = Nat.pair t (stp (Nat.pair a (Nat.pair acc params))) := by
  unfold foldStep
  simp only [unpair_pair_fst, unpair_pair_snd]
  have h1 : 1 - (Nat.pair a t + 1) = 0 := by omega
  have h2 : Nat.pair a t + 1 - 1 = Nat.pair a t := by omega
  rw [h1, h2, selectFn_zero, unpair_pair_fst, unpair_pair_snd]

/-- Fold the list coded by `c`, threading accumulator `z` and parameter `params`. Implemented as
`c`-fold iteration of `foldStep` from the initial state `pair c z`, projecting out the accumulator. -/
def foldCode (stp : ℕ → ℕ) (params z c : ℕ) : ℕ :=
  ((foldStep stp params)^[c] (Nat.pair c z)).unpair.2

/-- `Nat.rec` with a counter-independent step is just function iteration (choice-free). Needed to
bridge the `Nat.Primrec.prec` form (a `Nat.rec`) with `foldCode`'s `Function.iterate` form. -/
theorem rec_const_iterate (f : ℕ → ℕ) (s : ℕ) :
    ∀ k : ℕ, Nat.rec (motive := fun _ => ℕ) s (fun _ ih => f ih) k = f^[k] s
  | 0 => rfl
  | (k + 1) => by
      rw [Function.iterate_succ_apply']
      exact congrArg f (rec_const_iterate f s k)

/-- Core correctness of the iteration: starting from `pair (encodeList l) acc`, after at least
`l.length` steps the accumulator equals the `List.foldl` of the step over `l`. -/
theorem foldStep_iterate (stp : ℕ → ℕ) (params : ℕ) :
    ∀ (k : ℕ) (l : List ℕ) (acc : ℕ), l.length ≤ k →
      ((foldStep stp params)^[k] (Nat.pair (encodeList l) acc)).unpair.2
        = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) acc l := by
  intro k
  induction k with
  | zero =>
    intro l acc hlen
    cases l with
    | nil => simp only [Function.iterate_zero_apply, encodeList, unpair_pair_snd, List.foldl_nil]
    | cons a l' => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    intro l acc hlen
    rw [Function.iterate_succ_apply]
    cases l with
    | nil =>
      rw [show encodeList ([] : List ℕ) = 0 from rfl, foldStep_zero]
      exact ih [] acc (Nat.zero_le k)
    | cons a l' =>
      have hlen' : l'.length ≤ k := by simp only [List.length_cons] at hlen; omega
      rw [show encodeList (a :: l') = Nat.pair a (encodeList l') + 1 from rfl, foldStep_pos,
        ih l' (stp (Nat.pair a (Nat.pair acc params))) hlen', List.foldl_cons]

/-- **Correctness of `foldCode`.** Folding the code of `l` equals the corresponding `List.foldl`. -/
theorem foldCode_eq (stp : ℕ → ℕ) (params z : ℕ) (l : List ℕ) :
    foldCode stp params z (encodeList l)
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z l := by
  unfold foldCode
  exact foldStep_iterate stp params (encodeList l) l z (encodeList_length_le l)

/-- `n.unpair.2 ≤ n` (choice-free); the decreasing measure for `decodeList`. -/
theorem unpair_snd_le (n : ℕ) : n.unpair.2 ≤ n := by
  have h := le_pair_right n.unpair.1 n.unpair.2
  rwa [pair_unpair] at h

/-- Decode a natural back into a list of naturals, inverting `encodeList`. Well-founded on the
remaining code (`c.unpair.2 ≤ c < c + 1`). -/
def decodeList : ℕ → List ℕ
  | 0 => []
  | (c + 1) => c.unpair.1 :: decodeList c.unpair.2
decreasing_by exact Nat.lt_succ_of_le (unpair_snd_le c)

theorem decodeList_zero : decodeList 0 = [] := by rw [decodeList]

theorem decodeList_succ (c : ℕ) :
    decodeList (c + 1) = c.unpair.1 :: decodeList c.unpair.2 := by
  rw [decodeList]

/-- `encodeList ∘ decodeList = id`: every natural is the code of its decoded list. -/
theorem encodeList_decodeList (c : ℕ) : encodeList (decodeList c) = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp only [decodeList_zero, encodeList]
    | succ d =>
      rw [decodeList_succ, encodeList, ih d.unpair.2 (Nat.lt_succ_of_le (unpair_snd_le d)),
        pair_unpair]

/-- The decoded list is no longer than its code. -/
theorem decodeList_length_le (c : ℕ) : (decodeList c).length ≤ c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp [decodeList_zero]
    | succ d =>
      rw [decodeList_succ, List.length_cons]
      have hle := unpair_snd_le d
      have := ih d.unpair.2 (Nat.lt_succ_of_le hle)
      omega

/-- **Correctness of `foldCode` on an arbitrary code.** `foldCode` over any natural `c` equals the
`List.foldl` over the list `c` decodes to. -/
theorem foldCode_eq' (stp : ℕ → ℕ) (params z c : ℕ) :
    foldCode stp params z c
      = List.foldl (fun acc x => stp (Nat.pair x (Nat.pair acc params))) z (decodeList c) := by
  conv_lhs => rw [← encodeList_decodeList c]
  rw [foldCode_eq]

/-- `foldStep` (with the parameter packed into the state as `pair params state`) is primitive
recursive whenever the step `stp` is. This is the workhorse for `primrec_foldCode`. -/
theorem primrec_foldStepPacked {stp : ℕ → ℕ} (hstp : Nat.Primrec stp) :
    Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) := by
  have hparams : Nat.Primrec (fun w => w.unpair.1) := Nat.Primrec.left
  have hstate : Nat.Primrec (fun w => w.unpair.2) := Nat.Primrec.right
  have hrc : Nat.Primrec (fun w => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hcond : Nat.Primrec (fun w => 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.const 1) hrc
  have hrcm1 : Nat.Primrec (fun w => w.unpair.2.unpair.1 - 1) :=
    primrec_sub₂ hrc (Nat.Primrec.const 1)
  have hhead : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hrcm1
  have htail : Nat.Primrec (fun w => (w.unpair.2.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hrcm1
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2 w.unpair.1) := hacc.pair hparams
  have harg : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) := hhead.pair hinner
  have hstpv : Nat.Primrec
      (fun w => stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1))) := hstp.comp harg
  have helse : Nat.Primrec
      (fun w => Nat.pair (w.unpair.2.unpair.1 - 1).unpair.2
        (stp (Nat.pair (w.unpair.2.unpair.1 - 1).unpair.1
          (Nat.pair w.unpair.2.unpair.2 w.unpair.1)))) := htail.pair hstpv
  exact (primrec_selectFn hcond hstate helse).of_eq fun _ => rfl

/-- **`foldCode` is primitive recursive** in all of its (primitive-recursive) inputs. -/
theorem primrec_foldCode {stp : ℕ → ℕ} (hstp : Nat.Primrec stp)
    {params z c : ℕ → ℕ} (hp : Nat.Primrec params) (hz : Nat.Primrec z) (hc : Nat.Primrec c) :
    Nat.Primrec (fun n => foldCode stp (params n) (z n) (c n)) := by
  have hfoldw : Nat.Primrec (fun w => foldStep stp w.unpair.1 w.unpair.2) :=
    primrec_foldStepPacked hstp
  have hg : Nat.Primrec (fun x => foldStep stp x.unpair.1.unpair.1 x.unpair.2.unpair.2) :=
    (hfoldw.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
      (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun _ => by
        simp only [unpair_pair_fst, unpair_pair_snd]
  have hprec := Nat.Primrec.prec Nat.Primrec.right hg
  refine (Nat.Primrec.right.comp
    (hprec.comp ((hp.pair (hc.pair hz)).pair hc))).of_eq fun n => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rw [rec_const_iterate]
  rfl

/-! ## Primitive-recursive exponentiation (for the `2^q` subset bound)

The funSpace consistency decider quantifies over all `2^q` subsets of a `q`-element step-list, so it
needs `2^q` as a primitive-recursive bound. Choice-free (mathlib's `Nat.Primrec` lemmas for `^` route
through classical `simp`). -/

/-- `Nat.rec 1 (· * b)` computes `b ^ e` (choice-free). -/
theorem recPow_eq (b : ℕ) :
    ∀ e, Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => ih * b) e = b ^ e
  | 0 => (pow_zero b).symm
  | e + 1 => by rw [pow_succ]; exact congrArg (· * b) (recPow_eq b e)

/-- **Exponentiation is primitive recursive** (`unpaired (b, e) ↦ b ^ e`), choice-free. -/
theorem primrec_pow : Nat.Primrec (Nat.unpaired fun b e => b ^ e) := by
  have hg : Nat.Primrec (fun w => w.unpair.2.unpair.2 * w.unpair.1) :=
    primrec_mul₂ (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  refine (Nat.Primrec.prec (Nat.Primrec.const 1) hg).of_eq (fun p => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact recPow_eq p.unpair.1 p.unpair.2

/-- `n ↦ 2 ^ g n` is primitive recursive when `g` is. -/
theorem primrec_two_pow {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (fun n => 2 ^ g n) :=
  (primrec_pow.comp ((Nat.Primrec.const 2).pair hg)).of_eq fun n => by
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]

/-! ## Halving (`/2`, `%2`) for per-subset bit extraction

The funSpace consistency fold walks a step-list while consuming a subset bitmask `b` one bit at a
time: at each entry it reads `b % 2` (is this entry in the subset?) and recurses on `b / 2`. Only
division/modulus by the literal `2` is needed — which `omega` discharges directly — so this stays
choice-free without a general `div`/`mod`. Computed jointly by `halfParity n = pair (n/2) (n%2)`. -/

/-- `halfParity n = pair (n / 2) (n % 2)`, built by structural recursion: from `(h, p)` for `n`, the
value for `n+1` is `(h + p, 1 - p)` (carry on odd→even). -/
def halfParity (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun _ ih => Nat.pair (ih.unpair.1 + ih.unpair.2) (1 - ih.unpair.2)) n

theorem halfParity_spec (n : ℕ) : halfParity n = Nat.pair (n / 2) (n % 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.pair ((halfParity n).unpair.1 + (halfParity n).unpair.2) (1 - (halfParity n).unpair.2)
        = Nat.pair ((n + 1) / 2) ((n + 1) % 2)
    rw [ih, unpair_pair_fst, unpair_pair_snd]
    congr 1 <;> omega

theorem primrec_halfParity : Nat.Primrec halfParity := by
  have hIH : Nat.Primrec (fun w => w.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hstep : Nat.Primrec (fun w => Nat.pair (w.unpair.2.unpair.2.unpair.1 + w.unpair.2.unpair.2.unpair.2)
      (1 - w.unpair.2.unpair.2.unpair.2)) :=
    (primrec_add₂ (Nat.Primrec.left.comp hIH) (Nat.Primrec.right.comp hIH)).pair
      (primrec_sub₂ (Nat.Primrec.const 1) (Nat.Primrec.right.comp hIH))
  refine ((Nat.Primrec.prec (Nat.Primrec.const 0) hstep).comp
    ((Nat.Primrec.const 0).pair primrec_id)).of_eq (fun n => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rfl

theorem primrec_div2 : Nat.Primrec (fun n => n / 2) :=
  (Nat.Primrec.left.comp primrec_halfParity).of_eq fun n => by
    rw [halfParity_spec, unpair_pair_fst]

theorem primrec_mod2 : Nat.Primrec (fun n => n % 2) :=
  (Nat.Primrec.right.comp primrec_halfParity).of_eq fun n => by
    rw [halfParity_spec, unpair_pair_snd]

/-! ## Bounded quantifiers for recursively decidable predicates

Scott's function-space consistency decider (Theorem 7.5) is a *bounded universal* statement: a list of
step-pairs is consistent iff for **every** subset (coded by a bitmask `b < 2^q`) a component condition
holds. Bounded quantification of a recursively decidable predicate is again recursively decidable —
choice-free, via an explicit `Nat.rec` fold of the `{0,1}` indicator. -/

/-- Indicator of `v = 1`, as a `{0,1}`-valued primitive-recursive function. -/
def isOne (v : ℕ) : ℕ := 1 - ((v - 1) + (1 - v))

theorem isOne_le_one (v : ℕ) : isOne v ≤ 1 := by unfold isOne; omega

theorem isOne_eq_one_iff (v : ℕ) : isOne v = 1 ↔ v = 1 := by
  unfold isOne; constructor <;> (intro h; omega)

theorem primrec_isOne : Nat.Primrec isOne :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const 1))
      (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))

/-- `{0,1}` test for `n = 0`. -/
def isZero (n : ℕ) : ℕ := 1 - min n 1

theorem isZero_eq_one_iff (n : ℕ) : isZero n = 1 ↔ n = 0 := by
  unfold isZero; omega

theorem primrec_isZero : Nat.Primrec isZero := by
  have hmin : Nat.Primrec (fun n => min n 1) :=
    (primrec_sub₂ primrec_id (primrec_sub₂ primrec_id (Nat.Primrec.const 1))).of_eq fun n => by
      rcases n with _ | n <;> simp [min]
  exact primrec_sub₂ (Nat.Primrec.const 1) hmin

/-- `{0,1}` test for `f n ≤ g n` (truncated subtraction). -/
theorem primrec_le {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => isZero (f n - g n)) :=
  primrec_isZero.comp (primrec_sub₂ hf hg)

/-- `{0,1}`-valued `max` of two primitive-recursive functions. -/
theorem primrec_max {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.max (f n) (g n)) := by
  refine (primrec_selectFn (primrec_le hf hg) hg hf).of_eq fun n => by
    unfold selectFn isZero Nat.max
    by_cases h : f n ≤ g n
    · simp [Nat.sub_eq_zero_iff_le.mpr h, Nat.max_eq_right h]
    · have hlt : g n < f n := Nat.lt_of_not_ge h
      have hpos : 0 < f n - g n := Nat.sub_pos_of_lt hlt
      have hmin : min (f n - g n) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
      simp [isZero, hmin, Nat.max_eq_left (Nat.le_of_lt hlt)]

/-- Primitive-recursive `if` on a `{0,1}` condition. -/
theorem primrec_ite {c t f : ℕ → ℕ} (hc : Nat.Primrec c) (ht : Nat.Primrec t) (hf : Nat.Primrec f) :
    Nat.Primrec (fun n => selectFn (c n) (t n) (f n)) :=
  primrec_selectFn hc ht hf

/-- The `{0,1}`-valued bounded-`∀` indicator: `1` iff `g (pair i n) = 1` for all `i < N`. Folded
right-to-left with `selectFn` so the result stays in `{0,1}`. -/
def bForallFn (g : ℕ → ℕ) (n N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 1 (fun i ih => selectFn ih (isOne (g (Nat.pair i n))) 0) N

theorem bForallFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bForallFn g n N ≤ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ N ih =>
    show selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 ≤ 1
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]; exact Nat.zero_le 1
    · rw [h, selectFn_one]; exact isOne_le_one _

theorem bForallFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bForallFn g n N = 1 ↔ ∀ i, i < N → g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    constructor
    · intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _; rfl
  | succ N ih =>
    have hstep : bForallFn g n (N + 1)
        = selectFn (bForallFn g n N) (isOne (g (Nat.pair N n))) 0 := rfl
    have hle := bForallFn_le_one g n N
    rw [hstep]
    rcases (show bForallFn g n N = 0 ∨ bForallFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero]
      constructor
      · intro hcontra; exact absurd hcontra (by decide)
      · intro hall
        have hb : bForallFn g n N = 1 := ih.mpr (fun i hi => hall i (Nat.lt_succ_of_lt hi))
        rw [h0] at hb; exact hb
    · rw [h1, selectFn_one, isOne_eq_one_iff]
      constructor
      · intro hgN i hi
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · exact (ih.mp h1) i hlt
        · subst heq; exact hgN
      · intro hall; exact hall N (Nat.lt_succ_self N)

/-- The `{0,1}`-valued bounded-`∃` indicator: `1` iff `∃ i < N, g (pair i n) = 1`. Folded
right-to-left with `selectFn` so the result stays in `{0,1}`. -/
def bExistsFn (g : ℕ → ℕ) (n N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => selectFn ih 1 (isOne (g (Nat.pair i n)))) N

theorem bExistsFn_le_one (g : ℕ → ℕ) (n N : ℕ) : bExistsFn g n N ≤ 1 := by
  induction N with
  | zero => simp [bExistsFn]
  | succ N ih =>
    show selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) ≤ 1
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h | h
    · rw [h, selectFn_zero]
      exact isOne_le_one _
    · rw [h, selectFn_one]

theorem bExistsFn_eq_one_iff (g : ℕ → ℕ) (n N : ℕ) :
    bExistsFn g n N = 1 ↔ ∃ i, i < N ∧ g (Nat.pair i n) = 1 := by
  induction N with
  | zero =>
    simp [bExistsFn]
  | succ N ih =>
    have hstep : bExistsFn g n (N + 1)
        = selectFn (bExistsFn g n N) 1 (isOne (g (Nat.pair N n))) := rfl
    rw [hstep]
    have hle := bExistsFn_le_one g n N
    rcases (show bExistsFn g n N = 0 ∨ bExistsFn g n N = 1 by omega) with h0 | h1
    · rw [h0, selectFn_zero, isOne_eq_one_iff]
      constructor
      · intro hgN; exact ⟨N, Nat.lt_succ_self N, hgN⟩
      · intro ⟨i, hi, hg⟩
        rcases (show i < N ∨ i = N by omega) with hlt | heq
        · have hne : bExistsFn g n N = 1 := ih.mpr ⟨i, hlt, hg⟩
          omega
        · subst heq; exact hg
    · rw [h1, selectFn_one]
      constructor
      · intro _
        obtain ⟨i, hi, hg⟩ := ih.mp h1
        exact ⟨i, Nat.lt_succ_of_lt hi, hg⟩
      · intro _; rfl

theorem primrec_bExistsFn {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => bExistsFn g t.unpair.1 t.unpair.2) := by
  have hGfn : Nat.Primrec (fun w =>
      selectFn w.unpair.2.unpair.2 1 (isOne (g (Nat.pair w.unpair.2.unpair.1 w.unpair.1)))) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.const 1)
      (primrec_isOne.comp (hg.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  refine (hprec.comp (Nat.Primrec.left.pair Nat.Primrec.right)).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

/-- **Bounded universal quantifier preserves recursive decidability.** If `p` is recursively decidable
and `bound` is primitive recursive, then `fun n => ∀ i < bound n, p (pair i n)` is recursively
decidable (choice-free). -/
theorem RecDecidable.bForall {p : ℕ → Prop} (hp : RecDecidable p) {bound : ℕ → ℕ}
    (hb : Nat.Primrec bound) :
    RecDecidable (fun n => ∀ i, i < bound n → p (Nat.pair i n)) := by
  obtain ⟨f, hf, hfspec⟩ := hp
  refine ⟨fun n => bForallFn f n (bound n), ?_, ?_⟩
  · have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2
        (isOne (f (Nat.pair w.unpair.2.unpair.1 w.unpair.1))) 0) :=
      primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
        (primrec_isOne.comp (hf.comp
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
        (Nat.Primrec.const 0)
    have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
    refine (hprec.comp (primrec_id.pair hb)).of_eq (fun n => ?_)
    simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
    rfl
  · intro n
    show (∀ i, i < bound n → p (Nat.pair i n)) ↔ bForallFn f n (bound n) = 1
    rw [bForallFn_eq_one_iff]
    exact ⟨fun h i hi => (hfspec _).mp (h i hi), fun h i hi => (hfspec _).mpr (h i hi)⟩

/-- `decodeList ∘ encodeList = id` (the round-trip the other way from `encodeList_decodeList`). -/
theorem decodeList_encodeList : ∀ l : List ℕ, decodeList (encodeList l) = l
  | [] => by rw [encodeList, decodeList_zero]
  | a :: l => by
    rw [encodeList, decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_encodeList l]

/-! ## Bounded universal quantification of an r.e. predicate over a coded list

The "computable elements = computable maps" half of Theorem 7.5 needs r.e.-ness closed under
`∀ e ∈ decodeList c, p e` for an r.e. `p`. Classically this is the standard "bounded `∀` of r.e. is
r.e."; choice-free we realise the search for the finite tuple of witnesses as a *single* code `w`
whose decoded list supplies one witness per list entry, threaded through a `foldCode`. -/

/-- The pure (set-theoretic) witness-threading fold step. The accumulator is `pair remWitness flag`:
at the list head `x` we pop a witness `i` (the `decodeList` head of `remWitness`, i.e.
`(remWitness - 1).unpair.1`) with new remaining code `(remWitness - 1).unpair.2`, and `AND` the flag
with `isOne (qc ⟨i, x⟩)`. -/
def reForallF (qc : ℕ → ℕ) (acc x : ℕ) : ℕ :=
  Nat.pair (acc.unpair.1 - 1).unpair.2
    (selectFn acc.unpair.2 (isOne (qc (Nat.pair (acc.unpair.1 - 1).unpair.1 x))) 0)

/-- The `foldCode`-form step (parameter unused), used to package `reForallF` primitive-recursively. -/
def reForallStp (qc : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.2
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1))) 0)

/-- The `{0,1}`-flag computed by threading witness code `w` through the list coded by `c`. -/
def reForallChar (qc : ℕ → ℕ) (w c : ℕ) : ℕ :=
  (foldCode (reForallStp qc) 0 (Nat.pair w 1) c).unpair.2

theorem reForallStp_eq (qc : ℕ → ℕ) (acc x : ℕ) :
    reForallStp qc (Nat.pair x (Nat.pair acc 0)) = reForallF qc acc x := by
  unfold reForallStp reForallF
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem reForallChar_eq (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c
      = (List.foldl (reForallF qc) (Nat.pair w 1) (decodeList c)).unpair.2 := by
  have hfun : (fun (acc x : ℕ) => reForallStp qc (Nat.pair x (Nat.pair acc 0))) = reForallF qc := by
    funext acc x; exact reForallStp_eq qc acc x
  unfold reForallChar
  rw [foldCode_eq', hfun]

/-- **Core induction.** Threading witness code `w` through `l`, the final flag is `1` iff the start
flag was `1` and, position by position, the `k`-th witness of `decodeList w` satisfies `qc`. -/
theorem reForallF_foldl_eq_one_iff (qc : ℕ → ℕ) :
    ∀ (l : List ℕ) (w flag : ℕ), flag ≤ 1 →
      ((List.foldl (reForallF qc) (Nat.pair w flag) l).unpair.2 = 1 ↔
        flag = 1 ∧ ∀ k, k < l.length →
          qc (Nat.pair ((decodeList w).getD k 0) (l.getD k 0)) = 1) := by
  intro l
  induction l with
  | nil =>
    intro w flag _
    simp only [List.foldl_nil, unpair_pair_snd, List.length_nil, Nat.not_lt_zero,
      false_implies, implies_true, and_true]
  | cons x l ih =>
    intro w flag hflag
    have hi : (decodeList w).getD 0 0 = (w - 1).unpair.1 := by
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.1 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.fst Nat.unpair_zero
        rw [decodeList_zero, List.getD_nil, hz]
      · rw [decodeList_succ, List.getD_cons_zero, Nat.add_sub_cancel]
    have htail : ∀ k, (decodeList w).getD (k + 1) 0 = (decodeList (w - 1).unpair.2).getD k 0 := by
      intro k
      rcases w with _ | c
      · have hz : ((0 : ℕ) - 1).unpair.2 = 0 := by
          rw [Nat.zero_sub]; exact congrArg Prod.snd Nat.unpair_zero
        rw [decodeList_zero, hz, decodeList_zero, List.getD_nil, List.getD_nil]
      · rw [decodeList_succ, List.getD_cons_succ, Nat.add_sub_cancel]
    have hstep : List.foldl (reForallF qc) (Nat.pair w flag) (x :: l)
        = List.foldl (reForallF qc) (Nat.pair (w - 1).unpair.2
            (selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0)) l := by
      rw [List.foldl_cons]
      congr 1
      show reForallF qc (Nat.pair w flag) x = _
      unfold reForallF
      rw [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set flag' := selectFn flag (isOne (qc (Nat.pair (w - 1).unpair.1 x))) 0 with hflag'def
    have hflag'le : flag' ≤ 1 := by
      rw [hflag'def]
      rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih (w - 1).unpair.2 flag' hflag'le]
    constructor
    · rintro ⟨hf', hrest⟩
      have hsplit : flag = 1 ∧ qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        rw [hflag'def] at hf'
        rcases (show flag = 0 ∨ flag = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hf'; exact absurd hf' (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hf'; exact ⟨h, hf'⟩
      refine ⟨hsplit.1, fun k hk => ?_⟩
      rcases k with _ | k'
      · rw [List.getD_cons_zero, hi]; exact hsplit.2
      · rw [List.getD_cons_succ, htail]
        exact hrest k' (by simp only [List.length_cons] at hk; omega)
    · rintro ⟨hflag1, hall⟩
      have hhead : qc (Nat.pair (w - 1).unpair.1 x) = 1 := by
        have := hall 0 (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_zero, hi] at this
      refine ⟨?_, fun k hk => ?_⟩
      · rw [hflag'def, hflag1, selectFn_one, isOne_eq_one_iff]; exact hhead
      · have := hall (k + 1) (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_succ, htail] at this

theorem reForallChar_eq_one_iff (qc : ℕ → ℕ) (w c : ℕ) :
    reForallChar qc w c = 1 ↔
      ∀ k, k < (decodeList c).length →
        qc (Nat.pair ((decodeList w).getD k 0) ((decodeList c).getD k 0)) = 1 := by
  rw [reForallChar_eq, reForallF_foldl_eq_one_iff qc (decodeList c) w 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem primrec_reForallStp {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (reForallStp qc) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hrw : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hpm : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1 - 1) :=
    primrec_sub₂ hrw (Nat.Primrec.const 1)
  have hi : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1) :=
    Nat.Primrec.left.comp hpm
  have hrw' : Nat.Primrec (fun w : ℕ => (w.unpair.2.unpair.1.unpair.1 - 1).unpair.2) :=
    Nat.Primrec.right.comp hpm
  have hcall : Nat.Primrec (fun w : ℕ =>
      qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1)) :=
    hqc.comp (hi.pair hx)
  have hB : Nat.Primrec (fun w : ℕ =>
      selectFn w.unpair.2.unpair.1.unpair.2
        (isOne (qc (Nat.pair (w.unpair.2.unpair.1.unpair.1 - 1).unpair.1 w.unpair.1))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp hcall) (Nat.Primrec.const 0)
  exact (hrw'.pair hB).of_eq (fun _ => rfl)

theorem primrec_reForallChar {qc : ℕ → ℕ} (hqc : Nat.Primrec qc) :
    Nat.Primrec (fun t => reForallChar qc t.unpair.1 t.unpair.2) := by
  have hfold := primrec_foldCode (primrec_reForallStp hqc) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair (Nat.Primrec.const 1)) Nat.Primrec.right
  exact (Nat.Primrec.right.comp hfold).of_eq (fun _ => rfl)

/-- **Bounded `∀` over a coded list preserves recursive enumerability.** If `p` is r.e. then so is
`fun c => ∀ e ∈ decodeList c, p e`: the finite tuple of per-entry witnesses is packed into a single
search code `w`, and the `{0,1}` flag `reForallChar` makes the body recursively decidable. -/
theorem REPred.forall_mem_decodeList {p : ℕ → Prop} (hp : REPred p) :
    REPred (fun c => ∀ e ∈ decodeList c, p e) := by
  obtain ⟨q, hq, hqe⟩ := hp
  obtain ⟨qc, hqcp, hqcs⟩ := hq
  -- per-entry: `p e ↔ ∃ j, qc ⟨j, e⟩ = 1`
  have hpe : ∀ e, p e ↔ ∃ j, qc (Nat.pair j e) = 1 := by
    intro e; rw [hqe e]; exact exists_congr (fun j => hqcs (Nat.pair j e))
  -- membership gives an index whose `getD` recovers the element
  have hmemgetD : ∀ (l : List ℕ) (e : ℕ), e ∈ l → ∃ k, k < l.length ∧ l.getD k 0 = e := by
    intro l
    induction l with
    | nil => intro e he; cases he
    | cons a l ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨0, by simp only [List.length_cons]; omega, by rw [List.getD_cons_zero]⟩
      · obtain ⟨k, hk, hek⟩ := ih e he'
        exact ⟨k + 1, by simp only [List.length_cons]; omega, by rw [List.getD_cons_succ]; exact hek⟩
  refine ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2 = 1,
    ⟨fun t => reForallChar qc t.unpair.1 t.unpair.2, primrec_reForallChar hqcp,
      fun _ => Iff.rfl⟩, fun c => ?_⟩
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · intro hall
    -- build a witness list for `decodeList c`
    have hwit : ∀ (l : List ℕ), (∀ e ∈ l, ∃ j, qc (Nat.pair j e) = 1) →
        ∃ iws : List ℕ, ∀ k, k < l.length →
          qc (Nat.pair (iws.getD k 0) (l.getD k 0)) = 1 := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | cons e l ih =>
        intro hh
        obtain ⟨j, hj⟩ := hh e (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨iws, hiws⟩ := ih (fun e' he' => hh e' (List.mem_cons.mpr (Or.inr he')))
        refine ⟨j :: iws, fun k hk => ?_⟩
        rcases k with _ | k'
        · rw [List.getD_cons_zero, List.getD_cons_zero]; exact hj
        · rw [List.getD_cons_succ, List.getD_cons_succ]
          exact hiws k' (by simp only [List.length_cons] at hk; omega)
    obtain ⟨iws, hiws⟩ := hwit (decodeList c) (fun e he => (hpe e).mp (hall e he))
    refine ⟨encodeList iws, (reForallChar_eq_one_iff qc _ c).mpr (fun k hk => ?_)⟩
    rw [decodeList_encodeList]; exact hiws k hk
  · rintro ⟨w, hw⟩
    rw [reForallChar_eq_one_iff] at hw
    intro e he
    obtain ⟨k, hk, hek⟩ := hmemgetD (decodeList c) e he
    rw [hpe e]
    refine ⟨(decodeList w).getD k 0, ?_⟩
    have := hw k hk
    rwa [hek] at this

/-! ### Bounded `∀` over a coded list with a parameter (for `curry`, Theorem 7.5)

`curry`'s neighbourhood relation is a bounded `∀ e ∈ decodeList c, p n e` whose body depends on a
*parameter* `n` (the `𝒟₀`-index) as well as the list entry `e`. We reduce this to
`REPred.forall_mem_decodeList` by primitively-recursively re-coding the list `decodeList c` into the
list of pairs `⟨n, e⟩` (order is irrelevant under `∀ ∈`), so the parameterised body becomes the
plain `fun s => p s.1 s.2` over the re-coded list. -/

/-- Prepend the *pair* `⟨n, x⟩` onto the list coded by `acc`. -/
def mapPairStep (n acc x : ℕ) : ℕ := Nat.pair (Nat.pair n x) acc + 1

/-- `foldCode`-shaped wrapper of `mapPairStep` (parameter `n` threaded via the `params` slot). -/
def mapPairStp (w : ℕ) : ℕ :=
  mapPairStep w.unpair.2.unpair.2 w.unpair.2.unpair.1 w.unpair.1

theorem mapPairStp_eq (n acc x : ℕ) :
    mapPairStp (Nat.pair x (Nat.pair acc n)) = mapPairStep n acc x := by
  unfold mapPairStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem decodeList_mapPairStep (n acc x : ℕ) :
    decodeList (mapPairStep n acc x) = Nat.pair n x :: decodeList acc := by
  unfold mapPairStep; rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]

theorem decodeList_foldl_mapPairStp (n : ℕ) (el : List ℕ) (acc : ℕ) :
    decodeList (List.foldl (fun acc x => mapPairStp (Nat.pair x (Nat.pair acc n))) acc el)
      = (el.map (Nat.pair n ·)).reverse ++ decodeList acc := by
  induction el generalizing acc with
  | nil => simp
  | cons e el ih =>
    rw [List.foldl_cons, ih, mapPairStp_eq, decodeList_mapPairStep, List.map_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **`mapPairCode n c`** codes the list `(decodeList c).map ⟨n, ·⟩` (reversed). -/
def mapPairCode (n c : ℕ) : ℕ := foldCode mapPairStp n 0 c

theorem decodeList_mapPairCode (n c : ℕ) :
    decodeList (mapPairCode n c) = ((decodeList c).map (Nat.pair n ·)).reverse := by
  unfold mapPairCode
  rw [foldCode_eq']
  have h := decodeList_foldl_mapPairStp n (decodeList c) 0
  rwa [decodeList_zero, List.append_nil] at h

theorem primrec_mapPairStp : Nat.Primrec mapPairStp := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((h22.pair h1).pair h21)).of_eq (fun _ => rfl)

theorem primrec_mapPairCode : Nat.Primrec (fun t => mapPairCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_mapPairStp Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq (fun _ => rfl)

/-- **Parameterised bounded `∀` over a coded list preserves recursive enumerability.** If `p` is an
r.e. binary relation then `fun t => ∀ e ∈ decodeList t.2, p t.1 e` is r.e.: re-code the list into the
pairs `⟨t.1, e⟩` (`mapPairCode`) and apply the unparameterised `forall_mem_decodeList`. -/
theorem REPred.forall_mem_decodeList₂ {p : ℕ → ℕ → Prop} (hp : REPred₂ p) :
    REPred (fun t => ∀ e ∈ decodeList t.unpair.2, p t.unpair.1 e) := by
  have hp' : REPred (fun s => p s.unpair.1 s.unpair.2) := hp
  have hbase : REPred (fun c => ∀ e' ∈ decodeList c, p e'.unpair.1 e'.unpair.2) :=
    hp'.forall_mem_decodeList
  refine REPred.of_iff (fun t => ?_) (hbase.comp primrec_mapPairCode)
  rw [decodeList_mapPairCode]
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · rintro hall e' ⟨e, he, rfl⟩
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact hall e he
  · intro hall e he
    simpa only [unpair_pair_fst, unpair_pair_snd]
      using hall (Nat.pair t.unpair.1 e) ⟨e, he, rfl⟩

/-! ## Choice-free primitive-recursive bitwise OR (for Example 7.8, the powerset `PN`)

Scott's Example 7.8 enumerates the finite subsets of `ℕ` by `Eₙ = {k ∣ n.testBit k}` and presents the
powerset domain `PN` with neighbourhoods `ℕ ∖ Eₙ`. The intersection of two neighbourhoods is
`(ℕ ∖ Eₙ) ∩ (ℕ ∖ Eₘ) = ℕ ∖ (Eₙ ∪ Eₘ) = ℕ ∖ E_{n ||| m}` (bitwise OR), and Scott notes that the
relation `Eₙ ∪ Eₘ = E_k` is *recursive*. The presentation therefore needs `(n, m) ↦ n ||| m` as a
**primitive-recursive** intersection function.

mathlib's `Nat.lor` is defined through `Nat.bitwise`/`binaryRec`, none of which is exposed as a
`Nat.Primrec`. We build it choice-free by *iterating* a fixed step `lorStep` (which strips the low
bit of each argument, ORs them, and accumulates with a doubling weight). The result coincides with
`Nat.lor` (`myLor_eq_lor`), so all the set-level facts can use mathlib's clean `Nat.testBit_lor`. -/

/-- The low-bit OR `(x ||| y) % 2`, in arithmetic `{0,1}`-valued form (so it is primitive recursive
without referring to `Nat.lor`). Equal to `(x ||| y) % 2` by `lowOr_eq_mod`. -/
def lowOr (x y : ℕ) : ℕ := 1 - (1 - (x % 2 + y % 2))

theorem primrec_lowOr : Nat.Primrec (fun t => lowOr t.unpair.1 t.unpair.2) := by
  have hx : Nat.Primrec (fun t : ℕ => t.unpair.1 % 2) := primrec_mod2.comp Nat.Primrec.left
  have hy : Nat.Primrec (fun t : ℕ => t.unpair.2 % 2) := primrec_mod2.comp Nat.Primrec.right
  exact (primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_sub₂ (Nat.Primrec.const 1) (primrec_add₂ hx hy))).of_eq fun _ => rfl

/-- `lowOr x y = (x ||| y) % 2`: both sides depend only on the low bits `x % 2`, `y % 2`. -/
theorem lowOr_eq_mod (x y : ℕ) : lowOr x y = (x ||| y) % 2 := by
  have key : ((x ||| y) % 2 = 1) ↔ (x % 2 = 1 ∨ y % 2 = 1) := by
    have hb := Nat.testBit_lor x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_or]
  have e1 : (x ||| y) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold lowOr
  -- explicit case split avoids feeding `omega` an `↔`/disjunction (which pulls `Classical.choice`)
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · -- x%2=0, y%2=0 : `(x|||y)%2 ≠ 1`
    have hne : (x ||| y) % 2 ≠ 1 := fun h => by rcases key.mp h with h' | h' <;> omega
    omega
  · -- x%2=0, y%2=1
    rw [key.mpr (Or.inr hy)]
  · -- x%2=1, y%2=0
    rw [key.mpr (Or.inl hx)]
  · -- x%2=1, y%2=1
    rw [key.mpr (Or.inl hx)]

/-- Packed iteration state `pair (pair curA curB) (pair weight acc)` for the bitwise-OR fold. -/
def lorStep (s : ℕ) : ℕ :=
  Nat.pair (Nat.pair (s.unpair.1.unpair.1 / 2) (s.unpair.1.unpair.2 / 2))
    (Nat.pair (2 * s.unpair.2.unpair.1)
      (s.unpair.2.unpair.2 + s.unpair.2.unpair.1 * lowOr s.unpair.1.unpair.1 s.unpair.1.unpair.2))

theorem primrec_lorStep : Nat.Primrec lorStep := by
  have hA : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hB : Nat.Primrec (fun s : ℕ => s.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hW : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hAcc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hlow : Nat.Primrec (fun s : ℕ => lowOr s.unpair.1.unpair.1 s.unpair.1.unpair.2) :=
    (primrec_lowOr.comp (hA.pair hB)).of_eq fun s => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (((primrec_div2.comp hA).pair (primrec_div2.comp hB)).pair
    ((primrec_mul₂ (Nat.Primrec.const 2) hW).pair
      (primrec_add₂ hAcc (primrec_mul₂ hW hlow)))).of_eq fun _ => rfl

/-- The iterative bitwise OR: iterate `lorStep` `a + b` times (enough to consume every set bit of `a`
and `b`) from the initial state, and read off the accumulator. -/
def myLor (a b : ℕ) : ℕ :=
  (lorStep^[a + b] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2

/-- One recursion step for `Nat.lor` on the low bit: `x ||| y = 2 (x/2 ||| y/2) + lowOr x y`. -/
theorem lor_low_rec (x y : ℕ) : x ||| y = 2 * (x / 2 ||| y / 2) + lowOr x y := by
  have hdiv : (x ||| y) / 2 = x / 2 ||| y / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_add_one, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_add_one,
      Nat.testBit_add_one]
  have hmod := lowOr_eq_mod x y
  conv_lhs => rw [← Nat.div_add_mod (x ||| y) 2]
  rw [hdiv, hmod]

/-- **Invariant of the bitwise-OR iteration.** After `k` steps the two running arguments are
`a / 2^k`, `b / 2^k`, the weight is `2^k`, and `acc + 2^k · (a/2^k ||| b/2^k) = a ||| b`. -/
theorem lorStep_iter_spec (a b : ℕ) : ∀ k,
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 = a / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 = b / 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 = 2 ^ k ∧
    (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2 +
        2 ^ k * (a / 2 ^ k ||| b / 2 ^ k) = a ||| b := by
  intro k
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, unpair_pair_fst, unpair_pair_snd, pow_zero,
      Nat.div_one, Nat.one_mul, Nat.zero_add, true_and]
  | succ k ih =>
    obtain ⟨hA, hB, hW, hAcc⟩ := ih
    rw [Function.iterate_succ_apply']
    have hdd : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hdd' : b / 2 ^ (k + 1) = (b / 2 ^ k) / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    -- compute the four projections of one `lorStep`
    have p11 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.1
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_fst]
    have p12 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.1.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 / 2 := by
      unfold lorStep; rw [unpair_pair_fst, unpair_pair_snd]
    have p21 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.1
        = 2 * (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_fst]
    have p22 : (lorStep (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0)))).unpair.2.unpair.2
        = (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.2
          + (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.2.unpair.1
            * lowOr (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.1
                (lorStep^[k] (Nat.pair (Nat.pair a b) (Nat.pair 1 0))).unpair.1.unpair.2 := by
      unfold lorStep; rw [unpair_pair_snd, unpair_pair_snd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [p11, hA, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p12, hB, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [p21, hW, ← pow_succ']
    · rw [p22, hA, hB, hW, hdd, hdd', pow_succ, ← hAcc, lor_low_rec (a / 2 ^ k) (b / 2 ^ k)]
      ring

/-- **Correctness of the iterative bitwise OR.** `myLor a b = a ||| b`. -/
theorem myLor_eq_lor (a b : ℕ) : myLor a b = a ||| b := by
  unfold myLor
  obtain ⟨_, _, _, hAcc⟩ := lorStep_iter_spec a b (a + b)
  have ha0 : a / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right a b)))
  have hb0 : b / 2 ^ (a + b) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_left b a)))
  rw [ha0, hb0] at hAcc
  simpa using hAcc

/-! ## Bounded quantifiers over a coded list preserving recursive *decidability*

`reForallChar`/`REPred.forall_mem_decodeList` above handle bounded `∀` over `decodeList` for *r.e.*
predicates (which need a witness search). When the body is already recursively *decidable* the story
is simpler: fold the `{0,1}` decider over the list with a Boolean `AND` (for `∀`) or `OR` (for `∃`),
no witness threading. These are exactly what Scott's Smyth power-domain equality relation
(Proposition 7.10) needs: equality of two finite unions of down-sets unfolds to
`(∀ a ∈ A, ∃ b ∈ B, …) ∧ (∀ b ∈ B, ∃ a ∈ A, …)`, a nested bounded ∀/∃ over coded lists. All
choice-free. The list is coded by the *first* argument; the *second* argument is a free parameter
threaded through the `foldCode` `params` slot. -/

/-- AND-fold step (`foldCode` shape): `acc ↦ acc ∧ isOne (g ⟨head, params⟩)`. -/
def allListStp (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 (isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) 0

/-- OR-fold step (`foldCode` shape): `acc ↦ acc ∨ isOne (g ⟨head, params⟩)`. -/
def existsListStp (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 1 (isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2)))

/-- The `{0,1}` flag of the bounded `∀ e ∈ decodeList c, g ⟨e, p⟩ = 1`. -/
def allListChar (g : ℕ → ℕ) (p c : ℕ) : ℕ := foldCode (allListStp g) p 1 c

/-- The `{0,1}` flag of the bounded `∃ e ∈ decodeList c, g ⟨e, p⟩ = 1`. -/
def existsListChar (g : ℕ → ℕ) (p c : ℕ) : ℕ := foldCode (existsListStp g) p 0 c

theorem allListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    allListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc (isOne (g (Nat.pair x p))) 0 := by
  unfold allListStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem existsListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    existsListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc 1 (isOne (g (Nat.pair x p))) := by
  unfold existsListStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem allListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c
      = List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) 1 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => allListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) := by
    funext acc x; exact allListStp_eq g acc x p
  unfold allListChar; rw [foldCode_eq', hfun]

theorem existsListChar_eq (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c
      = List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) 0 (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => existsListStp g (Nat.pair x (Nat.pair acc p)))
      = (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) := by
    funext acc x; exact existsListStp_eq g acc x p
  unfold existsListChar; rw [foldCode_eq', hfun]

/-- Core induction for the AND-fold: starting from `acc ≤ 1`, the fold is `1` iff `acc = 1` and every
list entry passes the decider `g`. -/
theorem allList_foldl_eq_one_iff (g : ℕ → ℕ) (p : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
      (List.foldl (fun acc x => selectFn acc (isOne (g (Nat.pair x p))) 0) acc l = 1 ↔
        acc = 1 ∧ ∀ x ∈ l, g (Nat.pair x p) = 1) := by
  intro l
  induction l with
  | nil => intro acc _; simp only [List.foldl_nil, List.not_mem_nil, false_implies, implies_true,
      and_true]
  | cons x l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    set acc' := selectFn acc (isOne (g (Nat.pair x p))) 0 with hacc'
    have hacc'le : acc' ≤ 1 := by
      rw [hacc']
      rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact Nat.zero_le 1
      · rw [h, selectFn_one]; exact isOne_le_one _
    rw [ih acc' hacc'le]
    constructor
    · rintro ⟨hacc'1, hrest⟩
      have hsplit : acc = 1 ∧ g (Nat.pair x p) = 1 := by
        rw [hacc'] at hacc'1
        rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
        · rw [h, selectFn_zero] at hacc'1; exact absurd hacc'1 (by decide)
        · rw [h, selectFn_one, isOne_eq_one_iff] at hacc'1; exact ⟨h, hacc'1⟩
      refine ⟨hsplit.1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hsplit.2
      · exact hrest y hy'
    · rintro ⟨hacc1, hall⟩
      have hhead : g (Nat.pair x p) = 1 := hall x (List.mem_cons.mpr (Or.inl rfl))
      refine ⟨?_, fun y hy => hall y (List.mem_cons.mpr (Or.inr hy))⟩
      rw [hacc', hacc1, selectFn_one, isOne_eq_one_iff]; exact hhead

/-- Core induction for the OR-fold: starting from `acc ≤ 1`, the fold is `1` iff `acc = 1` or some
list entry passes the decider `g`. -/
theorem existsList_foldl_eq_one_iff (g : ℕ → ℕ) (p : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 1 →
      (List.foldl (fun acc x => selectFn acc 1 (isOne (g (Nat.pair x p)))) acc l = 1 ↔
        acc = 1 ∨ ∃ x ∈ l, g (Nat.pair x p) = 1) := by
  intro l
  induction l with
  | nil => intro acc _; simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false,
      or_false]
  | cons x l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    set acc' := selectFn acc 1 (isOne (g (Nat.pair x p))) with hacc'
    have hacc'le : acc' ≤ 1 := by
      rw [hacc']
      rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
      · rw [h, selectFn_zero]; exact isOne_le_one _
      · rw [h, selectFn_one]
    rw [ih acc' hacc'le]
    constructor
    · rintro (hacc'1 | ⟨y, hy, hyg⟩)
      · rw [hacc'] at hacc'1
        rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
        · rw [h, selectFn_zero, isOne_eq_one_iff] at hacc'1
          exact Or.inr ⟨x, List.mem_cons.mpr (Or.inl rfl), hacc'1⟩
        · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons.mpr (Or.inr hy), hyg⟩
    · rintro (hacc1 | ⟨y, hy, hyg⟩)
      · exact Or.inl (by rw [hacc', hacc1, selectFn_one])
      · rcases List.mem_cons.mp hy with rfl | hy'
        · refine Or.inl ?_
          rw [hacc']
          rcases (show acc = 0 ∨ acc = 1 by omega) with h | h
          · rw [h, selectFn_zero, isOne_eq_one_iff]; exact hyg
          · rw [h, selectFn_one]
        · exact Or.inr ⟨y, hy', hyg⟩

theorem allListChar_eq_one_iff (g : ℕ → ℕ) (p c : ℕ) :
    allListChar g p c = 1 ↔ ∀ x ∈ decodeList c, g (Nat.pair x p) = 1 := by
  rw [allListChar_eq, allList_foldl_eq_one_iff g p (decodeList c) 1 (Nat.le_refl 1)]
  simp only [true_and]

theorem existsListChar_eq_one_iff (g : ℕ → ℕ) (p c : ℕ) :
    existsListChar g p c = 1 ↔ ∃ x ∈ decodeList c, g (Nat.pair x p) = 1 := by
  rw [existsListChar_eq, existsList_foldl_eq_one_iff g p (decodeList c) 0 (Nat.zero_le 1)]
  simp only [Nat.zero_ne_one, false_or]

theorem primrec_allListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (allListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc hcall (Nat.Primrec.const 0)).of_eq fun _ => rfl

theorem primrec_existsListStp {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (existsListStp g) := by
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcall : Nat.Primrec (fun w : ℕ => isOne (g (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    primrec_isOne.comp (hg.comp (hx.pair hp))
  exact (primrec_selectFn hacc (Nat.Primrec.const 1) hcall).of_eq fun _ => rfl

theorem primrec_allListChar {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => allListChar g t.unpair.2 t.unpair.1) :=
  (primrec_foldCode (primrec_allListStp hg) Nat.Primrec.right (Nat.Primrec.const 1)
    Nat.Primrec.left).of_eq fun _ => rfl

theorem primrec_existsListChar {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => existsListChar g t.unpair.2 t.unpair.1) :=
  (primrec_foldCode (primrec_existsListStp hg) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

/-- `{0,1}` flag: `1` iff `n` encodes a binary digit (`0` or `1`). -/
def isBinDigit (n : ℕ) : ℕ :=
  selectFn (isOne (1 - n)) 1 (selectFn (isOne (2 - n)) 1 0)

theorem isBinDigit_eq_one_iff (n : ℕ) : isBinDigit n = 1 ↔ n = 0 ∨ n = 1 := by
  unfold isBinDigit selectFn isOne
  match n with | 0 | 1 => simp | n + 2 => simp

theorem primrec_isBinDigit : Nat.Primrec isBinDigit := by
  have h01 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id)
  have h12 := primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) primrec_id)
  refine (primrec_selectFn h01 (Nat.Primrec.const 1)
    (primrec_selectFn h12 (Nat.Primrec.const 1) (Nat.Primrec.const 0))).of_eq fun _ => rfl

/-- `{0,1}` flag: every entry of `decodeList c` is a binary digit. -/
def allBinDigitsChar (c : ℕ) : ℕ :=
  allListChar (fun t => isBinDigit t.unpair.1) 0 c

theorem allBinDigitsChar_eq_one_iff (c : ℕ) :
    allBinDigitsChar c = 1 ↔ ∀ x ∈ decodeList c, x = 0 ∨ x = 1 := by
  unfold allBinDigitsChar
  rw [allListChar_eq_one_iff]
  simp [unpair_pair_fst, unpair_pair_snd, isBinDigit_eq_one_iff]

set_option maxHeartbeats 800000 in
theorem primrec_allBinDigitsChar : Nat.Primrec allBinDigitsChar := by
  unfold allBinDigitsChar
  exact (primrec_foldCode (primrec_allListStp (primrec_isBinDigit.comp Nat.Primrec.left))
    (Nat.Primrec.const 0) (Nat.Primrec.const 1) primrec_id).of_eq fun _ => rfl

/-- **Bounded `∀` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∀ e ∈ decodeList c, q e p` is too (the list is coded by
the first argument, `p` is a free parameter). Choice-free. -/
theorem RecDecidable₂.bForallList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∀ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => allListChar g t.unpair.2 t.unpair.1, primrec_allListChar hgp, fun t => ?_⟩
  show (∀ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ allListChar g t.unpair.2 t.unpair.1 = 1
  rw [allListChar_eq_one_iff]
  refine forall_congr' fun e => forall_congr' fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this

/-- **Bounded `∃` over a coded list preserves recursive decidability.** If `q` is a recursively
decidable binary relation then `fun c p => ∃ e ∈ decodeList c, q e p` is too. Choice-free. -/
theorem RecDecidable₂.bExistsList {q : ℕ → ℕ → Prop} (hq : RecDecidable₂ q) :
    RecDecidable₂ (fun c p => ∃ e ∈ decodeList c, q e p) := by
  obtain ⟨g, hgp, hgs⟩ := hq
  refine ⟨fun t => existsListChar g t.unpair.2 t.unpair.1, primrec_existsListChar hgp, fun t => ?_⟩
  show (∃ e ∈ decodeList t.unpair.1, q e t.unpair.2) ↔ existsListChar g t.unpair.2 t.unpair.1 = 1
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  have := hgs (Nat.pair e t.unpair.2)
  simp only [unpair_pair_fst, unpair_pair_snd] at this
  exact this

/-- **Swap the two arguments** of a recursively decidable binary relation. -/
theorem RecDecidable₂.swap {r : ℕ → ℕ → Prop} (hr : RecDecidable₂ r) :
    RecDecidable₂ (fun a b => r b a) := by
  have hswap : Nat.Primrec (fun t => Nat.pair t.unpair.2 t.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  refine RecDecidable.of_iff (fun t => ?_) (hr.comp hswap)
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Bitwise OR is primitive recursive** (the `Nat.unpaired` form), choice-free. -/
theorem primrec_myLor : Nat.Primrec (fun t => myLor t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec
      (fun z => Nat.pair (Nat.pair z.unpair.1 z.unpair.2) (Nat.pair 1 0)) :=
    (Nat.Primrec.left.pair Nat.Primrec.right).pair
      ((Nat.Primrec.const 1).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w => lorStep w.unpair.2.unpair.2) :=
    primrec_lorStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  have hcount : Nat.Primrec (fun t => t.unpair.1 + t.unpair.2) :=
    primrec_add₂ Nat.Primrec.left Nat.Primrec.right
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair hcount))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  rfl

/-! ## Random access and tabulation of coded lists (for the iterate `𝒟^∞`, Exercise 7.15)

`𝒟^∞`-neighbourhoods are finitely-supported sequences of `𝒟`-neighbourhoods, coded as a list of
component indices. The presentation's relations index *positions* of the list, so we need
primitive-recursive list **indexing** `nthCode c i d = (decodeList c).getD i d` and a **tabulation**
`tabCode g p B` coding `[g⟨0,p⟩, …, g⟨B-1,p⟩]` (used for the intersection function). Both choice-free,
both built from the existing `foldCode`/`Nat.Primrec.prec` engine. -/

/-- `foldCode`-shaped indexing step. State `pair counter result`, parameter the target index `i`;
bump the counter and overwrite the result exactly when `counter = i` (via the `{0,1}` equality bit
`1 - ((counter - i) + (i - counter))`). -/
def nthStp (w : ℕ) : ℕ :=
  Nat.pair (w.unpair.2.unpair.1.unpair.1 + 1)
    (selectFn (1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
        + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1)))
      w.unpair.1 w.unpair.2.unpair.1.unpair.2)

theorem nthStp_val (i x s r : ℕ) :
    nthStp (Nat.pair x (Nat.pair (Nat.pair s r) i))
      = Nat.pair (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r) := by
  unfold nthStp; simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Primitive-recursive indexing into a coded list.** `nthCode c i d = (decodeList c).getD i d`. -/
def nthCode (c i d : ℕ) : ℕ := (foldCode nthStp i (Nat.pair 0 d) c).unpair.2

theorem nthCode_foldl (i : ℕ) : ∀ (l : List ℕ) (s r : ℕ),
    (List.foldl (fun acc x => nthStp (Nat.pair x (Nat.pair acc i))) (Nat.pair s r) l).unpair.2
      = if i < s then r else l.getD (i - s) r := by
  intro l
  induction l with
  | nil => intro s r; simp only [List.foldl_nil, unpair_pair_snd, List.getD_nil]; split <;> rfl
  | cons x l ih =>
    intro s r
    rw [List.foldl_cons, nthStp_val, ih (s + 1) (selectFn (1 - ((s - i) + (i - s))) x r)]
    by_cases h : i = s
    · subst h
      have he : (1 : ℕ) - ((i - i) + (i - i)) = 1 := by omega
      rw [he, selectFn_one, if_neg (lt_irrefl i), if_pos (Nat.lt_succ_self i), Nat.sub_self,
        List.getD_cons_zero]
    · by_cases h2 : i < s
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, if_pos h2, if_pos (Nat.lt_succ_of_lt h2)]
      · have he : (1 : ℕ) - ((s - i) + (i - s)) = 0 := by omega
        rw [he, selectFn_zero, if_neg h2, if_neg (show ¬ i < s + 1 by omega),
          show i - s = (i - (s + 1)) + 1 by omega, List.getD_cons_succ]

theorem nthCode_eq (c i d : ℕ) : nthCode c i d = (decodeList c).getD i d := by
  unfold nthCode
  rw [foldCode_eq']
  have h := nthCode_foldl i (decodeList c) 0 d
  rw [if_neg (Nat.not_lt_zero i), Nat.sub_zero] at h
  exact h

theorem primrec_nthStp : Nat.Primrec nthStp := by
  have hcount : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hres : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hbit : Nat.Primrec (fun w : ℕ => 1 - ((w.unpair.2.unpair.1.unpair.1 - w.unpair.2.unpair.2)
      + (w.unpair.2.unpair.2 - w.unpair.2.unpair.1.unpair.1))) :=
    primrec_sub₂ (Nat.Primrec.const 1)
      (primrec_add₂ (primrec_sub₂ hcount hi) (primrec_sub₂ hi hcount))
  exact ((Nat.Primrec.succ.comp hcount).pair (primrec_selectFn hbit hx hres)).of_eq fun _ => rfl

/-- `nthCode` is primitive recursive in `(c, i, d)` (coded as `pair c (pair i d)`). -/
theorem primrec_nthCode : Nat.Primrec
    (fun t => nthCode t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hfold := primrec_foldCode primrec_nthStp (Nat.Primrec.left.comp Nat.Primrec.right)
    ((Nat.Primrec.const 0).pair (Nat.Primrec.right.comp Nat.Primrec.right)) Nat.Primrec.left
  exact (Nat.Primrec.right.comp hfold).of_eq fun _ => rfl

/-- `tabCode`'s recursion step, in the `Nat.Primrec.prec` packaging: the state is
`pair a (pair y IH)` with `a = pair B p`; it prepends `g⟨B-1-y, p⟩` onto the tail `IH`. -/
def tabStep (g : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (g (Nat.pair (w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) w.unpair.1.unpair.2))
    w.unpair.2.unpair.2 + 1

theorem tabStep_val (g : ℕ → ℕ) (a y IH : ℕ) :
    tabStep g (Nat.pair a (Nat.pair y IH))
      = Nat.pair (g (Nat.pair (a.unpair.1 - 1 - y) a.unpair.2)) IH + 1 := by
  unfold tabStep; simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Primitive-recursive tabulation.** With `a = pair B p`, `tabCode g a B` codes the list
`[g⟨0,p⟩, g⟨1,p⟩, …, g⟨B-1,p⟩]` (length `B`). Built directly from the `prec` step `tabStep`. -/
def tabCode (g : ℕ → ℕ) (a B : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun y IH => tabStep g (Nat.pair a (Nat.pair y IH))) B

/-- After `K ≤ B` steps the accumulated code decodes to the indices `B-K, …, B-1`. -/
theorem decodeList_tabCode_aux (g : ℕ → ℕ) (B p : ℕ) :
    ∀ K, K ≤ B → decodeList (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)
      = (List.range' (B - K) K).map (fun j => g (Nat.pair j p)) := by
  intro K
  induction K with
  | zero => intro _; simp [decodeList_zero]
  | succ K ih =>
    intro hK
    have hKB : K ≤ B := Nat.le_of_succ_le hK
    show decodeList (tabStep g (Nat.pair (Nat.pair B p) (Nat.pair K
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => tabStep g (Nat.pair (Nat.pair B p) (Nat.pair y IH))) K)))) = _
    rw [tabStep_val]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, ih hKB,
      show B - (K + 1) = B - 1 - K by omega, List.range'_succ, List.map_cons,
      show B - 1 - K + 1 = B - K by omega]

theorem decodeList_tabCode (g : ℕ → ℕ) (B p : ℕ) :
    decodeList (tabCode g (Nat.pair B p) B) = (List.range B).map (fun j => g (Nat.pair j p)) := by
  have h := decodeList_tabCode_aux g B p B (le_refl B)
  rw [Nat.sub_self, ← List.range_eq_range'] at h
  exact h

/-! ### Choice-free `List.getD` facts.

Mathlib's `List.getD_eq_getElem`/`List.getD_eq_default`/`getD_append`(`_right`) are proved by `grind`,
which pulls `Classical.choice`. We re-prove the slice we need by structural induction (using only the
choice-free `getD_nil`/`getD_cons_zero`/`getD_cons_succ`), so the `D^∞` presentation stays
`⊆ {propext, Quot.sound}`. -/

/-- Choice-free `getD`-as-`getElem` in range. -/
theorem getD_eq_getElem_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ} (h : n < l.length), l.getD n d = l[n] := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.getD_cons_zero, List.getElem_cons_zero]
    | succ m => rw [List.getD_cons_succ, List.getElem_cons_succ]; exact ih _

/-- Choice-free default-out-of-range. -/
theorem getD_eq_default_cf {β : Type*} (l : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → l.getD n d = d := by
  induction l with
  | nil => intro n _; exact List.getD_nil
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m => rw [List.getD_cons_succ]; exact ih (by rw [List.length_cons] at h; omega)

/-- Choice-free `getD` of a left append. -/
theorem getD_append_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, n < l.length → (l ++ l').getD n d = l.getD n d := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.cons_append, List.getD_cons_zero, List.getD_cons_zero]
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by rw [List.length_cons] at h; omega)

/-- Choice-free `getD` of a right append. -/
theorem getD_append_right_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → (l ++ l').getD n d = l'.getD (n - l.length) d := by
  induction l with
  | nil => intro n _; rw [List.nil_append, List.length_nil, Nat.sub_zero]
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ]
      exact ih (by rw [List.length_cons] at h; omega)

/-- Choice-free `getD` of a mapped `range`. -/
theorem getD_map_range_cf {β : Type*} (h : ℕ → β) (d : β) {B i : ℕ} (hi : i < B) :
    ((List.range B).map h).getD i d = h i := by
  have hlen : ((List.range B).map h).length = B := by rw [List.length_map, List.length_range]
  rw [getD_eq_getElem_cf _ d (by rw [hlen]; exact hi), List.getElem_map, List.getElem_range]

theorem tabCode_nth_lt {g : ℕ → ℕ} {B p i : ℕ} (hi : i < B) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = g (Nat.pair i p) := by
  rw [nthCode_eq, decodeList_tabCode, getD_map_range_cf]; exact hi

theorem tabCode_nth_ge {g : ℕ → ℕ} {B p i : ℕ} (hi : B ≤ i) (d : ℕ) :
    nthCode (tabCode g (Nat.pair B p) B) i d = d := by
  rw [nthCode_eq, decodeList_tabCode, getD_eq_default_cf]
  rw [List.length_map, List.length_range]; exact hi

theorem primrec_tabStep {g : ℕ → ℕ} (hg : Nat.Primrec g) : Nat.Primrec (tabStep g) := by
  have hB : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hp : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hidx : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1 - 1 - w.unpair.2.unpair.1) :=
    primrec_sub₂ (primrec_sub₂ hB (Nat.Primrec.const 1)) hk
  exact (Nat.Primrec.succ.comp ((hg.comp (hidx.pair hp)).pair hih)).of_eq fun _ => rfl

/-- `tabCode g · ·` is primitive recursive in `(a, B)` (coded `pair a B`), whenever `g` is. -/
theorem primrec_tabCode {g : ℕ → ℕ} (hg : Nat.Primrec g) :
    Nat.Primrec (fun t => tabCode g t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const 0) (primrec_tabStep hg)).of_eq fun t => by
    simp only [Nat.unpaired]; rfl

/-- `Nat.max n 1` is primitive recursive. -/
theorem primrec_max_one : Nat.Primrec (fun n => Nat.max n 1) := by
  refine (primrec_selectFn (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) primrec_id))
    (Nat.Primrec.const 1) primrec_id).of_eq fun n => by
    unfold selectFn isOne Nat.max
    rcases n with _ | n <;> simp

/-- Tag-dispatch on `e.unpair.1 ∈ {0,1,2,3}` (else `fdef e`). -/
theorem primrec_tagCase4 {f0 f1 f2 f3 fdef : ℕ → ℕ}
    (hf0 : Nat.Primrec f0) (hf1 : Nat.Primrec f1) (hf2 : Nat.Primrec f2) (hf3 : Nat.Primrec f3)
    (hfdef : Nat.Primrec fdef) :
    Nat.Primrec (fun e =>
      let t := e.unpair.1
      selectFn (isOne (1 - t)) (f0 e)
        (selectFn (isOne (2 - t)) (f1 e)
          (selectFn (isOne (3 - t)) (f2 e)
            (selectFn (isOne (4 - t)) (f3 e) (fdef e))))) := by
  have ht : Nat.Primrec (fun e => e.unpair.1) := Nat.Primrec.left
  have h01 : Nat.Primrec (fun e => isOne (1 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) ht)
  have h12 : Nat.Primrec (fun e => isOne (2 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) ht)
  have h23 : Nat.Primrec (fun e => isOne (3 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 3) ht)
  have h34 : Nat.Primrec (fun e => isOne (4 - e.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 4) ht)
  refine (primrec_selectFn h01 hf0
    (primrec_selectFn h12 hf1
      (primrec_selectFn h23 hf2
        (primrec_selectFn h34 hf3 hfdef)))).of_eq fun e => rfl

/-! ## Exercise 7.22 C9b1 — fuel-bounded `SExpr` decode ok flag

Mirrors tag dispatch on `c.unpair.1 ∈ {0,1,2,3}`; at `fuel + 1` recurses at `fuel` on sub-codes
for `.cat`/`.cap`. Shallow correctness link ↔ `decodeFuel` (**7.22i(b)1(c–e)**) not yet in tree. -/

/-- `{0,1}` AND on flags (both must be `1`). -/
def mulBit (a b : ℕ) : ℕ := a * b

theorem mulBit_eq_one_iff (a b : ℕ) : mulBit a b = 1 ↔ a = 1 ∧ b = 1 := by
  simpa [mulBit] using nat_mul_eq_one

theorem primrec_mulBit : Nat.Primrec (fun t => mulBit t.unpair.1 t.unpair.2) :=
  primrec_mul₂ Nat.Primrec.left Nat.Primrec.right

/-- One step of fuel-bounded decode-ok (previous fuel level supplied as `prev`). -/
def decodeFuelOkCharBody (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  let sub := mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)
  selectFn (isOne (1 - c.unpair.1))
    (selectFn (isOne (1 - c.unpair.2)) 1 0)
    (selectFn (isOne (2 - c.unpair.1)) (allBinDigitsChar c.unpair.2)
      (selectFn (isOne (3 - c.unpair.1)) sub
        (selectFn (isOne (4 - c.unpair.1)) sub 0)))

/-- `{0,1}` flag: `1` iff fuel-bounded `SExpr` decode succeeds on code `c`. -/
def decodeFuelOkChar : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => decodeFuelOkCharBody (decodeFuelOkChar fuel) c

private theorem primrec_decodeFuelOkCharBody {prev : ℕ → ℕ} (hprev : Nat.Primrec prev) :
    Nat.Primrec (fun c => decodeFuelOkCharBody prev c) := by
  unfold decodeFuelOkCharBody
  have hleft : Nat.Primrec (fun c => prev c.unpair.2.unpair.1) :=
    (hprev.comp (Nat.Primrec.left.comp Nat.Primrec.right)).of_eq fun c => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hright : Nat.Primrec (fun c => prev c.unpair.2.unpair.2) :=
    (hprev.comp (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq fun c => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hsub : Nat.Primrec (fun c => mulBit (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2)) :=
    primrec_mul₂ hleft hright
  have hf0 : Nat.Primrec (fun c => selectFn (isOne (1 - c.unpair.2)) 1 0) :=
    primrec_selectFn
      (primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) Nat.Primrec.right))
      (Nat.Primrec.const 1) (Nat.Primrec.const 0)
  have hf1 : Nat.Primrec (fun c => allBinDigitsChar c.unpair.2) :=
    primrec_allBinDigitsChar.comp Nat.Primrec.right
  exact primrec_tagCase4 hf0 hf1 hsub hsub (Nat.Primrec.const 0)

theorem primrec_decodeFuelOkChar : ∀ fuel, Nat.Primrec (fun c => decodeFuelOkChar fuel c)
  | 0 => Nat.Primrec.const 0
  | fuel + 1 => by
    simpa [decodeFuelOkChar] using
      primrec_decodeFuelOkCharBody (primrec_decodeFuelOkChar fuel)

end Domain.Recursive
