import Scott1980.Neighborhood.Basic
import Mathlib.Data.Set.Insert

/-!
# Exercise 7.22 (Scott 1981, PRG-19, §7) — a domain over `{0,1}*` by least fixed point

> **EXERCISE 7.22.** (For algebraists.) Let `Σ = {0,1}*` be the free semigroup. A new domain is
> constructed by defining a family of sets by the least fixed point theorem as follows:
>
> `S = {Σ} ∪ {{σ} ∣ σ ∈ Σ} ∪ {XY ∣ X, Y ∈ S} ∪ {X ∩ Y ∣ X, Y ∈ S and X ∩ Y ≠ ∅}.`
>
> Here `XY = {στ ∣ σ ∈ X and τ ∈ Y}`.
>
> Prove that `S` is an effectively given, positive neighbourhood system. (Hint: the sets in `S` are
> each "regular events" in the terminology of automata theory, and we have a decision method for the
> set algebra of regular events.)
>
> Define multiplication on `|S|` by `xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`, and show `|S|` becomes
> a semigroup with `Σ` embedded into `|S|` by the homomorphism `σ ↦ {X ∈ S ∣ σ ∈ X}`.
>
> Investigate some *infinite words* in `S`, say those defined by least fixed points such as
> `σ⃗ = σ σ⃗` and `σ⃗ = σ⃗ σ`. Are the equations `σ⃗ σ⃗ = σ⃗`, `σ⃗ σ⃗ σ⃗ = σ⃗`,
> `σ⃗ 1⃗ σ⃗ 1⃗ = σ⃗ 1⃗`, and `01⃗ 01⃗ 01⃗ 01⃗ = 01⃗ 01⃗` true?

This file formalises the **algebraic core** of the exercise, fully and choice-free:

* the least-fixed-point family `S` as an inductive predicate `InS` over tokens `Σ = {0,1}* = List Bool`;
* `S` is a **positive neighbourhood system** `Ssys` (Definition 1.1 / Exercise 1.19), built choice-free
  via `NeighborhoodSystem.ofPositive`;
* the **multiplication** `xy` on the domain `|S|` and the proof that it is **associative**, so `|S|`
  is a semigroup (`mulElem`, `mulElem_assoc`);
* the **embedding** `σ ↦ {X ∈ S ∣ σ ∈ X}` of the free monoid into `|S|`, proved a semigroup
  **homomorphism** (`emb_mul`) and **injective** (`emb_injective`).

## On "effectively given" and the infinite-word equations (discussion)

Two parts of Scott's exercise are *not* mechanised here, and are discussed in prose rather than left
as `sorry` (the file is `sorry`-free):

* **Effective givenness.** Every member of `S` is a *regular event* (Scott's hint): `Σ = {0,1}*` and
  every singleton `{σ}` is regular, and regular languages are closed under concatenation `XY` and
  intersection `X ∩ Y`. An enumeration `X : ℕ → Set Σ` of `S` is obtained by Gödel-numbering the
  finite *syntax* of `S`-terms (the four generators `Σ`, `{σ}`, `·` for `XY`, `∩`). Scott's two
  decidability relations (Definition 7.1) — `Xₙ ∩ Xₘ = X_k` and the consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ`
  (which by **positivity** is just non-emptiness of `Xₙ ∩ Xₘ`) — are decidable because the *set
  algebra of regular events* is decidable (emptiness and equivalence of regular languages are
  decidable, e.g. via minimal DFAs / Myhill–Nerode, cf. `Example62Regular.lean`). Mechanising that
  decision procedure inside this project's bespoke **choice-free** recursion theory
  (`Recursive.lean`) would require building the automata-theoretic decision algorithms primitively;
  that is a separate, large undertaking and is left as the documented gap. The neighbourhood-system
  content (positivity) and the algebra (semigroup + embedding) are complete.

* **Infinite words.** Scott's last questions ask about *infinite words* in `S` and whether certain
  **multiplicative equations** hold in `|S|`. We formalise **`w⃗`** as the filter
  `Z ↦ InS Z ∧ ∀ n, wⁿ ∈ Z` (`streamElem`), and check Scott's equations as Lean theorems when the
  witness language `{wⁿ}` lies in `S` (`InS (powerLang w)`): `streamElem_idempotent` gives
  `w⃗ · w⃗ = w⃗`, and associativity gives the triple-product form; the `σ ++ [true]` case is the
  same with `w = σ ++ [true]`. Scott's last question (`01⃗⁴ = 01⃗²`?) is conditional on
  `InS (powerLang [false, true])` — if that language is not in `S`, the power-filter model and Scott's
  LFP reading may diverge (see **7.22l**).

Everything below depends only on `propext` / `Quot.sound` (no `Classical.choice`).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

/-! ## Concatenation of languages over `Σ = {0,1}*`

We work with tokens `Σ = List Bool` (the words over `{0,1}`); a neighbourhood is a `Set (List Bool)`
(a "language"). We use a bespoke `concat` (rather than mathlib's `Language.*`) so that intersection,
`Set.univ`, and singletons remain the native `Set` operations the neighbourhood-system API expects. -/

/-- Scott's `XY = {στ ∣ σ ∈ X and τ ∈ Y}`: the concatenation of two languages. -/
def concat (X Y : Set (List Bool)) : Set (List Bool) := {w | ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w}

@[simp] theorem mem_concat {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w := Iff.rfl

/-- `a ∈ X`, `b ∈ Y ⟹ a ++ b ∈ XY`. -/
theorem append_mem_concat {X Y : Set (List Bool)} {a b : List Bool} (ha : a ∈ X) (hb : b ∈ Y) :
    a ++ b ∈ concat X Y := ⟨a, ha, b, hb, rfl⟩

/-- Concatenation is monotone in both arguments. -/
theorem concat_mono {X X' Y Y' : Set (List Bool)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    concat X Y ⊆ concat X' Y' := by
  rintro w ⟨a, ha, b, hb, rfl⟩; exact ⟨a, hX ha, b, hY hb, rfl⟩

/-- Concatenation is associative (inherited from `List.append_assoc`). -/
theorem concat_assoc (X Y Z : Set (List Bool)) :
    concat (concat X Y) Z = concat X (concat Y Z) := by
  ext w
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b ++ c, ⟨b, hb, c, hc, rfl⟩, by rw [List.append_assoc]⟩
  · rintro ⟨a, ha, bc, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a ++ b, ⟨a, ha, b, hb, rfl⟩, c, hc, by rw [List.append_assoc]⟩

/-- The concatenation of two non-empty languages is non-empty. -/
theorem concat_nonempty {X Y : Set (List Bool)} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (concat X Y).Nonempty := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨a ++ b, a, ha, b, hb, rfl⟩

/-- `{a}{b} = {a ++ b}`: concatenation of singletons is the singleton of the concatenation. -/
theorem concat_singleton (a b : List Bool) : concat {a} {b} = {a ++ b} := by
  ext w
  simp only [mem_concat, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a', rfl, b', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, b, rfl, rfl⟩

/-! ## The least-fixed-point family `S` -/

/-- **Scott's family `S`**, as the least fixed point (an inductive predicate). A language `X` is *in
`S`* iff it is built from the four generators:

* `Σ = {0,1}*` itself (`Set.univ`);
* a singleton `{σ}`;
* a concatenation `XY` of two members;
* a *non-empty* intersection `X ∩ Y` of two members. -/
inductive InS : Set (List Bool) → Prop
  | univ : InS Set.univ
  | singleton (σ : List Bool) : InS {σ}
  | mul {X Y : Set (List Bool)} : InS X → InS Y → InS (concat X Y)
  | inter {X Y : Set (List Bool)} : InS X → InS Y → (X ∩ Y).Nonempty → InS (X ∩ Y)

/-- **Every member of `S` is non-empty.** (`Σ` and singletons are non-empty; concatenation preserves
non-emptiness; intersections are only admitted to `S` when non-empty.) This is what makes `S`
*positive*. -/
theorem InS.nonempty {X : Set (List Bool)} (h : InS X) : X.Nonempty := by
  induction h with
  | univ => exact ⟨[], trivial⟩
  | singleton σ => exact ⟨σ, rfl⟩
  | mul _ _ ihX ihY => exact concat_nonempty ihX ihY
  | inter _ _ hne _ _ => exact hne

/-! ## `S` is a positive neighbourhood system -/

/-- **Exercise 7.22 (neighbourhood-system part).** `S` is a *positive* neighbourhood system over the
token type `Σ = {0,1}*`, with master neighbourhood `Δ = Σ = Set.univ`. Built choice-free via
`NeighborhoodSystem.ofPositive`: positivity `(X ∩ Y) ∈ S ↔ (X ∩ Y).Nonempty` holds because every
member of `S` is non-empty (`InS.nonempty`, the `→` direction) and `InS.inter` is exactly the `←`. -/
def Ssys : NeighborhoodSystem (List Bool) :=
  NeighborhoodSystem.ofPositive InS Set.univ InS.univ (fun {X} _ => Set.subset_univ X)
    (fun _ _ hX hY => ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩)

@[simp] theorem Ssys_mem {X : Set (List Bool)} : Ssys.mem X ↔ InS X := Iff.rfl

theorem Ssys_master : Ssys.master = Set.univ := rfl

/-- `S` is indeed positive (Exercise 1.19's `IsPositive`). -/
theorem Ssys_isPositive : Ssys.IsPositive := by
  intro X Y hX hY
  exact ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩

/-! ## Multiplication on the domain `|S|`

`xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`. We show this is again a filter (an element of `|S|`). -/

/-- **Scott's multiplication on `|S|`.** `xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`. The filter
conditions:

* `master_mem`: take `X = Y = Σ` (both in any filter), `Σ·Σ ⊆ Σ`;
* `inter_mem`: from witnesses `X₁Y₁ ⊆ Z₁`, `X₂Y₂ ⊆ Z₂`, the pair `X₁ ∩ X₂ ∈ x`, `Y₁ ∩ Y₂ ∈ y` (filter
  closure) gives `(X₁ ∩ X₂)(Y₁ ∩ Y₂) ⊆ Z₁ ∩ Z₂` by monotonicity of `concat`, and `Z₁ ∩ Z₂ ∈ S`
  because this non-empty witness sits inside it (positivity);
* `up_mem`: transitivity of `⊆`. -/
def mulElem (x y : Ssys.Element) : Ssys.Element where
  mem Z := InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z
  sub h := h.1
  master_mem :=
    ⟨InS.univ, Set.univ, x.master_mem, Set.univ, y.master_mem, Set.subset_univ _⟩
  inter_mem := by
    rintro Z1 Z2 ⟨hZ1, X1, hX1, Y1, hY1, hsub1⟩ ⟨hZ2, X2, hX2, Y2, hY2, hsub2⟩
    have hXi : x.mem (X1 ∩ X2) := x.inter_mem hX1 hX2
    have hYi : y.mem (Y1 ∩ Y2) := y.inter_mem hY1 hY2
    have hcsub : concat (X1 ∩ X2) (Y1 ∩ Y2) ⊆ Z1 ∩ Z2 := by
      intro w hw
      exact ⟨hsub1 (concat_mono Set.inter_subset_left Set.inter_subset_left hw),
             hsub2 (concat_mono Set.inter_subset_right Set.inter_subset_right hw)⟩
    have hne : (Z1 ∩ Z2).Nonempty :=
      (concat_nonempty (x.sub hXi).nonempty (y.sub hYi).nonempty).mono hcsub
    exact ⟨InS.inter hZ1 hZ2 hne, X1 ∩ X2, hXi, Y1 ∩ Y2, hYi, hcsub⟩
  up_mem := by
    rintro Z W ⟨_, X, hX, Y, hY, hsub⟩ hW hZW
    exact ⟨hW, X, hX, Y, hY, hsub.trans hZW⟩

@[simp] theorem mem_mulElem {x y : Ssys.Element} {Z : Set (List Bool)} :
    (mulElem x y).mem Z ↔ InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z := Iff.rfl

/-- **Exercise 7.22 (semigroup part): multiplication on `|S|` is associative**, so `|S|` is a
semigroup. The forward inclusion rewrites `X(YZ) = (XY)Z` (`concat_assoc`) and uses monotonicity of
`concat` to push the witnesses through; the converse is symmetric. -/
theorem mulElem_assoc (x y z : Ssys.Element) :
    mulElem (mulElem x y) z = mulElem x (mulElem y z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨hW, P, ⟨_, X, hX, Y, hY, hXY⟩, Z, hZ, hPZ⟩
    refine ⟨hW, X, hX, concat Y Z, ⟨InS.mul (y.sub hY) (z.sub hZ), Y, hY, Z, hZ,
      Set.Subset.refl _⟩, ?_⟩
    rw [← concat_assoc]
    exact (concat_mono hXY (Set.Subset.refl _)).trans hPZ
  · rintro ⟨hW, X, hX, Q, ⟨_, Y, hY, Z, hZ, hYZ⟩, hXQ⟩
    refine ⟨hW, concat X Y, ⟨InS.mul (x.sub hX) (y.sub hY), X, hX, Y, hY,
      Set.Subset.refl _⟩, Z, hZ, ?_⟩
    rw [concat_assoc]
    exact (concat_mono (Set.Subset.refl _) hYZ).trans hXQ

/-! ## The embedding of `Σ = {0,1}*` into `|S|` -/

/-- **Scott's embedding** `σ ↦ {X ∈ S ∣ σ ∈ X}`. This is a filter (an element of `|S|`): it contains
`Σ`, is closed under intersection (the intersection is non-empty since it still contains `σ`, so it
lies in `S` by positivity), and is upward closed. -/
def emb (σ : List Bool) : Ssys.Element where
  mem X := InS X ∧ σ ∈ X
  sub h := h.1
  master_mem := ⟨InS.univ, Set.mem_univ σ⟩
  inter_mem := by
    rintro X Y ⟨hX, hσX⟩ ⟨hY, hσY⟩
    exact ⟨InS.inter hX hY ⟨σ, hσX, hσY⟩, hσX, hσY⟩
  up_mem := by
    rintro X Y ⟨_, hσ⟩ hY hsub
    exact ⟨hY, hsub hσ⟩

@[simp] theorem mem_emb {σ : List Bool} {X : Set (List Bool)} :
    (emb σ).mem X ↔ InS X ∧ σ ∈ X := Iff.rfl

/-- **Exercise 7.22 (homomorphism part): `emb` is a semigroup homomorphism**,
`emb (σ ++ τ) = emb σ · emb τ`. Forward: from `σ ++ τ ∈ Z`, the witnesses `X = {σ}`, `Y = {τ}` give
`{σ}{τ} = {σ ++ τ} ⊆ Z`. Converse: if `{σ}` ∈ `emb σ`, `{τ}` ∈ `emb τ` with `XY ⊆ Z` then
`σ ++ τ ∈ XY ⊆ Z`. -/
theorem emb_mul (σ τ : List Bool) : emb (σ ++ τ) = mulElem (emb σ) (emb τ) := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hστ⟩
    refine ⟨hZ, {σ}, ⟨InS.singleton σ, rfl⟩, {τ}, ⟨InS.singleton τ, rfl⟩, ?_⟩
    rw [concat_singleton]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw; exact hστ
  · rintro ⟨hZ, X, ⟨_, hσX⟩, Y, ⟨_, hτY⟩, hsub⟩
    exact ⟨hZ, hsub (append_mem_concat hσX hτY)⟩

/-- The embedding is **injective**: distinct words give distinct elements of `|S|`. (If
`emb σ = emb τ` then `emb τ` contains `{σ}`, forcing `τ = σ`.) So `Σ` genuinely *embeds* into `|S|`. -/
theorem emb_injective : Function.Injective emb := by
  intro σ τ h
  have hmem : (emb τ).mem {σ} := h ▸ (⟨InS.singleton σ, rfl⟩ : (emb σ).mem {σ})
  exact (Set.mem_singleton_iff.mp hmem.2).symm

/-! ## Stream elements (Scott's infinite-word investigations)

Write `wⁿ` for `w` appended to itself `n` times. **`streamElem w`** is the filter
`Z ↦ InS Z ∧ ∀ n, wⁿ ∈ Z` (Scott's `w⃗`). -/

/-- `wⁿ`: `w` concatenated with itself `n` times (`w⁰ = []`). -/
def repeatWord (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => w ++ repeatWord w n

@[simp] theorem repeatWord_zero (w : List Bool) : repeatWord w 0 = [] := rfl

theorem repeatWord_succ (w : List Bool) (n : ℕ) :
    repeatWord w (n + 1) = w ++ repeatWord w n := rfl

theorem repeatWord_add (w : List Bool) (a b : ℕ) :
    repeatWord w (a + b) = repeatWord w a ++ repeatWord w b := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih =>
      simp only [Nat.succ_add, repeatWord]
      rw [ih, List.append_assoc]

/-- `{wⁿ ∣ n}` — the language of all finite powers of `w`. -/
def powerLang (w : List Bool) : Set (List Bool) :=
  {u | ∃ n, repeatWord w n = u}

@[simp] theorem mem_powerLang {w u : List Bool} :
    u ∈ powerLang w ↔ ∃ n, repeatWord w n = u := Iff.rfl

theorem powerLang_concat (w : List Bool) :
    concat (powerLang w) (powerLang w) ⊆ powerLang w := by
  rintro u ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩
  exact ⟨m + n, by rw [repeatWord_add, hm, hn]⟩

theorem repeatWord_eq_empty (w : List Bool) (n : ℕ) (hw : w = []) :
    repeatWord w n = [] := by
  subst hw
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, ih]

theorem InS_powerLang_empty : InS (powerLang []) := by
  have h : powerLang [] = {[]} := by
    ext u
    simp only [mem_powerLang, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩; exact hn.symm.trans (repeatWord_eq_empty [] n rfl)
    · intro hu; subst hu; exact ⟨0, rfl⟩
  simpa [h] using InS.singleton []

/-- Membership in Scott's **`w⃗`**: every power `wⁿ` lies in `Z`. Concatenation-closure of `Z`
  is not required for membership, but holds for neighbourhoods in `mulElem (streamElem w) (streamElem w)`. -/
def streamElemMem (w : List Bool) (Z : Set (List Bool)) : Prop :=
  InS Z ∧ ∀ n, repeatWord w n ∈ Z

/-- Scott's **`w⃗`** as a domain element. -/
def streamElem (w : List Bool) : Ssys.Element where
  mem Z := streamElemMem w Z
  sub h := h.1
  master_mem := ⟨InS.univ, fun n => Set.mem_univ (repeatWord w n)⟩
  inter_mem := by
    intro X Y hX hY
    obtain ⟨hXIn, hXw⟩ := hX
    obtain ⟨hYIn, hYw⟩ := hY
    exact ⟨InS.inter hXIn hYIn ⟨repeatWord w 0, hXw 0, hYw 0⟩, fun n => ⟨hXw n, hYw n⟩⟩
  up_mem := by
    intro X Y hX hInSY hsub
    obtain ⟨_hXIn, hXw⟩ := hX
    exact ⟨hInSY, fun n => hsub (hXw n)⟩

@[simp] theorem mem_streamElem {w : List Bool} {Z : Set (List Bool)} :
    (streamElem w).mem Z ↔ streamElemMem w Z := Iff.rfl

/-- From **`w⃗ · w⃗`**, every power `wⁿ` still lies in `Z`. -/
theorem streamElem_powers_of_mul (w : List Bool) (Z : Set (List Bool))
    (h : (mulElem (streamElem w) (streamElem w)).mem Z) :
    streamElemMem w Z := by
  obtain ⟨hZ, X, hX, Y, hY, hsub⟩ := h
  obtain ⟨_hXIn, hXw⟩ := hX
  obtain ⟨_hYIn, hYw⟩ := hY
  refine ⟨hZ, fun n => ?_⟩
  have h1 := hsub (append_mem_concat (hXw n) (hYw 0))
  simpa [repeatWord_zero, List.append_nil] using h1

/-- **`w⃗ · w⃗` is in `Z` whenever `w⃗` is**, using the witness `powerLang w ∈ S`. -/
theorem streamElem_mul_self_mem (w : List Bool) (Z : Set (List Bool))
    (h : streamElemMem w Z) (hPL : InS (powerLang w)) :
    (mulElem (streamElem w) (streamElem w)).mem Z := by
  refine ⟨h.1, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, ?_⟩
  intro u hu
  obtain ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩ := hu
  simpa [hm, hn, repeatWord_add] using h.2 (m + n)

/-- Scott's stream equation **`w⃗ · w⃗ = w⃗`** (filter equality), when `{wⁿ}` lies in `S`. -/
theorem streamElem_idempotent (w : List Bool) (hPL : InS (powerLang w)) :
    mulElem (streamElem w) (streamElem w) = streamElem w := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  exact ⟨streamElem_powers_of_mul w Z, fun h => streamElem_mul_self_mem w Z h hPL⟩

/-- Scott's stream equations (Exercise 7.22, investigatory part). -/

example : mulElem (streamElem []) (streamElem []) = streamElem [] :=
  streamElem_idempotent [] InS_powerLang_empty

example (σ : List Bool) (Z : Set (List Bool)) :
    (mulElem (streamElem σ) (streamElem σ)).mem Z → streamElemMem σ Z :=
  streamElem_powers_of_mul σ Z

example (σ : List Bool) (h : InS (powerLang σ)) :
    mulElem (mulElem (streamElem σ) (streamElem σ)) (streamElem σ) = streamElem σ := by
  rw [mulElem_assoc, streamElem_idempotent σ h, streamElem_idempotent σ h]

example (σ : List Bool) (h : InS (powerLang (σ ++ [true]))) :
    mulElem (streamElem (σ ++ [true])) (streamElem (σ ++ [true])) =
      streamElem (σ ++ [true]) :=
  streamElem_idempotent (σ ++ [true]) h

example (h : InS (powerLang [false, true])) :
    mulElem
        (mulElem (streamElem [false, true]) (streamElem [false, true]))
        (mulElem (streamElem [false, true]) (streamElem [false, true])) =
      mulElem (streamElem [false, true]) (streamElem [false, true]) := by
  rw [streamElem_idempotent _ h, streamElem_idempotent _ h]

end Exercise722

end Scott1980.Neighborhood
