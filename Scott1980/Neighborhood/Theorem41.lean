import Scott1980.Neighborhood.FunctionSpace
import Scott1980.Neighborhood.ApproximableExercises

/-!
# Lecture IV (§4) — fixed points and recursion: Theorems 4.1 and 4.2

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture IV,
*Fixed points and recursion*. The heart of the matter is the **Fixed-point Theorem**:

* **Theorem 4.1** — every approximable mapping `f : 𝒟 → 𝒟` has a *least* element `x ∈ |𝒟|` with
  `f(x) = x`. Scott constructs `x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`, the family of neighbourhoods
  reachable from the master `Δ` along finitely many `f`-steps. We model the `n`-fold composition
  `fⁿ` by `iterMap f n` (`f⁰ = I_𝒟`, `f^{n+1} = f ∘ fⁿ`) and the fixed point by `fixElement f`.
  The fixed-point equation is `toElementMap_fixElement`; minimality among *pre-fixed* points
  (`f(z) ⊆ z ⟹ x ⊆ z`) is `fixElement_le_of_toElementMap_le`.

* **Theorem 4.2** — the operator `fix : (𝒟 → 𝒟) → 𝒟` is itself approximable. We build it as
  `fixMap V : ApproximableMap (funSpace V V) V` via the extension-from-finite-elements principle
  (Exercise 2.8, `ofMono`), sending the finite element `↑F` to `fix(↑F)` where `↑F = leastMap` is
  the least map of the neighbourhood `F` (here `toApproxMap (↑F)`). The defining computation
  `fixMap.toElementMap φ = fix(toApproxMap φ)` is Scott's equation (∗)
  `fix(f) = ⋃ {fix(↑F) ∣ f ∈ [F]}` (`fixMap_toElementMap`), whose non-trivial half — every
  finite `f`-chain factors through one finite approximant `F ∈ φ` — is `exists_principal_iterMap`.
  Then (i) `fix(f) = f(fix(f))` (`fixMap_fixed`); (ii) `f(x) ⊆ x ⟹ fix(f) ⊆ x` (`fixMap_least`);
  (iii) `fix(f) = ⊔ₙ fⁿ(⊥)` (`fixMap_eq_iSup`, with `iterElem_eq_iterate` giving the faithful
  `⊔ₙ fⁿ(⊥)` form); and uniqueness (`fixMap_unique`).

All *data* constructions (`iterMap`, `fixElement`, `iterElem`, `fixMap`) are **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the uniqueness lemma `fixMap_unique` pulls
`Classical.choice` only through the project's `ext_of_toElementMap`, as permitted.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The iterated map `fⁿ`. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The `n`-fold composition `fⁿ` of an endomap with itself:
`f⁰ = I_𝒟` and `f^{n+1} = f ∘ fⁿ`. -/
def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

@[simp] theorem iterMap_zero (f : ApproximableMap V V) : f.iterMap 0 = idMap V := rfl

@[simp] theorem iterMap_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterMap (n + 1) = f.comp (f.iterMap n) := rfl

/-- Composition is monotone in both arguments. -/
theorem comp_mono {f g a b : ApproximableMap V V} (hfg : f ≤ g) (hab : a ≤ b) :
    f.comp a ≤ g.comp b := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hab X Y hXY, hfg Y Z hYZ⟩

/-- The iterate is monotone in the map: `f ⊑ g ⟹ fⁿ ⊑ gⁿ` (Scott's "`fⁿ ⊆ gⁿ`"). -/
theorem iterMap_mono_map {f g : ApproximableMap V V} (hfg : f ≤ g) (n : ℕ) :
    f.iterMap n ≤ g.iterMap n := by
  induction n with
  | zero => show (idMap V) ≤ (idMap V); exact le_refl _
  | succ k ih => exact comp_mono hfg ih

/-- `f` commutes with its own iterate: `f ∘ fⁿ = fⁿ ∘ f`. Proved by induction using associativity
and the identity laws. -/
theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

/-- Scott's "a sequence for an `X ∈ x` can always be extended": if `Δ fⁿ X`, then `Δ f^{n+1} X`
(prepend a `Δ`-step, using `Δ f Δ`). -/
theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

/-- Monotonicity of the reachability relation in the number of steps: `n ≤ m` and `Δ fⁿ X` imply
`Δ fᵐ X`. -/
theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

/-! ### Theorem 4.1 — the least fixed point. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The least fixed point of `f`, Scott's
`x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`. The three filter conditions are exactly Scott's: `Δ ∈ x` (the
`n = 0` witness `I_𝒟`); closure under intersection follows from intersectivity (`inter_right`) of
the single iterate `f^{max n m}` reached by extending the shorter chain; upward closure is `mono`. -/
def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

@[simp] theorem mem_fixElement (f : ApproximableMap V V) {X : Set α} :
    f.fixElement.mem X ↔ ∃ n, (f.iterMap n).rel V.master X := Iff.rfl

/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is a *fixed point*: `f(x) = x`.
`f(x) ⊆ x` appends an `f`-step (`Δ f^{n+1} X` from `Δ fⁿ X' f X`); `x ⊆ f(x)` reads off the last
step of the chain (the empty chain forces `X = Δ`, handled by `master_mem`/`master_rel`). -/
theorem toElementMap_fixElement (f : ApproximableMap V V) :
    f.toElementMap f.fixElement = f.fixElement := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨n, hn⟩, hXY⟩
    exact ⟨n + 1, ⟨X, hn, hXY⟩⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      obtain ⟨_, hYmem, hmY⟩ := hn
      have hYmaster : Y = V.master := Set.Subset.antisymm (V.sub_master hYmem) hmY
      subst hYmaster
      exact ⟨V.master, f.fixElement.master_mem, f.master_rel⟩
    | succ k =>
      obtain ⟨Z, hZ, hZY⟩ := hn
      exact ⟨Z, ⟨k, hZ⟩, hZY⟩

/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is the *least pre-fixed point*: if
`f(z) ⊆ z`, then `x ⊆ z`. (Scott's induction: `Δ ∈ z`, and `X ∈ z`, `X f Y` give `Y ∈ f(z) ⊆ z`,
so `Δ fⁿ X` implies `X ∈ z`.) In particular `x` is the least element with `f(x) = x`. -/
theorem fixElement_le_of_toElementMap_le (f : ApproximableMap V V) {z : V.Element}
    (hz : f.toElementMap z ≤ z) : f.fixElement ≤ z := by
  have key : ∀ n X, (f.iterMap n).rel V.master X → z.mem X := by
    intro n
    induction n with
    | zero =>
      intro X hn
      obtain ⟨_, hXmem, hmX⟩ := hn
      have hXmaster : X = V.master := Set.Subset.antisymm (V.sub_master hXmem) hmX
      subst hXmaster
      exact z.master_mem
    | succ k ih =>
      intro X hn
      obtain ⟨W, hW, hWX⟩ := hn
      exact hz X ⟨W, ih W hW, hWX⟩
  rintro X ⟨n, hn⟩
  exact key n X hn

/-- The least fixed point is monotone in the map: `f ⊑ g ⟹ fix(f) ⊑ fix(g)` (immediate from
`iterMap_mono_map`; underlies the approximability of `fix` in 4.2). -/
theorem fixElement_mono {f g : ApproximableMap V V} (hfg : f ≤ g) :
    f.fixElement ≤ g.fixElement := by
  rintro X ⟨n, hn⟩
  exact ⟨n, iterMap_mono_map hfg n V.master X hn⟩

/-! ### Theorem 4.2(iii) — the iterates `fⁿ(⊥)`. -/

/-- The `n`-th approximant `fⁿ(⊥)` of the least fixed point. -/
def iterElem (f : ApproximableMap V V) (n : ℕ) : V.Element := (f.iterMap n).toElementMap V.bot

/-- `Y ∈ fⁿ(⊥) ↔ Δ fⁿ Y`: the `n`-th approximant is the family of neighbourhoods reachable from
`Δ` in exactly the `n` steps recorded by `fⁿ`. -/
theorem mem_iterElem (f : ApproximableMap V V) (n : ℕ) {X : Set α} :
    (f.iterElem n).mem X ↔ (f.iterMap n).rel V.master X := by
  constructor
  · rintro ⟨W, hW, hWX⟩
    rw [mem_bot] at hW; subst hW; exact hWX
  · intro h; exact ⟨V.master, by rw [mem_bot], h⟩

/-- The approximants form an increasing chain: `n ≤ m ⟹ fⁿ(⊥) ⊑ fᵐ(⊥)`. -/
theorem iterElem_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) :
    f.iterElem n ≤ f.iterElem m := by
  intro X hX
  rw [mem_iterElem] at hX ⊢
  exact rel_master_mono f hnm hX

/-- `fⁿ(⊥)` agrees with the iterated elementwise function `(f(·))^[n] ⊥` — Scott's `fⁿ(⊥)`. -/
theorem iterElem_eq_iterate (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n = (f.toElementMap)^[n] V.bot := by
  induction n with
  | zero =>
    show (f.iterMap 0).toElementMap V.bot = V.bot
    exact toElementMap_idMap V.bot
  | succ k ih =>
    have hstep : f.iterElem (k + 1) = f.toElementMap (f.iterElem k) := by
      show (f.comp (f.iterMap k)).toElementMap V.bot
          = f.toElementMap ((f.iterMap k).toElementMap V.bot)
      rw [toElementMap_comp]
    rw [hstep, ih, Function.iterate_succ', Function.comp_apply]

/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)`, here as the directed union of
the increasing chain of approximants. -/
theorem fixElement_eq_iSupDirected (f : ApproximableMap V V) :
    f.fixElement =
      NeighborhoodSystem.iSupDirected (f.iterElem)
        (fun i j => ⟨max i j, iterElem_mono f (le_max_left i j),
          iterElem_mono f (le_max_right i j)⟩) := by
  apply Element.ext
  intro X
  rw [NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap

/-! ### Theorem 4.2 — the approximable fixed-point operator `fix`. -/

open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19).** The fixed-point operator `fix : (𝒟 → 𝒟) → 𝒟` as an
approximable mapping. Built by the extension principle (Exercise 2.8, `ofMono`): on the finite
element `↑F` it returns `fix(↑F)`, where `↑F = toApproxMap (principal hF)` is the least map of the
neighbourhood `F` (Proposition 3.9). Monotonicity of `↑F ↦ fix(↑F)` is `fixElement_mono` composed
with the order-iso `funSpaceEquiv`. -/
def fixMap (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V :=
  ofMono (fun W hW => (toApproxMap ((funSpace V V).principal hW)).fixElement)
    (fun W W' hW hW' hW'W => by
      apply fixElement_mono
      exact (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff hW hW').mpr hW'W))

/-- On a finite element `↑F`, `fix` returns `fix(↑F)` (the least fixed point of the least map of
`F`). -/
theorem fixMap_toElementMap_principal (V : NeighborhoodSystem α)
    {W : Set (ApproximableMap V V)} (hW : (funSpace V V).mem W) :
    (fixMap V).toElementMap ((funSpace V V).principal hW) =
      (toApproxMap ((funSpace V V).principal hW)).fixElement :=
  toElementMap_ofMono_principal _ _ W hW

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗), hard half.** A finite `f`-chain
`Δ (toApproxMap φ)ⁿ X` factors through a *single* finite approximant `F ∈ φ`: there is a
neighbourhood `W ∈ φ` whose least map already realizes the same chain `Δ (↑W)ⁿ X`. The witness `W`
is accumulated as the intersection of the (finitely many) step-neighbourhoods used by the chain,
which lies in `φ` because `φ` is a filter. -/
theorem exists_principal_iterMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    ∀ (n : ℕ) (X : Set α), ((toApproxMap φ).iterMap n).rel V.master X →
      ∃ (W : Set (ApproximableMap V V)) (hw : φ.mem W),
        ((toApproxMap ((funSpace V V).principal (φ.sub hw))).iterMap n).rel V.master X := by
  intro n
  induction n with
  | zero =>
    intro X hX
    exact ⟨(funSpace V V).master, φ.master_mem, hX⟩
  | succ k ih =>
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hX
    obtain ⟨W₁, hw₁, hW₁⟩ := ih Y hY
    have hVY : V.mem Y := ((toApproxMap φ).iterMap k).rel_cod hY
    have hVX : V.mem X := (toApproxMap φ).rel_cod hYX
    have hw₂ : φ.mem (step Y X) := toApproxMap_rel.mp hYX
    have hwInter : φ.mem (W₁ ∩ step Y X) := φ.inter_mem hw₁ hw₂
    refine ⟨W₁ ∩ step Y X, hwInter, ?_⟩
    have hg₁g : toApproxMap ((funSpace V V).principal (φ.sub hw₁))
        ≤ toApproxMap ((funSpace V V).principal (φ.sub hwInter)) :=
      (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff (φ.sub hw₁) (φ.sub hwInter)).mpr Set.inter_subset_left)
    have hYg : ((toApproxMap ((funSpace V V).principal (φ.sub hwInter))).iterMap k).rel V.master Y :=
      iterMap_mono_map hg₁g k V.master Y hW₁
    have hgYX : (toApproxMap ((funSpace V V).principal (φ.sub hwInter))).rel Y X := by
      show ((funSpace V V).principal (φ.sub hwInter)).mem (step Y X)
      exact ⟨step_mem hVY hVX, Set.inter_subset_right⟩
    exact ⟨Y, hYg, hgYX⟩

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗).** The elementwise action of `fix` is
the least fixed point of the corresponding map: `fix.toElementMap φ = fix(toApproxMap φ)`. The
forward inclusion (`⊆ x`) is `exists_principal_iterMap`; the reverse is monotonicity of `fix` along
`↑W ⊑ toApproxMap φ`. -/
theorem fixMap_toElementMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ = (toApproxMap φ).fixElement := by
  apply Element.ext
  intro X
  rw [toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨W, hw, hmem⟩
    rw [fixMap_toElementMap_principal] at hmem
    have hle : (funSpace V V).principal (φ.sub hw) ≤ φ :=
      fun Z hZ => φ.up_mem hw hZ.1 hZ.2
    exact fixElement_mono ((funSpaceEquiv V V).monotone hle) X hmem
  · rintro ⟨n, hn⟩
    obtain ⟨W, hw, hWn⟩ := exists_principal_iterMap V φ n X hn
    refine ⟨W, hw, ?_⟩
    rw [fixMap_toElementMap_principal]
    exact ⟨n, hWn⟩

/-- **Theorem 4.2(i) (Scott 1981, PRG-19).** `fix(f) = f(fix(f))`: the value of `fix` is a fixed
point of the argument. (Equivalently `eval(f, fix(f)) = fix(f)` by `evalMap_apply`.) -/
theorem fixMap_fixed (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ := by
  rw [fixMap_toElementMap]
  exact toElementMap_fixElement (toApproxMap φ)

/-- **Theorem 4.2(ii) (Scott 1981, PRG-19).** `f(x) ⊆ x ⟹ fix(f) ⊆ x`: `fix` lands in the least
pre-fixed point. -/
theorem fixMap_least (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element}
    (hz : (toApproxMap φ).toElementMap z ≤ z) : (fixMap V).toElementMap φ ≤ z := by
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap φ) hz

/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)` (as a directed union). -/
theorem fixMap_eq_iSup (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ =
      NeighborhoodSystem.iSupDirected ((toApproxMap φ).iterElem)
        (fun i j => ⟨max i j, iterElem_mono _ (le_max_left i j),
          iterElem_mono _ (le_max_right i j)⟩) := by
  rw [fixMap_toElementMap]
  exact fixElement_eq_iSupDirected (toApproxMap φ)

/-- `fix` applied to (the filter of) an approximable map `f` returns the least fixed point of `f`.
This is the bridge to the "for any `f : 𝒟 → 𝒟`" form of Theorem 4.2, using the Theorem 3.10
isomorphism `toApproxMap (toFilter f) = f`. -/
theorem fixMap_toElementMap_toFilter (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    (fixMap V).toElementMap (toFilter f) = f.fixElement := by
  rw [fixMap_toElementMap]
  have h : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv V V).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  rw [h]

/-- **Theorem 4.2 (Scott 1981, PRG-19) — uniqueness.** Any approximable operator `fax` satisfying
(i) and (ii) coincides with `fix`. (Scott: from (i)(ii) one proves `fix(f) ⊆ fax(f)` and
`fax(f) ⊆ fix(f)`.) -/
theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))

end Scott1980.Neighborhood
