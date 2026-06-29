import Scott1980.Neighborhood.Product
import Scott1980.Neighborhood.Example23

/-!
# Exercise 3.26 (Scott 1981, PRG-19, §3) — the conditional operator `cond`

Scott asks: for every domain `D` there is an approximable mapping

`cond : T × D × D → D`

(the *conditional operator*) satisfying

* `cond(true,  x, y) = x`,
* `cond(false, x, y) = y`,
* `cond(⊥,     x, y) = ⊥`.

Here `T` is the truth domain of Example 1.2 (`Example12.neighborhoodSystem`), whose neighbourhoods
are `{Δ, {0}, {1}}` with `true = ↑{0}` (`Example23.trueElt`), `false = ↑{1}` (`falseElt`) and
`⊥ = {Δ}` (`botElt`). The product `T × D × D` is the tagged product of Exercise 3.14, modelled here
as `prod T (prod V V)` over the token type `T.Token ⊕ (α ⊕ α)`; a neighbourhood is
`0C ∪ 10X ∪ 110Y`, recovered from `W` by the projections `C = inl⁻¹ W`, `X = inl⁻¹ inr⁻¹ W`,
`Y = inr⁻¹ inr⁻¹ W`.

Scott's hint gives the relation directly:

```
0C ∪ 10X ∪ 110Y  cond  Z   iff   0 ∈ C and X ⊆ Z,  or
                                  1 ∈ C and Y ⊆ Z,  or
                                  0, 1 ∈ C and Δ ⊆ Z.
```

Since `T = {Δ, {0}, {1}}`, the three guards on `C` are *mutually exclusive and exhaustive*:
`0 ∈ C` (alone) means `C = {0}`, `1 ∈ C` (alone) means `C = {1}`, and `0, 1 ∈ C` means `C = Δ`. We
therefore phrase the relation with explicit equalities `C = {0} / {1} / Δ` (`condGuard`), which is
mathematically identical to Scott's membership form but makes the case analysis transparent and the
three identities clean.

Everything is **choice-free** in spirit; the only classical input is inherited from `T` (Example 1.2)
and from the project's `ext_of_toElementMap`/`Element.ext` machinery, as elsewhere in §3.
-/

namespace Scott1980.Neighborhood.Exercise326

open Scott1980.Neighborhood NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- The truth domain `T` of Example 1.2 (neighbourhoods `{Δ, {0}, {1}}`). -/
abbrev TD : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-! ### Token-level facts about `T`'s three neighbourhoods `{0}`, `{1}`, `Δ`. -/

theorem zero_ne_one : (Example12.zero : Set Example12.Token) ≠ Example12.one := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.zero, Example12.one] at h0

theorem zero_ne_master : (Example12.zero : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h1 := Set.ext_iff.mp h 1
  simp [Example12.zero, Example12.master] at h1

theorem one_ne_master : (Example12.one : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.one, Example12.master] at h0

/-- A `T`-neighbourhood contained in `{0}` is `{0}` (the other two, `Δ` and `{1}`, are not). -/
theorem Tmem_eq_zero {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.zero) :
    C = Example12.zero := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 1)) (by simp [Example12.zero])
  · rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])

/-- A `T`-neighbourhood contained in `{1}` is `{1}`. -/
theorem Tmem_eq_one {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.one) :
    C = Example12.one := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 0)) (by simp [Example12.one])
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])
  · rfl

/-! ### The conditional relation. -/

/-- Scott's guard for `cond`, phrased with explicit equalities on the truth component
`C = inl⁻¹ W`. With `X = inl⁻¹ inr⁻¹ W` and `Y = inr⁻¹ inr⁻¹ W`:

* `C = {0}` (`true`):  `X ⊆ Z`;
* `C = {1}` (`false`): `Y ⊆ Z`;
* `C = Δ` (`⊥`):       `Δ_D ⊆ Z`. -/
def condGuard (V : NeighborhoodSystem α) (W : Set (Example12.Token ⊕ (α ⊕ α))) (Z : Set α) : Prop :=
  (Sum.inl ⁻¹' W = Example12.zero ∧ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.one ∧ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.master ∧ V.master ⊆ Z)

variable (V : NeighborhoodSystem α)

theorem condGuard_zero {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.zero) : Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨_, h⟩ | ⟨hC', _⟩ | ⟨hC', _⟩
  · exact h
  · exact absurd (hC.symm.trans hC') zero_ne_one
  · exact absurd (hC.symm.trans hC') zero_ne_master

theorem condGuard_one {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.one) : Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨_, h⟩ | ⟨hC', _⟩
  · exact absurd (hC.symm.trans hC') zero_ne_one.symm
  · exact h
  · exact absurd (hC.symm.trans hC') one_ne_master

theorem condGuard_master {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.master) : V.master ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨hC', _⟩ | ⟨_, h⟩
  · exact absurd (hC.symm.trans hC') zero_ne_master.symm
  · exact absurd (hC.symm.trans hC') one_ne_master.symm
  · exact h

/-- The three components `C, X, Y` of an input neighbourhood are themselves neighbourhoods. -/
theorem cond_components {W : Set (Example12.Token ⊕ (α ⊕ α))}
    (hW : (prod TD (prod V V)).mem W) :
    Example12.mem (Sum.inl ⁻¹' W) ∧
      V.mem (Sum.inl ⁻¹' (Sum.inr ⁻¹' W)) ∧ V.mem (Sum.inr ⁻¹' (Sum.inr ⁻¹' W)) := by
  obtain ⟨C, P, hC, hP, rfl⟩ := hW
  obtain ⟨X, Y, hX, hY, rfl⟩ := hP
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨hC, hX, hY⟩

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The conditional operator `cond : T × D × D → D`. -/
def cond (V : NeighborhoodSystem α) : ApproximableMap (prod TD (prod V V)) V where
  rel W Z := (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨(prod TD (prod V V)).master_mem, V.master_mem, Or.inr (Or.inr ⟨?_, subset_rfl⟩)⟩
    show Sum.inl ⁻¹' (prod TD (prod V V)).master = Example12.master
    rw [prod_master, inl_preimage_prodNbhd]; rfl
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hg⟩ ⟨_, hZ', hg'⟩
    obtain ⟨_, hX, hY⟩ := cond_components V hW
    refine ⟨hW, ?_, ?_⟩
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact V.inter_mem hZ hZ' hX (Set.subset_inter hXZ (condGuard_zero V hg' hCz))
      · exact V.inter_mem hZ hZ' hY (Set.subset_inter hYZ (condGuard_one V hg' hCo))
      · exact V.inter_mem hZ hZ' V.master_mem (Set.subset_inter hmZ (condGuard_master V hg' hCm))
    · rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
      · exact Or.inl ⟨hCz, Set.subset_inter hXZ (condGuard_zero V hg' hCz)⟩
      · exact Or.inr (Or.inl ⟨hCo, Set.subset_inter hYZ (condGuard_one V hg' hCo)⟩)
      · exact Or.inr (Or.inr ⟨hCm, Set.subset_inter hmZ (condGuard_master V hg' hCm)⟩)
  mono := by
    rintro W W₂ Z Z₂ ⟨hW, hZ, hg⟩ hW₂W hZZ₂ hW₂ hZ₂
    obtain ⟨hC₂, hX₂, hY₂⟩ := cond_components V hW₂
    refine ⟨hW₂, hZ₂, ?_⟩
    have hCsub : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hXsub : Sum.inl ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    have hYsub : Sum.inr ⁻¹' (Sum.inr ⁻¹' W₂) ⊆ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) :=
      Set.preimage_mono (Set.preimage_mono hW₂W)
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨hCm, hmZ⟩
    · exact Or.inl ⟨Tmem_eq_zero hC₂ (hCsub.trans hCz.subset), (hXsub.trans hXZ).trans hZZ₂⟩
    · exact Or.inr (Or.inl ⟨Tmem_eq_one hC₂ (hCsub.trans hCo.subset),
        (hYsub.trans hYZ).trans hZZ₂⟩)
    · have hmZ₂ : V.master ⊆ Z₂ := hmZ.trans hZZ₂
      rcases (Example12.mem_iff (Sum.inl ⁻¹' W₂)).mp hC₂ with hC₂m | hC₂z | hC₂o
      · exact Or.inr (Or.inr ⟨hC₂m, hmZ₂⟩)
      · exact Or.inl ⟨hC₂z, (V.sub_master hX₂).trans hmZ₂⟩
      · exact Or.inr (Or.inl ⟨hC₂o, (V.sub_master hY₂).trans hmZ₂⟩)

@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

/-! ### Elementwise characterization, and the three defining identities. -/

/-- The elementwise action of `cond`, computed at a paired argument `⟨t, ⟨x, y⟩⟩`: a neighbourhood
`Z` lies in `cond(t, x, y)` iff `t` selects `true` (`{0} ∈ t`) and `Z ∈ x`, or `t` selects `false`
(`{1} ∈ t`) and `Z ∈ y`, or `Z = Δ_D` (the always-present master). The three defining identities are
immediate corollaries. -/
theorem cond_toElementMap_mem (t : TD.Element) (x y : V.Element) {Z : Set α} :
    ((cond V).toElementMap (pair t (pair x y))).mem Z ↔
      (t.mem Example12.zero ∧ x.mem Z) ∨ (t.mem Example12.one ∧ y.mem Z) ∨ Z = V.master := by
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCt, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, hXZ⟩ | ⟨hCo, hYZ⟩ | ⟨_, hmZ⟩
    · exact Or.inl ⟨hCz ▸ hCt, x.up_mem hXx hZ hXZ⟩
    · exact Or.inr (Or.inl ⟨hCo ▸ hCt, y.up_mem hYy hZ hYZ⟩)
    · exact Or.inr (Or.inr (Set.Subset.antisymm (V.sub_master hZ) hmZ))
  · intro h
    rcases h with ⟨ht0, hxZ⟩ | ⟨ht1, hyZ⟩ | rfl
    · have hZ : V.mem Z := x.sub hxZ
      refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
        ht0, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
      refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
      rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]
    · have hZ : V.mem Z := y.sub hyZ
      refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
        ht1, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
      refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
      rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]
    · refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
        ⟨Example12.master, prodNbhd V.master V.master, t.master_mem,
          ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
        prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
        V.master_mem, ?_⟩
      exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

/-- **Exercise 3.26(i) (Scott 1981, PRG-19).** `cond(true, x, y) = x`. -/
theorem cond_true (x y : V.Element) :
    (cond V).toElementMap (pair Example23.trueElt (pair x y)) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCtrue, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨_, hXZ⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact x.up_mem hXx hZ hXZ
    · rcases hCtrue with hCm | hCz
      · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
      · exact absurd (hCz.symm.trans hCo) zero_ne_one
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact x.master_mem
  · intro hxZ
    have hZ : V.mem Z := x.sub hxZ
    refine ⟨prodNbhd Example12.zero (prodNbhd Z V.master), ⟨Example12.zero, prodNbhd Z V.master,
      Or.inr rfl, ⟨Z, V.master, hxZ, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_zero (prod_mem_prodNbhd hZ V.master_mem), hZ, ?_⟩
    refine Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩
    rw [inr_preimage_prodNbhd, inl_preimage_prodNbhd]

/-- **Exercise 3.26(ii) (Scott 1981, PRG-19).** `cond(false, x, y) = y`. -/
theorem cond_false (x y : V.Element) :
    (cond V).toElementMap (pair Example23.falseElt (pair x y)) = y := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCfalse, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    rcases hg with ⟨hCz, _⟩ | ⟨_, hYZ⟩ | ⟨_, hmZ⟩
    · rcases hCfalse with hCm | hCo
      · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
      · exact absurd (hCo.symm.trans hCz) zero_ne_one.symm
    · exact y.up_mem hYy hZ hYZ
    · rw [Set.Subset.antisymm (V.sub_master hZ) hmZ]; exact y.master_mem
  · intro hyZ
    have hZ : V.mem Z := y.sub hyZ
    refine ⟨prodNbhd Example12.one (prodNbhd V.master Z), ⟨Example12.one, prodNbhd V.master Z,
      Or.inr rfl, ⟨V.master, Z, x.master_mem, hyZ, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_one (prod_mem_prodNbhd V.master_mem hZ), hZ, ?_⟩
    refine Or.inr (Or.inl ⟨inl_preimage_prodNbhd _ _, ?_⟩)
    rw [inr_preimage_prodNbhd, inr_preimage_prodNbhd]

/-- **Exercise 3.26(iii) (Scott 1981, PRG-19).** `cond(⊥, x, y) = ⊥`. -/
theorem cond_bot (x y : V.Element) :
    (cond V).toElementMap (pair Example23.botElt (pair x y)) = V.bot := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, _, hZ, hg⟩
    obtain ⟨C, P, hCbot, hPmem, rfl⟩ := hWmem
    obtain ⟨X, Y, hXx, hYy, rfl⟩ := hPmem
    simp only [condGuard, inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hg
    have hCm : C = Example12.master := hCbot
    rcases hg with ⟨hCz, _⟩ | ⟨hCo, _⟩ | ⟨_, hmZ⟩
    · exact absurd (hCm.symm.trans hCz) zero_ne_master.symm
    · exact absurd (hCm.symm.trans hCo) one_ne_master.symm
    · rw [mem_bot, Set.Subset.antisymm (V.sub_master hZ) hmZ]
  · intro hbZ
    rw [mem_bot] at hbZ
    subst hbZ
    refine ⟨prodNbhd Example12.master (prodNbhd V.master V.master),
      ⟨Example12.master, prodNbhd V.master V.master, rfl,
        ⟨V.master, V.master, x.master_mem, y.master_mem, rfl⟩, rfl⟩,
      prod_mem_prodNbhd Example12.mem_master (prod_mem_prodNbhd V.master_mem V.master_mem),
      V.master_mem, ?_⟩
    exact Or.inr (Or.inr ⟨inl_preimage_prodNbhd _ _, subset_rfl⟩)

end Scott1980.Neighborhood.Exercise326
