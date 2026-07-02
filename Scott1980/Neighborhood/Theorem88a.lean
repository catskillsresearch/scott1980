import Scott1980.Neighborhood.Theorem88
import Scott1980.Neighborhood.Definition610
import Mathlib.Data.Countable.Defs

/-!
# Theorem 8.8(a) (Scott 1981, PRG-19, Lecture VIII) — assembling `D ≅ᴰ D' ∧ D' ◁ U`

`Theorem88.lean` builds, for **any** sequence `X : ℕ → Set α` and master `Δ : Set α` with
`Δ.Nonempty`, a sequence `Yseq X Δ : ℕ → Set ℚ` satisfying the finite-constraint transfer laws.
This file supplies the missing final ingredient and assembles Theorem 8.8(a) in full.

## The `D†` preparation (Scott's "without loss of generality `𝒟 ≅ 𝒟†`")

Feeding an arbitrary countable `D`'s own enumeration `e : ℕ → Set α` directly into `Yseq` is
**not** enough: `Subsystem.inter_closed` demands that whenever `Yᵢ ∩ Yⱼ` happens to be a genuine
`U`-neighbourhood (which, since `U` is so permissive, happens whenever it is merely non-empty as a
raw set), the pulled-back `Xᵢ ∩ Xⱼ` must already be a `D`-neighbourhood. This can fail for a
perfectly good `D` where `Xᵢ, Xⱼ` overlap as raw sets without being *witnessed-consistent*
(`Scott 1981`, Definition 7.9's discussion: `↓X ∩ ↓Y = ↓(X ∩ Y)`, empty exactly when `{X,Y}` is
*not* consistent in `D`, regardless of whether `X ∩ Y ≠ ∅` as sets). Scott's fix is to replace `D`
by `D† = {↓X ∣ X ∈ D}` (down-sets in `D`'s own neighbourhood order) before running the
construction.

We implement this by **reindexing over `ℕ`** rather than building a `D†` `NeighborhoodSystem`
structure by hand: set

```
X' n := {m : ℕ ∣ e m ⊆ e n}         (Scott's `↓(e n)`, as a subset of the index set ℕ)
Δ' := Set.univ                      (Scott's `↓Δ = D`, i.e. "all indices")
```

and feed `(X', Δ')` into `Yseq`. Three facts drive everything below:

* `X' n` is **always non-empty** (`n ∈ X' n`), sidestepping any `Δ.Nonempty`/`∅`-freeness worries.
* `X' i ⊆ X' j ↔ e i ⊆ e j` (`idxSet_subset_iff`): the *raw* inclusion order on indices matches
  `D`'s inclusion order on neighbourhoods, so `transfer_subset_iff` transfers `D`'s own order
  exactly (`embed_subset_iff`).
* `e i ∩ e j = e m → X' i ∩ X' j = X' m` (`idxSet_inter_of_inter_eq`) is a **definitional**
  rewriting (no transfer needed): this is what repairs the `inter_closed` gap, because `D`'s own
  `inter_mem` axiom (not any separation hypothesis) is what supplies the witness `m` with
  `e i ∩ e j = e m` whenever `{e i, e j}` is witnessed-consistent — and *only* then.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- **Scott's `↓(e n)`, reindexed over `ℕ`**: the set of indices `m` whose neighbourhood `e m` sits
below `e n`. This is `D†`'s replacement for `e n` itself. -/
def idxSet (n : ℕ) : Set ℕ := {m | e m ⊆ e n}

@[simp] theorem mem_idxSet {m n : ℕ} : m ∈ idxSet e n ↔ e m ⊆ e n := Iff.rfl

/-- Every index belongs to its own `idxSet` (`e n ⊆ e n`) — so `idxSet e n` is always non-empty,
regardless of whether `e n` itself is empty. -/
theorem self_mem_idxSet (n : ℕ) : n ∈ idxSet e n := show e n ⊆ e n from subset_rfl

theorem idxSet_nonempty (n : ℕ) : (idxSet e n).Nonempty := ⟨n, self_mem_idxSet e n⟩

/-- The raw inclusion order on `idxSet`s matches `e`'s own inclusion order — this is the
"separation" property `D†` is built to have. -/
theorem idxSet_subset_iff (i j : ℕ) : idxSet e i ⊆ idxSet e j ↔ e i ⊆ e j :=
  ⟨fun h => h (self_mem_idxSet e i), fun h _ hm => hm.trans h⟩

theorem idxSet_eq_iff (i j : ℕ) : idxSet e i = idxSet e j ↔ e i = e j :=
  ⟨fun h => Set.Subset.antisymm ((idxSet_subset_iff e i j).mp h.subset)
      ((idxSet_subset_iff e j i).mp h.symm.subset),
    fun h => by rw [idxSet, idxSet, h]⟩

/-- If `e i ∩ e j = e m` (i.e. `{e i, e j}` is witnessed-consistent, with witness realizing the
intersection exactly as `e m`), then `idxSet e i ∩ idxSet e j = idxSet e m` — a **definitional**
rewriting of the set-builder, needing no transfer at all. -/
theorem idxSet_inter_of_inter_eq {i j m : ℕ} (h : e i ∩ e j = e m) :
    idxSet e i ∩ idxSet e j = idxSet e m := by
  ext k
  show e k ⊆ e i ∧ e k ⊆ e j ↔ e k ⊆ e m
  rw [← Set.subset_inter_iff, h]

theorem idxSet_zero_eq_univ {n0 : ℕ} (hsub : ∀ m, e m ⊆ e n0) : idxSet e n0 = Set.univ :=
  Set.eq_univ_of_forall hsub

end Reencode

/-! ## Setting up `D`'s enumeration and the induced `Yidx : ℕ → Set ℚ` -/

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- Every enumerated set is a genuine `D`-neighbourhood. -/
theorem D_mem_e (n : ℕ) : D.mem (e n) := (hcover (e n)).mpr ⟨n, rfl⟩

include hcover in
theorem e_subset_master (n : ℕ) : e n ⊆ D.master := D.sub_master (D_mem_e D e hcover n)

include hcover he0 in
theorem idxSet_zero : idxSet e 0 = Set.univ :=
  idxSet_zero_eq_univ e (fun m => he0 ▸ e_subset_master D e hcover m)

/-- `Δ' := Set.univ` is always non-empty, so the general `Yseq`/transfer apparatus of
`Theorem88.lean` applies to `(idxSet e, Set.univ)` unconditionally — no `∅`-freeness hypothesis on
`D` is ever needed, since we reindexed onto `ℕ` before invoking it (`idxSet_nonempty`). -/
theorem univ_nonempty_nat : (Set.univ : Set ℕ).Nonempty := ⟨0, trivial⟩

/-- **Scott's `Yₙ`, built from the separated reindexing.** -/
noncomputable abbrev Yidx (n : ℕ) : Set ℚ := Yseq (idxSet e) Set.univ n

include hcover he0 in
/-- `Yidx e 0 = U.master`, since `idxSet e 0 = Set.univ` (Scott's `X₀ = Δ`). -/
theorem Yidx_zero : Yidx e 0 = U.master :=
  Yseq_zero_eq_master (idxSet e) Set.univ univ_nonempty_nat (idxSet_zero D e hcover he0)

/-- `Yidx e n` is always `⊆ U.master`. -/
theorem Yidx_subset_master (n : ℕ) : Yidx e n ⊆ U.master :=
  Yseq_subset_master (idxSet e) Set.univ univ_nonempty_nat n

/-- `Yidx e n` is always `∅` or a genuine `U`-neighbourhood. -/
theorem Yidx_empty_or_mem (n : ℕ) : Yidx e n = ∅ ∨ U.mem (Yidx e n) :=
  Yseq_empty_or_mem (idxSet e) Set.univ univ_nonempty_nat n

/-- **`Yidx e n` is always non-empty** (hence, by `Yidx_empty_or_mem`, always a genuine
`U`-neighbourhood): `n` itself witnesses `n ∈ idxSet e n`. -/
theorem Yidx_nonempty (n : ℕ) : (Yidx e n).Nonempty :=
  Yseq_nonempty_of_mem (idxSet e) Set.univ univ_nonempty_nat (Set.mem_univ n) (self_mem_idxSet e n)

theorem Yidx_mem (n : ℕ) : U.mem (Yidx e n) :=
  (Yidx_empty_or_mem e n).resolve_left (Yidx_nonempty e n).ne_empty

/-- **The order-embedding at the neighbourhood level.** This is where the whole `idxSet`
reindexing pays off: because `idxSet`'s inclusion order matches `e`'s (`idxSet_subset_iff`), the
generic `transfer_subset_iff` (with `Δ' = Set.univ`, so the `Δ' ∩ ·`/`U.master ∩ ·` wrappers are
trivial since `Yidx e i ⊆ U.master` always) yields exactly Scott's matching invariant restricted to
plain inclusion. -/
theorem embed_subset_iff (i j : ℕ) : e i ⊆ e j ↔ Yidx e i ⊆ Yidx e j := by
  rw [← idxSet_subset_iff e i j]
  have := transfer_subset_iff (idxSet e) Set.univ univ_nonempty_nat i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at this

theorem embed_eq_iff (i j : ℕ) : e i = e j ↔ Yidx e i = Yidx e j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mp h.subset)
      ((embed_subset_iff e j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mpr h.subset)
      ((embed_subset_iff e j i).mpr h.symm.subset)⟩

end Setup

/-! ## The subsystem `D'` and `D' ◁ U` -/

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- **The shared "find a matching index" step.** Given `D.mem (e i ∩ e j)` (however that was
established — a direct witness, or `D`'s own `inter_mem`), `hcover` names it as `e m` for some
`m`, and `transfer_inter_eq_iff` (fed through the `idxSet`-level rewriting
`idxSet_inter_of_inter_eq`) pushes the equation across to `Yidx`. This single lemma drives
`DprimeU`'s `inter_mem`, `DprimeU_subsystem`'s `inter_closed`, and both halves of the element-level
isomorphism below. -/
theorem exists_inter_index_of_dmem {i j : ℕ} (hDij : D.mem (e i ∩ e j)) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  obtain ⟨m, hm⟩ := (hcover (e i ∩ e j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff (idxSet e) Set.univ univ_nonempty_nat i j m
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp (idxSet_inter_of_inter_eq e hm)⟩

include hcover in
/-- **The "unwitnessed" variant**, used exactly when only the raw non-emptiness of `Yidx e i ∩
Yidx e j` is known (not an explicit `D`-side witness): non-emptiness transfers down
(`transfer_inter_empty_iff`) to `idxSet e i ∩ idxSet e j`, any element `k` of which supplies
`e k ⊆ e i ∩ e j`, so `D`'s own `inter_mem` produces `D.mem (e i ∩ e j)` and
`exists_inter_index_of_dmem` finishes. -/
theorem exists_inter_index_of_nonempty {i j : ℕ} (hne : (Yidx e i ∩ Yidx e j).Nonempty) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  have hne' : (idxSet e i ∩ idxSet e j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff (idxSet e) Set.univ univ_nonempty_nat i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem D e hcover
    (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
      (Set.subset_inter hki hkj))

include hcover he0 in
/-- **`D'`**: the neighbourhood system generated by `{Yidx e n ∣ n ∈ ℕ}`. Its `inter_mem` axiom
transfers *directly* from `D`'s own `inter_mem`: a witness `X k ⊆ X i ∩ X j` on the `D'`-side pulls
back (`embed_subset_iff`) to a witness `e k ⊆ e i ∩ e j` on the `D`-side, so `D`'s own axiom
supplies `e m = e i ∩ e j` for some `m`, and `transfer_inter_eq_iff` pushes this equation back
across to `Yidx e i ∩ Yidx e j = Yidx e m`. -/
noncomputable def DprimeU : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yidx e n
  master := U.master
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yidx_subset_master e n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e k ⊆ e i := (embed_subset_iff e k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e k ⊆ e j := (embed_subset_iff e k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem D e hcover
      (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
        (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

include hcover he0 in
/-- **`D' ◁ U`.** `sub` is `Yidx_mem`; `inter_closed` uses `exists_inter_index_of_nonempty` to find
*some* witnessed-consistent pair on the `D`-side from the mere non-emptiness of `Yidx e i ∩ Yidx e
j` (guaranteed by `U.mem`). -/
theorem DprimeU_subsystem : DprimeU D e hcover he0 ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact Yidx_mem e n
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty D e hcover hUmem.2.1
    exact ⟨m, hYeq⟩

end Subsystem

/-! ## The element-level isomorphism `D ≅ᴰ D'` -/

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
/-- **Pushforward**: the `D'`-filter `{Yidx e n ∣ e n ∈ x}` induced by a `D`-filter `x`. -/
def toDprimeU (x : D.Element) : (DprimeU D e hcover he0).Element where
  mem Y := ∃ n, Y = Yidx e n ∧ x.mem (e n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm, by rw [he0]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem D e hcover (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e i ⊆ e j := (embed_subset_iff e i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D e hcover j) heij⟩

include hcover he0 in
/-- **Pullback**: the `D`-filter `{e n ∣ Yidx e n ∈ y}` induced by a `D'`-filter `y`. -/
def toD (y : (DprimeU D e hcover he0).Element) : D.Element where
  mem S := ∃ n, S = e n ∧ y.mem (Yidx e n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D e hcover n
  master_mem := ⟨0, he0.symm, by rw [Yidx_zero D e hcover he0]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeU D e hcover he0).mem (Yidx e i ∩ Yidx e j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty D e hcover
      ((DprimeU_subsystem D e hcover he0).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover T).mp hDT
    have hYij : Yidx e i ⊆ Yidx e j := (embed_subset_iff e i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

include hcover he0 in
/-- **The order isomorphism `D.Element ≃o D'.Element`.** `toDprimeU`/`toD` are mutually inverse
(via `embed_eq_iff`, which resolves the ambiguity of *which* index represents a given
neighbourhood) and preserve/reflect `≤` (via `hcover`, which shows every `D`-neighbourhood a
filter can mention is literally some `e n`). -/
noncomputable def domainIso : DomainIso D (DprimeU D e hcover he0) where
  toFun := toDprimeU D e hcover he0
  invFun := toD D e hcover he0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff e n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hxS)
      have hxn : x.mem (e n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeU D e hcover he0 x).mem (Yidx e n))
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

/-- **Theorem 8.8(a) (isomorphism half).** `D ≅ᴰ D'`. -/
theorem isomorphic_DprimeU : D ≅ᴰ DprimeU D e hcover he0 := ⟨domainIso D e hcover he0⟩

end Iso

/-! ## Theorem 8.8(a): the general (non-effective) universality of `U` -/

/-- **Theorem 8.8(a) (Scott 1981, PRG-19, Lecture VIII).** `𝒰` is universal: every *countable*
neighbourhood system `D` embeds, up to isomorphism, as a subsystem of `𝒰`.

The enumeration `e` is built from any surjection `f : ℕ → {S // D.mem S}` (`exists_surjective_nat`,
using `Countable`/`Nonempty` — the only place `Classical.choice` enters, since neither hypothesis is
data), shifted by one and patched at `0` to enforce Scott's convention `X₀ = Δ`. Everything else —
`idxSet`'s "separated" reindexing, the `Yidx`/transfer apparatus of `Theorem88.lean`, and the
`DprimeU`/`domainIso` machinery above — is then assembled directly. -/
theorem theorem_8_8_a {α : Type*} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] :
    ∃ D' : NeighborhoodSystem ℚ, (D ≅ᴰ D') ∧ (D' ◁ U) := by
  haveI : Nonempty {S : Set α // D.mem S} := ⟨⟨D.master, D.master_mem⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat {S : Set α // D.mem S}
  set e : ℕ → Set α := fun n => if n = 0 then D.master else (f (n - 1)).1 with hedef
  have he0 : e 0 = D.master := if_pos rfl
  have hen : ∀ n, e (n + 1) = (f n).1 := by
    intro n
    show (if n + 1 = 0 then D.master else (f (n + 1 - 1)).1) = (f n).1
    rw [if_neg (Nat.succ_ne_zero n), Nat.succ_sub_one]
  have hcover : ∀ S, D.mem S ↔ ∃ n, S = e n := by
    intro S
    constructor
    · intro hS
      obtain ⟨k, hk⟩ := hf ⟨S, hS⟩
      exact ⟨k + 1, by rw [hen k]; exact (congrArg Subtype.val hk).symm⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => rw [he0]; exact D.master_mem
      | succ n => rw [hen n]; exact (f n).2
  exact ⟨DprimeU D e hcover he0, isomorphic_DprimeU D e hcover he0, DprimeU_subsystem D e hcover he0⟩

end Scott1980.Neighborhood
