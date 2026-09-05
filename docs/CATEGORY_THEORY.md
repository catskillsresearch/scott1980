# Category Theory in the Scott1980 Lean Formalization

Category theory appears in this repository mainly as Scott's Lecture VI vocabulary and a few later
functor/monad exercises — not as a general Mathlib category-theory development.

## Design choice: bespoke, not Mathlib

The core abstraction lives in [`Scott1980/Neighborhood/Definition63.lean`](../Scott1980/Neighborhood/Definition63.lean).
It defines a small self-contained layer:

- **`Category`** — objects, `Hom`, `id`, `comp`, the three laws
- **`Endofunctor`** — `obj`, `map`, identity/composition preservation
- **`TAlgebra`**, **`AlgHom`**, **`IsInitial`**
- **`Iso`** (for Lambek-style results)

The file explicitly explains why **Mathlib's `CategoryTheory` is not imported**: Mathlib's
initial-algebra API would pull in `Classical.choice`, while this project's Propositions 6.6–6.7 are
proved choice-free. So the repo uses "a small amount of category theory" in Scott's sense,
implemented locally.

## 1. The category of domains (Scott's running example)

| Role | Lean type | Scott source |
|------|-----------|--------------|
| Objects | `DomainObj` (token type + `NeighborhoodSystem`) | Lecture VI |
| Morphisms | `ApproximableMap` | Def 2.1 |
| Laws | `idMap_comp`, `comp_idMap`, `comp_assoc` (Theorem 2.5) | Thm 2.5 |

This is the concrete instance of Scott's remark that neighbourhood systems and approximable maps
"form quite an interesting category."

## 2. Lecture VI: endofunctors, algebras, initial algebras

This is the main categorical spine, matching Scott's Definitions 6.3–6.5:

| Concept | Lean module | Scott source |
|---------|-------------|--------------|
| Endofunctor | `Endofunctor DomainObj` | Def 6.3 |
| `T`-algebra + homomorphisms | `TAlgebra`, `AlgHom` | Def 6.4 |
| Initial algebra | `IsInitial` | Def 6.5 |
| Unique iso of initials | `Proposition66.lean` | Prop 6.6 |
| Lambek's lemma | `lambek` in `Proposition67.lean` | Prop 6.7 |
| Continuous on maps | `ContinuousOnMaps` in `Definition68.lean` | Def 6.8 |
| Homomorphisms from fixed point | `Theorem69.lean` | Thm 6.9 |
| Monotone/continuous on domains | `Definition613.lean` | Def 6.13 |
| Existence of initial algebra | `Theorem614.lean` (colimit `⋃ₙ Tⁿ({Γ})`) | Thm 6.14 |
| Initial algebra embeds in every solution | `Theorem616.lean` | Thm 6.16 |

Theorem 6.14 is explicitly a **colimit** construction: iterate a functor from a generating system
`Γ` and take the union.

## 3. Cartesian closed category (Exercise 3.23)

[`Exercise323.lean`](../Scott1980/Neighborhood/Exercise323.lean) packages Scott's "for category
theorists" remark:

- **Terminal object:** `unitSys` (Exercise 3.15)
- **Products:** `prod`, `proj₀`, `proj₁`
- **Exponentials:** `curryEquiv` from Theorem 3.12

So the category of domains and approximable maps is shown to be **cartesian closed**, with
`(𝒟₀ → -)` as the right adjoint to `- × 𝒟₀`.

## 4. Functorial structure on domain constructors

Several files treat `×`, `+`, and `→` as **functors on maps**:

| Functor | Module(s) | Scott source |
|---------|-----------|--------------|
| Product `prodMap` | `Exercise319.lean`, `Exercise320.lean` | Exercises 3.19–3.20 |
| Sum `sumMap` | `Exercise319Sum.lean` | Exercise 3.19 (sum) |
| Exponential `expMap` | `FunctionSpace.lean`, `Proposition810b.lean`, `Exercise819.lean` | Thm 3.12, Ex 8.19 |

These are used heavily in Lecture VIII (Definition 8.9's combinators on `𝒰`, Proposition 8.10's
projection-closure).

## 5. Power domain as functor and monad (Lecture VII)

- **Exercise 7.19** ([`Exercise719.lean`](../Scott1980/Neighborhood/Exercise719.lean)): `D ↦ ℙD` is a
  functor via `PFmap` / `ℙf`, with identity and composition laws.
- **Exercise 7.20** ([`Exercise720.lean`](../Scott1980/Neighborhood/Exercise720.lean)): `union : ℙℙD → ℙD`
  is the monad multiplication `μ`; `↓ : D → ℙD` is the unit.

So the Smyth power domain is treated categorically as a **monad**, not just a domain construction.

## 6. Concrete syntax endofunctors (Exercises 6.21–6.23)

[`Exercise623.lean`](../Scott1980/Neighborhood/Exercise623.lean) is the big applied example:

- **`GExpr`** — syntactic functor expressions (`N`, `X`, `+`, `×`)
- **`gFunctor`** — every `GExpr` is an `Endofunctor` of the strict-map category `ScottSys`
- **`TexpF`** — the functor `T(X) = N ⊕ ((X×X) + (X×X))` from Exercise 6.23
- **Colimit tower** `gColim T = ⋃ₙ Tⁿ({Γ})` and the solution domain `Exp`

Related files: `Exercise617.lean`, `Exercise617Gen.lean`, `Exercise622.lean`, `Exercise621.lean`,
`Exercise619PartB.lean`.

## 7. Other categorical uses

- **Bottom functor `(·)_⊥`** — Exercise 6.26 ([`Exercise626.lean`](../Scott1980/Neighborhood/Exercise626.lean)):
  strict functor on Scott's category.
- **Functoriality of `⊴`** — Exercise 8.19 ([`Exercise819.lean`](../Scott1980/Neighborhood/Exercise819.lean)):
  covariant/contravariant functoriality of embedding in `prod`, `sum`, and `exp`.
- **Exercise 6.29 indexed products/sums** — `iprod`, `iotimes` as categorical-style universal
  constructions over index types.
- **Definition 8.9 / Prop 8.10** — universal-domain combinators built via `prodMap`, `sumMap`, `expMap`
  functor laws.

## What is *not* category theory (but often adjacent)

Most of the repo uses **order theory**, not category theory:

- `Element`, `element_le`, `OrderIso`, `DomainIso`, `⊴`, `◁`
- Fixed-point theorems (Lecture IV) via approximable maps, not general limits/colimits

These are Scott's domain-theoretic tools; they overlap with categorical language (`Iso`, "universal")
but are not built on the `Category`/`Endofunctor` API.

## Summary map

<img src="figures/category-theory-map.png" alt="Category theory summary map"
     style="display: block; margin: 0 auto; width: 2in; height: auto;" />

## Bottom line

Category theory here is concentrated in:

1. **Lecture VI** — domain-equation machinery (functors, algebras, initial algebras, colimits)
2. **Lecture III** — cartesian-closed structure (Exercise 3.23)
3. **Domain constructors** — functorial `×` / `+` / `→`
4. **Lecture VII** — power-domain monad (Exercises 7.19–7.20)
5. **Exercises 6.21–6.23** — `GExpr` syntax and concrete endofunctors

There is no broad category-theory library and no Mathlib `CategoryTheory` import; it is Scott's
minimal categorical vocabulary, implemented choice-free for the flagship VI results.
