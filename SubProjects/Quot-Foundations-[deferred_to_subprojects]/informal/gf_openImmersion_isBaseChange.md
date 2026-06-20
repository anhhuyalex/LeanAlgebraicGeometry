# RESOLVED (iter-056): flat base-change along an open immersion of affines (generic flatness)

## STATUS UPDATE (iter-056) — the base change is NO LONGER missing; it is BUILT.

The ingredient described below as "absent from Mathlib" turned out to be **fully constructible
from current Mathlib**, and is now built axiom-clean in `FlatteningStratification.lean`:

- `gf_flat_of_isEpi` — flat descent along a ring epimorphism `A → R`: from `Algebra.IsEpi A R`
  (`Mathlib.Algebra.Algebra.Epi`) the action map `R ⊗[A] M → M` is `TensorProduct.lid'` (an iso),
  giving `IsBaseChange R (id : M →ₗ[A] M)` via `IsBaseChange.of_equiv`; `Module.Flat.isBaseChange`
  finishes.
- `gf_isEpi_restrict_of_affine_le` — for affine opens `U ≤ V`, the restriction `Γ(S,V) → Γ(S,U)`
  is `Algebra.IsEpi`: `Spec.map (restriction) ≫ hV.fromSpec = hU.fromSpec`
  (`IsAffineOpen.map_fromSpec`) with `hU.fromSpec` a (open-immersion) **mono**, so `Spec.map ρ`
  is mono; the fully-faithful `Scheme.Spec` reflects it (`mono_of_mono_map`) to `Mono ρ.op`, i.e.
  `Epi ρ`; `CommRingCat.epi_iff_epi` gives `Algebra.IsEpi`.

`genericFlatness` now wires these in: the per-piece flatness `Module.Flat Γ(S,U) Γ(F, D g)`
DESCENDS from `Module.Flat Γ(S,V) Γ(F, D g)` along the epi `Γ(S,V) → Γ(S,U)`. The sole remaining
`sorry` is that residual `Module.Flat Γ(S,V) Γ(F, D g)` — **pure in-Mathlib localization algebra**,
not a base change: per-patch freeness is retained in `hfree`, transported via
`Module.free_of_isLocalizedModule` (`Mathlib.RingTheory.LocalProperties.Projective`) + the
source-localization B1 `gf_flat_localizedModule_sameBase`. No Mathlib gap remains.

The historical analysis below is kept for context only.

## Where it is needed

`AlgebraicGeometry.genericFlatness` (`AlgebraicJacobian/Picard/FlatteningStratification.lean`).
After iter-055 the proof is reduced to a **single** `sorry`: the per-piece flatness

```
Module.Flat Γ(S, U) Γ(F, X.basicOpen g)
```

where `U ≤ V = D(f) ⊆ U₀` is an arbitrary **affine** open of the base `S`, `g ∈ Γ(X, W)` cuts out
a basic open `D(g) ⊆ W ∩ W_i` matched (via `gf_crossChart_spanning_cover` / `gf_crossChart_basicOpen_eq`)
by a patch element `ḡ ∈ Γ(X, W_i)` with `D(g) = D(ḡ)`.

Everything **around** this step is now built and axiom-clean in the file:

- `gf_section_span_flat_descent` — span-descent core (`Module.flat_of_isLocalized_span`, base
  `R = Γ(S,U)`, source `Γ(X,W)`, pieces the basic-open section modules). Already applied to reduce
  the `(U,W)` goal to the per-piece flatness above.
- `gf_flat_of_isBaseChange_id` — **one-line consumer** of the missing ingredient: given
  `IsBaseChange Γ(S,U) (LinearMap.id : M →ₗ[Γ(S,V)] M)` and `Module.Flat Γ(S,V) M`, concludes
  `Module.Flat Γ(S,U) M` (via `Module.Flat.isBaseChange`).
- `gf_flat_localizedModule_sameBase` (B1), `gf_section_localization_twoleg` (B2.2),
  `gf_base_localization_comparison` (B2.3), `gf_patch_free_imp_flat`, `genericFlatnessAlgebraic`
  — the patch-freeness → `A_f`-flatness chain.

## The route the per-piece flatness should take

1. `Γ(F, D g) = Γ(F, D ḡ)` (same open, `gf_crossChart_basicOpen_eq` gives `D g = D ḡ`).
2. `Γ(F, D ḡ) = (M_i)_ḡ = LocalizedModule (powers ḡ) (Γ(F, W_i))` (B2.2 leg 2).
3. `(M_i)_f` is free, hence **flat over `A_f = Γ(S, V)`** (per-patch freeness from
   `genericFlatnessAlgebraic` on patch `i`, transported from the chosen `f₀ i` to the product
   `f = ∏ f₀ j` — localization of a free module is free).
4. Source-localise at `powers ḡ`, keeping `A_f`-flatness (`gf_flat_localizedModule_sameBase`),
   noting `f` is already invertible on `D ḡ ⊆ p⁻¹(U) ⊆ p⁻¹(V)`, so
   `(M_i)_ḡ = ((M_i)_f)_ḡ`. Hence `Module.Flat Γ(S,V) Γ(F, D g)`.
5. **DESCEND the base `Γ(S,V) → Γ(S,U)` along the open immersion `U ↪ V`** via
   `gf_flat_of_isBaseChange_id`.

Step 5 needs its hypothesis, which is the missing ingredient.

## Precise missing statement

For affine opens `U ≤ V` of a scheme `S` and an `Γ(S,U)`-module `M` (also a `Γ(S,V)`-module
through the restriction tower `Γ(S,V) → Γ(S,U) → M`):

```
IsBaseChange Γ(S,U) (LinearMap.id : M →ₗ[Γ(S,V)] M)
```

Equivalently, the canonical map `Γ(S,U) ⊗[Γ(S,V)] M → M` is an isomorphism. This holds because
`U ↪ V` is an **open immersion**, hence a **monomorphism of schemes**, so `Γ(S,V) → Γ(S,U)` is a
ring **epimorphism** (`Γ(S,U) ⊗[Γ(S,V)] Γ(S,U) ≅ Γ(S,U)`); for any `Γ(S,U)`-module `M` this forces
`Γ(S,U) ⊗[Γ(S,V)] M ≅ M`.

### Cleanest factoring for a `mathlib-build` lane

(a) **Ring-level**: `Spec (Γ(S,U)) ≅ U ↪ V ≅ Spec (Γ(S,V))` is an open immersion ⟹
    `Γ(S,V) → Γ(S,U)` is an epimorphism of commutative rings, i.e.
    `Function.Bijective (mul' : Γ(S,U) ⊗[Γ(S,V)] Γ(S,U) → Γ(S,U))`.
    (Mathlib has `IsOpenImmersion` and monomorphism API; the "open immersion of affines ⟹ section
    ring map is epi" packaging appears absent.)

(b) **Module-level (pure algebra)**: for a ring epimorphism `A → R` (`R ⊗[A] R ≅ R` via `mul'`) and
    an `R`-module `M`, the action map `R ⊗[A] M → M` is an isomorphism; therefore
    `IsBaseChange R (LinearMap.id : M →ₗ[A] M)`. Equivalent to: the restriction functor
    `R-Mod → A-Mod` is fully faithful. This pure-algebra flat-epimorphism fact is the heart;
    `Module.Flat.isBaseChange` then finishes (already wired through `gf_flat_of_isBaseChange_id`).

Why the existing localization API does **not** suffice: `B2.3` (`gf_base_localization_comparison`)
only proves `Γ(S,U)` *flat* over `Γ(S,V)`, and an arbitrary affine `U ≤ V` need **not** be a
*basic* open, so `Γ(S,U)` need not be a *localization* of `Γ(S,V)` — `Module.Flat.of_isLocalizedModule`
/ `Module.flat_iff_of_isLocalization` do not apply. The flat-**epimorphism** descent is strictly
more general and is the genuine gap.
