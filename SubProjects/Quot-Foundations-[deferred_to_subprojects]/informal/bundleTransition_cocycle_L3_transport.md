# L3 transport for `bundleTransition_cocycle` (C2)

**Target.** `AlgebraicGeometry.Grassmannian.bundleTransition_cocycle` (GrassmannianQuot.lean,
the `_hC2` form for `Scheme.Modules.glue` at `theGlueData d r` / `bundleTransitionData`).

**Status (iter-061).** L1 + L2 are CLOSED axiom-clean in the file:
- L2 `matrixToFreeIso_mul` — composing two `matrixToFreeIso` forward maps = `matrixEnd (B·A)`.
- L1 `bundleTransition_cocycle_matrix` — the Cramer-inverse cocycle
  `(X^J_K)⁻¹ (X^I_J)⁻¹ = (X^I_K)⁻¹` over the triple-overlap ring
  `S_I = Localization.Away (minorDet I J * minorDet I K)`, stated with the public ring homs
  `cocycleΘIJ`, `awayInclLeft`, `awayInclRight`. Proved by taking the `I`-minor of the
  ported `cocycle_imageMatrix_eq'`.

C2 has `apply Iso.ext` + a precise roadmap comment + `sorry`. The hom-level goal after
`Iso.ext` is the composite of three `pullbackBaseChangeTransport`s, with each
`bundleTransition I J` unfolded to `pullbackFreeIso (f I J) ≪≫ matrixToFreeIso (M_IJ) ≪≫
(pullbackFreeIso (t I J ≫ f J I)).symm`.

## The missing ingredient (net-new infrastructure)

### (a) matrixEnd-under-pullback naturality
For `p : T ⟶ S` (`T S : Scheme.{0}`) and `M : Matrix (Fin d) (Fin d) Γ(S,⊤)`:
```
(Scheme.Modules.pullback p).map (matrixEnd M)
  = (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
    ≫ matrixEnd ((CommRingCat.Hom.hom p.appTop).mapMatrix M)
    ≫ (Scheme.Modules.pullbackFreeIso p (Fin d)).inv
```
Here `p.appTop : Γ(S,⊤) ⟶ Γ(T,⊤)` is the comorphism on global sections
(`Scheme.Hom.appTop`). Proof route: `matrixEnd M = isoCoproduct.symm.hom ≫
biproduct.matrix (scalarEnd ∘ M) ≫ isoCoproduct.hom`; `Scheme.Modules.pullback p` is a left
adjoint, hence additive and biproduct-preserving, so it commutes with `biproduct.matrix` up
to the coproduct comparison; the crux is the single-entry statement
`(pullback p).map (scalarEnd a)` conjugated by the unit-pullback comparison
(`pullbackObjUnitToUnit`, the `pullbackFreeIso` at a one-element index) equals
`scalarEnd (p.appTop a)`. That is the genuine new lemma — `scalarEnd` naturality under
pullback — and lives squarely in "the diamond" (use term-mode, keep `pullbackComp`/
`pullbackId` opaque).

### (b) Base-change bridge to L1's ring homs
The base-change maps `Γ(U^I_J,⊤) ⟶ Γ(V_IJK,⊤)` induced by the projections / triple
transition `t'` must be identified — via `ΓSpecIso` naturality on the affine charts and the
way `theGlueData` / `chartTransition` are assembled from `transitionMap` — with the ring homs
`cocycleΘIJ` / `awayInclLeft` / `awayInclRight` over which L1 is stated. Then L1 applies to
the base-changed matrices produced by (a).

## Assembly once (a)+(b) land
Each `pullbackBaseChangeTransport` of a `bundleTransition`, after the `pullbackComp`
reassociations and the three `glueData_bridge_*`/`pullbackCongr` casts cancel the
`pullbackFreeIso` comparisons (via (a)), becomes `matrixEnd` of a base-changed Cramer inverse
on `O_{V_IJK}^d`. L2 composes the first two transports to `matrixEnd ((X^J_K)⁻¹(X^I_J)⁻¹)`,
L1 rewrites the argument to `(X^I_K)⁻¹` (after (b)), matching the third transport.

## Note on `cocycle_imageMatrix_eq` visibility
L1's proof needed `cocycle_imageMatrix_eq` and five matrix helpers
(`mul_submatrix_col`, `map_map_eq_of_comp`, `isUnit_algebraMap_away_left`,
`inv_mul_inv_mul_cancel`, `imageMatrix_map_eq`, `map_nonsing_inv`), all of which are
`private` in `GrassmannianCells.lean`. They were ported verbatim into GrassmannianQuot.lean
as `private … '`-suffixed copies. If the Cells owner makes these `theorem`/non-private, the
ports can be deleted and L1 simplified.
