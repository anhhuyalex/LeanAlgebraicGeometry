# Analogy: stateable signature for `baseChangeGammaPullbackEquiv` (FBC-B capstone)

## Mode
api-alignment

## Slug
fbcb-sig

## Iteration
081

## Question
Design an elaborating Lean signature for `AlgebraicGeometry.Modules.baseChangeGammaPullbackEquiv`
(blueprint `thm:fbcb_global_direct`): `Γ(X,F) ⊗_A B ≃ₗ[B] Γ(X',F')` with `A = groundRing X`,
`X' = X ×_{Spec A} Spec B`, `F' = (g')^* F`. The RHS `Γ(X',F')` is a module over `groundRing X'`,
NOT over `B` — find the idiom that makes `≃ₗ[B]` typecheck. (A `lean-scaffolder` crashed STATING it.)

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChangeGlobal.lean:241` — `baseChangeGammaEquiv`
  (`B ⊗_A Γ(X,F) ≃ₗ[B] eqLocus(B⊗leftRes, B⊗rightRes)`), the proof's starting point.
- `…FlatBaseChangeGlobal.lean:103/114` — `groundRing X := X.presheaf.obj (op ⊤)`;
  `gammaModA M U := (ModuleCat.restrictScalars (rhoU X U)).obj (M.val.obj (op U))`.
- `…FlatBaseChange.lean:2566/2606` — `affineBaseChange_pushforward_iso` /
  `flatBaseChange_pushforward_isIso` over an abstract `IsPullback g' f' f g`.

## Decisions identified

### Decision: how to express `B`-action on `Γ(X', F')` (no `groundRing X' = B`)
- **Mathlib/project idiom**: `groundRing X'` is genuinely NOT `B` (definitionally or as a
  carried iso). There IS a canonical *algebra map* `B → groundRing X'`, from the pullback
  projection `f' : X' ⟶ Spec B`: `f'.appTop.hom ∘ (Scheme.ΓSpecIso (.of B)).inv.hom`. View the
  RHS as a `B`-module by `ModuleCat.restrictScalars` ALONG THAT RING HOM — exactly how the
  project already builds `gammaModA` itself (restrictScalars along `rhoU X U`). The iso
  `groundRing X' ≅ B` is a *consequence* of the theorem at `F = O_X`, unavailable for stating it.
  Cite: `AlgebraicGeometry.Scheme.ΓSpecIso` (Mathlib `…/GammaSpecAdjunction.lean`),
  `AlgebraicGeometry.Scheme.Hom.appTop`, `ModuleCat.restrictScalars`.
- **Project's path**: restrictScalars-along-RingHom — matches `gammaModA`'s own construction.
- **Gap**: identical (project idiom). No `Algebra B (groundRing X')` instance needed —
  `restrictScalars` takes the raw `RingHom`, avoiding a non-canonical instance/diamond.
- **Verdict**: ALIGN_WITH_MATHLIB (use restrictScalars-along-RingHom; do NOT chase a fake
  `groundRing X' = B` equality).

### Decision: abstract pullback square vs. direct flat `A`-algebra `B`
- **Mathlib/project idiom**: `baseChangeGammaEquiv` (the proof's first step) tensors over
  `A = groundRing X` and takes `B` DIRECTLY as `[Algebra (groundRing X) B] [Module.Flat …]`.
  Its LHS `TensorProduct (groundRing X) B (gammaModA F ⊤)` is verbatim the capstone's LHS.
- **Abstract-square path's cost**: an `IsPullback g' f' f g` carries its tensor base at
  `groundRing S`, not `groundRing X`; `B = groundRing S'` is not canonically a
  `groundRing X`-algebra. To reuse `baseChangeGammaEquiv` you must additionally assume
  `S = Spec(groundRing X)`, `f = X.toSpecΓ`, `S' = Spec B` — three equation hypotheses that
  reproduce, less cleanly, the in-statement pullback construction.
- **Gap**: direct-`B` route = divergent-with-cost-AVOIDED; abstract route = divergent-with-cost.
- **Verdict**: ALIGN_WITH_MATHLIB — take `B` directly, build `X'`/`g'` in-statement via
  `pullback X.toSpecΓ (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))`.
  Cite: `AlgebraicGeometry.Scheme.toSpecΓ`, `AlgebraicGeometry.Spec.map`, `CommRingCat.ofHom`,
  `CategoryTheory.Limits.pullback` / `pullback.fst` / `pullback.snd`, `Scheme.Modules.pullback`.

## Recommendation
Mirror `baseChangeGammaEquiv`: parametrize over `(F : X.Modules) (B : Type u) [CommRing B]
[Algebra (groundRing X) B] [Module.Flat (groundRing X) B]`, construct the special pullback
`X' = X ×_{Spec A} Spec B` (over `f = X.toSpecΓ`, `S = Spec(groundRing X)`) inside the statement,
and view `Γ(X',F') = gammaModA ((pullback g').obj F) ⊤` as a `B`-module by
`ModuleCat.restrictScalars` along the named ring hom `B → groundRing X'`. Both decisions ALIGN
with existing idiom; no parallel API is introduced. Verified to elaborate (with the helper
`pullbackGroundRingAlg` factored out and a `sorry` body) — see the report for the exact header.
