# Analogy: restriction-composition iso for module sheaves (`M.restrict (j ≫ f) ≅ (M.restrict f).restrict j`)

## Mode
api-alignment

## Slug
restrictcomp039

## Iteration
039

## Question
Does Mathlib already provide the canonical iso `M.restrict (j ≫ f) ≅ (M.restrict f).restrict j`
for `M : Scheme.Modules X` and open-immersion restriction maps, or must it be built project-side?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:425` — `restrictIsoUnitOfLE`: manually
  rebuilds the SAME composite via `restrictFunctorIsoPullback`+`pullbackCongr`+`pullbackComp`
  instead of the one-liner `restrictFunctorComp`.
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:419-420` — doc comment already NAMES
  `restrictFunctorComp`/`restrictFunctorCongr` as the conceptual route (so the Mathlib decl
  was known to exist at some point).
- `AlgebraicJacobian/Picard/TensorObjInverse.lean:183` — `trivialisation_restrict_compat`
  (consumer; the 5 restriction-naturality squares feed it).

## Decisions identified

### Decision: reuse Mathlib's restriction-composition NatIso vs. build a project-side iso

- **Mathlib idiom**: `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`
  (module `Mathlib.AlgebraicGeometry.Modules.Sheaf`). Signature:
  ```
  restrictFunctorComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f
  ```
  This is the functoriality NatIso of the restriction pseudofunctor. Mathlib states it once
  at the functor level; applying `.app M` specialises to any object. Companions exist:
  `restrictFunctorId : restrictFunctor (𝟙 X) ≅ 𝟭`, and pullback-level
  `pullbackComp`/`pullbackCongr`/`pullbackId`, plus `restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f`.
  Axiom-clean (`propext, Classical.choice, Quot.sound`). Built from
  `SheafOfModules.pushforwardComp`/`pushforwardCongr`/`pushforwardNatIso`.

- **The target is a LITERAL `.app`**: `Scheme.Modules.restrict` is `@[reducible]`
  (`M.restrict f := (restrictFunctor f).obj M`), so with `j : X ⟶ Y`, `f : Y ⟶ Z`, `M : Z.Modules`:
  ```
  (Scheme.Modules.restrictFunctorComp j f).app M
    : M.restrict (j ≫ f) ≅ (M.restrict f).restrict j
  ```
  typechecks verbatim against the directive's stated type (verified via `lean_run_code`,
  noncomputable example, no `eqToHom`/coercion needed). Argument order: FIRST arg = OUTER/later
  restriction (`j`), SECOND arg = INNER/earlier (`f`).

- **The 5 naturality squares come FREE**: it is a genuine `NatIso`, so
  `(restrictFunctorComp j f).hom.naturality φ` / `.inv.naturality φ` give the commuting squares
  against any `φ : M ⟶ N`, and `.hom_inv_id`/`.inv_hom_id`/`.app` `Iso` lemmas are all available.
  (Naturality square verified typechecking via `lean_run_code`.) No auto-`@[simps]` `_hom_app`
  lemma exists (it's a plain `def`); unfold via `.hom.naturality` and `NatTrans`/`Functor.comp`
  lemmas, NOT a `restrictFunctorComp_hom_app` simp.

- **Project's current path**: rebuilds the composite manually inside `restrictIsoUnitOfLE`
  via `restrictFunctorIsoPullback ≪≫ pullbackCongr ≪≫ pullbackComp.symm ≪≫ pullback.mapIso`.
  Works and is axiom-clean, but is a hand-rolled instance of exactly what `restrictFunctorComp`
  packages — a parallel API for the same iso.

- **Gap**: divergent-with-cost (the directive's plan to BUILD a new `restrict_comp_iso` would be
  a third copy). For `restrictIsoUnitOfLE` itself: divergent-equivalent (already shipped, works).

- **Cost of divergence**: building a fresh `restrict_comp_iso` project-side instead of reusing
  `restrictFunctorComp` would (a) duplicate an axiom-clean Mathlib decl, (b) force every
  downstream naturality square to re-prove what `.hom.naturality` gives for free, (c) need its own
  `Id`/coherence companions that Mathlib already ships, (d) risk a defeq mismatch against the
  `@[reducible] restrict` that the Mathlib decl is built to respect.

- **Verdict**: ALIGN_WITH_MATHLIB.

## Recommendation
Do **not** build a project-side `restrict_comp_iso`. Use
`(Scheme.Modules.restrictFunctorComp j f).app M : M.restrict (j ≫ f) ≅ (M.restrict f).restrict j`
directly (first arg = outer map, second = inner). Derive the 5 restriction-naturality squares
feeding `trivialisation_restrict_compat` from `(restrictFunctorComp j f).hom.naturality`/
`.inv.naturality` plus `restrictFunctorIsoPullback` for the pullback-side legs. The directive's
"ABSENT from Mathlib" premise is a FALSE NEGATIVE: the prover lane grepped only
`Algebra/Category/ModuleCat/Sheaf/`, but the decl lives in
`Mathlib.AlgebraicGeometry.Modules.Sheaf` (namespace `AlgebraicGeometry.Scheme.Modules`);
and `loogle "SheafOfModules.restrict (?g ≫ ?f)"` missed it because it is stated at the FUNCTOR
level (`restrictFunctor (f ≫ g) ≅ …`) under `Scheme.Modules`, not as an object-level
`SheafOfModules.restrict (g ≫ f)`. Re-search idiom for future: `#check
@AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` or loogle `Scheme.Modules.restrictFunctor (?f ≫ ?g)`.
Secondary cleanup (low priority): `restrictIsoUnitOfLE` could be simplified to route through
`restrictFunctorComp` instead of the manual pullback chain — not required, but removes a parallel API.
