# Analogy: Mathlib shapes for gluing the tautological quotient sheaf + representability of the Grassmannian Quot functor

## Mode
api-alignment

## Slug
grquot-infra

## Iteration
049

## Question
For the new file `AlgebraicJacobian/Picard/GrassmannianQuot.lean` (5 decls from
`Picard_GrassmannianQuot.tex`): (1) Mathlib idiom to glue a rank-`d` locally-free
`SheafOfModules`/`Scheme.Modules` from per-chart free sheaves + a `GL_d` cocycle,
and to glue the tautological surjection `u : O^r ↠ U`; (2) Mathlib idiom for "scheme
`X` represents the functor of points `Schemeᵒᵖ ⥤ Type`" and the encoding of the
rank-`d`-quotients functor.

## Project artifact(s)
- `AlgebraicJacobian/Picard/GrassmannianCells.lean:1141` — `theGlueData : Scheme.GlueData`; `:1157` `scheme d r := (theGlueData d r).glued`.
- `blueprint/.../Picard_GrassmannianQuot.tex` — `chartQuotientMap`, `universalQuotient`, `tautologicalQuotient`, `functor`, `represents`.

## Decisions identified

### Decision: where do `Scheme.Modules` and the trivial bundles `O^r`, `O^d` live
- **Mathlib idiom**: `AlgebraicGeometry.Scheme.Modules X := SheafOfModules.{u} X.ringCatSheaf`
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:37`). Structure sheaf `O_X =
  SheafOfModules.unit R` (`Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:160`);
  free rank-`n` bundle `O_X^n = SheafOfModules.free (Fin n)` (`…/Sheaf/Free.lean:40`,
  `free I := ∐ (fun _:I => unit R)`). `SheafOfModules` is Abelian
  (`…/Sheaf/Abelian.lean`), so `Epi q` is available for "surjective".
- **Project's path**: use `SheafOfModules.free (Fin r)` / `(Fin d)` in `(chart).Modules`
  resp. `(scheme d r).Modules`; surjectivity = `Epi`.
- **Gap**: identical.
- **Verdict**: PROCEED.

### Decision: gluing a SheafOfModules from chart sheaves + GL_d transition cocycle
- **Mathlib idiom**: there is NO turn-key SheafOfModules/`Scheme.Modules` gluing from an
  open cover + cocycle. Closest:
  - Generic stack/descent: `CategoryTheory/Sites/Descent/DescentData.lean`
    (`F.DescentData f`, `:57`), `…/IsStack.lean` (`class IsStack`, `:49`,
    `isEquivalence_toDescentData`). Abstract pseudofunctor descent
    `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. **NOT instantiated for `Scheme.Modules`** — no
    `IsStack` instance for the modules-pseudofunctor anywhere in Mathlib (`grep IsStack`
    outside `Sites/Descent` = ∅). Using it would require building the modules
    pseudofunctor + proving Zariski effective descent for modules. Very heavy.
  - `AlgebraicGeometry.Scheme.GlueData` (`Mathlib/CategoryTheory/GlueData.lean` +
    AG instance) is the SCHEME-level gluing the project already used; it has no
    module-gluing companion.
  - Primitives that DO exist: `SheafOfModules.free`, `unit`, `Quasicoherent`
    (`QuasicoherentData`, `IsQuasicoherent`, `IsFinitePresentation` —
    `…/Sheaf/Quasicoherent.lean`), `pullback`/`pushforward` + adjunction
    (`…/Sheaf/PullbackContinuous.lean:53`), `pullback` of free is free
    (`…/Sheaf/PullbackFree.lean`, `mapFree` `Free.lean:186`).
- **Project's path**: build `universalQuotient : (scheme d r).Modules` by gluing the
  per-chart free sheaves `O_{U^I}^d` along `g_{I,J}=(X^I_J)⁻¹`.
- **Gap**: divergent — no idiom to align to; genuine gap.
- **Cost**: project must build a module-descent/gluing primitive over its
  `Scheme.GlueData` (or specialize the abstract `Sites/Descent` stack API). This is an
  INFRA BUILD, not a one-shot signature.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: predicate "locally free of rank d" for a sheaf of modules
- **Mathlib idiom**: NONE. `grep -r LocallyFree/IsLocallyFree Mathlib = ∅`. Mathlib has
  `Module.Free` (algebraic), `QuasicoherentData`/`IsQuasicoherent`/`IsFinitePresentation`
  (local presentation predicates), and `free` (globally free sheaf), but NO
  "locally free of rank `d`" / vector-bundle-of-rank-`d` predicate for
  `SheafOfModules`/`Scheme.Modules`. (`VectorBundle` exists only in
  differential-geometry `Mathlib/Geometry`/`Topology`, not for module sheaves.)
- **Project's path**: needs a predicate to state `U` is rank-`d` loc. free and to
  define the functor of points.
- **Gap**: divergent — genuine gap.
- **Cost**: project must define e.g.
  `IsLocallyFreeOfRank (M : X.Modules) (d : ℕ) : Prop` (local existence of a cover with
  `M.over (U i) ≅ free (Fin d)`), reusing `QuasicoherentData`'s "cover + local iso"
  shape so it composes with Mathlib's local-presentation API.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: gluing the sheaf morphism u : O^r ↠ U from local u^I
- **Mathlib idiom**: same as the object-gluing decision — no API. A morphism of glued
  sheaves is the morphism part of the same descent datum; once the module-gluing
  primitive exists it should also produce glued morphisms (descent of `Hom`).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (rides on the module-gluing primitive).

### Decision: action of a scheme morphism on the functor of points (φ^* F, φ^* u)
- **Mathlib idiom**: `AlgebraicGeometry.Scheme.Modules.pullback (f : X ⟶ Y) :
  Y.Modules ⥤ X.Modules` EXISTS (`…/Modules/Sheaf.lean:167`) with `pullbackId` (`:199`),
  `pullbackComp` (`:219`), `pullbackCongr` (`:235`) — the pseudofunctor coherences needed
  for functoriality of the functor of points and naturality of `represents`. Pullback of
  `free` is `free` (`PullbackFree.lean` / `mapFree`).
- **Gap**: identical — `φ^*` is exactly `Scheme.Modules.pullback φ`.
- **Verdict**: PROCEED (primitive exists).

### Decision: target shape for "scheme represents functor of points"
- **Mathlib idiom**: `CategoryTheory.Functor.RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C)`
  (`Mathlib/CategoryTheory/Yoneda.lean:285`) is the data form (a `homEquiv`
  `(X ⟶ Y) ≃ F.obj (op X)` natural in `X`); `Functor.IsRepresentable` (`:519`) is the
  Prop form; `IsRepresentable.mk'` from `yoneda.obj X ≅ F` (`:528`). AG uses exactly this:
  `AlgebraicGeometry/Sites/Representability.lean:187` `representableBy :
  F.1.RepresentableBy (glueData hf).glued`, `:202` `isRepresentable : F.1.IsRepresentable`.
- **Project's path**: `represents : (functor d r).RepresentableBy (scheme d r)`
  (return the `homEquiv` carrying `φ ↦ ⟨φ^*U, φ^*u⟩`).
- **Gap**: identical.
- **Verdict**: PROCEED (`RepresentableBy` is the canonical target).

### Decision: encoding the "rank-d quotients of O^r up to iso" functor
- **Mathlib idiom**: AG functors of points are typically `Schemeᵒᵖ ⥤ Type u` or
  `Sheaf Scheme.zariskiTopology (Type u)` (`Sites/Representability.lean` uses the sheaf
  form). No bundled "quotient sheaf up to iso" type exists; build it as a structure +
  setoid. `Sites/Representability.lean` (`Scheme.LocalRepresentability.isRepresentable`,
  Stacks 01JJ) proves a locally-representable Zariski sheaf is representable BY GLUING the
  representing scheme — related but engineered to *construct* the scheme, whereas
  `Grassmannian.scheme` is already built; usable as inspiration, not a drop-in.
- **Project's path**: a structure `RankQuotient r d T := {F : T.Modules, q : free (Fin r) ⟶ F,
  Epi q, IsLocallyFreeOfRank F d}`, quotient by the iso-relation (`f : F ≅ F'`, `f∘q=q'`;
  equivalently `ker q = ker q'`), giving `functor d r : Schemeᵒᵖ ⥤ Type _`.
- **Gap**: divergent-but-expected — structure+setoid is the normal Lean encoding; no
  Mathlib type to align to.
- **Cost**: depends on the `IsLocallyFreeOfRank` predicate (above). Map on morphisms via
  `Scheme.Modules.pullback`.
- **Verdict**: PROCEED (encoding) but blocked on the loc-free predicate gap.

## Recommendation
Two of the five blueprint decls (`universalQuotient`, `tautologicalQuotient`) rest on a
Mathlib-ABSENT primitive: gluing a `Scheme.Modules`/`SheafOfModules` (and a morphism of
them) from per-chart data + a `GL_d` cocycle over a `Scheme.GlueData`. A third
(`functor`) and the loc-free condition in it rest on an ABSENT `IsLocallyFreeOfRank`
predicate. Everything else aligns to existing Mathlib: `Scheme.Modules`, `free`/`unit`,
`Epi`, `Scheme.Modules.pullback` (+coherences), and `Functor.RepresentableBy` /
`IsRepresentable` as the representability target. **Therefore iter-050 should NOT scaffold
`universalQuotient`/`tautologicalQuotient`/`functor` signatures directly — it needs an
infra-build step first**, providing (a) a project-local module-gluing primitive over
`Scheme.GlueData` (glue objects + Hom from cover + cocycle), and (b) an
`IsLocallyFreeOfRank` predicate (modeled on `QuasicoherentData`'s cover+local-iso shape).
`chartQuotientMap` and `represents` (signature) can be scaffolded immediately since their
primitives all exist.
