# Analogy: strong-monoidality of the sheaf-of-modules pullback (inverse image)

## Mode
cross-domain-inspiration

## Slug
pullback-monoidal

## Iteration
240

## Structural problem (abstracted)
A left adjoint `L ⊣ R` between sheaf/presheaf-of-modules categories (here
`L = f^* = (pushforward f).leftAdjoint`) has no sectionwise/stalkwise value
formula, yet we must show the two canonical oplax-monoidal comparison maps
`L(A⊗B) → LA⊗LB` and `L𝟙 → 𝟙` are isomorphisms (i.e. `L` is **strong
monoidal**). The ambient categories carry a "restrict to an open / take a
local chart" family of conservative functors, and the comparison maps are
known-iso after restricting to suitable local charts (open immersions where
the comparison functor is `Final`).

## Failed approaches (from directive)
- Sectionwise `extendScalars` tensorator: pullback is an abstract left adjoint,
  never definitionally `extendScalars`, so there is no sectionwise object to
  attach the tensorator to.
- `Adjunction.leftAdjointOplaxMonoidal` for the free comparison map: **this name
  does not exist in Mathlib** (see correction below); the doctrinal direction
  Mathlib ships is the opposite (`rightAdjointLaxMonoidal`).
- `pullbackObjUnitToUnit` iso for general `f`: only iso under `F.Final`
  (open immersions), false for general `f`.

## Analogues found (ranked by porting cost)

### Analogue: `CategoryTheory.Functor.CoreMonoidal.ofOplaxMonoidal` (`Mathlib.CategoryTheory.Monoidal.Functor`)
- **Domain**: category theory (monoidal functors).
- **Same structural problem there**: given `F.OplaxMonoidal` and the two
  hypotheses `[IsIso (OplaxMonoidal.η F)]` and `[∀ X Y, IsIso (OplaxMonoidal.δ F X Y)]`,
  it manufactures `F.CoreMonoidal` (equiv. `F.Monoidal`, strong monoidal). The
  companions `ofOplaxMonoidal_εIso` / `ofOplaxMonoidal_μIso` give the **inverse**
  comparison isos as `(asIso η).symm` and `(asIso (δ X Y)).symm`. This is
  EXACTLY the packaged "oplax ⇒ strong under condition X" the directive asked
  for (Q2 = YES).
- **Technique**: the converter is purely formal — it does not prove the IsIso
  facts, it consumes them as typeclass hypotheses and repackages. So the entire
  mathematical content is shoved into proving `IsIso η` (unit comparison) and
  `IsIso (δ X Y)` (tensor comparison) — the two project obligations.
- **Mapping to project**: target functor is `PresheafOfModules.pullback φ`
  (where `MonoidalCategory (PresheafOfModules …)` DOES exist —
  `PresheafOfModules.monoidalCategory` in `…Presheaf.Monoidal`, over a
  `CommRingCat`-valued ring presheaf). Sheaf-level transport then rides the
  project's existing `sheafifyTensorUnitIso` brick + `Sheaf.monoidalCategory`.
- **Porting cost**: medium. The packaging is one line; the cost is entirely in
  the two `IsIso` proofs (next analogue) and in first producing the
  `OplaxMonoidal` instance on `pullback` (see correction — not free).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal` + the proven `IsLocallyTrivial.pullback` chart-chase (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` + project `LineBundlePullback.lean:156`)
- **Domain**: algebraic geometry / sheaves on sites (the project's own shelf).
- **Same structural problem there**: prove a pullback comparison map of sheaves
  of modules is iso by reduction to local charts on which the comparison functor
  is `Final`. Mathlib already supplies the UNIT half:
  `pullbackObjUnitToUnit φ : f^*(unit S) ⟶ unit R` is an `IsIso` **instance**
  whenever `F` is `Final`. The project has already assembled the full
  open-immersion chart-chase `i1 ≪≫ … ≪≫ i7` in `IsLocallyTrivial.pullback`
  (axiom-clean), using `restrictFunctorIsoPullback`, `pullbackComp`,
  `pullbackCongr`, and `asIso (pullbackObjUnitToUnit g)`.
- **Technique**: pick an affine chart `V`, factor `V.ι ≫ f = g ≫ U.ι` with
  `g = f.resLE U V`, get `(Opens.map g.base).Final` via
  `final_of_representablyFlat`, then transport the global map to the local
  `pullbackObjUnitToUnit g` through the naturality of the `pullbackComp` /
  `restrictFunctorIsoPullback` cluster; finish with the project's
  `isIso_of_isIso_restrict` (iso-on-every-chart ⇒ global iso).
- **Mapping to project**: the UNIT comparison `IsIso η` (Q's map 2) is reachable
  **today** — it is literally `pullbackObjUnitToUnit` glued over a cover, the
  same `i7` already used. The TENSOR comparison `IsIso (δ X Y)` (map 1) is the
  same chart-chase ONE LEVEL UP, but needs a `pullbackObjTensorToTensor`
  analogue of `pullbackObjUnitToUnit` that **Mathlib does not have** (Q1 = NO).
- **Porting cost**: low for the unit half (mirror `i1…i7`); the tensor half is
  the genuine gap.
- **Verdict**: ANALOGUE_FOUND (unit half) / PARTIAL_ANALOGUE (tensor half).

### Analogue: `CategoryTheory.Sheaf.instMonoidalFunctorOppositePresheafToSheaf` / `CategoryTheory.Sheaf.monoidalCategory` (`Mathlib.CategoryTheory.Sites.Monoidal`)
- **Domain**: topos theory / sites.
- **Same structural problem there**: under `[J.W.IsMonoidal]`, sheafification
  `presheafToSheaf J A` is `.Monoidal` (strong), and `Sheaf J A` itself carries
  a `MonoidalCategory`. This is the abstract engine behind "an inverse-image of
  sheaves commutes with ⊗": realize `f^*` on sheaves as
  `sheafify ∘ (presheaf-pullback) ∘ forget` and compose strong-monoidal pieces.
- **Technique**: strong-monoidality of sheafification is obtained from the
  monoidality of the localizer class `J.W` (`IsMonoidal`), NOT sectionwise.
- **Mapping to project**: `Sheaf J A` here is over a FIXED monoidal `A`, so it is
  **not** `SheafOfModules R` (module structures vary over the sheaf of rings) —
  the directive's "no `MonoidalCategory (SheafOfModules …)`" is correct as
  stated. But the `J.W.IsMonoidal` route IS the right shape for the project's
  sheafification-monoidal brick (`sheafifyTensorUnitIso`); the gate is
  establishing `J.W.IsMonoidal` for the relevant topology (cf. the absent
  `Sites.Point.IsMonoidalW` already logged in project memory).
- **Porting cost**: high. Requires the missing module-level monoidal sheaf
  category plus `J.W.IsMonoidal`.
- **Verdict**: PARTIAL_ANALOGUE.

## Correction to the directive's premise
`Adjunction.leftAdjointOplaxMonoidal` **does not exist in Mathlib** (loogle +
leansearch confirm: no such declaration). The only monoidal-adjunction transfer
shipped is `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`
(`Mathlib.CategoryTheory.Monoidal.Functor`): `F ⊣ G` with `[F.OplaxMonoidal]`
produces `G.LaxMonoidal` — i.e. **left-oplax ⇒ right-lax**, the opposite
direction from what the project needs. Consequence: the oplax comparison maps
`δ, η` on `pullback` are **NOT free**. To even state `ofOplaxMonoidal` you must
first produce `(PresheafOfModules.pullback φ).OplaxMonoidal` by hand — either as
the mate of the lax structure on `pushforward`, or from the concrete
extension-of-scalars description of the presheaf pullback. This is a real cost
the directive under-counted.

## Top suggestion
Two-phase. **Phase 1 (cheap, do first):** prove the UNIT comparison `f^*𝟙 ≅ 𝟙`
by mirroring the already-proven `IsLocallyTrivial.pullback` chart-chase
(`LineBundlePullback.lean:156-193`) — it is the same `i1…i7` glue terminating in
`asIso (SheafOfModules.pullbackObjUnitToUnit g)`, whose iso-ness over each chart
is the Mathlib instance `instIsIsoPullbackObjUnitToUnitOfFinal`; globalize with
the project's `isIso_of_isIso_restrict`. **Phase 2 (the real gap):** the TENSOR
comparison has NO Mathlib tensorator on `pullback` — `PresheafOfModules.pullback`
ships only `pullbackComp` / `pullbackId` / `pullback_assoc` (composition
coherence, no `μ`). The project must build a `pullbackObjTensorToTensor` analogue
of `pullbackObjUnitToUnit` (NEEDS_MATHLIB_GAP_FILL) and prove it iso by the same
finality chart-chase, then feed both `IsIso` facts into
`Functor.CoreMonoidal.ofOplaxMonoidal` for the packaged strong-monoidal upgrade
(with `μIso`/`εIso` delivering the inverse comparison isos). The directive's own
"build the naturality cluster from scratch" diagnosis is correct for Phase 2.
