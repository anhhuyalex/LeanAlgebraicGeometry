# Analogy: a `SheafOfModules` equivalence from a site equivalence with a *varying* structure ring sheaf

## Mode
api-alignment

## Slug
ana258-overeq

## Iteration
258

## Question
Does Mathlib already have a "sheaf-of-modules equivalence induced by a site equivalence +
ring-sheaf identification" primitive (so the project should mirror it rather than build a
parallel API), and what is the minimal shape + construction skeleton for
`SheafOfModules.overEquivalence X U : SheafOfModules (↑U).ringCatSheaf ≌ SheafOfModules (X.ringCatSheaf.over U)`?

## Project artifact(s)
- `AlgebraicJacobian/Picard/LineBundleCoherence.lean:203-206` — `chartOverIso` (the open `sorry`).
- `AlgebraicJacobian/Picard/TensorObjSubstrate/DualInverse.lean:291-323` — `dual_restrict_iso`
  / `sliceDualTransport` / `exists_tensorObj_inverse` consumer.
- `AlgebraicJacobian/Picard/TensorObjSubstrate/Vestigial.lean:689-721` — `overEquivInverseIsDenseSubsite`
  (project's already-built dense-subsite datum) + `overSliceSheafEquiv` (the **fixed-value-cat**,
  ring-invariant version that is INAPPLICABLE here).

## Decisions identified

### Decision 1: parallel API vs. mirror an existing Mathlib primitive

- **Mathlib idiom**: `SheafOfModules.pushforwardPushforwardEquivalence`. Cite:
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:305` (whole `section
  Equivalence`, L289–329). Signature (verbatim shape):
  ```
  variable {C} [Category C] {D} [Category D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (eqv : C ≌ D)
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    [Functor.IsContinuous eqv.functor J K] [Functor.IsContinuous eqv.inverse K J]
    (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat J K).obj R)
    (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat K J).obj S)
    (H₁ …) (H₂ …)
  def pushforwardPushforwardEquivalence : SheafOfModules R ≌ SheafOfModules S
  ```
  This is **exactly** "equivalence of module-sheaf categories from an equivalence of sites + an
  iso of the two structure ring sheaves" — `S` and `R` are DIFFERENT sheaves of rings (on `C` resp.
  `D`), reconciled by `φ`/`ψ`. It is the Joël-Riou primitive that `QuasicoherentData.bind` uses
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` ~L370). The underlying functor is
  `SheafOfModules.pushforward φ` (`PushforwardContinuous.lean:44`).
- **Project's current path**: `overSliceSheafEquiv` (`Vestigial.lean:715`) built via
  `Equivalence.sheafCongr` over `Functor.IsDenseSubsite` — but at a **fixed value category `A`**
  (`Sheaf … A`, not modules), so it CANNOT carry the varying base ring. Two prover sessions already
  confirmed it is inapplicable (`TensorObjSubstrate.lean:637-663`; `DualInverse.lean:262-272`).
- **Gap**: divergent-with-cost only if the project builds a *new* parallel equivalence by hand.
  Mathlib's `pushforwardPushforwardEquivalence` is the right tool and was simply not noticed.
- **Cost of divergence (if a hand-rolled equivalence is built)**: duplicate unit/counit/coherence
  proofs (~150+ LOC) that Mathlib already provides, plus a second incompatible "module-over-site"
  API that future quasi-coherent code can't consume.
- **Verdict**: ALIGN_WITH_MATHLIB — build via `pushforwardPushforwardEquivalence`
  (no shipped divergent code yet, so this is an adopt-the-idiom, not a refactor).

### Decision 2: full `Equivalence` vs. bare functor + two isos (minimal consumer shape)

- **Mathlib idiom**: the documented Mathlib TODO (`Mathlib/Topology/Sheaves/Over.lean:19-22`) targets
  the **full** equivalence. The underlying functor alone is `SheafOfModules.pushforward φ`
  (`PushforwardContinuous.lean:44`); the `restrict ↦ over` natural iso is a `pushforwardComp` +
  `pushforwardNatIso` composite — and Mathlib *already ships this exact recipe* in
  `Scheme.Modules.restrictFunctorAdjCounitIso` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:335-340`).
- **Project's current path**: directive proposes the full `Equivalence`.
- **Gap**: divergent-equivalent. The two consumers (`chartOverIso`, `sliceDualTransport`) need only
  `Φ.functor` applied to an iso `e`, plus two object isos (`restrict ↦ over`, `unit ↦ unit`). They
  do NOT use `Φ.inverse`/unit/counit. So a bare functor `restrictOverFunctor := pushforward φ`
  + the two isos is a strictly cheaper sufficient shape (skips `ψ`, `H₁`, `H₂`).
- **Verdict**: PROCEED (full equivalence is the canonical idiom and is only marginally more than the
  functor since continuity is free — see Decision 3 — but the functor-only `restrictOverIso` is a
  valid, documented fallback if `ψ`/`H₁`/`H₂` prove sticky).

### Decision 3: the continuity prerequisites (the apparent blocker) are ALREADY in the project

- **Mathlib idiom**: `pushforwardPushforwardEquivalence` needs `[IsContinuous eqv.functor J K]` AND
  `[IsContinuous eqv.inverse K J]`. Key chain:
  1. `Functor.IsDenseSubsite … ⇒ IsContinuous` is a `priority 900` instance
     (`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:548`).
  2. For an equivalence, `[e.inverse.IsDenseSubsite K J] ⇒ instance e.functor.IsDenseSubsite J K`
     **automatically** (`Mathlib/CategoryTheory/Sites/Equivalence.lean:106-108`).
- **Project's current path**: `overEquivInverseIsDenseSubsite`
  (`Vestigial.lean:689`) is exactly `(overEquivalence U).inverse.IsDenseSubsite (gt ↥U) ((gt X).over U)`
  = `e.inverse.IsDenseSubsite K J` for `e = overEquivalence U`. So BOTH continuity legs resolve by
  typeclass inference; the `Over.lean:19-22` TODO is *already discharged by the project for this case*.
- **Gap**: identical (the project unknowingly built precisely the hypothesis Mathlib's auto-instance
  consumes).
- **Verdict**: PROCEED — no work needed for continuity.

## Construction skeleton (confirmed primitives, file:line)

Set `e := TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U`
(`Topology/Sheaves/Over.lean:41`), `C = Over U` with `J = (Opens.grothendieckTopology X).over U`,
`D = Opens ↥U` with `K = Opens.grothendieckTopology ↥U`. Then
`SheafOfModules R ≌ SheafOfModules S` with `R = (↑U).ringCatSheaf` (on `D`), `S = X.ringCatSheaf.over U`
(on `C`) — i.e. the functor goes `SheafOfModules (↑U).ringCatSheaf ⥤ SheafOfModules (X.ringCatSheaf.over U)`,
exactly the directive's `overEquivalence X U` orientation.

1. Continuity: free (Decision 3). Bring `overEquivInverseIsDenseSubsite` into scope.
2. **The ring morphism `φ` (THE real content, ring-level, NOT module-level)**:
   `φ : (X.ringCatSheaf.over U) ⟶ (e.functor.sheafPushforwardContinuous RingCat J K).obj (↑U).ringCatSheaf`.
   Sectionwise at `V : Over U` this is `O_X(V.left) ⟶ O_{↥U}(e.functor V)`, the structure sheaf of
   the open immersion `U.ι : ↥U ⟶ X`. Build from `U.ι.appIso`/`(U.ι.appIso _).inv` — the IDENTICAL
   datum `Scheme.Modules.restrictFunctor` uses (`Sheaf.lean:320`: `α U := (f.appIso U.unop).inv`).
   `ψ` is the symmetric inverse iso. `Scheme.ringCatSheaf` = `sheafCompose (forget₂ CommRingCat RingCat)`
   applied to `X.sheaf` (`AlgebraicGeometry/Modules/Presheaf.lean:34`).
3. `H₁`, `H₂`: equalities of ring-presheaf nat-transes. On the thin poset `Opens` *naturality* is
   `Subsingleton.elim`-free, but the hom equalities themselves are NOT subsingleton — they follow
   from `φ`/`ψ` being mutual inverses via the `appIso` round-trip + `Sheaf.hom_ext`/`ext`.
   (Skippable entirely in the functor-only shape, Decision 2.)
4. `overEquivalence X U := pushforwardPushforwardEquivalence e φ ψ H₁ H₂`.
5. **Consumer iso (A) `restrict ↦ over`**: `(restrictFunctor U.ι ⋙ overEquivalence.functor).obj M ≅ M.over U`.
   `M.restrict U.ι` is *itself* `SheafOfModules.pushforward` along `U.ι.opensFunctor`
   (`Sheaf.lean:319-322`); compose with `overEquivalence.functor = pushforward φ` via
   `SheafOfModules.pushforwardComp` (`PushforwardContinuous.lean:101`, it is `Iso.refl _`), then
   `pushforwardNatIso` (`:188`) along the `eqToIso` natural iso of the two underlying functors
   `Over U ⥤ Opens X` (both `V ↦ V.left`). This is a verbatim mirror of
   `restrictFunctorAdjCounitIso` (`Sheaf.lean:335-340`).
6. **Consumer iso (B) `unit ↦ unit`**: `overEquivalence.functor.obj (unit (↑U).ringCatSheaf) ≅
   unit (X.ringCatSheaf.over U)` — `pushforward` of the unit module is the unit module up to the `φ`
   identification (the `pushforward`-of-unit computation; cf. the project's existing
   `pullbackObjUnitToUnitIso` pattern).
7. `chartOverIso M U e := (A).symm ≪≫ overEquivalence.functor.mapIso e ≪≫ (B)`; the dual lane's
   `sliceDualTransport` consumes the same three pieces.

## Recommendation

Build `SheafOfModules.overEquivalence` by **instantiating
`SheafOfModules.pushforwardPushforwardEquivalence` at `TopologicalSpace.Opens.overEquivalence U`** —
this is the canonical Mathlib idiom and the documented `Over.lean` TODO target. The apparent
"~200–350 LOC, Mathlib-scale" blocker collapses: (i) continuity is *already* discharged by the
project's `overEquivInverseIsDenseSubsite` + Mathlib's auto dense-subsite instance, and (ii) the only
genuine content — the ring morphism `φ` — is the open-immersion structure-sheaf iso the project
*already* writes inline in `restrictFunctor` (`(U.ι.appIso _).inv`). Realistic estimate **~120–220
LOC** in a standalone file, most of it mirroring `restrictFunctor` / `restrictFunctorAdjCounitIso` /
`pushforwardPushforwardEquivalence`. If `ψ`/`H₁`/`H₂` resist, fall back to the **functor-only**
`restrictOverFunctor := pushforward φ` + isos (A),(B): both consumers need only that, no inverse.
This is NOT a Mathlib gap-fill and NOT a parallel API — it is assembling three existing primitives.
