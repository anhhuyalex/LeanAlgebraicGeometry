# Analogy: does Mathlib carry `pushforward_commutes_restriction`, and is `pushforwardPushforwardEquivalence` / `over` the right API?

## Mode
api-alignment

## Slug
pushforward-restriction

## Iteration
061

## Question
Build `AlgebraicGeometry.pushforward_commutes_restriction`: for `φ : X ≅ Y`, `Φ =
Scheme.Modules.pushforwardEquivOfIso φ`, `H : X.Modules`, `U_i : Opens X`, `V_i = φ.inv ⁻¹ᵁ U_i`,
and `e_i` the homeomorphism-induced slice-module equivalence,
`e_i.functor.obj (H.over U_i) ≅ (Φ.functor.obj H).over V_i`
(i.e. `(f_*H)|_V ≅ (f|_{f⁻¹V})_*(H|_{f⁻¹V})` for `f = φ` iso). Confirm whether Mathlib already
provides this commutation, whether `pushforwardPushforwardEquivalence` is the canonical tool, and
whether `Scheme.Modules.over W` is the right "restrict to an open" abstraction.

## Where this is consumed
`AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean:532` — the lone `case hqc => sorry` in
`higherDirectImage_openImmersion_acyclic`. `hqc : (Φ.functor.obj H).IsQuasicoherent`, the R1 core of
the unbuilt `isQuasicoherent_pushforwardEquivOfIso` (see `analogies/need1-transport.md`).

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean:204` — `Scheme.Modules.pushforwardEquivOfIso φ` (`Φ.functor = Scheme.Modules.pushforward φ.hom`).
- `AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean:526-532` — the `ext_jShriekOU_eq_zero_of_specIso … ?hqc` call; `hqc` is the only open hole.
- No project-local `def over` for `Scheme.Modules` — `H.over U` is Mathlib's `SheafOfModules.over` (verified: grep finds no redefinition).

## Decisions identified

### Decision 1: Does Mathlib carry the comparison iso / qcoh-preservation under pushforward?

- **Mathlib idiom / state**: Mathlib carries **neither** the comparison iso **nor** any
  `IsQuasicoherent`-preservation lemma for `pushforward` / `pullback` / `restrict` / iso. Verified
  this iter against the project's pinned Mathlib:
  - The **only** `IsQuasicoherent` *instance* in all of Mathlib is `tilde`
    (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean:394`).
  - The **only** non-trivial *constructor* is `SheafOfModules.IsQuasicoherent.of_coversTop`
    (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:377`) plus its engine
    `QuasicoherentData.bind` (`Quasicoherent.lean:360`) and same-site `QuasicoherentData.ofIsIso`
    (`Quasicoherent.lean:323`). `grep IsQuasicoherent` over `Mathlib/` returns no pushforward /
    pullback / restrict / open-immersion preservation lemma.
  - No `over`-vs-`pushforward` commutation lemma exists in `PushforwardContinuous.lean`.
- **Project's path**: build the comparison iso from `pushforwardPushforwardEquivalence` +
  `Scheme.Modules.pushforward_obj_obj` (rfl on sections), then feed `of_coversTop`.
- **Gap**: divergent-but-mandatory — there is nothing to align *to*; the content does not exist
  upstream. The project's path reuses the correct Mathlib *machinery*.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**. (Genuine upstream gap, not a project failure.)

### Decision 2: Is `pushforwardPushforwardEquivalence` the canonical tool, or is there a slicker idiom?

- **Mathlib idiom**: `SheafOfModules.pushforwardPushforwardEquivalence`
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:305`) is precisely the tool
  Mathlib *itself* uses for exactly this transport: `QuasicoherentData.bind`'s `presentation` field
  (`Quasicoherent.lean:369-375`) builds `e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv …)`
  then `(P.map e.inverse (.refl _)).ofIsIso (e.fullyFaithfulFunctor.preimageIso (e.counitIso.app …)).hom`.
  The project's R1 is the *same shape* with the homeomorphism-induced opens-site equivalence in place
  of `Over.iteratedSliceEquiv`.
- **Why the equivalence is NECESSARY (no `pushforwardComp`-only shortcut)**: `Presentation.map`
  consumes a **colimit-preserving** functor between the slice module categories (generators/relations
  are colimits). A bare `SheafOfModules.pushforward` is a **right** adjoint (right adjoint to
  `pullback`) and does **not** preserve colimits, so it cannot transport a `Presentation`. Only the
  full *equivalence* (whose functor preserves all (co)limits) works. This is exactly why `bind` uses
  the equivalence and not a bare pushforward. Hence there is **no slicker single-`pushforwardComp`
  idiom** that avoids the over-site equivalence assembly.
- **The comparison ISO itself is short** (the expensive part is *not* the iso): it is the
  `restrictFunctorAdjCounitIso` recipe — `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:335` builds
  `pushforward f ⋙ restrictFunctor f ≅ 𝟭` as
  `pushforwardComp ≪≫ pushforwardNatIso (opens-equality) ≪≫ pushforwardCongr (ring-map equality) ≪≫ pushforwardId`,
  where `SheafOfModules.pushforwardComp` (`PushforwardContinuous.lean:101`) is **definitionally
  `Iso.refl`** and `pushforward_obj_obj` is `rfl`. The directive's comparison iso is the analogous
  four-step composite at object `H`.
- **Where the ~100-150 LOC actually lives (irreducible via this route)**: assembling the *site*
  equivalence `Over U_i ≌ Over V_i` from the homeomorphism `φ`, supplying its `IsContinuous`
  instances, and discharging `pushforwardPushforwardEquivalence`'s two coherence hyps `H₁ H₂`
  (in `bind` these are `by ext : 2; exact R.1.map_id _`-cheap; here `𝟙`-ring-map + structure-sheaf
  identifications, similarly cheap). Building blocks that exist:
  `Over.map` / `Over.forget` / `Over.star` are continuous (`Mathlib/CategoryTheory/Sites/Over.lean:283/243/335`);
  `Opens.map` of an (open-embedding/homeomorphism) base map is continuous
  (`Mathlib/Topology/Sheaves/Functors.lean:126`, `IsOpenEmbedding.functor_isContinuous`).
- **Verdict**: **PROCEED** with `pushforwardPushforwardEquivalence` — it is the canonical *and
  necessary* tool. No cheaper idiom exists.

### Decision 3: Is `Scheme.Modules.over W` the right abstraction, or a parallel API?

- **Mathlib idiom**: `SheafOfModules.over M X := (pushforward (𝟙 _)).obj M`
  (`PushforwardContinuous.lean:53`) — restriction to the *slice site* `Over X`. This is the **exact**
  abstraction Mathlib's qcoh layer is defined on: `QuasicoherentData.presentation (i) :
  (M.over (X i)).Presentation` (`Quasicoherent.lean:201,208`). Proving `IsQuasicoherent (Φ H)` via
  `of_coversTop` *forces* landing `IsQuasicoherent ((Φ H).over V_i)` per cover element.
- **Project's path**: uses `H.over U` = Mathlib's `SheafOfModules.over` directly (no redefinition).
- **The genuine parallel-API trap to avoid**: Mathlib *also* has `Scheme.Modules.restrictFunctor` /
  `restrict` (`Sheaf.lean:319,325`) — restriction along an **open-immersion morphism of schemes**
  (`Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)`). That is a **different** (geometric-morphism) abstraction;
  using it to feed `IsQuasicoherent`/`of_coversTop` would be the parallel-API mistake, because the
  qcoh definition speaks the slice-site `over` language, not the scheme-morphism `restrict` language.
- **Gap**: identical — the project already uses the canonical `over`.
- **Verdict**: **ALIGN_WITH_MATHLIB** — keep `over`; do **not** re-model the open-restriction via
  `Scheme.Modules.restrict` for the qcoh assembly.

## Recommendation

**PROCEED** with the `pushforwardPushforwardEquivalence` route — it is the canonical *and* necessary
idiom (the colimit-preservation that `Presentation.map` demands rules out any bare-`pushforward`
shortcut), and `over` is the mandated abstraction. The single best alignment move is to **mirror
`QuasicoherentData.bind`'s `presentation` field almost verbatim**: state
`isQuasicoherent_pushforwardEquivOfIso {X Y} (φ : X ≅ Y) (H : X.Modules) [H.IsQuasicoherent] :
((pushforwardEquivOfIso φ).functor.obj H).IsQuasicoherent`, prove it via `of_coversTop` over the
image cover `fun i => φ.inv ⁻¹ᵁ (q.X i)`, and for each `i` build the per-slice equivalence
`e_i := pushforwardPushforwardEquivalence <homeo-induced Over U_i ≌ Over V_i> (𝟙) (𝟙) H₁ H₂`,
then `(q.presentation i).map e_i.inverse (.refl _)).ofIsIso <comparison>.hom` exactly as `bind`
does with `Over.iteratedSliceEquiv`. The comparison iso `e_i.functor.obj (H.over U_i) ≅ (Φ H).over V_i`
is the short `pushforwardComp(=Iso.refl) ≪≫ pushforwardCongr ≪≫ pushforwardComp.symm` composite
(template: `restrictFunctorAdjCounitIso`, `Sheaf.lean:335`). Do not build a standalone bespoke
`pushforward_commutes_restriction` API divorced from `bind`'s shape, and do not route through
`Scheme.Modules.restrict`.

## Citations
- `SheafOfModules.over` — `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:53`
- `SheafOfModules.pushforward` — `…/PushforwardContinuous.lean:44`
- `SheafOfModules.pushforwardComp` (= `Iso.refl`) — `…/PushforwardContinuous.lean:101`
- `SheafOfModules.pushforwardCongr` — `…/PushforwardContinuous.lean:73`
- `SheafOfModules.pushforwardPushforwardEquivalence` — `…/PushforwardContinuous.lean:305`
- `QuasicoherentData` (`.presentation` field) — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:201,208`
- `QuasicoherentData.bind` (presentation field is the template) — `…/Quasicoherent.lean:360,369-375`
- `IsQuasicoherent.of_coversTop` — `…/Quasicoherent.lean:377`
- `QuasicoherentData.ofIsIso` (same-site only) — `…/Quasicoherent.lean:323`
- `Scheme.Modules.pushforward` / `pushforwardComp` / `restrictFunctor` / `restrictFunctorAdjCounitIso`
  — `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:151/210/319/335`
- only qcoh instance is `tilde` — `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:394`
- slice continuity instances — `Mathlib/CategoryTheory/Sites/Over.lean:283/243/335`
- `Opens.map` continuity — `Mathlib/Topology/Sheaves/Functors.lean:126`
