# Analogy: transporting local quasi-coherent presentations to finish gap1 on `Spec R`

## Mode
api-alignment

## Slug
quot-transport

## Iteration
030

## Question
To finish gap1 (`IsIso M.fromTildeΓ` for `M : (Spec R).Modules` with `[M.IsQuasicoherent]`)
the prover must, for each basic open `D(r) ≤ q.X i`, turn the *slice* presentation
`q.presentation i : (M.over (q.X i)).Presentation` into `IsIso ((M|_{D(r)}).fromTildeΓ)` on
`Spec R_r`. Two walls were reported: (1) "Mathlib `AlgebraicGeometry/Modules/` has no
restriction-to-open functor on `(Spec R).Modules`, no `over`↔pullback bridge, no QC-preservation";
(2) even *stating* `q.presentation i` times out on the slice `IsRightAdjoint` instance. Is the
`over`-slice route the wrong shape? Does Mathlib already provide the transport / the gap1 result?

## Project artifact(s)
- `AlgebraicJacobian/Picard/QuotScheme.lean:653` — `isIso_fromTildeΓ_iff_isLocalizedModule_restrict`
  (the reduction engine: gap1 ⇔ per-basic-open `IsLocalizedModule`; **built, axiom-clean**).
- `AlgebraicJacobian/Picard/QuotScheme.lean:686` — `isLocalizedModule_basicOpen_of_presentation`
  (global-presentation endpoint; **built**).
- `AlgebraicJacobian/Picard/QuotScheme.lean:730` — `exists_finite_basicOpen_cover_le_quasicoherentData`
  (finite basic-open cover refining `q.X`; **built**).
- `AlgebraicJacobian/Picard/QuotScheme.lean:253` — `SheafOfModules.IsLocallyFreeOfRank`
  (**already uses `Scheme.Modules.pullback (U i).ι`** — i.e. the project already knows the geometric
  restriction functor exists).

## Mathlib facts established (pinned commit; project's `.lake` Mathlib)

Restriction / pullback of `(Spec R).Modules` — **obstacle #1 is factually wrong**:
- `AlgebraicGeometry.Scheme.Modules.pullback (f : X ⟶ Y) : Y.Modules ⥤ X.Modules`
  (`Modules/Sheaf.lean:167`), a left adjoint (`:180`), additive (`:183`).
- An entire **`Restriction` section** for open immersions (`Modules/Sheaf.lean:312–451`):
  `restrictFunctor f : Y.Modules ⥤ X.Modules` (`:319`, docstring "isomorphic to the pullback
  functor … but has better defeqs"), `restrict M f` (`:325`), `restrict_obj : Γ(M.restrict f, U)
  = Γ(M, f ''ᵁ U)` (`:328`), `restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f`
  (`:371`), `restrictFunctorComp` (`:392`), `restrictStalkNatIso` (restriction commutes with
  stalks, `:424`). This IS "restriction of a `SheafOfModules` along an open immersion of schemes."

Presentation transport — **exists as a general idiom**:
- `SheafOfModules.Presentation.map (F) (η : F.obj (unit R) ≅ unit S) : Presentation (F.obj M)`
  for any `F` with `[PreservesColimitsOfSize F]` (`Quasicoherent.lean:179`); plus
  `Presentation.mapGenerators/mapRelations` (`:159,166`) and `Presentation.ofIsIso` (`:132`).
  `pullback`/`restrictFunctor` are left adjoints (preserve colimits) and send `unit ↦ unit`, so
  `Presentation.map` applies to them.

The abstract slice `over` (what `QuasicoherentData` actually carries):
- `SheafOfModules.over M X := (pushforward (𝟙 _)).obj M : SheafOfModules (R.over X)`
  (`PushforwardContinuous.lean:53`) — the **abstract Grothendieck-slice** restriction over the
  *site object* `X`, NOT the geometric `Scheme.Modules.restrict`. No Mathlib lemma connects the two.
- `QuasicoherentData` (`Quasicoherent.lean:201`) carries `presentation i : (M.over (X i)).Presentation`;
  `IsQuasicoherent` (`:249`) is `Nonempty QuasicoherentData` — **the only Mathlib access to local
  presentations is through the slice `over`.** There is no slice-free extractor.

The gap1 result itself — **absent**, exactly as in `quot-qcoh-affine-globalization.md`:
- `isIso_fromTildeΓ_iff : IsIso M.fromTildeΓ ↔ (tilde.functor R).essImage M` (`Tilde.lean:340`);
- `isIso_fromTildeΓ_of_presentation` needs a **global** `M.Presentation` (`Tilde.lean:398`);
- comment `Tilde.lean:310`: "We will later show that the essential image is exactly quasi-coherent
  modules" — i.e. QCoh = essImage is **not** in Mathlib.
- `presentationTilde` (`Tilde.lean:373`) + `(tilde M).IsQuasicoherent` (`:394`) — the EASY direction
  (any `tilde N` has a global presentation, since any module is `coker` of frees).

QC-preservation:
- The ONLY QC lemma is `IsQuasicoherent.of_coversTop` (`Quasicoherent.lean:377`): local QC ⟹ global
  QC. There is **no** "pullback/over preserves `IsQuasicoherent`".

The Mathlib template for slice presentation transport:
- `QuasicoherentData.bind` (`Quasicoherent.lean:360–375`) transports a presentation across an
  **iterated slice** via `(((D i.1).presentation i.2).map e.inverse (.refl _)).ofIsIso …`, where
  `e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv …)`
  (`PushforwardContinuous.lean:305`, `CategoryTheory/Sites/Over.lean:471–489`). It carries
  `#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/` and
  `set_option backward.isDefEq.respectTransparency false` — **Mathlib's own slice-presentation
  transport fights exactly the timeout the prover hit, and tames it with `set_option`.**

The iterated-slice equivalences (`Sites/Over.lean:469–489`) only relate `(J.over X).over f` to
`J.over (composite)` — slices-of-slices. They do **not** bridge the opens-site slice `J.over U` to
the *small Zariski site of the open subscheme* `U.toScheme`. That bridge is absent.

## Decisions identified

### Decision A: is there a restriction-to-open functor on `(Spec R).Modules`? (obstacle #1)
- **Mathlib idiom**: yes — `Scheme.Modules.pullback` and the open-immersion `restrictFunctor`
  (`Modules/Sheaf.lean:167,319`), with `restrict_obj` defeq, `restrictFunctorIsoPullback`,
  `restrictStalkNatIso`. The project *already* uses `Scheme.Modules.pullback (U i).ι` in
  `IsLocallyFreeOfRank` (`QuotScheme.lean:255`).
- **Gap**: the obstacle-#1 claim is **wrong**. These functors live in `Modules/Sheaf.lean`, which the
  prover apparently treated as out of the `{Presheaf, Sheaf, Tilde}` set. No parallel functor should
  be built.
- **Verdict**: PROCEED (use `Scheme.Modules.restrictFunctor`/`pullback`; do not hand-roll).

### Decision B: is the `M.over (q.X i)` / `q.presentation i` slice route the wrong shape?
- **Mathlib idiom**: For transporting a `QuasicoherentData` presentation, the slice route **is** the
  canonical idiom — `QuasicoherentData.bind` is the worked template (`Presentation.map e.inverse`
  + `pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv g)` + `.ofIsIso`). `IsQuasicoherent`
  is *defined* only via slice `QuasicoherentData`, so there is **no slice-free** way to pull a local
  presentation out of `[M.IsQuasicoherent]` (answer to directive Q2(i): NO).
- **The timeout is not structural.** Mathlib's `bind` defeats the very same
  `(sheafToPresheaf (J.over …)).IsRightAdjoint`/`HasSheafify` synthesis blow-up with
  `set_option backward.isDefEq.respectTransparency false` (+ heartbeat headroom). The prover hit it
  because those options were not in force.
- **Gap**: divergent-equivalent — the route is right, but it is *not where the difficulty lives*, and
  pushing slice-site manipulation all the way to `Spec R_r` by hand is the wrong amount of work.
- **Verdict**: PROCEED on the transport *as a sub-step*, but minimize slice contact (see Decision C).

### Decision C: the genuinely missing ingredient — the `over U ↔ Spec R_r` bridge
- **Mathlib idiom**: NONE. To apply `isIso_fromTildeΓ_of_presentation` (which needs
  `M : (Spec S).Modules` and a *geometric* presentation) we must identify the abstract slice
  `M.over (D r)` — an object of `SheafOfModules ((Spec R).ringCatSheaf.over (D r))` — with the
  geometric `(Spec R_r).Modules` and `M.restrict (D r).ι` across `D(r) ≅ Spec R_r`. Mathlib has the
  pieces but not the bridge: `Scheme.Hom.opensFunctor` (`OpenImmersion.lean:87`), the
  basicOpen↔`Spec R_r` isos (`AffineScheme.lean:566–572`, `isLocalization_basicOpen`), but **no**
  equivalence `J.over U ≃ Opens(U.toScheme)` of sites carrying `R.over U ≅ U.toScheme.ringCatSheaf`,
  hence no `M.over U ≅ M.restrict U.ι`.
- **Gap**: divergent-with-cost / missing — this single bridge is the load-bearing piece the prover's
  plan silently assumed. Without it, "transport the slice presentation to a presentation of
  `M|_{D(r)}` on `Spec R_r`" cannot even be *typed*.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — build `overRestrictIso` (named ingredient).

### Decision D: the section-localization descent (the real keystone, per iter-026)
- **Mathlib idiom**: NONE for the local→global step. Even granting `IsIso ((M|_{D(r)}).fromTildeΓ)`
  on each `Spec R_r`, that is section-localization of `M|_{D(r)}` over `R_r`; assembling the
  **global**-over-`R` statement `IsLocalizedModule (powers f) (Γ(M,⊤) → Γ(M,D f))` that the engine
  consumes requires the sheaf-equalizer + flat-localization descent (Hartshorne II.5.3 / Stacks
  01HA): `IsLocalization.flat`, finite cover, `M.isSheaf`. The plan's appeal to
  `isLocalizedModule_basicOpen_of_presentation` does NOT close this — that lemma needs a *global*
  presentation of `M` on `Spec R`, which is not produced by per-`D(r)` data.
- **Gap**: divergent-and-underestimated — this is genuine multi-step descent, the same irreducible
  content flagged in `quot-qcoh-affine-globalization.md`.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — this is the keystone, not the transport.

## Recommendation

The slice route is **not the wrong shape for the transport sub-step**, and obstacle #1 is wrong
(`Scheme.Modules.restrictFunctor`/`pullback` exist). But framing gap1 as "transport a presentation,
then `isLocalizedModule_basicOpen_of_presentation`" mislocates the work: the load-bearing missing
pieces are the **`over U ↔ Spec R_r` bridge (C)** and the **section-localization descent (D)**.
Build gap1 in this order, keeping slice contact to a single tamed lemma:

1. **`overRestrictIso` (C, the bridge).** For `U : X.Opens` of a scheme `X`, build
   `M.over U ≅ (restrictFunctor U.ι).obj M` (equivalently land it through
   `restrictFunctorIsoPullback`), via the site equivalence `J.over U ≃ Opens(U.toScheme)` induced by
   `U.ι.opensFunctor` carrying `R.over U ≅ U.toScheme.ringCatSheaf`. State and prove it with
   `set_option backward.isDefEq.respectTransparency false` (Mathlib's own `bind` incantation) to
   dodge the `IsRightAdjoint`/`HasSheafify` synthesis timeout. This is the ONE lemma that must touch
   the slice site; everything downstream is geometric.

2. **Per-affine local-tilde (P1).** For `r ∈ t` (from `exists_finite_basicOpen_cover_le_quasicoherentData`)
   with `D(r) ≤ q.X i`: take `q.presentation i : (M.over (q.X i)).Presentation`; transport to the
   smaller open with `Presentation.map` along the **iterated-slice** functor (template:
   `QuasicoherentData.bind`, `Quasicoherent.lean:360`); push through `overRestrictIso` and the
   `D(r) ≅ Spec R_r` iso (`Presentation.map` along `Scheme.Modules.pullback`) to land
   `(M' : (Spec R_r).Modules).Presentation`, then `isIso_fromTildeΓ_of_presentation`.

3. **Section-localization descent (D, the keystone).** From "M is locally tilde on the finite
   basic-open cover {D(r)}", prove `∀ f, IsLocalizedModule (powers f) (Γ(M,⊤) → Γ(M,D f))` via the
   sheaf equalizer over the finite cover + `IsLocalization.flat` (localization is exact and commutes
   with the finite limit). This is the genuine content; it is reused by gap2.

4. **Assemble.** Feed (3) into the existing `isIso_fromTildeΓ_iff_isLocalizedModule_restrict`
   (`QuotScheme.lean:653`) — already axiom-clean — to land `IsIso M.fromTildeΓ`.

Blueprint these four as separate `\lean{…}` obligations so a mathlib-build prover gets the right
shape; (C) and (D) are the two genuinely new lemmas, (P1)/(4) are Mathlib glue. Note the standing
project memory `quot-quasicoherentdata-slice-transport-wall` should be updated: the wall is *not*
"no restriction functor" (there is one) but "no `over U ↔ Spec R_r` bridge + the descent is the
keystone", and the slice timeout is tamed by `backward.isDefEq.respectTransparency false`.
