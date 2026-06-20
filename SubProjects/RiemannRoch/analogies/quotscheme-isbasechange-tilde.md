# Analogy: closing `IsBaseChange` on the affine-open section pullback baseMap

## Mode
api-alignment

## Slug
quotscheme-isbasechange-tilde

## Iteration
187

## Question

How does Mathlib idiomatically prove `IsBaseChange` for **sections of a
module-sheaf pullback over a pair of affine opens** — i.e. for the
project's `pullback_app_isoTensor_baseMap_isBaseChange` — without first
requiring `N` to be quasi-coherent? Is there a direct
`IsBaseChange`-conclusion lemma in Mathlib's `Tilde` /
`Scheme.Modules.pullback` machinery? Is `Module.Flat.isBaseChange`
(Stacks 02KE) the cheaper route?

## Project artifact(s)

- `AlgebraicJacobian/Picard/QuotScheme.lean:543-584` —
  `pullback_app_isoTensor_baseMap_isBaseChange` (typed sorry, the
  iter-184 / iter-185 / iter-186 wall).
- `AlgebraicJacobian/Picard/QuotScheme.lean:508-541` —
  `pullback_app_isoTensor_baseMap` (axiom-clean iter-186).
- `AlgebraicJacobian/Picard/QuotScheme.lean:586-606` —
  `pullback_app_isoTensor_isBaseChange` (axiom-clean modulo the typed
  sorry above).
- `AlgebraicJacobian/Picard/QuotScheme.lean:632-689` —
  `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`
  (inline sorry at L689, the consumer the cascade wants to close).

## Mathlib precedents examined (this iter)

| Mathlib symbol | Location | What it gives | Relevance |
|---|---|---|---|
| `AlgebraicGeometry.tilde` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:87` | `M^~` as a `(Spec R).Modules` from an `R`-module | foundational; needs an `R`-module input, so to apply to `N|_V` we must extract `N|_V ≅ tilde Γ(N, V)` first |
| `tilde.isoTop` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:177` | `M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤)` | the section-evaluation iso that powers any `Γ(tilde M, ⊤) = M` step |
| `tilde.adjunction` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:279` | `tilde.functor R ⊣ moduleSpecΓFunctor` with `IsIso unit` | tilde is fully faithful; eass image = quasi-coherent sheaves having a presentation |
| `isIso_fromTildeΓ_iff` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:340-342` | `IsIso M.fromTildeΓ ↔ tilde.functor.essImage M` | the bridge "essentially-image-of-tilde" |
| `isIso_fromTildeΓ_of_presentation` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:398` | `M.Presentation → IsIso M.fromTildeΓ` | gives essential-image-of-tilde from a *presentation*, NOT directly from `[IsQuasicoherent M]` (the latter only supplies a presentation on a cover, not the whole space) |
| `tilde (M).IsQuasicoherent` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:394-395` | instance: `tilde M` is quasi-coherent | the converse: tilde sheaves ARE quasi-coherent |
| `SheafOfModules.IsQuasicoherent` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249` | typeclass: ∃ cover + presentations on each | the "abstract" qc predicate; needs unwrapping to get a tilde-form |
| `SheafOfModules.pullback` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53` | `(pushforward φ).leftAdjoint` | **abstract**; no section formula |
| `SheafOfModules.pullbackIso` | same file line 105 | `pullback φ ≅ forget ⋙ PresheafOfModules.pullback ⋙ sheafification` | sheafification destroys the affine-open identification |
| `SheafOfModules.pullbackObjFreeIso` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:122` | `pullback φ (free I) ≅ free I` (only for free sheaves) | too restrictive — also requires `F.Final` of the underlying functor |
| `PresheafOfModules.pullback` | `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:44` | `(pushforward φ).leftAdjoint` on presheaves | also abstract — no `pullback_obj_obj` lemma |
| `IsBaseChange` | `Mathlib/RingTheory/IsTensorProduct.lean` | the Prop | predicate; producers are: `TensorProduct.isBaseChange`, `IsBaseChange.ofEquiv`, `IsBaseChange.of_lift_unique` |
| `TensorProduct.isBaseChange` | `Mathlib/RingTheory/IsTensorProduct.lean:363` | `IsBaseChange S (TensorProduct.mk R S M 1)` | THE canonical IsBaseChange witness; everything else transports along this |
| `IsBaseChange.ofEquiv` | `Mathlib/RingTheory/IsTensorProduct.lean` | `(e : M ≃ₗ[R] N) → IsBaseChange R e` | transport an `IsBaseChange` along a linear equiv |
| **`Module.Flat.isBaseChange`** | **`Mathlib/RingTheory/Flat/Stability.lean:90`** | **`[Module.Flat R M] → IsBaseChange S f → Module.Flat S N`** | **STABILITY statement — propagates flatness ACROSS a given IsBaseChange. NOT a producer of IsBaseChange. The directive's hint that this is "the cheaper route" is *wrong*.** |
| `IsBaseChange.equiv` | `Mathlib/RingTheory/IsTensorProduct.lean` | `IsBaseChange S f → TensorProduct R S M ≃ₗ[S] N` | the consumer side, used for the `.symm` in `pullback_app_isoTensor_isBaseChange` |
| `IsLocalization.linearMap_compatibleSMul` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:78` (use site) | for a *localization* map, M ⊗ S = localized module | gives base-change for LOCALIZATION maps only, not arbitrary affine ring maps |

## Decisions identified

### Decision 1: Is `Module.Flat.isBaseChange` a route?

- **Mathlib idiom**: `Module.Flat.isBaseChange` is **NOT** a producer of
  `IsBaseChange` witnesses. Reading its signature carefully:

      Module.Flat.isBaseChange : ∀ R S M [CommSemiring R] [CommSemiring S]
        [Algebra R S] [Module R M] [Module.Flat R M] (N) [...] {f : M →ₗ[R] N},
        IsBaseChange S f → Module.Flat S N

  it takes `IsBaseChange S f` as a **hypothesis** and concludes
  `Module.Flat S N` — this is Stacks 00H8 ("flatness is preserved
  under base change"), in the conclusion direction. The lemma cannot
  build the `IsBaseChange` witness on the project's `baseMap`; it only
  propagates flatness across one once obtained.

- **Project's path**: The iter-186 docstring of
  `pullback_app_isoTensor_baseMap_isBaseChange` mentions
  "`Module.Flat.isBaseChange` … on the flat ring map" as a potential
  route. This is a category mistake.

- **Gap**: divergent-and-wrong (specifically: misidentified Mathlib
  citation; this lemma is not an `IsBaseChange` producer).

- **Verdict**: **DROP the `Module.Flat.isBaseChange` route.** It is a
  consumer of `IsBaseChange`, not a producer. Do NOT thread
  `[Module.Flat ...]` instances through the consumer chain hoping to
  shortcut the section identification — the section identification IS
  the substantive content and flatness is downstream of it.

### Decision 2: Is the Tilde-isoTop route the right Mathlib idiom?

- **Mathlib idiom**: Yes, but only **conceptually**. Mathlib has the
  foundational pieces:
    - `tilde` functor (`Tilde.lean:87`)
    - `tilde.isoTop : M ≅ Γ(tilde M, ⊤)` (`Tilde.lean:177`)
    - `tilde.adjunction` + tilde fully-faithful (`Tilde.lean:279, 312`)
    - `isIso_fromTildeΓ_iff` (`Tilde.lean:340`) for the essential image
    - `IsQuasicoherent` (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249`)

  However, **Mathlib does NOT have the connector lemma**:

      "for an affine ring map φ : A → B, the (Scheme.Modules.pullback (Spec φ))
       sends `tilde M` to `tilde (B ⊗_A M)`"

  This is the Stacks 01HQ / 0BJ8 content that would close the proof.
  Direct LSP searches (`pullback.*tilde`, `tilde.*pullback`,
  `baseChange.*tilde`) return no matches in Mathlib. The only pullback
  formula at all is `pullbackObjFreeIso` on **free** sheaves
  (`PullbackFree.lean:122`), which is too restrictive for general
  modules.

- **Project's path**: The iter-186 docstring proposes building this
  identification as the body of `pullback_app_isoTensor_baseMap_isBaseChange`
  (estimated ~80-150 LOC). The conceptual structure is sound: extract
  `N|_V ≅ tilde Γ(N, V)` on `Spec(Γ(X, V))` (via `hV.isoSpec` + quasi-
  coherence), pull back along `(Spec(g.appLE V U e))` to get
  `tilde (Γ(Y, U) ⊗_{Γ(X,V)} Γ(N, V))` on `Spec(Γ(Y, U))`, then `tilde.isoTop`.

- **Gap**: NEEDS_MATHLIB_GAP_FILL.

- **Verdict**: **The Tilde-isoTop route is the correct conceptual
  approach, but it requires the project to fill the genuine Mathlib gap
  "pullback of tilde = tilde of base change".** This is a project-side
  sub-build, ~80-200 LOC, structurally a Mathlib PR candidate.

### Decision 3: Threading `[IsQuasicoherent N]` through the consumer chain

- **Mathlib idiom**: The Tilde route **strictly requires** that
  `N|_V ∈ essImage tilde` on `Spec(Γ(X, V))`. Stacks (and Mathlib's
  `tilde.fullyFaithfulFunctor`) characterizes essential image of tilde
  on Spec as "has a presentation". `IsQuasicoherent M` (`Quasicoherent.lean:249`)
  gives a cover + presentations on each cover element — which means on
  a cover refining `V`, not necessarily on `V` itself. Strictly the
  project would need `N|_V` to already have a presentation, or the
  cover from `[IsQuasicoherent N]` to be refined.

  However, in Stacks 02KH (which is the *cohomology* base-change goal
  the consumer chain is building toward), **the standard hypothesis is
  `[IsQuasicoherent F]`** on the input sheaf `F : X.Modules`. For
  qcqs `f`, `(pushforward f).obj F` inherits quasi-coherence (Stacks
  01XJ); Mathlib does NOT yet have this instance
  (`IsQuasicoherent.pushforward` is absent at the pinned commit — also
  a Mathlib gap, but smaller).

- **Project's path**: The consumer chain
  (`canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`
  through `flatBaseChangeCohomology`) currently has NO quasi-coherence
  hypothesis. This is incompatible with both the substantive Stacks 02KH
  statement AND the project's Tilde-route plan.

- **Gap**: divergent-with-cost (the consumer signatures dropped a
  hypothesis Stacks requires; the IsBaseChange Prop is essentially
  uninhabited at the current generality).

- **Verdict**: **ALIGN_WITH_MATHLIB.** Add `[F.IsQuasicoherent]` (or
  equivalently to the inner helpers, `[N.IsQuasicoherent]`) to the
  signatures from `pullback_app_isoTensor_baseMap_isBaseChange` upward
  through `canonicalBaseChangeMap_app_app_isIso_*` to
  `flatBaseChangeCohomology`. The downstream user
  (Picard / Quot scheme infrastructure) already works only with
  quasi-coherent sheaves, so this hypothesis is free at the call site.

### Decision 4: Is `PresheafOfModules.pullback` cheaper?

- **Mathlib idiom**: `PresheafOfModules.pullback` is also defined as
  `(pushforward φ).leftAdjoint` (`Pullback.lean:44`) via
  `PartialAdjoint` machinery. It has NO section formula. So routing
  through the presheaf level does not avoid the Tilde-gap; it just
  moves it.

- **Verdict**: PROCEED (the presheaf route is not cheaper). The
  `sheafificationCompPullback` iso (`PullbackContinuous.lean:117`) tells
  us pullback commutes with sheafification — but this is a categorical
  fact, not a section formula.

## Cost estimates (iter-187)

| Step | LOC | Notes |
|---|---|---|
| Add `[F.IsQuasicoherent]` to the consumer chain | ~5-10 across 4 declarations | Threading the hypothesis. |
| `tilde Γ(N, V) ≅ N|_V` via `(hV.isoSpec)` + `isIso_fromTildeΓ_iff` | ~30-50 | The "transport quasi-coherence from V to Spec" step. Requires a project-side `affineOpen_tilde_iso` helper or extraction of a presentation from `[IsQuasicoherent N]` on the cover refinement. |
| Pullback-of-tilde = tilde of base change on Spec | **~60-100** | The load-bearing step. Naturality of `tilde.adjunction` + the Spec-level base change. This is the genuine Mathlib gap. |
| Section evaluation via `tilde.isoTop` | ~10-20 | Standard. |
| Assemble `IsBaseChange` via `IsBaseChange.ofEquiv` ∘ `TensorProduct.isBaseChange` | ~10-20 | Once the linear equiv is constructed, transport. |

Total for closing `pullback_app_isoTensor_baseMap_isBaseChange`:
**~115-200 LOC** + the consumer-side hypothesis threading. This matches
the iter-186 estimate.

## Recommendation

**Lane F prover directive for iter-187+**:

1. **Drop the `Module.Flat.isBaseChange` reference** from the
   `pullback_app_isoTensor_baseMap_isBaseChange` docstring — that lemma
   does NOT produce IsBaseChange witnesses (it's a stability statement).
   The `_of_isAffineBase` docstring at L656 should also be revised: the
   "RHS via `Module.Flat.isBaseChange` + `IsBaseChange.equiv`" framing is
   incorrect; the RHS IS the IsBaseChange Prop's content, not a separate
   step.

2. **Thread `[F.IsQuasicoherent]`** through the consumer chain:
   - `pullback_app_isoTensor_baseMap_isBaseChange`: add `[N.IsQuasicoherent]`.
   - `pullback_app_isoTensor_isBaseChange`: add `[N.IsQuasicoherent]`.
   - `Scheme.Modules.pullback_app_isoTensor`: add `[N.IsQuasicoherent]`.
   - `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`:
     add `[F.IsQuasicoherent]` (and use it to derive `((pushforward f).obj F).IsQuasicoherent`,
     which needs the project-side instance `IsQuasicoherent.pushforward`
     for qcqs `f` — another Mathlib gap, ~30 LOC).
   - propagate to `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen`,
     `canonicalBaseChangeMap_app_app_isIso`, `canonicalBaseChangeMap_isIso`,
     `flatBaseChangeCohomology`.

3. **Body of `pullback_app_isoTensor_baseMap_isBaseChange`**: this remains
   a ~115-200 LOC project sub-build. The substantive step "pullback of tilde
   on Spec = tilde of base change" is the Mathlib gap. Split into named
   intermediate helpers (the iter-186 pattern):
   - `tildeRestrict_of_isAffineOpen` (or similar): `N|_V` is in the essential
     image of `tilde` on `Spec(Γ(X, V))` given `[N.IsQuasicoherent]`.
   - `pullback_tildeIso`: pullback of `tilde M` along an affine ring
     map `φ : A → B` is `tilde (B ⊗_A M)` on `Spec B`.
   - Compose these to get the section-level linear equiv, then transport
     `TensorProduct.isBaseChange` via `IsBaseChange.ofEquiv`.

   The single typed `sorry` should sit on `pullback_tildeIso` (the genuine
   Mathlib gap), not on the `IsBaseChange` Prop directly.

4. **Do NOT** chase a "third route" via flatness of `g.appLE V U e`.
   Flatness of the ring map is a hypothesis available downstream (via
   `Flat.flat_appLE`), but it does NOT bypass the section-identification
   step. Stacks 02KE/00H8 "flat-base-change-of-modules" is a CONSUMER of
   the section identification (used to conclude the global pushforward
   is the tensor product), not a substitute for it.

## Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| 1. `Module.Flat.isBaseChange` as route | divergent-and-wrong → DROP | critical |
| 2. Tilde-isoTop route | correct conceptually; needs `pullback_tildeIso` Mathlib gap-fill | high |
| 3. `[IsQuasicoherent]` threading | ALIGN_WITH_MATHLIB | critical |
| 4. `PresheafOfModules.pullback` route | not cheaper; PROCEED | informational |

The iter-187 dispatch should pivot from "another helper" to:
(a) drop the `Module.Flat.isBaseChange` framing,
(b) thread `[IsQuasicoherent]` through the consumer chain,
(c) split the IsBaseChange sorry into a named `pullback_tildeIso` helper
that pins the actual Mathlib gap.
