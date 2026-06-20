# Analogy: bounded re-route for `tensorObj_restrict_iso` (open-immersion vs line-bundle vs the dead δ-route)

## Mode
api-alignment

## Slug
tsroute208

## Iteration
208

## Question
Lane TS's abstract-adjoint comparison-map (mate δ) route for
`tensorObj_restrict_iso` is definitively blocked (it needs the absent
`(PresheafOfModules.pullback φ).Monoidal`). Which re-route is the
Mathlib-idiomatic, *bounded* one — (A) exploit that `f` is an open immersion
(sectionwise restriction + base-change-along-a-ring-iso), or (B) add
`IsLocallyTrivial` hypotheses and glue local isos — and do its prerequisites
exist at `b80f227` or are they an absent multi-file build?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:330-367` — `tensorObj_restrict_iso`
  (current body: 2 real reduction steps + residual `sorry`).
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:105-178` — the iter-207
  `restrictScalarsLaxMonoidal` instance built for the now-dead δ-route.
- `informal/tensorObj_restrict_iso.md`, `analogies/mate207.md`,
  `analogies/ts-design206.md`, `analogies/kaehler-tensorequiv-presheafpullback.md`.

## Key mathematical fact the routes hinge on

`tensorObj_restrict_iso` is **TRUE for arbitrary `M N : X.Modules`** — tensor
product commutes with restriction to an open subscheme with *no* local-freeness
hypothesis. Restriction along an open immersion is exact and is base change
along the structure-sheaf **isomorphism** `f.appIso`, not a general flat ring
map. This single observation reshapes the whole decision: Route (B)'s
`IsLocallyTrivial` hypotheses are mathematically *unnecessary* for this lemma,
and the δ-route's `extendScalars`-monoidality (needed only because it modeled
restriction as a *general* base change) is overkill.

## Decisions identified

### Decision A: Route (A) — open-immersion sectionwise / base-change-along-a-ring-iso

- **Mathlib idiom**: restriction along an open immersion is the **concrete,
  definitionally sectionwise** functor `Scheme.Modules.restrictFunctor`, NOT the
  abstract pullback. The load-bearing facts are all present at `b80f227`:
  - `restrict_obj` / `restrict_map` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:328,331`)
    — **both `rfl`**: `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)`. Restriction = reindex
    sections along `f.opensFunctor`.
  - `Scheme.Hom.appIso (U) : Γ(Y, f ''ᵁ U) ≅ Γ(X, U)`
    (`Mathlib/AlgebraicGeometry/OpenImmersion.lean:190`) — the `CommRingCat`
    isomorphism along which `restrictFunctor` reindexes scalars (it is literally
    `α.app U := (f.appIso U.unop).inv` in `restrictFunctor`'s def, Sheaf.lean:320).
  - `ModuleCat.restrictScalarsEquivalenceOfRingEquiv (e : R ≃+* S)`
    (`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:285`) — base change
    along a **ring iso** is an equivalence (the "extension of scalars along an
    iso is trivially iso" the directive asks for). PRESENT.
  - `PresheafOfModules.isoMk` (`Mathlib/Algebra/Category/ModuleCat/Presheaf.lean:118`)
    — assemble a sectionwise `app + naturality` into a presheaf-of-modules iso.
  - Iso-checking primitives: `Scheme.Modules.Hom.isIso_iff_isIso_app`
    (Sheaf.lean:132) — `IsIso φ ↔ ∀ U, IsIso (φ.app U)`; plus the stalkwise
    fallback `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` (Stalks.lean:652)
    and `Scheme.Modules.restrictStalkNatIso` (Sheaf.lean:425, restriction
    commutes with stalks).
- **The ONE genuine gap (bounded)**: to commute `.restrict f` past the
  `sheafification` inside `tensorObj`, the only Mathlib lemma is
  `SheafOfModules.sheafificationCompPullback` (PullbackContinuous.lean:117),
  which lands you on the **abstract** `PresheafOfModules.pullback φ.hom`
  (`Presheaf/Pullback.lean:44`, defined as `(pushforward φ).leftAdjoint` — no
  sectionwise formula). Mathlib has **no sectionwise unfolding** of presheaf
  `pullback`, and **no presheaf-level analogue of `restrictFunctorIsoPullback`**
  (i.e. "pullback along an open immersion ≅ sectionwise restriction" at the
  presheaf layer). This must be supplied project-side. **But it is bounded**:
  `analogies/kaehler-tensorequiv-presheafpullback.md` (Decision 5) hit the exact
  same opacity and estimated a **~30–60 LOC sectionwise-unfolding helper**, and
  that lane successfully built a base-change-via-`PresheafOfModules.pullback`
  iso. Here it is *easier* because `φ = (toRingCatSheafHom f).hom` is an
  open-immersion `appIso` (an iso), so the unfolded base change is along a ring
  iso (`restrictScalarsEquivalenceOfRingEquiv`), not a general algebra map.
- **Gap**: NEEDS_MATHLIB_GAP_FILL — but **small and single-file** (one
  presheaf-pullback-along-open-immersion sectionwise identification), NOT the
  multi-file monoidal build the δ-route needs. No new monoidal/`extendScalars`
  infra.
- **Verdict**: **PROCEED** with Route (A) (after landing the bounded unfolding
  helper as the first prover objective). This is the Mathlib-idiomatic route:
  use the *concrete* `restrictFunctor` sectionwise API, not abstract monoidal
  functor structure.

### Decision B: Route (B) — add `IsLocallyTrivial` and glue local isos

- **Mathlib idiom**: there is **no `SheafOfModules` gluing primitive** for
  assembling local isos into a global iso. The idiomatic move is the reverse:
  build a *global canonical morphism* first, then check it is an iso *locally*
  (`isIso_iff_isIso_app` per open, or `isIso_iff_stalkFunctor_map_iso` per
  stalk). "Build locally then glue the morphism" forces a cocycle/overlap
  agreement check with no off-the-shelf support.
- **Project's path (proposed)**: add `(hM hN : IsLocallyTrivial …)`, trivialise
  on a common affine `W`, build the iso there, glue.
- **Gap**: divergent-with-cost on two counts. (1) The hypotheses are
  **mathematically unnecessary** — the lemma holds for arbitrary `M, N`
  (tensor commutes with open restriction), so adding them is a false constraint
  that future general consumers cannot satisfy. (2) Even with them, you still
  need a *global* comparison morphism to apply any iso criterion, so the
  triviality buys you nothing the global-morphism-checked-locally route (A)
  doesn't already give for free — and the "glue local isos" step is strictly
  *more* work than (A) (cocycle bookkeeping with no primitive).
- **Verdict**: **DIVERGE_INTENTIONALLY = do NOT take (B)**. It is heavier than
  (A) and over-constrains the signature. (Local triviality remains the right
  tool for the *consumers* — `exists_tensorObj_inverse`, the unit/associator
  isos — just not for `tensorObj_restrict_iso` itself.)

### Decision δ: the abandoned mate route — `(PresheafOfModules.pullback φ).Monoidal`

- **Mathlib idiom**: the δ map exists (`Adjunction.leftAdjointOplaxMonoidal`,
  Functor.lean:1009, per `mate207.md`), but its hypothesis
  `(pushforward φ).LaxMonoidal` reduces to lifting
  `ModuleCat.extendScalars`-monoidality to the presheaf level for a **general**
  ring map — a multi-file genuine monoidal-functor build.
- **Gap**: NEEDS_MATHLIB_GAP_FILL — multi-file. The iter-207
  `restrictScalarsLaxMonoidal` instance (now in the file, lines 105-178) was the
  partial down-payment; completing it for `pullback` is the wall.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL — correctly abandoned.** It modeled
  open restriction as a general base change, paying for monoidality the
  open-immersion case gets for free.

## Recommendation

Re-route Lane TS to **Route (A)** and do **not** pause TS — this iso does **not**
bottom out in absent multi-file Mathlib infra. The route is:

1. **(Prerequisite, first prover objective, ~30–60 LOC.)** Build a sectionwise
   handle for `PresheafOfModules.pullback φ.hom` along the open-immersion ring
   map `φ = (Scheme.Hom.toRingCatSheafHom f).hom` — i.e. a presheaf-level
   identification of the abstract pullback with the concrete
   reindex-along-`f.opensFunctor` + base-change-along-`appIso`, mirroring
   `restrictFunctorIsoPullback` one layer down. (Or reuse/adapt the unfolding
   helper the kaehler lane built — `analogies/kaehler-tensorequiv-presheafpullback.md`
   Decision 5.) This is the single genuine gap; it is bounded and single-file.
2. **(Main body.)** Keep the existing steps 1-2 (`restrictFunctorIsoPullback` +
   `sheafificationCompPullback`) reducing to the presheaf residual
   `(pullback φ.hom).obj (M.val ⊗ N.val) ≅ (M.restrict f).val ⊗ (N.restrict f).val`.
   Discharge it sectionwise via `PresheafOfModules.isoMk`: over each `U` both
   sides are `M(f''U) ⊗ N(f''U)` (by `restrict_obj` `rfl`), differing only by the
   scalar ring `O_X(U)` vs `O_Y(f''U)`, identified by
   `restrictScalarsEquivalenceOfRingEquiv (f.appIso U).commRingCatIsoToRingEquiv`.
   No `extendScalars` monoidality, no `(pullback φ).Monoidal`.
3. **(Iso check, if a morphism-then-iso shape is used instead of `isoMk`.)**
   `Hom.isIso_iff_isIso_app` (per-open) or `isIso_iff_stalkFunctor_map_iso`
   + `restrictStalkNatIso` (per-stalk).

Drop Route (B): the lemma is true for arbitrary `M, N`, so do not add
`IsLocallyTrivial` hypotheses, and there is no Mathlib SheafOfModules
iso-gluing primitive to make "glue local isos" cheaper than (A). Keep the
iter-207 `restrictScalarsLaxMonoidal` instance only if some other consumer uses
it; for `tensorObj_restrict_iso` it is dead weight.

**Blunt closability verdict: YES, closable by a `prove`-mode round on Route (A)
— conditional on first landing the bounded (~30–60 LOC) presheaf-pullback-
along-open-immersion sectionwise-unfolding helper.** It does NOT also bottom out
in absent multi-file monoidal infra. Sequence it as: helper objective → main
body objective.
