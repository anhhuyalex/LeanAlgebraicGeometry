# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the three seed declarations
+ kernel-only axioms**, for the **Line-Bundle Comparison Iso** subproject
(A.1.c.sub of the Algebraic-Jacobian-Challenge). Seeds:

- `lem:pullback_tensor_iso_loctriv` — `pullbackTensorIsoOfLocallyTrivial` (D4′; body+chart-chase
  CLOSED iter-020; sole residual = brick K1, ACTIVE this iter).
- `lem:dual_isLocallyTrivial` — `dual_isLocallyTrivial` (DUAL route) — **DELIVERED iter-015**.
- `thm:rel_pic_addcommgroup_via_tensorobj` — `PicSharp.addCommGroup_via_tensorObj` (consumer; SCAFFOLD).

## Build state (iter-021 plan turn)

- **D3′ comparison-iso substrate COMPLETE @ iter-019** (`pullbackTensorMap_restrict` + whole base-change
  cone sorry-free, axiom-clean).
- **Seed-1 D4′ chart-chase ASSEMBLED @ iter-020**: `pullbackTensorIsoOfLocallyTrivial` (L4238) body
  sorry-free; reduces the whole D4′ `IsIso` to the single open-immersion brick **K1**.
- **`TensorObjSubstrate.lean`** — GREEN, 2 bare sorries:
  - L4172 — K1 `pullbackTensorMap_isIso_of_isOpenImmersion` (the ACTIVE target; transitive sorryAx to seed-1).
  - L734 `exists_tensorObj_inverse` — import-cycle-deferred terminal (never close here; see deferrals).
- **`SliceTransport.lean` / `DualInverse.lean`** — sorry-free (DUAL route CLOSED iter-015).
- Project-wide bare sorries: **2** (1 active K1 + 1 deferred terminal).

## Gate status (iter-021)
- **blueprint-reviewer bpr021: PASS — HARD GATE CLEAR** for `Picard_TensorObjSubstrate.tex`. K1 node
  `lem:pullback_tensor_map_isiso_open_immersion` well-formed (pin matches `pullbackTensorMap_isIso_of_isOpenImmersion`,
  proof sketch detailed, UNMARKED open); wired into D4′ `\uses`; "only D3′ is new" retracted. Coverage
  nodes `chart_isiso`, `base_unit` added. K1 `\uses` reduction-lemma added this turn (DAG honesty).
- **strategy-critic sc021: routes SOUND.** K1 verified NOT a Mathlib wall — `Adjunction.IsMonoidal`
  (`leftAdjoint_μ` field expresses the right adjoint's `μ` through the left adjoint's oplax `δ`),
  `leftAdjointUniq`, `conjugateEquiv` all present in Mathlib. Terminal file-MOVE acyclic.
- **progress-critic pc021: CHURNING** (strict 3/4-PARTIAL) — corrective = the K1 route pivot below,
  which the critic confirms is already embedded in this objective (genuine route change, not a reworded
  re-dispatch). Executing it IS the must-fix response.

## Current Objectives

1. **`AlgebraicJacobian/Picard/TensorObjSubstrate.lean`** — **seed-1 D4′ brick K1, `prove` mode.** Close
   the sole open sorry at L4172 inside `pullbackTensorMap_isIso_of_isOpenImmersion` (L4139). Closing it
   makes `chart_isIso` + `pullbackTensorIsoOfLocallyTrivial` (seed-1) axiom-clean — NO other edits needed.
   Blueprint: `chapters/Picard_TensorObjSubstrate.tex` — `lem:pullback_tensor_map_isiso_open_immersion`
   (K1, ~L3668, detailed presheaf-δ proof sketch).

   **K1 = `IsIso (pullbackTensorMap f M N)` for `[IsOpenImmersion f]`, ARBITRARY M,N.**

   **REDIRECT — do NOT retry the functor-level `Functor.Monoidal.transport` route** (the abandoned
   iter-020 attempt; its stale in-file comment at L4159–4171 documents WHY it fails — the monoidal-carrier
   diamond `MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)` is not globally synthesizable).
   Use the in-proof presheaf-δ route instead:
   - **Entry:** `apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta` (L1308, this file) — already the
     first line of K1's body. This reduces the goal to
     `IsIso (a_Y.map (δ (PresheafOfModules.pullback φ') M.val N.val))` where
     `φ' = (f.toRingCatSheafHom).hom`, `a_Y = PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)`.
   - **Sheafification preserves isos:** it suffices to show the PRESHEAF-level
     `IsIso (δ (PresheafOfModules.pullback φ') M.val N.val)` (then `a_Y.map` of an iso is an iso —
     `Functor.map_isIso` / `inferInstance`).
   - **Presheaf δ iso — MIRROR the CLOSED `tensorObj_restrict_iso`** (L473, axiom-clean, study its body
     L516–550): build, in-proof, H1 = the presheaf iso `pushforward β ≅ pullback φ'` via
     `hadj.leftAdjointUniq (pullbackPushforwardAdjunction φ')` (β the open-immersion structure map,
     `hadj := pushforwardPushforwardAdj …`), and H2 the strong-monoidal tensorator of `pushforward β`
     (β sectionwise the bijective `f.appIso`, so `restrictScalarsMonoidalOfBijective β' hβ` gives
     `(restrictScalars β').Monoidal`). The carrier diamond is dodged exactly as `tensorObj_restrict_iso`
     does (build over the SYNTACTIC `_ ⋙ forget₂` base form; result defeq to the goal; `exact`).
   - **Identify δ with the H1∘H2 comparison via the adjunction mate.** `δ (pullback φ')` is
     `presheafPullbackOplaxMonoidal` = the adjunction-mate oplax structure of
     `pullbackPushforwardAdjunction φ'`. Use `Adjunction.IsMonoidal` — its `leftAdjoint_μ` field
     [verified in Mathlib, sc021] expresses the right adjoint's `μ` through the left adjoint's oplax `δ`,
     so under H1 (≅ the strong-monoidal `pushforward β`) the δ is conjugate (by H1's iso components) to
     the invertible strong-monoidal tensorator `μIso`. This is the δ-side analogue of the unit-side
     `presheafUnit_comp_map_eta` (L1476, which uses `Adjunction.unit_app_unit_comp_map_η`) — study it as
     the working template for firing the Mathlib mate identity on THIS concrete adjunction.
   - **`IsIso`-via-conjugation:** an iso conjugated by isos is an iso (`IsIso.of_isIso_comp_left/right`,
     `IsIso.comp_isIso'`, `asIso`); `Functor.Monoidal.μIso`/`Functor.OplaxMonoidal.δ` of a strong-monoidal
     functor is an iso (Mathlib instance). `conjugateEquiv` (Mates.lean) may package the transport.

   - **Reference anchor:** Stacks `lemma-tensor-product-pullback` (pullback commutes with ⊗ functorially);
     along an open immersion the pullback is restriction = base change along the structure-sheaf ISO, hence
     strong monoidal. Quoted verbatim in the K1 blueprint node.
   - **Bar:** close the K1 sorry → seed-1 `pullbackTensorIsoOfLocallyTrivial` axiom-clean. Partial progress
     (presheaf-δ goal reached, H1/H2 spliced, mate-identity stated as a `have`) is committable (GREEN only).
   - **If the mate-compatibility `leftAdjoint_μ` does NOT fire on this concrete adjunction** (a genuine
     Mathlib-shape gap, not a naming miss): STOP, report the exact unprovable `have` + its goal state, and
     name the missing reconciliation lemma — next iter switches to `mathlib-build`. Do NOT fall back to the
     functor-level `transport` route.
   - **Coverage:** any NEW top-level (non-`private`) helper → list under `## Needs blueprint entry` with
     its `\uses` deps. Mark generic `IsIso`-plumbing helpers `private` (no node owed).

(`exists_tensorObj_inverse` (L734) stays deferred this iter — import-cycle; closes next phase via the
refactor-MOVE downstream of DualInverse. Seed-3 consumer `RelPicFunctor.lean` stays deferred until seed-1
+ the terminal close land.)

## Standing deferrals

- **Terminal `exists_tensorObj_inverse` (L734):** import-cycle-deferred; closes NEXT phase by a
  `refactor`-MOVE of the decl to a file downstream of `DualInverse.lean` (where `dual_isLocallyTrivial`
  is visible) + repoint `RelPicFunctor.lean`'s import (sole consumer — RE-GREP to confirm before the MOVE,
  per sc021). Then a prover closes the gluing proof (bridges B+C done; A = `homOfLocalCompat` descent).
- **Scaffold target (decl does not exist yet — NOT fill-sorry):** `PicSharp.addCommGroup_via_tensorObj`
  (seed 3, `RelPicFunctor.lean`); gated on seed-1 (map_add ← comparison iso) + the terminal close.
  The OnProduct-specialisation `pullback_tensorObj_iso` (`lem:pullback_compatible_with_tensorobj`) lands
  as an immediate downstream specialisation of seed-1.
- **Import architecture (in scope):** `LineBundlePullback → TensorObjSubstrate → SliceTransport →
  DualInverse`; `TensorObjSubstrate → RelPicFunctor`. The terminal MOVE adds
  `RelPicFunctor → {TensorObjInverse} → DualInverse` (acyclic).
- **AJC Lan-decomposition block** (`extendScalars`/`pullback0`/`pullbackLanDecomposition`) — NOT ported
  (confirmed dead code; not in any seed cone).
- **Doc-refresh debt (non-blocking):** stale headers/in-proof comments — `TensorObjSubstrate.lean`
  L44/L46/L4014/L158–159 (header line-numbers + the abandoned-`transport` comment L4159–4171 describe a
  superseded route), `DualInverse.lean` L44/L238, `Vestigial.lean`. Fix opportunistically when next touched.
- **Coverage / file-split debt:** bulk ~99 `lean_aux` decls remain (scheduled `Coverage + file-split`
  phase); the 3 substantive iter-020 helpers (K1, `chart_isIso`, `base_unit`) now have blueprint nodes.
  Split `TensorObjSubstrate.lean` (>3600 LOC) deferred until the active seed-1 lane lands.
- **Extraction note:** module names, file paths, blueprint labels unchanged from the parent so proved
  seeds merge back cleanly. Sibling extracts (Cech-Cohomology, Quot-Foundations) cover disjoint cones.
