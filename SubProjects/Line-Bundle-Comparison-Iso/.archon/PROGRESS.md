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
  CLOSED iter-020; sole residual = K1's `hcompat`, ACTIVE this iter via the recon022 idiom).
- `lem:dual_isLocallyTrivial` — `dual_isLocallyTrivial` (DUAL route) — **DELIVERED iter-015**.
- `thm:rel_pic_addcommgroup_via_tensorobj` — `PicSharp.addCommGroup_via_tensorObj` (consumer; SCAFFOLD).

## Build state (iter-022 plan turn)

- **D3′ comparison-iso substrate COMPLETE @ iter-019** (`pullbackTensorMap_restrict` + whole base-change
  cone sorry-free, axiom-clean).
- **Seed-1 D4′ chart-chase ASSEMBLED @ iter-020; K1 scaffolded @ iter-021**:
  `pullbackTensorIsoOfLocallyTrivial` (L4238) body sorry-free; `chart_isIso` + the whole D4′ `IsIso`
  reduce to the single open-immersion brick **K1** (`pullbackTensorMap_isIso_of_isOpenImmersion`, L4139),
  whose Steps A+B + the `hcompat` transposition are all in place — sole residual = the `hcompat` sorry (L4219).
- **`TensorObjSubstrate.lean`** — GREEN, 2 bare sorries:
  - L4219 — K1 `hcompat` (the ACTIVE target; transitive sorryAx to seed-1).
  - L734 `exists_tensorObj_inverse` — import-cycle-deferred terminal (never close here; see deferrals).
- **`SliceTransport.lean` / `DualInverse.lean`** — sorry-free (DUAL route CLOSED iter-015).
- Project-wide bare sorries: **2** (1 active K1 `hcompat` + 1 deferred terminal).

## Gate status (iter-022)

- **blueprint-reviewer: SKIPPED with rationale** (see `iter/iter-022/plan.md`). The K1 chapter node
  `lem:pullback_tensor_map_isiso_open_immersion` cleared the HARD GATE at bpr021 (complete+correct,
  pin resolves, no must-fix) and tos021 re-confirmed the residual `hcompat` is *exactly* the chapter's
  stated mate-compatibility obligation. NO blueprint chapter is edited this iter (the prover guidance lives
  in PROGRESS + `analogies/recon022.md`), so the gate remains satisfied. The tos021 MINOR (port the
  reduction telescope into the chapter body) is non-blocking → review-phase / next blueprint touch.
- **mathlib-analogist recon022 (api-alignment): ALIGN_WITH_MATHLIB.** The iter-021 hand-built `e`+`hcompat`
  reconciliation is reinventing the Mathlib carrier `Adjunction.IsMonoidal`. `hcompat` ⟺ `hadj.IsMonoidal`;
  NO Mathlib gap (full scaffolding present: `Adjunction.IsMonoidal`, mate (op)lax defs, the `≃` uniqueness
  `laxMonoidalEquivOplaxMonoidal`, δ-side lemmas). Smallest remaining ingredient = the project-side instance.
  Persistent recipe: `analogies/recon022.md`.
- **strategy-critic sc022: SOUND** — independently verified every named Mathlib decl against source
  (`Adjunction.IsMonoidal` Functor.lean:952, `laxMonoidalEquivOplaxMonoidal`+`right_inv` :1070,
  `leftAdjointOplaxMonoidal.δ` :1011, `μIso`⇒`IsIso δ` :389/396, `restrictScalarsMonoidalOfBijective`).
  Note: the sectionwise close may need multi-line `simp`/rewriting after the `homEquiv` transpose, NOT a
  bare `rfl` (cf. Mathlib mate proofs Functor.lean:1020–1051).
- **progress-critic pc022: STUCK** — its must-fix corrective ("Mathlib analogy consult BEFORE/INSTEAD OF
  another prover round") was EXECUTED this iter (recon022, in parallel); its escalation branch ("if NO
  Mathlib path → user escalation") does NOT fire — recon022 found a concrete project-side path. The
  post-consult route (build `hadj.IsMonoidal` via the Mathlib carrier) is a genuine technique change, not
  the reworded mathlib-build re-dispatch the critic (correctly) blocked. Rebuttal-with-action in the sidecar.

## Current Objectives

1. **`AlgebraicJacobian/Picard/TensorObjSubstrate.lean`** — **seed-1 D4′ brick K1 — close `hcompat`,
   `prove` mode.** Fill the SOLE open sorry at L4219 (inside `hcompat`, inside `hδ`, inside
   `pullbackTensorMap_isIso_of_isOpenImmersion`, L4139). Closing it makes `chart_isIso` +
   `pullbackTensorIsoOfLocallyTrivial` (seed-1) axiom-clean — NO other edits needed.
   Blueprint: `chapters/Picard_TensorObjSubstrate.tex` — `lem:pullback_tensor_map_isiso_open_immersion`
   (K1, ~L3651). Concrete recipe: `analogies/recon022.md` (mathlib-analogist, this iter).

   **The goal at L4219** (after the `rw` chain at L4207 already fired) is the presheaf-level
   mate-compatibility equation reducing to: `(leftAdjointOplaxMonoidal hadj).δ M.val N.val = μIsoβ.inv`,
   i.e. the project lax structure on `pushforward φ'` is the `hadj`-mate of `pushforward β`'s STRONG
   structure. **recon022 verdict: this is EXACTLY `hadj.IsMonoidal`** (the Mathlib carrier
   `Adjunction.IsMonoidal`). The iter-021 hand-built `e`+manual reconciliation is reinventing it.

   **RECIPE (recon022 + sc022, all decls verified against Mathlib source this iter):**
   - **Step 1 — the ONE irreducible step: build `hadj.IsMonoidal`.** `hadj : pushforward β ⊣ pushforward φ'`
     (already in scope, L4162). `pushforward β` is STRONG monoidal (oplax) via the `μIsoβ` you already built
     (`restrictScalarsMonoidalOfBijective β' hβ`); `pushforward φ'` is lax via `presheafPushforwardLaxMonoidal φ'`.
     Provide `haveI : hadj.IsMonoidal` (in-proof; promote to a top-level instance ONLY if cleaner/reused —
     see Coverage). Prove its two fields (`leftAdjoint_ε`, `leftAdjoint_μ`) **sectionwise**, the
     `ModuleCat/Monoidal/Adjunction.lean` idiom: transpose by `(hadj.homEquiv _ _).injective`, then close the
     resulting `PresheafOfModules`-hom equation by `tensor_ext` + sectionwise `ModuleCat` check.
     `[verified] Adjunction.IsMonoidal` (Mathlib `CategoryTheory/Monoidal/Functor.lean:952`, exactly two fields).
     ⚠ **sc022 caution:** the field close will likely need multi-line `simp`/rewriting after the transpose,
     NOT a bare `tensor_ext (fun _ _ ↦ rfl)` — study Mathlib's analogous mate proofs at `Functor.lean:1020–1051`
     for the post-transpose rewrite shape.
   - **Step 2 — collapse `hcompat`.** With `[hadj.IsMonoidal]` in scope, the project lax on `pushforward φ'`
     IS `rightAdjointLaxMonoidal hadj` of `pushforward β`'s strong-oplax, so by the Equiv `right_inv`,
     `leftAdjointOplaxMonoidal hadj = ` (the strong oplax on `pushforward β`), whose `.δ M N = μIsoβ.inv`
     via `Functor.Monoidal.μIso`/`μIso_inv`. `[verified] Adjunction.laxMonoidalEquivOplaxMonoidal` +
     `.right_inv` (`Functor.lean:1070`); `[verified] Functor.Monoidal.μIso`/`δ` (`:389/396`).
     *Alternative direct route:* rewrite `Adjunction.leftAdjointOplaxMonoidal_δ` with
     `Adjunction.IsMonoidal.leftAdjoint_μ`, then `Equiv.symm_apply_apply` collapses to the strong δ.
   - **δ-side lemmas now live** (available once `[hadj.IsMonoidal]`), if needed for the transpose:
     `[verified] Adjunction.unit_app_tensor_comp_map_δ` (`:973`),
     `[verified] Adjunction.map_μ_comp_counit_app_tensor` (`:983`) — the δ-twins of the η-side
     `Adjunction.unit_app_unit_comp_map_η` the project already uses in `presheafUnit_comp_map_eta` (L1476).
   - **DO NOT** retry the functor-level `Functor.Monoidal.transport` route (carrier diamond; L4159–4171 comment).
   - **Bar:** close the `hcompat` sorry → K1 axiom-clean → seed-1 `pullbackTensorIsoOfLocallyTrivial` axiom-clean.
     Partial progress (`hadj.IsMonoidal` fields stated as `have`s, one field closed) is committable (GREEN only).
   - **Coverage:** prefer the in-proof `haveI : hadj.IsMonoidal` (no new top-level decl → no coverage debt).
     If a top-level instance/lemma is genuinely cleaner (it IS reusable — DualInverse.lean uses the same
     `pushforwardPushforwardAdj`+`restrictScalarsMonoidalOfBijective` pair), create it and list it under
     `## Needs blueprint entry` with `\uses{lem:tensorobj_restrict_iso}` + the pushforward-adjunction deps.
   - **Reversal signal (genuine, not a checkbox):** if Step-1's field equation does NOT close after the
     sectionwise transpose — i.e. `presheafPushforwardLaxMonoidal β`'s underlying μ is NOT defeq to
     `restrictScalarsMonoidalOfBijective β'`'s μ — STOP, report the exact field goal state, and flag that the
     two lax structures on `pushforward β` genuinely differ (would need a `μ`-component identity lemma first).
     Do NOT fall back to the `transport` route or hand-build a fresh `e`.

(`exists_tensorObj_inverse` (L734) stays deferred this iter — import-cycle; closes next phase via the
refactor-MOVE downstream of DualInverse. Seed-3 consumer `RelPicFunctor.lean` stays deferred until seed-1
+ the terminal close land.)

## Standing deferrals

- **Terminal `exists_tensorObj_inverse` (L734):** import-cycle-deferred; closes NEXT phase by a
  `refactor`-MOVE of the decl to a file downstream of `DualInverse.lean` (where `dual_isLocallyTrivial`
  is visible) + repoint `RelPicFunctor.lean`'s import (sole consumer — RE-GREP to confirm before the MOVE).
  Then a prover closes the gluing proof (bridges B+C done; A = `homOfLocalCompat` descent).
- **Scaffold target (decl does not exist yet — NOT fill-sorry):** `PicSharp.addCommGroup_via_tensorObj`
  (seed 3, `RelPicFunctor.lean`); gated on seed-1 (map_add ← comparison iso) + the terminal close.
  The OnProduct-specialisation `pullback_tensorObj_iso` (`lem:pullback_compatible_with_tensorobj`) lands
  as an immediate downstream specialisation of seed-1.
- **Import architecture (in scope):** `LineBundlePullback → TensorObjSubstrate → SliceTransport →
  DualInverse`; `TensorObjSubstrate → RelPicFunctor`. The terminal MOVE adds
  `RelPicFunctor → {TensorObjInverse} → DualInverse` (acyclic).
- **AJC Lan-decomposition block** (`extendScalars`/`pullback0`/`pullbackLanDecomposition`) — NOT ported
  (confirmed dead code; not in any seed cone).
- **Blueprint K1 proof-body telescope (tos021 MINOR, non-blocking):** port the L4202–4218 `homEquiv`-
  transposition + `unit_leftAdjointUniq_hom_app` reduction (and now the recon022 `Adjunction.IsMonoidal`
  recipe) into the chapter K1 proof body, so the chapter — not a Lean comment — guides the close. Do at
  the next blueprint-writer touch.
- **Doc-refresh debt (non-blocking):** stale headers/in-proof comments — `TensorObjSubstrate.lean`
  L44/L46/L158–159/L4014 + the abandoned-`transport` comment L4159–4171 (describes a superseded route);
  `DualInverse.lean` L44/L238; `Vestigial.lean`. Fix opportunistically when next touched.
- **Coverage / file-split debt (deferred phase):** bulk ~105 `lean_aux` decls remain (scheduled
  `Coverage + file-split` phase); no NEW coverage debt this iter (K1 task result: no new top-level decls).
  Split `TensorObjSubstrate.lean` (>3600 LOC) deferred until the active seed-1 lane lands.
- **Extraction note:** module names, file paths, blueprint labels unchanged from the parent so proved
  seeds merge back cleanly. Sibling extracts (Cech-Cohomology, Quot-Foundations) cover disjoint cones.
