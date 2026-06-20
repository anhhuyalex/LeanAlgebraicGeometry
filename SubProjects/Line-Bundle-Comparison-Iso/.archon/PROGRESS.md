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

- `lem:pullback_tensor_iso_loctriv` — `pullbackTensorIsoOfLocallyTrivial` (D4′; body CLOSED; transitively
  sorry ONLY via K1 `pushforward_lax_mu_comparison_lhs_tmul`. η CLOSED iter-028, μ RHS + comparison-assembly
  CLOSED iter-029, `pushforward_mu_appIso_collapse` CLOSED iter-031. **SOLE residual = `lhs_tmul`, the
  iter-033 SOLO lane.**).
- `lem:dual_isLocallyTrivial` — `dual_isLocallyTrivial` (DUAL route) — **DELIVERED**.
- `thm:rel_pic_addcommgroup_via_tensorobj` — `PicSharp.addCommGroup_via_tensorObj` (consumer; SCAFFOLD,
  gated on seed-1 + terminal).

## Build state (iter-033 plan turn)

- **Import chain GREEN** since iter-031; iter-032 +0/−0 (no regression). Tree builds green-mod-sorry.
- iter-033 plan-phase edits (all committed pre-prover, root green): blueprint effort-break of
  `lem:trivialisation_restrict_compat` (5 squares + telescope) + blueprint-clean; comment/docstring
  cleanup refactor (7 edits across DualInverse/Vestigial/LineBundlePullback/TensorObjInverse, zero new
  sorries, root untouched).
- **True leaf-sorry disk state (3 sorries, unchanged):**
  - `TensorObjSubstrate.lean:4362` — `pushforward_lax_mu_comparison_lhs_tmul` (seed-1's sole residual,
    import-chain ROOT). **This iter's SOLO lane.**
  - `TensorObjInverse.lean:~244` — `trivialisation_restrict_compat` (now effort-broken; **prover
    DEFERRED to iter-034** — prove S2 template first).
  - `TensorObjInverse.lean:~492` — cocycle `exists_tensorObj_inverse` hedge (gated on the above).

## iter-033 decision — run the CHURNING `lhs_tmul` lane SOLO (single corrective test); effort-break the STUCK Terminal (done, not a prover lane)

**pc033: STUCK×2, dispatch=OK.** Both correctives executed this iter:

- **Route A `lhs_tmul` (STUCK, 4-iter `hadj'`-let wall):** the iter-033 SOLO prover lane IS the
  pc033-endorsed single corrective test — the FIRST prover shot with the iter-032-expanded blueprint
  (per-section comparison form; explicit step 1 = identify `hadj'` with `pushforwardPushforwardAdjunction`
  so the unit value lemma keys). Runs ALONE (no downstream co-dispatch → no iter-029 build-race).
  **pc033 must-fix: if `lhs_tmul` does NOT close this iter → iter-034 escalates to user immediately
  (no further blueprint/helper cycles on Route A).**
- **Route B Terminal `trivialisation_restrict_compat` (STUCK, 1st green window iter-032 closed only S1):**
  pc033 confirms the blueprint EFFORT-BREAK is the correct corrective (NOT escalation/pivot — the S1
  closure proves the sub-squares are individually tractable). EXECUTED this iter: effort-breaker split
  the lemma into 5 named per-constituent restriction-naturality squares (S2–S4c, incl. the
  blueprint-OMITTED `uι` 5th leg) + a telescope (target effort 6409→3928); bp033 verifies all five
  complete+correct. **Prover deferred to iter-034 (prove S2 `tensorObj_restrict_iso` square FIRST as the
  structural template). pc033 must-fix: iter-034 MUST dispatch S2 — a 2nd prover deferral crosses the
  persistent-deferral threshold.**

Why not co-run Terminal + lhs_tmul provers: import chain Terminal→DualInverse→Substrate; a root-churn
invalidates Terminal builds (iter-029 race, ARCHON_MEMORY). Terminal isn't prover-ready anyway (the 5
squares need Lean scaffolding first, iter-034).

Cheapest reversal: if the `lhs_tmul` lane leaves the root RED, sync_leanok re-strips markers — prover
instructed to keep green-mod-sorry. The effort-break + cleanup are banked regardless (blueprint/comment
only).

## Gate status (iter-033)

- **blueprint-reviewer bp033: HARD GATE for the `lhs_tmul` lane CLEARED.** `Picard_TensorObjSubstrate.tex`
  complete:true + correct:true, 0 must-fix; bp032's `correct:partial` (lhs_tmul statement-drift) is
  cleared — the per-section comparison statement now matches the Lean signature + consumer
  (`hom_ext` at L4410). The 5 new squares all complete+correct (feed iter-034). leandag 0
  unknown_uses/conflicts; doctor 0 broken refs / 0 axioms.
- **progress-critic pc033: STUCK×2, dispatch=OK** (both correctives executed/planned, see above).
- **strategy-critic: SKIPPED** — no route swap; STRATEGY.md edited only for the Terminal row estimate
  refresh + the tactical 5-square decomposition note (within the unchanged SOUND Terminal route);
  goal/routes identical to the sc024-SOUND state. (Rationale in `iter/iter-033/plan.md`.)

## Current Objectives

1. **`AlgebraicJacobian/Picard/TensorObjSubstrate.lean`** — close `pushforward_lax_mu_comparison_lhs_tmul`
   (decl L4303, **sorry@L4362**), seed-1's sole residual. **SOLO lane — do NOT touch any other file**
   (root must stay green-mod-sorry for the downstream chain). Build with `lake build`/LSP.
   Blueprint: `chapters/Picard_TensorObjSubstrate.tex` (`lem:pushforward_lax_mu_comparison_lhs_tmul`,
   reworded iter-032 to the per-section comparison form). `[prover-mode: prove]`
   - **The 4-iter wall + its concrete next step (blueprint step 1 + task_pending):** the opaque mate-μ
     is already reduced (iter-029/031) to the explicit 3-leg form `unit ≫ G.map(δGβ ≫ counit⊗counit)`,
     split sectionwise. The residual is the sectionwise value on `m⊗ₜn`. **Un-`let` `hadj'` (or `change`
     it to the `pushforwardPushforwardAdjunction` form) so `pushforwardPushforwardAdj_unit_app_app_apply`
     keys on the unit leg** — this is the wall every prior iter hit. Then: δGβ leg →
     `Functor.OplaxMonoidal.comp_δ` + `restrictScalars_μ_app_tmul` /
     `forget₂_restrictScalars_μ_hom_tmul`; counit pair → bijective `f.appIso`. All via `erw` (no whnf),
     mirroring the PROVED `pushforwardComp_lax_μ` (L2197) for a MATE LHS. Routing through
     `hadj'.IsMonoidal` is CIRCULAR (DEAD — ARCHON_MEMORY). Recipe also in `task_pending.md` (Seed 1).
   - Attempt the body with this recipe; leave partial progress (compiling sub-goals / the un-`let`
     `change` that finally keys the unit lemma) if stuck. **This is the final automated attempt — if it
     does not close, the route escalates to the user iter-034 (pc033 mandate).**

(Terminal `trivialisation_restrict_compat` prover DEFERRED to iter-034: effort-broken into 5 squares
this iter; iter-034 scaffolds them in `TensorObjInverse.lean` + proves S2 first as the template. Seed-3
`RelPicFunctor` BLOCKED on seed-1 + terminal.)

## Standing deferrals

- **Terminal route iter-034 (pc033 MUST-DISPATCH):** scaffold the 5 effort-broken squares
  (`tensorObj_restrict_iso_restrict_compat` (S2), `dual_restrict_iso_dualIsoOfIso_restrict_compat` (S3),
  `dual_unit_iso_restrict_compat` (S4a), `tensorObj_unit_iso_restrict_compat` (S4b),
  `trivialisation_uIota_restrict_compat` (S4c)) in `TensorObjInverse.lean`, then prove **S2 first** as
  the structural template (the 4-step chart-chase + ρ-threading; effort≈1502, the largest — re-break if
  it stalls). The other four are short once S2's pattern exists. Then the telescope closes
  `trivialisation_restrict_compat`, which fires the cocycle `| sorry` strip. The root will be settled
  after this iter's `lhs_tmul` lane (run the Terminal lane SOLO or co-dispatch only if root stays green).
- **Scaffold target (decl does not exist yet — NOT fill-sorry):** `PicSharp.addCommGroup_via_tensorObj`
  (seed 3, `RelPicFunctor.lean`); gated on seed-1 (K1) + the terminal. Stays BLOCKED.
- **Coverage / file-split debt (deferred phase):** ~106 `lean_aux` decls unmatched (bulk pre-existing,
  all `lean_aux` — no wire-up owed per bp033); the 5 new square `\lean{}` hints are `unmatched_lean`
  until iter-034 scaffolds them (expected, tex-precedes-Lean); `deltaConjOfMuComparison` +
  `linearEndo_apply_comm` are `private`. `TensorObjSubstrate.lean` (>3600 LOC) split scheduled. Defer
  until the active seed lanes land.
- **AJC Lan-decomposition block** (`extendScalars`/`pullback0`/`pullbackLanDecomposition`) — NOT ported
  (dead code; not in any seed cone).
- **Extraction note:** module names, file paths, blueprint labels unchanged from the parent so proved
  seeds merge back cleanly. Sibling extracts (Cech-Cohomology, Quot-Foundations) cover disjoint cones.
