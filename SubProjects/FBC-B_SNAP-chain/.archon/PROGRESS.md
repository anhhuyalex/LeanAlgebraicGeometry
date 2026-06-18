# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the seed declarations + kernel-only axioms.**
Two Čech-independent (i=0) legs split from the parent *Quot-Foundations* `thm:fga_pic_representability`
cone (full arc in STRATEGY.md):

- **FBC-B** — flat base change of the degree-0 pushforward (`thm:flat_base_change_pushforward`), via the
  CONCRETE-tilde equalizer chain. Per-chart iso (a) DONE sorry-free; restriction-naturality (b) reduced
  to its lone crux sub-lemma `pullback_spec_tilde_iso_ring_square_natural` (PARTIAL: 4-step transpose
  reduction validated iter-004; mechanical tail remains).
- **SNAP** — the section graded ring `Γ_*(X,L)` (`lem:sectionGradedRing_gcommSemiring`). `LocalizedMonoidal`
  foundation DONE axiom-clean (iter-004); 6 residual sorries gated on the 4 bridge lemmas, whose blueprint
  was re-typed iter-005 (object-iso-conjugated; the gate cleared via `snap-gate`).

## Current Objectives

TWO lanes, different files (no edit race). Both cleared the HARD GATE this iter. progress-critic `pc005`:
FBC CHURNING → corrective = dispatch the crux prover NOW (route validated, lemmas located, no more
prep); SNAP UNCLEAR/positive → proceed. blueprint-reviewer `br005` flagged the SNAP bridge lemmas as
ill-typed/under-specified → writer `snap-bridge-mu` re-typed them → scoped re-gate `snap-gate` PASS
(complete+correct).

1. **`AlgebraicJacobian/Cohomology/FlatBaseChange.lean`** — close the FBC (b) crux.
   - **PROVE** `AlgebraicGeometry.pullback_spec_tilde_iso_ring_square_natural`
     (`lem:pullback_spec_tilde_iso_ring_square_natural`): the lone residual sorry. **Attempt the body;
     recipe:** `task_results/AlgebraicJacobian_Cohomology_FlatBaseChange.lean.md` (iter-004) + the
     enriched blueprint proof. Route: the eq of isos reduces to the `.hom` morphism eq; rearrange the
     trailing inverse; the goal is a map OUT of `L_tot.obj M` (composite left adjoint
     `tilde ⋙ pullback(Spec inclR) ⋙ pullback(Spec ρB)`), so peel the 3 adjunctions in turn (each
     cancels a common unit prefix), landing in `ModuleCat ↑R`; there each `pullback_spec_tilde_iso` leg
     transposes to `gammaPushforwardNatIso` via `unit_conjugateEquiv` [verified]; the geometric
     comparison via `conjugateEquiv_pullbackComp_inv` [verified]; the reassociation via
     `ModuleCat.extendScalarsComp` [verified]; all identity-on-elements ⇒ coincide by the pointwise-`rfl`
     naturality of `gammaPushforwardNatIso`. All bricks (b1/geometric/b2-alg) already proved sorry-free.
   - **Do NOT touch** the dead mate decls (`base_change_mate_*`, `pushforward_base_change_mate_*`) or the
     seeds (`affineBaseChange_pushforward_iso`, `flatBaseChange_pushforward_isIso`) — those stay as-is
     (the mate apparatus is scheduled for a dedicated excision iter; see STRATEGY).
   - Blueprint: `chapters/Cohomology_FlatBaseChange.tex`
     (`lem:pullback_spec_tilde_iso_ring_square_natural` — proof block now carries the 4-step route).
     [prover-mode: prove]

2. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — build the bridge layer + close the coherences.
   The bridge blueprint was re-typed this iter (writer `snap-bridge-mu`); follow `sec:sgr_localized_monoidal`.
   Work bottom-up; go as far as possible, hand off a precise decomposition if blocked.
   - **Build** `tensorObjLocalizedIso F G : tensorObj F G ≅ F ⊗_loc G` (`def:tensorObjLocalizedIso`) =
     `μ⁻¹ ≫ (counit_F ⊗_loc counit_G)`, where `μ` is Mathlib `Localization.Monoidal.μ` [verified] and the
     counit is `sheafificationCounitIso`. This is the identification iso the bridges thread.
   - **Prove the 4 bridge lemmas** (`lem:tensorObjAssoc_eq_localizedAssociator`,
     `lem:tensorBraiding_eq_localizedBraiding`, `lem:tensorObjUnitor_eq_localized`,
     `lem:tensorObjRightUnitor_eq_localized`) in their **object-iso-CONJUGATED commuting-square form**
     (NOT bare `α = α^loc` — that is a type error since `⊗_loc` is not defeq to `tensorObj`). Expand both
     sides via the Mathlib component formulas `Localization.Monoidal.{associator_hom_app,
     leftUnitor_hom_app, rightUnitor_hom_app, braidingNatIso_hom_app, μ_natural_left, μ_natural_right}`
     [verified by writer]; both reduce to the sheafified presheaf coherence + μ-naturality.
   - **Close the 5 coherences** `tensorPowAdd_{rightUnit,braiding,assoc}` (succ steps),
     `sectionMul_assoc_core`, `sectionsMul_mul_assoc` via the Mathlib laws (`MonoidalCategory.pentagon`/
     `triangle`, `BraidedCategory.hexagon`) transported through the bridges + the existing `tensorPowAdd`
     inductions. Once these land, `instGMonoid/GSemiring/GCommSemiring` + `sectionGradedRing_gcommSemiring`
     become axiom-clean.
   - Blueprint: `chapters/Picard_SectionGradedRing.tex` (`sec:sgr_localized_monoidal`:
     `def:tensorObjLocalizedIso`, `lem:localizationMonoidal_mu_mathlib`, the 4 bridges, the coherence
     sketches). [prover-mode: mathlib-build]

## Queued — NEXT iters

- **FBC mate excision (dedicated cleanup iter)** — delete the COMPILE-DEAD mate apparatus
  (`base_change_mate_{domain,codomain}_read`/`_gstar_transpose`/`_section_identity`/`_generator_trace`/
  `pushforward_base_change_mate_*`) + dead `/-!` planning blocks + dead `set_option`s; sync the blueprint
  `\uses` web (delete `lem:pushforward_base_change_mate_*`/`_domain_read`/`_codomain_read` blocks). KEEP
  `base_change_mate_regroupEquiv` + `base_change_map_affine_local`. Run via `refactor`, NOT alongside an
  FBC prover (file-stability). Clears the recurring lean-auditor false-doc must-fix + enables file-split.
- **FBC Global assembly** `baseChange_sheafConditionFork_tensorIso` (FlatBaseChangeGlobal.lean): once (b)
  lands + `TensorProduct.piRight` (c), rewrite as the (a)+(b)+(c)→(d) assembly + ADD `[IsSeparated X]`/
  `[Fintype ι]`/`[F.IsQuasicoherent]` hyps + `baseChangeEqLocusToPullbackGamma` + `baseChangeGammaPullbackEquiv`.
- **FBC separated → MV → bridge → goal**: discharge both seeds. Bridge reverse gated on qcqs-pushforward-QC
  (Stacks 01XJ) — verify Mathlib / `mathlib-build` first (STRATEGY Open Q).
- **FBC file-split for parallelism** (user standing directive) — after mate excision.
- **SNAP** `sectionGradedModule_gmodule` — after the coherences close.

## Standing notes

- **Prover model:** `opus`.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf. FlatBaseChangeGlobal imports
  FlatBaseChange (one-way); FlatBaseChange imports RegroupHelper. SectionGradedRing standalone.
- **Cold-build:** validate with real `lake build AlgebraicJacobian.Cohomology.FlatBaseChange` /
  `...Picard.SectionGradedRing` (LSP hides `(kernel) deterministic timeout`); never add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **SNAP bridge hazard:** localized `⊗_loc` is NOT defeq to hand-built `tensorObj` → bridges are
  object-iso-conjugated via `tensorObjLocalizedIso` (Option B); a bare `α = α^loc` is a type error.
- **FBC do-not-retry:** the mate keystone is ABANDONED; per-affine base change uses concrete
  `pullback_spec_tilde_iso` (NOT abstract affineBC). `lem:pushforward_base_change_mate_sections_direct`
  `\lean{}` pin REMOVED iter-005 — never re-add.
- **Merge-back discipline:** never rename kept decls/labels; never add `\leanok` by hand. No declarations
  are currently protected — chain decls may be re-signed to add missing hyps.
