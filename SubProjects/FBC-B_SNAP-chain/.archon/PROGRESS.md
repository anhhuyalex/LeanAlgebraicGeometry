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
Two Čech-independent (i=0) legs split from the parent *Quot-Foundations*
`thm:fga_pic_representability` cone (full arc in STRATEGY.md):

- **FBC-B** — flat base change of the degree-0 pushforward (`thm:flat_base_change_pushforward`), via
  the CONCRETE-tilde equalizer chain. Foundation sorry-free; both ring-square mate legs closed
  (iter-018). The glue `pullback_spec_tilde_iso_ring_square_mate_glue` is the last frontier piece.
  **iter-026 pivot (pc026-endorsed structural pivot, NOT another helper):** the carrier-bearing
  natTrans route is OVER-BUDGET (elaborates @800k-hb, kernel-bombs @200k); replace it with the
  ABSTRACT carrier-free `ring_square_cocycle` (mathlib-analogist `analogies/fbc-glue-carrier-whnf.md`),
  close the glue by a single `exact` binding heavy carriers to metavars (kernel-light).
- **SNAP** — the section graded ring `Γ_*(X,L)` (`lem:sectionGradedRing_gcommSemiring`). **iter-026:
  build RESTORED to green** (iter-025's 3-concurrent-writer Option-A re-base left it RED; reverted to the
  iter-021 green monolith + removed the `SectionGradedRingLocalized` import from root). Associator wall
  intact (6 sorries). Option-A re-base is RE-DESIGNED for iter-027 as a SKELETON refactor (re-base 5 defs
  + `sorry` the broken coherences → green-with-sorries) + a prover fill — NOT a monolithic refactor.

## Current Objectives

ONE prover lane this iter. (SNAP build was just restored in the plan phase; its Option-A re-base is a
plan-phase REFACTOR for iter-027, NOT a prover task — do not add it here.)

1. **`Cohomology/FlatBaseChange.lean`** — author + prove the abstract `ring_square_cocycle`
   (blueprint `lem:ring_square_cocycle` @bp L2807, `\lean{AlgebraicGeometry.ring_square_cocycle}`),
   then close the glue `sorry` `pullback_spec_tilde_iso_ring_square_mate_glue` (body `sorry` @L2219 —
   blueprint `lem:pullback_spec_tilde_iso_ring_square_mate_glue` @bp L2879) by a SINGLE `exact`, and
   DELETE the obsolete `ring_square_glue_natTrans` (typed `sorry` @L2008). Closing the glue transitively
   closes the crux (`…_ring_square_natural` already `exact … mate_glue …`). Blueprint:
   `chapters/Cohomology_FlatBaseChange.tex`. [prover-mode: prove]
   - **WHY THIS, NOT THE natTrans TELESCOPE (pc024/pc025/pc026 — the iter-026 structural pivot).** The
     concrete-whisker `ring_square_glue_natTrans` whiskers over `tilde.functor`/`extendScalars`; its
     statement-seam AND `.app M` fold both whnf the heavy carrier → `(kernel) deterministic timeout
     @200000hb`. The term is WELL-TYPED (elaborates @800000hb) — over-budget, not ill-typed; and
     `maxHeartbeats 1e6` is FORBIDDEN. The mathlib-analogist escape (`analogies/fbc-glue-carrier-whnf.md`,
     blueprint-gate-cleared br025): prove the coherence as an ABSTRACT mate cocycle — NO `tilde`,
     `pullback (Spec _)`, or `extendScalars` anywhere in the statement OR proof — so no whnf can ever
     fire; then instantiate the heavy glue goal with one `exact`, binding the carriers to metavars.
   - **`ring_square_cocycle` statement (carrier-free).** Fix abstract categories + four columns of
     vertically-composable adjunctions arranged as the two composite-left-adjoint legs of a commuting
     square: geometric leg `L_geom = T ⋙ P` (right adj `R_geom`), algebraic leg `L_alg = E ⋙ T'` (right
     adj `R_alg`), a base-comparison family `γ` (abstract `gammaPushforwardNatIso`), and the per-leg
     comparison transformations. Hypotheses (each an abstract form of an ALREADY-CLOSED concrete lemma):
     (i) per-leg unit triangle (`pullback_spec_tilde_iso_inv_unit_triangle`), (ii) geometric-leg mate eqn
     (`ring_square_glue_geom_leg_nat`, CLOSED @L1836), (iii) algebraic-leg mate eqn
     (`ring_square_glue_alg_leg_nat`, CLOSED @L1867), (iv) composition coherence
     (`gammaPushforwardNatIso_comp`, CLOSED @L839). Conclusion = the two legs' iterated mates agree as a
     `≪≫`-telescope of conjugate/mate isos. **SHAPE the conclusion to the EXISTING glue goal** (the glue
     statement already typechecks @L2019) so the final `exact` unifies — the blueprint conclusion uses
     `(⋯)` ellipses for the telescope shape ON PURPOSE; recover the exact shape from the glue's type.
   - **`ring_square_cocycle` proof (pure mate calculus).** Reduce to the underlying inverse-natTrans
     equality; transpose each leg through its composite adjunctions via `conjugateEquiv_symm_comp`
     (composite inverse-conjugate telescopes into per-edge conjugates); recognise each edge's iterated
     single-step mate as a conjugate via `iterated_mateEquiv_conjugateEquiv` (recover the NatTrans through
     `TwoSquare.equivNatTrans` / `.natTrans`); fuse the per-leg `TwoSquare` pastings via
     `mateEquiv_vcomp` / `mateEquiv_hcomp`; discharge the 4 legs by hyps (i)–(iv); re-upgrade to isos via
     `conjugateIsoEquiv` (`conjugateIsoEquiv_apply_hom`). NO `.app`/`congrArg(Iso.app ·)`/`simp`/`rw`
     over a carrier anywhere.
   - **The fold.** Close the glue with one
     `exact ring_square_cocycle … (pullback_spec_tilde_iso_inv_unit_triangle …) (ring_square_glue_geom_leg_nat …) (ring_square_glue_alg_leg_nat …) (gammaPushforwardNatIso_comp …)`
     — the heavy carriers (`tilde`, `pullback (Spec ι/ρ)`, `extendScalars`) bind to metavars by
     unification, so the kernel never reduces them.
   - **VERIFY before building** (Mathlib bumps rename; br025 #checked these iter-025 — re-confirm):
     `mateEquiv_vcomp`, `mateEquiv_hcomp`, `conjugateEquiv_symm_comp`,
     `iterated_mateEquiv_conjugateEquiv`, `conjugateIsoEquiv`, `conjugateIsoEquiv_apply_hom`
     (all `…CategoryTheory.Adjunction.Mates`). If a name mismatches, STOP + surface.
   - **HARD CADENCE (pc026 must-fix):** cold-build (`lake build
     AlgebraicJacobian.Cohomology.FlatBaseChange`) after the cocycle STATEMENT compiles, again after its
     proof closes, again after the fold. If the final `exact` fails to unify (cocycle telescope shape ≠
     glue goal), DO NOT churn: leave the glue a typed `sorry`, report the exact unification mismatch (both
     types), so the planner re-shapes the cocycle statement next iter. A botched statement that fails to
     unify is worse than no statement (pc025). If the cocycle's OWN proof kernel-bombs, the carrier-free
     invariant was violated somewhere — report which term reintroduced a carrier.
   - Do NOT touch the 3 COMPILE-DEAD mate-apparatus sorries (@L2511/L2692/L2714); no `set_option` /
     comment cleanup (deferred to the mate-excision refactor). File MUST end cold-green.

## In-plan-phase this iter (no prover lane) — DONE

- **SNAP `SectionGradedRing.lean` — `snap-restore-green` refactor: COMPLETE, cold-green (firsthand:
  `lake build …SectionGradedRing` 2441 jobs, exit 0).** iter-025 left the file RED (half-migrated
  Option-A from 3 concurrent killed refactor agents). Reverted to the iter-021 green monolith
  (`SectionGradedRing.lean.presplit-backup`) + removed the `import …SectionGradedRingLocalized` line
  from root `AlgebraicJacobian.lean` (the monolith re-defines those symbols inline → avoids
  duplicate-declaration errors). 6 frontier sorries (iter-021 baseline). The broken half-migration is
  preserved at `SectionGradedRing.lean.optiona-partial-broken-iter025`; `SectionGradedRingLocalized.lean`
  stays on disk, unimported.

## Queued — NEXT iters

- **SNAP Option-A `⊗_loc` re-base — RE-DESIGNED as SKELETON + FILL (iter-027, pc026 must-fix: SNAP MUST
  get a real lane next iter).** ROOT CAUSE of 4 failed Option-A iters = the refactor agent was asked to
  re-base 5 defs AND re-prove ~10 coherences in one budget (too big → timeout-kill), iter-025 made it
  worse with 3 CONCURRENT writers to one file. FIX = decompose:
  (1) ONE refactor agent (NO concurrency), green-preserving: re-base the 5 structural defs (`tensorObj`,
  `tensorObjUnitIso`, `tensorBraiding`, `tensorObjRightUnitor`, `tensorObjAssoc`) onto
  `MonoidalCategory.tensorObj/leftUnitor/braiding/rightUnitor/associator (C := modulesLocalizedMonoidal X)`,
  and insert `sorry` at EVERY downstream coherence proof that breaks (the refactor agent's designed
  behavior — "inserts sorry at broken sites, never fills"). The bridge `tensorObjAssoc_eq_localizedAssociator`
  becomes `rfl` ⇒ the wall sorry `tensorObjAssoc_hK_lhs_native` is DELETED, not proved. Commit
  GREEN-WITH-SORRIES (cold-build the file AND root). (2) A PROVER lane then fills the (now `rfl`/easy)
  coherence sorries via Mathlib pentagon/triangle/hexagon + `Functor.Monoidal (L')` lax fields.
  **sc022/sc024 WATCH:** if ≥2 re-proved coherences re-summon the localized↔presheaf μ-boundary (the
  original wall, one layer down) → Option-A merely moved the wall → escalate to single-global-instance
  (give `X.Modules` the localized instance directly). DELETE-AFTER-CONFIRM the ~900L μ-keystone bridge
  machinery only once the coherences re-prove green.
- **FBC mate excision + cleanup (dedicated `refactor` iter):** delete the COMPILE-DEAD mate apparatus
  (`base_change_mate_*`, `pushforward_base_change_mate_*`, `_sections_direct` gap node, dead `/-!`
  blocks, the 3 dead sorries @L2511/L2692/L2714); after the cocycle lands, also delete the now-orphaned
  telescope scaffolding (`ring_square_glue_whiskerRight_lift`, `…whiskerLeft_lift`, `…pst_iterated_mate`
  + their blueprint blocks — br025 isolated-node triage). FIX the latent `set_option maxHeartbeats`
  placement bug (scopes to comments not theorems); strip stale iter-NNN comments. KEEP
  `base_change_mate_regroupEquiv` + `base_change_map_affine_local`. Sync blueprint `\uses` same iter.
- **FBC downstream (after glue + crux) — PARALLELISE (sc024).** Dispatch concurrently: 2 seeds
  (`affineBaseChange_pushforward_iso`, `flatBaseChange_pushforward_isIso` region) via the concrete chain;
  the Stacks-01XJ build (ASSEMBLY-ONLY — its analytic core
  `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` IS in Mathlib; only QC-preservation packaging is
  project-side, `[prover-mode: mathlib-build]`, ~100–200 LOC); global assembly
  `baseChange_sheafConditionFork_tensorIso` (+`TensorProduct.piRight`; add
  `[IsSeparated X]`/`[Fintype ι]`/`[F.IsQuasicoherent]`) → separated → MV → bridge → goal.
- **SNAP file-split coverage-debt** — ~70 unmatched `RelativeTensorCoequalizer.*`/`W_*` helpers (back in
  the monolith after the revert). Re-assess after Option-A settles (some helpers deleted by it).

## Standing notes

- **Prover model:** `opus`.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf. FlatBaseChangeGlobal imports
  FlatBaseChange (one-way); FlatBaseChange imports RegroupHelper. **SectionGradedRing is back to a
  self-contained MONOLITH** (iter-026 revert); `SectionGradedRingLocalized.lean` exists on disk but is
  UNIMPORTED. Re-introduce the split only if Option-A wants it.
- **Cold-build is the ONLY kernel-bomb detector:** validate with real `lake build
  AlgebraicJacobian.Cohomology.FlatBaseChange` / `...Picard.SectionGradedRing`. The LSP /
  `lean_multi_attempt` HIDE `(kernel) deterministic timeout`. Never add `maxHeartbeats 1e6`.
  **Process rule (iter-025 lesson):** NEVER dispatch >1 refactor/prover agent writing the SAME file
  concurrently — iter-025's 3 concurrent Option-A writers raced and produced the broken half-migration.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **FBC mate API (KB):** `iterated_mateEquiv_conjugateEquiv` (+`_symm`), `conjugateEquiv_comp`/`_symm_comp`,
  `mateEquiv_vcomp`/`_hcomp`, `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_conjugateEquiv_vcomp`,
  `conjugateIsoEquiv`(+`_apply_hom`) ALL REAL (`…Adjunction.Mates`, br025-verified iter-025).
  `mateEquiv` is `TwoSquare`-valued — recover NatTrans via `.natTrans` / `TwoSquare.equivNatTrans`. Both
  b2 legs CLOSED iter-018. Drive composites by splits, NEVER `unit_conjugateEquiv` over the composite.
- **SNAP Option A (KB):** associator-bridge wall = parallel-API anti-pattern (two `MonoidalCategory`
  instances on defeq copies). Fix = re-base onto `⊗_loc` (bridge `rfl`). Dual-instance DELETION REFUTED
  (load-bearing). Design `analogies/snap-instance-design.md`. Landing mechanism (iter-027) = SKELETON
  refactor (re-base + sorry) + prover fill, single agent, NEVER concurrent writers.
- **Merge-back discipline:** never rename kept decls/labels; never add `\leanok` by hand. No declarations
  are currently protected — chain decls may be re-signed to add missing hyps / pin instances.
