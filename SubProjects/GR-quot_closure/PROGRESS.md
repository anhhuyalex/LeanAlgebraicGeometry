# Project Progress

## Current Stage

prover  (**Leg closable scope COMPLETE.** GR functor-representability (`represents`) +
`tautologicalQuotient_epi` + SNAP assoc chain B1–B7 + ∀L `GSemiring` + invertible-`L` `GCommSemiring` +
the capped SNAP-S1 ℕ-graded ∀L graded MODULE `M(X,L,F)=⊕Γ(F⊗L^{⊗m})` (`sectionGradedModule_gmodule`,
`DirectSum.Gmodule`) are ALL sorry-free + axiom-clean. **No live closable prover frontier remains.** The
only open sorries are intentional out-of-leg deferrals: 4 χ file-skeletons in `QuotScheme.lean`
(`hilbert_polynomial`/`quot_functor`, need the cohomology engine) + `RelativeSpec.lean` (out-of-cone
inherited parent code). The leg is in a delivered / awaiting-merge terminal state.)

## Stages
- [x] init
- [x] autoformalize
- [ ] prover — Closable scope DONE (GR cone + ring `Γ_*(X,L)` through `GCommSemiring` + SNAP-S1 module
      `sectionGradedModule_gmodule`, all axiom-clean). No ready in-cone sorries remain. Remaining sorries
      = χ-blocked (`QuotScheme.lean`, 4) + out-of-cone (`RelativeSpec.lean`), both deferred to merge.
- [ ] polish — deferred: a golf/polish pass on the 4k-line `SectionGradedRing.lean` is low-value on an
      already-axiom-clean file; revisit only if requested. The leg's substance is delivered.

## End-state overview

**ACHIEVED:** goal seed `AlgebraicGeometry.Grassmannian.represents` (rank-`d`-quotient functor
representability) sorry-free + axiom-clean; `tautologicalQuotient_epi` (last GR sorry) — closable GR cone
0-sorry. The entire SNAP-S0 associativity chain B1–B7 (∀L), the ∀L section graded SEMIRING
`sectionGradedRing_gsemiring` (Stacks 01CV), and the invertible-`L` graded COMMUTATIVE semiring
`sectionGradedRing_gcommSemiring` (Stacks 01CR/01CV) — all axiom-clean. SNAP-S1 module lane CLOSED: (A)
`moduleTensorPowAdd_assoc`, (B) `moduleSectionAction_{mul_smul,one_smul}`, base
`moduleTensorPowAdd_zero_left`, (C) `sectionGradedModule_gmodule` — all axiom-clean; `SectionGradedRing.lean`
is SORRY-FREE.

**Goal boundary (do NOT mistake for a gap):** the goal-named `thm:grassmannian_representable`
(smooth-PROJECTIVE representability, `\uses` out-of-cone `relative_spec_*`) is delivered only as a weak
skeleton. The substantive functor-moduli content is `thm:grassmannian_universal_property` =
`Grassmannian.represents` (DELIVERED). The smooth/projective + relative-spec residue is out-of-cone,
parent-owned, resolved at merge. See STRATEGY `## Open strategic questions`.

## Current Objectives

**(no prover dispatch this iter — see iter/iter-037/plan.md for rationale)**

No closable in-cone sorry remains. The leg's mandated goal (GR representability cone + section graded ring
`Γ_*(X,L)`) plus the capped SNAP-S1 module stretch are ALL delivered axiom-clean (strategy-critic iter-037
verdict SOUND: stopping here is correct, not stopping short — the declined downstream nodes
`sectionGradedModule_fg` / `hilbertPoly_of_sectionModule` are Serre-finiteness/cohomology nodes, not
project sorries, and not closable in this H⁰ leg). Every remaining `sorry` is an intentional out-of-leg
deferral (χ → cohomology leg; RelativeSpec → out-of-cone inherited). Dispatching a prover would mean
either (a) re-probing a χ-blocked node we have correctly deferred since iter-001, (b) touching out-of-cone
inherited code, or (c) expanding past the goal boundary into χ-dependent downstream theory with no in-leg
consumer. None is warranted.

This iter is a **closeout / consolidation** pass: STRATEGY.md moved SNAP-S1 to `## Completed` and the
leg is recorded as delivered / awaiting-merge; the strategy-critic validated the stop; the stale root
`STRATEGY.md` stray was synced to the canonical `.archon/` version.

## Deferred (NOT objectives)

- **χ-blocked (`QuotScheme.lean`, 4 sorries):** `hilbertPolynomial`, `QuotFunctor`, `Grassmannian`
  functor — need a higher-cohomology / Euler-characteristic engine absent in this i=0 leg; filled from
  the cohomology leg at merge. KEEP `sorry`; do NOT re-probe.
- **`RelativeSpec.lean` (out-of-cone):** inherited parent code (iter-173–179 lineage); not in this leg's
  cone. Untouched.
- **Downstream blueprint nodes `sectionGradedModule_fg` / `hilbertPoly_of_sectionModule`:** NOT project
  sorries (blueprint `\lean{}` pins only, no Lean decl). Serre-finiteness (needs proper + ample + coherent,
  Hartshorne II.5) / Euler-char — cohomology-leg work. Do NOT formalize in-leg.

## Merge-back debt (NOT objectives — resolve at merge, do NOT edit in-leg)

- **Blueprint marker/pin reconciliation.** ~16 leandag "unproved" nodes are delivered-but-unmarked decls:
  anonymous-instance pins (`instGMulNatSectionDeg` etc.) sync cannot resolve to auto-generated names,
  abstract-concept pins (`def:sectionGradedRing` → `AlgebraicGeometry.sectionGradedRing`, no bare decl;
  real decls are `sectionGradedRing_gsemiring`/`_gcommSemiring`), plus the recurring `sync_leanok`
  over-strip on this chapter. Labels are the PARENT's; reconcile at merge. The review phase restores the
  over-stripped `\leanok` on axiom-clean blocks per the standing protocol.
- **356 `lean_aux` coverage-debt nodes + dormant broken `\ref`/`\uses` + 2 phantom covers-files**
  (`Cohomology_FlatBaseChange.tex`, `Picard_GlueDescent.tex`, `Picard_QuotScheme.tex`): extraction
  artifacts outside the 3-seed cone; resolve at merge, do NOT edit in-leg.
- **`Grassmannian.representable` weak skeleton** (`\lean{}` under-delivers smoothness/properness/Plücker):
  strengthen/split the label in the parent at merge.

## Standing notes

- **Prover model:** `opus`.
- **Cold-build validation:** `lake build AlgebraicJacobian.Picard.SectionGradedRing`; do NOT add
  `maxHeartbeats 1e6`. `maxRecDepth` OK for stack depth.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **Nothing is protected** — `archon-protected.yaml` has no active entries.
- **Stale root strays:** a root-level `STRATEGY.md`/`PROGRESS.md` mirror exists and drifts stale; the
  canonical files are under `.archon/`. When dispatching path-agnostic critics, pass the explicit
  `.archon/` path, or keep the root mirror synced (done iter-037 for STRATEGY).
- **`X.Modules`/value-ModuleCat diamond:** never positional `rw`/`simp`/`erw`; term-mode + `change`.
- **DESCENT TRAP:** `TopCat.Sheaf.hom_ext` on the underlying `TopCat.Sheaf Ab`, NEVER `Scheme.Modules.hom_ext`
  (⊤-trap).
- **Merge-back discipline:** the monoidal-localization pivot DIVERGES from the sibling by design. Never add
  `\leanok` by hand.
