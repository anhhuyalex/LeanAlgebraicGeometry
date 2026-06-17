# Strategy Critic Report

## Slug
iter-016

## Iteration
016

## Routes audited

### Route: appendix-first height route

- **Goal-alignment**: PASS — The three stated theorems (ThmBdRatIntro, ThmBdFinRank, thm:BdTorIntroNF) and all required intermediates are addressed by the blueprint chapters; the appendix-first ordering gives a clean dependency chain from ambient setup to the final counting theorems.
- **Mathematical soundness**: PASS — The dependency chain is coherent: universal geometry → Betti map/form → non-degeneracy criterion → height inequality (auxiliary then full) → distance/counting lemmas → pre-Mazur → final bounds. The blueprint chapter structure matches this order and the `\uses` graph is consistent.
- **Sunk-cost reasoning detected**: no
- **Infrastructure-deferral detected**: yes — see Infrastructure-deferral findings below. The Betti-map phase is proposed as a single undivided large phase without sub-phase decomposition; the canonical-height/positivity phase is acknowledged as entirely absent from Mathlib but estimated at a LOC range inconsistent with that admission; the Setup phase lists "curves/Jacobians API" as a Key Mathlib need that does not exist for genus ≥ 2.
- **Phantom prerequisites**: `CanonicalHeight`-style API (MISSING), `IsNef` (MISSING), `IsBig` (MISSING), Jacobian variety of a genus-g curve for g ≥ 2 (MISSING — Mathlib has only `WeierstrassCurve.Jacobian` = Jacobian coordinate system for elliptic curves, not the Jacobian abelian variety of a higher-genus curve), fine moduli space of smooth genus-g curves with level structure (MISSING).
- **Effort honesty**: under-counted — The canonical-height phase is 2-4 iters / 220-340 LOC to build from scratch a Néron-Tate API, IsNef/IsBig positivity wrappers, arithmetic Bézout, and pullback/graph formalism — all absent from Mathlib. That scope is 500–1 000 LOC minimum in any realistic formalization. The Betti-map phase is 3-5 iters / 360-540 LOC for real-analytic maps, analytification, and period-coordinate data for abelian schemes — also implausibly small. The Setup phase carries "curves/Jacobians API" as a Mathlib given when the Jacobian variety of a genus-g curve must be built from scratch; the 320-480 LOC estimate does not account for this.
- **Parallelism under-exploited**: no — the strategy explicitly notes that the rational-point and torsion-packet counting lanes can proceed in parallel once the shared height/distance lemmas are in place, and both are listed as separate phases.
- **Verdict**: CHALLENGE

## Format compliance

- **Size**: 43 lines / 4 268 bytes — within budget.
- **Headings**: PASS — `## Goal`, `## Phases & estimations`, `## Routes`, `## Open strategic questions`, `## Mathlib gaps & new material` in the required order; `## Completed` absent, which is acceptable when nothing has been completed yet.
- **Per-iter narrative detected**: no
- **Accumulation detected**: no
- **Table discipline**: PASS — `## Phases & estimations` table has the required columns and one short line per cell.
- **Format verdict**: COMPLIANT

## Infrastructure-deferral findings

### Deferred: Néron-Tate / canonical-height API

- **Required by goal**: yes — `thm:ht_inequality`, `thm:ht_inequality_full`, `prop:aux_ht_ineq`, `lem:vojtamumford`, and ultimately all three final theorems depend on it.
- **Current plan for building it**: Named as "Canonical-height and positivity infrastructure" phase (ACTIVE, 2-4 iters, 220-340 LOC). The phase table acknowledges the gap ("this layer is currently missing from Mathlib and should be isolated explicitly") but gives no sub-phase breakdown.
- **Timeline**: vague — a LOC range is given but it is inconsistent with the acknowledged scope; no sub-tasks.
- **Verdict**: CHALLENGE — The LOC/iters estimate must be revised upward and the phase must be decomposed into concrete sub-phases (e.g., (a) Weil height on abelian varieties → (b) quadratic limit → (c) canonical height properties → (d) IsNef/IsBig wrappers → (e) arithmetic Bézout / Siu statement). As stated, the estimate is dishonest relative to the acknowledged gap.

### Deferred: Jacobian variety of a curve of genus g ≥ 2

- **Required by goal**: yes — `def:ambient_setup` defines the universal Jacobian family, and every downstream result operates on it. The Jacobian appears by name in all three final theorems.
- **Current plan for building it**: Listed as "curves/Jacobians API" under Key Mathlib needs for the Setup phase, implying it is available from Mathlib.
- **Timeline**: absent — no project-side plan; treated as a Mathlib given.
- **Verdict**: REJECT — Mathlib does not contain the Jacobian variety of a smooth curve of genus g ≥ 2 (confirmed: `WeierstrassCurve.Jacobian` in Mathlib is Jacobian *coordinates* for genus-1 Weierstrass curves, not an abelian variety functor for higher genus). This construction is required by the goal, absent from Mathlib, and the strategy has no plan for building it. The Setup phase must be revised to include building the Jacobian variety as an explicit sub-task before any phase depending on it can be scheduled.

### Deferred: Betti map / real-analytic geometry infrastructure

- **Required by goal**: yes — `prop:betti_map`, `prop:betti_form`, `prop:betti_map_app`, `def:nondegenerate_app`, and the height inequality chain all depend on it.
- **Current plan for building it**: "Betti map and Betti form" phase (ACTIVE, 3-5 iters, 360-540 LOC). The strategy acknowledges "likely needs substantial project-specific infrastructure for Siegel/moduli data" but does not break the phase into sub-phases.
- **Timeline**: vague — a LOC range and iters estimate are given but without sub-phase decomposition, the phase is a single opaque block. The required constructions (analytification of algebraic varieties over ℂ, real-analytic maps to T^{2g}, local period isomorphisms, and the monodromy invariance of the Betti form) are each individually large.
- **Verdict**: CHALLENGE — This phase must be decomposed into sub-phases (e.g., (a) analytification wrapper and local trivializations → (b) Betti map existence with the four listed properties → (c) Betti form construction and semi-positivity → (d) general-base variant / étale-cover reduction → (e) Betti-rank Zariski-openness lemma). A monolithic 360-540 LOC phase with no internal structure is the infrastructure-deferral-by-undivided-large-phase pattern and will not converge.

### Deferred: Fine moduli space of smooth genus-g curves with level structure

- **Required by goal**: yes — `def:ambient_setup` is the first blueprint definition and it fixes M_g with level structure as the base of every subsequent construction.
- **Current plan for building it**: Listed in "Mathlib gaps & new material" as something the project needs; the Setup phase does not call it out explicitly as a sub-task.
- **Timeline**: absent — no concrete sub-phase or LOC allocation inside the Setup phase.
- **Verdict**: CHALLENGE — The Setup phase must be revised to enumerate building M_g with level structure as a concrete first sub-task, before the universal curve and the Torelli map can be placed over it.

## Alternative routes (suggested)

### Alternative: sorry-first / analytic-black-box approach

- **What it looks like**: State `prop:betti_map`, `prop:betti_form`, `prop:betti_map_app`, and the analytification assumptions as axioms (sorry stubs) in a dedicated `Analytic.lean` layer. Formalize the algebraic height-inequality and counting argument (sections 6–8 of the paper) against this stub interface first, establishing the final theorem skeletons. Return to the analytic layer once the algebraic core is verified.
- **Why it might be cheaper or sounder**: It decouples the hard analytic geometry from the combinatorial/height counting argument, allowing the latter to be verified end-to-end much earlier. The final three theorems can reach `sorry`-free proofs modulo the analytic stubs, which is a meaningful milestone. It also isolates exactly which analytic properties the downstream argument actually uses, sharpening the Betti-map sub-phase design.
- **What the current strategy may have rejected**: The appendix-first order follows the paper's own route and avoids the risk of building counting against an interface that later proves wrong. However, the paper's appendix generality is already cleanly separated in the blueprint (`prop:betti_map` vs `prop:betti_map_app`).
- **Severity of the omission**: major — given that the analytic infrastructure is the longest and most uncertain phase, the absence of this alternative leaves the project without a contingency if the Betti-map formalization blocks all downstream progress.

## Prerequisite verification

- `WeierstrassCurve.Jacobian` (Jacobian variety of genus-g curve): MISSING — name exists but refers to Jacobian coordinates for genus-1 elliptic curves, not the Jacobian abelian variety of a higher-genus curve.
- `CanonicalHeight` (Néron-Tate canonical height on abelian variety): MISSING
- `IsNef` (nef line bundle): MISSING
- `IsBig` (big line bundle): MISSING
- `Height.logHeight` / `Height.mulHeight` (Weil height basics): VERIFIED (`Mathlib.NumberTheory.Height.Basic`)
- `AlgebraicGeometry.IsProper` / pullback / fiber products: VERIFIED

## Must-fix-this-iter

- Route appendix-first height route: infrastructure-deferral REJECT — Jacobian variety of genus-g curve required by goal, absent from Mathlib, no project-side plan. The Setup phase must be revised to include this as a named sub-task with a concrete LOC and iter estimate before any phase depending on it is dispatched.
- Route appendix-first height route: infrastructure-deferral CHALLENGE — Néron-Tate/canonical-height and positivity infrastructure (`CanonicalHeight`, `IsNef`, `IsBig`) required by goal, absent from Mathlib, LOC estimate (220-340) dishonestly small for the acknowledged scope. Phase must be decomposed into named sub-phases and estimate revised.
- Route appendix-first height route: infrastructure-deferral CHALLENGE — Betti-map / real-analytic geometry phase is a single undivided large block with no sub-phase decomposition. Phase must be broken into at least five concrete sub-phases (analytification, Betti map, Betti form, general-base variant, rank-openness) with per-sub-phase estimates.
- Route appendix-first height route: infrastructure-deferral CHALLENGE — Fine moduli space M_g with level structure required by goal's first definition, absent from Mathlib, not called out as a sub-task in the Setup phase. Must be added as a concrete first sub-task.
- Alternative sorry-first/analytic-black-box: critical omission — the strategy has no contingency route if the Betti-map formalization blocks downstream progress. Planner must either adopt this alternative as a secondary lane or produce an explicit rebuttal.

## Overall verdict

The route is goal-aligned and mathematically coherent, following the paper's own dependency order. No sunk-cost reasoning is present and the final two counting lanes are correctly marked as parallelizable. However, the strategy defers three constructions that are required for the stated goal without any project-side plan: the Jacobian variety of a smooth curve of genus g ≥ 2 (confirmed MISSING from Mathlib, treated as an available Mathlib item in the Setup phase — this is a REJECT-severity deferral), the Néron-Tate canonical-height and positivity infrastructure (acknowledged missing from Mathlib but budgeted at 220-340 LOC with no sub-phase decomposition — CHALLENGE), and the real-analytic Betti-map geometry (acknowledged as "substantial project-specific infrastructure" but planned as a single undivided phase — CHALLENGE). The fine moduli space M_g with level structure is also required by the goal's first definition and is absent from Mathlib and from the Setup phase's explicit sub-tasks (CHALLENGE). The effort estimates for these phases are under-counted relative to the acknowledged gaps. The strategy defers the Jacobian variety, which is required for the stated goal, and has no project-side plan to build it; this is the most urgent blocker and must be resolved before any prover work is dispatched on phases that depend on it.
