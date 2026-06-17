# Strategy Critic Report

## Slug
iter-005-strategy

## Iteration
005

## Routes audited

### Route: Greenberg-Vatsal style comparison route

- **Goal-alignment**: PASS — the route, if fully executed, produces thm:thmA (anticyclotomic IMC), cor:PR, thm:thmB/cor:thmB, and thm:thmC exactly as the goal demands; the blueprint dependency chain is coherent and the `thm:thmA` proof correctly assembles Howard's divisibility + μ/λ equality + prop:equiv-imc into an equality of characteristic ideals.
- **Mathematical soundness**: PASS — the upgrade from one-sided divisibility to equality at the end of thm:thmA is sound: `μ(X_E)=μ(L_E)=0` and `λ(X_E)=λ(L_E)` together with the divisibility uniquely determine the equality for a torsion Λ-module with μ=0. The two downstream lanes (p-converse and BSD) are genuinely independent once thm:thmA is in hand. The pseudo-isomorphism `X ~ Λ ⊕ M ⊕ M` and its characteristic-ideal consequence are standard.
- **Sunk-cost reasoning detected**: no
- **Infrastructure-deferral detected**: yes — four constructions required by the stated goal are either explicitly sorry-backed or implicitly so, with no concrete timelines for lifting. See the Infrastructure-deferral findings section below.
- **Phantom prerequisites**: none detected beyond the acknowledged Mathlib gaps. `Module.IsTorsion` is VERIFIED (Mathlib.Algebra.Module.Torsion.Basic); `charIdeal` for torsion modules over power series rings is MISSING (confirmed via Loogle — no result); `KolyvaginSystem` is MISSING (confirmed via Loogle — no result).
- **Effort honesty**: reasonable — the LOC ranges and Iters-left cells are plausible given the blueprint content. One exception: the Howard abstract bound phase estimates ~220–360 LOC and 3 iters for a chapter that contains `thm:Zp-twisted` (described in the blueprint itself as "multi-page") PLUS the abstract Kolyvagin inductive machinery (`def:selmer-triple`, two lemmas, and the Lambda-adic specialization). The LOC lower bound of 220 may be optimistic; the strategy itself acknowledges sub-splitting is needed. The estimate is not dishonest but the downside is under-stated.
- **Parallelism under-exploited**: yes — `thm:howard` (abstract Lambda-adic bound, requires only `def:selmer-triple` and `thm:Zp-twisted`) and `thm:howard-HPKS` (Heegner Kolyvagin system construction, requires `def:selmer-triple` and `cor:characters`) are independent of each other. The strategy lists them as separate phases but does not explicitly state they can be formalized in parallel. A prover working on the Heegner KS construction does not need the abstract bound to be finished first. The serialization implied by listing them as sequential phases over 5–6 combined iters is a throughput risk.
- **Verdict**: CHALLENGE
  - The route is mathematically sound, but the infrastructure-deferral pattern (see below) means the route cannot be completed to the stated goal without lifting the sorries on `def:char-ideal`, the Kolyvagin systems, and the BDP/Katz L-functions. The strategy has no concrete plan for any of these liftings. Additionally, `prop:equiv-imc` (BCK Thm 5.2, required to finish thm:thmA) is an external-reference sorry-block that is not even listed in the Mathlib gaps section, leaving it unplanned.

---

## Format compliance

- **Size**: 41 lines / 6534 bytes — within budget.
- **Headings**: PASS — order is `## Goal`, `## Phases & estimations`, `## Routes`, `## Open strategic questions`, `## Mathlib gaps & new material`; `## Completed` is correctly omitted while no phase is complete.
- **Per-iter narrative detected**: no
- **Accumulation detected**: no
- **Table discipline**: PASS — `## Phases & estimations` has the correct six-column schema; Status values are inline tags (`ACTIVE`); LOC cells are rough ranges; Risks cells are appropriately short.
- **Format verdict**: COMPLIANT

---

## Infrastructure-deferral findings

### Deferred: `def:char-ideal` (characteristic ideal of a torsion Λ-module)

- **Required by goal**: yes — `thm:thmA` asserts `char_Λ(X_E)Λ^ur = (L_E)` as ideals; without a formalized characteristic ideal, this statement cannot be stated, let alone proved, in Lean without `sorry`.
- **Current plan for building it**: sorry-backed postulate in the Local Iwasawa chapter; strategy says "a future iter will lift the sorry when needed."
- **Timeline**: vague ("future iter") — no iter estimate, no triggering condition, no milestone.
- **Verdict**: CHALLENGE — the stated goal is `thm:thmA` as an equality of characteristic ideals. If `def:char-ideal` remains a `sorry`-postulate at the end of the project, the formalization of `thm:thmA` is vacuous. The planner must either (a) give a concrete iter range for when the sorry will be lifted (e.g., after the Local/Algebraic phases compile, begin a dedicated `char-ideal` sub-phase targeting `Mathlib.RingTheory.PowerSeries` + UFD + length theory), or (b) explicitly downgrade the stated goal to a sorry-admitted skeleton and revise `## Goal` accordingly.

### Deferred: Kolyvagin systems formalism (`def:selmer-triple`)

- **Required by goal**: yes — `thm:howard`, `thm:howard-HPKS`, and `thm:howard-HP` all have `def:selmer-triple` in their `\uses` clause; without it, Howard's divisibility is unproved and `thm:thmA` is inaccessible via the planned route.
- **Current plan for building it**: sorry-backed single-block postulate; strategy says a `def:kolyvaginSystem` block will be split off "if the prover finds `def:selmer-triple` too large." This addresses the splitting question, not the sorry-lifting question.
- **Timeline**: absent — no iter estimate for when the Kolyvagin-system axioms will be formally verified rather than postulated.
- **Verdict**: CHALLENGE — same structure as `def:char-ideal`. The planner should at minimum decompose `def:selmer-triple` into independently sorry-liftable pieces (the abstract Selmer structure, the finite-singular comparison isomorphism, the norm-relation axiom), assign each a target iter, and confirm that none requires Mathlib upstream work that is not already planned. The current "sorry-backed initially" language with no exit condition is infrastructure-deferral by inaction.

### Deferred: BDP/Katz p-adic L-functions (`thm:BDP`, `thm:Katz`)

- **Required by goal**: yes — `cor:Kriz` and `mulambda` (the analytic side of the μ/λ equality feeding into `thm:thmA`) depend on `thm:BDP` and `thm:Katz`. Without these, the analytic comparison lane produces nothing and `thm:thmA` cannot be assembled.
- **Current plan for building it**: sorry-backed source-backed theorem blocks; "formalization debt is explicit."
- **Timeline**: absent.
- **Verdict**: CHALLENGE — the BDP and Katz constructions are the deepest items in the analytic lane and the ones least likely to be liftable by a single Lean prover without dedicated Mathlib contributions (measure theory on Galois groups, CM periods, Serre–Tate expansions). The strategy should distinguish between (a) constructions where the sorry can be lifted within the project's iteration budget via direct formalization, and (b) constructions where the sorry will remain for the duration of the project as an axiom, and the goal should be re-stated to reflect that `thm:BDP` and `thm:Katz` are admitted axioms. Neither option is addressed. The planner must choose.

### Deferred: `prop:equiv-imc` (BCK Theorem 5.2, equivalence of the two main conjecture formulations)

- **Required by goal**: yes — `thm:thmA` and `cor:PR` both `\uses` `prop:equiv-imc`; without it, neither Howard's divisibility nor the Perrin-Riou corollary can be assembled into `thm:thmA`.
- **Current plan for building it**: the blueprint proof body describes it as "this is [BCK, Thm 5.2]... the argument of [BCK] goes through after inverting p." This is a sorry-backed external-reference block. It is NOT listed in `## Mathlib gaps & new material` in STRATEGY.md.
- **Timeline**: absent — not mentioned at all in the strategy.
- **Verdict**: CHALLENGE — an unlisted sorry-postulate on a result required by `thm:thmA`. The planner must add `prop:equiv-imc` to `## Mathlib gaps & new material` and decide whether to treat it as a self-contained sorry-admitted lemma (the involution argument is algebraic and could in principle be formalized project-side) or as an accepted external axiom. Leaving it completely unplanned is a blind spot.

---

## Alternative routes (suggested)

### Alternative: Explicit sorry-axiom ledger and revised goal tiers

- **What it looks like**: Rather than a single goal "Formalize the theorem chain of MR4372220," introduce two explicit goal tiers: (Tier 1) "Formalize the proof skeleton conditional on named axioms: `def:char-ideal`, Kolyvagin-system axioms, `thm:BDP`, `thm:Katz`, `prop:equiv-imc`"; (Tier 2) "Lift each named axiom." List the Tier 2 items explicitly in `## Mathlib gaps & new material` with independent iter estimates and dependency ordering.
- **Why it might be cheaper or sounder**: The current strategy conflates Tier 1 and Tier 2 work without acknowledging that Tier 2 items have radically different complexity profiles. `prop:equiv-imc` (algebraic involution) could plausibly be lifted in 1–2 iters. `thm:BDP` (measure theory, CM periods) might require a dedicated Mathlib contribution that could take 10–15 iters or be deferred to Mathlib upstream. Making this explicit would allow parallel prover dispatch: Tier 1 provers build the skeleton; a separate Tier 2 sub-effort lifts `prop:equiv-imc` and possibly `def:char-ideal` as priority items.
- **What the current strategy may have rejected**: not addressed; the strategy conflates the two tiers silently.
- **Severity of the omission**: major

---

## Prerequisite verification

- `Module.IsTorsion`: VERIFIED (Mathlib.Algebra.Module.Torsion.Basic)
- `charIdeal` (characteristic ideal for torsion Λ-modules): MISSING — Loogle returns no results for this name or related ring-theoretic constructs at the Iwasawa-algebra level.
- `KolyvaginSystem`: MISSING — Loogle returns no results.
- `PowerSeries`: VERIFIED (Mathlib.RingTheory.PowerSeries.Basic, present under `PowerSeries` and `MvPowerSeries`; can serve as the ambient ring for Λ = Z_p[[T]] after choosing a topological generator of Γ).

---

## Must-fix-this-iter

- Route Greenberg-Vatsal: CHALLENGE — parallelism under-exploited. The Howard abstract bound sub-phase and the Heegner KS sub-phase are independent; the planner must explicitly flag them as dispatchable in parallel to avoid serializing 5–6 iters of Howard work.
- Route Greenberg-Vatsal: infrastructure-deferral CHALLENGE — `def:char-ideal` required by goal (thm:thmA asserts equality of characteristic ideals), no concrete timeline. Planner must either give an iter estimate for lifting or revise `## Goal` to name sorry-axioms explicitly.
- Route Greenberg-Vatsal: infrastructure-deferral CHALLENGE — Kolyvagin systems (`def:selmer-triple`) required by goal via thm:howard and thm:howard-HP, no concrete timeline for lifting. Planner must decompose the postulate into liftable pieces and assign target iters.
- Route Greenberg-Vatsal: infrastructure-deferral CHALLENGE — `thm:BDP`/`thm:Katz` required by goal via the analytic comparison lane, no concrete timeline. Planner must decide: project-side formalization with iter estimate, or explicit sorry-axiom with goal revision.
- Route Greenberg-Vatsal: infrastructure-deferral CHALLENGE — `prop:equiv-imc` (BCK Thm 5.2) required by goal (thm:thmA uses it directly), not listed in `## Mathlib gaps & new material`, no plan at all. Planner must add it to the gaps section and assign handling (sorry-admit or project-side formalization).

---

## Overall verdict

The route is mathematically sound and the blueprint dependency chain is coherent: the Greenberg–Vatsal comparison argument, Howard's Kolyvagin-system divisibility, and the final upgrade via μ/λ equality are correctly assembled in the blueprint. The document is format-compliant. However, the strategy defers four constructions that are each individually required for the stated goal — `def:char-ideal` (the characteristic ideal, needed for the very statement of thm:thmA), the Kolyvagin systems formalism (`def:selmer-triple`, needed for all Howard results), the BDP and Katz p-adic L-functions (needed for the analytic comparison lane), and `prop:equiv-imc` (BCK Thm 5.2, needed to assemble thm:thmA from Howard's divisibility) — all with vague "future iter" or no timeline, and without distinguishing between items that could be lifted project-side within a modest iteration budget versus items that require major Mathlib upstream contributions. Until the strategy articulates a concrete per-item plan for each deferred construction — including an explicit decision on which items will remain as named sorry-axioms for the duration, with a corresponding revision of `## Goal` into explicit tiers — the project's stated goal of formalizing the theorem chain cannot be meaningfully tracked, and the parallelism between the Howard abstract bound and the Heegner KS construction sub-phases remains unrealised.
