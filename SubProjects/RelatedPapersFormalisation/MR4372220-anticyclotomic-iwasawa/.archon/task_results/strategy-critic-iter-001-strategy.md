# Strategy Critic Report

## Slug
iter-001-strategy

## Iteration
001

## Routes audited

### Route: Greenberg-Vatsal style comparison route

- **Goal-alignment**: PASS - The route targets the stated theorem chain and keeps the comparison theorems on the critical path to `thm:thmA`, `cor:PR`, `thm:thmB`/`cor:thmB`, and `thm:thmC`.
- **Mathematical soundness**: PARTIAL - The high-level implication chain is plausible, but the Howard/Kolyvagin bottleneck is not decomposed enough to justify the current budget, and the interface boundary for the source-backed arithmetic inputs is still underspecified.
- **Sunk-cost reasoning detected**: no
- **Infrastructure-deferral detected**: yes - `thm:howard`/`thm:howard-HP` are required by the goal, but the strategy only says the phase "should be broken into bridge lemmas before any prover work"; no concrete sub-phases or timeline are given.
- **Phantom prerequisites**: no obvious missing support among the named basics; `PowerSeries`, `IsNoetherian`, `Submodule.FG`, and `ShortExactSequence` all exist in Mathlib.
- **Effort honesty**: under-counted - The combined Selmer/Iwasawa foundation, Howard/Kolyvagin argument, and downstream BSD/p-converse consequences look larger than the current 7-11 iter / ~1320-2020 LOC envelope unless many paper results are treated as opaque theorem blocks.
- **Parallelism under-exploited**: yes - `thm:thmB`/`cor:thmB` and `thm:thmC` are separate downstream branches after `cor:PR`, but they are collapsed into one final phase.
- **Verdict**: CHALLENGE

## Format compliance

- **Size**: 37 lines / 4343 bytes - within budget.
- **Headings**: PASS - the strategy uses the canonical top-level sections in order, with `## Completed` omitted because nothing is complete yet.
- **Per-iter narrative detected**: no
- **Accumulation detected**: no
- **Table discipline**: PASS - the active phase table has the required columns and short inline cells.
- **Format verdict**: COMPLIANT

## Infrastructure-deferral findings

### Deferred: Howard/Kolyvagin bridge-lemma stack

- **Required by goal**: yes - the goal includes `thm:howard` and `thm:howard-HP`, which are the technical bottleneck for `thm:thmA` and `cor:PR`.
- **Current plan for building it**: the strategy says it "should be broken into bridge lemmas before any prover work", but it does not name the lemmas or split the work into concrete sub-phases.
- **Timeline**: vague
- **Verdict**: CHALLENGE - the planner needs a named decomposition before this branch can be scheduled honestly.

## Alternative routes

### Alternative: theorem-block-first modularization

- **What it looks like**: formalize the external comparison theorems and arithmetic interfaces (`MAINalgside`, `cor:Kriz`, `thm:howard`, `thm:howard-HP`) as first-class opaque/project-specific theorem blocks, then prove the downstream consequences in thinner layers once the API stabilizes.
- **Why it might be cheaper or sounder**: it locks down the hardest external dependencies early, reduces redesign churn, and lets the downstream applications proceed without waiting for the full Selmer/Iwasawa core to be perfect.
- **What the current strategy may have rejected**: probably the desire to keep the paper's hypotheses verbatim and avoid parallel APIs for the same anticyclotomic objects.
- **Severity of the omission**: major

## Prerequisite verification

- `PowerSeries`: VERIFIED
- `IsNoetherian`: VERIFIED
- `Submodule.FG`: VERIFIED
- `ShortExactSequence`: VERIFIED

## Must-fix-this-iter

- Route Greenberg-Vatsal style comparison route: CHALLENGE - split the Howard/Kolyvagin branch into named bridge lemmas or sub-phases, and separate the `thm:thmB` / `thm:thmC` downstream applications into distinct lanes with their own budgets.
- Deferred Howard/Kolyvagin bridge-lemma stack: CHALLENGE - the current plan is only a qualitative note; it needs a concrete decomposition and timeline before prover work can proceed safely.
