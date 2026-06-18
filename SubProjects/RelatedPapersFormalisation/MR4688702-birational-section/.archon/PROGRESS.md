# Project Progress

## Current Stage
loop

## Stages
- [x] init
- [x] dag (blueprint phase COMPLETE as of iter-002)
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Completed this iteration (iter-002)

- [x] Fixed 12 empty `\uses{}` arguments in Overview.tex (caused plastex crash)
- [x] Fixed broken `\uses{example:gm-loop}` reference in prop:simple
- [x] Added proof blocks for cor:morph-tbirl and cor:cusp-bl2 (were ∞-effort)
- [x] Added 3 missing `\uses{}` wire-ups (lem:nf-lift, thm:main-C ×2)
- [x] Retrieved 4 reference papers: bv15, bv19, bv23-valuative, tv18 (with correct arXiv IDs)
- [x] Corrected wrong arXiv IDs in ARCHON_MEMORY (1404.7475 �� 1610.07341; 1412.7523 → 1410.1164)
- [x] Blueprint-doctor: clean (0 malformed refs, 0 broken refs)
- [x] leandag: 0 ∞-effort nodes, 0 broken `\uses{}`, 0 isolated nodes, 66 edges
- [x] DAG_STATUS.md: COMPLETE

## Current Objectives

### Priority 1 — Blueprint clean-up (before prover dispatch)

These must be resolved to satisfy the blueprint-reviewer HARD GATE:

1. **Citation format fix**: Dispatch blueprint-writer to append `(read from references/MR4688702-birational-section.tex)` to all 39 `% SOURCE:` lines in Overview.tex. One-pass mechanical fix.

2. **Missing references**: Dispatch reference-retrievers for:
   - arXiv:2003.04649 (Bresciani "Sections of families") — backs prop:nffg proof (Cor 3.4, Cor 4.9) + lem:nf-lift proof (Cor A.3)
   - Stix 2013 "Rational Points and Arithmetic of Fundamental Groups" — backs lem:nf-lift (Thm B) + lem:bireq (Thm 17)
   - Saidí-Tyler arXiv:2109.05276 — backs thm:main-C (Thm C, NF reduction)

3. **example:gm-loop env fix**: Convert `\begin{example}[GmLoop]...\end{example}` → `\begin{lemma}[GmLoop]...\end{lemma}`, rename label to `lem:gm-loop`, update all `\cref{}` refs, add `\uses{lem:gm-loop}` to prop:simple.

4. **Re-run blueprint-reviewer** after items 1–3 to confirm `complete=true, correct=true`.

### Priority 2 — Axiom layer (first prover objective, once HARD GATE cleared)

5. **Write minimum axiom set in `Basic.lean`**:
   - `axiom BSC.FamiliesExactSeq` (backed by references/MR4688702-birational-section.tex, Lemma 1)
   - `axiom BSC.EtaleFundGerbe` (backed by bv15 §8)
   - `axiom BSC.RelFundGerbe` (backed by MR4688702 §1.1)
   - `axiom BSC.RelGerbeLimit` (backed by bv19 Prop 3.9)
   - `axiom BSC.ProrootValCrit` (backed by bv23-valuative Theorem 3.1)
   - `axiom BSC.SpecLoop` (backed by MR4688702 §2, Def 1)
   - `axiom BSC.UniqueLoopTorus` (backed by MR4688702 Lemma 3)
   - `axiom BSC.StixThmB` (Stix Thm B — reference needed first)
   - `axiom BSC.NFFG` (Tamagawa + Saidí-Tyler — reference needed first)
   - `axiom BSC.HilbertIrred` — confirm Mathlib availability first

6. **Rename BSC.TODO.* placeholders** to actual `BSC.*` names when writing Lean declarations.
