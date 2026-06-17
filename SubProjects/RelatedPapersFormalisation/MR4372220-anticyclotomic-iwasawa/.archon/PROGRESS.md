# Project Progress

## Current Stage
dag (iter-004 complete — ready for autoformalize)

## Stages
- [x] init
- [x] dag (iter-004: 33 nodes, 69 edges, 0 ∞-effort, 0 isolated, 0 broken \uses{})
- [ ] autoformalize
- [ ] prover
- [ ] polish

## iter-004 Summary (completed)

**Blueprint coverage**: 33 declarations across 6 files:
- `Local_Iwasawa_Selmer.tex`: 9 decls (def:iwasawa-algebra, def:char-ideal, lem:commalg, lem:local-char-wneqp, lem:local-char-wp, thm:mu-zero-theta, prop:lambda-theta, cor:characters)
  - Wait: actually 8 decls: def:iwasawa-algebra, def:char-ideal, lem:commalg, lem:local-char-wneqp, lem:local-char-wp, thm:mu-zero-theta, prop:lambda-theta, cor:characters
- `Algebraic_Iwasawa_Comparison.tex`: 4 decls (prop:modp-E, prop:modp-E-tors, cor:lambda-E, MAINalgside)
- `Analytic_Iwasawa_Comparison.tex`: 5 decls (thm:BDP, thm:Katz, thm:kriz, cor:Kriz, mulambda)
- `Howard_Kolyvagin.tex`: 7 decls (def:selmer-triple, lem:cebotarev-kolyvagin, lem:kolyvagin-inductive-step, thm:Zp-twisted, thm:howard, thm:howard-HPKS, thm:howard-HP)
- `Main_Conjecture_Applications.tex`: 9 decls (def:bdp-class, thm:control-jsw, thm:padic-gz, prop:equiv-imc, thm:thmA, cor:PR, thm:thmB, cor:thmB, thm:thmC)

**leandag metrics** (iter-004 final):
- Blueprint nodes: 33 | Edges: 69 | ∞-effort nodes: 0 | Isolated: 0 | Broken \uses{}: 0
- Axiom: def:iwasawa-algebra (root, impact=32)
- Leaves: cor:thmB, thm:thmC (terminal theorems)

**Fixes applied in iter-004**:
- Extracted 6 proof sketches from lemma environments into proper `\begin{proof}...\end{proof}` blocks
- Added all 5 chapters to `content.tex`
- Fixed `prop:modp-E` and `MAINalgside` missing `\uses{}` edges
- Added macros `\llbracket`, `\rrbracket`, `\mathds` to `macros/common.tex`
- Fixed broken `\ref{corcharacters}` and `\S\ref{subsec:Lp}` in source citation lines
- Added 6 new declarations: `def:char-ideal`, `lem:cebotarev-kolyvagin`, `lem:kolyvagin-inductive-step`, `def:bdp-class`, `thm:control-jsw`, `thm:padic-gz`
- Corrected all `\uses{}` dependency edges across all chapters

## Next Objectives (iter-005: autoformalize)
- Dispatch Lean skeleton writers: one per chapter, generating `sorry`-backed Lean stubs for all 33 declarations
- Priority order: Local → Algebraic → Howard → Analytic → Applications
- Target: 33 Lean declarations matching blueprint `\lean{}` names, all `sorry`-backed, compiling with `import Mathlib`
