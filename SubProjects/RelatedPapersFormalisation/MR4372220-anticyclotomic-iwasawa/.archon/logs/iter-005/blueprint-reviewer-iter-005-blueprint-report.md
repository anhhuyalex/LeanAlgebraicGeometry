# Blueprint Review: iter-005-blueprint
**Iter:** 005

## Top-level summaries

- **iter-004 must-fixes**: All resolved — def:char-ideal ✓, lem:cebotarev-kolyvagin ✓, lem:kolyvagin-inductive-step ✓, def:bdp-class ✓, thm:control-jsw ✓, thm:padic-gz ✓, prop:equiv-imc \uses{} ✓, thm:thmC \uses{} ✓, cor:lambda-E \uses{lem:local-char-wp} ✓, cor:Kriz \uses{thm:Katz} ✓, macros (\llbracket, \rrbracket, \mathds) ✓.
- **Cross-chapter edge thm:mu-zero-theta → thm:Katz**: correctly ABSENT. thm:mu-zero-theta is Selmer-group μ=0 (Rubin/Hida); thm:Katz uses a distinct external result (Hida's μ=0 for Katz L-functions, \cite{hidamu=0}). The two are mathematically separate. The edge should not be added.
- **Rendering**: clean — `archon blueprint-doctor` reports zero `malformed_refs`, zero undefined macros, zero broken_refs.
- **DAG**: `leandag build` — 33 nodes, 69 edges, 0 isolated, 0 `unknown_uses` (no broken \uses{}). All 33 `\lean{}` hints unmatched (expected — no Lean files yet). 0 gaps (all nodes have \lean{}).
- **Soon** (non-blocking, 3 items): missing `\mathlibok` anchors for 3 heavy external dependencies that provers will need to sorry-axiomize; see below.

## Unstarted-phase proposals

None. All 8 strategy phases have adequate blueprint coverage (≥3 meaningful declaration blocks each).

## Per-chapter

### `Overview.tex`
- **Complete**: false (stub — \chapter + 1 prose line, no declarations)
- **Correct**: true
- **Notes**: Intentional overview stub; archon:covers the root .lean + Basic.lean (blueprint-doctor does not flag these as missing, unlike the other chapters). No prover dispatch needed.

### `Local_Iwasawa_Selmer.tex`
- **Complete**: true (8 declarations: def:iwasawa-algebra, def:char-ideal, lem:commalg, lem:local-char-wneqp, lem:local-char-wp, thm:mu-zero-theta, prop:lambda-theta, cor:characters)
- **Correct**: true
- **Notes**: thm:mu-zero-theta proof invokes "Rubin's main-conjecture input" (\cite{rubinmainconj}) as a key step — an external result with no blueprint anchor (see Soon §1). Proof sketches are otherwise detailed enough for prover use.

### `Algebraic_Iwasawa_Comparison.tex`
- **Complete**: true (4 declarations: prop:modp-E, prop:modp-E-tors, cor:lambda-E, MAINalgside)
- **Correct**: true
- **Notes**: Label `MAINalgside` lacks `thm:` prefix (same for `mulambda` in Analytic) — stylistic inconsistency, used consistently across chapters, not a DAG/compile issue.

### `Analytic_Iwasawa_Comparison.tex`
- **Complete**: true (5 declarations: thm:BDP, thm:Katz, thm:kriz, cor:Kriz, mulambda)
- **Correct**: true
- **Notes**:
  - thm:Katz proof cites \cite{hidamu=0} (Hida's μ=0 for Katz L-functions) as the key step for μ(Lcal_θ)=0. No \mathlibok anchor exists. (Soon §2.)
  - mulambda proof invokes Rubin's MC for K ("λ(Lcal_φ)=λ(X_φ)") without a blueprint anchor. (Soon §1.)
  - Redundant `\uses{}` inside some proof blocks (thm:kriz, cor:Kriz proofs repeat declaration-level uses) — harmless, DAG unaffected.

### `Howard_Kolyvagin.tex`
- **Complete**: true (7 declarations: def:selmer-triple, lem:cebotarev-kolyvagin, lem:kolyvagin-inductive-step, thm:Zp-twisted, thm:howard, thm:howard-HPKS, thm:howard-HP)
- **Correct**: true
- **Notes**:
  - thm:howard-HPKS proof invokes Cornut–Vatsal non-vanishing without a blueprint anchor. (Soon §3.)
  - thm:Zp-twisted proof note "Full proof is multi-page; sub-splitting recommended" — useful prover guidance, not a defect.

### `Main_Conjecture_Applications.tex`
- **Complete**: true (9 declarations: def:bdp-class, thm:control-jsw, thm:padic-gz, prop:equiv-imc, thm:thmA, cor:PR, thm:thmB, cor:thmB, thm:thmC)
- **Correct**: true
- **Notes**:
  - thm:control-jsw and thm:padic-gz are explicitly sorry-backed in the blueprint ("the Lean verification will supply the missing comparison details") — acceptable and acknowledged.
  - thm:thmA proof correctly assembles thm:howard-HP + prop:equiv-imc + mulambda; the α-stabilization comparison (κ_1^Hg = κ_∞ as Λ-generators) is captured in def:bdp-class and transitively in prop:equiv-imc's \uses{}.

## Severity summary

- **must-fix**: none.
- **soon** (quality / prover ergonomics):
  1. **Rubin MC anchor** (`Local_Iwasawa_Selmer.tex` + `Analytic_Iwasawa_Comparison.tex`): Rubin's main conjecture for K (\cite{rubinmainconj}) is invoked in thm:mu-zero-theta proof (Local) and mulambda proof (Analytic) without a blueprint declaration. Recommend adding a `\mathlibok`-style sorry-backed declaration `thm:rubin-mc` (no Mathlib analog) in Local or a shared foundations section, and adding it to \uses{} of thm:mu-zero-theta and mulambda.
  2. **Hida μ=0 anchor** (`Analytic_Iwasawa_Comparison.tex`): Hida's μ=0 theorem for Katz p-adic L-functions (\cite{hidamu=0}) is used in thm:Katz and cor:Kriz proofs without a blueprint anchor. Recommend a sorry-backed `thm:hida-mu-zero` declaration in Analytic with \uses{def:iwasawa-algebra}, added to \uses{} of thm:Katz and cor:Kriz.
  3. **Cornut–Vatsal anchor** (`Howard_Kolyvagin.tex`): Non-vanishing of Heegner points over the anticyclotomic tower (\cite{cornut, vatsal}) is the final step of thm:howard-HPKS without a blueprint anchor. Recommend a sorry-backed `thm:cornut-vatsal` declaration in Howard, added to \uses{} of thm:howard-HPKS.

## HARD GATE verdicts (for prover dispatch)

| File | Chapter | complete | correct | Gate |
|---|---|---|---|---|
| Local.lean | Local_Iwasawa_Selmer.tex | true | true | ✅ PASS |
| Algebraic.lean | Algebraic_Iwasawa_Comparison.tex | true | true | ✅ PASS |
| Analytic.lean | Analytic_Iwasawa_Comparison.tex | true | true | ✅ PASS (soon items non-blocking) |
| Howard.lean | Howard_Kolyvagin.tex | true | true | ✅ PASS (soon items non-blocking) |
| Applications.lean | Main_Conjecture_Applications.tex | true | true | ✅ PASS |
