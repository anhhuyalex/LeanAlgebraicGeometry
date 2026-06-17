# Blueprint Review: iter-004-blueprint
**Iter:** 004

## Top-level summaries

- **Incomplete**: `Local_Iwasawa_Selmer.tex` (missing `def:char-ideal` — strategy-mandated sorry-backed postulate); `Howard_Kolyvagin.tex` (thm:Zp-twisted sub-lemmas needed per strategy); `Main_Conjecture_Applications.tex` (κ_∞ declaration missing; spurious \uses{} edges).
- **Bad Lean targets**: all 27 `\lean{...}` unmatched — expected (Lean files do not yet exist per covers_problems). Not a blueprint defect.
- **Multi-route**: Single route (Greenberg–Vatsal style comparison). No coverage gap.
- **Citations**: `Local_Iwasawa_Selmer.tex` cor:characters has broken `\ref{corcharacters}` in `% SOURCE:` comment (renders as "??" in blueprint); `Analytic_Iwasawa_Comparison.tex` thm:BDP visible `\textit{Source:}` line has broken `\S\ref{subsec:Lp}` (renders as "??"). Both files cite `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` — file EXISTS. ✓ All `% SOURCE QUOTE PROOF:` present for analytic and applications chapters; missing for `thm:mu-zero-theta` and `prop:lambda-theta` in local chapter, and `MAINalgside` in algebraic chapter.
- **Deps/Isolated**: 0 isolated nodes. Broken \uses{} edges: none (`leandag build` reports 0 `unknown_uses`). Missing edges: (1) `cor:lambda-E` should `\uses{lem:local-char-wp}` (proof invokes Λ-cofreeness from that lemma); (2) `cor:Kriz` should `\uses{thm:Katz}` (proof invokes Hida μ=0 result stated in thm:Katz). Spurious edges: (3) `prop:equiv-imc` statement has `\uses{thm:howard-HP, mulambda}` — these belong to thm:thmA's proof, not to the equivalence statement; (4) `thm:thmC` statement has `\uses{thm:thmB}` — strategy says BSD lane must be independent of p-converse lane; proof block correctly has only `\uses{thm:thmA, def:iwasawa-algebra}`.
- **Rendering**: 5 undefined macros across 4 chapters: `\mathds` (Algebraic, Analytic), `\llbracket`+`\rrbracket` (Local, Analytic, Howard, Applications). None defined in `macros/common.tex`. Must-fix: all render as raw TeX.
- **Covers problems**: 5 `.lean` files missing (all chapters) — expected; Lean has not been written yet.

---

## Unstarted-phase proposals

None. All 8 strategy phases have adequate blueprint coverage (≥3 meaningful declaration blocks). No proposals required.

---

## Per-chapter

### `Local_Iwasawa_Selmer.tex`
- **Complete**: false
- **Correct**: partial
- **Notes**:
  1. **MISSING `def:char-ideal`** — STRATEGY.md §Mathlib gaps explicitly requires a sorry-backed postulate block `def:char-ideal` with `\lean{MR4372220.Local.charIdeal}` in this chapter. It is absent. `char_Λ(...)` is used in Howard and Applications chapters but has no blueprint anchor. Must-fix.
  2. **Missing `\uses{thm:Katz}`** on `thm:mu-zero-theta`: proof invokes "Hida's vanishing of μ-invariant for the Katz p-adic L-function" — this is exactly what `thm:Katz` declares in the Analytic chapter. Either add cross-chapter edge or add a sorry-backed `lem:hida-mu-zero-char` here. Wire-up needed.
  3. **Broken ref `\ref{corcharacters}`** in `cor:characters` `% SOURCE:` comment — leandag picks this up; replace with plain text.
  4. **Missing `% SOURCE QUOTE PROOF:`** for `thm:mu-zero-theta` (proof cites Rubin MC + Hida — clearly source-derived) and `prop:lambda-theta` (proof steps directly follow source). Both proofs are thin for formalization: `thm:mu-zero-theta` needs the Shapiro's lemma identification spelled out (≥2 sub-steps).
  5. **Undefined macros**: `\llbracket`, `\rrbracket`.
  6. Proof sketches for `lem:commalg`, `lem:local-char-wneqp`, `lem:local-char-wp`, `cor:characters` are adequate.

### `Algebraic_Iwasawa_Comparison.tex`
- **Complete**: true
- **Correct**: partial
- **Notes**:
  1. **Missing edge**: `cor:lambda-E` \uses{prop:modp-E-tors} only — proof says "dual local cohomology at v̄ is Λ-cofree", invoking `lem:local-char-wp`. Must add `\uses{lem:local-char-wp}`. Wire-up.
  2. **Missing `% SOURCE QUOTE PROOF:`** for `MAINalgside` proof (clearly a translation of the source Thm MAINalgside).
  3. **Undefined macro**: `\mathds` (used for `\mathds{1}` in prop:modp-E and MAINalgside).
  4. All `% SOURCE:` pointers reference Eisenstein.tex which exists. ✓ SOURCE QUOTEs present. ✓ Visible `\textit{Source:}` present. ✓
  5. Proof sketches adequate for `prop:modp-E`, `prop:modp-E-tors`, `cor:lambda-E`, `MAINalgside`.

### `Analytic_Iwasawa_Comparison.tex`
- **Complete**: true
- **Correct**: partial
- **Notes**:
  1. **Missing edge**: `cor:Kriz` \uses{thm:kriz, def:iwasawa-algebra} — proof explicitly uses "Hida's theorem μ=0 for Katz p-adic L-functions" which is stated in `thm:Katz`. Must add `\uses{thm:Katz}`. Wire-up.
  2. **Broken ref `\S\ref{subsec:Lp}`** in visible `\textit{Source:}` line of `thm:BDP` — `subsec:Lp` is not a blueprint label; renders as "??". Replace with plain text.
  3. **Kriz congruence (`thm:kriz`)**: statement is correct — the N_+/N_- factorization and Euler-factor product formula match the source. Proof sketch (Serre–Tate, Kriz Thm 34 & Remark 32, measure construction) is detailed enough. ✓
  4. **`cor:Kriz` λ-formula proof**: the step "ψ = φ^{-1}ω implies λ(L_ψ) = λ(L_φ) via the functional equation for Katz L-functions" is stated without detail. For formalization this needs to be elaborated (≥1 sub-step citing the functional equation). Soon-fix.
  5. **`mulambda`**: correctly combines cor:Kriz and MAINalgside via Rubin's CM main conjecture. The Rubin input (λ(L_φ) = λ(X_φ)) is treated as an opaque background input — acceptable per strategy, but should note that Rubin's theorem is not declared as a blueprint postulate.
  6. **Undefined macros**: `\llbracket`, `\rrbracket`, `\mathds`.
  7. `% SOURCE QUOTE PROOF:` present for all 5 blocks. ✓ All source files exist. ✓

### `Howard_Kolyvagin.tex`
- **Complete**: partial
- **Correct**: true
- **Notes**:
  1. **thm:Zp-twisted sub-lemma gap**: proof sketch says "sub-splitting into the Čebotarev argument and the inductive Kolyvagin step is recommended" but declares no sub-lemmas. STRATEGY.md says "`thm:Zp-twisted` multi-page proof requires sub-splitting." For prover dispatch, at minimum two sub-lemma declarations are needed: `lem:cebotarev-kolyvagin` (Čebotarev choice of auxiliary primes) and `lem:kolyvagin-inductive-step` (the level-k length bound). Must-fix for Howard prover lane.
  2. **Howard Prop 1.5.5** (structural theorem on mod-m^k Selmer) is referenced in thm:Zp-twisted proof but not declared as a blueprint postulate or mathlibok. For formalization, this external structural input should be made explicit (sorry-backed `lem:howard-selmer-structure`). Soon-fix.
  3. **`def:selmer-triple`**: comprehensive, well-sourced. Three `% SOURCE QUOTE:` blocks, all from Eisenstein.tex. ✓
  4. **thm:howard proof**: detailed, height-one prime specialization argument spelled out, error term bounded. Adequate for formalization. ✓
  5. **thm:howard-HPKS proof**: Heegner point construction, Kolyvagin derivative operators, norm relations, Cornut–Vatsal nonvanishing — all mentioned. Adequate. ✓ \uses{def:selmer-triple, cor:characters} correctly captures residual exactness dependency. ✓
  6. **thm:howard-HP**: correctly combines thm:howard and thm:howard-HPKS. ✓
  7. **Undefined macros**: `\llbracket`, `\rrbracket`.
  8. All `% SOURCE QUOTE PROOF:` present. ✓

### `Main_Conjecture_Applications.tex`
- **Complete**: partial
- **Correct**: partial
- **Notes**:
  1. **κ_∞ missing declaration**: `prop:equiv-imc` formulation (i) and `cor:PR` both reference the BDP/Perrin-Riou Λ-adic class κ_∞ (written `κ_∞` in the chapter). It is never formally declared in the blueprint. For Lean formalization, this must be either declared as a sorry-backed postulate (e.g. `def:bdp-class`) or a `\mathlibok` anchor. Must-fix.
  2. **Spurious \uses{} in `prop:equiv-imc` statement**: `\uses{thm:howard-HP, mulambda, def:iwasawa-algebra}` — the STATEMENT of the equivalence does not logically depend on thm:howard-HP or mulambda; those are used to apply it in thm:thmA. Remove thm:howard-HP and mulambda from the statement's \uses{}, keep them in the proof's \uses{}. Must-fix (inflates DAG dependencies and harms prover ordering).
  3. **Spurious \uses{thm:thmB}** in `thm:thmC` statement: STRATEGY.md says "BSD rank-one formula...independent downstream lane; must not be blocked by p-converse lane." Having `thm:thmC \uses{thm:thmB}` creates an artificial sequencing dependency. The proof block correctly has `\uses{thm:thmA, def:iwasawa-algebra}` only — statement should match. Must-fix.
  4. **Anticyclotomic control theorem (JSW 3.3.1)** and **p-adic Gross–Zagier formula** used in thm:thmC proof are not declared as blueprint postulates. Two sorry-backed blocks needed: `thm:control-jsw` and `thm:padic-gz`. Without them the prover cannot close the BSD proof. Must-fix.
  5. **p-converse and BSD branches correctly separated**: §3 (thm:thmB, cor:thmB) and §4 (thm:thmC) are independent of each other in intent. ✓ (subject to fix 3 above)
  6. **thm:thmB proof**: both cases (r=0, r=1) spelled out with K-selection criteria, Kolyvagin theorem, GZ formula. Adequate. ✓
  7. **thm:thmC proof**: four steps clearly labeled. Uses JSW control theorem and p-adic GZ as black boxes — acceptable per strategy. Step 4 relies on Greenberg–Vatsal theorem for E^K — also an opaque external input, acceptable. ✓
  8. **Undefined macros**: `\llbracket`, `\rrbracket`.
  9. All `% SOURCE QUOTE:`, `% SOURCE QUOTE PROOF:`, `\textit{Source:}` present. ✓ Source file exists. ✓

---

## Cross-chapter notes

1. **`def:char-ideal` used but not declared**: `char_Λ(...)` appears in thm:howard, thm:howard-HP, thm:thmA, prop:equiv-imc, cor:PR, thm:thmC proof. No blueprint declaration. STRATEGY.md explicitly requires this in Local chapter. Blocking issue.
2. **Rubin CM main conjecture** used in `mulambda` proof (λ(L_φ) = λ(X_φ), λ(L_ψ) = λ(X_ψ)) but not declared as a sorry-backed lemma or mathlibok. Acceptable per strategy ("source-backed arithmetic inputs: Rubin"), but recommend adding an explicit `\mathlibok` anchor `lem:rubin-cm-mc` with note that Mathlib does not contain it yet (sorry-backed).
3. **lem:local-char-wp vs. label prefix**: declared as `\begin{proposition}` but labeled `lem:local-char-wp`. Minor inconsistency; no leandag impact. ✓

---

## DAG integrity (leandag)

- `leandag build --json`: 27 blueprint nodes, 54 edges, 0 isolated, 0 unknown_uses (no broken \uses{}). ✓
- All 27 `\lean{}` unmatched — expected (no .lean source yet).
- 1 axiom (def=0): `def:iwasawa-algebra` is the DAG root. ✓
- 2 leaves (rdep=0): `thm:thmC` and `cor:thmB` — the final results. ✓
- Wire-up findings: (i) add `cor:lambda-E \uses{lem:local-char-wp}`; (ii) add `cor:Kriz \uses{thm:Katz}`.
- Spurious-edge findings: (iii) remove `thm:howard-HP, mulambda` from `prop:equiv-imc` statement \uses{}; (iv) remove `thm:thmB` from `thm:thmC` statement \uses{}.

## Rendering (blueprint-doctor)

- **Undefined macros (must-fix)**: `\llbracket`, `\rrbracket` — missing from macros/common.tex; used in Local, Analytic, Howard, Applications. Recommend adding `\newcommand{\llbracket}{\mathopen{\lBrack}}` + `\newcommand{\rrbracket}{\mathclose{\rBrack}}` (or use `\usepackage{stmaryrd}`) to common.tex.
- **Undefined macro**: `\mathds` — used in Algebraic and Analytic chapters. Recommend `\usepackage{bbm}` or `\usepackage{dsfont}` in preamble + `\newcommand{\mathds}{\mathbb}` as fallback.
- **Broken refs**: `\ref{corcharacters}` in Local chapter (% SOURCE: comment, but doctor flags it); `\S\ref{subsec:Lp}` in Analytic chapter visible \textit{Source:} line. Both must be replaced with plain text.
- **covers_problems**: all 5 .lean files missing — expected.

---

## Severity summary

- **must-fix (blocks HARD GATE or prover dispatch)**:
  1. `Local_Iwasawa_Selmer.tex`: add `def:char-ideal` sorry-backed postulate block.
  2. `Local_Iwasawa_Selmer.tex`: fix broken `\ref{corcharacters}` in cor:characters % SOURCE: line.
  3. `Howard_Kolyvagin.tex`: declare `lem:cebotarev-kolyvagin` and `lem:kolyvagin-inductive-step` sub-lemmas for thm:Zp-twisted.
  4. `Main_Conjecture_Applications.tex`: declare `def:bdp-class` (κ_∞) sorry-backed postulate.
  5. `Main_Conjecture_Applications.tex`: declare `thm:control-jsw` and `thm:padic-gz` sorry-backed postulates (JSW control theorem and p-adic GZ formula used in thm:thmC proof).
  6. `Main_Conjecture_Applications.tex`: remove `thm:howard-HP, mulambda` from `prop:equiv-imc` statement \uses{}.
  7. `Main_Conjecture_Applications.tex`: remove `thm:thmB` from `thm:thmC` statement \uses{}.
  8. `Algebraic_Iwasawa_Comparison.tex`: add `lem:local-char-wp` to `cor:lambda-E` \uses{}.
  9. `Analytic_Iwasawa_Comparison.tex`: add `thm:Katz` to `cor:Kriz` \uses{}; fix broken `\S\ref{subsec:Lp}`.
  10. **macros/common.tex**: add `\llbracket`, `\rrbracket`, `\mathds` definitions (blocks rendering in 4 chapters).

- **soon (does not block gate but needed before prover can complete)**:
  11. `Local_Iwasawa_Selmer.tex`: add wire-up or sorry-backed anchor for Hida μ=0 used in thm:mu-zero-theta; add `% SOURCE QUOTE PROOF:` for thm:mu-zero-theta and prop:lambda-theta; flesh out thm:mu-zero-theta proof sketch (Shapiro's lemma identification step).
  12. `Algebraic_Iwasawa_Comparison.tex`: add `% SOURCE QUOTE PROOF:` for MAINalgside.
  13. `Analytic_Iwasawa_Comparison.tex`: flesh out the ψ = φ^{-1}ω functional-equation step in cor:Kriz proof.
  14. `Howard_Kolyvagin.tex`: add sorry-backed `lem:howard-selmer-structure` for Howard Prop 1.5.5.
  15. Cross-chapter: add sorry-backed or mathlibok anchor for Rubin CM main conjecture (used in mulambda proof).

## HARD GATE summary

| Chapter | complete | correct | gate |
|---|---|---|---|
| Local_Iwasawa_Selmer.tex | false | partial | BLOCKED |
| Algebraic_Iwasawa_Comparison.tex | true | partial | BLOCKED |
| Analytic_Iwasawa_Comparison.tex | true | partial | BLOCKED |
| Howard_Kolyvagin.tex | partial | true | BLOCKED |
| Main_Conjecture_Applications.tex | partial | partial | BLOCKED |

All gates blocked. No prover dispatch is safe until must-fix items 1–10 are addressed.
Blueprint-writer directives needed for: Local (def:char-ideal + must-fix 2, 11), Algebraic (must-fix 8, 12), Analytic (must-fix 9, 13), Howard (must-fix 3, 14), Applications (must-fix 4–7), and macros/common.tex (must-fix 10).
