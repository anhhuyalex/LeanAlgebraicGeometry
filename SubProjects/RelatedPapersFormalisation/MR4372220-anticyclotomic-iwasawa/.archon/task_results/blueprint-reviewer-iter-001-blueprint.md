# Blueprint Review: iter-001-blueprint
**Iter:** 001

## Top-level summaries
- **Incomplete**: `blueprint/src/chapters/Overview.tex` is a 1-paragraph scaffold; no `\definition`/`\lemma`/`\theorem` blocks, no `\uses{}`, no `\lean{}` targets.
- **Route**: the single Greenberg-Vatsal spine is uncovered; all 5 active STRATEGY phases still have zero blueprint coverage.
- **Deps/Rendering**: `.leandag/dag.json` has `0` nodes / `0` edges / `0` blueprint decls; `archon blueprint-doctor --json` is clean (`no malformed_refs`, `no broken_refs`, `no covers problems`).

## Unstarted-phase proposals
### Proposed chapter: `blueprint/src/chapters/Local_Iwasawa_Selmer.tex`
**Covers**: future `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Local.lean` + umbrella imports from the current root files
**Strategy phase**: Local Iwasawa and Selmer foundations
**Why now**: this fixes the shared notation/local exactness once, so algebraic, analytic, and Kolyvagin chapters can reuse it in parallel.

**Key declarations** (in dependency order):
1. `\definition` `\label{def:iwasawa-algebra}` — `\Lambda`, `\Lambda^{ur}`, `M_\theta`, `M_E`, the Gr/Ord Selmer structures, and imprimitive variants. `\lean{MR4372220.Local.iwasawaAlgebra}` [expected]. Source: `references/MR4372220-anticyclotomic-iwasawa.tex` Introduction; `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` §Algebraic side (`Local cohomology groups of characters`, `Selmer groups of characters`, `Local cohomology groups of E`, `Selmer groups of E`).
2. `\lemma` `\label{lem:local-char-wneqp}` — split `w\nmid p`: `char_\Lambda H^1(K_w,M_\theta)^\vee=(\mathcal P_w(\theta))`, `\mu=0`. `\lean{MR4372220.Local.localCohomologySplit}` [expected]. Source: `lemmawneqp`.
3. `\lemma` `\label{lem:local-char-wp}` — `w\mid p`: `H^1(K_w,M_\theta)` is `\Lambda`-cofree of rank `1` under `\theta|_{G_w}\neq 1,\omega`. `\lean{MR4372220.Local.localCohomologyAtP}` [expected]. Source: `propw=v`.
4. `\theorem` `\label{thm:mu-zero-theta}` — Rubin/Hida: `\mathfrak X_\theta` is torsion and `\mu=0`. `\lean{MR4372220.Local.muZeroTheta}` [expected]. Source: `thmmu=0`.
5. `\prop` `\label{prop:lambda-theta}` — imprimitive residual Selmer finite and `\dim_{\mathbb F_p} = \lambda(\mathfrak X_\theta^S)`. `\lean{MR4372220.Local.lambdaTheta}` [expected]. Source: `propchar`, `corcharacters`.

**`\uses` skeleton**:
- `thm:mu-zero-theta` uses `lem:local-char-wneqp`, `lem:local-char-wp`, Rubin/Hida.
- `prop:lambda-theta` uses `thm:mu-zero-theta`, `lem:local-char-wneqp`, `lem:local-char-wp`, `lem:commalg`.

**Main theorem proof strategy**: compute local cohomology at split and `p`-adic places via class field theory/Tate duality, package the primitive/imprimitive exact sequences, then invoke Rubin/Hida plus the structure theorem to convert `\mu=0` into the `\lambda` formula.

**References for writer**:
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` → §Algebraic side, subsections `Local cohomology groups of characters`, `Selmer groups of characters`, `Local cohomology groups of E`, `Selmer groups of E`.
- `references/MR4372220-anticyclotomic-iwasawa.tex` → Introduction `Statement of the main results`, `Method of proof and outline of the paper`.

### Proposed chapter: `blueprint/src/chapters/Algebraic_Iwasawa_Comparison.tex`
**Covers**: future `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Algebraic.lean` + umbrella imports
**Strategy phase**: Algebraic Iwasawa invariant comparison
**Why now**: this is independent of the analytic side once the local Selmer interface is fixed, so it can be written and checked in parallel.

**Key declarations** (in dependency order):
1. `\prop` `\label{prop:modp-E}` — exact sequence comparing `M_E[p]` with `M_\phi[p]` and `M_\psi[p]`, plus the residual Selmer sequence. `\lean{MR4372220.Algebraic.residualComparison}` [expected]. Source: `cormodp`.
2. `\prop` `\label{prop:modp-E-tors}` — `\mathfrak X_E^S` and `\mathfrak X_E` are `\Lambda`-torsion with `\mu=0`; `M[p]` vs `M` comparison. `\lean{MR4372220.Algebraic.muZeroE}` [expected]. Source: `propmodp`.
3. `\cor` `\label{cor:lambda-E}` — no finite `\Lambda`-submodules and `\lambda(\mathfrak X_E^S)=\dim_{\mathbb F_p} H^1_{\Fcal_{\rm Gr}^S}(K,M_E[p])`. `\lean{MR4372220.Algebraic.lambdaE}` [expected]. Source: `prop426`.
4. `\theorem` `\label{MAINalgside}` — algebraic comparison theorem for `\lambda(\mathfrak X_E)` vs `\lambda(\mathfrak X_\phi),\lambda(\mathfrak X_\psi)` and local Euler factors. `\lean{MR4372220.Algebraic.mainAlgSide}` [expected]. Source: `Comparison I: Algebraic Iwasawa invariants`.

**`\uses` skeleton**:
- `prop:modp-E` uses `corcharacters`.
- `prop:modp-E-tors` uses `prop:modp-E`.
- `cor:lambda-E` uses `prop:modp-E-tors`, `propchar`.
- `MAINalgside` uses `cor:lambda-E`, `propchar`, `prop:modp-E-tors`.

**Main theorem proof strategy**: build the residual exact sequence for `E[p]`, identify the character Selmer pieces by the local-character chapter, compare primitive/imprimitive Selmer groups via exactness and pseudo-null control, then turn the character `\lambda` formulas into the `E` formula.

**References for writer**:
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` → §Algebraic side, subsections `Local cohomology groups of E`, `Selmer groups of E`, `Comparison I: Algebraic Iwasawa invariants`.

### Proposed chapter: `blueprint/src/chapters/Analytic_Iwasawa_Comparison.tex`
**Covers**: future `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Analytic.lean` + umbrella imports
**Strategy phase**: Analytic p-adic L-function comparison
**Why now**: the BDP/Katz/Kriz side is independent once the local algebra is fixed, and it supplies the matching `\mu/\lambda` comparison needed later.

**Key declarations** (in dependency order):
1. `\theorem` `\label{thm:BDP}` — construct `\mathcal L_E` with the BDP interpolation formula. `\lean{MR4372220.Analytic.bdpLFunction}` [expected]. Source: `thm:BDP`.
2. `\theorem` `\label{thm:Katz}` — construct `\mathcal L_\theta` with the Katz interpolation formula. `\lean{MR4372220.Analytic.katzLFunction}` [expected]. Source: `thm:Katz`.
3. `\theorem` `\label{thm:kriz}` — Kriz congruence `\mathcal L_E \equiv (\mathcal E_{\phi,\psi}^\iota)^2(\mathcal L_\phi)^2 \bmod p`. `\lean{MR4372220.Analytic.krizCongruence}` [expected]. Source: `thm:kriz`.
4. `\theorem` `\label{cor:Kriz}` + `\theorem` `\label{mulambda}` — `\mu/\lambda` comparison for `\mathcal L_E`, then `\lambda(\mathcal L_E)=\lambda(\mathfrak X_E)`. `\lean{MR4372220.Analytic.kriZLambda}` / `\lean{MR4372220.Analytic.mulambda}` [expected]. Source: `cor:Kriz`, `mulambda`.

**`\uses` skeleton**:
- `thm:kriz` uses `thm:BDP`, `thm:Katz`.
- `cor:Kriz` uses `thm:kriz`.
- `mulambda` uses `MAINalgside`, `cor:Kriz`.

**Main theorem proof strategy**: define the two anticyclotomic `p`-adic `L`-functions, use Kriz’s Eisenstein congruence to compare BDP with Katz factors modulo `p`, then compute `\mu` and `\lambda` via the involution and local Euler-factor bookkeeping.

**References for writer**:
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` → §Analytic side, subsections `p-adic L-functions`, `Katz p-adic L-functions`, `Comparison II: Analytic Iwasawa invariants`.
- `references/MR4372220-anticyclotomic-iwasawa.tex` → Introduction `Method of proof and outline of the paper` (for the `\mu/\lambda` comparison role).

### Proposed chapter: `blueprint/src/chapters/Howard_Kolyvagin.tex`
**Covers**: future `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Howard.lean` + umbrella imports
**Strategy phase**: Howard/Kolyvagin system argument
**Why now**: this is the sequential bottleneck; it needs a staged blueprint before any prover work.

**Key declarations** (in dependency order):
1. `\definition` `\label{def:selmer-triple}` — Selmer structures, Selmer triples, modified local conditions, finite-singular comparison. `\lean{MR4372220.Howard.selmerTriple}` [expected]. Source: `IMCIII` `Selmer structures and Kolyvagin systems`.
2. `\theorem` `\label{thm:Zp-twisted}` — bound Selmer groups for anticyclotomic twists, with the explicit error term. `\lean{MR4372220.Howard.zpTwistedBound}` [expected]. Source: `Bounding Selmer groups`.
3. `\theorem` `\label{thm:howard}` — `\Lambda`-adic specialization of the Kolyvagin bound at height-one primes. `\lean{MR4372220.Howard.howardBound}` [expected]. Source: `Proof of Theorem~\ref{thm:howard}`.
4. `\theorem` `\label{thm:howard-HPKS}` — Heegner points produce a nonzero Kolyvagin system. `\lean{MR4372220.Howard.heegnerKolyvaginSystem}` [expected]. Source: `Proof of Theorem~\ref{thm:howard-HPKS}`.
5. `\theorem` `\label{thm:howard-HP}` — combine Howard + Heegner KS to get the divisibility needed downstream. `\lean{MR4372220.Howard.heegnerHoward}` [expected]. Source: `Proof of Theorem~\ref{thm:howard-HP}`.

**`\uses` skeleton**:
- `thm:Zp-twisted` uses `def:selmer-triple`, `lemmamod`, `propstructure`, `prop:prime2`, `lem:image1`, `lem:image2`.
- `thm:howard` uses `thm:Zp-twisted`.
- `thm:howard-HPKS` uses Heegner norm relations + Cornut-Vatsal nonvanishing.
- `thm:howard-HP` uses `thm:howard`, `thm:howard-HPKS`, `cor:howard`.

**Main theorem proof strategy**: first prove the general `Z_p`-twisted length bound by controlling specializations and the error term; then specialize at height-one primes of `\Lambda` to get Howard’s divisibility. Separately construct the Heegner-point Kolyvagin system and feed it into the abstract theorem.

**References for writer**:
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` → §A Kolyvagin system argument, subsections `Selmer structures and Kolyvagin systems`, `Bounding Selmer groups`, `Proof of Theorem~\ref{thm:Zp-twisted}`, `Proof of Theorem~\ref{thm:howard-HPKS}`, `Proof of the Iwasawa main conjectures`.
- `references/MR4372220-anticyclotomic-iwasawa.tex` → `Method of proof and outline of the paper` (for the role of the error term).

**Subphase choices exposed**:
- Choice A: one chapter for both the abstract Howard bound and the Heegner-point KS construction.
- Choice B: split into `Howard_Bounds.tex` and `Howard_HeegnerPoints.tex`. Recommendation: B, because the abstract specialization argument and the Heegner-point construction are separately reusable and the latter is the tighter source-heavy piece.

### Proposed chapter: `blueprint/src/chapters/Main_Conjecture_Applications.tex`
**Covers**: future `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Applications.lean` + umbrella imports
**Strategy phase**: Main conjecture and arithmetic applications
**Why now**: this is downstream only; it should stay downstream and reuse the comparison theorems verbatim.

**Key declarations** (in dependency order):
1. `\prop` `\label{prop:equiv-imc}` — equivalence between the Heegner-point and BDP main conjectures. `\lean{MR4372220.Applications.equivImc}` [expected]. Source: `Proof of the Iwasawa main conjectures`.
2. `\theorem` `\label{thm:thmA}` — anticyclotomic main conjecture at Eisenstein primes. `\lean{MR4372220.Applications.mainConjectureA}` [expected]. Source: `Proof of the Iwasawa main conjectures`.
3. `\cor` `\label{cor:PR}` — Perrin-Riou Heegner-point main conjecture. `\lean{MR4372220.Applications.perrinRiou}` [expected]. Source: `Proof of the Iwasawa main conjectures`.
4. `\theorem` `\label{thm:thmB}` + `\cor` `\label{cor:thmB}` — the `p`-converse to Gross--Zagier--Kolyvagin and its mod-`p` corollary. `\lean{MR4372220.Applications.pConverse}` [expected]. Source: introduction `Theorem~\ref{thm:E}` and the proof paragraphs after it.
5. `\theorem` `\label{thm:thmC}` — the `p`-part of BSD in analytic rank `1`. `\lean{MR4372220.Applications.bsdPPart}` [expected]. Source: `Proof of the p-part of BSD formula`.

**`\uses` skeleton**:
- `prop:equiv-imc` uses `thm:howard-HP`, `mulambda`.
- `thm:thmA` uses `prop:equiv-imc`, `thm:howard-HP`, `mulambda`.
- `cor:PR` uses `thm:thmA`, `thm:howard-HP`.
- `thm:thmB` uses `cor:PR`, Gross--Zagier/Kolyvagin input, twist-selection lemma.
- `thm:thmC` uses `thm:thmA`, `thm:thmB`, `controlthm`, `thmGZ`, `thmGV`.

**Main theorem proof strategy**: isolate the equivalence between the two main-conjecture formulations, derive `thm:thmA` from Howard plus the `\mu/\lambda` comparisons, then keep the arithmetic applications strictly downstream: `thm:thmB` via a suitable quadratic field `K`, and `thm:thmC` via the BSD/Gross--Zagier control-theorem bookkeeping.

**References for writer**:
- `references/MR4372220-anticyclotomic-iwasawa.tex` → Introduction `Statement of the main results`, `Method of proof and outline of the paper`, and the theorem statements for `thm:E`, `thm:F`.
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` → §Proof of the Iwasawa main conjectures, `§Proof of Theorem~\ref{thm:E}`, `§Proof of Theorem~\ref{thm:F}`.

**Subphase choices exposed**:
- Choice A: one combined downstream chapter for `thm:thmA` through `thm:thmC`.
- Choice B: split into a main-conjecture chapter, a `p`-converse chapter, and a BSD chapter. Recommendation: B, because the BSD proof uses extra control-theorem and Gross--Zagier bookkeeping that should not be interleaved with the main-conjecture formalism.

## Per-chapter
### `Overview.tex`
- **Complete**: false
- **Correct**: true
- **Notes**: only a chapter title, one `% archon:covers` comment, and one sentence; no proof blocks, no `\uses{}`, no `\lean{}` hints, and no source-backed statements to audit yet.

## Severity summary
- **must-fix**: expand `Overview.tex` into phase-bearing blueprint chapters before any prover objectives; all 5 active STRATEGY phases are currently uncovered.
