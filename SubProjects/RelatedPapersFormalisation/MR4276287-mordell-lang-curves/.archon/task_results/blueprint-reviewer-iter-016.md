# Blueprint Review: iter-016
**Iter:** 016

## Top-level summaries

- **Undefined macros (rendering broken)**: `MR4276287UniformityInMordellLangForCurves.tex` — `\IQbar` (→ `\overline{\mathbb{Q}}`), `\IR` (→ `\mathbb{R}`) not in any macros/*.tex; `MR4276287UniformityInMordellLangForCurves_Basic.tex` — `\hcA` (→ `h_{\overline{\mathcal{A}}}` per paper macros.tex), `\intercal` (requires amssymb — add `\usepackage{amssymb}` or add `\newcommand{\intercal}{\intercal}` after loading amssymb in print.tex/web.tex) not in macros/*.tex.
- **Wrong \uses{} edge**: `prop:aux_ht_ineq` statement lists `thm:silverman_tate` in `\uses{}` but ST is NOT used in the auxiliary height inequality (ST enters only in `thm:ht_inequality` proof). Remove `thm:silverman_tate` from `prop:aux_ht_ineq` statement's `\uses{}`.
- **Missing declarations (undeclared proof inputs)**: `thm:bd_rat_intro` proof invokes Rémond's quantitative Mordell-Lang bound (not declared); `thm:bd_tor_intro_nf` proof invokes Raynaud's Manin-Mumford theorem (not declared). Both need either `\mathlibok` anchors (if in Mathlib) or project lemma stubs.
- **Missing dependency anchors**: Northcott's theorem used in both `thm:bd_rat_intro` and `thm:bd_tor_intro_nf` proofs with no `\mathlibok` or lemma declaration.
- **Citation discipline**: `lem:moduli_height_comparison` — `% SOURCE QUOTE PROOF:` duplicates the statement-level `% SOURCE QUOTE:` verbatim; it should quote from the proof of the lemma in the source, not restate the statement; `def:ambient_setup` — has `% SOURCE QUOTE PROOF:` ("This section fixes...") that is non-verbatim and appears inside a definition block with no `\begin{proof}`; `Overview.tex` — `% SOURCE QUOTE: "the number of rational points is bounded"` is a truncated paraphrase (not verbatim from abstract); `% SOURCE QUOTE PROOF:` in Overview.tex is a meta-comment, not a source-verbatim quote.
- **Proof sketch too thin**: `thm:nondeg_for_bd` proof uses `\cite[Theorem~1.3]{GaoBettiRank}` and `\cite[Lemma~1.11]{OortSteenbrink}` as black boxes with no Lean-level breakdown of the three conditions (a), (b), (c) needed to apply Gao's theorem. A prover will need these conditions made explicit.
- **Unstarted phases**: 6 of 15 strategy phases have no blueprint coverage (< 3 meaningful declaration blocks). See proposals below.
- **Multi-route coverage**: Route 2 (sorry-first analytic-black-box) has zero blueprint coverage — no `Analytic.lean` stub chapter, no axiom stubs for `prop:betti_map`, `prop:betti_form`, `prop:betti_map_app`. Route 1 is PARTIAL (Betti and height inequality covered; Setup phases missing).

---

## Unstarted-phase proposals

### Proposed: `blueprint/src/chapters/ModuliSpace.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/ModuliSpace.lean` | **Phase**: Setup: M_g with level structure
- **Why now**: All counting theorems use `def:ambient_setup` as a black box; a prover cannot formalize `def:ambient_setup` without knowing what M_g, ℓ-structure, and the universal curve look like as Lean types.
- **Key defs** (dependency order):
  1. `\definition` `\label{def:level_structure}` — Level-ℓ structure on a smooth curve (principal level structure as kernel of the mod-ℓ map on the Jacobian). `\lean{MR4276287UniformityInMordellLangForCurves.ModuliSpace.LevelStructure}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`, §1.
  2. `\definition` `\label{def:Mg_level}` — Fine moduli space M_{g,ℓ} of smooth genus-g curves with level-ℓ structure (functor of families + representability by a quasi-projective variety). `\lean{MR4276287UniformityInMordellLangForCurves.ModuliSpace.M_g_level}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`.
  3. `\definition` `\label{def:universal_curve}` — Universal curve C_g → M_g (smooth proper with genus-g fibers). `\lean{MR4276287UniformityInMordellLangForCurves.ModuliSpace.universalCurve}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`, "There exists a universal curve...".
  4. `\proposition` `\label{prop:Mg_quasiprojective}` — M_g is quasi-projective over Spec ℤ[1/ℓ]; it admits a compactification M̄_g. `\lean{MR4276287UniformityInMordellLangForCurves.ModuliSpace.Mg_quasiProjective}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`.
  5. `\lemma` `\label{lem:torelli_quasi_finite}` — The Torelli map τ: M_g → A_g is quasi-finite. `\lean{MR4276287UniformityInMordellLangForCurves.ModuliSpace.torelli_quasiFinite}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` / OortSteenbrink [Lemma 1.11].
- **`\uses` skeleton**:
  - `def:universal_curve` uses `def:Mg_level`
  - `prop:Mg_quasiprojective` uses `def:Mg_level`
  - `lem:torelli_quasi_finite` uses `def:Mg_level`, `def:universal_curve`
- **Main theorem proof strategy**: M_g as a representable functor is standard (DM stack theory). The quasi-projectivity is a classical result of Mumford; in Lean it is a project-specific construction. The Torelli quasi-finiteness is cited as [OortSteenbrink, Lemma 1.11] — the proof strategy is: Torelli injective on ppavs of the same dimension, hence the fibers are discrete, hence quasi-finite.
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` §1-2; retrieval needed for OortSteenbrink "The local Torelli problem for curves" if not in local files.
- **Subphase choices**: Whether to define M_g as a coarse moduli space (easier in Lean) vs. fine moduli with level structure (needed by the paper). Recommendation: define fine moduli with level structure (per the paper) and axiomatize the DM-stack machinery needed.

---

### Proposed: `blueprint/src/chapters/Jacobian.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/Jacobian.lean` | **Phase**: Setup: Jacobian variety of genus-g curve
- **Why now**: CONFIRMED MISSING from Mathlib; every downstream result depends on Jac(C) as an abelian variety; without this chapter no prover can work on NT height, Abel-Jacobi, or counting results.
- **Key defs** (dependency order):
  1. `\definition` `\label{def:jacobian_av}` — Jacobian Jac(C) of a smooth genus-g curve C as a principally polarized abelian variety of dimension g. `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.Jacobian}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` §2 / standard reference (Mumford "Abelian Varieties", §2).
  2. `\lemma` `\label{lem:jacobian_ppav}` — Jac(C) carries a canonical principal polarization. `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.jacobian_ppav}` [expected]. Source: Mumford §6.
  3. `\definition` `\label{def:abel_jacobi}` — Abel-Jacobi embedding ι_{P0}: C → Jac(C) sending P ↦ [P - P0]. `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.abelJacobi}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/RatPt.tex` §1.
  4. `\theorem` `\label{thm:abel_jacobi_closed}` — The Abel-Jacobi map is a closed immersion (for g ≥ 2). `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.abelJacobi_closedImmersion}` [expected]. Source: standard.
  5. `\definition` `\label{def:faltings_zhang}` — Faltings-Zhang morphism D_M: C^[M+1] → Jac(C)^M for M ≥ 1. `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.faltingsZhang}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` §2 / "We consider the product C_g ×_{M_g} S → C_g^{[2]} composed with the Faltings-Zhang morphism".
  6. `\lemma` `\label{lem:curve_generates_jacobian}` — For g ≥ 2, the image of C under Abel-Jacobi generates Jac(C) as an abelian variety. `\lean{MR4276287UniformityInMordellLangForCurves.Jacobian.curve_generates_jacobian}` [expected]. Source: standard (Gao uses this in Theorem 1.3 conditions).
- **`\uses` skeleton**:
  - `lem:jacobian_ppav` uses `def:jacobian_av`
  - `def:abel_jacobi` uses `def:jacobian_av`
  - `thm:abel_jacobi_closed` uses `def:abel_jacobi`
  - `def:faltings_zhang` uses `def:jacobian_av`, `def:abel_jacobi`
  - `lem:curve_generates_jacobian` uses `def:abel_jacobi`, `def:jacobian_av`
- **Main theorem proof strategy**: Jac(C) is built via the Picard group / line bundles of degree 0. The principal polarization comes from the theta divisor. Abel-Jacobi is the classical embedding. The Faltings-Zhang morphism is the diagonal sum construction. Since all this is missing from Mathlib, consider axiomatizing Jac(C) as `[Axiom]` stubs first (Route 2 strategy applied to algebra).
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` §2; retrieval needed for Mumford "Abelian Varieties" if not local.
- **Subphase choices**: Axiom-stub approach (define `noncomputable def Jacobian : AbelianVariety` and state properties as axioms, fill later) vs. full Picard-group construction. Recommendation: axiom stubs for iter-017 to unblock downstream; return to full construction later.

---

### Proposed: `blueprint/src/chapters/Torelli.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/Torelli.lean` | **Phase**: Setup: Torelli map and universal Jacobian family
- **Why now**: The counting arguments assume the Torelli map τ: M_g → A_g and the universal abelian family A_g → A_g; without explicit declarations, the proof of `lem:moduli_height_comparison` and `thm:bd_fin_rank` cannot be formalized.
- **Key defs** (dependency order):
  1. `\definition` `\label{def:Ag_level}` — Siegel moduli space A_{g,ℓ} of principally polarized abelian varieties with level-ℓ structure. `\lean{MR4276287UniformityInMordellLangForCurves.Torelli.A_g_level}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex` / `SettingUp.tex`.
  2. `\definition` `\label{def:universal_av}` — Universal principally polarized abelian variety A_g → A_g (the universal family). `\lean{MR4276287UniformityInMordellLangForCurves.Torelli.universalAV}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex`.
  3. `\definition` `\label{def:torelli_map}` — Torelli morphism τ: M_g → A_g sending [C] ↦ [Jac(C)]. `\lean{MR4276287UniformityInMordellLangForCurves.Torelli.torelliMap}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`.
  4. `\theorem` `\label{thm:torelli_injective}` — Torelli theorem: τ is injective on k̄-points (two curves with isomorphic Jacobians are isomorphic). `\lean{MR4276287UniformityInMordellLangForCurves.Torelli.torelli_injective}` [expected]. Source: standard (Torelli's theorem).
  5. `\lemma` `\label{lem:universal_jacobian_fib}` — The fiber of A_g over τ(s) is the Jacobian Jac(C_s). `\lean{MR4276287UniformityInMordellLangForCurves.Torelli.universalJacobianFiber}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`.
- **`\uses` skeleton**:
  - `def:universal_av` uses `def:Ag_level`
  - `def:torelli_map` uses `def:Mg_level` (from ModuliSpace.tex), `def:Ag_level`, `def:jacobian_av` (from Jacobian.tex)
  - `thm:torelli_injective` uses `def:torelli_map`
  - `lem:universal_jacobian_fib` uses `def:torelli_map`, `def:universal_av`, `def:jacobian_av`
- **Main theorem proof strategy**: Torelli injectivity is a deep classical theorem; for the project, the strategy is to state it as `\mathlibok` if available or as a project axiom, then prove that A_{g,ℓ} is the universal family using the fine moduli property. The fiber identification follows from universality.
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` §1-2, `references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex` §2.
- **Subphase choices**: Whether to merge Torelli into ModuliSpace.tex (consolidated chapter via `archon:covers`). Recommendation: keep separate — Torelli introduces A_g which is architecturally distinct from M_g.

---

### Proposed: `blueprint/src/chapters/WeilHeight.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/WeilHeight.lean` | **Phase**: Canonical-height: Weil heights on abelian varieties + Néron-Tate limit
- **Why now**: `thm:silverman_tate` is declared but the Weil height `h` and NT height `\hat{h}` are used throughout the blueprint without being declared; a prover needs their signatures before formalizing any downstream result.
- **Key defs** (dependency order):
  1. `\mathlibok` `\label{thm:weil_height_mathlib}` — Weil height `Height.logHeight` / `Height.mulHeight` on projective space is in Mathlib.NumberTheory.Height.Basic. `\lean{Mathlib.NumberTheory.Height.logHeight}`. Source: Mathlib.
  2. `\definition` `\label{def:height_fib}` — Height on the total space: for P ∈ A(k̄) the naive height h(P) := h_{proj}(ι(P)) where ι: Ā → P^n is the compactification embedding. `\lean{MR4276287UniformityInMordellLangForCurves.WeilHeight.fiberwiseHeight}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/silvermantate.tex` §A.
  3. `\mathlibok` `\label{thm:northcott_mathlib}` — Northcott's theorem: there are only finitely many k̄-points of bounded degree and height. `\lean{Mathlib.NumberTheory.Height.Northcott}` [expected — verify Mathlib name]. Source: Mathlib.
  4. `\definition` `\label{def:nt_height}` — Néron-Tate height: \hat{h}_A(P) := lim_{N→∞} h([2^N]P)/4^N. `\lean{MR4276287UniformityInMordellLangForCurves.WeilHeight.neronTateHeight}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/silvermantate.tex`.
  5. `\proposition` `\label{prop:nt_quadratic}` — NT height is a quadratic function: \hat{h}([N]P) = N²\hat{h}(P). `\lean{MR4276287UniformityInMordellLangForCurves.WeilHeight.nt_quadratic}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/silvermantate.tex` / `NTbase.tex`.
  6. `\proposition` `\label{prop:nt_nonneg}` — NT height is non-negative with \hat{h}(P) = 0 iff P is torsion. `\lean{MR4276287UniformityInMordellLangForCurves.WeilHeight.nt_nonneg}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/silvermantate.tex`.
- **`\uses` skeleton**:
  - `def:height_fib` uses `thm:weil_height_mathlib`
  - `def:nt_height` uses `def:height_fib`, `def:ambient_setup`
  - `prop:nt_quadratic` uses `def:nt_height`
  - `prop:nt_nonneg` uses `def:nt_height`
  - `thm:silverman_tate` (existing) uses `def:nt_height`, `def:height_fib`
- **Main theorem proof strategy**: NT height defined as Cauchy limit via duplication bound (already in `thm:silverman_tate` proof). Quadraticity: \hat{h}([N]P) = lim h([2^k]([N]P))/4^k = N²·lim h([2^k]P)/4^k. Non-negativity requires that h ≥ 0 on the fiber and the bound |h(P) - \hat{h}(P)| ≤ c·h(π(P)): if h(π(P)) = 0 then \hat{h} = h(P) ≥ 0 up to bounded error.
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/silvermantate.tex` (Appendix A), `references/MR4276287-mordell-lang-curves-source/NTbase.tex` §5.
- **Subphase choices**: Merge NT limit and Weil height into one chapter (recommended — they're tightly coupled) vs. split. The existing `thm:silverman_tate` already lives in Basic.tex; this chapter provides the foundational declarations that Basic.tex should `\uses{}`. Note: `thm:silverman_tate` should gain `\uses{def:nt_height}` once WeilHeight.tex is written.

---

### Proposed: `blueprint/src/chapters/Positivity.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/Positivity.lean` | **Phase**: Canonical-height: IsNef/IsBig positivity wrappers
- **Why now**: `prop:aux_ht_ineq` proof invokes Siu's bigness criterion `\cite[Theorem~2.2.15]{PosAlgGeom}` as a black box; a prover needs these as declared lemmas with Lean signatures.
- **Key defs** (dependency order):
  1. `\definition` `\label{def:nef}` — IsNef: a line bundle L on X is nef if deg(L|_C) ≥ 0 for every irreducible curve C ⊂ X. `\lean{MR4276287UniformityInMordellLangForCurves.Positivity.IsNef}` [expected]. Source: Lazarsfeld "Positivity in Algebraic Geometry" §1.4 — retrieval needed (no local file).
  2. `\definition` `\label{def:big}` — IsBig: a line bundle L on X is big if h⁰(X, L^⊗m) grows like m^{dim X}. `\lean{MR4276287UniformityInMordellLangForCurves.Positivity.IsBig}` [expected]. Source: Lazarsfeld §2.2 — retrieval needed.
  3. `\theorem` `\label{thm:siu_criterion}` — Siu bigness criterion: if L, M are nef on an n-dimensional X and (L^n) > n·(M·L^{n-1}), then L^⊗q ⊗ M^⊗{-1} is big for some q. `\lean{MR4276287UniformityInMordellLangForCurves.Positivity.siuCriterion}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` — cite `[Theorem~2.2.15]{PosAlgGeom}` (Lazarsfeld).
  4. `\lemma` `\label{lem:nef_intersection}` — Intersection numbers are well-defined and multilinear on nef bundles (arithmetic Bézout for nef). `\lean{MR4276287UniformityInMordellLangForCurves.Positivity.nefIntersection}` [expected]. Source: Lazarsfeld §1.6 — retrieval needed.
- **`\uses` skeleton**:
  - `thm:siu_criterion` uses `def:nef`, `def:big`, `lem:nef_intersection`
  - `prop:aux_ht_ineq` (existing in Basic.tex) should `\uses{thm:siu_criterion, def:nef}` — current `\uses{}` is missing these
- **Main theorem proof strategy**: Siu's criterion is a consequence of the Nakai-Moishezon criterion + ampleness after twisting. In the project, it is cited as a black box from Lazarsfeld — state as `sorry`-stub theorem with the intersection-number hypothesis explicitly quantified. Defer the Nakai-Moishezon proof to a future phase.
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` §4; retrieval needed: Lazarsfeld "Positivity in Algebraic Geometry I" Theorem 2.2.15 (no local file exists).
- **Subphase choices**: Merge IsNef/IsBig into ArithBezout.tex vs. keep separate. Recommendation: keep separate — IsNef/IsBig are general algebraic geometry (usable beyond this paper) while arithmetic Bézout is project-specific.

---

### Proposed: `blueprint/src/chapters/ArithBezout.tex`
- **Covers**: `MR4276287UniformityInMordellLangForCurves/ArithBezout.lean` | **Phase**: Canonical-height: arithmetic Bézout and Siu positivity
- **Why now**: `lem:uniform_degree_bound` proof cites "Arithmetic Bézout theorem [Théorème~3]{HauteursAlt3}" as black box; `prop:aux_ht_ineq` proof uses intersection number estimates; neither has a declared lemma in the blueprint.
- **Key defs** (dependency order):
  1. `\theorem` `\label{thm:arith_bezout}` — Arithmetic Bézout: for cycles Z₁, Z₂ on P^n_ℤ of complementary codimension, their arithmetic intersection number satisfies ĥ(Z₁ · Z₂) ≤ deg(Z₁)·ĥ(Z₂) + deg(Z₂)·ĥ(Z₁) + c·deg(Z₁)·deg(Z₂). `\lean{MR4276287UniformityInMordellLangForCurves.ArithBezout.arithBezout}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` — cite "[Théorème~3]{HauteursAlt3}" (Autissier "Hauteurs des intersections et multiplicités"); retrieval needed.
  2. `\lemma` `\label{lem:bihomog_degree}` — The graph of the multiplication-by-N map [N]: A → A can be expressed by bihomogeneous polynomials of controlled degree (polynomial in N). `\lean{MR4276287UniformityInMordellLangForCurves.ArithBezout.bihomogDegree}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` §4.
  3. `\lemma` `\label{lem:siu_intersection_lower}` — Lower bound on (F^d) ≥ κ·N^{2d} from Betti-form positivity and scaling by N². `\lean{MR4276287UniformityInMordellLangForCurves.ArithBezout.siuIntersectionLower}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` §4.
  4. `\lemma` `\label{lem:siu_intersection_upper}` — Upper bound on (M · F^{d-1}) ≤ c·N^{2(d-1)} from bihomogeneous degree control. `\lean{MR4276287UniformityInMordellLangForCurves.ArithBezout.siuIntersectionUpper}` [expected]. Source: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` §4.
- **`\uses` skeleton**:
  - `lem:siu_intersection_lower` uses `prop:betti_form`, `lem:graph_construction`
  - `lem:siu_intersection_upper` uses `lem:bihomog_degree`, `lem:graph_construction`
  - `prop:aux_ht_ineq` (existing) should additionally `\uses{lem:siu_intersection_lower, lem:siu_intersection_upper, thm:siu_criterion, thm:arith_bezout}`
- **Main theorem proof strategy**: Arithmetic Bézout is cited from Autissier; use as an axiomatic stub. Bihomogeneous degree bound follows from expressing [2^l] by polynomials of degree 2^l in each homogeneous coordinate block. The intersection bounds then follow from multilinearity of intersection numbers and explicit degree tracking.
- **References for writer**: `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` §4 (full proof); `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` (Bézout reference); retrieval needed: Autissier "Hauteurs des intersections et multiplicités" [HauteursAlt3].

---

## Per-chapter

### `Overview.tex`
- **Complete**: false
- **Correct**: false
- **Notes**: No declaration blocks (intentional stub overview). Citation issues: `% SOURCE QUOTE: "the number of rational points is bounded"` is a paraphrase (not verbatim); `% SOURCE QUOTE PROOF:` is a meta-comment, not a source quote. Must-fix: if chapter is kept, either remove source quote markers or provide actual verbatim text from abstract. Low priority since Overview has no declaration blocks.

### `MR4276287UniformityInMordellLangForCurves_Basic.tex`
- **Complete**: partial
- **Correct**: partial
- **Notes**:
  - Undefined macros: `\hcA` (appears in `thm:silverman_tate` proof — needs `\newcommand{\hcA}{h_{\overline{\mathcal{A}}}}` in common.tex); `\intercal` (in `prop:betti_form` proof — requires amssymb package).
  - Wrong `\uses{}`: `prop:aux_ht_ineq` statement lists `thm:silverman_tate` in `\uses{}` but this is NOT a dependency of the auxiliary height inequality; ST enters only in `thm:ht_inequality`. Remove from `prop:aux_ht_ineq` statement's `\uses{}`.
  - Missing `\uses{}` in `prop:aux_ht_ineq` statement and proof: currently does not list the Siu criterion or IsNef/IsBig infrastructure (will be added once Positivity.tex and ArithBezout.tex chapters are written).
  - `def:ambient_setup`: `% SOURCE QUOTE PROOF:` line ("This section fixes...") is non-verbatim and occurs inside a definition block that has no proof. This line should be removed or replaced with correct format.
  - `lem:moduli_height_comparison`: `% SOURCE QUOTE PROOF:` is identical to `% SOURCE QUOTE:` — the proof needs a separate verbatim quote from the lemma's proof in the source (the Silverman height-machine argument). Source: `references/MR4276287-mordell-lang-curves-source/intro.tex` or `NTbase.tex`.
  - Proof sketch quality for `thm:nondeg_for_bd`: conditions (a), (b), (c) for Gao's Theorem 1.3 are listed but not explicitly labeled in a way a prover can follow. The condition "each fiber curve generates its Jacobian" needs `lem:curve_generates_jacobian` (from proposed Jacobian.tex) as a `\uses{}`.
  - `def:ambient_setup` and `def:nondegenerate_app` correctly have no `\begin{proof}` blocks (by design per directive). ✓
  - All 18 declarations have `\lean{}` hints ✓.
  - `% SOURCE:` parentheticals all name files that exist in `references/MR4276287-mordell-lang-curves-source/` ✓.

### `MR4276287UniformityInMordellLangForCurves.tex`
- **Complete**: partial
- **Correct**: partial
- **Notes**:
  - Undefined macros: `\IQbar` (appears extensively in source-quote comments and proof bodies — `\newcommand{\IQbar}{\overline{\mathbb{Q}}}` needed in common.tex); `\IR` (appears in `prop:premazur` proof — `\newcommand{\IR}{\mathbb{R}}`).
  - Missing declarations: `thm:bd_rat_intro` proof uses Rémond's estimate `\cite[page 643]{DPvarabII}` without a corresponding lemma or `\mathlibok` anchor. `thm:bd_tor_intro_nf` proof uses Raynaud's Manin-Mumford `\cite{Raynaud}` without a declaration. Northcott's theorem is also used in both without a `\mathlibok` anchor.
  - `prop:premazur` SOURCE QUOTE: "The exist constants..." — "The" should be "There" if verbatim; if this is the actual source text, it's OK, but it looks like a transcription error. Verify against `RatPt.tex`.
  - `% SOURCE QUOTE PROOF:` for all 4 declarations correctly placed before `\begin{proof}` and cites `(read from references/MR4276287-mordell-lang-curves-source/RatPt.tex)` ✓.
  - Proof of `thm:bd_rat_intro` invokes "Rémond's estimate" as a black box for the finitely-many-isomorphism-classes case; this step is load-bearing and needs a declared lemma stub.
  - Proof sketches for `thm:bd_fin_rank` and `thm:bd_tor_intro_nf` are adequately detailed for a prover modulo the missing declarations.
  - `\uses{}` edges: no broken `unknown_uses` per leandag ✓. `thm:bd_rat_intro` and `thm:bd_tor_intro_nf` both list `lem:moduli_height_comparison` ✓.

---

## Dependency graph summary

- `leandag build --json`: 22 blueprint nodes, 41 edges, 0 `unknown_uses`, 0 isolated nodes. ✓
- 22 `unmatched_lean` (all expected — Basic.lean has only `import Mathlib`). ✓
- 0 `leandag show gaps` (all 22 nodes have `\lean{}` hints). ✓
- 0 isolated nodes — DAG is fully connected. ✓

---

## Severity summary

- **must-fix-this-iter**:
  1. `common.tex` missing macros: add `\IQbar`, `\IR`, `\hcA` definitions; check amssymb for `\intercal`.
  2. `prop:aux_ht_ineq` statement: remove `thm:silverman_tate` from `\uses{}` (wrong edge).
  3. `thm:bd_rat_intro`: add `\mathlibok` or lemma stub for Rémond's estimate.
  4. `thm:bd_tor_intro_nf`: add `\mathlibok` or lemma stub for Raynaud's Manin-Mumford.
  5. Add `\mathlibok` anchor for Northcott's theorem (used in both counting proofs).
  6. All 6 unstarted-phase proposals: dispatch blueprint-writer for each.
- **soon**:
  1. `lem:moduli_height_comparison`: fix `% SOURCE QUOTE PROOF:` (currently duplicates statement quote).
  2. `def:ambient_setup`: remove non-verbatim `% SOURCE QUOTE PROOF:` comment.
  3. `Overview.tex`: fix or remove non-verbatim source quote markers.
  4. `prop:aux_ht_ineq` `\uses{}`: add Siu/Positivity declarations once those chapters are written.
  5. `thm:nondeg_for_bd` proof: add `lem:curve_generates_jacobian` to `\uses{}` once Jacobian.tex is written.
