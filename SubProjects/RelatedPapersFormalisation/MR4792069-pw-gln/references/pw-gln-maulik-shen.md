# The P=W conjecture for GL_n

## Citation
Davesh Maulik and Junliang Shen, "The P=W conjecture for GL_n", Annals of Mathematics 200 (2024), no. 2, 605––665. arXiv:2209.02568. MR4792069.

## Slug
pw-gln-maulik-shen

## Retrieval status
RETRIEVED — 2026-06-18

## Local source files
- `references/pw-gln-maulik-shen.pdf` — PDF (25 pp.), VERIFIED via `file` — retrieved from https://arxiv.org/pdf/2209.02568
- `references/pw-gln-maulik-shen.tex` — LaTeX source (single file, 170 KB), VERIFIED via `file` — retrieved from https://arxiv.org/e-print/2209.02568 (gunzipped from gzip archive)
- `references/pw-gln-maulik-shen.tar.gz` — original gzip archive kept as downloaded

## Why this source
This is the primary paper for the entire project. It will be used to: (1) write the blueprint chapter for the main P=W theorem (Theorem 0.2 / Conjecture 0.1); (2) identify which lemmas and definitions are formalizable in Lean 4 with current Mathlib; and (3) set up the formal statement of the main theorem. Every declaration block in the blueprint must cite verbatim from this source.

## Contents map

The PDF uses section numbering §0–§4 (table of contents extracted from the PDF text):

- **§0 Introduction** — p.1
  - §0.1 The P=W conjecture — p.1
    - **Conjecture 0.1** [The P=W conjecture for GL_n, de Cataldo–Hausel–Migliorini] — p.2
      `P_k H^m(M_Dol, Q) = W_{2k} H^m(M_B, Q) = W_{2k+1} H^m(M_B, Q)`
    - **Theorem 0.2** (main result): Conjecture 0.1 holds — p.2
    - **Theorem 0.3**: P=W for SL_p, prime p — p.3
  - §0.2 Idea of the proof (4 steps) — p.3
  - §0.3 Acknowledgements — p.4

- **§1 Perverse filtrations and vanishing cycles** — p.4
  - §1.1 Perverse filtrations — p.4
    - Definition: perverse filtration `P_i H^m(X,Q) := Im{H^{m-a+r}(Y, ^p τ_{≤i}(Rf_* Q_X[a-r])) → H^m(X,Q)}` — p.4
    - Definition: strong perversity c for γ ∈ H^l(X,Q) with respect to f — p.5
    - **Lemma 1.1**: Equi-dimensional fibers ⟹ perverse filtration terminates at P_m H^m — p.4
    - **Lemma 1.2**: γ of strong perversity c ⟹ cup product sends P_i H^m to P_{i+c} H^{m+l} — p.5
    - **Lemma 1.3**: Products of strong perversity c_j classes have strong perversity Σ c_j — p.5
  - §1.2 Vanishing cycles — p.6
    - Setup: vanishing cycle functor φ_g: D^b_c(X) → D^b_c(X_0), notation ϕ_g := ϕ_g(IC_X) — p.6
    - **Lemma 1.4**: φ_g(γ) coincides with i^*γ applied to ϕ_g (compatibility of vanishing cycles with cohomology restriction) — p.6
    - **Proposition 1.5**: Strong perversity preserved under vanishing cycle pullback (key tool for §2) — p.7

- **§2 Strong perversity for Chern classes** — p.7
  - §2.1 Tautological classes — p.7
    - Setup: PGL_n Dolbeault moduli space M̂_Dol, Γ = Pic^0(C)[n], tautological classes c_k(γ) — p.7–8
    - **Theorem 2.1** [Markman, Shende]: (i) tautological classes generate H^*(M̂_Dol, Q); (ii) c_k(γ) lies in ^k Hdg^*(M̂_B) — p.8
    - **Lemma** (curious Hard Lefschetz from Mellit): W_{2k} ⊂ P_k for all k ⟹ W_{2k} = P_k — p.8–9
    - **Conjecture 2.2** (equivalent version): ∏ c_{k_i}(γ_i) ∈ P_{Σk_i} H^*(M̂_Dol, Q) — p.9
  - §2.2 Strong perversity for Chern classes for L-twisted Hitchin systems — p.9
    - Setup: L-twisted Hitchin moduli M^L_Dol, h^L, SL_n/PGL_n twisted versions — p.9–10
    - **Theorem 2.5** [MS, Theorem 4.5]: Vanishing cycle of L(p)-twisted Hitchin = IC of L-twisted Hitchin — p.10
    - **Proposition 2.6**: PGL_n version of Theorem 2.5 (via Γ-quotient) — p.10–11
    - **Theorem 2.7** (key reduction): ch_k(U^L) has strong perversity k w.r.t. id × ĥ^L — p.11
  - §2.3 Theorem 2.7 implies Conjecture 2.2 — p.11
    - Claim: strong perversity descends from L(p)-twisted to L-twisted via Prop. 1.5 — p.11–12
    - Deduction: Theorem 2.7 ⟹ Conjecture 2.2 ⟹ Conjecture 0.1 — p.12–13

- **§3 Global Springer theory** — p.13
  - §3.1 Notations (L effective, deg(L) > 2g; G = PGL_n, B, T, W ≅ S_n) — p.13
  - §3.2 Parabolic moduli stacks — p.13
    - M̂^par: moduli of parabolic G-Higgs bundles, π: M̂^par → C × M̂ (global analog of Grothendieck simultaneous resolution) — p.13–14
    - Parabolic Hitchin system ĥ^par: M̂^par → C × Â — p.14
  - §3.3 Stable loci — p.14
    - M̂^par := (C × M̂) ×_{C×M̂^stack} M̂^par_stack — p.14–15
    - **Proposition 3.1**: M̂^par is nonsingular DM; ĥ^par is proper — p.15
    - **Theorem 3.2** (Support theorem for parabolic Hitchin map): Decomposition for ĥ^par has full support (proof deferred to §4) — p.16
  - §3.4 Proof of Theorem 2.7 — p.16
    - Three ingredients (A) splitting of π^*U into line bundles L(ξ); (B) strong perversity 1 for c_1(L(ξ)) [Yun, Lemma 3.2.3]; (C) Weyl group action on Rπ_*Q — p.16
    - **Claim**: ch_k(π^*U) has strong perversity k w.r.t. ĥ^par — p.17
    - **Lemma**: Strong perversity descends from M̂^par to C × M̂ via W-invariants — p.17

- **§4 Parabolic support theorem** — p.17
  - §4.1 Review of support theorems — p.17
    - Strategy: (I) support inequality for weak abelian fibration; (II) δ-regularity — p.17–18
  - §4.2 Parabolic Hitchin systems — p.18
    - Yun's result over elliptic locus: no strict supports for PGL_n (no nontrivial endoscopy) — p.18
    - Reduction: enough to show no support with generic point outside C × Â^ell — p.18
    - SL_n version M̌^par, Γ-quotient relation — p.18–19
  - §4.3 Weak abelian fibrations and δ-regularity — p.19
    - **Proposition 4.1**: (P, M̌^par, C × Â) is a weak abelian fibration (P = pullback of Prym variety) — p.19
    - Support inequality (\ref{delta_ineq}): codim(Z) ≤ δ_Z — p.19–20
    - Relative dimension bound (\ref{relative}): τ_{>2d}(Rȟ^par_* Q) = 0, d = dim M̌^par − dim(C × Â) — p.20
  - §4.4 Proof of the relative dimension bound — p.20
    - Formula: d = n(n−1)/2 · deg(L) + (n²−1)(g−1) — p.20
    - Strongly parabolic Higgs bundles M̌^spar(D), Hitchin map ȟ^spar: M̌^spar(D) → A(D) — p.21
    - dim M̌^spar(D)_0 = Σ_{j=2}^n ((j−1)deg(Ω_L) + g − 1) = d — p.21
    - Surjectivity of q: M̌^spar(D) → M̌^par restricted over C × A(D), base change gives dim bound — p.22

- **References** — p.23

## Caveats
- The published version (Annals of Mathematics 200 (2024), no. 2) may differ from arXiv:2209.02568v2 (May 17, 2024). The arXiv version is the one retrieved here (it is the same revision uploaded by the authors for the published version). The PDF downloaded from arXiv says "v2 [math.AG] 17 May 2024".
- Theorem numbering in the TeX source uses `\newtheorem{thm}{Theorem}[section]` (counters shared across thm/cor/lem/prop/conj/defn/rmk within each section). The PDF output uses sequential numbers within each section (1.1, 1.2, etc.).
- The TeX file is a single `.tex` file (not a multi-file project), so all content is directly readable.

## Quality / provenance
This is the definitive reference: the arXiv preprint by the authors (Maulik and Shen) that became the published Annals paper MR4792069. The PDF was retrieved directly from `arxiv.org/pdf/2209.02568` and the LaTeX source from `arxiv.org/e-print/2209.02568`; both were verified by the `file` command. This is the authoritative version for quoting.
