# Blueprint Writer Directive

## Slug
basic-proofs

## Target chapter
blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex

## Strategy context
This project formalizes the paper "Uniformity in Mordell-Lang for curves" (arXiv:2001.10276).
The blueprint follows Route 1 (appendix-first height route): build the general height inequality
and Betti-map package first, then specialize to the curve family. This chapter covers all the
geometric and height-theoretic infrastructure: the Betti map and Betti form, the non-degeneracy
criterion, the height inequality (including the full appendix version), and the combinatorial
counting lemmas (Vojta-Mumford, N-Alon, packets alternative).

All declaration STATEMENTS are already present with correct \lean{}, \uses{}, and % SOURCE:
citations. What is MISSING from the chapter is the PROOF BLOCKS: every non-definition
declaration currently lacks a \begin{proof}...\end{proof} environment. Your entire job this
iteration is to add those proof blocks.

## Required content

Add \begin{proof}...\end{proof} blocks (with appropriate \uses{} cross-refs inside the proof
environments where the proof uses other results) for EACH of the following declarations:

1. **lem:moduli_height_comparison** — The Weil height on the moduli space and the
   Neron-Tate height on the abelian family are comparable up to affine-linear error along
   the Torelli map. The key step: fix a projective embedding of the moduli space,
   use functoriality of height under the Torelli map to compare with the height on A_g,
   and invoke the standard boundedness of the difference between projective and Neron-Tate
   heights on an abelian variety (cf. Silverman-Tate). The error is bounded by a constant
   times max{1, h(base point)}.

2. **prop:betti_map** — Local existence of the Betti map. Proof: on the analytification of
   the universal abelian family, choose a local section of the period map giving a
   trivialization of the lattice bundle over a small disk Delta. The quotient map
   (fiber) -> T^{2g} is then a group isomorphism on each fiber, real-analytic as a family
   (product with projection is a real-analytic diffeomorphism). This is the standard
   construction from the theory of variation of Hodge structure.

3. **prop:betti_form** — Existence of the Betti form. Proof: the Betti form omega is
   defined as the pushforward of the standard symplectic form on the local trivialization
   T^{2g} via the (local) Betti map inverse. It is closed of type (1,1) because the
   torus T^{2g} is Kaehler. It scales by N^2 under multiplication-by-N because [N] acts
   on T^{2g} by multiplication by N, and the symplectic form scales quadratically. The
   top wedge omega^d = 0 at smooth points where the Betti map fails to be of full rank;
   where it has full rank, it equals the volume form, giving detectability.

4. **prop:betti_map_app** — The general (appendix) Betti map, without level-structure
   restrictions. Proof: starting from any regular base S and abelian scheme pi: A -> S,
   pass to a finite etale cover S' -> S that carries a level-N structure with N >= 3
   (to ensure the moduli stack is a fine moduli space), then apply the level-structure
   Betti-map construction from prop:betti_map. The map descends back to A_Delta via
   the etale descent because the Betti-map fiber homomorphisms are canonical.

5. **lem:betti_rank_zar_open_app** — Betti rank is unchanged on Zariski open dense
   subsets. Proof: the Betti map is real-analytic, so the set where its restriction
   to X achieves maximum real rank is an open dense subset of X^{an} in the analytic
   topology. Any Zariski open dense subset U of X has U^{an} dense in X^{an}, hence
   it meets this maximum-rank open. The maximum rank on U therefore equals the maximum
   rank on X.

6. **thm:silverman_tate** — The canonical height and the naive projective height on an
   abelian variety differ by an error bounded linearly in the base-point height. Proof:
   by the standard Tate limit argument (limit of h(2^n P)/4^n), the canonical height
   hat_h satisfies hat_h(P) = lim h([2^n]P)/4^n. The naive height h is a Weil height
   for the same polarization, so their difference on fibers is bounded by a constant
   independent of P; across fibers the error term is controlled by the base-point height
   via the projection formula.

7. **lem:graph_construction** — Construction of the graph variety X_N. Proof: for each
   integer N, define X_N as the fiber product of A with itself over S via (id, [N]):
   this is the graph of multiplication-by-N inside A x_S A. Take its Zariski closure
   in the compactification A-bar x_{S-bar} A-bar to get X_N-bar. The associated line
   bundles F and M on the compactification are the pullbacks of the polarization line
   bundles along the two projections; the relevant height functions are induced by these
   line bundles.

8. **prop:aux_ht_ineq** — The auxiliary height inequality. Proof: with X non-degenerate
   and the Betti form omega^d > 0 at a smooth point, Siu's bigness criterion (a
   differential-geometric version applied to line bundles on X_N-bar) gives that
   the line bundle F - c*M is big for some positive constant c. This forces the
   projective height h_F([N]P) >= c*h_M(pi(P)) - O(1). After applying the graph
   construction (lem:graph_construction) and inserting the explicit N^2 dependence from
   the Betti form's scaling, one obtains h([N]P) >= c_1*N^2*h(pi(P)) - c_2(N).

9. **thm:ht_inequality** — Height inequality under the paper's hypotheses. Proof: apply
   prop:aux_ht_ineq to get the inequality for the projective height h, then use
   thm:silverman_tate to pass from h to the canonical height hat_h_A on the fiber.
   The Silverman-Tate comparison absorbs the difference into an additive error bounded
   by a constant times max{1, h(pi(P))}. After choosing N large enough (e.g. N = 2
   suffices for the paper's setup) one obtains hat_h_A(P) >= c_1*h(pi(P)) - c_2 on a
   dense open subset of X.

10. **thm:ht_inequality_full** — Full height inequality for arbitrary non-degenerate
    subvarieties (Appendix B). Proof is a six-step devissage:
    (a) Close up X in the compactification.
    (b) Replace the base S by the image of X under the projection, so S is now an
        irreducible subvariety of A_g.
    (c) Use prop:betti_map_app (general Betti map) to work on an arbitrary regular S.
    (d) Pass to a finite etale cover S' carrying a principal polarization and level-N
        structure; use lem:betti_rank_zar_open_app to verify that the rank condition on
        X pulls back.
    (e) Invoke thm:ht_inequality (the already-proved height inequality under the paper's
        hypotheses) on the pulled-back data.
    (f) Descend back to X and U using etale descent and the rank-invariance result.
    The output is: hat_h_{A,L}(P) >= c_1*h_{S-bar,M}(pi(P)) - c_2 on a dense open
    subset U of X.

11. **lem:uniform_degree_bound** — Uniform bound on the degree and height of fiber
    translates. Proof: the family of curves C_s varies in a bounded-degree projective
    family (all fibers embed via the same projective embedding from def:ambient_setup),
    so the degree of any fiber is bounded by the degree of the embedding times a constant.
    The height of the translate C_s - P_s is bounded by the height of P_s plus the height
    of C_s in the Chow variety; the latter is bounded by the moduli-space height h_{M_g}(s)
    via the pullback formula for heights along the Chow morphism.

12. **thm:nondeg_for_bd** — Non-degeneracy of the Faltings-Zhang image. Proof: Gao's
    theorem (the main input) states that the image of the fiber power C_s^{M+1} under
    the Faltings-Zhang morphism D_M is non-degenerate in A when g >= 2 and M >= 3g-2.
    The argument is that D_M(C_s^{M+1}) has Betti rank equal to 2*dim = 2(M+1) at a
    generic point (proven by Gao via the monodromy of the universal Jacobian). Since
    the Faltings-Zhang image lies in the universal abelian variety, this yields
    non-degeneracy in the sense of def:nondegenerate_app.

13. **lem:vojtamumford** — Quantitative Vojta-Mumford bound. Proof: the standard
    Vojta-Mumford method counts rational points in Gamma on a curve C inside an abelian
    variety A by intersecting C with a translate of a finitely-generated subgroup. Points
    of large canonical height in C(kbar) ∩ Gamma are controlled by applying the
    Roth-type theorem (in the form of Vojta's inequality or the Faltings-Noether
    method): at most c^rho of them lie above the threshold c*max{1,h(C),c_NT,h_1},
    where rho is the rank of Gamma. The constants depend only on n = dim(A) and deg(C).

14. **lem:NAlon** — The N-Alon product-avoidance lemma. Proof: if Sigma is a subset of
    C(k) with |Sigma| >= B, the M-fold product Sigma^M is a subset of C^M of cardinality
    at least B^M. A proper Zariski closed Z in C^M has bounded intersection with C^M(k)
    by Bezout (Z has lower dimension). Choosing B large enough relative to M, deg(C), and
    deg(Z) ensures that B^M exceeds any Bezout bound, so Sigma^M is not contained in
    Z(k). The constant B depends only on these degrees.

15. **lem:packets_alternative3** — At most 84(g-1) points satisfy the packet condition
    to a proper closed subset. Proof: if Z is a proper Zariski closed subset of
    D_M(C^{M+1}) and (C - P)^M subset Z for some P in C(kbar), then P is a special
    point with respect to the correspondence D_M. By Hurwitz's theorem applied to the
    covering C -> P^1 of degree deg(C) = 2g-2+2 (Riemann-Hurwitz), there are at most
    2(2g-2)(2g-2+2-1) = O(g^2) such special points; a more careful count using the
    multiplicity bound gives 84(g-1) as in the source paper.

16. **prop:alg_pt_far** — Sparseness of algebraic points. Proof:
    For a generic curve C_s of genus g with large moduli height:
    (a) From thm:ht_inequality_full and thm:nondeg_for_bd, the height inequality
        hat_h_A(D_M(Q1,...,Q_{M+1})) >= c_1 * h_{M_g}(s) - c_2 holds for points in a
        dense open subset of D_M(C_s^{M+1}).
    (b) From lem:uniform_degree_bound, the height of C_s - P is bounded by the moduli
        height, placing the effective curve inside a bounded-height region for h small.
    (c) If there are many Q in C_s(kbar) with hat_h(Q - P) <= h_{M_g}(s)/c_3, then
        by lem:NAlon their M-fold difference (C_s - P)^M cannot be contained in a proper
        closed set Z of D_M. But lem:packets_alternative3 gives at most 84(g-1) points
        where that packet condition holds. So all but finitely many Q satisfy the large-
        height alternative.

## Out of scope

- Do NOT add any new declaration blocks (definitions, lemmas, theorems).
- Do NOT change any existing \lean{}, \label{}, or \uses{} in statement blocks.
- Do NOT touch the def:ambient_setup or def:nondegenerate_app blocks (they are
  definitions and need no proof).
- Do NOT add \leanok markers.
- Do NOT edit content.tex or any other file.

## References
- references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex: Betti map and Betti form (prop:betti_map, prop:betti_form)
- references/MR4276287-mordell-lang-curves-source/HtIneqFinalVer.tex: Appendix B — general Betti map, non-degeneracy def, full height inequality (prop:betti_map_app, lem:betti_rank_zar_open_app, thm:ht_inequality_full)
- references/MR4276287-mordell-lang-curves-source/silvermantate.tex: Appendix A — Silverman-Tate comparison (thm:silverman_tate)
- references/MR4276287-mordell-lang-curves-source/HtIneq.tex: Section 4 — graph construction, auxiliary height inequality (lem:graph_construction, prop:aux_ht_ineq)
- references/MR4276287-mordell-lang-curves-source/NTbase.tex: Section 5 — height inequality (thm:ht_inequality)
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex: Section 6 — ambient setup, degree bound, non-degeneracy, N-Alon, packets (lem:uniform_degree_bound, thm:nondeg_for_bd, lem:NAlon, lem:packets_alternative3)
- references/MR4276287-mordell-lang-curves-source/DistanceCurve.tex: Section 7 — sparse points proposition (prop:alg_pt_far)
- references/MR4276287-mordell-lang-curves-source/RatPt.tex: Section 8 — Vojta-Mumford estimate (lem:vojtamumford)
- references/MR4276287-mordell-lang-curves-source/intro.tex: Introduction — moduli height comparison (lem:moduli_height_comparison)

## Expected outcome
After this round, every lemma, proposition, and theorem in the chapter has a
\begin{proof}...\end{proof} block with a multi-sentence informal proof sketch,
source-quote comments (% SOURCE QUOTE PROOF:) citing verbatim text from the listed
reference files, and accurate \uses{} cross-refs within the proof environment.
The chapter will have zero infinity-effort nodes.
