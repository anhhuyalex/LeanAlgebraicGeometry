# Blueprint Writer Directive

## Slug
main-proofs

## Target chapter
blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves.tex

## Strategy context
This chapter contains the four main theorems of the project: the pre-Mazur bound
(prop:premazur), the finite-rank Mordell-Lang theorem (thm:bd_fin_rank), the
uniform rational-point bound (thm:bd_rat_intro), and the uniform torsion-packet
bound (thm:bd_tor_intro_nf). These are the culminating results derived from the
geometric and height infrastructure in the companion Basic chapter.

All four declaration STATEMENTS are already present with correct \lean{}, \uses{},
and % SOURCE: citations. What is MISSING is the PROOF BLOCKS. Your entire job is to
add \begin{proof}...\end{proof} environments to all four declarations.

## Required content

Add \begin{proof}...\end{proof} blocks for:

1. **prop:premazur** — Pre-Mazur bound: there exist c_1 >= 0 and c_2 >= 1 such that
   #(C_s(Qbar) - P_0) ∩ Gamma <= c_2^{1+rho}.
   Proof sketch:
   (a) Fix the moduli point s in M_g(Qbar) and the corresponding curve C_s.
   (b) Translate so the base point P_0 maps to 0 in the Jacobian J = Jac(C_s).
   (c) Apply prop:alg_pt_far: either a point Q in C_s(Qbar) ∩ Gamma is in the
       exceptional set Xi_s (whose size is bounded by lem:packets_alternative3 and
       lem:NAlon), or hat_h(Q) > h_{M_g}(s)/c_3.
   (d) The "large canonical height" part: lem:vojtamumford bounds the large-height
       points in C_s(Qbar) ∩ Gamma by c^rho, with the exponential dependence on the
       rank rho of Gamma.
   (e) The "exceptional set" part: these are bounded uniformly by 84(g-1) from
       lem:packets_alternative3.
   Combining (d) and (e) gives # C_s(Qbar) ∩ Gamma <= c_2^{1+rho} after absorbing
   the exceptional count into the constant c_2.
   Key \uses{}: thm:ht_inequality_full, thm:nondeg_for_bd, lem:vojtamumford,
   prop:alg_pt_far.

2. **thm:bd_fin_rank** — Finite-rank Mordell-Lang bound.
   Proof sketch:
   (a) Given the height threshold iota and rank rho, apply prop:premazur to the
       specific curve C_s at moduli point s.
   (b) Use lem:moduli_height_comparison: when the canonical height on the Jacobian
       is at least iota, the moduli height h_{M_g}(s) is bounded below by a linear
       function of iota (up to constants from the Torelli map comparison).
   (c) This forces h_{M_g}(s) to be large enough that prop:premazur's estimate
       is non-trivial, giving # C_s(F) ∩ Gamma <= c_2(g,iota)^{1+rho}.
   (d) The constants c_1(g,iota) and c_2(g,iota) absorb the dependence on the
       moduli height threshold.
   Key \uses{}: prop:premazur, lem:moduli_height_comparison.

3. **thm:bd_rat_intro** — Uniform rational-point bound.
   Proof sketch:
   (a) Start with C a smooth curve of genus g over F with [F:Q] <= d.
   (b) The Jacobian J = Jac(C) is defined over F, and C(F) embeds in J(F) after
       choosing P_0 in C(F).
   (c) The group Gamma = J(F) has rank rho <= d*rk(J/Q) by a standard result.
   (d) From lem:moduli_height_comparison: because [F:Q] <= d, the moduli point
       s = [C] in M_g satisfies h_{M_g}(s) <= d * h_Weil([C]) up to constants,
       and the Neron-Tate height on J(Qbar) is comparable to the moduli height.
   (e) Apply thm:bd_fin_rank with the iota determined by the degree-d constraint
       and the moduli-height comparison to obtain # C(F) <= c(g,d)^{1+rho}.
   Key \uses{}: thm:bd_fin_rank, lem:moduli_height_comparison.

4. **thm:bd_tor_intro_nf** — Uniform torsion-packet bound.
   Proof sketch:
   (a) The torsion subgroup J(Qbar)_{tors} is rank-zero (rho = 0).
   (b) Apply thm:bd_fin_rank with rho = 0 and the same moduli-height comparison:
       # (C(Qbar) - P_0) ∩ J(Qbar)_{tors} <= c_2(g,iota)^{1+0} = c_2(g,iota).
   (c) Use lem:moduli_height_comparison to bound iota in terms of the degree [F:Q] <= d,
       so c_2 depends only on g and d.
   (d) The base point P_0 drops out because torsion is invariant under translation by
       torsion points: (C - P_0) ∩ J_{tors} is independent of the P_0 choice up to
       a torsion translate.
   Key \uses{}: thm:bd_fin_rank, lem:moduli_height_comparison.

## Out of scope
- Do NOT add new declaration blocks.
- Do NOT change existing \lean{}, \label{}, or \uses{} in statement blocks.
- Do NOT add \leanok markers.
- Do NOT edit content.tex or any other file.

## References
- references/MR4276287-mordell-lang-curves-source/RatPt.tex: Section 8 — pre-Mazur bound (prop:premazur)
- references/MR4276287-mordell-lang-curves-source/intro.tex: Introduction — main theorems thm:bd_rat_intro, thm:bd_fin_rank, thm:bd_tor_intro_nf
- references/MR4276287-mordell-lang-curves-source/DistanceCurve.tex: Section 7 — distance proposition used in premazur (prop:alg_pt_far)

## Expected outcome
All four declarations in the chapter have \begin{proof}...\end{proof} blocks with
multi-sentence informal proof sketches grounded in source verbatim quotes, and
accurate \uses{} cross-refs within the proof environments. Zero infinity-effort
nodes remain in this chapter.
