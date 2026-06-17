# Blueprint Writer Directive

## Slug
jacobian

## Target chapter
blueprint/src/chapters/Jacobian.tex

## Strategy context
This chapter covers the Jacobian variety of a smooth genus-g curve as a principally
polarized abelian variety. This construction is CONFIRMED MISSING from Mathlib (Mathlib's
WeierstrassCurve.Jacobian = Jacobian coordinates for genus-1 elliptic curves only, not
the Jacobian abelian variety of a higher-genus curve). This is the largest single risk
in the project — every downstream result depends on Jac(C) as an abelian variety.

The recommended approach is to define the Jacobian via axiom stubs (noncomputable
definitions with sorry bodies or as parameters), stating the key properties as lemmas,
since a full Picard-group construction is out of scope for the blueprint.

This is a new chapter; create the file from scratch with:
  \chapter{Jacobian variety of a curve}
  \label{chap:jacobian}
  % archon:covers MR4276287UniformityInMordellLangForCurves/Jacobian.lean

## Required content

1. **def:jacobian_av** (`def:jacobianAV`) — The Jacobian Jac(C) of a smooth genus-g curve
   C as a g-dimensional abelian variety. State the universal property: for any abelian
   variety A and morphism f: C → A with f(P_0) = 0_A, there exists a unique group
   homomorphism Jac(C) → A making the diagram commute. Source: SettingUp.tex §2 /
   standard reference.

2. **lem:jacobian_ppav** (`lem:jacobianPpav`) — Jac(C) carries a canonical principal
   polarization θ: Jac(C) → Jac(C)^∨ (the theta polarization). Source: standard.

3. **def:abel_jacobi** (`def:abelJacobi`) — The Abel-Jacobi embedding ι_{P0}: C → Jac(C)
   sending P ↦ class of (P - P_0) in Pic^0(C). This is a closed immersion for g ≥ 2.
   Source: SettingUp.tex, RatPt.tex §1.

4. **thm:abel_jacobi_closed** (`thm:abelJacobi_closedImmersion`) — For g ≥ 2, the
   Abel-Jacobi map ι_{P0}: C → Jac(C) is a closed immersion. Source: standard.

5. **def:faltings_zhang** (`def:faltingsZhang`) — The Faltings-Zhang morphism
   D_M: C^{M+1} → Jac(C)^M defined by D_M(Q_0,...,Q_M) = (Q_i - Q_0)_{i=1}^M.
   Source: SettingUp.tex §6.

6. **lem:curve_generates_jacobian** (`lem:curveGeneratesJacobian`) — For g ≥ 2, the
   image of C under Abel-Jacobi generates Jac(C) as an abelian group. Source: standard
   (used in Gao's Theorem 1.3 non-degeneracy conditions).

\uses skeleton:
- lem:jacobian_ppav uses def:jacobian_av
- def:abel_jacobi uses def:jacobian_av
- thm:abel_jacobi_closed uses def:abel_jacobi
- def:faltings_zhang uses def:jacobian_av, def:abel_jacobi
- lem:curve_generates_jacobian uses def:abel_jacobi, def:jacobian_av
- def:ambient_setup (in Basic chapter) uses def:jacobian_av (to be wired up when Basic chapter is revised)
- thm:nondeg_for_bd (in Basic chapter) uses lem:curve_generates_jacobian (to be wired up)

## Out of scope
- Full Picard-group / theta-divisor construction (axiomatize the existence).
- Do NOT edit any other chapter.
- Do NOT add \leanok markers.

## References
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex: Section 6, Faltings-Zhang morphism, Abel-Jacobi embedding
- references/MR4276287-mordell-lang-curves-source/RatPt.tex: Section 1, Abel-Jacobi setup

## Expected outcome
New chapter with 6 well-formed declaration blocks. Definitions (def:jacobian_av,
def:abel_jacobi, def:faltings_zhang) state the mathematical objects clearly for a prover
to axiomatize. Lemmas and theorems have informal proof sketches (or explicit notes that
the proof is via a standard construction that the project will axiomatize). All citations
from locally-read source files.
