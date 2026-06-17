# Blueprint Writer Directive

## Slug
torelli

## Target chapter
blueprint/src/chapters/Torelli.tex

## Strategy context
This chapter covers the Siegel moduli space A_{g,ℓ} of principally polarized abelian
varieties, the universal abelian family over it, and the Torelli map from M_g to A_g.
These are needed to make sense of the moduli-height comparison (lem:moduli_height_comparison)
and the height inequality setup. This chapter depends on ModuliSpace.tex (def:Mg_level)
and Jacobian.tex (def:jacobian_av).

This is a new chapter; create the file from scratch with:
  \chapter{Torelli map and universal Jacobian family}
  \label{chap:torelli}
  % archon:covers MR4276287UniformityInMordellLangForCurves/Torelli.lean

## Required content

1. **def:Ag_level** (`def:AgLevel`) — The Siegel moduli space A_{g,ℓ} of principally
   polarized abelian varieties of dimension g with level-ℓ structure. For ℓ ≥ 3 this
   is a fine moduli scheme (quasi-projective, smooth). Source: BettiMapForm.tex §2 intro.

2. **def:universal_av** (`def:universalAV`) — The universal principally polarized abelian
   variety π^univ: A_g → A_{g,ℓ}: a principally polarized abelian scheme over A_{g,ℓ}
   representing the functor of ppavs with level-ℓ structure. Source: BettiMapForm.tex.

3. **def:torelli_map** (`def:torelliMap`) — The Torelli morphism τ: M_{g,ℓ} → A_{g,ℓ}
   sending [C] ↦ [Jac(C), θ_C] where θ_C is the canonical principal polarization.
   Source: SettingUp.tex.

4. **thm:torelli_injective** (`thm:torelliInjective`) — Torelli's theorem: τ is
   injective on geometric points (two smooth curves with isomorphic Jacobians are
   isomorphic as curves). Source: standard (Torelli's theorem).

5. **lem:universal_jacobian_fib** (`lem:universalJacobianFiber`) — The fiber of the
   universal abelian variety A_g over τ(s) is canonically isomorphic to Jac(C_s).
   Source: SettingUp.tex / fine moduli property.

\uses skeleton:
- def:universal_av uses def:Ag_level
- def:torelli_map uses def:Mg_level (from ModuliSpace.tex), def:Ag_level, def:jacobian_av (from Jacobian.tex)
- thm:torelli_injective uses def:torelli_map
- lem:universal_jacobian_fib uses def:torelli_map, def:universal_av, def:jacobian_av
- def:ambient_setup (in Basic.tex) uses def:Ag_level, def:universal_av, def:torelli_map (to be wired)
- lem:moduli_height_comparison (in Basic.tex) uses def:torelli_map (to be wired)

## Out of scope
- Do NOT add height functions or Weil-height comparisons (those go in WeilHeight.tex).
- Do NOT edit any other chapter.
- Do NOT add \leanok markers.

## References
- references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex: Section 2, A_{g,ℓ}, universal abelian variety
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex: Section 6, Torelli map, universal family

## Expected outcome
New chapter with 5 well-formed declaration blocks, each with accurate \uses{} edges,
verbatim source quotes, and informal proof sketches. def:Ag_level and def:universal_av
are definitions (no proof). thm:torelli_injective is stated as a deep theorem with a
one-paragraph sketch (the actual proof is the classical Torelli theorem; the project
will axiomatize it as a sorry stub).
