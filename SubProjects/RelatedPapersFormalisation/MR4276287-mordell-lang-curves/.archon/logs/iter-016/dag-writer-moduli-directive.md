# Blueprint Writer Directive

## Slug
moduli-space

## Target chapter
blueprint/src/chapters/ModuliSpace.tex

## Strategy context
This chapter covers the Setup phase for the fine moduli space M_g of smooth genus-g curves
with level structure. It provides the formal setting for def:ambient_setup. The chapter is
needed because M_g with level structure and the universal curve are confirmed MISSING from
Mathlib and must be set up as project-specific definitions.

This is a new chapter; create the file from scratch with:
  \chapter{Moduli space of curves}
  \label{chap:moduli}
  % archon:covers MR4276287UniformityInMordellLangForCurves/ModuliSpace.lean

## Required content

Produce a complete new chapter with the following declarations (in dependency order):

1. **def:level_structure** (`def:LevelStructure`) — A level-ℓ structure on a smooth genus-g
   curve C is an isomorphism C[ℓ] → (ℤ/ℓℤ)^{2g} of group schemes compatible with the
   Weil pairing. Source: SettingUp.tex §1.

2. **def:Mg_level** (`def:MgLevel`) — The fine moduli space M_{g,ℓ} of smooth genus-g
   curves with level-ℓ structure as a quasi-projective scheme over Spec ℤ[1/ℓ]. For
   ℓ ≥ 3, it is actually a fine moduli scheme (functor is representable). Source: SettingUp.tex.

3. **def:universal_curve** (`def:universalCurve`) — The universal curve C_g → M_{g,ℓ}:
   a smooth proper morphism of relative dimension 1 with genus-g fibers. Source: SettingUp.tex.

4. **prop:Mg_quasiprojective** (`prop:MgQuasiProjective`) — For ℓ ≥ 3, M_{g,ℓ} is a smooth
   quasi-projective variety that admits a compactification M̄_{g,ℓ}. Source: SettingUp.tex.

5. **lem:torelli_quasi_finite** (`lem:torelliQuasiFinite`) — The Torelli map
   τ: M_{g,ℓ} → A_{g,ℓ} (sending [C] to [Jac(C)]) is quasi-finite. Source: SettingUp.tex / OortSteenbrink Lemma 1.11.

\uses skeleton:
- def:universal_curve uses def:Mg_level
- prop:Mg_quasiprojective uses def:Mg_level
- lem:torelli_quasi_finite uses def:Mg_level, def:universal_curve
- def:ambient_setup (in Basic chapter) uses def:Mg_level, def:universal_curve

## Out of scope
- Do NOT add declarations for A_g or the universal abelian variety (those go in Torelli.tex).
- Do NOT add the Jacobian variety construction (that goes in Jacobian.tex).
- Do NOT edit content.tex.
- Do NOT add \leanok markers.

## References
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex: Section 6 setup, M_g, level structure, universal curve

## Expected outcome
A new chapter file blueprint/src/chapters/ModuliSpace.tex with 5 well-formed declaration
blocks (each with \label, \lean, \uses, % SOURCE:, % SOURCE QUOTE:, informal statement,
% SOURCE QUOTE PROOF:, and \begin{proof}...\end{proof} where applicable). Definitions have
no proof block; propositions and lemmas have proof blocks. All citations verbatim from
the locally-read SettingUp.tex.
