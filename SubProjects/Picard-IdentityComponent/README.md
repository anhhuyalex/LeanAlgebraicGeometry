# Picard-IdentityComponent

Isolated extraction subproject for **`Picard/IdentityComponent.lean`** (task **T5**,
roadmap `AJC.picrep`): the Pic⁰ identity-component spine of the Picard-representability
cone, extracted from `MainProjects/Algebraic-Jacobian-Challenge` so it can be iterated
**in parallel** with the live flat-base-change work (T2) without touching the AJC
`.lake` build directory.

## Contents

Exactly the FBC-free transitive import cone of `IdentityComponent.lean` (9 modules,
verified free of `Cohomology/Cech*` and the 02KH flat-base-change engine):

- `AlgebraicJacobian/Picard/IdentityComponent.lean` — G⁰ substrate + Pic⁰ (A.3 chapter)
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean` — sorry-backed FGA foundation
  (`PicScheme`, typeclass-isolated `⟨sorry⟩` sites)
- `AlgebraicJacobian/Genus.lean` — genus via `H¹(C, O_C)`
- `AlgebraicJacobian/Cohomology/{SheafCompose,StructureSheafAb,StructureSheafModuleK{,/*}}.lean`
  — H¹ substrate

Blueprint chapters for the same cone live under `blueprint/src/chapters/` (dangling
cross-chapter `\cref`s demoted to `\texttt` per the Albanese extraction precedent).
The 3 isolated DAG nodes (`def:Scheme_IsCechAcyclicCover` + 2 theorems) are pruning
artifacts — their only consumers live in the pruned `Cohomology_MayerVietoris`
chapter; they are kept so the files stay byte-identical to AJC for merge-back.

## Status / known sorries

The sorries here are **blocked, not proof-search debt** (see workspace memory,
run 0005 Ground verification):

- §1 group-scheme substrate sorries — blocked on Stacks **037Q/04KU** (connected +
  rational point ⟹ geometrically connected) and **02LB/04KS** clopen descent,
  absent from Mathlib v4.31.
- Pic⁰-specific leaves — inherit the sorry-backed FGA representability foundation
  (`instHasPicScheme`, `instPicSchemeGroupObject`, …) and the χ-blocked degree map;
  `isAbelianVariety`/`finrank_eq_genus` await the separate `AJC.pic0av` cone.

## Build

`lake build` (mathlib v4.31.0, shared `packagesDir ../../.lake-packages`; own `.lake`,
never rebuilds the AJC tree). Merge-back target: `MainProjects/Algebraic-Jacobian-Challenge`.
