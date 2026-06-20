## Status: COMPLETE

The blueprint is a complete, dependency-correct, one-cone mathematical roadmap for the
project goal `lem:cech_computes_cohomology`
(`AlgebraicGeometry.cech_computes_higherDirectImage`). All six DAG gate criteria hold
(confirmed by `leandag build` + `archon dag-query`, and by a fresh-context
`blueprint-reviewer` whole-blueprint audit, iter-013):

1. **Zero ∞ blueprint sources** — `archon dag-query gaps` empty; every declaration has an
   informal proof, a `\mathlibok` anchor, or a "proved directly in Lean" note.
2. **Zero broken `\uses{}`** — `leandag build` reports no `unknown_uses`; blueprint-doctor 0
   broken refs.
3. **Every blueprint declaration has `\lean{}`** — `Needs \lean{}` = 0.
4. **Connected, one cone** — `Isolated (no edges)` = 0 blueprint nodes; every blueprint node
   lies in the goal's ancestor cone.
5. **1-to-1 coverage** — `Lean-aux nodes` = 0; `archon dag-query unmatched` empty (every Lean
   declaration, including all 28 internal prover helpers, has a blueprint entry).
6. **`content.tex` inputs every chapter** — all 3 chapters present.

Remaining work is pure *proving* (formalizing the P3/P3b/P5a/P5b declarations whose informal
proofs are written), which is the `archon loop` prover phase's domain, not a blueprint gap.

## Declared coverage

- `blueprint/src/chapters/Cohomology_HigherDirectImage.tex` — covers
  `AlgebraicJacobian/Cohomology/HigherDirectImage.lean`: `def:higher_direct_image`,
  `def:right_acyclic`, and the right-derived/Mathlib anchors.
- `blueprint/src/chapters/Cohomology_AcyclicResolution.tex` — covers
  `AlgebraicJacobian/Cohomology/AcyclicResolution.lean` (P4 Leray acyclic-resolution lemma):
  `lem:acyclic_resolution_computes_derived`, `lem:acyclic_one_iso_coker`,
  `lem:acyclic_dimension_shift`, `lem:right_derived_shift_split_resolution`,
  horseshoe layer (`lem:horseshoe_twist`, `lem:horseshoe_chainMap`, `lem:horseshoe_dComp`,
  `lem:horseshoe_resolvesMiddle`, …), cosyzygy layer (`lem:cosyzygy_ses`,
  `lem:applied_cosyzygy_cycles`, `lem:cohomology_of_applied_resolution`) — incl. all
  twistedBiprod / cosyzygy / split-resolution helper Lean decls bundled into those entries.
- `blueprint/src/chapters/Cohomology_CechHigherDirectImage.tex` — consolidated, covers
  `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean` (P1 push–pull + P2 Čech machinery
  + frozen P5b assembly `lem:cech_computes_cohomology`),
  `AlgebraicJacobian/Cohomology/CechAcyclic.lean` (P3 `lem:cech_acyclic_affine`), and
  `AlgebraicJacobian/Cohomology/PresheafCech.lean` (P3b bridge: `def:cech_free_presheaf_complex`,
  `def:section_cech_complex`, `lem:cech_complex_hom_identification`,
  `lem:cech_free_complex_quasi_iso`, `lem:injective_cech_acyclic`, `lem:ses_cech_h1`,
  `lem:cech_to_cohomology_on_basis`, `lem:affine_serre_vanishing`) + P5a vanishing inputs
  (`lem:higher_direct_image_presheaf`, `lem:open_immersion_pushforward_comp`,
  `lem:cech_term_pushforward_acyclic`, `lem:cech_augmented_resolution`) — incl. all push–pull
  and cover-nerve helper Lean decls bundled into their entries.
