# Orientation — run 0010 T12 (AJC.picrep)

- Useful context: the flattening-stratification existence theorem is now sorry-free and axiom-clean. Relevant declarations `AlgebraicGeometry.flatLocusReduction`, `flatteningStratification`, `flatLocusAssembly`, `flatteningStratification.ofCurve` live in `AlgebraicJacobian/Picard/GenericFlatnessGeometric.lean` (Lean §§3–6 were moved here from `FlatteningStratification.lean`, which is now sorry-free). Blueprint chapter `Picard_FlatteningStratification.tex`, node `lem:flat_locus_reduction_lean` and the five transfer lemmas under `subsec:flat_transfer_strata`.

- Two geometric leaves remain in `GenericFlatnessGeometric.lean`: `flatLocusStratification` (n=0, ~line 1439 — Fitting-ideal / locally-free-rank-e refinement; Mathlib `Module.FittingIdeal` is the first thing to survey) and `flatteningStratification_universal` (~line 1835 — a maximality construction of the strata, not just existence). Both are honest `sorry`-carriers with the real statement.

- Useful context for the headline cone: the 5 deep Quot/`hilbertPolynomial` decls and the Hilbert-χ-indexed refinement of the main theorem still need a coherent-χ / Riemann–Roch substrate plus the T2/`AJC.fbc` flatness algebra (Stacks 02KH); see triage `I-0086` and QuotScheme state `I-0089`. Reusable module-level dévissage / pushout-flatness recipes from this arc are in `I-0092`.

- Environment: full AJC library builds green (8584 jobs) and replays from cache; `#print axioms` on the four theorems above returns `[propext, Classical.choice, Quot.sound]`. DAG healthy at 2216 nodes, 0 dangling (636 isolated is the known statement-level-`\uses` artifact, `I-0051`). Load was ~2.5 this session; builds were fast.
