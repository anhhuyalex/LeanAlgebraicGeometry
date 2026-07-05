# Orientation — after run 0010 T12 (session 0080)

- Useful context: `AlgebraicGeometry.Scheme.hilbertPolynomial` is now real and axiom-clean in `MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/HilbertPolynomial.lean` (H⁰-only graded route, eventual-match + unconditional uniqueness, `IsRatHilb`-conditional existence bridge to `gradedModule_hilbertSeries_rational`). `QuotScheme.lean` sits at 7 real `sorry` (4 headline reps + 3 FBC-gated base-change leaves).

- Relevant blueprint: `blueprint/src/chapters/Picard_QuotScheme.tex` `sec:hilbert_polynomial` (`def:hilbert_polynomial` `\leanok`, 11-node cone). The remaining `AJC.picrep` inputs are `lem:sectionGradedModule_fg` (Serre finite generation of the section module, ample+proper — needs ampleness vocabulary absent from v4.31, multi-session) and `thm:hilbertPoly_of_sectionModule`; both are non-`\leanok` with `\lean{}` forward pointers to planned decls (`sectionGradedModule_fg`, `hilbertPolynomialOfSectionModule`).

- Recent triage lives in memory `I-0109` (current QuotScheme lane order: `sectionGradedModule_fg` → DirectSum-decomposition bridge → `QuotFunctor` def) and `I-0088`/`I-0092` (v4.31 ModuleCat / dévissage recipes). The 3 `canonicalBaseChangeMap` leaves stay gated on `AJC.fbc`/T2 flatness (`I-0083`, `I-0076`).

- Environment note: `HilbertPolynomial` cone builds green (`lake build`, 8560 jobs, exit 0); only pre-existing unused-variable linter warnings in `GradedHilbertSerre.lean`. `horizon commit` currently no-ops under the concurrent integrator sweep — T12 Lean/blueprint work reached the ledger via `workspace[0010 r2] integrate 0080-horizon-T12`, not a semantic commit.
