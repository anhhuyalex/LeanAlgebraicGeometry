# Orientation — after run 0014 T14 (projectivity foundation)

- Useful context: the projective vocabulary is in `MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/{ProjectiveSpace,SerreTwist,ProjectiveMorphism,SerreFiniteness}.lean`. `Scheme.Hom.IsProjectiveWith π L` (closed immersion into `ℙ(Fin(d+1);S)` with `L ≅ i^*O(1)`) has `isProper`/`comp_isClosedImmersion`/`baseChange` proved; `sectionGradedModule_fg` and `twistTransition_cocycle` are the two named `sorry` leaves. Blueprint: `sec:projective_vocabulary` in `blueprint/src/chapters/Picard_QuotScheme.tex` (line 5044).

- The single leaf `twistTransition_cocycle` (`SerreTwist.lean:322`, C2 triple-overlap transport) is what taints everything mentioning `serreTwist` with `sorryAx`; it is the rank-1 analogue of the Grassmannian `bundleTransition_cocycle_transport`. Closing it makes the whole projective-space O(m) cone axiom-clean.

- The `QuotScheme` final theorem (`QuotFunctorDef.lean`, sorry at ~1073) is still pinned with `[IsProper π] [LocallyOfFiniteType π]` only — false-as-pinned per `I-0118`. The substrate to restate it honestly (consuming `IsProjectiveWith`, specialised to `Scheme.{0}` since the glue engine is universe-monomorphic) now exists; `I-0109` carries the Hilbert-lane ordering and `I-0126`/`I-0118` the constraints.

- `lem:quot_boundedness` (`Picard_QuotScheme.tex:5547`) is a stated blueprint target with `\lean{...TODO.quotBoundedness}` but no `\leanok` and no Lean symbol yet: a faithful Castelnuovo–Mumford statement first needs `Rⁱπ_*`-of-twists vocabulary against the Čech engine. Full build was green (8606 jobs); DAG shows 0 dangling for AJC.
