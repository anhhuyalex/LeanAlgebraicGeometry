# Orientation

- Useful context: T14 closed the Serre-twist cocycle. `overlapUnit_cocycle_transport` in `AlgebraicJacobian/Picard/SerreTwist.lean` is proved, so `serreTwist` = O(m) and `twistTransition_cocycle` are axiom-clean (Ground kernel-verified `[propext, Classical.choice, Quot.sound]`; `lake build` green, 8572 jobs). Blueprint `lem:serre_twist_cocycle` / `def:serre_twist` (`Picard_QuotScheme.tex:5178,5211`) carry `\leanok` with a complete proof of the triple-overlap fraction identity — Lean/blueprint 1-to-1.

- Relevant files: the new universe-poly substrate in `SerreTwist.lean` (`commonHom`, `fact_ij/ik/jk`, `section_restrict`, `awayMap_awayFraction_cocycle`, `topIso_inv_homOfLE_appTop`) is reusable for any Proj-cover module-descent computation, e.g. computing `Γ(ℙⁿ, O(1))` to validate the O(1) sign convention. The remaining T14 leaf is `sectionGradedModule_fg` (`SerreFiniteness.lean:75`), Serre finite-generation of the section graded module — the deep coherent-cohomology-on-ℙⁿ input tracked in `I-0109` / `I-0118`.

- Useful context: the projectivity predicate `Scheme.Hom.IsProjectiveWith` (`Picard/ProjectiveMorphism.lean`) is now de-tainted (O(1) was the former `sorryAx` source), so the honest restatement of `QuotScheme` under `IsProjectiveWith` + relatively-very-ample `L` (`I-0118`) can be written against axiom-clean substrate; Castelnuovo–Mumford boundedness stays a blueprint-only target.

- Environment note: the per-project VCS (`.archon-horizon/vcs/Algebraic-Jacobian-Challenge.git`) is stale at HEAD `6e7f7ae` (run 0005) with ~10 runs uncommitted; the live ledger is the workspace repo — inspect T14 and later history via `git --git-dir=.archon-horizon/vcs/workspace.git --work-tree=. log` (T14 commit `75f69ee26`, integrated as `14e4bc594`).
