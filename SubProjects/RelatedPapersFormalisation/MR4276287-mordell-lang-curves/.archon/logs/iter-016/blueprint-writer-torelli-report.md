# Blueprint Writer Report: torelli
**Status:** COMPLETE

## Changes
- Created `blueprint/src/chapters/Torelli.tex` from scratch with 5 declaration blocks.
- `def:Ag_level` (`Torelli.agLevel`): Siegel moduli space $\mathbb{A}_g$ as fine moduli of ppavs with level-$\ell$ structure; no proof needed. Source: SettingUp.tex §6 (verbatim quote included).
- `def:universal_av` (`Torelli.universalAV`): universal ppav $\pi^{\mathrm{univ}}: \mathfrak{A}_g \to \mathbb{A}_g$; uses `def:Ag_level`. Source: BettiMapForm.tex §2 intro (verbatim quote included).
- `def:torelli_map` (`Torelli.torelliMap`): Torelli morphism $\tau: \mathbb{M}_g \to \mathbb{A}_g$ via Cartesian diagram; uses `def:Mg_level`, `def:Ag_level`, `def:jacobian_av`. Source: SettingUp.tex §6 (verbatim quote included).
- `thm:torelli_injective` (`Torelli.torelliInjective`): classical Torelli injectivity on geometric points; uses `def:torelli_map`; proof is sorry stub per directive. No local reference file — standard result, source lines omitted per rule.
- `lem:universal_jacobian_fib` (`Torelli.universalJacobianFiber`): fiber over $\tau(s)$ is $\mathrm{Jac}(\mathfrak{C}_s)$; uses `def:torelli_map`, `def:universal_av`, `def:jacobian_av`. Source: SettingUp.tex §6 (verbatim quote included).
- leandag: 0 unknown_uses, 0 isolated nodes in chapter.

## References consulted
- `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`
- `references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex`
- `blueprint/src/chapters/ModuliSpace.tex` (for `def:Mg_level`)
- `blueprint/src/chapters/Jacobian.tex` (for `def:jacobian_av`)
- `blueprint/src/macros/common.tex`
