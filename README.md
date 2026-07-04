# LeanAlgebraicGeometry-Horizon

LeanAG Horizon is a multi-project Lean 4 / Mathlib formalization workspace around algebraic geometry, orchestrated by [Archon Horizon](https://github.com/frenzymath/Archon-Horizon). Its central goal is the algebraic-geometry version of the [Algebraic Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian.20challenge/near/587802685), proposed by Christian Merten after Kevin Buzzard's original differential-geometry challenge on Zulip.

The repository is structured as an Archon Horizon workspace rather than a single monolithic project. The main Jacobian formalization (`MainProjects/Algebraic-Jacobian-Challenge`) is developed alongside supporting and extracted member subprojects (`SubProjects/*`) as well as related-paper formalizations, so that reusable infrastructure can be shared, built, and verified across the entire workspace.

You can consult the [live dashboard](https://axeldlv00.github.io/LeanAlgebraicGeometry/) for a visual overview of each project's blueprint, code, progress, and dependency DAG.

> **Note on freshness.** The dashboard is a static snapshot published to GitHub Pages, which serves every file with a 10-minute cache (`Cache-Control: max-age=600`). Run data refreshes on each reload, but the page shell itself can lag the workspace by up to ~10 minutes. If it looks stale, just reload; you normally do **not** need a hard refresh (and on Safari a "Reload From Origin" won't help the data anyway — see the caching notes in the Archon Horizon dashboard docs).

For interactive exploration and logs, run `horizon dashboard` inside the workspace to spin up the local web dashboard, or use `horizon run` and `horizon discuss` to interact with the orchestration agents.

## Table of Contents

- [Scope Map](#scope-map)
- [Methodology](#methodology)
- [How to Contribute ?](#how-to-contribute-)
- [License](#license)

## Scope Map

| Project | Lean Files | LOC | Code | Open Sorries |
| --- | :---: | :---: | :---: | :---: |
| `Albanese` | 25 | 13,756 | 6,891 | 12 |
| `Algebraic-Jacobian-Challenge` | 82 | 75,354 | 41,908 | 59 |
| `Cech-Cohomology` | 26 | 18,438 | 11,107 | 0 |
| `GR-Quot-Closure` | 8 | 19,960 | 13,308 | 0 |
| `Line-Bundle-Comparison-Iso` | 15 | 15,730 | 8,207 | 0 |
| `Picard-IdentityComponent` | 10 | 2,518 | 806 | 16 |

## Methodology

We use [Archon Horizon](https://github.com/frenzymath/Archon-Horizon) to orchestrate formalization across this multi-project workspace. Archon Horizon coordinates execution between two specialized agent roles:

- **Ground Agent** — the constrained strategist. Maintains LaTeX blueprints, dependency DAGs (`leandag`), roadmaps, local/GitHub inboxes, and prevents divergence across member projects.
- **Horizon Agent** — the autonomous prover. Runs self-directed proving sessions over long horizons, writing Lean code, repairing compiler errors, and constructing proofs.

Member projects are configured in `config.yaml`. Archon Horizon allows projects to read from one another and merge completed deliverables back into `MainProjects/Algebraic-Jacobian-Challenge`, making development across the workspace scalable and modular.

## How to Contribute ?

Contributions are welcome and can take several forms:

- **Issues & Discussions**: Propose new member subprojects, suggest guidance or hints for Archon Horizon, report mathematical gaps, or discuss specific code structures. If your issue concerns a particular declaration, please mention the declaration name, file path, and clarify whether the discussion concerns the statement, naming, proof strategy, or intended usage.
- **Pull Requests**: Pull requests are welcome for direct contributions to the formalization. Since autonomous agents actively run across member projects, it can be helpful to open an issue before starting a larger contribution or work inside an isolated subproject under `SubProjects/` so work is not duplicated.
- **Tooling**: When adding declarations, please make names clear, stable, and mathematical. We strongly recommend installing and using [Archon Horizon](https://github.com/frenzymath/Archon-Horizon) (`horizon`) when running or managing projects in this workspace so your contributions integrate cleanly with the multi-project configuration and blueprints.

## License

This repository is distributed under the [Apache License 2.0](LICENSE).

Author: Axel Delaval, AI4MATH@PKU
