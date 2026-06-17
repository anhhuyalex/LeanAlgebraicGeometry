# LeanAG Scope

> Note: You can consult the [dashboard](https://axeldlv00.github.io/LeanAlgebraicGeometry/), it allows to consult blueprints/code/progress/DAG of each project in a more visual way.

This repository aims at formalizing a set of related algebraic-geometry projects in Lean 4 / Mathlib. 

The main intent is solving the [Algebraic Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian.20challenge/with/603571555) originally proposed by Kevin Buzzard in its Differential Geometry version on Zulip, while we focus on the [algebraic geometry version](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian.20challenge/near/587802685) proposed by Christian Merten. 

This project also contains related formalization projects, which may share some common infrastructure with the Jacobian challenge. 

See the [scope roadmap](roadmap.md) for a high-level overview of the scope's member projects and their dependencies.

## Table of Contents

- [Scope Map](#scope-map)
- [Methodology](#methodology)
- [How to Contribute ?](#how-to-contribute-)

## Scope Map

| Project | Role in the scope | Main dependency direction | Status |
| --- | --- | --- | --- | 
| `Algebraic-Jacobian-Challenge` | Core Jacobian / Picard / curve geometry engine | Provides infrastructure for most downstream projects | 🔄 In progress |
| `Cech-Cohomology` | Čech comparison and higher direct image machinery | Feeds back into the Jacobian challenge and related papers | ✅ Complete |
| `Line-Bundle-Comparison-Iso` | Tensor/dual comparison isomorphisms for relative Picard | Unblocks the Jacobian challenge at large scale | 🔄 In progress |
| `Quot-Foundations` | Quot, Grassmannian, and flat-base-change foundations | Supports the secant-bundle paper formalization | 🔄 In progress |
| Related papers | Formalization of related algebraic-geometry papers | Share infrastructure with the Jacobian challenge | 📝 Blueprint in progress |

## Methodology 

We use [Archon v0.3.0](https://github.com/frenzymath/Archon) to progress in the formalization, using `Claude Opus 4.8` in the critical steps, and `Claude Sonnet` for routine tasks. 

Archon is launched autonomously, human intervention is sometimes used as "hints" given occasionally as guidance. Creating subprojects or merging subprojects also requires human intervention, but Archon is used to generate the content of the subprojects and merge them afterwards.

Note that the version of Archon we use makes allows projects to read from each other, therefore avoiding dupplication of work and allowing for a more organic development of the projects.

## How to Contribute ?

Contribution is very welcome, and can take various forms. First, you may raise issues to propose subprojects, or hints that should be given to Archon. 

You may also directly contribute to the formalization, in this case you can create pull requests. You may use Archon or your own methods. You may create your own subprojects to avoid dupplicating your contribution with Archon's work, as Archon is currently running in most of these subprojects. 

