# LeanAlgebraicGeometry 

LeanAG is a collection of Lean 4 / Mathlib formalization projects around algebraic geometry. Its central goal is the algebraic-geometry version of the [Algebraic Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/583336-Autoformalization/topic/Jacobian.20challenge/near/587802685), proposed by Christian Merten after Kevin Buzzard's original differential-geometry challenge on Zulip.

The repository is organized as a scope rather than a single monolithic project. The main Jacobian formalization is developed alongside supporting subprojects and related-paper formalizations, so that reusable infrastructure can be shared across the whole effort.

You can consult the [dashboard](https://axeldlv00.github.io/LeanAlgebraicGeometry/) for a visual overview of each project's blueprint, code, progress, and dependency DAG.

See the [scope roadmap](roadmap.md) for a high-level overview of the scope's member projects and their dependencies.

For more details, run `archon dashboard <project-name>` for any project in the scope and consult the generated dashboard. It renders logs and diffs that cannot be shown on the static webpages.

## Table of Contents

- [Scope Map](#scope-map)
- [Methodology](#methodology)
- [How to Contribute ?](#how-to-contribute-)
- [License](#license)

## Scope Map

| Project | Role in the scope | Main dependency direction | Status (open `sorry`) |
| --- | --- | --- | --- | 
| `Algebraic-Jacobian-Challenge` | Core Jacobian / Picard / curve geometry engine | Provides infrastructure for most downstream projects | 🔄 In progress (87) ✨ |
| `Cech-Cohomology` | Čech comparison and higher direct image machinery | Feeds back into the Jacobian challenge and related papers | ✅ Complete (0) — merged back sorry-free into AJC ✨ |
| `Line-Bundle-Comparison-Iso` | Tensor/dual comparison isomorphisms for relative Picard | Unblocks the Jacobian challenge at large scale | 🔄 In progress (4) ✨ |
| `Albanese` | Albanese universal property + abelian-variety / codim-one extension leg | Extracted from `Algebraic-Jacobian-Challenge`; merges back | 🔄 In progress (17) ✨ |
| `RiemannRoch` | Weil divisors, `O(D)`/`O(P)`, `H¹`-vanishing and the RR formula core | Extracted from `Algebraic-Jacobian-Challenge`; merges back | 🔄 In progress (18) ✨ |
| `Quot-Foundations` | Quot, Grassmannian, and flat-base-change foundations | Deferred — active work moved to the `GR-quot_closure` / `FBC-B_SNAP-chain` extractions | ⏸️ Deferred (21) |
| `GR-quot_closure` | Grassmannian-quotient representability (H⁰ leg) | Extracted from `Quot-Foundations`; merges back | 🔄 In progress (9) ✨ |
| `FBC-B_SNAP-chain` | Flat-base-change leg + shared SNAP foundation | Extracted from `Quot-Foundations`; merges back | 🔄 In progress (16) ✨ |
| 36 related-paper projects | Formalization of related algebraic-geometry papers | A few consume the AG base (secant/perverse/Mordell–Lang); most are self-contained | 📝 Blueprint only (0 Lean) |

> Note: The related papers do not directly contribute to the Jacobian challenge, they are not advanced yet, I included them here because they might indirectly contribute. However, contributors or readers should focus their attention on the AJC and its related subprojects. 

## Methodology

We use [Archon v0.3.0](https://github.com/frenzymath/Archon) to make progress on the formalization, with `Claude Opus 4.8` for critical steps and `Claude Sonnet` for routine tasks.

Archon is launched autonomously, human intervention is sometimes used as "hints" given occasionally as guidance. Creating subprojects or merging subprojects also requires human intervention, but Archon is used to generate the content of the subprojects and merge them afterwards.

The version of Archon used here allows projects to read from each other. This helps avoid duplicated work and makes development across the scope more organic.

## How to Contribute ?

Contributions are welcome and can take several forms.

Issues are a good place to propose new subprojects, suggest hints that should be given to Archon, report gaps, or comment on specific parts of the code. If your issue concerns a particular declaration, please mention the declaration name and file path, and explain whether the question is about the statement, the name, the proof strategy, or its intended use.

Pull requests are welcome for direct contributions to the formalization. You may use Archon or your own methods. Since Archon is currently running in most subprojects, it can be useful to open an issue before starting a larger contribution, or to work in a separate subproject that you created, or to choose a point in [the roadmap](./roadmap.md) that is marked `[ ]`, so that work is not duplicated.

When adding declarations, please make names as clear and stable as possible. A good name should indicate the mathematical content of the result, fit the surrounding namespace, and be easy to search for later. If a theorem is only a temporary helper, make that clear either from its local context or from a short comment/docstring.

We recommend using [Archon v0.3.0](https://github.com/frenzymath/Archon) if you run projects in this scope, because the project is structured to be compatible with Archon, but you may also use your own methods, with or without harness.

## License

This repository is distributed under the [Apache License 2.0](LICENSE).

Author: Axel Delaval, AI4MATH@PKU