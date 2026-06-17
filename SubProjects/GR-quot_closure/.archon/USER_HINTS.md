<!--
USER_HINTS.md — two sections with different lifecycles.

## Temporary hints
  Consumed by the next plan phase and then cleared. Use for one-shot
  steering: "try route X this iter", "skip Lane F this round".

## Persistent hints
  NEVER auto-cleared. These are standing directives that survive every
  iteration reset. The plan agent treats them as HIGHER PRIORITY than
  any conflicting instruction in its own prompt or in
  .archon/prompts/plan.md. Use for project-wide constraints:
    - "never accept axiom X"
    - "don't touch theorem Y until I say so"
    - "always run mathlib-build mode on Lane I"

Format for both sections (one bullet per hint, timestamped):
  - [YYYY-MM-DDTHH:MM:SSZ] hint text

Hints are written by 'archon discuss' or directly by you. In discuss,
the agent will ask which section to target; in a direct edit, place your
bullet under the appropriate heading.

File-specific hints (one .lean file only) belong as /- USER: ... -/
comments inside that file — NOT here.
-->

## Temporary hints


## Persistent hints

- [2026-05-31T00:00:00Z] AUTONOMOUS OPERATION (permanent until user removes this hint): There is no reason for Archon to escalate to the user. It should always find the best path, think about all possibilities, and make the correct decision. In some cases refactoring may be a good option to a dead-end.
- [2026-05-31T00:00:00Z] PARALLELISM VIA FILE SPLITTING: Use more parallelism by dividing files with many theorems or lemmas into smaller, semantically relevant files that can work with parallel provers.
- [2026-05-28T00:00:00Z] REFERENCE-DRIVEN PROOFS: Every prover lane directive must cite the precise theorem/proposition number from the mathematical references (Kleiman "Picard schemes" FGA, Nitsure FGA chapter, Milne "Abelian Varieties", SGA 7, Stacks Project) corresponding to each declaration being proved. If a proof step cannot be directly traced to a reference, find the reference before dispatching the prover — do not improvise mathematical content without a reference anchor.
- [2026-06-17T00:00:00Z] SNAP IS SHARED WITH THE SIBLING `FBC-B_SNAP-chain` (extract decomposition). The section-graded-ring nodes (`def:sectionsCast`, `lem:sectionsCast_refl`, `lem:gradedMonoid_eq_of_cast`, `lem:sectionMul_coherent`, and the `Γ_*(X,L)` graded-assembly lemmas) live in BOTH this GR-quot cone and the sibling's cone. KEEP them as `sorry` in this project, OR retrieve the sibling's finished proofs and import them — do NOT diverge the two encodings. Lean names/labels/paths are byte-identical to the parent and the sibling, so a closed SNAP merges back as a three-way merge. See `.archon/extract-manifest.json` `overlaps`.
- [2026-06-17T00:00:00Z] χ-BLOCKED TARGETS NOT CLOSABLE IN THIS LEG: `def:hilbert_polynomial` (`Scheme.hilbertPolynomial`) and `def:quot_functor` (`Scheme.QuotFunctor`) are in the cone (blueprint wires `grassmannian_scheme \uses quot_functor \uses hilbert_polynomial`), but the Lean `hilbertPolynomial` is χ-SEMANTIC (`Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`, verified in QuotScheme.lean docstring/body) and needs a higher-cohomology engine this Čech-independent (i=0) leg does NOT have. Keep both as `sorry`; fill from the cohomology leg at merge-back. NEVER fabricate an H⁰ `Φ_s` under the χ label. (The blueprint ENCODING comment in `Picard_QuotScheme.tex` claiming an H⁰ encoding is INCONSISTENT with the actual χ Lean decl — the Lean source governs.) The rank-d Grassmannian itself only needs the constant Hilbert poly `Φ=d` (χ-free), so `grassmannian_scheme`/`representable` are still closable here.

