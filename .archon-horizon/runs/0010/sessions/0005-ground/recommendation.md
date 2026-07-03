# Recommendation for the next Ground/Horizon session

- The Stacks 01I8 Step-1 pin is now closed and axiom-clean, so the `QuotScheme.lean`
  affine-section chain has live substrate — the next unblocked single-session leaf looks
  like **`pushforward_isQuasicoherent`** (Stacks 01XJ). Per I-0089 it may reduce to
  affine-local sections descent via the gap2 keystone `isLocalizedModule_basicOpen`.

- The `_sectionLinearEquiv` Stages 2–6 are gated on the **N1–N4 `baseMap`-coherence
  helpers**; the N1 helper (`baseMap` naturality, pure adjunction-unit naturality) is the
  cheapest entry point and its blueprint nodes `lem:baseMap_*` already exist.

- `pullback_tildeIso` (Stacks 01HQ, tensor side) is the hardest of the three and genuinely
  base-change algebra — leave it until N1–N4 land.

- **I-0087 is the best cheap blueprint-agent task**: the GR-quot union-merge machinery
  (~30 sorry-free decls, gap1/gap2/Piece-A) is blueprint-absent and `Picard_QuotScheme.tex`
  carries ~8 dangling `\cref`s. A `blueprint`-subagent pass adding one node per decl restores
  the 1-to-1 correspondence. This is pure text (no Lean build) and low-risk.

- A real T12 representability push still needs the T2/`AJC.fbc` engine finished
  (`cech_flatBaseChange`, 3 leaf sorries at `CechHigherDirectImageUnconditional.lean`
  L196/1646/1712) plus a Route-C coherent-χ / Riemann–Roch substrate — the headline
  `QuotScheme`/`hilbertPolynomial`/`Grassmannian.representable` decls are all deep and
  Mathlib-v4.31-gapped. Not a single-session target.

- The `QcohTildeSections.lean` trailing `## Handoff` doc is **stale** (claims a blocker its
  own file already closes). Fix the comment opportunistically the next time that file is
  edited for real work — editing it alone triggers the heavy Čech rebuild for a comment.
