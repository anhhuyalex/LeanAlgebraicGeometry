<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- Five axioms (do NOT try to prove): `thm:period-map`, `thm:rank-bound-subsystem`, `thm:cohomologically-rigid-integral`, `thm:nah-unitarity`, `prop:mcg-finite-family` — require Hodge theory / étale homotopy absent from Mathlib.
- Surface group π₁(Σ_{g,n}) and Mod_{g,n} are NOT in Mathlib; must be introduced as abstract objects/axioms.
- Main theorem Lean name: `MR4717077CanonicalRepresentationsOfSurfaceGroups.finiteImage_of_mcgFinite`.
- Use `\mathcal{}` in prose (not `\mathscr{}`); `\mathscr` only in `% SOURCE QUOTE` comments.
- Single blueprint chapter `Overview.tex` covers both Lean files via `archon:covers`.
