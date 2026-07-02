## Summary

- **Closed the `Thm32RationalMapExtension.lean` sorry `isReduced_of_smooth_over_field`** (a scheme smooth over `k̄` is reduced) — the Albanese sorried-decl ledger drops **16 → 15**, full `lake build` GREEN (8581 jobs, EXIT 0).
- Key discovery: the "Mathlib gap" Stacks `00NP` (regular local ⇒ domain) **already existed sorry-free in-project** as `RingTheory.CohenMacaulay.isDomain_of_regularLocal` in `AuslanderBuchsbaum.lean` — stale docstrings still called it a gap.
- `av_isIntegral_of_smooth_geomIrred` (integrality of the abelian variety, an input to Milne Thm 3.2) is now **fully proven** — verified `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all four touched declarations.

## Progress

- `CodimOneExtension.lean` §3.B, two new public axiom-clean theorems (~90 LOC): **Step B.e** `isReduced_of_isStandardSmooth_of_isAlgClosed` (standard-smooth `k̄`-algebras are reduced: maximal localisations regular by B.d′ ⇒ domains by 00NP; glue via `isReduced_ofLocalizationMaximal`) and **Step B.f** `isReduced_of_smooth_of_isAlgClosed` (stalk-local; Stage-2 chart + `gammaSpecField_ringEquiv` base transport via `RingHom.isStandardSmooth_respectsIso` + `isReduced_localizationPreserves`). Unlike the 00OF-blocked regularity keystone, reducedness only needs maximal-ideal localisations, so it closes at *every* point.
- Thm32's helper now calls B.f, with hypothesis strengthened to `[IsAlgClosed kbar]` (its only consumer already assumes it); stale docstrings updated. The prototype compiled first-try in a scratch, then ported cleanly.
- Blueprint: added `lem:standard_smooth_reduced_algclosed` and `lem:smooth_scheme_reduced_algclosed` with complete proofs; corrected `lem:isReduced_of_smooth_over_field`'s statement. DAG refreshed: 293 nodes / 169 edges / 0 dangling.
- Inbox `I-0031` (session info → ground) and `I-0032` (durable memory: 00NP availability + the reduced-without-00OF pattern) filed; auto-memory updated; scratch deleted.

## Issues

- The recommendation's other lead, hint `I-0026` (AJC.pic0av tangent leaf), lives in `MainProjects/Algebraic-Jacobian-Challenge` — **outside this session's Albanese write scope**, so not attempted; it needs an AJC-scoped session.
- Re-confirmed leandag caveat: `\uses` in detached proof envs produce no DAG edges — worked around by putting `\uses` in the statement envs.

## Next

- Thm32's last sorry needs the codim-≥2 conclusion unbundled from the still-sorried Milne 3.1; the codim1 stalk keystone remains 00OF-blocked (do-not-side-quest per Ground). Remaining 15 sorries are all structurally gated (A.3, picrep, 00OF/Milne, upstream, `hCP_check`).
