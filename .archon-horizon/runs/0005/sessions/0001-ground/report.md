Both items registered. Here is my report.

## Summary
- Opening Ground for run 0005 (focus **T5**: extract & prove Pic⁰ `IdentityComponent`). No prior Horizon diff — I set direction.
- **STEP-0 gate PASSED**: I traced the `Picard/IdentityComponent` import cone (9 AJC modules + Mathlib) and confirmed it is **free of the Čech/flat-base-change engine** — safe to extract in parallel with the live T2 FBC build.
- Blueprint node `Picard_IdentityComponent.tex` is already complete and dependency-correct — no fixes needed.

## Progress
- Verified the 9 sorries individually against Lean + blueprint + mathlib v4.31 source.
- Confirmed the reverse "connected + `k`-rational section ⟹ geometrically connected" (Stacks 037Q/04KU) is **absent** from v4.31 `Geometrically/Connected.lean` (forward direction only).
- Confirmed `PicScheme` and `GrpObj (PicScheme C)` are `⟨sorry⟩`-backed (`FGAPicRepresentability.lean`, 26 sorries).
- Wrote `recommendation.md`; added roadmap comment on `AJC.picrep`; filed `I-0035` (info→human), `I-0036` (durable memory).

## Issues
- **All 9 IdentityComponent sorries are blocked, not proof-search debt**: §1 substrate (4) on the 037Q/04KU/02LB descent gap; Pic⁰ leaves (5) on the sorry-backed FGA foundation + χ-blocked Hilbert-poly + AJC.pic0av tangent-space overlap. STEP-2 ("close the 9 sorries") is over-optimistic — flagged to human.
- Task write-scope tension: T5 `write_set` is the AJC file, but STEP 1 creates `SubProjects/Picard-IdentityComponent`; Horizon's launch scope must cover the new subproject.
- `horizon` warns `MR0555258-Compactifying-Picard` mathlib is pinned v4.30.0 vs declared v4.31.0 (relevant to T7).
- No `lake build` run — opening Ground, nothing extracted yet; conclusions rest on static cone tracing + mathlib source (both done in-session).

## Next
- First Horizon T5 session: land the **isolated green subproject** (STEP 1, Albanese lakefile template) as the deliverable; preserve the 9 sorries as documented placeholders.
- Attempt only the marginal `Pic0Scheme` structural tidy if `LocallyOfFiniteType (PicScheme C).hom` resolves; do **not** chase 037Q/04KU or duplicate AJC.pic0av.
