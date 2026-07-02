I've completed the Ground review for run 0002 / T3. Here is the report.

## Summary
- This is the opening session of run 0002 — **no Horizon T3 work exists yet** (Albanese VCS has only the `baseline` commit), so I verified the true starting state and re-scoped the task.
- **Albanese `lake build` is GREEN (EXIT=0, ~13s): 18 `sorry` warnings, no hard v4.31 compile errors** — materially unlike GR-Quot-Closure.
- The **T3 premise is inaccurate**: the sorries are pre-existing *structural* placeholders (source docstrings say "iter-177 file-skeleton", "pending the A.3 row chapter", "Mathlib-upstream PR"), not v4.31 migration debt.

## Progress
- 18 real sorries across 8 files (roadmap's "17" is essentially right). Split by real blocker:
  - **Blocked** — `AlbaneseUP` ×7 (all descend from `bundle := sorry`, needs A.3/`AJC.pic0av`); `FGAPicRepresentability` ×2 (`⟨sorry⟩` existence = `AJC.picrep`); `WeilDivisor` ×1 (Mathlib upstream).
  - **Attackable now** — `CodimOneExtension` ×3, `GmScaling` ×3, `Points` ×1, `BareScheme` ×1; `Thm32` ×2 partly blocked.
- Disproved the "port from AJC" shortcut — AJC copies carry the **same** sorries (`AlbaneseUP` byte-identical), and `Genus0BaseObjects/*` are Albanese-only.
- Filed `I-0007` (info→human: re-scope), `I-0008` (hint→horizon: where to work/avoid); commented `ALB.up`, `ALB.fga`, `ALB.codim1`; recorded 2 memory files.

## Issues
- **T3 can't reach 0-sorry Albanese this round** — ~10/18 are blocked on active cones or upstream. Proposed re-scope to the ~8 self-contained sorries.
- Stray scratch `RationalCurveIso.{body,new,skeletal}` in the Albanese root (orphaned blueprint fragments) — left in place, flagged.
- Out-of-scope config warning: `MR0555258` pins mathlib `v4.30.0` vs declared `v4.31.0`.
- I did **not** edit any Lean (Ground doesn't do proof search) and did not touch the Albanese blueprint (no new work to reconcile).

## Next
- Human: decide on the T3 re-scope (`I-0007`) and whether to gate `ALB.up`/`ALB.fga` behind A.3 / picrep.
- Horizon (if run): follow `I-0008` — `Genus0BaseObjects/*` + `CodimOneExtension`; skip `AlbaneseUP`/`FGA`/`WeilDivisor`.
