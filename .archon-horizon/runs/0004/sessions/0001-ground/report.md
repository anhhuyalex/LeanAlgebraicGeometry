All three deliverables landed (hint `I-0011`, human info `I-0012`, roadmap comment on `AJC.linebundle`). The workspace needed no source edits — the blueprint was already honest and both trees are clean. Here's my report.

## Summary

- **T1 (merge Line-Bundle comparison-iso substrate into AJC) has not been worked on yet** — both project trees sit at registered baseline; run 0004 has only this Ground session. My role this round was **verification and setup**, leaving Horizon a precise, correct merge map.
- **T1 is verified merge-ready.** Both `Algebraic-Jacobian-Challenge` and `Line-Bundle-Comparison-Iso` are on `leanprover/lean4:v4.31.0` and the relevant modules compiled (oleans newer than source). This is a genuine finished-substrate **port**, not a migration repair.

## Progress

- **Corrected the stale sorry inventory.** AJC has **3** real `sorry`s, all in `Picard/TensorObjSubstrate.lean` (`tensorObj_unit_iso` @302, `tensorObj_restrict_iso` naturality @512, keystone `exists_tensorObj_inverse` @735) — **not** the task's "5 (×3 + PullbackTensorComp ×2)". `PullbackTensorComp.lean` is already `sorry`-free (closed upstream, iter-320).
- **Mapped the merge.** LBC refactored the keystone out into a new file `Picard/TensorObjInverse.lean` (sorry-free, 3424 lines) + 5 supporting files absent from AJC; the two small isos have closed bodies in LBC's `TensorObjSubstrate.lean`. Full chain + reconciliation risks handed to Horizon in **`I-0011`** (hint).
- **Blueprint checked, found honest.** `lem:tensorobj_restrict_iso`, `lem:tensorobj_inverse_invertible`, `lem:tensorobj_unit_iso` carry statement-level `\leanok` only; their proof blocks are correctly `\leanok`-free. No false-proved flag — no edit made.
- Logged status on roadmap `AJC.linebundle`; notified the human of the stale premise + readiness (**`I-0012`**).

## Issues

- **No fresh `lake build` was run this session.** The "both sides green on v4.31.0" claim rests on olean-vs-source mtimes, not a live rebuild (full AJC build too heavy for a one-shot). The definitive post-merge build is Horizon's to run.
- **Merge is not a clean file-add.** AJC's base `TensorObjSubstrate.lean` (2185 lines) diverges from LBC's (4592); the new LBC files may reference LBC-only base decls, and AJC's `PullbackTensorComp` vs LBC's `PullbackTensorMapIso` is a route mismatch. Both risks flagged in `I-0011`.
- Out-of-scope, still open: GR cluster hard v4.31 errors (`I-0001`/`I-0006`) — untouched this round, unrelated to T1.

## Next

- Human: `horizon run T1` — it is verified ready; Horizon should follow `I-0011`.
- Horizon (T1): port the 2 iso bodies + bring in the LBC keystone file-set, reconcile base-file divergence, build green, then add proof `\leanok` to the 3 blueprint nodes, refresh the DAG, and close `AJC.linebundle`.
