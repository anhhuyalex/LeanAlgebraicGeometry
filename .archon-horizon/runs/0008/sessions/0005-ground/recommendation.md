# Recommendation — run 0008 reconcile Ground (T5, `AJC.picrep`/`AJC.pic0av` spine)

Suggestions for the next Horizon/Ground agent. Grounded in the T5 reconcile; you self-scope.

## Next

- **`tangentSpaceIso` (`AJC.pic0av`) is now the single highest-value target** — the FGA rewire removed the opaque-`picSharp` blocker that made it unattackable. The move: attach **Kleiman Thm 5.11** (`Pic(C_ε) ≅ H¹(C_ε, O^×)` cocycle classification + the truncated-exponential split sequence `0 → O_C → O^×_{C_ε} → O^×_C → 1`, kernel `= H¹(C, O_C)`) through `(representable C).homEquiv` at `T = Spec k[ε]`. None of this H¹ machinery exists yet — it is the **largest remaining block** and now genuinely unblocked.

- **`Pic0Scheme.isAbelianVariety`'s `GrpObj` conjunct is now provable** via `IdentityComponent.isSubgroupHomomorphism` (`groupSchemeStructure` supplies `GrpObj (PicScheme C)`). Worth **splitting the 4-way conjunction** (proper ∧ smooth ∧ GrpObj ∧ finrank=genus) so the provable parts close now instead of waiting on the whole.

- **The FGA rewire is conditional on `[HasRationalPoint C]`** (see `I-0077`). Before anyone assembles the north star `AJC.jacobian`, decide: Galois/étale descent from a pointed finite extension, **or** a pointed restatement of `JacobianWitness`. This is a strategy call, not proof-search.

## Watch-outs

- **Build hazard is live**: a concurrent `claude-fable-5` Horizon agent + one `lean` compiler process were running during this reconcile. The FGA/RelPic/pic0av cone is **FBC-free** (does not import the `Cech*` chain), so it is safe to iterate there — but still `pgrep -f bin/lean` before any `lake build`, and never touch the `Cech*` oleans.

- `SubProjects/Picard-IdentityComponent` mirror is **further behind AJC** now (missing the rewired `FGAPicRepresentability`/`IdentityComponent` + `Pic0Scheme` real def). Re-sync or retire; out of this session's write scope.

- The genuine FGA `sorry` `instHasPicScheme` is the real Grothendieck existence theorem (Kleiman §4 `th:main` + `cor:algsch`) — a large build, not a quick win. Do not re-probe the `HasDivFunctor`/`HasAbelMap` carriers either; they are Quot-scheme-blocked (χ/Hilbert-polynomial endgame).
