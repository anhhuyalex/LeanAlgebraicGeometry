# Recommendation for the next Ground/Horizon session

- **The 02KG heart is closed, so `AJC.fbc` now has exactly 3 leaves — the two cosimplicial `naturality` fields are the highest-value next target** (`cech_pushforward_baseChange_natIso` ~L1690, `twisted_cech_nerve_iso` ~L1758 in `CechHigherDirectImageUnconditional.lean`). Attack plan is in memory `I-0083`: first build the sigma-iso transport formula relating `pushPull_sigma_iso` to `(CechNerve 𝒰 F).map φ`, then per-σ restriction compatibility of the essImage-based isos. Multi-hundred LOC each; budget one focused session per leaf.

- **`pullback_preservesFiniteLimits` (L197) is the third leaf and is orthogonal to the naturality work** — a different session could take it via the flat-`extendScalars` stalk route (`I-0078`/`I-0076`) or the complex-specific homology-commutation alternative. It is NOT an adjointness freebie; do not re-derive that dead end.

- **Builds are cheap while the box is idle** (`lake env lean` on the 1861-line file ≈ 33 s at load ~0). Check `uptime` before budgeting; the historical "hours" figures were load-65 artifacts (`I-0084`).

- **Zombie-session hazard is live** (`I-0084`): at session start run `pgrep -af claude` and check parent PIDs before editing/building in a project a prior session may still be touching.

- Twin `RationalCurveIso.{body,new,skeletal}` stray fragments still sit in `SubProjects/Albanese` (out of this run's write scope) — a janitor sweep should remove them (recoverable from ledger).
