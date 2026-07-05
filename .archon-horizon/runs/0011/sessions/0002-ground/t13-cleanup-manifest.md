# T13 Cleanup Manifest — genus-0 / Route-C surface (Algebraic-Jacobian-Challenge)

Paths are absolute; AJC root = `/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge`. Repo root = `/home/Axel/LeanAlgebraicGeometry-Horizon`.

Sequence note: do the **WeilDivisor carve first**, then update `roadmap.md` sorry counts, then rebuild web/. Ordering matters for the ×2→×1 count (below).

---

## 1. In-scope edits

### A. `/home/Axel/LeanAlgebraicGeometry-Horizon/roadmap.md`
- **L70** (stale-dead) — REWRITE. `Genus0BaseObjects` is deleted from the AJC tree (only stale `.lake` oleans remain); `Ga`/`Gm`/`ProjectiveLineBar` are likewise gone from AJC. Drop "defined"/"sorry-free in-tree"; state the group-scheme base objects + `Genus0BaseObjects` were retired from AJC with the genus-0 removal and now live only in the `SubProjects/Albanese` carve.
- **L72** (contradiction — see §3.5) — KEEP the live fact `RiemannRoch/WeilDivisor` remains in-tree, but (i) DELETE the trailing clause "the standalone `RiemannRoch` extraction is now obsolete" (no such subproject exists in `SubProjects/` or `config.yaml`), and (ii) change **×2 → ×1** *after* the carve deletes the L1138 sorry (only the L830 sorry survives).
- **L64–65** (stale-dead, genus-0-adjacent) — REWRITE. `Cotangent/*`, `Differentials`, standalone `Rigidity`/`RigidityKbar` are deleted from AJC (stale oleans confirm). Cite only survivors: `RigidityLemma.lean`, `Genus.lean`, `AbelJacobi.lean`.
- **L112–113** (contradiction — see §3.6) — KEEP as Albanese-carve history, but add caveat: "restored from the parent" is now dangling — the parent AJC copy of `Genus0BaseObjects/BareScheme` has since been deleted (genus-0 base is Albanese-only now).
- **L120** (contradiction — see §3.6) — KEEP. This is the **Albanese subproject** section; `SubProjects/Albanese/AlgebraicJacobian/Genus0BaseObjects/{BareScheme,Points}.lean` + `RiemannRoch/WeilDivisor.lean` all exist. Verify the ×1 counts against the current Albanese build. (Do NOT apply the lean-comments scout's "delete these entries" here — that scout mistook this Albanese row for the AJC tree.)
- **L77** (good-current-doc) — KEEP. Optionally disambiguate: label this the DEAD genus-0-base Route-C leg, distinct from the LIVE coherent-χ endgame at L62/L75.
- **L75** (good-current-doc) — KEEP; verify χ-blocked Quot sorry counts current. This is LIVE Route-C part (b).
- Non-genus-0 hygiene (optional, adjacent): L29 add missing `Picard-IdentityComponent` subproject row; L27–28 normalize display names to canonical keys `GR-Quot-Closure`, `MR0555258-Compactifying-Picard`.

### B. WeilDivisor carve — `/home/Axel/…/AlgebraicJacobian/RiemannRoch/WeilDivisor.lean` (1335 lines)
**Do NOT wholesale-delete** (breaks `CodimOneExtension` + `AlgebraicJacobian.lean` aggregator import L93). Carve in place.

Sorry ledger: currently **×2** = L830 (KEEP block) + L1138 (DELETE block). After carve → **×1** (L830 only).

| Range | Decls | Action |
|---|---|---|
| L1–53 | header prose (genusZero_curve_iso_P1 / RiemannRoch_RationalIsoP1.tex framing, 9-pin list) | **REWRITE** (not blank) — header describing only the codim-1 valuation substrate (PrimeDivisor, order, IsRegularInCodimensionOne, order naturality). Drop pins 3,4,5,8. |
| L13–15, L31–33 | docstring `genusZero_curve_iso_P1`/`AbelianVarietyRigidity` (deleted); RR.2/RR.3/RR.4 → RRFormula/OcOfD/RationalIsoP1.tex (nonexistent) | subsumed by header rewrite; retarget prose to live consumer `Albanese/CodimOneExtension`. |
| L55–61 | set_option/universe/open/namespace | **KEEP** untouched |
| L63–98 | §1 doc + `Scheme.PrimeDivisor` structure | **KEEP** — BUILD-CRITICAL minimal keep-set (see §3.1) |
| L100–116 | `Scheme.WeilDivisor` type + instances | **KEEP** (task list). Note: becomes dag-orphan after carve; Horizon may drop for a truly minimal file. |
| L118–215 | PrimeDivisor open-immersion bridge (ext/restrictToOpen/ofOpen/equivOpen/stalkIso) | **KEEP** |
| L219–353 | `Ring.*` ord naturality helpers | **KEEP** |
| L357–388 | `Scheme.Opens.functionFieldIso` | **KEEP** |
| L390–431 | §2 doc + `RationalMap.order` | **KEEP** |
| L433–500 | `IsRegularInCodimensionOne` class + 3 instances | **KEEP** |
| L518–536 | `ordFrac_stalkIso_naturality` | **KEEP** |
| L538–623 | `functionFieldIso_compat`, `order_eq_order_restrict` | **KEEP** |
| L625–753 | `order_*` algebraic family | **KEEP** |
| L755–830 | `rationalMap_order_finite_support` (**KEEP-block sorry L830**) | **KEEP**; TRIM stale comment L819–829 (Route C PAUSE + never-defined `degree_positivePart_principal_eq_finrank`) and L791 "HARD BAR pause" note. Gap sorry stays. |
| L832 | `namespace Scheme.WeilDivisor` | REMOVE if the whole §3–§7 body is carved and only PrimeDivisor/order substrate remains. |
| L836–884 | §3 `ofClosedPoint` family (+ header L836–841) | **DELETE** (Route-C RR→ℙ¹; no consumers) |
| L886–956 | §4 `degree`/`degree_hom`/arith (+ header L886–887) | **DELETE** (RR→ℙ¹ degree machinery; no consumers) |
| L958–1000 | `principal`/`principal_apply` | **VERIFY-then-DELETE** (dag-orphan after §4/§6 go) |
| **L1002–1015** | `order_one` | **KEEP — TRAP** (interleaved in principal block; must survive; relocate into L644–753 or leave in place) |
| L1017–1084 | `principal_one`/`principal_hom` | **VERIFY-then-DELETE** (dag-orphan) |
| L1086–1138 | `principal_degree_zero` (**DELETE-block sorry L1138**) | **DELETE** (RR→ℙ¹ endgame via φ:C→ℙ¹; no consumers) |
| L1140–1309 | §6 `positivePart` block | **DELETE** — scaffolding for phantom `degree_positivePart_principal_eq_finrank` (referenced 9×, never defined) |
| L1311–1330 | `LinearEquivalence` | **VERIFY-then-DELETE** (dag-orphan) |
| L1332/L1334 | `end Scheme.WeilDivisor` / `end AlgebraicGeometry` | KEEP (adjust if namespace removed) |

CodimOneExtension keep-set: only `Scheme.PrimeDivisor` (L79–98, `.point` field) is consumed downstream, at `CodimOneExtension.lean:1865–1879` (`mem_domain_iff_exists_partialMap_through_point`, ref L1874). See §3.1 + §3.4 (grep `.order` too).

### C. `/home/Axel/…/AlgebraicJacobian/RigidityLemma.lean`
- **L786–787** (stale-prose-live-math) — REWRITE prose, keep math. Milne Cor 1.5/1.2 are LIVE (consumed by `Albanese/AlbaneseUP`). Replace "that feed the genus-`0` base case (Route C)" with "used by the Albanese universal-property construction (Milne §I.1 additivity)".

### D. `/home/Axel/…/AlgebraicJacobian/Albanese/*.lean` (in write-glob; low-priority prose softening)
- `AuslanderBuchsbaum.lean:18` (stale-dead) — **REMOVE broken pointer** "Per STRATEGY.md L30" (no `STRATEGY.md`, no `.archon/`); re-anchor to `roadmap.md` or drop.
- `AlbaneseUP.lean:12–15`, `AuslanderBuchsbaum.lean:11–12`, `CodimOneExtension.lean:14`, `Thm32RationalMapExtension.lean:13–14` — optional soften "positive-genus arm of `nonempty_jacobianWitness`" (two-arm split retired; witness is now uniform). Math is LIVE — keep. E.g. "positive-genus content of the uniform `nonempty_jacobianWitness`".

### E. Blueprint `.tex` — `/home/Axel/…/blueprint/src/chapters/`
- `RiemannRoch_WeilDivisor.tex`:
  - **L14–18** (stale-dead) — REMOVE the `genusZero_curve_iso_P1` headline-bridge claim (not a real Lean decl).
  - **L11–26** — REWRITE Setup/motivation: drop RR.1–RR.4 bridge framing; reframe as standalone Weil-divisor substrate for the Albanese codim-1 order map (consumers `Albanese_CodimOneExtension`, `Albanese_CoheightBridge`).
  - **L53–55**, **L1130** ("RR.2–RR.4" tag), **L1465** ("depended on by the RR.3/RR.4 chain"), **L1594–1595** ("lives in the sibling chapter RR.3") — DROP the dead RR.2/RR.3/RR.4 sibling-chapter pointers; keep surrounding live math.
  - **L1633–1648** — REMOVE the three "sibling chapter (to be added)" bullets (RiemannRoch_OcOfD/_RRFormula/_RationalIsoP1.tex — retired, never added).
- `Albanese_AlbaneseUP.tex` **L521–529** — REWRITE the NOTE: drop dead `RiemannRoch_RRFormula.tex` ref; re-point gating at the LIVE coherent-χ substrate (`cor:flattening_stratification_curve`, `lem:cech_flat_base_change`). Lemma itself is live.
- `AbelianVarietyRigidity.tex` **L3** — REMOVE dead duplicate `\label{chap:avr_for_rr}` (only `\label{chap:AbelianVarietyRigidity}` L2 is `\cref`'d; source of stale `chap-avr_for_rr.html`). **L708** — reword comment to drop "which is what the genus-0 consumer needs" (lane retired; `av_regularMap_isHom_of_zero` is live).
- `Picard_FGAPicRepresentability.tex` **L888–889, L1036–1039, L1092–1097** — KEEP (LIVE Route-C coherent-χ face gating Sorry A / `instHasPicScheme`). Only verify wording still matches `cor:flattening_stratification_curve`, `lem:cech_flat_base_change`. No removal.
- KEEP / no edit (good-current-doc, uniform-Jacobian narrative): `Jacobian.tex` L4/100/200/269/437; `AbelJacobi.tex` L68; `Picard_Pic0AbelianVariety.tex` L1502–1505/1586–1591; `Picard_IdentityComponent.tex` L1132–1136.
- `content.tex` **L34** `\input{chapters/RiemannRoch_WeilDivisor}` — KEEP (only surviving RR chapter). No `\input` removals needed; all 33 live chapters stay.
- Adjacent blueprint-hygiene (NOT genus-0/Route-C — fix opportunistically): `Picard_GlueDescent.tex` **L597/605** (`lem:gr_glueChartFamily_pullback_map_pi`) and **L598/613** (`lem:gr_glueChartComponent_leg_compat`) — the 2 dangling `\uses`/`\cref` with no `\label`. Drop from `\uses` + reword `\cref`, or add the intended `\label` (near-miss: `lem:gr_glueChartFamily_equalizes`, `lem:gr_glueChartComponent_self_counit`).

### F. Blueprint `web/` (generated) — `/home/Axel/…/blueprint/web/`
- **REGENERATE wholesale** via plasTeX from `content.tex`; do NOT hand-edit HTML. Entire dir is a stale Jun-17 build predating genus-0 retirement (all ~38 files carry a stale TOC "BareScheme.lean … ℙ¹" link → `chap-avr_for_rr.html#a0000000063`).
- Regeneration drops the 15 orphan HTML with no `.tex` source. Genus-0/Route-C orphans (7): `chap-Genus0BaseObjects_Cross01Substrate.html`, `chap-avr_for_rr.html`, `chap-RiemannRoch_RationalCurveIso.html`, `chap-RiemannRoch_RRFormula.html`, `chap-RiemannRoch_OcOfD.html`, `chap-RiemannRoch_OCofP.html`, `chap-RR_H1Vanishing.html`. Other orphans that also vanish (rename/merge, out of T13 scope): `chap-Rigidity`, `chap-RigidityKbar`, `chap-Picard_Functor`, `chap-Picard_FunctorAb`, `chap-Picard_LineBundle`, `chap-cotangent-chartalgebra-s3`, `chap-cotangent-grpobj`, `chap-differentials`.

---

## 2. Out-of-T13-scope residue (human decides whether to widen)

Stale-dead (broken pointers — worth fixing if scope widens):
- `AlgebraicJacobian/Genus.lean:28` — broken `.archon/STRATEGY.md` ref (no `.archon/`; `blueprint/src/chapters/Genus.tex` DOES exist). Flag Genus-scope owner.
- `AlgebraicJacobian/Cohomology/SheafCompose.lean:11–23`, `Cohomology/StructureSheafAb.lean:11`, `Cohomology/StructureSheafModuleK.lean:13` — broken `STRATEGY.md` refs. Flag Cohomology-scope owner.

Good-current-doc (accurate; leave as-is even if scope widens):
- `AbelJacobi.lean:16–28, 78–80` — correctly documents "no genus-0 dite", uniform witness. Keep.
- `Jacobian.lean:22–26, 178–184` — accurate description of retired `genusZeroWitness`/`positiveGenusWitness` split. Keep.
- `Picard/QuotScheme.lean:139–168` (§1 Hilbert polynomial / Snapper / χ) — LIVE coherent-χ substrate, no genus-0 prose. Keep.

Non-genus-0 web orphans (already covered by §1.F regeneration): cotangent/differentials/Picard-rename/Rigidity HTML.

---

## 3. Dependency traps & correctness cautions

1. **WeilDivisor → CodimOneExtension build trap.** Wholesale-deleting `WeilDivisor.lean` breaks `Albanese/CodimOneExtension.lean` (uses `Scheme.PrimeDivisor.point` at L1874) and the `AlgebraicJacobian.lean` aggregator import (L93). Minimal keep-set = `Scheme.PrimeDivisor` (L79–98). Carve, don't delete.
2. **`order_one` interleave trap (L1002–1015).** It is a KEEP `order_*` lemma physically nested inside the DELETE-bound `principal` cluster (L958–1084). Do not sweep it out with the cluster; relocate to L644–753 or leave in place. No dependency on `principal`.
3. **Route-C is two-faced.** DEAD = RR-degree/ℙ¹ chain in `WeilDivisor.lean` §3–§6 (`degree`, `principal_degree_zero`, `positivePart`) → its only target was the deleted `genusZero_curve_iso_P1`; safe to carve. LIVE = coherent-χ / Hilbert-polynomial / Snapper endgame in `Picard/QuotScheme.lean` §1 + `Picard_FGAPicRepresentability.tex` gating the 5 headline Quot/FGA sorries → KEEP. Never conflate; roadmap.md labels only the dead leg "Route C" (L72/77), the live leg is unlabeled at L62/75.
4. **CodimOneExtension consumer-surface contradiction.** weildivisor-carve scout says CodimOneExtension uses "ONLY `Scheme.PrimeDivisor`(.point)"; lean-comments scout says "`PrimeDivisor`/`RationalMap.order`". Moot for the keep decision (all order substrate is kept anyway) but **grep both `.PrimeDivisor` AND `.order`/`RationalMap.order`** across the repo before trimming any order lemma.
5. **roadmap.md:72 disposition contradiction.** lean-comments = "KEEP whole (good-current-doc)"; roadmap-md = "trim the `standalone RiemannRoch extraction is now obsolete` clause". roadmap-md is more precise (no such extraction exists). Resolution: trim clause + change ×2→×1 post-carve.
6. **roadmap.md:112–113 / :120 AJC-vs-Albanese contradiction.** lean-comments flagged both as stale-dead (Genus0BaseObjects deleted); roadmap-md correctly identifies them as the **Albanese subproject** section where `SubProjects/Albanese/.../Genus0BaseObjects/{BareScheme,Points}.lean` genuinely exist. Trust roadmap-md: KEEP L120 (verify ×1 counts), KEEP L112–113 with a "parent no longer carries it" caveat. Have Horizon eyeball which section header L120 sits under before editing.
7. **No active genus-branching CODE anywhere.** Confirmed: no `dite`/`if` on `genus`; the only `dite` token is a comment at `AbelJacobi.lean:16` stating it was removed. Witness is uniform. Carve is prose/dead-math only — no control-flow risk.
8. **Broken file pointers being removed:** `genusZero_curve_iso_P1`, `AbelianVarietyRigidity.lean`, `RationalCurveIso.lean` (all deleted); blueprint `RiemannRoch_RRFormula/OcOfD/RationalIsoP1.tex` (never existed as source); `STRATEGY.md`/`.archon/` (never existed). Grep should return zero after carve.
9. **Stale generated HTML** must be regenerated, never hand-edited (§1.F).

---

## 4. Verification checklist (post-carve)

1. **Build the affected cone (kernel-faithful):** `lake build` for `AlgebraicJacobian.RiemannRoch.WeilDivisor` → `AlgebraicJacobian.Albanese.CodimOneExtension` → the `AlgebraicJacobian` aggregator (import L93). Must compile.
2. **Consumer grep (run BEFORE finalizing deletes):** `grep -rn '\.PrimeDivisor' && grep -rn 'RationalMap\.order\|\.order' && grep -rn 'ofClosedPoint\|\bdegree\b\|principal\|positivePart\|LinearEquivalence' AlgebraicJacobian/` — confirm the only surviving external consumer is `CodimOneExtension` (PrimeDivisor, +order if used); zero for the deleted decls.
3. **Dead-symbol grep (expect empty):** `genusZero_curve_iso_P1`, `degree_positivePart_principal_eq_finrank`, `RationalCurveIso`, `RiemannRoch_RRFormula`, `RiemannRoch_OcOfD`, `RiemannRoch_RationalIsoP1`, `STRATEGY.md`, `AbelianVarietyRigidity` (as a Lean decl).
4. **`order_one` survival:** confirm `RationalMap.order_one` still present + compiling (trap #2).
5. **Sorry count:** `grep -n 'sorry' AlgebraicJacobian/RiemannRoch/WeilDivisor.lean` → exactly **1** (L830 region only). Update `roadmap.md:72` to ×1 and re-verify. `#print axioms` on kept substrate should show no new axioms.
6. **Blueprint:** rebuild `web/` from `content.tex` (plasTeX / leanblueprint); confirm the 7 genus-0/Route-C orphan HTML + stale BareScheme TOC entries are gone. Optionally fix the 2 dangling `\uses` in `Picard_GlueDescent.tex`, then `horizon leandag` / `leanblueprint checkdecls` → expect dangling:0.
7. **leandag refresh:** confirm node graph still has zero `genus0`/`genusZero`/`routeC`/`RationalCurveIso`/`RRFormula` nodes and the single LIVE RR node source remains `RiemannRoch_WeilDivisor.tex`.

---
_Generated by Ground run 0011 via a 5-scout read-only workflow (blueprint-tex, lean-comments, roadmap-md, weildivisor-carve, dag-orphans). Line numbers are a snapshot; Horizon should re-anchor before editing._
