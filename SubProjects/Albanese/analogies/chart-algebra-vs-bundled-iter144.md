# Analogy: iter-144 mandatory chart-algebra-vs-bundled re-evaluation gate for piece (iii)

## Slug

chart-algebra-iter144

## Iteration

144

## Question

Given (a) iter-140 chart-algebra rigidity verdict HYBRID (LOC envelope
~450–900 LOC bundled vs ~980–1970 LOC full in-tree), (b) iter-141
scheme-Frobenius scoping verdict HYBRID-pivot-does-NOT-fire (LOC
midpoint ~1025; in-tree sustainable below 2000 LOC pivot threshold),
(c) iter-143 piece (i.b) Step 2 d_app PARTIAL with type-coercion
(`Eq.mpr` / `eqToHom` between pushforward composites) as the reported
obstacle (NOT recipe-level), (d) iter-144 user-hint M3 Route A
commitment dropping "off-loop PR lane" framing, (e) piece (i.b) Main
`mulRight_globalises_cotangent` body not yet attempted, **should the
iter-144+ piece (iii) scheme-Frobenius commitment switch to the
chart-algebra alternative, OR is the bundled in-tree scheme-Frobenius
path still the right choice?**

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:573–700` —
  `basechange_along_proj_two_inv_derivation`. d_map closed iter-142
  (L664–700); d_app PARTIAL iter-143 (L602–663) with `have hw`
  Step 3.a closure + 60 LOC scope-disclosure comments; residual sorry
  at L663.
- `AlgebraicJacobian/Cotangent/GrpObj.lean:745–751` —
  `basechange_along_proj_two_inv_app_isIso` (iter-143 NEW refactor
  extraction). Per-open IsIso obligation; body `sorry`; Route (b'2)
  items 2–4 closure path (~195–365 LOC bundled per
  `analogies/isiso-basechange-along-proj-two-inv.md`).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:890–901` —
  `mulRight_globalises_cotangent` (piece (i.b) Main). Body `sorry`,
  iter-145+ target after d_app + IsIso both close.
- `AlgebraicJacobian/Rigidity.lean:51` — only project mention of
  scheme-level absolute Frobenius (prose paragraph; no formal
  declaration).
- `STRATEGY.md` § Iter-142+ scheduled obligations L601–L612 — the
  iter-144 mandatory re-evaluation gate this analogist call answers.

## Read-input persistent files

- `analogies/direct-chart-algebra-rigidity-ib-ic.md` (iter-140) —
  HYBRID with chart-algebra pivot deferred as conditional fallback;
  CONTINUE_BUNDLED criterion ≥2 sub-sorries closed iter-140.
- `analogies/scheme-frobenius-piece-iii-scoping.md` (iter-141) — HYBRID
  with in-tree-build sustainable + chart-algebra LOC-dominant + named-
  gap alternative below pivot threshold; "Strongest recommendation:
  pursue option (2) chart-algebra unless (a) piece (i.b) Step 2 sub-
  sorry closure under bundled completes on iter-140 with ≥2 sub-sorries
  closed".
- `analogies/d-app-d-map-recipe-shape.md` (iter-141) — Decision 2
  NEEDS_MATHLIB_GAP_FILL on the d_app categorical chase.
- `analogies/isiso-basechange-along-proj-two-inv.md` (iter-139) —
  Route (b'2) verdict ~195–365 LOC.

## Mathlib infrastructure snapshot (`b80f227`, verified iter-144)

| Name | Location | Role |
|---|---|---|
| `RingHom.iterateFrobenius_comm` | `Mathlib.Algebra.CharP.Frobenius` | **Load-bearing for chart-algebra route on piece (iii)**: verified iter-144 via `lean_loogle`. Witness for "for each chart W of A, `f^# ∘ iterateFrobenius_{Γ(W), p, n} = iterateFrobenius_{Γ(f^{-1}W), p, n} ∘ f^#`" — gives chart-by-chart Frobenius iteration as a direct ring-level RingHom-commutation, no scheme-level lift needed |
| `Algebra.IsStandardSmooth.free_kaehlerDifferential` | `Mathlib.RingTheory.Smooth.StandardSmoothCotangent` | Per-chart Kähler free of rank n; consumed by chart-algebra (β) helper |
| `PresheafedSpace.comp_c_app` | `Mathlib/Geometry/RingedSpace/PresheafedSpace.lean:176` | Load-bearing for piece (iii) sub-piece 2 (`F_X |_U = F_U`) restriction compatibility AND for d_app Step 3.b lift — **same shape as the iter-143 d_app blocker** |
| `TopCat.Presheaf.Pushforward.comp_eq` | (definitional rfl) | `(f ≫ g) _* ℱ = g _* (f _* ℱ)` — **the iter-143 d_app type-coercion source**: bundled (i.b) Step 2 d_app needs this to identify `pushforward (fst).left.base ∘ pushforward G.hom.base = pushforward (G ⊗ G).hom.base` modulo `(fst).w` (propositional, not definitional) |
| `pullbackSpecIso` + `_hom_fst`/`_inv_fst` | `Mathlib.AlgebraicGeometry.Pullbacks` | Chart-algebra (α) helper foundation: ring-level `Algebra.IsPushout` from affine product, no pushforward composites |
| `Scheme.absoluteFrobenius` | **ABSENT** in `b80f227` | Bundled piece (iii) PHANTOM (~800–1500 LOC) |

The iter-143 d_app type-coercion obstacle is **structurally
reproducible** in piece (iii) sub-piece 2 (restriction compatibility):
both require `Pushforward.comp_eq` (definitional rfl) chained with
propositional-only `≫ = ` to bridge composite Hom equalities. The
chart-algebra route uses `pullbackSpecIso` + ring-level
`iterateFrobenius` instead, **completely avoiding pushforward-
composite Eq.mpr/eqToHom transport**.

## Decisions identified

### Decision 1: Does iter-143 d_app type-coercion foreshadow piece (iii) scheme-Frobenius type-coercion cost?

The iter-143 d_app obstacle is the chain:

  `(fst).left ≫ G.hom = (snd).left ≫ G.hom`   (propositional, via `(fst).w` + `(snd).w`)
   → `Pushforward.comp_eq` for both sides (definitional rfl)
   → `Adjunction.homEquiv_naturality_right_symm` transpose (modulo type alignment via `eqToHom`)
   → equating two natural transformations with different
     codomain pushforward parametrisations.

The iter-143 prover task-result is explicit: "the recipe is correct;
the difficulty is at the **Lean-level type-coercion**, NOT at the
recipe level. This is a **tooling-level obstacle, not a mathematical
one**."

**Piece (iii) scheme-Frobenius sub-piece-by-sub-piece foreshadow audit:**

- **Sub-piece 1** (`Scheme.absoluteFrobenius` definition, ~150–300 LOC):
  builds an `LRS.Hom X X` from `base = 𝟙` + sheaf-NatTrans (per-open
  `frobenius`) + stalk-locality. **Single Hom on X**, NOT a
  composition of two scheme morphisms. **No pushforward-composite
  obstacle**. Sub-piece 1 does NOT foreshadow the iter-143 obstacle.

- **Sub-piece 2** (restriction compatibility `F_X |_U = F_U`,
  ~80–150 LOC): commuting square `U.ι ≫ F_X = F_U ≫ U.ι` via
  `Scheme.Hom.ext` + per-open `frobenius_comm`. **Same shape** as
  iter-143 d_app pushforward-composite chase: one side is `U.ι ≫ F_X`
  (composition); proof goes through `comp_c_app` + naturality. **Sub-
  piece 2 DOES foreshadow** the iter-143 obstacle.

  However, sub-piece 2's commuting square is **easier**: `U.ι` is an
  open inclusion (much simpler than the binary-product `(fst).left`/
  `(snd).left` chase; `U.ι` has a controlled `(Opens.map U.ι.base)`-
  preimage with definitional `IsOpenImmersion` API). The iter-141
  ~80–150 LOC estimate is plausible **modulo** a ~20–40% Eq.mpr/
  eqToHom tax that compounds (per iter-143 evidence). Effective range
  ~96–210 LOC.

- **Sub-piece 3** (iterate `iterateFrobenius_X`, ~50–120 LOC): iterate
  of a single endo-Hom, no composite. **No foreshadow**.

- **Sub-piece 4** (consumer "df=0 ⇒ f factors through F_C^n",
  ~400–800 LOC): dominated by **local-form "char-p ring + df=0 ⇒
  r ∈ R^p"** (~200–400 LOC) and uniform-n glue + factor-through
  wrapper. Mathematical content is ring-side (smoothness +
  `KaehlerDifferential.D` kernel extraction) — **structurally different
  obstacle** from iter-143 d_app's pushforward-composite chase. The
  Eq.mpr tax for sub-piece 4 is bounded by ring-level constructions.
  **No structural foreshadow** from iter-143; sub-piece 4's cost is
  recipe-level.

**Aggregate audit**: iter-143 obstacle foreshadows ~+~20–40 LOC tax on
sub-piece 2 specifically (within the ~80–150 LOC envelope, manageable).
Sub-pieces 1+3+4 are NOT structurally similar. **The iter-141 LOC
estimate ~680–1370 LOC for the full piece (iii) build remains
credible** with mild upward pressure on sub-piece 2 only.

**Verdict on Decision 1**: PROCEED. iter-143 obstacle is **localized**
to scheme-level pushforward-composite chases; sub-piece 2 inherits the
tax (within envelope); sub-pieces 1+3+4 do not. Bundled piece (iii)
~800–1500 LOC remains credible.

### Decision 2: Under chart-algebra pivot, does piece (i.b) Step 2 still need its own chart-side closure (the d_app analog)?

Per `analogies/direct-chart-algebra-rigidity-ib-ic.md` (iter-140)
Decision 2: chart-algebra rigidity does NOT cleanly skip (i.b) — it
restructures (i.b)'s content into chart-level helpers:

- (α) chart-level `Algebra.IsPushout` helper (~80–150 LOC) via
  `pullbackSpecIso`.
- (β) per-chart translation-invariance argument (~150–300 LOC) via
  ring-level `KaehlerDifferential` API.

**Critical structural observation iter-144**: the chart-algebra route's
(α)+(β) work is **purely ring-level** — no
`PresheafOfModules.pullback`, no
`pullbackPushforwardAdjunction.homEquiv.symm`, no
`Pushforward.comp_eq` propositional-vs-definitional transport. The
chart-algebra route consumes Mathlib's ring-side `Algebra.IsPushout` +
`KaehlerDifferential.tensorKaehlerEquiv` + ring-level
`iterateFrobenius` directly.

**The iter-143 d_app type-coercion obstacle is STRUCTURALLY AVOIDED
by chart-algebra.** The chart-level (β) per-chart Kähler-derivation
construction is the chart-level analog of bundled d_app, but it does
not face the pushforward-composite Eq.mpr tax. The iter-142 d_map
closure technique (3-step ALIGN_WITH_MATHLIB chase via
`pushforward_obj_map_apply'` + `NatTrans.naturality_apply` +
`relativeDifferentials'_map_d`) does NOT transfer cleanly — but its
**pattern** does (per-chart Kähler-derivation laws via Mathlib's
`Derivation` API + `KaehlerDifferential.D` are ring-level analogs).

**Sunk-cost audit (iter-144 under chart-algebra pivot):**

| (i.b)-side asset | Survives chart-algebra pivot? | LOC |
|---|---|---|
| `shearMulRight` Step 1 (L350–L395) | NO — not needed under chart-algebra | ~45 LOC |
| `relativeDifferentialsPresheaf_basechange_along_proj_two` Step 2 + d_map closure | NO — replaced by chart-level (β) helper | ~250 LOC body + d_map technique |
| `basechange_along_proj_two_inv_app_isIso` (IsIso, NEW iter-143) | NO — Route (b'2) supersedes Mathlib-aligned to chart-level | ~25 LOC scaffold |
| `relativeDifferentialsPresheaf_restrict_along_identity_section` Step 3 | NO — section-restriction-along-η[G] not needed at chart level | ~50 LOC |
| `isIso_of_app_iso_module` helper | NO — Mathlib-PR-candidate side-product; survives but is unused | ~10 LOC |
| `mulRight_globalises_cotangent` Main scaffold | NO — sheaf-level RHS not the chart-algebra target | ~15 LOC |
| `schemeHomRingCompatibility` adjunction-transpose helper | NO | ~3 LOC |
| Auxiliary `section_snd_eq_identity_struct` lemma | NO | ~10 LOC |
| Long docstrings + scope-disclosure comments | NO | ~150 LOC |
| **Total sunk-cost on (i.b)-side bundled** | | **~558 LOC** |

Plus blueprint `RigidityKbar.tex` § Piece (i.b) Step 2 prose (~285 LOC
iter-143 expansion + earlier ~400 LOC) becomes legacy. Plus iter-138/
139/140/141/142/143 mathlib-analogist consults (5 of 5 mechanically
reached) become legacy reasoning capital.

**The d_map technique-advance does NOT transfer cleanly to chart-
algebra** — it's a sheaf-NatTrans naturality chase, not a ring-level
construction. The chart-algebra (β) helper uses different Mathlib API
(`Algebra.IsPushout` + `KaehlerDifferential.D` directly).

**Verdict on Decision 2**: chart-algebra **structurally avoids** the
iter-143 d_app type-coercion obstacle (~+20–40 LOC tax avoided), but
**discards ~558 LOC of bundled (i.b)-side investment** (mostly
mathematical scaffolding, not technique). The d_map technique-advance
does NOT transfer.

### Decision 3: Has iter-143 evidence changed the named-gap-sorry alternative attractiveness?

Per iter-141 verdict: named-gap-sorry sits at ~300–600 LOC modulo one
residual named-gap on piece (iii) consumer (the "df=0 ⇒ f factors
through F_C^n" theorem). The iter-141 LOC-pivot verdict ("not
elevated") was correct on its terms.

**What iter-143 changed:**

- Bundled (i.b) Step 2 has 3 consecutive PARTIAL iters (iter-140/142/
  143) on a 3-sub-sorry lane; cumulative strict-count closure = 1 of 3
  (d_map). The iter-140 chart-algebra analogist's CONTINUE_BUNDLED
  criterion (≥2 sub-sorries closed iter-140) is **NOT MET** — iter-140
  closed 0 sub-sorries. Even relaxed to cumulative iter-140/142/143,
  ≥2 not met.
- iter-143 obstacle is tooling-level (not recipe-level). The recipe
  is correct.

**What iter-144 user-hint changed:**

- Dropping "off-loop PR lane" framing for in-tree work means the
  bundled-path "Mathlib-PR contribution utility" (sub-pieces 1+3+
  `mulRight_globalises_cotangent` as named API; `omega_free` /
  `omega_rank_eq_dim` as named API) loses **bonus weight** as a
  project deliverable. In-tree material is project material; PR
  extraction is optional downstream.
- This **does NOT elevate named-gap-sorry**: the zero-sorry
  PROVISIONAL end-state commitment remains. The iter-144 user-hint
  reframing affects bundled-vs-chart-algebra weighting, not
  bundled-vs-named-gap weighting.
- The named-gap-sorry alternative is **strictly worse than chart-
  algebra** under iter-144 framing: chart-algebra preserves zero-sorry
  PROVISIONAL end-state at ~450–900 LOC, while named-gap-sorry leaves
  one residual named gap at ~300–600 LOC. Δ ~150–300 LOC for the
  zero-sorry guarantee is a defensible cost.

**Verdict on Decision 3**: iter-143 evidence does NOT elevate
named-gap-sorry. Chart-algebra dominates named-gap-sorry under iter-144
user-hint framing (~150–300 LOC delta buys zero-sorry PROVISIONAL
end-state).

### Decision 4: Re-weighed iter-144 pivot decision

The iter-140 chart-algebra rigidity analogist's "Strongest
recommendation: pursue option (2) chart-algebra unless ≥2 sub-sorries
closed iter-140" criterion was **not met** (iter-140 closed 0
sub-sorries; cumulative iter-140/142/143 closed 1 of 3).

The iter-141 strategy-critic deferred the pivot decision to iter-144
on grounds:
- (i) iter-138 sunk cost on Route (b) — partially recouped (d_map
  closed iter-142 substantively; ~110 LOC), but ~558 LOC bundled (i.b)-
  side total remains.
- (ii) `omega_free` / `omega_rank_eq_dim` / `mulRight_globalises_cotangent`
  / scheme-Frobenius Mathlib-PR utility — **dropped under iter-144
  user-hint reframing** ("in-tree project material; PR extraction is
  optional downstream").
- (iii) in-tree scheme-Frobenius sustainable below 2000 LOC — **still
  holds** (iter-141 verdict midpoint ~1025 LOC).
- (iv) chart-algebra also under 2000 LOC; choice is strategic — **still
  holds**, but the iter-144 user-hint reframing removes one of the
  three grounds favoring bundled.

**Honest re-weighed comparison (iter-144):**

| Axis | Bundled (continue) | Chart-algebra (pivot iter-144) |
|---|---|---|
| iter-140 CONTINUE_BUNDLED criterion (≥2 sub-sorries closed iter-140) | NOT MET (iter-140 closed 0; cumulative iter-140/142/143 closed 1 of 3) | criterion auto-recommends chart-algebra |
| iter-143 obstacle (pushforward-composite Eq.mpr/eqToHom) | encountered, plausibly closeable iter-144 per iter-143 review Arm A | structurally avoided (ring-level) |
| Total remaining LOC from iter-144 | ~1280–2945 LOC (i.b residual + i.c + ii + iii sub-pieces 1–4) | ~450–900 LOC (chart-algebra absorbed into piece (ii)) |
| Net LOC saving under chart-algebra | — | **~830–2045 LOC midpoint ~1438 LOC** |
| Mathlib-PR contribution bonus | strong (sub-pieces 1+3 scheme-Frobenius + omega_free + mulRight) | weak (chart-level helpers are project-internal) |
| User-hint reframing effect on PR bonus | **bonus weight DROPPED iter-144** | no change (chart-algebra never had PR bonus) |
| Sunk-cost on (i.b)-side bundled | preserved | ~558 LOC discarded |
| d_map technique-advance transfer | preserved (iter-142 close, technique-bearing) | does NOT transfer cleanly (different API) |
| Piece (ii) PIN-path-(b) envelope | 300–600 LOC (independent of pivot) | 600–1050 LOC (inflated to absorb chart-algebra) |
| Strategy/blueprint restructure cost | none | ~50–100 LOC one-off STRATEGY.md + RigidityKbar.tex rewrites |
| iter-141 LOC-pivot threshold (2000 LOC) | not triggered | not triggered |
| iter-145+ breakeven counter projection (3 entering iter-144) | counter rolls; close iter-144 d_app → counter 3 → 2 | counter discharge under pivot |
| Tooling-tax compounding signal (iter-143) | mild positive for bundled (sub-piece 2 only) | mild positive for chart-algebra (avoids pushforward-composite work entirely) |

**Honest tally**: chart-algebra dominates on net LOC (~1438 LOC midpoint
saving), avoids the iter-143 obstacle structurally, and the iter-144
user-hint reframing has dropped one of bundled's three strategic
grounds. Bundled retains: sunk-cost preservation (~558 LOC) + d_map
technique-advance + in-tree-build-sustainable-below-2000 LOC + iter-141
strategy-critic momentum.

**The honest verdict at iter-144 is a "should-pivot-now" finding,
mitigated by sunk-cost capitalisation considerations.** The strongest
single argument is the chart-algebra route's net LOC saving (~830–
2045 LOC) under the iter-144 user-hint reframing that dropped PR-bonus
weight.

**Verdict on Decision 4**: PIVOT TO CHART-ALGEBRA is the LOC-honest
iter-144 verdict; sunk-cost considerations argue for a **HYBRID
EXECUTION** that preserves iter-144 d_app prover lane (small-cost
closure attempt; ~40–80 LOC; counter discharge candidate) while
**committing the iter-145+ trajectory to chart-algebra** at the
STRATEGY.md level.

### Decision 5: Execution shape for HYBRID-EXECUTION verdict

**Iter-144 prover lane**: continue bundled d_app close attempt per
iter-143 review Arm A (~40–80 LOC; small scope; the iter-143 prover's
recipe Step 3 (3.a–3.d) decomposition is correct per its own task-
result Section "Mathematical proof").

- **If iter-144 d_app closes substantively (strict-count -1)**:
  consecutive-PARTIAL counter 3 → 2; iter-145 STRATEGY.md edit lands
  the chart-algebra commitment for iter-145+ piece (iii)+(i.c)+piece
  (ii) restructure. The iter-144 d_app close is the **last bundled
  technique-advance**; preserves d_map+d_app as Mathlib-PR-candidates
  off-loop (under iter-144 user-hint, NOT a project deliverable).
- **If iter-144 d_app PARTIAL again (counter 3 → 4 of 5 breakeven)**:
  iter-145 plan agent fires the chart-algebra commitment without
  iter-144 small-cost capitalisation; STRATEGY.md edit lands;
  bundled (i.b) Step 2 lane is suspended (sunk-cost ~558 LOC fully
  capitalised).
- **If iter-144 d_app FAIL + new pushforward-composite obstacle**:
  iter-145 plan agent fires chart-algebra commitment urgently;
  iter-141 verdict no longer holds (in-tree-build-sustainable
  becomes uncertain).

**Iter-145+ piece (i.c)+(i.b) Main schedule under chart-algebra
pivot**:
- piece (i.c.1/i.c.2/i.c.3) **descoped** (chart-localisation +
  freeness/rank package no longer needed; replaced by chart-algebra
  (α) + (β) helpers absorbed into piece (ii)).
- piece (i.b) Main `mulRight_globalises_cotangent` **descoped**
  (sheaf-level RHS no longer needed; chart-algebra route uses
  ring-level translation-invariance directly).
- piece (ii) PIN-path-(b) **inflated** from 300–600 LOC to 600–1050 LOC
  to absorb chart-algebra (α) chart-level `Algebra.IsPushout` +
  (β) per-chart translation-invariance.
- piece (iii) **ELIMINATED** as project obligation; scheme-level
  absolute Frobenius PHANTOM (~800–1500 LOC) descoped. Chart-level
  Frobenius via `RingHom.iterateFrobenius_comm` on each chart W
  delivers `f^# ∘ iterateFrobenius_{Γ(W), p, n} =
  iterateFrobenius_{Γ(f^{-1}W), p, n} ∘ f^#`, feeding the per-chart
  rigidity argument directly. **Iter-147+ scheme-Frobenius scoping
  consults retired**.

**Iter-150 trigger preservation**: iter-142 STRATEGY.md Edit 4's
M3 RelativeSpec in-loop scaffold re-evaluation trigger (925-LOC dual
threshold) preserved — chart-algebra pivot reduces M2.body-pile to
~450–900 LOC, well under 925; trigger fires later or not at all.

**Iter-144 STRATEGY.md edits required**:
1. M2.body-pile § rewrite to drop piece (i.c) sub-pieces 1/2/3 and
   piece (iii) scheme-Frobenius, replace with chart-algebra piece (ii)
   inflation.
2. § Iter-142+ scheduled obligations rewrite to retire the iter-144
   mandatory chart-algebra-vs-bundled gate (this analogist call
   discharged the gate; PIVOT committed).
3. § End-state PROVISIONAL framing relax: piece (iii) PHANTOM build
   conditional descoped; zero-sorry PROVISIONAL end-state preserved
   under chart-algebra route (no residual named gap).

**Iter-144 blueprint edits required**:
1. `RigidityKbar.tex` § Piece (i) prose rewrite to chart-algebra
   structure (~50–100 LOC).
2. `RigidityKbar.tex` § Piece (iii) Frobenius prose descope (~30 LOC
   becomes legacy/historical note).
3. `RigidityKbar.tex` § shared_pile prose update.

**Verdict on Decision 5**: HYBRID EXECUTION is the iter-144
implementation shape: bundled d_app prover lane fires iter-144 (small
cost; technique capitalisation if successful), chart-algebra
commitment lands iter-144 STRATEGY.md regardless of d_app outcome (the
LOC-honest finding does not depend on iter-144 d_app close).

## Cross-cutting LOC tally (iter-144 re-weighed)

| Pile component | Bundled iter-144→close | Chart-algebra iter-144 pivot |
|---|---|---|
| Iter-144 d_app close attempt | ~40–80 LOC body | ~40–80 LOC (still useful: technique capitalisation) |
| Iter-145+ IsIso Route (b'2) | ~195–365 LOC | 0 LOC (descoped) |
| Iter-145+ `mulRight_globalises_cotangent` Main | ~15 LOC + bundled-route closure | 0 LOC (descoped) |
| Iter-146+ piece (i.c.1/i.c.2/i.c.3) | ~200–500 LOC | 0 LOC (chart-algebra absorbs into piece (ii)) |
| Iter-145+ piece (ii) PIN-path-(b) | 300–600 LOC | 600–1050 LOC (inflated by 300–450 LOC chart-algebra upstream) |
| Iter-147+ piece (iii) sub-pieces 1+2+3+4 | 680–1370 LOC | 0 LOC (scheme-Frobenius PHANTOM descoped) |
| Sunk-cost on iter-138→143 (i.b)-side bundled | preserved | ~558 LOC capitalised |
| Strategy/blueprint restructure | none | ~50–100 LOC |
| **Total iter-144→close project obligation** | **~1430–3070 LOC** | **~690–1230 LOC** |
| **Net chart-algebra saving** | — | **~740–1840 LOC midpoint ~1290 LOC** |

The net saving is **~1290 LOC at midpoint**, well above the iter-141
verdict's ~480–1070 LOC chart-algebra-vs-bundled saving (revised
upward by ~258 LOC due to iter-143/144 sunk-cost capitalisation +
piece (iii) sub-piece 1 + 2 + 3 retirement under chart-algebra route).

## Risk tally (iter-144 re-weighed)

| Risk | Bundled (continue) | Chart-algebra (pivot) |
|---|---|---|
| Iter-143 obstacle reproducibility | mild on sub-piece 2 (~+20–40 LOC tax) | **AVOIDED** structurally (ring-level) |
| Iter-145+ piece (i.b) Main closure tractability | UNKNOWN; iter-144 d_app outcome informs | UNTOUCHED (descoped) |
| Mathlib-PR contribution shipping | strong (3+ named PR-shape lemmas) | weak (chart-algebra helpers are project-internal) — **NO LONGER A PROJECT DELIVERABLE per iter-144 user-hint** |
| Sunk-cost discard | preserved | ~558 LOC capitalised + d_map technique not transferring cleanly + 5 of 5 analogist consults' reasoning capital |
| Piece (ii) scope inflation | unchanged (300–600 LOC) | INFLATED to 600–1050 LOC (CHURNING risk on a larger lane) |
| Blueprint restructure cost | none | one-off ~50–100 LOC |
| Strategy-critic momentum preservation | preserved (iter-141 verdict carried) | partial discontinuity (iter-141 strategy-critic override on chart-algebra reverted; needs iter-144 strategy-critic adoption) |
| Iter-148+ piece (iv) Serre duality (deferred named gap; unchanged either path) | named gap | named gap |
| Iter-144 d_app outcome dependency | high (PARTIAL/FAIL forces re-route; PASS extends bundled momentum) | LOW (verdict independent of d_app outcome) |

## Verdict

**HYBRID EXECUTION — PIVOT TO CHART-ALGEBRA committed iter-144
STRATEGY.md; iter-144 d_app bundled prover lane fires as last
technique-capitalisation attempt; iter-145+ trajectory restructures
to chart-algebra route.**

**Strict directive-shape verdict**: **PIVOT TO CHART-ALGEBRA** with
HYBRID EXECUTION envelope (sunk-cost capitalisation iter-144).

### LOC delta and iter delta:

- **LOC saving**: ~740–1840 LOC midpoint ~1290 LOC, vs iter-141 ~480–
  1070 LOC envelope (revised upward by sunk-cost capitalisation +
  scheme-Frobenius sub-pieces 1+2+3 retirement).
- **Iter saving**: ~7–13 iter (piece (iii) sub-pieces 1+2+3 retire
  3–6 iter; sub-piece 4 retires 2–4 iter; piece (i.c) retires
  2–3 iter; offset by piece (ii) +1–2 iter inflation absorbing
  chart-algebra upstream).
- **Risk-adjusted iter saving**: ~5–10 iter at midpoint (the iter-141
  verdict's "in-tree sustainable" assessment holds; chart-algebra
  saves but doesn't slash an unsustainable-trajectory project).

### Impact on iter-143 d_app PARTIAL on Route 1:

- Chart-algebra structurally **avoids** the iter-143 d_app type-
  coercion obstacle (pushforward-composite Eq.mpr/eqToHom transport).
- Iter-144 d_app close attempt **still recommended** (technique
  capitalisation; ~40–80 LOC scope; small cost; counter discharge
  candidate) **but its closure is no longer load-bearing** for the
  iter-145+ trajectory under chart-algebra pivot.
- The d_map technique-advance (iter-142 close) **does NOT transfer
  cleanly to chart-algebra** — it's a sheaf-NatTrans naturality chase,
  not a ring-level construction.

### Watch criteria for iter-145+ under PIVOT:

- **Iter-145 plan agent**: confirm STRATEGY.md edits land; absorb
  chart-algebra pivot into M2.body-pile.
- **Iter-145 blueprint-writer**: `RigidityKbar.tex` restructure to
  chart-algebra (~50–100 LOC of prose churn).
- **Iter-146+ piece (ii) PIN-path-(b) prover lane**: scope envelope
  600–1050 LOC; if mid-iter `lean_diagnostic_messages` shows piece
  (ii) absorbing chart-algebra upstream is hitting > 1050 LOC, fire a
  mid-iter mathlib-analogist on the inflation breakdown.
- **Iter-148+ piece (iv) Serre duality**: unchanged (deferred named
  gap).

## Severity

**high-stakes.** This verdict re-shapes the iter-144+ M2 critical-
path trajectory by ~5–10 iter and ~1290 LOC at midpoint. The PIVOT
commitment is binding through iter-145+ strategy lock-in; reverting
post-iter-145 would compound sunk-cost (chart-algebra (α)+(β) work
becomes its own sunk-cost ~230–450 LOC if abandoned). The iter-141
strategy-critic momentum is partially reversed; iter-144 strategy-
critic re-verification is recommended (the iter-141 verdict's "below
pivot threshold, choice is strategic" framing carries forward; the
iter-144 user-hint reframing tilts the strategic balance toward
chart-algebra).

## Per-decision summary

| Decision | Verdict |
|---|---|
| 1. iter-143 d_app type-coercion foreshadow piece (iii) tooling tax | PROCEED — sub-piece 2 only (~+20–40 LOC); piece (iii) ~680–1370 LOC remains credible |
| 2. Chart-algebra restructures piece (i.b) Step 2 d_app to chart-side | DIVERGE_INTENTIONALLY — iter-143 obstacle structurally avoided; ~558 LOC sunk-cost |
| 3. iter-143 evidence on named-gap-sorry attractiveness | PROCEED — named-gap-sorry not elevated; chart-algebra dominates |
| 4. Iter-144 re-weighed pivot decision | **PIVOT_TO_CHART_ALGEBRA** with HYBRID EXECUTION envelope |
| 5. Execution shape | HYBRID: iter-144 d_app bundled lane fires as last technique-capitalisation; iter-145+ chart-algebra committed |

## Recommendation

Iter-144 plan agent should:

1. **Land 3 substantive STRATEGY.md edits** committing chart-algebra
   pivot:
   - M2.body-pile § rewrite (drop piece (i.c) + piece (iii); inflate
     piece (ii) to 600–1050 LOC absorbing chart-algebra upstream).
   - § Iter-142+ scheduled obligations § retire the iter-144 mandatory
     chart-algebra-vs-bundled gate (discharged this analogist call;
     PIVOT committed).
   - § End-state PROVISIONAL relax: piece (iii) PHANTOM build
     descoped; zero-sorry PROVISIONAL end-state preserved under
     chart-algebra route (no residual named gap).

2. **Continue iter-144 d_app bundled prover lane** per iter-143 review
   Arm A: wire `have hw` through to Step 3.b lift via
   `PresheafedSpace.comp_c_app`; extract Step 3.b/c into a named
   helper lemma (per iter-143 lean-vs-blueprint-checker MAJOR + iter-
   143 STRATEGY.md Edit 1 sorry-must-be-named-declaration); attempt
   d_app close ~40–80 LOC body. **Outcome does NOT alter the chart-
   algebra pivot commitment** — purely technique capitalisation.

3. **Dispatch iter-144 mandatory blueprint-writer** for
   `RigidityKbar.tex` chart-algebra restructure (~50–100 LOC prose
   churn, one-off).

4. **Dispatch iter-144 mandatory strategy-critic re-verification** to
   confirm the iter-141 strategy-critic override on chart-algebra is
   reversed iter-144 (vs preserved), and to verify the STRATEGY.md
   edits' internal consistency.

5. **Off-loop**: scheme-level `absoluteFrobenius` retains optional
   downstream Mathlib-PR utility (sub-pieces 1+3 at ~200–420 LOC are
   the clean Stacks Tag 0CC4 construction; sub-piece 4 unilaterally
   descoped). **Not a project deliverable** under iter-144 user-hint
   reframing.

The PIVOT is the **LOC-honest iter-144 finding**. The iter-141
strategy-critic's deferral to iter-144 has discharged at this analogist
call; the iter-141 conditional pivot trigger (iter-140 ≥2 sub-sorries
not closed) **mechanically fires**.

## Overall verdict (one sentence)

**PIVOT TO CHART-ALGEBRA committed iter-144 STRATEGY.md** with HYBRID
EXECUTION (iter-144 d_app bundled lane fires as last sunk-cost
capitalisation; iter-145+ piece (i.c)+(i.b) Main descoped, piece (ii)
PIN-path-(b) inflated to absorb chart-algebra upstream at 600–1050
LOC, piece (iii) scheme-Frobenius PHANTOM descoped); net saving ~740–
1840 LOC midpoint ~1290 LOC and ~5–10 iter at midpoint.
