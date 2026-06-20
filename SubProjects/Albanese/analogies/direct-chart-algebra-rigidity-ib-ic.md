# Analogy: direct chart-algebra rigidity alternative to bundled (i.b)+(i.c)

## Slug

chart-algebra-rigidity-iter140

## Iteration

140

## Question

Compare the current bundled **(i.b) `mulRight_globalises_cotangent`
sheaf-level globalisation + (i.c) chart-localisation + freeness/rank
package** (~610–1310 LOC envelope per STRATEGY.md) against a **direct
chart-algebra rigidity alternative** that:

- restricts `f^#` to each affine chart `V ⊆ A.left` (where `Γ(V)/k` is
  standard-smooth of dim `g`),
- uses Mathlib `Algebra.IsStandardSmooth.free_kaehlerDifferential`
  directly on each chart (no scheme-level `Ω_{A/k}` trivialisation),
- glues via `Scheme.Over.ext_of_eqOnOpen` (in-tree iter-125).

Verdict shape: `ALIGN_WITH_BUNDLED` | `PIVOT_TO_CHART_ALGEBRA` | `HYBRID`
| `NEEDS_MATHLIB_GAP_FILL`.

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:547–625` — iter-138 honest
  Route (b) skeleton for piece (i.b) Step 2; three concrete sub-sorries
  (`d_app` L581, `d_map` L585, `IsIso` L624).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:741–752` —
  `mulRight_globalises_cotangent` main lemma; body `sorry`, waits on
  Step 2 closure.
- `AlgebraicJacobian/Cotangent/GrpObj.lean:644–688` — iter-136-closed
  Step 3 `_restrict_along_identity_section` (in-tree, no sorry).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:96–242` — iter-132-closed
  piece (i.a) `cotangentSpaceAtIdentity` + rank lemma.
- `AlgebraicJacobian/Differentials.lean:124–142` — in-tree
  `smooth_locally_free_omega` (the per-chart free-rank-`n` Kähler
  extractor; consumed by chart-algebra alternative directly).
- `AlgebraicJacobian/Rigidity.lean:91–122` — in-tree iter-125
  `Scheme.Over.ext_of_eqOnOpen` glue.
- `analogies/cotangent-vanishing-pile-over-k.md` (iter-127) — over-k
  OK_OVER_K verdict on whole pile.
- `analogies/mulright-globalises-cotangent.md` (iter-133) — sheaf-level
  RHS verdict for (i.b); 210–440 LOC envelope (later widened to
  410–810 by iter-137/iter-138 helper layer).
- `analogies/kaehler-tensorequiv-presheafpullback.md` (iter-137) —
  5-step universal-property-at-presheaf recipe.
- `analogies/isiso-basechange-along-proj-two-inv.md` (iter-139) —
  Route (b'2) verdict for the `IsIso` sorry (~195–365 LOC).
- `analogies/differential-containConstants-alignment.md` (iter-138) —
  piece (ii) PIN-path-(b) direct `KaehlerDifferential.D` route
  (~300–600 LOC).
- `analogies/serre-duality.md` (iter-110) — piece (iv) deferred named
  gap (3000–8000 LOC honest).
- `blueprint/src/chapters/RigidityKbar.tex` § Piece (i) — structured
  prose pointer (informal); § shared_pile L60–L80; § Piece (i.b) Step 2
  L460+.

## Mathlib infrastructure snapshot (`b80f227`, verified this iter)

| Name | Location | Used by |
|---|---|---|
| `Algebra.IsStandardSmooth.free_kaehlerDifferential` | `Mathlib.RingTheory.Smooth.StandardSmoothCotangent` | both paths (chart-algebra direct; bundled via (i.c.2)) |
| `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` | `Mathlib.RingTheory.Smooth.StandardSmoothCotangent` | both paths |
| `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` | `Mathlib.AlgebraicGeometry.Morphisms.Smooth:136` | both paths (chart extractor) |
| `KaehlerDifferential.exact_mapBaseChange_map` | `Mathlib.RingTheory.Kaehler.Basic` | both paths (piece (ii) PIN-path-(b)) |
| `KaehlerDifferential.map_surjective` | `Mathlib.RingTheory.Kaehler.Basic` | both paths |
| `KaehlerDifferential.polynomialEquiv` family | `Mathlib.RingTheory.Kaehler.Polynomial` | both paths (piece (ii) char-0 reduction) |
| `KaehlerDifferential.tensorKaehlerEquiv` family | `Mathlib.RingTheory.Kaehler.TensorProduct` | both paths (algebra-side base-change-of-Ω) |
| `Polynomial.eq_C_of_derivative_eq_zero` (char-0 via `IsAddTorsionFree`) | `Mathlib.Algebra.Polynomial.Derivative` | both paths (piece (ii) polynomial-kernel reduction) |
| `iterateFrobenius` / `iterateFrobenius_def` / `_eq_pow` | `Mathlib.Algebra.CharP.Frobenius` | both paths (piece (iii) ring-level) |
| `AlgebraicGeometry.pullbackSpecIso` (+ `_hom_fst`, `_inv_fst`) | `Mathlib.AlgebraicGeometry.Pullbacks` | both paths (chart-level `Algebra.IsPushout` helper builds on top) |
| `AlgebraicGeometry.Scheme.absoluteFrobenius` / `Scheme.frobenius` | **ABSENT** in `b80f227` | both paths' piece (iii) PHANTOM scheme-lift cost |

The Mathlib roster is the same for both paths. The chart-algebra
alternative does **not** uncover a Mathlib piece that the bundled path
was missing, nor vice versa.

## Decisions identified

### Decision 1: What input does the rigidity argument actually consume from piece (i)?

The C.2.d keystone (Mumford-style cotangent-bundle route) reads:

1. `Ω_{A/k}` is free of rank `g` over `O_A` (a **sheaf-level** fact).
2. Global sections `H^0(A, Ω_{A/k})` therefore identify with the
   fibre `η_A^* Ω_{A/k}` (a **finite-dimensional** `k`-vector space of
   dim `g`).
3. For `f : C → A`, the pulled-back differential
   `df^∨ : H^0(C, f^* Ω_{A/k}) → H^0(C, Ω_{C/k})` is a `k`-linear
   map of finite-dimensional vector spaces; the target is **zero
   for genus-0 C** (piece (iv) Serre duality, deferred named gap;
   or piece (iii) Frobenius iteration in char-p).
4. Hence `df = 0` on all of `A` (because `Ω_{A/k}` is generated by
   global sections, by triviality).
5. Per-chart `df_W = 0`, then piece (ii) chart-by-chart shows `f|_W`
   factors through `Spec k`, glued by `ext_of_eqOnOpen` to `f = const`.

**What piece (i.b)+(i.c) buys**: steps 1–4. Specifically, the
finite-dimensional identification `H^0(A, Ω_{A/k}) ≅ η_A^* Ω_{A/k}`
(via globalisation) and the "Ω_A generated by global sections"
consequence that lets `df = 0` propagate from global sections to all
charts.

**Without (i.b)+(i.c)**: the chart-algebra alternative must supply
"per-chart `df_W = 0`" from a different argument. Two candidate
suppliers:

- **Frobenius (piece iii) in char-p**: replace `f` with `f ∘ F_C^n`,
  whose differential is zero "by construction". Per-chart
  `d(f ∘ F_C^n)_W = 0` directly. Apply piece (ii) chart-by-chart.
  Descent to `f` via smoothness of `A`. **Works only in char-p.**
- **Serre duality (piece iv) in char-0**: `H^0(C, Ω_{C/k}) = H^1(C, O_C)^∨`,
  zero for genus-0. But Serre duality is a deferred 3000–8000 LOC
  named gap. **Same blocker as bundled path.**

**Critical observation**: the chart-algebra alternative does
**not** eliminate the genus-0 → vanishing-1-forms input. It pushes
the same Serre/Frobenius dependency to a per-chart shape, but the
**load-bearing Mathlib gap is identical**. The (i.b)+(i.c) bundled
path's role is to package this dependency cleanly as
"`Ω_{A/k}` is trivialised by `g` global sections", not to bypass it.

**Verdict on Decision 1**: PROCEED — both paths need the same
genus-0 input; (i.b)+(i.c) does not bypass piece (iv) Serre / piece
(iii) Frobenius any more than chart-algebra does.

### Decision 2: Can chart-algebra rigidity skip (i.b) sheaf-level work entirely?

The chart-algebra alternative's per-chart input is "`d(f^# a) = 0`
in `Ω[Γ(f^{-1}W)/k]` for every `a ∈ Γ(W)`". To derive this
**without** the (i.b) sheaf-level trivialisation, the chart-algebra
path needs:

- (α) For each chart `W ⊆ A`, a **chart-level shear iso** identifying
  `Ω[Γ(W)/k]` with the base-change of the fibre cotangent — this is
  `tensorKaehlerEquiv` applied to a chart-level `Algebra.IsPushout`
  square cut out via `pullbackSpecIso`.
- (β) For each `f : C → A`, a per-chart computation that `df_W = 0`
  iff a finite system of "translation-invariant generators" vanishes.

**(α) cost**: ~80–150 LOC for the chart-level `Algebra.IsPushout` helper
(per iter-137 `kaehler-tensorequiv-presheafpullback.md` Decision 2; per
iter-139 `isiso-basechange-along-proj-two-inv.md` Decision 3 — **the same
helper that Route (b'2) for the IsIso sub-sorry needs**). This helper is
NOT shared between bundled and chart-algebra paths — the bundled path
needs it inside (i.b) Step 2, the chart-algebra path needs it as
standalone per-chart shear-iso machinery. **Either way, ~80–150 LOC of
shared infrastructure is unavoidable.**

**(β) cost**: ~150–300 LOC for the per-chart translation-invariance
argument. Concretely, given `a ∈ Γ(W)`, build the `g` "translation-
invariant generators" `{ω_1, ..., ω_g}` of `Ω[Γ(W)/k]` via the
`tensorKaehlerEquiv` from (α), write `d(f^# a) = Σ c_i · (f^# ω_i)`
with `c_i ∈ Γ(f^{-1}W)`, and conclude `c_i = 0` via the genus-0 input
(per Decision 1). **This is structurally the same chart-by-chart
unfolding of what piece (ii) `ext_of_diff_zero` proves**, just with
the genus-0 input plugged in **before** invoking piece (ii) instead
of as a separate sheaf-level argument upstream.

**(α) + (β) total**: ~230–450 LOC for the chart-algebra rigidity
replacement of (i.b) Step 2. Plus piece (ii) `ext_of_diff_zero`
(~300–600 LOC, unchanged from iter-138 PIN-path-(b)) + glue
(~included in piece (ii)).

**Comparison with bundled (i.b) Step 2 envelope**: ~410–810 LOC
(per iter-137 widening + iter-138/iter-139 helper layer +
Route (b'2) IsIso closure).

**Apparent savings**: ~180–360 LOC. But this is fragile:

- The (α) shared infrastructure (`Algebra.IsPushout` chart helper) is
  the same in both paths.
- The (β) per-chart translation-invariance argument is **not
  Mathlib-canonical** — it's a project-specific construction that
  reproduces piece (i.b)'s mathematical content algebraically without
  the sheaf-level shear iso. There's no Mathlib precedent for it.
- The (β) argument **requires chart-level "constants of `Ω[Γ(W)/k]`
  are translates of a fixed basis"** at each chart W, which is the
  same content as piece (i.b)'s `mulRight_globalises_cotangent`
  unfolded per chart. The mathematical work is conserved; only the
  bundling of artefacts changes.

**Verdict on Decision 2**: chart-algebra rigidity does NOT cleanly
escape (i.b) — it restructures (i.b)'s content into chart-level
helpers without a clean named artefact. Apparent LOC savings
~180–360 LOC are partially offset by the loss of named API
(`omega_free`, `omega_rank_eq_dim`) and the need to surface
chart-level translation-invariance helpers that have no Mathlib
precedent.

### Decision 3: Compatibility with piece (ii) (iter-138 `containConstants` verdict)

Piece (ii) `Scheme.Over.ext_of_diff_zero` per the iter-138 PIN-path-(b)
verdict already routes through:

1. Per-chart `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`
   (NEW algebra-level lemma, ~200–350 LOC).
2. Per-chart conclusion `f|_W factors through k`.
3. `Scheme.Over.ext_of_eqOnOpen` to globalise (~100–150 LOC).

**The chart-algebra rigidity alternative is essentially "use piece (ii)
chart-by-chart with the `df = 0` input directly, no globalisation
step"**. Piece (ii) already encodes step 1+2+3 of the chart-algebra
alternative's downstream half. The question is whether the chart-algebra
alternative's upstream half ((α) + (β) from Decision 2) replaces
(i.b)+(i.c.1)+(i.c.2)+(i.c.3) cleanly.

**Compatibility verdict**: chart-algebra is compatible with the iter-138
PIN-path-(b) piece (ii). Piece (ii) is unchanged; only its upstream
input ((α) chart-level shear iso + (β) per-chart translation-invariance
argument) changes from bundled (i.b)+(i.c) to chart-algebra.

**However**: piece (ii) PIN-path-(b)'s 300–600 LOC envelope ALREADY
absorbs the chart-by-chart Kähler reasoning. Adding the chart-algebra
upstream half to piece (ii)'s scope inflates piece (ii) to **600–1050 LOC**
(~300–600 LOC piece (ii) core + ~300–450 LOC chart-algebra upstream).

**Total chart-algebra envelope** (replacing bundled (i.b)+(i.c)):
~600–1050 LOC for piece (ii) (inflated) + Σ piece (i.a) iter-132 (KEEP, ~250 LOC closed) = **~850–1300 LOC** total.

**Total bundled envelope**: ~610–1310 LOC ((i.b) 410–810 + (i.c) 200–500),
**plus** ~300–600 LOC piece (ii), **plus** ~250 LOC piece (i.a) closed
= **~1160–2160 LOC** total.

**Net chart-algebra saving** (vs bundled): ~310–860 LOC. But:

- Loss of `omega_free` and `omega_rank_eq_dim` as named API.
- Loss of `mulRight_globalises_cotangent` as a sheaf-level lemma
  (potentially useful for non-rigidity consumers; though there are no
  in-tree consumers, this is a Mathlib-PR-able artefact).
- **Sunk-cost on iter-138 substantive Route (b) work** (3 narrowly-scoped
  sub-sorries, Route (b'2) plan ready for iter-140 prover lane).
- Piece (ii) scope inflation (600–1050 LOC); risk of progress-critic
  CHURNING on a larger lane.

**Verdict on Decision 3**: chart-algebra rigidity is COMPATIBLE with
piece (ii); it absorbs (i.b)+(i.c) into piece (ii)'s scope. The total
LOC saving is **modest and uncertain** (~310–860 LOC; range partially
absorbed by piece (ii) inflation). The API-loss cost is real.

### Decision 4: Compatibility with piece (iii) char-p Frobenius

Piece (iii) per `analogies/cotangent-vanishing-pile-over-k.md` Decision
(iii) is the **scheme-level absolute Frobenius `F_X`** lift (~800–1500
LOC PHANTOM in-tree per iter-128/iter-129 honest accounting; no
Mathlib `Scheme.absoluteFrobenius` in `b80f227`, verified this iter).

The scheme-level lift is needed regardless of (i.b)+(i.c) vs
chart-algebra because piece (iii) is the **char-p substitute for the
genus-0 input** — it replaces `f` with `f ∘ F_C^n` and reduces to
piece (ii) chart-by-chart.

**Chart-algebra alternative claim**: "compose with piece (iii) on
charts (ring-level `Mathlib.Algebra.CharP.Frobenius`) without the
scheme-level absolute Frobenius PHANTOM (800–1500 LOC)".

**Verification**: ring-level `iterateFrobenius` on `Γ(W)` for each
chart W is k-agnostic and chart-level (verified iter-127 + this iter).
For chart-algebra rigidity, **chart-by-chart Frobenius DOES suffice**:
for each chart W of A, `f^# ∘ iterateFrobenius_{Γ(W), p, n} =
iterateFrobenius_{Γ(f^{-1}W), p, n} ∘ f^#` by RingHom.iterateFrobenius_comm
(verified in `Mathlib.Algebra.CharP.Frobenius`). The chart-level
Frobenius iteration argument feeds `d(f^# (a^{p^n})) = 0` directly into
the chart-algebra rigidity per-chart application, completely
bypassing the scheme-level `Scheme.absoluteFrobenius` PHANTOM.

**Critical implication**: if chart-algebra rigidity is adopted, piece
(iii)'s scheme-level absolute Frobenius PHANTOM (800–1500 LOC) is
**eliminated as a project obligation**. This is a substantial saving
beyond the (i.b)+(i.c) bundled cost.

**However**: piece (iii) is **iter-144+** (sequenced after pieces (i)+(ii)
close). The piece (iii) saving is **conditional on chart-algebra
rigidity succeeding** at piece (ii)'s now-inflated 600–1050 LOC scope.
If piece (ii) chart-algebra-inflated stalls, the iter-144+ piece (iii)
saving never materialises.

**Verdict on Decision 4**: chart-algebra rigidity has a **significant
piece-(iii) compatibility advantage** — it eliminates the 800–1500 LOC
scheme-level Frobenius PHANTOM. **This is the strongest argument in
favour of PIVOT_TO_CHART_ALGEBRA**. But it is conditional on (a)
piece (ii) chart-algebra inflation closing, and (b) iter-144+ piece
(iii) build actually happening (currently gated on iter-141 (i.c) + iter-143
(ii) closure status per iter-139 STRATEGY.md edit on named-gap alternative).

### Decision 5: API value of `omega_free` / `omega_rank_eq_dim` as named consumers

`omega_free` (`Ω_{G/k}` is free as `O_G`-module) and `omega_rank_eq_dim`
(rank pinning to `dim G`) are independently useful Mathlib-shaped
consequences. **Potential consumers**:

- Any future scheme-side cotangent-sheaf user (smoothness criteria, RR,
  curve cohomology).
- Mathlib-PR candidate: "the relative cotangent of a smooth group
  scheme is trivial" is a clean named lemma matching Mathlib's
  `Mathlib.Geometry.Manifold.GroupLieAlgebra.mulInvariantVectorField`
  precedent at the scheme level (no scheme-level analogue exists in
  `b80f227`).

**Loss under chart-algebra pivot**: these named artefacts are not
built. The chart-level (β) translation-invariance helper is
project-internal, not Mathlib-PR-able.

**Severity**: moderate. The project's Mathlib-contributor framing per
iter-121 user directive emphasises building gap-filling pieces
in-tree at Mathlib-merge quality. Dropping `omega_free` / `omega_rank_eq_dim`
removes two clean named contributions. The chart-algebra pivot is
internally consistent with the project's needs but loses two upstream
PR candidates.

**Verdict on Decision 5**: API-value loss is **moderate, not
load-bearing**. The named artefacts would be project-internal Mathlib
contributions; the project has other named contributions in flight
(`kaehler_quotient_localization_iso`, M3 Relative Spec functor PR lane).

## Cross-cutting cost tally

| Cost axis | Bundled (i.b)+(i.c) | Chart-algebra rigidity |
|---|---|---|
| Piece (i.b) closure | 410–810 LOC (sheaf-level; iter-138 narrowed to 3 sub-sorries) | 0 LOC (replaced by chart-level helpers absorbed into piece (ii)) |
| Piece (i.c) (chart-localisation + freeness + rank) | 200–500 LOC | 0 LOC |
| Piece (ii) `ext_of_diff_zero` | 300–600 LOC (iter-138 PIN-path-(b)) | 600–1050 LOC (inflated to absorb chart-algebra upstream) |
| Chart-level `Algebra.IsPushout` helper | included in (i.b) | ~80–150 LOC (standalone) |
| Per-chart translation-invariance (β) | included in (i.b)+(i.c) | ~150–300 LOC (NEW project-internal helper) |
| Piece (iii) scheme-level absolute Frobenius PHANTOM | 800–1500 LOC | **0 LOC** (chart-level Frobenius suffices) |
| `omega_free` / `omega_rank_eq_dim` named API | YES (Mathlib-PR candidates) | NO |
| `mulRight_globalises_cotangent` sheaf-level lemma | YES (Mathlib-PR candidate) | NO |
| Iter-138 sunk cost (3 sub-sorries narrowed + Route (b'2) plan) | reused | **discarded** |
| Pile total (i.b)+(i.c)+(ii)+(iii) | **1710–3410 LOC** | **830–1500 LOC** |
| Piece (i.a) iter-132 closed | KEEP (~250 LOC closed, no change) | KEEP |
| **Grand total** | **~1960–3660 LOC** | **~1080–1750 LOC** |
| **Saving under chart-algebra** | — | **~880–1910 LOC** |

The dominant saving line is **piece (iii)** (800–1500 LOC PHANTOM
eliminated), NOT (i.b)+(i.c). The (i.b)+(i.c) saving alone is
~310–860 LOC and partially offset by piece (ii) inflation.

## Risk tally

| Risk | Bundled (i.b)+(i.c) | Chart-algebra rigidity |
|---|---|---|
| `PresheafOfModules.pullback` chart-opacity | EXPOSED in (i.b) Step 2 | AVOIDED |
| Scheme-level Frobenius PHANTOM | EXPOSED in (iii) | AVOIDED |
| Genus-0 → vanishing 1-forms input (Serre / Frobenius) | SAME (load-bearing) | SAME (load-bearing) |
| Sunk cost on iter-138 substantive work | reused | discarded (sub-sorries × 3, Route (b'2) plan) |
| API-value loss (`omega_free`, `omega_rank_eq_dim`, `mulRight_globalises_cotangent`) | preserved | lost |
| Piece (ii) scope inflation (CHURNING risk on a larger lane) | NO (piece (ii) at 300–600 LOC) | YES (piece (ii) at 600–1050 LOC) |
| Blueprint restructure cost | NO | YES (`RigidityKbar.tex` § Piece (i) + § shared_pile + § Piece (ii) prose all need rewrites) |
| Strategy-critic alignment cost | LOW (continues current STRATEGY.md `M2.body-pile`) | HIGH (requires rewriting M2.body-pile + piece accounting) |

## Verdict

**HYBRID with chart-algebra pivot deferred as conditional fallback.**

This is a genuine close call. Recommend the following staged decision:

### Primary recommendation (iter-140+ short-term): ALIGN_WITH_BUNDLED on (i.b)+(i.c)

For the iter-140 prover lane on (i.b) Step 2's 3 sub-sorries, **stay
the course**. Reasons:

1. **Iter-138 sunk cost is real and the work is narrowed**: 3
   concrete sub-sorries with closure recipes (Route (b'2) for IsIso at
   195–365 LOC per iter-139 analogist). Discarding this to pivot would
   waste iter-134→iter-138 prover-cycle investment.
2. **`omega_free` and `omega_rank_eq_dim` carry API value**:
   Mathlib-PR-candidate named lemmas matching scheme-level analogues
   of `mulInvariantVectorField`. Project's Mathlib-contributor framing
   (iter-121) values these.
3. **Iter-140 close-ratio determines pivot trigger**: if iter-140
   PROGRESS criterion fires (≥2-of-3 sub-sorries closed), the
   bundled path is confirmed tractable and the chart-algebra pivot
   becomes a sunk-cost-only loss. If iter-140 CHURNING criterion
   fires (0–1 sub-sorries closed, third consecutive PARTIAL), THEN
   the pivot decision re-opens.

### Conditional pivot trigger (iter-141+): consider PIVOT_TO_CHART_ALGEBRA if

- Iter-140 PARTIAL with 0–1 sub-sorries closed (CHURNING-trigger per
  `progress-critic-iter139` watch criterion), AND
- iter-141 dispatch of a 5th mathlib-analogist on piece (i.b) Step 2
  fires (per iter-139 Edit 2 analogist-overhead-axis 5-consult
  threshold), AND
- iter-140 §519 over-k auto-flag re-fires with stricter language (per
  iter-139 Edit 1).

Under these conditions, dispatch a **fresh chart-algebra strategy-critic
re-consult** with this analogy file as the read-input, and re-open the
pivot decision with the substantive piece-(iii) PHANTOM-elimination
argument in scope.

### Conditional pivot trigger (iter-143+): mandatory re-evaluation at piece (iii) gate

When the iter-144+ piece (iii) build is scheduled, **regardless of
(i.b)+(i.c) closure status**, re-dispatch a chart-algebra-vs-bundled
analysis with the iter-144 scheme-level Frobenius PHANTOM (800–1500
LOC) on the table. The piece-(iii) PHANTOM-elimination argument is
the **single strongest pivot driver** — at iter-144+ the question
becomes "is rebuilding piece (i.b)+(i.c) chart-style cheaper than
800–1500 LOC of scheme-Frobenius PHANTOM?". Answer is likely YES;
schedule a project-wide pivot consult at that gate.

## Per-decision summary

| Decision | Verdict |
|---|---|
| 1: Both paths need the same genus-0 → vanishing-1-forms input | PROCEED |
| 2: Chart-algebra cannot cleanly skip (i.b); restructures rather than eliminates | DIVERGE_INTENTIONALLY (continue bundled iter-140+ short-term) |
| 3: Compatibility with piece (ii) iter-138 PIN-path-(b) | PROCEED (chart-algebra inflates (ii) to 600–1050 LOC) |
| 4: Chart-algebra ELIMINATES piece (iii) scheme-level Frobenius PHANTOM | NEEDS_MATHLIB_GAP_FILL (the PHANTOM is the gap; chart-algebra bypasses it) — **STRONGEST PIVOT DRIVER** |
| 5: API value of `omega_free` / `omega_rank_eq_dim` | DIVERGE_INTENTIONALLY (moderate loss, not load-bearing) |

## Overall verdict

**HYBRID — short-term ALIGN_WITH_BUNDLED + iter-141 conditional pivot
trigger + iter-144 mandatory re-evaluation at piece (iii) gate.**

LOC savings:
- Iter-140 short-term: **0 LOC saved** (continue bundled).
- Iter-141 conditional pivot (if (i.b) Step 2 CHURNING): **~310–860
  LOC saved** on (i.b)+(i.c), partially offset by piece (ii) inflation.
- Iter-144 mandatory re-evaluation at piece (iii) gate: **~880–1910
  LOC saved** if pivot is adopted then (the piece-(iii) PHANTOM-
  elimination dominates).

Dependencies: continuation of iter-140 prover lane on (i.b) Step 2's 3
sub-sorries with Route (b'2) for IsIso per `analogies/isiso-basechange-along-proj-two-inv.md`.

Iter-140+ schedule recommendation:

| Iter | Action |
|---|---|
| 140 | Continue bundled (i.b) Step 2 prover lane per current PROGRESS.md plan. |
| 141 | If iter-140 closes ≥2 sub-sorries: continue bundled. Else: fresh chart-algebra strategy-critic consult with this file as input. |
| 143 | Schedule piece (ii) `ext_of_diff_zero` per iter-138 PIN-path-(b); 300–600 LOC envelope (unchanged). |
| 144 | **MANDATORY** chart-algebra re-evaluation BEFORE committing to scheme-Frobenius PHANTOM build. |

## Severity

**high-stakes.** The verdict directly determines the iter-140+
prover-lane direction AND scheduling of piece (iii) build. The
piece-(iii) PHANTOM elimination (~800–1500 LOC) is large enough to
re-shape the project's iter-144+ multi-iter sequencing. The bundled
short-term recommendation preserves iter-138 sunk cost; the conditional
piece-(iii)-gate re-evaluation prevents a sunk-cost trap on the
scheme-Frobenius PHANTOM.
