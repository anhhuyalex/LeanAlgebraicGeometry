# Analogy: `AlgebraicGeometry.Scheme.absoluteFrobenius` scheme-Frobenius scoping (piece (iii))

## Slug

scheme-frobenius-piece-iii-scoping

## Iteration

141

## Question

Scope `AlgebraicGeometry.Scheme.absoluteFrobenius` PHANTOM against
Mathlib `b80f227`, using Stacks Tag 0CC4 as the canonical construction
reference and `Mathlib.Algebra.CharP.Frobenius` as the ring-side
baseline. Output: per-sub-piece LOC estimate, idiom-alignment cost
broken out explicitly (parallel-API risk; consumer-side bridge-lemma
cost), prerequisite gaps, and a verdict on whether the in-tree build
is sustainable at < 2000 LOC (the iter-141 pivot threshold). The
analogy file is the read-input for the iter-144 mandatory
chart-algebra-vs-bundled re-evaluation gate.

## Project artifact(s)

- `STRATEGY.md` ~L471 — piece (iii) row in the Mathlib-gap inventory;
  iter-128 provisional 800–1500 LOC commitment; iter-139 honest-
  framing as switching-cost + zero-sorry-end-state-commitment-driven.
- `STRATEGY.md` ~L505 — sequencing row for piece (iii) iter-144+;
  honest in-tree build per `strategy-critic-iter128`.
- `STRATEGY.md` ~L591 — iter-141 mandatory scoping consult directive
  (this analogist call).
- `STRATEGY.md` ~L592 — iter-144 mandatory chart-algebra-vs-bundled
  re-evaluation gate; this analogy file is the read-input.
- `analogies/direct-chart-algebra-rigidity-ib-ic.md` (iter-140) —
  the chart-algebra alternative; verifies sub-piece 6.
- `AlgebraicJacobian/Rigidity.lean:51` — the only project mention of
  scheme-level absolute Frobenius (in a prose paragraph distinguishing
  it from the identity; no formal declaration anywhere).

## Mathlib infrastructure snapshot (`b80f227`, verified this iter)

| Name | Location | Role in scheme-Frobenius build |
|---|---|---|
| `frobenius R p : R →+* R` | `Mathlib.Algebra.CharP.Lemmas` | Ring-side baseline (sub-piece 1 chart) |
| `iterateFrobenius R p n : R →+* R` | `Mathlib.Algebra.CharP.Lemmas` | Ring-side iterate (sub-piece 3 chart) |
| `frobenius_def`, `iterateFrobenius_def`, `iterateFrobenius_eq_pow` | `Mathlib.Algebra.CharP.Frobenius` | Definitional unfolds (sub-piece 1/3 helpers) |
| `RingHom.map_frobenius`, `RingHom.frobenius_comm`, `RingHom.iterateFrobenius_comm` | `Mathlib.Algebra.CharP.Frobenius` | Naturality of `frobenius`/`iterateFrobenius` against arbitrary `R →+* S` — load-bearing for sheaf-NatTrans naturality (sub-piece 1) and chart-restriction compatibility (sub-piece 2) |
| `ExpChar R p`, `RingHom.charP`, `RingHom.charP_iff_charP` | `Mathlib.Algebra.CharP.Defs` / `.Algebra` | Char-p propagates from `Γ(X)` to each `Γ(U)` via the structure-sheaf restriction maps (no explicit per-open hypothesis needed once `[ExpChar Γ(X, ⊤) p]` is in scope) |
| `IsPurelyInseparable.iterateFrobenius_algebraMap` | `Mathlib.FieldTheory.PurelyInseparable.Exponent` | Field-theoretic ring-level analogue of "f factors through Frobenius iterate"; **NOT a scheme-side substitute** for sub-piece 4 |
| `AlgebraicGeometry.Spec.map (f : R ⟶ S)` + `map_id`/`map_comp`/`map_app`/`map_base`/`map_appLE`/`map_inv`/`map_eqToHom`/`map_basicOpen_eq` family | `Mathlib.AlgebraicGeometry.Scheme:499–541` | Functoriality of `Spec` on ring maps — gives the `Spec(frobenius R p) : Spec R ⟶ Spec R` lift on each affine for free; no parallel API needed |
| `AlgebraicGeometry.LocallyRingedSpace.Hom` (struct + `comp` + stalk-locality) | `Mathlib.Geometry.RingedSpace.LocallyRingedSpace:77–135` | The right abstraction for building `Scheme.Hom` from (base, sheaf-NatTrans, stalk-locality) data — the construction site for `absoluteFrobenius` (sub-piece 1) |
| `AlgebraicGeometry.PresheafedSpace.Hom` (struct = base + sheaf-NatTrans into pushforward) | `Mathlib.Geometry.RingedSpace.PresheafedSpace:70–84` | Lower-level layer the LRS construction builds on |
| `AlgebraicGeometry.Scheme.toSpecΓ` + `toSpecΓ_naturality` | `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` | Universal property `X ⟶ Spec Γ(X)`; not strictly needed for the construction but useful for `simp`-lemma family naturality |
| `AlgebraicGeometry.IsAffineOpen` + `.inf`/`.iInf`/`.biInf`/`.preimage`/`.of_subsingleton`/`.fromSpec`/`.fromSpecStalk_eq` | `Mathlib.AlgebraicGeometry.AffineScheme`, `.Morphisms.Affine`, `.Stalk` | Affine-open coverage + transfer lemmas — load-bearing for sub-piece 2 (restriction compatibility) |
| `AlgebraicGeometry.Scheme.AffineCover` | `Mathlib.AlgebraicGeometry.Cover.MorphismProperty` | Affine cover infrastructure — used in the proof of stalk-locality and restriction compatibility |
| `AlgebraicGeometry.Scheme.absoluteFrobenius` / `Scheme.frobenius` | **ABSENT** in `b80f227` | The construction target itself; PHANTOM |
| `AlgebraicGeometry.Scheme.iterateFrobenius_X` | **ABSENT** | Sub-piece 3 target; PHANTOM |
| Char-p scheme-level "df = 0 ⇒ f factors through F_C^n" theorem | **ABSENT** | Sub-piece 4 target; PHANTOM (closest precedent is the ring-side `IsPurelyInseparable.iterateFrobenius_algebraMap`, but that's a *field-only* statement with very different hypotheses) |

The verification confirms: ring-side baseline is rich (everything needed
to build the scheme-level construction on charts); scheme-side is empty
(no `Scheme.absoluteFrobenius`, no scheme-iterate, no factor-through-F_C
theorem).

## Decisions identified

### Decision 1: sub-piece 1 — `AlgebraicGeometry.Scheme.absoluteFrobenius` definition + functoriality + basic API

**Stacks Tag 0CC4 prose**: Let `p` be a prime and `X` a scheme in
characteristic `p` (meaning `p · 1 = 0` in `Γ(X, O_X)`). The **absolute
Frobenius** `F_X : X → X` is the morphism of schemes which is the
identity on the underlying topological space and whose sheaf map
`F_X^# : O_X → (id_*) O_X = O_X` raises each section to the `p`-th
power.

**Mathlib idiom for the construction site**: build a
`LocallyRingedSpace.Hom X.toLRS X.toLRS` (which auto-upgrades to a
`Scheme.Hom` via the LRS→Scheme inclusion), specifying:
- `base = 𝟙 X.toTopCat`,
- `c : Y.presheaf ⟶ (𝟙 X.toTopCat)_* X.presheaf` as a sheaf-NatTrans
  whose component at each `U` is `CommRingCat.ofHom (frobenius (X.presheaf.obj U) p)`,
- naturality across restriction `V ⊆ U`: this is **`RingHom.frobenius_comm`**
  applied componentwise (the restriction map `Γ(U) → Γ(V)` is a ring
  hom; frobenius commutes with all ring homs by `RingHom.frobenius_comm`),
- stalk-locality: the stalk-level map `O_{X,x} → O_{X,x}` is `frobenius
  O_{X,x} p` which is a local homomorphism (its preimage of the maximal
  ideal is the maximal ideal, since `m^p ⊆ m`).

**Char-p hypothesis shape**: cleanest is `[ExpChar Γ(X, ⊤) p]` at the
global section level. This propagates to each `[ExpChar Γ(X, U) p]` via
`RingHom.charP` applied to the restriction `Γ(X) → Γ(U)`. Provide a
helper `instance` so the per-open `frobenius` typechecks. **No new
typeclass needed** — Mathlib's `ExpChar` + `RingHom.charP` is exactly
the right shape.

**Stalk-locality of frobenius on a local ring**: `frobenius` of a local
ring `R` is local because `frobenius (m) = m^p ⊆ m` and the maximal
ideal of `R` is the preimage of the maximal ideal of `R`. This is
either a 5–10 LOC inline proof or wants a tiny helper
`IsLocalHom.frobenius` (could even ship to Mathlib as a 3-line lemma).

**LOC estimate for sub-piece 1**: ~150–300 LOC for the definition + a
basic `@[simp]` API (`absoluteFrobenius_base`, `absoluteFrobenius_app`,
`absoluteFrobenius_appLE`, the eqToHom for the pushforward
identification, the compatibility `(Spec R).absoluteFrobenius p =
Spec.map (CommRingCat.ofHom (frobenius R p))` for affines).

**Mathlib idiom**: there is no Mathlib precedent for `Scheme`-level
Frobenius at all (NEEDS_MATHLIB_GAP_FILL), but the construction pattern
(build LRS Hom from base + sheaf NatTrans + stalk-locality) is **exactly
how Mathlib builds other `Scheme.Hom` values**. The proposed build
follows Mathlib idiom cleanly.

**Verdict on Decision 1**: NEEDS_MATHLIB_GAP_FILL. The gap is genuine
and the construction follows the Mathlib idiom for building scheme
morphisms. **No idiom-alignment cost.**

### Decision 2: sub-piece 2 — restriction compatibility `F_X |_U = F_U`

For any open `U ⊆ X`, the absolute Frobenius of the open subscheme
`U.toScheme` agrees with the restriction of `F_X` along `U.ι`. As a
commuting square: `U.ι ≫ F_X = F_U ≫ U.ι` in `Scheme`.

**Construction**: both morphisms have the same topological base (the
identity on `|U|` composed with the inclusion, which equals the
inclusion composed with the identity), and the same sheaf map (both
restrict to `frobenius (Γ(V, O_X)) p` on each open `V ⊆ U`). The proof
is `Scheme.Hom.ext` followed by `app`/`base` componentwise unfolding;
the `app` componentwise equality reduces to `frobenius`
naturality which is `RingHom.frobenius_comm` against the restriction
`Γ(U, O_X) → Γ(V, O_X)`.

**Mathlib idiom**: `Scheme.Hom.ext` + per-open `app` equality is the
standard recipe; `IsAffineOpen.{inf, preimage, biInf}` infrastructure
covers affine-open intersection arguments. No new infrastructure
needed.

**LOC estimate for sub-piece 2**: ~80–150 LOC for the lemma + a small
`@[simp]` family (`absoluteFrobenius_restrict`,
`absoluteFrobenius_comp_inclusion`).

**Verdict on Decision 2**: NEEDS_MATHLIB_GAP_FILL. Standard idiom; no
parallel-API risk.

### Decision 3: sub-piece 3 — `iterateFrobenius_X p n : X ⟶ X`

Two routes:
1. **Categorical iterate**: `iterateFrobenius_X p n := (absoluteFrobenius X p)^[n]`
   in the monoid of `Scheme` endomorphisms (using `Monoid.npow` on
   `End X`, or unfolded explicitly as repeated composition with `𝟙` as
   the base case).
2. **Direct**: define `Scheme.Hom.{base := 𝟙, c := frobeniusNT^n}` and
   show it agrees with route 1.

**Mathlib precedent**: ring-side has both `iterateFrobenius R p n` and
`(frobenius R p)^[n]`, with `iterateFrobenius_eq_pow`
(`Mathlib.Algebra.CharP.Frobenius:40`) tying them. The scheme-side
should mirror: define `iterateFrobenius_X` and prove
`iterateFrobenius_X_eq_npow` and `iterateFrobenius_X_app_eq_iterateFrobenius`
(the chart-level statement that on `Γ(U)`, the iterate of the scheme
Frobenius restricts to `iterateFrobenius (Γ(U)) p n` — direct corollary
of sub-piece 1's `_app` lemma plus `RingHom`-side naturality).

**LOC estimate for sub-piece 3**: ~50–120 LOC for the definition + the
2–3 `simp` lemmas tying it to sub-piece 1's per-open Frobenius.

**Verdict on Decision 3**: NEEDS_MATHLIB_GAP_FILL. Trivially follows
sub-piece 1; no idiom-alignment cost.

### Decision 4: sub-piece 4 — consumer lemma "df = 0 ⇒ f factors through F_C^n iterate"

The consumer lemma the M2.a body actually needs is (schematically): for
a morphism `f : C → A` of smooth proper schemes over a char-p field `k`
with `df = 0` (Kähler differential map `f^* Ω_{A/k} → Ω_{C/k}` is
zero), there exists `n` such that `f` factors as `f = g ∘ F_C^n` for
some `g : C → A`. The proof structure (standard, e.g. Mumford's
*Abelian Varieties*):

1. **Local form**: on each affine chart `W ⊆ A`, `df = 0` ⇒ `d(f^# a) = 0`
   for all `a ∈ Γ(W)`. Then `Γ(W) / k` standard-smooth + `d r = 0` ⇒
   `r ∈ R^p` for the relevant `R = Γ(f^{-1}W)`. This is the
   *local-to-p-th-power-ideal* step.
2. **Uniform `n`**: a priori each section is some `p^{n_a}`-th power
   for unrelated `n_a`. Use smoothness + properness (so `C` is
   quasi-compact) to get a uniform `n` working for all sections in a
   finite chart cover.
3. **Glue**: the chart-wise factorizations through `iterateFrobenius`
   on charts glue to a scheme-level factorization `f = g ∘ F_C^n`.
   Globally `iterateFrobenius_X` is needed here (sub-piece 3).

**Mathlib precedent**: **none for the scheme-side statement**. The
closest Mathlib analogue is
`IsPurelyInseparable.iterateFrobenius_algebraMap`
(`Mathlib.FieldTheory.PurelyInseparable.Exponent`), which is a
ring-side statement *over a perfect field with purely inseparable
extension* — very different hypothesis shape, not a substitute.

**Sub-piece 4 prerequisites NOT YET IN MATHLIB**:
- "Char-p commutative ring + `Ω_{R/k}` free + `d r = 0` ⇒ `r ∈ R^p`"
  — the **local form**. Mathlib has neither a direct statement nor
  the smoothness-side machinery to extract a `p`-th-power witness from
  a kernel-of-derivation statement. **~200–400 LOC of new
  algebra-level Mathlib infrastructure** (which is closely related to
  piece (ii) PIN-path-(b)'s
  `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero` ~200–350 LOC
  estimate — they share the *kernel-of-D* reasoning shape but differ
  in target ("constant" for piece (ii) vs "`p`-th power" for piece
  (iii) sub-piece 4)).
- Quasi-compactness of `C` to extract uniform `n`. Mathlib has
  `IsCompact` + `AlgebraicGeometry.QuasiCompact` infrastructure; the
  argument is a noetherian-style finite-cover. **~50–100 LOC** of
  glue.
- Scheme-level factorization-through-morphism wrapper. **~30–80 LOC**.

**LOC estimate for sub-piece 4**: ~400–800 LOC total. The local form
(~200–400 LOC) is the dominant cost; uniform `n` glue (~50–100 LOC);
scheme-level factorization wrapper (~30–80 LOC); compatibility lemmas
threading sub-piece 1/2/3 (~50–100 LOC); main theorem statement +
proof (~70–120 LOC).

**Idiom-alignment cost**: sub-piece 4 has **no Mathlib idiom** for the
top-level theorem (`Scheme.factorsThrough_iterateFrobenius_of_diff_zero`
or similar). It would be a new top-level result. The pieces it consumes
(D = 0 implies p-th power; quasi-compactness glue) DO have Mathlib idiom
shapes; assembling them is project-internal.

**Verdict on Decision 4**: NEEDS_MATHLIB_GAP_FILL. The dominant LOC
cost in the whole sub-piece tally; no Mathlib precedent for the top-
level theorem. **However**, sub-piece 4 is the only one of (1)/(2)/
(3)/(4) that is **bypassable** by the chart-algebra alternative (see
Decision 6) — if chart-algebra is adopted, sub-piece 4 is replaced by
the per-chart Kähler-kernel statement absorbed into piece (ii), at
~150–300 LOC.

### Decision 5: parallel-API risk on `Scheme.Spec` functoriality

**Mathlib idiom**: `AlgebraicGeometry.Spec.map (f : R ⟶ S) : Spec S ⟶ Spec R`
exists with the full functoriality family `_id`/`_comp`/`_app`/`_base`/
`_appLE`/`_inv`/`_eqToHom`/`_basicOpen_eq` (`Mathlib.AlgebraicGeometry.Scheme:499–730`).
For the project's `(Spec R).absoluteFrobenius p`, the natural
identification is
```
(Spec R).absoluteFrobenius p = Spec.map (CommRingCat.ofHom (frobenius R p))
```
— a **single new lemma**, ~5–10 LOC, that anchors the scheme-side
construction to the existing `Spec.map` family. **No parallel API.**

The candidate-collision case raised in the directive
(`Scheme.specObj_specMap_frobenius : Scheme.Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ _ = _`):
this would only arise if the project re-defined `Spec.map`-style
functoriality on Frobenius specifically. Since the construction
direction is *to use* `Spec.map` (not to redefine it), no collision
arises.

**LOC contribution**: ~10–30 LOC for the affine-side anchoring lemma
+ `simp` attribute. Included in sub-piece 1's API count.

**Verdict on Decision 5**: PROCEED. **No parallel-API risk.** The
project's scheme-Frobenius build consumes Mathlib's `Spec.map` family
directly; it does not parallel it. This is the same shape as M3 Route
B (which lifts ring-side `kaehler_quotient_localization_iso` to scheme-
side via `Spec.map`), confirmed Mathlib-aligned.

### Decision 6: chart-algebra alternative (sub-piece 6)

Per `analogies/direct-chart-algebra-rigidity-ib-ic.md` (iter-140), the
chart-algebra alternative routes piece (iii) entirely through ring-level
chart algebras and `iterateFrobenius` on charts, by-passing the
scheme-level `Scheme.absoluteFrobenius` PHANTOM. The relevant
verification (iter-140 Decision 4):

> "for each chart W of A, `f^# ∘ iterateFrobenius_{Γ(W), p, n} =
> iterateFrobenius_{Γ(f^{-1}W), p, n} ∘ f^#` by
> RingHom.iterateFrobenius_comm (verified in
> `Mathlib.Algebra.CharP.Frobenius`)."

**Question this analogist answers**: is the chart-algebra route a
genuine replacement for the *whole* scheme-Frobenius PHANTOM build
(sub-pieces 1+2+3+4), or only for the M2.a-body consumer (sub-piece 4),
leaving sub-pieces 1+2+3 as load-bearing for other downstream consumers
(Mathlib-PR utility, future M4)?

**Analysis**:

- **In-project consumer (M2.a body)**: chart-algebra bypasses
  sub-pieces 1+2+3+4 entirely. The M2.a body needs only ring-level
  `iterateFrobenius` on chart algebras + `RingHom.iterateFrobenius_comm`
  + piece (ii) chart-by-chart. The chart-algebra alternative absorbs
  ~150–300 LOC of chart-level Frobenius work into piece (ii)'s scope
  (raising piece (ii) from 300–600 to 450–900 LOC if Frobenius is
  added on top of the iter-138 PIN-path-(b) envelope — slightly less
  than iter-140's 600–1050 LOC piece (ii) inflation estimate which
  includes the (i.b)+(i.c) absorption too). **The scheme-level
  `absoluteFrobenius` is NOT load-bearing for M2.a.**

- **Mathlib-PR utility**: scheme-level `absoluteFrobenius` is canonical
  Mathlib infrastructure (Stacks Tag 0CC4 is a canonical section
  precisely because every char-p scheme argument uses it). The
  `mathlib-analogist-p1-hedge-iter138` analogist + `strategy-critic-iter138`
  recorded `AlgebraicGeometry.Scheme.absoluteFrobenius` as an upstream-
  PR-shaped target analogous to the M1.d `kaehler_quotient_localization_iso`
  off-loop PR-extraction precedent. **Sub-pieces 1 + 3 (definition +
  iterate) at ~200–420 LOC remain meaningful as a standalone Mathlib
  PR**, even if the M2.a body doesn't need them.

- **Future M4 consumers**: the iter-127 over-k commitment foreclosed
  Serre-duality-based genus-0 identification (M2.c+M2.c.aux dropped).
  Future M4 (smoothness-criterion converse, isogeny analysis,
  crystalline-cohomology) would need scheme-Frobenius, but M4 is not
  on the active iter roadmap. **For the active project envelope,
  sub-pieces 1+3 are not load-bearing.**

- **Sub-piece 2 (restriction compatibility)**: even as a standalone
  Mathlib PR, sub-piece 2 is "polish" — it's load-bearing for downstream
  *uses* of `absoluteFrobenius` that work chart-by-chart, but the
  definition itself (sub-piece 1) is shippable without it for the
  initial PR. **Sub-piece 2 is deferrable** in any case.

- **Sub-piece 4 (consumer factor-through-F_C)**: this is the M2.a-body
  consumer that chart-algebra bypasses. As a Mathlib PR, it's a
  substantial standalone theorem (~400–800 LOC) and would be useful
  but is genuinely optional — it's the part chart-algebra
  *substantively* replaces.

**Critical finding**: the chart-algebra alternative GENUINELY by-passes
the *entire* scheme-Frobenius PHANTOM build for the M2.a-body consumer.
The scheme-level `absoluteFrobenius` is reduced from "project obligation"
to "off-loop Mathlib-PR target" (sub-pieces 1+3 only; ~200–420 LOC).
Sub-pieces 2+4 become discretionary, ~480–950 LOC of optional work.

**Verdict on Decision 6**: **CHART_ALGEBRA_BYPASSES_PHANTOM**. The
chart-algebra route is a genuine, not partial, replacement for the
scheme-Frobenius PHANTOM. Sub-pieces 1+3 retain Mathlib-PR utility
independent of M2.a; sub-pieces 2+4 are discretionary.

## Cross-cutting LOC tally (this analogist's revised estimates)

| Sub-piece | LOC range | Mathlib idiom alignment | Bypassable by chart-algebra? |
|---|---|---|---|
| 1. `Scheme.absoluteFrobenius` def + functoriality + basic API | **150–300 LOC** | Clean (build LRS Hom from base + sheaf-NatTrans + stalk-local; Mathlib idiom) | Yes (chart-algebra needs only chart-level `frobenius`) |
| 2. Restriction compatibility `F_X|_U = F_U` | **80–150 LOC** | Clean (`Scheme.Hom.ext` + per-open `frobenius_comm`) | Yes (chart-algebra needs only `RingHom.iterateFrobenius_comm`) |
| 3. Iterate `iterateFrobenius_X p n` | **50–120 LOC** | Clean (mirror `iterateFrobenius R p n` ring-side; `_eq_npow` simp lemma) | Yes (chart-algebra uses ring-side `iterateFrobenius` directly) |
| 4. Consumer "df=0 ⇒ f factors through F_C^n" | **400–800 LOC** | None for top-level theorem; pieces have Mathlib shape | Yes (chart-algebra absorbs ~150–300 LOC into piece (ii)) |
| 5. Parallel-API risk on `Scheme.Spec.map` | **+10–30 LOC** anchoring lemma (included in sub-piece 1) | None — uses `Spec.map` directly | N/A (no parallel API to consider) |
| **Sub-pieces 1–4 sum** | **680–1370 LOC** | NEEDS_MATHLIB_GAP_FILL across the board | **Yes, entirely** by chart-algebra |
| **Sub-pieces 1+3 only (Mathlib-PR core, off-loop)** | **200–420 LOC** | Clean, Mathlib-PR shipping shape | N/A — independent of M2.a |
| **Sub-pieces 1+2+3 (full canonical infra, off-loop)** | **280–570 LOC** | Clean | N/A — independent of M2.a |

The iter-128 strategy-critic estimate of **800–1500 LOC** is on the
high end of my sub-pieces 1–4 envelope (~680–1370 LOC) and matches my
midpoint (~1025 LOC). The 800–1500 LOC range is consistent and
honest; this analogist confirms its credibility.

## Pivot criterion verdict

**Pivot threshold (per directive): 2000 LOC.**

**My estimate for sub-pieces 1–4**: 680–1370 LOC (midpoint ~1025 LOC).

**My estimate for sub-pieces 1–4 + sub-piece 5 (anchoring lemmas
included)**: 690–1400 LOC (midpoint ~1045 LOC).

**Result**: my estimate is **substantially below the 2000 LOC pivot
threshold**. The upper bound (1400 LOC) leaves 600 LOC of slack against
the threshold; even accounting for typical project-side LOC inflation
(sub-piece 4's local form might double if smoothness-side infrastructure
needs more glue), the in-tree scheme-Frobenius build remains
sustainable.

**Verdict**: **IN-TREE BUILD SUSTAINABLE**. The named-gap-sorry
alternative does NOT need elevation from "active alternative" to
"preferred default" on LOC-pivot grounds.

**HOWEVER**, the chart-algebra HYBRID verdict (Decision 6) returns a
**stronger** finding: the entire ~680–1370 LOC scheme-Frobenius build
can be **bypassed** for M2.a-body purposes by the chart-algebra route,
which absorbs ~150–300 LOC into piece (ii) scope. The chart-algebra
route is the **dominant LOC-saver**.

## Net recommendation

This analogist's finding is **structurally identical** to the iter-140
`direct-chart-algebra-rigidity-ib-ic.md` Decision 4 finding, but with
sub-piece LOC scoping that the iter-140 file did not have:

| Path | LOC for piece (iii) only | LOC absorbed into piece (ii) | Total |
|---|---|---|---|
| In-tree scheme-Frobenius (sub-pieces 1–4) | 680–1370 LOC | 300–600 LOC (piece (ii) unchanged) | **980–1970 LOC** |
| In-tree scheme-Frobenius PR-shaped (sub-pieces 1+3 only) + named-gap on sub-piece 4 | 200–420 LOC | 300–600 LOC (piece (ii) unchanged; one residual named gap) | **500–1020 LOC** |
| Chart-algebra (no scheme-Frobenius) | 0 LOC | 450–900 LOC (piece (ii) inflated by ~150–300 chart-Frobenius) | **450–900 LOC** |
| Named-gap-sorry only (no chart-algebra, no scheme-Frobenius) | 0 LOC (one residual named gap on piece (iii) consumer) | 300–600 LOC (piece (ii) unchanged) | **300–600 LOC + one named gap** |

The honest cost ordering is:
1. Named-gap-sorry only: 300–600 LOC, residual named gap.
2. Chart-algebra: 450–900 LOC, no residual named gap.
3. PR-shaped scheme-Frobenius (sub-pieces 1+3) + named-gap on sub-piece 4: 500–1020 LOC, residual named gap, but two off-loop Mathlib-PR contributions.
4. Full in-tree scheme-Frobenius (sub-pieces 1–4): 980–1970 LOC, no residual named gap, full Mathlib-PR contribution.

All four options are **below the 2000 LOC pivot threshold** for the
project's total piece (iii) obligation. The pivot threshold does NOT
fire under this scoping.

**Strongest recommendation**: pursue **option (2) chart-algebra**
unless (a) piece (i.b) Step 2 sub-sorry closure under bundled completes
on iter-140 with `≥ 2` sub-sorries closed (iter-140 short-term
CONTINUE_BUNDLED criterion from `direct-chart-algebra-rigidity-ib-ic.md`),
in which case option (4) remains substantively viable as a *follow-on
Mathlib-PR contribution* (off-loop, not on the active iter loop).

**Iter-144 mandatory chart-algebra-vs-bundled re-evaluation**: read
this analogy file alongside `direct-chart-algebra-rigidity-ib-ic.md`.
Both files now triangulate the same finding: chart-algebra saves
~480–1070 LOC over in-tree bundled. The pivot-trigger condition is no
longer LOC-bound (both routes are below 2000 LOC); it's a *strategic*
choice between:
- (a) chart-algebra absorption (project-internal helpers, no
  Mathlib-PR contribution for piece (iii));
- (b) in-tree scheme-Frobenius (full Mathlib-PR contribution, +~530
  LOC of bundled work);
- (c) PR-shaped scheme-Frobenius sub-pieces 1+3 + named-gap on sub-
  piece 4 (mixed strategy: Mathlib-PR contribution for the canonical
  scheme-Frobenius construction; residual named gap on the consumer
  lemma).

This is genuinely a "depends on iter-140→iter-143 outcome + how much
the project values Mathlib-PR-shape of piece (iii)" choice, not a
forced pivot.

## Severity

**high-stakes.** The verdict directly determines iter-144+ piece (iii)
build direction. The pivot threshold (2000 LOC) does NOT fire under
honest scoping, but the chart-algebra and named-gap-sorry alternatives
remain genuinely competitive, and iter-144 mandatory re-evaluation
should proceed with this analogy file as a load-bearing input.

## Per-decision summary

| Decision | Verdict |
|---|---|
| 1. `Scheme.absoluteFrobenius` def + functoriality + API | NEEDS_MATHLIB_GAP_FILL (~150–300 LOC; Mathlib-idiom-clean) |
| 2. Restriction compatibility `F_X|_U = F_U` | NEEDS_MATHLIB_GAP_FILL (~80–150 LOC; deferrable for PR) |
| 3. Iterate `iterateFrobenius_X p n` | NEEDS_MATHLIB_GAP_FILL (~50–120 LOC; trivial after sub-piece 1) |
| 4. Consumer "df=0 ⇒ f factors through F_C^n" | NEEDS_MATHLIB_GAP_FILL (~400–800 LOC; bypassable by chart-algebra) |
| 5. Parallel-API risk on `Scheme.Spec.map` | PROCEED (no parallel API; consumes Mathlib's `Spec.map` family directly) |
| 6. Chart-algebra alternative | CHART_ALGEBRA_BYPASSES_PHANTOM — genuine replacement for sub-pieces 1+2+3+4 in M2.a-body context |

## Overall verdict

**HYBRID with in-tree-build sustainable + chart-algebra dominant +
named-gap alternative below pivot threshold.**

**LOC** for full sub-pieces 1–4 in-tree: 680–1370 LOC (well below
the 2000 LOC pivot threshold). **The pivot trigger does NOT fire on
LOC grounds.**

**However**, chart-algebra absorbs piece (iii) into piece (ii) at
450–900 LOC total, saving 230–470 LOC vs in-tree bundled and avoiding
the substantial sub-piece 4 cost (~400–800 LOC). Chart-algebra is the
**LOC-dominant** route.

**Recommendation for iter-144 mandatory chart-algebra-vs-bundled
re-evaluation**:
- Read this analogy file + `direct-chart-algebra-rigidity-ib-ic.md`.
- Evaluate based on iter-140→iter-143 closure status (per existing
  STRATEGY.md schedule), with both routes confirmed below the pivot
  threshold.
- The Mathlib-PR utility of scheme-level `absoluteFrobenius` (sub-
  pieces 1+3 at ~200–420 LOC) is preserved under **either** route as
  an off-loop PR contribution; the chart-algebra route does NOT
  foreclose this.

## Persistent input for iter-144 re-evaluation

This file is the load-bearing read-input for iter-144 mandatory
chart-algebra-vs-bundled re-evaluation. Cross-reference with:
- `analogies/direct-chart-algebra-rigidity-ib-ic.md` (iter-140) —
  chart-algebra alternative scoping for piece (i.b)+(i.c) absorption.
- `analogies/p1-hedge-genus-zero-witness.md` (iter-138) — NOT-VIABLE
  verdict on the ℙ¹-hedge alternative (eliminating that branch).
- `analogies/serre-duality.md` (iter-110) — deferred named-gap on
  piece (iv) (which is the alternative consumer for char-0 case).
