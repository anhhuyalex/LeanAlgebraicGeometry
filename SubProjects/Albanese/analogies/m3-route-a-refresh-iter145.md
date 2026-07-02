# Analogy: M3 Route A LOC audit refresh (iter-145)

## Slug

m3-route-a-refresh-iter145

## Iteration

145

## Question

Refresh the iter-123 Route A LOC audit (`analogies/m3-route-audit.md`)
against the current Mathlib snapshot. The iter-123 audit's midpoint
~6500 LOC underpins the iter-144 user-hint Route A commitment
(STRATEGY.md L639–656). It is 21 iters old; per `strategy-critic-iter144`
Must-fix #3 + STRATEGY.md L627, snapshot drift must be re-priced or the
~6500 LOC commitment is a sunk-cost trap.

Re-price A1 (Hilbert / QCoh / Coh / flattening, iter-123 ~4150 LOC),
A2 (Quot post-A1, iter-123 ~1400 LOC), A3 (identity-component subgroup
scheme, iter-123 ~1025 LOC) on current Mathlib.

## Project artifact(s)

- `AlgebraicJacobian/Jacobian.lean:194-215` — `positiveGenusWitness` stub
  (landed iter-134) with `sorry` body; the M3 target the refreshed
  estimate prices.
- `references/challenge.lean:63` — `nonempty_jacobianWitness` protected
  signature whose positive-genus arm `positiveGenusWitness` closes.
- `analogies/m3-route-audit.md` (iter-123) — the baseline whose numbers
  this refresh updates.
- `.archon/STRATEGY.md` § M3 (L237–294, L627, L639–656) — the iter-144
  Route A commitment + the iter-145 refresh mandate.

## Mathlib snapshot used (iter-145)

**Project pin (operational ground truth):** `b80f227` —
**UNCHANGED from iter-123**.

Verified via `lake-manifest.json:30-31`. The premise in the iter-145
directive ("Mathlib has moved forward [since iter-123]") refers to
upstream mainline movement; the project pin is identical to the snapshot
iter-123 audited. So this refresh has two distinct components:

1. **Pin re-inventory**: catch the iter-123 audit up to ground truth
   on what was *already* in `b80f227` but was not credited by
   iter-123. This is a correction of the iter-123 audit, not Mathlib
   progress per se.
2. **Mainline diff**: what has landed in `master` since `b80f227` that
   the project could obtain by bumping the pin.

The bulk of the iter-145 delta is from (1); (2) is essentially noise
for the M3 gating pieces.

### Mainline-vs-pin diff (AG directory)

Mainline `Mathlib/AlgebraicGeometry/` (verified via GitHub directory
listing at iter-145):

- **Subdirectories present in mainline but NOT in pin**: `Birational/`
- **Top-level files present in pin but NOT in mainline**:
  `RationalMap.lean` (moved into `Birational/` upstream).
- **Subdirectories present in both**: `AlgClosed`, `Cover`,
  `EllipticCurve`, `Geometrically`, `Group`, `IdealSheaf`, `Modules`,
  `Morphisms`, `ProjectiveSpectrum`, `Sites`.
- **`Group/` contents** (mainline + pin, both): `Abelian.lean`,
  `Smooth.lean`. No `Connected.lean`, no `IdentityComponent.lean`, no
  `Subgroup.lean`. **Bare**.
- **`Sites/` contents** (mainline + pin, both): no `Hilbert.lean`, no
  `Quot.lean`, no `Picard.lean`, no `Moduli.lean`. **Bare on the moduli
  axis.**

**Confirmation of absences (both pin and mainline at iter-145):**

- `HilbertScheme` / `HilbertFunctor`: no matches anywhere in `Mathlib/`.
- `QuotScheme` / `QuotFunctor`: no matches anywhere in `Mathlib/`.
- `PicardScheme` / `PicardFunctor`: no matches anywhere in `Mathlib/`
  (only `Mathlib.RingTheory.PicardGroup` — ring-level group, unchanged
  from iter-123).
- `FlatteningStratification` / `Stratification`: no matches; Stacks
  tag 052F is not referenced in `Mathlib/`.
- `identityComponent` / `IdentityComponent`: no matches in
  `Mathlib/AlgebraicGeometry/`. `Subgroup.connectedComponentOfOne`
  (topological) at `Mathlib.Topology.Algebra.Group.Basic:740` is
  unchanged from iter-123 and remains the **only** identity-component
  construction in Mathlib — still topological, not scheme-theoretic.
- `Scheme.QuasiCoherent` / `Scheme.IsCoherent` namespace: no matches.

These are the same iter-123 absences. **Mainline progress on the
load-bearing Route A gating pieces since `b80f227` is zero.**

### Pin re-inventory — what iter-123 missed

Iter-123 cited `SheafOfModules.Presentation` /
`Presentation.IsFinite` at `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:44-57`
but explicitly stated "**it is not lifted to a typeclass `QuasiCoherent`
/ `IsCoherent` on `SheafOfModules`**" (iter-123 audit, line 79). This
claim was inaccurate at the time. The same file already contained:

- **`class IsQuasicoherent (M : SheafOfModules R) : Prop`** at
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:249`. The
  typeclass *is* lifted to `SheafOfModules` over a general ringed site.
- **`class IsFinitePresentation (M : SheafOfModules R) : Prop`** at
  same file:262. Typeclass form of finite presentation.
- **`abbrev isQuasicoherent : ObjectProperty (SheafOfModules R)`** at
  same file:257 and the closed-under-iso instance at line 330.
- **`abbrev isFinitePresentation : ObjectProperty (SheafOfModules R)`**
  at same file:268.
- **`lemma IsQuasicoherent.of_coversTop`** at same file:377 — local
  characterisation already proved.

What is *not* yet lifted is the **scheme-side specialisation** —
i.e. there is no `Scheme.QuasiCoherent X` abbrev wrapping
`IsQuasicoherent` for `Scheme.ringSheaf X`, and no calibration that
identifies the abstract `IsQuasicoherent` predicate with the affine
`Tilde`-form (`Mathlib.AlgebraicGeometry.Modules.Tilde`) on affine
charts (Stacks 01BD's calibration). Iter-123's "calibration" gap stands,
but the **abstract typeclass itself is already present** and that was
the principal A1.1 LOC. The remaining work is plumbing.

Iter-123 also did not credit:

- **`class IsLocallyNoetherian (X : Scheme) : Prop`** at
  `Mathlib.AlgebraicGeometry.Noetherian:57` + `class IsNoetherian (X)
  : Prop extends IsLocallyNoetherian X, CompactSpace X` at same file:278,
  plus the affine-cover iff lemmas (lines 103, 131, 196) and the
  stalk-Noetherianness instance (line 346). This is the entire
  "Noetherian base" prerequisite for `Coherent` à la Stacks 01XZ, and
  iter-123 did not enumerate it.
- **`AlgebraicGeometry/Cover/` subdirectory** (`Open.lean`,
  `Sigma.lean`, `MorphismProperty.lean`, `Directed.lean`,
  `QuasiCompact.lean`, `Over.lean`) — the new
  `precoverage @IsOpenImmersion` abstraction (`Cover/Open.lean:40-49`)
  is the modern Mathlib idiom for the gluing data Route A's
  representability step consumes. Iter-123 did not credit this.
- **`AlgebraicGeometry/AlgClosed/Basic.lean`** — closed-point /
  K-residue identification (`residueFieldIsoBase`, `pointOfClosedPoint`,
  `pointEquivClosedPoint`) — useful for A3 base-change closures (the
  geometric-irreducibility-of-G^0 sub-piece).
- **`AlgebraicGeometry.RationalMap`** + (mainline) `Birational/` — birational
  geometry scaffolding. Not load-bearing for any of A1/A2/A3 but
  flagged for context.
- **`AlgebraicGeometry.SpreadingOut`** — spreading-out / approximation
  scaffolding; light A1 utility.

These were already present in `b80f227`; iter-123 missed them. Their
existence reduces the iter-123 estimates by the amounts itemised below.

## Decisions identified

The directive's decomposition is A1 / A2 / A3. For each, the per-piece
LOC refresh is below.

### A1 — Hilbert + QCoh + Coh + flattening (iter-123 ~3400–4900 LOC, midpoint ~4150)

#### A1.1 QuasiCoherent typeclass on `Scheme.SheafOfModules`

- **iter-123 estimate**: ~400–500 LOC.
- **Landed since iter-123 (i.e., already in `b80f227`, missed by iter-123)**:
  - `class IsQuasicoherent (M : SheafOfModules R) : Prop` —
    `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:249`
    (Role: the abstract typeclass on bundled `SheafOfModules` over a
    general ringed site).
  - `abbrev isQuasicoherent : ObjectProperty (SheafOfModules R)` at
    same file:257.
  - `lemma IsQuasicoherent.of_coversTop` at same file:377 (Role:
    local characterisation; gluing on covers).
  - `tilde.adjunction` at `Mathlib.AlgebraicGeometry.Modules.Tilde:279`
    (Role: the `M ↦ Tilde M` ⊣ `Γ` adjunction on affine charts,
    making the Tilde-side calibration tractable).
- **Still missing (NEEDS_MATHLIB_GAP_FILL, refreshed LOC)**:
  - `Scheme.IsQuasicoherent X` specialisation wrapper —
    `IsQuasicoherent` instantiated at `(Scheme.ringSheaf X).val`
    inside the small Zariski site `X.Opens`-as-`PreservesSheaves`
    structure. ~80–120 LOC of pure plumbing.
  - Affine-Tilde calibration: prove that `IsQuasicoherent M` on an
    affine `X = Spec R` is equivalent to `M ≃ tilde N` for some
    `N : ModuleCat R` (Stacks 01BD direction). Iter-123 implicitly
    folded this into the typeclass LOC; in the new landscape it is
    the *primary* outstanding A1.1 item. ~150–200 LOC (mostly
    threading the existing `tilde.adjunction` through the typeclass).
- **Refreshed A1.1 LOC**: ~230–320 LOC.
- **Net delta vs iter-123**: was ~400–500 → now ~230–320.
  **−170 to −180 LOC (−40%)**.

#### A1.2 Coherent sheaves + finite-presentation equivalence on Noetherian base

- **iter-123 estimate**: ~300–400 LOC.
- **Landed since iter-123 (already in `b80f227`, missed by iter-123)**:
  - `class IsFinitePresentation (M : SheafOfModules R) : Prop` —
    `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:262`.
  - `class IsLocallyNoetherian (X : Scheme) : Prop` —
    `Mathlib.AlgebraicGeometry.Noetherian:57`.
  - `class IsNoetherian (X : Scheme) : Prop extends
    IsLocallyNoetherian X, CompactSpace X` — same file:278.
  - `instance [IsLocallyNoetherian X] {x} : IsNoetherianRing
    (X.presheaf.stalk x)` — same file:346.
  - `theorem LocallyOfFiniteType.isLocallyNoetherian` — same file:237
    (Role: inheritance from `IsLocallyOfFiniteType` plus
    Noetherianness of the base).
- **Still missing (NEEDS_MATHLIB_GAP_FILL, refreshed LOC)**:
  - `Scheme.IsCoherent (M : (Scheme.ringSheaf X).Modules) : Prop` —
    the predicate "finitely generated and every locally finitely
    generated subsheaf is finitely presented" (Stacks 01XZ). ~100–150
    LOC.
  - **Equivalence on a Noetherian base**: `IsCoherent ↔
    IsQuasicoherent ∧ IsFinitePresentation` when
    `IsLocallyNoetherian X` (Stacks 01XZ.4 / 01XH). ~50–100 LOC
    (depends on the previous; mostly using already-present
    `IsLocallyNoetherian` instances).
- **Refreshed A1.2 LOC**: ~150–250 LOC.
- **Net delta vs iter-123**: was ~300–400 → now ~150–250.
  **−150 LOC (−43%)**.

#### A1.3 Flatness on `SheafOfModules`

- **iter-123 estimate**: ~200–300 LOC.
- **Landed since iter-123**: none on the *sheaf* side. The morphism-side
  `class Flat (f : X ⟶ Y)` at `Mathlib.AlgebraicGeometry.Morphisms.Flat:42`
  was already credited by iter-123. `FlatDescent.lean` /
  `FlatMono.lean` are new since iter-123's enumeration but address
  descent / monomorphism interactions, not lift-to-sheaves.
- **Still missing**: the entire sheaf-side `IsFlat M` typeclass; the
  Flat-locus formation; pullback-flatness on `SheafOfModules.pullback`.
  Iter-123's estimate stands.
- **Refreshed A1.3 LOC**: ~200–300 LOC. **Delta: 0**.

#### A1.4 Hilbert functor

- **iter-123 estimate**: ~400–600 LOC.
- **Landed since iter-123**: none. No `HilbertFunctor` / `HilbertScheme`
  anywhere in pin or mainline. Stacks 0DPA / 0DPB not referenced.
- **Refreshed A1.4 LOC**: ~400–600 LOC. **Delta: 0**.

#### A1.5 Grothendieck flattening stratification (Stacks 052F / 0BFR)

- **iter-123 estimate**: ~1500–2200 LOC. The single largest
  Route A line item.
- **Landed since iter-123**: none. `Stratification` / `FlatLocus` /
  `Flattening` not present anywhere in `Mathlib/`. Stacks 052F not
  referenced.
- **Refreshed A1.5 LOC**: ~1500–2200 LOC. **Delta: 0**.

#### A1.6 Hilbert scheme representability for `ℙ^N`

- **iter-123 estimate**: ~600–900 LOC.
- **Landed since iter-123**: none on the representability theorem
  itself. The new `Cover/Open.lean:40` `precoverage @IsOpenImmersion`
  abstraction and the existing
  `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
  (`...Sites.Representability:201`) remain the tools. ~50 LOC of
  modernisation savings from the newer `precoverage` idiom.
- **Refreshed A1.6 LOC**: ~550–850 LOC. **Delta: −50 LOC (−7%)**.

#### A1 subtotal

| Sub-piece | iter-123 LOC | iter-145 LOC | Delta |
|---|---|---|---|
| A1.1 QCoh typeclass on `Scheme.SheafOfModules` | 400–500 | 230–320 | −170 to −180 |
| A1.2 Coherent + finite-presentation equivalence | 300–400 | 150–250 | −150 |
| A1.3 Flatness on `SheafOfModules` | 200–300 | 200–300 | 0 |
| A1.4 Hilbert functor | 400–600 | 400–600 | 0 |
| A1.5 Flattening stratification | 1500–2200 | 1500–2200 | 0 |
| A1.6 Hilbert representability for `ℙ^N` | 600–900 | 550–850 | −50 |
| **A1 total** | **3400–4900** | **3030–4520** | **−370 to −380** |

- **A1 midpoint**: iter-123 ~4150 → iter-145 ~3775. **−375 LOC (−9%)**.
- Verdict: within ±20%, audit STABLE on A1.

### A2 — Quot scheme representability (post-A1) (iter-123 ~1100–1700 LOC, midpoint ~1400)

#### A2.1 Quot functor

- **iter-123 estimate**: ~400–600 LOC.
- **Landed since iter-123**: none. No `QuotFunctor` / `QuotScheme`
  anywhere in pin or mainline.
- **Refreshed A2.1 LOC**: ~400–600 LOC. **Delta: 0**.

#### A2.2 Sheaf condition + flattening reuse

- **iter-123 estimate**: ~300–500 LOC.
- **Landed since iter-123**: marginal. The `IsQuasicoherent` typeclass
  now-credited under A1.1 makes the bookkeeping around "quotient of a
  fixed coherent sheaf F" slightly simpler — `IsQuasicoherent` is the
  predicate the quotient inherits, and is now an already-defined
  typeclass to invoke rather than open-coded.
- **Refreshed A2.2 LOC**: ~250–450 LOC.
  **Delta: −50 LOC (−13%)**.

#### A2.3 Representability via local data + Hilbert

- **iter-123 estimate**: ~400–600 LOC.
- **Landed since iter-123**: same A1.6 modernisation savings from
  `precoverage @IsOpenImmersion` apply here. ~30 LOC.
- **Refreshed A2.3 LOC**: ~370–570 LOC. **Delta: −30 LOC (−6%)**.

#### A2 subtotal

| Sub-piece | iter-123 LOC | iter-145 LOC | Delta |
|---|---|---|---|
| A2.1 Quot functor | 400–600 | 400–600 | 0 |
| A2.2 Sheaf condition + flattening reuse | 300–500 | 250–450 | −50 |
| A2.3 Representability via local data + Hilbert | 400–600 | 370–570 | −30 |
| **A2 total** | **1100–1700** | **1020–1620** | **−80** |

- **A2 midpoint**: iter-123 ~1400 → iter-145 ~1320. **−80 LOC (−6%)**.
- Verdict: within ±20%, audit STABLE on A2.

### A3 — Identity-component `G^0 ⊆ G` as closed subgroup scheme (iter-123 ~850–1200 LOC, midpoint ~1025)

#### A3.1 Connected components of `G.left` are open

- **iter-123 estimate**: ~150–200 LOC.
- **Landed since iter-123**: none directly. `AlgebraicGeometry.Group.Smooth:38`
  (`smooth_of_grpObj_of_isAlgClosed`) was already credited by iter-123.
- **Refreshed A3.1 LOC**: ~150–200 LOC. **Delta: 0**.

#### A3.2 Identity component as reduced closed subscheme

- **iter-123 estimate**: ~200–300 LOC.
- **Landed since iter-123**: none.
- **Refreshed A3.2 LOC**: ~200–300 LOC. **Delta: 0**.

#### A3.3 Group-scheme structure on `G^0`

- **iter-123 estimate**: ~300–400 LOC.
- **Landed since iter-123**: none on the identity-component side. The
  `GrpObj` infrastructure (`Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_`)
  was already credited by iter-123.
- **Refreshed A3.3 LOC**: ~300–400 LOC. **Delta: 0**.

#### A3.4 Geometric irreducibility / smoothness inheritance

- **iter-123 estimate**: ~200–300 LOC.
- **Landed since iter-123**: `AlgebraicGeometry/AlgClosed/Basic.lean`
  (`residueFieldIsoBase`, `pointOfClosedPoint`, `pointEquivClosedPoint`)
  modestly simplifies the base-change-to-`k̄` closure. Iter-123 had to
  envelope this manually; iter-145 can use the existing K-point /
  residue identification. ~40–60 LOC saving.
- **Refreshed A3.4 LOC**: ~160–240 LOC. **Delta: −40 to −60 LOC (−18%)**.

#### A3 subtotal

| Sub-piece | iter-123 LOC | iter-145 LOC | Delta |
|---|---|---|---|
| A3.1 Connected components are open | 150–200 | 150–200 | 0 |
| A3.2 Identity component as reduced closed subscheme | 200–300 | 200–300 | 0 |
| A3.3 Group-scheme structure on `G^0` | 300–400 | 300–400 | 0 |
| A3.4 Geometric irreducibility / smoothness inheritance | 200–300 | 160–240 | −40 to −60 |
| **A3 total** | **850–1200** | **810–1140** | **−40 to −60** |

- **A3 midpoint**: iter-123 ~1025 → iter-145 ~975. **−50 LOC (−5%)**.
- Verdict: within ±20%, audit STABLE on A3.

### Route A cumulative refresh

| Piece | iter-123 LOC range | iter-145 LOC range | iter-123 midpoint | iter-145 midpoint | Delta on midpoint |
|---|---|---|---|---|---|
| A1 | 3400–4900 | 3030–4520 | 4150 | 3775 | −375 (−9%) |
| A2 | 1100–1700 | 1020–1620 | 1400 | 1320 | −80 (−6%) |
| A3 | 850–1200 | 810–1140 | 1025 | 975 | −50 (−5%) |
| **Total** | **5350–7800** | **4860–7280** | **~6500** | **~6070** | **−430 (−7%)** |

## Overall verdict

**AUDIT_STABLE.** The iter-145 refresh delta on every piece (A1, A2,
A3) is well inside ±20%, so on the directive's verdict scale the
iter-123 audit's midpoint estimates remain operationally valid.

- A1: −9% midpoint (within ±20%);
- A2: −6% midpoint (within ±20%);
- A3: −5% midpoint (within ±20%);
- Route A total midpoint: ~6500 → ~6070 LOC (−7%).

The refreshed numbers should replace the iter-123 numbers in
forward-looking planning, but the order of magnitude — and crucially,
the multi-year wall-clock implication of ~6000+ LOC — is unchanged.

## Sub-findings to surface

1. **Mainline Mathlib progress on the M3-gating sub-pieces since
   `b80f227` is essentially zero.** No HilbertScheme, no
   QuotScheme, no PicardScheme, no `Coherent` typeclass, no
   FlatteningStratification, no IdentityComponent on group schemes
   has landed in `master`. The A1.5 flattening-stratification piece
   (~1500–2200 LOC alone, by far the largest single line item) shows
   no upstream activity; this is the load-bearing risk for the
   multi-year timeline.

2. **The bulk of the −430 LOC refresh delta is from iter-123
   undercount, not Mathlib motion.** Iter-123 missed the
   `IsQuasicoherent` / `IsFinitePresentation` typeclasses already
   present in `b80f227` at
   `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:249,262`,
   and missed the `IsLocallyNoetherian` / `IsNoetherian` typeclasses
   on `Scheme` at `Mathlib.AlgebraicGeometry.Noetherian:57,278`.
   These reduce A1.1 + A1.2 by ~320 LOC at midpoint. The other ~110
   LOC of delta comes from the `precoverage @IsOpenImmersion`
   abstraction modernisation (A1.6, A2.3) and the
   `AlgClosed/Basic.lean` K-point identification helpers (A3.4).

3. **`Scheme.QuasiCoherent X` specialisation is the cheapest A1
   entry point.** With the bundled `IsQuasicoherent` typeclass on
   `SheafOfModules R` already present, the scheme-side wrapper
   (~80–120 LOC) plus the affine-Tilde calibration (~150–200 LOC)
   together total ~230–320 LOC of mostly definitional plumbing.
   This is the lowest-LOC starting point for any Route A in-tree
   work and is recommended as the first A1 lane the planner
   schedules.

4. **The directive's hypothetical "Hilbert representability has
   landed at `Mathlib.AlgebraicGeometry.Hilbert.Representability`"
   is FALSE.** No such file exists in either pin or mainline; no
   `Hilbert*` file exists under `Mathlib/AlgebraicGeometry/`.
   STRATEGY.md L627 should NOT cite that path as landed.

5. **Sunk-cost-trap guardrail (STRATEGY.md L627) is honored.** The
   iter-145 refresh was dispatched in iter-145 (well before the
   iter-150 deadline). The refreshed Route A ~6070 LOC midpoint
   does not falsify the iter-144 commitment; the route remains
   ~6× the historical 5000-LOC threshold and multi-year. No
   pivot is triggered by this refresh.

## Recommendation

The iter-144 Route A commitment is preserved. The planner should:

1. **Use the iter-145 refreshed numbers** in any forward-looking LOC
   accounting (A1 ~3775 / A2 ~1320 / A3 ~975 / total ~6070 LOC at
   midpoint), not the iter-123 numbers.

2. **Continue with the iter-138 in-tree-no-PR-lane disposition**
   (STRATEGY.md L639–656). The refreshed numbers do not change the
   in-tree-vs-PR-extraction choice.

3. **Order A1 sub-pieces by entry-cost when scheduling**: `Scheme`-side
   `IsQuasicoherent` specialisation (~230–320 LOC, A1.1) → coherent
   typeclass + Stacks 01XZ equivalence (~150–250 LOC, A1.2) →
   `RelativeSpec` (~700–1100 LOC, already flagged STRATEGY.md L638) →
   sheaf-side flatness (~200–300 LOC, A1.3) → Hilbert functor (~400–600
   LOC, A1.4). Defer A1.5 flattening (~1500–2200 LOC) — the largest
   single item — until the prerequisites land, since its proof depends
   on the coherent / Noetherian / flat infrastructure above.

4. **Set a re-refresh tripwire**. Re-dispatch this audit at iter-170
   (≈ 25 iters out, matching the iter-123→iter-145 cadence), OR
   earlier if any of HilbertScheme / QuotScheme / Coherent /
   FlatteningStratification / IdentityComponent lands in mainline.
   The simplest tripwire is a one-line `grep` of mainline
   `Mathlib/AlgebraicGeometry/` for `Hilbert`, `Quot`, `Coherent`,
   `Flattening`, `IdentityComponent` — anything matching triggers a
   fresh `mathlib-analogist` refresh.

5. **Do not** treat the −430 LOC midpoint delta as "Route A is cheaper
   now" — it is "iter-123 was conservative by ~7% even at the time of
   writing". The iter-145 numbers are a tighter baseline, not an
   easier target.
