# LeanAG — Scope Roadmap (condensed)

A high-level, mathematical checklist across the scope's member projects.

**Legend:**

- [x] proved / sorry-free (or, for a theme, its keystone declarations are sorry-free)
- [~] in progress (declarations exist, residual `sorry`)
- [ ] not started (no Lean yet — blueprint only, or theme not begun)

**Status snapshot** *(open `sorry` counts measured over each project's `AlgebraicJacobian/`
source tree, comments/docstrings excluded; 2026-06-22):*

| Project | Stage | Open `sorry` |
| --- | --- | --- |
| Algebraic-Jacobian-Challenge | prover | 86 ✨ |
| Cech-Cohomology | ✅ complete | 0 ✨ |
| Line-Bundle-Comparison-Iso | prover | 6 ✨ |
| Albanese | prover | 17 ✨ |
| RiemannRoch | prover | 25 ✨ |
| Quot-Foundations | ⏸️ deferred | 21 |
| GR-quot_closure | ✅ complete · merged → AJC | 0 ✨ |
| FBC-B_SNAP-chain | prover | 14 ✨ |
| 36 related-paper projects | 📝 blueprint only | 0 Lean (stub aggregators) |

> **Which related papers can be formalized now (or almost)?** See
> [Formalization-readiness ordering](#formalization-readiness-ordering--what-can-be-formalized-now-or-almost):
> five papers are **`R0` (ready now)** — `MR2223407` (Picard scheme), `MR2223407`
> (Hilbert/Quot), `MR3267585` (cohomology & base change), `MR1432198`, `MR1681097` — because
> their core obligation reduces to scope interfaces already proved sorry-free; five more are
> **`R1` (almost)**, waiting on the in-progress Albanese leg or Picard-functor close. This
> readiness axis is orthogonal to the `AJC #N` overlap ordering and follows the colleague's
> audit report (`SubProjects/RelatedPapersFormalisation/lean_mathlib_formal_audit_report.pdf`).

---

## Dependency spine

### Core algebraic-geometry engine

- `Line-Bundle-Comparison-Iso` → `Algebraic-Jacobian-Challenge` (largest leverage: unblocks the Picard / comparison-iso substrate; merges back the `A.1.c.sub` package)
- `Albanese` → `Algebraic-Jacobian-Challenge` (extracted Albanese / abelian-variety leg — Albanese universal property, codim-one & Thm 3.2 rational-map extension, Auslander–Buchsbaum/coheight bridge; merges back) ✨ 2026-06-20
- `RiemannRoch` → `Algebraic-Jacobian-Challenge` (extracted Weil-divisor / Riemann–Roch core — `O(D)`/`O(P)`, skyscraper SES, `H¹`-vanishing, RR formula, rational-curve iso; merges back) ✨ 2026-06-20
- `Cech-Cohomology` ↔ `Algebraic-Jacobian-Challenge` (the Čech `Rⁱf_*` engine is the cohomological substrate; proved sorry-free here, **merged sorry-free into the AJC tree** ✨ 2026-06-19 — all Čech MERGE-STUBs restored with the working proofs, AJC's full `lake build` is green and the capstone `cech_computes_higherDirectImage` is axiom-clean)
- `GR-quot_closure` → `Algebraic-Jacobian-Challenge` (Grassmannian-quotient representability H⁰ leg — `Grassmannian.represents`, SNAP section graded ring/module, cell-chart/glue-descent atlas; **merged sorry-free into the AJC tree** ✨ 2026-06-22 via a `union` merge, AJC `lake build` green) — originally extracted from `Quot-Foundations`
- `FBC-B_SNAP-chain` → `Quot-Foundations` (extracted work package of the Quot/Picard-representability cone; shares the SNAP section-graded-ring foundation `Picard/SectionGradedRing.lean` with `GR-quot_closure`)
- `Quot-Foundations` → `Algebraic-Jacobian-Challenge` (the H⁰ Picard-representability cone — flat base change, Grassmannian, Quot — merges back; **deferred**, active work now lives in the `GR-quot_closure` / `FBC-B_SNAP-chain` extractions)

### Related papers → AG base

**Every** related paper depends on the core engine: even where the blueprint does not yet
declare a `*_PeerDependencies` chapter, the paper cannot *state* its definitions without
the common scheme / cohomology / curve / Picard objects the scope provides. The
dependencies below are therefore **mathematical** (what the constructions require), inferred
from each paper's objects — only `MR4213770` and `MR4228499` currently pin them down with
explicit blueprint anchors. The per-paper sections give the full `Requires` / `New infra`
breakdown; this is the high-level shape.

**Shared infrastructure vocabulary** (provider in parentheses):

- **Sch** — schemes, morphisms, (quasi-)coherent sheaves *(AJC)*
- **Coh** — sheaf cohomology `H^i(X,F)` *(AJC `Scheme.HModule`)*; **Rⁱf_\*** higher direct images *(Cech-Cohomology)*
- **LB/Pic** — line bundles, invertible sheaves, Picard group, relative `Pic_{X/S}` *(AJC + Line-Bundle-Comparison-Iso)*
- **Div/RR** — Weil divisors, degree, Riemann–Roch, Euler characteristic *(AJC `RiemannRoch`)*
- **Ω** — Kähler differentials / canonical bundle `ωX` *(AJC `Cotangent`, `Differentials`)*
- **Ab/Jac** — Jacobian, abelian varieties, `Pic⁰`, Albanese *(AJC)*
- **Crv** — smooth proper curves, genus *(AJC)*
- **Grp** — group schemes `Ga`, `Gm`, `ℙ¹` *(AJC `Genus0BaseObjects`)*
- **Flat** — flat base change, generic flatness, flattening stratification *(Quot-Foundations + FBC-B_SNAP-chain)*
- **Mod** — moduli via Quot / Grassmannian, Hilbert polynomial *(Quot-Foundations + GR-quot_closure)*

**Coverage tiers** (which scope infra each paper draws on — detail per-paper below):

- **Tier 1 — Core (Sch + Coh) + a little:** MR1432198, MR1681097, MR3267585, MR4419629, MR4583777, MR4681144, MR4681148
- **Tier 2 — + curves / Picard / Jacobian / divisors / Ω:** MR0555258, MR1822457, MR2223407 (picard-scheme), MR4199442, MR4228499, MR4276287, MR4372220, MR4448992, MR4493324, MR4513142, MR4628606, MR4654610, MR4665779, MR4680514, MR4688702, MR4717077, MR4733470, MR5250499
- **Tier 3 — + moduli (Quot / Grassmannian) + flat base change:** MR2223407 (construction-hilbert-quot), MR4213770, MR4258055, MR4411733, MR4413746, MR4433079, MR4433080, MR4689373, MR4712868, MR4736527, MR4792069

**New infrastructure the scope does not yet have** (recurring across papers, would be built
once and shared): intersection theory / Chow groups / cycle classes; perverse sheaves,
characteristic cycles, nearby & vanishing cycles; motives & realizations; algebraic stacks
(incl. root stacks, Picard stack); étale fundamental group / gerbes; Galois & flat
cohomology; non-abelian Hodge theory / variations of Hodge structure; heights; vertex
algebras.

> The previously-asserted paper-to-paper edges (`MR4199442+MR4213770+MR4228499 → MR4665779`)
> remain dropped — they are not in the blueprints, and the real dependencies are on the
> shared AG base above, not on sibling papers.

---

## Algebraic-Jacobian-Challenge  *(core engine — prover stage, 86 open `sorry`)* ✨

**Goal:** the Jacobian of a smooth proper geometrically-irreducible curve — smooth of
relative dimension = genus, proper, geometrically irreducible, and the Albanese variety
(`exists_unique_ofCurve_comp`). Spine = pointed vs. unpointed; 0 project axioms.

- [x] **Kähler-differential / cotangent substrate** — `Cotangent/GrpObj`, `Cotangent/ChartAlgebra`, `Differentials` (cotangent iso, chart algebra) **sorry-free**
- [x] **Rigidity & Abel–Jacobi scaffolding** — `Rigidity`, `RigidityLemma`, `Genus`, `AbelJacobi` **sorry-free**
- [x] **Line-bundle coherence substrate** — `Picard/LineBundleCoherence`, `Picard/LineBundlePullback`, `Picard/RelPicFunctor`, `Picard/RelativeSpec` **sorry-free** (local triviality, pullback-tensor compatibility)
- [x] **Čech higher-direct-image engine (A.2.c)** — the comparison theorem `cech_computes_higherDirectImage` and `pushPull` functoriality (`pushPullFunctor`, `pushPullMap_comp`) are **proved sorry-free in `Cech-Cohomology`** and merged in **sorry-free** ✨; `cechHigherDirectImage` is sorry-free in the AJC tree. *(The Čech theorem itself has no open mathematical gap.)*
- [x] **Čech merge-back RESTORED** ✨ *(2026-06-19)* — the former **7 MERGE-STUBs** (`CechSectionIdentificationLeg` ×5, `CechToHigherDirectImage` ×2, `sorry`-ed during the merge to dodge build-time elaboration blow-ups) are now **replaced with the working proofs from `Cech-Cohomology` and build clean**: the monolithic `…Leg` was split to match the subproject (`…Mid1/Mid2/Top/Aux`) and the `cechAugmented_to_acyclicResolutionInput` iso proof was given a term-shrinking rewrite. AJC's full `lake build` is green; the AJC capstone `cech_computes_higherDirectImage` depends only on `[propext, Classical.choice, Quot.sound]`.
- [~] **Flat base change (Stacks 02KH)** — the genuinely-open Čech *consumer* still has `sorry`: `flatBaseChange_pushforward_isIso` (`FlatBaseChange`), `cech_flatBaseChange` (`CechHigherDirectImageUnconditional`). *(Not a gap in the Čech engine itself.)*
- [~] **Group schemes** — `Ga`, `Gm`, `ProjectiveLineBar` (ℙ¹) **defined**; `Genus0BaseObjects` carries **2 residual `sorry`** (`BareScheme`, `GmScaling`) *(was previously mismarked "not started")*
- [~] **Tensor/dual comparison substrate + Picard group (A.1.c.sub)** — `Picard/TensorObjSubstrate` defines `PicGroup`/`picCommGroup` and the slice-dual transport; **3 residual `sorry`** *(shared with `Line-Bundle-Comparison-Iso`)*
- [~] **Weil divisors & Riemann–Roch core** — order valuation, degree homomorphism, principal divisors, skyscraper SES (`RiemannRoch/*`, **15 `sorry`**: `RationalCurveIso`, `OcOfD`, `OCofP`, `WeilDivisor` ×3 each; `H1Vanishing` ×2; `RRFormula` ×1)
- [~] **Albanese / abelian-variety leg** — `Albanese/*` (**12 `sorry`**: `AlbaneseUP` ×7, `CodimOneExtension` ×3, `Thm32RationalMapExtension` ×2; `AuslanderBuchsbaum`, `CoheightBridge` sorry-free)
- [x] **GR/Quot representability merged from `GR-quot_closure`** ✨ *(union merge 2026-06-22)* — the relative-Grassmannian representability deliverable is now in-tree **sorry-free**: `Grassmannian.represents` (rank-`d` quotient-functor representability), `tautologicalQuotient_epi`, the section graded **ring** (`sectionGradedRing_gcommSemiring`, Stacks 01CV) and graded **module** (`sectionGradedModule_gmodule`) lanes, graded Hilbert–Serre rationality, and the Grassmannian cell-chart / glue-descent atlas. Five new sorry-free files (`Picard/GrassmannianCells`, `GlueDescent`, `GrassmannianQuot`, `GradedHilbertSerre`, `SectionGradedRing`). `QuotScheme.lean` was reconciled as a *union* (AJC's base-change cohomology lane kept; the subproject's quasi-coherent descent machinery appended). Three same-name/different-meaning collisions with the existing `TensorObjSubstrate` were resolved by renaming the imported copies (`sheafTensorObj`, `IsInvertibleGr`, `gr_pullbackObjUnitToUnit_comp`) — both implementations kept. Full `lake build` green; **0 new `sorry`**.
- [~] **Picard representability cone** — `Picard/QuotScheme` (×12: the χ-blocked `hilbertPolynomial`/`QuotFunctor`/`Grassmannian.representable` stubs + Quot endgame), `IdentityComponent` (×9), `FGAPicRepresentability` (×7), `FlatteningStratification` (×7), `Pic0AbelianVariety` (×5) *(the Grassmannian-representability substrate `Grassmannian.represents` is now sorry-free in-tree — see above)*
- [~] **Flatness & generic flatness** — flat-locus open → Noetherian stratification (`FlatteningStratification`; shared root with `Quot-Foundations`)
- [ ] **Smooth proper curves** — projectivity, normalization iso, function-field equivalence *(held: classically RR-dependent; Route C paused)*
- [ ] **Top goal: `Pic_{C/k}` representability + Jacobian = Albanese** *(once the substrate + engine themes close)*

## Cech-Cohomology  *(✅ complete — 0 open `sorry`; merged back sorry-free into AJC ✨ 2026-06-19)*

**Goal:** `cech_computes_higherDirectImage` — for a separated quasi-compact `f : X ⟶ S`,
a quasi-coherent `F`, and a finite affine open cover, the cohomology of the relative Čech
complex computes `Rⁱf_* F`. Unconditional (no enough-injectives appeal).

- [x] **Combinatorial / free Čech engine** — alternating coface complex, homotopy contraction, exactness
- [x] **Section Čech complex & localization comparison** — `AwayComparison`, `phi/phiL` naturality
- [x] **Affine acyclicity (Serre vanishing)** — tilde-vanishing ⇒ affine Čech vanishing
- [x] **Cover/nerve combinatorics** — Čech nerve, wide pullbacks, `pushPull` sigma iso, finitary-extensive distributivity
- [x] **Quasi-coherence on opens** — over-equivalences, restrict-to-basic-open, modules-over-opens equivalence
- [x] **Higher direct image & acyclicity** — injective resolutions, horseshoe lemma, pushforward acyclicity
- [x] **PushPull functoriality** — `pushPullMap` composition, leg coherence, pentagon
- [x] **Comparison theorem `cech_computes_higherDirectImage`** *(proved iter-079, 0 sorries)*

## Line-Bundle-Comparison-Iso  *(prover stage — extraction hub → Jacobian, 6 open `sorry`)* ✨

**Goal:** the comparison-isomorphism substrate giving `Pic♯_{C/k}` its abelian-group
structure (the A.1.c.sub package; merges back into the Jacobian challenge).

- [x] **Stalk-tensor / internal-hom machinery** — `TensorObjSubstrate/StalkTensor`, `PresheafInternalHom` **sorry-free**
- [x] **Slice-dual transport iso (DUAL route)** — `TensorObjSubstrate/DualInverse`, `DualInverse/SliceTransport` **sorry-free**
- [x] **Line-bundle pullback / relative Pic functor** — `LineBundlePullback`, `RelPicFunctor` **sorry-free**; seed `pullback_tensor_iso_loctriv` delivered ✨
- [x] **Bridge B2 terminal blocker** — `TensorObjInverse.restrictFunctorIsoPullback_comp_compat` is closed axiom-clean; `TensorObjInverse.lean` builds green with the blocker gone ✨
- [~] **Terminal comparison inverse** — `TensorObjInverse` (×6): B1 crux, immersion-compatibility squares, and final trivialisation restriction compatibility

## Albanese  *(prover stage — extraction → Jacobian, 17 open `sorry`)* ✨

**Goal:** the Albanese universal property of `Pic⁰` (Milne III §6 Prop 6.1, seed
`thm:albanese_universal_property`) and the rational-map-extension machinery feeding the
abelian-variety leg of the Jacobian challenge. Extracted from `Algebraic-Jacobian-Challenge`
on 2026-06-20; merges back. *(Full `lake build` green — the carve had dropped load-bearing
`Genus0BaseObjects/BareScheme` grading / `Over` / standard-smooth instances, restored from
the parent ✨ 2026-06-20.)*

- [x] **Auslander–Buchsbaum / coheight bridge** — `Albanese/AuslanderBuchsbaum`, `Albanese/CoheightBridge` **sorry-free**
- [x] **Rigidity lemma + structure-sheaf module substrate** — `RigidityLemma`, `Cohomology/StructureSheaf*` **sorry-free**
- [~] **Albanese universal property** — `Albanese/AlbaneseUP` (×7): the headline `Pic.albaneseUP` + universal-map descent
- [~] **Codim-one & Thm 3.2 rational-map extension** — `Albanese/CodimOneExtension` (×3), `Albanese/Thm32RationalMapExtension` (×2)
- [~] **FGA Picard representability slice** — `Picard/FGAPicRepresentability` (×2)
- [~] **Genus-0 base + Weil-divisor riders** — `Genus0BaseObjects/BareScheme` (×1, `projectiveLineBar_geomIrred` scaffold), `Genus0BaseObjects/GmScaling` (×1), `RiemannRoch/WeilDivisor` (×1)

## RiemannRoch  *(prover stage — extraction → Jacobian, 25 open `sorry`)* ✨

**Goal:** the Weil-divisor / Riemann–Roch core for a smooth proper curve — order valuation,
degree homomorphism, `O(D)`/`O(P)`, the skyscraper SES, `H¹`-vanishing, and the RR formula.
Extracted from `Algebraic-Jacobian-Challenge` on 2026-06-20; merges back. *(Full `lake build` green.)*

- [x] **Structure-sheaf module substrate + rigidity** — `Cohomology/StructureSheaf*`, `RigidityLemma` **sorry-free**
- [x] **`O(D)` carrier-stalk chain** — the S3 binding leaf `carrierSheaf_stalk_eq` is closed axiom-clean; `OcOfD` dropped from 11 to 6 sorries ✨
- [~] **Weil divisors and smooth-regular substrate** — `RiemannRoch/WeilDivisor` (×2), `RiemannRoch/SmoothRegular` (×1): divisor arithmetic plus the smooth-stalk regularity bridge
- [~] **`O(D)` / `O(P)` line bundles** — `RiemannRoch/OcOfD` (×6), `RiemannRoch/OCofP` (×3): carrier, cokernel, and skyscraper SES bridges
- [~] **`H¹`-vanishing & RR formula** — `RiemannRoch/H1Vanishing` (×1), `RiemannRoch/RRFormula` (×5)
- [~] **Rational-curve iso + abelian-variety rigidity** — `RiemannRoch/RationalCurveIso` (×3), `AbelianVarietyRigidity` (×1)
- [~] **Genus-0 base riders** — `Genus0BaseObjects/BareScheme` (×1), `Genus0BaseObjects/GmScaling` (×2)

## Quot-Foundations  *(⏸️ deferred — 21 open `sorry`; active work moved to subproject extractions)*

**Goal:** the Čech-independent (i = 0) leg of FGA Picard representability — flat base
change, generic flatness, and Quot/Grassmannian foundations. The Grassmannian-quotient
representability endgame and the flat-base-change/SNAP legs are carved into the sibling
extractions `GR-quot_closure` and `FBC-B_SNAP-chain` (below); proofs merge back here.
**Deferred:** the directory is parked as `Quot-Foundations-[deferred_to_subprojects]` while
the two extractions carry the active proving.

- [x] **Grassmannian construction & gluing** — `GrassmannianCells`, `GlueDescent` **sorry-free** (rank-quotient setoid, charts, transition cocycle, effective descent)
- [x] **RelativeSpec / flattening stratification** — `RelativeSpec`, `FlatteningStratification` **sorry-free**
- [x] **Graded Hilbert–Serre helper** — `GradedHilbertSerre`, `RegroupHelper` **sorry-free**
- [~] **Flat base change (degree 0)** — `Cohomology/FlatBaseChange` (×4), `FlatBaseChangeGlobal` (×1); pushforward Mayer–Vietoris / finite-generation criteria
- [~] **Tautological / universal quotient** — `GrassmannianQuot` (×3): `represents` done, `tautologicalQuotient_epi` closing
- [~] **Quot scheme** — `QuotScheme` (×4): `RepresentableBy` upgrade + Quot-representability core
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×9): cast coherence → Hilbert polynomial *(shared with the sibling extractions)*

## GR-quot_closure  *(✅ complete — 0 open `sorry`; core deliverable merged back sorry-free into AJC ✨ 2026-06-22)*

**Goal:** representability of the relative Grassmannian — the Čech-independent (H⁰) leg that
builds `Grass(V, d)` from affine charts via the `GL_d` cocycle and proves it represents the
rank-`d`-quotient functor. Extracted from `Quot-Foundations`. **Merged back into
`Algebraic-Jacobian-Challenge` ✨ 2026-06-22** (union merge): the five sorry-free files +
`Grassmannian.represents` + the SNAP graded ring/module lane are now in the AJC tree, AJC
`lake build` green. *(The configured `enrich` scope was a no-op — all shared declarations
were identical or target-stronger — so the merge ran as a `union` to carry the real,
non-shared deliverable; three `Scheme.Modules.*` name collisions resolved by renaming the
imported copies.)*

- [x] **Grassmannian cells, gluing & descent** — `GrassmannianCells`, `GrassmannianQuot`, `GlueDescent`, `GradedHilbertSerre`, `RelativeSpec` **sorry-free** *(now also in AJC)*
- [x] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` **sorry-free** through the graded ring and module stretch ✨ *(now also in AJC)*
- [x] **Quot scheme** — `QuotScheme` **sorry-free** ✨ *(2026-06-22)*: the four χ-blocked endgame stubs (`hilbertPolynomial`, `QuotFunctor`, the `Grassmannian` functor def, `Grassmannian.representable` — the Hilbert-polynomial/χ formulation, distinct from the proved `Grassmannian.represents`) were **removed** from this leg, since they need the cohomology / Euler-characteristic engine that is out of scope for the H⁰ Grassmannian deliverable; the file's sorry-free quasi-coherent-descent machinery is retained and `lake build` is green (8317 jobs). *(The same stubs still live in the AJC tree's own `Picard/QuotScheme` copy — see the AJC §"Picard representability cone" line — and remain open there.)*

## FBC-B_SNAP-chain  *(prover stage — 14 open `sorry`)* ✨

**Goal:** the flat-base-change (FBC-B) leg of the Quot/Picard-representability cone, sharing the
SNAP section-graded-ring foundation with `GR-quot_closure`. *(Lean scaffolding has been
generated — this is no longer an empty extraction skeleton.)*

- [x] **Regroup helper** — `Cohomology/RegroupHelper` **sorry-free**
- [x] **FBC ring-square mate legs** — geometric and algebraic mate legs in `Cohomology/FlatBaseChange` are closed axiom-clean ✨
- [~] **Flat base change (FBC-B)** — `Cohomology/FlatBaseChange` (×4), `FlatBaseChangeGlobal` (×4): pushforward flat base-change leg
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×6): shared foundation with `GR-quot_closure`

---


## Related papers  *(📝 blueprint stage — scaffold blueprints at varying depth; Lean formalization not begun)*

All 36 related-paper projects below are blueprint-only: their Lean targets are stub
aggregators (0 real declarations), so every Lean item is `[ ]`.

> **Blueprints are NOT complete.** Each is a **scaffold / overview** of its (often 50–150-page)
> source paper — it states the main theorems and principal definitions at varying depth, not a
> full proof-level decomposition. The per-paper *Blueprint:* line gives the actual depth
> (chapters / statements / proof sketches). In particular **8 papers are skeletons whose Lean
> targets are all `TODO` placeholders** (MR4411733, MR4448992, MR4583777, MR4628606, MR4681144,
> MR4681148, MR4688702, MR4712868) — e.g. MR4628606 (rank AJC #1) is a single 887-line chapter
> with 27 statements, all targets `TODO`, for a 122-page paper. A few are genuinely developed
> (MR4199442: 7 chapters / 88 statements; MR4736527: 8 / 76; MR4276287: 9 / 56). The
> "complete blueprint" wording inside some chapter files is autoformalizer boilerplate, not a
> completeness claim.

The checklist items track the **blueprint chapters / main-theorem structure**. Each paper's
checklist starts with two infrastructure items, then its blueprint chapters:

- **`[~]` Requires (scope)** — existing AG-base anchors it builds on (vocabulary from the
  Dependency-spine table above); marked `[~]` because that infra is itself in progress
  (per-project status in the sections above). **Inferred from the mathematics** — what the
  paper's objects and lemmas need — except where marked *(explicit anchors)*.
- **`[ ]` New infra** — objects/theories the scope does **not** yet have, that this paper would
  force us to build (and which would then be shared across siblings that need them).

**Three orthogonal axes.** Each paper heading now carries three tags; do not conflate them.

- **`AJC #N` — overlap.** Sorts by **(indirect) contribution to the Jacobian challenge**:
  `AJC #1` formalizes infrastructure that most overlaps what AJC itself needs (relative
  Picard / Abel–Jacobi, Riemann–Roch, Čech `Rⁱf_*`, Quot-representability, abelian
  varieties); the last entries are mathematically farthest from AJC.
- **`tier N` — breadth.** How much of the shared-vocabulary table the paper touches; *not*
  AJC-proximity.
- **`Rn` — formalization readiness (NEW).** Can the paper's *core technical obligation* be
  written as a compiling Lean statement (and partially proved) **right now**, given the
  current scope infra? `R0` ready now · `R1` almost (waits on a scope leg already in
  progress) · `R2` has interface tasks but the core needs major new infra · `R3` not yet
  suitable. This is the axis that answers the question "what can we start today," and it is
  **orthogonal to — and often inverted from — `AJC #N`.**

> **The inversion is the headline.** The bare-skeleton interface papers `MR2223407` (Picard
> scheme), `MR2223407` (Hilbert/Quot) and `MR3267585` (cohomology & base change) sit at
> **`AJC #27–31`** (low overlap by the old ordering) yet are **`R0`** — because their core
> obligation reduces to interfaces the scope has *already built sorry-free* (relative Picard
> functor + tensor-pullback coherence; `Grassmannian.represents`; the Čech `Rⁱf_*` engine).
> Conversely `MR4628606` is **`AJC #1`** (highest overlap) yet **`R3`** — its core needs the
> full Picard *stack* + double-ramification cycles, which the scope does not have. A
> developed blueprint (e.g. `MR4199442`, 88 statements) is *less* ready than a one-line
> skeleton whose obligation is already a green Lean lemma. **Readiness, not blueprint depth
> or AJC-overlap, decides what to formalize next.**

### Formalization-readiness ordering — what can be formalized now (or almost)

This ranking, and the audit-task IDs (`T01–T28`) and priorities (`P0–P2`) it cites, follow
the colleague's audit report
(`SubProjects/RelatedPapersFormalisation/lean_mathlib_formal_audit_report.pdf`, 2026-06-16).
Its thesis: the high-value, low-risk output is **not** end-to-end paper formalization but
small **source-grounded, reusable formal-audit tasks** — a Lean statement (proof may be
`sorry`) with an *exact* hypothesis list. The tasks below are stated against scope infra that
has advanced since the report (Čech `Rⁱf_*` and Grassmannian representability are now merged
into AJC sorry-free), so several obligations the report rated "readiness 2/3" are now `R0`.

**`R0` — ready now** *(core obligation = an interface the scope already proved sorry-free, or pure Mathlib algebra)*

| Paper | Core auditable obligation | Unblocked by (scope deliverable) | Audit tasks (`P`) |
| --- | --- | --- | --- |
| **MR2223407** *The Picard scheme* | relative Picard functor + pullback-tensor functoriality / `Pic` quotient (representability black-boxed) | AJC `Picard/RelPicFunctor`, `LineBundleCoherence` sorry-free; `Line-Bundle-Comparison-Iso` tensor-pullback substrate | T01–T03, T07, T27 (P0) |
| **MR2223407** *Construction of Hilbert and Quot* | Quot-functor functoriality + Quot/Grassmannian representability **interface** | AJC `Grassmannian.represents` sorry-free (merged 2026-06-22) | T13–T15 (P0) |
| **MR3267585** *Cohomology and base change* | cohomology/base-change **theorem registry** + naturality of the base-change map | Čech `cech_computes_higherDirectImage` + `pushPull` functoriality sorry-free | T16, T17 (P0) |
| **MR1432198** *Intersection number, punctual Hilbert* | the intersection-number result as a polynomial / finite-sum identity | Mathlib algebra (no AG infra needed) | T19, T20 (P2) |
| **MR1681097** *Chern classes of tautological sheaves* | the Chern-class generating function as a formal-power-series equality | Mathlib `PowerSeries` / graded algebra | T20 (P2) |

**`R1` — almost** *(waits on an AJC leg currently being proved)*

| Paper | Core auditable obligation | Waiting on | Audit tasks (`P`) |
| --- | --- | --- | --- |
| **MR5250499** *Albanese base change* | Albanese universal property under separable base change + purely-inseparable caveat checker | `Albanese/*` (17 `sorry`, in progress) | T24, T25 (P0) |
| **MR4680514** *Para-abelian / Albanese maps* | Albanese-map functoriality + field-extension / descent | Albanese leg + `Descent of equality` (T05) | T24, T05 (P1) |
| **MR4733470** *Albanese maps, open spaces* | Albanese functoriality & base change | Albanese leg | T24 (P1) |
| **MR0555258** *Compactifying the Picard scheme* | relative-Picard base-change + degree bookkeeping (compactification black-boxed) | Picard functor (`R0`) + descent | T04, T21, T22 (P1) |
| **MR1822457** *Compactifying the relative Jacobian* | degree/multidegree bookkeeping + base change of the relative Jacobian | Picard functor + RR degree map | T08, T21 (P1) |

**`R2` — interface tasks extractable, core needs major new infra.** `MR4654610` (its
Huybrechts–RR *polynomial* is an `R0` heavy-computation benchmark; the classification needs
hyper-Kähler / BBF infra), `MR4213770` (Requires already built — Čech `Rⁱf_*`, pushforward
base change, stalkwise module-iso — blocked on Koszul/syzygy `K_{p,q}`), `MR4258055`
(degeneracy-locus / Quot interface ready; blocked on `ℙ¹`-splitting + Hurwitz space +
deformation theory), `MR4513142` (Picard-scheme / base-change interface ready; blocked on
Enriques classification + Brauer + flat cohomology).

**`R3` — not yet suitable.** The remaining 22 papers: their core needs infra the scope does
not have (motives / Chow groups, perverse sheaves & characteristic cycles, algebraic stacks,
heights, vertex algebras, Shimura varieties, D-modules, perfectoid / flat cohomology, etc.).
They remain valuable as **interface-specification** and **hidden-hypothesis audit** targets —
just not as short-term Lean proofs.

**The colleague's five recommended pilot directions** (all `R0`/`R1`), mapped to scope deliverables:

1. **Relative Picard functor + line-bundle coherence** (T01–T04, T07, T27) → `Line-Bundle-Comparison-Iso` + AJC Picard substrate.
2. **Descent of equality after algebraic closure** (T05, T23) → Mathlib fpqc/morphism-property API; the minimal core of every "we may assume `k = k̄`" step.
3. **Cohomology & base-change theorem registry** (T16, T17) → the Čech engine; record exact hypotheses/output per cited theorem version.
4. **Hilbert/Quot/flattening as black-box interfaces** (T13–T15) → `Grassmannian.represents`; specify representability, don't reprove it.
5. **Heavy-computation microbenchmarks** (T19–T21) → Mathlib algebra; ideal AI-theorem-proving benchmark items.




### A. Closest to AJC — exercise the Picard / Jacobian / Riemann–Roch / representability + Čech cone

#### MR4628606 — Pixton's formula and Abel–Jacobi theory on the Picard stack  ·  **AJC #1**  ·  tier 2  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 27 statements, 14 proof sketches.*
**Main theorem:** Pixton's formula computes the universal twisted double-ramification cycle on the Picard stack and vanishes above codimension g.

- [~] **Requires (scope):** Crv (prestable curves); LB/Pic (Picard stack, relative `Pic`); Div/RR (Weil divisors, DR cycles); Ω (twisted differentials); Ab/Jac (Abel–Jacobi); Mod (moduli `M_{g,n}`).
- [ ] **New infra:** algebraic stacks (`Pic` stack, `M̄_{g,n}`); tautological ring & DR cycles; Pixton's formula.
- [ ] **DR cycles & prestable graphs** — double ramification cycles, decorated graphs
- [ ] **Pixton's formula & vanishing** — modular construction, vanishing above codim g
- [ ] **Twisted differentials & universal formula** — Farkas–Pandharipande Conjecture A, invariance, degree-0 universal formula

#### MR4213770 — Universal secant bundles and syzygies of canonical curves  ·  **AJC #2**  ·  tier 3  ·  **R2**
*Blueprint: overview (single chapter) — 2 ch, 48 statements, 39 proof sketches.*
**Main theorem:** generic Green's conjecture for general canonical curves (`K_{k,1}(C,ωC)=0` for general genus 2k/2k+1) and the even-genus geometric-syzygy structure theorem for K3 sections.

- [~] **Requires (scope):** Crv + Ω (canonical curves, `ωC`); LB/Pic; Coh (`H^i`) + Rⁱf_*; Flat (pushforward base change); Mod (stalkwise module-iso, Quot). *(explicit anchors)*
- [ ] **New infra:** Koszul / syzygy cohomology `K_{p,q}`, K3 surfaces, kernel bundles.
- [ ] **Peer dependencies** — Rⁱf_*, H^i scheme cohomology, pushforward base change, stalkwise module-iso *(explicit anchors)*
- [ ] **Universal secant bundles & syzygies** — universal zero locus, secant bundles, local freeness, Voisin's theorem, even-genus structure, geometric syzygy conjecture

#### MR4258055 — A refined Brill–Noether theory over Hurwitz spaces  ·  **AJC #3**  ·  tier 3  ·  **R2**
*Blueprint: overview (single chapter) — 1 ch, 21 statements, 14 proof sketches.*
**Main theorem:** for general degree-`k` genus-`g` covers, the Brill–Noether splitting locus is smooth of pure dimension `g − u(⃗e)` (empty when `u > g`).

- [~] **Requires (scope):** Crv (degree-`k` covers `C→ℙ¹`); Grp (`ℙ¹`); LB/Pic (Brill–Noether loci `W^r_d`, relative `Pic`); Div/RR (degree); Coh + Rⁱf_* (pushforward); Mod (degeneracy loci via Quot/Grassmannian).
- [ ] **New infra:** vector bundles on `ℙ¹` & splitting types; Hurwitz space; deformation theory of splitting loci.
- [ ] **Splitting types & loci** — bundles on ℙ¹, balanced bundles, expected codimension, degeneracy loci
- [ ] **Degeneration & smoothness** — elliptic pushforward, deformation-theoretic smoothness, Hurwitz conditions

#### MR4654610 — Computing Riemann–Roch polynomials and classifying hyper-Kähler fourfolds  ·  **AJC #4**  ·  tier 2  ·  **R2**
*Blueprint: overview (single chapter) — 1 ch, 29 statements, 25 proof sketches.*
**Main theorem:** every hyper-Kähler fourfold of K3^[2] numerical type is of K3^[2] deformation type (O'Grady), with explicit Huybrechts–Riemann–Roch polynomial.

- [~] **Requires (scope):** Div/RR (Riemann–Roch, Euler characteristic, Chern classes); LB/Pic; Coh + Rⁱf_* (`H^i` for RR); Ab/Jac (fibrations).
- [ ] **New infra:** hyper-Kähler manifolds; Beauville–Bogomolov–Fujiki form; Hirzebruch–Riemann–Roch / characteristic classes; Lagrangian fibrations / SYZ.
- [ ] **HK fourfolds & BBF form** — numerical/deformation types, Beauville–Bogomolov–Fujiki form, Fujiki constant
- [ ] **Riemann–Roch & Lagrangian fibrations** — Huybrechts–RR polynomial, Lagrangian fibrations, SYZ in dim 4

#### MR4665779 — A Chabauty–Coleman bound for surfaces  ·  **AJC #5**  ·  tier 2  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 45 statements, 40 proof sketches.*
**Main theorem:** the Caro–Pastén Chabauty–Coleman bound for hyperbolic surfaces in abelian varieties of Mordell–Weil rank ≤ 1, with rational/quadratic-points applications.

- [~] **Requires (scope):** Crv + Ω (`ωC` for Coleman integration); Ab/Jac (Jacobian, Albanese embedding, abelian varieties); Div/RR (divisors, symmetric square `Sym²C`); Coh.
- [ ] **New infra:** surface singularities; p-adic / Coleman integration; Chabauty–Coleman method; specialization of Néron models.
- [ ] **Geometry interfaces & packages** — curves and surface singularities, abelian varieties and specialization
- [ ] **Local Chabauty–Coleman bound** — bound over Q_p extensions, specialization to Q_p
- [ ] **Number-field transfer & applications** — rational points, density-one and symmetric-square applications

#### MR4228499 — Bounds for the stalks of perverse sheaves in characteristic p  ·  **AJC #6**  ·  tier 2  ·  **R3**
*Blueprint: developed (multi-chapter) — 5 ch, 53 statements, 31 proof sketches.*
**Main theorem:** the Massey stalk bound (stalk dim ≤ polar multiplicity of the characteristic cycle) and the Shende–Tsimerman Betti-number bound for theta-locus intersections in hyperelliptic Jacobians.

- [~] **Requires (scope):** Crv + Ω (canonical differentials); Ab/Jac (hyperelliptic Jacobian); Div/RR (Weil divisors, symmetric powers `Cⁿ`); Coh + Rⁱf_*. *(explicit anchors)*
- [ ] **New infra:** perverse sheaves; singular support & characteristic cycles; nearby & vanishing cycles; polar multiplicities.
- [ ] **Peer dependencies** — Jacobian, Weil divisors, symmetric powers Cⁿ, canonical differentials, Rⁱf_*
- [ ] **Terminology & axioms** — conical cycles, polar multiplicities, transversality; nearby/vanishing cycles, singular support, characteristic cycles (as black boxes)
- [ ] **Massey bound** — polar-multiplicity equivalences, global polar bound
- [ ] **Shende–Tsimerman application** — theta-map characteristic cycle, pushforward decomposition, explicit bound

#### MR4276287 — Uniformity in Mordell–Lang for curves  ·  **AJC #7**  ·  tier 2  ·  **R3**
*Blueprint: developed (multi-chapter) — 9 ch, 56 statements, 40 proof sketches.*
**Main theorem:** uniform bound `c^{1+ρ}` on rational points of genus-`g` curves over number fields of bounded degree (ρ = Mordell–Weil rank of the Jacobian).

- [~] **Requires (scope):** Crv; Ab/Jac (Jacobian, principal polarization, Albanese); Div/RR (heights via divisors); Mod (moduli of curves / universal Jacobian).
- [ ] **New infra:** Weil / canonical heights; moduli stack `M_g` & Torelli; arithmetic Bézout; Mordell–Lang / Manin–Mumford.
- [ ] **Moduli space & Jacobian** — moduli stack of curves, Jacobian abelian variety, principal polarization, Torelli / universal family
- [ ] **Heights & positivity** — Weil heights on varieties and abelian groups, positivity conditions
- [ ] **Arithmetic Bézout & uniform bounds** — intersection-theoretic height estimates, Northcott, Rémond bound, Raynaud–Manin–Mumford, torsion-packet bounds

#### MR4513142 — There is no Enriques surface over the integers  ·  **AJC #8**  ·  tier 2  ·  **R2**
*Blueprint: overview (single chapter) — 1 ch, 24 statements, 10 proof sketches.*
**Main theorem:** the moduli stack of Enriques surfaces over Spec(ℤ) is empty (no flat proper family over ℤ).

- [~] **Requires (scope):** LB/Pic (Picard scheme, numerically-trivial `Pic`, relative `Pic_{X/S}`); Sch (surfaces, families); Ab/Jac (genus-one / Jacobian fibrations → elliptic curves); Coh + Rⁱf_*; Flat.
- [ ] **New infra:** Enriques surfaces & their classification; Brauer group; flat / étale cohomology; genus-one fibrations.
- [ ] **Picard schemes & Enriques surfaces** — numerically trivial Picard scheme, exceptional vs non-exceptional
- [ ] **Families & reduction to ℤ** — constant Picard scheme, Minkowski/Brauer vanishing, canonical coverings
- [ ] **Nonexceptional classification** — Weierstrass/Jacobian fibrations, elimination of Kodaira symbols

#### MR2223407 — The Picard scheme  ·  **AJC #27**  ·  tier 2  ·  **R0** ✅
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Representability of the relative Picard functor for proper flat families.

- [~] **Requires (scope):** Sch, LB/Pic, Coh.
- [ ] **New infra:** relative Picard functor representability.
- [ ] **Picard functor representability** — representability theorem

#### MR0555258 — Compactifying the Picard scheme  ·  **AJC #28**  ·  tier 2  ·  **R1**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Construction and representability of the compactified Picard scheme for reduced curves.

- [~] **Requires (scope):** Sch, LB/Pic, Mod, Flat.
- [ ] **New infra:** compactified Picard functor, torsion-free rank-one sheaves.
- [ ] **Compactification of Picard** — representability and properties

#### MR1822457 — Compactifying the relative Jacobian over families of reduced curves  ·  **AJC #29**  ·  tier 2  ·  **R1**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Constructing the relative compactified Jacobian and its base-change/descent properties.

- [~] **Requires (scope):** Sch, LB/Pic, Ab/Jac, Crv.
- [ ] **New infra:** relative compactified Jacobian.
- [ ] **Relative compactified Jacobian** — construction and base change

#### MR2223407 — Construction of Hilbert and Quot Schemes  ·  **AJC #30**  ·  tier 3  ·  **R0** ✅
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Construction and representability of the Hilbert and Quot schemes for projective schemes.

- [~] **Requires (scope):** Sch, Mod, Flat, Coh.
- [ ] **New infra:** Quot functor, Hilbert polynomial, flattening stratification.
- [ ] **Representability of Quot** — Grothendieck construction

#### MR3267585 — Cohomology and base change for algebraic stacks  ·  **AJC #31**  ·  tier 1  ·  **R0** ✅
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Generalization of cohomology and base change theorems to algebraic stacks.

- [~] **Requires (scope):** Sch, Coh + Rⁱf_*.
- [ ] **New infra:** algebraic stacks, stacky cohomology.
- [ ] **Cohomology and base change** — stacky base change map

#### MR1432198 — An intersection number for the punctual Hilbert scheme of a surface  ·  **AJC #32**  ·  tier 1  ·  **R0** ✅
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Computation of the intersection number for the punctual Hilbert scheme.

- [~] **Requires (scope):** Sch, Div/RR.
- [ ] **New infra:** punctual Hilbert scheme, intersection number.
- [ ] **Intersection formula** — intersection number computation

#### MR1681097 — Chern classes of tautological sheaves on Hilbert schemes of points on surfaces  ·  **AJC #33**  ·  tier 1  ·  **R0** ✅
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** The Chern classes of tautological sheaves on Hilbert schemes of points on surfaces.

- [~] **Requires (scope):** Sch, Div/RR.
- [ ] **New infra:** Hilbert scheme of points, tautological sheaves, Chern classes.
- [ ] **Chern class formula** — generating function representation


### B. Middle — abelian varieties & moduli of bundles, with substantial off-AJC new infra

#### MR4448992 — Geometric Bogomolov conjecture in arbitrary characteristics  ·  **AJC #9**  ·  tier 2  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 40 statements, 24 proof sketches.*
**Main theorem:** small-points-dense subvarieties of abelian varieties over function fields are special (translate of an abelian subvariety by a torsion point).

- [~] **Requires (scope):** Ab/Jac (abelian varieties over function fields, `Pic⁰`, `K/k`-trace); LB/Pic + Div/RR (canonical heights via divisor classes).
- [ ] **New infra:** Chow groups & intersection theory; canonical / Néron–Tate heights; special subvarieties; Manin–Mumford.
- [ ] **Heights & small points** — naive/canonical heights, special subvarieties, K/k-trace
- [ ] **Non-proper intersections** — Chow groups, Bertini, excess locus, comparison inequality
- [ ] **Descent & reduction** — lowering transcendence degree, Yamaki reduction, Manin–Mumford application

#### MR4199442 — Standard conjectures for abelian fourfolds  ·  **AJC #10**  ·  tier 2  ·  **R3**
*Blueprint: developed (multi-chapter) — 7 ch, 88 statements, 61 proof sketches.*
**Main theorem:** the standard conjecture of Hodge type for abelian fourfolds in characteristic p (positive signature of the codimension-2 numerical intersection form).

- [~] **Requires (scope):** Ab/Jac (abelian fourfolds, `Pic⁰`); Coh + Rⁱf_* (cohomology realizations); LB/Pic + Div/RR (divisor / cycle classes).
- [ ] **New infra:** algebraic cycles, Chow groups & numerical equivalence; pure motives (Chow/numerical) and realizations (ℓ-adic, crystalline, Hyodo–Kato); intersection pairing on cycles.
- [ ] **Motives & realizations** — conventions, Chow–Künneth, Lefschetz formalism, CM structures
- [ ] **Exotic classes & quadratic forms** — exotic motives in H⁴, rank-two orthogonal motives, Hilbert symbol
- [ ] **p-adic periods & Clozel** — Hyodo–Kato realization, crystalline periods, num = ℓ-adic hom
- [ ] **Main theorem** — standard conjecture of Hodge type

#### MR4411733 — Very stable Higgs bundles, equivariant multiplicity and mirror symmetry  ·  **AJC #11**  ·  tier 3  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 33 statements, 9 proof sketches.*
**Main theorem:** classification of very stable Higgs bundles (Białynicki-Birula theory), the multiplicity formula, and mirror-symmetry (Fourier–Mukai) isomorphisms.

- [~] **Requires (scope):** Crv; LB/Pic (line bundles, spectral data); Ab/Jac (Jacobian of the spectral curve); Coh + Rⁱf_* (pushforward); Mod (moduli of Higgs bundles via Quot); Flat.
- [ ] **New infra:** Higgs bundles & the Hitchin map; `Gm`-actions / Białynicki-Birula; Fourier–Mukai / derived categories.
- [ ] **Classification & BB partition** — very stable Higgs bundles, weight decomposition
- [ ] **Multiplicity & mirror symmetry** — multiplicity formula, mirror bundle / Fourier–Mukai, equivariant Euler pairing

#### MR4736527 — Geometric local systems on very general curves and isomonodromy  ·  **AJC #12**  ·  tier 3  ·  **R3**
*Blueprint: developed (multi-chapter) — 8 ch, 76 statements, 33 proof sketches.*
**Main theorem:** on a suitably general n-pointed genus-`g` curve, the minimal rank of a non-isotrivial local system of geometric origin is ≥ `2√(g+1)` (Esnault–Kerz / Budur–Wang conjectures).

- [~] **Requires (scope):** Crv (very general pointed curves); Mod (moduli of curves & of bundles, Harder–Narasimhan via Quot/Grassmannian); Ab/Jac (abelian schemes); LB/Pic (parabolic bundles, flat connections); Coh + Rⁱf_*.
- [ ] **New infra:** isomonodromic deformation; variations of Hodge structure; parabolic Higgs bundles; Kodaira–Parshin construction.
- [ ] **Foundations & parabolic structures** — hyperbolic pointed curves, Hodge structures, very general points, parabolic bundles
- [ ] **Isomonodromy & Hodge theory** — isomonodromic deformation, variations of Hodge structure, Harder–Narasimhan filtration
- [ ] **Counterexample & main results** — Kodaira–Parshin construction, Hodge-theoretic rank bound

#### MR4712868 — Virasoro constraints on moduli of sheaves and vertex algebras  ·  **AJC #13**  ·  tier 3  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 41 statements, 10 proof sketches.*
**Main theorem:** Virasoro constraints hold for moduli of semistable sheaves on curves and on surfaces with `h^{1,0}=h^{2,0}=0`, as primary-state conditions in Joyce's vertex algebra.

- [~] **Requires (scope):** Crv + surfaces (Sch); Mod (moduli of semistable sheaves = Quot); Div/RR (Chern classes); LB/Pic; Coh + Rⁱf_*.
- [ ] **New infra:** stability & moduli of sheaves; Joyce's vertex algebra / VOAs; wall-crossing.
- [ ] **Virasoro operators & VOAs** — weight-zero descendents, vertex operator algebras, primary states
- [ ] **Joyce's vertex algebra & proof** — sheaf-theoretic vertex algebra, lattice VOA iso, wall-crossing, proof via primary states

#### MR4433080 — Hitchin fibrations, abelian surfaces and the P=W conjecture  ·  **AJC #14**  ·  tier 3  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 22 statements, 8 proof sketches.*
**Main theorem:** P=W for genus-2 curves (all rank); the conjecture on the even tautological subalgebra in all genera.

- [~] **Requires (scope):** Crv; LB/Pic; Ab/Jac (abelian surfaces, `Pic⁰`); Coh + Rⁱf_* (perverse direct images); Mod (Dolbeault / Higgs moduli, Hilbert scheme → Hilbert–Chow); Div/RR (Chern classes).
- [ ] **New infra:** Hitchin system & character variety; non-abelian Hodge; perverse & weight filtrations.
- [ ] **Setup & filtrations** — Hitchin fibration, character variety, NAH diffeomorphism, weight/perverse filtrations
- [ ] **Tautological classes & perverse sheaves** — twisted Chern character, perverse truncation/splitting
- [ ] **Abelian surfaces & genus-2 result** — Hilbert–Chow, Markman monodromy, even/odd tautological perversity

#### MR4792069 — The P=W conjecture for GL_n  ·  **AJC #15**  ·  tier 3  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 10 statements, 1 proof sketches.*
**Main theorem:** P=W for `GL_n` character varieties of smooth projective curves of genus ≥ 2 (perverse filtration = weight filtration).

- [~] **Requires (scope):** Crv; LB/Pic; Ab/Jac; Mod (moduli of Higgs bundles via Quot); Div/RR (tautological Chern classes); Coh + Rⁱf_* (perverse direct images).
- [ ] **New infra:** character variety & Hitchin system; non-abelian Hodge; perverse / weight filtrations; global Springer theory.
- [ ] **Setup & filtrations** — character varieties, Hitchin fibration, weight/perverse filtrations
- [ ] **Perversity & support** — strong perversity of tautological Chern classes, vanishing cycles, global Springer theory, parabolic support theorem
- [ ] **Comparison** — curious Hard Lefschetz, P=W comparison

#### MR4413746 — Rigid local systems and the multiplicative eigenvalue problem  ·  **AJC #16**  ·  tier 3  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 27 statements, 10 proof sketches.*
**Main theorem:** bijection between rigid irreducible unitary local systems on ℙ¹ and F-vertices of the multiplicative eigenvalue polytope; no rigid irreducibles of rank > 1 when n is prime.

- [~] **Requires (scope):** Grp (`ℙ¹`); Crv; LB/Pic (parabolic / F-line bundles, Picard cone); Mod (moduli of parabolic bundles, Schubert / Grassmannian).
- [ ] **New infra:** parabolic bundles & stability; local systems / monodromy; quantum cohomology & Schubert calculus.
- [ ] **Rigid local systems & polytope** — irreducibility, multiplicative eigenvalue vertices
- [ ] **Parabolic parametrization & duality** — F-line bundles on parabolic bundles, strange duality
- [ ] **Schubert calculus & asymptotics** — quantum Schubert calculus, GW inequalities, nearby cycles

#### MR4689373 — Higher Siegel–Weil formula for unitary groups: the non-singular terms  ·  **AJC #17**  ·  tier 3  ·  **R3**
*Blueprint: developed (multi-chapter) — 6 ch, 50 statements, 16 proof sketches.*
**Main theorem:** for Hermitian bundles on `X'`, the r-th derivative of the normalized Eisenstein series equals the degree of the special cycle (higher Siegel–Weil, non-singular terms).

- [~] **Requires (scope):** Crv; Mod (moduli of Hermitian shtukas / bundles via Quot); Div/RR (special cycles, virtual fundamental classes); Coh + Rⁱf_* (perverse direct images); Ab/Jac.
- [ ] **New infra:** shtukas; perverse sheaves & Springer theory; special cycles / virtual classes; Eisenstein series; sheaf–function dictionary.
- [ ] **Geometric side** — moduli of Hermitian shtukas, special cycles, virtual fundamental classes
- [ ] **Springer / perverse sheaves** — Hermitian Springer sheaf, perverse sheaves on Herm_2d, Weyl-group reps
- [ ] **Assembly** — sheaf–function correspondence comparison

#### MR4717077 — Canonical representations of surface groups  ·  **AJC #18**  ·  tier 2  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 25 statements, 22 proof sketches.*
**Main theorem:** any MCG-finite representation `ρ: π₁(Σ_{g,n}) → GL_r(ℂ)` with `r < √(g+1)` has finite image.

- [~] **Requires (scope):** Crv (Riemann surfaces `Σ_{g,n}`); Ab/Jac (period maps into abelian varieties); LB/Pic (Higgs / vector bundles); Coh.
- [ ] **New infra:** non-abelian Hodge theory / VHS; mapping-class-group actions; cohomological rigidity & integrality.
- [ ] **Preliminaries & non-abelian Hodge** — Birman sequence, MCG-finiteness, unitarity from VHS
- [ ] **Period maps & rank bounds** — bilinear pairings, cohomological rank bounds/vanishing
- [ ] **Main proof** — asymptotic Putman–Wieland, cohomological rigidity / integrality

#### MR5250499 — A complete answer to Albanese base change for incomplete varieties  ·  **AJC #34**  ·  tier 2  ·  **R1**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Behavior of the Albanese variety and its base change under separable/inseparable field extensions.

- [~] **Requires (scope):** Sch, Ab/Jac.
- [ ] **New infra:** Albanese base change, inseparable extensions.
- [ ] **Albanese base change** — base change compatibility theorem

#### MR4680514 — Para-abelian varieties and Albanese maps  ·  **AJC #35**  ·  tier 2  ·  **R1**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Construction of the Albanese map for proper algebraic spaces.

- [~] **Requires (scope):** Sch, Ab/Jac, Grp.
- [ ] **New infra:** para-abelian varieties, algebraic spaces.
- [ ] **Albanese map construction** — para-abelian varieties

#### MR4733470 — Albanese maps for open algebraic spaces  ·  **AJC #36**  ·  tier 2  ·  **R1**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 1 statement, 1 proof sketch.*
**Main theorem:** Construction and base change of Albanese maps for open algebraic spaces.

- [~] **Requires (scope):** Sch, Ab/Jac.
- [ ] **New infra:** open algebraic spaces, Albanese maps.
- [ ] **Open Albanese maps** — functoriality and base change


### C. Furthest — largely disjoint infrastructure (number theory, D-modules, stacks/anabelian, arithmetic statistics)

#### MR4493324 — The universal p-adic Gross–Zagier formula  ·  **AJC #19**  ·  tier 2  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 28 statements, 15 proof sketches.*
**Main theorem:** the p-adic height of the universal Heegner class over a Hida family equals the cyclotomic derivative of the p-adic L-function (with classical-point specializations).

- [~] **Requires (scope):** Ab/Jac (Shimura varieties as moduli of abelian varieties); LB/Pic + Div/RR (Heegner cycles & height pairing); Coh.
- [ ] **New infra:** Shimura varieties; automorphic / Galois representations; Bloch–Kato / Nekovář Selmer complexes; p-adic heights & L-functions.
- [ ] **Setup & Galois representations** — Shimura varieties, automorphic reps, Bloch–Kato/Nekovář Selmer complexes
- [ ] **Height pairing & Heegner classes** — p-adic height pairing, Heegner cycles, universal class over Hida families
- [ ] **Main theorems** — p-adic BBK, Gross–Zagier, universal-class interpolation

#### MR4372220 — Anticyclotomic Iwasawa theory at Eisenstein primes  ·  **AJC #20**  ·  tier 2  ·  **R3**
*Blueprint: developed (multi-chapter) — 6 ch, 34 statements, 30 proof sketches.*
**Main theorem:** structure of anticyclotomic Selmer groups / Heegner–Howard–Kolyvagin systems for rational elliptic curves at Eisenstein primes.

- [~] **Requires (scope):** Crv + Ab/Jac (elliptic curves, `Pic⁰`); LB/Pic (modular curves, CM/Heegner points as divisors); Coh.
- [ ] **New infra:** Selmer groups & Galois cohomology; Iwasawa modules; Heegner / Kolyvagin systems; p-adic L-functions.
- [ ] **Local Iwasawa & Selmer** — local Iwasawa theory, Selmer groups
- [ ] **Algebraic / analytic comparison** — algebraic and analytic Iwasawa comparison
- [ ] **Howard–Kolyvagin & main conjecture** — Kolyvagin construction, main-conjecture applications

#### MR4433079 — Intersection complexes and unramified L-factors  ·  **AJC #21**  ·  tier 3  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 21 statements, 8 proof sketches.*
**Main theorem:** for type-T affine spherical varieties, the IC function on the arc space equals a ratio of local unramified L-values.

- [~] **Requires (scope):** Crv (spectral curves); Ab/Jac (Jacobians of spectral curves); Coh + Rⁱf_* (IC sheaves, pushforward); Mod (moduli of `G`-bundles, affine Grassmannian via Grassmannian infra).
- [ ] **New infra:** arc / jet spaces; perverse sheaves & IC; geometric Satake / MV cycles; nearby cycles; Kashiwara crystals.
- [ ] **Group data & arc spaces** — reductive data, type-T condition, arc spaces, IC functions
- [ ] **Global models & central fibers** — Zastava spaces, spectral curves, Mirković–Vilonen cycles, Kashiwara crystal structure
- [ ] **Semi-smallness & dimension estimates** — semi-smallness of Zastava maps, central-fiber dimension bounds
- [ ] **IC formula & asymptotics** — nearby-cycle commutation, affine-closure formula, Plancherel decomposition

#### MR4681144 — Purity for flat cohomology  ·  **AJC #22**  ·  tier 1  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 18 statements, 12 proof sketches.*
**Main theorem:** for a Noetherian local complete intersection ring and a finite flat group scheme G, flat cohomology `H^i_m(R,G)` vanishes for `i < dim R`.

- [~] **Requires (scope):** Sch (lci rings, local schemes); Grp (finite flat group schemes generalizing `Ga`/`Gm`); Coh (local cohomology `H^i_m`); Flat (flat base change).
- [ ] **New infra:** flat & étale cohomology; perfectoid rings; absolute cohomological purity; André's lemma.
- [ ] **Absolute cohomological purity** — étale purity/semipurity, perfectoid purity
- [ ] **Perfectoid geometry & prime-to-char aspects** — integral perfectoid rings, Lefschetz hyperplane, excision, André's lemma

#### MR4681148 — Motivic invariants of birational maps  ·  **AJC #23**  ·  tier 1  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 18 statements, 6 proof sketches.*
**Main theorem:** construction of motivic invariants `c`, `c̃` for birational maps over an arbitrary field, with structure results on truncated Grothendieck groups and the graded Burnside ring.

- [~] **Requires (scope):** Sch (varieties, birational maps); Div/RR (exceptional divisors, blow-ups); LB/Pic.
- [ ] **New infra:** Grothendieck ring of varieties & Burnside ring; motivic measures; resolution / weak factorization.
- [ ] **Varieties & birational maps** — notation, exceptional sets
- [ ] **Motivic invariant & structure** — invariant `c`, truncated Grothendieck groups, birational-class structure

#### MR4688702 — On the birational section conjecture with strong birationality assumptions  ·  **AJC #24**  ·  tier 2  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 38 statements, 25 proof sketches.*
**Main theorem:** every birational Galois section of a smooth geometrically connected curve over a finitely generated field is cuspidal (BSC).

- [~] **Requires (scope):** Crv (smooth geometrically connected curves); Sch + LB/Pic (root stacks via line bundles).
- [ ] **New infra:** étale fundamental group / gerbes; root stacks (Talpo–Vistoli); Galois sections & anabelian geometry.
- [ ] **Fundamental gerbes & specializations** — étale fundamental gerbes, root-stack non-unique specializations
- [ ] **Liftable sections & main argument** — t-birationally liftable sections, specializing loops, uniqueness criteria

#### MR4583777 — Tate's thesis in the de Rham setting  ·  **AJC #25**  ·  tier 1  ·  **R3**
*Blueprint: skeleton, **Lean targets all `TODO` placeholders** — 1 ch, 32 statements, 12 proof sketches.*
**Main theorem:** a canonical DG equivalence `D^!(LLA) ≅ IndCohStar(Y)` between sheaves on the algebraic loop space and ind-coherent sheaves on a moduli of rank-1 de Rham local systems.

- [~] **Requires (scope):** Sch + Coh (coherent / quasi-coherent sheaves); Grp (`Gm` & its loop group); LB/Pic (rank-1 local systems ↔ `Gm`-bundles).
- [ ] **New infra:** loop / arc ind-schemes; ind-coherent sheaves & `t`-structures; D-modules / Weyl algebras; DG categories.
- [ ] **Loop spaces & moduli Y** — loop space LLA, rank-1 de Rham local systems, derived equalizer / gauge quotient
- [ ] **Ind-coherent sheaves** — Coh/IndCohStar, t-structure, semi-coherence
- [ ] **Spectral realization & equivalence** — Weyl-algebra convolution, main DG equivalence

#### MR4419629 — Squarefree values of polynomial discriminants I  ·  **AJC #26**  ·  tier 1  ·  **R3**
*Blueprint: overview (single chapter) — 1 ch, 49 statements, 25 proof sketches.*
**Main theorem:** the density of monic integer polynomials with squarefree discriminant exists and equals an explicit Euler product; maximal-order density is ζ(2)⁻¹.

- [~] **Requires (scope):** Sch (`Spec` of orders `ℤ[x]/(f)`); Ω (discriminant = different / ramification via Kähler differentials); Flat / étale loci.
- [ ] **New infra:** discriminant / resultant of polynomials; orders & lattices; p-adic and archimedean densities (geometry of numbers); `SO_n` invariant theory.
- [ ] **Densities & local integrals** — height/discriminant definitions, p-adic local densities
- [ ] **Invariant theory & orbit counting** — SO_n invariant theory, geometry-of-numbers (odd/even degree)
- [ ] **Main density theorems** — squarefree-discriminant and maximal-order densities, monogenic fields
