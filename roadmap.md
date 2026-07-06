# LeanAG — Scope Roadmap (condensed)

A high-level, mathematical checklist across the scope's member projects.

**Legend:**

- [x] proved / sorry-free (or, for a theme, its keystone declarations are sorry-free)
- [~] in progress (declarations exist, residual `sorry`)
- [ ] not started (no Lean yet — blueprint only, or theme not begun)

**Status snapshot** *(open `sorry` counts over each project's `AlgebraicJacobian/` source tree
via a Lean comment-stripping pass — comments/docstrings excluded; measured 2026-06-30. The two
active loops move these between pushes; the **[live dashboard](https://axeldlv00.github.io/LeanAlgebraicGeometry/)**
holds the authoritative per-node counts. **v4.31 note (repaid 2026-07-03):** the mathlib
v4.31.0 bump had introduced ~20–30 mechanical **migration-interim** `sorry`s; all are now
closed — the AJC in-tree copies (T8, commit `eed5383`), the `GR-Quot-Closure` and
`Cech-Cohomology` standalones (back-ports, both verified green end-to-end), and
`MR0555258` (migrated v4.30.0→v4.31.0, first green build). No migration debt remains.):*

| Project | Stage | Open `sorry` |
| --- | --- | --- |
| Algebraic-Jacobian-Challenge | prover | 101 ✨ |
| Cech-Cohomology | ✅ complete · merged → AJC | 0 — standalone green, v4.31-clean ✨ |
| Line-Bundle-Comparison-Iso | prover | 3 ✨ |
| Albanese | prover | 17 |
| Quot-Foundations | ⏸️ deferred | 21 |
| GR-quot_closure | ✅ complete · merged → AJC | 0 — standalone green, v4.31-clean ✨ |
| MR0555258-compactifying-picard | prover | 1 ✨ |
| 35 related-paper projects | 📝 blueprint only | 0 Lean (stub aggregators) |

---

## Dependency spine

### Core algebraic-geometry engine

- `Line-Bundle-Comparison-Iso` → `Algebraic-Jacobian-Challenge` (largest leverage: unblocks the Picard / comparison-iso substrate; merges back the `A.1.c.sub` package)
- `Albanese` → `Algebraic-Jacobian-Challenge` (extracted Albanese / abelian-variety leg — Albanese universal property, codim-one & Thm 3.2 rational-map extension, Auslander–Buchsbaum/coheight bridge; merges back) ✨ 2026-06-20
- `Cech-Cohomology` ↔ `Algebraic-Jacobian-Challenge` (the Čech `Rⁱf_*` engine is the cohomological substrate; proved sorry-free here, **merged sorry-free into the AJC tree** ✨ 2026-06-19 — all Čech MERGE-STUBs restored with the working proofs, AJC's full `lake build` is green and the capstone `cech_computes_higherDirectImage` is axiom-clean)
- `GR-quot_closure` → `Algebraic-Jacobian-Challenge` (Grassmannian-quotient representability H⁰ leg — `Grassmannian.represents`, SNAP section graded ring/module, cell-chart/glue-descent atlas; **merged sorry-free into the AJC tree** ✨ 2026-06-22 via a `union` merge, AJC `lake build` green) — originally extracted from `Quot-Foundations`
- `Quot-Foundations` → `Algebraic-Jacobian-Challenge` (the H⁰ Picard-representability cone — flat base change, Grassmannian, Quot — merges back; **deferred**, active work now lives in the `GR-quot_closure` extraction)

### Related papers → AG base

The 35 related-paper formalisations all depend on the core AG engine (schemes, cohomology,
curves, Picard) and are **blueprint-stage only**. Their per-paper `Requires` / `New infra`
breakdown, the shared-infrastructure vocabulary, coverage tiers, and the formalization-readiness
ordering now live in the dedicated **[Related-Papers roadmap](SubProjects/RelatedPapersFormalisation/roadmap.md)** ✨,
so this scope roadmap stays focused on the Jacobian-challenge critical path.

---

## Algebraic-Jacobian-Challenge  *(core engine — prover stage, 101 open `sorry`)* ✨

**Goal:** the Jacobian of a smooth proper geometrically-irreducible curve — smooth of
relative dimension = genus, proper, geometrically irreducible, and the Albanese variety
(`exists_unique_ofCurve_comp`). Spine = pointed vs. unpointed; 0 project axioms.

> **v4.31 note (repaid 2026-07-03):** the ~20–30 mechanical *migration-interim* `sorry`s from the
> mathlib v4.31.0 bump (Čech library + GR/Quot-merge files) are all closed — T8 (`eed5383`) fixed
> the AJC in-tree copies, and the fixes were back-ported to the standalones. The remaining open
> `sorry`s in AJC are genuine structural/math gaps (χ-endgame, FGA, Pic⁰ cone …), not migration debt.

- [x] **Kähler-differential / cotangent substrate** — `Cotangent/GrpObj`, `Cotangent/ChartAlgebra`, `Differentials` (cotangent iso, chart algebra) **sorry-free**
- [x] **Rigidity & Abel–Jacobi scaffolding** — `Rigidity`, `RigidityLemma`, `Genus`, `AbelJacobi` **sorry-free**
- [x] **Line-bundle coherence substrate** — `Picard/LineBundleCoherence`, `Picard/LineBundlePullback`, `Picard/RelPicFunctor`, `Picard/RelativeSpec` **sorry-free** (local triviality, pullback-tensor compatibility)
- [x] **Čech higher-direct-image engine (A.2.c)** — the comparison theorem `cech_computes_higherDirectImage` and `pushPull` functoriality (`pushPullFunctor`, `pushPullMap_comp`) are **proved sorry-free in `Cech-Cohomology`** and merged in **sorry-free** ✨; `cechHigherDirectImage` is sorry-free in the AJC tree. *(The Čech theorem itself has no open mathematical gap; the 16 `sorry`s now in the Čech library — `CechHigherDirectImage` ×7, `CechSectionIdentificationBase` ×8, `PresheafCech` ×1 — are v4.31 migration-interim, mechanical.)*
- [x] **Čech merge-back RESTORED** ✨ *(2026-06-19)* — the former **7 MERGE-STUBs** (`CechSectionIdentificationLeg` ×5, `CechToHigherDirectImage` ×2, `sorry`-ed during the merge to dodge build-time elaboration blow-ups) are now **replaced with the working proofs from `Cech-Cohomology` and build clean**: the monolithic `…Leg` was split to match the subproject (`…Mid1/Mid2/Top/Aux`) and the `cechAugmented_to_acyclicResolutionInput` iso proof was given a term-shrinking rewrite. AJC's full `lake build` is green; the AJC capstone `cech_computes_higherDirectImage` depends only on `[propext, Classical.choice, Quot.sound]`.
- [~] **Flat base change (Stacks 02KH)** ✨ *(2026-06-24, Čech route)* — `cech_flatBaseChange` (`CechHigherDirectImageUnconditional`): the top-level assembly **and all homology machinery are now sorry-free** (separated case — **no spectral sequence**: `mapHomologicalComplexHomologyIso`, flat-pullback `PreservesHomology` derived via `preservesHomologyOfExact`, `pullback_mapHC_homologyIso`). **Two** genuine open leaves remain: `pullback_preservesFiniteLimits` (flat ⇒ `g^*` left-exact — verified-reduced to presheaf-pullback left-exactness; `forget`+`sheafification` already preserve finite limits in Mathlib) and `cechComplex_baseChange_iso` (Stacks 02KG, the termwise affine base change, via the still-open `affineBaseChange_pushforward_iso` in `FlatBaseChange`). Reusable FBC-B foundations salvaged in-tree sorry-free (`Cohomology/RegroupHelper`, `Cohomology/FlatBaseChangeGlobal` prefix: `gammaTopEquivEqLocus`, `baseChangeGammaEquiv`). *(Not a gap in the Čech engine itself; full general/qcqs 02KH would additionally need the Čech-to-cohomology spectral sequence — present only abstractly in Mathlib.)*
- [x] **Group schemes** — `Ga`, `Gm`, `ProjectiveLineBar` (ℙ¹) **defined**; `Genus0BaseObjects` is **sorry-free in-tree** ✨ (the `BareScheme`/`GmScaling` riders now live only in the `Albanese` extraction)
- [~] **Tensor/dual comparison substrate + Picard group (A.1.c.sub)** — `Picard/TensorObjSubstrate` defines `PicGroup`/`picCommGroup` and the slice-dual transport; **5 residual `sorry`** (`TensorObjSubstrate` ×3 + `TensorObjSubstrate/PullbackTensorComp` ×2) *(shared with `Line-Bundle-Comparison-Iso`)*
- [~] **Weil-divisor remnant** — only `RiemannRoch/WeilDivisor` (**×2**) remains in-tree; the rest of the Riemann–Roch core left the AJC tree with the genus-0 / Route-C removal (the standalone `RiemannRoch` extraction is now obsolete)
- [~] **Albanese / abelian-variety leg** — `Albanese/*` (**12 `sorry`**: `AlbaneseUP` ×7, `CodimOneExtension` ×3, `Thm32RationalMapExtension` ×2; `AuslanderBuchsbaum`, `CoheightBridge` sorry-free)
- [x] **GR/Quot representability merged from `GR-quot_closure`** ✨ *(union merge 2026-06-22)* — the relative-Grassmannian representability deliverable is now in-tree **sorry-free**: `Grassmannian.represents` (rank-`d` quotient-functor representability), `tautologicalQuotient_epi`, the section graded **ring** (`sectionGradedRing_gcommSemiring`, Stacks 01CV) and graded **module** (`sectionGradedModule_gmodule`) lanes, graded Hilbert–Serre rationality, and the Grassmannian cell-chart / glue-descent atlas. Five new sorry-free files (`Picard/GrassmannianCells`, `GlueDescent`, `GrassmannianQuot`, `GradedHilbertSerre`, `SectionGradedRing`). `QuotScheme.lean` was reconciled as a *union* (AJC's base-change cohomology lane kept; the subproject's quasi-coherent descent machinery appended). Three same-name/different-meaning collisions with the existing `TensorObjSubstrate` were resolved by renaming the imported copies (`sheafTensorObj`, `IsInvertibleGr`, `gr_pullbackObjUnitToUnit_comp`) — both implementations kept. Full `lake build` green at merge; the v4.31 bump since then left **migration-interim `sorry`s** in these files (`SectionGradedRing` ×8, `GrassmannianQuot` ×4, `GlueDescent` ×3 — mechanical debt, not the deliverable).
- [~] **Picard representability cone** — `Picard/QuotScheme` (×14: the χ-blocked `hilbertPolynomial`/`QuotFunctor`/`Grassmannian.representable` stubs + Quot endgame), `IdentityComponent` (×9), `FGAPicRepresentability` (×7), `FlatteningStratification` (×7), `Pic0AbelianVariety` (×5) *(the Grassmannian-representability substrate `Grassmannian.represents` is now sorry-free in-tree — see above)*
- [~] **Flatness & generic flatness** — flat-locus open → Noetherian stratification (`FlatteningStratification`; shared root with `Quot-Foundations`)
- [ ] **Smooth proper curves** — projectivity, normalization iso, function-field equivalence *(held: classically RR-dependent; Route C paused)*
- [ ] **Top goal: `Pic_{C/k}` representability + Jacobian = Albanese** *(once the substrate + engine themes close)*

## Cech-Cohomology  *(✅ complete — deliverable merged sorry-free into AJC ✨ 2026-06-19; standalone fully green + sorry-free — the 16 v4.31-interim `sorry`s were closed and the full build (incl. the `CechToHigherDirectImage` capstone) verified 2026-07-03)*

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

## Line-Bundle-Comparison-Iso  *(prover stage — extraction hub → Jacobian, 3 open `sorry`)* ✨

**Goal:** the comparison-isomorphism substrate giving `Pic♯_{C/k}` its abelian-group
structure (the A.1.c.sub package; merges back into the Jacobian challenge).

- [x] **Stalk-tensor / internal-hom machinery** — `TensorObjSubstrate/StalkTensor`, `PresheafInternalHom` **sorry-free**
- [x] **Slice-dual transport iso (DUAL route)** — `TensorObjSubstrate/DualInverse`, `DualInverse/SliceTransport` **sorry-free**
- [x] **Line-bundle pullback / relative Pic functor** — `LineBundlePullback`, `RelPicFunctor` **sorry-free**; seed `pullback_tensor_iso_loctriv` delivered ✨
- [x] **Bridge B2 terminal blocker** — `TensorObjInverse.restrictFunctorIsoPullback_comp_compat` is closed axiom-clean; `TensorObjInverse.lean` builds green with the blocker gone ✨
- [~] **Terminal comparison inverse** — **3 residual `sorry`**: the keystone `trivialisation_restrict_compat` (`TensorObjInverse`, iter-103 effort-broken into 3 seams), a dead-dup stub (`TensorObjSubstrate`), and one infrastructure `sorry` (`TrivialisationRestrict`) ✨

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
- [~] **Genus-0 base + Weil-divisor riders** — `Genus0BaseObjects/BareScheme` (×1, `projectiveLineBar_geomIrred` scaffold), `Genus0BaseObjects/Points` (×1), `RiemannRoch/WeilDivisor` (×1)

## Quot-Foundations  *(⏸️ deferred — 21 open `sorry`; active work moved to subproject extractions)*

**Goal:** the Čech-independent (i = 0) leg of FGA Picard representability — flat base
change, generic flatness, and Quot/Grassmannian foundations. The Grassmannian-quotient
representability endgame is carved into the sibling extraction `GR-quot_closure` (below); the
flat-base-change leg is now pursued via the Čech route in AJC, and proofs merge back here.
**Deferred:** the directory is parked as `Quot-Foundations-[deferred_to_subprojects]` while
that extraction carries the active proving.

- [x] **Grassmannian construction & gluing** — `GrassmannianCells`, `GlueDescent` **sorry-free** (rank-quotient setoid, charts, transition cocycle, effective descent)
- [x] **RelativeSpec / flattening stratification** — `RelativeSpec`, `FlatteningStratification` **sorry-free**
- [x] **Graded Hilbert–Serre helper** — `GradedHilbertSerre`, `RegroupHelper` **sorry-free**
- [~] **Flat base change (degree 0)** — `Cohomology/FlatBaseChange` (×4), `FlatBaseChangeGlobal` (×1); pushforward Mayer–Vietoris / finite-generation criteria
- [~] **Tautological / universal quotient** — `GrassmannianQuot` (×3): `represents` done, `tautologicalQuotient_epi` closing
- [~] **Quot scheme** — `QuotScheme` (×4): `RepresentableBy` upgrade + Quot-representability core
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×9): cast coherence → Hilbert polynomial *(shared with the sibling extractions)*

## GR-quot_closure  *(✅ complete — core deliverable merged sorry-free into AJC ✨ 2026-06-22; standalone fully green + sorry-free since 2026-07-03 — the v4.31 `SectionGradedRing` red build and the 3 interim `sorry`s are closed)*

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

---

## Related papers  *(📝 blueprint stage — moved to a dedicated roadmap ✨ 2026-06-30)*

The 35 related-paper projects now live in their own roadmap to keep this file readable:
**[SubProjects/RelatedPapersFormalisation/roadmap.md](SubProjects/RelatedPapersFormalisation/roadmap.md)**.

They are blueprint-only (Lean targets are stub aggregators, 0 real declarations) and do **not**
directly contribute to the Jacobian challenge. Five are formalization-ready *now* (`R0` —
`MR2223407` Picard scheme, `MR2223407` Hilbert/Quot, `MR3267585` cohomology & base change,
`MR1432198`, `MR1681097`); the readiness ordering (`R0`–`R3`) and full per-paper catalogue are
in that roadmap.
