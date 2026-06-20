# Strategy

## Goal

Close the `sorry`-bearing nodes of the **Čech-independent leg** of the parent's
`thm:fga_pic_representability` cone (Kleiman FGA, "The Picard scheme", §4), then merge back:

- **FBC** — `lem:affine_base_change_pushforward` + `thm:flat_base_change_pushforward`
  (the i=0 base-change map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism).
- **GF** — `thm:generic_flatness` with algebraic core `thm:generic_flatness_algebraic` (DONE).
- **QUOT** — `def:grassmannian_scheme`, `thm:grassmannian_representable` (χ-independent core).
  NOTE (verified iter-081): the parent's `def:hilbert_polynomial` / `def:quot_functor` are
  **χ-semantic** (`Φ(m)=χ(F(m))=Σᵢ(-1)ⁱ dim Hⁱ`) and need the sibling cohomology leg's χ engine —
  this i=0 / Čech-independent leg does NOT faithfully close them (see Q1). It owes only the
  χ-independent core: the Grassmannian construction + representability via rank-d locally-free
  quotients (Hilbert condition ⇒ constant rank), backed by the H⁰ graded ring `Γ_*(X,L)`.

End-state: zero project `sorry` in the 29-node closure, zero project axioms, kernel-only axioms.
Names/labels are the parent's so finished work merges back into its A.2.c engine.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---|---|---|---|
| FBC-B i=0 via Stacks 02KH(2) equalizer | ACTIVE‖ | 2–4 | ~250–500 | flat preserves finite equalizer | `baseChangeGammaPullbackEquiv` stub landed iter-081 (analogist-verified sig); residue = fork assembly + discharge 2 frozen named legs |
| GR-quot/repr — taut. quotient + representability | ACTIVE‖ | 2–5 | ~300–700 | effective descent for `SheafOfModules`; `Functor.RepresentableBy` | Residue = `tautologicalQuotient_epi` (last sorry) + `represents` |
| SNAP-S0 — section graded ring | ACTIVE | 1–3 | ~120–300 | `DirectSum.Ring` assembly | Builds the H⁰ object `Γ_*(X,L)`; residue = cast-coherence + graded assembly |
| RelativeSpec — `RepresentableBy` upgrade | NEXT | 3–6 | ~200–500 | relative Spec of a sheaf of algebras (Mathlib-absent) | Independent of GR-quot/SNAP; gated on Q4 tag retrieval; chapter prose DONE, Lean is `IsAffineHom` (weaker) |
| QUOT-repr core — Grass scheme + representability | BLOCKED | 3–6 | ~150–350 | `Modules.pullback` packaging; rank-d locally-free quotient | χ-INDEPENDENT core only (Q1); needs SNAP-S0 + RelativeSpec; χ Hilbert-poly/Quot-functor OUT (sibling leg) |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---|---|---|---|---|---|
| GF-geo — `genericFlatness` geometric close | 059 · ~10 | ~600 | `FlatteningStratification.lean` | `genericFlatness` axiom-clean ([IsQuasicoherent]+[IsFiniteType]); seam-1/G1/G3/epi-route base change | epi-route base change; `map_smul`+`map_appLE`/`appLE_map` ρ-agreement; semilinear flat-transport | stalk route DEAD; bare image needs basic-open EQUALITY datum |
| GF-alg — algebraic core | 022 · ~9 | ~900 | `FlatteningStratification.lean` | `genericFlatnessAlgebraic` axiom-clean (Nitsure §4 dévissage) | `g:=g0·g1`+`exists_multiple_integral_of_isLocalization`; `IsLocalizedModule.iso`; strong induction | `letI`-built algebra `isDefEq` dead end; deep stack needs heartbeats |
| FBC RegroupHelper | 011 · 4 | ~120 | `Cohomology_RegroupHelper` | `regroupEquiv` `(A⊗_R R')⊗_A M ≅ R'⊗_R M` | `eT` identity-bridge + `TensorProduct.induction_on` beats transparent diamonds | `erw [TensorProduct.zero_tmul]` for zero-branch |
| FBC affine lemma + global infra | ~077 · — | ~? | `FlatBaseChange.lean`, `FlatBaseChangeGlobal.lean` | `pullback_spec_tilde_iso` (01I9); `eqLocus` H⁰-equalizer; `baseChangeGammaEquiv`; FlatBaseChangeGlobal 0-sorry | element-level `gammaResA`/`leftRes`/`rightRes`/`gammaTopEquivEqLocus` equalizer presentation | A-linear "build-ahead" pins retired (phantom nodes) |
| GR-cells/glue/sep/proper | 012–038 · ~11 | ~1310 | `GrassmannianCells.lean` | charts, cocycle, `Grassmannian.scheme`, `isSeparated`, `isProper` | `IsLocalization.Away.lift`; `ValuativeCriterion`; cocycle telescopes via rotMid | `Matrix.det_updateColumn` absent; `Spec.map_comp` rw fails on Scheme-cat diamond |
| SNAP-S2 Hilbert–Serre engine | 012–020 · ~10 | ~1470 | `QuotScheme.lean`, `GradedHilbertSerre.lean` | `IsRatHilb.ofDiffEq`; `gradedModule_hilbertSeries_rational` (00K1) | Route-2 ambient-subquotient pairs sidestep quotient gradings | bundled `IsInternal` over quotient carrier is a hard `isDefEq` dead end |
| QUOT P1+gap1+gap2 | 011–044 · ~17 | ~990 | `QuotScheme.lean` | schematic/proper support; gap1 `isIso_fromTildeΓ`; gap2 `isLocalizedModule_basicOpen` | equivalence-transport beats `IsContinuous`; open-imm pullback-unit IS Final | general-U `_of_cover` unprovable (basic-open only); never positional rw under `X.Modules` diamond |
| SNAP-S0 tensor crux + chain | 066–078 · ~6 | ~? | `SectionGradedRing.lean` | `isIso_sheafification_whiskerRight_unit`; `tensorObjAssoc`; `tensorPowAdd` axiom-clean | `W.whiskerRight`@`ModuleCat (ULift ℤ)` + `modToAb` + coequalizer descent (NOT stalks) | instance synth flaky in long `≪≫` — pass `@asIso _ _ _ _ f h`; `whiskerRightIso` iso-arg breaks `(C:=MonoidalPresheaf X)` |

## Routes

The leg is a fan of independent leaves merging upstream. FBC-B, GR-quot, SNAP-S0 run in parallel
(independent files); RelativeSpec is an independent NEXT lane; QUOT-repr core is the residue behind them.

**FBC route — DIRECT Stacks 02KH(2) equalizer (mate framing ABANDONED).** The i=0 iso assembles from the
finite-affine-cover H⁰-equalizer + per-chart affine module base change — NO mate keystone `_legs_conj`.
Inputs DONE: `eqLocus` H⁰-equalizer, `pullback_spec_tilde_iso` (01I9), `baseChangeGammaEquiv`. Capstone
`baseChangeGammaPullbackEquiv` (`Γ(X,F)⊗_A B ≃ₗ[B] Γ(X',F')`) sig analogist-verified, stub landed; residue
= fork assembly + discharge the 2 frozen named legs from it. The mate framing (`FlatBaseChange.lean` 14
sorries) is dead apparatus — retire once the named legs land (P2 cleanup lane).

**GF route — DONE.** Algebraic core (Nitsure §4 induction) + geometric wrap both axiom-clean.

**GR-quot route.** Glue `SheafOfModules` over `Scheme.GlueData` → effective-descent iso
`isIso_glueRestrictionHom` (DONE, keystone 0-sorry) → Nitsure §5 inverse `grPointOfRankQuotient` (DONE)
→ `represents` (DONE) → residue `tautologicalQuotient_epi` (last sorry, unblocked by keystone). Faithful
Lean image of Nitsure §5 cell-gluing + GL_d cocycle; inverse/representability Archon-original (Nitsure
leaves it as an exercise, §5).

**QUOT-repr core route (χ-independent).** Per Q1, this leg does NOT build the χ Hilbert polynomial /
general Quot functor — those go to the sibling cohomology leg. It builds `grassmannian_scheme` +
`thm:grassmannian_representable` via rank-d locally-free quotients (the Hilbert condition is constant
rank, χ-free), consuming SNAP-S0 `Γ_*(X,L)` for the Plücker/projective coordinate ring and RelativeSpec
for the representing object. Gated on SNAP-S0 + RelativeSpec.

**SNAP-S0 route.** Crux `IsIso(sheafification.map(η_P ▷ Q))`, associator, `tensorPowAdd` all CLOSED
axiom-clean. Remaining: cast-coherence (`sectionMul_coherent`, scaffolded iter-081) → graded assembly
(`gcommSemiring`/`gmodule`). Produces the H⁰ graded ring `Γ_*(X,L)`. Full `MonoidalCategory
(SheafOfModules)` NOT needed; stalkwise / "presheaf+Γ-at-end" routes are DEAD.

## Open strategic questions

- **Q1 — RESOLVED iter-081 (merge-back semantics VERIFIED).** Read the parent
  (`Algebraic-Jacobian-Challenge`) `def:hilbert_polynomial` = `Scheme.hilbertPolynomial`: it is
  **χ-semantic** (`Φ(m)=χ(F(m))=Σᵢ(-1)ⁱ dim Hⁱ(X,F⊗Lᵐ)`; Lean docstring "unfolds to the
  graded-Euler-characteristic construction once χ … in scope"). An H⁰-`Φ_s` def under that label would
  silently change the theorem. Decision: this leg does NOT formalize an H⁰ encoding of
  `def:hilbert_polynomial`/`def:quot_functor` and claim merge-back; those χ nodes belong to the sibling
  cohomology leg. This leg keeps the χ-independent QUOT core (`grassmannian_scheme`/representability via
  rank-d locally-free; the Hilbert condition reduces to constant rank, χ-free). SNAP-S0 `Γ_*(X,L)` is
  still required (projective/Plücker coordinate ring), χ-independent.
- **Merge-back signature check.** Confirm re-signed `genericFlatness`/GR-repr decls match the parent cone
  (Q1 settled the χ semantics; this is the remaining signature-shape check).
- **Q4 — RelativeSpec Stacks-tag pin (gates the RelativeSpec NEXT lane).** Retrieve 01LM/01LP/01LT before
  dispatching the `RepresentableBy`-upgrade prover; the lane is independent of GR-quot/SNAP and runs in
  parallel once pinned.

## Mathlib gaps & new material

Gaps to fill:
- FBC-B: fork assembly for `baseChangeGammaPullbackEquiv` (`tensorEqLocusEquiv` is in Mathlib, verified).
- RelativeSpec: relative Spec of a sheaf of algebras + its `RepresentableBy` universal property
  (Mathlib has only absolute `Spec`, verified absent).

New project material:
- `genericFlatnessAlgebraic`; re-signed `genericFlatness` (+`IsQuasicoherent`+`IsFiniteType`).
- `FlatBaseChangeGlobal.lean` element-level equalizer presentation (`baseChangeGammaEquiv`; capstone
  `baseChangeGammaPullbackEquiv` via `restrictScalars` along `B → groundRing X'`).
- `Grassmannian` (rank-d locally-free quotients) + representability as `IsRepresentable`.
