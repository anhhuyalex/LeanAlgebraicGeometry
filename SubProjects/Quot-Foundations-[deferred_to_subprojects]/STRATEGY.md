# Strategy

## Goal

Close the `sorry`-bearing nodes of the **Čech-independent leg** of the parent's
`thm:fga_pic_representability` cone (Kleiman FGA, "The Picard scheme", §4), then merge back:

- **FBC** — `lem:affine_base_change_pushforward` + `thm:flat_base_change_pushforward`
  (the i=0 base-change map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism).
- **GF** — `thm:generic_flatness` with algebraic core `thm:generic_flatness_algebraic`.
- **QUOT** — `def:hilbert_polynomial`, `def:quot_functor`, `def:grassmannian_scheme`,
  `thm:grassmannian_representable`.

End-state: zero project `sorry` in the 29-node closure, zero axioms (kernel-only). Names/labels are the
parent's so finished work merges back into its A.2.c engine.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---|---|---|---|
| FBC-B — global H⁰ iso (DIRECT equalizer route) | ACTIVE | 2–4 | ~150–350 | `tensorEqLocusEquiv` (Mathlib, present) | PRIMARY route to the named goal legs (Stacks 02KH.2). Module core DONE 0-sorry in `FlatBaseChangeGlobal.lean` (`baseChangeGammaEquiv`+`gammaTopEquivEqLocus`+finite cover). Remaining = scaffold+prove `baseChangeGammaPullbackEquiv` (`thm:fbcb_global_direct`: per-chart 01I9 identification + assembly), then discharge the named `flatBaseChange_pushforward_isIso` + `affineBaseChange_pushforward_iso` bodies from it (signatures frozen, bodies free). Does NOT use the mate keystone. |
| FBC-A — affine mate keystone `_legs_conj` | OFF-PATH | — | — | — | ABANDONED for the goal. The 4 sorries in `FlatBaseChange.lean` (`base_change_mate_fstar_reindex_legs_conj`@1802, `..._gstar_transpose`@2291, and the two named targets `affineBaseChange_pushforward_iso`@2566 / `flatBaseChange_pushforward_isIso`@2606 currently routed through them) are NOT required: the two named targets get filled via FBC-B direct; the two `mate_*` lemmas then become dead apparatus to delete in a cleanup/refactor lane. |
| GR-quot — `universalQuotient` + universal property | ACTIVE (riders endgame) | 1–3 | ~350–700 | none new — all infra project-local | C2 + `universalQuotient` CLOSED iter-064 (bridge chain + transport, axiom-clean). Residue = rectangular `matrixEndRect` infra (~300–600 LOC, recipe in hand) → `tautologicalQuotient` overlap condition → `represents` (Nitsure §1 functor-of-points). |
| SNAP — `def:sectionGradedRing` tensor-powers | ACTIVE (assembly) | 1–4 | ~150–400 | `DirectSum.GCommSemiring`/`Gmodule` graded-mul field shapes | CRUX CHAIN DONE 0-sorry (`ztensor_whisker_localIso`, `isIso_sheafification_whiskerRight_unit`, `tensorObjAssoc`, `tensorPowAdd` — SectionGradedRing.lean). Remaining = graded-ring assembly `sectionGradedRing_gcommSemiring`/`gmodule` in QuotScheme.lean, gated on STATING `sectionsMul_assoc_unit` (the `snap-coherent` scaffolder died on this signature shape — mathlib-analogist api-alignment first). Required to STATE `def:hilbert_polynomial`. |
| SNAP-S1/S3 — section-module input + `Φ_s` extraction | BLOCKED | 3–6 | ~150–400 | `existsUnique_hilbertPoly` | GATED on Open Q1 + the SNAP row above. |
| QUOT-repr — `thm:grassmannian_representable` | BLOCKED | 6–12 | ~400–1000+ | Grassmannian-of-quotients as a scheme; RelativeSpec → `RepresentableBy` | deepest target; GR-cells/glue/sep DONE; GR-quot active (row above); repr-via-functor-of-points in Routes |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---|---|---|---|---|---|
| GF-alg — algebraic core | 022 · ~9 | ~900 | FlatteningStratification.lean | `genericFlatnessAlgebraic` axiom-clean (Nitsure §4 dévissage); L4/L5 | `g:=g0·g1`; ring↔module bridge `IsLocalizedModule.iso` + `extendScalarsOfIsLocalization`; base-generalizing strong induction | `letI`-built `Algebra A Cg` is `isDefEq` dead end (use ambient); deep stack needs `maxHeartbeats 1600000` |
| FBC RegroupHelper | 011 · 4 | ~120 | Cohomology_RegroupHelper | `regroupEquiv` `(A⊗_R R')⊗_A M ≅ R'⊗_R M` axiom-clean | `eT` identity-bridge + `TensorProduct.induction_on` to beat transparent-instance diamonds | element `map_smul'` zero-branch needed `erw [TensorProduct.zero_tmul]` |
| GR-cells (charts+cocycle) | 012 · 2 | ~600 | GrassmannianCells.lean | big-cell charts, transition maps, `lem:gr_cocycle` — 28 decls | `IsLocalization.Away.lift` for localized transition maps; prove distributed-matrix forms by `exact` then `rw` | `rw [Matrix.map_mul]` fails on Away-base-changed matrices (hidden `algebraMap` diamond) |
| GR-glue + separated | 034 · 4 | ~350 | GrassmannianCells.lean | `Grassmannian.scheme` (GlueData), `isSeparated`/`isSeparatedToSpecZ`, `diagonalRingMap_surjective` | `Spec ℤ` genuinely terminal for `Scheme.{0}` ⟹ `toSpecZ` + glue by `IsTerminal.hom_ext`; faithful `Proj.isSeparated` port (per-patch closed immersion) | `convert!`/`pullback.map_fst` absent (use `convert … using 1`, `pullback.lift_fst`); `← Spec.map_comp` bare `rw` dead on the Scheme-cat diamond (route via `show`) |
| SNAP-S2 power-series engine | 012 · 1 | ~180 | QuotScheme.lean (`IsRatHilb`) | antidifference + `IsRatHilb.ofDiffEq` (power-series half of Stacks 00K1), 8 decls | telescoping via `invOneSubPow`; `IsRatHilb` predicate isolates series bookkeeping | `PowerSeries.C` ring arg implicit; `open … in` must precede docstring |
| SNAP-S2 graded Hilbert–Serre rationality | 020 · 9 | ~1290 | GradedHilbertSerre.lean | keystone `gradedModule_hilbertSeries_rational` (Stacks 00K1) axiom-clean | Route-2 ambient-subquotient pairs (`Naux⊓ℳn`) sidestep quotient-carrier gradings | bundled `DirectSum.Decomposition`/`IsInternal` over quotient/subtype carrier is a hard `isDefEq` dead end (Route 2 supersedes) |
| QUOT-defs P1 predicates | 011 · 1 | ~90 | QuotScheme.lean | schematic-support, proper-support via `IdealSheafData.ofIdeals`/`.subscheme` | annihilator-ideal-sheaf needs NO QCoh bridge | — |
| GR-proper — valuative criterion | 038 · ~5 | ~300 | GrassmannianCells.lean | `Grassmannian.isProper` (Gr(d,r) proper over ℤ); E4/E5/existence-lift | Nitsure §1 DVR-filler (minimal minor J, factor through R⊂K); term-mode glue for Spec.map composition | keyed `rw` dead on Scheme-cat diamond (use `congrArg`/`calc`); `existence_lift` noncomputable; pass `(R:=S.R)` to E2/E3 |
| QUOT gap1 — section-loc descent | 041 · ~14 | ~600 | QuotScheme.lean | gap1 `isIso_fromTildeΓ_of_isQuasicoherent` + keystone `isLocalizedModule_basicOpen_descent` + `Hfr` producer (Hartshorne II.5.3), WITHOUT global QCoh≃Mod | keep immersion `j` OPAQUE in helpers; σ `S`-vs-`Γ(Spec S,⊤)` rebasing is `rfl` | concrete `j` → >3.2M-heartbeat `whnf` runaway; general-U `_of_cover` `Hfr` is an unprovable trap (use basic-open) |
| QUOT gap2 — qcoh section-localization on basic opens | 044 · ~3 | ~520 | QuotScheme.lean | `isLocalizedModule_basicOpen` + Piece A `isQuasicoherent_pullback_fromSpec` (L1–L6) + Piece B eqToHom bridge | QC-under-pullback via equivalence-transport (`overRestrictUnitIsoInv`); open-imm pullback-unit Final via open-map adjunction; `.IsQuasicoherent` dot-notation | gateway `↥V`/`↥↑V` coercion + IsContinuous non-synth = dead route; bypass via equivalence-transport |
| QUOT-defs consumers — annihilator / P2 | 046 · ~2 | ~150 | QuotScheme.lean | `annihilator_map_basicOpen` + `annihilator_ideal` axiom-clean; P2 local-freeness predicate | annihilator needs GLOBAL `hfin : ∀ V, Module.Finite` (mirror `Hom.ker_apply`) | single-U annihilator form UNPROVABLE (`ofIdeals` = largest coherent subsheaf, reverse inclusion is global) |
| GF-geo — `genericFlatness` (geometric wrapper) | 059 · ~10 | ~700 | FlatteningStratification.lean | `genericFlatness` axiom-clean (`[IsQuasicoherent]`+`[IsFiniteType]`); ring-epi flat-descent route; G1 section-finiteness | per-piece flat descends via `gf_openImmersion_isEpi`+`gf_flat_descend_isEpi` over open-imm mono + `Spec.fullyFaithful`; `flatV` STEP-3 semilinear transport = `map_smul`+native-defeq+appLE ρ-agreement | stalk assembly DEAD (no `SheafOfModules.stalk`); source-span descent supersedes; `letI`-built `Algebra` is defeq dead end |
| SNAP coequalizer rows — `relTensorActL/R/Proj` | 060 · ~3 | ~400 | SectionGradedRing.lean | three objectwise coequalizer-row nat. transforms axiom-clean; `RelativeTensorCoequalizer` 22-decl API | carrier gap fixed by `objRestrict`; `relTensorProj.naturality` = bare-ℤ `TensorProduct.ext'`-square then transport to `Ab` (`AddCommGrpCat`) | the `forget₂ CommRingCat→RingCat` carrier "blocker" was illusory — real obstacle was additivity, not the carrier |

## Routes

Single route per target; the leg is a fan of independent leaves merging back upstream. FBC-A, GF-geo,
and QUOT-consumers are the live frontier. FBC-B follows FBC-A; QUOT-repr follows QUOT-defs + SNAP.

**FBC route — DIRECT (Čech-cohomology-free), primary.** Both named legs are reached without the
adjoint-mate keystone. `H⁰(X,F)=Γ(X,F)` is the **finite** equalizer `∏Γ(Uᵢ,F) ⇉ ∏Γ(Uᵢⱼ,F)` over a
finite affine cover of a qcqs scheme, and flat `−⊗B` preserves that finite equalizer. The module-level
core is DONE 0-sorry (`FlatBaseChangeGlobal.lean`): `gammaTopEquivEqLocus` (Γ = `eqLocus` of the two
restriction legs, via sheaf separatedness+gluing) and `baseChangeGammaEquiv` (`B⊗_A Γ(X,M) ≅
eqLocus(B⊗leftRes,B⊗rightRes)` via `tensorEqLocusEquiv`), over the finite-cover lemma. Remaining
(`thm:fbcb_global_direct`, frontier): identify the base-changed RHS legs per chart with `g'^*F` over the
pulled-back cover (Stacks 01I9 / `pullback_spec_tilde_iso`, DONE), assemble `baseChangeGammaPullbackEquiv`,
then fill the named `flatBaseChange_pushforward_isIso` (+ the affine specialization
`affineBaseChange_pushforward_iso`) bodies from it. No `gammaPushforwardNatIso`, no `conjugateIsoEquiv`,
no `_legs_conj`.

*Mate keystone — ABANDONED.* The earlier obligation-2 conjugate/mate route (`_legs_conj` →
`_gstar_transpose`) hit a kill-criterion and is OFF-PATH: its sorries do not gate the goal once the named
targets are filled via the direct route. Delete the `base_change_mate_*` apparatus in a cleanup lane.

**GF route.** Algebraic core `genericFlatnessAlgebraic` DONE (Nitsure §4). Geometric `genericFlatness`
(`[IsQuasicoherent]`+`[IsFiniteType]`) wraps it: pass to affine `Spec A ⊆ S` (noetherian domain), cover
`p⁻¹(Spec A)` by finite affine `W_j = Spec B_j` (finite-type/A), read `M_j = Γ(F,W_j)` finite over `B_j`
(via G1 — **DONE**), apply the algebraic form per patch, conclude flatness over `V = D(∏ f_j)`. G3 promotes
per-patch freeness `(M_j)_f` free/`A_f` to flatness of section modules `Γ(F,W)/Γ(S,U)` for arbitrary
affine `W ≤ p⁻¹U`. Pure-algebra anchors DONE: G3.1 `gf_patch_free_imp_flat` (`Module.Flat.of_free`),
G3.3 `gf_flat_base_local_on_source` (`Module.flat_of_isLocalized_maximal`), G3.4 `gf_stalk_flat_localBase`
(localized-base transitivity).
- *Stalk route DEAD; source-span descent DONE.* The old stalk assembly (no `SheafOfModules.stalk` in Mathlib)
  and its source-span re-spec are both resolved: B1 `gf_flat_localizedModule_sameBase`, B2 section-localization,
  the span criterion `Module.flat_of_isLocalized_span`, the patch-aligned cover, and the witness `V=D(∏fⱼ)` are
  all axiom-clean. The proof was reduced (iter-055) to a single per-piece flatness `Module.Flat Γ(S,U) Γ(F,D g)`.
- *Final gap RESOLVED via the ring-epi route.* That per-piece step descends the base `Γ(S,V)→Γ(S,U)` along the
  open immersion `U↪V` of affines. The inclusion is a scheme **mono** (open immersion) ⟹ by `Spec.fullyFaithful`
  the restriction `Γ(S,V)→Γ(S,U)` is a ring **epi** ⟹ `Algebra.IsEpi` (`CommRingCat.epi_iff_epi`) ⟹ Mathlib's
  `TensorProduct.lid'` gives `Γ(S,U)⊗_{Γ(S,V)}M ≅ M`, so `Module.Flat.baseChange` + `.of_linearEquiv` descend
  flatness. Two new project lemmas: `gf_openImmersion_isEpi` (the epi bridge) + `gf_flat_descend_isEpi` (the
  descent). NO Mathlib gap remains — all anchors verified present (`Mathlib.Algebra.Algebra.Epi`).

**QUOT route.** Foundational decisions:
- *Hilbert-poly encoding = graded Hilbert function.* `def:hilbert_polynomial` = `Φ_s` agreeing for `m≫0`
  with `m ↦ dim_{κ(s)} Γ(X_s, F_s ⊗ L_s^m)` (Hartshorne I.7.5; Nitsure §1), via
  `Polynomial.existsUnique_hilbertPoly` (`[CharZero]`) + `lem:gradedHilbertSerre_rational` (DONE).
- *Rationality engine = Route 2* (Stacks 00K1 over pairs `N'≤N` in a fixed ambient graded κ-module). DONE.
- *SNAP-S1 input* (GATED — Q1): chosen f.g. presentation — every coherent `F` on `Proj S` is `M̃` for a
  f.g. graded `M`, sidestepping the doubtful "Γ_*(F) f.g." lemma.
- *QUOT-defs*: P1 support predicates DONE; gap1 DONE; consumers (G1-core/gap2/annihilator) + P2 NEXT.
  `Grassmannian := QuotFunctor (𝟙 S) V Φ_d`.
- *QUOT-repr decomposed*: GR-cells/glue/separated/proper (DONE); GR-quot (tautological rank-`d` quotient +
  universal property); GR-repr (functor-of-points ⟹ `RepresentableBy` via `thm:relative_spec_univ`).

## Open strategic questions

- **Q1 — SNAP route DECISION (blocks S1) — LIVE (gap1 landed iter-044, no cohomology engine in scope).**
  `def:hilbert_polynomial` is the H⁰ graded-Hilbert-function `Φ_s` polynomial (NOT a χ/Euler char — the
  project has no higher-cohomology machinery; χ is unreachable here, so the H⁰ route is the ONLY viable one).
  Canonicity of `Φ_s`: either (a) chosen-presentation `Φ_s` + a cited Serre `m≫0` agreement, or (b) H¹-free
  finiteness with a reference. Action: dispatch a reference-retriever for the Serre `m≫0` agreement (the
  "Hartshorne II.5.17" attribution is unverified/likely wrong), then decide (a) vs (b). `def:sectionGradedRing`
  tensor-powers owed regardless.
- **Q2 — FBC keystone `_legs_conj` — RESOLVED by route swap (iter-079).** The mate keystone is ABANDONED;
  the named FBC legs are reached via the DIRECT H⁰-equalizer route (module core DONE). No keystone discharge
  needed. Residual = cleanup-delete the dead `base_change_mate_*` apparatus.
- **Q3 — `def:hilbert_polynomial` standard-graded hypothesis (fence before any SNAP/S1 prover).** Stacks
  00K1 needs `S₊` generated in degree 1 ⟹ the def must carry a standard-graded/very-ample hypothesis
  (ample-only insufficient). Verify the Lean signature carries it before S1.
- **Q4 — RelativeSpec Stacks-tag pin (fence before QUOT-repr).** `thm:relative_spec_univ` underpins GR-repr;
  `references/summary.md` flags tag uncertainty (01LL is a §-label, 01LO is transitivity not the affine
  case, 01LR is the defining eqn — real targets likely 01LM/01LP/01LT). Reference-retrieve + pin the
  affine-base-change tag before any QUOT-repr prover.
- **Merge-back signature check.** Confirm re-signed `genericFlatness`/QUOT decls match the parent cone.

## Mathlib gaps & new material

Gaps to fill (detail in Routes):
- FBC-A: keystone `_legs_conj` via composite adjunctions `adjL`/`adjR` + the `conjugateEquiv_symm_comp`
  leg-chain (no new Mathlib lemma; the conjugate API exists).
- GF-geo: **NO Mathlib gap remains.** Final per-piece flatness descends via the ring-epi route
  (`gf_openImmersion_isEpi` + `gf_flat_descend_isEpi`) over verified Mathlib anchors `TensorProduct.lid'`,
  `CommRingCat.epi_iff_epi`, `Spec.fullyFaithful`, `Module.Flat.baseChange/.of_linearEquiv`. Span descent
  (`gf_section_span_flat_descent`), B1, B2, cover scaffold, witness all DONE. Close `genericFlatness`.
- **gap1 (QCoh≃Mod affine descent), G1-core, gap2 (`isLocalizedModule_basicOpen`): all DONE** (see
  `## Completed`). gap2 → annihilator characterization (frontier-ready) + GF-G1 locality (DONE).
- **SheafOfModules tensor powers (blocks `def:sectionGradedRing` ⟹ SNAP):** wire Mathlib's existing
  `PresheafOfModules.Monoidal` + `Sheaf.monoidalCategory` through to `SheafOfModules` over the scheme
  (reuse, don't re-derive) + lax-monoidal `Γ`; Mathlib-gradient sub-build owed before SNAP.
- QUOT predicates: rank-`r` local-freeness for `SheafOfModules`. QUOT-repr: Grassmannian-of-quotients as
  a scheme (Nitsure §1/§5 big-cell patching).

New project material:
- `genericFlatnessAlgebraic` (done); re-signed `genericFlatness` + coherence encoding
  (`[IsQuasicoherent]`+`[IsFiniteType]` over a locally noetherian base).
- QUOT defs with tightened signatures; `Grassmannian` via `QuotFunctor`; representability as `IsRepresentable`.
