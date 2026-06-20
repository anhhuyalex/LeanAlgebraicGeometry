# Done Tasks

## iter-080 prover closures (global sorry 12→9)
- **GlueDescent 1→0 — KEYSTONE CLOSED.** `glueChartComponent_leg_compat` (the conjugated-cocycle
  keystone) closed: legs folded to canonical 5-factor form (`map_fold₅`, `side_collapse_*`) and equated
  by the single C2 hypothesis. `isIso_glueRestrictionHom` / `glueRestrictionIso` fully realized.
- **GrassmannianQuot 3→1.** Both `represents` `RepresentableBy` inverse halves closed (via
  `grPointOfRankQuotient_rqPullback_tautological` + `rqPullback_grPointOfRankQuotient_rel` +
  `chartComposite/chartLocus_rqPullback`); `universalQuotient_isLocallyFreeOfRank` closed by chart-cover
  reduction. Residual = `tautologicalQuotient_epi`, now unblocked (keystone=0).

## iter-064 — GR-quot C2 `bundleTransition_cocycle` CLOSED + rider `universalQuotient` CLOSED
- **GR-quot (`GrassmannianQuot.lean`, 4→2 sorry):** the full (b)→(c)→C2 cascade in one session, all
  axiom-clean kernel-validated (40s cold build): 5 bridge lemmas (`baseChange_bridge_gammaSpec/_left/
  _right/_transition` + matrix assembly `baseChange_bridge`), `tripleOverlapSections`, hom-level
  transport `bundleTransition_cocycle_transport`, 3 generic `pullbackCongr` cast-collapse lemmas, then
  **C2 by `Iso.ext`** and **`universalQuotient := Scheme.Modules.glue (theGlueData) …`**. Load-bearing
  unlock: `appTop (Y := Spec (of …))` statement-level ascription (dissolves the Γ(chart)/Γ(Spec)
  print-identical defeq mismatch). New primitive `Scheme.Modules.glueLift` (generic-context
  `equalizer.lift`; `Limits.Pi.lift_π` NOT `limit.lift_π`); `tautologicalQuotient` now a structured
  `glueLift` assembly with ONE named sorry (overlap compatibility; rectangular-matrixEnd recipe in the
  archived task result). Prover also did the comparison-cluster relocation (the staged refactor died).
  Dead ends logged: `coe_comp`+`← Matrix.map_map` over-split; concrete-instantiation `equalizer.lift`;
  `reassoc_of% matrixEnd_comp` under the transport.
- **SNAP lane never ran** (plan-phase truncation killed the scaffolder; re-staged iter-065).

## iter-063 — GR-quot L3 step (a) + (c)-core closed; SNAP `relativeTensorCoequalizerIso` closed (both lanes delivered)
- **GR-quot (`GrassmannianQuot.lean`, 5→4 sorry):** `matrixEnd_pullback` (L3 step (a)) CLOSED axiom-clean
  (helper `ιFree_matrixEnd`; cancel `Q.inv` + `Cofan.IsColimit.hom_ext` + per-entry `scalarEnd_pullback`;
  the `free`/`∐` value-diamond bridges with `erw` — but `erw [Category.assoc]` against `pullbackComp` whnf's
  the opaque pseudofunctor term, near-OOM, keep `pullbackComp` away from `erw`). PLUS net-new
  **`pullbackBaseChangeTransport_matrixToFreeIso`** — the abstract (a)→(c) transport core: chart-independent
  identification of a transported bundle-transition-shaped iso with `matrixEnd` of the base-changed matrix;
  `rw [← hfront, ← hback]; rfl` closes assoc-equal SheafOfModules composites. C2 still sorry; named residuals:
  (1) decl-ordering relocation (cluster sits after C2), (2) `baseChange_bridge` (Cells-internals
  identification). Stale `glue` section NOTE rewritten (recurring auditor MAJOR cleared).
- **SNAP (`SectionGradedRing.lean`, 2→0 sorry — file done again):** `relativeTensorCoequalizerIso` CLOSED
  axiom-clean: cofork condition extracted as `relTensorActL_proj_eq` (objectwise `coeq_condition`, defeq
  carriers); `IsColimit` body = `evaluationJointlyReflectsColimits` + **`isColimitMapCoconeCoforkEquiv`**
  (the key tool that commutes `evaluation.mapCocone` with `Cofork.ofπ` — record for future functor-category
  cofork promotions) applied to the 22-decl objectwise `isColimitCofork`. Defeq did all apex matching.

## iter-062 — GR-quot L3 ATOM `scalarEnd_pullback` closed axiom-clean (hard-gate cleared)
- **GR-quot (`GrassmannianQuot.lean`, 4→5 sorry — BUILD task):** the progress-critic hard-gate make-or-break
  ATOM **`scalarEnd_pullback`** (scalar-endomorphism naturality under pullback,
  `(pullback p).map (scalarEnd a) ≫ q = q ≫ scalarEnd (p.appTop a)`) CLOSED axiom-clean, via transposing
  under the pullback–pushforward adjunction (`homEquiv_naturality_left/right` supplied as TERMS — positional
  `rw` fails under the `X.Modules` diamond) + new proof-internal helper **`unitToPushforward_scalarEnd_comm`**
  (CLOSED, the `change`-to-nested-application lever beats the value-ModuleCat diamond; universe-0 only).
  `matrixEnd_pullback` (a) scaffolded to its biproduct-transport residual (honest sorry). The atom did NOT
  stall ⇒ escalation tripwire not fired; L3 chain unblocked at its core. (SNAP lane dropped again by the
  no-op filter — decl never existed; root-fixed iter-063 via plan-phase scaffold.)

## iter-061 — GR-quot C2 chain L1 + L2 closed axiom-clean
- **GR-quot (`GrassmannianQuot.lean`, 4→4 sorry — BUILD task):** two NEW closed theorems.
  **L1** `bundleTransition_cocycle_matrix` — the Cramer-inverse cocycle `(X^J_K)⁻¹(X^I_J)⁻¹=(X^I_K)⁻¹`
  over the triple-overlap ring `S_I`, proved by taking the `I`-minor of `cocycle_imageMatrix_eq'`.
  **L2** `matrixToFreeIso_mul` — one-liner via `matrixToFreeIso_hom`+`matrixEnd_comp`. Both axiom-clean.
  +7 ported `private …'` matrix helpers (the Cells originals are private, not importable). C2
  (`bundleTransition_cocycle`, L891) still sorry — L3 transport stalled exactly as the planner pre-stated
  ("isolate L3 standalone iter-062"); prover named the gap precisely: (a) matrixEnd-under-pullback
  naturality + (b) ΓSpecIso base-change bridge. (SNAP lane never ran — dropped by no-op dispatch filter.)

## iter-060 — SNAP `SectionGradedRing` FULLY CLOSED + GR-quot cold-build OOM RESOLVED
- **SNAP (`SectionGradedRing.lean`, 1→0 sorry — file done):** `relTensorProj.naturality` discharged via the
  bare-ℤ-square route (`TensorProduct.ext'`+`rfl` on elementary tensors, then transport to `Ab` via
  `LinearMap.congr_fun`+`simpa`). The feared `forget₂ CommRingCat→RingCat` carrier blocker was ILLUSORY — the
  real obstacle was additivity (`map_add` not firing on the `Ab`-morphism), dissolved by `TensorProduct.ext'`.
  All three coequalizer-row nat. transforms (`relTensorActL`/`relTensorActR`/`relTensorProj`) now complete.
  Axiom-clean.
- **GR-quot (`GrassmannianQuot.lean`, 4→4 sorry — resource fix):** cold-build OOM ceiling (blocked cold build
  + sync_leanok 3 iters) RESOLVED. `bundleTransition_self` re-proven leaner at the iso level (new helper
  `pullbackFreeIso_trans_symm_eqToIso`, `subst`-generic so immersions stay opaque); `maxHeartbeats 1e6`
  override DROPPED; cold `lake build` 227s→22s / ~7GB / axiom-clean. OOM was proof-local — NO file split.

## iter-059 — GF `genericFlatness` FULLY CLOSED (HEADLINE) + GR-quot GL_d matrix infra + C1
- **GF (`FlatteningStratification.lean`, 1→0 sorry — phase DONE):** the final `flatV` STEP-3 transport
  semilinearity sorry discharged. `genericFlatness` axiom-clean `{propext, Classical.choice, Quot.sound}`.
  Close = `l(c•x)=(refl)c•l x`: `simp`-collapse of `addCommGroupIsoToAddEquiv`→`eqToHom=i.op`
  (`Subsingleton.elim`) → native action rewrites (`← IsScalarTower.algebraMap_smul`+`Module.compHom` defeq)
  → `Scheme.Modules.map_smul` → `congr 1` → ρ-agreement (both sides = `p.appLE (D f)(D g) hg_pre c` via
  `appLE_map`/`map_appLE`). GF-geo phase → STRATEGY ## Completed.
- **GR-quot (`GrassmannianQuot.lean`, 3→4 sorry; net-positive infra):** built GL_d matrix infra (scalarEnd
  ring-hom API, `matrixEnd`/`_comp`/`_one`, `matrixToFreeIso`, `bundleTransition`) + PROVED C1
  (`bundleTransition_self`, needed `maxHeartbeats 1000000` → iter-060 cold-build OOM ceiling). C2 + 3 riders
  scaffolded sorry.

## iter-053 — GF source-span algebra core + GR opensMap_final keystone + SNAP objectwise coequalizer (all axiom-clean; 0 declaration-sorry closed)
- **GF B1.0/B1** (`FlatteningStratification.lean`, +2 axiom-clean): `gf_localizedModule_baseChange_tensor_comm`
  (`LocalizedModule T (N⊗_R K) ≅ (LocalizedModule T N)⊗_R K`, via `IsLocalizedModule.rTensor`) +
  `gf_flat_localizedModule_sameBase` (`[Module.Flat R N]` ⟹ `Module.Flat R (LocalizedModule T N)` — the one
  genuine Mathlib gap, source-submonoid localization preserves base flatness; via `Flat.iff_lTensor_injectiveₛ`
  + `IsLocalizedModule.map_lTensor`/`map_injective`). **GF algebra core DONE**; `genericFlatness` blocker now
  GEOMETRIC. iter-054 effort-broke B2 into B2.1–B2.4.
- **GR-quot keystone + functor assembly** (`GrassmannianQuot.lean`, +8 axiom-clean; 5→5 declaration-sorry):
  `opensMap_final` (`(Opens.map φ.base).Final` for ANY scheme morphism — terminal `⊤` in the structured-arrow
  cat) ⟹ `pullbackFreeIso` (general `f^* free ≅ free`) + `pullback_isLocallyFreeOfRank`; `RankQuotient`(+Rel/
  setoid/refl/symm/trans), `rqPullback`/`rqPullback_rel`; `functor : Scheme.{0}ᵒᵖ ⥤ Type 1` fully assembled
  (obj+map proven), `map_id`/`map_comp` reduced to ONE named coherence `pullbackObjUnitToUnit(𝟙)=(pullbackId).
  app unit` (2 internal law-sorries). Forced sig: value is `Type 1` (RankQuotient bundles large `F`).
- **SNAP objectwise coequalizer** (`SectionGradedRing.lean`, +22 axiom-clean; file 0-sorry): namespace
  `RelativeTensorCoequalizer` — `M⊗[S]N` is the `AddCommGrpCat` coequalizer of the two `S`-action maps
  `M⊗_ℤ(S⊗_ℤN) ⇉ M⊗_ℤN`; headline `isColimitCofork` via `TensorProduct.liftAddHom` + `cancel_epi (piMor)` +
  `Cofork.IsColimit.mk`. The hardest Mathlib-absent brick of route (a). Remaining = presheaf promotion + crux.

## iter-052 — GF G3 algebraic anchors + GR-quot C2 transport + SNAP crux reductions (all axiom-clean)
- **GF G3.1/G3.3/G3.4** (`FlatteningStratification.lean`, +3 axiom-clean): `gf_patch_free_imp_flat`
  (`Module.Flat.of_free`), `gf_flat_base_local_on_source` (`Module.flat_of_isLocalized_maximal`, source-side),
  `gf_stalk_flat_localBase` (stalk-FREE localized-base transitivity via `IsLocalization.flat`+`Flat.trans`).
  **GF KEY FINDING: blueprinted stalk route DEAD** (Mathlib has no `SheafOfModules.stalk`); G3.2+assembly
  un-typeable. Re-spec'd iter-053 to source-span descent (B1.0/B1/B2). `genericFlatness` still sorry.
- **GR-quot C2 transport** (`GrassmannianQuot.lean`, +4 axiom-clean, glue body still sorry by design):
  `pullbackBaseChangeTransport` (the C2 ingredient; `pullbackComp` route, whnf-safe — fixes iter-051 runaway)
  + `glueData_bridge_{src,mid,tgt}` (triple-overlap endpoint equalities) + well-typed `_hC2` on `glue`.
- **SNAP crux reductions** (`SectionGradedRing.lean`, +3 axiom-clean, file 0-sorry): `isIso_sheafification_map_iff`
  + `localIso_toPresheaf_map_unit` (unit ∈ J.W) + `isIso_sheafification_map_unit` (un-whiskered crux). Crux
  `isIso_sheafification_whiskerRight_unit` REDUCED to one abelian gap `J.W(toPresheaf.map(η_P ▷ Q))`; route =
  coequalizer brick `relativeTensor_as_coequalizer` (Mathlib-absent, blueprinted iter-053). un-`private`d `sheafification`.

## iter-051 — GF G1 CLOSED + GR-quot chartQuotientMap_epi (+7 axiom-clean)
- **GF G1 FULLY CLOSED** (`FlatteningStratification.lean`, +3 axiom-clean): G1 base case
  `gf_qcoh_finite_sections_of_genSections` (the gap1-hard X.Modules↔Spec transport, three sub-steps a/b/c:
  QC-pullback `fromSpec` + `isIso fromTildeΓ`; `GeneratingSections.map` transport across `isoSpec.inv` +
  `tildeFinsupp`; `gammaPullbackImageIso` semilinear identification) + G1 assembly
  `gf_qcoh_fintype_finite_sections` + helper `module_finite_of_ringEquiv_semilinear`. Clears the 3-iter
  CHURNING blocker. Gotcha: `Epi σ'.π` unfindable in nested `epi_comp` synth → `epi_comp' inferInstance σ'.epi`.
- **GR-quot `chartQuotientMap_epi`** (`GrassmannianQuot.lean`, +4 axiom-clean): split-epi via I-column
  inclusion `s_I ≫ u^I = 𝟙`; chain `scalarEnd_one`/`scalarEnd_zero` + private `chartQuotientMap_ιFree`
  (I-minor = identity, via `universalMatrix_submatrix_self` + biproduct↔coproduct bridge) + `chartQuotientMap_epi`.
  `glue` C1 cocycle hyp added (`_hC1`). Gotcha: mixed `affineChart`/`Spec` forms → `set A;set S` at top;
  category `rw`/`erw` fail under `chartQuotientMap` diamond → defeq proof TERMS only.


Resolved obligations (axiom-clean unless noted). Newest first.

## iter-047 prover round (2 lanes: GF-G1 seams 2/3 + SNAP layer-1 — both axiom-clean, both hit named walls)
- **GF-G1 affine base case partial (+3 decls, axiom-clean `{propext, Classical.choice, Quot.sound}`).**
  `gf_affine_qcoh_Gamma_epi` (seam-2 crux: Γ sends qcoh epis to surjections via Mathlib `tilde.adjunction`
  counit `fromTildeΓNatTrans` naturality + `tilde.functor` faithful-reflects-epi; 3 glue fixes: `change`-defeq
  for the counit defeq, `IsIso.eq_comp_inv` as TERM not rw, explicit `epi_comp` to beat the 20k-heartbeat
  `infer_instance` timeout); `gf_qcoh_finite_sections_globally_generated` (seam-3, `Module.Finite.of_surjective`);
  `gf_qcoh_finite_sections_of_free_epi` (UNPLANNED self-contained free-epi base case via tilde counit+unit iso).
  Blocked: seam-1 `gf_finiteType_affine_finite_cover_generated` (Mathlib-absent, 3 primitives) + X.Modules↔Spec
  transport. → **iter-048 effort-broke seam-1 into 1a/1b/1c + disentangled free-epi pin.**
- **SNAP layer-1 DONE (NEW `SectionGradedRing.lean`; +10 axiom-clean decls).** `sheafification`,
  `MonoidalPresheaf`, `tensorObj` (`def:sheafTensorObj`), `unitModule`, `tensorPow` (`def:sheafTensorPow`),
  `moduleTensorPow` (`def:sheafModuleTwist`), `sheafificationCounitIso`, `tensorObjUnitIso`,
  `tensorObjRightUnitor`, `tensorBraiding` + 3 simp lemmas. Root import added (acyclic). Blocked:
  `tensorPowAdd` = the sheaf-level associator (Mathlib-absent strong-monoidality of sheafification). →
  **iter-048 analogist DECIDED the bespoke line-bundle local-iso route (Analogue 4); blueprint rewritten.**

## iter-046 prover round (1 lane: QUOT annihilator characterization DONE)
- **QUOT annihilator (+2 decls, axiom-clean `{propext, Classical.choice, Quot.sound}`).**
  `annihilator_map_basicOpen` (per-affine annihilator-localization coherence = the
  `IdealSheafData.map_ideal_basicOpen` field; gap2 `isLocalizedModule_basicOpen` + engine
  `Module.annihilator_isLocalizedModule_eq_map`, via local `compHom`+`IsScalarTower.of_algebraMap_smul`);
  `annihilator_ideal` (`lem:modules_annihilator_ideal`, affine-open characterization `(annihilator F).ideal U
  = Ann_{Γ(X,U)}(Γ(F,U))` via honest `IdealSheafData` assembly + `ofIdeals_ideal`). **Justified signature
  deviation:** GLOBAL `hfin : ∀ V, Module.Finite Γ(X,V) Γ(F,V)` not single-`U` — single-`U` PROVEN unprovable
  (`ofIdeals` = largest *coherent* sub-sheaf; reverse inclusion needs global coherence; mirrors Mathlib
  `Hom.ker_apply`). Finite-type F discharges `hfin` via G1 affine-locality later. Blueprint corrected iter-047
  (statement→global, proof→`ofIdeals_ideal` assembly, dropped false "inf of comaps"; added dedicated
  `lem:annihilator_map_basicOpen` block — clears coverage debt).

## iter-043 prover round (2 lanes: QUOT gap2 Piece B LANDED; FBC tilde-transport REVERSAL)
- **QUOT gap2 Piece B LANDED (+1 decl, axiom-clean `{propext, Classical.choice, Quot.sound}`).**
  `isLocalizedModule_basicOpen_of_hP1` (the full gap2 eqToHom bridge): instantiate
  `section_localization_hfr_aux_general` at `j=fromSpec`, then transport to `restrictBasicOpenₗ` via the
  open identifications (`eT : j''ᵁ⊤=U`, `eB : j''ᵁD(f)=basicOpen f` from `IsAffineOpen.fromSpec_image_basicOpen`),
  ring iso `ρ` with `ρ f_im=f` (crux `fromSpec_image_top_section_coherence`), bridge-I
  `isLocalizedModule_of_ringEquiv_semilinear`, `Submonoid.map_powers`. gap2 final `isLocalizedModule_basicOpen`
  left ABSENT — gated on **Piece A only** (`isQuasicoherent_pullback_fromSpec`). Blueprint block authored
  iter-044 (`lem:isLocalizedModule_basicOpen_of_hP1`); Piece A decomposed into route-1 L1–L6 chain iter-044.
- **FBC affine tilde-transport REVERSAL (0 decls).** The iter-042-planned `sections_direct` bypass is
  illusory: `g'=pullback.fst` has no element normal form, so `Γ(α)` must transit the tilde dictionaries =
  the conjugate intertwining. Both routes funnel through the keystone `_legs_conj` @1848. Prover correctly
  added nothing. RESOLVED iter-044: NOT escalated (autonomous); analogist found a factored
  `conjugateEquiv_symm_comp` route (no monolithic β) → keystone is now an active mathlib-build lane.

## iter-042 prover round (1 lane: QUOT G1-core CLOSED + gap2 core/crux LANDED; gap2 deferred)
- **QUOT G1-core CLOSED + gap2 ~80% (+5 decls, axiom-clean `{propext, Classical.choice, Quot.sound}`).**
  `isLocalizedModule_basicOpen_of_isQuasicoherent` (G1-core, `lem:qcoh_affine_section_localization` —
  one-liner `isLocalizedModule_restrict_of_isIso_fromTildeΓ M f` over gap1); `restrictₗ` (Γ(X,U)-linear
  compHom-form restriction); `restrictBasicOpenₗ` (scalar-tower form); `fromSpec_image_top_section_coherence`
  (the gap2 CRUX `ρ(σf)=f` — `← eqToHom_map` fold + `Subsingleton.elim`); `section_localization_hfr_aux_general`
  (gap2-CORE transport, general ambient X via the LOCAL ring `A=Γ(X,j''ᵁ⊤)`, no `restrictScalars` bridge).
  gap2 `isLocalizedModule_basicOpen` left ABSENT (mathlib-build discipline) pending **Piece A** (QC preserved
  under pullback along `hU.fromSpec` — Mathlib-absent `QuasicoherentData` cover-refinement) + **Piece B**
  (mechanical eqToHom bridge whose only non-trivial input = the proven crux). Blueprint blocks for all 5 +
  Piece A authored iter-043 (gap2 HARD GATE re-cleared). G1-core/gap2 unblock GF-G1 (gap2-gated) + annihilator.

## iter-040 prover round (1 lane: QUOT producer (a) + range-b LANDED; TOP deferred)
- **QUOT producer (a) + range-half of (b) LANDED axiom-clean (+4 decls).** `compositeBasicOpenImmersion`
  (def, the composite immersion `j = isoSpec.inv ≫ ι_W ≫ ι_{q.X i}`), `pullback_composite_immersion_isIso_fromTildeΓ`
  (producer (a) — the critical object-level `IsIso ((pullback j).obj M).fromTildeΓ`; via two `pullbackComp`
  coherences chained `≪≫` + positional `@isIso_fromTildeΓ_of_iso _ _ _ e (isIso_fromTildeΓ_restrict_basicOpen …)`),
  `compositeBasicOpenImmersion_isOpenImmersion` (instance), `compositeBasicOpenImmersion_opensRange` (range
  half of (b): `j.opensRange = D(s)`). TOP `section_localization_hfr_basicOpen` + keystone + gap1 DEFERRED
  (3-bridge ring-identification build). iter-041 analogist confirmed **bridge-1 is DEFEQ** (no transport) —
  de-risking the assembly. Blueprint: producer-(b) block split into range (DONE) + f-locus (open) iter-041.

## iter-039 prover round (2 lanes; FBC conj-2b/2d landed [kill-criterion fired]; QUOT 3 gap1 feeders)
- **FBC conj-2b + conj-2d LANDED axiom-clean (+2 non-private).** `base_change_mate_reindex_conj_pullbackLeg`
  (conj-2b; one-liner `= Adjunction.conjugateEquiv_leftAdjointCompIso_inv`) + `base_change_mate_reindex_conj_crossLayer`
  (conj-2d; the ring-map-general port of Seam-1 `base_change_mate_unit_value` via `unit_conjugateEquiv_symm`
  raised by `conjugateEquiv_comp`). All three closing legs (conj-2b/2c/2d) now in hand. `_legs_conj` (sorry
  @~1822) UNCHANGED — the one-shot `conjugateEquiv.injective` reframing did NOT close. **Kill-criterion
  FIRED.** iter-040 plan-cycle analogist resolved the route: Fallback B (layer-by-layer conjugate transport,
  `analogies/fbc-legs-conj-injective-route.md`); iter-041 = FINAL in-loop FBC round.
- **QUOT 3 gap1 feeders LANDED axiom-clean (+3 non-private).** `isLocalizedModule_powers_transport` (combined
  bridge I+II combiner), `isLocalizedModule_basicOpen_descent_of_basicOpen_cover` (the instantiable basic-open
  cover form; general-U `_of_cover` is a recorded unprovable trap for quasi-coherent M), `isIso_fromTildeΓ_of_iso`
  (iso-invariance via `essImage.ofIso`). `descent_surj` gained an `(∃ s, U = D s)` precondition (both call
  sites updated). ALL gap1 consumers now built; sole residual = the geometric section-transport producer
  (decomposed iter-040 into a `\uses`-linked chain a–d + TOP `section_localization_hfr_basicOpen`).

## iter-038 prover round (2 lanes; GR PROPERNESS LANE CLOSED; QUOT semilinearity wall landed)
- **GR properness arc CLOSED (+6 axiom-clean) — `Gr(d,r)` proper over ℤ.** Assigned E4; prover blew past
  it since E1–E3 + cheap ingredients were in: `existence_chart_kpoint_eq` (top-triangle K-point identity,
  NEW public helper) → `existence_lift` (E4, `noncomputable def` → `sq.LiftStruct`; filler `Spec g' ≫ ι_J`;
  top triangle via E1+`g=algebraMap∘g'`+`existence_chart_kpoint_eq`, bottom via `specZIsTerminal.hom_ext`) →
  `valuativeExistence_toSpecZ` (E5) → **`isProper` (E6, `lem:gr_proper`)** + 2 private helpers
  (`liftToBaseOfMemRange`, `algebraMap_comp_liftToBaseOfMemRange`). Term-mode glue mandatory (keyed
  `rw`/`Spec.map_comp`/`Category.assoc` FAIL on `Spec.map (ofHom …)` over MvPolynomial/Away — Scheme-cat
  diamond; use `congrArg`/`.symm`/`calc`). Nothing further in this file's chain. Coverage block
  `lem:gr_existence_chart_kpoint_eq` added iter-039.
- **QUOT gap1 semilinearity wall LANDED (+2 axiom-clean non-private).** `gammaImageRingEquiv` (σ_V, built
  SOURCE→IMAGE `Γ(U,V) ≃+* Γ(Y, j ''ᵁ V)` via `(j.appIso V).commRingCatIsoToRingEquiv.symm` — load-bearing
  direction for bridge (I)/semilinearity typecheck; blueprint display flipped to match iter-039) +
  `gammaPullbackImageIso_hom_semilinear` (`hom (a•x)=σ_V a • hom x`; 3-line proof: unfold mapIso →
  `erw [Hom.app_smul]` → `rfl` on the `restrictScalars`-action defeq). Handed off precise 6-step Hfr
  assembly; critical path = step 1 (slice presentation ↔ scheme-pullback `IsIso fromTildeΓ` transport).

## iter-037 prover round (3 lanes; GR-E3full lane CLOSED; QUOT bridges landed; FBC tripwire fired)
- **GR-E3full — CLOSED (3 decls axiom-clean).** `det_one_updateCol` (private; column-substituted-identity
  det = `v p`, NO sign, via `Matrix.cramer_apply`+`mulVec_cramer` — `det_updateColumn` does NOT exist),
  `exists_minorDet_eq_free_entry` (free entry = ±signed minor via `det_permute'`+`Int.units_eq_one_or`),
  `existence_factor_through_valuationRing` (E3-full — every generator of `R^J` maps into `(algebraMap R K).range`
  via ratio-core + E2 bound + cofactor helper, then `MvPolynomial.induction_on`). Last matrix-algebra gap of
  GR existence. (blueprint blocks: `lem:gr_free_entry_eq_signed_minor` added iter-038.)
- **QUOT bridges (I)+(II) — landed axiom-clean (2 non-private decls).**
  `isLocalizedModule_of_ringEquiv_semilinear` (I — `IsLocalizedModule` across a ring iso + σ-semilinear
  `AddEquiv` pair; Mathlib only has same-ring `of_linearEquiv`) and
  `isLocalizedModule_restrictScalars_powers_algebraMap` (II — descend a localization at
  `powers (algebraMap R Rr f)` to `powers f`). Hfr assembly deferred (the semilinearity wall — iter-038 lane).
  (blueprint blocks added iter-038: `lem:isLocalizedModule_ringEquiv_semilinear`,
  `lem:isLocalizedModule_restrictScalars_powers_algebraMap`.)
- **FBC-A1 — assembly pass closed nothing (tripwire fired).** No code edits; step (a) and `_legs_conj` confirmed
  the same dependent-motive obstruction. Resolved iter-038 by analogist (KEEP, no refactor); the `_legs_conj`
  conjugate-side proof is the iter-039 prover round.

## iter-034 prover round (4 lanes; THREE keystones landed; net 0 active sorry; +~37 axiom-clean)

- **GR-sep LANE CLOSED (+7 axiom-clean, keystone landed).** `Grassmannian.isSeparated`
  (`lem:gr_separated`) axiom-clean via route (b). `Spec ℤ` genuinely terminal for `Scheme.{0}`
  collapses the glue to `IsTerminal.hom_ext`; `isSeparatedToSpecZ` is a faithful `Proj.isSeparated`
  port (per-patch closed immersion from `diagonalRingMap_surjective`). New decls: `toSpecZ`, `ι_toSpecZ`,
  `pullbackιIso_inv_fst`/`_snd`, `chartTransition_comp_chartIncl`, `isSeparatedToSpecZ`, `isSeparated`.
  Pitfalls captured: `convert!`/`pullback.map_fst` don't exist (use `convert … using 1`,
  `pullback.lift_fst`); `← Spec.map_comp` bare `rw` fails on the Scheme-cat diamond (route via `show`).
  Only `lem:gr_proper` remains in the GR cone.
- **QUOT gap1 P1 COMPLETE (+7 axiom-clean, keystone landed).** `isIso_fromTildeΓ_restrict_basicOpen`
  (`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent`) axiom-clean via the 5-step affine descent
  (Z-route): global presentation on `Z=(q.X i)` → single `Presentation.map` slice → `overRestrictPresentation`
  → iso-transport across `IsAffineOpen.isoSpec` (Final-based unit-iso, NOT open-immersion) →
  `isIso_fromTildeΓ_of_presentation`. The GENERAL `isIso_fromTildeΓ_presentationPullback` (form D
  consumes) also landed. New decls: `presentationPullbackιRestrict`, `opensMapEquivOfIso`,
  `opensMap_final_of_schemeIso`, `pullbackSchemeIsoUnitIso`, `presentationPullbackOfSchemeIso`,
  `isIso_fromTildeΓ_presentationPullback`, `isIso_fromTildeΓ_restrict_basicOpen`. Dead-end reconfirmed:
  open-immersion `pullback`-unit is NOT `Final`; the iso route sidesteps it.
- **FBC-B sub-lane + payoff DONE (`FlatBaseChangeGlobal.lean`, +13–15 axiom-clean).**
  `gammaTopEquivEqLocus` (Γ(M,⊤) ≅ₗ_A eqLocus leftRes rightRes via element-level sheaf axioms
  `eq_of_locally_eq'`/`existsUnique_gluing'`, NOT the categorical fork) + `baseChangeGammaEquiv`
  (flat base change commutes with the H⁰ equalizer, via `LinearMap.tensorEqLocusEquiv`). Full helper
  chain: `groundRing`/`rhoU`/`gammaModA`/`rhoU_comp`/`gammaResAHom`/`gammaResA`(+`_apply`/`_comp`)/
  `leftRes`/`rightRes`/`toCover`/`leftRes_toCover`/`toCoverEqLocus`. Base ring `A = X.presheaf.obj(op ⊤)`;
  A-module via `ModuleCat.restrictScalars rhoU`. Chain ASSEMBLY remains gated on FBC-A's affine sorry.
- **FBC-A 4→4 (PARTIAL, conj-0 foundation landed; `_legs` did NOT close → tripwire fired).**
  `pullbackComp_eq_leftAdjointCompIso` + `_inv` form: identifies the project pseudofunctor coherence
  `pullbackComp` with Mathlib's abstract `leftAdjointCompIso` (via `conjugateEquiv.injective`). Confirmed
  pinned Mathlib HAS the full `CompositionIso` calculus (`leftAdjointCompIso` @72,
  `conjugateEquiv_leftAdjointCompIso_inv` @82, `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` @140).
  conj-1 (codomain-read re-cut, new-def-then-bridge) + conj-2 (`_legs` discharge) deferred — see iter-035.

## iter-033 prover round (4 lanes, all PARTIAL / axiom-clean; net 0 sorry; FBC-A route ruled out)

- **FBC-A 4→4 (route ruled out — direct-on-sections ABANDONED).** Term-mode `congrArg` collapse of the
  trailing transparent `pushforwardComp(g', Spec φ).hom` factor to `𝟙` inside the locked `_legs` goal
  landed (green). Residual = cross-layer naturality (F2/F3 cancellers vs their codomain-read partners),
  needing `conjugateEquiv`/mate coherence the explicit-factor route cannot express. HARD-COMMIT boundary
  reached ⟹ iter-034 pivots to the conjugate-side re-encoding.
- **FBC-B → 0 sorry (NEW file `FlatBaseChangeGlobal.lean`, +3 axiom-clean).** L1
  `exists_finite_affineCover_inter_isQuasiCompact`, L2 `gammaIsLimitSheafConditionFork`, and the
  consolidation `exists_finite_affineCover_isLimit_sheafConditionFork`. BOTH Mathlib anchors verified to
  EXIST (`isSheaf_iff_isSheafEqualizerProducts`, `LinearMap.tensorEqLocusEquiv`). Coverage block for the
  consolidation corollary present (`lem:gamma_finite_equalizer_cover`).
- **QUOT-P1 4→4 (+4 axiom-clean, slice-touching crux closed).** `isIso_unitToPushforwardObjUnit_of_isIso'`
  (private), `overRestrictUnitIso`, `overRestrictPresentation`, `presentationPullbackιOfQuasicoherentData`
  — the slice→geometric Presentation transport. Keystone `isIso_fromTildeΓ_restrict_basicOpen` deferred
  (5-step recipe handed off). Coverage blocks added (writer `quot-cov`, iter-034): `def:over_restrict_unit_iso`,
  `def:over_restrict_presentation`, `def:presentation_pullback_iota_of_quasicoherentData`.
- **GR-sep 0→0 (+6 axiom-clean, ring heart done).** `transitionPreMap_minorDet_swap_mul`, `diagonalRingMap`
  + `_left`/`_right`/`_surjective` (the surjective restricted-diagonal comorphism — Proj's hardest analogue),
  `pullbackιIso` (e₂ source iso). Keystone `isSeparated` deferred (route (b) handed off). Coverage blocks
  added (writer `gr-cov`, iter-034): `lem:gr_transitionPreMap_minorDet_swap_mul`, `def:gr_diagonalRingMap`,
  `lem:gr_diagonalRingMap_left/right/surjective`, `def:gr_pullbackιIso`.

## iter-032 prover round (GR-glue CLOSED; QUOT gap1 bridge C CLOSED; FBC partial advance)

- **GR-glue LANE CLOSED (+8 axiom-clean).** `Grassmannian.scheme := (theGlueData d r).glued` now exists
  and is axiom-clean — the keystone of the Grassmannian construction. `cocyclePhiId` (Φ=id ring identity)
  proved by telescoping: `rotMid` recovers `cocycleΘJK` in the I,J,K frame, `cocycleCondition` collapses
  Θ_{I,J}∘Θ_{J,K}=Θ_{I,K}, leaving ONE inverse pair closed by the matrix engine `transitionInvImageMatrix`.
  Scheme-level `chartTransition'_cocycle` (`maxHeartbeats 1600000` for the `HasPullback`/`MvPolynomial`
  diamond); `Scheme.GlueData` bundle with `f_mono`/`f_hasPullback` by default `infer_instance`. New
  helpers: `rotMid`/`transitionInvImageMatrix`/`transitionInvPair` (private), `theGlueData`,
  `awayMulCommEquiv_comp_awayInclLeft`. Coverage blocks added (blueprint-writer `gr-cov`):
  `def:gr_the_glue_data`, `lem:gr_chartTransition'_cocycle`, `lem:gr_awayMulCommEquiv_comp_awayInclLeft`.
- **QUOT gap1 bridge C CLOSED (+4 axiom-clean).** `overRestrictIso` (the blueprint `\lean{}` pin) +
  `overRestrictEquiv` (step-3 module-category equivalence), `overRestrictFunctorIso` (step-4 functor-level),
  `overRestrictPullbackIso` (P1 consumer form). The named step-2 obstacle (geometric ring-sheaf
  identification) collapsed to `rfl` (`toScheme_presheaf` defeq); steps 3–4 via
  `pushforwardPushforwardEquivalence`/`pushforwardComp`/`pushforwardCongr` + `cat_disch`. Coverage blocks
  added (blueprint-writer `quot-cov`): `def:over_restrict_equiv`, `lem:over_restrict_functor_iso`,
  `lem:over_restrict_pullback_iso`; P1 node `\uses{}` updated. **P1 now unblocked** via
  `overRestrictPullbackIso` + `Presentation.map` + `isIso_fromTildeΓ_of_presentation`.
- **FBC 4→4 (partial advance, no sorry closed — budget boundary).** `_legs` proof advanced: a verified
  `simp only [base_change_mate_codomain_read_legs, …]` unfolds the variable-legs codomain read and
  distributes the LHS into atomic factors, exposing all cancellers syntactically. Two concrete blockers
  surfaced for the final round: (1) the 3 eCancel atoms + `inner_value_eq` are declared AFTER `_legs`, so
  prior rounds could not reference them — the route was NEVER executable; fix = INLINE the canceller
  content (`pullback_isEquivalence_of_iso`, `hom_inv_id_app`, `gammaMap_pushforwardComp_hom_eq_id`) ahead
  of `_legs`; (2) the codomain-read body sits behind three `Eq.mpr` casts from the `subst` — collapse via
  the concrete-legs `base_change_mate_codomain_read` before splicing. progress-critic `iter032`: STUCK
  (tripwire); strategy-critic `iter032`: CHALLENGE (parallelize FBC-B + ModuleCat fork). effort-breaker
  `fbcb`: FBC-B re-expressed as a 7-block `\uses`-linked chain (Mathlib sheaf-condition API located).

## iter-030 prover round (FBC distribution wall passed; QUOT bridge-C topological layer; GR no-output)

- **FBC 4→4 (mechanism advance, no sorry closed).** Built
  `base_change_mate_fstar_reindex_legs_link_distributeCollapse` (axiom-clean): both sides stated at the
  single composite functor `(Spec φ)_* ⋙ Γ_R` (one instance ⇒ `gammaDistribute` fires, no diamond), then
  factor-3 collapse in term mode. Spliced into the locked `_legs` goal via
  `refine (congrArg (fun z => _ ≫ (z ≫ _) ≫ _) (…distributeCollapse…)).trans ?_` — PASSED the step-(iii)
  distribution wall that blocked iters 026–029, now inside the locked main goal. Residual = eCancel
  telescoping of factors 2 & 4 against the unfolded `codomain_read_legs` across the `gammaPushforwardIso`/
  `MidColl` transport layer. → iter-031: blueprint reconciled (Path B, L1+L2→`distributeCollapse` block);
  prover builds the 3 remaining clean-term wrapper lemmas + assembles.
- **QUOT +6 axiom-clean (bridge-C topological layer).** `overEquivalence_sheafCongr` (the over-site↔
  open-subspace sheaf-category equivalence) + 4 (co)continuity/dense-subsite instances + `IsContinuous` of
  both functors — filled the explicit Mathlib `Topology/Sheaves/Over.lean` TODO. gap1 NOT closed; next
  obstacle now precisely identified: bridge-C step 2 = geometric ring-sheaf identification (was
  topos-theoretic). → iter-031: 6 coverage blocks added; prover builds step 2→3→4 ⟹ `overRestrictIso`.
- **GR — no output** (no edits; 2nd consecutive iter). ROOT-CAUSED iter-031: a 0-sorry file is silently
  dropped by the no-op objective filter (`sorry_count.py`) unless the objective text carries a scaffold
  keyword; prior "NEW-declaration build" wording did not match. A dispatch-wording bug, NOT a math wall
  (the cocycle reduction is solved per the in-file HANDOFF). → iter-031: objective re-worded with a
  scaffold keyword; standalone `lem:gr_cocycle_phi_id` blueprint block added.

## iter-029 prover round (FBC definitive diagnosis + riders; QUOT finite-cover front; GR no-output)

- **FBC 4→4 (no sorry closed; definitive negative diagnosis + compiling riders).**
  `base_change_mate_fstar_reindex_legs` @1335: proved CONCLUSIVELY that the entire keyed-rewriting family
  (rw/simp/erw/conv/set/dsimp) is defeated by the `X.Modules` instance diamond — even `rw` of a `rfl`-true
  `have` whose LHS is the goal's own printed factor fails (`kabstract` can't see through the comp-instance
  diamond), and even `rw [Category.comp_id]` can't find `?f ≫ 𝟙`. Established the defeq map (factor-2 / G3
  = `rfl`-trivial; G1/G2/G4 = genuine isos). Route pinned: ONE hand-built `exact`/`convert` term splicing
  the SHIPPED atoms on clean separately-elaborated terms, bridging the diamond only at the final `exact`.
  Riders (all compile): removed dead `hpfc`; de-privated the 3 `gammaMap_*` atoms (@1174/1182/1193 — pins
  now resolve); fixed the 2 false "sorry-free" docstrings (@1838/@1907 → "transitively sorry-backed via
  gstar_transpose"). `gstar_transpose` untouched (gated on `_legs`, same diamond). → iter-030 corrective:
  effort-breaker `fbc-legs` decomposed `_legs` into 5 clean-term link sub-lemmas (single-instance, no
  diamond), assembled by one closing `exact`.
- **QUOT +1 axiom-clean (`exists_finite_basicOpen_cover_le_quasicoherentData`).** The topological
  finite-cover front of the gap1 transport. gap1 itself NOT added — blocked on the per-element presentation
  transport (`q.presentation i` slice instances time out synthInstance). → iter-030 corrective:
  mathlib-analogist `quot-transport` returned the corrected decomposition (restriction functor EXISTS in
  Mathlib; real gaps = (C) `overRestrictIso` + (D) section-localization descent; slice timeout tamed by
  `backward.isDefEq.respectTransparency false`).
- **GR — no output** (no edits committed; the cocycle ring-identity lane produced nothing iter-029). →
  iter-030: re-dispatch with sharpened directive (prove `Φ=id` as a STANDALONE named lemma first).

## iter-028 prover round (3 lanes: FBC inner_value cascade + QUOT gap1 reduction + GR t'/t_fac)

- **FBC `base_change_mate_inner_value_eq` CLOSED** (5→4 sorry) via the one-line cascade
  `exact base_change_mate_fstar_reindex ψ φ M` (removed a redundant walled inline reproof). Root crux
  `base_change_mate_fstar_reindex_legs` @1445 PARTIAL — blocked by the `X.Modules` instance diamond
  (composed-⋙ vs nested-obj `Functor.map` domain): `rw`/`simp` no-match, `erw` whnf-timeout. The collapse
  fact IS available (`hpfc`) but unapplicable by keyed rewriting. RESOLUTION (iter-029 analogist): the GR
  term-mode recipe ports directly — splice the SHIPPED eCancel atoms via `congrArg`/`.trans`/`exact`.
- **QUOT G1-core reduced to a SINGLE lemma.** +2 axiom-clean decls
  (`isLocalizedModule_basicOpen_of_presentation`, `map_units_restrict_basicOpen` — map_units holds
  unconditionally). Established G1-core ≡ gap1 ≡ `isIso_fromTildeΓ_of_isQuasicoherent` (the iff + the
  3-field engine already in-file from iter-026). Mathlib has NO bridge (source-grep verified); the
  local/stalk shortcuts do NOT avoid it. Handed off the sub-build `exists_isIso_fromTildeΓ_basicOpen_cover`.
- **GR `t'`/`t_fac` + ring identity CLOSED.** +4 axiom-clean decls (`chartTransition'`,
  `chartTransition'_fac`, `chartTransition'_ringIdentity`, `awayMulCommEquiv_comp_algebraMap`). The
  `HasPullback` instance diamond on `chartTransition'_fac` resolved via `erw [awayPullbackIso_inv_snd]` +
  `exact congrArg (_≫·)` + `Iso.inv_comp_eq` (defeq-inside-`exact`). `cocycle` categorical reduction
  solved; residual = the ring identity `Φ = id` (rotated `cocycleCondition`), handed off.

## iter-026 prover round (3 lanes: FBC erw-unlock + QUOT glue + GR transition layer)

- **FBC literal-form lock BROKEN (4-iter blocker, iters 018–024) — `erw` fires where `rw` cannot.**
  `base_change_mate_fstar_reindex_legs` now performs the `(g')`-unit expansion (the step 4 prior iters
  could not pass) via `erw [base_change_mate_fstar_reindex_legs_unitExpand e.hom (Spec.map inclA) (tilde M)]`
  — defeq match succeeds where syntactic `rw` misses on invisible implicit args (re-verified `rw` fails in
  5 arg-forms). Memory `fbc-subst-legs-literal-form-lock` updated. Sorry count flat 5→5; residual = the
  ~100-LOC cancellation assembly (term-mode `_gammaDistribute` distribution → unfold codomain read → 3
  proved atoms → Seam 1 transport). The inline `inner_value_eq` pre-subst route is CONFIRMED WALLED (leg
  only propositionally equal) — live route is via `_legs`. NOT yet a closed obligation; recorded as the
  verified-advance milestone.
- **QUOT downstream glue `G1-core ⟹ gap1 ⟹ keystone` CLOSED axiom-clean (5 decls).**
  `isIso_fromTildeΓ_of_isLocalizedModule_restrict` (G1-assemble: per-basic-open localization ⟹
  `IsIso M.fromTildeΓ`), `isIso_fromTildeΓ_iff_isLocalizedModule_restrict` (capstone iff),
  `isIso_sheaf_of_isIso_app_basicOpen` (private; iso-on-basis ⟹ sheaf iso via stalks),
  `bijective_comp_of_localizations` (private; diamond-safe, instances explicit). The keystone's remaining
  obligation is now EXACTLY G1-core. Diamond pitfall: `set`-binding the two localization maps zeta-unfolds
  and loses the `IsLocalizedModule` instance — pass as explicit hypotheses (`bijective_comp_of_localizations`).
- **GR scheme-level transition layer + linchpin pullback iso CLOSED axiom-clean (11 decls).**
  `minorDet_self`, `chartOverlap`/`chartIncl`(`_isOpenImmersion`/`_self_isIso`), `chartTransition`(`_self`)
  — the 7 "easy" `Scheme.GlueData` fields — plus `awayPullbackIso` (pullback of two `Spec` away-localizations
  ≅ `Spec` of the away-product), its two leg lemmas `awayPullbackIso_inv_fst/_snd`, and `awayMulCommEquiv`
  (the `orderSwap` `Away(a·b) ≃+* Away(b·a)` resolving the product-order subtlety in `t'`). Pitfall: plug
  the heavy chart ring `MvPolynomial … ℤ` into `IsScalarTower`/tensor synthesis directly ⟹ 20000-heartbeat
  timeout; state `awayPullbackIso` over a generic base ring `A` and instantiate. GlueData itself
  (`t'/t_fac/cocycle/.glued`) NOT yet built — construction volume, precise decomposition handed off.

## iter-024 closed (parent; reflected in the extracted tree)

- **FBC 3 `inner_eCancel` atoms CLOSED axiom-clean** — `base_change_mate_inner_eCancel_eUnit`
  (`haveI := pullback_isEquivalence_of_iso e; infer_instance`),
  `..._pushforwardComp` (`congr_map`/`map_id` term-mode chain; naive `Functor.map_id` finisher fails),
  `..._pullbackComp` (`(pullbackComp _ _).hom_inv_id_app (tilde M)`; no `intro` — binders auto-introduced).
- **FBC Seam B `base_change_mate_gstar_generator_close` CLOSED axiom-clean** — residual element identity
  `ρ.hom x = regroupEquiv.inv (1⊗ₜx)` closes by **`rfl`** (both reduce to `(1:A⊗_R R')⊗ₜ[A] x`); the
  iter-023 conjectured `inner_value_apply`/`regroupEquiv_inv_one_tmul` re-break was unnecessary.
- **QUOT 2 affine engines CLOSED axiom-clean** — `isLocalizedModule_tilde_restrict` (basic-open
  restriction of `tilde N` localizes; Mathlib `IsLocalizedModule(.powers f)(tilde.toOpen N (D f))` +
  `tilde.isoTop` + `tilde.toOpen_res` + `of_linearEquiv_right`) and
  `isLocalizedModule_restrict_of_isIso_fromTildeΓ` (transports it across `[IsIso M.fromTildeΓ]` via the
  `modulesSpecToSheaf` naturality square). These are the keystone's affine ingredients; blueprinted
  iter-026 (coverage debt cleared). Keystone `isLocalizedModule_basicOpen` itself NOT built — gated on
  the gap1 descent, re-decomposed iter-026 to G1-core (see iter-026 plan).

## iter-023 closed

- **FBC Seam C `base_change_mate_gstar_counit_transport` — CLOSED axiom-clean.** The counit dual of
  Seam-1's `unit_conjugateEquiv_symm`, generalized over an arbitrary `W : (Spec R').Modules`. Lifted from
  the inline `huce` scaffold inside `gstar_transpose`: `set adjL/adjR/β` + `hpullinv` (by `rfl`) +
  `conjugateEquiv_counit_symm` + two `Adjunction.comp_counit_app` splits. First sorry-elimination in the
  gstar K-window — vindicates the iter-023 effort-breaker decomposition.
- **GF `genericFlatness` correctness fix.** Re-signed with `[QuasiCompact p]` (was FALSE with only
  `[LocallyOfFiniteType p]`; counterexample `⊔ᵢ Spec ℤ → Spec ℤ`). `Nonempty`/`IsDomain`/`IsNoetherianRing`
  for `A := Γ(S,U₀)` discharged sound (no sorry). Not protected, no consumers — safe re-sign.

## iter-022 closed

- **GF algebraic core `genericFlatnessAlgebraic` — CLOSED axiom-clean** (`{propext, Classical.choice,
  Quot.sound}`). The §4-dévissage non-torsion branch over `C := B ⧸ p.asIdeal`: reduce `N ≅ C`, torsion
  split, Noether normalisation (L4) + polynomial core (L5) + ring↔module localisation bridge + descent
  (`free_localizationAway_of_away_tower`). Bridge: `IsLocalizedModule.iso (powers g) (toAlgHom A C Cg)`
  upgraded A-linear→A_g-linear by `LinearEquiv.extendScalarsOfIsLocalization`. Two enabling NON-protected
  changes: L4 gained a 4th existential conjunct (tower-compatibility of the `awayMap`), and the decl
  narrowed to single-universe `(A B M : Type u)`. **GF-alg phase COMPLETE** — only remaining GF sorry is
  geometric `genericFlatness` (@~2173). DIAMOND pitfall: hand-built `Algebra A Cg` via `letI` is an
  `isDefEq` dead end — use ambient instances; needs `maxHeartbeats 1600000`.

## iter-019 prover round (3 lanes: FBC route-swap + GF L4 injectivity + QUOT keystone; all axiom-clean)

- **QUOT SNAP-S2 keystone assembled end-to-end + finiteness transfer CLOSED (axiom-clean).**
  `gradedModule_hilbertSeries_rational` (the Stacks-00K1 ambient subquotient induction) is wired
  end-to-end: `subquotient_finite_transfer` (the 3-iter blocker — σ-semilinear transfer along
  `lastVarAlgHom : κ[t₀..t_r]↠κ[t₀..t_{r-1}]` + `Module.Finite.of_surjective`, defeq-carrier quotient
  trick), the `SubquotientDatum.ker`/`.coker` constructors, the `P(r)` induction
  `subquotient_hilbertSeries_rational`, and the `(⊤,⊥)` bridge — all axiom-clean. +17 decls; the only
  residual is the base-case `iSupIndep` leaf (route (b) queued). Blueprinted iter-020
  (`quot-iter020`: base-case block + 16 coverage blocks).
- **GF L4 injectivity crux CLOSED (axiom-clean).** `exists_localizationAway_finite_mvPolynomial`
  injectivity half fully proved: comparison maps ν=`IsLocalization.lift`, ψ; generators bⱼ; φ=`aeval b`;
  the awayMap compatibility square `hsquare`; `Function.Injective φ` via `ν∘φ = gK∘map ψ` (composite of
  injectives). New reusable helper `isLocalization_lift_injective` (blueprinted
  `lem:gf_isLocalization_lift_injective`). Residual = the L4 finiteness conjunct only.
- **FBC route swap — `base_change_mate_domain_read` built axiom-clean; Seam-2 crux bypassed.** A refactor
  (`fbc-decouple-legs`) constructed the domain read `Γ(g'^*(f'_*(tilde M))) ≅ R'⊗_R A⊗_A M`
  (axiom-clean) + `pullback_fst_snd_specMap_tensor`, and re-routed `base_change_mate_section_identity` to
  derive from `domain_read` + `codomain_read` + Seam-3 `gstar_transpose` — making the 6-iter-stuck
  Seam-2 `fstar_reindex` mate-unwinding crux **dead code**. Blueprint reconciled iter-020
  (`fbc-reroute`: 3 phantom blocks deleted, `fstar_reindex` apparatus marked superseded). Live FBC crux
  is now Seam-3 `gstar_transpose`.

## iter-017 prover round (3 lanes: FBC refactor + GF L5 + QUOT Route-2; all axiom-clean)

- **GF L5 `exists_free_localizationAway_polynomial` (CLOSED, axiom-clean).** The OreLocalization
  instance-presentation diamond (2-iter blocker, iters 015–016) DEFUSED by dropping the redundant
  canonical 6th existential (`Module A_g T_g`, always `inferInstance`) from `gf_torsion_reindex` —
  bundling it created an opaque fvar breaking instance matching on the doubly-localised carrier. After
  the drop, the recorded IH+descent assembly closes verbatim. `gf_torsion_reindex` re-verified
  axiom-clean post-simplification.
- **FBC Seam-2 motive wall DISSOLVED (4 axiom-clean sub-lemmas).** `base_change_mate_codomain_read_legs`
  (variable-legs codomain read — the subst-able device) + 3 Γ-collapse lemmas
  (`gammaMap_pushforwardComp_hom_eq_id`, `…_inv_eq_id`, `gammaMap_pushforwardCongr_hom`). The concrete
  `base_change_mate_fstar_reindex` is now sorry-free (reduces to `…_legs` by `exact`). The multi-iter
  "motive is not type correct" wall is gone; the Seam-2 content sorry shrank to an isolated single
  affine goal (step-iii mate-unwinding) inside `base_change_mate_fstar_reindex_legs`. Blueprinted
  iter-018 (5 pins, FBC coverage debt → 0).
- **QUOT Route-2 D6 + ambient homogeneity calculus (13 axiom-clean decls).** Keystone D6
  `subquotient_degreewise_diff` (single κ-linear-map route, avoids `N'≤N` and quotient constructions)
  + `subquotientHilb` + the full ambient homogeneity calculus (`RaisesDegree`(`.mem`),
  `decompose_raisesDegree`(`_zero`), `comap/map/inf/sup_isHomogeneous`, `map_inf_degree_eq`,
  `sup_inf_degree_eq`, private `finrank_comap_subtype`). No isDefEq/whnf pathology fired (Route-2
  validated). Blueprinted iter-018 ("Ambient homogeneity calculus" subsubsection, QUOT coverage debt
  → 0 modulo the intentionally-private `finrank_comap_subtype`).

## iter-016 prover round (2 lanes: FBC + GF; both landed axiom-clean)

- **FBC `pullbackPushforward_unit_comp` (NEW, axiom-clean).** Pseudofunctoriality of the
  pullback–pushforward unit — the leg-reindex engine the Seam-2 recipe needs. Built via
  `CategoryTheory.unit_conjugateEquiv` for the composite adjunction +
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv` + `Adjunction.comp_unit_app`. `N` lives on the
  codomain `X₃`. Wired into Seam 2 as `have key`. Blueprinted iter-017 (`lem:pullbackPushforward_unit_comp`
  + 3 `\mathlibok` anchors).
- **GF `free_localizationAway_of_away_tower` (CLOSED, axiom-clean).** The tower-descent helper (CHURNING
  corrective). Witness `f := g·a`; module side `IsLocalizedModule (powers (g·a))` via `IsBaseChange.comp`
  (compose the two localisation base changes `A→A_g→A_h`); freeness transport via
  `IsLocalization.algEquiv` + `Module.Basis.mapCoeffs σ.symm` + `LinearEquiv.extendScalarsOfIsLocalization`
  + `Module.Free.of_equiv'`; ring side `IsLocalization.Away.mul_of_associated`. Needs
  `synthInstance.maxHeartbeats 1000000` (doubly-localised carrier; succeeds, not looping).

## iter-012 prover round (4 lanes) + iter-013 DAG (coverage debt → 0)

- **GrassmannianCells — DONE (file GREEN, 0 sorry).** `lem:gr_cocycle` (`cocycleCondition`) CLOSED
  axiom-clean + 11 supporting decls (`awayInclLeft/Right`(`_comp_algebraMap`), `transitionPreMap_
  minorDet`, `cocycleΘIJ/JK/IK`, `cocycle_imageMatrix_eq` + privates). Whole triple-overlap/cocycle
  infra built from scratch this iter; verified `{propext, Classical.choice, Quot.sound}`. The GR-cells
  phase is complete; next GR target `def:gr_glued_scheme` needs a gluing API (out of this file).
- **FBC (partial, intentional decomposition).** `base_change_mate_inner_value` (ρ) PROVEN
  axiom-clean; `base_change_mate_section_identity` proved modulo Seam 3 (own body sorry-free, via
  `Adjunction.homEquiv_counit` counit factorization). 3 typed seam holes remain (unit_value/fstar_
  reindex/gstar_transpose) — closed by the iter-014 abstract-conjugate route.
- **GF (partial).** `gf_torsion_reindex` — the hard content `Module.Finite (P_g/⟨F_g⟩) T_g'` landed
  and compiles; residual (a)–(e) bookkeeping is the iter-014 helper-factoring must-close.
- **QUOT (SNAP-S2 power-series engine, 8 decls axiom-clean).** `rationalHilbert_antidiff`,
  `IsRatHilb` (+ `.ofEventuallyZero/.bump/.sub/.shiftRight/.antidiff/.ofDiffEq`),
  `coeff_invOneSubPow_one_mul` — the COMPLETE power-series half of Stacks 00K1.
- **iter-013 DAG.** All 44 prover-generated `lean_aux` helpers blueprinted (1-to-1 Lean↔tex
  COMPLETE); leandag 0 isolated / 0 broken-uses / 0 axioms; whole-blueprint reviewer PASS.

## iter-011 prover round (4 lanes, all axiom-clean; 0 must-fix in review)

- **GrassmannianCells** — STUCK→DONE: 16 axiom-clean decls landed (`universalMatrix`, `minorDet`,
  `universalMinor`, `isUnit_det_universalMinor`, `universalMinorInv`, `universalMinorInv_mul_cancel`,
  `imageMatrix`, `transitionPreMap`, `isUnit_transitionPreMap_minorDet`, `transitionMap`,
  `transitionMap_self` + 3 matrix helpers + 2 lemmas). File GREEN, 0 sorry. The `def:gr_transition`
  monolith (2-iter zero-output wall) broken via the iter-011 effort-break + fast-path.
- **GF (3 Nagata dévissage sub-lemmas)** — `gf_torsion_annihilator`, `gf_nagata_monic_lastVar`,
  `mvPolynomial_quotient_finite_of_monic_lastVar` (`lem:gf_mvPolynomial_quotient_finite_monic`,
  `RingHom.Finite` encoding) PROVED axiom-clean; wired into `gf_torsion_reindex` body (typechecks).
- **QUOT (5 predicate/annihilator decls)** — `Scheme.Modules.annihilator` (`def:modules_annihilator`,
  via `IdealSheafData.ofIdeals`, no bridge), `annihilator_ideal_le`, `schematicSupport`
  (`def:schematic_support`), `schematicSupportι`, `HasProperSupport` (`def:has_proper_support`).
  Axiom-clean.
- **FBC `base_change_mate_regroupEquiv`** — re-closed axiom-clean on the `eT` identity-bridge +
  `TensorProduct.induction_on` route; the multi-iter `map_smul'` transparent-instance wall (open
  since iter-008) broken via `erw [TensorProduct.zero_tmul]`. 2 zero-branch sorries eliminated.

## GF-alg — `Picard/FlatteningStratification.lean` (iter-008)

- `gf_generic_rank_ses` (`lem:gf_generic_rank_ses`) — the generic-rank SES
  `0→P_d^{⊕m}→N→T→0`, `m := finrank (FractionRing P_d) (LocalizedModule (P_d)⁰ N)`, built over
  `P_d` directly (no `g`-inversion). PROVED axiom-clean (`[propext, Classical.choice, Quot.sound]`).
- `gf_clear_one_denominator` (`lem:gf_clear_one_denominator`) — clears one polynomial's
  denominators via `IsLocalization.exist_integer_multiples` over `p.support`; encoded with
  `IsLocalization.map` (avoids the missing `Algebra (Localization.Away g) (FractionRing A)`).
  PROVED axiom-clean.

## QUOT-defs — `Picard/QuotScheme.lean` + `Picard/GrassmannianCells.lean` (iter-007)

- `Grassmannian.affineChart` (`def:gr_affine_chart`) — `Spec ℤ[X^I]` on the `d(r-d)` free entries;
  axiom-clean. GrassmannianCells.lean now 0 real sorry (one stale docstring remains).
- `SheafOfModules.IsLocallyFreeOfRank` (`def:is_locally_free_of_rank`) — rank-`d` local-freeness
  predicate (open cover + `O_U^d` isos via `Scheme.Modules.pullback`/`SheafOfModules.free`),
  axiom-clean. (`X.Opens` formulation; `Scheme.OpenCover` route fails on universe inference.)
- `Module.annihilator_isLocalizedModule_eq_map` (engine lemma, `lem:annihilator_localization_eq_map`)
  — `Ann(S⁻¹M) = (Ann M)·S⁻¹R` for f.g. `M`; missing-from-Mathlib, axiom-clean. Blueprint block
  added iter-008.

## FBC-A — `Cohomology/FlatBaseChange.lean`

- `pullback_fst_snd_specMap_tensor`, `base_change_mate_domain_read`,
  `base_change_mate_codomain_read` (L1/L2/L3 reads) — iter-003, axiom-clean.
- `pullbackIsoEquivalenceOfIso`, `pullback_isEquivalence_of_iso` (helpers) — iter-003.
- `base_change_regroup_linearEquiv` (L4-a pure-tensor core, `(A⊗_R R')⊗_A M ≃ₗ[R'] R'⊗_R M`)
  — iter-004, axiom-clean. iter-006: MOVED to new file `Cohomology/RegroupHelper.lean`
  (separate compilation unit, normalises the `Module A (A⊗_R R')` diamond).
- `base_change_mate_generator_trace` (L4-c IsIso corollary) — iter-004 (body closed;
  transitively on `…_generator_trace_eq`).
- All tilde-dictionary lemmas (`pushforward_spec_tilde_iso`, `pullback_spec_tilde_iso`,
  `gammaPushforward*`, etc.) — pre-iter-002 / inherited, axiom-clean.
- `base_change_map_affine_local` — proved (locality reduction).

## GF-alg — `Picard/FlatteningStratification.lean` (`GenericFreeness`)

- `exists_free_localizationAway_of_finite`, `…_of_moduleFinite`, `…_of_torsion` (L1),
  `exists_flat_localizationAway_of_finite` — iter-002/003, axiom-clean.
- L3 chain (iter-004, all axiom-clean):
  `exact_localizedModule_powers_of_shortExact` (L3a),
  `free_localizationAway_of_free_of_eq_mul` (L3b, the 553-effort node),
  `free_of_shortExact_of_free_free` (L3c),
  `exists_free_localizationAway_of_shortExact` (L3 assembly).
- `exists_free_localizationAway_polynomial` d=0 base + d≥1 torsion sub-case — iter-003/004.

## iter-014 closed (both hard-must-close targets, axiom-clean)

- **FBC Seam 1** `base_change_mate_unit_value` — CLOSED iter-014, `{propext, Classical.choice,
  Quot.sound}`. The conjugate-unit calculus (`unit_conjugateEquiv_symm` + tilde–Γ right-triangle
  `tilde.adjunction.right_triangle_components`); recipe `analogies/fbc-mate.md`. `section_identity` /
  `generator_trace` / `cancelBaseChange` now proven MODULO Seam 3.
- **GF reindex** `gf_torsion_reindex` — CLOSED iter-014, axiom-clean. Factored (a)–(e) into 5 helpers
  (`pullbackModuleAddEquiv`, `finite_of_pullbackModuleAddEquiv`, `pullback_isScalarTower`,
  `finite_of_quotientRingEquiv`, `isLocalizedModule_restrictScalars`); `ebar` via
  `IsLocalization.ringEquivOfRingEquiv` (NOT `algEquivOfAlgEquiv` — dead end on doubly-indexed rings);
  action-diamond resolved via `LinearEquiv.extendScalarsOfIsLocalization`. Blueprinted iter-015
  (`lem:gf_pullback_module_transport`, `…_finite_of_quotient_ringequiv`,
  `…_islocalizedmodule_restrictscalars`).

## iter-021 closed

- **GF L4 finiteness leaf** `exists_localizationAway_finite_mvPolynomial`
  (`lem:gf_noether_clear_denominators`) — CLOSED axiom-clean. Witness `g := g0·g1`; per-generator
  denominator clearing via the Mathlib collapsing lemma
  `IsIntegral.exists_multiple_integral_of_isLocalization` (NOT a per-coefficient
  `gf_clear_one_denominator` fold — blueprint step-2 corrected iter-022 to match). The ν/ψ/b/φ/hsquare
  injectivity scaffolding transferred verbatim `g0→g`. L4 + L5 now both closed ⟹
  `genericFlatnessAlgebraic` is pure §4-dévissage assembly (sole gap = ring↔module bridge, Mathlib-
  confirmed iter-022).

## iter-020 / iter-021 closed

- **QUOT SNAP-S2 keystone** `gradedModule_hilbertSeries_rational` (Stacks 00K1 graded Hilbert–Serre
  rationality) — CLOSED axiom-clean iter-020 via `subquotient_base_eventuallyZero` (ROUTE (b) ambient
  degree-i membership; new helper `iSupIndep_map_of_mem_ker_sup`). The Mathlib-ABSENT rationality bridge
  of SNAP. No `isDefEq` pathology (validates the Route-2 ambient-carrier pivot).
- **GF dévissage** `genericFlatnessAlgebraic` motive + subsingleton + short-exact obligations — CLOSED
  axiom-clean iter-020 (`Module.compHom` restricted-A-action; B/𝔭 obligation remains, bottoms at L4).
- **QUOT file-split** (iter-021, refactor `quot-split`) — `GradedHilbertSerre.lean` extracted (graded
  layer, 1287 lines, 0 sorries); `QuotScheme.lean` trimmed to 423 lines (Quot-defs + 4 protected stubs);
  11 decls de-privatized (IsRatHilb toolkit + `finrank_comap_subtype` + `iSupIndep_map_of_mem_ker_sup`);
  stale "RESIDUAL LEAF/OBSTRUCTION" comment removed. Honors the standing user parallelism directive;
  clears M1 (QUOT toolkit). Both modules build clean.
- **Coverage debt** (iter-021) — blueprinted `lem:graded_finrank_comap_subtype` +
  `lem:graded_iSupIndep_map_of_mem_ker_sup`; wired into consumers' `\uses{}`. leandag 0 unknown_uses.

## iter-035 closed (axiom-clean infra; 2 keystones reduced to single obligations)

- **QUOT gap1-D cover form** `Scheme.Modules.isLocalizedModule_basicOpen_descent_of_cover` — CLOSED
  axiom-clean (Stacks `lemma-invert-f-sections` / Hartshorne II.5.3, cover-hypothesis form). +6 decls
  (1 public keystone + 5 private: `descent_surj`/`descent_smul_eq_zero`/`descent_overlap_agree`/
  `res_comp`/`iSup_basicOpen_subtype_eq_top`). Direct sheaf-gluing of the 3 `IsLocalizedModule` fields;
  does NOT route through the global `QCoh≃Mod` equivalence (= gap1 itself). Named form
  `isLocalizedModule_basicOpen_descent` + gap1 stay gated solely on the `Hfr` slice→`Spec R_r` SECTION
  transport (`Γ(pullback ι M,⊤)≅Γ(M,image)`). Memory `quot-gap1d-descent-and-modulecat-restriction-termmode`.
- **GR-proper reduction** — `Grassmannian.isProper` reduced to the SINGLE obligation
  `ValuativeCriterion.Existence (toSpecZ d r)` via `isProper_of_valuativeExistence` (+ the three cheap
  ingredients `compactSpace_scheme`/`quasiCompact_toSpecZ`/`locallyOfFiniteType_toSpecZ`/
  `quasiSeparated_toSpecZ`/`valuativeUniqueness_toSpecZ`). Existence algebraic core
  `transitionPreMap_minorDet_mul` (E3 minor-ratio identity) landed. +7 decls, axiom-clean. Remaining =
  E1 (chart factorization, primary missing Mathlib API) / E2 / E3-combinatorics / E4.
- **FBC-A conjugate route EXHAUSTED (trip-wire FIRED).** Atomized conjugate chain ran: +7 sorry-free
  decls (conj-1a/1b/2c, `conjPullbackFactor`[+eq], param[+eq_param]); `_legs` body made sorry-free thin
  wrapper. Residual sorry MOVED into conj-2a `base_change_mate_fstar_reindex_legs_conj` (the
  section-composite→`conjugateEquiv`-component reframing, 5-iter wall). Route abandoned per trip-wire;
  iter-036 pivots to affine-local explicit-inverse + element-`ext`.

## iter-036 closed (axiom-clean infra; each lane advanced to a single named residual)

- **FBC step (b) LANDED** — `base_change_mate_gstar_generator_close` / `base_change_mate_extendScalars_inner_value_counit`
  axiom-clean (`ext`→`Counit.map_apply_one_tmul`→`congrArg _ rfl`): `extendScalars ψ (ρ) ≫ ε^alg = regroupEquiv.inv`
  on the generator. Tripwire did NOT fire. `gstar_transpose` (@2167) now needs only inline step-(a) reindex
  (from the proved `inner_eCancel_*` atoms) + dictionary cancellation; step (c) master `huce`
  (`gstar_counit_transport`) also proved/assembled. The two are redundant variants → iter-037 consolidates.
- **QUOT `gammaPullbackTopIso` + general-in-V + naturality LANDED** — the whole `lem:pullback_gamma_top_iso`,
  axiom-clean. `gammaPullbackImageIso` via `Functor.mapIso` of `restrictFunctorIsoPullback.symm.app M`
  (sidesteps the failing `IsIso (φ.app U)` synthesis); `gammaPullbackImageIso_hom_naturality` = the
  abelian-presheaf naturality square; `gammaPullbackTopIso` = the `U=⊤` instance via
  `image_top_eq_opensRange`. Hfr is NOT a one-liner after it: two Mathlib-absent ingredients remain —
  (I) ring-iso-semilinear `IsLocalizedModule` transport, (II) base-change-of-localization `R→R_r` (iter-037).
- **GR E1 + E2 + E3-ratio-core LANDED** — `existence_chart_factorization` (E1; `IsOpenImmersion.lift` +
  `Spec.preimage` + field-`Spec` subsingleton), `existence_minimal_valuation` (E2; `Finite.exists_max` of
  `ValuationRing.valuation`), `existence_lift_transitionPreMap_minorDet_mul` (E3 ratio core;
  `IsLocalization.Away.lift` of `transitionPreMap_minorDet_mul`). All axiom-clean. E3-full
  (`existence_factor_through_valuationRing`) blocked on the cofactor-expansion matrix helper (det of a
  column-substituted identity = entry up to sign) — iter-037 target via `Matrix.cramer_apply`/`det_succ_column`.

## iter-041 closed (QUOT gap1 — lane-defining close)

- **QUOT gap1 CLOSED axiom-clean.** 7 new non-private decls in `QuotScheme.lean`
  (`#print axioms` = `{propext, Classical.choice, Quot.sound}`): `image_basicOpen_of_affine`,
  `compositeBasicOpenImmersion_image_basicOpen`, `image_basicOpen_eq_inf`,
  `section_localization_hfr_aux` (opaque-`j` core), `section_localization_hfr_basicOpen` (TOP),
  `isLocalizedModule_basicOpen_descent` (keystone), `isIso_fromTildeΓ_of_isQuasicoherent` (gap1).
  The ~14-iter section-localization-descent arc (Hartshorne II.5.3 / Stacks invert-f-sections,
  built WITHOUT global QCoh≃Mod) is complete. Load-bearing lesson: keep the composite immersion `j`
  OPAQUE in helpers (concrete triple-composite → >3.2M-heartbeat whnf runaway). gap1 unblocks
  G1-core / GF-G1 / annihilator forward direction.
- **FBC `_legs_conj` — conjugate route EXHAUSTED in-loop (FINAL round).** No new decls; added a
  verified in-proof Γ-collapse stage (collapses 2/3 transparent coherences). The multi-layer
  composite-`conjugateEquiv` recognition (S2) is a bespoke Mathlib-absent construction unclosed
  across iters 037–041. Per armed protocol: route closed off, pivot to affine tilde-transport.

## iter-044 — QUOT gap2 CLOSED axiom-clean (ends the ~16-iter section-localization arc)
- **`isLocalizedModule_basicOpen`** (`lem:qcoh_section_localization_basicOpen`, QuotScheme.lean) — gap2
  keystone, kernel-clean (`{propext, Classical.choice, Quot.sound}`). Built via Piece A route-1 chain L1–L6
  + 2 helpers + Piece B bridge (iter-043). 11 axiom-clean decls total, 0 new sorries.
  - L1 `overRestrictUnitIsoInv` (equivalence-transport — bypassed the IsContinuous/↥V-coercion gateway),
    `pullbackOpenImmersionUnitIso` (open-imm pullback-unit IS Final via open-map adjunction), L2
    `overRestrictPresentationInv`, L3 `pullbackPreimageιIso`+`presentationPullbackιPreimage`, L4
    `isQuasicoherent_over_preimage` (dot-notation `.IsQuasicoherent`), L5 `coversTop_preimage`, L6
    `isQuasicoherent_pullback_of_isOpenImmersion` (`q.shrink` for `of_coversTop` universe), target
    `isQuasicoherent_pullback_fromSpec`. All axiom-clean; coverage debt (blueprint blocks) cleared.
  - Consumed by: GF-G1 (iter-045) and the QUOT annihilator reverse inclusion (iter-046).

## iter-045 — GF-G1 locality half DONE + FBC keystone scaffolds (PARKED)
- **GF-G1 LOCALITY reduction DONE axiom-clean** (`FlatteningStratification.lean`; first cross-leaf
  `import …Picard.QuotScheme`, acyclic): `gf_finite_sections_of_basicOpen_finite_cover` (Stacks 01PB
  locality half — `Module.Finite.of_localizationSpan_finite` + gap2 `isLocalizedModule_basicOpen` per
  basic open) + helper `finite_localizedModule_of_isLocalizedModule` (model-independence of localized-
  module finiteness; Mathlib only goes global→local). G1 FULL form blocked on the finite-type base case.
- **FBC keystone scaffolds DONE axiom-clean** (`FlatBaseChange.lean`): `keystoneAdjR` (depth-3 right
  adjunction of the conjugate pair) + `keystoneBeta` (non-monolithic comparison nat-iso). Resolved the
  8-iter structural unknown (depth-2 conjugate pair + non-monolithic β assemblable + conjugate-comparable).
  Keystone `_legs_conj` NOT closed (residual = large structurally-known φ/ψ Spec-layer transport). PARKED.

## iter-049 — GF seam-1b/1c + SNAP sectionsMul DONE axiom-clean
- **GF seam-1b** `gf_affine_finite_standard_subcover` (`FlatteningStratification.lean`, Stacks 01PB):
  affine cover → finite standard basic-open subfamily via `IsAffineOpen.exists_basicOpen_le` +
  `self_le_iSup_basicOpen_iff` + `Ideal.span_eq_top_iff_finite`. Gotcha: `TopologicalSpace.Opens.mem_iSup`
  fully-qualified. Axiom-clean.
- **GF seam-1c** `gf_finite_gen_iff_free_epi` (same file): finite generation ⟺ free-epi `𝒪^I ↠ F`, via
  `SheafOfModules.GeneratingSections`/`freeHomEquiv`. Stated in abstract `SheafOfModules.{u} R` generality
  (applies to sliced restrictions). Axiom-clean. (Blueprint prose generalised iter-050: dropped spurious
  "quasi-coherent".)
- **SNAP** `sectionsMul` (`SectionGradedRing.lean`, `def:sectionMul`): lax-Γ multiplication
  `Γ(F)⊗_{Γ(𝒪)}Γ(G) → Γ(F⊗G)` via the sheafification unit; `ModuleCat ⟶` form dodges the ring-expr diamond.
  Axiom-clean. 10 layer-1 helpers privatized.

## iter-050 — GF seam-1 CLOSED + GR-quot new file (both lanes converging)
- **GF seam-1 CLOSED** (`FlatteningStratification.lean`, +5 axiom-clean): engine `GeneratingSections.map`/
  `map_I`/`map_isFiniteType` (transport a generating family along a colimit/unit-preserving functor; take
  `PreservesColimitsOfSize` EXPLICIT, not instance — def-backed `Scheme.Modules` trap) + seam-1a
  `gf_localGenerators_restrict` (the STUCK make-or-break gate — finite generation survives restriction, via
  `overRestrictPullbackIso` through epi-preserving `pullback U.ι` + `pullbackOpenImmersionUnitIso`) + assembly
  `gf_finiteType_affine_finite_cover_generated` (dropped unused `[F.IsQuasicoherent]`). G1 now reduces EXACTLY
  to the base case `gf_qcoh_finite_sections_of_genSections` (gap1-hard Spec transport, sub-steps a/b/c).
- **GR-quot NEW FILE** (`GrassmannianQuot.lean`, root-imported, +3 axiom-clean +5 scaffolds):
  `globalUnitSection` + `scalarEnd` (O_X scalar-endo plumbing) + headline `chartQuotientMap` (u^I=·X^I via
  `biproduct.matrix`; sections have NO module instance; `HasFiniteBiproducts` not global —
  `of_hasFiniteProducts`). Scaffolds `glue`/`universalQuotient`/`tautologicalQuotient`/`functor`/`represents`.
  Next: `chartQuotientMap_epi` (split-epi, ≥5-lemma chain) + `glue` cocycle signature fix.

## iter-056/058 — glue CLOSED, GF base-change built, SNAP carrier refactor landed
- **GR-quot `Scheme.Modules.glue` CLOSED** (`GrassmannianQuot.lean`, axiom-clean iter-056): effective
  descent as `equalizer a b` of two pushforward legs `∏ᵢ(ιᵢ)_*Mᵢ ⇉ ∏(j_ij)_*(f_ij^*Mᵢ)` (`X.Modules`
  `HasLimits` ⟹ exists + auto-sheaf); cocycle hyps `_hC1`/`_hC2` not needed for the object. sorry 4→3.
- **GF base change BUILT** (`FlatteningStratification.lean`, axiom-clean iter-056): `gf_flat_of_isEpi`
  (`Algebra.IsEpi`+`TensorProduct.lid'`+`Module.Flat.isBaseChange`) + `gf_isEpi_restrict_of_affine_le`
  (reflect `Mono (Spec.map ρ)` through fully-faithful `Spec`). Dissolved the 5-iter "missing base
  change" STUCK. `genericFlatness` reduced to the single `flatV` localization assembly.
- **SNAP carrier refactor LANDED** (`SectionGradedRing.lean`, iter-058): `objRestrict` = distinct
  `↥(P.obj U) →ₗ[ℤ] ↥(P.obj V)` `ℤ`-linear restriction; `relTensorDomainPresheaf`/`relTensorTriplePresheaf`
  rebuilt to use it uniformly, dissolving the iter-056 `map_tmul` carrier-unification wall by construction
  (functoriality re-proofs now trivial; `relTensorActL` unblocked). File green-with-4-sorries.

## iter-066 — SNAP CRUX CLOSED + GR tautologicalQuotient CLOSED (both lanes MAJOR)
- **SNAP crux CLOSED** (`SectionGradedRing.lean` 2→0, axiom-clean, real `lake build`):
  `isIso_sheafification_whiskerRight_unit` + feeder `ztensor_whisker_localIso`. Route: Mathlib
  `GrothendieckTopology.W.whiskerRight` at `ModuleCat (ULift ℤ)` (same-universe monoidal constraint)
  + carrier-preserving equivalence `modToAb` transfers `J.W` both ways
  (`Sheaf.preservesSheafification_of_adjunction` on `asEquivalence.toAdjunction`) + coequalizer
  descent through `relativeTensorCoequalizerIso`. ~330 LOC, all helpers `private`. Stalk route
  never needed. Chapter blocks rewritten to the real route (iter-067 plan phase).
- **GR `tautologicalQuotient` CLOSED + `represents` decomposed** (`GrassmannianQuot.lean`, 2 sessions):
  session 1 closed the L1973 overlap sorry via the rect `matrixEndRect` chain
  (`ιFree_matrixEndRect`/`biproduct_matrix_comp_rect`/`chartQuotientMap_eq_matrixEndRect`);
  session 2 built the descent-restriction layer (~350 LOC proven: `glueIsoEqualizer` = `Iso.refl`
  zeta-unfold lever, `glueProj`/`glueLift_glueProj`, `glueRestrictionHom` + adjoint-transpose bridge,
  `restrictFunctor_isRightAdjoint` + open-immersion pullback preserves limits,
  `glueData_preimage_image_eq`, `universalQuotient_restrictionIso`,
  `universalQuotient_isLocallyFreeOfRank` PROVEN mod keystone, `represents` forward map +
  `homEquiv_comp` PROVEN). Residue = 5 scoped sorries: keystone `isIso_glueRestrictionHom`
  (effective descent, route in docstring, β_ij `glueOverlapBaseChangeIso` partial),
  `tautologicalQuotient_epi`, `grPointOfRankQuotient`(+`_rel`), 2 inverse laws.
- **Traps recorded:** `glue`/`glueLift` universe-pinned `Scheme.GlueData.{0}`; `restrictFunctor`
  instance needs explicit `(PullbackConstruction.adjunction _).isRightAdjoint`;
  `PreservesSheafification` synth times out — supply via adjunction explicitly; `ModuleCat`
  monoidal is same-universe-only (hence `ULift ℤ`).

## iter-078 closures (first real prover iter since 067)
- **SectionGradedRing → sorry-free.** `tensorObjAssoc` (`cor:sheafTensorObjAssoc`) + `tensorPowAdd`
  (`lem:sheafTensorPow_add`) both closed kernel-axiom-only; `unitModule` made public.
- **GrassmannianQuot 6→4.** Closed `isIso_pullback_isoLocus_map` (Mathlib stalk route) and
  `chartLocus_isOpenCover` (~600 LOC affine projective-splitting). Landed Nitsure overlap matrix core
  (`presentedMatrix_changeOfBasis`, `isUnit_of_isIso_matrixEndRect`) + 15-helper matrix toolbox.
- **GlueDescent keystone body complete + compiling**, reduced to 2 named sorries
  (`gr_glueOverlapFactor_transpose`, `gr_glueChartFamily_equalizes`). `pullback_map_jointly_faithful`
  proven (core of `lem:gr_modules_glue_unique`).

## iter-079 plan-phase landings (no prover edits yet)
- **FBC route swap (STRATEGY).** Discovered `FlatBaseChangeGlobal.lean` already proves the direct
  H⁰-equalizer core 0-sorry (`baseChangeGammaEquiv`/`gammaTopEquivEqLocus`/finite cover). Mate keystone
  `_legs_conj`/`_gstar_transpose` ABANDONED. Blueprint `thm:fbcb_global_direct` added (writer fbc-b-direct).
- **GR coverage debt cleared** (writers glue-coverage/grquot-coverage/grquot-debt): 15-helper matrix
  toolbox blueprinted, `chartLocus_isOpenCover` prose rewritten to the affine-splitting route.

## iter-079 prover closures (global sorry 14→12)
- **GlueDescent 2→1.** `glueOverlapFactor_transpose` SOLVED (8-step site-level route).
  `glueChartFamily_equalizes` sorry-free MODULO extracted core `glueChartComponent_leg_compat` (L2081);
  landed the full triple-overlap toolkit (~13 compiling helpers). 4-step residual route in iter-079 task result.
- **GrassmannianQuot 4→3.** `grPointOfRankQuotient` overlap-compat SOLVED via `chartMorphism_glue_compat`
  + 10 supporting lemmas; `def:grPointOfRankQuotient` sorry-free. `represents` first bridge
  `chartComposite_rqPullback` landed; layers (b)/(c) scoped.

## iter-080 plan-phase landings
- **Blueprint coverage cleared** (writers glue-tripleC2 + grquot-univ): GlueDescent +13 triple-toolkit
  blocks + `lem:gr_glueChartComponent_leg_compat`; GrassmannianQuot +18 blocks. Both GATE CLEAR (fast080).
- **SNAP design corrected** (analogist snap-gcomm + writer snap-assembly): `sectionsMul_assoc_unit` =
  FOUR cast-mediated component Eqs (TensorPower.Basic idiom); added `def:sectionsCast` +
  `lem:gradedMonoid_eq_of_cast`; assembly proofs rewritten field-for-field. SNAP → mathlib-build lane next iter.
