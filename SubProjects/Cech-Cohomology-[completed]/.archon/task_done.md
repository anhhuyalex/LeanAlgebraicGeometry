# Completed Tasks

Resolved obligations (most recent first).

## Iter-079 — CAPSTONE CLOSED (Route-A complete; project mathematical content done)
- **`CechToHigherDirectImage.lean` `cech_computes_higherDirectImage_of_affineCover`
  (`lem:cech_computes_cohomology_affineCover`) — PROVED, 0 sorries.** The consumer assembly was fully
  written but ill-typed: it called the producer `cechTerm_pushforward_acyclic` without the `[S.IsSeparated]`
  instance or the `hres` family. Closed by the **refactor subagent** `thread-affinecover` (pure signature
  plumbing — NOT a prover lane, since the file had 0 sorries and plan-validate's noop-trap kept dropping
  the `prove` objective): added `[S.IsSeparated]` + `(hres : ∀ (n) (σ : Fin (n+1) → 𝒰.I₀),
  HasInjectiveResolutions (coverInterOpen 𝒰 σ).toScheme.Modules)` to the signature, carried `[X.IsSeparated]`
  explicitly to match the producer (redundant-but-harmless; strategy-critic's sanctioned fallback), and
  forwarded `(hres n)` at the call. LSP: 0 errors, 0 sorries (review-build gate verifies against a larger
  cap). Blueprint prose aligned to carry `[X.IsSeparated]` explicitly. ⟹ **Route A complete**:
  `Hⁱ(Čech) ≅ Rⁱf_* F` under the correct (affine-cover, `S`-separated) hypotheses. Only residual project
  sorry = the frozen, user-owned, false-as-signed `cech_computes_higherDirectImage` (CHDI:780).

## Iter-076 prover output (P5a-resolution CLOSED)
- **`CechAugmentedResolution.lean` `cechAugmented_exact` / `cechSection_isZero_homology`
  (`lem:cech_augmented_resolution`, `lem:cechSection_isZero_homology`) — CLOSED.** The `hSec` sorry
  (line ~229) closed by a 1-lemma consumer wrapper `cechSection_isZero_homology :=
  isZero_homology_of_iso_homotopy_id_zero (cechSection_complex_iso 𝒰 F V) p (cechSection_contractible …)`,
  then `exact cechSection_isZero_homology …` at the augmentation-node. Prover hit exit-137 (build-wall);
  the review-build gate (512 GiB) rebuilt the module GREEN, exit 0, 0 errors — kernel-sound. ⟹ the
  augmented Čech complex resolves any `O_X`-module ⟹ P5a-resolution DONE. Markers `\leanok` applied
  (review override after first-hand exit-0 confirmation, since sync's budget couldn't build the heavy
  module). This was the last P5a sorry; only the P5b capstone + the frozen false decl remained.

## Iter-075 prover output (CSI route 1→0 — FULLY CLOSED)
- **`CechSectionIdentificationLeg.lean` `pushPull_interLegHom_sections` (`lem:pushPull_interLegHom_sections`)
  — CLOSED.** The last CSI leaf: the per-leg restriction-naturality seam `coreIso_comm_leg` reduces to.
  Merged the scratch-validated 5-step route (Step 0 `unit_pushforward_rFIP_inv`, Step 1 `restrict_unit_comp`
  + `inner_beta_chain`, Step 2 `pullbackComp_rFIP_compat`, Step 3′ `pushPull_toRestrict_comm`, Step 4
  on-sections collapse via `pls_eq`+`thin_resid5`). Verified by lean-auditor `iter075` (0 sorry/0 axioms,
  full chain `unit_pushforward_rFIP_inv → … → coreIso_comm` correctly wired, consumed by CSI lines 61/156)
  and lean-vs-blueprint-checker `leg` (all (a)–(d) steps realized, no placeholder). **⟹ CSI/Base/Leg all
  0-sorry; Sub-brick A DONE.** Coverage debt from the +5 substantive public helpers + ~36 other lean_aux
  nodes cleared iter-076 (blueprint-writer `covdebt076`, `unmatched` 41→0).

## Iter-074 prover output (CSI route 2→1 leaf; build/sync-verified)
- **`CechSectionIdentification.lean` `sectionCechAugV_π` (`lem:sectionCechAugV_π`) — CLOSED axiom-clean**
  (`#print axioms` = kernel only). Degree-0 augmentation seam via the terminal-object collapse
  (`cechAugmentation_pushPullMap` + `pushPull_sigma_iso_π` + `unit_pushPull_leg_sections`). Whole Stub-6
  block now sorry-free IN-FILE. +5 private helpers (`stubEqToHomRestr`, `rawPushPullMap_unit`,
  `cechNervePointIso_inv_eq_unit`, `cechAugmentation_pushPullMap`, `unit_pushPull_leg_sections`).
- **`CechSectionIdentificationLeg.lean` `backboneIncl_proj` — CLOSED** (sync_leanok-verified, +19 `\leanok`).
  The 12.8M-heartbeat reassociation wall killed by factoring into abstract `entry_chain`/`glue_chain` +
  one pre-extensive combo lemma. `coreIso_comm_leg` restructured to reduce to the single extracted leaf
  `pushPull_interLegHom_sections` (the last CSI sorry).

## Iter-072 plan phase (recovery — re-executed the killed iter-070/071 wave intents)
- **Refactor cleanup LANDED + verified (build GREEN):** dead `CechAcyclic.affine` stub deleted
  (superseded by `affine_cech_vanishing_qcoh`; `lem:cech_acyclic_affine` `\lean{}` already repointed to
  `sectionCech_affine_vanishing`+`CombinatorialCech.*`); 3 stale OpenImm planning-comment regions cleaned.
  (refactor `cleanup072`, killed during its verify step; planner ran the build.)
- **`coreIso_comm` effort-broken** into `lem:coreIso_comm_leg` (≈1602) → `lem:coreIso_comm_coface` (≈985)
  → `lem:coreIso_comm_sum` (≈1167); target 2242→1330; Lean names `AlgebraicGeometry.coreIso_comm_{leg,coface,sum}`
  confirmed free. (effort-breaker `corecomm072` — the progress-critic `iter072` CHURNING corrective.)
- **Blueprint gate re-cleared:** blueprint-clean `clean072` (5 purity edits) + blueprint-reviewer `iter072`
  HARD GATE PASS for CSI; stale `def:cech_free_presheaf_complex` in `lem:cechSection_contractible`
  statement `\uses` removed by planner.

## Iter-067 prover output (processed iter-071 — report LOST to a harness 401 auth kill during the final verification pass; work committed & builds green; reconstructed from code + iter-070 critic directive)
- **`CechSectionIdentification.lean` (sorry 3→2, project 6→5).** Of the iter-067 decomposed `coreIso` chain:
  - `coverInterOpen_inf_eq_iInf_inf` (`lem:coverInterOpen_inf_distrib`) — CLOSED axiom-clean (the `Opens` lattice fact).
  - `coreIso_objIso` (`lem:coreIso_obj_iso`) — CLOSED axiom-clean (degreewise object iso via `pushPull_eval_prod_iso` + `Pi.mapIso`/`eqToIso` reindex).
  - **`hcompat` — CLOSED** by folding into the CANONICAL augmentation: built `sectionCechAugV` (the evaluated Čech augmentation transported across `coreIso_objIso 0`) + `sectionCechAugV_comp_d`, both axiom-clean; degree-0 compatibility is now BY CONSTRUCTION.
  - **FALSE scaffold fixed:** free `ε`/`hε` parameters removed from `cechSection_complex_iso`/`cechSection_contractible` (for non-canonical `ε` both statements are false; the consumer `hSec` calls with no `ε`).
  - Residual: `coreIso_comm` (line 1506) — precise stuck point recorded in-file (sum bookkeeping: `Preadditive.comp_sum`/`Functor.map_sum` vs the bundled `AddCommGrpCat`-hom `objD` sum; per-coface naturality of `pushPull_eval_prod_iso` through `pushPull_sigma_iso`/`PreservesProduct.iso`/`pushPull_leg_sections`) + Stub 6 (1735, untouched; `depHomotopy`/`depHomotopy_spec` engine verified present).

## Iters 068–070 — infrastructure outage, NO route signal
- 068/069: plan+prover died <10s each (auth outage); zero work. 070: plan dispatched blueprint-writer `csi070`
  (LANDED — `def:sectionCechAugV`/`lem:sectionCechAugV_comp_d` blocks + canonical-augmentation sync in the
  consolidated chapter) but died before writing objectives; effort-breaker never dispatched; refactor + critic
  killed without output; prover re-ran stale objectives, interrupted, ZERO edits. Lost actions re-executed iter-071.

## Iter-066 prover output (processed iter-067) — OpenImm `_comp` FULLY CLOSED (P5a-consumer DONE, open-immersion arc complete); CSI Stub 5 reduced to `coreIso`/`hcompat`
- **`OpenImmersionPushforward.lean` (sorry 4→0). `higherDirectImage_openImmersion_comp` (`R^k f_*(j_*H) ≅
  R^k(j≫f)_*H`) FULLY CLOSED axiom-clean** ⟹ the termwise `f_*`-acyclicity P5b needs is DONE; file now 0 sorries.
  - **`hacyc`** (`j_* Iⁿ` is `f_*`-acyclic) — the iter-066-corrected ADJOINT route (NOT the flawed Serre-vanishing
    on `U∩f⁻¹V`). UNLOCK: `unfold Scheme.Modules.restrictFunctor; exact inferInstanceAs (SheafOfModules.pushforward
    _).IsRightAdjoint` (plain `infer_instance` post-`unfold` FAILS; `inferInstanceAs (… _).IsRightAdjoint` with the
    metavar hom succeeds) → `preservesMonomorphisms_of_isRightAdjoint` → `Injective.injective_of_adjoint
    (restrictAdjunction j) Iⁿ` → `Functor.IsRightAcyclic.ofInjective`. Used `restrictAdjunction j` directly (no
    `restrictFunctorIsoPullback`/`pullback` detour — cleaner than the blueprint).
  - **`eRes`** = `(pushforward j).mapIso (H ≅ I•.cycles 0) ≪≫ gCosyzygyIsoCocycles (pushforward j) I• 0`; the
    augmentation `H ≅ I•.cycles 0` read off `InjectiveResolution.isLimitKernelFork` (`singleObjHomologySelfIso.symm
    ≪≫ isoOfQuasiIsoAt ι 0 ≪≫ isoHomologyπ₀.symm`).
  - **`hexact`** = `exactAt_iff_isZero_homology` + transport `IsZero (higherDirectImage j (n+1) H)` (Part (1)
    `_acyclic`) across `isoRightDerivedObj (pushforward j) (n+1)`.
  - **`transport`** = `(homologyFunctor _ _ k).mapIso (NatIso.mapHomologicalComplex (pushforwardComp j f) I•) ≪≫
    (isoRightDerivedObj (pushforward (j≫f)) k).symm`; LHS defeq `(pushforward j ⋙ pushforward f).mapHC.obj I•`.
  - STALE-OLEAN: `#print axioms` via a separate import read OLD olean (`sorryAx`); `lake build <module>` FIRST.
- **`CechSectionIdentification.lean` (sorry 2→3, structural advance). Stub 5 `cechSection_complex_iso` reduced.**
  Built 3 sorry-free augmentation helpers — `mapHC_augment_iso` (additive functor commutes with `augment`,
  identity components), `map_augment_cond` (`f·d⁰=0` survives an additive functor), `augmentCochainIso` (augmented
  iso from base iso + node iso + compat square) — + the full augmentation-peeling assembly (`mapHC_augment_iso` ×2
  + `augmentCochainIso`, `eY := Iso.refl` adapter). Isolated Stub 5's content to the NON-augmented `coreIso` (1492)
  + degree-0 `hcompat` (1504). Stub 6 untouched. iter-067 decomposed `coreIso` into the
  `coverInterOpen_inf_eq_iInf_inf`/`coreIso_objIso`/`coreIso_comm` chain (CHURNING corrective).

## Iter-065 prover output (processed iter-066) — 2 targeted `prove` lanes, BOTH major closures, sorry 12→9; OPEN-IMMERSION ACYCLICITY FULLY CLOSED; CSI Stubs 2/4 cascaded
- **`OpenImmersionPushforward.lean` (sorry 5→4). `higherDirectImage_openImmersion_acyclic` (`R^q j_* = 0`, j
  affine open immersion) FULLY CLOSED axiom-clean — the project's sole open-immersion-acyclicity milestone.**
  The 4-iter (iters 061–064) φ'' "object-relabel iso" wall (billed ~40–80 LOC) was a DEFEQ:
  `Functor.sheafPushforwardContinuousComp` = `Iso.refl`, `Over.mapForget` = `rfl`, so
  `sliceReverseRingMap := sliceStructureSheafHom φ.symm (φ.inv⁻¹ᵁ Ui)` retypes by defeq. H₁/H₂ (opens-morphism
  proof-irrelevance, `Subsingleton.elim`/`congr 1`), `pushforwardSlicePullbackIso` (`leftAdjointUniq ≪≫ Iso.refl`),
  `pushforward_iso_preserves_qcoh`, `case hqc`, and the whole `_acyclic` cone cascaded shut. `#print axioms`
  kernel-only. Residual = STRETCH `_comp` (4 typed sub-sorries hacyc/eRes/hexact/transport).
- **`CechSectionIdentification.lean` (sorry 4→2). Both `pushPull_coprod_prod` induction leaves CLOSED → Stubs 2
  & 4 cascaded axiom-clean.** `pushPull_coprod_prod_empty` via new helper `isZero_modules_of_isEmpty` (module
  sheaf over empty/initial scheme = 0, through faithful `toPresheaf` + `Module.subsingleton`);
  `coprodToProd_isIso_of_equiv` via `Sigma.whiskerEquiv`/`Pi.whiskerEquiv` reindex + projection-wise key identity
  (Attempt-1 `Pi.reindex` route failed — codomain `∏(f∘e)` won't match `Pi.lift_π` lambda; `Pi.whiskerEquiv`
  works). With all 3 `coprodToProd_isIso_*` steps closed, `pushPull_sigma_iso` (Stub 2) + `pushPull_eval_prod_iso`
  (Stub 4) are axiom-clean with zero extra proof. Residual = Stubs 5/6 (augmented section-complex iso + homotopy).
- lean-auditor iter-065: 0 axiom-laundering, 0 thin-cat traps, all closed decls genuine.

## Iter-064 prover output (processed iter-065) — 2 FINE-GRAINED lanes, decompose+mode-switch corrective CONVERTED both routes (first real closures), sorry 9→12 BY DESIGN
- **`CechSectionIdentification.lean` (sorry 5→4; +5 axiom-clean helpers). CLOSED the substantive Option-step.**
  `coprodToProd_isIso_option` (the `Finite.induction_empty_option` adjoin-one step reusing the ★ binary
  coherence) closed axiom-clean — the first real closure in the induction chain after the mode-switch. Plus
  `pushPull_binary_coprod_prod_hom`, `pushPullObjCongr_hom`, `coprodToProdMap_comp_π`, `piOptionIso_inv_π_none/some`.
  Three Lean walls cleared + documented ([[csi-l2-binary-prodlift-trap]]): beta-redex product mismatch →
  `let ls` (fvar); `rw`/`simp` syntactic-key vs `erw` defeq projection matching (`prod.lift_fst`/`Pi.lift_π` fire
  ONLY under `erw`); reverse `← pushPullMap_comp` whnf-timeout → forward-fold via `heq`+forward `pushPullMap_comp`.
  Residual = 2 named leaves: `pushPull_coprod_prod_empty` (983, REDUCED to `IsZero ((pullback q).obj F)` over the
  initial scheme) + `coprodToProd_isIso_of_equiv` (999, reindex). `#print axioms` kernel-only.
- **`OpenImmersionPushforward.lean` (sorry 2→5 by decomposition; +10 decls, 2 sub-lemmas CLOSED). `case hqc`
  monolith decomposed → 4 typed leaves; upper chain compiles.** `pushforwardSliceTwoAdjunction` +
  `pushforward_iso_preserves_qcoh` axiom-clean (modulo leaves); `leftAdjointUniq` half of `pushforwardSlicePullbackIso`
  built; `_acyclic` body now sorry-free (`exact pushforward_iso_preserves_qcoh`, transitively dep on the leaves).
  Residual collapses to ONE keystone φ'' (`sliceReverseRingMap`, 607) codomain-bridge part (b) object-relabel iso;
  H₁ (649)/H₂ (660)/pullbackIso section-id (692) all fall once φ'' concrete. `#print axioms` kernel-only on closed decls.
- **Coverage/blueprint (iter-065 plan phase):** lvb-csi must-fix `coprodToProd_isIso_of_equiv` under-specified →
  blueprint-writer `gate065` added the dedicated block + `def:coprodOverIncl`/`def:coprodToProdMap` +
  `lem:coprodToProd_isIso_option` + realigned empty-base proof + expanded φ'' part (a)/(b); blueprint-reviewer
  `rescope065` HARD GATE CLEARS `correct: true` 0 must-fix. lean-auditor iter-064: 0 must-fix / 1 major (the
  `case hqc` "in full" comment should say "modulo 4 leaves") / 3 minor.

## Iter-063 prover output (processed iter-064) — 2 lanes, +9 axiom-clean decls, sorry 9→9 (FOURTH flat iter; both terminal walls cleared)
- **`CechSectionIdentification.lean` (+3 axiom-clean; sorry 4→4). Fixed a RED build + landed the substantive L2 node.**
  Arrived broken (2 errors + missing `end BinaryDecomp`). Fixed, then added `pushPull_binary_leg_coherence` (★,
  renamed from the broken `pushPullCoprodLeg_coherence`; `rfl` closes a `Functor.map_comp`-normalized goal — NOT
  a thin-cat collapse, lean-auditor confirmed), `pushPull_binary_coprod_prod` (the canonical L2 assembly
  `asIso (prod.lift (pushPullMap F overInl) (pushPullMap F overInr))` matched vs `chainIso`; leg-match via
  `prod.lift`/`comp_lift` identities + trailing `rfl` because `Category.assoc` REFUSES to reassociate
  `(A≫B≫C)≫prod.fst` over pushforward objs), `sigmaOptionIso` (reusable `Option`-coproduct split). Residual =
  `pushPull_coprod_prod` finite-index induction, decomposed by the prover into 6 small mechanical pieces (~120 LOC):
  `pushPullObjCongr`/`over_sigmaOptionIso`/`piOptionIso`/`pushPull_coprod_prod_empty` (initial-scheme terminality)/
  the induction/specialization. Declined the monolith near budget. `#print axioms` kernel-only on all 3.
- **`OpenImmersionPushforward.lean` (+6 axiom-clean; sorry 2→2). The iters-060–062 metavar wall CLEARED.**
  `opensMapHomBase_isEquivalence`, `opensEquivOfIso` (= `Opens.mapMapIso (Scheme.forgetToTop.mapIso φ).symm`),
  `sliceOversEquiv` (= `Over.postEquiv Uᵢ (opensEquivOfIso φ)`), `sliceOversEquiv_functor_isContinuous`,
  `overPost_slice_inverse_isContinuous`, and the KEY UNBLOCK `sliceOversEquiv_inverse_isContinuous` (the
  inverse-functor continuity = the stuck `[F.IsContinuous J K]` metavar behind `pushforwardPushforwardAdj` for 3
  iters; built via `@Functor.isContinuous_comp` with 9 explicit args + `GrothendieckTopology.instIsContinuousOverMapOver`
  for the `unitIso.inv` factor). KEY HANDOFF: φ'' is **object-level correction-FREE** (= over-pullback of
  `φ.hom.toRingCatSheafHom`; the iter-063 blueprint's `sliceStructureSheafHom φ.symm` is a TYPE-MISMATCH);
  H₁/H₂ reduce to `eqToHom = eqToHom`. Residual = the φ''/H₁/H₂ comparison-iso chain. `#print axioms` kernel-only on all 6.
- **Coverage/blueprint (iter-064 plan phase):** φ'' CORRECTED + both terminal chains decomposed into fine-grained
  sub-lemmas; HARD GATE re-cleared (`correct: true`). lean-auditor iter-063: 0 must-fix / 2 major (stale CSI
  comment ~695–729; duplicate `isZero_of_faithful_preservesZeroMorphisms` OpenImm↔CechAugmentedResolution, latent).

## Iter-062 prover output (processed iter-063) — 2 lanes, +8 axiom-clean decls, sorry 9→9 (third flat iter; both walls cleared/corrected)
- **`CechSectionIdentification.lean` (+2 axiom-clean decls; sorry 4→4). L2 leaf closed; L2 is bigger than thought.**
  `isIso_coprodDecompMap` (the disjoint-cover decomposition `M ⟶ inl_*(M|inl) ⨯ inr_*(M|inr)` is iso, via
  `TopCat.Sheaf.isProductOfDisjoint` reflected through `SheafOfModules.evaluation ⋙ forget₂ (ModuleCat) Ab`
  + `isIso_map_prodLift_of_isLimit`) + the general helper `isIso_map_prodLift_of_isLimit`. **KEY CORRECTION:**
  the iter-061 readiness claim was WRONG — `pushPull_binary_coprod_prod` (L2) is NOT this leaf; it is the full
  `q_*`-coherence assembly (~200–300 LOC: per-leg coherence ★ + chainIso + induction + specialization) bridging
  `coprodDecompMap (q^*F)` in `(A⨿B).Modules` to the `X.Modules` `q_*(q^*F)` statement. Prover worked out the
  COMPLETE reduction in-file, confirmed every Mathlib lemma exists (key `pushforwardComp` identity-on-objects
  by `rfl`), left unbuilt rather than sorry. Blueprint decomposed iter-063 (`lem:pushPull_binary_leg_coherence`).
  `#print axioms` kernel-only on both.
- **`OpenImmersionPushforward.lean` (+6 axiom-clean decls; sorry 2→2). ψ_r "genuine wall" CLEARED.**
  Entire ψ_r slice-structure-sheaf infra: `sliceStructureSheafHom` (= ψ_r, `overPullback.map φ.inv.toRingCatSheafHom`,
  Beck–Chevalley `rfl` codomain) + `opensMapInvBase_isEquivalence`, `overPost_slice_isContinuous`,
  `sliceStructureSheafHom_pre_isRightAdjoint`, `sliceStructureSheafHom_isRightAdjoint` (the
  `IsRightAdjoint`/`Final`/`IsContinuous` discharge did NOT stall — presheaf via
  `isRightAdjoint_of_leftAdjointObjIsDefined_eq_top` + `.{u}` pin; sheaf via `inferInstance` under bumped
  heartbeats). `hqc` sharpened to one per-slice obligation (line 670). Residual = comparison iso
  `pushforwardSlicePullbackIso`; **prover found the blueprint proof was WRONG (unit-only `pullbackObjUnitToUnit`,
  not general H)** and identified the correct `leftAdjointUniq` route. Blueprint rewritten + decomposed iter-063
  (`lem:pushforward_slice_two_adjunction`). `#print axioms` kernel-only on all 6.

## Iter-061 prover output (processed iter-062) — 2 lanes, +5 axiom-clean decls, sorry 9→9 (foundations under assembly holes)
- **`CechSectionIdentification.lean` (+3 axiom-clean decls; sorry 4→4). L1 closed, L2 blocked-with-fix.**
  L1 `isIso_modules_of_toPresheaf` PROVED (`isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)`,
  one-liner). +2 prep helpers `isIso_prodLift_of_isLimit` (`BinaryFan.mk` limit ⟹ `prod.lift` iso) +
  `coprodDecompMap` (binary disjoint-cover comparison map). L2 `isIso_coprodDecompMap`/
  `pushPull_binary_coprod_prod` BLOCKED — removed rather than sorry'd. **Precise fix handed off (now
  blueprinted iter-062 `% NOTE`):** (a) instance trap — use `SheafOfModules.evaluation V` NOT
  `toPresheaf ⋙ evaluation`, reduce via `Scheme.Modules.Hom.isIso_iff_isIso_app`; (b) reflect the
  `isProductOfDisjoint` Ab-limit to ModuleCat via `isLimitOfReflects (forget₂ (ModuleCat R) Ab)`
  (~60–100 LOC cone bookkeeping). `#print axioms` kernel-only on all 3.
- **`OpenImmersionPushforward.lean` (+2 axiom-clean decls; sorry 2→2). `hqc` REDUCED + route simplified.**
  `coversTop_preimage_of_iso` (cover transport along the scheme iso) + `pushforward_iso_qcoh_of_slice_qcoh`
  (`of_coversTop` reduction of `hqc` to per-slice). `hqc` now reduced to per-slice presentation transport;
  lone residual = cross-ring slice structure-sheaf ring hom `ψ_r` (~100–150 LOC, absent from Mathlib).
  **Prover found a SIMPLER route** (`SheafOfModules.pullback ψ_r`, single left-adjoint hom) than the
  blueprint's `pushforwardPushforwardEquivalence` quadruple — blueprint retargeted + ψ_r effort-broken
  iter-062. `#print axioms` kernel-only on both.

## Iter-060 prover output (processed iter-061) — 2 lanes, +7 axiom-clean decls, 2 keystones closed (sorry 11→9)
- **`CechSectionIdentification.lean` (+3 axiom-clean decls; sorry 5→4). STUB 1 CLOSED.**
  `cechBackbone_left_sigma` PROVED via the iter-059-prescribed universe reduction: reindex
  `𝒰.I₀ ≃ Fin (Nat.card 𝒰.I₀)` (Finite.equivFin), run the Type-0 core `widePullback_coproduct_iso` at
  `Fin n`, transport back with `Sigma.whiskerEquiv` (both families given explicitly — else `g` stays a
  metavar) + `Sigma.mapIso (coverInterProdIso ·)`. New helpers `coverInterProdIso` (σ-component
  slice-product→intersection-open) + `widePullbackBaseCongr` (wide-fibre-power transport along apex iso —
  TRAP: generic `{C}` hom-universe metavar SILENTLY no-ops `rw/simp` on composites → specialize to `Scheme`;
  `lift_fac _ _ _` all-underscore stuck instance, LSP false-clean → pass explicit args). `#print axioms`
  kernel-only. Stub 1 no longer gates Stubs 2→4.
- **`OpenImmersionPushforward.lean` (+1 public +2 private axiom-clean decls; sorry 3→2). `hjt` CLOSED.**
  `jShriekOU_transport_along_iso` discharges `case hjt` of `higherDirectImage_openImmersion_acyclic` via
  `CorepresentableBy.uniqueUpToIso` on two witnesses (`sectionsCorep` direct + `sectionsCorepPushforward`
  via adjunction) corepresenting the SAME `sectionsFunctor(φ.inv⁻¹V) ⋙ forget` — improved on the blueprint's
  coyoneda route. Sole Need#1 residual = `hqc` (qcoh-preservation along the scheme iso). `#print axioms`
  kernel-only.

## Iter-058 prover output (processed iter-059) — 2 lanes, +11 axiom-clean decls, Need#2 CLOSED end-to-end
- **`AffineSerreVanishing.lean` (+2 axiom-clean decls; sorry 0→0). NEED#2 CLOSED.** `affine_tildeVanishing_general`
  (private — the general-affine analogue of `affine_tildeVanishing`, swapping seed
  `sectionCech_homology_exact_of_localizationAway`→`_of_affineOpen` and hyp `hcov`→`IsAffineOpen`) +
  the public top `affine_serre_vanishing_general_open` (= `affine_serre_vanishing_general_of_tildeVanishing F
  (affine_tildeVanishing_general F)`). Unconditional `Ext^p(jShriekOU V,F)=0` for any affine open V, p>0,
  qcoh F over `Spec R`. `#print axioms` kernel-only. The general-affine 02KG cone closes end-to-end.
- **`CechSectionIdentification.lean` (+9 axiom-clean decls; sorry 5→5). STUB-1 BRICK SET COMPLETE.** The 4
  blueprint-named decomposed leaves (`widePullback_overX_eq_prod`, `prod_coproduct_distrib`,
  `coproduct_fibrePower_reindex`, `widePullback_coproduct_iso_zero`) + `prodFinSuccIso` (confirmed Mathlib
  gap, built via `mkFanLimit`+`Fin.cases`) + 4 `Over S` (co)product helpers (`widePullback_overX_isLimit`,
  `overSigmaDescCofan`/`IsColimit`/`Iso`). EVERY categorical brick the induction needs now exists; only the
  inductive assembly `widePullback_coproduct_iso` + Over-S bridge `overProd_coproduct_distrib` + consumer
  `cechBackbone_left_sigma` remain (iter-059 Lane 1). **UNIVERSE TRAP discovered iter-059:** the leaves MUST
  stay `{ι:Type}` (Type 0) — `isIso_sigmaDesc_fst` is Type-0-only; the consumer reindexes `𝒰.I₀≃Fin n`.

## Iter-057 prover output (processed iter-058) — 3 lanes, +16 axiom-clean decls, Need#2 seed CLOSED
- **`CechAcyclic.lean` (+6 axiom-clean decls; sorry 1→1).** The Need#2 change-of-ring section-Čech seed
  is **fully built in one iter**: `isLocalizedModule_baseChange_away` (the one novel ingredient — base-change
  composite localization via `IsBaseChange.comp` + `isLocalizedModule_iff_isBaseChange`),
  `SectionCechModule.dDiff_exact_of_affineCover`, `sectionCechAbExact_affine` (private),
  `sectionCech_homology_exact_of_affineCover`, `basicOpen_algMap_section` (private), and the consumer-facing
  `sectionCech_homology_exact_of_affineOpen` — same conclusion shape as the done `_of_localizationAway`
  sibling, discharges `htilde` verbatim. All `{propext, Classical.choice, Quot.sound}`. The flagged
  `IsScalarTower`/semiring-diamond risk did NOT materialize (OreLocalization machinery resolves cleanly).
  TRAP: `Algebra Γ(V) Γ(D a)` / `Algebra Γ(⊤) Γ(V)` are NOT synthesizable — `letI` the restriction-map
  `.toAlgebra` + `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`; `basicOpen_algMap_section` sidesteps the
  `Γ(⊤) Γ(V)` instance via `basicOpen_res`/`basicOpen_eq_of_affine`.
- **`CechSectionIdentification.lean` (+6 axiom-clean decls; sorry 5→5).** Stub-1 geometric backbone:
  `mem_iInf_opens_of_finite` (private), `widePullback_openImm_inter`, `cechBackbone_obj_widePullback`
  (`Iso.refl`, definitional), and the coproduct-in-`Over X` leaf `coverArrowOverCofan`/`coverArrowOverIsColimit`/
  `coverArrowOverSigmaIso` (via `mkCofanColimit`, NOT reflection). The hard `coproduct_distrib_fibrePower`
  (wide extensivity, ~120–200 LOC) correctly DEFERRED not stubbed (mathlib-build no-sorry).
- **`OpenImmersionPushforward.lean` (+4 axiom-clean decls; sorry 2→2).** Need#1 Ext-transport core:
  `pushforwardEquivOfIso` (module-cat equivalence along a scheme iso), `pushforwardEquivOfIso_functor_additive`,
  `pushforwardExtAddEquiv` (via `Functor.mapExt_bijective_of_preservesInjectiveObjects` — the decisive find,
  sidesteps the absent `Ext.mapExactFunctor` composition), `modulesIsoSpecExtTransport`. Residual = the
  jShriekOU scheme-iso transport (decomposed iter-058) + qcoh-preservation. Needs `[EnoughInjectives U.Modules]`
  (the ~6-LOC `HasInjectiveResolutions→EnoughInjectives` connector, at the consumer site).

## Iter-056 prover output (processed iter-057) — Need#2 done modulo 1 seed; Stub 3 closed + Stubs 5/6 disproved
- **`AffineSerreVanishing.lean` (+7 axiom-clean decls; sorry 0→0).** Need#2 cover-system enlargement built
  end-to-end: `isAffineOpen_specBasicOpen`, `standard_cover_cofinal_affine`, `affine_surj_of_vanishing_affine`,
  `affineCoverSystemGeneral` (basis = all affine opens), `affine_cech_vanishing_qcoh_general_of_tildeVanishing`,
  `affine_serre_vanishing_general_of_seed`, `affine_serre_vanishing_general_of_tildeVanishing`. Reduces
  general-affine-open Serre vanishing to ONE isolated hypothesis `htilde` (change-of-ring section Čech seed).
  All `{propext, Classical.choice, Quot.sound}`. (analogist's "no new gap" estimate missed the
  `HasVanishingHigherCech` seed consumer; seed is a genuine ~230–320 LOC build, route B1 — see task_pending.)
- **`CechSectionIdentification.lean` (+1 axiom-clean decl; sorry 6→5).** Stub 3 `pushPull_leg_sections`
  closed (`Γ(V,j_*j^*F)≅Γ(U_σ∩V,F)` via `pushforward_obj_obj`/`restrictFunctorIsoPullback`/`restrict_obj`).
  **DECISION-CHANGING:** Stubs 5/6 (`cechSection_complex_iso`, `cechSection_contractible`) proven FALSE as
  specified — consumer needs the AUGMENTED complex `D'_aug` (`D'_aug.X(-1)=Γ(V,F)`), not the non-augmented
  `D'` (one-member cover ⟹ `H⁰(D')=Γ(V,F)≠0`). Re-spec'd in blueprint iter-057. Stubs 1/2/4 correctly
  specified; Stub 1 (`cechBackbone_left_sigma`) blocked on missing-Mathlib scheme coproduct/fibre-product
  distribution (≫150 LOC) → Stub 2/4 chained behind it. Prover reverted a partial `ε≫d⁰=0` rather than ship a sorry.

## Iter-055 prover output (processed iter-056) — corepresentability + consumer glue (recorded retroactively iter-057)
- **`OpenImmersionPushforward.lean` (+5 axiom-clean corepresentability helpers).** `sectionsFunctorCorepIso`
  + `rightDerivedNatIso`; `_acyclic` leaf reshaped to `IsZero(Ext^q(jShriekOU(j⁻¹W),H))` (geometry-free).
- **`CechAugmentedResolution.lean` (+1 glue).** `isZero_homology_of_iso_homotopy_id_zero`; `hSec` re-routed
  to consume Sub-brick A. `CombinatorialCech.Dependent` de-privatized (refactor).

## Iter-054 prover output (processed iter-055) — both lanes sharpened; Lane-1 wall confirmed = Sub-brick A
- **`CechAugmentedResolution.lean` (+1 axiom-clean helper; residual sharpened, sorry 1→1).** Built
  `isZero_homology_of_homotopy_id_zero` (`Homotopy (𝟙 D) 0 → IsZero (D.homology p)`, any preadditive C;
  `{propext, Classical.choice, Quot.sound}`) and WIRED it into `cechAugmented_exact`, sharpening the single
  residual from `IsZero (D.homology p)` to the exact contracting-homotopy obligation `Homotopy (𝟙 D) 0`
  (line 205). Prover diagnosis (CONFIRMED by progress-critic `iter055` CHURNING + analogist `subbrickA`):
  the residual is **Sub-brick A** = per-degree section identification `Γ(V, pushPullObj F Y) ≅ ∏_σ Γ(U_σ∩V,F)`,
  the SAME L1 wall as the dead `CechAcyclic.affine`. 4th consecutive PARTIAL → D1 reversal signal → iter-055
  executes the STRUCTURAL corrective (decompose + de-privatize engine), NOT a 5th whole-theorem re-dispatch.
- **`OpenImmersionPushforward.lean` (+4 axiom-clean; `_comp` re-signed; sorry 2→2).** `_acyclic` wired
  axiom-clean down to ONE precisely-typed Serre leaf `IsZero (((pushforwardSectionsFunctor j W).rightDerived q).obj H)`
  (affine `j⁻¹W`, q>0). Helpers: `isZero_presheafToSheaf_of_sections_locally_zero` (sectionwise local-zero ⟹
  sheafification zero — affine opens not downward-closed), `pushforwardSectionsFunctor` (+`_additive` via explicit
  `instAdditiveComp` chain — flat 5-fold composite over `pushforward j` defeats `infer_instance`), and a
  duplicated `isZero_of_faithful_preservesZeroMorphisms` (import-isolation copy; lean-auditor `iter054` major).
  `_comp` re-signed `Nonempty(A≅B)`→canonical `A≅B` (D2). progress-critic `iter055`: **CONVERGING** — continue
  with a prover directly on the Serre leaf (rightDerived-sections↔Ext + change-of-space to `Spec R` →
  `affine_serre_vanishing`). lean-auditor `iter054`: 0 must-fix; both `congr 1`/`Subsingleton.elim` kernel-sound.

## Iter-053 prover output (processed iter-054) — both P5a lanes collapsed to crisp residuals
- **`CechAugmentedResolution.lean` (+2 axiom-clean helpers; residual `hSec` sorry remains).** First real
  prover pass. The whole `cechAugmented_exact` theorem WIRED axiom-clean end-to-end (toSheaf reflect →
  `homologyIsoSheafify` → sheafification square → locally-zero site lemma → covering sieve from
  `iSup_opensRange` → eval-preserves-homology via `mapHomologyIso'`) down to ONE isolated residual: `IsZero`
  of the F-valued augmented Čech **section** complex homology for `V ≤ coverOpen 𝒰 i`. Reusable helpers:
  `isZero_of_faithful_preservesZeroMorphisms` (`{propext, Classical.choice}`),
  `isZero_presheafToSheaf_of_locally_isZero` (`{propext, Classical.choice, Quot.sound}`). Both blueprinted
  iter-054 (`\lean{}` blocks). `lake env lean` GREEN; `#print axioms cechAugmented_exact` = kernel+sorryAx only.
- **`OpenImmersionPushforward.lean` (+1 axiom-clean private; 2 residual sorries remain).** First real prover
  pass. `isAffineHom_of_affine_separated` (private, `{propext, Classical.choice, Quot.sound}`) — open
  immersion of affine into separated ⇒ affine morphism, via `IsAffineHom.of_comp j (terminal.from X)`.
  Both tops (`_acyclic`, `_comp`) upgraded from bare sorry to real partial reductions; both bottom out on
  the shared bridge (1) cohomology-presheaf identification (the deferred hand-off in
  HigherDirectImagePresheaf.lean) + Serre-transport + PresheafOfModules.sheafification site lemma. No sorry
  papered. lean-auditor `iter053`: 0 critical, 3 must-fix (= the 3 expected sorries), no kernel-soundness trap.

## Iter-052 prover output (processed iter-053) — 02KG TOPS unconditional + upstream site lemmas
- **`AffineSerreVanishing.lean` (+3 axiom-clean; file 0-sorry).** Lane A SOLVED — both 02KG tops now
  UNCONDITIONAL: `affine_serre_vanishing` + `affine_cech_vanishing_qcoh`, via the private reshaper
  `affine_tildeVanishing` (bundles iter-051's `sectionCech_homology_exact_of_localizationAway` into the
  `ULift (Fin n)` `htilde` shape) + two `_of_tildeVanishing` specializations. `affine_tildeVanishing`
  folded into a chapter `\lean{}` (iter-053, coverage debt cleared).
- **`CechHigherDirectImage.lean` (+3 axiom-clean site lemmas; protected line-780 sorry unchanged).** Lane B
  PARTIAL — `cechAugmented_exact` found UNPROVABLE IN THIS FILE (import cycle: all route ingredients
  transitively import it). Landed the reusable upstream Step-2 site lemmas
  `GrothendieckTopology.isZero_presheafToSheaf_obj_of_W` / `_of_W_isZero` / `_of_isLocallyBijective`
  (blueprint `lem:sheafify_kills_locally_zero`, authored iter-053). RELOCATION decided iter-053:
  `cechAugmented_exact` → new `CechAugmentedResolution.lean`. lean-auditor `iter052` 0 must-fix.

## Iter-051 prover output (processed iter-052) — 02KG residual SOLVED + augmented-complex object layer
- **`CechAcyclic.lean` (+3 public/private axiom-clean `{propext, Classical.choice, Quot.sound}`; file 0-sorry
  except the dead line-110 `affine`).** Lane 1 (02KG residual, route B) **fully closed**:
  - **`sectionCech_homology_exact_of_localizationAway`** (`lem:affine_cech_vanishing_tilde_subcover`) — the
    residual `htilde`: positive-degree section Čech vanishing of `~M` over a standard cover of a PROPER
    `D(f)` (cover spans `√(f)`, not `R`). The whole 02KG critical leaf.
  - **`SectionCechModule.dDiff_exact_of_localizationAway`** — the math core: instantiate the polymorphic
    `dDiff_exact` over `Rf = Localization.Away f`, transport pos-degree exactness back via the degreewise
    `M_{sσ}≅(M_f)_{sσ}` AddEquiv ladder.
  - **`AwayComparison.isLocalizedModule_comp_away`** — composite of two away-localisations (`M→M_f→(M_f)_{sσ}`
    presents `M` localised at `sσ` when `f ∣ sσⁿ`). + private `sectionCechAbExact_loc`.
  - lean-auditor `iter051` 0 must-fix/0 major; lean-vs-blueprint faithful. Blueprint coverage debt for the
    3 helpers cleared iter-052 (blueprint-writer blocks).
- **`CechHigherDirectImage.lean` (+6 axiom-clean; file sorry unchanged at the protected line-780).** Lane 2
  PARTIAL — augmented-complex OBJECT layer built: `cechComplexOnX`, `cechNervePointIso`, `cechAugmentation`,
  `augmentation_comp_alternatingCofaceMap_objD_zero` (private), `cechAugmentation_comp_d`,
  `cechAugmentedComplex`. The exactness theorem `cechAugmented_exact` NOT added (no sorry inserted) — the
  iter-051 stalk-at-prime plan hit a genuine Mathlib gap (no `SheafOfModules.stalk` / no exact-iff-stalkwise).
  iter-052 re-routed to sections/sheafification (analogist `stalkwise`); object-layer blueprint debt cleared.

## Iter-049 prover output (processed iter-050) — +4 axiom-clean; 02KG reduced to ONE residual
- **`AffineSerreVanishing.lean` (+4 axiom-clean, kernel-verified `{propext, Classical.choice, Quot.sound}`;
  file 0-sorry; new import `QcohTildeSections`, re-activated `attribute [local instance] hasExtModules`).**
  - **`affine_cover_span_localizationAway`** — base change of the cover spanning condition: if `D(gᵢ)` cover
    `D(f)` in `Spec R`, the images `gᵢ → R_f = Localization.Away f` span `⊤`. Sub-leaf #1 of the residual.
  - **`cechCohomology_isZero_of_iso`** — Čech cohomology transports along ANY coefficient iso `F≅G`
    (`(homologyFunctor).mapIso ∘ (sectionCechComplexFunctor U).mapIso`). Reusable transport.
  - **`affine_cech_vanishing_qcoh_of_tildeVanishing`** — 02KG SEED reduced: transports along
    `qcoh_iso_tilde_sections F` (now unconditional) to the tilde case, bottoming out at the explicit
    hypothesis `htilde`.
  - **`affine_serre_vanishing_of_tildeVanishing`** — 02KG TOP reduced: instantiates
    `cech_eq_cohomology_of_basis (affineCoverSystem R)` at `V=⊤`; verifies the full Lane-1 assembly
    typechecks end-to-end. Also bottoms out at the same `htilde`.
  - **NET:** both blueprint targets `affine_cech_vanishing_qcoh` (seed) + `affine_serre_vanishing` (top)
    are now reduced to a SINGLE crisp residual `htilde` = positive-degree section Čech vanishing of `~M`
    over a standard cover of a **proper** `D(f)`. Route = change-of-base to `R_f` (Stacks 02KG "Write
    U = Spec A"); sub-leaf #1 (spanning) DONE; remaining sub-leaves = per-σ section iso + cochain-complex
    iso + transport. NOT papered (residual is an explicit hyp, no sorry). See 02KG section of task_pending.

## Iter-048 prover output (processed iter-049) — +2 axiom-clean; 01I8 CLOSED
- **`QcohTildeSections.lean` (+2 axiom-clean, kernel-verified `{propext, Classical.choice, Quot.sound}`; file 0-sorry).**
  - **`isIso_fromTildeΓ_of_quasicoherent`** (`lem:qcoh_isIso_fromTildeGamma`, the objective) — the Route-B
    assembly, registered as an `instance`: for qcoh `F` on `Spec R`, `IsIso F.fromTildeΓ`. ⟹
    **`qcoh_iso_tilde_sections F` is now UNCONDITIONAL for quasi-coherent `F`.** Terminal milestone of the
    01I8 / Route B section-localization program (iters 040→048). Basis-check via
    `SpecModulesToSheafFullyFaithful.isIso_of_isIso_map` + `Functor.IsCoverDense.iso_of_restrict_iso`
    (`specBasicOpen` space-pinning) + `NatIso.isIso_of_isIso_app`.
  - **`isIso_fromTildeΓ_app_basicOpen`** (private component helper, bundled into `lem:qcoh_isIso_fromTildeGamma`)
    — each `D(r)`-component = `IsLocalizedModule.linearEquiv` of the two localizations `tilde.toOpen` and the
    keystone `ρ_r`; bijective ⟹ `IsIso` via `ConcreteCategory.isIso_iff_bijective`.
  - lean-auditor `iter048` + lean-vs-blueprint `iter048-qts`: 0 must-fix; axiom-clean confirmed first-hand.

## Iter-047 prover output (processed iter-048) — +6 axiom-clean; Route-B KEYSTONE SOLVED + EXCEEDED
- **`QcohTildeSections.lean` (+6 axiom-clean, kernel-verified `{propext, Classical.choice, Quot.sound}`; file 0-sorry).**
  - **`qcoh_section_isLocalizedModule`** (`lem:qcoh_section_isLocalizedModule`) — **THE Route-B KEYSTONE**:
    for qcoh `F` on `Spec R` and `f∈R`, `ρ_f : Γ(X,F)→Γ(D(f),F)` is `IsLocalizedModule (powers f)`.
    Built DIRECTLY via the abstract left-exact-ladder kernel comparison `isLocalizedModule_of_exact` over
    the two `qcoh_section_equalizer` rows + per-tile/overlap localizations. The single hardest leaf of 01I8.
  - **`qcoh_section_kernel_comparison`** (`lem:qcoh_section_kernel_comparison`, the original objective) —
    packaged-iso corollary `IsLocalizedModule.iso ρ_f`, one-liner from the keystone.
  - **`isLocalizedModule_of_exact`** (`lem:isLocalizedModule_of_exact`, NEW abstract primitive) — converse of
    Mathlib's `IsLocalizedModule.map_exact`: left-exact ladder + 2 localized verticals ⟹ 3rd vertical
    localized. Project-general, upstream candidate.
  - +3 private helpers (`overlap_section_localization`, `overlap_target_eq`, `presheaf_map_comp₂_apply`).
  - **Recurring wall = `↑R`-Semiring instance diamond** (`basicOpen` pulls CommRing→Semiring; `ModuleCat`
    lemmas use `Ring.toSemiring`): `rw`/`simp` on `∘ₗ`/`LinearMap.pi` silently fail. Recipe (now in KB):
    `change`(defeq) + presheaf-abstracted helpers via `refine (…).trans ?_`, `@`-threaded instances. New
    import `Mathlib.RingTheory.TensorProduct.IsBaseChangePi`.
  - **Coverage debt + `\uses` inversion cleared (iter-048 plan):** blueprint-writer `fix-deps` authored
    `lem:isLocalizedModule_of_exact` + `lem:overlap_section_localization`, flipped the keystone↔corollary
    `\uses` edge (lean-vs-blueprint `qts` flagged it as a real DAG error; non-circular both ways), moved the
    chase into the keystone block. blueprint-clean `fix` + planner wired `isScalarTower_restrictScalars_obj`
    into the statement `\uses` ⟹ `unmatched`/`isolated` both = 1 (only the pre-existing dead
    `CechAcyclic.affine`). blueprint-reviewer `iter048` = complete+correct, 0 must-fix, HARD GATE clears.
  - lean-auditor `iter047` + lean-vs-blueprint `qts`: 0 must-fix; all `change`/`Subsingleton.elim`/`@`-thread
    genuine (NOT the kernel-soundness trap); `maxHeartbeats 1000000` justified.

## Iter-046 prover output (processed iter-047) — +5 axiom-clean; `tile_section_localization` SOLVED (last tile leaf)
- **`QcohTildeSections.lean` (+5 axiom-clean, kernel-verified `{propext, Classical.choice, Quot.sound}`; file 0-sorry).**
  - **`tile_section_localization`** (`lem:tile_section_localization`) — the LAST keystone-feeding tile leaf:
    per element `g`, `IsLocalizedModule (powers f)` of `Γ(D(g),F)→Γ(D(gf),F)`. Built via the bundled
    `(ModuleCat.restrictScalars (algebraMap R R_g)).obj _` carrier recipe (`analogies/tile-descent-instance-shape.md`,
    mathlib-analogist iter-046) — the iter-045 W1/W2/W3 Lean-engineering walls dissolved (all of
    `Module R`/`Module R_g`/`IsScalarTower R R_g` TC-structural, no `letI` install).
  - **`tileReconcileEquiv`** + `tileReconcileEquiv_apply`/`_symm_apply` (private) — the R-linear reconcile equiv
    (id-on-carrier, `map_smul'` = `tile_scalar_compat'`) used in the transport. **`isScalarTower_restrictScalars_obj`**
    (Prop instance) — `IsScalarTower R S` on the bundled restrictScalars carrier (kills W2, no codegen).
    **`tile_restrict_map_apply`** (private, `rfl`) — tile restriction = F restriction over image opens, stated
    at the `⇑`-value level (bundled LinearMap eqn fails on R_g≠R).
  - Two-layer transport: Layer A (reconcile via `of_linearEquiv(_right)`), Layer B (opens `mapIso` via
    `eqToIso`); final morphism equality closed by explicit `congrArg (… .hom) (Subsingleton.elim _ _)` (NOT
    bare `congr`/`ext` — kernel-soundness trap). Prover also deleted the two stale sync-fooling comment blocks.
  - **Coverage debt cleared (iter-047 plan):** blueprint-writer `coverage-debt` added blocks for `tileReconcileEquiv`
    + `isScalarTower_restrictScalars_obj`, bundled the 3 private helpers, fixed 2 stale `\uses` edges → `unmatched`
    6→1. blueprint-clean `cov` + blueprint-reviewer `iter047` (complete+correct, 0 must-fix, HARD GATE clears).
  - progress-critic `routeb` iter-047 = CONVERGING (the iter-045 CHURNING resolved on contact).

## Iter-045 prover output (processed iter-046) — +5 axiom-clean; the V=D(f̄) compat + general-open companions
- **`QcohTildeSections.lean` (+5 axiom-clean, kernel-verified `{propext, Classical.choice, Quot.sound}`; file 0-sorry).**
  - **`tile_scalar_compat'`** (`lem:tile_scalar_compat_genV`) — general-open `V` scalar-tower compat `R→R_g`;
    the `V=D(f̄)` instance is the keystone sub-need. Same route-(A) structure as `tile_scalar_compat` (⊤) at
    arbitrary `V`, discharged via `tile_section_ring_identity'` + the smul bridges (`maxHeartbeats 1000000`).
  - **`tile_section_ring_identity'`** (`lem:tile_section_ring_identity_genV`) — general-`V` structure-sheaf
    ring identity; derived from the ⊤ case by post-composing with `ι ''ᵁ V ≤ ι ''ᵁ ⊤`, pushing the restriction
    through the two open-immersion section isos via the `appIso_inv_res` wrappers; `res(⊤≤⊤)=id` by `Subsingleton`.
  - **`appIso_inv_res` / `appIso_inv_res_assoc`** (private; bundled into `lem:tile_section_ring_identity_genV`'s
    `\lean{}`) — section-restriction forms of `Scheme.Hom.appIso_inv_naturality` in `rw`-matchable shape.
  - **`modulesRestrictBasicOpen_smul_eq'`** (`lem:modulesRestrictBasicOpen_smul_eq_genV`) — general-`V` tile-action
    `rfl` bridge.
  - **`tile_section_localization` NOT papered — correctly left absent.** Math COMPLETE (all ingredients
    axiom-clean, map identity `rfl`); blocked on Lean-engineering W1/W2/W3. **RESOLVED iter-046** by the
    mathlib-analogist (restrictScalars-carrier reshape — W1/W2 were a manual-instance-installation anti-pattern).
  - **Review (iter-046 plan):** mathlib-analogist `tile-descent` = ALIGN_WITH_MATHLIB (bundled
    `ModuleCat.restrictScalars (algebraMap R R_g)` carrier ⟹ all instances TC-structural; recipe
    `analogies/tile-descent-instance-shape.md`). progress-critic `routeb` = CHURNING-but-converging (dispatch=OK;
    corrective = the analogist consult, executed). Coverage debt cleared (5 companion blocks; `unmatched` 6→1).
    Blueprint Step 4/5 rewritten to the restriction-of-scalars descent (HARD GATE satisfied). Review iter-045
    removed a false `\leanok` on the keystone leaf (sync fooled by a commented-out `lemma` — HIGH-2 cleanup
    queued for the iter-046 prover lane).

## Iter-044 prover output (processed iter-045) — +5 axiom-clean; Sub-lemma B's residual ring identity CLOSED
- **`QcohTildeSections.lean` — `tile_scalar_compat` (= Sub-lemma B residual) + 4 route-(A) helpers (+5 axiom-clean, kernel-verified via `lake env lean`).** File 0-sorry throughout.
  - **`tile_scalar_compat`** (`lem:tile_scalar_compat`) — scalar compatibility at `V=⊤`: for `r∈R` and a
    section `x` of `F` over the tile image `D(g)`, `r • x` (as `R`-section) = `(algebraMap R R_g r) • x` (as
    `R_g`-section of the tile). The single structure-sheaf ring identity to which iter-043's two rfl bridges
    reduced Sub-lemma B's scalar core. Closed via route (A) (ΓSpec naturality): the two bridges + `congr 1` +
    `tile_section_ring_identity` applied elementwise (`set_option maxHeartbeats 1000000`). The in-file "PROVEN
    tactic prefix" comment was VALIDATED with `lean_goal` first (progress-critic enforcement). NOT an iso, NOT
    `lem:tile_section_comparison` (which stays unformalized — pin rejected by lean-vs-blueprint `qts` Q1).
  - **`appTop_appIso_inv_eq_res`** — general open-immersion lemma: `f.appTop ≫ (f.appIso ⊤).inv =
    Y.presheaf.map (homOfLE le_top).op`. Section-restriction reading of `appIso`.
  - **`key_morph`** — ΓSpec naturality of `specAwayToSpec g = Spec.map (algebraMap R R_g)`. **Crucial finding:**
    must be in `Scheme.ΓSpecIso.inv` form (NOT `globalSectionsIso.hom`, whose codomain is defeq-but-not-
    syntactic to `(Spec R).presheaf`, breaking `assoc`/`rw`). Swap is `CommRingCat.hom_ext rfl`.
  - **`tile_appIso_comp`** — `comp_appIso` fold of the two tile section isos into `(specAwayToSpec g).appIso ⊤`.
  - **`tile_section_ring_identity`** — the assembled morphism-level ring identity `ρ^{D(g)}(θ_R r)=β_g^{-1}(θ_{R_g}r̄)`.
  - **`tile_section_localization` NOT added — correctly NOT papered.** Obstruction precisely characterised: the
    bundled carriers are different `ModuleCat`s (`ModuleCat R_g` vs `ModuleCat R`), so the descent must run at
    the UNDERLYING-type/`F.val` level with `letI`'d `Module R` + `IsScalarTower R R_g` + `eqToHom` opens transport.
  - **Review (iter-045 plan):** progress-critic `routeb` = CONVERGING (iter-044 CHURNING does not carry forward;
    obstruction shrank monotonically to zero ingredients). lean-auditor `iter044` SOUND (0 must-fix; 2 major =
    deprecated `Sheaf.val` in the two smul-bridge type signatures — cleanup, not blocking). lean-vs-blueprint
    `qts` Lean clean (0 red flags; 5 major + 2 minor blueprint-side — ALL fixed iter-045 by blueprint-writer
    `tsl-step4` + blueprint-clean + blueprint-reviewer `iter045` HARD-GATE-CLEARS: 5 helper blocks authored,
    `tile_section_comparison` proof corrected, Step 4 rewritten to the underlying-type descent + V=D(f̄) sub-need).

## Iter-043 prover output (processed iter-044) — +2 axiom-clean rfl bridges; Sub-lemma B reduced to ONE ring identity
- **`QcohTildeSections.lean` — two `rfl` scalar-action bridges (+2 axiom-clean, kernel-verified via `lake env lean`).**
  - **`modulesSpecToSheaf_smul_eq`** (`lem:modulesSpecToSheaf_smul_eq`) — the native `R`-action on a
    `modulesSpecToSheaf.obj F` section over an open `W` equals `c_R • x_F`, with
    `c_R = (ringCatSheaf.map (homOfLE (W≤⊤)).op).hom ((StructureSheaf.globalSectionsIso R).hom r)` acting on
    `x` viewed as a section of `F.val` over `W`. Proof `rfl` (modulesSpecToSheaf action = restrict-scalars
    along `globalSectionsIso`). `#print axioms` = `{propext, Classical.choice, Quot.sound}`.
  - **`modulesRestrictBasicOpen_smul_eq`** (`lem:modulesRestrictBasicOpen_smul_eq`) — the tile (restricted-
    module) action transports rfl-style through the two open-immersion `appIso` ring maps
    `(specBasicOpen g).ι.appIso`, `(basicOpenIsoSpecAway g).inv.appIso` to `F.val`'s structure-sheaf action.
    Proof `rfl`. Axiom-clean.
  - **The MAJOR REDUCTION:** these two rfl bridges show the scalar action on BOTH sides is definitional and
    the carriers coincide via `restrict_obj` (when the F-side open is kept in iterated-image form `W`, not
    rewritten to `D(g)`). iter-042's "~150 LOC non-definitional wall" is now ONE structure-sheaf ring identity
    (~30–50 LOC): `(ringCatSheaf.map …).hom (algebraMap R Γ(W,𝒪) r) = ((basicOpenIsoSpecAway g).inv.appIso
    ⊤).inv.hom (algebraMap R_g Γ(⊤,𝒪_{R_g}) (algebraMap R R_g r))` — "sections over `D(g)` = `R_g`, compatibly
    with `algebraMap`." Closable by (A) ΓSpec naturality of `specAwayToSpec g = Spec.map (algebraMap R R_g)`
    or (B) `IsLocalization.Away` uniqueness. The "bundled `ModuleCat R_g` vs `ModuleCat R`" difference is real
    only at the category level; carriers + scalar actions are definitional.
  - **`tile_section_comparison` / `tile_section_localization` NOT added — correctly NOT papered with a sorry.**
  - Review (iter-043): lean-auditor `iter043` SOUND (0 must-fix; 3 major = 2 deprecated `Sheaf.val` uses that
    will break when the alias is removed + 1 "PROVEN tactic prefix" comment over-claim). lean-vs-blueprint
    `qts` Lean clean (0 red flags); flagged the `lem:tile_section_comparison` sketch as now INACCURATE (3–5×
    overstated) + 2 coverage-debt nodes — **both fixed iter-044 by blueprint-writer `tile-residual`**.

## Iter-042 prover output (processed iter-043) — +1 axiom-clean; Route B keystone Sub-lemma A (opens identities)
- **`QcohTildeSections.lean` — `tile_image_opens_identities` (Sub-lemma A of the tile lemma) (+1 axiom-clean).**
  - **`tile_image_opens_identities`** (`lem:tile_image_opens_identities`) — the two image-opens identities of
    the affine identification `ι = specAwayToSpec g`: `(specBasicOpen g).ι ''ᵁ ((basicOpenIsoSpecAway g).inv
    ''ᵁ ⊤) = specBasicOpen g` and `… ''ᵁ D(algebraMap R R_g f) = specBasicOpen (g*f)`. Proof via
    `Scheme.Hom.image_top_eq_opensRange`/`opensRange_of_isIso`, `Scheme.Hom.comp_image`, `specAwayToSpec_eq`,
    `PrimeSpectrum.localization_away_comap_range`, `comap_basicOpen`, `basicOpen_mul`. `#print axioms` =
    `{propext, Classical.choice, Quot.sound}`. Review pinned `\lean{}` iter-042.
  - **Import added:** `import AlgebraicJacobian.Cohomology.QcohRestrictBasicOpen` (tile infrastructure; no cycle).
  - **`tile_section_localization` NOT added — correctly NOT papered with a sorry.** The prover CONFIRMED on a
    clean `lake env lean` that Sub-lemma B (`tile_section_comparison`) is genuinely non-definitional: the tile
    sections `(modulesSpecToSheaf.obj (modulesRestrictBasicOpen g F)).presheaf.obj (op V) : ModuleCat ↑R_g`
    and the F-side `(modulesSpecToSheaf.obj F).presheaf.obj (op (ι ''ᵁ V)) : ModuleCat ↑R` are **not the same
    type** (different base rings). Earlier `lean_run_code` "rfl" successes were STALE-`.olean` artifacts — the
    project-memory [[keystone-tile-reconciliation-not-rfl]] trap, confirmed at the kernel level.
  - lean-auditor `iter042`: SOUND (0 must-fix). lean-vs-blueprint-checker `qts`: Lean clean, NO must-fix; the
    `lem:tile_section_comparison` blueprint sketch is accurate (honest ~100–150 LOC natural iso, NOT rfl).
    (1 major: 3 pre-existing decls lack `\leanok` — a stale-sync artifact; file builds clean, sync to re-mark.)

## Iter-041 prover output (processed iter-042) — +3 axiom-clean; Route B keystone FIRST LEAF (sheaf-axiom equalizer) + base-ring descent
- **`QcohTildeSections.lean` — `qcoh_section_equalizer` (the first keystone leaf) + base-ring descent (+3 axiom-clean).**
  - **`qcoh_section_equalizer`** (`lem:qcoh_section_equalizer`) — degree-0/1 sheaf-axiom equalizer
    `0→Γ(W,F)→∏ⱼΓ(W∩D(gⱼ),F)→∏ⱼₖΓ(W∩D(gⱼgₖ),F)` (injectivity via `IsSheaf.section_ext`; exactness via
    `existsUnique_gluing'`). Formalized **STRICTLY MORE GENERAL** than blueprinted (arbitrary index `ι` +
    abstract open cover of `W`, not just `U i = W∩D(gᵢ)`); `% NOTE` records the generalization + the two
    downstream specializations. New import `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.
  - **`isLocalizedModule_powers_restrictScalars_of_algebraMap`** (`lem:isLocalizedModule_powers_restrictScalars_of_algebraMap`)
    — base-ring descent: an `A`-linear localization at `powers(algebraMap R A f)` (over `A`) restricts
    `R`-linearly to a localization at `powers f` (over `R`), under `IsScalarTower R A M/N`. The CONVERSE of
    Mathlib's `of_restrictScalars` (Mathlib LACKS it). The ingredient `tile_section_localization` needs to
    bridge the `R_g`-localization (from the tile lemma) down to the `R`-localization (kernel comparison).
  - Private `res_trans_apply` (restriction functoriality; coverage bundled into `lem:qcoh_section_equalizer`
    `\lean{}` iter-042). All `#print axioms` = `{propext, Classical.choice, Quot.sound}`; `lake env lean` exit 0.
  - lean-auditor `iter041`: SOUND (0 must-fix; 1 minor `simp only []` no-op). lean-vs-blueprint-checker `qts`:
    Lean clean; one **must-fix on the BLUEPRINT** (tile_section_localization sketch omitted the base-ring
    descent + carried the unsound `restrict_obj`-rfl recipe) — FIXED iter-042 (blueprint-writer `tile-descent`).

## Iter-040 prover output (processed iter-041) — +4 axiom-clean; Route B B3 OBJECT ISO + B4 CLOSED (B-chain leaves done)
- **`QcohRestrictBasicOpen.lean` — B3 object iso + B4 COMPLETE (+4 axiom-clean, first genuine attempt).**
  - **`overBasicOpenIsoRestrict`** (`lem:restrict_over_compat`, B3 object iso) — the B3b intermediate iso
    `(modulesOverBasicOpenEquivalence g).inverse.obj (M.over (specBasicOpen g)) ≅ M.restrict (specBasicOpen g).ι`
    via `(pushforwardComp …).app M ≪≫ (pushforwardCongr (F := ι.opensFunctor) h).app M`. The
    `pushforwardCongr` data equality `h` closed kernel-clean (`ext U:3; simp; rfl` — genuine defeq, verified
    `lake env lean`+`#print axioms`, NOT the thin-cat spurious-rfl trap). Site functor `F` supplied explicitly.
  - **`presentationModulesRestrictBasicOpen`** (`lem:presentation_modulesRestrictBasicOpen`, B4) — B2
    presentation → `ofIsIso (overBasicOpenIsoRestrict).hom` → `Presentation.map (restrictFunctor
    (basicOpenIsoSpecAway g).inv) (restrictBasicOpenUnitIso g)`. The B3c affine transport lives HERE.
  - Helpers `restrictBasicOpenUnitIso`, `pullbackObjUnitToUnit_isIso_basicOpen` (coverage cleared iter-041,
    folded into B4's `\lean{}`). All `#print axioms` = `{propext, Classical.choice, Quot.sound}`.

## Iter-038 prover output (processed iter-039) — +8 axiom-clean; Route B B3 ENGINE CLOSED
- **`QcohRestrictBasicOpen.lean` — B3 engine COMPLETE (+8 axiom-clean).** `modulesOverBasicOpenEquivalence`
  (`def:modules_over_basicOpen_equivalence`): the equivalence `↥D(g).toScheme.Modules ≌ SheafOfModules
  (ringCatSheaf.over D(g))` from `pushforwardPushforwardEquivalence (Opens.overEquivalence (specBasicOpen g))
  φ ψ H₁ H₂` — the analogist-designated single load-bearing lane of B3. Plus 7 B3a helpers:
  `overForgetIso` (`Over.forget ≅ overEquivalence.functor ⋙ ι.opensFunctor`, object = `eqToIso` of
  image–preimage identity; naturality auto via thin `Opens` `Subsingleton.elim`), `overForgetInvIso` (= `Iso.refl`,
  the reverse datum is definitional), `overBasicOpenRingHom`/`overBasicOpenRingInvHom` (φ/ψ = whiskerings of
  `overForgetIso.inv`/`overForgetInvIso.inv`), the private `specBasicOpen_ι_image_overEquivalence_functor`, and
  two `overEquivalence_*_isContinuous_toScheme` defeq re-statement instances.
  **Key discoveries:** `Scheme.Opens.ι_appIso = Iso.refl` (open-immersion structure-sheaf comparison is the
  identity); `toScheme_presheaf_obj/_map` are `rfl` so both ring sheaves factor through `(Spec R).ringCatSheaf.val`.
  **CRITICAL kernel-soundness trap (recorded):** bare `ext`/`congr 1` auto-closed the thin-category H₁/H₂
  coherence via an UNSOUND rfl-term the LSP accepted but `lake env lean` rejected (`unknown free variable _fvar…`).
  Fix: explicit `NatTrans.ext`/`congrArg`/`Subsingleton.elim`, re-verified with `lake env lean` + `#print axioms`.
- Coverage debt (8 decls) cleared by planner iter-039: `def:modules_over_basicOpen_equivalence` pins the engine +
  5 B3a helpers; the two `_isContinuous_toScheme` folded into `lem:overEquivalence_isContinuous`.
- The named B3 OBJECT iso `overBasicOpenIsoRestrict` + B4 left ABSENT (mathlib-build no-sorry invariant) — precise
  in-file TODO; re-dispatched iter-039. progress-critic `iter039` = CONVERGING.

## Iter-037 prover output (processed iter-038) — +7 axiom-clean; Route B B1+B2 CLOSED (first named closures in this phase)
- **`QcohTildeSections.lean` — B1 COMPLETE (+2 axiom-clean).** `qcoh_finite_presentation_cover`
  (`lem:qcoh_finite_presentation_cover`): from `[F.IsQuasicoherent]` take `QuasicoherentData F`, translate
  `J.CoversTop` → `⨆ Uᵢ=⊤` via the helper `coversTop_iSup_eq_top`, feed `exists_finite_basicOpen_subcover`
  to get a finite `D(gⱼ)⊆U_{φⱼ}`, `span{gⱼ}=⊤`, each carrying the datum's presentation. Universe trap: pin
  `QuasicoherentData.{u,u,u,u}`; use dot-notation `[hF : F.IsQuasicoherent]` (unqualified errors). Helper
  `coversTop_iSup_eq_top` bundled into B1's `\lean{}` (writer `b3decomp`, iter-038).
- **`QcohRestrictBasicOpen.lean` — B2 COMPLETE + continuity quartet (+5 axiom-clean).**
  `presentationOverBasicOpen` (B2, `lem:presentation_over_basicOpen`): restrict `Presentation(M.over U)` to
  `Presentation(M.over D(g))` via `pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)` +
  `Presentation.map`/`ofIsIso` (pin `.{u,u,u}`; `IsContinuous`-literal `W.left` trap; `set_option
  backward.isDefEq.respectTransparency false`). PLUS the 4 `Opens.overEquivalence_*` continuity decls
  (`_functor/_inverse × _coverPreserving/_isContinuous`) that CLOSE a Mathlib TODO — the gateway B3's
  `pushforwardPushforwardEquivalence` instantiation requires. All blueprinted iter-038 as
  `lem:overEquivalence_isContinuous` (+ `lem:overEquivalence_mathlib` anchor); coverage debt cleared.
- **B3 `overBasicOpenIsoRestrict` NOT added** — the single load-bearing bridge. Site-equivalence (IsContinuous)
  half discharged by the continuity quartet; residual = the structure-sheaf compat datum `φ/ψ/H₁/H₂` built
  from `(specBasicOpen g).ι.appIso`. Decomposed B3a/B3b/B3c by the prover; blueprint sketch expanded iter-038.
  B4 mechanical after B3. Re-dispatched iter-038.

## Iter-036 prover output (processed iter-037) — +3 axiom-clean Route B local-model bricks
- **`QcohTildeSections.lean` — local model COMPLETE (+3 axiom-clean).** `tilde_section_isLocalizedModule`
  (section-restriction `Γ(⊤,M^~)→Γ(D f,M^~)` is `IsLocalizedModule (powers f)`, via `tilde.toOpen` +
  global-sections iso), `section_isLocalizedModule_of_isIso_fromTildeΓ` (the per-piece engine: counit-iso
  case, conjugate the brick through `Sheaf.forget` naturality), `section_isLocalizedModule_of_presentation`
  (globally-presented case, via `isIso_fromTildeΓ_of_presentation`). These are B0 of the keystone chain.
- **Keystone `qcoh_section_isLocalizedModule` NOT added** — blocked on the `.over`→affine base-change bridge
  (= the SAME geometric base-change that blocked Route P L2 at iter-035; Route B did not escape it). iter-037
  response: NOT a pivot — mathlib-analogist `bridge` decomposed the keystone into the B1–B6 chain with B3
  `restrict-over-compat` (`pushforwardPushforwardEquivalence`) as the single load-bearing build; chapter
  rewritten + HARD GATE PASS; B2/B3/B4 ∥ B1 dispatched. `modulesRestrictBasicOpen` wired into the root barrel.

## Iter-035 prover output (processed iter-036) — +9 axiom-clean decls; both lanes NOW DORMANT (Route B pivot)
- **Lane A `QcohRestrictBasicOpen.lean` (NEW FILE) — P1a L1 COMPLETE (+5 axiom-clean).**
  `specBasicOpen`, `specAwayToSpec` (abbrevs), `modulesRestrictBasicOpen` + `modulesRestrictBasicOpenIso`
  (the two L1 named targets — `F|_{D(f)}` transported to `(Spec R_f).Modules` via iterated
  `Scheme.Modules.restrict` + `basicOpenIsoSpecAway`, plus the comparison iso to the pullback), and
  `specAwayToSpec_eq` (= `Spec.map (algebraMap R R_f)`, the L2 feeder). L2 `tilde_restrict_basicOpen` /
  L3 `presentation_restrict_basicOpen` NOT added — both blocked on the **absent-Mathlib tilde base-change**
  (`pullback (Spec.map φ) ∘ tilde ≅ tilde ∘ baseChange φ`, Stacks `lemma-widetilde-pullback`), confirmed via
  loogle+leansearch empty. The 3 helpers wired into `lem:modules_restrict_basicOpen` `\lean{}` (writer-route-b).
- **Lane B `TildeExactness.lean` — PARTIAL (+4 axiom-clean).** `tilde_germ_algebraMap_smul` (germ is R-linear),
  `stalkMapₗ` (sub-step A: σ_x packaged as R-LINEAR map — the `map_smul'` content), `stalkMapₗ_eq`
  (σ_x = the localised map `IsLocalizedModule.map`), `stalkMapₗ_injective`. Named target
  `tildePreservesFiniteLimits` still ABSENT; residual = jointly-reflecting stalk-family assembly. The 4
  helpers wired into `lem:tilde_preserves_kernels` `\lean{}` (iter-036, this plan phase).
- **PIVOT (iter-036): both lanes DROPPED from the critical path.** mathlib-analogist `o1i8-route` showed the
  shortest Mathlib-aligned 01I8 path (Route B, section-localization) needs NEITHER tilde base-change (kills
  Lane A L2/L3) NOR `tildePreservesFiniteLimits` (kills Lane B's named target). All 9 decls + the L1 targets
  are kept as **dormant axiom-clean assets** (Route A fallback). No further prover work on either file.

## Iter-034 prover output (processed iter-035) — +6 axiom-clean decls; +Cov correctness fix (iter-035)
- **Lane A `AffineSerreVanishing.lean` — 02KG cover-system COMPLETE (+4 axiom-clean).**
  `toSheaf_preservesFiniteColimits` (Mathlib right-exact gap-fill via the sheafification square
  `sheafificationCompToSheaf`, universe-pinned `toSheaf.{v'}`, NEVER through `forget`),
  `toSheaf_preservesEpimorphisms` (corollary via `preservesEpimorphisms_of_preservesColimitsOfShape`),
  `affine_surj_of_vanishing` (`ses_cech_h1` affine instantiation; `@Functor.map_epi … .{u}` for the
  non-reducible-`Scheme.Modules` Epi-synthesis gotcha), `affineCoverSystem` (`BasisCovSystem (Spec R)`).
- **Cov correctness fix (iter-035, refactor `cov-fix`).** iter-034 lean-auditor found `affineCoverSystem.Cov`
  was built as ALL finite basic-open families WITHOUT the covering condition — making
  `HasVanishingHigherCech` over it FALSE for qcoh (counterexample `{D(x),D(y)}` on `Spec k[x,y]`, `Ȟ¹(O)≠0`).
  Adjudicated for the auditor (lvb's "broader is sound" read REFUTED — verified independently: the cokernel
  contains `x⁻¹y⁻¹ ∉ R_x+R_y`). Refactor tightened `Cov` to carry `D(f)=⨆ᵢD(gᵢ)` and re-signed
  `affine_surj_of_vanishing`'s `hvanish` to quantify only over covering families (threading the covering
  witness `standard_cover_cofinal` already produces). EXIT 0, no sorries, both decls axiom-clean.
- **Lane B `TildeExactness.lean` PARTIAL (+2 axiom-clean).** 01I8 Route-P step P3:
  `tilde_stalkFunctor_map_toStalk` (the germ-naturality CRUX — Ab-stalk path via
  `stalkFunctor_map_germ_apply` + `StructureSheaf.comapₗ_const`; the single hardest piece) +
  `tildePreservesFiniteLimits_of_toPresheaf` (categorical reduction via
  `preservesFiniteLimits_of_reflects_of_preserves` — REFUTES the feared "obstruction 2"). Named target
  `tildePreservesFiniteLimits` still ABSENT; residual sharpened to: R-linearity packaging of the Ab stalk
  map `σ_x` (HSMul/Module-R synthesis friction) + jointly-reflecting stalk-family assembly (~100–150 LOC).
  Both helpers bundled into `lem:tilde_preserves_kernels` `\lean{}` (iter-035).

## Iter-033 prover output (processed iter-034) — +3 axiom-clean decls, 0 new sorries, build green
- **Lane B `TildeExactness.lean` (NEW FILE) PARTIAL (+3 axiom-clean).** 01I8 Route-P step P3:
  `tilde_preservesFiniteColimits` (right-exact half — `~` is a left adjoint, `inferInstance` via
  `tilde.adjunction`), `tilde_toStalk_map_injective` (flatness core — `IsLocalizedModule.map_injective`
  on the public `IsLocalizedModule (tilde.toStalk · x).hom` instances),
  `tilde_preservesFiniteLimits_of_preservesKernels` (reduction via the Mathlib lemma
  `Functor.preservesFiniteLimits_of_preservesKernels`). Named target `tildePreservesFiniteLimits` left
  ABSENT (no pin) — sole residual is the Ab-stalk germ-naturality mono-transport (lean-auditor confirmed
  the earlier-feared "categorical glue" obstruction was already circumvented by the kernel-route lemma).
  3 helpers bundled into `lem:tilde_preserves_kernels` `\lean{}` (unmatched→1, iter-034).
- **Lane A `AffineSerreVanishing.lean` DID NOT RUN** (dispatch/parallelism shortfall — prover phase
  launched only one prover; file byte-unchanged). Re-dispatched unchanged iter-034.
- **Plan-phase infra (iter-034):** root barrel now imports `TildeExactness` (refactor; `lake build` EXIT 0);
  P1a `lem:isQuasicoherent_restrict_basicOpen` decomposed into a 3-lemma chain
  (`modules_restrict_basicOpen`→`tilde_restrict_basicOpen`→`presentation_restrict_basicOpen`) for the
  next-iter P1a prover lane (effort-breaker + blueprint-clean).

## Iter-032 prover output (processed iter-033) — +8 axiom-clean decls, 0 new sorries, build green
- **Lane A `AffineSerreVanishing.lean` PARTIAL (+1 axiom-clean).** `standard_cover_cofinal` (Tag 009L) —
  finite standard-open refinement of any cover of `D(f)`, realized in the indexed-cover/refinement form
  (∃ n, g : Fin n → R, φ with `D(f) = ⨆ᵢ D(gᵢ)` and `D(gᵢ) ≤ W(φ i)`); via `isCompact_basicOpen` +
  `isTopologicalBasis_basic_opens` + `IsCompact.elim_finite_subcover`. Blocked on
  `toSheaf_preservesEpimorphisms` — discovered to be `PreservesFiniteColimits (SheafOfModules.toSheaf)`
  (NOT a small instance), route resolved this iter (`analogies/tosheaf-epi.md`).
- **Lane B `QcohTildeSections.lean` COMPLETE (+7 axiom-clean).** P1b `isLocalizedModule_of_span_cover`
  (IsLocalizedModule is local on a finite spanning cover) — the entire assigned objective — + 6 private
  helpers (`exists_sum_pow_eq_one`, `mem_range_of_span_pow`, `eq_zero_of_span_pow`, `map_smul_endFun`,
  `bump_eq`, `per_j_surj`, `per_j_eq`). Direct 3-clause `IsLocalizedModule` descent via partition-of-unity
  + `bijective_of_localized_span`. Pure-algebra patching primitive for the 01I8 P1 localisation step.
  All 7 helpers bundled into `lem:isLocalizedModule_of_span_cover` `\lean{}` (unmatched 8→1, iter-033).

## Iter-031 prover output (processed iter-032) — +11 axiom-clean decls, 0 new sorries, build green
- **Lane A `CechBridge.lean` COMPLETE (+10 `…Fam` decls).** Family-parameterized Čech bridge built over a
  raw finite family `{ι}[Finite ι](U : ι → Opens X)` with NO covering hypothesis, both NAMED targets
  **`sectionCechComplexMapOpIsoFam`** + **`injective_cech_acyclicFam`** axiom-clean (mechanical mirror of the
  iter-025 X.OpenCover chain; consumes Lane-A's `cechFreeComplex_quasiIsoFam`). 8 supporting helpers
  (`homCechCosimplicialFam`, `homCechComplexFam`, `homCechSectionIsoAppFam`, `homCechSectionCosimplicialIsoFam`,
  `cechComplex_hom_identificationFam`, `homCechComplexMapOpIsoFam` + 3 private). Existing X.OpenCover decls
  byte-identical; downstream untouched. **`injective_cech_acyclicFam` now discharges
  `BasisCovSystem.injective_acyclic` over covers of any open D(f) directly.**
- **Lane B `QcohTildeSections.lean` PARTIAL (+1 axiom-clean).** P0 `exists_finite_basicOpen_subcover` landed
  (pure topology, signature matches blueprint pin). P1 `qcoh_localized_sections` NOT added (no sorry): the
  prover located the genuine blocker as TWO missing pieces — (P1a) SheafOfModules restriction-to-basic-open
  ≅ Spec-of-localization + presentation transport, (P1b) `IsLocalizedModule` local-on-a-finite-spanning-cover
  patching primitive (provable standalone via `IsLocalizedModule.mk`). Recommended split P1 = P1a + P1b +
  sheaf condition; correctly declined the off-critical-path conditional/global form.
- lean-auditor iter031: 0 must-fix / 0 major / 1 minor (stale CechBridge module doc). Both files axiom-clean,
  non-vacuous, no covering hyp smuggled in.

## Iter-030 prover output (processed iter-031) — +53 axiom-clean decls, 0 new sorries, build green
- **Lane A `FreePresheafComplex.lean` COMPLETE (+50 `…Fam` decls).** Re-parameterized the ENTIRE free
  Čech resolution chain from `(𝒰 : X.OpenCover)[Finite 𝒰.I₀]` to a raw finite family
  `{ι : Type u}[Finite ι](U : ι → Opens X)` with NO covering hypothesis, up to and including
  **`cechFreeComplex_quasiIsoFam`** (the cover-agnostic deliverable 02KG consumes over covers of arbitrary
  `D(f)`). All 50 axiom-clean. Prover REJECTED the wrapper-delegation suggestion (would break
  CechBridge:251 `dsimp only [cechFreeSimplicial]`) and instead ADDED a parallel `section
  FamilyParameterized`, keeping every X.OpenCover decl byte-identical → CechBridge + PresheafCech stay
  green & untouched. Coverage debt (50 Fam + 3 QcohTilde) cleared by blueprint-writer iter-031 (unmatched 54→1).
- **Lane B `QcohTildeSections.lean` PARTIAL (+3 axiom-clean).** 01I8 steps (2)–(3) formalised:
  `isIso_fromTildeΓ_of_genSections` (two GLOBAL generating families ⟹ IsIso fromTildeΓ via Presentation),
  `qcoh_iso_tilde_sections_of_genSections` (F≅~ΓF from the two families), `free_isQuasicoherent`. Reduced
  the residual to step (1) affine global generation (`Γ(D(f),F)=Γ(X,F)_f` + qcoh kernel closure, both
  absent from Mathlib). Prover correctly declined to relabel the gap as a single-hypothesis reduction.

## Iter-028 prover output (processed iter-029) — +7 axiom-clean decls, 0 new sorries, build green; ENTIRE 01EO chain LANDED (beyond hedge)
- **`CechToCohomology.lean` (+7)**: the whole remaining 01EO comparison chain closed axiom-clean in ONE lane,
  exceeding the iter-028 hedge (which required only L3 + 2 defs + per-face SES):
  - `sectionsFunctor` (def) — sections functor `Γ(V,-) : X.Modules ⥤ Ab`.
  - `faceShortComplex_shortExact_of_sheaf_ses` (`lem:face_ses_of_sheaf_ses`) — per-face SES bridge; mono+exact
    from `sectionsFunctor` left-exactness (`PreservesFiniteLimits` of `toPresheafOfModules ⋙ toPresheaf ⋙ eval`),
    epi from the surjectivity hypothesis (`AddCommGrpCat.epi_iff_surjective`). Built via `ShortComplex.ShortExact.mk`.
  - `absoluteCohomology_one_eq_zero_of_basis` (`lem:absolute_cohomology_one_vanishing`) — L3 base case; Ext LES
    at n=1, injective vanishing kills H¹(I), the iter-027 naturality decl transfers `hsurj`→H⁰(g) surjective ⇒ δ=0.
    Gotcha: `attribute [local instance] hasExtModules` to re-activate the file-local HasExt (else `Ext` overloads/times out).
  - `CovDatum` (abbrev) + `BasisCovSystem` (structure) + `HasVanishingHigherCech` (reducible def) — the cover-system
    encoding (`def:basis_cov_system`, `def:has_vanishing_higher_cech`). **BasisCovSystem carries 5 fields incl. the
    sheaf-theoretic `surj_of_vanishing` + `injective_acyclic`** (NOT raw cofinality — that's the deferred plumbing).
  - `injSES`/`injSES_shortExact` (private) — injective-embedding SES `0→F→I→I/F→0`.
  - `absoluteCohomology_eq_zero_of_basis` (`lem:absolute_cohomology_pos_vanishing`) — L4 dimension-shift induction
    over ALL F with `HasVanishingHigherCech`; `induction n`, Q re-enters the class via per-face-SES→L1→L2.
  - `cech_eq_cohomology_of_basis` (`lem:cech_to_cohomology_on_basis`) — TOP, thin assembly = L4 instantiated.
- **Design carry**: L4 + top carry `[EnoughInjectives X.Modules]` as an explicit hypothesis (the instance is
  genuinely ABSENT in Mathlib for sheaves of modules — would need `IsGrothendieckAbelian (SheafOfModules R)`).
  P5a convention; threads to downstream (02KG/P5b) consumers.
- Audits: lean-auditor `iter028` — 0 must-fix, 0 major, 4 minor (stale header L9–14, mildly-misleading top name,
  `show`-vs-`change`, long line). Confirmed BasisCovSystem fields non-vacuous + `[EnoughInjectives]` genuinely used.
  lvb `cechtocohom-iter028` — 0 Lean red flags, all proofs faithful; **3 blueprint-side majors (planner iter-029
  job)**: (1) `def:basis_cov_system` prose describes raw cofinality, Lean has the 5-field encoding; (2) stale
  `% NOTE: not yet formalized` annotations (already cleared by sync/review — defs now `\leanok`); (3)
  `[EnoughInjectives]` missing from L4/top blueprint statements. Plus helper-pin debt: CovDatum, sectionsFunctor,
  injSES, injSES_shortExact (`unmatched`=4).

## Iter-027 prover output (processed iter-028) — +17 axiom-clean decls (5+12), 0 new sorries, build green; 01EO L1+L2 + H⁰≅Γ naturality LANDED
- **Lane 1 — `AbsoluteCohomology.lean` (+5)**: `absoluteCohomologyZeroAddEquiv_naturality` LANDED axiom-clean
  (first try) — naturality of the H⁰≅Γ iso in the coefficient sheaf. Top arrow `H⁰(U,g) = e.comp (Ext.mk₀ g)
  (add_zero 0)`; bottom arrow `g_U = ConcreteCategory.hom (((toPresheafOfModules X).map g).app (op U))`. So
  `g_U` surjective ⇒ `H⁰(U,g)` surjective (the L3 transfer). +4 private helpers (`homEquiv₀_comp_mk₀`,
  `freeYonedaHomEquiv_naturality`, `sheafificationHomAddEquiv_naturality`, `jShriekOU_homEquiv_naturality`).
  Key: `toPresheafOfModules X` is DEFEQ `SheafOfModules.forget ⋙ restrictScalars (𝟙 _)` (`rfl`), so
  `Adjunction.homEquiv_naturality_right` applies; carriers fold by plain `rfl` (no defeq-carrier snag).
- **Lane 2 — `CechToCohomology.lean` (NEW file, +12)**: 01EO **L1 + L2 both LANDED** axiom-clean. Section-Čech
  functoriality bricks (`sectionCechCosimplicialMap/Functor`, `sectionCechComplexFunctor/Map`), `cechCohomology`
  accessor, AB4* keystone `shortExact_piMap` (product-of-SES in Ab — `Epi (Pi.map φ)` is NOT inferInstance,
  proved elementwise via `Concrete.productEquiv`), `faceShortComplex`, `sectionCechComplexShortComplex`,
  L1 `cechComplex_shortExact_of_basis`, L2 core `cechHomology_quotient_vanishing` + `quotient_cech_vanishing_of_basis`.
  Landed in the **cover-local, presheaf-level, hypothesis-driven** form (more general than the effort-breaker
  sketch): L1 takes `U : ι → Opens X`, `P : ShortComplex X.PresheafOfModules`, per-face `hface`; L2 takes the
  SES output `hSES` + explicit `hI`/`hF` vanishing in `cechCohomology` terms.
- **Wired into build root (refactor `root-import` iter-028)**: `import …CechToCohomology` added; `lake build` exit 0.
- Audits: lean-auditor `iter027` — 0 must-fix, 0 major, 3 minor; both focus targets confirmed genuine/non-vacuous.
  lvb `cechtocohom` — 2 **must-fix (blueprint prose)**: L1/L2 prose lagged the landed cover-local form; +2 major
  (shortExact_piMap, cechHomology_quotient_vanishing need blocks). **ALL FIXED iter-028** by blueprint-writer
  `01eo-reconcile` (prose rewritten to cover-local; helper blocks added; `unmatched` 14→0); blueprint-reviewer
  `iter028` HARD GATE re-CLEARS the chapter (`complete:true · correct:true`, fast-path).

## Iter-026 prover output (processed iter-027) — +10 axiom-clean decls, 0 new sorries, build green; Form-B absolute-cohomology scaffold COMPLETE
- **`AbsoluteCohomology.lean` (NEW file, +10)** — the complete Form-B absolute-cohomology scaffold landed
  in full, first prover attempt, all 6 PROGRESS objectives: `jShriekOU` (`sheafification(free(yoneda U))`),
  `sheafificationHomAddEquiv` + `jShriekOU_homEquiv` (corepr iso `(jShriekOU U ⟶ F) ≃+ Γ(U,F)`),
  `absoluteCohomology` (`AddCommGrpCat.of (Ext (jShriekOU U) F p)`), `absoluteCohomologyZeroAddEquiv`
  (H⁰≅Γ), `absoluteCohomology_eq_zero_of_injective` (one-liner — `I` is 2nd Ext arg, Form-A blocker
  eliminated), `absoluteCohomology_covariant_exact₁/₂/₃` (covariant LES wrappers). All axiom-clean
  `{propext, Classical.choice, Quot.sound}`, 0 sorries, `lake env lean` exit 0.
- **Wired into build root** (refactor `wire-root`): `import AlgebraicJacobian.Cohomology.AbsoluteCohomology`
  added to `AlgebraicJacobian.lean` — `lake build` exit 0, 8327 jobs.
- **Key Lean lessons** (now KB): `HasExt` is a Prop with THREE universe params — bare `HasExt.standard _`
  fails (rigid `w`), pin `HasExt.{u+1,u,u+1}` as a `local instance`; Mathlib's category is `AddCommGrpCat`
  (not `AddCommGrp`); `Ext.comp` degree proof must be explicit `add_zero n` (not `omega`); `∃ x.comp …`
  needs explicit binder type; adjunction `homEquiv` additivity via `erw [Functor.map_add, Preadditive.comp_add]; rfl`.
- Audits: lvb `abscohom` — 0 must-fix, 0 red flags, 3 pinned decls faithful + 5 `\mathlibok` anchors valid;
  flagged 5 substantive wrappers missing `\lean{}` blocks (MAJOR) → **fixed by the iter-027 blueprint-writer**
  (`lem:absolute_cohomology_zero`/`_injective_vanishing`/`_covariant_les` now pinned; `unmatched`=0).
- **This iter (plan) prepared the 01EO lane**: effort-breaker split `cech_to_cohomology_on_basis` into a
  4-link chain; strategy-critic SOUND (general basis criterion DECIDED); blueprint-reviewer HARD GATE CLEARS;
  progress-critic CONVERGING. Naturality of H⁰≅Γ added as an explicit 01EO sub-target.

## Iter-025 prover output (processed iter-026) — +1 axiom-clean named target, 0 new sorries, build green; the P3b Čech bridge is COMPLETE
- **P3b bridge `CechBridge.lean`** (+1) — **`injective_cech_acyclic` LANDED axiom-clean** (positive-degree
  Čech vanishing for injective sheaves, `IsZero ((sectionCechComplex (coverOpen 𝒰) (toPresheafOfModules I)).homology p)`
  for `0<p`). Landed first try via the planned one-step op-transport assembly: `cechFreeComplex_quasiIso` ⊕
  `injective_toPresheafOfModules` ⊕ `quasiIso_map_preadditiveYoneda_of_injective` ⊕ `sectionCechComplexMapOpIso`;
  `maxHeartbeats 2000000` (auditor-confirmed justified). Also fixed the 2 stale module docstrings.
  With `cechFreeComplex_quasiIso`+`ses_cech_h1` (iter-024) this closes ALL THREE P3b bridge bricks.
- Audits: lvb `cechbridge` PASS (0 must-fix; faithful p>0 realization, the p=0 `Ȟ⁰=I(U)` clause deliberately
  unformalized — review added a `% NOTE:`). lean-auditor `iter025` 0 must-fix, 3 major = stale CechBridge
  comments (planner-strategy block at 77–119 names `isoOfComponents` not the shipped `alternatingCofaceMapComplex.mapIso`
  route; "gated on Lane-1" header at 273; future-tense docstring at 357) — carried (zero-sorry file; fix when reopened).

## Iter-024 prover outputs (processed iter-025) — +21 axiom-clean decls, 0 new sorries, build green; BOTH lane bottlenecks closed in one iter
- **P3b free `FreePresheafComplex.lean`** (+10) — **`cechFreeComplex_quasiIso` LANDED axiom-clean** (the
  free Čech complex augmentation is a quasi-iso / free resolution of `O_𝒰`; project's longest churn,
  named target absent iters 020–023). Route B (arrow-iso transfer, NOT Homotopy repackaging): engine
  resolution `cechEngineComplexAug_quasiIso` (pos degrees from `cechEngineComplex_exactAt`; deg-0 from
  `descOpcycles` + `cechEngineAug0_split`), deg-0 bridge `cechFreeAug_eval_eq`, geometric identification
  `coverStructurePresheafEval_iso` (`(eval V) O_𝒰 ≅ O_X(V)` via mono+epi⇒iso), `quasiIso_of_arrow_mk_iso`
  along `cechFreeEvalEngineIso`. Plus `cechEngineComplexAug_f_zero`, `epi_cechEngineAug0`,
  `cechFreeEvalEngineIso_hom_f`, `coverStructurePresheafEval_iso_hom`, `cechFreeEval_quasiIso_of_nonempty`.
- **P3b bridge `CechBridge.lean`** (+11) — **`ses_cech_h1` LANDED axiom-clean** (Čech-H¹ sheaf-gluing
  surjectivity, full Stacks `lemma-ses-cech-h1`): single-cover-with-local-lifts faithful decomposition of
  the "cofinal system" argument. Heart = iter-023's `sectionCech_one_coboundary_of_isZero_homology`. +10
  `private` helpers (`restr_trans`, `restr_inj_of_eq`, `restr_op_unique`, `restr_g'_transport`,
  `fι_sectionCechFaceRestr`, `coverConst_iInf`, `coverPair_iInf`, `pair_comp_δ0`, `pair_comp_δ1`).
- Audits: lean-auditor `iter024` 0 must-fix (2 major = stale CechBridge module-docstrings: `ses_cech_h1`
  "(planned)" + `injective_cech_acyclic` "gated on Lane-1", both now FALSE — fix when CechBridge next
  opened, i.e. THIS iter). lvb both files PASS, axiom-clean, signature-faithful, 0 red flags.
- **Coverage debt cleared (processed iter-025)**: 32 prover-created helpers bundled into `\lean{}` lists
  (`archon dag-query unmatched` 0→0); `\restriction` macro fixed.

## Iter-023 prover outputs (processed iter-024) — +16 axiom-clean decls, 0 new sorries, build green; the 3-iter free-side bottleneck BROKE
- **P3b free `FreePresheafComplex.lean`** (+14) — **`cechFreeEvalEngineIso` LANDED axiom-clean** (the
  degreewise chain-iso `(eval V).mapHC.obj (cechFreePresheafComplex) ≅ cechEngineComplex 𝒰 V`); this is the
  differential comm-square / chain-vs-cochain variance match that CHURNED iters 020–022. Plus its
  workhorse `cechFreeEvalEngine_comm`, the per-summand bridges (`cechFreeEval_X_ι_inv`,
  `cechFreeEvalEngine_X_inv_hom_ι`, `cechFreeEvalEngine_map_ι`, `cechFree_d_ι`, `freeYonedaAug_app_comp`,
  `freeYonedaEval_iso_of_le_hom_eq_aug`, `freeYonedaEval_iso_of_le_natural`), the engine-augmentation
  cluster (`cechEngineAug0`, `cechEngineAug0_ι`, `cechEngineD_comp_aug`, `cechEngineComplexAug`), and the
  bonus positive-degree acyclicity `cechEngineComplex_exactAt`. Named end-target `cechFreeComplex_quasiIso`
  NOT built (all-or-nothing def; remaining (2) `cechFreeEval_quasiIso_of_nonempty` + (3) glue have ALL
  prereqs in-file + precise recipe in `task_results/FreePresheafComplex.md`). **KB technique**: free-complex
  objects carry `Fin (unop.len+1)`/degree `p+2` indices defeq-but-not-syntactic to `Fin (p+1+1)`, silently
  defeating `rw`/`slice`/`Category.assoc`/`Functor.map_comp` — escape via `erw` + `refine (term).trans ?_`
  (close up to defeq) + clean-codomain RHS framing.
- **P3b bridge `CechBridge.lean`** (+2) — the `ses_cech_h1` Čech-algebra core:
  `sectionCech_objD_exact_of_isZero_homology` (IsZero homology ⟹ `Function.Exact` of `objD`s) +
  `sectionCech_one_coboundary_of_isZero_homology` (Ȟ¹=0 ⟹ 1-cocycle is a coboundary, section coords).
  CechBridge now imports CechAcyclic (no cycle) to reuse the `sectionCech*` machinery. Named `ses_cech_h1`
  absent — residual is pure sheaf theory (local-surjectivity + Grothendieck gluing).
- Audits: lean-auditor `iter023` 0 must-fix (1 major = stale FreePresheafComplex module-doc "owns"
  `cechFreeComplex_quasiIso"; 3 minor). lvb `freepresheaf-i23` 0 must-fix, 2 major (blueprint-side:
  engine-augmentation cluster + `freeYonedaEval_iso_of_le_natural` unpinned). lvb `cechbridge-i23` 0 must-fix,
  2 major (blueprint-side: coboundary-core helpers unpinned; `ses_cech_h1` sketch missing Mathlib API hints).

## Iter-022 prover outputs (processed iter-023) — +30 axiom-clean decls, 0 new sorries, build green; P3 section-form CLOSED
- **P3 L1 `CechAcyclic.lean`** (+16) — **LANE FULLY CLOSED (section form, tilde case)**: the complete
  tilde F-bridge dissolving exactly as the iter-022 analogist predicted (defeq, keep the Ab complex).
  `phiL`/`phi` (φ_σ = one-line `IsLocalizedModule.iso`), `phiL_naturality` (the bottleneck, via
  `IsLocalizedModule.ext`), `restr_bridge` (accessor-1↔accessor-2, `rfl` on abstract inclusion),
  `phi_naturality`, the additive ladder (`sectionProdAddEquiv`, `sectionToModuleAddEquiv`+apply,
  `sectionProdEquiv_symm_apply`), `sectionCechCofaceMatch` (`lem:section_cech_coface_match`),
  `sectionCechAbExact` (`lem:section_cech_ab_exact`, via `Function.Exact.of_ladder_addEquiv_of_exact`),
  and the **two named public theorems** `sectionCech_homology_exact` (`lem:section_cech_homology_exact`)
  + `sectionCech_affine_vanishing` (`lem:cech_acyclic_affine` §section form). All axiom-clean. Only
  deferred gap: general-qcoh `F≅~(ΓF)` (01I8) globalisation — folded into the 02KG consumer, NOT a P3
  blocker. lean-auditor + lvb `cechacyclic`: 0 must-fix, 0 major (3 minor: stale module-doc header,
  alias theorem, private-name `\lean{}` links). Coverage debt (12 helpers) cleared iter-023 blueprint.
  **Perf lessons** (KB): `set;clear_value` to abstract heavy `modulesSpecToSheaf` section maps before
  `IsLocalizedModule.ext` (else `whnf` timeout); `change`/`DFunLike.congr_fun` on `↑(LinearEquiv).symm ∘ₗ _`
  (NOT `rw [comp_apply/coe_comp/comp_assoc]` — silent semilinear `RingHomCompTriple` mismatch).
- **P3b free `FreePresheafComplex.lean`** (+14) — engine complex built; named target still absent. The
  CHURNING corrective ran (analogist→prover): the ENTIRE engine target complex `cechEngineComplex`
  (`cechEngineD` index-insertion differential, `d²=0` `cechEngineD_comp`, contracting homotopy
  `cechEnginePrepend_spec` closed first try, positive-degree exactness `cechEngineD_exact`) + the object
  half of the engine iso (`cechFreeEvalEngine_X`, `survivingEquiv`, `cechFreeEvalDropZeros`,
  `le_coverInterOpen_iff`, `coverSectionModule`, `cechEngineX`/`_ι`). This RESOLVES the chain-vs-cochain
  variance question (chain differential = alternating sum of index-DROP reindexings `σ↦σ∘succAbove i`).
  Named target `cechFreeEvalEngineIso` (the differential comm-square) NOT built — left as documented
  comment (no sorry, no axiom). Residual = single comm-square, all inputs in-file. lean-auditor: 0 must-fix,
  1 major (module-doc overstates ownership of `cechFreeComplex_quasiIso`). lvb `freepresheafcomplex`:
  0 must-fix, 6 major — ALL blueprint-side (cleared iter-023: new `lem:cech_engine_complex` for the 14
  decls + re-pointed 2 prepend-homotopy pins to engine level + expanded engine-iso sketch).
- Processing (iter-023 plan): coverage debt 26→0 (blueprint-writer `coverage`); blueprint-clean (no edits,
  source quote verbatim-verified); blueprint-reviewer `iter023` **HARD GATE CLEARS both lanes**;
  progress-critic `iter023`: Route 2 **CHURNING-near-convergence** (corrective = blueprint expansion, done;
  prover gated on writer return), Route 3 (`ses_cech_h1`) UNCLEAR/fresh. STRATEGY: **P3 section-form moved
  to Completed**.

## Iter-021 prover outputs (processed iter-022) — +5 axiom-clean decls (CechAcyclic), 0 new sorries, build green
- **P3 L1 `CechAcyclic.lean`** (+5, +1 private): the *abstract* categorical→module homology bridge
  (step c1–c3 abstract half): `sectionCechProductEquiv` + `sectionCechProductEquiv_apply` (c1, the
  `∏ᶜ↔pi` `Concrete.productEquiv`), `sectionCechFaceRestr` + `sectionCech_objD_apply` (c2 abstract
  cosimplicial unfold of `objD` as an alternating sum of presheaf face restrictions — NO sheaf id yet),
  `sectionCech_isZero_homology_of_objD_exact` (c3 reduction: `IsZero homology` given `Function.Exact` of
  `objD`), plus private helper `ab_hom_finsetSum_apply`. All `#print axioms`-clean. Blocked on the tilde
  F-bridge (the concrete per-σ section identification) — RESOLVED by iter-022 analogist as a `rfl`-level
  `IsLocalizedModule.iso` one-liner. Coverage debt (5 unmatched) cleared by blueprint-writer `cofacematch`.
- **FreePresheafComplex `FreePresheafComplex.lean`**: NOOP-DROPPED at plan-validate (0-sorry file, scaffold
  keyword on the line after the `.lean` path) — no prover ran; the CHURNING corrective is re-dispatched
  iter-022 with the keyword fixed.

## Iter-020 prover outputs (processed iter-021) — +18 axiom-clean decls, 0 new sorries, build green; 3 NAMED sub-targets landed
- **P3b free `FreePresheafComplex.lean`** (+10): the **`FreeCechEngine.*` combinatorial contracting-homotopy
  engine** (constant-coeff free-side port of the private `CombinatorialCech.*`: `combDifferential`/`_comp`/
  `_exact`/`_eq_of_cocycle`, `combHomotopy`/`_spec`/`_zero`, `combSign_flip`, `cons_comp_succAbove_succ`) +
  per-summand evaluation bridges (`freeYonedaEval_iso_of_le`/`_isZero_of_not_le`) + named targets
  `cechFreeEval_X` (`lem:cech_free_eval_sectionwise` entry) and `cechFreeEval_quasiIso_of_isEmpty`
  (`lem:cech_free_eval_empty`). `cechFreeComplex_quasiIso` NOT built — blocker is the **differential
  match** (evaluated alt-face differential ↔ `combDifferential` on coproduct injections); blueprinted
  iter-021 as new node `lem:cech_free_eval_engine_iso`.
- **P3 L1 `CechAcyclic.lean`** (+4): named target `qcohSectionsAwayLocalized` (`def:qcoh_sections_localized`,
  tilde case) + the two step-(c) bricks `basicOpen_sprod`, `qcohRestriction_eq_comparison`. Step (c)
  `sectionCech_homology_exact` blocked: `sectionCechComplex` is Ab-valued with `∏ᶜ` objects, so
  `moduleCat_exact_iff` inapplicable — needs `ab_exact_iff` + `Concrete.productEquiv`; blueprinted
  iter-021 as a 3-sub-lemma chain.
- **P3b bridge `CechBridge.lean`** (+4): contravariant-transport bridge `homCechComplexMapOpIso`,
  `sectionCechComplexMapOpIso` + degreewise `homCechComplex_d_eq` (resolved iter-019 Probe sorry; file now
  0 sorries). `injective_cech_acyclic` correctly held (gated on Lane-1 quasi-iso); now a one-step assembly.
- Processing (iter-021 plan): blueprint-writer cleared coverage debt 24→0 + added the differential-match
  node + the ab_exact_iff 3-sub-lemma section chain + 3 bridge blocks; private-`CombinatorialCech.*`
  refs purged from free-eval proofs; blueprint-reviewer `iter021` HARD GATE CLEARS both prover lanes;
  progress-critic `iter021`: Route 1 CONVERGING (SLIPPING), **Route 2 CHURNING** (corrective = the
  differential-match blueprint node + dispatch, which this iter executes).

## Iter-019 prover outputs (processed iter-020) — +29 axiom-clean decls, 0 new sorries, build green; 2 NAMED targets landed
- **P3 L1 `CechAcyclic.lean`** (+24): the entire `R`-module exactness core of the section form, built
  bottom-up — localisation-transitivity keystone `AwayComparison.comparison_isLocalizedModule`
  (`M_a[1/b]=M_{ab}`), the un-localised section module complex `D• = ∏_σ M_{s_σ}` (`SectionCechModule.*`),
  the differential-naturality square, the `fLoc`/`IsLocalizedModule.pi` chain, culminating in the
  **named step-(a) target `dDiff_exact`** (`lem:section_cech_module_exact`): positive-degree
  `Function.Exact` of `D•` via `exact_of_isLocalized_span`. Steps (b)–(d) handed off.
- **P3b bridge `CechBridge.lean`** (+2): the **named Lane-1 target `cechComplex_hom_identification`**
  (`homCechComplex 𝒰 F ≅ sectionCechComplex (coverOpen 𝒰) F`) via `homCechSectionCosimplicialIso`
  + `(alternatingCofaceMapComplex Ab).mapIso`. `injective_cech_acyclic` correctly held (needs quasi-iso).
- **P3b free `FreePresheafComplex.lean`** (+3): `quasiIso_of_evaluation` (objectwise reduction, step 1
  of 3) reducing `cechFreeComplex_quasiIso` to a single per-`V` obligation; used the JOINT-conservativity
  route (single-functor `quasiIso_map_iff_of_preservesHomology` fails — `evaluation` not
  `ReflectsIsomorphisms`). Named target NOT built (per-`V` homotopy is the ~20-decl combinatorial core).
- Processing (iter-020 plan): `lem:cech_free_complex_quasi_iso` effort-broken into a 6-link `\uses` chain
  (route (a)); coverage debt 28→0 (`def:section_cech_module_complex` + `lem:section_cech_module_exact`
  blocks + bundling); 4 lean-auditor stale-comment majors fixed (2 refactor, 2 folded into prover
  instructions); blueprint-reviewer `iter020` HARD GATE CLEARS all 3 lanes; progress-critic `iter020`
  all CONVERGING.

## Iter-018 prover outputs (processed iter-019) — +36 axiom-clean decls, 0 new sorries, build green
- **P3 L1 `CechAcyclic.lean`** (+22): away-localisation comparison algebra `AwayComparison.*` (11) +
  concrete Čech localised maps `CechLocalized.*` (11) with the 3 compatibilities, capstone
  `cechLocalized_exact` (positive-degree exactness of the section complex localised at a spanning
  element) — the hardest, most-uncertain L1 sub-task. Section-form named target not yet built.
- **P3b free `FreePresheafComplex.lean`** (+3, +1 repair): augmentation chain map
  `cechFreeComplexAug : K(𝒰)_• ⟶ O_𝒰[0]` (`cechFreeComplexAug_f_zero`, `cechFree_d_comp_factorThruImage`);
  repaired the broken-on-entry `cechFree_d_comp_aug` (file now compiles). Target `cechFreeComplex_quasiIso`
  rephrased to `QuasiIso (cechFreeComplexAug)`, not yet built (large homotopy lane).
- **P3b bridge `CechBridge.lean`** (+5): the full mathematical core of the hom-identification
  (`homCechCosimplicial`, `homCechComplex`, `homCechSectionIsoApp`, `homCechSectionIsoApp_hom_π`,
  `freeYonedaHomAddEquiv_naturality`). Target `cechComplex_hom_identification` held back OPERATIONALLY
  (concurrent FreePresheafComplex breakage — now resolved); 2-decl assembly recipe fully derived.
- **P5a `HigherDirectImagePresheaf.lean`** (NEW file, +6): reusable 01XJ engine
  `PresheafOfModules.homologyIsoSheafify` + resolution form `higherDirectImage_iso_sheafify_presheafHomology`.
- Reviews: lean-auditor `iter018` 0 must-fix on Lean code (all 36 `#print axioms`-clean); the review
  signal was administrative (orphan import, P5a design fork, 44-node coverage debt, 4 stale comments,
  broken `\uses`) — ALL cleared iter-019 (plan phase).

## Iter-019 (plan phase) — P5a re-sign + cleanup + 3 gate-cleared lanes dispatched
- **P5a re-signed (LEAF)**: `lem:higher_direct_image_presheaf` → resolution form + new engine block
  `def:cohomology_sheaf_is_sheafify_homology` (blueprint-writer + blueprint-clean). strategy-critic
  `iter019` CHALLENGE (the re-sign RELOCATES, not eliminates, the absolute-cohomology obligation to the
  consumers) — addressed in STRATEGY.md framing + `Sheaf.H`-path open question.
- **Coverage debt 44→0** (all helpers bundled into `\lean{...}` lists); broken `\uses{}` removed;
  orphan `HigherDirectImagePresheaf.lean` wired into root barrel; 4 stale comments fixed (refactor
  `cleanup`); `lake build` green 8326 jobs.
- **blueprint-reviewer `iter019`** (whole blueprint): Lanes 1 & 2 GATE CLEAR; Lane 3 cleared after the
  broken-`\uses` removal (deterministically verified, unmatched 0). **progress-critic `iter019`**: all
  routes CONVERGING/UNCLEAR, 0 CHURNING/STUCK.
- **3 parallel lanes dispatched**: CechBridge (hom-id, shortest), FreePresheafComplex (quasiIso, large),
  CechAcyclic (P3 L1 section-form named targets).

## Iter-016 prover outputs (processed iter-017) — +21 axiom-clean decls, 0 new sorries
- **P3b free `cechFreePresheafComplex`** (`def:cech_free_presheaf_complex`) — DONE: built via the
  simplicial route (`cechFreeSimplicial` → `alternatingFaceMapComplex`, `d²=0` free). +8 decls
  (`freeYoneda`, `coverOpen`, `coverInterOpen`, `coverInterOpen_comp_le`, `cechFreeSimplicial`,
  `cechFreePresheafComplex`, `cechFreePresheafComplex_X`, `sigma_ι_eqToHom_transport`). `[Finite 𝒰.I₀]`
  added (needed for coproducts; matches downstream). Used `∐` (coproduct) = `⨁` for finite index.
- **P3b section `sectionCechComplex`** (`def:section_cech_complex`) — DONE: built `Ab`-valued
  (`CochainComplex Ab ℕ`, matching the Stacks source quote) via `sectionCechCosimplicial` +
  `alternatingCofaceMapComplex`. +4 decls (incl. `freeYonedaHomAddEquiv`, the additive upgrade).
- **P3 dependent-coefficient L3 port** (`CechAcyclic.lean`) — DONE: +9 axiom-clean
  `CombinatorialCech.Dependent.*` decls ending in `depDiff_exact : Function.Exact`. Both L3 forms
  (constant + dependent) + L2 certifier now in place.
- Reviews (lean-auditor + 3 lvb-checkers): 0 must-fix on Lean code; all axiom-clean (kernel-only).

## Iter-016 (plan phase) — L1 blueprint filled; P3b split into 2 parallel files; 3 lanes gate-cleared
- **Coverage debt cleared**: 11 unmatched helper decls bundled into 3 `\lean{...}` lists
  (`lem:cech_acyclic_affine` +9 `CombinatorialCech.*`; `lem:cech_complex_hom_identification`
  +`freeYonedaHomEquiv`; `lem:injective_cech_acyclic` +`injective_toPresheafOfModules`).
- **L1 gap filled** (blueprint-writer `l1bridge`): added the categorical→module bridge paragraph to
  the proof of `lem:cech_acyclic_affine` — term id `Γ(D(s_σ),F)=M_{s_σ}`, differential compatibility,
  iso of cochain complexes reducing positive-degree vanishing to L2+L3. Sourced verbatim to Stacks
  Schemes Tag 01HV(4)–(5); retriever child fetched `references/stacks-schemes.tex`.
- **P3b file-split** (refactor `split-freecomplex`): created `FreePresheafComplex.lean` (skeleton +
  strategy comment, no decls), wired root import; build green (8324 jobs). `% archon:covers` updated.
- **blueprint-reviewer `iter016`**: HARD GATE clears for all 3 target files (1 must-fix = the missing
  covers line, fixed by plan agent). L1 bridge "sound and adequate for formalization."
- **progress-critic `iter016`**: both routes UNCLEAR (one genuine prover data point — iter-015; priors
  externally killed). No CHURNING/STUCK. Commitment recorded: P3 must dispatch (done this iter).
- **3 parallel lanes dispatched** (next prover round): `PresheafCech.lean` (sectionCechComplex),
  `FreePresheafComplex.lean` (cechFreePresheafComplex + quasiIso), `CechAcyclic.lean` (close affine).

## Iter-015 (prover phase) — first genuine prover trajectory; both critical lanes advanced axiom-clean
- **P3 `CechAcyclic.lean`**: +9 axiom-clean private decls in `CombinatorialCech` — the L3 contracting
  homotopy (`combDifferential`, `combHomotopy`, `combHomotopy_spec` = `d∘h+h∘d=id`, `combDifferential_comp`
  = `d²=0`, `combDifferential_exact` = `Function.Exact`, +4 helpers). Target `CechAcyclic.affine` still
  1 sorry (blocked on L1 — addressed iter-016). lean-auditor + lean-vs-blueprint-checker: 0 must-fix.
- **P3b `PresheafCech.lean`**: +2 axiom-clean decls — `injective_toPresheafOfModules` (Part 1 of
  `injective_cech_acyclic`, via `Injective.injective_of_adjoint`+`sheafificationAdjunction`) and
  `freeYonedaHomEquiv` (per-term core of the hom-identification). 3 bricks handed off with recipes.
  lean-vs-blueprint-checker: blueprint adequate, 0 must-fix.

## Iter-011 (plan phase) — P3b realigned to bypass two expensive bricks; file-split + 2 parallel lanes dispatched
- **Gate cleared (same-iter fast path).** Entered with the iter-010 bridge chapter cleared by an
  `injcech-recheck`. blueprint-reviewer (`iter011`) flagged `lem:injective_cech_acyclic` referenced
  undeclared presheaf sub-lemmas → blueprint-writer (`injcech`) added them + clean + recheck CLEARED.
- **STRATEGY-MODIFYING: analogist `p3b-presheafcech` found the P3b machinery mis-aligned + over-built.**
  `injective_cech_acyclic` does NOT need presheaf enough-injectives or the Čech δ-functor universality
  (both Mathlib-absent + expensive: no `IsGrothendieckAbelian (PresheafOfModules)`, no functor-category
  transfer, no AB5). Direct route: injective sheaf ⟹ injective presheaf via
  `Injective.injective_of_adjoint`(`sheafificationAdjunction`) + Hom(-,I)-exactness on the free
  resolution. Also: the bespoke `j_!` must be `PresheafOfModules.free(yoneda U)` (parallel-API risk).
- **Blueprint realigned** (blueprint-writer `p3b-realign` + clean + reviewer `p3b-realign-recheck`):
  rewrote `cechFreePresheafComplex` (free(yoneda), no `j_!`), added `def:section_cech_complex` (distinct
  from relative `CechComplex`), restated `cechComplex_hom_identification`, rewrote `injective_cech_acyclic`
  to the direct route, added 2 `\mathlibok` anchors (`injective_of_adjoint`, `sheafificationAdjunction`),
  REMOVED 4 off-path blocks (`presheaf_modules_enough_injectives`, `cech_delta_functor_presheaves`, +2
  Grothendieck anchors). DAG acyclic, `unknown_uses: []`. Recheck: P3 + P3b machinery HARD GATE CLEAR.
  STRATEGY.md updated (bypass route; format must-fix from strategy-critic). Fixed the one residual
  must-fix (stale δ-functor sentence in `lem:higher_direct_image_presheaf`) directly.
- **File-split executed** (standing directive; lean-scaffolder `p3-split` + `p3b-skeleton`):
  `CechAcyclic.lean` (P3, `CechAcyclic.affine` re-signed to the spanning bundle, build green) +
  `PresheafCech.lean` (P3b roadmap skeleton, build green), both under one `% archon:covers`; frozen
  `cech_computes_higherDirectImage` kept in `CechHigherDirectImage.lean`. blueprint-doctor clean.
- **P5a design captured** (analogist `p5a-01xj`, NEEDS_GAP_FILL): funnel into the P4 engine; avoid a
  bespoke module-valued cohomology; persistent `analogies/p5a-01xj.md`. Blueprint realign next iter.
- **Two parallel `mathlib-build` lanes dispatched**: P3 (`CechAcyclic.lean`) + P3b (`PresheafCech.lean`).
- progress-critic SKIPPED (prior iter-010 ran no prover phase → no trajectory; rationale in
  iter-011/plan.md `## Subagent skips`). strategy-critic ran (`iter011`, SOUND).

## Iter-010 (plan phase) — caught + repaired a circular blueprint; strategy corrected
- **Circularity caught by TWO independent critics + repaired.** blueprint-reviewer (HARD GATE fail) +
  strategy-critic (CHALLENGE) both found the iter-009 de-spectral-sequencing made
  `lem:cech_to_cohomology_on_basis` circular: it obtained affine Serre vanishing "from the P3
  contracting homotopy alone," but term `G`-acyclicity IS affine vanishing on a smaller affine — a
  regress with no inductive base, hidden by a missing `\uses` edge. Confirmed by reading Stacks directly
  (`stacks-cohomology.tex` L1287–1773): affine vanishing (02KG) genuinely needs the Čech↔derived bridge.
- **FIX (blueprint-writer `cech-bridge` + blueprint-clean `cech-bridge`)**: added the minimal
  **torsor-free** bridge — `lem:injective_cech_acyclic` (`lemma-injective-trivial-cech`) +
  `lem:ses_cech_h1` (`lemma-ses-cech-h1`) + the genuine dimension-shift proof of
  `lem:cech_to_cohomology_on_basis` (01EO `lemma-cech-vanish-basis`). Cycle broken (proof `\uses` no
  longer routes `affine_serre_vanishing` back). The FULL 01EO/torsor bootstrap (`lemma-cech-h1`,
  `lemma-kill-cohomology-class`) confirmed avoidable. DAG re-verified acyclic (`unknown_uses: []`,
  `conflicts: []`); all 7 source quotes validated verbatim. Blueprint nodes 43→46.
- **STRATEGY.md restructured**: new phase **P3b** (the bridge) with honest estimates; circular
  "term-acyclicity from homotopy" claim removed from Routes; format DRIFT (5 iter-NNN prose refs)
  stripped; Mathlib gaps updated (presheaf-Čech for `O_X`-modules; P3 cover-type + `exact_of_isLocalized_span`).
- **P3 design LOCKED (mathlib-analogist `p3-localisation`)**: cover-type → `affineOpenCoverOfSpanRangeEqTop`
  bundle `(s, hs)`; local-to-global → `exact_of_isLocalized_span` (spanning elements, not primes); L1+L3
  the from-scratch core. Added `def:standard_affine_cover` `\mathlibok` anchor. Persistent:
  `.archon/analogies/p3-localisation.md`.
- **No prover dispatched** (mechanical gate): chapter restructured this iter; needs fresh gate +
  bridge effort-break + signature refactor before dispatch. iter-011 plan recorded in PROGRESS.md.
- progress-critic SKIPPED (only active route P4 completed prior iter — no trajectory; rationale in
  iter-010/plan.md `## Subagent skips`).

## Iter-009 (prover phase) — P4 abstract layer CLOSED
- **`AcyclicResolution.lean`: 2 final P4 decls added** (`rightDerivedOneIsoCokerOfAcyclic`,
  `rightDerivedIsoOfAcyclicResolution` = TARGET 3), both axiom-clean `{propext, Classical.choice,
  Quot.sound}`, full `lake build` passes. lean-vs-blueprint-checker (`acyclic`): 0 must-fix, signatures +
  proofs faithful. lean-auditor (`iter009`): the 2 new decls sound; flagged stale `.lean` narrative
  comments (out of plan write-domain — carried to upkeep). **P4 phase CLOSED**; DAG gaps = 0.

## Iter-009 (plan phase)
- **P5a effort-honesty CHALLENGE addressed** (strategy-critic must-fix). STRATEGY.md updated:
- **P5a effort-honesty CHALLENGE addressed** (strategy-critic must-fix). STRATEGY.md updated:
  the basis lemma `lem:cech_to_cohomology_on_basis` is no longer treated as atomic — enumerated
  its sub-prerequisites and committed the REDUCED-SCOPE route (project only needs the affine /
  standard-cover special case, proved directly via the P4 theorem with `G = Γ(B,-)` + the P3
  contracting homotopy; NOT the full Stacks-01EO Čech-to-derived-H¹ bootstrap). Confirmed the
  P3↔basis bridge is non-circular (basis lemma consumes narrowed-P3 standard-cover Čech vanishing,
  produces general affine vanishing). Re-estimated P5a (~3–6 iters / ~250–550 LOC).
- **3 mandatory critics dispatched.** progress-critic: P4 **CONVERGING** (residual 5→3→2, precise
  recipes for last 2 leaves, dispatch to close). strategy-critic: **CHALLENGE** (Route A verified
  genuinely SS-free — traced the rewrite for all three suspect P5 lemmas with exact Stacks line
  refs; the one challenge = P5a effort honesty, addressed above). blueprint-reviewer:
  `Cohomology_AcyclicResolution.tex` **HARD GATE CLEARS** for both remaining P4 leaves;
  `Cohomology_CechHigherDirectImage.tex` `partial/partial` (3 SS-contaminated blocks).
- **P5a blueprint de-spectral-sequencing dispatched** (blueprint-writer): rewrote the three
  contaminated proof blocks (`lem:cech_to_cohomology_on_basis`, `lem:open_immersion_pushforward_comp`
  part (2), `lem:cech_term_pushforward_acyclic` prose) to Route-A arguments. Forward investment to
  open P5a as a parallel prover lane next iter.

## Iter-007 (prover phase) — P4 cosyzygy layer; 3 of 5 TARGET-3 leaves closed
- **`AcyclicResolution.lean`: 11 axiom-clean decls added** (`Cosyzygy` section, 0 sorry; axioms
  `{propext, Classical.choice, Quot.sound}`). Closed 3 of the 5 TARGET-3 leaves:
  `lem:cosyzygy_ses` (`cosyzygyShortExact`), `lem:applied_cosyzygy_cycles`
  (`gCosyzygyIsoCocycles`), `lem:cohomology_of_applied_resolution`
  (`cohomologyAppliedResolutionIso` n≥1 + `gHomologyZeroIso` n=0).
- Prover **declined** the last 2 leaves at a clean cut (avoiding a non-axiom-clean partial under
  mathlib-build) and handed off a precise, indexing-checked recipe for both (see iter-009
  PROGRESS objective). Input-type design decision recorded by the prover (it owns this; no
  protected decl affected): bare `K : CochainComplex 𝒜 ℕ` + `(e : A ≅ K.cycles 0)` +
  `(hexact : ∀ n, K.ExactAt (n+1))` + `[∀ n, G.IsRightAcyclic (K.X n)] [G.Additive]
  [PreservesFiniteLimits G]`.
- Reusable Lean lessons (in task result): `ShortComplex.mapCyclesIso` is wrong for a left-exact
  functor (use `isLimitForkMapOfIsLimit'` + `conePointUniqueUpToIso`); `← G.map_comp` silently
  fails beside a mapped-complex term (isolate in a clean `have`, close in term mode).
- lean-vs-blueprint-checker (`acyclic`) + lean-auditor (`iter007`): the 3 closed leaves verified
  axiom-clean + faithful to blueprint; no must-fix; the 2 frontier-leaf blueprints flagged
  Lean-level under-specified (input type / LES mechanism) — handled in PROGRESS hints, not blueprint.

## Iter-008 (dag re-sync stage)
- Deterministic DAG re-sync (no prover phase). Graph: zero broken `\uses{}`, zero isolated nodes.

## Iter-007 (plan phase)
- **TARGET 3 effort-broken + gate-cleared.** `effort-breaker` decomposed
  `lem:acyclic_resolution_computes_derived` (the comparison theorem) into a sourced `\uses`-chain:
  `lem:cosyzygy_ses`, `lem:acyclic_one_iso_coker` (the iter-006 PARTIAL-COVERAGE base coker iso,
  split out of `lem:acyclic_dimension_shift`), `lem:applied_cosyzygy_cycles`,
  `lem:cohomology_of_applied_resolution` + assembly. `lem:acyclic_dimension_shift` now states part
  (1) only (matches its Lean decl exactly).
- **2 broken `\uses{}` refs fixed.** Plan agent wrote blueprint blocks `lem:quasiIso_tau2`
  (`HomologicalComplex.HomologySequence.quasiIso_τ₂`) + `lem:right_derived_shift_split_resolution`
  (`Functor.rightDerivedShiftIsoOfSplitResolutionSES`) for two already-proven Lean decls. DAG now
  has zero broken edges, zero isolated blueprint nodes.
- **P4 HARD GATE CLEARS** (fast path): blueprint-clean (6 process-NOTE blocks stripped, source
  quotes validated) + whole blueprint-reviewer → `Cohomology_AcyclicResolution.tex` `complete +
  correct`, all `\mathlibok` anchors verified, 0 unstarted-phase proposals.
- progress-critic: P4 CONVERGING. strategy-critic: CHALLENGE (specific) — addressed in STRATEGY.md
  (P5a/P5b split committed, basis lemma scoped, format de-narrativised, P5 spectral-sequence-rewrite
  open question added).

## Iter-006
- **P4 TARGET 1 + TARGET 2 CLOSED** (`mathlib-build`, 14 axiom-clean decls). Built the middle-term
  quasi-iso transfer `HomologicalComplex.HomologySequence.quasiIso_τ₂` (ABSENT from Mathlib; a
  homology four-lemma over `mapComposableArrows₅` windows), then assembled straight-line:
  `quasiIso_horseshoeι` → `ofShortExact_resolvesMiddle` → `ofShortExact` (dual Horseshoe Lemma,
  TARGET 1) → `rightDerivedShiftIsoOfAcyclic` (object-level dimension shift, part 1, TARGET 2). The
  multi-iter horseshoe bottleneck closed. Prover correctly declined TARGET 3 (separate multi-lemma
  construction) and handed off the (a) base coker iso + (b) cosyzygy-SES recipe.

## Iter-005
- **Horseshoe DECOMPOSED.** `effort-breaker` split `lem:injective_resolution_of_ses`
  (`InjectiveResolution.ofShortExact`) into a 7-link `\uses`-chain: 2 verified `\mathlibok`
  anchors (`Injective.instBiprod`, `ShortComplex.Splitting.ofHasBinaryBiproduct`), 1
  project-decl anchor (`mono_biprod_lift_factorThru_of_exact`), 4 NEW provable sub-goals
  (`ofShortExact_twist`/`_dComp`/`_chainMap`/`_resolvesMiddle`). Target effort 1754→1228.
- **DAG poisoning fixed.** `refactor` reformatted the backtick code-fence in `AcyclicResolution.lean`
  that fooled `sync_leanok` into a false `\leanok` on the (nonexistent) horseshoe; file compiles,
  markers auto-strip this iter.
- **P4 HARD GATE re-cleared** (fast path): blueprint-clean + whole blueprint-reviewer →
  `Cohomology_AcyclicResolution.tex` `complete: true`, `correct: true`; both `\mathlibok` anchors
  verified faithful; `lem:horseshoe_twist` needs no finer re-break. Fixed the one "soon" finding
  (imprecise exactness citation in the twist proof) directly in the blueprint.
- progress-critic: P4 UNCLEAR (fresh, 1 effective prover iter) — proceed; decompose-then-build is
  the correct response to the monolith. P3 narrowing DECIDED (option a, downstream-safe).

## Iter-004
- **P4 horseshoe CONSUMERS all built + axiom-clean** (`mathlib-build`, 5 decls): the dimension-shift
  engine `rightDerivedShiftIsoOfSplitResolutionSES` (via `δIso`, not a hand-rolled LES — key
  discovery), `isZero_homology_mapHomologicalComplex_of_isRightAcyclic`,
  `shortExact_of_degreewise_splitting`, `shortExact_map_mapHomologicalComplex_of_degreewise_splitting`,
  and the per-stage horseshoe mono `mono_biprod_lift_factorThru_of_exact`. Collapsed the entire P4
  chain to the single remaining horseshoe object. (Prover correctly declined the monolith.)

## Iter-003
- **P4 unblocked + scaffolded + dispatched.** `Cohomology_AcyclicResolution.tex` anchor
  must-fix fixed (`lem:homology_long_exact_sequence` `\lean{}` now names all four
  `homology_exact₁/₂/₃`+`δ`, verified present) → scoped re-review → **P4 HARD GATE CLEARS**.
  (blueprint-writer + clean + re-review)
- `AcyclicResolution.lean` created (compiles, 8321/8321): `CategoryTheory.Functor.IsRightAcyclic`
  class + `[Injective]` instance landed no-sorry; three hard targets documented in the strategy
  block; wired into root build. (lean-scaffolder)
- **mathlib-analogist re-validated the P4 route**: horseshoe is the cheapest/necessary gap;
  Ext LES (Hom-specific) and derived-category route (open Mathlib TODO bridge) both rejected.
  Persistent rationale: `analogies/p4-derived-les.md`.
- Blueprint hygiene: rewrote misleading `lem:push_pull_comp` proof body (real
  `rawPushPullMap`/pentagon route); added `def:push_pull_functor` + `def:cech_nerve_cosimplicial`
  blocks (1-to-1 restored). (blueprint-writer + clean)
- Verified Mathlib P4 infra present (`isoRightDerivedObj`, `rightDerivedZeroIsoSelf`,
  `isZero_rightDerived_obj_injective_succ`, `homology_exact₁/₂/₃`, `δ`); horseshoe absent. (plan agent)

## Iter-002
- STRATEGY.md: addressed both strategy-critic CHALLENGEs — P4 reframed honestly (shared
  SES-acyclicity-propagation / LES kernel, buildable from Mathlib's complex-level homology
  sequence + a to-build horseshoe); P5 re-estimated (bundles 3 `Scheme.Modules` vanishing
  theorems). (plan agent)
- `Cohomology_AcyclicResolution.tex`: rewrote the P4 proofs off the phantom `rightDerived`-level
  δ-functor onto the comparison-of-resolutions kernel (new homology-LES `\mathlibok` anchor +
  to-build horseshoe block). (blueprint-writer + clean)
- `Cohomology_CechHigherDirectImage.tex`: scoped P3/P5 fixes — verbatim SOURCE QUOTE on
  `lem:cech_to_cohomology_on_basis`; two new wired sub-lemmas for `lem:cech_term_pushforward_acyclic`.
  Chapter re-reviewed → `complete + correct`; **P1 HARD GATE cleared** (fast-path). (blueprint-writer + clean + scoped re-review)
- Retrieved Stacks `cohomology.tex` → `references/stacks-cohomology.tex` (Tags 01EO/01XJ/relative-Leray).
- Frontier validation: confirmed the push–pull mate lemmas are already PROVED and
  `pushPullMap_comp` is a build-and-prove target (no decl yet) — corrected a graph mis-read. (plan agent)

## Iter-001
- Strategy pivot to the acyclic-resolution route (Route A); STRATEGY.md restructured to the
  canonical skeleton. (plan agent)
- Blueprint rewrite to Route A: new chapter `Cohomology_AcyclicResolution.tex`; comparison
  proof of `lem:cech_computes_cohomology` rewritten; `lem:push_pull_functor` split into
  `lem:push_pull_id` + `lem:push_pull_comp`; `lem:cech_acyclic_affine` split into Čech-complex
  vanishing + `lem:affine_serre_vanishing` + `lem:cech_to_cohomology_on_basis`. Cleaned
  (blueprint-clean) and graph-consistent (`unknown_uses: []`, acyclic). (blueprint-writers)
- Retrieved Stacks `derived.tex` + `homology.tex` for the acyclic-resolution chapter.

## Pre-existing (inherited from parent at extraction; verified axiom-clean)
- `pushPullMap_id`, `pushPull_unit_mate`, `pushPull_transport_cancel`, `pushPull_unit_comp`,
  `pushforwardComp_hom_app_id`, `rawPushPullMap`, `pushPullMap_eq_raw`, `coverArrow`,
  `coverCechNerve`, `pushPullObj`, `pushPullMap`, `relativeCechComplexOfNerve`, `CechComplex`
  (def, modulo `CechNerve`), `higherDirectImage`.
