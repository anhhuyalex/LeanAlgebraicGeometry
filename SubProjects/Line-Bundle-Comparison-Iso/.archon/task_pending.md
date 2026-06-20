# Pending Tasks
<!-- Current open-task set, last-known state only. Per-attempt detail → iter sidecars. -->

## Seed 1 — `pullbackTensorIsoOfLocallyTrivial` (D4′ chart-chase) — `TensorObjSubstrate.lean` — ACTIVE iter-033 (SOLO lane)
STATE: body CLOSED. K1 residual `hmon` DECOMPOSED; **η-side CLOSED iter-028**; μ-side RHS + comparison-assembly
CLOSED iter-029; **`pushforward_mu_appIso_collapse` CLOSED iter-031** (via new axiom-clean abstract helper
`deltaConjOfMuComparison` + one-line `exact`; see task_done). **SOLE residual = `lhs_tmul`** (sorry@L4362).
This is the import-chain ROOT; co-dispatching it with downstream lanes caused the iter-029 build-race
(ARCHON_MEMORY), so it runs ALONE. **iter-032 deferred it to iter-033** because iter-032's mandated SOLO lane
is the STUCK Terminal (TensorObjInverse, which imports this root — cannot co-run a root-churn). Blueprint
`lem:pushforward_lax_mu_comparison_lhs_tmul` REWORDED + EXPANDED iter-032 (writer `lhs-tmul` + clean: statement
→ per-section comparison form; first proof step = identify `hadj'` with `pushforwardPushforwardAdjunction` so
the unit value lemma applies). iter-033 must land it (pc032: 4-iter recurring blocker, CHURNING).
- **`pushforward_lax_mu_comparison_lhs_tmul`** (`lem:pushforward_lax_mu_comparison_lhs_tmul`, sorry@L4362)
  — THE genuine residual (multi-hundred-LOC mate seam). Per-section comparison (let-chain + fixed `W`,
  `tensor_ext` INSIDE — UNSTATABLE as a standalone pure-tensor lemma, module-instance trap). iter-029 committed
  `tensor_ext` + `rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]` (mate → explicit
  `unit ≫ G.map(δGβ ≫ counit⊗counit)`); iter-031 committed the verified sectionwise split `rw [comp_app,
  hom_comp, comp_apply]` (opaque mate-μ now the explicit 3-leg form). RESIDUAL = sectionwise value of the unfolded
  mate on `m⊗ₜn`. **iter-033 NEXT STEP (the 4-iter wall):** un-`let` `hadj'` (or `change` to the
  `pushforwardPushforwardAdjunction` form) so `pushforwardPushforwardAdj_unit_app_app_apply` keys on the unit leg;
  then δGβ leg → `Functor.OplaxMonoidal.comp_δ` + `restrictScalars_μ_app_tmul`/`forget₂_restrictScalars_μ_hom_tmul`;
  counit pair → bijective `f.appIso`. All via `erw` (no whnf), mirroring `pushforwardComp_lax_μ` for a MATE LHS.
  Routing through `hadj'.IsMonoidal` is CIRCULAR.
- Pin: `AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoOfLocallyTrivial`. Blueprint §"K1 monoidal-mate
  bridge". Reference: Stacks `lemma-tensor-product-pullback` — `references/stacks-modules.tex`.

## Terminal — `exists_tensorObj_inverse` (`lem:tensorobj_inverse_invertible`) — prover DEFERRED to iter-034 (effort-break iter-033)
STATE: descent skeleton BUILT; collapse MECHANISM PROVEN (iter-028); **import chain GREEN since iter-031**.
**pc032 reversal LIVE: route CONFIRMED STUCK (math/infra, not infra-flake).** iter-032's first clean green-window
SOLO lane closed only S1 of `trivialisation_restrict_compat` (chart morphism `j=resLE`, reindex endpoints
`hobjU`/`hobjV` — all proved in-proof) and replaced the bare sorry with a 4-square scaffold ending in a scoped
sorry. The block is NOT a tactic gap — it is 5 bespoke per-constituent restriction-naturality squares. **iter-033
corrective = blueprint EFFORT-BREAK (NOT a 4th blind prover lane):** split `lem:trivialisation_restrict_compat`
into 5 named squares + telescope (effort-breaker `trivcompat-squares`). iter-034 then proves S2
`tensorObj_restrict_iso` square first as the structural template. Both cocycle connectors EXIST:
`homOfLocalCompat_restrictFunctor_map` (DualInverse:786), `image_preimage_of_le` (DualInverse:519). Two sorries:
- **`trivialisation_restrict_compat` (`TensorObjInverse.lean` L183 sorry@~L244)** — restriction-functor
  naturality of the trivialisation iso-chain. S1 CLOSED iter-032 (chart morphism `j`+reindex endpoints, kept as
  scaffold — telescope consumes them). Residual = 5 per-constituent restrict-naturality squares against `j`
  (tensorObj_restrict_iso; dual_restrict_iso≫dualIsoOfIso eM; dual_unit_iso; tensorObj_unit_iso; +
  blueprint-OMITTED `uι`=restrictFunctorIsoPullback≫pullbackUnitIso). Each is a composite pullback+sheafification
  iso, NO codebase precedent. effort-broken into sub-lemmas iter-033. Mirror `restrictIsoUnitOfLE`
  (`analogies/cocycle-a.md` §A); memory [[restrictfunctor-glued-morphism-pattern]] (`SheafOfModules.Hom.ext`
  before `PresheafOfModules.hom_ext`; `eqToHom_comp_iff`+`exact`-matched naturality; forward `rw [naturality]`
  fails on X-vs-restrict defeq). DEAD probes (iter-032): subst/rcases on `hVU:V≤U` (not eqn),
  `simp[restrictIsoUnitOfLE]`, `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`.
- **Cocycle `exists_tensorObj_inverse` (`TensorObjInverse.lean` sorry@~L438, `first | <derivation> | sorry`)** —
  **FULL iso-algebra reduction DERIVED + written in-code iter-029, hedged iter-030** (paper- + abstract-verified
  `/- Planner strategy -/` block): `erw [trivialisation_restrict_compat …]` reduces both overlap legs to one `t`;
  `dualIsoOfIso_trans` + insert `dual_unit_iso ≪≫ dual_unit_iso.symm = 𝟙` ⇒ `dualLeg eMj = dualLeg eMi ≪≫ sConj`;
  `tensorObjIsoOfIso_trans` factors RHS; the residual is EXACTLY `tensorObj_unit_self_duality_collapse t`
  (sorry-free). iter-032: on the green tree, verify the `first` branch fires + **strip the `| sorry` hedge**;
  transitively gated on `trivialisation_restrict_compat`. NEVER sheafify-the-eval (d.2 dead-end).
- **Residual B** — CLOSED iter-026. Recipe `rem:dual_discharges_inverse`. Non-critical branch (seed-3
  `map_add` rides seed-1→K1).

## Scaffold target — seed 3 `PicSharp.addCommGroup_via_tensorObj` (`RelPicFunctor.lean`)
STATE: not in Lean. Gated on seed-1 (map_add ← comparison iso) + `exists_tensorObj_inverse` (group inverse).

## Tracked debt
- Coverage: 5 iter-019 helpers are `private` generic plumbing (no node owed) except
  `sheafificationCompPullback_comp_inv` (pinned `lem:pullback_val_iso_comp_scpb`). Bulk ~99 `lean_aux`
  decls remain; scheduled `Coverage + file-split` phase.
- File-split: `TensorObjSubstrate.lean` >3600 LOC (over 1000-LOC policy) — split scheduled after the
  active seed-1 lane lands (avoid disrupting the warm file).

## Completeness audit (user-requested) — DONE
3-seed cone COMPLETE vs AJC: 108/108 nodes, cone sizes 52/36/32 exact. Diffs = AJC dead-code Lan block
(not ported) + out-of-scope Route-A. Nothing required missing.
