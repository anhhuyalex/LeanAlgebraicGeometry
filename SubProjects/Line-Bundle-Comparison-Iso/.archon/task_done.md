# Done Tasks
<!-- Resolved items, last-known state only. Per-attempt detail → iter sidecars. -->

- **K1 μ/δ-side `pushforward_mu_appIso_collapse` (`TensorObjSubstrate.lean`) — CLOSED iter-031, axiom-clean.**
  The circular-mate blocker for iters 026–030. Bypassed by extracting the reduction as a NEW abstract helper
  `deltaConjOfMuComparison` (`private`, L4423; `Type*` clean fvars dodge the zeta-`let`/whnf friction that
  killed every inline attempt) + a one-line `exact deltaConjOfMuComparison hadj' (pullbackPushforwardAdjunction
  φ') A B (pushforward_lax_mu_comparison f A B)`. `lean_verify`: only propext/Classical.choice/Quot.sound.
  Transitively sorry ONLY via `lhs_tmul` (through `pushforward_lax_mu_comparison`). `deltaConjOfMuComparison`
  is private → no blueprint block owed (coverage phase). Closes fully once `lhs_tmul` lands.

- **K1 μ-side RHS `pushforward_lax_mu_comparison_rhs_tmul` (`TensorObjSubstrate.lean`) — PROVEN iter-029,
  axiom-clean (green).** The RHS-composition tensorator's pure-tensor value: `(μ (restrictScalars φ') M₁ M₂).app W
  (m⊗ₜn) = m⊗ₜn`, proof `= restrictScalars_μ_app_tmul`. Stated generic/abstract (abstract base-ring functors +
  abstract `M₁ M₂`) with `set_option backward.isDefEq.respectTransparency false in` BEFORE the doc comment —
  concrete K1 `Gβ.obj`/`pushforward₀` section binders fail module-synth (memory `restrictscalars-mu-tmul-binder-trap`);
  applied to the K1 objects by defeq. Also: parent `pushforward_lax_mu_comparison` body is now sorry-free
  (clean `hom_ext` delegation to the per-section lemma — the prior undecomposed in-proof sorry eliminated);
  transitively sorry only via `_lhs_tmul` (still open, deferred to iter-031 solo lane).

- **K1 η-side `pushforward_eta_appIso_collapse` (`TensorObjSubstrate.lean`) — CLOSED iter-028, axiom-clean.**
  First K1 critical-path sorry eliminated after the ~14-iter η stall (leaf sorries 6→5). The blocker was pure
  Lean plumbing (RingCat `map_one` won't fire; `𝟙_` `OfNat` won't synth), solved by the mathlib-analogist
  `analogies/eta-plumbing.md` idiom: new sorry-free helper `restrictScalars_oplaxMonoidal_η_app_one` states
  `1` through `(S ⋙ forget₂ CommRingCat RingCat).obj W`; closer `erw [restrictScalars_oplaxMonoidal_η_app_one
  β' hβ (op (f⁻¹ᵁU)), map_one]; rfl`. (`rw [Functor.map_id]` FAILS — dependent motive; `erw [helper]` matches
  the whole `(restrictScalars β').map 𝟙 ≫ η` composite up to defeq.) Blueprint helper entry authored bp029.
- **Cocycle-A collapse mechanism (`TensorObjInverse.lean`) — PROVEN mod B1, iter-028, axiom-clean.** Two new
  fully-proven helpers: `tensorHom_inv_comp_leftUnitor` (generic monoidal coherence `s≫s'=𝟙 → (s⊗ₘs')≫λ=λ`)
  and `tensorObjIsoOfIso_comp_unit_iso` (B2; the `X.ringCatSheaf.val` vs `presheaf⋙forget₂` carrier diamond
  crossed via `erw [Functor.map_comp]` + `exact congrArg (·≫_) hmap`). `tensorObj_unit_self_duality_collapse`
  body now sorry-free (N-leg via `congrArg Iso.symm (dualUnitIso_dualIsoOfIso t)` + `simpa`; the
  `(dualIsoOfIso t).symm = dualIsoOfIso t.symm` rewrite is a DEAD route — `Iso.self_symm_id` "pattern not
  found"). Memory: [[cocycle-a-collapse-mechanism]]. Residual = B1's eval-core (N) only.

- **Connector `homOfLocalCompat_restrictFunctor_map` (`DualInverse.lean`) — CLOSED iter-026, axiom-clean.**
  `(restrictFunctor (U i).ι).map (homOfLocalCompat U hU f hf) = f i`. Route: reconstruct gluing internals
  defeq + `change` to glued-section form + morphism-level `key` collapsing the `homLocalSection`
  eqToHom-conjugation via `eqToHom_comp_iff` + `exact`-matched `α.naturality` (forward `rw [naturality]`
  fails — X-level vs restrict-level only defeq, not syntactic). `SheafOfModules.Hom.ext` BEFORE
  `PresheafOfModules.hom_ext`. `(U i).ι ''ᵁ P ≤ U i` = `Scheme.Opens.ι_image_le` (NOT `image_le_range`).
  DualInverse.lean now fully sorry-free. (Memory: [[restrictfunctor-glued-morphism-pattern]].)
- **Terminal residual B (`exists_tensorObj_inverse`, `TensorObjInverse.lean`) — CLOSED iter-026.** With the
  connector decl present, `rw [key]; exact hfiso x` where `key := homOfLocalCompat_restrictFunctor_map U _ f _ x`.
  Leaf sorries 5→3. The 3-iter connector "non-delivery" was a plan-validate DROP (file had 0 sorries →
  prover never dispatched), fixed by scaffolding the stub first (iter-026 plan turn).

- **Seed-1 D4′ chart-chase ASSEMBLED iter-020** (`pullbackTensorIsoOfLocallyTrivial`, L4238): body sorry-free,
  reduces the whole D4′ `IsIso` obligation to the single open-immersion brick K1. 3 new sorry-free `private`
  helpers (aud020: non-vacuous + used): `isIso_of_isIso_comp4_mid` (generic plumbing), `chart_isIso` (per-chart
  core: `isIso_of_isIso_restrict` transport + two `pullbackTensorMap_restrict` D3′ splits), and K2
  `pullbackTensorMap_isIso_of_base_unit` (trivial-base case via `pullbackTensorMap_natural` D1′ +
  `pullbackTensorMap_unit_isIso` D2′). Residual = K1 only (see task_pending). aud020 + tos020 PASS; tos020
  must-fix = blueprint mis-counted D4′ ("only D3′ is new" wrong) → K1 node added iter-021.

- **`pullbackValIso_comp_leg` (Sq4, `lem:pullback_val_iso_comp`) — CLOSED iter-019 axiom-clean** (`propext, Classical.choice, Quot.sound`; no `sorryAx`). The 5-iteration-stuck D3′ leaf brick. Key unblock: `η^Z` unit-naturality on both legs factors a common leading `η ≫ forget(·)`, collapsing the goal to a clean sheaf-level cocycle `hH`; `slice_lhs`/`slice_rhs` fold + `exact comp_forget_cocycle`. `hH` chased via Sq4a inverse (`inv_telescope`) + `pullbackComp` naturality at counit + adjunction triangle `(adj.homEquiv).left_inv`. 5 new sorry-free `private` helpers: `comp_forget_cocycle`, `inv_telescope`, `cocycle_assemble`, `sheafificationCompPullback_comp_inv` (realises `lem:pullback_val_iso_comp_scpb`), `adj_unit_map_counit` (realises `lem:pullback_val_iso_comp_counit`). **Consequence: `pullbackTensorMap_restrict` (`lem:pullback_tensor_map_basechange`) and the WHOLE D3′ comparison-iso substrate cone are now sorry-free.** progress-critic standing CHURNING resolved by an actual sorry elimination. (aud019 + tos019 PASS.)

- `AlgebraicGeometry.Scheme.Modules.dualUnitRingSwap_apply` — solved helper from session 2; supports the DUAL inverse path and is now accounted for in the project state.
- `sheafificationCompPullback_comp_tail` (`lem:sheafificationcomppullback_comp_tail`) — CLOSED iter-006 (the 6-iter STUCK D3′ node) via `conjugateEquiv_comp` at NatTrans level (recipe `d3cocycle006.md`); its caller `sheafificationCompPullback_comp` is now sorry-free end-to-end. Also `sheafificationCompPullback_comp_natTrans` (prototype) and the `hδ`/Sq2b sub-sorry of `pullbackTensorMap_restrict`.
- `sliceDualTransport.toFun.naturality` (forward ε-square) — CLOSED iter-007 via the morphism-level recipe (`dualnat006.md`): extracted standalone `sliceDualTransport_naturality_apply`, closed pointwise through `appIso_hom_naturality_apply` + `dualUnitRingSwap_apply` + `φ.naturality_apply` (never sending `inv ε` through `whnf`). Also `map_add'`/`map_smul'`. This is the working template for the inv-naturality root.
- `sliceDualTransportInv.naturality` (the DUAL ROOT, multi-iter blocker gating the whole dual chain) — CLOSED iter-012 axiom-clean. NOT the morphism-level rotation (that times out at `whnf` of `inv ε`); instead the forward template's route — an extracted shallow-statement lemma `sliceDualTransportInv_naturality_apply` (down-set facts passed explicitly, ε-swap legs kept shallow), then the def's `naturality` field closed by `exact` (defeq matches the rfl-legs automatically). Proof of the apply-lemma: `hM` M-side coherence + `ψ`-naturality + `appIso_inv_naturality`. Helper `sliceDualTransportInv_app_apply` (rfl) also added. Blueprint entries authored iter-013 (`lem:slice_dual_transport_inv_naturality_apply`, `lem:slice_dual_transport_inv_app_apply`).
- `sheafifyMap_pullbackComp_hom_inv_id` (D3′ brick 1, `lem:sheafify_pullbackcomp_hom_inv_cancel`) — PROVED iter-012 axiom-clean (`private lemma`): `rw [← Functor.map_comp]; erw [Iso.hom_inv_id_app]; exact aZ.map_id _`. The step-(i) cancellation of the four-square interleave. (`Functor.map_id/comp` resolve to the monad first — use `aZ.map_id`/`aZ.map_comp`; `Iso.hom_inv_id_app` needs `erw` post-merge.)
- `sliceDualTransport.left_inv` + `.right_inv` (DUAL route final) — CLOSED iter-015 axiom-clean; `SliceTransport.lean` now sorry-free, seed `dual_isLocallyTrivial` delivered, DUAL route COMPLETE. Root cause was NOT a tactic gap: L890 was already fixed; the file was RED from a heartbeat-budget overflow on the inline 6-field `≃ₗ` — fixed by `set_option maxHeartbeats 1600000`. `right_inv` = 3-step mirror of `left_inv` (ring-identity collapse via `appIso_inv_naturality`, ψ-naturality at a thin-poset slice, `Y.presheaf` round-trip). Built in an isolated HEAD worktree to dodge the import race. (Dead ends: `rw [← hnat]` proof-term mismatch → `show … from hnat.symm`; `simp [eqToHom_map]` over-collapses → targeted `rw`.)
- **D3′ step (i) `D ≫ E = 𝟙` cancellation** (the iters-012–015 wall) — CLOSED iter-015. New `private comp_cancel_mid` (generic single-`[Category C]` middle-cancellation `(r0 ≫ r1 ≫ r5 ≫ d) ≫ e ≫ rest = r0 ≫ r1 ≫ r5 ≫ rest` for `d ≫ e = 𝟙`) applied by `exact` (NOT `rw`): the defeq unifier crosses the defeq-but-not-syntactic `SheafOfModules` instance gap that defeats `rw [Category.assoc]` and mate-`whnf`-bombs `erw`. Spliced via `erw [reassoc_of% hmain]`. General device for instance-boundary cancellation. (lean-auditor aud015: SOUND, not vacuous, genuinely used.)
- **D3′ step (ii) δ-split** — CLOSED + SPLICED iter-016 via `sheafifyMap_δcomp_split` (`lem:sheafifymap_deltacomp_split`, axiom-clean): `a_Z.map δcomp = a_Z.map((pullback φ'_h).map δ_f) ≫ a_Z.map δ_h`, definitional from `Functor.OplaxMonoidal.comp` (`rw [← Functor.map_comp]; congr 1`), spliced by `erw`.
- **D3′ step (iii)-a/b.1/b.2** — SPLICED iter-017, narrowing the `pullbackTensorMap_restrict` residual to the single presheaf identity `hcore2`. (iii)-a = `S1^h` slide (`comp_slide_nested` + `.symm` of `sheafificationCompPullback h` naturality at `δ_f`); (iii)-b.1 = prefix cancel (`comp_cancel_three_lr`); (iii)-b.2 = slide of `V` (`comp_slide_three` + `map_comp_slide`; `hcomb` via `sheafificationCompPullback h` naturality at `gg` + `a_Y.map_comp` + `sheafifyTensorUnitIso_hom_eq'`). All helpers `private`, generic instance-boundary plumbing applied by `exact`/`refine`. Also iter-017 RED→GREEN repair (stray bombing `erw` removed). (lean-auditor aud017: 4 helpers non-vacuous + used.)
- **D3′ step (iii).b.3 merged Sq3/Sq4 presheaf core `hcore2`** — CLOSED iter-018. Fold-then-presheaf chase mirroring D1′ `pullbackTensorMap_natural`: `sheafifyTensorUnitIso_hom_eq'` rewrites each `sTUI.hom` to `a_Z.map(η⊗η)`; new `private map_comp4_eq_comp5` folds the 4-vs-5 `a_Z.map` chain to one `a_Z.map Ψ` (applied by `refine`, crosses the instance wall); concrete fully-applied `have hδnat := δ_natural …` (instance pinned via `show … from`) spliced by `erw [← reassoc_of% hδnat]` (metavar `δ_natural` whnf-bombs); new `private tensorHom_collapse_3_4` collapses the tensorHom chains by bifunctoriality to two per-leg identities. `pullbackTensorMap_restrict` is now **sorry-free modulo** the single isolated brick `pullbackValIso_comp_leg`. (lean-auditor aud018: 3 helpers non-vacuous + used; not laundered.) The standalone-extraction `pullbackTensorMap_restrict_core` was ABANDONED (carrier `MonoidalCategoryStruct` not top-level synthesizable); blueprint node `lem:pullback_tensor_basechange_presheaf_core` DROPPED iter-019 (content realised in-place).
