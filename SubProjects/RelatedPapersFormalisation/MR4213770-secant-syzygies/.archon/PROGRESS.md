# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] dag
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Notes
**P0a Foundations substrate COMPLETE** (iters 006–013, axiom-clean): two-tier sheaf-cohomology bridge,
heavy `IsGrothendieckAbelian X.Modules`, openwise + sheafified `Scheme.Modules.{exteriorPower,symPower}`.

**P0b eval-map / kernel-bundle substrate (iters 014–020):** `Scheme.Modules.{trivialBundle, evalMap,
evalKernel}`; `Basic.lean` `MR4213770.kernelBundle := evalKernel L`. Core-2 affine-reduction chain
(Hartshorne III Ex 6.5): **L1**+**L2** (016) + **L3** (017) + **tilde-pullback nodes 1–3** (018) +
**node-4 (c)** localizationTransitivity (019) + **node-4 (d1)** source_isLocalizedModule + stalk-instance
shims (020) ALL LANDED axiom-clean. `Foundations.lean` ~1783 lines, 0 sorry.

**iter-021 — the (a1) "wall" is GONE.** mathlib-analogist `a1-stalk` (HARD result, both anchors
loogle-verified by planner): (a1) "sheafification of a module presheaf is stalkwise-iso" is **NOT a
Mathlib gap** — `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` (general value category) gives
it directly at `AddCommGrpCat`. The project already does ALL module-sheaf stalk work at the Ab level via
`Scheme.Modules.toPresheaf` (`def:peer_module_iso_locality`, `Foundations.lean:53`), so (a1)/(a2) need
only **Ab** stalk isos — the iter-019/020 `Module ↑R`/ModuleCat-stalk synthesis fears DO NOT apply at
this layer. Blueprint (a1)/(a2) proofs rewritten with the concrete decl chain; (a2) bridge node added;
3 coverage-debt blocks cleared; (d1) `\uses` wired. HARD GATE GREEN (blueprint-reviewer `r21`: PASS,
complete+correct, 0 must-fix; 3 new `\mathlibok` anchors loogle-verified; leandag + doctor clean).
progress-critic `node4`: CONVERGING (on schedule, 7/4–9 iters; no helper-churn).

Reminder (ARCHON_MEMORY): a mathlib-build lane on a zero-sorry file MUST lead its objective line with
the literal verb **"Scaffold"** or plan-validate drops it as `failed_all_noop`.

## Current Objectives

1. **`MR4213770UniversalSecantBundlesAndSyzygiesOfCanonicalCurves/Foundations.lean`** — **Scaffold** the
   node-4 stalkwise-iso chain (a1)→(a2-bridge)→(a2)→(a)→(d2) INTO the file (file is ZERO-sorry;
   mathlib-build ADDs axiom-clean decls bottom-up, NOT a fill-the-sorry task). Build as far up as you
   can; each decl fully proved or absent (no `sorry`, clean STOP/handoff if blocked). Blueprint:
   `chapters/Kemeny_PeerDependencies.tex` (HARD GATE GREEN, blueprint-reviewer `r21`).
   [prover-mode: mathlib-build]

   **DECISIVE CONTEXT (kills the iter-019/020 stalk-synthesis fears):** the project already performs every
   module-sheaf-iso check at the `AddCommGrpCat` level through `Scheme.Modules.toPresheaf X`
   (`Modules.isIso_iff_isIso_stalkFunctor_map`, `Foundations.lean:53`, = `def:peer_module_iso_locality`;
   it uses `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` + `toPresheaf` reflects isos). So (a1)/(a2)
   only need **Ab** stalk isomorphisms; the structure-sheaf-stalk module structure is recovered at the
   very end by `toPresheaf`-reflects-isos, never per node. Do NOT synthesize `Module ↑R`/ModuleCat stalk
   instances at this layer.

   **DISPATCH ORDER (bottom-up):**

   1. **(a1)** `lem:tilde_pullback_stalk_sheafificationStalk` →
      `tildePullbackComparison_stalk_sheafificationStalkIso`. THE 3-step recipe (analogist `a1-stalk`,
      anchors planner-verified):
      (i) reduce to an `AddCommGrpCat` stalk iso via `Scheme.Modules.toPresheaf` /
      `def:peer_module_iso_locality`; `SheafOfModules.pullbackIso`
      (`…/ModuleCat/Sheaf/PullbackContinuous.lean`) puts `(SheafOfModules.pullback q_f).obj (tilde M)`
      into `forget ⋙ presheafPullback ⋙ sheafification` form, so the comparison map IS the sheafification
      unit (α = `𝟙 R.obj`);
      (ii) rewrite the underlying-Ab unit to `toSheafify` via
      `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app` [verified] — holds by `rfl`
      (needs `IsLocallyInjective`/`IsLocallySurjective`/`WEqualsLocallyBijective AddCommGrpCat`/
      `HasWeakSheafify` instances for α = 𝟙 — should be automatic for the identity);
      (iii) close with `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := AddCommGrpCat)`
      [verified].
   2. **(a2-bridge)** `lem:tilde_pullback_stalk_presheafPullback_toPresheaf_bridge` →
      `tildePullbackComparison_presheafPullback_toPresheaf_iso`: the underlying-`AddCommGrpCat` presheaf
      of the `PresheafOfModules`-pullback of `tilde M` along `q_f` ≅ the `TopCat.Presheaf` inverse-image
      of its underlying Ab presheaf along `q_f.base` (both = left Kan extension along `Opens.map q_f.base`).
      **CRUX the prover must resolve (was stripped from blueprint as syntactic):** confirm whether
      `SheafOfModules.pullback`'s inverse image is carried by `PresheafOfModules.pullback φ.hom`
      (change-of-rings, `…/Sheaf/Pullback.lean:44`) or the continuous functor `F`/`sheafPushforwardContinuous`
      — this fixes WHICH `TopCat.Presheaf.pullback` instance `stalkPullbackIso` must match. Pin it before
      stating the iso.
   3. **(a2)** `lem:tilde_pullback_stalk_presheafPullbackStalk` →
      `tildePullbackComparison_stalk_presheafPullbackStalkIso`: compose the (a2-bridge) with
      `TopCat.Presheaf.stalkPullbackIso` [verified, `mathlib:stalkPullbackIso`] to get the presheaf-pullback
      stalk ≅ `(tilde M)` stalk at the image point `q_f(x)`.
   4. **(a)** `lem:tilde_pullback_stalk_pullbackStalkIso` →
      `tildePullbackComparison_stalk_pullbackStalkIso`: compose (a1) ∘ (a2) → `(q_f^* tilde M)_x ≅
      (tilde M)_{q_f(x)}`.
   5. **(d2)** `lem:tilde_pullback_stalk_target_isLocalizedModule` →
      `tildePullbackComparison_stalk_target_isLocalizedModule`: the (d)-analogue of the landed (d1). By
      (a), `(q_f^* tilde M)_x ≅ (tilde M)_𝔮`; the latter is `IsLocalizedModule 𝔮ᶜ M` via
      `mathlib:tilde_stalk_localization` (`instIsLocalizedModuleStalkOfTilde`). Transport along the iso
      (an `IsLocalizedModule` is preserved under a linear iso of the target). The `Module ↑R` structure
      here IS needed (it is the `(d)` localization claim, not an Ab-only stalk iso) — reuse the iter-020
      recipe: restricted R-module via `Module.compHom _ φ` + `IsScalarTower.of_algebraMap_smul`.

   **If you factor a reusable non-private helper** (e.g. a generic "IsLocalizedModule transports along a
   linear iso" or an "Ab stalk iso reflects to module iso" lemma), it is coverage debt: list it with its
   real `\uses` under "## Needs blueprint entry". A `private`/local construction needs no entry.

   **HAZARDS (carried):** `change` not `show`; `← cancel_mono` for iso-cancels; ascribe `(↑s : R)` on
   submonoid-coe smul; universe-pin ring-sheaf on `tilde`/`free` constructions. **FABRICATED (absent
   v4.30.0, grep-confirmed):** `SheafOfModules.{IsLocallyFree,stalk}`, `PresheafOfModules.stalk`,
   `ModuleCat.Tilde.stalkIso`, `tildeInModuleCat`, `ModuleCat.tilde{,Finsupp}`,
   `TopCat.Presheaf.sheafifyStalkIso` (this last is `Type`-only étale-space — do NOT use for the site
   sheafification). Keep bespoke `Scheme.Modules.IsLocallyFree`.

   **OUT OF SCOPE (do NOT stub):** (d3) `comparison_commutes` (needs α_M germ-naturality + the
   `toPresheaf`↔`moduleSpecΓFunctor` germ bridge — defer), node-4 target
   `found:tilde_pullback_comparison_stalk`, `found:tilde_pullback_iso`, `found:tilde_restrict_basicOpen`,
   L4 `lem:isLocallyFree_kernel_on_affine`, `found:isLocallyFree_kernel_of_shortExact`,
   `found:rank_kernel_of_shortExact`, `found:eval_kernel_locally_free`,
   `MR4213770.kernelBundle_isLocallyFree`.

## Out of scope this iter
- **(d3) `tilde_pullback_stalk_comparison_commutes`** — the irreducible (d) step: needs α_M germ-naturality
  through `stalkFunctor` + the `toPresheaf`↔`moduleSpecΓFunctor` germ bridge. Defer; NEVER state it as
  `target_map := (α_M)_x ∘ source_map` (circular). With (d1)+(d2) landed, the node-4 target then needs
  only (d3) + `mathlib:isLocalizedModule_uniqueness`.
- **The three deferred `Basic.lean` paper objects** — `lazarsfeldMukaiBundle`, `GrassmannPencilMap`,
  `BNPGen` (`def:kemeny_LM_bundle`, `lem:kemeny_grassmann_pencil_map`, `lem:kemeny_BNP_gen`). `\uses`
  UNDER-DECLARES the real substrate (K3 Picard-rank-one, curve inclusion, `g^1_{k+1}` pencils, `i_*A`,
  Brill–Noether `W^1_{k+1}`, Grassmannian) — none built (P2/P3). `opaque` stubs stay.
- **`def:kemeny_koszul_cohomology`** — needs line-bundle tensor powers `L^q`, `H⁰(L^q)`, Koszul
  differentials; a later mathlib-build lane.
- **Core-2 chain tip (gated on node 4):** L4 + `isLocallyFree_kernel_of_shortExact` +
  `rank_kernel_of_shortExact` + `evalKernel_isLocallyFree`; `MR4213770.kernelBundle_isLocallyFree`.
