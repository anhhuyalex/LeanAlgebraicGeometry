# Index
<!-- One line per file. Update line numbers when the file changes. -->

- `Foundations.lean` (iter-021 ACTIVE) — Core-2 affine-reduction chain. L1+L2+L3 + tilde-pullback
  nodes 1–3 + node-4 (c)+(d1)+stalk-instance shims LANDED axiom-clean (~1783 lines, 0 sorry). Chain tip
  `found:tilde_restrict_basicOpen` gated on node 4 `found:tilde_pullback_comparison_stalk` (7-lemma
  `\uses`-chain). HARD GATE GREEN (blueprint-reviewer `r21` PASS, 0 must-fix; progress-critic
  `node4`/iter-021 CONVERGING).
  • **(c)** LANDED 019, **(d1)** + shims + `extendScalars_unit_isLocalizedModule` LANDED 020 (see task_done).
  • **(a1) IS NOT A MATHLIB GAP** (analogist `a1-stalk`/iter-021, both anchors loogle-verified by planner):
    `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` (general value cat, use at `AddCommGrpCat`)
    gives sheafification-stalk-iso directly; `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`
    rewrites unit→`toSheafify` by `rfl`. The project does ALL module-sheaf stalk work at Ab level via
    `Scheme.Modules.toPresheaf`/`def:peer_module_iso_locality` ⇒ (a1)/(a2) need only Ab isos (NO Module↑R synth).
  THIS iter (021): `mathlib-build` lane (lead "Scaffold") to land **(a1)→(a2-bridge)→(a2)→(a)→(d2)** bottom-up:
  • **(a1)** `…_sheafificationStalkIso` — the 3-step recipe above.
  • **(a2-bridge)** `…_presheafPullback_toPresheaf_iso` — module-pullback's underlying Ab presheaf = TopCat
    inverse-image; CRUX the prover pins: which `TopCat.Presheaf.pullback` instance `stalkPullbackIso` matches
    (change-of-rings `PresheafOfModules.pullback φ.hom` vs continuous functor).
  • **(a2)** `…_presheafPullbackStalkIso` = (a2-bridge) ∘ `TopCat.Presheaf.stalkPullbackIso`.
  • **(a)** `…_pullbackStalkIso` = (a1) ∘ (a2): `(q_f^* tilde M)_x ≅ (tilde M)_{q_f(x)}`.
  • **(d2)** `…_target_isLocalizedModule` = (d)-analogue of landed (d1): via (a) transport
    `mathlib:tilde_stalk_localization`; Module↑R via `Module.compHom _ φ`+`IsScalarTower.of_algebraMap_smul`.
  Full recipe in chapter `Kemeny_PeerDependencies.tex` (node-4 chain) + PROGRESS.md.
  **STOP at (d3)** `…_comparison_commutes` (α_M germ-naturality + `toPresheaf`↔`moduleSpecΓFunctor` germ
  bridge); NEVER state it as `(α_M)_x ∘ source_map` (circular). DO-NOT-USE (FABRICATED, absent v4.30.0):
  `SheafOfModules.{IsLocallyFree,stalk}`, `PresheafOfModules.stalk`, `Tilde.stalkIso`, `ModuleCat.tilde`,
  `TopCat.Presheaf.sheafifyStalkIso` (Type-only étale-space). Any NEW non-private helper = coverage debt.

- DEFERRED — Core-2 chain TIP (gated on the tilde chain above): once `found:tilde_restrict_basicOpen`
  lands, assemble L4 `lem:isLocallyFree_kernel_on_affine` (consumes the pullback form), target
  `found:isLocallyFree_kernel_of_shortExact` (Hartshorne III Ex 6.5), `found:rank_kernel_of_shortExact`,
  `found:eval_kernel_locally_free`; then `MR4213770.kernelBundle_isLocallyFree`
  (`lem:kemeny_kernel_bundle_locally_free`, Basic.lean) waits on the whole chain.

- DEFERRED (substrate absent, P2/P3 arc) — `def:kemeny_LM_bundle` (E), `lem:kemeny_grassmann_pencil_map`,
  `lem:kemeny_BNP_gen`: "ready" on the frontier but `\uses` UNDER-DECLARES the true deps (K3 Picard-rank-one
  lattice, curve inclusion i:C↪X, g^1_{k+1} pencils, pushforward i_*A, Brill–Noether W^1, the Grassmannian)
  — none blueprinted. `opaque` stubs in Basic.lean stay. Do NOT dispatch a formalize prover (fake
  statements — HARD GATE forbids). `def:kemeny_koszul_cohomology` waits on line-bundle tensor powers `L^q`
  + Koszul differentials (later substrate lane).
