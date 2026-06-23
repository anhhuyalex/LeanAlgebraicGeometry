# Strategy

## Goal

Close the `sorry`-bearing nodes of two **Čech-independent (i=0)** legs split from the parent
*Quot-Foundations* `thm:fga_pic_representability` cone, then merge back (names/labels are the parent's):

- **FBC-B** — flat base change of the degree-0 pushforward: the i=0 map `g^* f_* F ⟶ f'_* g'^* F` is an
  isomorphism. Seeds `affineBaseChange_pushforward_iso` + `flatBaseChange_pushforward_isIso`
  (`thm:flat_base_change_pushforward`), via the CONCRETE-tilde equalizer chain.
- **SNAP** — the section graded ring `Γ_*(X,L) = ⊕_{n≥0} Γ(X,L^{⊗n})` as a graded commutative semiring
  (`lem:sectionGradedRing_gcommSemiring`) + its graded module (`lem:sectionGradedModule_gmodule`).

End-state: zero project `sorry` in these two cones, zero axioms (kernel-only).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---|---|---|---|
| FBC-B — global H⁰ iso (concrete-tilde equalizer chain) | ACTIVE | 1–3 | ~150–300 | `iterated_mateEquiv_conjugateEquiv` (Mates.lean, TwoSquare-valued); `TensorProduct.piRight`; `isLocalization_basicOpen_of_qcqs` (01XJ core, present) | Frontier `ring_square_glue_natTrans`+fold: nat-trans-level whnf could recur (decisive STUCK test). Downstream seeds/01XJ/assembly are independent → MUST parallel-dispatch. |
| SNAP — `Γ_*(X,L)` graded comm ring (Option A: re-base structural defs on `⊗_loc`) | ACTIVE | 1–3 (or escalate) | ~120–300 (net DEL ~900L) | `Localization.Monoidal` (`LocalizedMonoidal`/`toMonoidalCategory`/`L.Monoidal`, all present); `DirectSum.GCommSemiring`/`Gmodule` | Option-A refactor 0-edit-timed-out ×3 (now mitigated by file split). Section coherences may re-summon the μ-boundary one layer down → delete-after-confirm. 4th timeout ⇒ user escalation. |

Both routes are ~4–5× over their original iter estimates (FBC entered ~iter-003, SNAP ~iter-008); the
estimates above are the post-unblock remaining figures, conditional on the frontier tests passing.

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---|---|---|---|---|---|
| FBC RegroupHelper | 011 · 4 | ~120 | RegroupHelper.lean | `regroupEquiv` `(A⊗_R R')⊗_A M ≅ R'⊗_R M` axiom-clean | `eT` identity-bridge + `TensorProduct.induction_on` to beat transparent-instance diamonds | `map_smul'` zero-branch needs `erw [TensorProduct.zero_tmul]` |
| SNAP coequalizer rows | 060 · 3 | ~400 | SectionGradedRing.lean | `relTensorActL/R/Proj` objectwise coequalizer; `RelativeTensorCoequalizer` 22-decl API | carrier gap fixed by `objRestrict`; `relTensorProj.naturality` = bare-ℤ `TensorProduct.ext'` then transport to `AddCommGrpCat` | `forget₂ CommRing→Ring` carrier "blocker" illusory — real obstacle was additivity |
| SNAP crux chain + graded bricks + left-unit | 002 · ~2 | ~720 | SectionGradedRing.lean | `ztensor_whisker_localIso`, `isIso_sheafification_whiskerRight_unit`, `tensorObjAssoc`, `tensorPowAdd`; graded bricks; `sectionsMul_one_mul` | sheafification-functoriality of presheaf monoidal isos; `sectionsCast`; `adj.homEquiv` transpose core; `show`/`change` to split `Γ(f≫g)` across the `X.Modules` diamond | stalkwise / full `MonoidalCategory(SheafOfModules)` routes DEAD; carrier `AddCommGrpCat` |
| FBC module core + concrete pivot | 002 · 2 | ~500 | FlatBaseChangeGlobal.lean | `gammaTopEquivEqLocus`, `baseChangeGammaEquiv`, finite-cover equalizer; pivot off mate → concrete-tilde | `H⁰(X,F)=Γ(X,F)` = finite equalizer; flat `−⊗B` preserves it (`tensorEqLocusEquiv`) | sheaf-level adjoint-mate keystone abandoned (compile-dead) |
| FBC foundation + both mate legs + glue scaffold | 016–024 · ~8 | ~400 | FlatBaseChange.lean | `gammaPushforwardNatIso_comp`; both b2 mate legs; 5/6 `ring_square_glue_*`; geom leg made syntactic | `← conjugateEquiv_comp` split ×2 + `simp[…eq_mpr_eq_cast,cast_eq]` cast-dissolve; redefine obj-def as `…Nat.app(tilde M)` to make a defeq leg syntactic | sheaf-level `.app/.obj (tilde M)` folds = sheafification-whnf kernel bomb (any tactic); morphism-level routes only |

## Routes

Single route per leg; the two legs are independent and merge back upstream.

**FBC route — concrete-tilde equalizer chain (Čech-free).** Both seeds are reached WITHOUT the
adjoint-mate keystone. `H⁰(X,F)=Γ(X,F)` is the finite equalizer `∏Γ(Uᵢ,F) ⇉ ∏Γ(Uᵢⱼ,F)` over a finite
affine cover of a separated qc scheme, and flat `−⊗B` preserves it. Module core DONE 0-sorry
(`FlatBaseChangeGlobal.lean`). The frontier `baseChange_sheafConditionFork_tensorIso` decomposes into
per-chart iso (01I9 + Mathlib `cancelBaseChange`), the crux restriction-naturality glue (project-built,
axiom-clean), and `TensorProduct.piRight` (Mathlib). Assembly climbs separated → Mayer–Vietoris →
bridge `flatBaseChange_isIso_iff_gammaTensorComparison` → goal. The sheaf-level adjoint-MATE apparatus
(`base_change_mate_*`, `pushforward_base_change_mate_*`) is 100% COMPILE-DEAD and deletable in a
dedicated cleanup iter (KEEP `base_change_mate_regroupEquiv`, `base_change_map_affine_local`); the seeds
keep clean `sorry` stubs until the concrete chain fills them.

**SNAP route — sheaf tensor powers ⟹ graded ring, coherence by monoidal localization (Option A).**
`Γ_*(X,L)` is the direct sum of section groups of `L^{⊗n}`, multiplication from the lax-monoidal section
pairing `sectionsMul` + the `tensorPowAdd` index-addition isos; the graded structure rides
`DirectSum.GCommSemiring`. Mathlib's `Localization.Monoidal` builds a full symmetric `MonoidalCategory`
(pentagon/triangle/hexagon) on `LocalizedMonoidal L W ε` (`= modulesLocalizedMonoidal X`), with
`L = sheafification`, `W.IsMonoidal` from the proved `ztensor_whisker_localIso`. **Option A:** re-base
the structural defs DIRECTLY onto `⊗_loc` (`tensorObj := MonoidalCategory.tensorObj (C :=
modulesLocalizedMonoidal X)`, similarly unitor/braiding/associator). Synonym defeq + unit IS `unitModule X`
(via ε) ⇒ object spellings unchanged ⇒ `tensorObjAssoc_eq_localizedAssociator` etc. become `rfl` — the
stuck crux is DELETED, not proved. μ then lives only opaque in `sectionsMul`/`tensorObjLocalizedIso`
(`Iso.refl`). Downstream coherences re-prove from the Mathlib monoidal laws + `Functor.Monoidal L` lax
fields. Option B (bridge the hand-built product to `⊗_loc` via the μ-conjugated iso) is ABANDONED — its
bridge `tensorObjAssoc_eq_localizedAssociator` STUCK ~10 iters on dual-instance μ-token-divergence. Both
monoidal instances KEPT (the presheaf `pshModMonoidal` is load-bearing; deletion refuted). Design:
`analogies/snap-instance-design.md`.

## Open strategic questions

- **SNAP Option A — does the μ-boundary reappear in the section-level coherences?** The structural
  coherences are now `rfl` inside `⊗_loc`. Risk: `sectionsMul_*` / `sectionMul_coherent` may relate an
  `⊗_loc` coherence to the section structure across the defeq-not-syntactic boundary → wall one layer
  down. MITIGATION (sc024): DELETE-AFTER-CONFIRM — keep the μ-keystones until the section coherences
  re-prove green from the lax fields; only then delete the ~900L. Cheap signal = a stubborn post-refactor
  sorry resisting the law-based re-prove → re-consult the analogist.
- **FBC qcqs-pushforward-QC (Stacks 01XJ) — sub-prerequisite CONFIRMED PRESENT; build = assembly only.**
  The hard analytic core `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` IS in Mathlib
  (`…Morphisms.QuasiSeparated`, verified sc024). Only the QC-preservation-under-pushforward packaging is
  project-side (`[prover-mode: mathlib-build]`, ~100–200 LOC). No longer "UNCONFIRMED".
- **FBC chain signatures.** Scaffolded chain decls (`baseChange_sheafConditionFork_tensorIso`,
  `baseChangeEqLocusToPullbackGamma`, `baseChangeGammaPullbackEquiv`) omit
  `[IsSeparated X]`/finiteness/`[F.IsQuasicoherent]`; add (re-sign freely, not protected) when sorries fill.
- **FBC parallelism (sc024 must-fix).** The downstream seeds, the 01XJ build, and the global assembly are
  mutually independent — dispatch concurrently to hit the 1–3-iter estimate; serialized expect ~2×.

## Mathlib gaps & new material

Gaps to fill:
- FBC: `pullback_spec_tilde_iso_restriction_naturality` (concrete localization functoriality; project-built
  axiom-clean). Affine cancellation = Mathlib `cancelBaseChange` (or project `regroupEquiv`, DONE).
  `TensorProduct.piRight` present. 01XJ packaging = assembly over `isLocalization_basicOpen_of_qcqs`.
- SNAP coherence (Option A): re-base `tensorObj`/unitor/braiding/associator onto `⊗_loc` (bridges `rfl`);
  downstream coherences from Mathlib monoidal laws + `Functor.Monoidal L` lax fields.

New project material:
- FBC concrete chain (per-chart iso + restriction naturality + finite-product commutation + assembly).
- SNAP tensor-power coherences + the `Γ_*(X,L)` graded (co)semiring/module instances.
