# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the seed declarations + kernel-only axioms.**
Two Čech-independent (i=0) legs split from the parent *Quot-Foundations* `thm:fga_pic_representability`
cone (full arc in STRATEGY.md):

- **FBC-B** — flat base change of the degree-0 pushforward (`thm:flat_base_change_pushforward`), via the
  CONCRETE-tilde equalizer chain. FOUNDATION SORRY-FREE (iter-016). **iter-018: BOTH ring-square mate legs
  CLOSED** (geometric + algebraic, axiom-clean). CONVERGING (pc019). Frontier = the glue
  `pullback_spec_tilde_iso_ring_square_mate_glue` (pure iterated-mate assembly; both dependency legs live),
  then crux rewire + 2 seeds.
- **SNAP** — the section graded ring `Γ_*(X,L)` (`lem:sectionGradedRing_gcommSemiring`). Foundation +
  bridges + 4 seams + 2 keystones + `hK_rhs` + head + (iter-018) `native` DONE. `native` BROKE the 7-iter
  reassoc wall; the chain runs bomb-free to the head lemma. **STUCK (pc019, 4 PARTIAL / 0 net elim):**
  residual = applying the proven head lemma over the full-`tail` goal whnf-bombs (heavy μ in `tail`).
  iter-019 = the analogist-validated SUFFIX-REMOVAL route (last automated attempt before a refactor pivot).

## Current Objectives

TWO prover lanes, independent files → parallel.

1. **`Picard/SectionGradedRing.lean`** — close `tensorObjAssoc_hK_lhs_native` (~L2058) then `hK_lhs`
   (~L2127) via the SUFFIX-REMOVAL route. Blueprint: `chapters/Picard_SectionGradedRing.tex`
   (`lem:tensorObjAssoc_hK_lhs_native`, `lem:tensorObjAssoc_hK_lhs_head` DONE, `lem:tensorObjAssoc_hK_lhs`).
   Recipe: **`analogies/snap-suffix-cancel.md`** (analogist `snap-suffix-cancel`, PROCEED). [prover-mode: prove]
   - **CONTEXT (pc019: STUCK route — this is the LAST automated attempt).** iter-018's `native` lemma runs
     the full reassoc→associator-expand→whisker-merge→μ-cancel chain bomb-free down to the goal
     `μ.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{a⊗ₚb,c}.hom ≫ tail = s1.inv ≫ tail`, where the 3-factor prefix is
     EXACTLY the proven head lemma `tensorObjAssoc_hK_lhs_head A B C : (prefix) = s1.inv`. The ONLY
     remaining step — applying head — whnf-bombs because the goal still carries the heavy `tail`
     (multiple `Localization.Monoidal.μ`). DO NOT retry any full-goal op on the concrete goal
     (`rw [head]`/`erw`/`simp only [head]`/`rw [reassoc_of% head]`/`conv … rw`/`refine (h2 _).trans` — ALL
     VERIFIED-DEAD iter-018).
   - **THE FIX — remove the heavy suffix BEFORE applying head (analogist-validated, PROCEED):**
     - **PRIMARY:** put `@[reassoc]` on `tensorObjAssoc_hK_lhs_head` (auto-generates the suffixed sibling
       `…_head_assoc {Z'} (g) : prefix ≫ g = s1.inv ≫ g` with `Category.assoc` baked in). Then in `native`,
       after `conv_rhs => rw [assocCommonForm]; simp only [sheafification, toMonoidalCategory]` exposes the
       RHS as `s1.inv ≫ tail` (prover-confirmed bomb-free), close with
       `exact tensorObjAssoc_hK_lhs_head_assoc A B C` (the `?g` metavar binds `tail` by structural ≫-match,
       so `tail` is never whnf'd). If `@[reassoc]`'s generated decl shows in `unmatched`, instead define a
       `private` sibling `_head_assoc := by rw [reassoc_of% tensorObjAssoc_hK_lhs_head]` (or `:= reassoc_of%
       …`) so it leaves the scan.
     - **FALLBACK** (if structural ≫-match still trips the instance): `generalize hT : tail = t` (after the
       `conv_rhs` alignment so `tail` is token-identical on both sides — the load-bearing guard), VERIFY both
       sides now show `t`, then `exact reassoc_of% tensorObjAssoc_hK_lhs_head A B C` (or `rw [reassoc_of% …]`).
     - **PREFIX RESIDUAL:** the analogist flags that suffix-removal is NECESSARY-not-sufficient — once `tail`
       is gone, the prefix μ's (head-lemma spelling vs goal spelling) may still need the head lemma's own
       `show`-to-uniform-localized recast on the now-tail-free prefix before `exact`. Apply it if the
       prefix unification bombs.
   - **Then `hK_lhs`** (~L2127): `simp only [tensorObj]` (unfold once) + `exact tensorObjAssoc_hK_lhs_native
     A B C`. If THAT `exact` still bombs on the full term, apply the SAME suffix-removal idiom to the
     `hK_lhs`↔`native` connection (it is the same prefix/tail shape).
   - **If `hK_lhs` closes** → assembly `tensorObjAssoc_eq_localizedAssociator` (~L2115) closes transitively.
   - **NET-PROGRESS FALLBACK (this is a STUCK lane — extract progress regardless of hK_lhs):** whether or
     not the suffix route lands, spend remaining budget on the leandag-READY independent bridge
     `tensorObjUnitor_eq_localized` (~blueprint L1883; a UNITOR bridge via `leftUnitor_hom_app`, structurally
     simpler than the associator and NOT gated on hK_lhs) and then the cascade coherences
     (`tensorPowAdd_*`/`sectionsMul_mul_assoc`/`sectionMul_coherent`). Reuse KB idioms (`show`-to-uniform +
     `simp [tensorHom_comp_tensorHom]` (NOT rw) + counit-triangle + statement-level `(C := MonoidalPresheaf
     X)` pinning + the NEW suffix-removal idiom where a heavy-μ tail blocks a prefix-equality application).
     Leave a typed sorry on any that doesn't yield — do not thrash.
   - **GUARD:** do NOT re-sign `assocCommonForm` (risks the CLOSED `hK_rhs`).
   - **MANDATORY:** validate with cold `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP HIDES
     `(kernel) deterministic timeout`). Do NOT add `maxHeartbeats 1e6`. Revert any bombing close to a clean
     stub; the file MUST end green.

2. **`Cohomology/FlatBaseChange.lean`** — assemble the glue, then rewire the crux + seeds. Blueprint:
   `chapters/Cohomology_FlatBaseChange.tex` (`lem:pullback_spec_tilde_iso_ring_square_mate_glue`; both
   leg lemmas `lem:chartBaseChangeGeometricComparison_mate`,
   `lem:chartBaseChangeModuleReassoc_extendScalarsComp` CLOSED iter-018). [prover-mode: prove]
   - **GLUE `pullback_spec_tilde_iso_ring_square_mate_glue`** (~L1760) — both dependency legs are now live,
     so this is the iterated-mate ASSEMBLY: transpose the M-component iso equation through
     `iterated_mateEquiv_conjugateEquiv` (`_symm`) + the per-leg unit triangle
     `pullback_spec_tilde_iso_inv_unit_triangle` (@L897) + `gammaPushforwardNatIso_comp`, combining the
     geometric leg `chartBaseChangeGeometricComparison_mate` + algebraic leg
     `chartBaseChangeModuleReassoc_extendScalarsComp`. HAZARD (documented): `iterated_mateEquiv_conjugateEquiv`
     is `TwoSquare`-valued (whiskerings are TwoSquare pasting, NOT `Functor.whiskerLeft`); naive use forces
     the composite-adjunction unit to whnf → 200k-hb bomb. MIRROR the leg engine: drive by the CLOSED
     coherences + `← conjugateEquiv_comp` splits with explicit midpoints, NEVER `unit_conjugateEquiv` over a
     composite. If the TwoSquare transposition bombs, leave the typed sorry and report the exact blocked step
     (do NOT thrash).
   - **VERIFY before building** (Mathlib bumps): `loogle`/`local_search` `iterated_mateEquiv_conjugateEquiv`,
     `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_conjugateEquiv_vcomp` (KB: all REAL in `…Adjunction.Mates`).
     If a name mismatches, STOP + surface — do NOT thrash.
   - **If the glue lands** → rewire the crux body `pullback_spec_tilde_iso_ring_square_natural` to
     `exact … mate_glue …`; then attempt the 2 downstream seeds (`affineBaseChange_pushforward_iso` @L1875,
     `flatBaseChange_pushforward_isIso` @L1897) via the concrete chain — leave typed sorry if not ready.
   - **MANDATORY cold-build self-check + revert-on-bomb:** after each close run cold `lake build
     AlgebraicJacobian.Cohomology.FlatBaseChange`. If it bombs → REVERT to the clean stub-sorry. The file
     MUST end green. Do NOT touch the COMPILE-DEAD mate sorries (@L1694/L1875/L1897 apparatus); no
     `set_option`/comment cleanup (deferred to the mate-excision refactor). Do NOT add `maxHeartbeats 1e6`.

## Queued — NEXT iters

- **SNAP refactor pivot (iter-020, CONDITIONAL — fires ONLY if the iter-019 suffix route bombs):** glue
  Option A — rewire the hand-built `tensorObj*` defs onto the `LocalizedMonoidal X` synonym `⊗` so the
  bridges (`tensorObjLocalizedIso` et al.) become DEFINITIONAL and the comp-instance boundary disappears.
  Dispatch the `refactor` subagent (directive to `logs/iter-020/refactor-snap-…-directive.md`); sync the
  blueprint the same iter. This is the autonomous dead-end response (standing directive: no user escalation).
  Dual-instance DELETION stays REFUTED (load-bearing).
- **FBC downstream (after glue + crux):** rewire crux → seeds → Global assembly
  `baseChange_sheafConditionFork_tensorIso` (+ `TensorProduct.piRight`; add
  `[IsSeparated X]`/`[Fintype ι]`/`[F.IsQuasicoherent]`) → separated → MV → bridge → goal (bridge reverse
  gated on Stacks 01XJ — verify Mathlib / `mathlib-build` first, STRATEGY Open Q).
- **SNAP cascade coherences + `sectionGradedModule_gmodule`** — after `hK_lhs` + assembly close.
- **FBC mate excision + cleanup (dedicated `refactor` iter):** delete the COMPILE-DEAD mate apparatus +
  dead `/-!` blocks; FIX the latent `set_option maxHeartbeats` placement bug (scopes to comments not
  theorems); strip stale iter-NNN comments. KEEP `base_change_mate_regroupEquiv` +
  `base_change_map_affine_local`. Sync blueprint `\uses` same iter. (Auditor: FBC L1957-1960 orphan
  `maxHeartbeats`, L2000-2104 104-line scaffold; SNAP L2148-2278 ~130-line dead scaffold.)
- **SNAP file-split + coverage-debt clear** — `SectionGradedRing.lean` >2200 lines, ~70 unmatched
  `RelativeTensorCoequalizer.*`/`W_*` helpers. Split into smaller files (user standing directive:
  parallelism) + mark impl-detail helpers `private` + blueprint genuine infra. Dedicated `refactor` iter.

## Standing notes

- **Prover model:** `opus`.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf. FlatBaseChangeGlobal imports
  FlatBaseChange (one-way); FlatBaseChange imports RegroupHelper. SectionGradedRing standalone.
- **Cold-build is the ONLY kernel-bomb detector:** validate with real `lake build
  AlgebraicJacobian.Cohomology.FlatBaseChange` / `...Picard.SectionGradedRing`. The LSP / `lean_multi_attempt`
  HIDE `(kernel) deterministic timeout`. Never add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **SNAP localized↔X.Modules μ-boundary (KB):** the comp boundary is defeq-not-syntactic. (1) Object-phrasing
  discipline: a folded `tensorObj` inside a μ-object bombs every reassoc/`associator_*`/`Category.assoc`
  → state the step with μ-objects in unfolded `(L').obj _` form. (2) μ-pair cancel/merge fires via `erw`
  ONLY when ISOLATED (slice/`have`/`conv`); full-goal `rw`/`simp` whnf-bombs. (3) NEW (iter-019): applying a
  proven prefix-equality over a goal carrying a heavy μ-`tail` whnf-bombs → REMOVE the suffix first
  (`@[reassoc]`/`generalize`). Recipes: `analogies/snap-suffix-cancel.md`, `snap-reassoc-pin.md`,
  `snap-mu-identity.md`, `snap-assoc-expose.md`, `snap-localized-comp-cancel.md`.
- **FBC mate API (KB):** GEOMETRIC per-piece mate `conjugateEquiv_pullbackComp_inv` REAL (Sheaf.lean:238,
  `@[simp]`); ALGEBRAIC engine `conjugateEquiv_extendScalarsComp`+`natTrans_ext_of_unit` (DONE). Both legs
  CLOSED iter-018 via `← conjugateEquiv_comp` split ×2 + `simp only […eq_mpr_eq_cast,cast_eq]` cast-dissolve.
  Drive composites by `conjugateEquiv_comp` splits, NEVER `unit_conjugateEquiv` over the composite (whnf
  bomb). `iterated_mateEquiv_conjugateEquiv` (for the glue) is TwoSquare-valued.
- **Merge-back discipline:** never rename kept decls/labels; never add `\leanok` by hand. No declarations
  are currently protected — chain decls may be re-signed to add missing hyps / pin instances.
