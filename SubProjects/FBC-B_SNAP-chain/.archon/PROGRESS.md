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
  CONCRETE-tilde equalizer chain. Per-chart iso (a) DONE sorry-free; restriction-naturality (b) reduced
  to its crux `pullback_spec_tilde_iso_ring_square_natural`, gated on the foundation
  `gammaPushforwardNatIso_comp` (own body CLOSED iter-011). Residual = `gammaPushforwardIso_comp` (@L743).
  **iter-014:** element/sheaf-element family VERIFIED-EXHAUSTED (kernel bomb is the RHS reduction across
  the value-`ModuleCat`/`X.Modules` junction, NOT the cast). **iter-015:** MORPHISM-LEVEL route
  (analogist-found, gate-cleared bp015): prove `_comp` as a morphism equality (RHS = `map_comp` law),
  single junction crossing + proof-irrelevance closer — NEVER element-wise. Refactor fallback queued.
- **SNAP** — the section graded ring `Γ_*(X,L)` (`lem:sectionGradedRing_gcommSemiring`). Foundation +
  bridges + `sectionMul_assoc_core` + 4 seams + 2 keystones DONE. Assembly
  `tensorObjAssoc_eq_localizedAssociator = hK_lhs.trans hK_rhs.symm` (sorry-free body); **`hK_rhs` CLOSED
  iter-014** (cold-build green). Residual = `hK_lhs` (@L1919). **iter-015:** mechanize the analogist-
  VALIDATED (cold-LSP) exposure recipe (`analogies/snap-assoc-expose.md`); closing it closes the assembly.

## Current Objectives

TWO prover lanes, independent files → parallel. iter-015 is the pre-committed escalation iter: BOTH
correctives were SUBAGENT consults (not warm prover retries), and BOTH returned actionable recipes that
are now blueprint-gate-cleared (bp015 complete+correct on both patched chapters). SNAP's recipe is
cold-LSP-VALIDATED; FBC's is a genuinely NEW (morphism-level) family — the exhausted element family is
abandoned. pc015: SNAP CHURNING-transitional (corrective genuine), FBC STUCK (morphism route is the
structural pivot, not a retry).

1. **`Picard/SectionGradedRing.lean`** — mechanize the VALIDATED `hK_lhs` exposure recipe.
   Blueprint: `chapters/Picard_SectionGradedRing.tex` (`lem:tensorObjAssoc_hK_lhs`, rewritten + cleared
   bp015). Recipe: `analogies/snap-assoc-expose.md` (cold-LSP-validated, verbatim). [prover-mode: fine-grained]
   - **`tensorObjAssoc_eq_localizedAssociator_hK_lhs` (sorry @L1919):** after the existing
     `rw [assocCommonForm]; simp only [tensorObjLocalizedIso, …]` (@L1892–1894):
     - **Step 0 (MANDATORY FIRST):** re-elaborate the LHS uniformly in the `modulesLocalizedMonoidal X`
       comp via the SAME `show`-to-uniform template that landed `hK_rhs` (@L1999–2026) — every `≫` must
       become `CategoryStruct.comp (modulesLocalizedMonoidal X)`. Until then the interchange laws NO-MATCH
       (the outer `≫` is the `X.Modules` comp). `change`/`dsimp` across the boundary stay DEAD — use `show`.
     - **Step 1:** `rw [← Localization.Monoidal.tensorHom_id]` (fires — whiskering is instance-agnostic),
       then `← tensor_comp` merge + re-split to expose `((c_A⊗ₘc_B)⊗ₘc_C)`.
     - **Step 2:** `rw [Localization.Monoidal.associator_naturality (c_A).hom (c_B).hom (c_C).hom]`
       [verified Basic.lean L286] — native-ises `α_ A B C → α_ (L'A♭)(L'B♭)(L'C♭)`. (The iter-014 plan to
       "relate `c_{A⊗B}` to `μ_{A,B}`" was MIS-FRAMED/not-well-typed — `c_{A⊗B}` stays WHOLE.)
     - **Step 3:** `rw [Localization.Monoidal.associator_hom_app]` [verified L234] expands the native α.
     - **Step 4:** `simp only [← whiskerRight_comp, Iso.inv_hom_id]` cancels the `μ_{A♭,B♭}` pair on the
       `▷ L'C♭` slot, leaving `c_{A⊗B} ▷ L'C♭` whole.
     - **Step 5 (the only non-routine step — prove as a `have hHead`):**
       `μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom = (L'(η_{A♭⊗B♭} ▷ C♭))⁻¹`, via
       `μ_natural_left _ _ _ η_{A♭⊗B♭} C♭` [verified L188] + the adjunction triangle
       `(sheafificationAdjunction _).left_triangle_components (A♭⊗B♭)` (gives `c_{A⊗B}=(L'η)⁻¹`) + cancel
       `μ⁻¹≫μ`. Then `rw [hHead]`; the tail (from `L'(α^p)`) already coincides with `K`. ∎
   - **Object-arg align:** in `μ_natural_left`'s output the μ first-objects print as `(L'⋙forget⋙restrict).obj _`
     / `(𝟭 _).obj _` — defeq to the goal's forms; align with the `Functor.id_obj` simp already at L1742/L1766.
   - **Assembly** `tensorObjAssoc_eq_localizedAssociator` (@L2044) is already `= hK_lhs.trans hK_rhs.symm`
     (sorry-free); closing `hK_lhs` closes it. Do NOT touch the 5 cascade coherences yet (next iter).
   - Validate with cold `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP hides kernel
     timeouts). Do NOT add `maxHeartbeats 1e6`.

2. **`Cohomology/FlatBaseChange.lean`** — MORPHISM-LEVEL close of `gammaPushforwardIso_comp`.
   Blueprint: `chapters/Cohomology_FlatBaseChange.tex` (`lem:gammaPushforwardIso_comp`, rewritten + cleared
   bp015). Recipe: `analogies/fbc-morphism-comp.md`. [prover-mode: prove]
   - **`gammaPushforwardIso_comp` (sorry @L776):** REPLACE the body — DELETE the `apply ModuleCat.hom_ext;
     refine LinearMap.ext fun x => ?_` descent (that descent IS the kernel-bomb entry point; the
     element/sheaf-element family is VERIFIED-EXHAUSTED). Prove the MORPHISM equality (goal shown in the
     analogy @L30; RHS is verbatim `PresheafOfModules.map_comp`). Steps:
     1. Normalise the codomain glue: `restrictScalarsComp φ.hom ρ.hom` → `restrictScalarsComp' φ.hom ρ.hom
        (ρ.hom.comp φ.hom) rfl` (defeq), then `rw [ModuleCat.restrictScalarsComp'_inv_app]`.
     2. **ADD** a `rfl` lemma `gammaPushforwardIso_hom_def` unfolding `(gammaPushforwardIso ψ N).hom` to its
        defining `restrictScalarsComp'App`/`restrictScalarsCongr` composite (single-layer rfl, green in
        isolation); `rw` it for `φ≫ρ`, `φ`, `ρ` — pure morphism rewrites, NO elements.
     3. Slide the middle `(restrictScalars φ.hom).map (gammaPushforwardIso ρ N).hom` leftward via
        `ModuleCat.restrictScalarsComp'App_hom_naturality_assoc` [expected — verify] / `_inv_naturality`.
     4. **ADD** a morphism-level bridge lemma crossing the junction EXACTLY ONCE:
        `moduleSpecΓFunctor.map ((eqToIso (Spec.map_comp φ ρ)).hom.app N ≫ pushforwardComp.inv.app N)
        = <explicit restrictScalars coherence morphism over Γ(N,⊤)>` (proof = the single junction rfl/short
        reduction — cold-build GREEN per iter-014). `rw` it; goal then has NO `moduleSpecΓFunctor.map`/`pushforward`.
     5. Close the residual `restrictScalarsCongr` endpoint mismatch by PROOF-IRRELEVANCE (`congr 1` /
        `Subsingleton.elim` on the `Prop` endpoint equalities; the equality content is
        `globalSectionsIso_hom_comp3_specMap_appTop`). NO `ext x`.
   - **MANDATORY self-check + revert-on-bomb:** after any close attempt, run cold `lake build
     AlgebraicJacobian.Cohomology.FlatBaseChange`. If `(kernel) deterministic timeout` → REVERT to the
     clean partial (LHS reduced + `sorry`, currently green) and report. NEVER commit a kernel-bomb term
     (the iter-013 regression). The 2 new helpers are kernel-light `rfl`s — they are safe.
   - Closing `gammaPushforwardIso_comp` closes the foundation `gammaPushforwardNatIso_comp` transitively
     (its body is `exact gammaPushforwardIso_comp φ ρ N`). If it closes AND budget remains, attempt the
     crux `pullback_spec_tilde_iso_ring_square_natural` (@~L1289) via the mate recipe
     (`analogies/fbc-pst-pseudofunctor.md`; `mateEquiv` TwoSquare-valued → `.natTrans`); typed `sorry` ok.
   - **Do NOT** touch the COMPILE-DEAD mate sorries; do NOT attempt set_option/comment cleanup (deferred
     to the dedicated mate-excision refactor iter). Do NOT add `maxHeartbeats 1e6`.

## Queued — NEXT iters

- **iter-016 escalation (pre-committed):** If SNAP `hK_lhs` stalls AGAIN despite the validated recipe →
  surface the exact failing step (do NOT warm-retry); the recipe is cold-LSP-validated so a stall implies
  a syntactic-shape mismatch worth a focused 3rd analogist on that step. If FBC morphism-level close
  kernel-bombs OR steps 3–5 prove syntactically fragile → execute the **junction-free refactor of
  `gammaPushforwardIso`** (`refactor` subagent, NOT a prover): reconstruct so the value/scheme junction is
  crossed once centrally (a `moduleSpecΓObjIso` natural iso, or package as the `map_comp` field of a
  presheaf-of-modules / restrictScalars-pseudofunctor structure) so `_comp` + future coherences are
  `cat_disch`-cheap. analogist also flagged `analogies/fbc-pst-pseudofunctor.md` mis-records this coherence
  cost as "pointwise rfl" — correct it when the refactor lands.
- **SNAP cascade + `sectionGradedModule_gmodule`** — once the assembly closes, the 5 coherences
  (`tensorPowAdd_rightUnit/_braiding/_assoc×2`, `sectionsMul_mul_assoc`) cascade; all reuse the REUSABLE
  `show`-to-uniform-localized-form + `simp [tensorHom_comp_tensorHom]` (NOT rw) + counit-triangle unblock
  (KB, promoted iter-014). Gate-confirm each block + the 2 unitor bridges' `\lean{}` names when activating.
- **FBC crux → Global assembly** `baseChange_sheafConditionFork_tensorIso`: after the crux +
  `TensorProduct.piRight`; add `[IsSeparated X]`/`[Fintype ι]`/`[F.IsQuasicoherent]` hyps.
- **FBC separated → MV → bridge → goal**: both seeds. Bridge reverse gated on qcqs-pushforward-QC
  (Stacks 01XJ) — verify Mathlib / `mathlib-build` first (STRATEGY Open Q).
- **FBC mate excision + cleanup (dedicated `refactor` iter)** — delete the COMPILE-DEAD mate apparatus +
  dead `/-!` blocks; FIX the latent `set_option maxHeartbeats` placement bug (scopes to comments not
  theorems); strip stale comments. KEEP `base_change_mate_regroupEquiv` + `base_change_map_affine_local`.
  Sync the blueprint `\uses` same iter. Run via `refactor`, NOT alongside a prover.
- **SNAP file-split + coverage-debt clear** — `SectionGradedRing.lean` >2200 lines with ~70 unmatched
  Lean helpers (mostly `RelativeTensorCoequalizer.*`). Split into smaller files (user standing directive:
  parallelism) + mark impl-detail helpers `private` + blueprint genuine infra. Dedicated `refactor` iter.
  (Also blueprint the 2 new FBC helpers `gammaPushforwardIso_hom_def` + the junction bridge once named.)

## Standing notes

- **Prover model:** `opus`.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf. FlatBaseChangeGlobal imports
  FlatBaseChange (one-way); FlatBaseChange imports RegroupHelper. SectionGradedRing standalone.
- **Cold-build is the ONLY kernel-bomb detector:** validate with real `lake build
  AlgebraicJacobian.Cohomology.FlatBaseChange` / `...Picard.SectionGradedRing`. The LSP / `lean_multi_attempt`
  HIDE `(kernel) deterministic timeout`. Never add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **SNAP localized-comp boundary (analogist-VALIDATED):** the `LocalizedMonoidal`↔`X.Modules` comp boundary
  is defeq-not-syntactic. hK_rhs μ-cancel (`analogies/snap-localized-comp-cancel.md`): `erw [assoc];
  congrArg leading-μ.inv peel; erw [assoc, Iso.hom_inv_id_assoc]`. hK_lhs exposure
  (`analogies/snap-assoc-expose.md`): Step-0 `show`-to-uniform FIRST, then `associator_naturality` →
  `associator_hom_app` → μ-cancel → `μ_natural_left` + `left_triangle_components` head reduction.
- **FBC element family EXHAUSTED (iter-014, cold-build-verified):** the bomb is the RHS-composite REDUCTION
  across the value-`ModuleCat`/`X.Modules` junction (compounds past the kernel limit), NOT the residual
  cast. ANY `ext`/element descent re-crosses the junction per-wrapper → bomb. Morphism-level (cross once)
  is the only route; junction-free refactor is the structural fix (`analogies/fbc-morphism-comp.md`).
- **Merge-back discipline:** never rename kept decls/labels; never add `\leanok` by hand. No declarations
  are currently protected — chain decls may be re-signed to add missing hyps.
