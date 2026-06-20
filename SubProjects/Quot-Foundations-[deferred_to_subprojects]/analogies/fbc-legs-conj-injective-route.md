# Analogy: how does Mathlib prove a multi-functor mate/conjugate coherence — `.injective`+conjugate-dictionary, or element-`ext`?

## Mode
api-alignment

## Slug
fbc-fork

## Iteration
040

## Question
For `base_change_mate_fstar_reindex_legs_conj` (`_legs_conj`), which Mathlib idiom should we align
to: **Fallback A** (element/component `ext` + a change-of-rings dictionary of per-leg rewrites) or
**Fallback B** (restructure so the section-level composite IS a `conjugateEquiv`/`leftAdjointCompIso`
value, so `conjugateEquiv.injective` applies without a reframing step)? Is there a third idiom?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:1757-1822` — `_legs_conj`, the open `sorry`.
- `…:1625-1635` — conj-2b `base_change_mate_reindex_conj_pullbackLeg` (already = `conjugateEquiv_leftAdjointCompIso_inv`).
- `…:1652-1724` — conj-2d `base_change_mate_reindex_conj_crossLayer` (already via `unit_conjugateEquiv_symm` on `adjL`/`adjR`).
- `…:1736-1747` — conj-2c `base_change_mate_reindex_conj_pushforwardCollapse` (the three Γ-collapses).
- `…:1181-1205` — conj-0/0′ `pullbackComp_(inv_)eq_leftAdjointCompIso(_inv)`.
- `…:1563-1588` — conj-1a `base_change_mate_codomain_read_legs_conj`.

## Decisions identified

### Decision: composite mate coherence — `.injective`+conjugate-dictionary vs element-`ext`

- **Mathlib idiom**: Mathlib proves multi-functor coherences between left-adjoint composites by
  **never leaving the conjugate calculus**: it BUILDS each comparison as a conjugate value and then
  closes coherences by `obtain …surjective; apply conjugateEquiv.injective; simp/rw [conjugate
  push-through dictionary]`. The push-through dictionary is `conjugateEquiv_comp`
  (`Mathlib/CategoryTheory/Adjunction/Mates.lean:337`, `@[reassoc (attr := simp)]`),
  `conjugateEquiv_whiskerLeft`/`_whiskerRight` (`Mates.lean:525`/`536`),
  `conjugateEquiv_associator_hom` (`Mates.lean:501`), `unit_conjugateEquiv_symm` (`Mates.lean:305`),
  and `conjugateEquiv_leftAdjointCompIso_inv` (`CompositionIso.lean:82`). The exemplars of the route
  are `leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm` (`CompositionIso.lean:130`),
  `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` (`:140`), `leftAdjointCompNatTrans_assoc`
  (`:155`), and `leftAdjointCompIso_assoc` (`:168`):

  ```
  -- CompositionIso.lean:130-138  (the 3-functor associativity-flavoured coherence)
  obtain ⟨τ₁₂₃, rfl⟩ := (conjugateEquiv adj₁₃ (adj₁₂.comp adj₂₃)).surjective τ₁₂₃
  obtain ⟨τ₀₁₃, rfl⟩ := (conjugateEquiv adj₀₃ (adj₀₁.comp adj₁₃)).surjective τ₀₁₃
  apply (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).injective
  simp [leftAdjointCompNatTrans, ← conjugateEquiv_whiskerLeft _ _ adj₀₁]
  ```
  `apply injective` works *because* both sides, after `simp [leftAdjointCompNatTrans]`, are
  `(conjugateEquiv ..).symm (…)` values — `Equiv.apply_symm_apply` collapses them and the goal
  becomes an equation on the right-adjoint (here pushforward/Γ) side, which the dictionary closes.

  Element-`ext` IS used in Mathlib — but **only to prove the ATOMIC dictionary leaves**
  (`conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft/Right`, `unit_conjugateEquiv`,
  `conjugateEquiv_associator_hom` are each `ext X; simp` over a SINGLE adjunction pair, where
  unit/counit naturality + the triangle identities give a normal form). It is **never** used on the
  multi-pair composite. That is precisely the distinction the project missed.

  The directly-analogous precedent for the project's objects:
  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean` *defines*
  `PresheafOfModules.pullbackComp := Adjunction.leftAdjointCompIso … (pushforward coherence)`
  (`Pullback.lean:131-134`) and proves every pseudofunctor law by handing the obvious pushforward
  law to the matching `leftAdjointCompIso_*`:
  `pullback_assoc := leftAdjointCompIso_assoc … (pushforward_assoc …)` (`:142-147`),
  `pullback_id_comp := leftAdjointCompIso_id_comp …` (`:151-154`),
  `pullback_comp_id := leftAdjointCompIso_comp_id …` (`:156-159`). Zero element-`ext`, zero
  hand-rolled composite normalisation. This is the scheme-Modules ↔ presheaf-of-modules mirror of
  exactly the project's `pullbackComp`/`pushforwardComp` situation, and conj-0′
  (`pullbackComp_eq_leftAdjointCompIso`) already establishes the bridge.

- **Project's current path (intended)**: recognise the *whole* raw section-level composite as one
  `conjugateEquiv` value and `apply .injective` in one shot. Failed 3 iters because the composite is
  syntactically a mix of `gammaPushforwardTildeIso.inv`, `Γ.map(unit ≫ pushforwardComp ≫
  pushforwardCongr ≫ pushforwardComp.inv)`, `gammaPushforwardIso`, `restrictScalars.mapIso` —
  factors living in THREE different adjunction pairs (`tilde⊣Γ`, `pullback⊣pushforward`,
  `extend⊣restrict`) glued by section functors, so it is not literally `conjugateEquiv (…)`.

- **Project's Fallback A**: element-`ext` on that composite + a change-of-rings dictionary. At
  iter-035 (`FlatBaseChange.lean:2097`) a bare element-`ext` produced NO normal form — bottoming out
  at the cross-layer naturality of `gammaPushforwardIso` under the `X.Modules` instance diamond.

- **Gap**: Fallback A = **divergent-and-wrong** (element-`ext` on the composite is exactly the
  iter-035 dead end; Mathlib reserves `ext` for the atomic leaves only). Fallback B =
  **identical to the Mathlib idiom** once refined into the third idiom below.

- **Cost of divergence (Fallback A)**: a bespoke per-component change-of-rings simp set would have to
  re-derive, by hand and at the element level, the very `gammaPushforwardIso`-naturality that
  `unit_conjugateEquiv_symm` already gives conj-2d for free — i.e. re-prove conj-2d's content under
  the instance diamond, fighting the diamond at every `simp` step, and throw away the three
  axiom-clean legs (conj-2b/2c/2d) which are already STATED in conjugate (not component) form. That
  is unbounded bridge-lemma sprawl with no Mathlib backing.

- **Verdict**: ALIGN_WITH_MATHLIB (adopt Fallback B, executed via the third idiom).

### Decision: the third idiom — functor-layer-at-a-time conjugate transport (not a one-shot recognise)

- **Mathlib idiom**: do NOT recognise the whole composite as one conjugate value. Instead split it
  with `conjugateEquiv_comp`/`conjugateEquiv_symm_comp` (`Mates.lean:337`/`354`, both `reassoc`+`simp`)
  into a chain of single-pair conjugate factors, and discharge each factor by its push-through lemma —
  `conjugateEquiv_whiskerLeft`/`_whiskerRight` peel one functor layer at a time, exactly as
  `leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm` does with
  `simp […, ← conjugateEquiv_whiskerLeft _ _ adj₀₁]`. This is not a separate fallback; it is the
  engine that makes Fallback B's `.injective` actually close, and it is why conj-2d already builds
  `huce := unit_conjugateEquiv_symm adjL adjR β.hom N` rather than touching components.

- **Verdict**: ALIGN_WITH_MATHLIB — this is the concrete shape of Fallback B for the project.

## Recommendation

Adopt **Fallback B**, executed as the Mathlib **third idiom** (functor-layer-at-a-time conjugate
transport), and DROP Fallback A entirely. The codomain side is already conjugate-native (conj-1a),
and conj-0′ already proves `pullbackComp = leftAdjointCompIso (pushforwardComp)` — the same
definitional identity Mathlib's `Pullback.lean:131` uses. The remaining restructure mirrors
`leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` (`CompositionIso.lean:140`): express the
post-`subst` LHS mate composite as `(conjugateEquiv adjL adjR).symm (assembled β.hom)` — generalising
conj-2d's `huce` from the bare cross-layer factor to the full four-factor inner composite by
inserting the pullback leg (conj-2b) and the Γ-collapses (conj-2c) as additional conjugate factors
via `conjugateEquiv_symm_comp` — then `apply (conjugateEquiv adjL adjR).injective` (or
`Equiv.apply_eq_iff_eq`) and close with `simp` over the dictionary
`[conjugateEquiv_comp, conjugateEquiv_symm_comp, conjugateEquiv_whiskerLeft,
conjugateEquiv_whiskerRight, conjugateEquiv_leftAdjointCompIso_inv, unit_conjugateEquiv_symm]`
plus the three already-proved legs. **Concrete first proof step** (replacing the `ext`/one-shot
recognise): after `subst hfst; subst hsnd; rw [base_change_mate_codomain_read_legs_conj]`, introduce
`adjL`/`adjR` exactly as conj-2d does (`FlatBaseChange.lean:1667-1670`) and rewrite the goal's LHS
toward `(conjugateEquiv adjL adjR).symm …` using `conjugateEquiv_symm_comp` to split it — never
`ext x`, never positional `rw`/`simp`/`erw` under the `X.Modules` diamond.
