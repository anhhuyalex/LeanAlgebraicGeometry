# Analogy: transporting an adjunction's unit across a conjugate/mate (FBC Seam 1)

## Mode
api-alignment

## Slug
fbc-mate

## Iteration
014

## Question
What Mathlib idiom expresses "the conjugate (mate) of an adjunction's unit, under a pair of
comparison isomorphisms, is the other adjunction's unit", so that `comparison(geometric unit) =
algebraic unit` (Seam 1, `AlgebraicGeometry.base_change_mate_unit_value`) is a one-step
adjunction-calculus identity rather than an opaque element chase?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:689-696` — `pullback_spec_tilde_iso`, built as
  `(((conjugateIsoEquiv adjL adjR).symm (gammaPushforwardNatIso φ)).symm).app M`.
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:980-1010` — `base_change_mate_unit_value` (Seam 1),
  the open `sorry`.
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:667-673` — `gammaPushforwardNatIso` (the right-adjoint
  comparison nat-iso `β : R₁ ≅ R₂` fed to `conjugateIsoEquiv`).

## Decisions identified

### Decision: which Mathlib lemma transports the UNIT across the conjugate

- **Mathlib idiom**: `CategoryTheory.unit_conjugateEquiv` and its inverse
  `CategoryTheory.unit_conjugateEquiv_symm`, both in
  `Mathlib/CategoryTheory/Adjunction/Mates.lean` (the `section conjugateEquiv`, inside
  `namespace CategoryTheory open Adjunction`). Exact signatures at the pinned Mathlib:

  ```
  theorem CategoryTheory.unit_conjugateEquiv
      {C D} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
      (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (c : C) :
    adj₁.unit.app c ≫ (conjugateEquiv adj₁ adj₂ α).app (L₁.obj c)
      = adj₂.unit.app c ≫ R₂.map (α.app c)

  theorem CategoryTheory.unit_conjugateEquiv_symm
      {C D} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
      (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : R₁ ⟶ R₂) (c : C) :
    adj₁.unit.app c ≫ α.app (L₁.obj c)
      = adj₂.unit.app c ≫ R₂.map (((conjugateEquiv adj₁ adj₂).symm α).app c)
  ```

  These are *literally* "geometric unit, post-composed with the right-adjoint comparison `α`, equals
  the algebraic unit, post-composed with `R₂` of the conjugate (= the left-adjoint dictionary iso)".
  The general (non-conjugate, vertical-functors-non-identity) versions are
  `CategoryTheory.unit_mateEquiv` / `unit_mateEquiv_symm` in the same file; the project uses
  `conjugateIsoEquiv` (vertical functors = `𝟭`), so the conjugate versions are the right specialisation.

- **Project's current path**: the prover attempted an element-level `ext`/generator chase through
  `pullback_spec_tilde_iso`, whose action on `r' ⊗ m` is opaque because it is a `conjugateIsoEquiv`
  term. No element computation pushes through `conjugateIsoEquiv`.

- **Gap**: divergent-with-cost — the project is reproving (by elements, unsuccessfully) a unit-transport
  fact Mathlib already states abstractly.

- **Cost of divergence**: two iters burned on a dead-end `ext` chase; the `simp` normal form of
  `conjugateIsoEquiv` is irreducible on elements, so the element route cannot terminate.

- **Verdict**: ALIGN_WITH_MATHLIB — consume `unit_conjugateEquiv_symm`; do not reprove element-wise.

### Decision: how to expose `adjL.unit` / `adjR.unit` (both are `.comp` of two adjunctions)

- **Mathlib idiom**: `CategoryTheory.Adjunction.comp_unit_app`
  (`Mathlib/CategoryTheory/Adjunction/Basic.lean`):
  ```
  (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
  ```
  where `adj₁ : F ⊣ G`, `adj₂ : H ⊣ I`. Applied to `adjL = tilde.adjunction.comp
  pullbackPushforwardAdjunction` it produces *exactly* the seam's first two factors:
  `(tilde.toTildeΓNatIso.app M).hom ≫ Γ_A.map((pullbackPushforwardAdjunction (Spec inclA)).unit.app (tilde M))`
  (using `tilde.adjunction.unit := toTildeΓNatIso.hom`, a definitional field —
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:280`). Applied to
  `adjR = extendRestrictScalarsAdj.comp (tilde.adjunction (R := A⊗R'))` it splits the algebraic
  unit off as the first factor, with the residual `restrictScalars.map(tilde-Γ unit)` factor that
  the seam's trailing `(tilde.toTildeΓNatIso …).symm` is there to cancel.

- **Verdict**: ALIGN_WITH_MATHLIB — these splits are one `rw`/`simp only` each.

### Decision: is `homEquiv_unit` / `leftAdjointUniq` the right toolset (directive Q2)?

- **Mathlib idiom**: `Adjunction.homEquiv_unit : adj.homEquiv X Y f = adj.unit.app X ≫ G.map f` is the
  hom-set formula for a *single* adjunction; it does not relate *two* adjunctions across a comparison,
  so it cannot transport between `adjL` and `adjR`. `Adjunction.leftAdjointUniq` compares two left
  adjoints of the *same* right adjoint; here the two right adjoints genuinely differ (they are related
  by `gammaPushforwardNatIso`, not equal), so `leftAdjointUniq` does not apply — that is precisely why
  the construction used `conjugateIsoEquiv`.
- **Verdict**: PROCEED (Q2 answered NO) — the conjugate unit-coherence lemmas, not `homEquiv_unit` /
  `leftAdjointUniq`, are the correct tools.

## Recommendation
Close Seam 1 by abstract conjugate calculus, in four moves (none touches elements):

1. `Adjunction.comp_unit_app` + `tilde.adjunction` definitional unit ⇒ seam factors 1+2 = `adjL.unit.app M`.
2. `unit_conjugateEquiv_symm adjL adjR (gammaPushforwardNatIso inclA).hom M` ⇒ the central identity
   `adjL.unit.app M ≫ β.hom.app (L₁.obj M) = adjR.unit.app M ≫ R₂.map ((pullback_spec_tilde_iso inclA M).inv)`,
   where `β := gammaPushforwardNatIso inclA` and the `.inv` identification uses
   `conjugateIsoEquiv_symm_apply_hom` + `Iso.symm`.
3. `Adjunction.comp_unit_app` on `adjR.unit` ⇒ split off `extendRestrictScalarsAdj.unit.app M` (the RHS)
   from the residual `restrictScalars.map(tilde-Γ unit)` factor.
4. ONE project-local "dictionary bridge" remains: the seam's second bracket (built from
   `pushforward_spec_tilde_iso` + `tilde.toTildeΓNatIso` + `Γ_A.map(pushforward.mapIso (pullback_spec_tilde_iso))`)
   must be matched against `β.hom.app (L₁.obj M)` composed with `R₂.map(pullback_spec_tilde_iso.inv)` and
   the residual tilde-Γ factor from step 3. This is a comparison of two *isos that share the
   `gammaPushforwardIso` core* (`gammaPushforwardNatIso` vs `gammaPushforwardTildeIso`/`pushforward_spec_tilde_iso`),
   provable by unfolding those project definitions — NOT an element chase. After it, steps 1–3 cancel the
   non-algebraic factors and leave `extendRestrictScalarsAdj.unit.app M`.

The win: steps 1–3 are three named one-line rewrites; the irreducible work shrinks to the single
structural iso identity in step 4, which lives entirely at the `gammaPushforwardIso` level.
