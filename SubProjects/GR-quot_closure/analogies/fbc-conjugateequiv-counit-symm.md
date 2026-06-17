# Analogy: `conjugateEquiv_counit_symm` for the FBC `g^*`-counit seam (Seam 3)

## Mode
api-alignment

## Slug
fbc-conjugateequiv-counit-symm

## Iteration
022

## Question
Verify `CategoryTheory.conjugateEquiv_counit_symm` (the counit dual of the already-used
`unit_conjugateEquiv_symm`) exists with the right type, that the `Adjunction.comp` counit-splitting
lemma exists, and that the `conjugateEquiv` vs `.symm` DIRECTION matches what
`base_change_mate_gstar_transpose` needs (`.symm α = pullback_spec_tilde_iso ψ`).

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:1490-1551` — `base_change_mate_gstar_transpose`,
  the live crux `sorry` (Seam 3).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:689-696` — `pullback_spec_tilde_iso`, built via the
  iso-level `conjugateIsoEquiv` with a **double** `.symm` (line 696).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:1018-1076` — the PROVEN unit seam
  `base_change_mate_unit_value`, which closed the dual unit coherence via `unit_conjugateEquiv_symm`
  (line 1043) and pinned the direction lemma `hpullinv` (lines 1041-1042). This is the template.

## (a) Existence + signature — VERIFIED VERBATIM

`Mathlib/CategoryTheory/Adjunction/Mates.lean:287` (current pinned Mathlib, in
`namespace CategoryTheory open Adjunction`, `section conjugateEquiv`):

```
theorem conjugateEquiv_counit_symm
    {C D} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : R₁ ⟶ R₂) (d : D) :
  L₂.map (α.app _) ≫ adj₂.counit.app d
    = ((conjugateEquiv adj₁ adj₂).symm α).app _ ≫ adj₁.counit.app d
```

Exactly the signature the directive reported. Note `α : R₁ ⟶ R₂` is a transformation between the
RIGHT adjoints (feed `(gammaPushforwardNatIso ψ).hom`, since the project's `α` is an iso). It is proved
from `conjugateEquiv_counit` (line 281) by the same `right_inv` rewrite that `unit_conjugateEquiv_symm`
(line 305) uses — they sit 18 lines apart in the same section.

## (b) Dual relationship + composite-counit splitting — VERIFIED

- `conjugateEquiv_counit_symm` (line 287) is the literal counit dual of `unit_conjugateEquiv_symm`
  (line 305); both are exported from `Mathlib/CategoryTheory/Adjunction/Mates.lean`, both `@[simps!]`-free
  plain theorems in the same `conjugateEquiv` section. The unit version is already consumed successfully
  by `base_change_mate_unit_value` — the dual route is therefore on equal footing.
- Composite-counit split: `CategoryTheory.Adjunction.comp_counit_app`,
  `Mathlib/CategoryTheory/Adjunction/Basic.lean:590`:
  ```
  (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X
  ```
  (for `adj₁ : F ⊣ G`, `adj₂ : H ⊣ I`). This is the counit mirror of `comp_unit_app` (line 585) that
  the unit seam used (line 1028); it splits `adjL.counit` / `adjR.counit` into their two factors.

## (c) DIRECTION / VARIANCE — CRITICAL, do NOT take the directive's casual phrasing literally

The directive writes "`(conjugateEquiv adjL adjR).symm α = pullback_spec_tilde_iso ψ`". As a *morphism
component* this is FALSE on the nose — it equals the **`.inv`**, because `pullback_spec_tilde_iso` is
defined (line 696) with an OUTER `.symm` on top of the `conjugateIsoEquiv.symm`:

```
pullback_spec_tilde_iso φ M := (((conjugateIsoEquiv adjL adjR).symm (gammaPushforwardNatIso φ)).symm).app M
```

The unit seam already pinned the exact relation (lines 1041-1042), and it is the model to copy:

```
have hpullinv : ((conjugateEquiv adjL adjR).symm β.hom).app M
    = (pullback_spec_tilde_iso inclA M).inv := by rw [hβ]; rfl
```

i.e. `((conjugateEquiv adjL adjR).symm (gammaPushforwardNatIso ψ).hom).app M
= (pullback_spec_tilde_iso ψ M).inv` — by `rfl` after unfolding `β`. So the prover takes
`(conjugateEquiv adjL adjR).symm` (NOT `conjugateEquiv` forward), feeds `(gammaPushforwardNatIso ψ).hom`,
and identifies the result with the **`.inv`** of `pullback_spec_tilde_iso ψ`, replicating `hpullinv`.
Picking `conjugateEquiv` forward, or assuming `.hom`, is the wrong branch.

### Adjunction roles in the instantiation
`adj₁ := adjL = (tilde.adjunction R).comp (pullbackPushforwardAdjunction (Spec.map ψ))`,
`adj₂ := adjR = (ModuleCat.extendRestrictScalarsAdj ψ.hom).comp (tilde.adjunction R')`,
`α := (gammaPushforwardNatIso ψ).hom`. Then in `conjugateEquiv_counit_symm`:
`adj₁.counit = adjL.counit` carries the GEOMETRIC counit (the `pullbackPushforwardAdjunction (Spec.map ψ)`
counit `ε_g` that appears in the goal LHS, via `comp_counit_app`); `adj₂.counit = adjR.counit` carries
the ALGEBRAIC `extendRestrictScalars` counit (the target). The lemma is an equation, usable in either
orientation — match `adjL.counit`'s composite factor to `ε_g` with `comp_counit_app`, exactly mirroring
how the unit seam matched `adjL.unit` with `comp_unit_app`.

## Decisions identified

### Decision: which Mathlib lemma transports the COUNIT across the conjugate (Seam 3)
- **Mathlib idiom**: `CategoryTheory.conjugateEquiv_counit_symm`
  (`Mathlib/CategoryTheory/Adjunction/Mates.lean:287`) + `Adjunction.comp_counit_app`
  (`Mathlib/CategoryTheory/Adjunction/Basic.lean:590`). Direction-pin via the in-file `hpullinv`
  pattern (`.symm (…).hom = pullback_spec_tilde_iso.inv`, by `rfl`).
- **Project's current path**: documented in the `sorry` block (lines 1521-1550) — it correctly names
  `conjugateEquiv_counit_symm` and identifies the per-generator `ext` chase as a dead end (the geometric
  counit/pullback/Γ have no element-level normal form). The abstract conjugate calculus is the only route.
- **Gap**: identical — the lemma the prover pinned is the right one and exists verbatim; the only risk is
  the variance trap in (c).
- **Verdict**: ALIGN_WITH_MATHLIB (confirm-and-proceed) — `conjugateEquiv_counit_symm` is confirmed; use
  `.symm` direction and identify with `pullback_spec_tilde_iso ψ`'s **`.inv`**, not `.hom`.

## Recommendation
Close Seam 3 by the dual of the proven unit seam: (1) `Functor.map_comp` + `Iso.inv_comp_eq` /
`Iso.eq_comp_inv` to isolate the two geometric Γ-factors `Γ(g^*(θ_in)) ≫ Γ(ε_g)` (already done in the
source up to the `sorry`); (2) split `adjL.counit` via `comp_counit_app` to expose the geometric
`pullbackPushforwardAdjunction (Spec.map ψ)` counit; (3) apply
`conjugateEquiv_counit_symm adjL adjR (gammaPushforwardNatIso ψ).hom _` and rewrite the conjugate via the
`hpullinv`-analogue `((conjugateEquiv adjL adjR).symm (gammaPushforwardNatIso ψ).hom).app _ =
(pullback_spec_tilde_iso ψ _).inv` (by `rfl`), turning the geometric counit into the algebraic
`extendRestrictScalars` counit; (4) discharge the two residual pieces (the `Γ_R(θ_in)=ρ` inner reindex,
reproven inline per the `sorry` note, and the `extendScalars ψ (ρ) ≫ algebraic counit = regroupEquiv.inv`
one-generator `ext`). All four moves mirror `base_change_mate_unit_value`; no element chase.
