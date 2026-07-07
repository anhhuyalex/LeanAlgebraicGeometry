import Mathlib

/-!
# Scheme-general tangent-space helpers

This file packages the scheme-general dual-number substrate needed by the
Picard/Jacobian tangent-space arguments. The goal is to move non-Picard
content out of `Pic0AbelianVariety.lean`, so that the remaining `sorry`s in
that file record only the genuinely Picard-specific work.

Current closures in this file are intentionally modest but real:

* the dual-number objects used for functor-of-points tangent spaces;
* the subtype of pointed dual-number points at a rational point;
* the residue-field identification for a section over `Spec k`;
* finite-dimensionality of the cotangent space at a point of a scheme locally
  of finite type over a field.

The remaining comparison
`pointedDualNumberPoints ≃ Module.Dual (CotangentSpace ...)` is stated here as
an honest typed `sorry`, because it is scheme-general and should not remain
buried in the Picard file.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- The ring of dual numbers `k[ε]` as an object of `CommRingCat`. -/
noncomputable abbrev dualNumbers (k : Type u) [Field k] : CommRingCat.{u} :=
  .of (DualNumber k)

/-- The augmentation `k[ε] → k`, sending `ε` to `0`. -/
noncomputable def dualNumbersAugment (k : Type u) [Field k] :
    dualNumbers k ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom

/-- Pointed `k[ε]`-valued points of a `k`-scheme `X` at a rational point
`e : Spec k ⟶ X`. -/
def pointedDualNumberPoints {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (e : Spec (.of k) ⟶ X.left) : Type u :=
  { f : Spec (dualNumbers k) ⟶ X.left //
    f ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
    Spec.map (dualNumbersAugment k) ≫ f = e }

/-- A section `e : Spec k ⟶ X` of a scheme over `Spec k` is a `k`-rational point,
so the residue field at `e` is canonically `k`. -/
theorem residueFieldIso_of_section_over_field {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (e : Spec (.of k) ⟶ X.left)
    (hsec : e ≫ X.hom = 𝟙 (Spec (.of k))) :
    Nonempty (X.left.residueField (e.base default) ≅ CommRingCat.of k) := by
  set sbar := e.residueFieldMap default with hsbar
  set pbar := X.hom.residueFieldMap (e.base default) with hpbar
  have hc : (e ≫ X.hom).residueFieldMap default = pbar ≫ sbar :=
    residueFieldMap_comp e X.hom default
  haveI : IsOpenImmersion (e ≫ X.hom) := by rw [hsec]; infer_instance
  haveI : IsIso (pbar ≫ sbar) :=
    hc ▸ (inferInstance : IsIso ((e ≫ X.hom).residueFieldMap default))
  haveI : IsSplitEpi sbar :=
    ⟨⟨inv (pbar ≫ sbar) ≫ pbar, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩
  haveI : Mono sbar :=
    ConcreteCategory.mono_of_injective sbar sbar.hom.injective
  haveI : IsIso sbar := isIso_of_mono_of_isSplitEpi sbar
  obtain ⟨hbase⟩ : Nonempty ((Spec (.of k)).residueField default ≅ CommRingCat.of k) := by
    let x : Spec (.of k) := default
    refine ⟨Scheme.Spec.residueFieldIso (.of k) default ≪≫ ?_⟩
    exact
      ((Ideal.algEquivResidueFieldOfField (k := k) x.asIdeal).toRingEquiv.toCommRingCatIso).symm
  exact ⟨asIso sbar ≪≫ hbase⟩

/-- For a scheme locally of finite type over a field, the cotangent space at any
point is finite-dimensional over the residue field. This is the local
Noetherianity input that later dimension arguments need. -/
theorem finiteDimensional_cotangentSpace_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (x : X.left) :
    FiniteDimensional (IsLocalRing.ResidueField (X.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  infer_instance

/-- **Typed sorry (scheme-general, Stacks 0B28).** For a section
`e : Spec k ⟶ X` over `Spec k`, pointed `k[ε]`-valued points at `e` are in
canonical bijection with linear forms on the cotangent space at `e`.

This is the scheme-level dual-number tangent dictionary and is deliberately
stated here, outside the Picard file, because its proof should only use
general scheme/local-ring API:

1. `SpecToEquivOfLocalRing` converts `Spec k[ε] ⟶ X` to local ring maps out of
   the stalk;
2. the pointing conditions force the image point to be `e.base default` and
   the residue-field part to be the standard augmentation;
3. the remaining data is a derivation into the square-zero ideal, hence a
   functional on `m/m²`.

The hard work is therefore real but non-Picard-specific. -/
theorem pointedDualNumberPoints_equiv_cotangentSpaceDual_of_section
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (e : Spec (.of k) ⟶ X.left) (hsec : e ≫ X.hom = 𝟙 (Spec (.of k))) :
    Nonempty (pointedDualNumberPoints X e ≃
      Module.Dual
        (IsLocalRing.ResidueField (X.left.presheaf.stalk (e.base default)))
        (IsLocalRing.CotangentSpace (X.left.presheaf.stalk (e.base default)))) := by
  sorry

end Scheme

end AlgebraicGeometry
