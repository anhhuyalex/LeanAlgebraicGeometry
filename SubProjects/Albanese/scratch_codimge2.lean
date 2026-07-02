import Mathlib
import AlgebraicJacobian.Albanese.CodimOneExtension

set_option maxSynthPendingDepth 3
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-- Glue: the function-field morphism of a partial map factors through the
`Spec`-of-stalk morphism at any point of its domain. -/
private lemma fromFunctionField_factor
    {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X.PartialMap Y) {x : X}
    (hx : x ∈ g.domain) :
    g.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)) ≫
        g.fromSpecStalkOfMem hx := by
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
    Category.assoc, Opens.fromSpecStalkOfMem_ι,
    SpecMap_stalkSpecializes_fromSpecStalk]

/-- Bridge: the `algebraMap` of `stalkFunctionFieldAlgebra` is the
stalk-specialization map. -/
private lemma ofHom_algebraMap_stalk_functionField
    {X : Scheme.{u}} [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) :=
  rfl

theorem indeterminacy_codimGe2_of_smooth_of_complete'
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of kbar))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    ∀ z ∈ indeterminacyLocus f, 2 ≤ Order.coheight z := by
  intro z hz
  have hzdom : z ∉ f.domain := hz
  by_contra hlt
  have hle : Order.coheight z ≤ 1 := by
    have h2 : Order.coheight z < 2 := not_le.mp hlt
    rwa [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.lt_add_one_iff one_ne_top] at h2
  -- The generic point of X.
  have hspec : genericPoint X.left ⤳ z :=
    (genericPoint_spec X.left).specializes trivial
  -- Over-ness at the function-field level.
  have hff : f.fromFunctionField ≫ Y.hom
      = X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
    obtain ⟨g0, rfl⟩ := f.exists_rep
    have h1' : (g0.compHom Y.hom).toRationalMap
        = X.hom.toPartialMap.toRationalMap := by
      rw [← RationalMap.compHom_toRationalMap]; exact hf
    have h2 := congrArg RationalMap.fromFunctionField h1'
    rw [RationalMap.fromFunctionField_toRationalMap,
      RationalMap.fromFunctionField_toRationalMap] at h2
    simpa using h2
  rcases hle.lt_or_eq with h0 | h1
  · -- coheight 0: `z` is the generic point, which lies in the dense open domain.
    rw [Order.lt_one_iff] at h0
    have hmax : IsMax z := Order.coheight_eq_zero.mp h0
    have hzeq : z = genericPoint X.left :=
      (show z ⤳ genericPoint X.left from hmax hspec).antisymm hspec
    obtain ⟨w, hw⟩ := f.dense_domain.nonempty
    exact hzdom (hzeq ▸ (genericPoint_specializes w).mem_open f.domain.2 hw)
  · -- coheight 1: valuative criterion at the DVR stalk.
    haveI hDVR : IsDiscreteValuationRing (X.left.presheaf.stalk z) :=
      Scheme.localRing_dvr_of_codim_one z h1.symm
    haveI : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    -- The valuative criterion for the proper structure morphism of Y.
    have hVC : ValuativeCriterion Y.hom := by
      have hP : IsProper Y.hom := inferInstance
      rw [IsProper.eq_valuativeCriterion] at hP
      exact hP.1.1.1
    -- The valuative commutative square.
    have hcommSq : CommSq f.fromFunctionField
        (Spec.map (CommRingCat.ofHom
          (algebraMap (X.left.presheaf.stalk z) X.left.functionField)))
        Y.hom (X.left.fromSpecStalk z ≫ X.hom) := ⟨by
      rw [hff, ← Category.assoc, ofHom_algebraMap_stalk_functionField,
        SpecMap_stalkSpecializes_fromSpecStalk hspec]⟩
    let S : ValuativeCommSq Y.hom :=
      { R := X.left.presheaf.stalk z
        K := X.left.functionField
        i₁ := f.fromFunctionField
        i₂ := X.left.fromSpecStalk z ≫ X.hom
        commSq := hcommSq }
    obtain ⟨hlift⟩ := hVC S
    obtain ⟨L, hfacl, hfacr⟩ := hlift.default
    -- Spread the lift out to a partial map defined at z.
    let g : X.left.PartialMap Y.left :=
      PartialMap.ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hzg : z ∈ g.domain :=
      PartialMap.mem_domain_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgL : g.fromSpecStalkOfMem hzg = L :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgen : g.toRationalMap = f := by
      refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
      rw [RationalMap.fromFunctionField_toRationalMap,
        fromFunctionField_factor g hzg, hgL,
        ← ofHom_algebraMap_stalk_functionField]
      exact hfacl
    exact hzdom (RationalMap.mem_domain.mpr ⟨g, hzg, hgen⟩)

end RationalMap

end Scheme

end AlgebraicGeometry
