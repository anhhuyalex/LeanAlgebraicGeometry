import AlgebraicJacobian.Picard.TensorObjSubstrate

set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry
namespace Scheme
namespace Modules

set_option maxHeartbeats 2000000 in
/-- Sheaf-level identity (★) that core C reduces to after transposing under sheafification. -/
lemma coreC_sheaf {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) :
    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)).inv ≫
      (Scheme.Modules.pullback h).map (pullbackValIso f M).hom
    = (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
          ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
              (𝟙 Y.ringCatSheaf.val)).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
          (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)) ≫
      (pullbackValIso h ((Scheme.Modules.pullback f).obj M)).hom := by
  -- abbreviations (plain `let`-free; written out so spellings match the goal).
  -- (★★): the homEquiv round-trip identity `a_Y(cmp) ≫ ε = g.hom`.
  have hcmp_he : (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.val)).unit.app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
      (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom
      = (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.val)).homEquiv _ _ (pullbackValIso f M).hom := by
    rw [Adjunction.homEquiv_unit, Functor.comp_map, restrictScalarsId_map]
  have hstar : (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
            (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom) ≫
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.val)).counit.app ((Scheme.Modules.pullback f).obj M)
      = (pullbackValIso f M).hom := by
    rw [hcmp_he, ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  -- unfold pvi h N (kept in `asIso` form so the `rfl` closes), then reduce the counit `asIso`.
  rw [show (pullbackValIso h ((Scheme.Modules.pullback f).obj M)).hom
      = ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((Scheme.Modules.pullback f).obj M).val).inv ≫
        (Scheme.Modules.pullback h).map
          ((asIso (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
            (𝟙 Y.ringCatSheaf.val)).counit).app ((Scheme.Modules.pullback f).obj M)).hom
      from by simp only [pullbackValIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]]
  simp only [Iso.app_hom, asIso_hom]
  -- naturality of `scPbH.inv` at `cmp`.
  have hnat := (SheafOfModules.sheafificationCompPullback
    (Hom.toRingCatSheafHom h)).inv.naturality
      ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.val)).unit.app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
      (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
  simp only [Functor.comp_map] at hnat
  rw [show ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
        ((Scheme.Modules.pullback f).obj M).val).inv
      = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).inv.app
        ((Scheme.Modules.pullback f).obj M).val from rfl,
      show ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)).inv
      = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).inv.app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) from rfl]
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, hstar]


set_option maxHeartbeats 2000000 in
/-- Core coherence C, the residual of `cmp_leg` after its verified prefix. -/
lemma cmp_leg_coreC {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) :
    (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
        (𝟙 Z.ringCatSheaf.val)).unit.app
      ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)) ≫
    (SheafOfModules.forget Z.ringCatSheaf).map
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)).inv ≫
    (SheafOfModules.forget Z.ringCatSheaf).map
      ((Scheme.Modules.pullback h).map (pullbackValIso f M).hom)
    = (PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
        ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
            (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom) ≫
      (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
          (𝟙 Z.ringCatSheaf.val)).unit.app
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
          ((Scheme.Modules.pullback f).obj M).val) ≫
      (SheafOfModules.forget Z.ringCatSheaf).map
        (pullbackValIso h ((Scheme.Modules.pullback f).obj M)).hom := by
  sorry

end Modules
end Scheme
end AlgebraicGeometry
