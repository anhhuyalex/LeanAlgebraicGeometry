/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegTop

/-!
# Sub-brick A — LegAux: the upper `coreIso_comm` chain

The three upper lemmas of the `coreIso_comm` chain:
`coreIso_comm_coface`, `coreIso_comm_sum`, `coreIso_comm`.

Split from `CechSectionIdentificationLeg` to allow both files to compile within
the 10-minute heartbeat budget (the three lemmas totalled ~14 M HB).

Depends on `CechSectionIdentificationLeg` (transitively Base).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

set_option maxHeartbeats 6400000 in
/-- **Per-coface square of the core comparison** (`lem:coreIso_comm_coface`): for each
degree `p` and coface index `k`, the object isos intertwine the individual cofaces.
Coordinatewise extensionality (`Pi.hom_ext`); the `σ'`-coordinate of the left side is the
face restriction by the defining `Pi.lift_π` of the section-Čech cosimplicial map, and the
right side is `coreIso_comm_leg`. -/
lemma coreIso_comm_coface (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) (k : Fin (p + 2)) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)).δ k =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  ext x
  apply (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1)).injective
  funext σ'
  have hπ : (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F)).map (SimplexCategory.δ k) ≫
        Pi.π _ σ' =
      Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k :=
    Pi.lift_π _ σ'
  have hL := ConcreteCategory.congr_hom hπ (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x)
  have hR := ConcreteCategory.congr_hom (coreIso_comm_leg 𝒰 F V p k σ') x
  exact ((sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ').trans hL).trans
    (((sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ').trans hR).symm)

set_option maxHeartbeats 6400000 in
/-- **Alternating-sum assembly of the core comparison square** (`lem:coreIso_comm_sum`):
the full alternating-coface differentials are intertwined by the object isos.  Proved
ELEMENTWISE (per the iter-067 dead-end note: no `Preadditive.comp_sum` against the bundled
`AddCommGrpCat`-hom `objD`): both sides, evaluated at an element and a coordinate `σ'`, are
the same finite alternating sum, matched summand-by-summand by `coreIso_comm_leg`. -/
lemma coreIso_comm_sum (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F)) p =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (AlgebraicTopology.AlternatingCofaceMapComplex.objD
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  haveI : (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).Additive := inferInstance
  haveI : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).Additive :=
    inferInstance
  -- (1) Element-level decomposition of the evaluated nerve differential.  All steps are
  -- term-chained (`Eq.trans`/`congrArg`) — no `rw` of a `have` against the goal, dodging the
  -- instance-path mismatch on the `Finset.sum` of the `Preadditive` hom group.
  have hpush : ∀ x : ToType (((SheafOfModules.forget X.ringCatSheaf).obj
        (pushPullObj F
          ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))))).presheaf.obj
        (Opposite.op V)),
      ConcreteCategory.hom
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              (AlgebraicTopology.AlternatingCofaceMapComplex.objD
                (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p))) x =
        ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ConcreteCategory.hom
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
                (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
              ((SheafOfModules.forget X.ringCatSheaf ⋙
                  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
                ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i))) x := by
    intro x
    have h1 : (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (AlgebraicTopology.AlternatingCofaceMapComplex.objD
            (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p) =
        ∑ i : Fin (p + 2), (SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((-1 : ℤ) ^ (i : ℕ) • (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i) :=
      Functor.map_sum _ _ _
    have h2 : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (AlgebraicTopology.AlternatingCofaceMapComplex.objD
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p)) =
        ∑ i : Fin (p + 2),
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((-1 : ℤ) ^ (i : ℕ) •
                (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) :=
      (congrArg (fun m => (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map m) h1).trans
        (Functor.map_sum _ _ _)
    refine (ConcreteCategory.congr_hom h2 x).trans ?_
    rw [abHom_finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((-1 : ℤ) ^ (i : ℕ) •
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) =
        (-1 : ℤ) ^ (i : ℕ) •
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) :=
      (congrArg (fun m => (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map m)
        (Functor.map_zsmul _)).trans (Functor.map_zsmul _)
    exact (ConcreteCategory.congr_hom h3 x).trans rfl
  -- (2) Elementwise comparison through the product equivalence, coordinate by coordinate.
  ext x
  apply (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1)).injective
  funext σ'
  refine Eq.trans (sectionCech_objD_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) p
    (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x) σ') (Eq.symm ?_)
  refine Eq.trans (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ') ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (ConcreteCategory.comp_apply _ ((coreIso_objIso 𝒰 F (p + 1) V).hom) x)) ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (congrArg (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) (hpush x))) ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (map_sum (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) _ Finset.univ)) ?_
  refine Eq.trans (map_sum (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ')) _ Finset.univ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (map_zsmul (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) _ _)) ?_
  refine Eq.trans (map_zsmul (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ')) _ _) ?_
  congr 1
  have hleg := ConcreteCategory.congr_hom (coreIso_comm_leg 𝒰 F V p i σ') x
  simp only [ConcreteCategory.comp_apply] at hleg
  rw [sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) p
    (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x)
    (σ' ∘ (SimplexCategory.δ i).toOrderHom)]
  exact hleg

set_option maxHeartbeats 1600000 in
/-- **The core comparison intertwines the Čech differentials** (`lem:coreIso_comm`).  Under the
degreewise object isos `coreIso_objIso`, the alternating-coface differential of the evaluated
backbone complex `(G_V ∘ Ψ) Č•(𝒰, F)` matches the alternating-coface differential of the
concrete restricted section complex `Č•(𝒰', F)`.  The square is exactly the alternating-sum
assembly `coreIso_comm_sum` (built from the per-coface squares `coreIso_comm_coface`, in turn
from the per-leg naturality `coreIso_comm_leg`). -/
lemma coreIso_comm (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (coreIso_objIso 𝒰 F i V).hom ≫ (sectionCechComplexV 𝒰 F V).d i j =
      (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
              (Opposite.op V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (cechComplexOnX 𝒰 F))).d i j ≫
        (coreIso_objIso 𝒰 F j V).hom := by
  obtain rfl : i + 1 = j := hij
  rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
  have hsec : (sectionCechComplexV 𝒰 F V).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)) i :=
    CochainComplex.of_d _ _ (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared _) i
  have hX : (cechComplexOnX 𝒰 F).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) i :=
    CochainComplex.of_d _ _ (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared _) i
  rw [hsec, hX]
  exact coreIso_comm_sum 𝒰 F V i

end AlgebraicGeometry
