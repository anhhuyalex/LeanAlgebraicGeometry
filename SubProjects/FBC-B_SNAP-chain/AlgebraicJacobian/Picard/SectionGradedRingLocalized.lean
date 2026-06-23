import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Section graded ring infrastructure, Layer 1: tensor powers of a sheaf of modules

This file builds the Mathlib-absent infrastructure of
`blueprint/src/chapters/Picard_SectionGradedRing.tex`, Layer 1
(`sec:sgr_tensor_powers`): the tensor product, tensor powers, and twists of
sheaves of modules over a scheme `X`, together with the unitor and braiding
isomorphisms of the sheaf tensor product.

The category `X.Modules = SheafOfModules X.ringCatSheaf` of sheaves of modules
over a scheme carries **no** monoidal structure in Mathlib (the structure sheaf
varies the base ring over opens).  Mathlib *does* supply:

* the symmetric monoidal structure on the category of **presheaves** of modules
  `PresheafOfModules.monoidalCategory`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`), and
* the sheafification functor `PresheafOfModules.sheafification`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`).

We therefore build the tensor product of sheaves of modules as the sheafification
of the objectwise (presheaf) tensor product, following
[Stacks, Tag 01CA].

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.sheafification` — the scheme-level
  sheafification functor `X.PresheafOfModules ⥤ X.Modules`.
* `AlgebraicGeometry.Scheme.Modules.tensorObj` (`def:sheafTensorObj`) —
  `F ⊗ G := (F.toPresheaf ⊗ G.toPresheaf)^#`.
* `AlgebraicGeometry.Scheme.Modules.tensorPow` (`def:sheafTensorPow`) —
  the `m`-th tensor power `L^{⊗m}` of a sheaf of modules.
* `AlgebraicGeometry.Scheme.Modules.moduleTensorPow` (`def:sheafModuleTwist`) —
  the `m`-twist `F(m) = F ⊗ L^{⊗m}`.
* `AlgebraicGeometry.Scheme.Modules.sheafificationCounitIso` — the reflective
  counit iso `(F.toPresheaf)^# ≅ F`.
* `AlgebraicGeometry.Scheme.Modules.tensorObjUnitIso`,
  `AlgebraicGeometry.Scheme.Modules.tensorObjRightUnitor`,
  `AlgebraicGeometry.Scheme.Modules.tensorBraiding` — the left/right unitor and
  braiding isomorphisms of the sheaf tensor product.

The comparison isomorphism `L^{⊗m} ⊗ L^{⊗m'} ≅ L^{⊗(m+m')}`
(`tensorPowAdd`, `lem:sheafTensorPow_add`) is provided in this file, built on the
strong-monoidality comparison `isIso_sheafification_whiskerRight_unit` and the
associator/braiding of the sheaf tensor product.
-/

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The scheme-level sheafification functor, sending a presheaf of modules over a
scheme `X` to its associated sheaf of modules `X.Modules`.  It is the
`PresheafOfModules.sheafification` functor for the identity morphism of the
underlying presheaf of rings (which is locally bijective).  Non-private because it
appears in the statement of `isIso_sheafification_whiskerRight_unit`. -/
noncomputable def sheafification : X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The category `X.PresheafOfModules` of presheaves of modules over a scheme,
presented in the exact form `PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)`
for which Mathlib equips it with a symmetric monoidal structure.  This is
*definitionally* `X.PresheafOfModules` (since
`X.ringCatSheaf.obj = X.sheaf.obj ⋙ forget₂ CommRingCat RingCat`), so a term of
either type is accepted for the other. -/
abbrev MonoidalPresheaf (X : Scheme.{u}) : Type _ :=
  _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)

/-- The structure sheaf as a sheaf of modules over itself: the unit object of the
tensor product, i.e. the zeroth tensor power `L^{⊗0} = 𝒪_X`
(`def:unitModule`, backed by `lem:moduleUnit_mathlib`).  Public: the SNAP graded
assembly (`sectionsMul_assoc_unit`, `lem:sectionMul_coherent`) states unitality
against this object. -/
noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The counit isomorphism of the module sheafification adjunction: sheafifying
the underlying presheaf of a sheaf of modules returns the sheaf itself.  This is
an isomorphism because the counit of `sheafification ⊣ toPresheafOfModules` is
invertible (the right adjoint `SheafOfModules.forget` is fully faithful).  It is
the launching pad for the left-unitor base case of `tensorPowAdd`. -/
noncomputable def sheafificationCounitIso (G : X.Modules) :
    sheafification.obj ((toPresheafOfModules X).obj G) ≅ G :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app G

/-! ### The strong-monoidality comparison `isIso_sheafification_whiskerRight_unit`

Following `analogies/snap-route.md` (Analogue 1) and the blueprint proof of
`lem:isIso_sheafification_whiskerRight_unit`: module sheafification is the
localization functor at the class `W := J.W.inverseImage (toPresheaf R₀)` of
morphisms of presheaves of modules whose underlying abelian-presheaf morphism is a
local isomorphism (a `J.W` for the opens topology `J` on `X`). -/

/-- The Grothendieck topology on the opens of the scheme `X`. -/
private abbrev opensTopology (X : Scheme.{u}) : GrothendieckTopology (TopologicalSpace.Opens X) :=
  Opens.grothendieckTopology (X : TopCat)

open MorphismProperty in
/-- **Localization criterion for module sheafification.**  The scheme-level module
sheafification `sheafification.map f` is an isomorphism of sheaves of modules iff the
underlying abelian-presheaf morphism `(PresheafOfModules.toPresheaf _).map f` lies in
the weak-equivalence class `J.W` of the opens topology (i.e. is a local isomorphism of
abelian-group presheaves).  This is the reduction step of
`isIso_sheafification_whiskerRight_unit`: it turns the strong-monoidality comparison
into a purely abelian local-isomorphism statement.  Project-local: it specialises
`_root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` to the
identity morphism of `X.ringCatSheaf.obj`. -/
lemma isIso_sheafification_map_iff {P Q : X.PresheafOfModules} (f : P ⟶ Q) :
    IsIso (sheafification.map f) ↔
      (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) := by
  have e := _root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (J := opensTopology X) (𝟙 X.ringCatSheaf.obj)
  constructor
  · intro h
    have h' : ((MorphismProperty.isomorphisms (SheafOfModules X.ringCatSheaf)).inverseImage
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) f := h
    rw [← e] at h'
    exact h'
  · intro h
    have h' : (((opensTopology X).W).inverseImage
        (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)) f := h
    rw [e] at h'
    exact h'

/-- **The sheafification unit is an abelian local isomorphism.**  The underlying
abelian-presheaf morphism of the module sheafification unit `η_P : P ⟶ P^#` is
*definitionally* the abelian sheafification unit `toSheafify J P.presheaf`
(`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`), which lies
in the weak-equivalence class `J.W` of the opens topology by
`GrothendieckTopology.W_toSheafify`.  Project-local: this is the `η_P ∈ J.W`
ingredient of the abelian-`J.W`-monoidality transfer underlying
`isIso_sheafification_whiskerRight_unit`. -/
lemma localIso_toPresheaf_map_unit (P : X.PresheafOfModules) :
    (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (opensTopology X).W_toSheafify _

/-! ## Project-local Mathlib supplement — relative tensor product as a coequalizer

This section builds the **objectwise** content of `lem:relativeTensor_as_coequalizer`
(`relativeTensorCoequalizerIso`): over a commutative ring `S` and `S`-modules `M, N`,
the relative tensor product `M ⊗[S] N` is the coequalizer, *in the category of abelian
groups*, of the two `S`-action maps

  `M ⊗[ℤ] S ⊗[ℤ] N  ⇉  M ⊗[ℤ] N`,    `m ⊗ s ⊗ n ↦ (s • m) ⊗ n`  /  `m ⊗ (s • n)`.

This is the Mathlib-absent brick on which the strong-monoidality comparison
`isIso_sheafification_whiskerRight_unit` rests: the underlying abelian presheaf of the
presheaf-level relative tensor `P ⊗_p Q` is, objectwise, exactly this coequalizer.  The
universal property is the abelian-group universal property of the relative tensor product,
packaged by `TensorProduct.liftAddHom`.  Everything here is axiom-clean.

The promotion of this objectwise colimit to the presheaf category `Cᵒᵖ ⥤ AddCommGrp`
(where colimits are computed objectwise) and the identification of the whiskered unit
`η_P ▷ Q` with the induced map of coequalizers are the next steps; see the handoff note. -/

namespace RelativeTensorCoequalizer

open TensorProduct

variable (S : Type u) [CommRing S] (M N : Type u)
  [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

/-- The `S`-action map `S ⊗[ℤ] N → N`, `s ⊗ n ↦ s • n`, as a `ℤ`-linear map. -/
noncomputable def actN : (S ⊗[ℤ] N) →ₗ[ℤ] N :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun s n => s • n)
    (fun s1 s2 n => add_smul s1 s2 n) (fun c s n => smul_assoc c s n)
    (fun s n1 n2 => smul_add s n1 n2) (fun c s n => smul_comm s c n))

/-- The `S`-action map `M ⊗[ℤ] S → M`, `m ⊗ s ↦ s • m`, as a `ℤ`-linear map. -/
noncomputable def actM : (M ⊗[ℤ] S) →ₗ[ℤ] M :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun m s => s • m)
    (fun m1 m2 s => smul_add s m1 m2) (fun c m s => smul_comm s c m)
    (fun m s1 s2 => add_smul s1 s2 m) (fun c m s => smul_assoc c s m))

/-- Right action map `M ⊗[ℤ] (S ⊗[ℤ] N) → M ⊗[ℤ] N`, `m ⊗ (s ⊗ n) ↦ m ⊗ (s • n)`. -/
noncomputable def actRmap : (M ⊗[ℤ] (S ⊗[ℤ] N)) →ₗ[ℤ] (M ⊗[ℤ] N) :=
  TensorProduct.map LinearMap.id (actN S N)

/-- Left action map `M ⊗[ℤ] (S ⊗[ℤ] N) → M ⊗[ℤ] N`, `m ⊗ (s ⊗ n) ↦ (s • m) ⊗ n`. -/
noncomputable def actLmap : (M ⊗[ℤ] (S ⊗[ℤ] N)) →ₗ[ℤ] (M ⊗[ℤ] N) :=
  (TensorProduct.map (actM S M) LinearMap.id).comp
    (TensorProduct.assoc ℤ M S N).symm.toLinearMap

omit [Module S M] in
@[simp] lemma actRmap_tmul (m : M) (s : S) (n : N) :
    actRmap S M N (m ⊗ₜ (s ⊗ₜ n)) = m ⊗ₜ (s • n) := rfl

omit [Module S N] in
@[simp] lemma actLmap_tmul (m : M) (s : S) (n : N) :
    actLmap S M N (m ⊗ₜ (s ⊗ₜ n)) = (s • m) ⊗ₜ n := rfl

/-- The canonical projection `M ⊗[ℤ] N → M ⊗[S] N`, `m ⊗ n ↦ m ⊗ n`, as a `ℤ`-linear
map.  It is the cofork map exhibiting `M ⊗[S] N` as the coequalizer. -/
noncomputable def projL : (M ⊗[ℤ] N) →ₗ[ℤ] (M ⊗[S] N) :=
  (TensorProduct.liftAddHom
    { toFun := fun m =>
        (LinearMap.toAddMonoidHom (((TensorProduct.mk S M N) m).restrictScalars ℤ))
      map_zero' := by ext n; simp
      map_add' := fun m1 m2 => by ext n; simp }
    (fun r m n => by simp)).toIntLinearMap

@[simp] lemma projL_tmul (m : M) (n : N) : projL S M N (m ⊗ₜ n) = m ⊗ₜ[S] n := rfl

/-- The projection `M ⊗[ℤ] N → M ⊗[S] N` is surjective (it is the canonical
quotient map onto the relative tensor). -/
lemma projL_surjective : Function.Surjective (projL S M N) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n => exact ⟨m ⊗ₜ[ℤ] n, projL_tmul S M N m n⟩
  | add a b ha hb =>
    obtain ⟨pa, rfl⟩ := ha; obtain ⟨pb, rfl⟩ := hb; exact ⟨pa + pb, map_add _ _ _⟩

/-- The two action maps become equal after the projection: this is the cofork
coequalizing condition, established at the level of `ℤ`-linear maps. -/
lemma projL_comp_act :
    (projL S M N).comp (actLmap S M N) = (projL S M N).comp (actRmap S M N) := by
  apply TensorProduct.ext'; intro m x
  induction x with
  | zero => rw [tmul_zero, map_zero, map_zero]
  | tmul s n =>
    change projL S M N (actLmap S M N (m ⊗ₜ (s ⊗ₜ n)))
      = projL S M N (actRmap S M N (m ⊗ₜ (s ⊗ₜ n)))
    rw [actLmap_tmul, actRmap_tmul, projL_tmul, projL_tmul, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [tmul_add, map_add, map_add, ha, hb]

/-- Left action map as a morphism of abelian groups. -/
noncomputable def aL :
    AddCommGrpCat.of (M ⊗[ℤ] (S ⊗[ℤ] N)) ⟶ AddCommGrpCat.of (M ⊗[ℤ] N) :=
  AddCommGrpCat.ofHom (actLmap S M N).toAddMonoidHom
/-- Right action map as a morphism of abelian groups. -/
noncomputable def aR :
    AddCommGrpCat.of (M ⊗[ℤ] (S ⊗[ℤ] N)) ⟶ AddCommGrpCat.of (M ⊗[ℤ] N) :=
  AddCommGrpCat.ofHom (actRmap S M N).toAddMonoidHom
/-- The projection as a morphism of abelian groups. -/
noncomputable def piMor :
    AddCommGrpCat.of (M ⊗[ℤ] N) ⟶ AddCommGrpCat.of (M ⊗[S] N) :=
  AddCommGrpCat.ofHom (projL S M N).toAddMonoidHom

@[simp] lemma piMor_apply (x) : (ConcreteCategory.hom (piMor S M N)) x = projL S M N x := rfl

instance piMor_epi : Epi (piMor S M N) :=
  ConcreteCategory.epi_of_surjective (piMor S M N) (projL_surjective S M N)

/-- The projection coequalizes the two action maps (as morphisms of abelian groups). -/
lemma coeq_condition : aL S M N ≫ piMor S M N = aR S M N ≫ piMor S M N := by
  ext x; exact LinearMap.congr_fun (projL_comp_act S M N) x

/-- The cofork `M ⊗[ℤ] (S ⊗[ℤ] N) ⇉ M ⊗[ℤ] N → M ⊗[S] N` of abelian groups. -/
noncomputable def cofork : Limits.Cofork (aL S M N) (aR S M N) :=
  Limits.Cofork.ofπ (piMor S M N) (coeq_condition S M N)

/-- The descent map out of `M ⊗[S] N` induced by a cofork `s`: a pair of global
sections balanced under the `S`-action factors through the relative tensor.  This
is the universal property packaged by `TensorProduct.liftAddHom`. -/
noncomputable def descHom (s : Limits.Cofork (aL S M N) (aR S M N)) :
    (M ⊗[S] N) →+ s.pt :=
  TensorProduct.liftAddHom
    { toFun := fun m =>
        { toFun := fun n => (ConcreteCategory.hom s.π) (m ⊗ₜ[ℤ] n)
          map_zero' := by rw [tmul_zero, map_zero]
          map_add' := fun n1 n2 => by rw [tmul_add, map_add] }
      map_zero' := by ext n; simp [zero_tmul]
      map_add' := fun m1 m2 => by ext n; simp [add_tmul] }
    (fun a m n => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      have key :=
        congrArg (fun φ => (ConcreteCategory.hom φ) (m ⊗ₜ[ℤ] (a ⊗ₜ[ℤ] n))) s.condition
      simpa using key)

@[simp] lemma descHom_tmul (s : Limits.Cofork (aL S M N) (aR S M N)) (m : M) (n : N) :
    descHom S M N s (m ⊗ₜ[S] n) = (ConcreteCategory.hom s.π) (m ⊗ₜ[ℤ] n) := rfl

/-- The descent map as a morphism of abelian groups out of the cofork apex. -/
noncomputable def descMor (s : Limits.Cofork (aL S M N) (aR S M N)) :
    (cofork S M N).pt ⟶ s.pt :=
  AddCommGrpCat.ofHom (descHom S M N s)

/-- The descent map factors the cofork's projection: `π ≫ descMor s = s.π`. -/
lemma descFac (s : Limits.Cofork (aL S M N) (aR S M N)) :
    (cofork S M N).π ≫ descMor S M N s = s.π := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    change descHom S M N s (projL S M N (m ⊗ₜ[ℤ] n)) = (ConcreteCategory.hom s.π) (m ⊗ₜ[ℤ] n)
    rw [projL_tmul, descHom_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **`M ⊗[S] N` is the coequalizer**, in the category of abelian groups, of the two
`S`-action maps `M ⊗[ℤ] (S ⊗[ℤ] N) ⇉ M ⊗[ℤ] N`.  This is the objectwise content of
`lem:relativeTensor_as_coequalizer`; uniqueness uses that the projection `piMor` is an
epimorphism.  Axiom-clean. -/
noncomputable def isColimitCofork : Limits.IsColimit (cofork S M N) :=
  Limits.Cofork.IsColimit.mk _ (descMor S M N) (descFac S M N)
    (fun s _ hf => (cancel_epi (piMor S M N)).mp (hf.trans (descFac S M N s).symm))

end RelativeTensorCoequalizer

/-! ## Project-local Mathlib supplement — presheaf promotion of the coequalizer (Step 1)

The objectwise coequalizer `RelativeTensorCoequalizer.isColimitCofork` exhibits, for a fixed
open `U`, the relative tensor `Γ(U,P) ⊗_{R(U)} Γ(U,Q)` as a coequalizer of the two
`R(U)`-action maps on `Γ(U,P) ⊗_ℤ R(U) ⊗_ℤ Γ(U,Q) ⇉ Γ(U,P) ⊗_ℤ Γ(U,Q)`.  To promote this
to the functor category `(Opens X)ᵒᵖ ⥤ Ab` (where colimits are computed objectwise, via
`CategoryTheory.Limits.evaluationJointlyReflectsColimits`) one first needs the two **domain
presheaves of the cofork as honest functors**, whose restriction maps are the `ℤ`-tensors of
the underlying restriction maps.  This section builds the first of those two functors
(`relTensorDomainPresheaf`, the `Γ(-,P) ⊗_ℤ Γ(-,Q)` presheaf); it is the concrete Step-1 brick
of `lem:relativeTensor_as_coequalizer` (`relativeTensorCoequalizerIso`).

See the handoff note at the end of the file for the verified recipe for the remaining pieces
(triple-tensor presheaf, the natural action/projection transformations, the colimit lift, and
the apex identification) and the heartbeat/coercion friction points that must be budgeted. -/

open scoped TensorProduct

/-- Restriction map for a presheaf of modules with syntactic `↥(P.obj U)` carriers.
The underlying function is `(P.presheaf.map f).hom`; the type annotation forces the
domain/codomain to print as `↥(P.obj U)` / `↥(P.obj V)` (not `↥((P.presheaf).obj U)`,
which are rfl-defeq but syntactically distinct).  The syntactic agreement is the
load-bearing ingredient for `TensorProduct.map_tmul` unification in
`relTensorActL.naturality` / `relTensorActR.naturality`. -/
private noncomputable def objRestrict (P : X.PresheafOfModules)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (f : U ⟶ V) :
    ↥(P.obj U) →ₗ[ℤ] ↥(P.obj V) :=
  (show ↥(P.obj U) →+ ↥(P.obj V) from
    { toFun := (P.presheaf.map f).hom
      map_zero' := map_zero (P.presheaf.map f).hom
      map_add' := map_add (P.presheaf.map f).hom }).toIntLinearMap

@[simp] private lemma objRestrict_apply (P : X.PresheafOfModules)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (f : U ⟶ V) (x : ↥(P.obj U)) :
    objRestrict P f x = (P.presheaf.map f).hom x := rfl

/-- Identity law for the syntactic-carrier restriction: `objRestrict P (𝟙 U) = id`. -/
private lemma objRestrict_id (P : X.PresheafOfModules) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    objRestrict P (𝟙 U) = LinearMap.id := by
  ext x
  simp only [objRestrict_apply, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
    AddMonoidHom.id_apply, LinearMap.id_coe, id_eq]

/-- Composition law for the syntactic-carrier restriction:
`objRestrict P (f ≫ g) = (objRestrict P g) ∘ (objRestrict P f)`. -/
private lemma objRestrict_comp (P : X.PresheafOfModules)
    {U V W : (TopologicalSpace.Opens X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    objRestrict P (f ≫ g) = (objRestrict P g).comp (objRestrict P f) := by
  ext x
  simp only [objRestrict_apply, CategoryTheory.Functor.map_comp, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.comp_apply]

/-- The objectwise `ℤ`-tensor presheaf `U ↦ Γ(U,P) ⊗_ℤ Γ(U,Q)` of two presheaves of modules
over a scheme, as a functor into abelian groups, with restriction maps the `ℤ`-tensors of the
two underlying restriction maps.  This is the codomain (apex-adjacent) presheaf of the cofork
in the presheaf promotion of `RelativeTensorCoequalizer.isColimitCofork`; it is the concrete
Step-1 brick of the presheaf-level coequalizer iso `relativeTensorCoequalizerIso`
(`lem:relativeTensor_as_coequalizer`).  Project-local: no objectwise `ℤ`-tensor of
abelian-group presheaves is provided by Mathlib (`AddCommGrpCat` carries no monoidal
structure in the current pin). -/
noncomputable def relTensorDomainPresheaf (P Q : X.PresheafOfModules) :
    (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (P.obj U ⊗[ℤ] Q.obj U)
  map {U V} f := AddCommGrpCat.ofHom
    (TensorProduct.map (objRestrict P f) (objRestrict Q f)).toAddMonoidHom
  map_id U := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [AddCommGrpCat.hom_ofHom, LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
        objRestrict_apply, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  map_comp {U V W} f g := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [AddCommGrpCat.hom_ofHom, LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
        objRestrict_apply, CategoryTheory.Functor.map_comp,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The objectwise `ℤ`-tensor triple presheaf `U ↦ Γ(U,P) ⊗_ℤ (𝒪_X(U) ⊗_ℤ Γ(U,Q))` of two
presheaves of modules over a scheme, as a functor into abelian groups, with restriction maps the
`ℤ`-tensors of the underlying restriction maps (the middle factor restricting via the ring
restriction map of `𝒪_X`).  This is the **domain** row of the relative-tensor coequalizer
presentation (`lem:relativeTensor_as_coequalizer`); objectwise it is the triple tensor on which
the two `R(U)`-action maps `RelativeTensorCoequalizer.actLmap`/`actRmap` act.  Project-local: no
objectwise `ℤ`-tensor of abelian-group presheaves is provided by Mathlib. -/
noncomputable def relTensorTriplePresheaf (P Q : X.PresheafOfModules) :
    (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (P.obj U ⊗[ℤ] (X.sheaf.obj.obj U ⊗[ℤ] Q.obj U))
  map {U V} f := AddCommGrpCat.ofHom
    (TensorProduct.map (objRestrict P f)
      (TensorProduct.map (X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap
        (objRestrict Q f))).toAddMonoidHom
  map_id U := by
    have hR : (X.sheaf.obj.map (𝟙 U)).hom.toAddMonoidHom.toIntLinearMap =
        LinearMap.id (R := ℤ) (M := ↥(X.sheaf.obj.obj U)) := by
      ext s
      simp only [CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_toIntLinearMap, LinearMap.id_coe, id_eq]
      rfl
    rw [objRestrict_id P U, objRestrict_id Q U, hR, TensorProduct.map_id, TensorProduct.map_id]
    rfl
  map_comp {U V W} f g := by
    have hR : (X.sheaf.obj.map (f ≫ g)).hom.toAddMonoidHom.toIntLinearMap =
        ((X.sheaf.obj.map g).hom.toAddMonoidHom.toIntLinearMap).comp
          ((X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap) := by
      ext s
      simp only [CategoryTheory.Functor.map_comp, CommRingCat.hom_comp,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_toIntLinearMap, LinearMap.coe_comp,
        Function.comp_apply]
      rfl
    rw [objRestrict_comp P f g, objRestrict_comp Q f g, hR, TensorProduct.map_comp,
      TensorProduct.map_comp]
    rfl

/-- The **left-action** natural transformation of the coequalizer rows
(`def:relTensorActL`): `relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q`, whose
component at `U` is the objectwise left-action map
`RelativeTensorCoequalizer.actLmap` collapsing the middle ring factor through the scalar
action of `𝒪_X(U)` on `Γ(U,P)`, `m ⊗ (s ⊗ n) ↦ (s • m) ⊗ n`.  Naturality in `U` is the
compatibility of the module action with the restriction maps, checked on elementary tensors
by `⊗`-induction (the single fact `PresheafOfModules.map_smul`, bridged to the abelian
restriction by `objRestrict_apply`). -/
noncomputable def relTensorActL (P Q : X.PresheafOfModules) :
    relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q where
  app U := AddCommGrpCat.ofHom
    (RelativeTensorCoequalizer.actLmap (X.sheaf.obj.obj U) (P.obj U) (Q.obj U)).toAddMonoidHom
  naturality {U V} f := by
    -- The underlying ℤ-linear naturality square, proven by `⊗`-induction.  The single
    -- mathematical fact is `PresheafOfModules.map_smul` (semilinearity of the restriction).
    have key :
        (RelativeTensorCoequalizer.actLmap (↥(X.sheaf.obj.obj V)) (↥(P.obj V)) (↥(Q.obj V))).comp
            (TensorProduct.map (objRestrict P f)
              (TensorProduct.map (X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap
                (objRestrict Q f)))
          = (TensorProduct.map (objRestrict P f) (objRestrict Q f)).comp
              (RelativeTensorCoequalizer.actLmap (↥(X.sheaf.obj.obj U)) (↥(P.obj U))
                (↥(Q.obj U))) := by
      apply TensorProduct.ext'
      intro m y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s n =>
        change ((X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap s • objRestrict P f m)
              ⊗ₜ[ℤ] objRestrict Q f n
            = objRestrict P f (s • m) ⊗ₜ[ℤ] objRestrict Q f n
        congr 1
        rw [objRestrict_apply, objRestrict_apply]
        exact (PresheafOfModules.map_smul P f s m).symm
      | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.tmul_add]
    -- Transport the linear-map square to the categorical naturality square in `Ab`.
    apply AddCommGrpCat.hom_ext
    dsimp only [relTensorTriplePresheaf, relTensorDomainPresheaf]
    ext z
    have hz := LinearMap.congr_fun key z
    simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply] using hz

/-- The **right-action** natural transformation of the coequalizer rows
(`def:relTensorActR`): `relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q`, whose
component at `U` is the objectwise right-action map
`RelativeTensorCoequalizer.actRmap` collapsing the middle ring factor through the scalar
action of `𝒪_X(U)` on `Γ(U,Q)`, `m ⊗ (s ⊗ n) ↦ m ⊗ (s • n)`.  Naturality is the
compatibility of the module action with the restriction maps (`PresheafOfModules.map_smul`
on `Q`), checked on elementary tensors by `⊗`-induction. -/
noncomputable def relTensorActR (P Q : X.PresheafOfModules) :
    relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q where
  app U := AddCommGrpCat.ofHom
    (RelativeTensorCoequalizer.actRmap (X.sheaf.obj.obj U) (P.obj U) (Q.obj U)).toAddMonoidHom
  naturality {U V} f := by
    have key :
        (RelativeTensorCoequalizer.actRmap (↥(X.sheaf.obj.obj V)) (↥(P.obj V)) (↥(Q.obj V))).comp
            (TensorProduct.map (objRestrict P f)
              (TensorProduct.map (X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap
                (objRestrict Q f)))
          = (TensorProduct.map (objRestrict P f) (objRestrict Q f)).comp
              (RelativeTensorCoequalizer.actRmap (↥(X.sheaf.obj.obj U)) (↥(P.obj U))
                (↥(Q.obj U))) := by
      apply TensorProduct.ext'
      intro m y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s n =>
        change objRestrict P f m
              ⊗ₜ[ℤ] ((X.sheaf.obj.map f).hom.toAddMonoidHom.toIntLinearMap s • objRestrict Q f n)
            = objRestrict P f m ⊗ₜ[ℤ] objRestrict Q f (s • n)
        congr 1
        rw [objRestrict_apply, objRestrict_apply]
        exact (PresheafOfModules.map_smul Q f s n).symm
      | add a b ha hb => simp only [map_add, ha, hb, TensorProduct.tmul_add]
    apply AddCommGrpCat.hom_ext
    dsimp only [relTensorTriplePresheaf, relTensorDomainPresheaf]
    ext z
    have hz := LinearMap.congr_fun key z
    simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply] using hz

/-- The **projection** natural transformation (`relTensorProj`):
`relTensorDomainPresheaf P Q ⟶ (toPresheaf).obj (P ⊗_p Q)`, whose component at `U` is the
canonical quotient `RelativeTensorCoequalizer.projL` from the objectwise `ℤ`-tensor onto the
relative tensor `Γ(U,P) ⊗_{𝒪_X(U)} Γ(U,Q)` (the apex of the cofork, identified with the value of
the presheaf monoidal tensor by `PresheafOfModules.Monoidal.tensorObj_obj`).  This is the cofork
map of the presheaf-level coequalizer presentation `relativeTensorCoequalizerIso`. -/
noncomputable def relTensorProj (P Q : X.PresheafOfModules) :
    relTensorDomainPresheaf P Q ⟶
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q) where
  app U := AddCommGrpCat.ofHom
    (RelativeTensorCoequalizer.projL (X.sheaf.obj.obj U) (P.obj U) (Q.obj U)).toAddMonoidHom
  naturality {U V} f := by
    -- NATURALITY (the square `projL_V ∘ domain.map f = apex.map f ∘ projL_U`).  We prove the
    -- underlying `ℤ`-linear square as `key` and transport it to the categorical square in `Ab`.
    -- An element-level `⊗`-induction at the `Ab` level is blocked by the `AddCommGrpCat.of` carrier
    -- instance mismatch (`map_add` fails to fire on the bundled `Ab`-morphism applied to `a + b`);
    -- working with bare `ℤ`-linear maps and `TensorProduct.ext'` sidesteps it entirely.  On an
    -- elementary tensor `m ⊗ₜ n` both composites send it to
    -- `(objRestrict P f m) ⊗ₜ[R(V)] (objRestrict Q f n)` definitionally: the LHS via
    -- `TensorProduct.map`+`projL`, the RHS via `projL`+`tensorObj_map_tmul`
    -- (both `⊗ₜ`-on-the-nose).  The `S = X.sheaf.obj.obj V` vs `R.obj V` base-ring discrepancy is a
    -- `forget₂ CommRingCat RingCat`-identity, so the elementary-tensor case is `rfl` (no instance
    -- re-synthesis, since the existing goal instances are reused).
    have key :
        (RelativeTensorCoequalizer.projL (↑(X.sheaf.obj.obj V)) (↑(P.obj V)) (↑(Q.obj V))).comp
            (TensorProduct.map (objRestrict P f) (objRestrict Q f))
          = (AddCommGrpCat.Hom.hom
                (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
                  (MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q)).map
                    f)).toIntLinearMap.comp
              (RelativeTensorCoequalizer.projL (↑(X.sheaf.obj.obj U)) (↑(P.obj U))
                (↑(Q.obj U))) := by
      apply TensorProduct.ext'
      intro m n
      rfl
    apply AddCommGrpCat.hom_ext
    ext z
    have hz := LinearMap.congr_fun key z
    simpa only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap] using hz

/-- The cofork condition for the presheaf-level relative-tensor coequalizer: the left- and
right-action rows compose equally with the projection, `a_L ≫ π = a_R ≫ π`, as natural
transformations of `(Opens X)ᵒᵖ ⥤ Ab`.  Objectwise it is
`RelativeTensorCoequalizer.coeq_condition`. -/
lemma relTensorActL_proj_eq (P Q : X.PresheafOfModules) :
    relTensorActL P Q ≫ relTensorProj P Q = relTensorActR P Q ≫ relTensorProj P Q := by
  ext U : 2
  exact RelativeTensorCoequalizer.coeq_condition (X.sheaf.obj.obj U) (P.obj U) (Q.obj U)

/- Planner strategy: 3-step promotion (blueprint `lem:relativeTensor_as_coequalizer` proof):
1. OBJECTWISE — at each `U`, instantiate `RelativeTensorCoequalizer.isColimitCofork` with
   `S = O_X(U)`, `M = P(U)`, `N = Q(U)`. (API DONE axiom-clean.)
2. PROMOTE — the three objectwise families ARE `relTensorActL`/`relTensorActR`/`relTensorProj`
   (already natural). A functor-category cocone is a colimit iff every evaluation is, via
   `CategoryTheory.Limits.evaluationJointlyReflectsColimits` [Mathlib, verify with leansearch].
   NOTE (iter-063): leansearch only finds `CategoryTheory.Limits.evaluationJointlyReflectsLimits`
   (limits), not the colimit version; the colimit analogue may be
   `PresheafOfModules.evaluationJointlyReflectsColimits` or
   `CategoryTheory.Limits.combinedIsColimit` — verify before use.
3. APEX — identify the apex presheaf `U ↦ P(U) ⊗_{O_X(U)} Q(U)` with the underlying Ab-presheaf
   of `P ⊗_p Q` via `PresheafOfModules.Monoidal.tensorObj_obj` (verified in Mathlib);
   transport the colimit along it.
Reusable recipe: the `TensorProduct.ext'`→transport-to-`Ab` idiom from `relTensorProj.naturality`
is the carrier-bookkeeping pattern. `(P ⊗ Q)` in a fresh `have` must be written
`MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q` (bare `⊗` re-resolves to TensorProduct).
-/
/-- The underlying abelian-group presheaf of the presheaf-level relative tensor product
`P ⊗_p Q` is the coequalizer, in the functor category `(Opens X)ᵒᵖ ⥤ Ab`, of the parallel pair
`relTensorActL P Q` / `relTensorActR P Q` with cofork leg `relTensorProj P Q`.  This is the
presheaf-level promotion of `RelativeTensorCoequalizer.isColimitCofork` (the objectwise content of
`lem:relativeTensor_as_coequalizer`): colimits in a functor category are computed objectwise, so
the objectwise coequalizer at each `U` promotes to a coequalizer in `(Opens X)ᵒᵖ ⥤ Ab`.
(`lem:relativeTensor_as_coequalizer`, `lem:evaluationJointlyReflectsColimits_mathlib`,
`lem:presheaf_tensorObj_obj_mathlib`.) -/
noncomputable def relativeTensorCoequalizerIso (P Q : X.PresheafOfModules) :
    Limits.IsColimit (Limits.Cofork.ofπ (relTensorProj P Q) (relTensorActL_proj_eq P Q)) :=
  evaluationJointlyReflectsColimits _ fun U =>
    (isColimitMapCoconeCoforkEquiv ((evaluation _ _).obj U) (relTensorActL_proj_eq P Q)).symm
      (RelativeTensorCoequalizer.isColimitCofork (X.sheaf.obj.obj U) (P.obj U) (Q.obj U))

/-! ## Project-local Mathlib supplement — relative-tensor whiskering preserves `J.W`

The class `J.W` of abelian local isomorphisms is closed under right-whiskering by an
arbitrary presheaf in the **pointwise** monoidal structure on `Cᵒᵖ ⥤ A` whenever `A` is
braided monoidal closed: this is Mathlib's `GrothendieckTopology.W.whiskerRight`
(Day reflection, `CategoryTheory/Sites/Monoidal.lean`).  Two gaps separate that statement
from `ztensor_whisker_localIso`:

* `Ab` carries no (tensor) monoidal structure in Mathlib, and the `ModuleCat` monoidal
  structure insists that ring and modules live in the same universe.  We therefore work in
  `ModuleCat.{u} (ULift.{u} ℤ)` and transport `J.W` along the carrier-preserving
  equivalence `modToAb` (an equivalence is a left adjoint in both directions, hence
  preserves sheafification both ways — `W_whiskerRight_modToAb_iff`).
* the morphism in `ztensor_whisker_localIso` is the *relative*-tensor whiskering
  `f ▷ R` (over `𝒪_X`), not the `ℤ`-tensor one.  The coequalizer presentation
  `relativeTensorCoequalizerIso` exhibits its underlying abelian map as the map induced on
  coequalizers by the two `ℤ`-tensor whiskered rows (`domWhisker`, `tripWhisker`); abelian
  sheafification preserves the coequalizers and inverts the rows, hence inverts the induced
  map (`GrothendieckTopology.W_iff`).
-/

section ZTensorWhisker

open TensorProduct

/-- Promote an additive homomorphism of abelian groups to a `ULift ℤ`-linear map (any
additive map of abelian groups is `ℤ`-linear, and the `ULift ℤ`-action is the `ℤ`-action). -/
private def toULiftIntLinearMap {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (φ : M →+ N) : M →ₗ[ULift.{u} ℤ] N where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c x := by
    change φ (c.down • x) = c.down • φ x
    exact map_zsmul φ c.down x

/-- The relative tensor product over `ULift ℤ` of two abelian groups agrees with their
`ℤ`-tensor product (`TensorProduct.equivOfCompatibleSMul`); both directions send an
elementary tensor `m ⊗ₜ n` to `m ⊗ₜ n`. -/
private noncomputable def uTensorEquiv (M N : Type u) [AddCommGroup M] [AddCommGroup N] :
    (M ⊗[ULift.{u} ℤ] N) ≃ₗ[ℤ] (M ⊗[ℤ] N) :=
  TensorProduct.equivOfCompatibleSMul ℤ (ULift.{u} ℤ) ℤ M N

/-- The triple-tensor variant of `uTensorEquiv`:
`M ⊗[ULift ℤ] (S ⊗[ULift ℤ] N) ≃ M ⊗[ℤ] (S ⊗[ℤ] N)`, sending `m ⊗ₜ (s ⊗ₜ n)` to itself. -/
private noncomputable def uTripleEquiv (M S N : Type u) [AddCommGroup M] [AddCommGroup S]
    [AddCommGroup N] :
    (M ⊗[ULift.{u} ℤ] (S ⊗[ULift.{u} ℤ] N)) ≃ₗ[ℤ] (M ⊗[ℤ] (S ⊗[ℤ] N)) :=
  (uTensorEquiv M (S ⊗[ULift.{u} ℤ] N)) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl ℤ M) (uTensorEquiv S N))

/-- The presheaf of `ULift ℤ`-modules underlying a presheaf of `𝒪_X`-modules, with the
syntactic `↥(P.obj U)` carriers of `objRestrict`.  This places the underlying abelian
presheaf of `P` in a category (`Cᵒᵖ ⥤ ModuleCat (ULift ℤ)`) which Mathlib equips with a
pointwise braided monoidal-closed structure, so that
`GrothendieckTopology.W.whiskerRight` applies. -/
private noncomputable def uModPresheaf (P : X.PresheafOfModules) :
    (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ) where
  obj U := ModuleCat.of (ULift.{u} ℤ) ↥(P.obj U)
  map {U V} g := ModuleCat.ofHom (toULiftIntLinearMap (objRestrict P g).toAddMonoidHom)
  map_id U := by
    ext x
    exact LinearMap.congr_fun (objRestrict_id P U) x
  map_comp {U V W} g h := by
    ext x
    exact LinearMap.congr_fun (objRestrict_comp P g h) x

/-- The presheaf of `ULift ℤ`-modules underlying the structure sheaf of `X`. -/
private noncomputable def uModRingPresheaf (X : Scheme.{u}) :
    (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ) where
  obj U := ModuleCat.of (ULift.{u} ℤ) ↥(X.sheaf.obj.obj U)
  map {U V} g := ModuleCat.ofHom
    (toULiftIntLinearMap (X.sheaf.obj.map g).hom.toAddMonoidHom)
  map_id U := by
    ext s
    change (X.sheaf.obj.map (𝟙 U)).hom s = s
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {U V W} g h := by
    ext s
    change (X.sheaf.obj.map (g ≫ h)).hom s
      = (X.sheaf.obj.map h).hom ((X.sheaf.obj.map g).hom s)
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The morphism of `ULift ℤ`-module presheaves underlying a morphism of presheaves of
modules. -/
private noncomputable def uModHom {P Q : X.PresheafOfModules} (f : P ⟶ Q) :
    uModPresheaf P ⟶ uModPresheaf Q where
  app U := ModuleCat.ofHom (toULiftIntLinearMap (f.app U).hom.toAddMonoidHom)
  naturality {U V} g := by
    ext x
    exact PresheafOfModules.naturality_apply f g x

/-- The carrier-preserving equivalence from `ULift ℤ`-modules to abelian groups:
restriction of scalars along `ℤ ≅ ULift ℤ` followed by the standard equivalence
`ModuleCat ℤ ≌ Ab`. -/
private noncomputable def modToAb : ModuleCat.{u} (ULift.{u} ℤ) ⥤ Ab.{u} :=
  ModuleCat.restrictScalars (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom ⋙
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}

private instance : modToAb.{u}.IsEquivalence := by
  unfold modToAb
  infer_instance

/-- **`J.W` transfers along `modToAb`** (both directions).  The equivalence `modToAb` is a
left adjoint in both directions, hence preserves sheafification both ways
(`Sheaf.preservesSheafification_of_adjunction`). -/
private lemma W_whiskerRight_modToAb_iff {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)} (ψ : F ⟶ G) :
    J.W (Functor.whiskerRight ψ modToAb.{u}) ↔ J.W ψ := by
  haveI h₁ : J.PreservesSheafification modToAb.{u} :=
    Sheaf.preservesSheafification_of_adjunction J modToAb.{u}.asEquivalence.toAdjunction
  haveI h₂ : J.PreservesSheafification modToAb.{u}.asEquivalence.inverse :=
    Sheaf.preservesSheafification_of_adjunction J modToAb.{u}.asEquivalence.symm.toAdjunction
  constructor
  · intro h
    have h2 := J.W_of_preservesSheafification modToAb.{u}.asEquivalence.inverse _ h
    refine ((J.W).arrow_mk_iso_iff ?_).mp h2
    refine Arrow.isoMk
      (NatIso.ofComponents
        (fun U => modToAb.{u}.asEquivalence.unitIso.symm.app (F.obj U)) ?_)
      (NatIso.ofComponents
        (fun U => modToAb.{u}.asEquivalence.unitIso.symm.app (G.obj U)) ?_) ?_
    · intro U V g
      exact modToAb.{u}.asEquivalence.unitIso.inv.naturality (F.map g)
    · intro U V g
      exact modToAb.{u}.asEquivalence.unitIso.inv.naturality (G.map g)
    · ext U : 2
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Arrow.mk_hom]
      exact (modToAb.{u}.asEquivalence.unitIso.inv.naturality (ψ.app U)).symm
  · intro h
    exact J.W_of_preservesSheafification modToAb.{u} _ h

/-- The abelian presheaf underlying `uModPresheaf P` is the underlying abelian presheaf
of `P` (carrier-preserving comparison). -/
private noncomputable def uModForgetIso (P : X.PresheafOfModules) :
    uModPresheaf P ⋙ modToAb.{u} ≅
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj P :=
  NatIso.ofComponents
    (fun U =>
      { hom := AddCommGrpCat.ofHom
          { toFun := fun x => x
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        inv := AddCommGrpCat.ofHom
          { toFun := fun x => x
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl })
    (fun {U V} g => by
      apply AddCommGrpCat.hom_ext
      ext x
      rfl)

/-- The abelian presheaf underlying the pointwise tensor `uModPresheaf P ⊗ uModPresheaf R`
is the `ℤ`-tensor presheaf `relTensorDomainPresheaf P R` (componentwise `uTensorEquiv`). -/
private noncomputable def uDomIso (P R : X.PresheafOfModules) :
    (MonoidalCategory.tensorObj (uModPresheaf P) (uModPresheaf R)) ⋙ modToAb.{u} ≅
      relTensorDomainPresheaf P R :=
  NatIso.ofComponents
    (fun U =>
      { hom := AddCommGrpCat.ofHom
          (uTensorEquiv ↥(P.obj U) ↥(R.obj U)).toLinearMap.toAddMonoidHom
        inv := AddCommGrpCat.ofHom
          (uTensorEquiv ↥(P.obj U) ↥(R.obj U)).symm.toLinearMap.toAddMonoidHom
        hom_inv_id := by
          ext z
          exact (uTensorEquiv ↥(P.obj U) ↥(R.obj U)).symm_apply_apply z
        inv_hom_id := by
          ext z
          exact (uTensorEquiv ↥(P.obj U) ↥(R.obj U)).apply_symm_apply z })
    (fun {U V} g => by
      apply AddCommGrpCat.hom_ext
      ext z
      induction z using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul m n => rfl
      | add a b ha hb =>
        refine ((map_add _ a b).trans ?_).trans (map_add _ a b).symm
        exact congrArg₂ (fun x y => x + y) ha hb)

set_option maxHeartbeats 800000 in
/-- The abelian presheaf underlying `uModPresheaf P ⊗ (uModRingPresheaf X ⊗ uModPresheaf R)`
is the `ℤ`-tensor triple presheaf `relTensorTriplePresheaf P R` (componentwise
`uTripleEquiv`). -/
private noncomputable def uTripIso (P R : X.PresheafOfModules) :
    (MonoidalCategory.tensorObj (uModPresheaf P)
        (MonoidalCategory.tensorObj (uModRingPresheaf X) (uModPresheaf R))) ⋙ modToAb.{u} ≅
      relTensorTriplePresheaf P R :=
  NatIso.ofComponents
    (fun U =>
      { hom := AddCommGrpCat.ofHom
          (uTripleEquiv ↥(P.obj U) ↥(X.sheaf.obj.obj U) ↥(R.obj U)).toLinearMap.toAddMonoidHom
        inv := AddCommGrpCat.ofHom
          (uTripleEquiv ↥(P.obj U) ↥(X.sheaf.obj.obj U)
            ↥(R.obj U)).symm.toLinearMap.toAddMonoidHom
        hom_inv_id := by
          ext z
          exact (uTripleEquiv ↥(P.obj U) ↥(X.sheaf.obj.obj U)
            ↥(R.obj U)).symm_apply_apply z
        inv_hom_id := by
          ext z
          exact (uTripleEquiv ↥(P.obj U) ↥(X.sheaf.obj.obj U)
            ↥(R.obj U)).apply_symm_apply z })
    (fun {U V} g => by
      apply AddCommGrpCat.hom_ext
      ext z
      induction z using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul m y =>
        induction y using TensorProduct.induction_on with
        | zero =>
          exact (congrArg _ (TensorProduct.tmul_zero _ m)).trans
            (((map_zero _).trans (map_zero _).symm).trans
              (congrArg _ (TensorProduct.tmul_zero _ m)).symm)
        | tmul s n => rfl
        | add a b ha hb =>
          refine (congrArg _ (TensorProduct.tmul_add m a b)).trans
            (((map_add _ _ _).trans ?_).trans
              ((map_add _ _ _).symm.trans (congrArg _ (TensorProduct.tmul_add m a b)).symm))
          exact congrArg₂ (fun x y => x + y) ha hb
      | add a b ha hb =>
        refine ((map_add _ a b).trans ?_).trans (map_add _ a b).symm
        exact congrArg₂ (fun x y => x + y) ha hb)

/-- The `ℤ`-tensor right-whiskering of `f` on the domain row, transported from the
pointwise whiskering `uModHom f ▷ uModPresheaf R` along the comparison isos. -/
private noncomputable def domWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (R : X.PresheafOfModules) :
    relTensorDomainPresheaf P R ⟶ relTensorDomainPresheaf Q R :=
  (uDomIso P R).inv ≫
    Functor.whiskerRight
      (MonoidalCategory.whiskerRight (uModHom f) (uModPresheaf R)) modToAb.{u} ≫
    (uDomIso Q R).hom

/-- The `ℤ`-tensor right-whiskering of `f` on the triple row, transported from the
pointwise whiskering `uModHom f ▷ (uModRingPresheaf X ⊗ uModPresheaf R)`. -/
private noncomputable def tripWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (R : X.PresheafOfModules) :
    relTensorTriplePresheaf P R ⟶ relTensorTriplePresheaf Q R :=
  (uTripIso P R).inv ≫
    Functor.whiskerRight
      (MonoidalCategory.whiskerRight (uModHom f)
        (MonoidalCategory.tensorObj (uModRingPresheaf X) (uModPresheaf R))) modToAb.{u} ≫
    (uTripIso Q R).hom

/-- `uModHom f` is a local isomorphism whenever the underlying abelian map of `f` is. -/
private lemma W_uModHom {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (hf : (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)) :
    (opensTopology X).W (uModHom f) := by
  rw [← W_whiskerRight_modToAb_iff]
  refine (((opensTopology X).W).arrow_mk_iso_iff
    (Arrow.isoMk (uModForgetIso P) (uModForgetIso Q) ?_)).mpr hf
  ext U : 2
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

/-- The whiskered domain row is a local isomorphism (`W.whiskerRight` over
`ModuleCat (ULift ℤ)`, transported). -/
private lemma W_domWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (hf : (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))
    (R : X.PresheafOfModules) :
    (opensTopology X).W (domWhisker f R) := by
  have h1 : (opensTopology X).W
      (MonoidalCategory.whiskerRight (uModHom f) (uModPresheaf R)) :=
    (W_uModHom f hf).whiskerRight _
  have h2 := (W_whiskerRight_modToAb_iff (opensTopology X) _).mpr h1
  refine (((opensTopology X).W).arrow_mk_iso_iff
    (Arrow.isoMk (uDomIso P R) (uDomIso Q R) ?_)).mp h2
  show (uDomIso P R).hom ≫ domWhisker f R
    = Functor.whiskerRight (MonoidalCategory.whiskerRight (uModHom f) (uModPresheaf R))
        modToAb.{u} ≫ (uDomIso Q R).hom
  exact (uDomIso P R).hom_inv_id_assoc _

/-- The whiskered triple row is a local isomorphism. -/
private lemma W_tripWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (hf : (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))
    (R : X.PresheafOfModules) :
    (opensTopology X).W (tripWhisker f R) := by
  have h1 : (opensTopology X).W
      (MonoidalCategory.whiskerRight (uModHom f)
        (MonoidalCategory.tensorObj (uModRingPresheaf X) (uModPresheaf R))) :=
    (W_uModHom f hf).whiskerRight _
  have h2 := (W_whiskerRight_modToAb_iff (opensTopology X) _).mpr h1
  refine (((opensTopology X).W).arrow_mk_iso_iff
    (Arrow.isoMk (uTripIso P R) (uTripIso Q R) ?_)).mp h2
  show (uTripIso P R).hom ≫ tripWhisker f R
    = Functor.whiskerRight
        (MonoidalCategory.whiskerRight (uModHom f)
          (MonoidalCategory.tensorObj (uModRingPresheaf X) (uModPresheaf R))) modToAb.{u} ≫
      (uTripIso Q R).hom
  exact (uTripIso P R).hom_inv_id_assoc _

/-- The whiskered rows commute with the left-action transformation. -/
private lemma actL_domWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (R : X.PresheafOfModules) :
    relTensorActL P R ≫ domWhisker f R = tripWhisker f R ≫ relTensorActL Q R := by
  ext U : 2
  apply AddCommGrpCat.hom_ext
  ext z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul m y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (TensorProduct.tmul_zero _ m)).trans
        (((map_zero _).trans (map_zero _).symm).trans
          (congrArg _ (TensorProduct.tmul_zero _ m)).symm)
    | tmul s n =>
      have t1 : (AddCommGrpCat.Hom.hom ((relTensorActL P R).app U))
          (m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n)) = (s • m) ⊗ₜ[ℤ] n := rfl
      have t2 : (AddCommGrpCat.Hom.hom ((domWhisker f R).app U)) ((s • m) ⊗ₜ[ℤ] n)
          = (ConcreteCategory.hom (f.app U)) (s • m) ⊗ₜ[ℤ] n := rfl
      have t3 : (AddCommGrpCat.Hom.hom ((tripWhisker f R).app U))
          (m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n))
          = (ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n) := rfl
      have t4 : (AddCommGrpCat.Hom.hom ((relTensorActL Q R).app U))
          ((ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n))
          = (s • (ConcreteCategory.hom (f.app U)) m) ⊗ₜ[ℤ] n := rfl
      have key : (ConcreteCategory.hom (f.app U)) (s • m)
          = s • (ConcreteCategory.hom (f.app U)) m :=
        _root_.map_smul (ModuleCat.Hom.hom (f.app U)) s m
      exact (((congrArg (AddCommGrpCat.Hom.hom ((domWhisker f R).app U)) t1).trans
        t2).trans (congrArg (fun w => w ⊗ₜ[ℤ] n) key)).trans
        (((congrArg (AddCommGrpCat.Hom.hom ((relTensorActL Q R).app U)) t3).trans t4).symm)
    | add a b ha hb =>
      refine (congrArg _ (TensorProduct.tmul_add m a b)).trans
        (((map_add _ _ _).trans ?_).trans
          ((map_add _ _ _).symm.trans (congrArg _ (TensorProduct.tmul_add m a b)).symm))
      exact congrArg₂ (fun x y => x + y) ha hb
  | add a b ha hb =>
    refine ((map_add _ a b).trans ?_).trans (map_add _ a b).symm
    exact congrArg₂ (fun x y => x + y) ha hb

/-- The whiskered rows commute with the right-action transformation. -/
private lemma actR_domWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (R : X.PresheafOfModules) :
    relTensorActR P R ≫ domWhisker f R = tripWhisker f R ≫ relTensorActR Q R := by
  ext U : 2
  apply AddCommGrpCat.hom_ext
  ext z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul m y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (TensorProduct.tmul_zero _ m)).trans
        (((map_zero _).trans (map_zero _).symm).trans
          (congrArg _ (TensorProduct.tmul_zero _ m)).symm)
    | tmul s n =>
      have t1 : (AddCommGrpCat.Hom.hom ((relTensorActR P R).app U))
          (m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n)) = m ⊗ₜ[ℤ] (s • n) := rfl
      have t2 : (AddCommGrpCat.Hom.hom ((domWhisker f R).app U)) (m ⊗ₜ[ℤ] (s • n))
          = (ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s • n) := rfl
      have t3 : (AddCommGrpCat.Hom.hom ((tripWhisker f R).app U))
          (m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n))
          = (ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n) := rfl
      have t4 : (AddCommGrpCat.Hom.hom ((relTensorActR Q R).app U))
          ((ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s ⊗ₜ[ℤ] n))
          = (ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] (s • n) := rfl
      exact ((congrArg (AddCommGrpCat.Hom.hom ((domWhisker f R).app U)) t1).trans
        t2).trans
        (((congrArg (AddCommGrpCat.Hom.hom ((relTensorActR Q R).app U)) t3).trans t4).symm)
    | add a b ha hb =>
      refine (congrArg _ (TensorProduct.tmul_add m a b)).trans
        (((map_add _ _ _).trans ?_).trans
          ((map_add _ _ _).symm.trans (congrArg _ (TensorProduct.tmul_add m a b)).symm))
      exact congrArg₂ (fun x y => x + y) ha hb
  | add a b ha hb =>
    refine ((map_add _ a b).trans ?_).trans (map_add _ a b).symm
    exact congrArg₂ (fun x y => x + y) ha hb

/-- The whiskered domain row covers the relative-tensor whiskering through the
coequalizer projections. -/
private lemma proj_domWhisker {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (R : X.PresheafOfModules) :
    domWhisker f R ≫ relTensorProj Q R =
      relTensorProj P R ≫ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) f R) := by
  ext U : 2
  apply AddCommGrpCat.hom_ext
  ext z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul m n =>
    have t1 : (AddCommGrpCat.Hom.hom ((domWhisker f R).app U)) (m ⊗ₜ[ℤ] n)
        = (ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] n := rfl
    have t2 : (AddCommGrpCat.Hom.hom ((relTensorProj Q R).app U))
        ((ConcreteCategory.hom (f.app U)) m ⊗ₜ[ℤ] n)
        = (AddCommGrpCat.Hom.hom ((relTensorProj P R ≫
            (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
              (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) f R)).app U))
          (m ⊗ₜ[ℤ] n) := rfl
    exact (congrArg (AddCommGrpCat.Hom.hom ((relTensorProj Q R).app U)) t1).trans t2
  | add a b ha hb =>
    refine ((map_add _ a b).trans ?_).trans (map_add _ a b).symm
    exact congrArg₂ (fun x y => x + y) ha hb

end ZTensorWhisker

/-- **A ℤ-whiskered stalkwise isomorphism is a local isomorphism** (`lem:snap_ztensor_whisker_localIso`).
Let `f : P ⟶ Q` be a morphism of presheaves of `𝒪_X`-modules such that the underlying
abelian-presheaf morphism `(toPresheaf _).map f` lies in the weak-equivalence class `J.W`
of the opens topology on `X` (i.e., `f` is a stalkwise isomorphism of abelian-group
presheaves). Then for any presheaf of modules `R`, the underlying abelian morphism of the
right-whiskered map `f ▷ R : P ⊗_p R ⟶ Q ⊗_p R` (in the presheaf monoidal structure
`PresheafOfModules.monoidalCategory`) is again a stalkwise isomorphism, hence lies in `J.W`.

Proof route (actual — NOT the stalk route): present the underlying abelian presheaf of
`P ⊗_p R` as the coequalizer of the two `𝒪`-action rows (`relativeTensorCoequalizerIso`);
abelian sheafification `a = presheafToSheaf J Ab` is a left adjoint, so it preserves this
coequalizer.  The whiskered rows `tripWhisker f R` / `domWhisker f R` lie in `J.W` by
`W_tripWhisker` / `W_domWhisker` (the ULift/`W.whiskerRight` transfer at
`ModuleCat (ULift ℤ)`), so `a` inverts them; the induced map of coequalizer points —
which is `a.map` of our morphism — is then an isomorphism, i.e. the morphism lies in
`J.W` by `GrothendieckTopology.W_iff`. -/
lemma ztensor_whisker_localIso {P Q : X.PresheafOfModules}
    (f : P ⟶ Q)
    (hf : (opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f))
    (R : X.PresheafOfModules) :
    (opensTopology X).W
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) f R)) := by
  -- Apply the abelian sheafification functor `a` to the coequalizer presentations of
  -- `P ⊗_p R` and `Q ⊗_p R` (`relativeTensorCoequalizerIso`); the whiskered rows
  -- `tripWhisker`/`domWhisker` become isomorphisms (they lie in `J.W`), so the induced
  -- map of coequalizer points — which is `a.map` of our morphism — is an isomorphism.
  have hWdom : (opensTopology X).W (domWhisker f R) := W_domWhisker f hf R
  have hWtrip : (opensTopology X).W (tripWhisker f R) := W_tripWhisker f hf R
  rw [GrothendieckTopology.W_iff]
  set a := presheafToSheaf (opensTopology X) Ab.{u} with ha
  have hcP := Limits.isColimitOfPreserves a (relativeTensorCoequalizerIso P R)
  have hcQ := Limits.isColimitOfPreserves a (relativeTensorCoequalizerIso Q R)
  -- the morphism of parallel pairs given by the whiskered rows
  let β : Limits.parallelPair (relTensorActL P R) (relTensorActR P R) ⟶
      Limits.parallelPair (relTensorActL Q R) (relTensorActR Q R) :=
    Limits.parallelPairHom (relTensorActL P R) (relTensorActR P R)
      (relTensorActL Q R) (relTensorActR Q R) (tripWhisker f R) (domWhisker f R)
      (actL_domWhisker f R) (actR_domWhisker f R)
  have hβ : ∀ j, IsIso ((Functor.whiskerRight β a).app j) := by
    rintro (_ | _)
    · show IsIso (a.map (β.app Limits.WalkingParallelPair.zero))
      rw [show β.app Limits.WalkingParallelPair.zero = tripWhisker f R from
        Limits.parallelPairHom_app_zero ..]
      exact ((opensTopology X).W_iff _).mp hWtrip
    · show IsIso (a.map (β.app Limits.WalkingParallelPair.one))
      rw [show β.app Limits.WalkingParallelPair.one = domWhisker f R from
        Limits.parallelPairHom_app_one ..]
      exact ((opensTopology X).W_iff _).mp hWdom
  haveI : IsIso (Functor.whiskerRight β a) :=
    NatIso.isIso_of_isIso_app _
  -- the induced map of cocone points is `a.map` of our morphism …
  have hmap : hcP.map
      (a.mapCocone (Limits.Cofork.ofπ (relTensorProj Q R) (relTensorActL_proj_eq Q R)))
      (Functor.whiskerRight β a)
      = a.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) f R)) := by
    apply hcP.hom_ext
    intro j
    rw [Limits.IsColimit.ι_map]
    have hone :
        (Functor.whiskerRight β a).app Limits.WalkingParallelPair.one ≫
          (a.mapCocone (Limits.Cofork.ofπ (relTensorProj Q R)
            (relTensorActL_proj_eq Q R))).ι.app Limits.WalkingParallelPair.one
        = (a.mapCocone (Limits.Cofork.ofπ (relTensorProj P R)
            (relTensorActL_proj_eq P R))).ι.app Limits.WalkingParallelPair.one ≫
          a.map ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
            (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) f R)) := by
      show a.map (β.app Limits.WalkingParallelPair.one) ≫ a.map (relTensorProj Q R)
        = a.map (relTensorProj P R) ≫ a.map _
      rw [show β.app Limits.WalkingParallelPair.one = domWhisker f R from
        Limits.parallelPairHom_app_one .., ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun t => a.map t) (proj_domWhisker f R)
    match j with
    | Limits.WalkingParallelPair.one => exact hone
    | Limits.WalkingParallelPair.zero =>
      have wP := (a.mapCocone (Limits.Cofork.ofπ (relTensorProj P R)
        (relTensorActL_proj_eq P R))).w Limits.WalkingParallelPairHom.left
      have wQ := (a.mapCocone (Limits.Cofork.ofπ (relTensorProj Q R)
        (relTensorActL_proj_eq Q R))).w Limits.WalkingParallelPairHom.left
      rw [← wP, ← wQ]
      refine (CategoryTheory.Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun w => w ≫ _)
        ((Functor.whiskerRight β a).naturality
          Limits.WalkingParallelPairHom.left).symm).trans ?_
      refine (CategoryTheory.Category.assoc _ _ _).trans ?_
      refine (congrArg (fun w => _ ≫ w) hone).trans ?_
      exact (CategoryTheory.Category.assoc _ _ _).symm
  rw [← hmap,
    show hcP.map
      (a.mapCocone (Limits.Cofork.ofπ (relTensorProj Q R) (relTensorActL_proj_eq Q R)))
      (Functor.whiskerRight β a)
      = (Limits.IsColimit.coconePointsIsoOfNatIso hcP hcQ
          (asIso (Functor.whiskerRight β a))).hom by simp]
  infer_instance

/- Planner strategy: 4-step proof (blueprint `lem:isIso_sheafification_whiskerRight_unit`):

Step 1 (LOCALIZATION CRITERION). Apply `isIso_sheafification_map_iff` to reduce the goal
    `IsIso (sheafification.map (η_P ▷ Q))`
to the purely abelian statement
    `(opensTopology X).W ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (η_P ▷ Q))`.

Step 2 (COEQUALIZER PRESENTATION). The underlying abelian-group presheaf of `P ⊗_p Q` is
the coequalizer of `relTensorActL P Q` / `relTensorActR P Q` with cofork leg `relTensorProj P Q`
in `(Opens X)ᵒᵖ ⥤ Ab`. This is `relativeTensorCoequalizerIso P Q` (the `IsColimit` of the
cofork), axiom-clean in-file. Abelian sheafification (`presheafToSheaf J Ab`) is a left adjoint
and therefore preserves this coequalizer.

Step 3 (WHISKERED UNITS IN J.W). The morphism `(toPresheaf _).map (η_P ▷ Q)` is the coequalizer
map induced by the ℤ-whiskerings `η_{P,ab} ⊗_ℤ id_Q` and `η_{P,ab} ⊗_ℤ id_{R₀ ⊗_ℤ Q}` on both
rows of the parallel pair (by the objectwise formula `PresheafOfModules.Monoidal.tensorObj_obj`).
By `localIso_toPresheaf_map_unit`, the underlying abelian map `η_{P,ab}` lies in `J.W`. Apply
`ztensor_whisker_localIso` to each row to conclude both whiskered maps lie in `J.W`. A morphism
of parallel pairs lying in `J.W` induces a `J.W`-morphism on coequalizers (sheafification
preserves coequalizers and turns them into isomorphisms).

Step 4 (CLOSING). Fed back through `(isIso_sheafification_map_iff _).mpr`, this closes the
original `IsIso` goal.

KEY MATHLIB REFERENCES (verified by planner):
- `CategoryTheory.Limits.evaluationJointlyReflectsColimits` EXISTS at
  `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean:103`; fallback
  `combinedIsColimit` same file L145.
- `relativeTensorCoequalizerIso` and the full `RelativeTensorCoequalizer` 22-decl API
  are DONE axiom-clean in-file (closed iter-053).
- The abelian-group category in this file is `AddCommGrpCat`, NOT `AddCommGrp`. Any fresh
  `have` about `P ⊗ Q` must spell
  `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`.
- `ztensor_whisker_localIso` (the declaration immediately above) closes the stalkwise-iso
  ingredient for each whiskered row.
-/
/-- **Sheafification inverts the whiskered localization unit** (`lem:isIso_sheafification_whiskerRight_unit`).
For presheaves of `𝒪_X`-modules `P` and `Q`, let `η_P : P ⟶ P^#` be the unit of the
sheafification adjunction (here `P^# = (toPresheafOfModules X).obj (sheafification.obj P)`).
The sheafification of the right-whiskered map `η_P ▷ Q : P ⊗_p Q ⟶ P^# ⊗_p Q` (in the
presheaf monoidal structure), namely
  `(η_P ▷ Q)^# : (P ⊗_p Q)^# ⟶ (P^# ⊗_p Q)^#`,
is an isomorphism of sheaves of modules. This is the strong-monoidality comparison of the
module sheafification functor on a whiskered unit; it is the key brick for the sheaf-level
associator (`cor:sheafTensorObjAssoc`) and the `tensorPowAdd` comparison. -/
lemma isIso_sheafification_whiskerRight_unit (P Q : X.PresheafOfModules) :
    IsIso (sheafification.map
      (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) Q)) :=
  (isIso_sheafification_map_iff _).mpr
    (ztensor_whisker_localIso _ (localIso_toPresheaf_map_unit P) Q)

/-! ## Associativity and tensor-power comparison (`cor:sheafTensorObjAssoc`, `lem:sheafTensorPow_add`)

These are the next SNAP chain targets after the crux `isIso_sheafification_whiskerRight_unit`
(closed axiom-clean, iter-066).  Both are now constructed (iter-078) following the planner
strategy comments below, which document the construction route. -/

/- Planner strategy for `tensorObjAssoc` (`cor:sheafTensorObjAssoc`, blueprint L1069–L1126):

SETUP: write a = (toPresheafOfModules X).obj A, b = ..., c = ...,
  unit_app P := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P.
  The two iterated sheaf tensors unfold as:
    (A ⊗ B) ⊗ C  =  ((a ⊗_p b)^# ⊗_p c)^#  =  tensorObj (tensorObj A B) C
    A ⊗ (B ⊗ C)  =  (a ⊗_p (b ⊗_p c)^#)^#  =  tensorObj A (tensorObj B C)
  (Here (-)^# = sheafification.obj, ⊗_p = MonoidalCategory.tensorObj (C := MonoidalPresheaf X).)

THREE-SEGMENT COMPOSITE:
  Segment 1 — INVERSE WHISKERED UNIT on the left factor:
    `isIso_sheafification_whiskerRight_unit (a ⊗_p b) c` gives
        IsIso of sheafification.map (whiskerRight (unit_app (a ⊗_p b)) c),
    a map  ((a ⊗_p b) ⊗_p c)^# ⟶ ((a ⊗_p b)^# ⊗_p c)^# = (A ⊗ B) ⊗ C.
    Take `.symm` of `asIso (...)` : (A⊗B)⊗C ≅ ((a⊗b) ⊗_p c)^#.

  Segment 2 — PRESHEAF ASSOCIATOR under sheafification:
    `sheafification.mapIso (MonoidalCategory.associator (C := MonoidalPresheaf X) a b c)`
    gives  ((a ⊗_p b) ⊗_p c)^# ≅ (a ⊗_p (b ⊗_p c))^#.

  Segment 3 — WHISKERED UNIT on the right factor (via presheaf braiding):
    Apply `isIso_sheafification_whiskerRight_unit (b ⊗_p c) a` to get
        IsIso of  ((b ⊗_p c) ⊗_p a)^# ⟶ ((b ⊗_p c)^# ⊗_p a)^#.
    Conjugate with the presheaf braiding isos:
        `sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X) a (b ⊗_p c))`
    then the whiskered-unit iso then
        `sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X) ((toPresheafOfModules X).obj (tensorObj B C)) a)`
    to land in (a ⊗_p (b ⊗_p c)^#)^# = A ⊗ (B ⊗ C).
    Alternatively, use `MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X) a` version
    if it exists, bypassing the braiding conjugation.

  Full composite (pseudocode):
    (asIso (sheafification.map (whiskerRight (unit_app (a ⊗_p b)) c))).symm   -- seg 1
    ≪≫ sheafification.mapIso (associator (C := MonoidalPresheaf X) a b c)      -- seg 2
    ≪≫ (braiding_conjugate of asIso(whiskerRight (unit_app (b ⊗_p c)) a))     -- seg 3

CARRIER IDIOMS (load-bearing, iter-066):
  • Abelian-group category = AddCommGrpCat, NOT AddCommGrp.
  • Any fresh `have` for P ⊗ Q must write
        MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q
    (bare `⊗` re-resolves to TensorProduct and fails to elaborate).
  • simp/rw CANNOT fire under the functor-composition diamond; use defeq-tolerant term-mode
    congruence: `congrArg`, `.trans`, `Iso.ext`, `(exact fstar_reindex)`-style proofs.
  • `set_option maxHeartbeats N in` must precede the docstring, not sit between it and the decl.
  • `whiskerRight` = `MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)`.
  • `unit.app P` = `(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P`.
  • All three sheafification isos are already `asIso`-eligible; no additional instance synthesis.
-/
/-! ## Project-local Mathlib supplement — symmetric monoidal coherence by localization transfer

Following `blueprint/src/chapters/Picard_SectionGradedRing.tex`, `sec:sgr_localized_monoidal`:
`X.Modules` is the localization of `PshMod(𝒪_X)` at the class `W` inverted by sheafification,
and Mathlib's `CategoryTheory.Localization.Monoidal.LocalizedMonoidal L W ε` equips that
localization with a symmetric monoidal structure for free (pentagon/triangle/hexagon), provided
`W` is a *monoidal* morphism class.  We discharge that single precondition (`W_isMonoidal`) and
instantiate the synonym (`modulesLocalizedMonoidal`).

The monoidal structure on the presheaf side `PresheafOfModules X.ringCatSheaf.obj` is only found
by instance resolution under the syntactic form `MonoidalPresheaf X`
(`= PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)`, definitionally equal); we
therefore phrase the localization data with the domain ascribed to `MonoidalPresheaf X`. -/

/-- A morphism property `W` on a braided monoidal category is monoidal as soon as it is
multiplicative, respects isomorphisms, and is stable under right whiskering: left-whiskering
stability follows by conjugating with the braiding (`X ◁ g = β ≫ (g ▷ X) ≫ β⁻¹`).  Project-local:
it packages the `whiskerLeft`-from-`whiskerRight` reduction the blueprint prescribes for
`def:W_isMonoidal`. -/
private lemma isMonoidal_of_braided_whiskerRight {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (W : MorphismProperty C) [W.IsMultiplicative] [W.RespectsIso]
    (hwr : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂), W f → ∀ Y, W (MonoidalCategory.whiskerRight f Y)) :
    W.IsMonoidal where
  whiskerRight f hf Y := hwr f hf Y
  whiskerLeft X Y₁ Y₂ g hg := by
    have hn := CategoryTheory.BraidedCategory.braiding_naturality_right X g
    have heq : MonoidalCategory.whiskerLeft X g
        = (β_ X Y₁).hom ≫ (MonoidalCategory.whiskerRight g X) ≫ (β_ X Y₂).inv := by
      rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [heq]
    exact MorphismProperty.RespectsIso.precomp W (β_ X Y₁).hom _
      (MorphismProperty.RespectsIso.postcomp W (β_ X Y₂).inv _ (hwr g hg X))

/-- The presheaf symmetric monoidal structure, transported to the *syntactic* form
`PresheafOfModules X.ringCatSheaf.obj` (the domain of the module sheafification functor).  Mathlib
provides `PresheafOfModules.monoidalCategory` only for the form
`PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)` (here `MonoidalPresheaf X`), which is
*definitionally* equal but not found by instance synthesis on the bare form; this re-export makes
it synthesizable so `CategoryTheory.LocalizedMonoidal` can be instantiated on the sheafification
functor's literal domain. -/
noncomputable instance pshModMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (MonoidalPresheaf X))

/-- The presheaf braiding, transported to the syntactic bare form (see `pshModMonoidal`). -/
noncomputable instance pshModBraided :
    BraidedCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (BraidedCategory (MonoidalPresheaf X))

/-- The presheaf symmetry, transported to the syntactic bare form (see `pshModMonoidal`). -/
noncomputable instance pshModSymmetric :
    SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory (MonoidalPresheaf X))

/-- The sheafification localization class as a morphism property of the presheaf-of-modules
category: a morphism lies in `W` iff its underlying abelian-presheaf morphism is a local
isomorphism for the opens topology.  This is the class `W` of `def:W_isMonoidal`. -/
abbrev Wsheaf (X : Scheme.{u}) :
    MorphismProperty (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  (opensTopology X).W.inverseImage (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

/-- **The sheafification class is monoidal** (`def:W_isMonoidal`): the class `W` of presheaf-of-module
morphisms inverted by sheafification is multiplicative and stable under whiskering on both sides.
Right-whiskering stability is the proved `ztensor_whisker_localIso`; left-whiskering follows by
braiding conjugation (`isMonoidal_of_braided_whiskerRight`); multiplicativity and iso-respect are
inherited from the local-isomorphism class through `inverseImage`.  This is the single new
precondition for the Mathlib monoidal-localization machinery. -/
instance W_isMonoidal : (Wsheaf X).IsMonoidal :=
  isMonoidal_of_braided_whiskerRight (Wsheaf X) <| fun f hf R =>
    ztensor_whisker_localIso f hf R

/-- **Unit comparison for the localized monoidal structure** (`def:localizedMonoidalUnitIso`):
the sheafification of the presheaf monoidal unit `𝟙_(PshMod)` is the unit module `𝟙_X`.  Since the
underlying presheaf of `unitModule X` is *definitionally* the presheaf monoidal unit, this is just
the reflective sheafification counit iso.  It is the datum `ε` instantiating
`CategoryTheory.LocalizedMonoidal`. -/
noncomputable def localizedMonoidalUnitIso (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (𝟙_ (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj)) ≅ unitModule X :=
  sheafificationCounitIso (unitModule X)

/-- **The localized symmetric monoidal structure on the sheaves of modules**
(`def:modulesLocalizedMonoidal`): the Mathlib type synonym
`CategoryTheory.LocalizedMonoidal L W ε` of `X.Modules`, with `L` module sheafification, `W` the
sheafification class (monoidal by `W_isMonoidal`, a localization by the Mathlib instance), and `ε`
the unit comparison.  It carries a symmetric monoidal category structure (pentagon, triangle,
hexagon for free) by the Mathlib monoidal-localization machinery, deliberately on the synonym so
it never clashes with structure on `X.Modules` itself. -/
noncomputable abbrev modulesLocalizedMonoidal (X : Scheme.{u}) : Type (u + 1) :=
  LocalizedMonoidal (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
    (localizedMonoidalUnitIso X)

end AlgebraicGeometry.Scheme.Modules
