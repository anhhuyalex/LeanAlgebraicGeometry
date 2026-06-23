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
private abbrev MonoidalPresheaf (X : Scheme.{u}) : Type _ :=
  _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)

/-- The tensor product of two sheaves of modules over a scheme, defined as the
sheafification of the objectwise tensor product presheaf
(Mathlib `PresheafOfModules.monoidalCategory`).  See [Stacks, Tag 01CA]
(`def:sheafTensorObj`). -/
noncomputable def tensorObj (F G : X.Modules) : X.Modules :=
  sheafification.obj
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))

/-- The structure sheaf as a sheaf of modules over itself: the unit object of the
tensor product, i.e. the zeroth tensor power `L^{⊗0} = 𝒪_X`
(`def:unitModule`, backed by `lem:moduleUnit_mathlib`).  Public: the SNAP graded
assembly (`sectionsMul_assoc_unit`, `lem:sectionMul_coherent`) states unitality
against this object. -/
noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The `m`-th tensor power `L^{⊗m}` of a sheaf of modules over a scheme, defined
by recursion: `L^{⊗0} = 𝒪_X` (the unit module) and
`L^{⊗(m+1)} = L^{⊗m} ⊗ L`.  See [Stacks, Tag 01CU] (`def:sheafTensorPow`). -/
noncomputable def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => unitModule X
  | (m + 1) => tensorObj (tensorPow L m) L

/-- The `m`-twist `F(m) = F ⊗ L^{⊗m}` of a sheaf of modules `F` by the `m`-th
tensor power of a line bundle `L` (`def:sheafModuleTwist`).  This is the
degree-`m` carrier of the section graded module. -/
noncomputable def moduleTensorPow (F L : X.Modules) (m : ℕ) : X.Modules :=
  tensorObj F (tensorPow L m)

/-! ### Unitor and braiding isomorphisms of the sheaf tensor product

These are the parts of the (would-be) symmetric monoidal structure on `X.Modules`
that descend through sheafification from `PresheafOfModules.monoidalCategory`
using only *functoriality* of `sheafification` (and, for the unitors, the
reflective counit iso) — no strong-monoidality of `sheafification` is needed, so
they are axiom-clean.  They are the launching pad for `tensorPowAdd`. -/

/-- The counit isomorphism of the module sheafification adjunction: sheafifying
the underlying presheaf of a sheaf of modules returns the sheaf itself.  This is
an isomorphism because the counit of `sheafification ⊣ toPresheafOfModules` is
invertible (the right adjoint `SheafOfModules.forget` is fully faithful).  It is
the launching pad for the left-unitor base case of `tensorPowAdd`. -/
private noncomputable def sheafificationCounitIso (G : X.Modules) :
    sheafification.obj ((toPresheafOfModules X).obj G) ≅ G :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app G

/-- The left-unitor isomorphism `unitModule X ⊗ G ≅ G` of the sheaf tensor
product: the presheaf left unitor `λ_` descended through sheafification, composed
with the counit iso `sheafificationCounitIso`.  This is the base case (`m = 0`) of
`tensorPowAdd`.  Axiom-clean. -/
noncomputable def tensorObjUnitIso (G : X.Modules) :
    tensorObj (unitModule X) G ≅ G :=
  sheafification.mapIso
      (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G)) ≪≫
    sheafificationCounitIso G

/-- The braiding isomorphism `F ⊗ G ≅ G ⊗ F` of the sheaf tensor product,
descended through sheafification from the symmetric braiding on
`X.PresheafOfModules` (`PresheafOfModules.monoidalCategory`).  Axiom-clean: the
braiding is pure sheafification-functoriality of the presheaf-level braiding, so
no monoidal structure on `X.Modules` is required.  This is the symmetry used in
the inductive step of `tensorPowAdd`. -/
noncomputable def tensorBraiding (F G : X.Modules) :
    tensorObj F G ≅ tensorObj G F :=
  sheafification.mapIso
    (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))

/-- The right-unitor isomorphism `G ⊗ unitModule X ≅ G` of the sheaf tensor product
(`def:tensorObjRightUnitor`), defined — following [Stacks, Tag 01CA] and the symmetric-monoidal
convention — as the braiding `β_{G,𝟙}` that swaps the two factors followed by the left unitor
`λ_G` (`tensorObjUnitIso`).  Like the braiding and left unitor it descends from the presheaf
symmetric monoidal structure through sheafification-functoriality and the reflective counit,
requiring no monoidal structure on `X.Modules`.  It is the base of the right-unitality reduction
of `tensorPowAdd` (`lem:tensorPowAdd_rightUnit`). -/
noncomputable def tensorObjRightUnitor (G : X.Modules) :
    tensorObj G (unitModule X) ≅ G :=
  tensorBraiding G (unitModule X) ≪≫ tensorObjUnitIso G

/-- The hom of the right-unitor iso splits as the braiding followed by the left unitor. -/
lemma tensorObjRightUnitor_hom (G : X.Modules) :
    (tensorObjRightUnitor G).hom
      = (tensorBraiding G (unitModule X)).hom ≫ (tensorObjUnitIso G).hom :=
  rfl

/-! ### Lax-monoidal global sections: the section multiplication

The global-sections functor `Γ(X, -)` is only *lax* monoidal: a pair of global
sections does not commute with sheafification, so the multiplication is a map,
not an isomorphism.  It is nonetheless `Γ(X, 𝒪_X)`-linear and is the data the
section graded ring is built from. -/

/-- The **section multiplication** (`def:sectionMul`), the `Γ(X,𝒪_X)`-bilinear map
`Γ(X,F) ⊗_{Γ(X,𝒪_X)} Γ(X,G) → Γ(X, F ⊗ G)`.

Its domain `(F.toPresheaf ⊗ G.toPresheaf)(X)` is, by the objectwise formula of
`PresheafOfModules.monoidalCategory`, the `Γ(X,𝒪_X)`-module
`Γ(X,F) ⊗_{Γ(X,𝒪_X)} Γ(X,G)` of elementary tensors of global sections; a pair
`(σ, τ)` is sent to `σ ⊗ τ`.  Postcomposing with the global-sections component of
the sheafification unit `η : P → P^#` (`def:sheafTensorObj`) lands in
`Γ(X, F ⊗ G)`.  As a morphism in `ModuleCat (Γ(X,𝒪_X))` it is automatically
`Γ(X,𝒪_X)`-bilinear; this records that linearity.  Axiom-clean: it is pure
sheafification-unit naturality, requiring no monoidal structure on `X.Modules`. -/
noncomputable def sectionsMul (F G : X.Modules) :
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).obj (Opposite.op ⊤) ⟶
      (tensorObj F G).val.obj (Opposite.op ⊤) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))).app (Opposite.op ⊤)

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
/-- The associativity isomorphism `(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)` for the sheaf tensor product
`tensorObj` on a scheme `X` (`cor:sheafTensorObjAssoc`).

Both iterated sheaf tensors are compared to the sheafification of the triple presheaf tensor via
the now-proven `isIso_sheafification_whiskerRight_unit` (whiskered sheafification units are isos,
iter-066); the presheaf-level associator (`PresheafOfModules.monoidalCategory`) then descends
through `sheafification.mapIso`.  See the planner strategy comment above for the three-segment
composite and the carrier-idiom checklist. -/
noncomputable def tensorObjAssoc (A B C : X.Modules) :
    tensorObj (tensorObj A B) C ≅ tensorObj A (tensorObj B C) := by
  -- Segment-1 and segment-3 whiskered units are isos by the crux lemma.
  haveI := isIso_sheafification_whiskerRight_unit
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
    ((toPresheafOfModules X).obj C)
  haveI := isIso_sheafification_whiskerRight_unit
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))
    ((toPresheafOfModules X).obj A)
  exact
    -- Segment 1 (inverse whiskered unit on the left factor):
    -- (A ⊗ B) ⊗ C ≅ ((a ⊗_p b) ⊗_p c)^#
    (asIso (sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
        ((toPresheafOfModules X).obj C)))).symm ≪≫
    -- Segment 2 (presheaf associator under sheafification):
    -- ((a ⊗_p b) ⊗_p c)^# ≅ (a ⊗_p (b ⊗_p c))^#
    sheafification.mapIso (MonoidalCategory.associator (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
      ((toPresheafOfModules X).obj C)) ≪≫
    -- Segment 3 (whiskered unit on the right factor, conjugated by the braiding):
    -- (a ⊗_p (b ⊗_p c))^# ≅ ((b ⊗_p c) ⊗_p a)^#
    sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A)
      (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))) ≪≫
    -- ((b ⊗_p c) ⊗_p a)^# ≅ ((b ⊗_p c)^# ⊗_p a)^#
    @asIso _ _ _ _
      (sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)))
        ((toPresheafOfModules X).obj A)))
      (isIso_sheafification_whiskerRight_unit
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))
        ((toPresheafOfModules X).obj A)) ≪≫
    -- ((b ⊗_p c)^# ⊗_p a)^# ≅ (a ⊗_p (b ⊗_p c)^#)^# = A ⊗ (B ⊗ C)
    sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj (tensorObj B C)) ((toPresheafOfModules X).obj A))

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
private noncomputable instance pshModMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (MonoidalPresheaf X))

/-- The presheaf braiding, transported to the syntactic bare form (see `pshModMonoidal`). -/
private noncomputable instance pshModBraided :
    BraidedCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (BraidedCategory (MonoidalPresheaf X))

/-- The presheaf symmetry, transported to the syntactic bare form (see `pshModMonoidal`). -/
private noncomputable instance pshModSymmetric :
    SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory (MonoidalPresheaf X))

/-- The sheafification localization class as a morphism property of the presheaf-of-modules
category: a morphism lies in `W` iff its underlying abelian-presheaf morphism is a local
isomorphism for the opens topology.  This is the class `W` of `def:W_isMonoidal`. -/
private abbrev Wsheaf (X : Scheme.{u}) :
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

/-- **Object identification: hand-built versus localized tensor** (`def:tensorObjLocalizedIso`).
The object-identification isomorphism `i_{F,G} : F ⊗ G ≅ F ⊗_loc G` between the hand-built sheaf
tensor product `tensorObj` (`def:sheafTensorObj`) and the localized monoidal tensor product of
`modulesLocalizedMonoidal X`.  It is the composite `μ⁻¹_{F^♭,G^♭} ≫ (c_F ⊗_loc c_G)`, where `μ`
is the Mathlib strong-monoidality comparison of the monoidal localization
(`Localization.Monoidal.μ`) at the underlying presheaves and `c_F = sheafificationCounitIso F`
is the reflective sheafification counit iso.  This is the identification all four bridge lemmas
thread through (Option B of `sec:sgr_localized_monoidal`). -/
noncomputable def tensorObjLocalizedIso (F G : X.Modules) :
    tensorObj F G ≅
      MonoidalCategory.tensorObj (C := modulesLocalizedMonoidal X)
        (F : modulesLocalizedMonoidal X) (G : modulesLocalizedMonoidal X) :=
  (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (Wsheaf X) (localizedMonoidalUnitIso X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).symm ≪≫
    MonoidalCategory.tensorIso (C := modulesLocalizedMonoidal X)
      (sheafificationCounitIso F) (sheafificationCounitIso G)

/-- Right-whiskering of a sheaf-level isomorphism by a sheaf of modules: given
`e : F ≅ F'`, the isomorphism `F ⊗ G ≅ F' ⊗ G` of sheaf tensor products, obtained
by sheafifying the presheaf-level right-whiskering (`whiskerRightIso`) of the
underlying presheaf isomorphism `(toPresheafOfModules X).mapIso e`.  Pure
sheafification-functoriality — no monoidal structure on `X.Modules` needed.
Used for step (d) of `tensorPowAdd` (whiskering the inductive hypothesis by `L`). -/
private noncomputable def tensorObjWhiskerRightIso {F F' : X.Modules} (e : F ≅ F')
    (G : X.Modules) : tensorObj F G ≅ tensorObj F' G where
  hom := sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
    ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G))
  inv := sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
    ((toPresheafOfModules X).map e.inv) ((toPresheafOfModules X).obj G))
  hom_inv_id := by
    -- term-mode congruence (positional rw cannot fire under the Scheme-cat diamond)
    have hcomp : (toPresheafOfModules X).map e.hom ≫ (toPresheafOfModules X).map e.inv
        = 𝟙 ((toPresheafOfModules X).obj F) :=
      ((toPresheafOfModules X).map_comp e.hom e.inv).symm.trans
        ((congrArg (toPresheafOfModules X).map e.hom_inv_id).trans
          ((toPresheafOfModules X).map_id F))
    have hw : MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G) ≫
        MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).map e.inv) ((toPresheafOfModules X).obj G)
        = 𝟙 (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)) :=
      (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
        ((congrArg (fun t => MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) t
            ((toPresheafOfModules X).obj G)) hcomp).trans
          (MonoidalCategory.id_whiskerRight _ _))
    exact (sheafification.map_comp _ _).symm.trans
      ((congrArg sheafification.map hw).trans (sheafification.map_id _))
  inv_hom_id := by
    have hcomp : (toPresheafOfModules X).map e.inv ≫ (toPresheafOfModules X).map e.hom
        = 𝟙 ((toPresheafOfModules X).obj F') :=
      ((toPresheafOfModules X).map_comp e.inv e.hom).symm.trans
        ((congrArg (toPresheafOfModules X).map e.inv_hom_id).trans
          ((toPresheafOfModules X).map_id F'))
    have hw : MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).map e.inv) ((toPresheafOfModules X).obj G) ≫
        MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G)
        = 𝟙 (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F') ((toPresheafOfModules X).obj G)) :=
      (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
        ((congrArg (fun t => MonoidalCategory.whiskerRight (C := MonoidalPresheaf X) t
            ((toPresheafOfModules X).obj G)) hcomp).trans
          (MonoidalCategory.id_whiskerRight _ _))
    exact (sheafification.map_comp _ _).symm.trans
      ((congrArg sheafification.map hw).trans (sheafification.map_id _))

/-- Left-whiskering of a sheaf-level isomorphism by a sheaf of modules: given
`e : G ≅ G'`, the isomorphism `F ⊗ G ≅ F ⊗ G'` of sheaf tensor products, obtained
by sheafifying the presheaf-level left-whiskering (`whiskerLeftIso`) of the
underlying presheaf isomorphism.  Used for step (b) of `tensorPowAdd` (braiding
the inner factor under the fixed left factor `L^⊗k`). -/
private noncomputable def tensorObjWhiskerLeftIso (F : X.Modules) {G G' : X.Modules}
    (e : G ≅ G') : tensorObj F G ≅ tensorObj F G' :=
  sheafification.mapIso
    (MonoidalCategory.whiskerLeftIso (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).mapIso e))

/- Planner strategy for `tensorPowAdd` (`lem:sheafTensorPow_add`, blueprint L1158–L1243):

INDUCTION ON m (blueprint proof block L1186–L1222):

BASE CASE (m = 0):
  tensorObj (tensorPow L 0) (tensorPow L m')
    = tensorObj (unitModule X) (tensorPow L m')   [by tensorPow_zero]
  Iso: tensorObjUnitIso (tensorPow L m') ≪≫ eqToIso (by simp [Nat.zero_add])

INDUCTIVE STEP (m = k+1, IH : tensorObj (tensorPow L k) (tensorPow L m') ≅ tensorPow L (k+m')):
  tensorObj (tensorPow L (k+1)) (tensorPow L m')
    = tensorObj (tensorObj (tensorPow L k) L) (tensorPow L m')   [by tensorPow_succ]

  Step (a) — ASSOCIATOR (left-to-right):
    tensorObjAssoc (tensorPow L k) L (tensorPow L m')
    gives tensorObj (tensorPow L k) (tensorObj L (tensorPow L m'))

  Step (b) — BRAIDING on the inner factor:
    sheafification.mapIso
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj L)
        ((toPresheafOfModules X).obj (tensorPow L m')))
    OR equivalently `tensorBraiding L (tensorPow L m')` (already in file, private),
    whiskered to act on the right factor of tensorPow L k.
    After this: tensorObj (tensorPow L k) (tensorObj (tensorPow L m') L).

  Step (c) — INVERSE ASSOCIATOR:
    (tensorObjAssoc (tensorPow L k) (tensorPow L m') L).symm
    gives tensorObj (tensorObj (tensorPow L k) (tensorPow L m')) L.

  Step (d) — WHISKER IH BY L ON THE RIGHT:
    Need tensorObj (tensorPow L (k + m')) L ≅ tensorPow L ((k+m')+1).
    Since tensorPow L ((k+m')+1) = tensorObj (tensorPow L (k+m')) L (by tensorPow_succ),
    this is just `Iso.refl _` (or `eqToIso rfl`).
    The IH itself: sheafification.mapIso applied to
        MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          <presheaf-level map lifting IH> ((toPresheafOfModules X).obj L)
    — but IH is a sheaf-level iso, so lifting to presheaf level is non-trivial.
    ALTERNATIVE: define the sheaf-level whiskering endofunctor
        fun F => tensorObj F L
    as a Lean Functor and apply `Functor.mapIso` to IH; or use `Iso.mk` building hom/inv
    from the presheaf-level morphisms obtained from IH.hom/IH.inv via
        sheafification.map (whiskerRight ((toPresheafOfModules X).map IH.hom) (toPresheaf L))
    (here (toPresheafOfModules X).map : X.Modules ⥤ X.PresheafOfModules is the right adjoint,
    already called `toPresheafOfModules X`).

  Step (e) — REINDEX:
    eqToIso (by omega : (k + m') + 1 = (k + 1) + m')   [Nat.succ_add]
    composes on the target to land in tensorPow L ((k+1) + m').

IMPLEMENTATION NOTE: Lean's `Nat.rec` for ℕ-indexed Iso families works cleanly as a
  `match m with | 0 => ... | k+1 => ...` in a `noncomputable def`.  The `eqToIso` steps are
  the index-bookkeeping glue; `omega` closes all arithmetic goals.

CARRIER IDIOMS (same as tensorObjAssoc above; additionally):
  • `tensorPow_zero`/`tensorPow_succ` are `@[simp] private lemma`s in this file; use them
    via `rw [tensorPow_succ]` or `show ... = tensorObj ... ...` to unfold.
  • Step (d)'s sheaf-level right-whisker: verify `(toPresheafOfModules X).map` exists
    (it is the forgetful `SheafOfModules → PresheafOfModules` functor) before using it.
  • If `(toPresheafOfModules X).map IH.hom` causes universe issues, build the inner
    morphism at the presheaf level directly from the sorry body using `sheafification.map`.
-/
/-- The tensor-power comparison isomorphism `L^⊗m ⊗ L^⊗m' ≅ L^⊗(m+m')` for the sheaf tensor
power `tensorPow` (`lem:sheafTensorPow_add`, [Stacks, Tag 01CU]).

Proof by induction on `m`: the base case `m = 0` uses the left-unitor `tensorObjUnitIso`
(already in file, axiom-clean); the inductive step uses `tensorObjAssoc` (above), the braiding
`tensorBraiding` (in file), and sheaf-level right-whiskering of the inductive hypothesis.
See the planner strategy comment above for the step-by-step construction and carrier-idiom
checklist. -/
noncomputable def tensorPowAdd (L : X.Modules) (m m' : ℕ) :
    tensorObj (tensorPow L m) (tensorPow L m') ≅ tensorPow L (m + m') :=
  match m with
  | 0 =>
    -- Base case: the left unitor, reindexed along `0 + m' = m'`.
    tensorObjUnitIso (tensorPow L m') ≪≫
      eqToIso (congrArg (tensorPow L) (Nat.zero_add m').symm)
  | (k + 1) =>
    -- (a) associator, (b) braiding under the left factor, (c) inverse associator,
    -- (d) inductive hypothesis whiskered by `L` on the right, (e) reindexing.
    tensorObjAssoc (tensorPow L k) L (tensorPow L m') ≪≫
      tensorObjWhiskerLeftIso (tensorPow L k) (tensorBraiding L (tensorPow L m')) ≪≫
      (tensorObjAssoc (tensorPow L k) (tensorPow L m') L).symm ≪≫
      tensorObjWhiskerRightIso (tensorPowAdd L k m') L ≪≫
      eqToIso (congrArg (tensorPow L) (Nat.succ_add k m').symm)

/-! ### Bridge lemmas: hand-built isomorphisms versus the localized monoidal structure

Option B of `sec:sgr_localized_monoidal`: each hand-built structural iso of the sheaf tensor
product is the corresponding iso of `modulesLocalizedMonoidal X` conjugated by the object
identification `tensorObjLocalizedIso`.  The proofs expand both sides via the Mathlib component
formulas (`Localization.Monoidal.{μ_natural_left,μ_natural_right,braidingNatIso_hom_app,
leftUnitor_hom_app,rightUnitor_hom_app,associator_hom_app}`) and cancel the `μ`'s. -/

/-- The lax-monoidal structure map of the localization functor `L'` is the `hom` of the
strong-monoidality comparison `Localization.Monoidal.μ`.  Definitional repackaging. -/
private lemma laxMonoidal_μ_eq (P Q : X.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Localization.Monoidal.toMonoidalCategory
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
        (localizedMonoidalUnitIso X)) P Q
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
          (Wsheaf X) (localizedMonoidalUnitIso X) P Q).hom := rfl

/-- The oplax-monoidal structure map of the localization functor `L'` is the `inv` of the
strong-monoidality comparison `Localization.Monoidal.μ`.  Definitional repackaging. -/
private lemma oplaxMonoidal_δ_eq (P Q : X.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (Localization.Monoidal.toMonoidalCategory
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
        (localizedMonoidalUnitIso X)) P Q
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
          (Wsheaf X) (localizedMonoidalUnitIso X) P Q).inv := rfl

/-- **Bridge: the hand-built braiding is the localized braiding**
(`lem:tensorBraiding_eq_localizedBraiding`).  The hand-built braiding `tensorBraiding F G` equals
the localized braiding `β^loc_{F,G}` conjugated by the object identifications
`tensorObjLocalizedIso` on both tensor slots.  Proof: substitute the definition of
`tensorObjLocalizedIso`, move `β^loc` across the counit tensor by `braiding_naturality`, cancel the
counits, expand `β^loc` at `L'`-objects by `braidingNatIso_hom_app`, and cancel the `μ`'s. -/
lemma tensorBraiding_eq_localizedBraiding (F G : X.Modules) :
    (@BraidedCategory.braiding (modulesLocalizedMonoidal X) _ _ _ F G)
      = (tensorObjLocalizedIso F G).symm ≪≫ tensorBraiding F G ≪≫
          tensorObjLocalizedIso G F := by
  -- Rewrite the hand-built braiding to the defeq localized `L'.mapIso (β^p)`, so the whole RHS
  -- iso is typed in the localized category and `Iso.ext` produces localized compositions.
  rw [show tensorBraiding F G
      = (Localization.Monoidal.toMonoidalCategory (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)) (Wsheaf X) (localizedMonoidalUnitIso X)).mapIso
          (β_ ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)) from rfl]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, tensorObjLocalizedIso,
    MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorIso_inv, Iso.symm_inv,
    Functor.mapIso_hom]
  -- Naturality of the localized braiding `β^loc` along the counit isos `c_F, c_G` reduces the
  -- general-object braiding to the `L'`-object one, whose Mathlib formula `β_hom_app` is
  -- `μ ≫ L'(β^p) ≫ μ⁻¹` (lax/oplax structure maps recognised as `μ.hom`/`μ.inv`).  Keeping the
  -- rewrite inside `hnat` avoids the `X.Modules`-vs-`LocalizedMonoidal` composition-instance clash.
  have hnat := BraidedCategory.braiding_naturality (C := modulesLocalizedMonoidal X)
    (sheafificationCounitIso F).hom (sheafificationCounitIso G).hom
  erw [Localization.Monoidal.β_hom_app (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj F)
      ((toPresheafOfModules X).obj G)] at hnat
  rw [laxMonoidal_μ_eq, oplaxMonoidal_δ_eq] at hnat
  -- Solve `hnat` for `β^loc_{F,G}` in *uniform* `LocalizedMonoidal` composition flavor (`key`):
  -- cancel the epi `c_F ⊗ c_G` and collapse `(c⊗c) ≫ (c⁻¹⊗c⁻¹) = 𝟙`.  Then close the goal by
  -- `exact key` — definitional equality bridges the `X.Modules`-vs-`LocalizedMonoidal` comp clash.
  have key : (@BraidedCategory.braiding (modulesLocalizedMonoidal X) _ _ _ F G).hom =
      MonoidalCategory.tensorHom (C := modulesLocalizedMonoidal X)
          (sheafificationCounitIso F).inv (sheafificationCounitIso G).inv ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom ≫
        (Localization.Monoidal.toMonoidalCategory (PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)) (Wsheaf X) (localizedMonoidalUnitIso X)).map
          (β_ ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X)
            ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)).inv ≫
        MonoidalCategory.tensorHom (C := modulesLocalizedMonoidal X)
          (sheafificationCounitIso G).hom (sheafificationCounitIso F).hom := by
    rw [← cancel_epi (MonoidalCategory.tensorHom (C := modulesLocalizedMonoidal X)
        (sheafificationCounitIso F).hom (sheafificationCounitIso G).hom), hnat]
    letI mc : MonoidalCategory (modulesLocalizedMonoidal X) := inferInstance
    -- Thread the monoidal-category instance `mc` explicitly into `tensorIso`: re-synthesising
    -- `MonoidalCategory (modulesLocalizedMonoidal X)` inside the large `exact` term fails, while
    -- the already-found `mc` discharges it deterministically.
    exact ((@MonoidalCategory.tensorIso (modulesLocalizedMonoidal X) _ mc _ _ _ _
      (sheafificationCounitIso F) (sheafificationCounitIso G)).hom_inv_id_assoc _).symm
  exact key

/-- **Bridge: the hand-built left unitor is the localized left unitor**
(`lem:tensorObjUnitor_eq_localized`).  The hand-built left unitor `λ_G = tensorObjUnitIso G`
(`def:tensorObjUnitIso`) equals the localized left unitor `λ^loc_G` precomposed with the object
identification `i_{𝟙,G} = tensorObjLocalizedIso (unitModule X) G`.  Proof: `leftUnitor` naturality
along the counit `c_G` reduces to `G = (G♭)^#`, where the Mathlib component formula
`leftUnitor_hom_app` gives `λ^loc_{L'G♭} = (ε⁻¹ ▷ L'G♭) ; μ_{𝟙,G♭} ; L'(λ^p_{G♭})`; the `ε`/`ε⁻¹`
whisker collapses and the `μ`-pair (the one in `i⁻¹` and the one from the formula, both at
`(𝟙_psh, G♭)`) cancels, leaving `L'(λ^p_{G♭}) ; c_G`, which is exactly `(tensorObjUnitIso G).hom`. -/
lemma tensorObjUnitIso_eq_localizedLeftUnitor (G : X.Modules) :
    tensorObjUnitIso G
      = tensorObjLocalizedIso (unitModule X) G ≪≫
          MonoidalCategoryStruct.leftUnitor (C := modulesLocalizedMonoidal X)
            (G : modulesLocalizedMonoidal X) := by
  apply Iso.ext
  -- Expose both sides: `hand.hom = i.hom ≫ λ^loc_G.hom`; flip + `Iso.eq_inv_comp` isolates the
  -- localized unitor `(λ_G).hom = (c₁⁻¹ ⊗ c_G⁻¹) ≫ μ_{𝟙♭,G♭} ≫ L'(λ^p_{G♭}) ≫ c_G`.
  rw [Iso.trans_hom]
  symm
  rw [← Iso.eq_inv_comp]
  simp only [tensorObjUnitIso, tensorObjLocalizedIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, MonoidalCategory.tensorIso_inv, Category.assoc]
  -- `λ^loc` is only computable at an `L'`-object, so cancel the counit `c_G` by whiskering on the
  -- left (`cancel_epi (𝟙 ◁ c_G)`) and pull it through by `leftUnitor_naturality`; then the Mathlib
  -- component formula `leftUnitor_hom_app` rewrites `λ^loc_{L'G♭} = (ε⁻¹ ▷) ≫ μ ≫ L'(λ^p)`.
  apply (cancel_epi (MonoidalCategoryStruct.whiskerLeft (C := modulesLocalizedMonoidal X)
    (unitModule X) (sheafificationCounitIso G).hom)).1
  erw [MonoidalCategory.leftUnitor_naturality (C := modulesLocalizedMonoidal X)
      (sheafificationCounitIso G).hom,
    Localization.Monoidal.leftUnitor_hom_app (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj G)]
  -- `ε = localizedMonoidalUnitIso X = sheafificationCounitIso (unitModule X) = c₁` (definitional).
  -- Split the counit tensor `c₁⁻¹ ⊗ c_G⁻¹`, exchange the whiskers so the `c_G`/`c_G⁻¹` pair meets and
  -- cancels, leaving `(c₁⁻¹ ▷ L'G♭) ≫ μ_{𝟙♭,G♭}` on both sides (the two `μ`'s agree definitionally).
  -- `ε = c₁` (definitional); rewrite `𝟙 ◁ c_G = 𝟙 ⊗ₘ c_G`, then the interchange `tensor_comp` merges
  -- `(𝟙 ⊗ c_G) ≫ (c₁⁻¹ ⊗ c_G⁻¹) = (𝟙 ≫ c₁⁻¹) ⊗ (c_G ≫ c_G⁻¹) = c₁⁻¹ ⊗ 𝟙 = c₁⁻¹ ▷ L'G♭`; both sides
  -- reduce to `(c₁⁻¹ ▷ L'G♭) ≫ μ ≫ L'(λ^p) ≫ c_G` (the two `μ`'s agree definitionally).
  simp only [Localization.Monoidal.ε', localizedMonoidalUnitIso, ← MonoidalCategory.id_tensorHom]
  -- The merge straddles the `modulesLocalizedMonoidal X` ↔ `LocalizedMonoidal` comp-instance boundary
  -- (defeq-not-syntactic), so the interchange + iso-cancel chain fires via `erw` (reducible
  -- transparency) rather than `rw`.  Both sides land on `(c₁⁻¹ ▷ L'G♭) ≫ μ ≫ L'(λ^p) ≫ c_G`.
  erw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, Iso.hom_inv_id,
    MonoidalCategory.tensorHom_id]
  -- Both sides are now `(c₁⁻¹ ▷ L'G♭) ≫ μ ≫ L'(λ^p) ≫ c_G`, equal up to associativity grouping and
  -- the definitional spellings `toMonoidalCategory = sheafification`, `𝟙_psh = (unitModule X)♭`.
  rfl

/-! ### Associator bridge seams (`lem:tensorObjAssoc_eq_localizedAssociator`)

The hand-built associator `tensorObjAssoc` is a five-segment composite (segment 1 = inverse
whiskered unit, segment 2 = sheafified presheaf associator, segments 3–5 = braiding-conjugated
whiskered unit).  We isolate its mathematical content in four seam lemmas: the seg-2 defeq
(`sheafification_mapIso_associator_eq_localizationMap`), the two keystones identifying a sheafified
whiskered unit with a `μ` component (`sheafification_whiskerRight_unit_eq_mu` via `μ_natural_left`,
`sheafification_whiskerLeft_unit_eq_mu` via `μ_natural_right`), and the braiding-conjugation
collapse of segments 3–5 (`sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit`). -/

/-- **Seam (segment 2): the sheafified presheaf associator is the localization image of the
presheaf associator** (`lem:sheafificationMapIso_assoc_eq_localized`).  The localization functor
`L' = toMonoidalCategory` is, by construction, sheafification on morphisms, so `L'(α^p)` is
definitionally `(α^p)^#`; the equality holds by reflexivity. -/
lemma sheafification_mapIso_associator_eq_localizationMap (P Q R : X.PresheafOfModules) :
    (sheafification.mapIso (MonoidalCategory.associator (C := MonoidalPresheaf X) P Q R)).hom
      = (Localization.Monoidal.toMonoidalCategory
          (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)).map
          (MonoidalCategory.associator (C := MonoidalPresheaf X) P Q R).hom := rfl

/-- **Keystone: the sheafified right-whiskered unit is a `μ` component** (via `μ_natural_left`,
`lem:whiskeredUnit_eq_localizationMu`).  For presheaves `P, Q`, the sheafified right-whiskered unit
`(η_P ▷ Q)^#` equals the `μ`-conjugate of the localized right-whiskering of the sheafified unit:
`(η_P ▷ Q)^# = μ_{P,Q}⁻¹ ; ((η_P)^# ▷_loc Q^#) ; μ_{P^♭,Q}`. -/
lemma sheafification_whiskerRight_unit_eq_mu (P Q : X.PresheafOfModules) :
    sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) Q)
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P Q).inv ≫
          MonoidalCategory.whiskerRight (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P))
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).obj Q) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) _ Q).hom := by
  simp only [CategoryTheory.Functor.id_obj]
  rw [Localization.Monoidal.μ_natural_left, Iso.inv_hom_id_assoc]
  rfl

/-- **Keystone variant: the sheafified left-whiskered unit is a `μ` component** (via
`μ_natural_right`, `lem:whiskeredUnitLeft_eq_localizationMu`).  For presheaves `P, Q`, the
sheafified left-whiskered unit `(P ◁ η_Q)^#` equals the `μ`-conjugate of the localized
left-whiskering of the sheafified unit:
`(P ◁ η_Q)^# = μ_{P,Q}⁻¹ ; (P^# ◁_loc (η_Q)^#) ; μ_{P,Q^♭}`. -/
lemma sheafification_whiskerLeft_unit_eq_mu (P Q : X.PresheafOfModules) :
    sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X) P
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q))
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P Q).inv ≫
          MonoidalCategory.whiskerLeft (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).obj P)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q)) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P _).hom := by
  simp only [CategoryTheory.Functor.id_obj]
  rw [Localization.Monoidal.μ_natural_right, Iso.inv_hom_id_assoc]
  rfl

/-- **Canonical right keystone** (`lem:whiskeredUnit_eq_localizationMu_canonical`): the
right-whiskered keystone `sheafification_whiskerRight_unit_eq_mu` restated with the trailing
`μ`'s first object argument pinned to the counit-object form
`(toPresheafOfModules X).obj (sheafification.obj P)` (= `(P^#)^♭`) exactly as in
`tensorObjLocalizedIso`, so the two `μ` occurrences in the associator bridge become the
syntactically same comparison and cancel.  Mathematically identical to the unprimed keystone;
the restatement only fixes the representation of the comparison's object. -/
lemma sheafification_whiskerRight_unit_eq_mu' (P Q : X.PresheafOfModules) :
    sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) Q)
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P Q).inv ≫
          MonoidalCategory.whiskerRight (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P))
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).obj Q) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X)
            ((toPresheafOfModules X).obj (sheafification.obj P)) Q).hom :=
  sheafification_whiskerRight_unit_eq_mu P Q

/-- **Canonical left keystone** (`lem:whiskeredUnitLeft_eq_localizationMu_canonical`): the
left-whiskered keystone `sheafification_whiskerLeft_unit_eq_mu` restated with the trailing
`μ`'s second object argument pinned to the counit-object form
`(toPresheafOfModules X).obj (sheafification.obj Q)` (= `(Q^#)^♭`) exactly as in
`tensorObjLocalizedIso`.  Mathematically identical to the unprimed keystone. -/
lemma sheafification_whiskerLeft_unit_eq_mu' (P Q : X.PresheafOfModules) :
    sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X) P
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q))
      = (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P Q).inv ≫
          MonoidalCategory.whiskerLeft (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).obj P)
            ((Localization.Monoidal.toMonoidalCategory
              (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
              (localizedMonoidalUnitIso X)).map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q)) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Wsheaf X) (localizedMonoidalUnitIso X) P
            ((toPresheafOfModules X).obj (sheafification.obj Q))).hom :=
  sheafification_whiskerLeft_unit_eq_mu P Q

/-- **Seam (braiding conjugation realises the left-whiskered unit)**
(`lem:sheafification_braidingConj_whiskerRightUnit`).  At the presheaf level, naturality of the
braiding in its right argument is the braided-category identity
`A ◁ η_P = β_{A,P} ; (η_P ▷ A) ; β_{P^♭,A}`; sheafification preserves composition. -/
lemma sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit (A P : X.PresheafOfModules) :
    sheafification.map (BraidedCategory.braiding (C := MonoidalPresheaf X) A P).hom ≫
        sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) A) ≫
        sheafification.map (BraidedCategory.braiding (C := MonoidalPresheaf X) A _).inv
      = sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X) A
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  rw [← sheafification.map_comp, ← sheafification.map_comp]
  congr 1
  -- Presheaf-level: `β_{A,P} ; (η_P ▷ A) ; β_{A,P^♭}⁻¹ = A ◁ η_P` by right-argument braiding
  -- naturality (`braiding_naturality_right`).
  have hn := BraidedCategory.braiding_naturality_right (C := MonoidalPresheaf X) A
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  rw [← Category.assoc, Iso.comp_inv_eq]
  exact hn.symm

/-- **The common form `K` of the associator bridge** (the meeting point of the two
half-assemblies `hK_lhs`/`hK_rhs`, blueprint `K` of `lem:tensorObjAssoc_eq_localizedAssociator`).
Well-typed Lean realisation of the blueprint schematic
`K = L'(α^p) ; μ⁻¹ ; (L'a ◁ μ⁻¹) ; (c_A ⊗ (c_B ⊗ c_C))`, prefixed by the inverse segment-1
whiskered unit `(L'(η_{a⊗b} ▷ c))⁻¹` so the domain is the assembly domain
`tensorObj (tensorObj A B) C` (the schematic core's domain `L'((a⊗b)⊗c)` differs by exactly this
unit — the "counit object-glue on the 4 tensor slots" the plan flags).  Its five factors:
inverse segment-1 unit, `L'(α^p)`, `μ⁻¹_{a,b⊗c}`, `(L'a ◁ μ⁻¹_{b,c})`, and
`(c_A ⊗ (c_B ⊗ c_C))`. -/
private noncomputable def assocCommonForm (A B C : X.Modules) :
    tensorObj (tensorObj A B) C ⟶
      MonoidalCategory.tensorObj (C := modulesLocalizedMonoidal X)
        (A : modulesLocalizedMonoidal X)
        (MonoidalCategory.tensorObj (C := modulesLocalizedMonoidal X)
          (B : modulesLocalizedMonoidal X) (C : modulesLocalizedMonoidal X)) :=
  (@asIso _ _ _ _
      (sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
        ((toPresheafOfModules X).obj C)))
      (isIso_sheafification_whiskerRight_unit
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
        ((toPresheafOfModules X).obj C))).inv ≫
    sheafification.map (MonoidalCategory.associator (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
      ((toPresheafOfModules X).obj C)).hom ≫
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj A)
      (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))).inv ≫
    MonoidalCategory.whiskerLeft (C := modulesLocalizedMonoidal X)
      ((Localization.Monoidal.toMonoidalCategory
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
        (localizedMonoidalUnitIso X)).obj ((toPresheafOfModules X).obj A))
      (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj B)
        ((toPresheafOfModules X).obj C)).inv ≫
    MonoidalCategory.tensorHom (C := modulesLocalizedMonoidal X)
      (sheafificationCounitIso A).hom
      (MonoidalCategory.tensorHom (C := modulesLocalizedMonoidal X)
        (sheafificationCounitIso B).hom (sheafificationCounitIso C).hom)

/-- Adjunction triangle in sheafified form: `L'(η_P) ≫ c_{L'P} = 𝟙`, where `c` is the reflective
counit iso `sheafificationCounitIso`.  This is `Adjunction.left_triangle_components` with the counit
written through `sheafificationCounitIso` (defeq), used to collapse the whisker head of `hK_lhs`. -/
private lemma sheafification_map_unit_comp_counitIso_hom (P : X.PresheafOfModules) :
    sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) ≫
        (sheafification.obj P).sheafificationCounitIso.hom
      = 𝟙 (sheafification.obj P) := by
  simp only [sheafificationCounitIso]
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P

/-- **Head reduction for the localized half-assembly** (`lem:tensorObjAssoc_hK_lhs`, recipe Step 5,
`analogies/snap-assoc-expose.md`).  The composite of the leading inverse-μ, the whiskered counit at
the composite object `A⊗B`, and the μ at the presheaf tensor `A♭⊗B♭` collapses to the inverse of the
sheafified whiskered unit `(L'(η_{A♭⊗B♭} ▷ C♭))⁻¹` — the head of the common form `K`.  Proof: the
naturality square `μ_natural_left η_{A♭⊗B♭} C♭` plus the adjunction triangle
`left_triangle_components (A♭⊗B♭)` (giving `c_{A⊗B} = (L'η)⁻¹`), then the μ-pair cancels.  This is the
only non-routine step of `hK_lhs`; it is isolated here because it is provable independently of the
(currently blocked) interchange merge in `hK_lhs`.

`@[reassoc]` auto-generates the suffixed sibling `tensorObjAssoc_hK_lhs_head_assoc` with
`Category.assoc` baked in (`prefix ≫ g = s1.inv ≫ g`); `tensorObjAssoc_hK_lhs_native` applies it via
plain `exact` so the heavy localized `tail` binds to the `?g` metavar by structural `≫`-match and is
never `whnf`'d (the `reassoc_of%` use-site elaborator bombs because its internal `simp` whnf-unfolds
the localized μ; the pre-generated `_assoc` lemma does not). -/
@[reassoc]
private lemma tensorObjAssoc_hK_lhs_head (A B C : X.Modules) :
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          ((toPresheafOfModules X).obj (sheafification.obj
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
          ((toPresheafOfModules X).obj C)).inv ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (A.tensorObj B).sheafificationCounitIso.hom
          (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
          ((toPresheafOfModules X).obj C)).hom
      = (@asIso _ _ _ _
          (sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
            ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
            ((toPresheafOfModules X).obj C)))
          (isIso_sheafification_whiskerRight_unit
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C))).inv := by
  -- `LHS = s1.inv` ⟺ `s1.hom ≫ LHS = 𝟙`.  Expand `s1.hom` by the existing right-whiskered keystone
  -- `sheafification_whiskerRight_unit_eq_mu'` (= `μ₂'.inv ≫ (L'η ▷) ≫ μ₁.hom`); then the μ-pairs cancel
  -- and the adjunction triangle `L'η ≫ c_{A⊗B} = 𝟙` (`left_triangle_components`) collapses the head.
  refine (cancel_epi (@asIso _ _ _ _ (sheafification.map (MonoidalCategory.whiskerRight
      (C := MonoidalPresheaf X)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
      ((toPresheafOfModules X).obj C)))
      (isIso_sheafification_whiskerRight_unit _ _)).hom).mp ?_
  refine Eq.trans ?_ (Iso.hom_inv_id _).symm
  rw [asIso_hom,
    sheafification_whiskerRight_unit_eq_mu' (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)) ((toPresheafOfModules X).obj C)]
  simp only [tensorObj]
  -- The middle `μ_X.hom ≫ μ_X.inv` cancel straddles the `modulesLocalizedMonoidal`↔`X.Modules` comp
  -- boundary (plain `rw [assoc]` no-match; `erw [assoc]` whnf-bombs μ).  Re-elaborate uniformly in the
  -- localized comp (`show`, defeq cross), then the cancel + whisker-merge + triangle fire with plain `rw`.
  show
    ((Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C)).inv ≫
        (MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.toMonoidalCategory (PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)) (Wsheaf X) (localizedMonoidalUnitIso X)).map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                  ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
            ((Localization.Monoidal.toMonoidalCategory (PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)) (Wsheaf X) (localizedMonoidalUnitIso X)).obj
              ((toPresheafOfModules X).obj C)) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)
            ((toPresheafOfModules X).obj
              (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
            ((toPresheafOfModules X).obj C)).hom)) ≫
      ((Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)
            ((toPresheafOfModules X).obj
              (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
            ((toPresheafOfModules X).obj C)).inv ≫
        (MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A)
              ((toPresheafOfModules X).obj B))).sheafificationCounitIso.hom
            (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C)).hom)) = 𝟙 _
  simp only [Category.assoc]
  -- RESIDUAL (single μ-pair cancel): goal is now the FLAT, uniform-comp
  --   `μ₂'.inv ≫ (L'η ▷) ≫ μ_X.hom ≫ μ_X.inv ≫ (c_{A⊗B} ▷) ≫ μ₂'.hom = 𝟙`.
  -- Mathematically: `μ_X.hom ≫ μ_X.inv = 𝟙`, then `(L'η ≫ c_{A⊗B}) ▷ = 𝟙 ▷ = 𝟙`
  -- (`comp_whiskerRight` + `left_triangle_components`), then `μ₂'.inv ≫ μ₂'.hom = 𝟙`.
  -- BLOCKER (iter-015, cold-probed): the two `μ_X` occurrences print identically but are NOT
  -- token-identical — `μ_X.hom` originates from the keystone expansion of `s1.hom`, `μ_X.inv` from this
  -- lemma's statement (after `simp [tensorObj]`).  EVERY cancel route bombs on the heavy
  -- `Localization.Monoidal.μ` term:  `rw [Iso.hom_inv_id_assoc]` → "pattern not found" (the two `?self`
  -- don't syntactically unify at reducible transparency);  `slice_lhs 3 4 => rw [Iso.hom_inv_id]` /
  -- `simp [Iso.hom_inv_id]` → `(deterministic) timeout at isDefEq` (confirming the μ's must be
  -- isDefEq-checked, which whnf-expands μ → `Localization.fac` → bomb).  This is the SAME
  -- μ-syntactic-identity wall as the `hK_lhs` interchange merge.  FIX for iter-016: make the two `μ_X`
  -- token-identical — restate `tensorObjAssoc_hK_lhs_head`'s leading μ with the keystone's pinned object
  -- `(toPresheafOfModules X).obj (sheafification.obj (A♭⊗B♭))` (NOT `(A.tensorObj B)`) so no `simp`
  -- normalization is needed and `Iso.hom_inv_id_assoc` unifies `?self` syntactically; then the
  -- whisker-merge + triangle tail (already written above, GREEN past the cancel) closes it.
  -- iter-016: STATEMENT-level instance pinning (μ object-args to `MonoidalPresheaf X`) made the two
  -- μ-pairs defeq-compatible; the cancel fires with `erw` (reducible transparency, NOT plain `rw`).
  erw [Iso.hom_inv_id_assoc]
  -- Residual: `μ₂'.inv ≫ (L'η ▷ Z) ≫ (c ▷ Z) ≫ μ₂'.hom = 𝟙`.  Re-elaborate the two whiskered
  -- factors uniformly in `sheafification` form (the keystone prints `L'η`/`Z` via the
  -- `toMonoidalCategory` wrapper; `sheafification.map`/`sheafification.obj` are defeq — cheap, no
  -- μ-whnf), so `comp_whiskerRight` merges them; then the adjunction triangle `L'η ≫ c = 𝟙`
  -- collapses the whisker and the outer μ-pair cancels.
  show
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
          ((toPresheafOfModules X).obj C)).inv ≫
      (MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
          (sheafification.obj ((toPresheafOfModules X).obj C))) ≫
        (MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A)
              ((toPresheafOfModules X).obj B))).sheafificationCounitIso.hom
            (sheafification.obj ((toPresheafOfModules X).obj C))) ≫
          (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C)).hom = 𝟙 _
  -- The two whiskered factors collapse to `𝟙`: merge by `comp_whiskerRight` (`erw` bridges the defeq
  -- `(L'⋙…).obj P` ↔ `(L'P)♭` middle object), then the adjunction triangle `L'η ≫ c = 𝟙`.  Proved as
  -- an ISOLATED `have` because the triangle `rw` only fires here — inside the full goal its motive
  -- re-typechecks the surrounding `μ`'s and isDefEq-bombs.
  have hmid :
      MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
          (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            ((toPresheafOfModules X).obj B))).sheafificationCounitIso.hom
          (sheafification.obj ((toPresheafOfModules X).obj C))
      = 𝟙 _ := by
    erw [← MonoidalCategory.comp_whiskerRight, sheafification_map_unit_comp_counitIso_hom,
      MonoidalCategory.id_whiskerRight]
  -- Collapse the middle factor, then the outer μ-pair (`μ₂'` and the statement's `midμ`, now
  -- token-identical from the statement-level pinning) cancels.
  slice_lhs 2 3 => erw [hmid]
  -- `𝟙 ≫ midμ.hom` is defeq `midμ.hom`; close by `μ₂'.inv ≫ midμ.hom = 𝟙` in term mode (a rewrite
  -- here re-typechecks the surrounding μ-objects and isDefEq-bombs).
  exact Iso.inv_hom_id _

/-- **Image-form (unfolded-`sheafification`) restatement of the head reduction**, token-identical to the
post-chain goal of `tensorObjAssoc_hK_lhs_native`.  The closed head lemma `tensorObjAssoc_hK_lhs_head`
is stated in a MIXED spelling (leading μ in image form, the whiskered counit at the FOLDED
`A.tensorObj B`); after the native chain applies `simp only [sheafification, …]` the goal's whole prefix
is in UNFOLDED `PresheafOfModules.sheafification (𝟙 _)` + image-`tensorObj` form, so applying the folded
head lemma forces the unifier to whnf the localized μ to reconcile the fold mismatch (200000-hb bomb).
This restatement is the head lemma normalised by `simp only [sheafification, tensorObj]` so it matches
the native goal SYNTACTICALLY; `@[reassoc]` then gives the suffixed sibling whose `exact … _` binds the
heavy `tail` to its `?g` metavar with no whnf.  Proof: `simpa` from the folded head lemma (the simp set
is pure delta-unfolds — no μ whnf). -/
@[reassoc]
private lemma tensorObjAssoc_hK_lhs_head_img (A B C : X.Modules) :
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          ((toPresheafOfModules X).obj
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
              ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C)).inv ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (sheafificationCounitIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
            ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B))).hom
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj ((toPresheafOfModules X).obj C)) ≫
        (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B)
          ((toPresheafOfModules X).obj C)).hom
      = (@asIso _ _ _ _
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                  ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
              ((toPresheafOfModules X).obj C)))
          (isIso_sheafification_whiskerRight_unit
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C))).inv := by
  have h := tensorObjAssoc_hK_lhs_head A B C
  simpa only [sheafification, tensorObj, Localization.Monoidal.toMonoidalCategory] using h

/-- **Native (image-form) reassociation+associator step for `hK_lhs`** (`lem:tensorObjAssoc_hK_lhs_native`,
recipe `analogies/snap-reassoc-pin.md` Part A).  This is the post-`hsplit` goal of `hK_lhs` with the
LEADING μ-object written in UNFOLDED image form `sheafification.obj (tensorObj (C := MonoidalPresheaf X)
A♭ B♭)` (NOT the folded `A.tensorObj B`).  With every μ-object pinned to image form, the reassociation
`(W ≫ T) ≫ α → W ≫ (T ≫ α)` and the subsequent `associator_naturality`/`associator_hom_app` fire
syntactically (no `whnf` of the folded `tensorObj` → no `Localization.fac` bomb).  This is the iter-016
head-lemma statement-pinning generalised from the head reduction to the reassoc step. -/
private lemma tensorObjAssoc_hK_lhs_native (A B C : X.Modules) :
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          ((toPresheafOfModules X).obj (A.tensorObj B))
          ((toPresheafOfModules X).obj C)).inv ≫
        (MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            ((A.tensorObj B).sheafificationCounitIso.hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
                  (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj A)
                  ((toPresheafOfModules X).obj B)).inv)
            (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
          MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
            (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
              A.sheafificationCounitIso.hom B.sheafificationCounitIso.hom)
            C.sheafificationCounitIso.hom) ≫
        (MonoidalCategoryStruct.associator (C := modulesLocalizedMonoidal X)
          (A : modulesLocalizedMonoidal X) B C).hom
      = assocCommonForm A B C := by
  -- The statement is in FOLDED form (verbatim the post-`hsplit` `hK_lhs` goal) so `hK_lhs` closes by a
  -- syntactic `exact`.  Image-ise the goal once with a cheap `simp only [tensorObj]` (delta-unfold of
  -- `Scheme.Modules.tensorObj`, no μ whnf) so every μ-object is in `sheafification.obj (A♭⊗B♭)` image
  -- form and the reassoc/`associator_*` chain below fires syntactically.
  simp only [tensorObj]
  -- Objects are all pinned image-forms, so the reassoc + naturalise fire syntactically (no μ whnf).
  -- Reassociate `(W ≫ T) ≫ α → W ≫ T ≫ α` then push the counit isos through `α` (native-ising it to
  -- `α_ (L'A♭)(L'B♭)(L'C♭)`).  Keep the RHS `assocCommonForm` FOLDED (small) — expanding the associator
  -- AND `K` together makes a ~13-μ-factor goal that isDefEq-bombs on every slice/rw.
  rw [Category.assoc, Localization.Monoidal.associator_naturality]
  -- Expand the native associator, unfold the `toMonoidalCategory`/`sheafification` functor spellings so
  -- every object is the SAME `(PresheafOfModules.sheafification …).obj _` form, then `simp` flattens.
  erw [Localization.Monoidal.associator_hom_app]
  -- Unfold the `sheafification`/`toMonoidalCategory` functor spellings so every object is the SAME
  -- `(PresheafOfModules.sheafification …).obj _` form; convert `μ.hom ⊗ₘ 𝟙 → μ.hom ▷ _`,
  -- `𝟙 ⊗ₘ μ.inv → _ ◁ μ.inv`, and flatten.
  simp only [sheafification, Localization.Monoidal.toMonoidalCategory,
    Localization.Monoidal.tensorHom_id, Localization.Monoidal.id_tensorHom, Category.assoc]
  -- Merge the two right-whiskers `(c ≫ μ.inv) ▷ Z ≫ μ.hom ▷ Z → ((c ≫ μ.inv) ≫ μ.hom) ▷ Z` (the
  -- `erw` bridges the `modulesLocalizedMonoidal X` ↔ `LocalizedMonoidal …` whiskerRight-instance
  -- spelling; isolated to the merge so it does NOT whnf the μ's).
  erw [← Localization.Monoidal.whiskerRight_comp_assoc]
  -- Cancel the merged `μ_{A♭,B♭}.inv ≫ μ_{A♭,B♭}.hom = 𝟙` INSIDE the whisker arg (the two μ's are
  -- defeq-not-token-identical, so the cancel needs `erw`; isolate it in `conv` so the `erw` whnf stays
  -- local and does not blow up the surrounding μ's).  Leaves the head whisker as the bare counit `c_{A⊗B}`.
  conv_lhs => enter [2, 1]; rw [Category.assoc]; erw [Iso.inv_hom_id]
  erw [Category.comp_id]
  -- GOAL NOW (cold-verified bomb-free up to here): the head `μ.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom`
  -- is EXACTLY `tensorObjAssoc_hK_lhs_head A B C` and the trailing `tail`
  -- (`L'(α^p) ≫ μ_{A♭,B♭⊗C♭}.inv ≫ (L'A♭ ◁ μ_{B♭,C♭}.inv) ≫ (c_A ⊗ₘ c_B ⊗ₘ c_C)`) is `assocCommonForm`'s
  -- tail.  So mathematically the goal is `(tensorObjAssoc_hK_lhs_head A B C) ≫= tail`, i.e. CLOSED by the
  -- already-proven head lemma.
  -- GOAL NOW: `μ.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom ≫ tail = K`, whose 3-factor prefix is
  -- EXACTLY `tensorObjAssoc_hK_lhs_head A B C` and whose `tail` is `assocCommonForm`'s tail.
  -- SUFFIX-REMOVAL (iter-019, `analogies/snap-suffix-cancel.md`): every direct application of the head
  -- lemma over this goal whnf-bombs (the unifier re-checks the `LocalizedMonoidal`↔`modulesLocalizedMonoidal
  -- X` comp-instance over the heavy `Localization.Monoidal.μ` terms in `tail`).  FIX: first re-spell the
  -- folded RHS `assocCommonForm = s1.inv ≫ tail` with the SAME unfolding `simp` the chain applied to the
  -- LHS so the two `tail`s become token-identical; THEN the `@[reassoc]`-generated head sibling
  -- `tensorObjAssoc_hK_lhs_head_assoc` applies by plain `exact` — the `tail` binds to its `?g` metavar by
  -- structural `≫`-match (never `whnf`'d) and the prefix factors unify by cheap object-fold defeq.
  -- (`reassoc_of%` at the use-site instead bombs: its internal `simp` whnf-unfolds the localized μ.)
  conv_rhs => rw [assocCommonForm]; simp only [sheafification,
    Localization.Monoidal.toMonoidalCategory, Localization.Monoidal.tensorHom_id,
    Localization.Monoidal.id_tensorHom, Category.assoc]
  -- `…_head_assoc A B C` is `∀ (h), prefix ≫ h = s1.inv ≫ h`; supply the heavy `tail` as the
  -- explicit `h` via `_` so it binds by structural `≫`-match (never `whnf`'d).  The prefix factors
  -- GOAL HERE (chain runs bomb-free to this point, cold-verified): `prefix ≫ tail = s1.inv ≫ tail`,
  -- where `prefix = μ.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom` is EXACTLY the proven head lemma
  -- `tensorObjAssoc_hK_lhs_head A B C : prefix' = s1.inv'` and `tail` is `assocCommonForm`'s tail.
  --
  -- REMAINING WALL (iter-019, precisely isolated): applying the head lemma here requires `prefix` to be
  -- TOKEN-IDENTICAL to the head lemma's `prefix'`, but they diverge in spelling — the native chain's
  -- `simp only [sheafification, toMonoidalCategory, tensorHom_id, id_tensorHom]` (post-`associator_hom_app`)
  -- normalised THIS goal's prefix, while the head lemma is stated in the MIXED folded/image spelling.
  -- Every bridge attempted bombs:
  --   • `exact tensorObjAssoc_hK_lhs_head_assoc A B C _` (folded `@[reassoc]` sibling)  → whnf timeout
  --     (folded↔unfolded `sheafification`/`tensorObj` over the localized-comp μ, 200000 hb);
  --   • `exact tensorObjAssoc_hK_lhs_head_img_assoc A B C _` (hand-transcribed image-form sibling, COMPILES)
  --     → isDefEq timeout (residual `▷` instance spelling: the chain's `simp [toMonoidalCategory]` unfolds
  --     the localized whiskerRight instance, the image lemma keeps the `modulesLocalizedMonoidal X` synonym);
  --   • `simp only [sheafification, tensorObj, toMonoidalCategory, tensorHom_id, id_tensorHom,
  --     Category.assoc] at key` (normalise the head lemma into the goal's spelling, then `reassoc_of% key`)
  --     → the `simp at key` itself whnf-bombs: `key` carries the μ-at-composite-object `c_{A⊗B} ≫ μ.inv`
  --     that the post-native-isation goal no longer has, so the SAME simp set that is bomb-free on the
  --     goal whnf-unfolds μ→`Localization.fac` when run on `key`.
  -- ROOT: the localized whiskerRight/μ spelling produced by `simp [toMonoidalCategory]` on the chain goal
  -- is NOT reproducible on the head lemma without re-incurring the μ-whnf bomb — the token-divergence wall
  -- documented in `analogies/snap-mu-identity.md` / `snap-reassoc-pin.md`.  This is the precise step the
  -- iter-020 REFACTOR PIVOT (glue Option A: rewire the hand-built defs onto the `LocalizedMonoidal` synonym
  -- ⊗ so the bridges become definitional and the comp-instance boundary disappears) is queued to resolve.
  -- The reusable image-form head reduction `tensorObjAssoc_hK_lhs_head_img` (above, COMPILES sorry-free)
  -- is the head equation already in unfolded form for that pivot.
  --
  -- RESIDUAL WALL (iter-019, fully isolated and cold-build characterised).  GOAL HERE is
  -- `prefix ≫ tail = s1.inv ≫ tail` with `prefix = μ.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom`
  -- EXACTLY the proven head lemma `tensorObjAssoc_hK_lhs_head A B C` and `tail` a composite of isos.
  -- Every route to apply the head lemma bombs (each cold-build verified, 200000 hb):
  --   • `exact tensorObjAssoc_hK_lhs_head_assoc A B C _` (folded `@[reassoc]` sibling) → whnf timeout;
  --   • `exact tensorObjAssoc_hK_lhs_head_img_assoc A B C _` (image-form sibling, COMPILES) → isDefEq;
  --   • `have key := …head…; simp only [sheafification, tensorObj, toMonoidalCategory, tensorHom_id,
  --     id_tensorHom, Category.assoc] at key; exact reassoc_of% key` → the `simp at key` whnf-bombs
  --     (`key` carries the μ-at-composite-object `c_{A⊗B} ≫ μ.inv` the post-native-isation goal lacks);
  --   • `rw [cancel_mono]` (strip the iso `tail` to isolate `prefix = s1.inv`) → bombs at the rewrite
  --     itself: matching `?g ≫ ?f = ?h ≫ ?f` forces an associativity-reconciliation isDefEq over the
  --     heavy right-associated goal, which whnf-unfolds μ.
  -- ROOT: the localized whiskerRight/μ spelling the native chain produced (via `associator_hom_app` +
  -- `simp [sheafification, toMonoidalCategory, tensorHom_id, id_tensorHom]`) is NOT reproducible on the
  -- head lemma without re-incurring the μ-whnf bomb — the project-local DUAL-`MonoidalCategory`-instance
  -- μ-token-divergence wall (`analogies/snap-mu-identity.md`, `snap-reassoc-pin.md`).  Resolution is the
  -- queued iter-020 REFACTOR PIVOT (glue Option A: rewire the hand-built `tensorObj*` defs onto the
  -- `LocalizedMonoidal` synonym ⊗ so the bridges become definitional and this comp-instance boundary —
  -- the sole source of the spelling divergence — disappears).  The reusable image-form head reduction
  -- `tensorObjAssoc_hK_lhs_head_img` (above, COMPILES sorry-free) is the head equation already in
  -- unfolded form for that pivot.  Everything ELSE in `hK_lhs`/`hK_rhs`/the assembly is CLOSED; this
  -- single 3-factor prefix equation is the last open node of the associator bridge.
  -- iter-020 PROBE (cold-build VERIFIED DEAD): `congr 1` splits `prefix ≫ tail = s1.inv ≫ tail` and
  -- the LSP REPL closes it (its internal `rfl` does the full `prefix = s1.inv` defeq within 200000 hb),
  -- but the full-declaration cold build whnf-BOMBS (`(deterministic) timeout at whnf` @decl head) —
  -- `congr`'s `rfl` re-incurs the same μ-token-divergence whnf as every other route.  Likewise dead
  -- (all cold-verified iter-020): `exact tensorObjAssoc_hK_lhs_head_img_assoc A B C _` (whnf timeout —
  -- the `?Z` codomain forces suffix unification); `exact (head_img) =≫ _` (whnf — prefix divergence);
  -- `rw [← head_img]` (isDefEq timeout — kabstract over the heavy goal).  ROOT unchanged: the chain's
  -- `simp [toMonoidalCategory]` whiskerRight-instance spelling is NOT token-identical to head_img's
  -- `modulesLocalizedMonoidal X` synonym spelling, so EVERY application unifies the divergent prefix →
  -- μ-whnf bomb (`analogies/snap-mu-identity.md`).  Resolution is the queued iter-020 REFACTOR PIVOT
  -- (glue Option A), NOT a further prover route.  `tensorObjAssoc_hK_lhs_head_img` (above, sorry-free)
  -- is the head equation already in the unfolded form that pivot needs.
  -- iter-020 (continuation) — TWO further NEW routes cold/LSP-VERIFIED DEAD, both pinpointing the
  -- SAME root (do NOT re-attempt):
  --   • PREVENT the divergence upstream: drop `Localization.Monoidal.toMonoidalCategory` from the
  --     merge `simp only` (@~L2139) so the goal's `▷` stays in folded `modulesLocalizedMonoidal X`
  --     synonym form matching head_img.  REFUTED: `toMonoidalCategory` is LOAD-BEARING — without it
  --     the `erw [← whiskerRight_comp_assoc]` merge (@~L2144) and the μ-pair cancel (@~L2148) no
  --     longer fire (isDefEq timeout @L2144; the head whisker `(c ≫ μ.inv) ▷` is left unmerged).
  --   • MATCH the spelling on the head side: `have h := tensorObjAssoc_hK_lhs_head_img A B C;
  --     simp only [sheafification, toMonoidalCategory, tensorHom_id, id_tensorHom, Category.assoc]
  --     at h; (rw|exact) reassoc_of% h`.  REFUTED: the `simp … at h` itself whnf-BOMBS (200000 hb).
  --     ASYMMETRY (the precise mechanism): the SAME simp set fires bomb-free on the GOAL because the
  --     goal carries productive `μ.hom ⊗ₘ 𝟙 → ▷` / `𝟙 ⊗ₘ μ.inv → ◁` redexes (from
  --     `associator_hom_app`) that simp rewrites WITHOUT whnf'ing the deep μ; head_img has NO such
  --     redexes (`tensorHom_id`/`id_tensorHom` report "unused"), so `toMonoidalCategory` is forced to
  --     unfold structurally over the μ-laden terms → whnf bomb.  CONCLUSION: the goal's
  --     `toMonoidalCategory`-unfolded `▷` spelling is producible ONLY through the productive native
  --     chain, NEVER reproducible on the head equation in isolation.  This is exactly the
  --     μ-token-divergence wall; the ONLY resolution is the structural refactor (glue Option A:
  --     definitionally rewire `tensorObj*` onto the synonym ⊗ so no `toMonoidalCategory` unfold is
  --     ever needed), a plan/refactor-agent task, NOT a prover route.
  --
  -- iter-021 (NEW cold-build evidence — do NOT re-attempt): the divergence is precisely the `▷`
  -- whiskerRight *instance* on the single `c_{A⊗B} ▷ L'C♭` factor (goal: `simp [toMonoidalCategory]`-
  -- unfolded instance; head equation `tensorObjAssoc_hK_lhs_head_img`: `modulesLocalizedMonoidal X`
  -- synonym instance).  Attempted the most surgical possible fix — `conv_lhs => enter [2, 1];
  -- change MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X) c_{A⊗B} L'C♭`,
  -- i.e. an ISOLATED local defeq of JUST that one small whisker subterm (no μ syntactically inside
  -- it), then `exact tensorObjAssoc_hK_lhs_head_img_assoc A B C _`.  COLD-BUILD VERIFIED DEAD: the
  -- `change` ALONE times out at `isDefEq` (200000 hb).  CONCLUSION: reconciling the two whiskerRight
  -- *instances* is itself the bomb — `Localization.Monoidal.toMonoidalCategory`'s `whiskerRight`
  -- field is defined via the localization lift and comparing it to the synonym instance forces a
  -- whnf of the localized μ, *independently of any heavy tail*.  This is the irreducible
  -- dual-`MonoidalCategory`-instance μ-token-divergence (`analogies/snap-mu-identity.md`); the ONLY
  -- resolution is the queued iter-020/021 REFACTOR PIVOT (glue Option A: rewire `tensorObj*` onto
  -- the `LocalizedMonoidal` synonym ⊗ so the `toMonoidalCategory` unfold — the sole source of the
  -- instance divergence — never arises).  `tensorObjAssoc_hK_lhs_head_img` (sorry-free) is the head
  -- equation already in the unfolded form that pivot needs.
  sorry

/-- **Localized half-assembly of the associator bridge equals the common form**
(`lem:tensorObjAssoc_hK_lhs`).  The localized side `Φ^L ≫ α^loc` of the bridge equals the common
form `K = assocCommonForm A B C`. -/
private lemma tensorObjAssoc_eq_localizedAssociator_hK_lhs (A B C : X.Modules) :
    (tensorObjLocalizedIso (tensorObj A B) C).hom ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (tensorObjLocalizedIso A B).hom (C : modulesLocalizedMonoidal X) ≫
        (MonoidalCategoryStruct.associator (C := modulesLocalizedMonoidal X)
          (A : modulesLocalizedMonoidal X) B C).hom
      = assocCommonForm A B C := by
  rw [assocCommonForm]
  simp only [tensorObjLocalizedIso, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
    Category.assoc]
  -- ISOLATED localized-side goal: LHS = `μ_{(A⊗B)♭,c}.inv ≫ (c_{A⊗B} ⊗ c_C) ≫ ((μ_{a,b}.inv ≫
  -- (c_A⊗c_B)) ▷ C) ≫ (α_ A B C).hom`; RHS = K.  Unlike `hK_rhs` there is no whiskered unit here,
  -- so the route is to convert `α_ A B C` (arbitrary objects) to `α_ (L'a)(L'b)(L'c)` by pushing
  -- the counit isos `c_A,c_B,c_C` through it with `Localization.Monoidal.associator_naturality`
  -- (+ `tensorHom_id`/`id_tensorHom` to turn `▷`/`◁` into `⊗ₘ`); THEN `associator_hom_app` fires,
  -- making the `μ`'s native so the `μ`-pairs cancel by `Iso.hom_inv_id_assoc` and `μ_natural_*` +
  -- the counit triangle leave K.  (`associator_hom_app` does NOT fire on `α_ A B C` directly —
  -- verified: its LHS pattern requires the objects to be literally `(L').obj _`.)
  --
  -- iter-014 COLD-PROBE (per pc014 WATCH — STOP + surface precisely, do NOT finer-μ-chase):
  --   • `rw [Localization.Monoidal.associator_hom_app]` — NO MATCH: pattern needs
  --     `α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)`, goal has `α_ A B C` (A,B,C arbitrary
  --     `X.Modules`, not `(L').obj _`).  Confirms the comment above.
  --   • `rw [Localization.Monoidal.associator_naturality]` (fwd) — NO MATCH: needs prefix
  --     `((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom`; the goal's prefix before `α_ A B C` is
  --     `(c_{A⊗B} ⊗ₘ c_C) ≫ ((μ_{A,B}.inv ≫ (c_A ⊗ₘ c_B)) ▷ C)`, NOT `((c_A⊗ₘc_B)⊗ₘc_C)`.
  --   EXPOSURE the iter-015 analogist must map out: split `(μ.inv ≫ (c_A⊗ₘc_B)) ▷ C` via
  --   `comp_whiskerRight` + `tensorHom_id` into `(μ_{A,B}.inv ▷ C) ≫ ((c_A⊗ₘc_B) ⊗ₘ 𝟙_C)`, then
  --   `associator_naturality c_A c_B (𝟙 C)` exposes `α_ (L'A♭) (L'B♭) C` — but C is STILL not an
  --   `(L').obj _`, so a SINGLE naturality cannot make all three `μ`'s native; the `c_{A⊗B}` slot
  --   (a counit at the COMPOSITE object `A⊗B`, not `L'A♭⊗L'B♭`) is the genuine obstacle (it must
  --   first be related to `μ_{A,B}` + `(c_A⊗ₘc_B)`).  Once `α` is fully at `(L').obj _`,
  --   `associator_hom_app` fires and the SAME `show`-uniform + `simp [tensorHom_comp_tensorHom]` +
  --   `congr`/`left_triangle_components_assoc` close that landed `hK_rhs` (@~L1976) applies.
  -- Step 0: re-elaborate the LHS uniformly in the `modulesLocalizedMonoidal X` comp (hK_rhs template).
  show
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj (A.tensorObj B))
          ((toPresheafOfModules X).obj C)).inv ≫
      MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
          (A.tensorObj B).sheafificationCounitIso.hom C.sheafificationCounitIso.hom ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            ((Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
                  (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj A)
                  ((toPresheafOfModules X).obj B)).inv ≫
              MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
                A.sheafificationCounitIso.hom B.sheafificationCounitIso.hom) C ≫
          (MonoidalCategoryStruct.associator (C := modulesLocalizedMonoidal X) A B C).hom =
      assocCommonForm A B C
  -- NB: do NOT `rw [assocCommonForm]` here.  The proof closes with `exact tensorObjAssoc_hK_lhs_native`,
  -- whose RHS is the FOLDED `assocCommonForm A B C`; expanding the RHS would force the final `exact` to
  -- delta-unfold + compare μ-laden expansions (whnf bomb).  Keep the RHS folded so the `exact` matches.
  -- Step 0 (above `show`) and Step 1a below are mechanized and GREEN.  Step 1's interchange MERGE
  -- is the WALL (iter-015, cold-probed): exposing `((c_A⊗ₘc_B)⊗ₘc_C) ≫ α` for `associator_naturality`
  -- needs `(c_{A⊗B} ⊗ₘ c_C) ≫ ((μ_{A♭,B♭}.inv ≫ (c_A⊗ₘc_B)) ⊗ₘ 𝟙 C)` merged by `tensor_comp` /
  -- `tensorHom_comp_tensorHom`.  Both FAIL: plain `rw` → "pattern not found" (only reducible
  -- transparency); `conv`/`erw` → `(kernel/whnf) deterministic timeout` (200000 hb).  Root cause: the
  -- merge straddles the `c_{A⊗B} ≫ μ_{A♭,B♭}.inv` junction at the COMPOSITE object `A⊗B = L'(A♭⊗B♭)`,
  -- so unifying the goal's `≫` (`instCategoryLocalizedMonoidal`) with the lemma's `≫`
  -- (`toMonoidalCategory.toCategory`) forces whnf of `Localization.Monoidal.μ` (→ `Localization.fac`)
  -- and bombs.  hK_rhs's analogous `simp [tensorHom_comp_tensorHom]` merge succeeded precisely BECAUSE
  -- its tensorHoms do NOT straddle a μ-at-composite-object junction; hK_lhs's do (the asymmetric
  -- `c_{A⊗B}` slot).  The downstream head reduction is isolated below as `tensorObjAssoc_hK_lhs_head`
  -- (recipe Step 5, provable independently of this merge).  SURFACED for iter-016 (do NOT warm-retry):
  -- the blocker is the interchange merge across the μ-composite junction, NOT the head reduction.
  -- Step 1a: ▷ C → ⊗ₘ 𝟙 C  (GREEN)
  rw [← Localization.Monoidal.tensorHom_id]
  -- Step 1 (interchange MERGE — the iter-015 WALL).  iter-016: the merge bombs in the FULL goal
  -- (its `rw` motive re-typechecks the surrounding μ's → isDefEq blowup), but fires cleanly when
  -- ISOLATED to the two `⊗ₘ` factors via `slice` (local motive) with `erw` (bridges the localized
  -- comp boundary).  This is the SAME isolation idiom that closed `tensorObjAssoc_hK_lhs_head`.
  slice_lhs 2 3 => erw [← Localization.Monoidal.tensor_comp]
  -- Clean the `c_C ≫ 𝟙 C` leg.  GREEN.
  simp only [Category.comp_id]
  -- REMAINING (recipe `analogies/snap-assoc-expose.md`, now unblocked by the closed head lemma
  -- `tensorObjAssoc_hK_lhs_head` and the iter-016 slice+erw isolation idiom):
  --   (a) re-split the merged factor `(c_{A⊗B} ≫ μ_{A♭,B♭}.inv ≫ (c_A⊗ₘc_B)) ⊗ₘ c_C` into
  --       `((c_{A⊗B}≫μ_{A♭,B♭}.inv) ▷ L'C♭) ≫ ((c_A⊗ₘc_B) ⊗ₘ c_C)` (group via `← Category.assoc`
  --       on the ⊗ₘ first arg + `← Category.id_comp c_C` + `tensor_comp`, all inside a `conv`/`slice`
  --       focused on the single ⊗ₘ to keep the rewrite motive off the surrounding μ's);
  --   (b) `Localization.Monoidal.associator_naturality c_A c_B c_C` native-ises `α_ A B C` to
  --       `α_ (L'A♭)(L'B♭)(L'C♭)` (verified: the prefix `((c_A⊗ₘc_B)⊗ₘc_C) ≫ α` then matches);
  --   (c) `Localization.Monoidal.associator_hom_app` expands the native α; the `μ_{A♭,B♭}` pair on
  --       the `▷ L'C♭` slot cancels via `← comp_whiskerRight` + `Iso.inv_hom_id` (use the isolated
  --       slice idiom — `erw` for the localized-comp boundary);
  --   (d) the residual head `μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom` is exactly
  --       `(tensorObjAssoc_hK_lhs_head A B C)` — `rw`/`erw [tensorObjAssoc_hK_lhs_head]`; the tail
  --       (`L'(α^p)` onward) is already identical to `K`.
  -- The merge WALL (iter-015) is now defeated (`slice_lhs 2 3 => erw [← tensor_comp]` above); the
  -- remaining steps are the mechanical recipe tail.
  --
  -- iter-017: HARD-GATE on slice step (a) hit (the `slice`/`conv` re-split isDefEq-bombs), so we use
  -- the SANCTIONED ALTERNATIVE isolation mechanism — a standalone `have` + `congrArg`-peel of the
  -- WHOLE outer context (NO full-goal `rw`, NO kabstract over the leading μ → no bomb).
  --
  -- Step (a): re-split the merged factor `(c_{A⊗B} ≫ μ.inv ≫ (c_A⊗ₘc_B)) ⊗ₘ c_C` into
  -- `((c_{A⊗B} ≫ μ.inv) ▷ L'C♭) ≫ ((c_A⊗ₘc_B) ⊗ₘ c_C)`.  Proven as an ISOLATED `have` (its goal has
  -- the inner μ.inv but NO surrounding outer μ, so `← tensorHom_id`/`← tensor_comp` fire cleanly; the
  -- residual assoc/id-cleanup is done by `congr 1` + term-mode `Category.assoc`/`id_comp`, NOT a
  -- full-goal `rw [Category.assoc]` which kabstract-bombs).
  have hsplit :
      MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
          ((A.tensorObj B).sheafificationCounitIso.hom ≫
            (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
                (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)).inv ≫
              MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
                A.sheafificationCounitIso.hom B.sheafificationCounitIso.hom)
          C.sheafificationCounitIso.hom
        = MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            ((A.tensorObj B).sheafificationCounitIso.hom ≫
              (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
                  (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)).inv)
            (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
          MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
            (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
              A.sheafificationCounitIso.hom B.sheafificationCounitIso.hom)
            C.sheafificationCounitIso.hom := by
    rw [← Localization.Monoidal.tensorHom_id, ← Localization.Monoidal.tensor_comp]
    congr 1 <;> first | exact (Category.assoc _ _ _).symm | exact (Category.id_comp _).symm
  refine (congrArg (fun t =>
      (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
        (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj (A.tensorObj B))
        ((toPresheafOfModules X).obj C)).inv ≫ t ≫ _) hsplit).trans ?_
  -- iter-017 STATE: step (a) is DONE and cold-build GREEN.  Goal is now
  --   `μ_{(A⊗B)♭,C♭}.inv ≫ ((W ≫ T) ≫ (α_ A B C).hom) = K`
  -- with `W = (c_{A⊗B} ≫ μ_{A♭,B♭}.inv) ▷ L'C♭`, `T = (c_A⊗ₘc_B)⊗ₘc_C`.  The next recipe move is the
  -- reassociation `(W ≫ T) ≫ α  →  W ≫ (T ≫ α)` so that `associator_naturality` (step b) can fire on
  -- `T ≫ α` (VERIFIED in true isolation: `rw [Localization.Monoidal.associator_naturality,
  -- associator_hom_app]` fires bomb-free on a goal whose LHS is literally `W ≫ T ≫ α`).
  --
  -- NEW WALL (iter-017, distinct from the iter-015 merge wall and the step-(a) re-split): the
  -- reassociation is BLOCKED in every available mechanism by the localized-tensor OBJECTS (the μ at
  -- `sheafification.obj (A♭ ⊗ B♭)` and the `c_{A⊗B} ≫ μ_{A♭,B♭}.inv` junction, whose codomain
  -- `L'A♭ ⊗_loc L'B♭` is `(toMonoidalCategory …).obj`-defeq-not-syntactic to `A.tensorObj B`):
  --   • `rw [Category.assoc]`  → isDefEq/whnf timeout (motive re-typechecks the localized objects);
  --   • `simp only [Category.assoc]`  → whnf timeout (same; even after `simp only [tensorObj]`);
  --   • `conv_lhs => enter [2]; rw [Category.assoc]`  → whnf timeout even though `enter [2]` correctly
  --     drops the leading μ from the focus (the kabstract over `(W≫T)≫α` alone still bombs);
  --   • `refine (congrArg (μ.inv ≫ ·) (Category.assoc _ _ _)).trans ?_`  → isDefEq timeout: the
  --     `Category.assoc` OBJECT metavars, when solved against the goal's localized tensors via `.trans`,
  --     whnf the μ.  (Contrast: step (a)'s `congrArg … hsplit` is bomb-free precisely because `hsplit`'s
  --     two sides are EXACT goal subterms — no fresh object inference.)
  --   • isolated-`have` route for the reassoc/associator is ALSO blocked: STATING the `whiskerRight
  --     (c_{A⊗B} ≫ μ_{A♭,B♭}.inv) (L'C♭) ≫ … ≫ α` junction freshly isDefEq-bombs at elaboration
  --     (the `c_{A⊗B} ≫ μ.inv` codomain + the trailing `≫ α` over-constrain; `hsplit` elaborates only
  --     because its RHS type flows from the goal/`M`, and the head lemma's `▷` is bare `c_{A⊗B}`, not the
  --     `c_{A⊗B} ≫ μ.inv` composite).
  -- ⇒ The only bomb-free transformer is an equation whose sides are EXACT current-goal subterms (à la
  -- `hsplit`); a generic `Category.assoc`/associator with fresh objects always whnf's the localized
  -- μ-objects.  RESOLVED (iter-019): after the `hsplit` `congrArg`, the goal is exactly the statement of
  -- `tensorObjAssoc_hK_lhs_native A B C` (the post-split reassociation lemma stated with every μ-object in
  -- unfolded `(L').obj _` image form), modulo cheap object-fold defeq (`A.tensorObj B` ↔
  -- `sheafification.obj (A♭⊗B♭)` and `assocCommonForm` ↔ its expansion).  `native` carries out the
  -- reassociation + associator-naturalisation + μ-cancel + head reduction; close by `exact`.
  -- `native` is now stated in FOLDED form (verbatim this goal), so the `exact` is syntactic — no
  -- `simp only [tensorObj]` here (which would change the equation's hom-type and force the unifier to
  -- whnf μ reconciling the fold mismatch, 200000-hb bomb).  The image-isation happens INSIDE `native`.
  exact tensorObjAssoc_hK_lhs_native A B C

/-- **Hand-built half-assembly of the associator bridge equals the common form**
(`lem:tensorObjAssoc_hK_rhs`).  The hand-built side `α ≫ Φ^R` of the bridge equals the same common
form `K = assocCommonForm A B C`. -/
private lemma tensorObjAssoc_eq_localizedAssociator_hK_rhs (A B C : X.Modules) :
    (tensorObjAssoc A B C).hom ≫
        (tensorObjLocalizedIso A (tensorObj B C)).hom ≫
        MonoidalCategoryStruct.whiskerLeft (C := modulesLocalizedMonoidal X)
          (A : modulesLocalizedMonoidal X) (tensorObjLocalizedIso B C).hom
      = assocCommonForm A B C := by
  rw [tensorObjAssoc]
  simp only [tensorObjLocalizedIso, assocCommonForm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, MonoidalCategory.tensorIso_hom, asIso_hom, asIso_inv, Category.assoc]
  -- After unfolding both sides share the prefix `inv(map (η_{a⊗b} ▷ c)) ≫ map (α^p) ≫ …`; strip
  -- it with two `congrArg`s, leaving the small tail (segments 3–5 vs `Φ^R`) as the obligation.
  refine congrArg (fun t => _ ≫ t) ?_
  refine congrArg (fun t => _ ≫ t) ?_
  -- Collapse the braiding-conjugated whiskered unit (segments 3–5) to `(A ◁ η_{b⊗c})^#`
  -- (`sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit`, after the symmetric swap).
  have hcol : sheafification.map (β_ ((toPresheafOfModules X).obj A)
        ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C)).hom ≫
      sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C) ▷
          (toPresheafOfModules X).obj A) ≫
      sheafification.map (β_ ((toPresheafOfModules X).obj (B.tensorObj C))
        ((toPresheafOfModules X).obj A)).hom =
      (sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C))) :
        _ ⟶ tensorObj A (tensorObj B C)) := by
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
    exact sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit _ _
  slice_lhs 1 3 => erw [hcol]
  simp only [Category.assoc]
  -- Rewrite `(A ◁ η_{b⊗c})^#` as a `μ`-conjugate (canonical left keystone); `erw` absorbs the
  -- `◁` instance-form mismatch (`MonoidalPresheaf X` vs the bare presheaf monoidal instance).
  erw [sheafification_whiskerLeft_unit_eq_mu' ((toPresheafOfModules X).obj A)
    ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C)]
  -- iter-013 DIAGNOSIS (the μ-cancel blocker, now PRECISELY mechanized via isolated LSP probes).
  -- The keystone emits the grouped composite `(μ_{a,bc}.inv ≫ (L'a ◁ L'η_{bc}) ≫ μ.hom)`
  -- whose INTERNAL `≫` is the `modulesLocalizedMonoidal X` (localized-synonym) `comp`, while
  -- the boundary `≫ μ_{a,bc}.inv` from `tensorObjLocalizedIso` uses the `X.Modules` `comp`.
  -- After `simp only [tensorObj]` BOTH `μ` objects print identically (object-fold cleared).
  -- The two comps are DEFEQ but DISTINCT instances; the cancel `μ.hom ≫ μ.inv` never forms:
  --   • `rw [Category.assoc]` / `simp only [Category.assoc]` find NO `(f ≫ g) ≫ h` — the mixed
  --     loc/syn `≫` heads block the single-instance pattern (verified);
  --   • a SINGLE `erw [Category.assoc]` DOES cross one boundary (defeq match, μ kept intact) and
  --     reassociates the outer `≫`, but a SECOND `erw [Category.assoc]` UNFOLDS
  --     `Localization.Monoidal.μ` into its raw `Functor.curry.mapIso (Localization.fac …)` form
  --     (verified) — catastrophic, not a cancel;
  --   • after one crossing the keystone tail `(L'a ◁ L'η_{bc}) ≫_loc μ.hom` is an ATOMIC
  --     `X.Modules`-factor (verified by `slice_lhs 2 3` grabbing it whole), so the buried `μ.hom`
  --     is unreachable for `Iso.hom_inv_id_assoc` / `slice … Iso.hom_inv_id`.
  -- ACTIONABLE FIX (iter-013 idiom consult, per PROGRESS Queued): UNIFY the two comps. Cleanest
  -- is to RESTATE the keystone lemmas (`sheafification_whiskerLeft_unit_eq_mu'` /
  -- `…whiskerRight…`) with the `X.Modules` synonym `comp` on their RHS (type-ascribe the localized
  -- whiskering/μ composite to an `X.Modules` hom — defeq, so the proof body is unchanged), OR add a
  -- `@[simp]` rfl-lemma collapsing `@CategoryStruct.comp (modulesLocalizedMonoidal X)` to
  -- `@CategoryStruct.comp X.Modules` (defeq via the synonym's `inferInstanceAs` Category instance).
  -- Either makes every `≫` one instance; then `simp only [tensorObj, Category.assoc,
  -- Iso.hom_inv_id_assoc]` cancels the μ-pair and the residual is the counit coherence
  --   `(L'a ◁ L'η_{bc}) ≫ (c_A ⊗ c_{bc}) ≫ (A ◁ (μ_{bc}.inv ≫ (c_B ⊗ c_C)))
  --      = (L'a ◁ μ_{bc}.inv) ≫ (c_A ⊗ (c_B ⊗ c_C))`
  -- (`μ_natural_right` + the sheafification unit/counit triangle `L'η ≫ c = id`).
  -- Partial advance to the furthest CLEAN point (one boundary crossed, μ intact):
  simp only [tensorObj]
  erw [Category.assoc]
  -- Peel the common leading `μ_{A,B⊗C}.inv` (mandatory shield; proof's own idiom at ~L1919).
  refine congrArg (fun t => _ ≫ t) ?_
  -- Reassociate across the comp-instance boundary + cancel `μ.hom ≫ μ.inv` (analogist-validated).
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  -- Residual counit coherence.  The post-cancel goal is MIXED-instance — `⊗ₘ` is the
  -- `modulesLocalizedMonoidal X` tensorHom but the joining `≫` is the (defeq) `X.Modules` comp, so
  -- `Category.assoc`/`tensorHom_comp_tensorHom`/`whisker_exchange` all refuse to fire (plain `rw`
  -- finds no pattern; bare `erw` resolves `C := X.Modules` which has no `MonoidalCategory`; pinned
  -- `erw` whnf-bombs the μ).  Re-elaborate the goal in a UNIFORM all-localized form via `show`
  -- (defeq cross), after which every `≫` is the localized comp and the clean interchange + the
  -- adjunction triangle `L'η ≫ c_{(B⊗C)^#} = 𝟙` fire with plain `rw`.
  show (((Localization.Monoidal.toMonoidalCategory
            (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)).obj ((toPresheafOfModules X).obj A)) ◁
        ((Localization.Monoidal.toMonoidalCategory
            (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
            (localizedMonoidalUnitIso X)).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C)))) ≫
      (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
          (sheafificationCounitIso A).hom
          (sheafificationCounitIso (sheafification.obj
            ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C))).hom) ≫
        MonoidalCategoryStruct.whiskerLeft (C := modulesLocalizedMonoidal X) A
          ((Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
              (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj B)
              ((toPresheafOfModules X).obj C)).inv ≫
            (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
              (sheafificationCounitIso B).hom (sheafificationCounitIso C).hom)) =
    (((Localization.Monoidal.toMonoidalCategory
          (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)).obj ((toPresheafOfModules X).obj A)) ◁
        (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
          (Wsheaf X) (localizedMonoidalUnitIso X) ((toPresheafOfModules X).obj B)
          ((toPresheafOfModules X).obj C)).inv) ≫
      (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
        (sheafificationCounitIso A).hom
        (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
          (sheafificationCounitIso B).hom (sheafificationCounitIso C).hom))
  simp only [← MonoidalCategory.id_tensorHom]
  -- Merge by interchange (`simp` discrimination-tree matching avoids the `rw` isDefEq blowup now
  -- that the comp instance is uniform); the identity legs clean up too.
  simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  -- Split the merged `_ ⊗ₘ _`; first factor closes by `congr`'s rfl, second is the triangle.
  congr 1
  simp only [sheafificationCounitIso]
  erw [(PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).left_triangle_components_assoc]
  rfl

/-- **Bridge: the hand-built associator is the localized associator**
(`lem:tensorObjAssoc_eq_localizedAssociator`).  The hand-built associator `tensorObjAssoc A B C`
equals the localized associator `α^loc_{A,B,C}` conjugated by the object identifications
`tensorObjLocalizedIso` on all four tensor slots.  Both halves meet at the common form `K`
(`assocCommonForm`): the localized side by `tensorObjAssoc_eq_localizedAssociator_hK_lhs`, the
hand-built side by `tensorObjAssoc_eq_localizedAssociator_hK_rhs`. -/
lemma tensorObjAssoc_eq_localizedAssociator (A B C : X.Modules) :
    (tensorObjLocalizedIso (tensorObj A B) C).hom ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
          (tensorObjLocalizedIso A B).hom (C : modulesLocalizedMonoidal X) ≫
        (MonoidalCategoryStruct.associator (C := modulesLocalizedMonoidal X)
          (A : modulesLocalizedMonoidal X) B C).hom
      = (tensorObjAssoc A B C).hom ≫
        (tensorObjLocalizedIso A (tensorObj B C)).hom ≫
        MonoidalCategoryStruct.whiskerLeft (C := modulesLocalizedMonoidal X)
          (A : modulesLocalizedMonoidal X) (tensorObjLocalizedIso B C).hom :=
  (tensorObjAssoc_eq_localizedAssociator_hK_lhs A B C).trans
    (tensorObjAssoc_eq_localizedAssociator_hK_rhs A B C).symm

/- Retained reference: the former monolithic in-place reduction of the bridge (superseded by the
`hK_lhs`/`hK_rhs` split above).  The reduction recipe is preserved below as a comment for use in the
half-lemma proofs.

  rw [tensorObjAssoc]
  simp only [tensorObjLocalizedIso, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom]
  -- Move the inverse segment-1 whiskered unit (`s1.inv`) from the right side onto the left by
  -- `Iso.eq_inv_comp`; the localized side is then prefixed by the iso `s1` (`asIso_hom`).
  simp only [Category.assoc]
  rw [Iso.eq_inv_comp, asIso_hom]
  simp only [Functor.mapIso_hom, asIso_hom]
  -- Collapse the braiding-conjugated whiskered unit (segments 3–5) to the left-whiskered unit
  -- `(A ◁ η_{b⊗c})^#` (`sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit`, after the
  -- symmetric swap `β_{(BC)♭,a} = β_{a,(BC)♭}⁻¹`).
  have hcol : sheafification.map (β_ ((toPresheafOfModules X).obj A)
        ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C)).hom ≫
      sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C) ▷
          (toPresheafOfModules X).obj A) ≫
      sheafification.map (β_ ((toPresheafOfModules X).obj (B.tensorObj C))
        ((toPresheafOfModules X).obj A)).hom =
      (sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C))) :
        _ ⟶ tensorObj A (tensorObj B C)) := by
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
    exact sheafification_braiding_whiskerRight_unit_eq_whiskerLeft_unit _ _
  slice_rhs 2 4 => erw [hcol]
  -- Rewrite the two whiskered units as `μ`-conjugates (`sheafification_whiskerRight_unit_eq_mu`
  -- on the localized side's segment 1, `sheafification_whiskerLeft_unit_eq_mu` on the collapsed
  -- left-whiskered unit).
  rw [sheafification_whiskerRight_unit_eq_mu']
  slice_rhs 2 2 => erw [sheafification_whiskerLeft_unit_eq_mu' ((toPresheafOfModules X).obj A)
    ((toPresheafOfModules X).obj B ⊗ (toPresheafOfModules X).obj C)]
  -- ADVANCE (iter-011): the canonical keystones (`_eq_mu'`) emit the trailing `μ` with object
  -- `(toPresheafOfModules X).obj (sheafification.obj (a⊗b))`, and `simp only [tensorObj]` rewrites
  -- `tensorObjLocalizedIso`'s `μ` object `(toPresheafOfModules X).obj (A.tensorObj B)` to the SAME
  -- unfolded form — so both `μ` occurrences now print with *identical object arguments* on each
  -- side (verified via LSP `lean_goal`).  This clears iter-010's object-fold blocker: the residual
  -- `μ`-pair is `μ.hom ≫ μ.inv` (LHS, segment-1 keystone vs `tensorObjLocalizedIso`) and
  -- `μ.hom ≫ μ.inv` (RHS, left-keystone vs `tensorObjLocalizedIso`).
  simp only [tensorObj]
  -- RESIDUAL BLOCKER (iter-011): `Iso.hom_inv_id_assoc` still does NOT fire, and
  -- `simp only [tensorObj, Category.assoc, Iso.hom_inv_id_assoc]` reports `Iso.hom_inv_id_assoc`
  -- UNUSED — i.e. the two `μ` isos, though they PRINT with identical object arguments, are not
  -- recognised as the same `Iso` term `e` (the implicit monoidal/category instances of
  -- `Localization.Monoidal.μ` resolve differently in the keystone-rewrite context vs the
  -- `tensorObjLocalizedIso` context).  `simp [Category.assoc]` also does not bring `μ.hom`/`μ.inv`
  -- adjacent (the segment-1 keystone composite sits as one atomic factor; the boundary `≫` is not
  -- re-associated past it).  Per the analogist recipe (`analogies/snap-mu-nesting.md`) and the
  -- plan, the cancel needs the goal ISOLATED into the half-assemblies `..._hK_lhs`/`..._hK_rhs`,
  -- where on the small goal a `change`/`show` forces the instance-level defeq of the two `μ`s
  -- before `Iso.hom_inv_id_assoc` — that `change` whnf-times-out on this full goal.  The remaining
  -- downstream reduction to the common form `K` (triangle `left_triangle_components`,
  -- `μ_natural_left/right`, `associator_hom_app`, counit-triple identification) then proceeds on
  -- each isolated half.  Constructing the well-typed `K` (with the counit object-glue on all four
  -- tensor slots) is the gating sub-task for that split; see task_results.
-/

/-! ### Section components and index-equality transport
(`def:sectionsCast`, `lem:sectionsCast_refl`, `lem:gradedMonoid_eq_of_cast`,
`lem:sectionMul_coherent`)
-/

/- Planner strategy: these are the bottom bricks of the graded-ring assembly.  The prover
(mathlib-build mode) will prove them, THEN build `sectionGradedRing_gcommSemiring` /
`sectionGradedModule_gmodule` instances on top — those instance defs are LEFT UNSCAFFOLDED here.

Pattern: field-for-field port of `Mathlib.LinearAlgebra.TensorPower.Basic`
  (GradedMonoid.GMonoid → DirectSum.GSemiring → DirectSum.GCommSemiring; separate DirectSum.Gmodule),
with `sectionsCast` in place of `TensorPower.cast` and `gradedMonoid_eq_of_cast` producing the
GMonoid sigma-Eq fields.  `gnpow` defaults: do NOT supply (TensorPower.Basic:192-197 omits them).

Crux inputs `tensorObjAssoc`, `tensorPowAdd` are DONE/leanok above in this file.

Implementation hints per `analogies/snap-gcomm.md`:
• `sectionsCast L h` = the `Γ𝒪`-linear equiv underlying
  `((eqToIso (congrArg (tensorPow L) h)).hom.val.app (op ⊤))`;
  refl case: `eqToIso_refl` gives `Iso.refl`, `map_id` collapses to `LinearEquiv.refl`.
• `gradedMonoid_eq_of_cast`: substitute `j = i` via `h`, apply `sectionsCast_refl`; `simpa`.
• Coherence proofs reduce to the presheaf level where eval at the top open is STRICT monoidal
  (naturality of the sheafification unit η through `tensorObjAssoc`/`tensorObjUnitIso`/
  `tensorPowAdd`; ride η through associator, unitors, braiding).
• `GMul.mul a b` = `(tensorPowAdd L i j).hom.val.app (op ⊤)` ∘ `sectionsMul (tensorPow L i)
  (tensorPow L j)` applied to `a ⊗ₜ b`.
• `GOne.one` = image of `(1 : Γ𝒪)` under the canonical iso
  `Γ(X, 𝒪_X) ≅ Γ(X, unitModule X) = sectionDeg L 0`.
-/

/-- The carrier type of the section graded ring at degree `m`: the `Γ(X,𝒪_X)`-module of global
sections of the `m`-th tensor power of `L`.  Inherits `AddCommGroup` and `Module Γ(X,𝒪_X)` from
the underlying `ModuleCat` object. -/
abbrev sectionDeg (L : X.Modules) (m : ℕ) : Type u :=
  ↥((tensorPow L m).val.obj (Opposite.op ⊤))

/-- Index-equality transport of section components: applying `Γ(X,-)` to the canonical isomorphism
`L^{⊗i} ≅ L^{⊗j}` induced by `h : i = j` under `tensorPow` (`def:sectionsCast`).
Section-level analogue of `TensorPower.cast` from `Mathlib.LinearAlgebra.TensorPower.Basic`. -/
noncomputable def sectionsCast (L : X.Modules) {i j : ℕ} (h : i = j) :
    sectionDeg L i ≃ₗ[↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))] sectionDeg L j :=
  match j, h with
  | _, rfl => LinearEquiv.refl _ _

/-- The transport along the reflexive equality `rfl : i = i` equals the identity automorphism
(`lem:sectionsCast_refl`).  Section-level analogue of `TensorPower.cast_refl`. -/
@[simp] lemma sectionsCast_refl (L : X.Modules) (i : ℕ) :
    sectionsCast L (rfl : i = i) = LinearEquiv.refl _ (sectionDeg L i) :=
  rfl

/-- The section transport `sectionsCast L h` is `Γ(X,-)` (evaluation at the top open of the
underlying presheaf-of-modules morphism) applied to the canonical index isomorphism
`eqToIso (congrArg (tensorPow L) h) : L^{⊗i} ≅ L^{⊗j}`.  This is the identification that lets the
coherence proofs (`sectionsMul_*`) cancel the `eqToIso` reindexing baked into `tensorPowAdd`
against the outer `sectionsCast`.  Proved by `subst`: at `rfl` both sides are the identity. -/
lemma sectionsCast_eq_eqToIso (L : X.Modules) {i j : ℕ} (h : i = j) (x : sectionDeg L i) :
    sectionsCast L h x =
      ((eqToIso (congrArg (tensorPow L) h)).hom.val.app (Opposite.op ⊤)).hom x := by
  subst h
  rfl

/-- Cancellation of the `tensorPowAdd`-style reindexing against the outer section transport: for
`h : j = i`, transporting along `h` undoes `Γ` of the index isomorphism induced by `h.symm`.  This
is the precise shape consumed by `sectionsMul_one_mul` / `sectionsMul_mul_one` (where `tensorPowAdd`
ends in `eqToIso (congrArg (tensorPow L) (·).symm)`). -/
lemma sectionsCast_eqToIso_cancel (L : X.Modules) {i j : ℕ} (h : j = i) (y : sectionDeg L i) :
    sectionsCast L h
        (((eqToIso (congrArg (tensorPow L) h.symm)).hom.val.app (Opposite.op ⊤)).hom y) = y := by
  subst h
  rfl

/-- Cast-mediated equality in the graded sigma type: if `a.fst = b.fst` and the section-component
transport maps `a.snd` to `b.snd`, then `a = b` as dependent pairs (`lem:gradedMonoid_eq_of_cast`).
Section-level analogue of `gradedMonoid_eq_of_cast` from `TensorPower.Basic` (line 123 there). -/
lemma gradedMonoid_eq_of_cast (L : X.Modules) {a b : GradedMonoid (sectionDeg L)}
    (h : a.1 = b.1) (h2 : sectionsCast L h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain rfl : i = j := h
  rw [sectionsCast_refl, LinearEquiv.refl_apply] at h2
  subst h2
  rfl

/-- Degreewise graded multiplication on section components:
`sectionDeg L i × sectionDeg L j → sectionDeg L (i+j)`, defined as the composition
`Γ(μ_{i,j}) ∘ sectionsMul` applied to `a ⊗ₜ b`.  Required for the coherence lemma signatures. -/
noncomputable instance (L : X.Modules) : GradedMonoid.GMul (sectionDeg L) where
  mul {i j} (a : sectionDeg L i) (b : sectionDeg L j) :=
    ((tensorPowAdd L i j).hom.val.app (Opposite.op ⊤)).hom
      ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
        (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] b))

/-- Graded unit in degree 0: the image of `1 ∈ Γ(X,𝒪_X)` in `sectionDeg L 0 = Γ(X, L^{⊗0})`
via the canonical `Γ𝒪`-module isomorphism.  Required for the coherence lemma signatures. -/
noncomputable instance (L : X.Modules) : GradedMonoid.GOne (sectionDeg L) where
  one := (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))

/-- Definitional unfolding of the graded multiplication: `a * b` is the section
multiplication of the components followed by `Γ` of the tensor-power comparison
`μ_{i,j}`.  Holds by `rfl` and is the reuse handle for the bilinearity (`GSemiring`)
fields below. -/
lemma gMul_def (L : X.Modules) {i j : ℕ} (a : sectionDeg L i) (b : sectionDeg L j) :
    GradedMonoid.GMul.mul a b
      = ((tensorPowAdd L i j).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
            (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] b)) :=
  rfl

/-! ### Helpers for the coherence proofs

The coherences (`sectionsMul_*`) all reduce, after cancelling the `tensorPowAdd`
reindexing against the outer `sectionsCast`, to an identity of the shape
`Γ(structural-iso)(η(elementary tensor)) = …`, which is proved by `η`-naturality
against the corresponding presheaf-level structural isomorphism plus a
triangle/unitor identity.  These helpers package the recurring carrier bookkeeping
(`SheafOfModules.comp_val` + `PresheafOfModules.comp_app` + the value-`ModuleCat`
diamond, handled in term mode) so the mathematical content stays visible. -/

/-- Application of a composite sheaf-of-modules morphism at the top open splits as the
composition of the applications: `Γ(f ≫ g)(x) = Γ(g)(Γ(f)(x))`.  This is the non-`rfl`
split needed because the positional `comp_apply`/`hom_comp` rewrites hit the value-`ModuleCat`
diamond; the final `rfl` is the term-mode reduction. -/
lemma val_app_top_comp {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥(A.val.obj (Opposite.op ⊤))) :
    ((f ≫ g).val.app (Opposite.op ⊤)).hom x
      = (g.val.app (Opposite.op ⊤)).hom ((f.val.app (Opposite.op ⊤)).hom x) :=
  rfl

/-- The `m = 0` branch of `tensorPowAdd`: `μ_{0,n}` is the left unitor reindexed along
`0 + n = n`.  Holds by `rfl` (iota on the literal `0`), so it never forces the
whnf-timeout-prone unfolding of the recursive branch. -/
lemma tensorPowAdd_zero (L : X.Modules) (n : ℕ) :
    tensorPowAdd L 0 n =
      tensorObjUnitIso (tensorPow L n) ≪≫
        eqToIso (congrArg (tensorPow L) (Nat.zero_add n).symm) :=
  rfl

/-- The hom of the left-unitor iso splits as the sheafified presheaf left unitor followed by
the sheafification counit. -/
lemma tensorObjUnitIso_hom (G : X.Modules) :
    (tensorObjUnitIso G).hom
      = sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom ≫ (sheafificationCounitIso G).hom :=
  rfl

/-- **Unitor-η core** of left unitality.  Applying `Γ` of the left-unitor iso
`tensorObjUnitIso G` to the section multiplication `η(1 ⊗ a)` returns `a`.

Mathematically: split `(tensorObjUnitIso G).hom = Γ(λ_p)^# ≫ ε_G` (sheafified presheaf
left unitor, then the sheafification counit).  Unit-naturality of `η` against the
presheaf left unitor `λ_p` (whose value at `⊤` sends `1 ⊗ a ↦ 1 • a = a`) rewrites
`Γ(λ_p)^#(η(1⊗a)) = η_G(a)`; the right-triangle identity of the sheafification
adjunction then gives `ε_G(η_G(a)) = a`. -/
lemma unitor_sectionsMul (G : X.Modules) (a : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorObjUnitIso G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (unitModule X) G).hom
          ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
            ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] a)) = a := by
  -- Split the unitor into the sheafified presheaf left unitor and the counit, then peel the
  -- composite application via `val_app_top_comp` (handles the value-`ModuleCat` diamond in
  -- term mode).
  rw [tensorObjUnitIso_hom]
  -- Split the composite application `Γ(f ≫ g)(x) = Γ(g)(Γ(f)(x))` in term mode (`show` reduces
  -- at default transparency, bridging the `tensorObj`/`sheafification.obj` def and the value-
  -- `ModuleCat` diamond that block positional `rw`).
  show ((sheafificationCounitIso G).hom.val.app (Opposite.op ⊤)).hom
        (((sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G)).hom).val.app (Opposite.op ⊤)).hom
          ((sectionsMul (unitModule X) G).hom
            ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
              ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] a))) = a
  -- Transpose identity: the composite `λ_p^# ≫ ε_G` is the adjunct of the presheaf left unitor
  -- `λ_p`.  In the adjunction `sheafification ⊣ forget`, `homEquiv (λ_p^# ≫ ε_G) = λ_p`: indeed
  -- `homEquiv.symm λ_p = (λ_p)^# ≫ ε_G` (`homEquiv_counit`), which is exactly the composite (the
  -- counit iso is the counit), so applying `homEquiv` to both sides gives the claim.
  have H : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)) G
        (sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G)).hom ≫ (sheafificationCounitIso G).hom)
      = (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom := by
    have hsymm : sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G)).hom ≫ (sheafificationCounitIso G).hom
        = ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)) G).symm
            (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj G)).hom :=
      (Adjunction.homEquiv_counit (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)) _ _ _).symm
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj (unitModule X))
          ((toPresheafOfModules X).obj G)) G).apply_eq_iff_eq_symm_apply.mpr hsymm
  -- Unfold `homEquiv` to the unit form, evaluate at the top open on `1 ⊗ a`.
  rw [Adjunction.homEquiv_unit] at H
  have Hel := congrArg
      (fun m : (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)) ⟶
            (toPresheafOfModules X).obj G =>
        (m.app (Opposite.op ⊤)).hom
          ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
            ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] a)) H
  -- The presheaf left unitor sends `1 ⊗ a ↦ 1 • a = a`.
  have Hunit :
      ((MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom.app (Opposite.op ⊤)).hom
        ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
          ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] a) = a := by
    -- The presheaf left unitor at `⊤` is, by construction, the value-`ModuleCat` left unitor.
    have happ : (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G)).hom.app (Opposite.op ⊤)
          = (MonoidalCategory.leftUnitor (C := ModuleCat (X.sheaf.obj.obj (Opposite.op ⊤)))
              (((toPresheafOfModules X).obj G).obj (Opposite.op ⊤))).hom := rfl
    rw [happ]
    -- `erw` bridges the `CommRingCat`/`RingCat` tmul-key diamond; the unitor sends `1 ⊗ a ↦ 1 • a`.
    erw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul]
  exact Hel.trans Hunit

/-- **Braiding-η core** of commutativity (`lem:sectionMul_braiding_core`).  Applying `Γ` of the
braiding iso `tensorBraiding F G` to the section multiplication `η(σ ⊗ τ)` swaps the factors:
it equals the section multiplication `η(τ ⊗ σ)` of the swapped pair.

Mathematically this is pure unit-naturality of `η` against the presheaf braiding `β_p`: the
naturality square `β_p ≫ η_{G⊗_pF} = η_{F⊗_pG} ≫ (β_p)^#` evaluated at the top open on
`σ ⊗ τ`, using that `β_p` at `⊤` sends `σ ⊗ τ ↦ τ ⊗ σ`.  No counit/triangle input is needed. -/
lemma sectionMul_braiding_core (F G : X.Modules)
    (σ : ↥(F.val.obj (Opposite.op ⊤))) (τ : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorBraiding F G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul F G).hom
          (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ))
      = (sectionsMul G F).hom
          (τ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] σ) := by
  -- Unit naturality of `η` against the presheaf braiding `β_p : F⊗_pG ⟶ G⊗_pF`.
  have H := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom
  -- Evaluate the presheaf-morphism equality at the top open on `σ ⊗ τ`.
  have Hel := congrArg
      (fun m : (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)) ⟶
            (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
              (SheafOfModules.forget X.ringCatSheaf).comp
                (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj))).obj
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)) =>
        (m.app (Opposite.op ⊤)).hom
          (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ)) H
  -- The presheaf braiding at `⊤` sends `σ ⊗ τ ↦ τ ⊗ σ`.
  have Hbraid :
      ((BraidedCategory.braiding (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom.app
            (Opposite.op ⊤)).hom (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ)
        = τ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] σ := by
    have happ : (BraidedCategory.braiding (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom.app
              (Opposite.op ⊤)
          = (BraidedCategory.braiding (C := ModuleCat (X.sheaf.obj.obj (Opposite.op ⊤)))
              (((toPresheafOfModules X).obj F).obj (Opposite.op ⊤))
              (((toPresheafOfModules X).obj G).obj (Opposite.op ⊤))).hom := rfl
    rw [happ]
    rfl
  -- `Hel.symm` is, after the defeq comp-app split + the `forget/restrictScalars` identity of the
  -- right adjoint, exactly `Γ(β)(sectionsMul F G (σ⊗τ)) = sectionsMul G F (β_p(σ⊗τ))`; rewriting
  -- the braiding image `β_p(σ⊗τ) = τ⊗σ` inside `sectionsMul G F` (`Hbraid`) closes the goal.
  exact Hel.symm.trans (congrArg (fun w => (sectionsMul G F).hom w) Hbraid)

/-- **Right-unitor-η core** of right unitality (`lem:sectionMul_rightUnitor_core`).  Applying `Γ`
of the right unitor `tensorObjRightUnitor G` to the section multiplication `η(a ⊗ 1)` returns `a`.

Reduction (blueprint): `ρ_G = λ_G ∘ β_{G,𝟙}`; split the application via `val_app_top_comp`, send
`η(a ⊗ 1)` across the braiding to `η(1 ⊗ a)` by `sectionMul_braiding_core`, then apply the
left-unitor core `unitor_sectionsMul`. -/
lemma sectionMul_rightUnitor_core (G : X.Modules) (a : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorObjRightUnitor G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul G (unitModule X)).hom
          (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))]
            (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))))) = a := by
  rw [tensorObjRightUnitor_hom]
  rw [show ((tensorBraiding G (unitModule X)).hom ≫ (tensorObjUnitIso G).hom).val.app
        (Opposite.op ⊤)
      = ((tensorBraiding G (unitModule X)).hom.val.app (Opposite.op ⊤)) ≫
          ((tensorObjUnitIso G).hom.val.app (Opposite.op ⊤)) from rfl]
  show ((tensorObjUnitIso G).hom.val.app (Opposite.op ⊤)).hom
      (((tensorBraiding G (unitModule X)).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul G (unitModule X)).hom
          (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))]
            (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))))) = a
  rw [sectionMul_braiding_core G (unitModule X) a (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))]
  exact unitor_sectionsMul G a

/-- **Unit-naturality at the top open** (project-local helper).  Applying `Γ` (the top-open value)
of the sheafification `sheafification.map f` of a presheaf-of-modules morphism `f : P ⟶ Q` to the
sheafification-unit image `η_P(x)` returns the unit image `η_Q(f(x))` of the transported element.
This is the single naturality square of the sheafification unit `η`, evaluated at `⊤`; it is the
common engine of the section-η cores and is applied once per segment in `sectionMul_assoc_core`. -/
private lemma sheafification_map_unit_top {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    (x : ↥(P.obj (Opposite.op ⊤))) :
    ((sheafification.map f).val.app (Opposite.op ⊤)).hom
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
          (Opposite.op ⊤)).hom x)
      = ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q).app
          (Opposite.op ⊤)).hom ((f.app (Opposite.op ⊤)).hom x)) := by
  have H := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality f
  exact (congrArg (fun m => (m.app (Opposite.op ⊤)).hom x) H).symm

/-- Inverse companion of `sheafification_map_unit_top`: when `sheafification.map f` is an
isomorphism, `Γ(inv (sheafification.map f))` sends the unit image `η_Q(f x)` back to the unit image
`η_P(x)`.  Used for the inverse whiskered-unit segment (segment 1) of `tensorObjAssoc`. -/
private lemma sheafification_map_unit_top_inv {P Q : X.PresheafOfModules} (f : P ⟶ Q)
    [IsIso (sheafification.map f)] (x : ↥(P.obj (Opposite.op ⊤))) :
    ((inv (sheafification.map f)).val.app (Opposite.op ⊤)).hom
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q).app
          (Opposite.op ⊤)).hom ((f.app (Opposite.op ⊤)).hom x))
      = ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
          (Opposite.op ⊤)).hom x) := by
  rw [← sheafification_map_unit_top f x, ← val_app_top_comp, IsIso.hom_inv_id]
  rfl

/-- **Associativity-η core** of associativity (`lem:sectionMul_assoc_core`).  Applying `Γ` of the
sheaf associator `tensorObjAssoc A B C` to the left-bracketed iterated section multiplication
`η((σ·τ) ⊗ υ)` yields the right-bracketed one `η(σ ⊗ (τ·υ))`.

Mathematically (blueprint): both sides are iterated `η`-images of elementary tensors; the sheaf
associator is the presheaf associator `α_p` sheafified and conjugated by the whiskered-unit
comparison isos (`tensorObjAssoc`, `isIso_sheafification_whiskerRight_unit`).  On an `η`-image
those comparison isos act as the identity reparametrisation, so only `(α_p)^#` contributes, and
`η`-naturality against `α_p` (which reassociates `(σ⊗τ)⊗υ ↦ σ⊗(τ⊗υ)` at the top open) closes it.

The reparametrisation-by-comparison-iso step (the conjugation in `tensorObjAssoc` segments 1/3
acting trivially on a unit image) is the remaining obstacle; it is the sheaf-level shadow of the
Mac Lane coherence transfer also needed by `tensorPowAdd_assoc`. -/
lemma sectionMul_assoc_core (A B C : X.Modules)
    (σ : ↥(A.val.obj (Opposite.op ⊤))) (τ : ↥(B.val.obj (Opposite.op ⊤)))
    (υ : ↥(C.val.obj (Opposite.op ⊤))) :
    ((tensorObjAssoc A B C).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorObj A B) C).hom
          (((sectionsMul A B).hom (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ))
            ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] υ))
      = (sectionsMul A (tensorObj B C)).hom
          (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))]
            ((sectionsMul B C).hom (τ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] υ))) := by
  -- The whiskered-unit segments (1 and 4) are isos by the strong-monoidality comparison.
  haveI i1 := isIso_sheafification_whiskerRight_unit
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
    ((toPresheafOfModules X).obj C)
  haveI i2 := isIso_sheafification_whiskerRight_unit
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))
    ((toPresheafOfModules X).obj A)
  -- Expand `tensorObjAssoc` into its five segments and peel the top-open application of the
  -- composite into the five nested `Γ(sheafification.map _)` (segment 1 inverted).
  simp only [tensorObjAssoc, Iso.trans_hom, val_app_top_comp, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.mapIso_hom]
  -- Segment 1 (inverse whiskered unit): sends the `sectionsMul` nest back to the triple-presheaf
  -- unit image `η_{(a⊗ₚb)⊗ₚc}((σ⊗τ)⊗υ)`.
  have h1 : ((inv (sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C)))).val.app (Opposite.op ⊤)).hom
          ((sectionsMul (tensorObj A B) C).hom
            (((sectionsMul A B).hom (σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ))
              ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] υ))
        = (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
              ((toPresheafOfModules X).obj C))).app (Opposite.op ⊤)).hom
            ((σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ)
              ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] υ) :=
    sheafification_map_unit_top_inv (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
        ((toPresheafOfModules X).obj C))
      ((σ ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] τ)
        ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] υ)
  erw [h1]
  -- Segments 2–5: unit naturality (associator, braiding, whiskered unit, braiding).
  erw [sheafification_map_unit_top (MonoidalCategory.associator (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
        ((toPresheafOfModules X).obj C)).hom,
    sheafification_map_unit_top (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A)
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))).hom,
    sheafification_map_unit_top (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)))
        ((toPresheafOfModules X).obj A)),
    sheafification_map_unit_top (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj (tensorObj B C)) ((toPresheafOfModules X).obj A)).hom]
  -- The remaining presheaf-level structural maps (associator, braiding, whiskered unit, braiding)
  -- evaluated at the top open compute definitionally on the elementary tensor `(σ⊗τ)⊗υ`, sending it
  -- to `σ ⊗ η(τ⊗υ)`, which is the right-bracketed section multiplication.
  rfl

/-! ### Tensor-power comparison coherences (`lem:tensorPowAdd_{rightUnit,braiding,assoc}`)

These factor the comparison `μ_{m,m'}` (`tensorPowAdd`) along the unit/braiding/associator
branches, transferring the symmetric-monoidal Mac Lane coherences of the presheaf monoidal
structure through the `isIso_sheafification_whiskerRight_unit` comparison isos.  They are the
structural half of `lem:sectionMul_coherent`; the section-level cores above discharge the
sheafification-unit bookkeeping. -/

/-- In any braided monoidal category the braiding of the unit object with itself is the identity,
`β_{𝟙,𝟙} = 𝟙`.  (`braiding_tensorUnit_left` at `𝟙` plus `unitors_equal`.)  Project-local helper for
the base cases of the tensor-power comparison coherences. -/
private lemma braiding_unit_unit {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] :
    β_ (𝟙_ C) (𝟙_ C) = Iso.refl _ := by
  apply Iso.ext
  rw [Iso.refl_hom, braiding_tensorUnit_left, MonoidalCategory.unitors_equal, Iso.hom_inv_id]

/-- The hand-built sheaf braiding of the unit module with itself is the identity.  Pure
sheafification-functoriality of the presheaf-level fact `braiding_unit_unit` (no monoidal structure
on `X.Modules` needed): the underlying presheaf of `unitModule X` is the presheaf monoidal unit. -/
private lemma tensorBraiding_unitModule (X : Scheme.{u}) :
    tensorBraiding (unitModule X) (unitModule X) = Iso.refl _ := by
  have hb : BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj (unitModule X))
      = Iso.refl _ := braiding_unit_unit
  show sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj (unitModule X))
      ((toPresheafOfModules X).obj (unitModule X))) = Iso.refl _
  rw [hb]
  exact Functor.mapIso_refl _ _

/-- The hand-built sheaf braiding is involutive: `β_{F,G} ≫ β_{G,F} = 𝟙`.  Pure
sheafification-functoriality of the presheaf symmetry `SymmetricCategory.symmetry` (no monoidal
structure on `X.Modules` needed).  Used in the base case of `tensorPowAdd_braiding`. -/
private lemma tensorBraiding_symm (F G : X.Modules) :
    tensorBraiding F G ≪≫ tensorBraiding G F = Iso.refl _ := by
  have hs : (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)) ≪≫
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)) = Iso.refl _ := by
    apply Iso.ext; simp [SymmetricCategory.symmetry]
  show sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)) ≪≫
      sheafification.mapIso (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)) = Iso.refl _
  rw [← Functor.mapIso_trans]
  exact (congrArg sheafification.mapIso hs).trans (Functor.mapIso_refl _ _)

/-- **Right-unit branch** of the tensor-power comparison (`lem:tensorPowAdd_rightUnit`): `μ_{n,0}`
factors as the right unitor `ρ_{L^{⊗n}}` (`tensorObjRightUnitor`) followed by the index-equality
isomorphism `n = n + 0`.  Proved by induction on `n`; the successor step is the symmetric-monoidal
identity `ρ_{A⊗L} = (ρ_A ▷ L) ∘ α⁻¹ ∘ (A ◁ β) ∘ α` transferred from the presheaf level. -/
lemma tensorPowAdd_rightUnit (L : X.Modules) (n : ℕ) :
    tensorPowAdd L n 0 = tensorObjRightUnitor (tensorPow L n) ≪≫
      eqToIso (congrArg (tensorPow L) (add_zero n).symm) := by
  induction n with
  | zero =>
    -- Base: `μ_{0,0}` is `λ_𝟙` (by `tensorPowAdd_zero`) and `ρ_𝟙 = λ_𝟙 ∘ β_{𝟙,𝟙}`.  After
    -- unfolding both unitors and matching the index isos, `congr 1` reduces the base case to the
    -- single residual `λ_𝟙 = β_{𝟙,𝟙} ≫ λ_𝟙`, i.e. `tensorBraiding 𝟙 𝟙 = 𝟙` (the symmetry on the
    -- unit object), the one remaining presheaf-level coherence fact for the base.
    rw [tensorPowAdd_zero, tensorObjRightUnitor]
    congr 1
    show tensorObjUnitIso (unitModule X)
        = tensorBraiding (unitModule X) (unitModule X) ≪≫ tensorObjUnitIso (unitModule X)
    rw [tensorBraiding_unitModule, Iso.refl_trans]
  | succ k _ih =>
    -- Successor: expand `μ_{k+1,0}` by the `tensorPowAdd` successor branch and use the IH; the
    -- residual is the Mac Lane right-unit coherence transferred through `tensorObjAssoc`.
    sorry

/-- **Commutativity branch** of the tensor-power comparison (`lem:tensorPowAdd_braiding`):
`μ_{na,nb}` agrees with `μ_{nb,na}` after braiding `β_{L^{⊗na},L^{⊗nb}}` and the index-equality
isomorphism `nb + na = na + nb`.  Proved by induction on `na`; transfers the hexagon coherence of
the presheaf symmetric monoidal structure. -/
lemma tensorPowAdd_braiding (L : X.Modules) (na nb : ℕ) :
    tensorPowAdd L na nb = tensorBraiding (tensorPow L na) (tensorPow L nb) ≪≫
      tensorPowAdd L nb na ≪≫ eqToIso (congrArg (tensorPow L) (add_comm nb na)) := by
  induction na with
  | zero =>
    -- Base: `μ_{0,nb} = λ`, and `μ_{nb,0} = ρ = λ ∘ β` (`tensorPowAdd_rightUnit`); the two
    -- braidings `β_{𝟙,L^{⊗nb}}` / `β_{L^{⊗nb},𝟙}` cancel by `tensorBraiding_symm`, leaving the
    -- left unitor with matching `eqToIso` reindexers (proof-irrelevant Nat equalities).
    show tensorPowAdd L 0 nb = tensorBraiding (unitModule X) (tensorPow L nb) ≪≫
      tensorPowAdd L nb 0 ≪≫ eqToIso (congrArg (tensorPow L) (add_comm nb 0))
    rw [tensorPowAdd_zero, tensorPowAdd_rightUnit]
    simp only [tensorObjRightUnitor, Iso.trans_assoc]
    rw [← Iso.trans_assoc, tensorBraiding_symm (unitModule X) (tensorPow L nb), Iso.refl_trans]
    congr 1
  | succ k _ih =>
    -- Successor: hexagon coherence transferred through `tensorObjAssoc` + IH at index `k`.
    sorry

/-- **Associativity branch** of the tensor-power comparison (`lem:tensorPowAdd_assoc`): the two
bracketings of `L^{⊗na} ⊗ L^{⊗nb} ⊗ L^{⊗nc}` agree after the index-equality isomorphism
`(na+nb)+nc = na+(nb+nc)`.  Proved by induction on `na`; transfers the pentagon coherence. -/
lemma tensorPowAdd_assoc (L : X.Modules) (na nb nc : ℕ) :
    (tensorObjWhiskerRightIso (tensorPowAdd L na nb) (tensorPow L nc)).symm ≪≫
        tensorObjAssoc (tensorPow L na) (tensorPow L nb) (tensorPow L nc) ≪≫
        tensorObjWhiskerLeftIso (tensorPow L na) (tensorPowAdd L nb nc) ≪≫
        tensorPowAdd L na (nb + nc) =
      tensorPowAdd L (na + nb) nc ≪≫
        eqToIso (congrArg (tensorPow L) (add_assoc na nb nc)) := by
  induction na with
  | zero =>
    -- Base: reduces to the triangle identity relating left unitor and associator.
    sorry
  | succ k _ih =>
    -- Successor: pentagon coherence transferred through `tensorObjAssoc` + IH at index `k`.
    sorry

/-- Left unitality of the graded section multiplication (`lem:sectionMul_coherent`, left-unit case):
for `a ∈ Γ(X, L^{⊗n})`, transporting `1 · a` along `0 + n = n` gives `a`.
Mirrors `TensorPower.one_mul`.

Reduction: `μ_{0,n}` is (by the `m = 0` branch of `tensorPowAdd`, `tensorPowAdd_zero`) the left
unitor `tensorObjUnitIso (L^{⊗n})` post-composed with the index reindex
`eqToIso (congrArg (tensorPow L) (Nat.zero_add n).symm)`.  Splitting `Γ(μ_{0,n})` along this
composite (`Iso.trans_hom` + `val_app_top_comp`) and cancelling the reindex against the outer
`sectionsCast` (`sectionsCast_eqToIso_cancel`) reduces the goal to the unitor-η core
`unitor_sectionsMul`. -/
theorem sectionsMul_one_mul (L : X.Modules) {n : ℕ} (a : sectionDeg L n) :
    sectionsCast L (zero_add n) (GradedMonoid.GMul.mul GradedMonoid.GOne.one a) = a := by
  rw [gMul_def, tensorPowAdd_zero, Iso.trans_hom]
  -- Split off the index reindex `eqToIso` and align the element to the unit form, all by defeq
  -- (`show`, default transparency): `Γ(unitor ≫ eqToIso)(η(1·a)) = Γ(eqToIso)(Γ(unitor)(η(1·a)))`.
  show sectionsCast L (zero_add n)
      (((eqToIso (congrArg (tensorPow L) (zero_add n).symm)).hom.val.app (Opposite.op ⊤)).hom
        (((tensorObjUnitIso (tensorPow L n)).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul (unitModule X) (tensorPow L n)).hom
            ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
              ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] a)))) = a
  rw [sectionsCast_eqToIso_cancel]
  exact unitor_sectionsMul (tensorPow L n) a

/-- Right unitality of the graded section multiplication
(`lem:sectionMul_coherent`, right-unit case):
for `a ∈ Γ(X, L^{⊗n})`, transporting `a · 1` along `n + 0 = n` gives `a`.
Mirrors `TensorPower.mul_one`. -/
theorem sectionsMul_mul_one (L : X.Modules) {n : ℕ} (a : sectionDeg L n) :
    sectionsCast L (add_zero n) (GradedMonoid.GMul.mul a GradedMonoid.GOne.one) = a := by
  rw [gMul_def, tensorPowAdd_rightUnit, Iso.trans_hom]
  -- Split off the index reindex `eqToIso` and align the element to the right-unit form (defeq).
  show sectionsCast L (add_zero n)
      (((eqToIso (congrArg (tensorPow L) (add_zero n).symm)).hom.val.app (Opposite.op ⊤)).hom
        (((tensorObjRightUnitor (tensorPow L n)).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul (tensorPow L n) (unitModule X)).hom
            (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))]
              (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))))))) = a
  rw [sectionsCast_eqToIso_cancel]
  exact sectionMul_rightUnitor_core (tensorPow L n) a

/-- Associativity of the graded section multiplication (`lem:sectionMul_coherent`, associativity):
transporting `(a · b) · c` along `(na + nb) + nc = na + (nb + nc)` gives `a · (b · c)`.
Mirrors `TensorPower.mul_assoc`. -/
theorem sectionsMul_mul_assoc (L : X.Modules) {na nb nc : ℕ}
    (a : sectionDeg L na) (b : sectionDeg L nb) (c : sectionDeg L nc) :
    sectionsCast L (add_assoc na nb nc)
      (GradedMonoid.GMul.mul (GradedMonoid.GMul.mul a b) c) =
      GradedMonoid.GMul.mul a (GradedMonoid.GMul.mul b c) := by
  -- Unfold the degreewise multiplication on both bracketings into `Γ(μ) ∘ sectionsMul` nests.
  simp only [gMul_def]
  -- Remaining bridge (blueprint `lem:sectionMul_coherent`, associativity case): factor
  -- `μ_{na+nb,nc}` and `μ_{na,nb+nc}` via `tensorPowAdd_assoc`, cancel the `eqToIso` reindex
  -- against the outer `sectionsCast` (`sectionsCast_eq_eqToIso`/`sectionsCast_eqToIso_cancel`),
  -- and intertwine the two iterated section multiplications through `Γ(α)` by
  -- `sectionMul_assoc_core` — using the naturality of `sectionsMul` in each variable under the
  -- whiskerings `tensorObjWhiskerRightIso`/`tensorObjWhiskerLeftIso` that appear in
  -- `tensorPowAdd_assoc`.  The `sectionsMul`-whiskering naturality bricks are not yet in file.
  sorry

/-- Commutativity of the graded section multiplication (`lem:sectionMul_coherent`, commutativity):
transporting `a · b` along `na + nb = nb + na` gives `b · a`.
Section-level analogue of the `mul_comm` in `TensorPower.Basic`. -/
theorem sectionsMul_mul_comm (L : X.Modules) {na nb : ℕ}
    (a : sectionDeg L na) (b : sectionDeg L nb) :
    sectionsCast L (add_comm na nb) (GradedMonoid.GMul.mul a b) =
    GradedMonoid.GMul.mul b a := by
  rw [gMul_def, tensorPowAdd_braiding, Iso.trans_hom, Iso.trans_hom]
  -- Split `Γ(β ≫ μ_{nb,na} ≫ eqToIso)(η(a⊗b))` into the three applications (defeq).
  show sectionsCast L (add_comm na nb)
      (((eqToIso (congrArg (tensorPow L) (add_comm nb na))).hom.val.app (Opposite.op ⊤)).hom
        (((tensorPowAdd L nb na).hom.val.app (Opposite.op ⊤)).hom
          (((tensorBraiding (tensorPow L na) (tensorPow L nb)).hom.val.app (Opposite.op ⊤)).hom
            ((sectionsMul (tensorPow L na) (tensorPow L nb)).hom
              (a ⊗ₜ[↥(X.sheaf.obj.obj (Opposite.op ⊤))] b))))) = GradedMonoid.GMul.mul b a
  -- Send `Γ(β)(η(a⊗b))` to `η(b⊗a)` (braiding core), cancel the reindex, recognise `b · a`.
  rw [sectionMul_braiding_core (tensorPow L na) (tensorPow L nb) a b,
    sectionsCast_eqToIso_cancel]
  rfl

/-! ### Graded-ring assembly (`lem:sectionGradedRing_gcommSemiring`)

The section components `m ↦ Γ(X, L^{⊗m})` carry a `DirectSum.GCommSemiring`, assembled
field-for-field as `Mathlib.LinearAlgebra.TensorPower.Basic` builds its graded semiring:
the graded-monoid layer from the four cast-mediated coherences via `gradedMonoid_eq_of_cast`,
and the bilinearity (`GSemiring`) fields for free from the `Γ(X,𝒪_X)`-linearity of the
degreewise multiplication `Γ(μ) ∘ sectionsMul` (recorded by `gMul_def`). -/

/-- Graded-monoid structure on the section components: the unit and associativity coherences
are the cast-mediated identities `sectionsMul_{one_mul,mul_one,mul_assoc}` repackaged as
dependent-pair equalities by `gradedMonoid_eq_of_cast`.  `gnpow` is defaulted (as in
`TensorPower.Basic`). -/
noncomputable instance instGMonoid (L : X.Modules) : GradedMonoid.GMonoid (sectionDeg L) :=
  { (inferInstance : GradedMonoid.GMul (sectionDeg L)),
    (inferInstance : GradedMonoid.GOne (sectionDeg L)) with
    one_mul := fun _ => gradedMonoid_eq_of_cast L (zero_add _) (sectionsMul_one_mul L _)
    mul_one := fun _ => gradedMonoid_eq_of_cast L (add_zero _) (sectionsMul_mul_one L _)
    mul_assoc := fun _ _ _ =>
      gradedMonoid_eq_of_cast L (add_assoc _ _ _) (sectionsMul_mul_assoc L _ _ _) }

/-- Graded-semiring structure on the section components.  The bilinearity fields are free:
the degreewise multiplication `Γ(μ) ∘ sectionsMul` is `Γ(X,𝒪_X)`-linear (it is a composite of
the bilinear section multiplication with the linear comparison map), so it annihilates `0` and
distributes over sums in each variable; `natCast n` is the `n`-fold sum of the degree-`0`
unit. -/
noncomputable instance instGSemiring (L : X.Modules) : DirectSum.GSemiring (sectionDeg L) :=
  { instGMonoid L with
    mul_zero := fun a => by
      rw [gMul_def]
      conv_rhs => rw [← map_zero ((tensorPowAdd L _ _).hom.val.app (Opposite.op ⊤)).hom,
        ← map_zero (sectionsMul (tensorPow L _) (tensorPow L _)).hom]
      congr 2
      exact TensorProduct.tmul_zero _ a
    zero_mul := fun b => by
      rw [gMul_def]
      conv_rhs => rw [← map_zero ((tensorPowAdd L _ _).hom.val.app (Opposite.op ⊤)).hom,
        ← map_zero (sectionsMul (tensorPow L _) (tensorPow L _)).hom]
      congr 2
      exact TensorProduct.zero_tmul _ b
    mul_add := fun a b c => by
      rw [gMul_def, gMul_def, gMul_def, ← map_add, ← map_add]
      congr 2
      exact TensorProduct.tmul_add a b c
    add_mul := fun a b c => by
      rw [gMul_def, gMul_def, gMul_def, ← map_add, ← map_add]
      congr 2
      exact TensorProduct.add_tmul a b c
    natCast := fun n =>
      (n : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))) • (GradedMonoid.GOne.one : sectionDeg L 0)
    natCast_zero := by rw [Nat.cast_zero, zero_smul]
    natCast_succ := fun n => by rw [Nat.cast_succ, add_smul, one_smul] }

/-- Graded *commutative* semiring structure on the section components: graded commutativity is
the cast-mediated identity `sectionsMul_mul_comm` repackaged by `gradedMonoid_eq_of_cast`. -/
noncomputable instance instGCommSemiring (L : X.Modules) :
    DirectSum.GCommSemiring (sectionDeg L) :=
  { instGSemiring L with
    mul_comm := fun _ _ => gradedMonoid_eq_of_cast L (add_comm _ _) (sectionsMul_mul_comm L _ _) }

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-- **The section graded ring** (`lem:sectionGradedRing_gcommSemiring`): the family of
`Γ(X,𝒪_X)`-modules `m ↦ Γ(X, L^{⊗m})` carries a `DirectSum.GCommSemiring`, hence
`⨁ m, Γ(X, L^{⊗m})` is a commutative semiring (the section graded ring `R(X,L)`).  The
degreewise multiplication is the section multiplication followed by the tensor-power comparison
`Γ(μ_{m,m'})`; the unit is `1 ∈ Γ(X,𝒪_X) = Γ(X, L^{⊗0})`. -/
noncomputable instance sectionGradedRing_gcommSemiring (L : X.Modules) :
    DirectSum.GCommSemiring (Scheme.Modules.sectionDeg L) :=
  Scheme.Modules.instGCommSemiring L

end AlgebraicGeometry
