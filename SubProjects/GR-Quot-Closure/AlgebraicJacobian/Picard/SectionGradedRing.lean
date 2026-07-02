import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.GradedModule
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
import Mathlib.RingTheory.PicardGroup

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
(`lem:sheafTensorPow_add`, here `tensorPowAdd`) is **built** (iter-007 monoidal-localization pivot:
the sheaf tensor product inherits a full `MonoidalCategory`/`SymmetricCategory` structure via
`CategoryTheory.Localization.Monoidal`).  On top of it this file assembles the section graded
semiring `Γ_*(X,L)` (∀ `L`), its commutative upgrade for invertible `L`, and the graded module
`M(X,L,F) = ⊕_m Γ(F ⊗ L^{⊗m})`.
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

@[simp] private lemma tensorPow_zero (L : X.Modules) : tensorPow L 0 = unitModule X := rfl

@[simp] private lemma tensorPow_succ (L : X.Modules) (m : ℕ) :
    tensorPow L (m + 1) = tensorObj (tensorPow L m) L := rfl

/-- The `m`-twist `F(m) = F ⊗ L^{⊗m}` of a sheaf of modules `F` by the `m`-th
tensor power of a line bundle `L` (`def:sheafModuleTwist`).  This is the
degree-`m` carrier of the section graded module. -/
noncomputable def moduleTensorPow (F L : X.Modules) (m : ℕ) : X.Modules :=
  tensorObj F (tensorPow L m)

@[simp] private lemma moduleTensorPow_zero (F L : X.Modules) :
    moduleTensorPow F L 0 = tensorObj F (unitModule X) := rfl

/-- An **invertible** sheaf of modules (`def:isInvertible`, [Stacks, Tag 01CR]): `L` carries a
**trivializing basis** — a basis `{Uᵢ}` of opens of `X` on each of which the section module
`Γ(L, Uᵢ)` is an invertible `Γ(X, Uᵢ)`-module (equivalently, locally free of rank one,
[Stacks, Tag 01CR]).  Over a scheme every stalk is a local ring, so an invertible module over a
local ring is free of rank one (`CommRing.Pic.instFreeOfSubsingleton`).  This is the
line-bundle hypothesis under which the section graded ring becomes commutative
(`lem:sectionGradedRing_gcommSemiring`); for a general sheaf the section ring is the free
tensor algebra on `Γ(X,L)` and is non-commutative, which is why Stacks defines `Γ_*(X,𝓛)`
only for invertible `𝓛`.  The sole arithmetic consequence consumed is the trivial
self-braiding `β_{L,L} = 𝟙` (`tensorBraiding_self_eq_id_of_isInvertible`,
`lem:braiding_eq_id_of_invertible`), proved by basis-local descent via
`Module.Invertible.tensorProductComm_eq_refl` — crucially, the braiding is never evaluated at
the global open `⊤` (where `Γ(X, L)` need not be invertible). -/
class IsInvertible (L : X.Modules) : Prop where
  /-- There exists an indexed basis `{Uᵢ}` of opens of `X` such that the section module
  `Γ(L, Uᵢ)` is an invertible `Γ(X, Uᵢ)`-module for each `i`. -/
  exists_trivializing_basis :
    ∃ (ι : Type u) (U : ι → TopologicalSpace.Opens X),
      TopologicalSpace.Opens.IsBasis (Set.range U) ∧
      ∀ i, Module.Invertible ↥(X.presheaf.obj (Opposite.op (U i)))
                              ↥(L.val.obj (Opposite.op (U i)))

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
private noncomputable def tensorObjUnitIso (G : X.Modules) :
    tensorObj (unitModule X) G ≅ G :=
  sheafification.mapIso
      (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G)) ≪≫
    sheafificationCounitIso G

/-- The right-unitor isomorphism `G ⊗ unitModule X ≅ G` of the sheaf tensor
product: the presheaf right unitor `ρ_` descended through sheafification, composed
with the counit iso `sheafificationCounitIso`.  Axiom-clean (no monoidal structure
on `X.Modules` is required). -/
noncomputable def tensorObjRightUnitor (G : X.Modules) :
    tensorObj G (unitModule X) ≅ G :=
  sheafification.mapIso
      (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G)) ≪≫
    sheafificationCounitIso G

/-- The braiding isomorphism `F ⊗ G ≅ G ⊗ F` of the sheaf tensor product,
descended through sheafification from the symmetric braiding on
`X.PresheafOfModules` (`PresheafOfModules.monoidalCategory`).  Axiom-clean: the
braiding is pure sheafification-functoriality of the presheaf-level braiding, so
no monoidal structure on `X.Modules` is required.  This is the symmetry used in
the inductive step of `tensorPowAdd`. -/
private noncomputable def tensorBraiding (F G : X.Modules) :
    tensorObj F G ≅ tensorObj G F :=
  sheafification.mapIso
    (BraidedCategory.braiding (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))

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

/-- **Sheafification inverts the localization unit.**  `sheafification.map η_P` is an
isomorphism of sheaves of modules (the reflective-localization unit becomes invertible
after sheafifying).  Obtained by feeding `localIso_toPresheaf_map_unit` through the
localization criterion `isIso_sheafification_map_iff`.  Project-local: the `m = 0`
launching pad and the un-whiskered special case of
`isIso_sheafification_whiskerRight_unit`. -/
lemma isIso_sheafification_map_unit (P : X.PresheafOfModules) :
    IsIso (sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  rw [isIso_sheafification_map_iff]
  exact localIso_toPresheaf_map_unit _

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
      exact key)

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
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply] at hz
    exact hz

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
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply] at hz
    exact hz

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
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap] at hz
    exact hz

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

/-
### Action / projection natural transformations of the coequalizer rows — DEFERRED (handoff)

The next promotion step assembles `actLmap`/`actRmap`/`projL` into NATURAL transformations of
`(Opens X)ᵒᵖ ⥤ Ab` between `relTensorTriplePresheaf P Q`, `relTensorDomainPresheaf P Q`, and the
apex `(toPresheaf).obj (P ⊗_p Q)`, then lifts the cofork via
`CategoryTheory.Limits.evaluationJointlyReflectsColimits` (apex identified by
`PresheafOfModules.Monoidal.tensorObj_obj`) to `relativeTensorCoequalizerIso`
(`lem:relativeTensor_as_coequalizer`).

The left-action component
`app U := AddCommGrpCat.ofHom (RelativeTensorCoequalizer.actLmap (X.sheaf.obj.obj U) (P.obj U)
(Q.obj U)).toAddMonoidHom : relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q` TYPECHECKS,
and naturality reduces mathematically to the SINGLE fact `PresheafOfModules.map_smul` on
`m ⊗ (s ⊗ n)`, bridged onto the abelian restriction by the verified lemma
`PresheafOfModules.presheaf_map_apply_coe : (M.presheaf.map f).hom x = (ConcreteCategory.hom (M.map f)) x`.

BLOCKER (iter-056, root-caused after ~12 distinct attempts — a genuine whnf/defeq matching wall):
after peeling the `≫`-composite (`AddCommGrpCat.hom_comp` + `AddMonoidHom.comp_apply`),
`TensorProduct.map_tmul` / `LinearMap.toAddMonoidHom_coe` REFUSE to reduce the inner
`(TensorProduct.map (P.presheaf.map f).hom.toIntLinearMap …).toAddMonoidHom (m ⊗ₜ (s ⊗ₜ n))`.
Root cause: the `tmul` element comes from `TensorProduct.induction_on` on `x : ↥(obj U)` where
`obj U = AddCommGrpCat.of (P.obj U ⊗[ℤ] …)`, so `m : ↥(P.obj U)`, whereas the restriction map
(`(P.presheaf.map f).hom.toIntLinearMap`, the only `ℤ`-linear restriction Mathlib provides) has
domain `↥((P.presheaf).obj U)`.  These carriers are `rfl`-defeq but SYNTACTICALLY distinct, so
`map_tmul`'s LHS `(TensorProduct.map ?f ?g) (?a ⊗ₜ ?b)` cannot unify the element's tensor type with
the map's domain.  VERIFIED: the identical reduction succeeds in isolation when the carriers agree
(both free, or both `(AddCommGrpCat.Hom.hom φ).toIntLinearMap` with matching domain).

Attempts ruled out THIS iter (all hit the SAME element-vs-map carrier gap from a different angle):
  • pure-`LinearMap` lemma + `LinearMap.congr_fun` (`comp_apply` peels one side, `rw` misses other);
  • `show … from`-ascribing restriction maps to `↥(P.obj ·)` — defeq-erased, no effect;
  • `inferInstanceAs`-aligning `actLmap`'s domain carriers to `(P.presheaf).obj ·` — typechecks, but
    the restriction-map side still mismatches the `obj`-carrier element;
  • making BOTH presheaves' `obj` carriers `(P.presheaf).obj ·` (so induction elements match the
    maps) — CASCADES: breaks the proven `relTensorDomainPresheaf.map_id`/`map_comp` (their `𝟙`/`rfl`
    leaves now mismatch) AND `comp_apply` becomes intermittent; reverted;
  • full `simp`, `erw`, explicit `rw` chains, `conv … => enter [2]` (focuses the subterm, the def-
    unfold + `hom_ofHom` fire there but `map_tmul` STILL doesn't) — same wall.

NEXT-ITER HANDLES (untried, in priority order):
  (1) Provide a `ℤ`-linear restriction with SYNTACTIC `↥(P.obj U) → ↥(P.obj V)` carriers as a DISTINCT
      term (not a defeq ascription) — e.g. from the `ModuleCat` restriction `P.map f` via
      `ModuleCat.Hom.hom` + a `restrictScalars` carrier-identity — and use it uniformly in
      `relTensorTriplePresheaf`/`relTensorDomainPresheaf` AND `actLmap`, so element and map carriers
      agree by construction.  Re-prove the (now trivial) `map_id`/`map_comp`.
  (2) After peeling, `eqToHom`/`cast`-transport the inner element `BIG : ↥((P.presheaf).obj V)⊗…` to
      the `↥(P.obj V)⊗…`-form (or vice versa) so `map_tmul` matches, then transport back.
  (3) Escalate: this is the documented diamond/whnf friction (memory `quot-gap1-closed-opaque-immersion`),
      and the math content is one `map_smul`; a Mathlib-side `@[simp]` apply lemma for the abelian
      restriction-map-on-tmul (or a `PresheafOfModules`/`AddCommGrpCat`-tensor restriction API) would
      dissolve it.

-/

/-
### (superseded handoff notes — retained for the additional `inferInstanceAs` detail)

The remaining promotion step assembles `actRmap`/`projL` into NATURAL transformations of
`(Opens X)ᵒᵖ ⥤ Ab` between `relTensorTriplePresheaf P Q`, `relTensorDomainPresheaf P Q`, and the
apex `(toPresheaf).obj (P ⊗_p Q)`, then lifts the cofork via
`CategoryTheory.Limits.evaluationJointlyReflectsColimits` (apex identified by
`PresheafOfModules.Monoidal.tensorObj_obj`) to `relativeTensorCoequalizerIso`
(`lem:relativeTensor_as_coequalizer`).

The left-action component
`app U := AddCommGrpCat.ofHom (RelativeTensorCoequalizer.actLmap (X.sheaf.obj.obj U) (P.obj U)
(Q.obj U)).toAddMonoidHom : relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q` TYPECHECKS,
and naturality reduces mathematically to `PresheafOfModules.map_smul` on `m ⊗ (s ⊗ n)`, bridged onto
the abelian restriction by the verified lemma
`PresheafOfModules.presheaf_map_apply_coe : (M.presheaf.map f).hom x = (ConcreteCategory.hom (M.map f)) x`.

BLOCKER (iter-056, attempted at length, NOT a carrier mismatch): after peeling the `≫`-composite
(`AddCommGrpCat.hom_comp` + `AddMonoidHom.comp_apply` — both fire), `simp`/`rw` REFUSE to reduce the
inner `(TensorProduct.map …).toAddMonoidHom (m ⊗ₜ (s ⊗ₜ n))` while it sits UNDER the
`actLmap.toAddMonoidHom (…)` head: `LinearMap.toAddMonoidHom_coe` and `TensorProduct.map_tmul` report
`unused`/no-progress, *even though* the IDENTICAL reduction succeeds in isolation (verified:
`simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul]` closes
`(TensorProduct.map A (TensorProduct.map B C)).toAddMonoidHom (m ⊗ₜ (s ⊗ₜ n)) = A m ⊗ₜ (B s ⊗ₜ C n)`).

Approaches tried and ruled out THIS iter:
  • pure-`LinearMap` naturality lemma + `LinearMap.congr_fun` transport — `LinearMap.comp_apply`
    peels one side, `rw` fails to find the pattern on the other (`(?f ∘ₛₗ ?g) ?x` not matched);
  • `show … from`-ascribing the restriction maps to `↥(P.obj ·)` carriers — defeq-erased, no effect;
  • aligning `actLmap`'s domain carriers to the `(P.presheaf).obj ·`-form via VERIFIED
    `inferInstanceAs`-transported `Module` instances (so `actLmap`'s domain matches the restriction
    maps' codomain SYNTACTICALLY) — typechecks, but `simp` STILL refuses the inner reduction, proving
    the wall is a `simp`/whnf descent pathology under the (folded, large) `actLmap` head, NOT the
    `(P.presheaf).obj`-vs-`P.obj` carrier gap;
  • full `simp` (vs `simp only`), `erw`, explicit `rw` chains — same.

NEXT-ITER HANDLES (untried): (1) reduce the inner map application BEFORE composing — e.g. rewrite
`(relTensorTriplePresheaf P Q).map f` to a pre-reduced `tmul`-aware form via a dedicated
`@[simp] relTensorTriplePresheaf_map_tmul` lemma proved by `rfl`/`induction`, so the naturality leaf
never has to descend under `actLmap`; (2) `conv`-navigate explicitly into the `actLmap` argument
and rewrite there; (3) prove the AddMonoidHom equality by `DFunLike.ext` on the COMPOSITE BEFORE
peeling, exposing both maps' actions simultaneously.  The genuine mathematical content is the single
`map_smul`/`presheaf_map_apply_coe` step.

The component `app U := AddCommGrpCat.ofHom (actLmap (X.sheaf.obj.obj U) (P.obj U)
(Q.obj U)).toAddMonoidHom : relTensorTriplePresheaf P Q ⟶ relTensorDomainPresheaf P Q` TYPECHECKS,
and naturality reduces mathematically to `PresheafOfModules.map_smul` on `m ⊗ (s ⊗ n)`, bridged onto
the abelian restriction `(P.presheaf.map f)` by the verified lemma
`PresheafOfModules.presheaf_map_apply_coe : (M.presheaf.map f).hom x = (ConcreteCategory.hom (M.map f)) x`.

BLOCKER (iter-056, root-caused): after peeling the `≫`-composite (`AddCommGrpCat.hom_comp` +
`AddMonoidHom.comp_apply`, both fire on the small folded form), `simp`/`rw` CANNOT descend into
`actLmap_V.toAddMonoidHom (BIG)` to reduce the inner
`BIG = (TensorProduct.map …).toAddMonoidHom (m ⊗ₜ (s ⊗ₜ n))`: `LinearMap.toAddMonoidHom_coe` and
`TensorProduct.map_tmul` (verified to fire on the IDENTICAL term in isolation) report `unused`.
Cause: `BIG : ↥((P.presheaf).obj V) ⊗ …` (codomain of the abelian restriction maps in
`relTensorTriplePresheaf.map`), whereas `actLmap_V`'s domain is `↥(P.obj V) ⊗ …`.  These are
`rfl`-defeq but SYNTACTICALLY distinct, so `simp`'s congruence motive `fun a => actLmap_V.toAddMonoidHom a`
fails to typecheck `BIG` at the abstracted (P.obj-form) domain and refuses to rewrite under the head.

ATTEMPTED + RULED OUT: (i) a pure-`LinearMap` naturality lemma + `LinearMap.congr_fun` transport —
same carrier mismatch (`rw [LinearMap.comp_apply]` peels one side, fails on the other).  (ii) Type
ascription `show ↥(P.obj U) →ₗ[ℤ] ↥(P.obj V) from (P.presheaf.map f).hom.toIntLinearMap` on the
presheaves' restriction maps — ELABORATED AWAY (defeq), the underlying term stays `(P.presheaf.map f)`.

GENUINE FIX (next iter), most promising FIRST: align `actLmap`'s domain carriers with the restriction
maps' `(P.presheaf).obj`-form instead of the reverse.  Define `app U` as
`AddCommGrpCat.ofHom (actLmap (X.sheaf.obj.obj U) ((P.presheaf).obj U) ((Q.presheaf).obj U)).toAddMonoidHom`,
supplying the `Module ↥(X.sheaf.obj.obj U) ↥((P.presheaf).obj U)` instances (NOT auto-found) by
`inferInstanceAs (Module _ ↥(P.obj U))` — VERIFIED to elaborate (the carriers are `rfl`-defeq and the
instance transports).  Then `actLmap_V`'s domain is SYNTACTICALLY `↥((P.presheaf).obj V) ⊗ …`,
matching `BIG`, so `simp` descends and `map_tmul`/`actLmap_tmul`/`presheaf_map_apply_coe`/`map_smul`
close it.  The wrinkle: the `letI`/`haveI` instances must be in scope for the `naturality` proof too
(use a top-level `haveI` by writing the `NatTrans` via `{ app := …, naturality := … }` inside a
`by`-block that opens the instances, or thread them explicitly).  Alternative fixes: (a) a `(P.map f)`-derived
`ℤ`-linear restriction with `P.obj` codomain; (b) `erw`/`conv`/`eqToHom`-transport of `BIG`.  The genuine
mathematical content is the single `map_smul`/`presheaf_map_apply_coe` step; the rest is carrier
bookkeeping.  Once `relTensorActL`/`relTensorActR`/`relTensorProj` land, lift the cofork to
`Cᵒᵖ ⥤ Ab` via `CategoryTheory.Limits.evaluationJointlyReflectsColimits` (apex identified with
`(toPresheaf).obj (P ⊗_p Q)` by `PresheafOfModules.Monoidal.tensorObj_obj`), giving
`relativeTensorCoequalizerIso` (`lem:relativeTensor_as_coequalizer`).

-/

/-
### The tensor-power comparison isomorphism `tensorPowAdd` — BUILT (iter-007 pivot)

HISTORICAL NOTE.  Earlier iterations left the comparison isomorphism
(`lem:sheafTensorPow_add`, [Stacks, Tag 01CU])

  `tensorPowAdd (L : X.Modules) (m m' : ℕ) :`
  `  tensorObj (tensorPow L m) (tensorPow L m') ≅ tensorPow L (m + m')`

deferred, pending the sheaf-level **associator** — equivalently the strong-monoidality of the module
sheafification functor.  The iter-007 pivot resolved this directly: the sheaf tensor product inherits
a full `MonoidalCategory`/`SymmetricCategory` structure on `X.Modules` from Mathlib's
`CategoryTheory.Localization.Monoidal` machinery (the sheafification localizer), so `tensorObjAssoc`
is the *canonical* associator transported along the bridge `tensorObjIso` and `tensorPowAdd` is built
unconditionally (see `tensorPowAdd`, `tensorPowAdd_assoc`, etc. below).  The abandoned
`RelativeTensorCoequalizer` route (presenting the relative tensor as an abelian coequalizer to invert
`η_P ▷ Q` through `GrothendieckTopology.W.monoidal`) is no longer on the critical path; the
`namespace RelativeTensorCoequalizer` helpers above are retained only as inherited coverage debt to be
resolved at merge — do not extend them.
-/

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

@[simp] private lemma toULiftIntLinearMap_apply {M N : Type u} [AddCommGroup M]
    [AddCommGroup N] (φ : M →+ N) (x : M) : toULiftIntLinearMap φ x = φ x := rfl

/-- The `ℤ`- and `ULift ℤ`-actions on abelian groups are tensor-compatible. -/
private instance compatibleSMul_int_uliftInt (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] : CompatibleSMul ℤ (ULift.{u} ℤ) M N :=
  ⟨fun c m n => smul_tmul c.down m n⟩

/-- The relative tensor product over `ULift ℤ` of two abelian groups agrees with their
`ℤ`-tensor product (`TensorProduct.equivOfCompatibleSMul`); both directions send an
elementary tensor `m ⊗ₜ n` to `m ⊗ₜ n`. -/
private noncomputable def uTensorEquiv (M N : Type u) [AddCommGroup M] [AddCommGroup N] :
    (M ⊗[ULift.{u} ℤ] N) ≃ₗ[ℤ] (M ⊗[ℤ] N) :=
  TensorProduct.equivOfCompatibleSMul ℤ (ULift.{u} ℤ) ℤ M N

@[simp] private lemma uTensorEquiv_tmul (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    (m : M) (n : N) : uTensorEquiv M N (m ⊗ₜ n) = m ⊗ₜ n := rfl

@[simp] private lemma uTensorEquiv_symm_tmul (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] (m : M) (n : N) : (uTensorEquiv M N).symm (m ⊗ₜ n) = m ⊗ₜ n := rfl

/-- The triple-tensor variant of `uTensorEquiv`:
`M ⊗[ULift ℤ] (S ⊗[ULift ℤ] N) ≃ M ⊗[ℤ] (S ⊗[ℤ] N)`, sending `m ⊗ₜ (s ⊗ₜ n)` to itself. -/
private noncomputable def uTripleEquiv (M S N : Type u) [AddCommGroup M] [AddCommGroup S]
    [AddCommGroup N] :
    (M ⊗[ULift.{u} ℤ] (S ⊗[ULift.{u} ℤ] N)) ≃ₗ[ℤ] (M ⊗[ℤ] (S ⊗[ℤ] N)) :=
  (uTensorEquiv M (S ⊗[ULift.{u} ℤ] N)) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl ℤ M) (uTensorEquiv S N))

@[simp] private lemma uTripleEquiv_tmul (M S N : Type u) [AddCommGroup M] [AddCommGroup S]
    [AddCommGroup N] (m : M) (s : S) (n : N) :
    uTripleEquiv M S N (m ⊗ₜ (s ⊗ₜ n)) = m ⊗ₜ (s ⊗ₜ n) := rfl

@[simp] private lemma uTripleEquiv_symm_tmul (M S N : Type u) [AddCommGroup M]
    [AddCommGroup S] [AddCommGroup N] (m : M) (s : S) (n : N) :
    (uTripleEquiv M S N).symm (m ⊗ₜ (s ⊗ₜ n)) = m ⊗ₜ (s ⊗ₜ n) := rfl

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

@[simp] private lemma modToAb_map_apply {M N : ModuleCat.{u} (ULift.{u} ℤ)} (ψ : M ⟶ N)
    (x : M) : (ConcreteCategory.hom (modToAb.map ψ)) x = ψ.hom x := rfl

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

/-! ### The symmetric monoidal structure on `X.Modules` by monoidal localization
(`def:sheafModule_W_isMonoidal`, `def:sheafModule_monoidalStructure`)

Following `analogies/tensorobjassoc.md` and the Mathlib precedent
`CategoryTheory.Sheaf.monoidalCategory` (`Mathlib/CategoryTheory/Sites/Monoidal.lean:165`):
module sheafification is the localization functor at the class `W'` of morphisms of presheaves
of `𝒪_X`-modules whose underlying abelian-presheaf morphism is a local isomorphism
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`).  We prove that `W'` is
*compatible with the presheaf tensor product* (`W_isMonoidal`), then transport the entire
symmetric monoidal structure of `MonoidalPresheaf X` onto `X.Modules` via Mathlib's
`LocalizedMonoidal` machinery (`monoidalCategory`, `braidedCategory`, `symmetricCategory`).
The associator, pentagon, triangle, braiding and hexagon are therefore **inherited** rather
than hand-proved, dissolving the non-canonicity of the hand-rolled `tensorObjAssoc`. -/

/-- The sheafification functor typed with the **monoidal** presentation `MonoidalPresheaf X` of its
domain (definitionally `X.PresheafOfModules`).  A reducible abbreviation so that instance synthesis
sees the `PresheafOfModules (R ⋙ forget₂ _ _)` carrier form on which Mathlib registers the symmetric
monoidal structure, while still unfolding to `sheafification` for the `IsLocalization` instance. -/
noncomputable abbrev sheafificationMon (X : Scheme.{u}) : MonoidalPresheaf X ⥤ X.Modules :=
  sheafification

/-- The **sheafification localization class** `W'` on presheaves of `𝒪_X`-modules: the morphisms
whose underlying abelian-presheaf morphism `(toPresheaf R₀).map f` lies in the local-isomorphism
class `J.W` of the opens topology, equivalently the morphisms that module sheafification sends to
isomorphisms.  This is exactly the class for which `sheafification` is a localization functor
(`PresheafOfModules.sheafification … .IsLocalization (J.W.inverseImage (toPresheaf R₀))`,
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean:48`).  Typed as a morphism property of
`MonoidalPresheaf X` (definitionally `X.PresheafOfModules`) for monoidal-instance synthesis. -/
abbrev sheafificationW (X : Scheme.{u}) : MorphismProperty (MonoidalPresheaf X) :=
  (opensTopology X).W.inverseImage (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

/-- The sheafification functor is a localization functor for `sheafificationW`.  This bridges the
project's `sheafification` (a non-reducible `def`) to Mathlib's localization instance on
`PresheafOfModules.sheafification (𝟙 R₀)` (`ModuleCat/Sheaf/Localization.lean:48`), which instance
resolution would not otherwise unfold to. -/
instance sheafificationMon_isLocalization :
    (sheafificationMon X).IsLocalization (sheafificationW X) :=
  inferInstanceAs ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
    ((opensTopology X).W.inverseImage (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))

/-- **Tensor-compatibility of the sheafification localization class**
(`def:sheafModule_W_isMonoidal`):
the class `W' = J.W.inverseImage (toPresheaf R₀)` satisfies `MorphismProperty.IsMonoidal`, i.e. it is
multiplicative and stable under left- and right-whiskering by arbitrary presheaves of modules.

* Multiplicativity is inherited (`W'` is an `inverseImage`, and the inverse image of the
  multiplicative class `J.W` is multiplicative).
* The right-whiskering field is the already-proven general whisker brick
  `ztensor_whisker_localIso`: for any `f` with `(toPresheaf R₀).map f ∈ J.W` and any `R`, the
  underlying abelian morphism of `f ▷ R` is again a local isomorphism.
* The left-whiskering field follows by conjugating the right-whiskering field with the symmetric
  braiding of `MonoidalPresheaf X` (`PresheafOfModules.symmetricCategory`): `Z ◁ g` and `g ▷ Z`
  are carried to one another by the braiding isomorphism on both ends, and membership in `W'` is
  invariant under isomorphism of arrows (`MorphismProperty.arrow_mk_iso_iff`).  This is the trick
  Mathlib uses in the opposite direction at `Sites/Monoidal.lean:144`.

This is the only project-supplied input of the monoidal-localization transport; with it,
`Mathlib.CategoryTheory.Localization.Monoidal` produces the whole structure for free. -/
instance W_isMonoidal : (sheafificationW X).IsMonoidal where
  whiskerRight f hf Y := ztensor_whisker_localIso f hf Y
  whiskerLeft Z {Y₁ Y₂} g hg :=
    ((sheafificationW X).arrow_mk_iso_iff
      (Arrow.isoMk (β_ Z Y₁) (β_ Z Y₂)
        (by exact (BraidedCategory.braiding_naturality_right Z g).symm))).2
      (ztensor_whisker_localIso g hg Z)

/-- The preferred unit isomorphism feeding the monoidal-localization transport: the underlying
presheaf of the unit module `𝟙_X = SheafOfModules.unit` is *definitionally* the monoidal unit
`𝟙_ (MonoidalPresheaf X) = PresheafOfModules.unit R₀`, and `unitModule X` is already a sheaf, so
its sheafification counit `sheafificationCounitIso` identifies `sheafification.obj (𝟙_ C)` with
`unitModule X`.  This picks `unitModule X` as the tensor unit of the transported structure. -/
noncomputable def localizationUnitIso (X : Scheme.{u}) :
    (sheafificationMon X).obj (𝟙_ (MonoidalPresheaf X)) ≅ unitModule X :=
  sheafificationCounitIso (unitModule X)

/-- **The monoidal structure on `X.Modules` by transport** (`def:sheafModule_monoidalStructure`):
the category `X.Modules` of sheaves of `𝒪_X`-modules acquires a `MonoidalCategory` structure by
transporting the monoidal structure of `MonoidalPresheaf X` along the sheafification localization
functor (`CategoryTheory.Localization.LocalizedMonoidal`).  The associator is the canonical
Mac Lane associator and the pentagon and triangle laws hold by inheritance.  The tensor unit is
`unitModule X` (see `localizationUnitIso`). -/
@[instance_reducible]
noncomputable def monoidalCategory : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafificationMon X) (W := sheafificationW X)
      (localizationUnitIso X)))

attribute [local instance] monoidalCategory

/-- The transported monoidal structure on `X.Modules` is **braided**, inherited from the symmetric
braiding of `MonoidalPresheaf X` (`Mathlib.CategoryTheory.Localization.Monoidal.Braided`). -/
@[implicit_reducible]
noncomputable def braidedCategory : BraidedCategory X.Modules :=
  inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := sheafificationMon X) (W := sheafificationW X)
      (localizationUnitIso X)))

attribute [local instance] braidedCategory

/-- The transported monoidal structure on `X.Modules` is **symmetric**
(`def:sheafModule_monoidalStructure`), inherited from the symmetric monoidal structure of
`MonoidalPresheaf X` (`PresheafOfModules.symmetricCategory`); in particular the hexagon identities
hold by inheritance. -/
@[implicit_reducible]
noncomputable def symmetricCategory : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := sheafificationMon X) (W := sheafificationW X)
      (localizationUnitIso X)))

/-- **The inherited tensor product agrees with the project's `tensorObj`.**  The strong-monoidal
comparison `μ` of the monoidal localization, precomposed with the sheafification counit isomorphisms
on each factor, identifies the *transported* tensor product `F ⊗ G` (`monoidalCategory`) with the
project's hand-built sheaf tensor product `tensorObj F G`.  This is the bridge that lets the
inherited (canonical) associator/unitor/braiding coherence be read off as coherence for the
project's `tensorObj` family — the launching pad for rewiring `tensorObjAssoc`, `tensorPowAdd` and
the section-multiplication coherence laws onto the inherited structure. -/
noncomputable def tensorObjIso (F G : X.Modules) :
    F ⊗ G ≅ tensorObj F G :=
  MonoidalCategory.tensorIso (sheafificationCounitIso F).symm (sheafificationCounitIso G).symm ≪≫
    Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)

/-! ### Bridge lemmas: hand-built unitors/braiding equal the canonical ones via `tensorObjIso`

The unit object `𝟙_ X.Modules` of the inherited `monoidalCategory` is *definitionally* `unitModule X`
(it is the codomain of the localization unit `ε = localizationUnitIso X`).  These lemmas identify the
hand-built `tensorObjUnitIso`/`tensorObjRightUnitor`/`tensorBraiding` with the canonical
`λ_`/`ρ_`/`β_` transported along the bridge `tensorObjIso`, so the coherence laws of `tensorPowAdd`
and the section multiplication can be read off the canonical (Mac Lane / hexagon) coherence. -/

set_option backward.isDefEq.respectTransparency false in
/-- Bridge: the hand-built right unitor is the canonical `ρ_` transported along `tensorObjIso`. -/
lemma tensorObjRightUnitor_eq (G : X.Modules) :
    tensorObjRightUnitor G = (tensorObjIso G (unitModule X)).symm ≪≫ ρ_ G := by
  apply Iso.ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.eq_inv_comp]
  -- Replace `(ρ_ G).hom` by the canonical right unitor of `sheafification.obj g` conjugated by the
  -- sheafification counit, via right-unitor naturality (`f = counit.inv : G ⟶ sheafification.obj g`).
  have hnat : G.sheafificationCounitIso.inv ▷ (𝟙_ X.Modules) ≫
        (ρ_ (sheafification.obj ((toPresheafOfModules X).obj G))).hom ≫
          G.sheafificationCounitIso.hom = (ρ_ G).hom := by
    rw [← Category.assoc, MonoidalCategory.rightUnitor_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  -- The canonical right unitor of `sheafification.obj g` via Mathlib's `rightUnitor_hom_app`
  -- (stated in the exact syntactic form occurring in the goal; `exact` absorbs the
  -- `(toMonoidalCategory …).obj = sheafification.obj` / `ε' = localizationUnitIso` defeqs).
  have hru : (ρ_ (sheafification.obj ((toPresheafOfModules X).obj G))).hom =
      sheafification.obj ((toPresheafOfModules X).obj G) ◁ (localizationUnitIso X).inv ≫
        (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
          ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj (unitModule X))).hom ≫
        sheafification.map (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom :=
    Localization.Monoidal.rightUnitor_hom_app (sheafificationMon X) (sheafificationW X)
      (localizationUnitIso X) ((toPresheafOfModules X).obj G)
  dsimp only [tensorObjRightUnitor, tensorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom]
  rw [← hnat, hru]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bridge: the hand-built left unitor is the canonical `λ_` transported along `tensorObjIso`. -/
private lemma tensorObjUnitIso_eq (G : X.Modules) :
    tensorObjUnitIso G = (tensorObjIso (unitModule X) G).symm ≪≫ λ_ G := by
  apply Iso.ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.eq_inv_comp]
  have hnat : (𝟙_ X.Modules) ◁ G.sheafificationCounitIso.inv ≫
        (λ_ (sheafification.obj ((toPresheafOfModules X).obj G))).hom ≫
          G.sheafificationCounitIso.hom = (λ_ G).hom := by
    rw [← Category.assoc, MonoidalCategory.leftUnitor_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hlu : (λ_ (sheafification.obj ((toPresheafOfModules X).obj G))).hom =
      (localizationUnitIso X).inv ▷ sheafification.obj ((toPresheafOfModules X).obj G) ≫
        (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
          ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)).hom ≫
        sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom :=
    Localization.Monoidal.leftUnitor_hom_app (sheafificationMon X) (sheafificationW X)
      (localizationUnitIso X) ((toPresheafOfModules X).obj G)
  dsimp only [tensorObjUnitIso, tensorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom]
  rw [← hnat, hlu]
  simp only [Category.assoc]
  -- v4.31: the leading `⊗ₘ`-vs-whisker pair is `tensorHom_def'` (a theorem, not a defeq in the
  -- transported structure).  `simp`/`erw` congruence cannot descend into the goal (type-incorrect
  -- at `instances` transparency via `X.ringCatSheaf.obj`), so restate by `show` (checked at
  -- default transparency) to expose the `⊗ₘ` head syntactically, then rewrite at top level.
  show (((unitModule X).sheafificationCounitIso.inv ⊗ₘ G.sheafificationCounitIso.inv) ≫
      (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
        ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)).hom) ≫
      (sheafification.map (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom ≫
        G.sheafificationCounitIso.hom) = _
  rw [MonoidalCategory.tensorHom_def']
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bridge: the hand-built braiding is the canonical `β_` transported along `tensorObjIso`. -/
private lemma tensorBraiding_eq (F G : X.Modules) :
    tensorBraiding F G = (tensorObjIso F G).symm ≪≫ β_ F G ≪≫ tensorObjIso G F := by
  apply Iso.ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom, Iso.eq_inv_comp]
  -- Reduce `(β_ F G).hom` to the canonical braiding of `sheafification.obj`'s conjugated by counits.
  have hbnat : (F.sheafificationCounitIso.inv ⊗ₘ G.sheafificationCounitIso.inv) ≫
        (β_ (sheafification.obj ((toPresheafOfModules X).obj F))
            (sheafification.obj ((toPresheafOfModules X).obj G))).hom ≫
          (G.sheafificationCounitIso.hom ⊗ₘ F.sheafificationCounitIso.hom) = (β_ F G).hom := by
    rw [← BraidedCategory.braiding_naturality, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp]
  -- The canonical braiding of `sheafification.obj` via Mathlib's `β_hom_app` (the localized
  -- monoidal functor's `LaxMonoidal.μ`/`δ` are definitionally `Localization.Monoidal.μ`'s
  -- `hom`/`inv`, so `exact` accepts the canonical-`μ` phrasing).
  have hβ : (β_ (sheafification.obj ((toPresheafOfModules X).obj F))
        (sheafification.obj ((toPresheafOfModules X).obj G))).hom =
      (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom ≫
        sheafification.map (BraidedCategory.braiding (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom ≫
        (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
          ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)).inv :=
    Localization.Monoidal.β_hom_app (sheafificationMon X) (sheafificationW X)
      (localizationUnitIso X) ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)
  dsimp only [tensorBraiding, tensorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom]
  rw [← hbnat, hβ]
  -- Peel the common left factor `(F.inv ⊗ G.inv)`, collapse the counit cancellation
  -- `(G.hom ⊗ F.hom) ≫ (G.inv ⊗ F.inv) = 𝟙`, then cancel `μ_{g,f}⁻¹ ≫ μ_{g,f} = 𝟙`.  The final
  -- associativity steps are done in **term mode** (`Category.assoc _ _ _`): tactic `rw`/`simp` cannot
  -- match the composition pattern across the `LocalizedMonoidal`/`X.Modules` instance diamond, but a
  -- term-level `Category.assoc` is checked up to defeq and so goes through.
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_tensorHom_id, Category.id_comp]
  congr 1
  -- residual: `μ_{f,g} ≫ map = (μ_{f,g} ≫ map ≫ μ_{g,f}⁻¹) ≫ μ_{g,f}`.
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg _ (Category.assoc _ _ _)).trans ?_
  -- `erw` (keyed matching at higher transparency) bridges the instance diamond that blocks `rw`.
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

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
    tensorObj (tensorObj A B) C ≅ tensorObj A (tensorObj B C) :=
  -- iter-008 REWIRE: the associator is now the *canonical* Mac Lane associator `α_` of the
  -- inherited `monoidalCategory X.Modules` (built by monoidal localization, iter-007),
  -- transported along the bridge `tensorObjIso : F ⊗ G ≅ tensorObj F G`.  This dissolves the
  -- non-canonicity of the old hand-rolled double-braiding composite: `tensorObjAssoc` now
  -- inherits pentagon/triangle coherence from the canonical `α_` by construction.
  (tensorObjIso (tensorObj A B) C).symm ≪≫
    MonoidalCategory.whiskerRightIso (tensorObjIso A B).symm C ≪≫
    α_ A B C ≪≫
    MonoidalCategory.whiskerLeftIso A (tensorObjIso B C) ≪≫
    tensorObjIso A (tensorObj B C)

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

set_option backward.isDefEq.respectTransparency false in
/-- Bridge: the hand-built left-whiskering `tensorObjWhiskerLeftIso F e` is the canonical left
whiskering `F ◁ e` transported along the bridge `tensorObjIso`.  Mirror of `tensorBraiding_eq`,
using `μ`-naturality in the right variable (`Localization.Monoidal.μ_natural_right`). -/
private lemma tensorObjWhiskerLeftIso_eq (F : X.Modules) {G G' : X.Modules} (e : G ≅ G') :
    tensorObjWhiskerLeftIso F e
      = (tensorObjIso F G).symm ≪≫ MonoidalCategory.whiskerLeftIso F e ≪≫ tensorObjIso F G' := by
  apply Iso.ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom, Iso.eq_inv_comp]
  -- `hwnat`: the canonical whisker `F ◁ e.hom` equals the sheaf-level whisker conjugated by
  -- counits.
  have hwnat : (F.sheafificationCounitIso.inv ⊗ₘ G.sheafificationCounitIso.inv) ≫
        (sheafification.obj ((toPresheafOfModules X).obj F) ◁
          sheafification.map ((toPresheafOfModules X).map e.hom)) ≫
        (F.sheafificationCounitIso.hom ⊗ₘ G'.sheafificationCounitIso.hom)
      = F ◁ e.hom := by
    rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    refine congrArg₂ MonoidalCategory.tensorHom ?_ ?_
    · rw [Category.id_comp, Iso.inv_hom_id]
    · rw [show sheafification.map ((toPresheafOfModules X).map e.hom) ≫
            G'.sheafificationCounitIso.hom = G.sheafificationCounitIso.hom ≫ e.hom from
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.naturality e.hom,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- `hwμ`: the sheaf-level whisker is the descended presheaf whisker conjugated by `μ`
  -- (analogue of `hβ`, via `μ_natural_right`).
  have hwμ : sheafification.obj ((toPresheafOfModules X).obj F) ◁
        sheafification.map ((toPresheafOfModules X).map e.hom)
      = (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X)
          (localizationUnitIso X) ((toPresheafOfModules X).obj F)
          ((toPresheafOfModules X).obj G)).hom ≫
        sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).map e.hom)) ≫
        (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X)
          (localizationUnitIso X) ((toPresheafOfModules X).obj F)
          ((toPresheafOfModules X).obj G')).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 (Localization.Monoidal.μ_natural_right (sheafificationMon X)
      (sheafificationW X) (localizationUnitIso X) ((toPresheafOfModules X).obj F)
      ((toPresheafOfModules X).map e.hom))
  dsimp only [tensorObjWhiskerLeftIso, tensorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom, MonoidalCategory.whiskerLeftIso_hom]
  rw [← hwnat, hwμ]
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_tensorHom_id, Category.id_comp]
  congr 1
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg _ (Category.assoc _ _ _)).trans ?_
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bridge: the hand-built right-whiskering `tensorObjWhiskerRightIso e G` is the canonical right
whiskering `e ▷ G` transported along the bridge `tensorObjIso`.  Mirror of `tensorBraiding_eq`,
using `μ`-naturality in the left variable (`Localization.Monoidal.μ_natural_left`). -/
private lemma tensorObjWhiskerRightIso_eq {F F' : X.Modules} (e : F ≅ F') (G : X.Modules) :
    tensorObjWhiskerRightIso e G
      = (tensorObjIso F G).symm ≪≫ MonoidalCategory.whiskerRightIso e G ≪≫ tensorObjIso F' G := by
  apply Iso.ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom, Iso.eq_inv_comp]
  have hwnat : (F.sheafificationCounitIso.inv ⊗ₘ G.sheafificationCounitIso.inv) ≫
        (sheafification.map ((toPresheafOfModules X).map e.hom) ▷
          sheafification.obj ((toPresheafOfModules X).obj G)) ≫
        (F'.sheafificationCounitIso.hom ⊗ₘ G.sheafificationCounitIso.hom)
      = e.hom ▷ G := by
    rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    refine congrArg₂ MonoidalCategory.tensorHom ?_ ?_
    · rw [show sheafification.map ((toPresheafOfModules X).map e.hom) ≫
            F'.sheafificationCounitIso.hom = F.sheafificationCounitIso.hom ≫ e.hom from
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).counit.naturality e.hom,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · rw [Category.id_comp, Iso.inv_hom_id]
  have hwμ : sheafification.map ((toPresheafOfModules X).map e.hom) ▷
        sheafification.obj ((toPresheafOfModules X).obj G)
      = (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X)
          (localizationUnitIso X) ((toPresheafOfModules X).obj F)
          ((toPresheafOfModules X).obj G)).hom ≫
        sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G)) ≫
        (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X)
          (localizationUnitIso X) ((toPresheafOfModules X).obj F')
          ((toPresheafOfModules X).obj G)).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).2 (Localization.Monoidal.μ_natural_left (sheafificationMon X)
      (sheafificationW X) (localizationUnitIso X) ((toPresheafOfModules X).map e.hom)
      ((toPresheafOfModules X).obj G))
  dsimp only [tensorObjWhiskerRightIso, tensorObjIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom, MonoidalCategory.whiskerRightIso_hom]
  rw [← hwnat, hwμ]
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_tensorHom_id, Category.id_comp]
  congr 1
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg _ (Category.assoc _ _ _)).trans ?_
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Functoriality of the hand-built right-whiskering under iso-composition: route (b) of
`analogies/whisker-synonym.md` (iter-020, lean_run_code-VERIFIED).  Proved by routing through the
canonical bridge `tensorObjWhiskerRightIso_eq` (NOT by re-deriving on the `MonoidalPresheaf X` synonym
side, which re-opens the synonym diamond), so the residual is uniformly `X.Modules`-comp and
`comp_whiskerRight` fires under `apply Iso.ext; simp`. -/
private lemma tensorObjWhiskerRightIso_trans {F F' F'' : X.Modules}
    (e : F ≅ F') (f : F' ≅ F'') (G : X.Modules) :
    tensorObjWhiskerRightIso (e ≪≫ f) G
      = tensorObjWhiskerRightIso e G ≪≫ tensorObjWhiskerRightIso f G := by
  rw [tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq]
  apply Iso.ext; simp

/-- Trailing-composed form of `tensorObjWhiskerRightIso_trans`: collapses two adjacent right
whiskerings occurring as a prefix of a longer `≪≫` chain.  Used in the `tensorPowAdd_assoc` succ
case to fold the doubled `ih` leg back into a single right-whisker. -/
private lemma tensorObjWhiskerRightIso_trans_assoc {F F' F'' : X.Modules}
    (e : F ≅ F') (f : F' ≅ F'') (G : X.Modules) {W : X.Modules}
    (r : tensorObj F'' G ≅ W) :
    tensorObjWhiskerRightIso e G ≪≫ tensorObjWhiskerRightIso f G ≪≫ r
      = tensorObjWhiskerRightIso (e ≪≫ f) G ≪≫ r := by
  rw [tensorObjWhiskerRightIso_trans, Iso.trans_assoc]

/-- Reflexivity of the hand-built right-whiskering: `tensorObjWhiskerRightIso (Iso.refl F) G` is the
identity iso.  Route (b), via the canonical bridge. -/
private lemma tensorObjWhiskerRightIso_refl (F G : X.Modules) :
    tensorObjWhiskerRightIso (Iso.refl F) G = Iso.refl _ := by
  rw [tensorObjWhiskerRightIso_eq]; apply Iso.ext; simp

/-- Right-whiskering a reindexing `eqToIso` is the corresponding object-level `eqToIso`.  Lets the
reindexers straddling the inductive seam (`tensorPowAdd_succ` ↔ `tensorPowAdd_assoc_succ_reindex`)
merge and cancel so the `(ii-a)` transposition lemma can fire on the bare double-whisker. -/
private lemma tensorObjWhiskerRightIso_eqToIso {F F' : X.Modules} (h : F = F') (G : X.Modules) :
    tensorObjWhiskerRightIso (eqToIso h) G = eqToIso (congrArg (fun Z => tensorObj Z G) h) := by
  subst h; simp [tensorObjWhiskerRightIso_refl]

/-- An `eqToIso` between an object and itself is the identity (proof irrelevance).  Used to collapse
the seam reindexer of the `tensorPowAdd_assoc` succ case once the two inverse reindexers merge. -/
private lemma eqToIso_self {Y : X.Modules} (h : Y = Y) : eqToIso h = Iso.refl Y := by
  simp

/-- Functoriality of the hand-built left-whiskering under iso-composition: route (b), via the
canonical bridge `tensorObjWhiskerLeftIso_eq`.  Mirror of `tensorObjWhiskerRightIso_trans`. -/
private lemma tensorObjWhiskerLeftIso_trans (F : X.Modules) {G G' G'' : X.Modules}
    (e : G ≅ G') (f : G' ≅ G'') :
    tensorObjWhiskerLeftIso F (e ≪≫ f)
      = tensorObjWhiskerLeftIso F e ≪≫ tensorObjWhiskerLeftIso F f := by
  rw [tensorObjWhiskerLeftIso_eq, tensorObjWhiskerLeftIso_eq, tensorObjWhiskerLeftIso_eq]
  apply Iso.ext; simp

/-- Reflexivity of the hand-built left-whiskering.  Route (b), via the canonical bridge. -/
private lemma tensorObjWhiskerLeftIso_refl (F G : X.Modules) :
    tensorObjWhiskerLeftIso F (Iso.refl G) = Iso.refl _ := by
  rw [tensorObjWhiskerLeftIso_eq]; apply Iso.ext; simp

/-- The tensor-power comparison isomorphism `L^⊗m ⊗ L^⊗m' ≅ L^⊗(m+m')` for the sheaf tensor
power `tensorPow` (`lem:sheafTensorPow_add`, [Stacks, Tag 01CU]).

Defined by recursion on the SECOND index `m'` (iter-023 root-cause refactor — the canonical
`pow_add` orientation), which is **braiding-free**: both `tensorPow` and `Nat.add` grow on the
right, so the freshly-added `L` stays at the right edge of source and target with no `tensorBraiding`
and no `eqToIso` reindexer.  Base `m' = 0` (`m + 0 = m`, `rfl`) is the right unitor
`tensorObjRightUnitor`; succ `m' = c+1` (`m + (c+1) = (m+c)+1`, `rfl`) is the inverse associator
`tensorObjAssoc.symm` followed by the inductive comparison `μ_{m,c}` right-whiskered by `L`.
The earlier first-index recursion forced a braiding (a definitional artifact); recursing on the
second index eliminates it, making `tensorPowAdd_assoc` a pure braiding-free pentagon. -/
noncomputable def tensorPowAdd (L : X.Modules) (m m' : ℕ) :
    tensorObj (tensorPow L m) (tensorPow L m') ≅ tensorPow L (m + m') :=
  match m' with
  | 0 =>
    -- Base case `m + 0 = m` (`rfl`): the right unitor on `L^{⊗m}`.
    tensorObjRightUnitor (tensorPow L m)
  | (c + 1) =>
    -- Succ case `m + (c+1) = (m+c)+1` (`rfl`): inverse associator (regroup the freshly-added `L`
    -- to the right edge) then the inductive comparison `μ_{m,c}` whiskered by `L` on the right.
    -- NO braiding, NO `eqToIso`: both `tensorPow` and `Nat.add` grow on the right, so recursing on
    -- the SECOND index keeps the new `L` at the right edge of source and target (canonical
    -- `pow_add` orientation, `Mathlib.Algebra.Group.Defs`).
    (tensorObjAssoc (tensorPow L m) (tensorPow L c) L).symm ≪≫
      tensorObjWhiskerRightIso (tensorPowAdd L m c) L

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
  ((toPresheafOfModules X ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj
    (Opposite.op ⊤)).mapIso (eqToIso (congrArg (tensorPow L) h))).toLinearEquiv

/-- The transport along the reflexive equality `rfl : i = i` equals the identity automorphism
(`lem:sectionsCast_refl`).  Section-level analogue of `TensorPower.cast_refl`. -/
@[simp] lemma sectionsCast_refl (L : X.Modules) (i : ℕ) :
    sectionsCast L (rfl : i = i) = LinearEquiv.refl _ (sectionDeg L i) := by
  ext x
  rfl

/-- Cast-mediated equality in the graded sigma type: if `a.fst = b.fst` and the section-component
transport maps `a.snd` to `b.snd`, then `a = b` as dependent pairs (`lem:gradedMonoid_eq_of_cast`).
Section-level analogue of `gradedMonoid_eq_of_cast` from `TensorPower.Basic` (line 123 there). -/
lemma gradedMonoid_eq_of_cast (L : X.Modules) {a b : GradedMonoid (sectionDeg L)}
    (h : a.1 = b.1) (h2 : sectionsCast L h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain rfl : i = j := h
  simp only [sectionsCast_refl, LinearEquiv.refl_apply] at h2
  subst h2
  rfl

/-- Degreewise graded multiplication on section components:
`sectionDeg L i × sectionDeg L j → sectionDeg L (i+j)`, defined as the composition
`Γ(μ_{i,j}) ∘ sectionsMul` applied to `a ⊗ₜ b`.  Required for the coherence lemma signatures. -/
noncomputable instance (L : X.Modules) : GradedMonoid.GMul (sectionDeg L) where
  mul {i j} (a : sectionDeg L i) (b : sectionDeg L j) :=
    ((tensorPowAdd L i j).hom.val.app (Opposite.op ⊤)).hom
      ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b))

/-- Graded unit in degree 0: the image of `1 ∈ Γ(X,𝒪_X)` in `sectionDeg L 0 = Γ(X, L^{⊗0})`
via the canonical `Γ𝒪`-module isomorphism.  Required for the coherence lemma signatures. -/
noncomputable instance (L : X.Modules) : GradedMonoid.GOne (sectionDeg L) where
  one := (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))

/-- Definitional unfolding of the graded multiplication, as a clean rewrite handle for the
coherence proofs: `a · b = Γ(μ_{i,j})(sectionsMul (a ⊗ₜ b))`. -/
private lemma gMul_mul_apply (L : X.Modules) {i j : ℕ}
    (a : sectionDeg L i) (b : sectionDeg L j) :
    (GradedMonoid.GMul.mul a b : sectionDeg L (i + j))
      = ((tensorPowAdd L i j).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
            (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)) :=
  rfl

/-- Definitional unfolding of the graded unit. -/
private lemma gOne_one_eq (L : X.Modules) :
    (GradedMonoid.GOne.one : sectionDeg L 0)
      = (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))) :=
  rfl

/-- Definitional unfolding of the section transport applied to an element. -/
private lemma sectionsCast_apply (L : X.Modules) {i j : ℕ} (h : i = j) (y : sectionDeg L i) :
    sectionsCast L h y
      = ((eqToIso (congrArg (tensorPow L) h)).hom.val.app (Opposite.op ⊤)).hom y :=
  rfl

/-- Two index transports along inverse equalities cancel. -/
private lemma sectionsCast_sectionsCast (L : X.Modules) {i j : ℕ} (h₁ : i = j) (h₂ : j = i)
    (x : sectionDeg L i) : sectionsCast L h₂ (sectionsCast L h₁ x) = x := by
  obtain rfl := h₁
  rw [Subsingleton.elim h₂ rfl]
  simp only [sectionsCast_refl, LinearEquiv.refl_apply]

/-- The transport along a reflexive index equality is the identity (on elements). -/
private lemma sectionsCast_self (L : X.Modules) {i : ℕ} (h : i = i) (x : sectionDeg L i) :
    sectionsCast L h x = x := by
  rw [Subsingleton.elim h rfl, sectionsCast_refl, LinearEquiv.refl_apply]

/-- The core left-unit identity at the presheaf top open: the left unitor of the sheaf tensor
product post-composed with the section multiplication `sectionsMul (unit) G` sends `1 ⊗ₜ a` to `a`.
This is the lax-monoidal unit law, proved by riding the sheafification unit `η` through the
presheaf left unitor (strict-monoidal at the top open) via `η`-naturality, the `ModuleCat`
left-unitor formula `r ⊗ₜ m ↦ r • m`, and the adjunction right-triangle identity. -/
private lemma tensorObjUnitIso_hom_sectionsMul (G : X.Modules)
    (a : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorObjUnitIso G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (unitModule X) G).hom
          ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a)) = a := by
  -- The presheaf-morphism identity `η ≫ Γ(unitIso) = λ_` (left unitor), via η-naturality
  -- and the adjunction right-triangle identity, then evaluate at the top open on `1 ⊗ₜ a`.
  have hmor :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G))
        ≫ (tensorObjUnitIso G).hom.val
      = (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom := by
    have e1 : (tensorObjUnitIso G).hom.val
        = (SheafOfModules.forget X.ringCatSheaf
              ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
              (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj G)).hom
            ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app G) :=
      rfl
    rw [e1, Functor.map_comp]
    erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit_naturality_assoc,
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).right_triangle_components,
      Category.comp_id]
  -- the left unitor of `ModuleCat` sends `1 ⊗ₜ a ↦ 1 • a = a`
  have hlam : ((MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G)).hom.app (Opposite.op ⊤)).hom
        ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a) = a := by
    change (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))) • a = a
    rw [one_smul]
  -- evaluate the morphism identity `hmor` at the top open on `1 ⊗ₜ a`
  have key := congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj (unitModule X)) ((toPresheafOfModules X).obj G)
        ⟶ (toPresheafOfModules X).obj G) =>
      (φ.app (Opposite.op ⊤)).hom
        ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a)) hmor
  exact key.trans hlam

/-- The core right-unit identity at the presheaf top open: the right unitor of the sheaf tensor
product post-composed with the section multiplication `sectionsMul G (unit)` sends `a ⊗ₜ 1` to `a`.
Mirror of `tensorObjUnitIso_hom_sectionsMul`, via the same η-naturality + right-triangle argument
and the `ModuleCat` right-unitor formula `m ⊗ₜ r ↦ r • m`. -/
private lemma tensorObjRightUnitor_hom_sectionsMul (G : X.Modules)
    (a : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorObjRightUnitor G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul G (unitModule X)).hom
          (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
            (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))))) = a := by
  have hmor :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj (unitModule X)))
        ≫ (tensorObjRightUnitor G).hom.val
      = (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom := by
    have e1 : (tensorObjRightUnitor G).hom.val
        = (SheafOfModules.forget X.ringCatSheaf
              ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
              (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj G)).hom
            ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app G) :=
      rfl
    rw [e1, Functor.map_comp]
    erw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit_naturality_assoc,
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).right_triangle_components,
      Category.comp_id]
  have hrho : ((MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj G)).hom.app (Opposite.op ⊤)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))) = a := by
    change (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))) • a = a
    rw [one_smul]
  have key := congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj (unitModule X))
        ⟶ (toPresheafOfModules X).obj G) =>
      (φ.app (Opposite.op ⊤)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))))) hmor
  exact key.trans hrho

/-- Section-level naturality of the braiding (`lem:tensorBraiding_hom_sectionsMul`): applying global
sections of the braiding `tensorBraiding F G` to the section product `sectionsMul F G (a ⊗ₜ b)`
returns the swapped section product `sectionsMul G F (b ⊗ₜ a)`.  Proved by `η`-naturality of the
sheafification unit (the braiding is pure sheafification-functoriality of the presheaf braiding) and
the `ModuleCat` braiding formula `a ⊗ₜ b ↦ b ⊗ₜ a` at the top open.  Section-level partner of the
commutativity constraint `tensorPowAdd_comm`. -/
private lemma tensorBraiding_hom_sectionsMul (F G : X.Modules)
    (a : ↥(F.val.obj (Opposite.op ⊤))) (b : ↥(G.val.obj (Opposite.op ⊤))) :
    ((tensorBraiding F G).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul F G).hom
          (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b))
      = (sectionsMul G F).hom
          (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a) := by
  -- The presheaf-morphism identity `η_{F⊗G} ≫ Γ(braiding)ᵥ = β_p ≫ η_{G⊗F}`, by η-naturality of
  -- the sheafification unit applied to the presheaf braiding morphism.
  have hmor :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))
        ≫ (tensorBraiding F G).hom.val
      = (BraidedCategory.braiding (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom
        ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)) := by
    have e1 : (tensorBraiding F G).hom.val
        = (SheafOfModules.forget X.ringCatSheaf
              ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
              (BraidedCategory.braiding (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom) :=
      rfl
    rw [e1]
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom).symm
  -- The presheaf braiding at the top open is the `ModuleCat` braiding `a ⊗ₜ b ↦ b ⊗ₜ a`.
  have hβ : ((BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)).hom.app
          (Opposite.op ⊤)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
      = (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a :
          ↥(MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G) ((toPresheafOfModules X).obj F)
              |>.obj (Opposite.op ⊤))) :=
    rfl
  -- evaluate the morphism identity `hmor` at the top open on `a ⊗ₜ b`
  have key := congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)
        ⟶ (tensorObj G F).val) =>
      (φ.app (Opposite.op ⊤)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)) hmor
  exact key.trans (congrArg (sectionsMul G F).hom hβ)

/-- **Presheaf associator at the top open** (`lem:presheafAssociator_top_apply`): the associator
`α^p_{A,B,C}` of the presheaf monoidal structure (`PresheafOfModules.monoidalCategory`),
evaluated at the top open, is the `ModuleCat` associator on module sections.  On elementary
tensors it is the reassociation `(a ⊗ₜ b) ⊗ₜ c ↦ a ⊗ₜ (b ⊗ₜ c)` (apply
`ModuleCat.MonoidalCategory.associator_hom_apply` to the RHS of this lemma).  Stated at the
*morphism* level — the form the telescoping of `tensorObjAssoc_eta_factor` consumes — because the
element-level statement runs into the `CommRing`-behind-`forget₂` instance diamond (a bare
`⊗ₜ[…]` annotation triggers eager `CommSemiring`/`Module` synthesis on the `RingCat` carrier,
which fails; the instances are only found when an enclosing `.hom` application drives the expected
type).  Proved by `rfl`: the presheaf monoidal structure is defined objectwise, so its associator
at any open is *definitionally* the `ModuleCat` associator of the sections
(`PresheafOfModules.associator_hom_app`, itself a `@[simp] rfl` lemma). -/
private lemma presheafAssociator_top_apply (A B C : MonoidalPresheaf X) :
    (MonoidalCategory.associator (C := MonoidalPresheaf X) A B C).hom.app (Opposite.op ⊤)
      = (MonoidalCategory.associator (C := ModuleCat (X.sheaf.obj.obj (Opposite.op ⊤)))
          (A.obj (Opposite.op ⊤)) (B.obj (Opposite.op ⊤)) (C.obj (Opposite.op ⊤))).hom :=
  rfl

/-- **Right-whiskered-unit leg of the iterated section product** (`lem:sectionsMul_whiskerRight_unit`),
element form.  The composite `(η_{A⊗ₚB} ▷ C) ≫ η_{(A⊗B)⊗ₚC}` of presheaf-of-modules morphisms,
evaluated at the top open on `(a ⊗ₜ b) ⊗ₜ c`, recovers the iterated section product over the
already-sheafified first factor.  Proved by the objectwise `whiskerRight` formula of the presheaf
monoidal structure (`PresheafOfModules.Monoidal.whiskerRight_app` + ModuleCat `whiskerRight_apply`,
both `rfl`) and the definitional identity `sectionsMul = η.app (op ⊤)`. -/
private lemma sectionsMul_whiskerRight_unit (A B C : X.Modules)
    (a : ↥(A.val.obj (Opposite.op ⊤))) (b : ↥(B.val.obj (Opposite.op ⊤)))
    (c : ↥(C.val.obj (Opposite.op ⊤))) :
    ((MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj (tensorObj A B))
            ((toPresheafOfModules X).obj C))).app (Opposite.op ⊤)).hom
        ((a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c)
      = (sectionsMul (tensorObj A B) C).hom
          ((sectionsMul A B).hom
              (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c) := by
  rfl

/-- **Left-whiskered-unit leg of the iterated section product** (`lem:sectionsMul_whiskerLeft_unit`),
element form.  The composite `(A ◁ η_{B⊗ₚC}) ≫ η_{A⊗ₚ(B⊗C)}` of presheaf-of-modules morphisms,
evaluated at the top open on `a ⊗ₜ (b ⊗ₜ c)`, recovers the iterated section product over the
already-sheafified second factor.  Left-whiskered analogue of `sectionsMul_whiskerRight_unit`,
via `PresheafOfModules.Monoidal.whiskerLeft_app` + ModuleCat `whiskerLeft_apply`. -/
private lemma sectionsMul_whiskerLeft_unit (A B C : X.Modules)
    (a : ↥(A.val.obj (Opposite.op ⊤))) (b : ↥(B.val.obj (Opposite.op ⊤)))
    (c : ↥(C.val.obj (Opposite.op ⊤))) :
    ((MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            ((toPresheafOfModules X).obj (tensorObj B C)))).app (Opposite.op ⊤)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c))
      = (sectionsMul A (tensorObj B C)).hom
          (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
            (sectionsMul B C).hom
              (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c)) := by
  rfl

/-- **Triangle identity**: sheafifying the localization unit at `P` gives the inverse of the
sheafification counit isomorphism at `sheafification.obj P`.  (`L.map η_P = ε_{LP}⁻¹`, the left
triangle of the reflective sheafification adjunction.) -/
private lemma sheafification_map_unit_eq (P : MonoidalPresheaf X) :
    sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
      = (sheafificationCounitIso (sheafification.obj P)).inv := by
  have h : sheafification.map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P) ≫
      (sheafificationCounitIso (sheafification.obj P)).hom = 𝟙 _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P
  simp only [Functor.id_obj] at h
  exact (Iso.comp_hom_eq_id _).mp h

/-- **`n`/`eF` round-trip prefix is the identity** (head step of the associator coherence below).
The leading `eF.inv ▷ C' ≫ n.hom ≫ n.inv ≫ eF.hom ▷ C'` block (the `μ`-pair `n` inside the counit
`eF` whiskering) collapses to the identity.  Small standalone goal so it has a cheap fresh budget;
applied to the main goal by `congrArg` (no simp/`kabstract` over the full coherence term). -/
private lemma neF_prefix_id {M : Type*} [Category M] [MonoidalCategory M]
    {F P C' G K : M} (eF : F ≅ P) (n : F ⊗ C' ≅ G) (k : P ⊗ C' ⟶ K) :
    eF.inv ▷ C' ≫ n.hom ≫ n.inv ≫ eF.hom ▷ C' ≫ k = k := by
  simp only [Iso.hom_inv_id_assoc, MonoidalCategory.inv_hom_whiskerRight_assoc]

/-- **Counit round-trip tail is the identity** (tail step of the associator coherence below).
After the canonical associator is pushed to the front by naturality, the residual block of counit
`hom`/`inv` pairs (outer `eA`, then middle/right `eB`/`eC`) is an endomorphism of `A' ⊗ B' ⊗ C'`
equal to the identity (interchange law + iso cancellation).  Split out as its own declaration so its
`whisker_exchange`/`whiskerLeft_comp` simp normalisation gets a fresh heartbeat budget, and applied to
the main goal by `congrArg` (no kabstract). -/
private lemma counit_assoc_tail_id {M : Type*} [Category M] [MonoidalCategory M]
    {A A' B B' C C' Z : M} (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C)
    (g : A' ⊗ B' ⊗ C' ⟶ Z) :
    eA.hom ▷ (B' ⊗ C') ≫ A ◁ eB.hom ▷ C' ≫ A ◁ B ◁ eC.hom ≫ eA.inv ▷ (B ⊗ C) ≫
        A' ◁ eB.inv ▷ C ≫ A' ◁ B' ◁ eC.inv ≫ g = g := by
  simp only [MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **Tail of the associator coherence** — the post-naturality goal of
`tensorObjAssoc_associator_counit_coherence` (after the `(α_ A' B' C')` has been pushed to the front).
Closed by `congrArg` on the common `m1 ≫ m3 ▷ C' ≫ α` prefix using `counit_assoc_tail_id`.  Stated as
its own declaration so the main coherence lemma can discharge its post-`simp` goal by a single
syntactic `exact` (cheap), keeping the expensive `congrArg`/`counit_assoc_tail_id` `isDefEq` in this
lemma's own heartbeat budget. -/
private lemma tensorObjAssoc_associator_counit_coherence_tail
    {M : Type*} [Category M] [MonoidalCategory M]
    {A B C A' B' C' P Q R D E : M}
    (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C) (eR : R ≅ Q)
    (m1 : D ⟶ P ⊗ C') (m3 : P ⟶ A' ⊗ B') (m4 : B' ⊗ C' ⟶ Q) (m5 : A' ⊗ R ⟶ E) :
    m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ eA.hom ▷ (B' ⊗ C') ≫ A ◁ eB.hom ▷ C' ≫
        A ◁ B ◁ eC.hom ≫ eA.inv ▷ (B ⊗ C) ≫ A' ◁ eB.inv ▷ C ≫ A' ◁ B' ◁ eC.inv ≫
        A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5
      = m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5 :=
  congrArg (m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ ·)
    (counit_assoc_tail_id eA eB eC (A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5))

/-- Stage 2 of the coherence: after the interchange-law reordering (`whisker_exchange`), push the
canonical associator to the front (associator naturality) and hand off to the tail lemma.  A separate
declaration so its single `simp` + handoff `exact` fit one heartbeat budget. -/
private lemma tensorObjAssoc_associator_counit_coherence_stage2
    {M : Type*} [Category M] [MonoidalCategory M]
    {A B C A' B' C' P Q R D E : M}
    (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C) (eR : R ≅ Q)
    (m1 : D ⟶ P ⊗ C') (m3 : P ⟶ A' ⊗ B') (m4 : B' ⊗ C' ⟶ Q) (m5 : A' ⊗ R ⟶ E) :
    m1 ≫ m3 ▷ C' ≫ eA.hom ▷ B' ▷ C' ≫ (A ◁ eB.hom) ▷ C' ≫ (A ⊗ B) ◁ eC.hom ≫
        (α_ A B C).hom ≫ eA.inv ▷ (B ⊗ C) ≫ A' ◁ eB.inv ▷ C ≫ A' ◁ B' ◁ eC.inv ≫
        A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5
      = m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5 := by
  simp only [MonoidalCategory.associator_naturality_right_assoc,
    MonoidalCategory.associator_naturality_middle_assoc,
    MonoidalCategory.associator_naturality_left_assoc]
  exact tensorObjAssoc_associator_counit_coherence_tail eA eB eC eR m1 m3 m4 m5

/-- Stage 1 of the coherence: after the `n`/`eF` cancellation + whisker expansion (done by the caller),
reorder the independent whiskerings (`whisker_exchange`) and hand off to stage 2.  A separate
declaration so its single `simp` + handoff `exact` fit one heartbeat budget. -/
private lemma tensorObjAssoc_associator_counit_coherence_stage1
    {M : Type*} [Category M] [MonoidalCategory M]
    {A B C A' B' C' P Q R D E : M}
    (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C) (eR : R ≅ Q)
    (m1 : D ⟶ P ⊗ C') (m3 : P ⟶ A' ⊗ B') (m4 : B' ⊗ C' ⟶ Q) (m5 : A' ⊗ R ⟶ E) :
    m1 ≫ P ◁ eC.hom ≫ m3 ▷ C ≫ eA.hom ▷ B' ▷ C ≫ (A ◁ eB.hom) ▷ C ≫ (α_ A B C).hom ≫
        A ◁ eB.inv ▷ C ≫ A ◁ B' ◁ eC.inv ≫ A ◁ m4 ≫ eA.inv ▷ Q ≫ A' ◁ eR.inv ≫ m5
      = m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5 := by
  simp only [MonoidalCategory.whisker_exchange_assoc]
  exact tensorObjAssoc_associator_counit_coherence_stage2 eA eB eC eR m1 m3 m4 m5

/-- Stage 0 of the coherence: after the `n`/`eF` cancellation (done by the caller), expand the two
whiskered composites (`comp_whiskerRight`/`whiskerLeft_comp`) and hand off to stage 1.  A separate
declaration so its `simp` expansion gets a fresh heartbeat budget. -/
private lemma tensorObjAssoc_associator_counit_coherence_stage0
    {M : Type*} [Category M] [MonoidalCategory M]
    {A B C A' B' C' P Q R D E : M}
    (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C) (eR : R ≅ Q)
    (m1 : D ⟶ P ⊗ C') (m3 : P ⟶ A' ⊗ B') (m4 : B' ⊗ C' ⟶ Q) (m5 : A' ⊗ R ⟶ E) :
    m1 ≫ P ◁ eC.hom ≫ (m3 ≫ eA.hom ▷ B' ≫ A ◁ eB.hom) ▷ C ≫ (α_ A B C).hom ≫
        A ◁ (eB.inv ▷ C ≫ B' ◁ eC.inv ≫ m4) ≫ eA.inv ▷ Q ≫ A' ◁ eR.inv ≫ m5
      = m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ eR.inv ≫ m5 := by
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  exact tensorObjAssoc_associator_counit_coherence_stage1 eA eB eC eR m1 m3 m4 m5

-- The single full-term `isDefEq` of the assembled term-mode proof needs ~600k–800k heartbeats (the
-- abstract coherence term is large); raised to the file's established 800000 budget (cf. the
-- `set_option maxHeartbeats 800000` at the top of this file).  NOT the forbidden 1e6, and NOT papering
-- over a missing proof — the proof is complete; this is the genuine elaboration cost of the big term.
set_option maxHeartbeats 800000 in
/-- **Abstract associator-naturality coherence** (mechanical core of `★ tensorObjAssoc_eta_factor_sheaf`).
Stated over a *generic* monoidal category `M` so that all `≫`/`▷`/`◁`/`α_` resolve to a single uniform
category instance (no `LocalizedMonoidal`/`X.Modules` comp-instance diamond), making the standard
naturality/cancellation simp set fire.  Plugged into `★` by `exact` (the instance diamond is `rfl`-defeq,
so `exact`'s `isDefEq` bridges it).  The two `μ`-pair (`n`) and counit (`eF`) cancellations plus the
associator naturality conjugated by the counit isos `eA`/`eB`/`eC` are exactly the residual `★` goal. -/
private lemma tensorObjAssoc_associator_counit_coherence
    {M : Type*} [Category M] [MonoidalCategory M]
    {A B C A' B' C' P Q F G R D E : M}
    (eA : A' ≅ A) (eB : B' ≅ B) (eC : C' ≅ C) (eF : F ≅ P) (eR : R ≅ Q)
    (n : F ⊗ C' ≅ G)
    (m1 : D ⟶ P ⊗ C') (m3 : P ⟶ A' ⊗ B') (m4 : B' ⊗ C' ⟶ Q)
    (m5 : A' ⊗ R ⟶ E) (m6 : Q ⟶ R) (hm6 : m6 = eR.inv) :
    m1 ≫ eF.inv ▷ C' ≫ n.hom ≫ n.inv ≫ eF.hom ▷ C' ≫ P ◁ eC.hom
      ≫ (m3 ≫ eA.hom ▷ B' ≫ A ◁ eB.hom) ▷ C ≫ (α_ A B C).hom
      ≫ A ◁ (eB.inv ▷ C ≫ B' ◁ eC.inv ≫ m4) ≫ eA.inv ▷ Q ≫ A' ◁ eR.inv ≫ m5
    = m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ m6 ≫ m5 := by
  -- Pure term-mode chain (NO `simp`/`rw`/`subst` over this full coherence term — each such scan or
  -- `kabstract` alone exceeds the 200000-heartbeat budget).  Cancel the leading `n`/`eF` round-trip by
  -- `congrArg`+`neF_prefix_id`, hand the compact goal to `stage0` (which expands + reorders + applies
  -- associator naturality + the tail cancellation, each in its own fresh budget), then re-identify
  -- `eR.inv` back to `m6` by `congrArg`+`hm6`.  The only full-term operation here is the final
  -- `exact`'s structural `isDefEq` (the abstract term is large ⇒ the 800000-heartbeat budget above).
  exact ((congrArg (m1 ≫ ·) (neF_prefix_id eF n _)).trans
      (tensorObjAssoc_associator_counit_coherence_stage0 eA eB eC eR m1 m3 m4 m5)).trans
    (congrArg (fun t => m1 ≫ m3 ▷ C' ≫ (α_ A' B' C').hom ≫ A' ◁ m4 ≫ A' ◁ t ≫ m5) hm6.symm)

-- The final `exact tensorObjAssoc_associator_counit_coherence (M := LocalizedMonoidal …) …` discharges
-- a large concrete monoidal coherence; its (terminating, head-aligned) `isDefEq` recurses deeper than
-- the default `maxRecDepth = 512`.  Raised to 4000 (a stack-depth bound, NOT the forbidden heartbeat
-- bump — the elaboration is fast once the depth suffices; `lean_multi_attempt` closes it instantly).
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Sheaf-level factorization of the associator** (the `X.Modules`-internal core of
`lem:tensorObjAssoc_eta_factor`).  As morphisms of *sheaves* of modules, the sheafified
right-whiskered unit composed with `tensorObjAssoc` equals the sheafified presheaf associator
composed with the sheafified left-whiskered unit:
`L(η_{A⊗ₚB} ▷ C) ≫ tensorObjAssoc = L(α^p) ≫ L(A ◁ η_{B⊗ₚC})`.
This is the bridge-telescoping identity entirely inside the inherited (localized) monoidal structure
on `X.Modules`; the presheaf-morphism statement `tensorObjAssoc_eta_factor` follows from it by
`η`-naturality (the unit of the sheafification adjunction). -/
private lemma tensorObjAssoc_eta_factor_sheaf (A B C : X.Modules) :
    sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
        ((toPresheafOfModules X).obj C)) ≫ (tensorObjAssoc A B C).hom
      = sheafification.map (MonoidalCategory.associator (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
          ((toPresheafOfModules X).obj C)).hom ≫
        sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)))) := by
  -- iter-014 DECORATION-ERASE: state the μ-naturality splits in BARE `toPresheafOfModules` form and
  -- prove them by pure `exact`/term proofs (the `restrictScalars (𝟙)` decoration on `η`'s codomain is
  -- `rfl`-equal to the bare form, so `exact` bridges it during elaboration — see analogies/restrict-
  -- decoration.md).  Once the splits are stated bare, `rw` substitutes them into the goal with bare
  -- `μ` indices, so the adjacent `μ`/`tensorObjIso` pairs cancel positionally.
  -- Split the right-whiskered unit on the LHS (μ-naturality, left variable).
  have hηL :
      sheafification.map (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C))
        = (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
              ((toPresheafOfModules X).obj C)).inv ≫
          (sheafification.map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                  ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))) ▷
            sheafification.obj ((toPresheafOfModules X).obj C)) ≫
          (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
            ((toPresheafOfModules X).obj (tensorObj A B)) ((toPresheafOfModules X).obj C)).hom :=
    ((Iso.inv_comp_eq _).2 (Localization.Monoidal.μ_natural_left (sheafificationMon X)
      (sheafificationW X) (localizationUnitIso X)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
      ((toPresheafOfModules X).obj C))).symm
  -- Split the left-whiskered unit on the RHS (μ-naturality, right variable).
  have hηR :
      sheafification.map (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))))
        = (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
              ((toPresheafOfModules X).obj A)
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))).inv ≫
          (sheafification.obj ((toPresheafOfModules X).obj A) ◁
            sheafification.map
              ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                  ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)))) ≫
          (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj (tensorObj B C))).hom :=
    ((Iso.inv_comp_eq _).2 (Localization.Monoidal.μ_natural_right (sheafificationMon X)
      (sheafificationW X) (localizationUnitIso X) ((toPresheafOfModules X).obj A)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))))).symm
  -- The sheafified presheaf associator, conjugated into the inherited canonical associator by μ.
  have hα :
      sheafification.map (MonoidalCategory.associator (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
          ((toPresheafOfModules X).obj C)).hom
        = (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
              ((toPresheafOfModules X).obj C)).inv ≫
          ((Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)).inv ▷
            (Localization.Monoidal.toMonoidalCategory (sheafificationMon X) (sheafificationW X)
                (localizationUnitIso X)).obj ((toPresheafOfModules X).obj C)) ≫
          (α_ ((Localization.Monoidal.toMonoidalCategory (sheafificationMon X) (sheafificationW X)
                (localizationUnitIso X)).obj ((toPresheafOfModules X).obj A))
              ((Localization.Monoidal.toMonoidalCategory (sheafificationMon X) (sheafificationW X)
                (localizationUnitIso X)).obj ((toPresheafOfModules X).obj B))
              ((Localization.Monoidal.toMonoidalCategory (sheafificationMon X) (sheafificationW X)
                (localizationUnitIso X)).obj ((toPresheafOfModules X).obj C))).hom ≫
          ((Localization.Monoidal.toMonoidalCategory (sheafificationMon X) (sheafificationW X)
              (localizationUnitIso X)).obj ((toPresheafOfModules X).obj A) ◁
            (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)).hom) ≫
          (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
            ((toPresheafOfModules X).obj A)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))).hom := by
    have key := Localization.Monoidal.associator_hom_app (sheafificationMon X) (sheafificationW X)
      (localizationUnitIso X) ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
      ((toPresheafOfModules X).obj C)
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] at key
    rw [key]
    simp only [Category.assoc,
      MonoidalCategory.inv_hom_whiskerRight_assoc, MonoidalCategory.whiskerLeft_inv_hom_assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  erw [hηR]
  simp only [hηL, hα, sheafification_map_unit_eq]
  simp only [tensorObjAssoc, tensorObjIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorIso_inv,
    Category.assoc]
  -- Normalise the `(Localization.Monoidal.toMonoidalCategory …).obj` form (from `hα`/
  -- `associator_hom_app`) to the `(sheafificationMon X).obj` = `sheafification.obj` form used by the
  -- `tensorObjIso`/`sheafificationCounitIso` factors, so both sides share one object syntax.  This
  -- DOES advance the goal (verified): `toMonoidalCategory L W ε := L` and `sheafificationMon := L`.
  simp only [Localization.Monoidal.toMonoidalCategory]
  -- iter-015 COMP-BRIDGE (mathlib-analogist `comp-instance-diamond`, VALIDATED).  Normalize every `≫`
  -- UP onto the `LocalizedMonoidal`-comp head so positional `rw [Category.assoc]` fires (the two
  -- `Category` instances are `rfl`-defeq but syntactically distinct ⇒ raw `rw`/`simp [Category.assoc]`
  -- no-match, `repeat erw` heartbeat-times-out).  See analogies/comp-instance-diamond.md.
  have hc : ∀ {P Q R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R),
      @CategoryStruct.comp X.Modules
          (AlgebraicGeometry.Scheme.Modules.instCategory (X := X)).toCategoryStruct P Q R f g
        = @CategoryStruct.comp
          (LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
          _ P Q R f g := fun f g => rfl
  -- iter-015 PROGRESS (mechanism found, beyond the prior 9-iter wall): the validated comp-bridge
  -- works ONLY when keyed to the *explicit* native instance `instCategory` (the default-/`inferInstance`-
  -- elaborated `f ≫ g` resolves to the `LocalizedMonoidal`-copy and is reflexive → no-op).  With the
  -- explicit-instance `hc` in the simp set, `Category.assoc` flattens, `tensorObj` unifies the object
  -- forms (`A.tensorObj B` ↔ `sheafification.obj (a ⊗ b)`), `tensorHom_def` decomposes `⊗ₘ` into
  -- whiskerings, and the positional whisker/`Iso` cancel lemmas fire on all NON-diamond junctions.
  simp only [hc, Category.assoc, tensorObj, MonoidalCategory.tensorHom_def,
    sheafification_map_unit_eq,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.inv_hom_whiskerRight_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc, MonoidalCategory.whiskerLeft_inv_hom_assoc,
    Iso.inv_hom_id, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  -- The residual `μ`/`εc` bridge pairs and the `α`-naturality coherence straddle the
  -- `instCategory`/`LocalizedMonoidal` comp diamond; they resist positional `rw`/`simp` but each step
  -- DOES fire under the defeq-tolerant `erw` (verified: `erw [Iso.hom_inv_id_assoc]` cancels the
  -- cross-diamond `μ (A) (B⊗C)` pair, and `erw [MonoidalCategory.associator_naturality]` fires on the
  -- coherence step).  One confirmed cancellation is applied below.
  erw [Iso.hom_inv_id_assoc]
  -- iter-017 — CLOSED via the abstract, diamond-free monoidal coherence
  -- `tensorObjAssoc_associator_counit_coherence`, PINNED to the `LocalizedMonoidal` synonym instance
  -- `(M := LocalizedMonoidal …)`.  Head-alignment (NOT term-shrinking) is the lever: post-`hc` the goal
  -- carries the `LocalizedMonoidal` comp/monoidal head, so pinning `M` to the same synonym makes the
  -- generic conclusion instantiate with that head ⇒ `exact`'s top-level `isDefEq` short-circuits
  -- instead of traversing the ~1.2M-char `instCategory`/`LocalizedMonoidal` rfl-diamond.  All isos and
  -- morphisms are supplied explicitly (`eA … m6`) so no unification search runs; `hm6 = m6 = eR.inv`
  -- is `sheafification_map_unit_eq` (`L(η_P) = εc⁻¹`).  See analogies/coherence-placement.md, STEP A.
  exact tensorObjAssoc_associator_counit_coherence
    (M := LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
    A.sheafificationCounitIso B.sheafificationCounitIso C.sheafificationCounitIso
    (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))).sheafificationCounitIso
    (sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))).sheafificationCounitIso
    (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      ((toPresheafOfModules X).obj (sheafification.obj (MonoidalCategory.tensorObj
        (C := MonoidalPresheaf X) ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
      ((toPresheafOfModules X).obj C))
    (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
      ((toPresheafOfModules X).obj C)).inv
    (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)).inv
    (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)).hom
    (Localization.Monoidal.μ (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)
      ((toPresheafOfModules X).obj A)
      ((toPresheafOfModules X).obj (sheafification.obj (MonoidalCategory.tensorObj
        (C := MonoidalPresheaf X) ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))))).hom
    (sheafification.map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))))
    (sheafification_map_unit_eq _)

/-- **Presheaf-morphism factorization of the associator** (`lem:tensorObjAssoc_eta_factor`).
As morphisms of presheaves of modules `(A ⊗ₚ B) ⊗ₚ C ⟶ (tensorObj A (tensorObj B C)).val`,
the right-whiskered-unit leg composed with `Γ(tensorObjAssoc)` equals the presheaf associator
`α^p` composed with the left-whiskered-unit leg:
`(η_{A⊗ₚB} ▷ C ≫ η_{(A⊗B)⊗ₚC}) ≫ Γ(α) = α^p ≫ (A ◁ η_{B⊗ₚC} ≫ η_{A⊗ₚ(B⊗C)})`.
This is the `η`-naturality-plus-bridge-telescoping identity that lets `Γ(tensorObjAssoc)` push the
presheaf associator through the iterated `sectionsMul`; evaluating it at the top open on the
iterated elementary tensor is what feeds `tensorObjAssoc_hom_sectionsMul`. -/
private lemma tensorObjAssoc_eta_factor (A B C : X.Modules) :
    (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj (tensorObj A B)) ((toPresheafOfModules X).obj C))) ≫
        (tensorObjAssoc A B C).hom.val
      = (MonoidalCategory.associator (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
          ((toPresheafOfModules X).obj C)).hom ≫
        (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj (tensorObj B C)))) := by
  -- REDUCTION (B4 → sheaf-level core).  `T := toPresheafOfModules X = SheafOfModules.forget` sends
  -- `f ↦ f.val`, and the unit `η` of the sheafification adjunction is natural.  By `η`-naturality
  -- both sides collapse to `η_{(A⊗ₚB)⊗ₚC} ≫ T.map Φ`, and the sheaf-level core
  -- `tensorObjAssoc_eta_factor_sheaf` supplies `Φ_L = Φ_R` (an equation entirely inside the
  -- inherited monoidal structure on `X.Modules`, where the bridge telescoping lives).
  have key := tensorObjAssoc_eta_factor_sheaf A B C
  have hval : (tensorObjAssoc A B C).hom.val
      = (toPresheafOfModules X).map (tensorObjAssoc A B C).hom := rfl
  -- Clean naturality equalities, with the right-adjoint codomain written in `toPresheafOfModules`
  -- form (`restrictScalars (𝟙)` is defeq `𝟭`, so `exact unit.naturality _` bridges the decoration).
  have hnatL :
      MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
          ((toPresheafOfModules X).obj C) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj (tensorObj A B)) ((toPresheafOfModules X).obj C))
      = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C)) ≫
        (toPresheafOfModules X).map (sheafification.map
          (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
            ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)))
            ((toPresheafOfModules X).obj C))) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality _
  have hnatA :
      (MonoidalCategory.associator (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
            ((toPresheafOfModules X).obj C)).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C)))
      = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
            ((toPresheafOfModules X).obj C)) ≫
        (toPresheafOfModules X).map (sheafification.map
          (MonoidalCategory.associator (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)
            ((toPresheafOfModules X).obj C)).hom) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality _
  have hnatR :
      MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj A)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj (tensorObj B C)))
      = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))) ≫
        (toPresheafOfModules X).map (sheafification.map
          (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A)
            ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj C))))) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality _
  -- `erw` bridges the `restrictScalars (𝟙)` decoration on the shared middle object
  -- (`η`'s codomain carries it; `tensorObjAssoc`'s domain does not — defeq, but `rw` needs `erw`).
  rw [hval, hnatL]
  erw [Category.assoc, ← Functor.map_comp, key, Functor.map_comp, hnatR]
  erw [← Category.assoc, ← Category.assoc, hnatA]
  rfl

/-- Section-level naturality of the associator (`lem:tensorObjAssoc_hom_sectionsMul`): applying
global sections of `tensorObjAssoc A B C` to the iterated section product reassociates the three
section factors.  Section-level partner of the associativity constraint `tensorPowAdd_assoc`. -/
private lemma tensorObjAssoc_hom_sectionsMul (A B C : X.Modules)
    (a : ↥(A.val.obj (Opposite.op ⊤))) (b : ↥(B.val.obj (Opposite.op ⊤)))
    (c : ↥(C.val.obj (Opposite.op ⊤))) :
    ((tensorObjAssoc A B C).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorObj A B) C).hom
          ((sectionsMul A B).hom
              (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c))
      = (sectionsMul A (tensorObj B C)).hom
          (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
            (sectionsMul B C).hom
              (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c)) := by
  -- ASSEMBLY (B5).  TRUE for arbitrary `L` (tensor-algebra associativity).  The morphism-level
  -- factorization `tensorObjAssoc_eta_factor` (B4) is evaluated at the top open on `(a⊗b)⊗c`; its
  -- left side is recognized by `sectionsMul_whiskerRight_unit` (B2), its right side by
  -- `presheafAssociator_top_apply` (B1, `(a⊗b)⊗c ↦ a⊗(b⊗c)`) + `sectionsMul_whiskerLeft_unit` (B3).
  -- Rewrite both `sectionsMul`-nests back into their whiskered-unit-leg composites (B2/B3)…
  rw [← sectionsMul_whiskerRight_unit A B C a b c, ← sectionsMul_whiskerLeft_unit A B C a b c]
  -- …evaluate B4 at the top open on `(a⊗b)⊗c`: its two composites' `.app ⊤` split definitionally as
  -- `second.app⊤ ∘ first.app⊤`, so the LHS already matches; the RHS is `B3comp.app⊤ (α^p ((a⊗b)⊗c))`.
  refine (congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))
          ((toPresheafOfModules X).obj C)
        ⟶ (tensorObj A (tensorObj B C)).val) =>
      (φ.app (Opposite.op ⊤)).hom
        ((a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c))
    (tensorObjAssoc_eta_factor A B C)).trans ?_
  -- Residual: `B3comp.app⊤ (α^p ((a⊗b)⊗c)) = B3comp.app⊤ (a ⊗ (b ⊗ c))` — the presheaf associator
  -- at the top open is objectwise the ModuleCat associator (B1, `associator_hom_app` is `rfl`), and
  -- the ModuleCat associator reassociates the elementary tensor definitionally, so this is `rfl`.
  rfl

/-- Right-unit coherence of the tensor-power comparison family: the degree-`(n,0)` comparison
`μ_{n,0}` is the right unitor.  After the iter-023 second-index refactor this is the literal base
clause of `tensorPowAdd`, hence `rfl` (`lem:tensorPowAdd_zero_right`). -/
private lemma tensorPowAdd_zero_right (L : X.Modules) (n : ℕ) :
    tensorPowAdd L n 0 = tensorObjRightUnitor (tensorPow L n) := rfl

/-- Index-reindexing slide for the `tensorObjIso (L^·) L` family: an index equality `h : a = b`
transports the comparison `(tensorObjIso (L^a) L).inv ≫ (eqToHom ▷ L) ≫ (tensorObjIso (L^b) L).hom`
to the single reindexer `eqToHom` on `L^{·+1}`.  Proved by `subst` on the (fresh-variable) index
equality.  Used to discharge the `0 + c = c` reindexing residue of the `tensorPowAdd_zero_left`
succ case. -/
private lemma tensorObjIso_succ_reindex (L : X.Modules) {a b : ℕ} (h : a = b) :
    (tensorObjIso (tensorPow L a) L).inv ≫
        eqToHom (congrArg (tensorPow L) h) ▷ L ≫ (tensorObjIso (tensorPow L b) L).hom
      = eqToHom (congrArg (fun i => tensorObj (tensorPow L i) L) h) := by
  subst h
  simp

/-- Left-unit coherence of the tensor-power comparison family (`lem:tensorPowAdd_zero_left`): the
degree-`(0,n)` comparison `μ_{0,n}` is the left unitor, reindexed along `0 + n = n`.  After the
iter-023 second-index refactor this is no longer the base clause (that role passed to
`tensorPowAdd_zero_right`); it is proved by induction on `n` mirroring the new recursion.  The base
case `n = 0` is the unit coherence `λ_𝟙 = ρ_𝟙` (`unitors_equal`) descended through sheafification;
the succ case is the canonical left-unit triangle, discharged after the route-(b) `_eq` bridges by
the `monoidal` tactic. -/
private lemma tensorPowAdd_zero_left (L : X.Modules) (n : ℕ) :
    tensorPowAdd L 0 n = tensorObjUnitIso (tensorPow L n) ≪≫
      eqToIso (congrArg (tensorPow L) (Nat.zero_add n).symm) := by
  induction n with
  | zero =>
    -- base: `μ_{0,0} = ρ_{𝟙}` (the new base clause) and `ρ_𝟙 = λ_𝟙` (`unitors_equal`), descended
    -- through `sheafification`; the `eqToIso` along `0 + 0 = 0` is the identity.
    rw [Subsingleton.elim (congrArg (tensorPow L) (Nat.zero_add 0).symm)
        (rfl : tensorPow L 0 = tensorPow L (0 + 0)), eqToIso_refl, Iso.trans_refl]
    change tensorObjRightUnitor (tensorPow L 0) = tensorObjUnitIso (tensorPow L 0)
    change sheafification.mapIso (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj (tensorPow L 0))) ≪≫ sheafificationCounitIso (tensorPow L 0)
        = sheafification.mapIso (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj (tensorPow L 0))) ≪≫ sheafificationCounitIso (tensorPow L 0)
    congr 2
    apply Iso.ext
    exact MonoidalCategory.unitors_equal.symm
  | succ c ih =>
    -- succ: unfold the new succ clause `μ_{0,c+1} = α⁻¹ ≪≫ (μ_{0,c} ▷ L)`, fold `ih`, bridge to
    -- canonical `α_`/`λ_`/`▷`.  iter-023: this residual is **braiding-free** (left-unit triangle,
    -- `MonoidalCategory.leftUnitor_tensor`), NOT a hexagon.
    have hsucc : tensorPowAdd L 0 (c + 1) =
        (tensorObjAssoc (tensorPow L 0) (tensorPow L c) L).symm ≪≫
          tensorObjWhiskerRightIso (tensorPowAdd L 0 c) L := rfl
    rw [hsucc, ih]
    apply Iso.ext
    simp only [tensorObjWhiskerRightIso_eq, tensorObjUnitIso_eq, tensorObjAssoc,
      Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerRightIso_hom,
      MonoidalCategory.whiskerLeftIso_inv, MonoidalCategory.whiskerRightIso_inv,
      eqToIso.hom, eqToHom_map, Category.assoc,
      Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc,
      MonoidalCategory.hom_inv_whiskerRight_assoc, Iso.cancel_iso_inv_left,
      MonoidalCategory.comp_whiskerRight]
    -- Telescope the `tensorObjIso` bridges; the `(B3.hom ▷ L) ≫ (B3.inv ▷ L)` pair cancels.  Residual:
    --   `B1.inv ≫ unit ◁ B2.inv ≫ α⁻¹ ≫ (λ_{L^c} ▷ L) ≫ (eqToHom_c ▷ L) ≫ B4.hom
    --      = B1.inv ≫ (λ_{(L^c)⊗L}).hom ≫ eqToHom_{c+1}`  (B1=tensorObjIso unit ((L^c)⊗L),
    --   B2=tensorObjIso (L^c) L, B4=tensorObjIso (L^{0+c}) L).  NO braiding.
    simp only [tensorPow_zero, tensorPow_succ, MonoidalCategory.comp_whiskerRight, Category.assoc,
      MonoidalCategory.hom_inv_whiskerRight_assoc]
    -- CLOSE ROUTE (iter-023): `α⁻¹ ≫ (λ_{L^c} ▷ L) = λ_{(L^c)⊗L}` (`leftUnitor_tensor`), then
    -- `unit ◁ B2.inv ≫ λ = λ ≫ B2.inv` (`leftUnitor_naturality`), cancel the common `λ`, leaving the
    -- pure reindexer identity `B2.inv ≫ (eqToHom_c ▷ L) ≫ B4.hom = eqToHom_{c+1}` (holds by `0+c = c`).
    have hlt : (α_ (unitModule X) (L.tensorPow c) L).inv ≫ (λ_ (L.tensorPow c)).hom ▷ L
        = (λ_ (L.tensorPow c ⊗ L)).hom := by monoidal
    rw [reassoc_of% hlt]
    erw [MonoidalCategory.leftUnitor_naturality_assoc]
    -- cancel the common `B1.inv ≫ λ` prefix; the residual is the pure `0 + c = c` reindexer.
    congr 1
    congr 1
    exact tensorObjIso_succ_reindex L (Nat.zero_add c).symm

/-- Left unitality of the graded section multiplication (`lem:sectionMul_coherent`, left-unit case):
for `a ∈ Γ(X, L^{⊗n})`, transporting `1 · a` along `0 + n = n` gives `a`.
Mirrors `TensorPower.one_mul`. -/
theorem sectionsMul_one_mul (L : X.Modules) {n : ℕ} (a : sectionDeg L n) :
    sectionsCast L (zero_add n) (GradedMonoid.GMul.mul GradedMonoid.GOne.one a) = a := by
  rw [gMul_mul_apply, gOne_one_eq, tensorPowAdd_zero_left L n]
  -- `tensorPowAdd L 0 n = tensorObjUnitIso ≪≫ eqToIso`; the inner cast pairs with the outer
  -- `sectionsCast` and the two cancel (`sectionsCast_sectionsCast`), leaving the left unitor.
  change sectionsCast L (zero_add n) (sectionsCast L (Nat.zero_add n).symm
      (((tensorObjUnitIso (tensorPow L n)).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorPow L 0) (tensorPow L n)).hom
          ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] a)))) = a
  rw [sectionsCast_sectionsCast]
  exact tensorObjUnitIso_hom_sectionsMul (tensorPow L n) a

/-- Right unitality of the graded section multiplication
(`lem:sectionMul_coherent`, right-unit case):
for `a ∈ Γ(X, L^{⊗n})`, transporting `a · 1` along `n + 0 = n` gives `a`.
Mirrors `TensorPower.mul_one`. -/
theorem sectionsMul_mul_one (L : X.Modules) {n : ℕ} (a : sectionDeg L n) :
    sectionsCast L (add_zero n) (GradedMonoid.GMul.mul a GradedMonoid.GOne.one) = a := by
  rw [gMul_mul_apply, gOne_one_eq]
  -- The right-unit coherence of the comparison family: the degree-`(n,0)` comparison IS the right
  -- unitor.  After the iter-023 second-index refactor this is the literal `m' = 0` base clause of
  -- `tensorPowAdd`, so `tensorPowAdd L n 0 = tensorObjRightUnitor (tensorPow L n)` holds by `rfl`
  -- (`tensorPowAdd_zero_right`) — NO induction, NO braiding, NO triangle.  The degreewise statement
  -- then follows from `tensorObjRightUnitor_hom_sectionsMul` (axiom-clean) + `sectionsCast_self`.
  have hμn0 : tensorPowAdd L n 0 = tensorObjRightUnitor (tensorPow L n) :=
    tensorPowAdd_zero_right L n
  have hinner : ((tensorPowAdd L n 0).hom.val.app (Opposite.op ⊤)).hom
      ((sectionsMul (tensorPow L n) (tensorPow L 0)).hom
        (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          (1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))))) = a := by
    rw [hμn0]
    exact tensorObjRightUnitor_hom_sectionsMul (tensorPow L n) a
  rw [hinner]
  exact sectionsCast_self L (add_zero n) a

/-- Reindexing slide for the `tensorObjIso`/`tensorPowAdd` tail: the index-`p` comparison composite
flanked by the reindexing `eqToHom`s along `p = m'` equals the index-`m'` composite.  Proved by
`subst` on the index equality (collapsing all `eqToHom`s to identities).  Used to discharge the
`0 + m' = m'` reindexing residue of the `tensorPowAdd_assoc` base case. -/
private lemma tensorObjIso_tensorPowAdd_reindex (L : X.Modules) (m' m'' : ℕ) {p s : ℕ}
    (hp : p = m') (hs : p + m'' = s) (hs' : m' + m'' = s) :
    eqToHom (congrArg (tensorPow L) hp.symm) ▷ tensorPow L m'' ≫
        (tensorObjIso (tensorPow L p) (tensorPow L m'')).hom ≫
        (tensorPowAdd L p m'').hom ≫ eqToHom (congrArg (tensorPow L) hs)
      = (tensorObjIso (tensorPow L m') (tensorPow L m'')).hom ≫ (tensorPowAdd L m' m'').hom ≫
          eqToHom (congrArg (tensorPow L) hs') := by
  subst hp
  subst hs
  simp

/-- Definitional succ-clause of the comparison `μ = tensorPowAdd` (the second-index `(c+1)`-branch
of the iter-023 refactored recursion), packaged as a rewrite lemma.  `rfl`. -/
private lemma tensorPowAdd_succ (L : X.Modules) (m c : ℕ) :
    tensorPowAdd L m (c + 1) =
      (tensorObjAssoc (tensorPow L m) (tensorPow L c) L).symm ≪≫
      tensorObjWhiskerRightIso (tensorPowAdd L m c) L := rfl

/-- Right-whiskering by a tensor-object factors through the associator (hand-built analogue of the
canonical `MonoidalCategory.whiskerRight_tensor`): `e ▷ (A ⊗ B) = α⁻¹ ≪≫ ((e ▷ A) ▷ B) ≪≫ α`.  This
is the iso-level distribution used to fold the inductive hypothesis in the succ case of
`tensorPowAdd_assoc` (it exposes the single right-whisker `WR(e) A` that `ih` consumes).  Proved by
the route-(b) bridge recipe + the canonical `whiskerRight_tensor`. -/
private lemma tensorObjWhiskerRightIso_tensorObj {F F' : X.Modules} (e : F ≅ F')
    (A B : X.Modules) :
    tensorObjWhiskerRightIso e (tensorObj A B)
      = (tensorObjAssoc F A B).symm ≪≫
          tensorObjWhiskerRightIso (tensorObjWhiskerRightIso e A) B ≪≫ tensorObjAssoc F' A B := by
  apply Iso.ext
  simp only [tensorObjWhiskerRightIso_eq, tensorObjAssoc, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, MonoidalCategory.whiskerRightIso_hom,
    MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.whiskerLeftIso_inv, Category.assoc, MonoidalCategory.comp_whiskerRight,
    Iso.hom_inv_id_assoc, MonoidalCategory.hom_inv_whiskerRight_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc, Iso.cancel_iso_inv_left]
  -- canonical `whiskerRight_tensor` (regroup `(e ▷ A) ▷ B` to `e ▷ (A⊗B)`), then `whisker_exchange`
  -- slides `e ▷ -` past the bridge `T = tensorObjIso A B`, which cancels (`Iso.inv_hom_id`).
  rw [← MonoidalCategory.whiskerRight_tensor_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **Generic-`M` core of the succ-case canonical pentagon residual of `tensorPowAdd_assoc`.**
Stated over an arbitrary monoidal category `M` so that all `≫`/`▷`/`◁`/`α_` resolve to a single
uniform category instance (no `LocalizedMonoidal`/`X.Modules` comp-instance diamond), making the
fold + cancellation + associator-naturality simp set fire.  Plugged into the succ branch by `exact`
(the instance diamond is `rfl`-defeq, so `exact`'s `isDefEq` bridges it; cf.
`tensorObjAssoc_associator_counit_coherence`).  `foldhyp` is the whiskered inductive hypothesis
`ihRh`; `hμ5` is the second-index succ-unfold of the right comparison atom `μ_{m,m'+(c+1)}`.  The
proof folds `foldhyp` (after cancelling its `iABCL.inv` epi prefix), substitutes `hμ5`, telescopes
the bridge `hom`/`inv` pairs, and closes the residual associator-naturality square with one
`associator_inv_naturality_left` slide + `whisker_assoc`/`whisker_exchange` + `monoidal`. -/
private lemma tensorPowAdd_assoc_succ_core
    {M : Type*} [Category M] [MonoidalCategory M]
    {a b cc l ab abc bc r Pab Pcl Pbc Pbcl Pabc Q8
      Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q9 Q10 : M}
    (iAB_CL : Pab ⊗ Pcl ≅ Q1) (iCL : cc ⊗ l ≅ Pcl)
    (iAB_C : Pab ⊗ cc ≅ Pabc) (iab_C : ab ⊗ cc ≅ Q2) (iab_CL : ab ⊗ Pcl ≅ Q3)
    (iABC_L : abc ⊗ l ≅ Q4) (iR_L : r ⊗ l ≅ Q5)
    (iAB : a ⊗ b ≅ Pab) (iB_CL : b ⊗ Pcl ≅ Pbcl) (iB_C : b ⊗ cc ≅ Pbc)
    (iBC_L : bc ⊗ l ≅ Q6) (iA_S : a ⊗ Q6 ≅ Q7)
    (iABCL : Pabc ⊗ l ≅ Q8) (iA_BC : a ⊗ Pbc ≅ Q9) (iA_bc : a ⊗ bc ≅ Q10)
    (μ1 : Pab ⟶ ab) (μ2 : Q2 ⟶ abc) (μ3 : Q10 ⟶ r) (μ4 : Pbc ⟶ bc) (μ5 : Q7 ⟶ Q5)
    (e : abc ⟶ r)
    (foldhyp :
      iABCL.inv ≫ (iAB_C.inv ≫ μ1 ▷ cc ≫ iab_C.hom) ▷ l ≫ μ2 ▷ l ≫ e ▷ l ≫ iR_L.hom
        = iABCL.inv ≫ (iAB_C.inv ≫ iAB.inv ▷ cc ≫ (α_ a b cc).hom ≫ a ◁ iB_C.hom ≫ iA_BC.hom) ▷ l
            ≫ (iA_BC.inv ≫ a ◁ μ4 ≫ iA_bc.hom) ▷ l ≫ μ3 ▷ l ≫ iR_L.hom)
    (hμ5 : iA_S.hom ≫ μ5
        = a ◁ iBC_L.inv ≫ (α_ a bc l).inv ≫ iA_bc.hom ▷ l ≫ μ3 ▷ l ≫ iR_L.hom) :
    iAB_CL.inv ≫ Pab ◁ iCL.inv ≫ (α_ Pab cc l).inv ≫ iAB_C.hom ▷ l
        ≫ (iAB_C.inv ≫ μ1 ▷ cc ≫ iab_C.hom) ▷ l ≫ iab_C.inv ▷ l ≫ (α_ ab cc l).hom
        ≫ ab ◁ iCL.hom ≫ iab_CL.hom
        ≫ (iab_CL.inv ≫ ab ◁ iCL.inv ≫ (α_ ab cc l).inv ≫ iab_C.hom ▷ l ≫ μ2 ▷ l ≫ iABC_L.hom)
        ≫ iABC_L.inv ≫ e ▷ l ≫ iR_L.hom
      = iAB_CL.inv ≫ iAB.inv ▷ Pcl ≫ (α_ a b Pcl).hom ≫ a ◁ iB_CL.hom
        ≫ a ◁ (iB_CL.inv ≫ b ◁ iCL.inv ≫ (α_ b cc l).inv ≫ iB_C.hom ▷ l ≫ μ4 ▷ l ≫ iBC_L.hom)
        ≫ iA_S.hom ≫ μ5 := by
  rw [hμ5]
  have foldhyp' := (cancel_epi iABCL.inv).mp foldhyp
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc, MonoidalCategory.inv_hom_whiskerRight_assoc]
  rw [foldhyp']
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.hom_inv_whiskerRight_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [← MonoidalCategory.associator_inv_naturality_left_assoc]
  simp only [Category.assoc, MonoidalCategory.whisker_assoc, MonoidalCategory.whisker_exchange_assoc]
  monoidal

-- The final `exact tensorPowAdd_assoc_succ_core (M := LocalizedMonoidal …) …` in the succ branch
-- discharges the canonical pentagon via a head-aligned `isDefEq` across the `instCategory`/
-- `LocalizedMonoidal` rfl-diamond; pinning `M` makes it short-circuit, but it still recurses past the
-- default `maxRecDepth = 512` (a stack-depth bound, NOT the forbidden heartbeat bump).
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Associativity constraint for the tensor-power comparison** (`lem:tensorPowAdd_assoc`): the
two bracketings of `L^⊗m ⊗ L^⊗m' ⊗ L^⊗m''` into `L^⊗(m+m'+m'')` agree:
`(μ_{m,m'} ▷ L^m'') ≫ μ_{m+m',m''}` (reindexed by `(m+m')+m'' = m+(m'+m'')`) equals
`α ≫ (L^m ◁ μ_{m',m''}) ≫ μ_{m,m'+m''}`, where `α = tensorObjAssoc`.  This is the canonical
pentagon constraint of `tensorPowAdd` — SOUND for arbitrary `L` (both bracketings realise the SAME
permutation of the `m+m'+m''` identical `L`-factors, unlike the commutativity hexagon).  Proved by
induction on `m` mirroring the recursion of `tensorPowAdd` (analogue of `tensorPowAdd_zero_right`):
after the whisker bridges `tensorObjWhiskerRightIso_eq`/`tensorObjWhiskerLeftIso_eq` rewrite the
hand-built whiskerings to canonical ones and the `tensorObjIso` bridges telescope in adjacent pairs,
the obligation collapses to `MonoidalCategory.pentagon` of the inherited monoidal structure. -/
private lemma tensorPowAdd_assoc (L : X.Modules) (m m' m'' : ℕ) :
    tensorObjWhiskerRightIso (tensorPowAdd L m m') (tensorPow L m'') ≪≫
        tensorPowAdd L (m + m') m'' ≪≫
        eqToIso (congrArg (tensorPow L) (add_assoc m m' m''))
      = tensorObjAssoc (tensorPow L m) (tensorPow L m') (tensorPow L m'') ≪≫
        tensorObjWhiskerLeftIso (tensorPow L m) (tensorPowAdd L m' m'') ≪≫
        tensorPowAdd L m (m' + m'') := by
  -- iter-023 braiding-free pentagon induction on the LAST index `m''` (mirrors the refactored
  -- second-index recursion of `tensorPowAdd`).  Both bracketings are composites of canonical
  -- associators and right-whiskers ONLY — no braiding — so after the route-(b) `_eq` bridges rewrite
  -- the hand-built constructs to canonical `α_`/`ρ_`/`λ_`/`▷`/`◁` and the `tensorObjIso` bridge pairs
  -- telescope, the residual is the canonical pentagon, closed by `monoidal`.
  induction m'' with
  | zero =>
    -- base `m'' = 0`: `μ_{·,0} = ρ` (`tensorPowAdd_zero_right`, rfl); the `add_assoc _ _ 0`
    -- reindexer is the identity.  The residual right-unit triangle / ρ-naturality closes by
    -- `monoidal`.
    rw [Subsingleton.elim (congrArg (tensorPow L) (add_assoc m m' 0))
        (rfl : tensorPow L (m + m' + 0) = tensorPow L (m + (m' + 0))), eqToIso_refl, Iso.trans_refl]
    apply Iso.ext
    simp only [tensorPowAdd_zero_right, add_zero, tensorObjWhiskerRightIso_eq,
      tensorObjWhiskerLeftIso_eq, tensorObjRightUnitor_eq, tensorObjAssoc, Iso.trans_hom,
      Iso.symm_hom, MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerRightIso_hom,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_inv_left]
    -- cancel the unit-side `tensorObjIso` bridge pairs, then close by ρ-naturality on both sides
    -- flanking the right-unit triangle (`htri`), and the surviving bridge `B = tensorObjIso (L^m) (L^m')`
    -- cancels via `Iso.inv_hom_id`.  No braiding.
    simp only [tensorPow_zero, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc]
    -- `erw` bridges the `unitModule X = 𝟙_ X.Modules` head defeq that blocks plain `rw`.
    erw [MonoidalCategory.rightUnitor_naturality]
    have htri : (α_ (L.tensorPow m) (L.tensorPow m') (unitModule X)).hom ≫
        L.tensorPow m ◁ (ρ_ (L.tensorPow m')).hom = (ρ_ (L.tensorPow m ⊗ L.tensorPow m')).hom := by
      monoidal
    rw [reassoc_of% htri]
    -- second ρ-naturality slide (`_assoc` form: `ρ` is mid-chain) brings the bridge `B.inv` adjacent
    -- to `B.hom` (`Iso.inv_hom_id_assoc`, matched up to the `m'+0 = m'` defeq by `erw`); the residual
    -- `ρ ≫ μ_{m,m'} = ρ ≫ μ_{m,m'+0}` is `rfl` (`m'+0 = m'`).
    erw [MonoidalCategory.rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]
    rfl
  | succ c ih =>
    -- succ `m'' = c+1`.  iter-023 refactor CONFIRMED: this residual is **braiding-free** — the goal
    -- below is built ENTIRELY from `tensorObjAssoc` (canonical `α_`), `tensorObjWhiskerRightIso`/
    -- `tensorObjWhiskerLeftIso` and the folded `tensorPowAdd` atoms + `eqToIso` reindexers, with NO
    -- `tensorBraiding` anywhere (the old first-index recursion forced a `β`; the second-index
    -- recursion does not).  So the reverse signal (a reappearing braiding ⇒ refactor wrong) is ABSENT;
    -- the obligation is the pure categorified-`pow_add` pentagon.
    --
    -- GROUNDWORK (compiles): unfold both second-index succ-clauses (`μ_{·,c+1} = α⁻¹ ≪≫ (μ_{·,c} ▷ L)`,
    -- `tensorPowAdd_succ`), distribute the outer right-whisker over `L^{c+1} = L^c ⊗ L`
    -- (`tensorObjWhiskerRightIso_tensorObj`, the new helper) and the left-whisker
    -- (`tensorObjWhiskerLeftIso_trans`); `ihR` is `ih` whiskered `▷ L` and distributed.  After this the
    -- goal LHS carries the adjacent pair `α'' ≪≫ α''.symm` (`α'' = tensorObjAssoc (L^{m+m'}) (L^c) L`)
    -- whose cancellation exposes `WR(WR μ_{m,m'} (L^c)) L ≪≫ WR(μ_{m+m',c}) L`, i.e. the first two
    -- factors of `ihR`'s LHS — the fold point.
    --
    -- REMAINING BLOCKER (iter-024, PRECISELY LOCALIZED via `lean_multi_attempt` — it is the
    -- `LocalizedMonoidal`/`X.Modules` **comp-instance diamond**, NOT a dependent-`eqToIso` motive as the
    -- iter-023 note guessed).  The reduction below is BANKED groundwork (every step verified to fire):
    --   • `ihRh` = `ih` whiskered `▷ L` (`ihR`), pushed to `.hom` and canonicalised — relates the four
    --     atoms `μ_{m,m'}`,`μ_{m+m',c}`,`μ_{m',c}`,`μ_{m,m'+c}` at hom level.  WORKS.
    --   • `key` rewrites the trailing dependent `eqToIso (add_assoc m m' (c+1))` to
    --     `WR(eqToIso (add_assoc m m' c), L)` (`tensorObjWhiskerRightIso_eqToIso` + `rfl`), making the
    --     goal's trailing factor match `ihRh`'s.  WORKS (`rw [key]` fires).
    --   • `Iso.ext` + the canonical `simp only` bridge set reduces the goal to a FULLY-CANONICAL hom
    --     equation (only `α_`/`▷`/`◁`/`tensorObjIso`-bridges/`μ`-atom-homs/`eqToHom`).  WORKS.
    -- At that point `ihRh.LHS` is a subterm of the goal LHS *modulo* the telescope
    -- `Tr.hom ≫ Tr.inv` (`Tr = tensorObjIso (L^{m+m'}) ((L^c)⊗L)`) collapsing to `𝟙`.  That single
    -- `Iso.hom_inv_id_assoc` CANNOT fire: the `≫` at that junction mixes the native `X.Modules`-comp
    -- (from the `tensorObjWhiskerRightIso_tensorObj` distribution) with the `LocalizedMonoidal`-comp
    -- (from the `tensorPowAdd_succ` unfold).  CONFIRMED dead for this junction: `rw`/`simp`/`simp [hc]`
    -- (comp-bridge, both directions)/explicit-arg `Iso.trans_assoc` all fail to match `(?f ≫ ?g) ≫ ?h`
    -- / `e.hom ≫ e.inv ≫ ?`; `erw [Iso.trans_assoc]` times out (>200k whnf — the diamond `isDefEq`).
    -- This is the SAME diamond `tensorObjAssoc_eta_factor_sheaf` (this file, ~L2637) solved by
    -- abstracting the whole canonical equation to a *generic* monoidal `M` and closing via `exact`
    -- (whose `isDefEq` bridges the rfl-defeq diamond; `rw`/`simp` cannot).
    -- NEXT (the path, fully scoped): state `private lemma tensorPowAdd_assoc_succ_core {M}[Cat M]
    -- [Mon M] (…isos/μ-homs…) (foldhyp : <ihRh>) : <canonical hom equation> := by
    --   simp only [Category.assoc, Iso.hom_inv_id_assoc, MonoidalCategory.whisker_exchange_assoc,
    --     MonoidalCategory.associator_naturality_*]; rw [foldhyp]; … ; monoidal`,
    -- then `exact tensorPowAdd_assoc_succ_core … ihRh` here.  NB the RHS atom `μ_{m,m'+(c+1)}` must be
    -- unfolded via `tensorPowAdd_succ` (its index `m'+(c+1)` is DEFEQ to `(m'+c)+1`) to expose
    -- `μ_{m,m'+c}` (the `ihRh` RHS atom) before the generic statement is read off.
    have ihR := congrArg (fun i => tensorObjWhiskerRightIso i L) ih
    simp only [tensorObjWhiskerRightIso_trans] at ihR
    -- `ihRh` : the canonicalised hom image of the whiskered inductive hypothesis (the fold relation).
    have ihRh : _ = _ := congrArg Iso.hom ihR
    simp only [Iso.trans_hom, Iso.symm_hom, tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq,
      tensorObjAssoc, MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
      eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc] at ihRh
    -- `key` : align the trailing dependent reindexer with `ihRh`'s `WR(eqToIso, L)` trailing factor.
    have key : eqToIso (congrArg (tensorPow L) (add_assoc m m' (c + 1)))
        = tensorObjWhiskerRightIso (eqToIso (congrArg (tensorPow L) (add_assoc m m' c))) L := by
      rw [tensorObjWhiskerRightIso_eqToIso]; rfl
    simp only [tensorPow_succ, tensorPowAdd_succ, tensorObjWhiskerRightIso_tensorObj,
      tensorObjWhiskerLeftIso_trans, Iso.trans_assoc]
    rw [key]
    refine Iso.ext ?_
    -- Fully-canonical hom goal: `α_`/`▷`/`◁`/`tensorObjIso`-bridges/`μ`-atom-homs/`eqToHom` only.
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorObjAssoc,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
      MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
      eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    -- Canonical-pentagon residual.  Closed (iter-025) via the generic-`M` core
    -- `tensorPowAdd_assoc_succ_core`, pinned to the `LocalizedMonoidal` synonym so `exact`'s `isDefEq`
    -- bridges the `X.Modules` comp-instance diamond (`rw`/`simp`/`erw`/`hc` all confirmed dead here).
    -- `ihRh` supplies `foldhyp`; `hμ5` is the second-index succ-unfold of the right comparison atom
    -- `μ_{m,m'+(c+1)}` (`tensorPowAdd_succ` (DEFEQ index `m'+(c+1) = (m'+c)+1`) + `tensorObjAssoc`/
    -- `tensorObjWhiskerRightIso_eq` telescoping, the two surviving `tensorObjIso` pairs cancelling).
    have hdef : L.tensorPowAdd m (m' + (c + 1))
        = (tensorObjAssoc (L.tensorPow m) (L.tensorPow (m' + c)) L).symm ≪≫
          tensorObjWhiskerRightIso (L.tensorPowAdd m (m' + c)) L := rfl
    have hμ5 : ((L.tensorPow m).tensorObjIso ((L.tensorPow (m' + c)).tensorObj L)).hom
          ≫ (L.tensorPowAdd m (m' + (c + 1))).hom
        = L.tensorPow m ◁ ((L.tensorPow (m' + c)).tensorObjIso L).inv
          ≫ (α_ (L.tensorPow m) (L.tensorPow (m' + c)) L).inv
          ≫ ((L.tensorPow m).tensorObjIso (L.tensorPow (m' + c))).hom ▷ L
          ≫ (L.tensorPowAdd m (m' + c)).hom ▷ L
          ≫ ((L.tensorPow (m + (m' + c))).tensorObjIso L).hom := by
      rw [hdef]
      simp only [tensorObjAssoc, tensorObjWhiskerRightIso_eq, Iso.trans_hom, Iso.symm_hom,
        Iso.trans_inv, Iso.symm_inv, MonoidalCategory.whiskerRightIso_hom,
        MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv, Category.assoc,
        Iso.hom_inv_id_assoc]
      exact Iso.hom_inv_id_assoc _ _
    exact tensorPowAdd_assoc_succ_core
      (M := LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
      (iAB_CL :=
        ((L.tensorPow m).tensorObj (L.tensorPow m')).tensorObjIso ((L.tensorPow c).tensorObj L))
      (iCL := (L.tensorPow c).tensorObjIso L)
      (iab_CL := (L.tensorPow (m + m')).tensorObjIso ((L.tensorPow c).tensorObj L))
      (iABC_L := (L.tensorPow (m + m' + c)).tensorObjIso L)
      (iB_CL := (L.tensorPow m').tensorObjIso ((L.tensorPow c).tensorObj L))
      (foldhyp := ihRh) (hμ5 := hμ5)

/-- **Right-whisker naturality of the section product** (`lem:sectionsMul_whiskerRight_natural`),
iso form.  General-morphism analogue of `sectionsMul_whiskerRight_unit` (which is the special case
`e = η`): for an iso `e : F ≅ F'`, sliding `Γ(e.hom)` out of the first tensor factor of the outer
`sectionsMul` turns it into the whiskered comparison `Γ((tensorObjWhiskerRightIso e G).hom)`.
Proved exactly like `tensorBraiding_hom_sectionsMul`: by `η`-naturality of the sheafification unit
along the *presheaf* right-whiskering `(toPresheaf e.hom) ▷_p (toPresheaf G)` (whose sheafification
IS `(tensorObjWhiskerRightIso e G).hom` by `rfl`), plus the objectwise whisker formula at the top
open (`x ⊗ y ↦ Γ(e.hom)(x) ⊗ y`, `rfl`).  The slide used in the associativity leg of
`sectionsMul_mul_assoc` to move an inner `Γ(μ)` out of the first factor. -/
private lemma sectionsMul_whiskerRight_natural {F F' : X.Modules} (e : F ≅ F') (G : X.Modules)
    (x : ↥(F.val.obj (Opposite.op ⊤))) (y : ↥(G.val.obj (Opposite.op ⊤))) :
    (sectionsMul F' G).hom
        (((e.hom.val.app (Opposite.op ⊤)).hom x)
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)
      = ((tensorObjWhiskerRightIso e G).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul F G).hom
            (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)) := by
  -- η-naturality along the presheaf right-whiskering of `toPresheaf e.hom` by `toPresheaf G`.
  have hmor :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))
        ≫ (tensorObjWhiskerRightIso e G).hom.val
      = (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G))
        ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj F') ((toPresheafOfModules X).obj G)) := by
    have e1 : (tensorObjWhiskerRightIso e G).hom.val
        = (SheafOfModules.forget X.ringCatSheaf
              ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
              (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G))) :=
      rfl
    rw [e1]
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G))).symm
  -- The presheaf right-whisker at the top open: `x ⊗ y ↦ Γ(e.hom)(x) ⊗ y`.
  have hw : ((MonoidalCategory.whiskerRight (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).map e.hom) ((toPresheafOfModules X).obj G)).app
          (Opposite.op ⊤)).hom
        (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)
      = (((e.hom.val.app (Opposite.op ⊤)).hom x)
          ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y :
          ↥(MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F') ((toPresheafOfModules X).obj G)
              |>.obj (Opposite.op ⊤))) :=
    rfl
  -- Evaluate the morphism identity `hmor` at the top open on `x ⊗ y`.
  have key := congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)
        ⟶ (tensorObj F' G).val) =>
      (φ.app (Opposite.op ⊤)).hom
        (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)) hmor
  exact ((congrArg (sectionsMul F' G).hom hw).symm).trans key.symm

/-- **Left-whisker naturality of the section product** (`lem:sectionsMul_whiskerLeft_natural`),
iso form.  General-morphism analogue of `sectionsMul_whiskerLeft_unit`: for an iso `e : G ≅ G'`,
sliding `Γ(e.hom)` out of the second tensor factor of the outer `sectionsMul` turns it into the
whiskered comparison `Γ((tensorObjWhiskerLeftIso F e).hom)`.  Left-handed mirror of
`sectionsMul_whiskerRight_natural`: η-naturality along the presheaf left-whiskering
`(toPresheaf F) ◁_p (toPresheaf e.hom)`, plus the objectwise whisker formula
(`x ⊗ y ↦ x ⊗ Γ(e.hom)(y)`).  The slide used in the associativity leg of `sectionsMul_mul_assoc`
to move an inner `Γ(μ)` out of the second factor. -/
private lemma sectionsMul_whiskerLeft_natural (F : X.Modules) {G G' : X.Modules} (e : G ≅ G')
    (x : ↥(F.val.obj (Opposite.op ⊤))) (y : ↥(G.val.obj (Opposite.op ⊤))) :
    (sectionsMul F G').hom
        (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          ((e.hom.val.app (Opposite.op ⊤)).hom y))
      = ((tensorObjWhiskerLeftIso F e).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul F G).hom
            (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)) := by
  -- η-naturality along the presheaf left-whiskering of `toPresheaf e.hom` by `toPresheaf F`.
  have hmor :
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G))
        ≫ (tensorObjWhiskerLeftIso F e).hom.val
      = (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).map e.hom))
        ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G')) := by
    have e1 : (tensorObjWhiskerLeftIso F e).hom.val
        = (SheafOfModules.forget X.ringCatSheaf
              ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
              (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
                ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).map e.hom))) :=
      rfl
    rw [e1]
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).map e.hom))).symm
  -- The presheaf left-whisker at the top open: `x ⊗ y ↦ x ⊗ Γ(e.hom)(y)`.
  have hw : ((MonoidalCategory.whiskerLeft (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).map e.hom)).app
          (Opposite.op ⊤)).hom
        (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)
      = (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)]
          ((e.hom.val.app (Opposite.op ⊤)).hom y) :
          ↥(MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G')
              |>.obj (Opposite.op ⊤))) :=
    rfl
  -- Evaluate the morphism identity `hmor` at the top open on `x ⊗ y`.
  have key := congrArg
    (fun (φ : MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj F) ((toPresheafOfModules X).obj G)
        ⟶ (tensorObj F G').val) =>
      (φ.app (Opposite.op ⊤)).hom
        (x ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] y)) hmor
  exact ((congrArg (sectionsMul F G').hom hw).symm).trans key.symm

/-- Associativity of the graded section multiplication (`lem:sectionMul_coherent`, associativity):
transporting `(a · b) · c` along `(na + nb) + nc = na + (nb + nc)` gives `a · (b · c)`.
Mirrors `TensorPower.mul_assoc`. -/
theorem sectionsMul_mul_assoc (L : X.Modules) {na nb nc : ℕ}
    (a : sectionDeg L na) (b : sectionDeg L nb) (c : sectionDeg L nc) :
    sectionsCast L (add_assoc na nb nc)
      (GradedMonoid.GMul.mul (GradedMonoid.GMul.mul a b) c) =
      GradedMonoid.GMul.mul a (GradedMonoid.GMul.mul b c) := by
  -- Unfold the degreewise multiplication on both sides to `Γ(μ) ∘ sectionsMul`.
  simp only [gMul_mul_apply]
  -- ASSEMBLY (iter-026).  TRUE for arbitrary `L` (associativity of the tensor-algebra product).
  -- Three ingredients combine, mirroring `sectionsMul_mul_one`:
  --   (2a) RIGHT slide `sectionsMul_whiskerRight_natural` (e = μ_{na,nb}): move the inner
  --        `Γ(μ_{na,nb})` out of the first factor of the outer `sectionsMul (L^{na+nb}) (L^nc)`,
  --        turning it into `Γ(WR(μ_{na,nb}) (L^nc))` applied to `sectionsMul (L^na⊗L^nb) (L^nc) …`.
  rw [sectionsMul_whiskerRight_natural (tensorPowAdd L na nb) (tensorPow L nc)
        ((sectionsMul (tensorPow L na) (tensorPow L nb)).hom
          (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)) c]
  --   (2b) LEFT slide `sectionsMul_whiskerLeft_natural` (e = μ_{nb,nc}): move the inner
  --        `Γ(μ_{nb,nc})` out of the second factor of the outer `sectionsMul (L^na) (L^{nb+nc})`.
  rw [sectionsMul_whiskerLeft_natural (tensorPow L na) (tensorPowAdd L nb nc) a
        ((sectionsMul (tensorPow L nb) (tensorPow L nc)).hom
          (b ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c))]
  --   (1) B5 `tensorObjAssoc_hom_sectionsMul` (backwards): recognise the RHS iterated section
  --       product `sectionsMul (L^na) (L^nb⊗L^nc) (a ⊗ sectionsMul (L^nb)(L^nc)(b⊗c))` as
  --       `Γ(α) (sectionsMul (L^na⊗L^nb)(L^nc) (sectionsMul (L^na)(L^nb)(a⊗b) ⊗ c))`.
  rw [← tensorObjAssoc_hom_sectionsMul (tensorPow L na) (tensorPow L nb) (tensorPow L nc) a b c]
  --   (3) B6 `tensorPowAdd_assoc` (the iso-level pentagon) applied at the common base element
  --       `z = sectionsMul (L^na⊗L^nb)(L^nc) (sectionsMul (L^na)(L^nb)(a⊗b) ⊗ c)`.  Both sides of
  --       the goal are now `Γ(·)(z)` for the two pentagon composites, equal up to defeq (functor
  --       composition / `Iso.trans_hom` / `sectionsCast_apply` are all `rfl`).
  exact congrArg
    (fun (i : tensorObj (tensorObj (tensorPow L na) (tensorPow L nb)) (tensorPow L nc)
        ≅ tensorPow L (na + (nb + nc))) =>
      (i.hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorObj (tensorPow L na) (tensorPow L nb)) (tensorPow L nc)).hom
          ((sectionsMul (tensorPow L na) (tensorPow L nb)).hom
              (a ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] b)
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] c)))
    (tensorPowAdd_assoc L na nb nc)

/-! ## Project-local Mathlib supplement — the section graded semiring (∀L, Stacks 01CV)

Assembly of the graded-ring structure on `m ↦ Γ(X, L^{⊗m})` from the now-complete coherence
chain.  Field-for-field port of `Mathlib.LinearAlgebra.TensorPower.Basic`, with `sectionsCast`
in place of `TensorPower.cast` and the three hypothesis-free clauses of `sectionMul_coherent`
(`sectionsMul_one_mul`/`sectionsMul_mul_one`/`sectionsMul_mul_assoc`) as the graded-monoid axioms.
No invertibility hypothesis — the resulting semiring is in general non-commutative (the free
tensor algebra on `Γ(X,L)`).  The `GCommSemiring` upgrade for invertible `L` is built
(`sectionGradedRing_gcommSemiring`, below). -/

/-- **Graded monoid structure on the section components** (`lem:sectionGradedRing_gsemiring`,
GMonoid layer): the family `m ↦ Γ(X, L^{⊗m})` is a `GradedMonoid.GMonoid` under the degreewise
multiplication `Γ(μ_{m,m'}) ∘ sectionsMul` (the `GMul` instance) and the unit `1 ∈ Γ(X,𝒪_X)` (the
`GOne` instance).  The three graded-monoid axioms are the hypothesis-free unit/associativity
clauses `sectionsMul_one_mul`, `sectionsMul_mul_one`, `sectionsMul_mul_assoc`, each routed through
`gradedMonoid_eq_of_cast` (transport-mediated equality → dependent-pair equality).  The graded
power `gnpow` takes its Mathlib default (mirrors `TensorPower.Basic`, which omits it).
Project-local: Mathlib has no graded monoid on sheaf-section tensor powers. -/
@[reducible] noncomputable def sectionGradedRing_gmonoid (L : X.Modules) :
    GradedMonoid.GMonoid (sectionDeg L) :=
  { (inferInstance : GradedMonoid.GMul (sectionDeg L)),
    (inferInstance : GradedMonoid.GOne (sectionDeg L)) with
    one_mul := fun a => gradedMonoid_eq_of_cast L (zero_add a.1) (sectionsMul_one_mul L a.2)
    mul_one := fun a => gradedMonoid_eq_of_cast L (add_zero a.1) (sectionsMul_mul_one L a.2)
    mul_assoc := fun a b c =>
      gradedMonoid_eq_of_cast L (add_assoc a.1 b.1 c.1) (sectionsMul_mul_assoc L a.2 b.2 c.2) }

/-- **Graded semiring structure on the section components** (`lem:sectionGradedRing_gsemiring`,
[Stacks, Tag 01CV]): for an *arbitrary* `L : X.Modules`, the family `m ↦ Γ(X, L^{⊗m})` carries a
`DirectSum.GSemiring`, so `⊕_m Γ(X, L^{⊗m})` is a semiring.  Extends `sectionGradedRing_gmonoid`
with the bilinearity clauses — the degreewise multiplication `Γ(μ_{i,j}) ∘ sectionsMul` is the
composite of the bilinear `sectionsMul` (a `TensorProduct`-based map) with the linear comparison
`Γ(μ_{i,j})`, so it annihilates `0` and distributes over `+` (via `TensorProduct.tmul_zero`/
`zero_tmul`/`tmul_add`/`add_tmul` + `map_zero`/`map_add`) — and the natural-number coercion
`n ↦ n • 1` (the `n`-fold sum of the degree-`0` unit).  No commutativity clause enters: this layer
exists for every `L` and is in general non-commutative.  Project-local infrastructure (Stacks 01CV
graded ring `⊕ Γ(X,L^{⊗n})`); the `GCommSemiring` upgrade for invertible `L` is built below
(`sectionGradedRing_gcommSemiring`). -/
@[reducible] noncomputable def sectionGradedRing_gsemiring (L : X.Modules) :
    DirectSum.GSemiring (sectionDeg L) :=
  { sectionGradedRing_gmonoid L with
    -- Bilinearity: `Γ(μ) ∘ sectionsMul` is the composite of additive maps; push `0`/`+` through
    -- the `TensorProduct` step then through the two `ModuleCat` morphisms (`erw` to cross the
    -- `ModuleCat.Hom.hom`/`DFunLike` coercion of `tensorPowAdd`/`sectionsMul`).
    mul_zero := fun a => by
      simp only [gMul_mul_apply]; erw [TensorProduct.tmul_zero, map_zero, map_zero]
    zero_mul := fun b => by
      simp only [gMul_mul_apply]; erw [TensorProduct.zero_tmul, map_zero, map_zero]
    mul_add := fun a b c => by
      simp only [gMul_mul_apply]; erw [TensorProduct.tmul_add, map_add, map_add]
    add_mul := fun a b c => by
      simp only [gMul_mul_apply]; erw [TensorProduct.add_tmul, map_add, map_add]
    natCast := fun n => n • (GradedMonoid.GOne.one : sectionDeg L 0)
    natCast_zero := by rw [zero_nsmul]
    natCast_succ := fun n => by rw [succ_nsmul] }

/-- Sanity confirmation of the deliverable (mirrors `TensorPower.Basic`'s closing `example`):
the section graded semiring assembles the genuine `Semiring` on `⊕_m Γ(X, L^{⊗m})`
(`def:sectionGradedRing`, the underlying additive structure of `Γ_*(X,L)`), obtained from the
`GSemiring` via `DirectSum.toSemiring`.  Stated as `Nonempty` to avoid registering a global
instance (the carrier family depends on `L`) and to sidestep codegen on the noncomputable term. -/
theorem sectionGradedRing_semiring_nonempty (L : X.Modules) :
    Nonempty (Semiring (DirectSum ℕ (sectionDeg L))) :=
  ⟨letI := sectionGradedRing_gsemiring L; inferInstance⟩

/-- **Action comparison isomorphism for the twisted family** (launching pad for
`lem:sectionGradedModule_gmodule`): the degree-`(i,j)` action lands `L^{⊗i} ⊗ (F ⊗ L^{⊗j})` in
`F ⊗ L^{⊗(i+j)} = moduleTensorPow F L (i+j)` by reassociating and braiding the `L^{⊗i}` factor
past `F`, then merging the two line-bundle blocks via `tensorPowAdd`.  The braiding here is between
the *distinct* objects `L^{⊗i}` and `F`, so it always exists (symmetric monoidal structure) — no
invertibility hypothesis is needed for the module layer.  Project-local. -/
noncomputable def moduleTensorPowAdd (F L : X.Modules) (i j : ℕ) :
    tensorObj (tensorPow L i) (moduleTensorPow F L j) ≅ moduleTensorPow F L (i + j) :=
  (tensorObjAssoc (tensorPow L i) F (tensorPow L j)).symm ≪≫
    tensorObjWhiskerRightIso (tensorBraiding (tensorPow L i) F) (tensorPow L j) ≪≫
    tensorObjAssoc F (tensorPow L i) (tensorPow L j) ≪≫
    tensorObjWhiskerLeftIso F (tensorPowAdd L i j)

/-! ### Trivializing-open braiding component (helpers for `tensorBraiding_self_eq_id_of_isInvertible`)

The braiding of an invertible sheaf with itself becomes the identity after sheafification.
The descent is local-to-global: on each trivializing open of the basis carried by `IsInvertible L`,
the presheaf braiding component is the `ModuleCat` braiding `TensorProduct.comm`, which is the
identity on an invertible module. -/

/-- The `ModuleCat` self-braiding hom is the concrete `TensorProduct.comm` swap (no invertibility
needed): both send `m ⊗ₜ m'` to `m' ⊗ₜ m`.  Project-local helper. -/
private lemma moduleCat_braiding_hom_eq_comm {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) :
    (β_ M M).hom = ModuleCat.ofHom (TensorProduct.comm R M M).toLinearMap := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m m'
  rfl

/-- On an **invertible** module the `ModuleCat` self-braiding is the identity, since
`TensorProduct.comm` is the identity (`Module.Invertible.tensorProductComm_eq_refl`).  The
invertibility is taken as an explicit argument so the project's `Γ(X,U)`-vs-`R.obj U`
ring-spelling is reconciled by definitional unification rather than instance search.
Project-local helper. -/
private lemma moduleCat_braiding_self_hom_eq_id {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (hM : Module.Invertible R M) :
    (β_ M M).hom = 𝟙 (M ⊗ M) := by
  haveI := hM
  rw [moduleCat_braiding_hom_eq_comm, Module.Invertible.tensorProductComm_eq_refl]
  rfl

/-- **Presheaf self-braiding is the identity on a trivializing open.**  On an open `U` where the
section module `Γ(L, U)` is an invertible `Γ(X, U)`-module, the component at `op U` of the presheaf
self-braiding of `L` is the identity.  By `PresheafOfModules.braiding_hom_app` the component is the
`ModuleCat` braiding, which is `𝟙` by `moduleCat_braiding_self_hom_eq_id`.  Project-local helper for
`tensorBraiding_self_eq_id_of_isInvertible`. -/
private lemma braiding_self_app_eq_id_of_invertible (L : X.Modules)
    (U : TopologicalSpace.Opens X)
    (h : Module.Invertible ↥(X.presheaf.obj (Opposite.op U))
                           ↥(L.val.obj (Opposite.op U))) :
    (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)).hom.app (Opposite.op U)
      = 𝟙 _ := by
  erw [PresheafOfModules.braiding_hom_app]
  exact moduleCat_braiding_self_hom_eq_id _ h

/-- **Descent equation for the self-braiding** (helper for `tensorBraiding_self_eq_id_of_isInvertible`):
the presheaf self-braiding `β^{pre}` composed with the sheafification unit equals the unit.  Both
land in a sheaf, and they agree on the trivializing basis carried by `IsInvertible L` (where
`β^{pre}` is the identity, `braiding_self_app_eq_id_of_invertible`), so they are equal by sheaf
separatedness (`TopCat.Sheaf.hom_ext`).  Project-local. -/
private lemma braiding_comp_unit_eq_unit_of_isInvertible (L : X.Modules) [IsInvertible L] :
    (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)).hom
      ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L))
      = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)) := by
  obtain ⟨ι, U, hbasis, hinv⟩ := IsInvertible.exists_trivializing_basis (L := L)
  apply (PresheafOfModules.toPresheaf _).map_injective
  refine TopCat.Sheaf.hom_ext _
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj (tensorObj L L)) hbasis ?_
  intro i
  rw [Functor.map_comp, NatTrans.comp_app]
  have hb : ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
        (BraidedCategory.braiding (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)).hom).app
          (Opposite.op (U i)) = 𝟙 _ := by
    ext x
    erw [PresheafOfModules.toPresheaf_map_app_apply]
    rw [braiding_self_app_eq_id_of_invertible L (U i) (hinv i)]
    rfl
  rw [hb, Category.id_comp]

/-- **Trivial self-braiding of an invertible sheaf** (`lem:braiding_eq_id_of_invertible`,
[Stacks, Tag 01CR]): for an invertible `L`, the braiding of `L` with itself is the identity,
`β_{L,L} = 𝟙_{L ⊗ L}`.  Equality of sheaf-of-module morphisms is local, so it suffices to
check on a trivializing cover, where `L` is free of rank one and the presheaf braiding is the
swap `TensorProduct.comm`, which is the identity on an invertible module
(`Module.Invertible.tensorProductComm_eq_refl`); descending through sheafification gives the
claim.  **Crucially the identity must NOT be checked at the global open `⊤`**: `Γ(X,L)` need
not be an invertible `Γ(X,𝒪_X)`-module, so the local-to-global route is essential.  This is the
single arithmetic input distinguishing the invertible (commutative) case; it is the consumed
ingredient of the `GCommSemiring` assembly (`sectionGradedRing_gcommSemiring`, built below). -/
lemma tensorBraiding_self_eq_id_of_isInvertible (L : X.Modules) [IsInvertible L] :
    tensorBraiding L L = Iso.refl (tensorObj L L) := by
  -- Local-to-global: the presheaf self-braiding agrees with `𝟙` after composing with the
  -- sheafification unit (`braiding_comp_unit_eq_unit_of_isInvertible`), so the sheafified braiding
  -- is the identity by unit-injectivity of the sheafification adjunction.
  apply Iso.ext
  change sheafification.map
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)).hom
    = 𝟙 (tensorObj L L)
  -- Reduce to `sheafification.map β^{pre} = 𝟙` via the adjunction hom-equivalence.
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
      ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)) (tensorObj L L) |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  -- `unit ≫ G.map (sheafification.map β^{pre}) = β^{pre} ≫ unit = unit` (descent).
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj L)).hom).symm.trans
    (braiding_comp_unit_eq_unit_of_isInvertible L)

/-- **Right-unitor = braiding-then-left-unit** (base-case helper for `tensorPowAdd_comm`): the sheaf
right unitor of `G` equals the self-braiding with the unit followed by the left-unit iso.  Descended
through sheafification from the presheaf symmetric coherence `β_{G,𝟙} ≫ λ = ρ`
(`MonoidalCategory.braiding_leftUnitor`).  Project-local. -/
private lemma tensorObjRightUnitor_eq_braiding_unit (G : X.Modules) :
    tensorObjRightUnitor G = tensorBraiding G (unitModule X) ≪≫ tensorObjUnitIso G := by
  apply Iso.ext
  change sheafification.map
        (MonoidalCategory.rightUnitor (C := MonoidalPresheaf X)
          ((toPresheafOfModules X).obj G)).hom ≫ (sheafificationCounitIso G).hom
    = sheafification.map
          (BraidedCategory.braiding (C := MonoidalPresheaf X)
            ((toPresheafOfModules X).obj G) (𝟙_ (MonoidalPresheaf X))).hom ≫
        (sheafification.map
            (MonoidalCategory.leftUnitor (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj G)).hom ≫ (sheafificationCounitIso G).hom)
  rw [← Category.assoc (sheafification.map _), ← CategoryTheory.Functor.map_comp]
  congr 2
  exact (CategoryTheory.braiding_leftUnitor _).symm

/-- **Descended forward hexagon for the sheaf braiding** (`lem:tensorBraiding_hexagon_forward`):
the hand-built braiding (`tensorBraiding`) and associator (`tensorObjAssoc`) satisfy the forward
hexagon identity, mirroring `CategoryTheory.BraidedCategory.hexagon_forward` of the inherited
symmetric structure.  Proved by rewriting every hand-built construct to its canonical counterpart
conjugated by the bridge `tensorObjIso` (`tensorBraiding_eq`, `tensorObjAssoc` def,
`tensorObjWhiskerRightIso_eq`, `tensorObjWhiskerLeftIso_eq`); the bridges telescope in inverse pairs,
leaving the canonical hexagon.  Project-local; consumed by the succ case of `tensorPowAdd_comm`. -/
private lemma tensorBraiding_hexagon_forward (F A B : X.Modules) :
    tensorObjAssoc F A B ≪≫ tensorBraiding F (tensorObj A B) ≪≫ tensorObjAssoc A B F
      = tensorObjWhiskerRightIso (tensorBraiding F A) B ≪≫ tensorObjAssoc A F B ≪≫
          tensorObjWhiskerLeftIso A (tensorBraiding F B) := by
  rw [tensorBraiding_eq, tensorBraiding_eq, tensorBraiding_eq,
    tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq]
  apply Iso.ext
  simp only [tensorObjAssoc, Iso.trans_hom, Iso.symm_hom,
    MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [BraidedCategory.hexagon_forward_assoc]
  simp only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc]

/-- **Symmetry of the hand-built braiding**: `β_{A,B} ≪≫ β_{B,A} = 𝟙`.  Descended from the symmetric
structure on `X.Modules` (`SymmetricCategory.symmetry`) through the bridge `tensorBraiding_eq`; the
inner `tensorObjIso B A` pair telescopes and the canonical symmetry collapses the braiding pair.
Project-local; consumed by the succ case of `tensorPowAdd_comm` and `tensorPowAdd_succ_left_braided`. -/
private lemma tensorBraiding_symm (A B : X.Modules) :
    tensorBraiding A B ≪≫ tensorBraiding B A = Iso.refl (tensorObj A B) := by
  apply Iso.ext
  rw [tensorBraiding, tensorBraiding]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
  have hsymm : (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B)).hom ≫
      (BraidedCategory.braiding (C := MonoidalPresheaf X)
        ((toPresheafOfModules X).obj B) ((toPresheafOfModules X).obj A)).hom = 𝟙 _ :=
    SymmetricCategory.symmetry (C := MonoidalPresheaf X) _ _
  exact (sheafification.map_comp _ _).symm.trans
    ((congrArg sheafification.map hsymm).trans (sheafification.map_id _))

/-- **Canonical self-braiding of an invertible sheaf is the identity** (named sub-brick): the
*canonical* symmetric-monoidal braiding `β_ L L` of `X.Modules` is the identity on `L ⊗ L`.  This
is the canonical-level image of the hand-built PRIMARY `tensorBraiding_self_eq_id_of_isInvertible`,
read off through the bridge `tensorBraiding_eq`.  Project-local; the β-collapse input to the succ
case of `tensorPowAdd_succ_left_braided` and the succ case of `tensorPowAdd_comm`. -/
private lemma braiding_canonical_self_eq_id_of_isInvertible (L : X.Modules) [IsInvertible L] :
    (β_ L L).hom = 𝟙 (L ⊗ L) := by
  have h := congrArg Iso.hom (tensorBraiding_eq L L)
  rw [tensorBraiding_self_eq_id_of_isInvertible] at h
  simp only [Iso.refl_hom, Iso.trans_hom, Iso.symm_hom] at h
  -- `h : 𝟙 = (tensorObjIso L L).inv ≫ (β_ L L).hom ≫ (tensorObjIso L L).hom`.
  rw [eq_comm, Iso.inv_comp_eq] at h
  -- `h : (β_ L L).hom ≫ (tensorObjIso L L).hom = (tensorObjIso L L).hom`.
  exact (cancel_mono (tensorObjIso L L).hom).mp (h.trans (Category.id_comp _).symm)

/-- **First-index successor recursion of the tensor-power comparison** (`lem:tensorPowAdd_succ_left`):
the comparison `μ_{c+1,m}` is recovered from the lower comparison `μ_{c,1+m}` by peeling the
freshly-added factor to the left, the first-index dual of the (second-index) definitional succ
clause `tensorPowAdd_succ`.  Braiding-free and valid for arbitrary `L`.  Obtained by solving the
B6 pentagon `tensorPowAdd_assoc` at indices `(c,1,m)` for `μ_{c+1,m}` — inverting the right-unit
whisker `μ_{c,1} ▷ L^m`.  Project-local; consumed by the succ case of `tensorPowAdd_comm`. -/
private lemma tensorPowAdd_succ_left (L : X.Modules) (c m : ℕ) :
    tensorPowAdd L (c + 1) m ≪≫ eqToIso (congrArg (tensorPow L) (add_assoc c 1 m)) =
      (tensorObjWhiskerRightIso (tensorPowAdd L c 1) (tensorPow L m)).symm ≪≫
        tensorObjAssoc (tensorPow L c) (tensorPow L 1) (tensorPow L m) ≪≫
        tensorObjWhiskerLeftIso (tensorPow L c) (tensorPowAdd L 1 m) ≪≫
        tensorPowAdd L c (1 + m) := by
  apply Iso.ext
  have hh := congrArg Iso.hom (tensorPowAdd_assoc L c 1 m)
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom] at hh ⊢
  rw [Iso.eq_inv_comp]
  exact hh

/-- **Generic-`M` core of the succ-case canonical hexagon residual of `tensorPowAdd_succ_left_braided`
(brick 1′).**  Stated over an arbitrary monoidal category `M` so that all `≫`/`▷`/`◁`/`α_` resolve to a
single uniform instance (no `LocalizedMonoidal`/`X.Modules` comp-instance diamond), making the
`(…) ▷ l` / `a ◁ (…)` whisker distributions fire and the adjacent bridge `hom`/`inv` pairs (`iA1k'`,
`ilK1`, `iaK1`) cancel.  After distribution the structural associators + the two opaque atoms `β`, `μ`
sit in naturality-compatible positions; `hk` reconciles the trailing reindex bridges
(`r1 ▷ l ≫ iT1 = iT2 ≫ r2`), then `monoidal` closes.  Plugged in by `exact` (the instance diamond is
`rfl`-defeq, so `exact`'s `isDefEq` bridges it).  Braided analogue of `tensorPowAdd_assoc_succ_core`
(no `foldhyp`: the inductive hypothesis is already substituted at iso level). -/
private lemma tensorPowAdd_succ_left_braided_core
    {M : Type*} [Category M] [MonoidalCategory M]
    {a l k' K1 A1 Plk' Pak' ck Pckl T1 PT1l PlK1 PK1l PaK1 PT2l PA1K1 PA1k' : M}
    (iA1K1 : A1 ⊗ K1 ≅ PA1K1) (i2 : k' ⊗ l ≅ K1) (iA1k' : A1 ⊗ k' ≅ PA1k')
    (ial : a ⊗ l ≅ A1) (ilk' : l ⊗ k' ≅ Plk') (iak' : a ⊗ k' ≅ Pak')
    (ickl : ck ⊗ l ≅ Pckl) (iT1 : T1 ⊗ l ≅ PT1l) (ilK1 : l ⊗ K1 ≅ PlK1)
    (iK1l : K1 ⊗ l ≅ PK1l) (iaK1 : a ⊗ K1 ≅ PaK1) (iT2 : Pckl ⊗ l ≅ PT2l)
    (β : Plk' ⟶ K1) (μ : Pak' ⟶ ck) (r1 : Pckl ⟶ T1) (r2 : PT2l ⟶ PT1l)
    (hk : r1 ▷ l ≫ iT1.hom = iT2.hom ≫ r2) :
    iA1K1.inv ≫ A1 ◁ i2.inv ≫ (α_ A1 k' l).inv ≫ iA1k'.hom ▷ l ≫
        (iA1k'.inv ≫ ial.inv ▷ k' ≫ (α_ a l k').hom ≫ a ◁ ilk'.hom ≫ a ◁ β ≫ a ◁ i2.inv ≫
          (α_ a k' l).inv ≫ iak'.hom ▷ l ≫ μ ▷ l ≫ ickl.hom ≫ r1) ▷ l ≫ iT1.hom
      = iA1K1.inv ≫ ial.inv ▷ K1 ≫ (α_ a l K1).hom ≫ a ◁ ilK1.hom ≫
        a ◁ (ilK1.inv ≫ l ◁ i2.inv ≫ (α_ l k' l).inv ≫ ilk'.hom ▷ l ≫ β ▷ l ≫ iK1l.hom) ≫
        a ◁ iK1l.inv ≫ (α_ a K1 l).inv ≫ iaK1.hom ▷ l ≫
        (iaK1.inv ≫ a ◁ i2.inv ≫ (α_ a k' l).inv ≫ iak'.hom ▷ l ≫ μ ▷ l ≫ ickl.hom) ▷ l ≫
        iT2.hom ≫ r2 := by
  simp only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [hk]
  rw [← MonoidalCategory.associator_inv_naturality_left_assoc]
  simp only [Category.assoc, MonoidalCategory.whisker_assoc, MonoidalCategory.whisker_exchange_assoc]
  monoidal

/-- **Order-reversing first-index successor recursion** (`lem:tensorPowAdd_succ_left_braided`,
brick 1′): for an invertible `L`, the comparison `μ_{c+1,m}` is recovered from the *lower* comparison
`μ_{c,m}` by braiding the freshly-added left factor `L` past the block `L^{⊗m}` and applying
`μ_{c,m}` on the right, framed by associators.  Unlike the order-*preserving*
`tensorPowAdd_succ_left` (which surfaces opaque non-matching atoms), this surfaces exactly `μ_{c,m}`
demanded by the inductive hypothesis of `tensorPowAdd_comm`, at the cost of a genuine braiding
`β_{L,L^m}`; hence invertibility (consumed as `β_{L,L} = 𝟙`) enters here.  Proved by its own
induction on `m` (braided analogue of the `tensorPowAdd_assoc` pentagon).  Project-local. -/
private lemma tensorPowAdd_succ_left_braided (L : X.Modules) [IsInvertible L] (c m : ℕ) :
    tensorPowAdd L (c + 1) m =
      tensorObjAssoc (tensorPow L c) L (tensorPow L m) ≪≫
        tensorObjWhiskerLeftIso (tensorPow L c) (tensorBraiding L (tensorPow L m)) ≪≫
        (tensorObjAssoc (tensorPow L c) (tensorPow L m) L).symm ≪≫
        tensorObjWhiskerRightIso (tensorPowAdd L c m) L ≪≫
        eqToIso (congrArg (tensorPow L) (show c + m + 1 = c + 1 + m by omega)) := by
  induction m with
  | zero =>
    have hbu : tensorBraiding L (tensorPow L 0)
        = tensorObjRightUnitor L ≪≫ (tensorObjUnitIso L).symm := by
      rw [tensorObjRightUnitor_eq_braiding_unit L]; simp
    rw [tensorPowAdd_zero_right, tensorPowAdd_zero_right, hbu]
    apply Iso.ext
    simp only [tensorPow_zero, tensorObjRightUnitor_eq, tensorObjUnitIso_eq,
      tensorObjWhiskerLeftIso_eq, tensorObjWhiskerRightIso_eq, tensorObjAssoc, Iso.trans_hom,
      Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, MonoidalCategory.whiskerLeftIso_hom,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_inv,
      MonoidalCategory.whiskerRightIso_inv, eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    simp
    -- Clean canonical goal: `ρ_(L^c⊗L) = (bridge.inv ▷ 𝟙) ≫ [canonical coherence = ρ] ≫ bridge.hom`.
    -- Reassociate, pull the trailing bridge to the left, apply right-unitor naturality to fold the
    -- leading `bridge.inv ▷ 𝟙` into `ρ`, then the residual canonical coherence closes by `monoidal`.
    simp only [← Category.assoc]
    rw [← Iso.comp_inv_eq, ← MonoidalCategory.rightUnitor_naturality]
    simp only [Category.assoc]
    congr 1
    monoidal
  | succ k ih =>
    rw [tensorPowAdd_succ, ih]
    rw [show tensorPowAdd L c (k + 1) = (tensorObjAssoc (tensorPow L c) (tensorPow L k) L).symm ≪≫
        tensorObjWhiskerRightIso (tensorPowAdd L c k) L from tensorPowAdd_succ L c k]
    -- INVERTIBILITY-COLLAPSED hexagon split of `β_{L, L^k ⊗ L}` (`L^{k+1} = L^k ⊗ L` by `rfl`).
    -- The forward hexagon (brick 2) gives `β_{L,A⊗L} = α⁻¹ ≪≫ WR(β_{L,A}) L ≪≫ α ≪≫ WL_A(β_{L,L}) ≪≫ α⁻¹`;
    -- when `L` is invertible, `β_{L,L} = 𝟙` (PRIMARY) makes `WL_A(β_{L,L}) = 𝟙` and the `α ≪≫ α⁻¹` pair
    -- collapses, leaving the clean `β_{L,A⊗L} = α⁻¹ ≪≫ WR(β_{L,A}) L`.
    have hwlrefl : tensorObjWhiskerLeftIso (tensorPow L k) (Iso.refl (tensorObj L L))
        = Iso.refl (tensorObj (tensorPow L k) (tensorObj L L)) := by
      apply Iso.ext
      simp only [tensorObjWhiskerLeftIso_eq, Iso.refl_hom, Iso.trans_hom, Iso.symm_hom,
        MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp,
        Iso.inv_hom_id]
    have hβ' : tensorBraiding L (tensorObj (tensorPow L k) L)
        = (tensorObjAssoc L (tensorPow L k) L).symm ≪≫
            tensorObjWhiskerRightIso (tensorBraiding L (tensorPow L k)) L := by
      have hhex := tensorBraiding_hexagon_forward L (tensorPow L k) L
      rw [tensorBraiding_self_eq_id_of_isInvertible, hwlrefl, Iso.trans_refl] at hhex
      -- hhex : α ≪≫ tB ≪≫ α' = WR(β) L ≪≫ α'
      apply Iso.ext
      have hb := congrArg Iso.hom hhex
      simp only [Iso.trans_hom] at hb
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [Iso.eq_inv_comp]
      -- goal: α.hom ≫ tB.hom = WR.hom ; from hb cancel trailing α'.hom
      exact (cancel_mono (tensorObjAssoc (tensorPow L k) L L).hom).mp (by
        simpa only [Category.assoc] using hb)
    rw [show tensorBraiding L (tensorPow L (k + 1))
        = tensorBraiding L (tensorObj (tensorPow L k) L) from rfl, hβ']
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorObjAssoc,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
      MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
      eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    refine tensorPowAdd_succ_left_braided_core
      (M := LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?hk
    -- `hk`: reindex reconciliation `eqToHom ▷ L ≫ μ_bridge_{c+1+k} = μ_bridge_{c+(k+1)} ≫ eqToHom`,
    -- the naturality of the tensor-power bridge family along `c+1+k = c+(k+1)`; proof-irrelevance lets
    -- the constructed `eqToHom`s match the goal's anonymous reindexers.
    have gen : ∀ {n1 n2 : ℕ} (hn : n1 = n2),
        eqToHom (congrArg (L.tensorPow) hn.symm) ▷ L ≫ ((L.tensorPow n1).tensorObjIso L).hom
          = ((L.tensorPow n2).tensorObjIso L).hom ≫
              eqToHom (congrArg (fun n => (L.tensorPow n).tensorObj L) hn.symm) := by
      rintro n1 n2 rfl
      simp
    exact gen (show c + 1 + k = c + (k + 1) from by omega)

/-- **Generic-`M` core of the succ-case canonical hexagon residual of `tensorPowAdd_comm`.**  Stated
over an arbitrary monoidal category `M` (single comp instance, no `LocalizedMonoidal`/`X.Modules`
diamond at the `μ_{c+1,m}`-substitution junction).  After substituting brick 1′ for `μ_{c+1,m}`, the
two halves' bridge `hom`/`inv` pairs telescope and the opposite braidings `βm1`, `β1m` (= `β_{L^m,L}`,
`β_{L,L^m}`) collapse via the symmetry hypothesis `hsymm` (`βm1 ≫ β1m = 𝟙`); `hk` reconciles the
reindex bridges, and `monoidal` closes.  Plugged in by `exact`.  Reindex/symmetry analogue of
`tensorPowAdd_succ_left_braided_core`. -/
private lemma tensorPowAdd_comm_succ_core
    {M : Type*} [Category M] [MonoidalCategory M]
    {mm a l Pal Pmc Pcm Pm1 P1m Pcm_sum Pmc_sum Pfin
      Qmtcl QmcL QcmL Qtclm : M}
    (imtcl : mm ⊗ Pal ≅ Qmtcl) (icl : a ⊗ l ≅ Pal) (imc : mm ⊗ a ≅ Pmc)
    (imcL : Pmc_sum ⊗ l ≅ QmcL) (icm : a ⊗ mm ≅ Pcm) (im1 : mm ⊗ l ≅ Pm1)
    (i1m : l ⊗ mm ≅ P1m) (itclm : Pal ⊗ mm ≅ Qtclm) (icmL : Pcm_sum ⊗ l ≅ QcmL)
    (βmc : Pmc ⟶ Pcm) (βm1 : Pm1 ⟶ P1m) (β1m : P1m ⟶ Pm1) (μ : Pcm ⟶ Pcm_sum)
    (r0 : Pcm_sum ⟶ Pmc_sum) (r2 : QcmL ⟶ Pfin) (rfinal : Pfin ⟶ QmcL)
    (hsymm : βm1 ≫ β1m = 𝟙 Pm1)
    (hk : r0 ▷ l ≫ imcL.hom = icmL.hom ≫ r2 ≫ rfinal) :
    imtcl.inv ≫ mm ◁ icl.inv ≫ (α_ mm a l).inv ≫ imc.hom ▷ l ≫ βmc ▷ l ≫ μ ▷ l ≫ r0 ▷ l ≫ imcL.hom
      = (imtcl.inv ≫ mm ◁ icl.inv ≫ (α_ mm a l).inv ≫ imc.hom ▷ l ≫ βmc ▷ l ≫ icm.inv ▷ l ≫
            (α_ a mm l).hom ≫ a ◁ im1.hom ≫ a ◁ βm1 ≫ a ◁ i1m.inv ≫ (α_ a l mm).inv ≫
            icl.hom ▷ mm ≫ itclm.hom) ≫
          (itclm.inv ≫ icl.inv ▷ mm ≫ (α_ a l mm).hom ≫ a ◁ i1m.hom ≫ a ◁ β1m ≫ a ◁ im1.inv ≫
            (α_ a mm l).inv ≫ icm.hom ▷ l ≫ μ ▷ l ≫ icmL.hom ≫ r2) ≫ rfinal := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc, MonoidalCategory.inv_hom_whiskerRight_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, reassoc_of% hsymm, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [hk]

set_option backward.isDefEq.respectTransparency false in
/-- **Commutativity constraint of the tensor-power comparison** (`lem:tensorPowAdd_comm`): for an
invertible `L`, the comparison family is symmetric, `μ_{m,m'} = β_{L^m,L^m'} ≫ μ_{m',m}` after
the reindexing `m' + m = m + m'`.  The invertibility hypothesis is essential — for a general
sheaf the two sides realise different permutations of the `m + m'` identical `L`-factors; already
at `m = m' = 1` it reduces to `β_{L,L} = 𝟙` (`tensorBraiding_self_eq_id_of_isInvertible`).
Invertibility-gated; consumed by `sectionsMul_mul_comm` / `sectionGradedRing_gcommSemiring`. -/
lemma tensorPowAdd_comm (L : X.Modules) [IsInvertible L] (m m' : ℕ) :
    tensorPowAdd L m m' =
      tensorBraiding (tensorPow L m) (tensorPow L m') ≪≫ tensorPowAdd L m' m ≪≫
        eqToIso (congrArg (tensorPow L) (Nat.add_comm m' m)) := by
  -- Induction on the second index `m'`, mirroring the recursion of `μ = tensorPowAdd`.
  induction m' with
  | zero =>
    -- Base `m' = 0`: `μ_{m,0} = ρ_{L^m}` (`tensorPowAdd_zero_right`), and the RHS is
    -- `β_{L^m,𝟙} ≫ μ_{0,m} ≫ reindex = β ≫ λ ≫ reindex`.  The braiding-unit coherence
    -- `tensorObjRightUnitor_eq_braiding_unit` makes `ρ = β ≫ λ`; the trailing `eqToIso`s along
    -- `m = 0 + m = m + 0` collapse to the identity.
    rw [tensorPowAdd_zero_right, tensorObjRightUnitor_eq_braiding_unit, tensorPowAdd_zero_left]
    apply Iso.ext
    simp only [Iso.trans_hom, eqToIso.hom]
    congr 1
    simp
  | succ c ih =>
    -- Succ `m' = c + 1`: the braided analogue of the `tensorPowAdd_assoc` pentagon (CLOSED iter-031).
    -- Unfold the LHS by the 2nd-index succ clause + `ih`, split the RHS braiding `β_{L^m, L^{c+1}}`
    -- (`L^{c+1} = L^c ⊗ L`) by the descended hexagon `hβ`, distribute the LHS right-whisker, then
    -- substitute brick 1′ (`tensorPowAdd_succ_left_braided`) for `μ_{c+1,m}`.  The shared prefix
    -- `α⁻¹_{L^m,L^c,L} ≪≫ WR(β_{L^m,L^c}) L` agrees on both sides; after descending to canonical the
    -- opposite braidings `β_{L^m,L}`, `β_{L,L^m}` collapse by symmetry (`tensorBraiding_symm`) and the
    -- residual is a reindex identity — discharged by the generic-`M` core `tensorPowAdd_comm_succ_core`
    -- (which dissolves the `μ_{c+1,m}`-substitution comp-instance diamond).  Everything downstream
    -- (`sectionsMul_mul_comm`, `sectionGradedRing_gcommSemiring`) consumes `tensorPowAdd_comm`.
    rw [tensorPowAdd_succ, ih]
    have hβ : (L.tensorPow m).tensorBraiding (tensorObj (L.tensorPow c) L) =
        ((L.tensorPow m).tensorObjAssoc (L.tensorPow c) L).symm ≪≫
          (tensorObjWhiskerRightIso ((L.tensorPow m).tensorBraiding (L.tensorPow c)) L ≪≫
            (L.tensorPow c).tensorObjAssoc (L.tensorPow m) L ≪≫
            tensorObjWhiskerLeftIso (L.tensorPow c) ((L.tensorPow m).tensorBraiding L)) ≪≫
          ((L.tensorPow c).tensorObjAssoc L (L.tensorPow m)).symm := by
      apply Iso.ext
      have hb := congrArg Iso.hom (tensorBraiding_hexagon_forward (L.tensorPow m) (L.tensorPow c) L)
      simp only [Iso.trans_hom] at hb
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [Iso.eq_inv_comp, Iso.eq_comp_inv]
      simp only [Category.assoc]
      exact hb
    rw [show (L.tensorPow m).tensorBraiding (L.tensorPow (c + 1))
        = (L.tensorPow m).tensorBraiding (tensorObj (L.tensorPow c) L) from rfl]
    rw [hβ]
    simp only [tensorObjWhiskerRightIso_trans]
    rw [tensorPowAdd_succ_left_braided L c m]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorObjAssoc,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
      MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
      eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    refine tensorPowAdd_comm_succ_core
      (M := LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?hsymm ?hk
    · -- `hsymm`: opposite self-braidings cancel (symmetry `β_{L^m,L} ≫ β_{L,L^m} = 𝟙`).
      have h := congrArg Iso.hom (tensorBraiding_symm (L.tensorPow m) L)
      simp only [Iso.trans_hom, Iso.refl_hom] at h
      exact h
    · -- `hk`: reindex reconciliation of the trailing tensor-power bridge family.
      have gen : ∀ {n1 n2 : ℕ} (hn : n1 = n2),
          eqToHom (congrArg (L.tensorPow) hn.symm) ▷ L ≫ ((L.tensorPow n1).tensorObjIso L).hom
            = ((L.tensorPow n2).tensorObjIso L).hom ≫
                eqToHom (congrArg (fun n => (L.tensorPow n).tensorObj L) hn.symm) := by
        rintro n1 n2 rfl
        simp
      convert gen (show m + c = c + m from by omega) using 2
      exact eqToHom_trans _ _

/-- Section-level functoriality of a composite of `X.Modules` isos at the top open: evaluating the
`.hom` of a composite `f ≪≫ g` on a section is the composite of the two evaluations.  Project-local
helper used to read off the iso-level `tensorPowAdd_comm` on elements. -/
private lemma iso_trans_hom_val_app_apply {A B C : X.Modules} (f : A ≅ B) (g : B ≅ C)
    (z : ↥(A.val.obj (Opposite.op ⊤))) :
    ((f ≪≫ g).hom.val.app (Opposite.op ⊤)).hom z
      = (g.hom.val.app (Opposite.op ⊤)).hom ((f.hom.val.app (Opposite.op ⊤)).hom z) := by
  rw [Iso.trans_hom]
  rfl

/-- Commutativity of the graded section multiplication (`lem:sectionMul_coherent`, commutativity):
transporting `a · b` along `na + nb = nb + na` gives `b · a`.
Section-level analogue of the `mul_comm` in `TensorPower.Basic`.

**Invertibility-gated (iter-011 re-anchor).**  For an *arbitrary* `L : X.Modules` this statement
is FALSE — the section graded ring is the free tensor algebra on `Γ(X,L)`, which is
non-commutative (counterexample `L = 𝒪_X²`); [Stacks, Tag, §17.25].  It becomes TRUE exactly when
`L` is invertible (`IsInvertible L`, [Stacks, Tag 01CR]), the line-bundle case relevant to
`Γ_*(X,𝓛)`.  The single arithmetic input is the trivial self-braiding `β_{L,L} = 𝟙`
(`tensorBraiding_self_eq_id_of_isInvertible`, axiom-clean).  **COMPLETE (iter-031), axiom-clean** —
the iso-level commutativity constraint `tensorPowAdd_comm` is read off on the base element
`x = sectionsMul (L^na)(L^nb)(a ⊗ₜ b)` (the element-level `congrArg`/cast-cancellation pattern of B7
`sectionsMul_mul_assoc`). -/
theorem sectionsMul_mul_comm (L : X.Modules) [IsInvertible L] {na nb : ℕ}
    (a : sectionDeg L na) (b : sectionDeg L nb) :
    sectionsCast L (add_comm na nb) (GradedMonoid.GMul.mul a b) =
    GradedMonoid.GMul.mul b a := by
  -- Unfold the degreewise multiplication on both sides to `Γ(μ) ∘ sectionsMul`.
  simp only [gMul_mul_apply]
  -- Push the proven section-level braiding naturality `tensorBraiding_hom_sectionsMul` into RHS:
  -- it rewrites `sectionsMul (L^nb) (L^na) (b ⊗ₜ a)` as `Γ(β)(sectionsMul (L^na) (L^nb) (a ⊗ₜ b))`,
  -- collapsing both sides to the single element `x := sectionsMul (L^na) (L^nb) (a ⊗ₜ b)`.
  rw [← tensorBraiding_hom_sectionsMul (tensorPow L na) (tensorPow L nb) a b]
  -- The residual goal is the section-level *commutativity constraint* of the comparison family:
  --   `sectionsCast (add_comm na nb) (Γ(μ_{na,nb}) x) = Γ(μ_{nb,na}) (Γ(tensorBraiding (L^na)(L^nb)) x)`,
  -- i.e. the iso-level identity `μ_{na,nb} ≫ eqToHom = tensorBraiding (L^na)(L^nb) ≫ μ_{nb,na}`
  -- (`lem:tensorPowAdd_comm`) read off on `x`.
  --
  -- ⚠ MATHEMATICAL OBSTACLE (genuine, not a difficulty): this residual identity — and hence
  -- `sectionsMul_mul_comm` as stated for an ARBITRARY `L : X.Modules` — is FALSE.  It forces
  -- `tensorBraiding (L^m) (L^n) ≫ μ_{n,m} = μ_{m,n}` (mod reindex); for `m = n = 1` this reduces to
  -- `β_{L,L} = 𝟙`, which holds iff `L` is invertible (rank ≤ 1).  For non-invertible `L`
  -- (e.g. `L = 𝒪_X²`, rank 2) the graded object `⊕ₘ Γ(L^{⊗m})` is the *free tensor algebra* on
  -- `Γ(L)`, which is non-commutative, so no proof exists without `sorryAx`.  The blueprint claim
  -- (`lem:tensorPowAdd_comm`) that "Mac Lane coherence for the symmetric structure discharges the
  -- hexagon" is incorrect: `μ_{m,n}` and `μ_{n,m} ≫ β` induce *different* permutations of the
  -- `m+n` identical `L`-factors, so symmetric-monoidal coherence does NOT equate them.  The
  -- statement becomes true (and provable from this reduction + `tensorBraiding_hom_sectionsMul`)
  -- once an invertibility hypothesis on `L` is added — equivalently once `β_{L,L} = 𝟙` is available.
  -- Rewrite the LHS comparison via `tensorPowAdd_comm` and cancel the reindexing casts.
  rw [tensorPowAdd_comm L na nb, iso_trans_hom_val_app_apply, iso_trans_hom_val_app_apply,
    ← sectionsCast_apply, sectionsCast_sectionsCast]
  exact Nat.add_comm nb na

/-- **Graded commutative semiring structure for an invertible line bundle**
(`lem:sectionGradedRing_gcommSemiring`, [Stacks, Tag 01CV] commutative case): when `L` is invertible
(`IsInvertible L`, [Stacks, Tag 01CR]), the section graded semiring `⊕_m Γ(X, L^{⊗m})` is *graded
commutative* — `a · b = b · a` after the reindexing `i + j = j + i`.  Extends
`sectionGradedRing_gsemiring` with the single graded `mul_comm` clause, supplied by the iso-level
commutativity constraint `tensorPowAdd_comm` read off on sections (`sectionsMul_mul_comm`) and routed
through `gradedMonoid_eq_of_cast`.  Invertibility is essential: for general `L` the section ring is
the free tensor algebra on `Γ(X,L)`, which is non-commutative (see `sectionsMul_mul_comm`).
Project-local: Mathlib has no graded commutative semiring on sheaf-section tensor powers. -/
@[reducible] noncomputable def sectionGradedRing_gcommSemiring (L : X.Modules) [IsInvertible L] :
    DirectSum.GCommSemiring (sectionDeg L) :=
  { sectionGradedRing_gsemiring L with
    mul_comm := fun a b =>
      gradedMonoid_eq_of_cast L (add_comm a.1 b.1) (sectionsMul_mul_comm L a.2 b.2) }

/-- Sanity confirmation of the commutative deliverable: for invertible `L`, the section graded
commutative semiring assembles a genuine `CommSemiring` on `⊕_m Γ(X, L^{⊗m})` (the commutative
`Γ_*(X,𝓛)`), via `DirectSum.toCommSemiring`.  Stated as `Nonempty` (the carrier family depends on
`L`; sidesteps codegen on the noncomputable term). -/
theorem sectionGradedRing_commSemiring_nonempty (L : X.Modules) [IsInvertible L] :
    Nonempty (CommSemiring (DirectSum ℕ (sectionDeg L))) :=
  ⟨letI := sectionGradedRing_gcommSemiring L; inferInstance⟩

/-! ## Project-local Mathlib supplement — SNAP-S1 graded module `M(X,L,F)=⊕_m Γ(F⊗L^{⊗m})` -/

/-- **SNAP-S1 module hexagon** (`lem:moduleTensorPowAdd_assoc`): the associativity coherence for the
graded-module structure `M(X,L,F)=⊕_m Γ(F⊗L^{⊗m})`.  Project-local.  Genuine braided hexagon
(`β_{L^i,F}` does not collapse since `F` need not be invertible). -/
private lemma moduleTensorPowAdd_assoc (F L : X.Modules) (i j k : ℕ) :
    tensorObjWhiskerRightIso (tensorPowAdd L i j) (moduleTensorPow F L k) ≪≫
        moduleTensorPowAdd F L (i + j) k ≪≫
        eqToIso (congrArg (moduleTensorPow F L) (add_assoc i j k))
      = tensorObjAssoc (tensorPow L i) (tensorPow L j) (moduleTensorPow F L k) ≪≫
        tensorObjWhiskerLeftIso (tensorPow L i) (moduleTensorPowAdd F L j k) ≪≫
        moduleTensorPowAdd F L i (j + k) := by
  apply Iso.ext
  simp only [moduleTensorPowAdd, moduleTensorPow, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv,
    tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorBraiding_eq, tensorObjAssoc,
    MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
    eqToIso.hom, Category.assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc]
  have hp := congrArg Iso.hom (tensorPowAdd_assoc L i j k)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorObjAssoc,
    MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
    eqToIso.hom, Category.assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc] at hp
  -- (1) slide μ_{i,j} to the F-side; β_{L^{i+j},F} → β_{tensorObj L^i L^j,F}
  rw [← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_inv_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left]
  rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.whisker_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc]
  -- (2) inject pentagon under F ◁
  have hp' := (cancel_epi (((L.tensorPow i).tensorObj (L.tensorPow j)).tensorObjIso
    (L.tensorPow k)).inv).mp hp
  have hgen : ∀ {n1 n2 : ℕ} (hn : n1 = n2),
      (F.tensorObjIso (L.tensorPow n1)).hom ≫
          eqToHom (congrArg (fun n => F.tensorObj (L.tensorPow n)) hn)
        = F ◁ eqToHom (congrArg (L.tensorPow) hn) ≫ (F.tensorObjIso (L.tensorPow n2)).hom := by
    rintro n1 n2 rfl; simp
  rw [hgen (add_assoc i j k), ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [hp']
  -- (3) β_{tensorObj L^i L^j,F} → canonical β_{L^i⊗L^j,F}, then split via hexagon_reverse
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.associator_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    ← BraidedCategory.braiding_naturality_left, MonoidalCategory.comp_whiskerRight_assoc]
  have hhex : (β_ (L.tensorPow i ⊗ L.tensorPow j) F).hom
      = (α_ (L.tensorPow i) (L.tensorPow j) F).hom ≫
          (L.tensorPow i ◁ (β_ (L.tensorPow j) F).hom ≫
            (α_ (L.tensorPow i) F (L.tensorPow j)).inv ≫ (β_ (L.tensorPow i) F).hom ▷ L.tensorPow j)
          ≫ (α_ F (L.tensorPow i) (L.tensorPow j)).hom := by
    rw [← BraidedCategory.hexagon_reverse]
    simp
  rw [hhex]
  -- (4) Both legs differ from coherence by TWO interchanges of atoms on disjoint factors:
  --   (T1) the top swap of `T_{F,c}⁻¹` (whiskerLeft on `F⊗Lᵏ`) with `T_{a,b}⁻¹` (whiskerRight on
  --        `Lⁱ⊗Lʲ`), and (T2) `β_a = β_{Lⁱ,F}` past the inner merge `T_{b,c} ; μ_{j,k}`.
  --   `monoidal` does coherence but not interchange of two non-structural atoms, so we do both
  --   by hand (associator-naturality to expose the `(·⊗·)◁` form, then `whisker_exchange`),
  --   then `monoidal`.
  -- (T1) swap T_{F,c}⁻¹ before T_{a,b}⁻¹ on the RHS leg.
  rw [← MonoidalCategory.associator_naturality_right_assoc (L.tensorPow i) (L.tensorPow j)
        ((F.tensorObjIso (L.tensorPow k)).inv),
      ← MonoidalCategory.whisker_exchange_assoc ((L.tensorPow i).tensorObjIso (L.tensorPow j)).inv
        ((F.tensorObjIso (L.tensorPow k)).inv)]
  -- (T2) reassociate `L^i ◁ F ◁ _` (RHS leg) into `(L^i ⊗ F) ◁ _`, then slide β_a leftward past
  -- `μ_{j,k}` and `T_{b,c}` by interchange.
  rw [MonoidalCategory.associator_inv_naturality_right_assoc (L.tensorPow i) F
        (L.tensorPowAdd j k).hom,
      MonoidalCategory.associator_inv_naturality_right_assoc (L.tensorPow i) F
        ((L.tensorPow j).tensorObjIso (L.tensorPow k)).hom,
      MonoidalCategory.whisker_exchange_assoc (β_ (L.tensorPow i) F).hom (L.tensorPowAdd j k).hom,
      MonoidalCategory.whisker_exchange_assoc (β_ (L.tensorPow i) F).hom
        ((L.tensorPow j).tensorObjIso (L.tensorPow k)).hom]
  monoidal

private lemma moduleTensorPowAdd_zero_left (F L : X.Modules) (k : ℕ) :
    moduleTensorPowAdd F L 0 k = tensorObjUnitIso (moduleTensorPow F L k) ≪≫
      eqToIso (congrArg (moduleTensorPow F L) (Nat.zero_add k).symm) := by
  apply Iso.ext
  simp only [moduleTensorPowAdd, moduleTensorPow, tensorPowAdd_zero_left, tensorPow_zero,
    tensorObjUnitIso_eq, tensorObjWhiskerRightIso_eq, tensorObjWhiskerLeftIso_eq, tensorBraiding_eq,
    tensorObjAssoc, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.whiskerRightIso_inv, MonoidalCategory.whiskerLeftIso_inv,
    eqToIso.hom, Category.assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc]
  -- The reindexing slide for the `F ◁ eqToHom`/`tensorObjIso` family (mirror of the (A)-hexagon
  -- `hgen`): fuse `F ◁ eqToHom ≫ T'.hom` into `T.hom ≫ eqToHom`.
  have hgen : ∀ {n1 n2 : ℕ} (hn : n1 = n2),
      (F.tensorObjIso (L.tensorPow n1)).hom ≫
          eqToHom (congrArg (fun n => F.tensorObj (L.tensorPow n)) hn)
        = F ◁ eqToHom (congrArg (L.tensorPow) hn) ≫ (F.tensorObjIso (L.tensorPow n2)).hom := by
    rintro n1 n2 rfl; simp
  -- The middle unit-coherence square, stated over the canonical unit `𝟙_` so that
  -- `braiding_tensorUnit_left` + `monoidal` fire (they special-case `𝟙_`, not `unitModule X`); then
  -- transported to the `unitModule X` goal by defeq.
  have hmid₀ : (α_ (𝟙_ X.Modules) F (L.tensorPow k)).inv ≫
        (β_ (𝟙_ X.Modules) F).hom ▷ L.tensorPow k ≫
          (α_ F (𝟙_ X.Modules) (L.tensorPow k)).hom ≫ F ◁ (λ_ (L.tensorPow k)).hom
      = (λ_ (F ⊗ L.tensorPow k)).hom := by
    rw [show (β_ (𝟙_ X.Modules) F).hom = (λ_ F).hom ≫ (ρ_ F).inv from braiding_tensorUnit_left F]
    monoidal
  have hmid : (α_ (unitModule X) F (L.tensorPow k)).inv ≫
        (β_ (unitModule X) F).hom ▷ L.tensorPow k ≫
          (α_ F (unitModule X) (L.tensorPow k)).hom ≫ F ◁ (λ_ (L.tensorPow k)).hom
      = (λ_ (F ⊗ L.tensorPow k)).hom := hmid₀
  -- Left-unitor naturality of `T.inv` — stated over `𝟙_` then transported to `unitModule X` by
  -- defeq (`leftUnitor_naturality` special-cases `𝟙_`, so a positional `rw` on the `unitModule X`
  -- whisker fails to match).
  have hlun₀ : (𝟙_ X.Modules) ◁ (F.tensorObjIso (L.tensorPow k)).inv ≫
        (λ_ (F ⊗ L.tensorPow k)).hom
      = (λ_ (F.tensorObj (L.tensorPow k))).hom ≫ (F.tensorObjIso (L.tensorPow k)).inv :=
    MonoidalCategory.leftUnitor_naturality (F.tensorObjIso (L.tensorPow k)).inv
  have hlun : (unitModule X) ◁ (F.tensorObjIso (L.tensorPow k)).inv ≫
        (λ_ (F ⊗ L.tensorPow k)).hom
      = (λ_ (F.tensorObj (L.tensorPow k))).hom ≫ (F.tensorObjIso (L.tensorPow k)).inv := hlun₀
  rw [reassoc_of% hmid, reassoc_of% hlun, ← hgen (Nat.zero_add k).symm, Iso.inv_hom_id_assoc]

/-! ### Graded-module carrier, transport and degreewise action (scaffolding for the `Gmodule`) -/

/-- The carrier type of the graded module at degree `m`: the `Γ(X,𝒪_X)`-module of global sections of
`F ⊗ L^{⊗m}` (`def:sheafModuleTwist`).  Module analogue of `sectionDeg`. -/
abbrev moduleSectionDeg (F L : X.Modules) (m : ℕ) : Type u :=
  ↥((moduleTensorPow F L m).val.obj (Opposite.op ⊤))

/-- Index-equality transport of module-section components, the module analogue of `sectionsCast`:
`Γ(X,-)` applied to the canonical iso `F⊗L^{⊗i} ≅ F⊗L^{⊗j}` from `h : i = j`. -/
noncomputable def moduleSectionsCast (F L : X.Modules) {i j : ℕ} (h : i = j) :
    moduleSectionDeg F L i ≃ₗ[↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤))] moduleSectionDeg F L j :=
  ((toPresheafOfModules X ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj
    (Opposite.op ⊤)).mapIso (eqToIso (congrArg (moduleTensorPow F L) h))).toLinearEquiv

/-- Transport along `rfl` is the identity (module analogue of `sectionsCast_refl`). -/
@[simp] lemma moduleSectionsCast_refl (F L : X.Modules) (i : ℕ) :
    moduleSectionsCast F L (rfl : i = i) = LinearEquiv.refl _ (moduleSectionDeg F L i) := by
  ext x
  rfl

/-- Cast-mediated equality in the module graded sigma type (module analogue of
`gradedMonoid_eq_of_cast`). -/
lemma moduleGradedMonoid_eq_of_cast (F L : X.Modules)
    {a b : GradedMonoid (moduleSectionDeg F L)}
    (h : a.1 = b.1) (h2 : moduleSectionsCast F L h a.2 = b.2) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain rfl : i = j := h
  simp only [moduleSectionsCast_refl, LinearEquiv.refl_apply] at h2
  subst h2
  rfl

/-- Degreewise graded action `sectionDeg L i × moduleSectionDeg F L j → moduleSectionDeg F L (i+j)`,
the section multiplication followed by global sections of the action comparison `a_{i,j}`
(`def:moduleTensorPowAdd`).  Module analogue of the `GradedMonoid.GMul` instance on `sectionDeg`. -/
noncomputable instance (F L : X.Modules) :
    GradedMonoid.GSMul (sectionDeg L) (moduleSectionDeg F L) where
  smul {i j} (r : sectionDeg L i) (x : moduleSectionDeg F L j) :=
    ((moduleTensorPowAdd F L i j).hom.val.app (Opposite.op ⊤)).hom
      ((sectionsMul (tensorPow L i) (moduleTensorPow F L j)).hom
        (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] x))

/-- Definitional unfolding of the graded action, as a rewrite handle for the coherence proofs. -/
private lemma gSMul_smul_apply (F L : X.Modules) {i j : ℕ}
    (r : sectionDeg L i) (x : moduleSectionDeg F L j) :
    (GradedMonoid.GSMul.smul r x : moduleSectionDeg F L (i + j))
      = ((moduleTensorPowAdd F L i j).hom.val.app (Opposite.op ⊤)).hom
          ((sectionsMul (tensorPow L i) (moduleTensorPow F L j)).hom
            (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] x)) :=
  rfl

/-- Definitional unfolding of the module section transport applied to an element. -/
private lemma moduleSectionsCast_apply (F L : X.Modules) {i j : ℕ} (h : i = j)
    (y : moduleSectionDeg F L i) :
    moduleSectionsCast F L h y
      = ((eqToIso (congrArg (moduleTensorPow F L) h)).hom.val.app (Opposite.op ⊤)).hom y :=
  rfl

/-- Two index transports along inverse equalities cancel (module analogue). -/
private lemma moduleSectionsCast_sectionsCast (F L : X.Modules) {i j : ℕ} (h₁ : i = j) (h₂ : j = i)
    (x : moduleSectionDeg F L i) :
    moduleSectionsCast F L h₂ (moduleSectionsCast F L h₁ x) = x := by
  obtain rfl := h₁
  rw [Subsingleton.elim h₂ rfl]
  simp only [moduleSectionsCast_refl, LinearEquiv.refl_apply]

set_option maxRecDepth 4000 in
/-- **Compatibility of the graded module action** (`lem:moduleSectionAction_coherent`, compatibility
clause): transporting `(r·r')⋆x` along `(i+j)+k = i+(j+k)` gives `r⋆(r'⋆x)`.  Module analogue of
`sectionsMul_mul_assoc` (B7): the same three-slide assembly with the action comparison `a` replacing
the ring comparison `μ` on the legs touching `F`, closed by the iso-level hexagon
`moduleTensorPowAdd_assoc` (A). -/
theorem moduleSectionAction_mul_smul (F L : X.Modules) {i j k : ℕ}
    (r : sectionDeg L i) (r' : sectionDeg L j) (x : moduleSectionDeg F L k) :
    moduleSectionsCast F L (add_assoc i j k)
        (GradedMonoid.GSMul.smul (GradedMonoid.GMul.mul r r') x)
      = GradedMonoid.GSMul.smul r (GradedMonoid.GSMul.smul r' x) := by
  -- Unfold the degreewise action/multiplication on both sides to `Γ(comparison) ∘ sectionsMul`;
  -- normalize the `+ᵥ` (graded-action degree) to `+`.
  simp only [vadd_eq_add, gSMul_smul_apply, gMul_mul_apply]
  --   RIGHT slide (e = μ_{i,j}): move the inner `Γ(μ_{i,j})` out of the first factor of the outer
  --   `sectionsMul (L^{i+j}) (F⊗L^k)`.
  rw [sectionsMul_whiskerRight_natural (tensorPowAdd L i j) (moduleTensorPow F L k)
        ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
          (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] r')) x]
  --   LEFT slide (e = a_{j,k}): move the inner `Γ(a_{j,k})` out of the second factor of the outer
  --   `sectionsMul (L^i) (F⊗L^{j+k})`.
  rw [sectionsMul_whiskerLeft_natural (tensorPow L i) (moduleTensorPowAdd F L j k) r
        ((sectionsMul (tensorPow L j) (moduleTensorPow F L k)).hom
          (r' ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] x))]
  --   B5 backwards: recognise the RHS iterated section product as `Γ(α)(…)`.
  rw [← tensorObjAssoc_hom_sectionsMul (tensorPow L i) (tensorPow L j) (moduleTensorPow F L k)
        r r' x]
  --   (A) the iso-level module hexagon applied at the common base element.
  exact congrArg
    (fun (iso : tensorObj (tensorObj (tensorPow L i) (tensorPow L j)) (moduleTensorPow F L k)
        ≅ moduleTensorPow F L (i + (j + k))) =>
      (iso.hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorObj (tensorPow L i) (tensorPow L j)) (moduleTensorPow F L k)).hom
          ((sectionsMul (tensorPow L i) (tensorPow L j)).hom
              (r ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] r')
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] x)))
    (moduleTensorPowAdd_assoc F L i j k)

set_option maxRecDepth 4000 in
/-- **Unitality of the graded module action** (`lem:moduleSectionAction_coherent`, unitality
clause): transporting `1 ⋆ x` along `0 + k = k` gives `x`.  Module analogue of
`sectionsMul_one_mul`: the
degree-`(0,k)` action comparison `a_{0,k}` is the left unitor (`moduleTensorPowAdd_zero_left`), and
the inner cast pairs with the outer `moduleSectionsCast` and cancels, leaving the left-unit law
`tensorObjUnitIso_hom_sectionsMul`. -/
theorem moduleSectionAction_one_smul (F L : X.Modules) {k : ℕ} (x : moduleSectionDeg F L k) :
    moduleSectionsCast F L (zero_add k)
        (GradedMonoid.GSMul.smul (1 : sectionDeg L 0) x) = x := by
  -- NOTE: the graded unit is spelled `(1 : sectionDeg L 0)` rather than `GradedMonoid.GOne.one`
  -- (defeq by `gOne_one_eq`): the bare `GradedMonoid.GOne.one` projection as an argument to the
  -- `+ᵥ`-graded `GSMul.smul` triggers a whnf blow-up during *statement* elaboration.
  rw [gSMul_smul_apply, moduleTensorPowAdd_zero_left F L k]
  -- `moduleTensorPowAdd L 0 k = tensorObjUnitIso ≪≫ eqToIso`; the inner cast pairs with the outer
  -- `moduleSectionsCast` and the two cancel, leaving the left unitor.
  change moduleSectionsCast F L (zero_add k) (moduleSectionsCast F L (Nat.zero_add k).symm
      (((tensorObjUnitIso (moduleTensorPow F L k)).hom.val.app (Opposite.op ⊤)).hom
        ((sectionsMul (tensorPow L 0) (moduleTensorPow F L k)).hom
          ((1 : ↥(X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
            ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op ⊤)] x)))) = x
  rw [moduleSectionsCast_sectionsCast]
  exact tensorObjUnitIso_hom_sectionsMul (moduleTensorPow F L k) x

set_option maxRecDepth 4000 in
/-- **Graded-module structure on the twisted section components**
(`lem:sectionGradedModule_gmodule`,
module analogue of [Stacks, Tag 01CV]): for an *arbitrary* `L : X.Modules` and any `F : X.Modules`,
the family `m ↦ Γ(X, F ⊗ L^{⊗m})` is a `DirectSum.Gmodule` over the section graded monoid
`m ↦ Γ(X, L^{⊗m})`, so `⊕_m Γ(X, F ⊗ L^{⊗m})` is a graded module over `Γ_*(X, L)`.  The degreewise
action `Γ(a_{i,j}) ∘ sectionsMul` (the `GSMul` instance) satisfies the two `GMulAction` coherence
clauses `moduleSectionAction_one_smul` / `moduleSectionAction_mul_smul` (routed, like the ring's
`sectionGradedRing_gmonoid`, through `moduleGradedMonoid_eq_of_cast`), and the bilinearity clauses
hold because `Γ(a_{i,j}) ∘ sectionsMul` is a composite of additive maps (push `0`/`+` through the
`TensorProduct` step then the two `ModuleCat` morphisms — `erw` to cross the `DFunLike` coercion).
Project-local: Mathlib has no graded module on sheaf-section twists. -/
@[reducible] noncomputable def sectionGradedModule_gmodule (F L : X.Modules) :
    letI := sectionGradedRing_gmonoid L
    DirectSum.Gmodule (sectionDeg L) (moduleSectionDeg F L) :=
  letI := sectionGradedRing_gmonoid L
  { (inferInstance : GradedMonoid.GSMul (sectionDeg L) (moduleSectionDeg F L)) with
    one_smul := fun b =>
      moduleGradedMonoid_eq_of_cast F L (zero_add b.1) (moduleSectionAction_one_smul F L b.2)
    mul_smul := fun a a' b =>
      moduleGradedMonoid_eq_of_cast F L (add_assoc a.1 a'.1 b.1)
        (moduleSectionAction_mul_smul F L a.2 a'.2 b.2)
    smul_add := fun a b c => by
      simp only [gSMul_smul_apply]; erw [TensorProduct.tmul_add, map_add, map_add]
    smul_zero := fun a => by
      simp only [gSMul_smul_apply]; erw [TensorProduct.tmul_zero, map_zero, map_zero]
    add_smul := fun a a' b => by
      simp only [gSMul_smul_apply]; erw [TensorProduct.add_tmul, map_add, map_add]
    zero_smul := fun b => by
      simp only [gSMul_smul_apply]; erw [TensorProduct.zero_tmul, map_zero, map_zero] }

end AlgebraicGeometry.Scheme.Modules
