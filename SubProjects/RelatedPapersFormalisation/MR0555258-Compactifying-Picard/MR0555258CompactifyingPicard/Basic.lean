import Mathlib

set_option linter.style.header false

/-!
# MR0555258: Compactifying the Picard scheme — §1 (Base-change theory)

This file scaffolds Section 1 ("Some Base-Change Theory") of
Altman–Kleiman, *Compactifying the Picard Scheme*, Adv. Math. 35 (1980), 54–63.

The whole §1 development is proved **relative to** nine EGA/OB external inputs,
realized here as `axiom`s under the `External` namespace (these are results the
paper *cites*; they are never proved here).

## Mathlib gaps (project-local scaffolding)

Several notions the paper uses are not (yet) in Mathlib:

* the **relative local Ext sheaf** `sExt^q_{X/S}(I,F)`, an `𝒪_S`-module;
* the **representing module** `H(I,F)` and its universal element `h(I,F)`;
* tensor products of sheaves of modules and base-change tensors `F ⊗_S M`;
* finite-presentation / flatness predicates for sheaves of modules.

These are introduced below as **minimal project-local definitions** (often
`opaque`, with the mathematically correct *type*) so that the §1 statements can
be transcribed faithfully. Replacing the opaque bodies with genuine
constructions is future work; the type signatures match the paper.

A handful of the deepest statements (those genuinely requiring scheme-theoretic
fibre products, projective limits of schemes, or the explicit base-change
comparison map) are left as clearly-marked `TODO` blocks rather than wrong-typed
stubs, per the project directive "faithfulness beats coverage".
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

open scoped ZeroObject

namespace MR0555258CompactifyingPicard

variable {X S : Scheme.{u}}

/-! ## Project-local scaffolding for Mathlib gaps -/

/-- The category of `𝒪_X`-modules is abelian, hence has a zero object, so it is
nonempty. This instance is what lets the `opaque` placeholders below (whose
return types are module categories) be declared. -/
private instance instNonemptyModules {X : Scheme.{u}} : Nonempty X.Modules := ⟨0⟩

/-- Project-local (Mathlib gap): `M` is a locally finitely presented
`𝒪_X`-module. Realized via Mathlib's `SheafOfModules.IsFinitePresentation` for
the sheaf of modules underlying `M`, using that `X.Modules` is by definition
`SheafOfModules X.ringCatSheaf`. -/
def IsLFP {X : Scheme.{u}} (M : X.Modules) : Prop :=
  SheafOfModules.IsFinitePresentation M

/-- Project-local (Mathlib gap): the `𝒪_X`-module `M` is flat over the base `S`
along `f : X ⟶ S`. Realized stalkwise: at every point `x : X` the stalk of `M`
(a module over the local ring `𝒪_{X,x}`) is flat over `𝒪_{S,f(x)}` via the local
ring map `f.stalkMap x`. This is the pointwise/stalkwise incarnation of the
affine-local "`M(V)` flat over `R`" definition of Altman–Kleiman (1.1).

The module structure on the stalk `(stalk M.val.presheaf x)` over `𝒪_{X,x}` comes
from `Mathlib.Algebra.Category.ModuleCat.Stalk`; restriction of scalars along
`f.stalkMap x : 𝒪_{S,f(x)} → 𝒪_{X,x}` makes it an `𝒪_{S,f(x)}`-module. -/
def IsSFlat {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∀ x : X,
    letI : Module ↑(X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (M := M.val) x
    letI : Module ↑(S.presheaf.stalk (f.base x)) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
      Module.compHom _ (f.stalkMap x).hom
    Module.Flat ↑(S.presheaf.stalk (f.base x)) ↑(TopCat.Presheaf.stalk M.val.presheaf x)

/-- Project-local (Mathlib gap): tensor product `M ⊗_{𝒪_X} N` of two
`𝒪_X`-modules, the sheafification of the presheaf-level tensor product. Realized
via Mathlib's presheaf monoidal tensor `PresheafOfModules.Monoidal.tensorObj`
(over the `CommRingCat`-presheaf `X.presheaf`) followed by
`PresheafOfModules.sheafification` along the identity `X.ringCatSheaf.obj ⟶
X.ringCatSheaf.obj`. There is no `MonoidalCategory X.Modules` instance in
Mathlib, so the tensor is assembled by hand from the presheaf monoidal structure
plus sheafification. -/
noncomputable def tensorMod {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

/-- Project-local (Mathlib gap): `L` is an invertible `𝒪_X`-module, i.e. there is
an `𝒪_X`-module `L'` with `L ⊗_{𝒪_X} L' ≅ 𝒪_X`. Realized as an invertible object
for the tensor `tensorMod`, with unit the structure sheaf `SheafOfModules.unit`. -/
def IsInvertibleMod {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∃ L' : X.Modules, Nonempty (tensorMod L L' ≅ SheafOfModules.unit X.ringCatSheaf)

/-- Project-local (Mathlib gap): the "tensor by `F`" endofunctor on
`𝒪_X`-modules, `N ↦ F ⊗_{𝒪_X} N`. On objects it is `tensorMod F`; on a morphism
`φ` it sheafifies the presheaf-level tensor `PresheafOfModules.Monoidal.tensorHom
(𝟙 F.val) φ.val`. Mirrors the construction of `tensorMod`; there is no
`MonoidalCategory X.Modules` instance in Mathlib, so the functor is assembled by
hand from the presheaf monoidal tensor plus sheafification. -/
noncomputable def tensorLeft {X : Scheme.{u}} (F : X.Modules) : X.Modules ⥤ X.Modules where
  obj N := tensorMod F N
  map {N N'} φ :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) φ.val)
  map_id N := by
    have h : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 N.val)
        = 𝟙 (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) F.val N.val) := by
      ext1 Y
      rw [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app,
        PresheafOfModules.id_app, PresheafOfModules.id_app]
      exact MonoidalCategory.id_tensorHom_id _ _
    exact (congrArg (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map h).trans
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_id _)
  map_comp {N N' N''} φ ψ := by
    have h : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (φ.val ≫ ψ.val)
        = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) φ.val
          ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) ψ.val := by
      ext1 Y
      rw [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
        PresheafOfModules.comp_app, PresheafOfModules.Monoidal.tensorHom_app,
        PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
      exact MonoidalCategory.id_tensor_comp _ _
    exact (congrArg (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map h).trans
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _)

/-- **(`def:tensorRight`)** Project-local (Mathlib gap): the "tensor by `L` on the
right" endofunctor on `𝒪_X`-modules, `N ↦ N ⊗_{𝒪_X} L`. The right-handed mirror of
`tensorLeft` [line ~101]: on objects `tensorMod · L`; on a morphism `φ` it sheafifies
`PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val)`. There is no
`MonoidalCategory X.Modules` instance in Mathlib, so it is assembled by hand from the
presheaf monoidal tensor plus sheafification. -/
noncomputable def tensorRight {X : Scheme.{u}} (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj N := tensorMod N L
  map {N N'} φ :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val (𝟙 L.val))
  map_id N := by
    have h : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 N.val) (𝟙 L.val)
        = 𝟙 (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) N.val L.val) := by
      ext1 Y
      rw [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app,
        PresheafOfModules.id_app, PresheafOfModules.id_app]
      exact MonoidalCategory.id_tensorHom_id _ _
    exact (congrArg (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map h).trans
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_id _)
  map_comp {N N' N''} φ ψ := by
    have h : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (φ.val ≫ ψ.val) (𝟙 L.val)
        = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val (𝟙 L.val)
          ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) ψ.val (𝟙 L.val) := by
      ext1 Y
      rw [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
        PresheafOfModules.comp_app, PresheafOfModules.Monoidal.tensorHom_app,
        PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
      exact MonoidalCategory.comp_tensor_id _ _
    exact (congrArg (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map h).trans
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _)

/-- Project-local (general category theory, Mathlib gap in the `Type u`-valued form):
for a fully faithful endofunctor `G : C ⥤ C` and an object `I`, the natural
isomorphism `G ⋙ coyoneda(op (G.obj I)) ≅ coyoneda(op I)` reflecting the
full-faithfulness Hom-bijection `(G.obj I ⟶ G.obj Z) ≅ (I ⟶ Z)`, natural in `Z`.
Mathlib's `Functor.FullyFaithful.homNatIso'` states this only through `uliftCoyoneda`
(landing in `ULift`-ed homs); this `Type u`-valued form is what the (1.1.2) Yoneda
step needs to compare the two `homTensorFunctor`s. -/
noncomputable def coyonedaCompFF {C : Type*} [Category C] {G : C ⥤ C}
    (hG : G.FullyFaithful) (I : C) :
    G ⋙ coyoneda.obj (op (G.obj I)) ≅ coyoneda.obj (op I) :=
  NatIso.ofComponents
    (fun Z => (hG.homEquiv (X := I) (Y := Z)).symm.toIso)
    (by aesop_cat)

/-! ## Project-local Mathlib supplement — symmetric-monoidal scaffolding for `tensorMod`

Mathlib provides the monoidal structure on **presheaves** of modules
(`PresheafOfModules.monoidalCategory`, with associators and unitors) but registers
no braided/symmetric instance even at the presheaf level, and no monoidal structure
on `SheafOfModules` over a sheaf of rings. The isomorphisms below supply the
braiding (and, where reachable, the unitor) of the sheafified tensor `tensorMod`,
built by transporting the pointwise module-level structure (`TensorProduct.comm`,
encoded as the `ModuleCat` symmetric braiding `β_`) through the presheaf tensor and
sheafification. They are the algebraic engine of the `H`-twist isomorphisms
(1.1.2)/(1.1.3). -/

/-- Project-local (Mathlib gap): the braiding of the presheaf-level monoidal tensor
`PresheafOfModules.Monoidal.tensorObj`. There is no `BraidedCategory`/`SymmetricCategory`
instance on `PresheafOfModules` in Mathlib, so we build the swap by hand: the rings
`R(U)` are commutative, hence each pointwise tensor carries the `ModuleCat` symmetric
braiding `β_`, and these assemble (via `PresheafOfModules.isoMk`) into an isomorphism
of presheaves of modules. -/
noncomputable def presheafTensorBraiding {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat}
    (M N : PresheafOfModules (R.comp (forget₂ CommRingCat RingCat))) :
    PresheafOfModules.Monoidal.tensorObj M N ≅ PresheafOfModules.Monoidal.tensorObj N M :=
  PresheafOfModules.isoMk
    (fun X => β_ (M.obj X) (N.obj X))
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m n
      erw [PresheafOfModules.Monoidal.tensorObj_map_tmul])

/-- Project-local (Mathlib gap): the braiding (symmetry) of the `𝒪_X`-tensor
`tensorMod` of \cref{def:tensorMod}, `A ⊗_{𝒪_X} B ≅ B ⊗_{𝒪_X} A`. Obtained by
applying the sheafification functor (`.mapIso`) to the hand-built presheaf-level
braiding `presheafTensorBraiding`. -/
noncomputable def tensorBraiding {X : Scheme.{u}} (A B : X.Modules) :
    tensorMod A B ≅ tensorMod B A :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (presheafTensorBraiding (R := X.presheaf) A.val B.val)

/-- Project-local (Mathlib gap): **naturality of the presheaf-level braiding**
`presheafTensorBraiding` in its first factor. For `f : M ⟶ M'` the square
`(f ⊗ 𝟙_N) ≫ β_{M',N} = β_{M,N} ≫ (𝟙_N ⊗ f)` commutes — it is the pointwise
`ModuleCat` braiding naturality (`BraidedCategory.braiding_naturality`) assembled
over the site. Used to make `tensorBraiding` natural (`tensorBraidingNatIso`). -/
lemma presheafTensorBraiding_naturality {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat}
    {M M' N : PresheafOfModules (R.comp (forget₂ CommRingCat RingCat))} (f : M ⟶ M') :
    PresheafOfModules.Monoidal.tensorHom f (𝟙 N) ≫ (presheafTensorBraiding M' N).hom
      = (presheafTensorBraiding M N).hom ≫ PresheafOfModules.Monoidal.tensorHom (𝟙 N) f := by
  ext1 Y
  simp only [PresheafOfModules.comp_app, PresheafOfModules.Monoidal.tensorHom_app,
    PresheafOfModules.id_app, presheafTensorBraiding, PresheafOfModules.isoMk_hom_app]
  exact BraidedCategory.braiding_naturality (f.app Y) (𝟙 (N.obj Y))

/-- Project-local (Mathlib gap): the braiding `tensorBraiding` of the `𝒪_X`-tensor,
packaged as a **natural isomorphism of endofunctors** `tensorRight B ≅ tensorLeft B`
(i.e. `A ⊗ B ≅ B ⊗ A` natural in `A`). Naturality in `A` follows from
`presheafTensorBraiding_naturality` and functoriality of sheafification; this is the
first-variable-naturality input to `tensorRearrangeNatIso`. -/
noncomputable def tensorBraidingNatIso {X : Scheme.{u}} (B : X.Modules) :
    tensorRight B ≅ tensorLeft B :=
  NatIso.ofComponents (fun A => tensorBraiding A B) (by
    intro A A' φ
    change (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val (𝟙 B.val)) ≫
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
          (presheafTensorBraiding (R := X.presheaf) A'.val B.val)).hom
      = ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
          (presheafTensorBraiding (R := X.presheaf) A.val B.val)).hom ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 B.val) φ.val)
    rw [Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (presheafTensorBraiding_naturality (R := X.presheaf) φ.val))

/-- Project-local (Mathlib gap): the presheaf-level left unitor of the monoidal
tensor `PresheafOfModules.Monoidal.tensorObj`. The monoidal unit `𝟙_` of
`PresheafOfModules` is (definitionally) `PresheafOfModules.unit`, so this is just
the monoidal `leftUnitor`; stated in this form so it composes with `tensorMod`,
whose unit is `SheafOfModules.unit` (whose `.val` is `PresheafOfModules.unit`). -/
noncomputable def presheafLeftUnitor {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat}
    (M : PresheafOfModules (R.comp (forget₂ CommRingCat RingCat))) :
    PresheafOfModules.Monoidal.tensorObj (PresheafOfModules.unit _) M ≅ M :=
  MonoidalCategory.leftUnitor M

/-- Project-local (Mathlib gap): for an `𝒪_X`-module `A` (a sheaf of modules), the
sheafification of its underlying presheaf is canonically isomorphic to `A` itself.
This is the counit of the (reflective) module-sheafification adjunction at the
sheaf `A`, which is an isomorphism. The type is intentionally left to be inferred
from the counit: pinning it as `sheafification.obj A.val ≅ A` forces a different
instance path for `sheafification` and breaks `IsIso` synthesis. -/
noncomputable def sheafifyValIso {X : Scheme.{u}} (A : X.Modules) :=
  asIso ((PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit.app A)

/-- Project-local (Mathlib gap): the left unitor of the `𝒪_X`-tensor `tensorMod`,
`𝒪_X ⊗_{𝒪_X} A ≅ A`, with the structure sheaf `SheafOfModules.unit` as tensor unit.
Sheafify the presheaf-level left unitor `presheafLeftUnitor` (pointwise
`TensorProduct.lid`), then identify the sheafification of the sheaf `A` with `A`
itself via `sheafifyValIso`. -/
noncomputable def tensorLeftUnitor {X : Scheme.{u}} (A : X.Modules) :
    tensorMod (SheafOfModules.unit X.ringCatSheaf) A ≅ A :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (presheafLeftUnitor (R := X.presheaf) A.val) ≪≫ sheafifyValIso A

/-- Project-local (Mathlib gap): the right unitor of the `𝒪_X`-tensor `tensorMod`,
`A ⊗_{𝒪_X} 𝒪_X ≅ A`. Derived from the braiding and the left unitor, as in the
blueprint (`A ⊗ 𝒪_X ≅ 𝒪_X ⊗ A ≅ A`). -/
noncomputable def tensorRightUnitor {X : Scheme.{u}} (A : X.Modules) :
    tensorMod A (SheafOfModules.unit X.ringCatSheaf) ≅ A :=
  tensorBraiding A (SheafOfModules.unit X.ringCatSheaf) ≪≫ tensorLeftUnitor A

/-- Project-local (Mathlib gap): **module sheafification inverts locally-bijective
morphisms.** If a morphism `g` of presheaves of modules is locally injective and
locally surjective (a "local isomorphism"), then `g` becomes an isomorphism after
sheafification. This is the engine underlying the comparison
`sheafifyTensorComparison` and hence the associator `tensorAssoc`.

The proof uses that `PresheafOfModules.sheafification α` is a localization functor
at `J.W.inverseImage (toPresheaf R₀)` (`PresheafOfModules.instIsLocalization…`,
from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization`), and that a
localization functor inverts every morphism of its localizing class
(`CategoryTheory.Localization.inverts`); membership in `J.W` is exactly local
bijectivity via `GrothendieckTopology.W_of_isLocallyBijective`. Mathlib has no
ready-made statement of this for `PresheafOfModules`, so it is project-local. -/
lemma sheafification_map_isIso_of_locallyBijective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat} {R : Sheaf J RingCat} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
    {P P' : PresheafOfModules R₀} (g : P ⟶ P')
    (hi : PresheafOfModules.IsLocallyInjective J g)
    (hs : PresheafOfModules.IsLocallySurjective J g) :
    IsIso ((PresheafOfModules.sheafification α).map g) := by
  haveI := hi; haveI := hs
  have hW : J.W ((PresheafOfModules.toPresheaf R₀).map g) := J.W_of_isLocallyBijective _
  exact Localization.inverts (PresheafOfModules.sheafification α)
    (J.W.inverseImage (PresheafOfModules.toPresheaf R₀)) g hW

/-- Project-local (Mathlib gap): the sheafification unit `η_P : P → (P̃).val` of a
presheaf of modules `P` on a scheme `X`, as a morphism of presheaves of modules.
It is the unit of `PresheafOfModules.sheafificationAdjunction` at `P`; its codomain
`(restrictScalars (𝟙 …)).obj _` is definitionally the underlying presheaf
`((sheafification …).obj P).val`. This is the map that, whiskered by a fixed `Q`,
induces `sheafifyTensorComparison`. -/
noncomputable def sheafifyUnit {X : Scheme.{u}}
    (P : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).unit.app P

/-- Project-local (Mathlib gap): the sheafification unit `η_P` whiskered on the right
by a fixed presheaf of modules `Q`, i.e. `η_P ⊗ 𝟙_Q : P ⊗ Q → (P̃).val ⊗ Q`. Sheafifying
this map and inverting it is exactly `sheafifyTensorComparison`. -/
noncomputable def sheafifyTensorUnitWhiskerRight {X : Scheme.{u}}
    (P Q : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.Monoidal.tensorObj P Q ⟶
      PresheafOfModules.Monoidal.tensorObj ((PresheafOfModules.sheafification
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P).val Q :=
  PresheafOfModules.Monoidal.tensorHom (sheafifyUnit P) (𝟙 Q)

/-- Project-local (Mathlib gap): the **module-sheafification ⊗ comparison**,
`(((P̃).val) ⊗ Q)̃ ≅ (P ⊗ Q)̃`, *conditional* on the unit-whiskering
`sheafifyTensorUnitWhiskerRight P Q` being locally injective and locally surjective.

Given those two facts, the map is `(sheafification …).map (η_P ⊗ 𝟙_Q)`, which is an
isomorphism by `sheafification_map_isIso_of_locallyBijective`; the comparison is its
inverse (`asIso … |>.symm`). This is the assembled comparison
(blueprint `lem:sheafifyTensorComparison`) with the genuine remaining gap isolated
into the two hypotheses `hi`, `hs`: *tensoring by a fixed `Q` preserves local
bijectivity of the sheafification unit*. That preservation is not provable at the
presheaf level (tensoring is not left exact); it requires the stalkwise description
of local bijectivity on the scheme site (or monoidal-closedness of
`PresheafOfModules`, which Mathlib lacks). See the task handoff. -/
noncomputable def sheafifyTensorComparisonOfLocallyBijective {X : Scheme.{u}}
    (P Q : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (hi : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerRight P Q))
    (hs : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerRight P Q)) :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj ((PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P).val Q) ≅
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj P Q) :=
  have : IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (sheafifyTensorUnitWhiskerRight P Q)) :=
    sheafification_map_isIso_of_locallyBijective (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj) (sheafifyTensorUnitWhiskerRight P Q) hi hs
  (asIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).map (sheafifyTensorUnitWhiskerRight P Q))).symm

/-- Project-local (Mathlib gap): the sheafification unit `η_Q` whiskered on the left
by a fixed `P`, i.e. `𝟙_P ⊗ η_Q : P ⊗ Q → P ⊗ (Q̃).val`. The left-handed counterpart
of `sheafifyTensorUnitWhiskerRight`, used for the right leg of `tensorAssoc`. -/
noncomputable def sheafifyTensorUnitWhiskerLeft {X : Scheme.{u}}
    (P Q : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.Monoidal.tensorObj P Q ⟶
      PresheafOfModules.Monoidal.tensorObj P ((PresheafOfModules.sheafification
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj Q).val :=
  PresheafOfModules.Monoidal.tensorHom (𝟙 P) (sheafifyUnit Q)

/-- Project-local (Mathlib gap): the left-handed module-sheafification ⊗ comparison,
`(P ⊗ (Q̃).val)̃ ≅ (P ⊗ Q)̃`, *conditional* on the left unit-whiskering being locally
bijective. Symmetric to `sheafifyTensorComparisonOfLocallyBijective`; same isolated
gap. -/
noncomputable def sheafifyTensorComparisonLeftOfLocallyBijective {X : Scheme.{u}}
    (P Q : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (hi : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerLeft P Q))
    (hs : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerLeft P Q)) :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj P ((PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj Q).val) ≅
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj P Q) :=
  have : IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (sheafifyTensorUnitWhiskerLeft P Q)) :=
    sheafification_map_isIso_of_locallyBijective (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj) (sheafifyTensorUnitWhiskerLeft P Q) hi hs
  (asIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).map (sheafifyTensorUnitWhiskerLeft P Q))).symm

/-- Project-local (Mathlib gap): the **associator** of the `𝒪_X`-tensor `tensorMod`,
`(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)` (blueprint `lem:tensorMod_assoc`), *conditional* on the
four local-bijectivity facts that make the two sheafification ⊗ comparisons
(`sheafifyTensorComparisonOfLocallyBijective` on the left leg,
`sheafifyTensorComparisonLeftOfLocallyBijective` on the right leg) into isomorphisms.

The assembly is the blueprint chain
`((A⊗B)̃ ⊗ C)̃ ≅ ((A⊗B) ⊗ C)̃ ≅ (A ⊗ (B⊗C))̃ ≅ (A ⊗ (B⊗C)̃)̃`,
the middle step being the sheafification of the presheaf-level
`MonoidalCategory.associator` (`TensorProduct.assoc` pointwise). The four hypotheses
are precisely the genuine remaining gap (tensoring preserves local bijectivity);
once Mathlib gains the stalkwise/closed-category infrastructure they are discharged
automatically and this becomes the unconditional `tensorAssoc`. -/
noncomputable def tensorAssocOfLocallyBijective {X : Scheme.{u}} (A B C : X.Modules)
    (hiR : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerRight (PresheafOfModules.Monoidal.tensorObj A.val B.val) C.val))
    (hsR : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerRight (PresheafOfModules.Monoidal.tensorObj A.val B.val) C.val))
    (hiL : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerLeft A.val (PresheafOfModules.Monoidal.tensorObj B.val C.val)))
    (hsL : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (sheafifyTensorUnitWhiskerLeft A.val (PresheafOfModules.Monoidal.tensorObj B.val C.val))) :
    tensorMod (tensorMod A B) C ≅ tensorMod A (tensorMod B C) :=
  sheafifyTensorComparisonOfLocallyBijective
      (PresheafOfModules.Monoidal.tensorObj A.val B.val) C.val hiR hsR ≪≫
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.associator
        (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
        A.val B.val C.val) ≪≫
    (sheafifyTensorComparisonLeftOfLocallyBijective A.val
      (PresheafOfModules.Monoidal.tensorObj B.val C.val) hiL hsL).symm

/-! ### (1.1.2 STEP 1) Mathlib-gap anchor: module-sheafification is monoidal

The unconditional sheafification–tensor comparison `~((~P) ⊗ Q) ≅ ~(P ⊗ Q)` (and
its left-handed twin `~(P ⊗ (~Q)) ≅ ~(P ⊗ Q)`). This is the *true general fact*
that the module-sheafification functor `~(-)` on `PresheafOfModules` is monoidal
(a monoidal localization). It is ABSENT from Mathlib for `PresheafOfModules`: the
naive "tensoring preserves local isomorphisms" route fails on the injectivity half
(`ℤ/2 ⊗ ·2`; iter-008 finding, recorded at `sheafifyTensorComparisonOfLocallyBijective`)
and the `CategoryTheory.Localization.Monoidal` route needs `W.IsMonoidal` +
`L.IsLocalization W` for module sheafification, both absent. It carries **NO
§1 content** — it is pure category theory, anchored exactly as
`External.affine_fp_tilde` / `External.flat_tensor_exact` anchor true general facts
Mathlib lacks at the needed generality. See `lem:sheafifyTensorComparison_uncond`.

These are the unconditional forms of `sheafifyTensorComparisonOfLocallyBijective`
and `sheafifyTensorComparisonLeftOfLocallyBijective` (their local-bijectivity
hypotheses, false in general, dropped). -/
/-- Module sheafification `~(-) : PresheafOfModules → SheafOfModules` on `X`, packaged
as a named functor. Defined object/morphism-wise from
`PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)` (the applied `.obj`/`.map`
form, which drives the `IsLocallyInjective`/`IsLocallySurjective` instance synthesis
that the bare-functor form leaves as metavariables). Used to build the bifunctorial
comparison anchors without instance-synthesis-order failures. -/
noncomputable def moduleSheafification (X : Scheme.{u}) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⥤
      SheafOfModules X.ringCatSheaf where
  obj P := (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P
  map f := (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map f
  map_id P :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map_id P
  map_comp f g :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map_comp f g

/-- The "sheafify then forget" endofunctor on presheaves of `𝒪_X`-modules,
`P ↦ (P̃).val`. Used to phrase the bifunctorial (natural) form of the comparison
anchors `External.sheafifyTensorComparison{,Left}`. -/
noncomputable def sheafifyForget (X : Scheme.{u}) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  moduleSheafification X ⋙ SheafOfModules.forget X.ringCatSheaf

/-- The bifunctor `(P, Q) ↦ ~(P ⊗ Q)` on presheaves of `𝒪_X`-modules: the
presheaf-level monoidal tensor followed by module sheafification. The common
right-hand side of both comparison anchors.

Hand-built (rather than `MonoidalCategory.tensor ⋙ moduleSheafification`) with an
**explicit** action on morphisms `f ↦ ~(f.1 ⊗ f.2)`, so that `(tensorThenSheafify
X).map (a, b)` reduces *cheaply* (single `rfl`) to the hand-built
`tensorLeft`/`tensorRight` morphism maps. The `MonoidalCategory.tensor` packaging
makes that reduction blow up `whnf` (the monoidal-instance `tensorHom` does not
unfold cheaply), which blocks the (1.1.2) naturality layer. Objects are unchanged,
so the comparison anchors and `tensorAssoc` (which only use `.app`) are unaffected. -/
noncomputable def tensorThenSheafify (X : Scheme.{u}) :
    (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
       PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) ⥤
      SheafOfModules X.ringCatSheaf where
  obj P := (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj P.1 P.2)
  map {P P'} f :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom f.1 f.2)
  map_id P := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map_id _)
    congr 1
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app, prod_id_fst,
      prod_id_snd]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {P P' P''} f g := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _)
    congr 1
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app, prod_comp_fst,
      prod_comp_snd]
    exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- The bifunctor `(P, Q) ↦ ~((~P).val ⊗ Q)` — sheafify the first factor, then
`tensorThenSheafify`. The left-hand side of `External.sheafifyTensorComparison`.
Hand-built (explicit `obj`/`map`) so that `.obj`/`.map` reduce cheaply to the
`tensorMod`/`tensorRight`-`tensorLeft` forms used by the (1.1.2) naturality layer. -/
noncomputable def sheafifyFstTensorThenSheafify (X : Scheme.{u}) :
    (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
       PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) ⥤
      SheafOfModules X.ringCatSheaf where
  obj P := (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P.1).val
      P.2)
  map {P P'} f :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map f.1).val
        f.2)
  map_id P := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map_id _)
    congr 1
    rw [prod_id_fst, prod_id_snd]
    have hv : ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 P.1)).val
        = 𝟙 ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).obj P.1).val := by
      erw [CategoryTheory.Functor.map_id]
      rw [SheafOfModules.id_val]
    rw [hv]
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {P P' P''} f g := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _)
    congr 1
    have hv : ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map (f ≫ g).1).val
        = ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map f.1).val ≫
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map g.1).val := by
      rw [prod_comp_fst]
      erw [Functor.map_comp]
      rw [SheafOfModules.comp_val]
    rw [hv, prod_comp_snd]
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app]
    exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- The bifunctor `(P, Q) ↦ ~(P ⊗ (~Q).val)` — sheafify the second factor, then
`tensorThenSheafify`. The left-hand side of `External.sheafifyTensorComparisonLeft`.
Hand-built (explicit `obj`/`map`), the left-handed mirror of
`sheafifyFstTensorThenSheafify`. -/
noncomputable def sheafifySndTensorThenSheafify (X : Scheme.{u}) :
    (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
       PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) ⥤
      SheafOfModules X.ringCatSheaf where
  obj P := (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj P.1
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P.2).val)
  map {P P'} f :=
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom f.1
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map f.2).val)
  map_id P := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map_id _)
    congr 1
    rw [prod_id_fst, prod_id_snd]
    have hv : ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 P.2)).val
        = 𝟙 ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).obj P.2).val := by
      erw [CategoryTheory.Functor.map_id]
      rw [SheafOfModules.id_val]
    rw [hv]
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {P P' P''} f g := by
    refine Eq.trans ?_
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _)
    congr 1
    have hv : ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map (f ≫ g).2).val
        = ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map f.2).val ≫
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map g.2).val := by
      rw [prod_comp_snd]
      erw [Functor.map_comp]
      rw [SheafOfModules.comp_val]
    rw [hv, prod_comp_fst]
    ext1 Y
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app]
    exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- **(1.1.2 STEP 1, natural form)** Mathlib-gap anchor: module sheafification is
monoidal, stated as a **natural isomorphism of bifunctors**
`((P,Q) ↦ ~((~P).val ⊗ Q)) ≅ ((P,Q) ↦ ~(P ⊗ Q))`. The object-level comparison
`~((~P).val ⊗ Q) ≅ ~(P ⊗ Q)` is recovered as `(… ).app (P, Q)`; naturality (the
new content over the iter-031 object-level axiom) is exactly what the (1.1.2)
naturality layer needs. Net axiom count is unchanged — this *replaces* the
object-level `External.sheafifyTensorComparison`. See
`lem:sheafifyTensorComparison_uncond`. -/
axiom External.sheafifyTensorComparison {X : Scheme.{u}} :
    sheafifyFstTensorThenSheafify X ≅ tensorThenSheafify X

/-- Left-handed companion of `External.sheafifyTensorComparison` (natural form):
`((P,Q) ↦ ~(P ⊗ (~Q).val)) ≅ ((P,Q) ↦ ~(P ⊗ Q))`. See its doc. -/
axiom External.sheafifyTensorComparisonLeft {X : Scheme.{u}} :
    sheafifySndTensorThenSheafify X ≅ tensorThenSheafify X

/-- **(1.1.2 STEP 2)** Project-local (built on the STEP-1 anchor): the
**unconditional associator** of the `𝒪_X`-tensor `tensorMod`,
`(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)`. This is `tensorAssocOfLocallyBijective` run with the
unconditional comparisons `External.sheafifyTensorComparison{,Left}` (STEP 1, now
natural) in place of the conditional (false-hypothesis) ones; the middle step is the
sheafification of Mathlib's presheaf-level `MonoidalCategory.associator`
(`TensorProduct.assoc` pointwise). The comparison object-isos are extracted from the
natural anchors via `NatIso.app`. See `lem:tensorMod_assoc_uncond`. -/
noncomputable def tensorAssoc {X : Scheme.{u}} (A B C : X.Modules) :
    tensorMod (tensorMod A B) C ≅ tensorMod A (tensorMod B C) :=
  External.sheafifyTensorComparison.app
      (PresheafOfModules.Monoidal.tensorObj A.val B.val, C.val) ≪≫
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.associator
        (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
        A.val B.val C.val) ≪≫
    (External.sheafifyTensorComparisonLeft.app
      (A.val, PresheafOfModules.Monoidal.tensorObj B.val C.val)).symm

/-- **(1.1.2 STEP 3)** Project-local: the **rearrangement** of three `𝒪_X`-modules
`(F ⊗ Y) ⊗ L ≅ (F ⊗ L) ⊗ Y`, built from the unconditional associator `tensorAssoc`
(STEP 2) and the braiding `tensorBraiding` (swapping the inner `Y` and `L`). This is
the algebraic core that, instantiated at `Y = f^* M`, gives the rearrangement
`(F ⊗_S M) ⊗ L ≅ (F ⊗ L) ⊗_S M` of the (1.1.2) twist. The chain is
`(F ⊗ Y) ⊗ L ≅ F ⊗ (Y ⊗ L) ≅ F ⊗ (L ⊗ Y) ≅ (F ⊗ L) ⊗ Y`. -/
noncomputable def tensorRearrange {X : Scheme.{u}} (F Y L : X.Modules) :
    tensorMod (tensorMod F Y) L ≅ tensorMod (tensorMod F L) Y :=
  tensorAssoc F Y L ≪≫
    (tensorLeft F).mapIso (tensorBraiding Y L) ≪≫
    (tensorAssoc F L Y).symm

/-- **[internal-monoidal coherence: right-unitor triangle of `tensorMod`]** The
right-unitality triangle of the hand-built sheafified-tensor monoidal structure on
`X.Modules`: for `M N : X.Modules`, reassociating `(M ⊗ N) ⊗ 𝒪_X` to `M ⊗ (N ⊗ 𝒪_X)`
and then collapsing the inner `N ⊗ 𝒪_X` by the right unitor `ρ_N` equals collapsing
`(M ⊗ N) ⊗ 𝒪_X` directly by the right unitor `ρ_{M ⊗ N}`:
`α_{M,N,𝒪_X} ; (M ◁ ρ_N) = ρ_{M ⊗ N}`.

This is the standard monoidal right-unitor triangle, true in **any** monoidal
category. It is absent here only because Mathlib v4.30.0 carries **no**
`MonoidalCategory X.Modules` instance: the associator `tensorAssoc` and the unitors
`tensorRightUnitor` are assembled by hand on top of the anchored module-sheafification
comparisons `External.sheafifyTensorComparison{,Left}`, so their coherences are not
available from a Mathlib instance. The two sides cannot be reconciled by `coherence`/
`monoidal_coherence`/`aesop`: the LHS carries the opaque `sheafifyTensorComparison{,Left}`
(inside `tensorAssoc`) while the RHS (`tensorRightUnitor` = braiding ≫ presheaf left
unitor ≫ sheafification counit) is comparison-free, so the equation is recorded here as
an external input, in-family with `External.sheafifyTensorComparison{,Left}` (the whole
monoidal layer on `X.Modules` is anchor-backed). It mentions neither `H` nor
admissibility nor `f^*` nor Eilenberg–Watts, so it is strictly weaker than `H_tensor`.
See `lem:internal_tensorMod_rightUnitality`. -/
axiom External.tensorMod_rightUnitality {X : Scheme.{u}} (M N : X.Modules) :
    (tensorAssoc M N (SheafOfModules.unit X.ringCatSheaf)).hom
        ≫ (tensorLeft M).map (tensorRightUnitor N).hom
      = (tensorRightUnitor (tensorMod M N)).hom

/-! ### (1.1.2 naturality layer) — naturality of `tensorAssoc`, `tensorRearrangeNatIso`

The naturality of `tensorAssoc` in each variable is the `NatTrans.naturality` of the
comparison anchors `External.sheafifyTensorComparison{,Left}` (now `NatIso`s of bifunctors).
To *use* that naturality one identifies the anchor-bifunctor's action
`(sheafifyFstTensorThenSheafify X).map (a,b)` with the hand-built
`(tensorRight L).map ((tensorLeft F).map φ)`. Because `sheafifyFst/SndTensorThenSheafify`
and `tensorThenSheafify` are now **hand-built** (explicit `obj`/`map`, above), both the
object types and the morphism actions reduce *cheaply* (single `rfl`) to the `tensorMod`/
`tensorLeft`/`tensorRight` forms — the bridge lemmas below are therefore cheap `rfl`s. -/

/-- Cheap single-unfold of `tensorLeft`'s action on morphisms. -/
private lemma tensorLeft_map_eq {X : Scheme.{u}} (F : X.Modules) {N N' : X.Modules} (φ : N ⟶ N') :
    (tensorLeft F).map φ =
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) φ.val) := rfl

/-- Cheap single-unfold of `tensorRight`'s action on morphisms. -/
private lemma tensorRight_map_eq {X : Scheme.{u}} (L : X.Modules) {N N' : X.Modules} (φ : N ⟶ N') :
    (tensorRight L).map φ =
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val)) := rfl

/-- Cheap single-unfold of the hand-built bifunctor `sheafifyFstTensorThenSheafify`
(generic morphism `f`, so both sides are syntactically `~(…)` — avoids the `isDefEq`
blowup that the pair form `(a,b)` triggers). -/
private lemma sheafifyFst_map_eq {X : Scheme.{u}}
    {P P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ P') :
    (sheafifyFstTensorThenSheafify X).map f
    = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map f.1).val f.2) := rfl

/-- Cheap single-unfold of the hand-built bifunctor `sheafifySndTensorThenSheafify`. -/
private lemma sheafifySnd_map_eq {X : Scheme.{u}}
    {P P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ P') :
    (sheafifySndTensorThenSheafify X).map f
    = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom f.1
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map f.2).val) := rfl

/-- The presheaf-level tensor of two identities is the identity (assembled pointwise
from the `ModuleCat`-level `id_tensorHom_id`). Used to collapse the outer `F ⊗ L`
factor in the last-factor associator naturality. -/
private lemma presheaf_id_tensorHom_id {X : Scheme.{u}}
    (M N : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 M) (𝟙 N)
      = 𝟙 (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N) := by
  ext1 Z
  simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
  exact MonoidalCategory.id_tensorHom_id _ _

/-- The underlying presheaf morphism of the sheafification of an identity is the
identity. Bridges `(~(𝟙 P)).val` to `𝟙 (~P).val` in the last-factor naturality. -/
private lemma sheafify_map_id_val {X : Scheme.{u}}
    (P : PresheafOfModules X.ringCatSheaf.obj) :
    ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (𝟙 P)).val
      = 𝟙 ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).obj P).val := by
  rw [CategoryTheory.Functor.map_id, SheafOfModules.id_val]

/-- Cheap single-unfold of the hand-built bifunctor `tensorThenSheafify`. -/
private lemma tensorThenSheafify_map_eq {X : Scheme.{u}}
    {P P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ P') :
    (tensorThenSheafify X).map f
    = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom f.1 f.2) := rfl

/-- Index functor `Y ↦ (F.val ⊗ Y.val, L.val)` from `𝒪_X`-modules to the
presheaf-of-modules product, used to express the middle-factor naturality of
`tensorAssoc` as a whiskered comparison anchor. Hand-built (explicit `obj`/`map`
with `tensorHom`) to match the file's `tensorHom`-based conventions. -/
private noncomputable def assocIdxL {X : Scheme.{u}} (F L : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj Y := (PresheafOfModules.Monoidal.tensorObj F.val Y.val, L.val)
  map {Y Y'} φ := (PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) φ.val, 𝟙 L.val)
  map_id Y := by
    refine Prod.ext ?_ rfl
    change PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) (𝟙 Y.val) = 𝟙 _
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {Y Y' Y''} φ ψ := by
    refine Prod.ext ?_ (Category.id_comp _).symm
    change PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) (φ.val ≫ ψ.val)
        = PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) φ.val
          ≫ PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) ψ.val
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
      PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensor_comp _ _

/-- Index functor `Y ↦ (F.val, Y.val ⊗ L.val)`, the right-handed mirror of
`assocIdxL`, used for the last-factor naturality of `tensorAssoc`. -/
private noncomputable def assocIdxR {X : Scheme.{u}} (F L : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj Y := (F.val, PresheafOfModules.Monoidal.tensorObj Y.val L.val)
  map {Y Y'} φ := (𝟙 F.val, PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val))
  map_id Y := by
    refine Prod.ext rfl ?_
    change PresheafOfModules.Monoidal.tensorHom (𝟙 Y.val) (𝟙 L.val) = 𝟙 _
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {Y Y' Y''} φ ψ := by
    refine Prod.ext (Category.id_comp _).symm ?_
    change PresheafOfModules.Monoidal.tensorHom (φ.val ≫ ψ.val) (𝟙 L.val)
        = PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val)
          ≫ PresheafOfModules.Monoidal.tensorHom ψ.val (𝟙 L.val)
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
      PresheafOfModules.id_app]
    exact MonoidalCategory.comp_tensor_id _ _

/-- **(1.1.2 naturality, middle factor)** Naturality of the unconditional associator
`tensorAssoc F · L` in its middle factor, packaged as a natural isomorphism of
endofunctors `tensorLeft F ⋙ tensorRight L ≅ tensorRight L ⋙ tensorLeft F`
(`Y ↦ ((F ⊗ Y) ⊗ L ≅ F ⊗ (Y ⊗ L))`). Built as the composite of three natural
isomorphisms — the two comparison anchors (`External.sheafifyTensorComparison{,Left}`,
now `NatIso`s of bifunctors), whiskered by the index functors `assocIdxL`/`assocIdxR`,
and the sheafified presheaf associator. Each leg's naturality is a single square proved
through the generic bridge lemmas (objects stay abstract, so the concrete-object
`isDefEq` blowup is avoided); composing at the `Iso` level (`≪≫`) handles the object
identifications at full transparency. See `lem:tensorAssocNatIso2`. -/
noncomputable def tensorAssocNatIso₂ {X : Scheme.{u}} (F L : X.Modules) :
    tensorLeft F ⋙ tensorRight L ≅ tensorRight L ⋙ tensorLeft F :=
  -- leg 1: the first comparison anchor, whiskered, as a natural iso
  (NatIso.ofComponents
    (fun Y => (External.sheafifyTensorComparison (X := X)).app
      (PresheafOfModules.Monoidal.tensorObj F.val Y.val, L.val)) (by
      intro Y Y' φ
      have h := (External.sheafifyTensorComparison (X := X)).hom.naturality
        ((PresheafOfModules.Monoidal.tensorHom (𝟙 F.val) φ.val, 𝟙 L.val) :
          (PresheafOfModules.Monoidal.tensorObj F.val Y.val, L.val) ⟶
            (PresheafOfModules.Monoidal.tensorObj F.val Y'.val, L.val))
      simp only [assocIdxL, sheafifyFst_map_eq, tensorRight_map_eq, tensorLeft_map_eq,
        tensorThenSheafify_map_eq, Iso.app_hom, Functor.comp_map] at h ⊢
      exact h) :
    tensorLeft F ⋙ tensorRight L ≅ assocIdxL F L ⋙ tensorThenSheafify X) ≪≫
  -- leg 2: the sheafified presheaf associator, as a natural iso
  (NatIso.ofComponents
    (fun Y => (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).mapIso
        (MonoidalCategory.associator
          (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
          F.val Y.val L.val)) (by
      intro Y Y' φ
      simp only [assocIdxL, assocIdxR, Functor.comp_map, tensorThenSheafify_map_eq,
        Functor.mapIso_hom]
      exact ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
        (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).congr_map
          (MonoidalCategory.associator_naturality
            (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            (𝟙 F.val) φ.val (𝟙 L.val))).trans
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map_comp _ _))) :
    assocIdxL F L ⋙ tensorThenSheafify X ≅ assocIdxR F L ⋙ tensorThenSheafify X) ≪≫
  -- leg 3: the last (left) comparison anchor, whiskered and inverted
  (NatIso.ofComponents
    (fun Y => ((External.sheafifyTensorComparisonLeft (X := X)).app
      (F.val, PresheafOfModules.Monoidal.tensorObj Y.val L.val)).symm) (by
      intro Y Y' φ
      have h := (External.sheafifyTensorComparisonLeft (X := X)).inv.naturality
        ((𝟙 F.val, PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val)) :
          (F.val, PresheafOfModules.Monoidal.tensorObj Y.val L.val) ⟶
            (F.val, PresheafOfModules.Monoidal.tensorObj Y'.val L.val))
      simp only [assocIdxR, sheafifySnd_map_eq, tensorRight_map_eq, tensorLeft_map_eq,
        tensorThenSheafify_map_eq, Iso.app_inv, Iso.symm_hom, Functor.comp_map] at h ⊢
      exact h) :
    assocIdxR F L ⋙ tensorThenSheafify X ≅ tensorRight L ⋙ tensorLeft F)

/-- Index functor `Y ↦ (F.val ⊗ L.val, Y.val)`, the last-factor analogue of
`assocIdxL` (here the *last* tensor slot `Y` varies). -/
private noncomputable def assocIdxL₃ {X : Scheme.{u}} (F L : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj Y := (PresheafOfModules.Monoidal.tensorObj F.val L.val, Y.val)
  map {Y Y'} φ :=
    (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val), φ.val)
  map_id Y := by
    refine Prod.ext (presheaf_id_tensorHom_id F.val L.val) ?_
    exact SheafOfModules.id_val Y
  map_comp {Y Y' Y''} φ ψ := by
    refine Prod.ext ?_ (SheafOfModules.comp_val φ ψ)
    have e := presheaf_id_tensorHom_id (X := X) F.val L.val
    change PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val)
        = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val)
          ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val)
    exact (Category.id_comp _).symm.trans
      (congrArg (· ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val))
        e.symm)

/-- Index functor `Y ↦ (F.val, L.val ⊗ Y.val)`, the last-factor analogue of
`assocIdxR`. -/
private noncomputable def assocIdxR₃ {X : Scheme.{u}} (F L : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj Y := (F.val, PresheafOfModules.Monoidal.tensorObj L.val Y.val)
  map {Y Y'} φ := (𝟙 F.val, PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) φ.val)
  map_id Y := by
    refine Prod.ext rfl ?_
    change PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 Y.val) = 𝟙 _
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensorHom_id _ _
  map_comp {Y Y' Y''} φ ψ := by
    refine Prod.ext (Category.id_comp _).symm ?_
    change PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (φ.val ≫ ψ.val)
        = PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) φ.val
          ≫ PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) ψ.val
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
      PresheafOfModules.id_app]
    exact MonoidalCategory.id_tensor_comp _ _

/-- **(1.1.2 naturality, last factor)** Naturality of the unconditional associator
`tensorAssoc F L ·` in its last factor, packaged as a natural isomorphism of
endofunctors `tensorLeft L ⋙ tensorLeft F ≅ tensorLeft (F ⊗ L)`
(`Y ↦ (F ⊗ (L ⊗ Y) ≅ (F ⊗ L) ⊗ Y)`). The mirror of `tensorAssocNatIso₂`, built as the
`.symm` of the composite of the three legs `tensorLeft (F ⊗ L) ≅ … ≅ tensorLeft L ⋙
tensorLeft F` (comparison anchors whiskered by `assocIdxL₃`/`assocIdxR₃` + sheafified
associator). See `lem:tensorAssocNatIso3`. -/
noncomputable def tensorAssocNatIso₃ {X : Scheme.{u}} (F L : X.Modules) :
    tensorLeft L ⋙ tensorLeft F ≅ tensorLeft (tensorMod F L) :=
  ((NatIso.ofComponents
    (fun Y => (External.sheafifyTensorComparison (X := X)).app
      (PresheafOfModules.Monoidal.tensorObj F.val L.val, Y.val)) (by
      intro Y Y' φ
      have h := (External.sheafifyTensorComparison (X := X)).hom.naturality
        ((PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (𝟙 L.val), φ.val) :
          (PresheafOfModules.Monoidal.tensorObj F.val L.val, Y.val) ⟶
            (PresheafOfModules.Monoidal.tensorObj F.val L.val, Y'.val))
      simp only [assocIdxL₃, sheafifyFst_map_eq, tensorLeft_map_eq, tensorThenSheafify_map_eq,
        Iso.app_hom, Functor.comp_map] at h ⊢
      convert h using 4
      exact congrArg
        (fun a => (PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map
            (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) a φ.val))
        (((congrArg (fun m => ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map m).val) (presheaf_id_tensorHom_id F.val L.val)).trans
            (sheafify_map_id_val _)).symm)) :
    tensorLeft (tensorMod F L) ≅ assocIdxL₃ F L ⋙ tensorThenSheafify X) ≪≫
  (NatIso.ofComponents
    (fun Y => (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).mapIso
        (MonoidalCategory.associator
          (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
          F.val L.val Y.val)) (by
      intro Y Y' φ
      simp only [assocIdxL₃, assocIdxR₃, Functor.comp_map, tensorThenSheafify_map_eq,
        Functor.mapIso_hom]
      exact ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
        (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).congr_map
          (MonoidalCategory.associator_naturality
            (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            (𝟙 F.val) (𝟙 L.val) φ.val)).trans
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map_comp _ _))) :
    assocIdxL₃ F L ⋙ tensorThenSheafify X ≅ assocIdxR₃ F L ⋙ tensorThenSheafify X) ≪≫
  (NatIso.ofComponents
    (fun Y => ((External.sheafifyTensorComparisonLeft (X := X)).app
      (F.val, PresheafOfModules.Monoidal.tensorObj L.val Y.val)).symm) (by
      intro Y Y' φ
      have h := (External.sheafifyTensorComparisonLeft (X := X)).inv.naturality
        ((𝟙 F.val, PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) φ.val) :
          (F.val, PresheafOfModules.Monoidal.tensorObj L.val Y.val) ⟶
            (F.val, PresheafOfModules.Monoidal.tensorObj L.val Y'.val))
      simp only [assocIdxR₃, sheafifySnd_map_eq, tensorLeft_map_eq, tensorThenSheafify_map_eq,
        Iso.app_inv, Iso.symm_hom, Functor.comp_map] at h ⊢
      exact h) :
    assocIdxR₃ F L ⋙ tensorThenSheafify X ≅ tensorLeft L ⋙ tensorLeft F)).symm

/-- **(1.1.2 STEP C-iii)** Naturality of the rearrangement `tensorRearrange F · L`,
packaged as a natural isomorphism of endofunctors
`tensorLeft F ⋙ tensorRight L ≅ tensorLeft (F ⊗ L)`
(`Y ↦ ((F ⊗ Y) ⊗ L ≅ (F ⊗ L) ⊗ Y)`). Composes the three natural steps: the
middle-factor associator naturality `tensorAssocNatIso₂`, the inner braiding
naturality `tensorBraidingNatIso L` (whiskered into `tensorLeft F`, swapping `Y` and
`L`), and the last-factor associator naturality `tensorAssocNatIso₃`. See
`lem:tensorRearrange_natIso`. -/
noncomputable def tensorRearrangeNatIso {X : Scheme.{u}} (F L : X.Modules) :
    tensorLeft F ⋙ tensorRight L ≅ tensorLeft (tensorMod F L) :=
  tensorAssocNatIso₂ F L ≪≫
    Functor.isoWhiskerRight (tensorBraidingNatIso L) (tensorLeft F) ≪≫
    tensorAssocNatIso₃ F L

/-- Project-local (Mathlib gap): the base-change tensor functor
`M ↦ F ⊗_S M` from `𝒪_S`-modules to `𝒪_X`-modules (pull `M` back along `f` and
tensor with `F` over `𝒪_X`). Realized as the composite of Mathlib's pullback
functor `Scheme.Modules.pullback f` with the hand-built `tensorLeft F`. -/
noncomputable def tensorBaseChangeFunctor {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    S.Modules ⥤ X.Modules :=
  Scheme.Modules.pullback f ⋙ tensorLeft F

/-- `F ⊗_S M`, the base change of `F` by an `𝒪_S`-module `M`. -/
noncomputable def tensorBC (f : X ⟶ S) (F : X.Modules) (M : S.Modules) : X.Modules :=
  (tensorBaseChangeFunctor f F).obj M

/-- The covariant functor `M ↦ Hom_X(I, F ⊗_S M)` on quasi-coherent
`𝒪_S`-modules, valued in types. `H(I,F)` is, by definition, an object
corepresenting this functor. -/
noncomputable def homTensorFunctor (f : X ⟶ S) (I F : X.Modules) : S.Modules ⥤ Type u :=
  tensorBaseChangeFunctor f F ⋙ coyoneda.obj (op I)

/-! ## Project-local Mathlib supplement — InternalHom (brick 1 foundation)

Infrastructure toward the internal-hom sheaf `internalHom I : X.Modules ⥤ X.Modules`
(`def:internalHom`), the first foundational brick of the relative-Ext build (`def:relExt`).

The **section module** of `ℋom_{𝒪_X}(I,M)` over an open `U` is the `𝒪_X(U)`-linear
maps `I|_U ⟶ M|_U`, i.e. a hom-set in `(↑U).Modules` carrying a `Γ(↑U,⊤) = 𝒪_X(U)`-module
structure. That per-section module structure — `Module Γ(Y,⊤) (M ⟶ N)` for `M N : Y.Modules`
— is *not* in Mathlib (the structure-sheaf sections form a `RingCat`, which forgets
commutativity, so the `Linear`-over-a-`CommRing` structure on `ModuleCat` hom-sets is not
directly available on `SheafOfModules` hom-sets). We build it here from scratch: a global
section `r : Γ(Y,⊤)` acts on `φ : M ⟶ N` by scaling each `φ.val.app U` by the restriction
`r|_U`, the resulting family being natural (semilinear-restriction compatible). This is the
atom each `internalHom` section module is an instance of (take `Y := ↑U`). -/

/-- Restrict a global section `r : Γ(Y,⊤)` of the structure sheaf to the open `U.unop`,
landing in the section ring `↑(Y.ringCatSheaf.obj.obj U)` (`= Γ(Y, U.unop)`). -/
private noncomputable def globalSectionRestrict {Y : Scheme.{u}} (r : Γ(Y, ⊤))
    (U : (TopologicalSpace.Opens ↑Y)ᵒᵖ) : ↑(Y.ringCatSheaf.obj.obj U) :=
  (Y.ringCatSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r

private lemma globalSectionRestrict_one {Y : Scheme.{u}}
    (U : (TopologicalSpace.Opens ↑Y)ᵒᵖ) :
    globalSectionRestrict (1 : Γ(Y, ⊤)) U = 1 := by
  unfold globalSectionRestrict; exact map_one _

private lemma globalSectionRestrict_zero {Y : Scheme.{u}}
    (U : (TopologicalSpace.Opens ↑Y)ᵒᵖ) :
    globalSectionRestrict (0 : Γ(Y, ⊤)) U = 0 := by
  unfold globalSectionRestrict; exact map_zero _

private lemma globalSectionRestrict_mul {Y : Scheme.{u}} (r s : Γ(Y, ⊤))
    (U : (TopologicalSpace.Opens ↑Y)ᵒᵖ) :
    globalSectionRestrict (r * s) U = globalSectionRestrict r U * globalSectionRestrict s U := by
  unfold globalSectionRestrict; exact map_mul _ _ _

private lemma globalSectionRestrict_add {Y : Scheme.{u}} (r s : Γ(Y, ⊤))
    (U : (TopologicalSpace.Opens ↑Y)ᵒᵖ) :
    globalSectionRestrict (r + s) U = globalSectionRestrict r U + globalSectionRestrict s U := by
  unfold globalSectionRestrict; exact map_add _ _ _

/-- Restricting a *global* section commutes with any further structure-sheaf restriction
map `R.map f`: both sides are `r` restricted to the smaller open (uniqueness of the
`Opens` morphism into `⊤`). -/
private lemma globalSectionRestrict_naturality {Y : Scheme.{u}} (r : Γ(Y, ⊤))
    {U V : (TopologicalSpace.Opens ↑Y)ᵒᵖ} (f : U ⟶ V) :
    (Y.ringCatSheaf.obj.map f) (globalSectionRestrict r U) = globalSectionRestrict r V := by
  unfold globalSectionRestrict
  rw [← CategoryTheory.comp_apply, ← Y.ringCatSheaf.obj.map_comp]; congr 1

/-- `restrictScalars` along `g : A →+* B` carries a `B`-scaled morphism `g a • h` to the
`A`-scaled restriction `a • restrictScalars h`. The semilinear-restriction compatibility
underlying the naturality of `internalHom`'s scalar action. -/
private lemma restrictScalars_map_smul {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    {P Q : ModuleCat.{u} B} (a : A) (h : P ⟶ Q) :
    (ModuleCat.restrictScalars g).map ((g a) • h) = a • (ModuleCat.restrictScalars g).map h := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  rw [ModuleCat.restrictScalars.map_apply]
  change (g a • h) x = a • ((ModuleCat.restrictScalars g).map h) x
  rw [ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars.smul_def (M := Q)]; simp

/-- The underlying presheaf-of-modules morphism of `r • φ`: scale each section component
`φ.val.app U` by the restricted global section `r|_U`. Naturality is the
semilinear-restriction compatibility (`restrictScalars_map_smul`) plus `φ`'s naturality. -/
private noncomputable def internalHomSmulVal {Y : Scheme.{u}} {M N : Y.Modules}
    (r : Γ(Y, ⊤)) (φ : M ⟶ N) : M.val ⟶ N.val :=
  PresheafOfModules.Hom.mk
    (fun U =>
      letI : CommRing ↑(Y.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing Γ(Y, U.unop))
      globalSectionRestrict r U • φ.val.app U) (by
    intro U V f
    letI cU : CommRing ↑(Y.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing Γ(Y, U.unop))
    letI cV : CommRing ↑(Y.ringCatSheaf.obj.obj V) := inferInstanceAs (CommRing Γ(Y, V.unop))
    change M.val.map f ≫ (ModuleCat.restrictScalars _).map (globalSectionRestrict r V • φ.val.app V)
        = (globalSectionRestrict r U • φ.val.app U) ≫ N.val.map f
    rw [← globalSectionRestrict_naturality r f,
      restrictScalars_map_smul (RingCat.Hom.hom (Y.ringCatSheaf.obj.map f))
        (globalSectionRestrict r U) (φ.val.app V),
      Linear.comp_smul, φ.val.naturality f, Linear.smul_comp])

/-- **Brick 1 foundation (Mathlib gap).** The module structure on hom-sets of sheaves of
modules over a scheme `Y`, over the global sections `Γ(Y,⊤)` of the structure sheaf: a global
function `r` acts on `φ : M ⟶ N` by scaling each section by `r|_U`. This is the per-section
module structure that every section of the internal-hom sheaf `ℋom_{𝒪_X}(I,-)` carries
(taking `Y := ↑U` for an open `U ⊆ X`), and is absent from Mathlib because the structure
sheaf is valued in `RingCat`, hiding the commutativity needed for the `Linear` structure on
`ModuleCat` hom-sets. See `def:internalHom`. -/
noncomputable instance homModuleOverGlobalSections {Y : Scheme.{u}} {M N : Y.Modules} :
    Module Γ(Y, ⊤) (M ⟶ N) where
  smul r φ := ⟨internalHomSmulVal r φ⟩
  one_smul φ := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict 1 X • φ.val.app X = φ.val.app X
    rw [globalSectionRestrict_one, one_smul]
  mul_smul r s φ := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict (r * s) X • φ.val.app X
        = globalSectionRestrict r X • globalSectionRestrict s X • φ.val.app X
    rw [globalSectionRestrict_mul, mul_smul]
  smul_zero r := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict r X • (0 : M.val.obj X ⟶ N.val.obj X) = 0
    exact smul_zero _
  smul_add r φ ψ := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict r X • (φ.val.app X + ψ.val.app X)
        = globalSectionRestrict r X • φ.val.app X + globalSectionRestrict r X • ψ.val.app X
    rw [smul_add]
  add_smul r s φ := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict (r + s) X • φ.val.app X
        = globalSectionRestrict r X • φ.val.app X + globalSectionRestrict s X • φ.val.app X
    rw [globalSectionRestrict_add, add_smul]
  zero_smul φ := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change globalSectionRestrict 0 X • φ.val.app X = 0
    rw [globalSectionRestrict_zero, zero_smul]

/-- **Brick 1 foundation (Mathlib gap).** The category of `𝒪_Y`-modules is `Γ(Y,⊤)`-linear:
composition is bilinear over the global functions acting by `homModuleOverGlobalSections`.
This is the structural form of the per-section module structure, packaging that internal-hom's
scalar action is compatible with composition (needed for `internalHom`'s functoriality and the
`𝒪_S`-linearity of `relExt`). Absent from Mathlib for the same `RingCat`-vs-`CommRing` reason.
See `def:internalHom`. -/
noncomputable instance linearOverGlobalSections {Y : Scheme.{u}} :
    Linear Γ(Y, ⊤) Y.Modules where
  smul_comp P Q R' r f g := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change (globalSectionRestrict r X • f.val.app X) ≫ g.val.app X
        = globalSectionRestrict r X • (f.val.app X ≫ g.val.app X)
    rw [Linear.smul_comp]
  comp_smul P Q R' f r g := by
    apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro X
    letI : CommRing ↑(Y.ringCatSheaf.obj.obj X) := inferInstanceAs (CommRing Γ(Y, X.unop))
    change f.val.app X ≫ (globalSectionRestrict r X • g.val.app X)
        = globalSectionRestrict r X • (f.val.app X ≫ g.val.app X)
    rw [Linear.comp_smul]

/-- Project-local (Mathlib gap): the relative local Ext sheaf
`sExt^q_{X/S}(I,F)`, an `𝒪_S`-module (morally `R^q f_*` of the sheaf-Ext of `I`
and `F`). -/
noncomputable opaque relExt {X S : Scheme.{u}} (q : ℕ) (f : X ⟶ S) (I F : X.Modules) : S.Modules

/-- Project-local (Mathlib gap): the (absolute) Ext group `Ext^q_Y(M, N)` of two
`𝒪_Y`-modules, used only to phrase the acyclicity in `exists_acyclic_surjection`.

Realized via the standard derived category of `Y.Modules` (an abelian category):
`Ext^q_Y(M,N)` is `CategoryTheory.Abelian.Ext M N q`, the `q`-th Yoneda Ext.
The target universe is `Ab.{u+1}` (not `Ab.{u}`): `Abelian.Ext` lives one universe
up because it is a morphism set in the derived category. This is harmless — the
group is only ever used through `IsZero (extGroup …)`, which is universe-agnostic. -/
noncomputable def extGroup {Y : Scheme.{u}} (q : ℕ) (M N : Y.Modules) : Ab.{u+1} :=
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  AddCommGrpCat.of (CategoryTheory.Abelian.Ext M N q)

/-- Project-local (Mathlib gap): sheaf cohomology `H^q(U, F)` as an abelian
group, used only to state the affine-acyclicity input. Realized as the absolute
Ext group `Ext^q_U(𝒪_U, F)` of the structure sheaf (monoidal unit) against `F`,
which is the usual cohomology `H^q(U, F)`. Lives in `Ab.{u+1}` for the same
universe reason as `extGroup`; only ever used through `IsZero (…)`. -/
noncomputable def sheafCohomology {U : Scheme.{u}} (q : ℕ) (F : U.Modules) : Ab.{u+1} :=
  extGroup q (SheafOfModules.unit U.ringCatSheaf) F

/-- Project-local (Mathlib gap): `M` is locally free of finite rank on the open
`U ⊆ S`. Realized faithfully: at every point `x ∈ U` there is an open neighbourhood
`V ⊆ U` on which the restriction of `M` (pulled back along the open immersion
`V.ι`, using that `S.Modules = SheafOfModules S.ringCatSheaf`) is isomorphic to a
*finite* free sheaf of modules `SheafOfModules.free Λ` (`Finite Λ`). -/
def IsLocallyFreeOfFiniteRankOn {S : Scheme.{u}} (M : S.Modules) (U : S.Opens) : Prop :=
  ∀ x : S, x ∈ U → ∃ (V : S.Opens), x ∈ V ∧ V ≤ U ∧
    ∃ (Λ : Type u), Finite Λ ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅
        SheafOfModules.free (R := (↑V : Scheme.{u}).ringCatSheaf) Λ)

/-- Project-local (Mathlib gap): the open `U ⊆ S` is retrocompact (its inclusion
is quasi-compact). Realized as quasi-compactness of the open immersion `U.ι : U ⟶ S`
via Mathlib's `QuasiCompact` predicate on scheme morphisms. -/
def IsRetrocompact {S : Scheme.{u}} (U : S.Opens) : Prop :=
  QuasiCompact U.ι

/-- Project-local (Mathlib gap): the fibre Ext vanishes,
`Ext^q_{X(s)}(I(s), F(s)) = 0`, at the point `s ∈ S`.

Realized as the absolute Ext group on the scheme-theoretic fibre `X(s) = f.fiber s`
(Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`) of the restrictions
`I(s) = j^* I`, `F(s) = j^* F` along the fibre inclusion `j = f.fiberι s : X(s) ⟶ X`
(pulled back via `Scheme.Modules.pullback`), wrapped in `IsZero`. This is exactly
the paper's condition `Ext^q_{X(s)}(I(s), F(s)) = 0` (AK §1, quoted in
`thm:H_locallyFree`). -/
def FiberExtVanishes {X S : Scheme.{u}} (q : ℕ) (f : X ⟶ S) (I F : X.Modules)
    (s : S) : Prop :=
  IsZero (extGroup q ((Scheme.Modules.pullback (f.fiberι s)).obj I)
                     ((Scheme.Modules.pullback (f.fiberι s)).obj F))

/-- Project-local (Mathlib gap): the relative Ext sheaf `relExt c f I F` is
locally finitely presented and flat over the open `V ⊆ S`. -/
opaque IsLFPAndFlatOn {X S : Scheme.{u}} (c : ℕ) (f : X ⟶ S) (I F : X.Modules)
    (V : S.Opens) : Prop

/-- Project-local (Mathlib gap): `J` is a free `𝒪_X`-module, i.e. isomorphic to a
coproduct `𝒪_X^{(Λ)}` of copies of the unit. Realized via Mathlib's
`SheafOfModules.free`. -/
def IsFreeMod {X : Scheme.{u}} (J : X.Modules) : Prop :=
  ∃ (Λ : Type u), Nonempty (J ≅ SheafOfModules.free (R := X.ringCatSheaf) Λ)

/-- Project-local (Mathlib gap): the additive endofunctor `T` on finitely
generated `A`-modules is half-exact. Realized directly: for every short exact
sequence `S` of `A`-modules and every choice of additive structure on `T` (so that
`T` preserves zero morphisms and `S.map T` is defined), the image short complex
`S.map T` is exact at its middle object. -/
def IsHalfExact {A : Type u} [CommRing A] (T : ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A) : Prop :=
  ∀ [T.Additive] (S : ShortComplex (ModuleCat.{u} A)), S.ShortExact → (S.map T).Exact

/-- The standing hypotheses of Altman–Kleiman (1.1): `f` is finitely presented
and proper, `I` and `F` are locally finitely presented, and `F` is flat over the
base. These are the hypotheses under which `H(I,F)` and `h(I,F)` are defined. -/
structure Admissible (f : X ⟶ S) (I F : X.Modules) : Prop where
  proper : IsProper f
  finitePresentation : LocallyOfFinitePresentation f
  lfp_I : IsLFP I
  lfp_F : IsLFP F
  flat_F : IsSFlat f F

/-! ## External dependency anchors (EGA/OB) — realized as axioms -/

/-- **[EGA III₂, 7.7.8/7.7.9; ASDS (12)]** Existence of the representing module
`H`. Over a (Noetherian) base the functor `M ↦ Hom_X(I, F ⊗_S M)` on
quasi-coherent `𝒪_S`-modules is corepresentable; combined with descent this
gives `H(I,F)`. See `thm:ega_H_existence`. -/
axiom External.H_existence (f : X ⟶ S) (I F : X.Modules) (ha : Admissible f I F) :
    (homTensorFunctor f I F).IsCorepresentable

/-- **[Serre / EGA]** Vanishing of higher cohomology of a quasi-coherent sheaf on
an affine scheme: `H^q(U, F) = 0` for `q > 0`. See `thm:ega_ext_affine_acyclic`. -/
axiom External.ext_affine_acyclic {U : Scheme.{u}} (q : ℕ) (F : U.Modules)
    (hU : IsAffine U) (hF : F.IsQuasicoherent) (hq : 0 < q) :
    IsZero (sheafCohomology q F)

/-- **[EGA IV₃, §8]** Descent of finitely presented data to a Noetherian base.
For a finitely presented morphism `f : X ⟶ S` of affine schemes and an `S`-flat,
finitely presented `𝒪_X`-module `I`, the data `(X, I)` descend to a Noetherian
affine base: there are a Noetherian ring `A₀`, a morphism `p : X ⟶ Spec A₀`, and
a finitely presented `𝒪_{Spec A₀}`-module `I₀` with `I ≅ p* I₀`.

This is the **data-descent form** actually consumed by the 1.4 free-resolution
step. The source quote ("all the data descend to S₀") covers the full data, so
recording the descended module `I₀` (not merely the Noetherian base reduction) is
a *faithful* transcription, not a strengthening beyond what EGA IV₃ §8 supplies.
The descended base is delivered as a literal `Spec A₀` (EGA descent produces a
finitely generated `ℤ`-algebra, which is Noetherian), so the affine bridge applies
downstream with no scheme→`Spec` transport. See `thm:ega_descent_noetherian`. -/
axiom External.descent_noetherian {X S : Scheme.{u}} (hS : IsAffine S)
    (f : X ⟶ S) (haX : IsAffine X) (I : X.Modules) (hI : IsLFP I) (hflat : IsSFlat f I) :
    ∃ (A₀ : CommRingCat.{u}) (_ : IsNoetherianRing ↑A₀) (p : X ⟶ Spec A₀)
      (I₀ : (Spec A₀).Modules), I₀.IsFinitePresentation ∧
        Nonempty (I ≅ (Scheme.Modules.pullback p).obj I₀)

/-- **[OB, 2.1] / [EGA III₂, 7.5.3]** Vanishing of a half-exact additive functor
over a Noetherian local ring: if `T` is half-exact and `T(k) = 0` then
`T(M) = 0` for every finitely generated module `M`. See `thm:ob_halfexact_free`. -/
axiom External.halfexact_free (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (T : ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A) [T.Additive]
    (hHE : IsHalfExact T)
    (hk : IsZero (T.obj (ModuleCat.of A (IsLocalRing.ResidueField A))))
    (M : ModuleCat.{u} A) :
    IsZero (T.obj M)

/-- **[EGA IV₃, 12.3.4]** Openness (and retrocompactness) of the local
Ext-vanishing locus `{ s : sExt^q_{X(s)}(I(s),F(s)) = 0 }`.
See `thm:ega_ext_vanishing_open`. -/
axiom External.ext_vanishing_open (q : ℕ) (f : X ⟶ S) (I F : X.Modules) :
    IsOpen {s : S | FiberExtVanishes q f I F s}

/-- **[EGA III₂, 12.3.3]** Coherence / local finite presentation of the relative
local Ext module over a Noetherian base. See `thm:ega_ext_coherent_fp`. -/
axiom External.ext_coherent_fp (c : ℕ) (f : X ⟶ S) (I F : X.Modules)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hI : IsLFP I) (hF : IsLFP F) :
    IsLFP (relExt c f I F)

/-- **[Stacks 01IA + 01PC]** Affine quasi-coherence (essential surjectivity of
`tilde` onto finitely presented quasi-coherent sheaves). On an affine scheme
`Spec R`, a finitely presented `𝒪_{Spec R}`-module `I` is the tilde of a finitely
presented `R`-module `M` (namely `M = Γ(Spec R, I)`).

By **Stacks 01IA** (`F ≅ ~Γ(F)` for a quasi-coherent sheaf on an affine scheme)
the quasi-coherent `I` is `≅ ~Γ(I)`; by **Stacks 01PC** (`~M` finitely presented
⇔ `M` finitely presented as an `R`-module) the module `M = Γ(I)` is finitely
presented. This is the essential-surjectivity half of the affine equivalence
`QCoh(Spec R) ≃ Mod_R`, absent from Mathlib v4.30.0 (`tilde.functor` has
`Full`/`Faithful`/`IsLeftAdjoint` but no `EssSurj`/`essImage`). Anchored to
complete the affine bridge; see `thm:stacks_affine_fp_tilde` and quotes in
`references/stacks-qcoh-affine.md`. -/
axiom External.affine_fp_tilde {R : CommRingCat.{u}} (I : (Spec R).Modules)
    [I.IsFinitePresentation] :
    ∃ (M : ModuleCat.{u} ↑R), Module.FinitePresentation ↑R M ∧
      Nonempty (AlgebraicGeometry.tilde M ≅ I)

/-- **[Stacks 01PC, forward]** Tilde of a finitely presented module is a finitely
presented sheaf. The forward direction of the affine quasi-coherence equivalence
(`thm:stacks_affine_fp_tilde` supplies the reverse): for a finitely presented
`R`-module `M`, the quasi-coherent sheaf `~M` on `Spec R` is of finite presentation
as an `𝒪_{Spec R}`-module.

Mathematically this is pure assembly from the landed bridge lemmas: `M` fp gives a
global free presentation `Rᵐ → Rⁿ → M → 0` which `tilde_exact` + `tilde_free` tilde
to a presentation of `~M` by finite free sheaves, and a global presentation by
finite free sheaves is a finite-presentation datum (`SheafOfModules.IsFinitePresentation`
via `Presentation.quasicoherentData` on the trivial cover). That last globalization
step (turning a global finite `SheafOfModules.Presentation` into the cover-indexed
`QuasicoherentData` finite-presentation witness) is the genuine remaining Mathlib
gap; anchored here as the cited Stacks 01PC forward direction to keep the
free-resolution step (1.4) unblocked, and flagged buildable/upstreamable. -/
axiom External.tilde_isFP {R : CommRingCat.{u}} (M : ModuleCat.{u} ↑R)
    [Module.FinitePresentation ↑R M] :
    IsLFP (AlgebraicGeometry.tilde M : (Spec R).Modules)

/-- **[standard / EGA]** Flat pullback preserves short exactness. Pullback of
sheaves of modules is right exact always, and left exact (hence preserves short
exact sequences) when the term being killed is flat over the base. Mathlib has this
at the module level (`Module.Flat.lTensor_shortComplex_exact`) but NOT for
`Scheme.Modules.pullback` of a `ShortComplex` of sheaves of modules. Anchored as the
standard input used in the last step of the 1.4 proof ("since `I` is flat, the
pullback of the sequence on `X₀` is the desired sequence on `X`"); the flatness
hypothesis is the genuine one 1.4 has — the right-hand term `I`, isomorphic to the
pullback `p* sc₀.X₃`, is `S`-flat. See `thm:flat_pullback_exact`. -/
axiom External.flat_pullback_exact {X X₀ S : Scheme.{u}} (f : X ⟶ S) (p : X ⟶ X₀)
    (sc₀ : ShortComplex X₀.Modules) (hsc : sc₀.ShortExact)
    (I : X.Modules) (hflat : IsSFlat f I)
    (e : I ≅ (Scheme.Modules.pullback p).obj sc₀.X₃) :
    (sc₀.map (Scheme.Modules.pullback p)).ShortExact

/-- **[standard / EGA]** Pullback of a free `𝒪_Y`-module along a scheme morphism `p`
is a free `𝒪_X`-module. Mathematically immediate: `p^* 𝒪_Y ≅ 𝒪_X`, and the pullback —
a left adjoint — preserves the coproduct defining `free Λ = ∐_Λ 𝒪_Y`, so
`(pullback p).obj (free Λ) ≅ free Λ`. The precise iso is
`SheafOfModules.pullbackObjFreeIso`, which however requires the site functor
`Opens.map p.base` to be **final**; that instance is absent from Mathlib v4.30.0 for a
general scheme morphism (the structure-sheaf-pullback iso for `Scheme.Modules.pullback`
is not wired up). Anchored as the standard pullback-preserves-free fact invoked
implicitly in the 1.4 Step-3 ("the pullback of the sequence on `X₀` is the desired
sequence on `X`"). See `thm:pullback_preserves_free`. -/
axiom External.pullback_isFreeMod {X Y : Scheme.{u}} (p : X ⟶ Y) {M : Y.Modules}
    (h : IsFreeMod M) : IsFreeMod ((Scheme.Modules.pullback p).obj M)

/-- **[standard / EGA]** Pullback preserves finite presentation: if `M` is a locally
finitely presented `𝒪_Y`-module then so is its pullback `(pullback p).obj M`. Standard
base-change stability of finite presentation; Mathlib v4.30.0 has no instance or lemma
supplying `SheafOfModules.IsFinitePresentation ((Scheme.Modules.pullback p).obj M)` from
`M.IsFinitePresentation` (the fp-globalization / structure-sheaf-pullback reconstruction
is absent for `Scheme.Modules.pullback`). Anchored as the standard
pullback-preserves-finite-presentation fact invoked implicitly in the 1.4 Step-3.
See `thm:pullback_preserves_fp`. -/
axiom External.pullback_isLFP {X Y : Scheme.{u}} (p : X ⟶ Y) {M : Y.Modules}
    (h : IsLFP M) : IsLFP ((Scheme.Modules.pullback p).obj M)

/-- **[standard / EGA]** Strong monoidality of the pullback (inverse-image) functor
`f^* = Scheme.Modules.pullback f`: for `𝒪_S`-modules `A, B` there is a canonical
isomorphism `f^*A ⊗_X f^*B ≅ f^*(A ⊗_S B)`. This is the general fact that the
inverse-image functor is strong monoidal — `f^*` factors as
`forget ∘ (presheaf base change) ∘ sheafify`, presheaf base change is monoidal
pointwise (it is the pointwise extension of scalars along the ring map, which
commutes with the tensor product), and module sheafification is monoidal
(`External.sheafifyTensorComparison`). Mathlib v4.30.0 carries **no** monoidal
structure on `Scheme.Modules.pullback` / `PresheafOfModules.pullback` (neither a
`MonoidalFunctor` instance nor a comparison iso — verified absent via
loogle/leansearch, iter-035), so the comparison is anchored here, exactly parallel
to the sanctioned `External.sheafifyTensorComparison`.

**Natural form (re-typed @036, net axiom count unchanged).** Stated as a
**natural isomorphism of functors `S.Modules ⥤ X.Modules`**, natural in the second
slot `B` with the first slot `A` a parameter:
`(B ↦ f^*A ⊗_X f^*B) ≅ (B ↦ f^*(A ⊗_S B))`, i.e.
`pullback f ⋙ tensorLeft (f^*A) ≅ tensorLeft A ⋙ pullback f`. The object-level
comparison `f^*A ⊗_X f^*B ≅ f^*(A ⊗_S B)` is recovered as `(… A).app B`; the new
content over the iter-035 object-level axiom is the second-slot naturality square,
which is exactly what the (1.1.3) comparison-map `θ` needs to be natural in `N`
(the first slot is always the *fixed* `H(I,F)` there). This **replaces** the
object-level axiom — net axiom count unchanged. See `lem:pullbackTensorComparison`. -/
axiom External.pullbackTensorComparison {X S : Scheme.{u}} (f : X ⟶ S) (A : S.Modules) :
    Scheme.Modules.pullback f ⋙ tensorLeft ((Scheme.Modules.pullback f).obj A) ≅
      tensorLeft A ⋙ Scheme.Modules.pullback f

/-- **[standard: pullback of the structure sheaf]** Base-change unit `f^*𝒪_S ≅ 𝒪_X`.
For a morphism of schemes `f : X ⟶ S`, the pullback of the structure sheaf `𝒪_S`
(the tensor unit of `𝒪_S`-modules) is canonically isomorphic to the structure sheaf
`𝒪_X` (the tensor unit of `𝒪_X`-modules): `f^*𝒪_S ≅ 𝒪_X`.

Standard fact: `f^*` is a (strong) monoidal functor and so carries the tensor unit to
the tensor unit. Mathlib v4.30.0 registers **no** monoidal structure on
`Scheme.Modules.pullback`, so the unit isomorphism is recorded here as an external input,
exactly parallel to the `f^*`-monoidality comparison `External.pullbackTensorComparison`.
See `thm:ega_pullbackUnit`. -/
axiom External.pullbackUnit {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit S.ringCatSheaf)
      ≅ SheafOfModules.unit X.ringCatSheaf

/-- **[standard: `f^*` right-unitality coherence]** The right-unitality square of the
(strong) monoidal functor `f^* = Scheme.Modules.pullback f` commutes. Writing
`μ_{A,𝒪} : f^*A ⊗_X f^*𝒪_S → f^*(A ⊗_S 𝒪_S)` for the `f^*`-laxity comparison
(`External.pullbackTensorComparison`), `ε : f^*𝒪_S ≅ 𝒪_X` for the unit comparison
(`External.pullbackUnit`), and `ρ` for the right unitor (`tensorRightUnitor`), one has,
in diagrammatic (left-to-right) order,
`μ_{A,𝒪} ; f^*(ρ_A) = (id_{f^*A} ⊗ ε) ; ρ_{f^*A}`, i.e.
`f^*A ⊗ f^*𝒪 --μ--> f^*(A⊗𝒪) --f^*ρ--> f^*A` equals
`f^*A ⊗ f^*𝒪 --id⊗ε--> f^*A ⊗ 𝒪_X --ρ--> f^*A`.

Standard: this is one of the two unit coherence axioms of a (strong/lax) monoidal
functor. Mathlib v4.30.0 registers **no** monoidal structure on
`Scheme.Modules.pullback`, so — exactly as for the laxity `μ`
(`External.pullbackTensorComparison`) and the unit `ε` (`External.pullbackUnit`) — the
coherence relating these two otherwise-independent comparison data is recorded as an
external input, in-family with the existing `f^*`-monoidality anchors. It mentions
neither `H` nor admissibility nor Eilenberg–Watts, so it is strictly weaker than
`H_tensor`. See `thm:ega_pullback_rightUnitality`. -/
axiom External.pullback_rightUnitality {X S : Scheme.{u}} (f : X ⟶ S) (A : S.Modules) :
    ((External.pullbackTensorComparison f A).app (SheafOfModules.unit S.ringCatSheaf)).hom
        ≫ (Scheme.Modules.pullback f).map (tensorRightUnitor A).hom
      = (tensorLeft ((Scheme.Modules.pullback f).obj A)).map (External.pullbackUnit f).hom
        ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj A)).hom

/-- **[EGA O_I, 4.4.3.1]** Adjunction isomorphism for `Hom` under base change,
in the **degree-0 / module-level form actually consumed by (1.3)**.

Altman–Kleiman state this (in the (1.7) proof) as the sheaf iso
`Hom_X(I, (1×g)_* N) ≅ (1×g)_* Hom_{X_T}(I_T, N)` for a base change `g : T → S`.
The only instance (1.3) consumes is the closed-fibre, *Hom-set* incarnation: for
the fibre inclusion `j = f.fiberι s : X(s) ⟶ X` (a general scheme morphism `j`)
and a quasi-coherent module `G` on the source, the natural bijection
`Hom_X(I, j_* G) ≅ Hom_{X(s)}(j^* I, G)` — these are the vertical maps in AK's
commutative diagram, with `j^* I = I(s)`.

Unlike the other `External.*` anchors this is **not** an axiom: the fibre-product
form is a genuine Mathlib gap, but the degree-0 Hom-set form it reduces to is
*exactly* the hom-equivalence of Mathlib's pullback–pushforward adjunction
`Scheme.Modules.pullbackPushforwardAdjunction j` (`pullback j ⊣ pushforward j`).
So we realize it as a proved theorem rather than an assumed axiom. The `\lean`
hint `thm:ega_adjunction` points here; review may mark it `\mathlibok`. -/
noncomputable def External.adjunction {X Y : Scheme.{u}} (j : Y ⟶ X) (I : X.Modules)
    (G : Y.Modules) :
    (I ⟶ (Scheme.Modules.pushforward j).obj G) ≃ ((Scheme.Modules.pullback j).obj I ⟶ G) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv I G).symm

/-
TODO (deferred external anchors — need infrastructure absent from Mathlib):

* `External.basechange_q0`  (thm:ega_basechange_q0)  — the `q = 0` case of the
  `sExt`-limit isomorphism; requires projective limits of schemes/modules and
  the comparison map `lim Hom_{X_λ}(I_λ,F_λ) → Hom_X(I,F)`.
* `External.nakayama_iso`   (thm:ob_nakayama_iso)    — the Nakayama-type iso
  `R(𝒪_s) ⊗ N ≅ R(N)`; phrasable in pure module theory but needs the explicit
  base-change comparison natural transformation to be stated faithfully.
-/

/-! ## Project-local Mathlib supplement — half-exactness of the Ext-tensor functor

The homological core of (1.3): the functor `N ↦ Ext^q_X(I, F ⊗_S N)` is
half-exact. The genuine homological content (Mathlib's covariant `Ext` long exact
sequence) is built here; the one missing input is that, for `F` `S`-flat, the
base-change tensor `F ⊗_S (-)` carries a short exact sequence of `𝒪_S`-modules to
a short exact sequence of `𝒪_X`-modules (stalkwise flatness through sheafification,
a from-scratch gap parallel to `tilde_exact` / the `j_!`-pullback). That input is
isolated as the hypothesis `hSE` below — the conclusion of a future anchor
`External.flat_tensor_exact f F hF sc hsc : (sc.map (tensorBaseChangeFunctor f F)).ShortExact`. -/

/-- `tensorLeft F` preserves zero morphisms: the presheaf monoidal tensor is
bilinear (`MonoidalPreadditive.tensor_zero`) and sheafification is additive.
Project-local because `X.Modules` has no `MonoidalCategory` instance, so
`tensorLeft` is hand-built and its additivity is not inferred. -/
instance tensorLeft_preservesZeroMorphisms {X : Scheme.{u}} (F : X.Modules) :
    (tensorLeft F).PreservesZeroMorphisms where
  map_zero N N' := by
    change (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (0 : N ⟶ N').val) = 0
    have hv : (SheafOfModules.Hom.val (0 : N ⟶ N')) = 0 := rfl
    have ht : (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val)
        (0 : N.val ⟶ N'.val)) = 0 := by
      ext1 Y
      rw [PresheafOfModules.Monoidal.tensorHom_app]
      exact CategoryTheory.MonoidalPreadditive.tensor_zero _
    rw [hv, ht]
    exact Functor.map_zero _ _ _

/-- The base-change tensor functor `F ⊗_S (-) = pullback f ⋙ tensorLeft F`
preserves zero morphisms (composite of two zero-preserving functors). Needed so
that `ShortComplex.map (tensorBaseChangeFunctor f F)` is well-formed. -/
instance tensorBaseChangeFunctor_preservesZeroMorphisms {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) : (tensorBaseChangeFunctor f F).PreservesZeroMorphisms := by
  unfold tensorBaseChangeFunctor
  infer_instance

/-- **[AK §1, (1.3) proof]** Half-exactness of `N ↦ Ext^q_X(I, F ⊗_S N)`, in the
exactness-at-the-middle (membership) form matching Mathlib's covariant `Ext` long
exact sequence `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂`.

Conditional form: the hypothesis `hSE` is that the base-changed sequence
`sc.map (tensorBaseChangeFunctor f F)` is short exact — exactly what `F` being
`S`-flat supplies (the to-be-anchored `External.flat_tensor_exact`). Given that,
every degree-`q` Ext class on the middle term `Ext^q_X(I, F ⊗_S sc.X₂)` that maps
to `0` under the third map lifts to the first term, i.e. the sequence
`Ext^q_X(I, F⊗N') → Ext^q_X(I, F⊗N) → Ext^q_X(I, F⊗N'')` is exact at the middle.

Project-local: assembles Mathlib's `Ext` LES against the hand-built base-change
tensor `tensorBaseChangeFunctor`. See `lem:ext_tensor_halfexact`. -/
theorem ext_tensor_halfexact {X S : Scheme.{u}} (f : X ⟶ S) (I F : X.Modules) (q : ℕ)
    (sc : ShortComplex S.Modules)
    (hSE : (sc.map (tensorBaseChangeFunctor f F)).ShortExact) :
    letI : HasDerivedCategory X.Modules := HasDerivedCategory.standard X.Modules
    haveI := CategoryTheory.hasExt_of_hasDerivedCategory X.Modules
    ∀ (x₂ : CategoryTheory.Abelian.Ext I (tensorBC f F sc.X₂) q),
      x₂.comp (CategoryTheory.Abelian.Ext.mk₀ (sc.map (tensorBaseChangeFunctor f F)).g)
        (add_zero q) = 0 →
      ∃ x₁ : CategoryTheory.Abelian.Ext I (tensorBC f F sc.X₁) q,
        x₁.comp (CategoryTheory.Abelian.Ext.mk₀ (sc.map (tensorBaseChangeFunctor f F)).f)
          (add_zero q) = x₂ := by
  letI : HasDerivedCategory X.Modules := HasDerivedCategory.standard X.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory X.Modules
  intro x₂ hx₂
  exact CategoryTheory.Abelian.Ext.covariant_sequence_exact₂ I hSE x₂ hx₂

/-- **[AK §1, (1.3) proof; standard flatness]** `F` `S`-flat ⟹ the base-change
tensor `F ⊗_S (−) = tensorBaseChangeFunctor f F` carries a short exact sequence of
`S.Modules` to a short exact sequence of `X.Modules`.

`F` being `S`-flat means each stalk `F_x` is flat over `𝒪_{S,f(x)}`, so the
module-level fact `Module.Flat.lTensor_shortComplex_exact` gives exactness
stalkwise; reflecting that through the `IsLocalizedModule`/stalk layer and
sheafification (the route of `tilde_exact`) is a genuine from-scratch
stalkwise-flatness Mathlib gap, parallel to `External.flat_pullback_exact`. Anchored
as the standard flatness input that discharges the hypothesis `hSE` of
`ext_tensor_halfexact`, making the half-exactness of `N ↦ Ext^q_X(I, F ⊗_S N)`
unconditional. See `thm:flat_tensor_exact`. -/
axiom External.flat_tensor_exact {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (hF : IsSFlat f F) (sc : ShortComplex S.Modules) (hsc : sc.ShortExact) :
    (sc.map (tensorBaseChangeFunctor f F)).ShortExact

/-- **[standard / EGA; AK §1, (1.3) proof p. 56]** Flat restriction to the closed
fibre preserves short exactness — the **correct** flatness mechanism for the (1.3)
fibre diagram (replacing the iter-028 named gap `hpullflat`).

Altman–Kleiman restrict the acyclic short exact sequence `0 → K → J → I → 0` to the
closed fibre `X(s)`; *because the right-hand term `I = sc.X₃` is flat over the **base**
`S`* (NOT over the fibre map `j`), base change along `S → k(s)`
(equivalently `Tor₁^{𝒪_S}(I, k(s)) = 0`) keeps the restricted sequence
`0 → j^*K → j^*J → j^*I → 0` short exact, where `j = f.fiberι s`. This is a *different,
correct* anchor from `External.flat_pullback_exact` (whose flatness slot is on the
pulled-back term): the @028 prover showed that deriving `IsSFlat (j ≫ f) (j^*I)` from
`IsSFlat f I` is FALSE in general (a fibre preimmersion `j` is not flat), so this anchor
states exactly the input AK use. Standard commutative algebra / EGA; absent from Mathlib
at the sheaf level (parallel to `External.flat_pullback_exact`/`flat_tensor_exact`).
AK quote: *"Since `I` is `S`-flat, the sequence remains exact when restricted to `X(s)`."*
See `thm:ega_flat_fibre_restriction`. -/
axiom External.flat_fibre_restriction_exact {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (sc : ShortComplex X.Modules) (hsc : sc.ShortExact) (hflat : IsSFlat f sc.X₃) :
    (sc.map (Scheme.Modules.pullback (f.fiberι s))).ShortExact

/-- **[standard / EGA; AK §1, (1.3) proof p. 56]** Fibre pushforward of a base-change is
the residue tensor (brick 5, the fibre identification). For `A` Noetherian local with
closed point `s` and residue field `k = k(s)`, `f : X ⟶ Spec A`, and `F : X.Modules`,
the projection / base-change formula identifies
`j_*j^*F ≅ F ⊗_S k(s)~ = (tensorBaseChangeFunctor f F).obj (k~)`, where
`j = f.fiberι s` is the inclusion of the closed fibre. This turns the homological
assembly `ext1_X_pushforward_fibre_vanishes` (`Ext¹_X(I, j_*j^*F) = 0`) into the residue
value `T(k(s)) = 0` of the functor `T`. General EGA base change along the closed
immersion of the closed fibre; NOT §1 content (AK use it implicitly: *"the latter Ext is
just `T(k(s))`"*). Absent from Mathlib at this generality. See `thm:ega_fibre_tensor_residue`. -/
axiom External.fibre_tensor_residue_iso {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsLocalRing ↑A] (f : X ⟶ Spec A) (F : X.Modules) :
    (Scheme.Modules.pushforward (f.fiberι (IsLocalRing.closedPoint ↑A))).obj
        ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint ↑A))).obj F)
      ≅ (tensorBaseChangeFunctor f F).obj
          (AlgebraicGeometry.tilde (ModuleCat.of ↑A (IsLocalRing.ResidueField ↑A)))

/-- **[standard / EGA]** Quasicoherence of the fibre pushforward `j_*j^*F`. For a
quasi-coherent `F` and the fibre inclusion `j = f.fiberι s` (a quasi-compact,
quasi-separated morphism, being a base change of `Spec k(s) → S`), the pullback `j^*F`
is quasi-coherent and its pushforward `j_*j^*F` along the qcqs `j` is again
quasi-coherent. Mathlib v4.30.0 has no instance/lemma supplying
`SheafOfModules.IsQuasicoherent` through `Scheme.Modules.pullback` / `pushforward`, so the
standard preservation fact is anchored here; it discharges the `hWqc` named gap of the
iter-028 `ext1_X_pushforward_fibre_vanishes`. See `thm:ega_fibre_pushforward_qcoh`. -/
axiom External.fibre_pushforward_qcoh {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pushforward (f.fiberι s)).obj
      ((Scheme.Modules.pullback (f.fiberι s)).obj F)).IsQuasicoherent

/-- **[AK §1, (1.3) proof]** Unconditional half-exactness of `N ↦ Ext^q_X(I, F ⊗_S N)`
for `F` `S`-flat. Discharges the hypothesis `hSE` of `ext_tensor_halfexact` with the
flatness anchor `External.flat_tensor_exact f F hF sc hsc`: every degree-`q` Ext class
on the middle term that maps to `0` under the third map lifts to the first term.

Project-local helper specializing `ext_tensor_halfexact` to the genuine flatness
input. See `lem:ext_tensor_halfexact` / `thm:flat_tensor_exact`. -/
theorem ext_tensor_halfexact_of_flat {X S : Scheme.{u}} (f : X ⟶ S) (I F : X.Modules)
    (hF : IsSFlat f F) (q : ℕ) (sc : ShortComplex S.Modules) (hsc : sc.ShortExact) :
    letI : HasDerivedCategory X.Modules := HasDerivedCategory.standard X.Modules
    haveI := CategoryTheory.hasExt_of_hasDerivedCategory X.Modules
    ∀ (x₂ : CategoryTheory.Abelian.Ext I (tensorBC f F sc.X₂) q),
      x₂.comp (CategoryTheory.Abelian.Ext.mk₀ (sc.map (tensorBaseChangeFunctor f F)).g)
        (add_zero q) = 0 →
      ∃ x₁ : CategoryTheory.Abelian.Ext I (tensorBC f F sc.X₁) q,
        x₁.comp (CategoryTheory.Abelian.Ext.mk₀ (sc.map (tensorBaseChangeFunctor f F)).f)
          (add_zero q) = x₂ :=
  ext_tensor_halfexact f I F q sc (External.flat_tensor_exact f F hF sc hsc)

/-! ## Project-local Mathlib supplement — additivity of `tensorLeft`

Mathlib registers `PreservesZeroMorphisms` for `PresheafOfModules.sheafification`
(used in `tensorLeft_preservesZeroMorphisms`) but no `Additive` instance. We supply
it from the sheafification adjunction: sheafification is the left adjoint, its right
adjoint `forget ⋙ restrictScalars` is additive, and a left adjoint of an additive
functor is additive (`Adjunction.left_adjoint_additive`). This unblocks the
additivity of the hand-built `tensorLeft F` (no `MonoidalCategory X.Modules`
instance, so additivity is not inferred). -/

/-- Project-local (Mathlib gap): the module-sheafification functor
`PresheafOfModules.sheafification α` is **additive**. It is the left adjoint of
`PresheafOfModules.sheafificationAdjunction α`, whose right adjoint
`(SheafOfModules.forget R) ⋙ (PresheafOfModules.restrictScalars α)` is additive
(`SheafOfModules.forget` and `PresheafOfModules.restrictScalars` are each additive,
and additivity is closed under composition), so the left adjoint is additive by
`CategoryTheory.Adjunction.left_adjoint_additive`. See `lem:sheafification_additive`. -/
instance presheafOfModules_sheafification_additive
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat} {R : Sheaf J RingCat} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] :
    (PresheafOfModules.sheafification α).Additive :=
  (PresheafOfModules.sheafificationAdjunction α).left_adjoint_additive

/-- Project-local (Mathlib gap): the hand-built endofunctor `tensorLeft F`
(`N ↦ F ⊗_{𝒪_X} N`) is **additive**. On the presheaf level `𝟙_F ⊗ (-)` is additive
because `ModuleCat` is monoidal-preadditive (`MonoidalPreadditive.tensor_add`
pointwise), and sheafification is additive
(`presheafOfModules_sheafification_additive`); the composite is additive.
Project-local because `X.Modules` carries no `MonoidalCategory` instance, so
`tensorLeft` is hand-built and its additivity is not inferred. See
`lem:tensorLeft_additive`. -/
instance tensorLeft_additive {X : Scheme.{u}} (F : X.Modules) :
    (tensorLeft F).Additive where
  map_add {N N' φ ψ} := by
    change (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) (φ + ψ).val) = _
    have hv : ((φ + ψ : N ⟶ N').val) = φ.val + ψ.val := rfl
    have ht : (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val)
          (φ.val + ψ.val))
        = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) φ.val
          + PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 F.val) ψ.val := by
      ext1 Y
      simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.add_app]
      exact CategoryTheory.MonoidalPreadditive.tensor_add _ _ _
    rw [hv, ht]
    exact Functor.map_add _

/-! ## Project-local Mathlib supplement — the functor `T` of (1.3)

Altman–Kleiman (1.3) opens with the functor `T(M) = Ext¹_X(I, F ⊗_S M~)` from
finitely generated `A`-modules to `A`-modules. We package it as a typed functor
`functorT`. Because Mathlib has **no** `Functor.Linear A` route into
`AddCommGrpCat` (that target is only `ℤ`-linear), the `A`-module structure on the
Ext groups is supplied by a general *End-action lift* `liftAdditiveToModuleCat`:
any additive `G : ModuleCat A ⥤ AddCommGrpCat` lifts to a functor
`ModuleCat A ⥤ ModuleCat A` whose value on `M` has the same underlying group as
`G.obj M` and `A`-action `a • x = (G.map (a • 𝟙 M)) x`. The ring hom
`A →+* AddMonoid.End (G.obj M)`, `a ↦ G.map (a • 𝟙 M)`, is `endRingHom`
(multiplicativity uses commutativity of `A`); `Module.compHom` then transports the
canonical `AddMonoid.End`-action to an `A`-module structure (`moduleOfLift`).

**Universe note (genuine obstruction, flagged for the later 1.3 bricks).** The
covariant `Ext` of `Y.Modules` (`Y : Scheme.{u}`) lands in `AddCommGrpCat.{u+1}`
(it is a hom in the standard derived category, whose universe is the *object*
universe `u+1` of `Y.Modules`; cf. `extGroup`, which lands in `Ab.{u+1}` for the
same reason). Consequently `functorT` is genuinely
`ModuleCat.{u} ↑A ⥤ ModuleCat.{u+1} ↑A`, **not** an endofunctor of
`ModuleCat.{u} ↑A`. Feeding it to `External.halfexact_free` (which is stated for an
endofunctor `ModuleCat.{u} A ⥤ ModuleCat.{u} A`) therefore needs a universe
reconciliation downstream — either re-typing `External.halfexact_free` /
`IsHalfExact` to the `{u}/{u+1}` shape, or collapsing the Ext universe via a
small-hom derived category. This is the precise next-brick gap. -/

/-- `tensorBaseChangeFunctor f F` is additive: it is the composite of the additive
`Scheme.Modules.pullback f` (a left adjoint) and the additive `tensorLeft F`
(`tensorLeft_additive`). Project-local because `tensorBaseChangeFunctor` is a `def`,
so the composite-additivity is not synthesized through it without unfolding. -/
instance tensorBaseChangeFunctor_additive {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) : (tensorBaseChangeFunctor f F).Additive := by
  unfold tensorBaseChangeFunctor; infer_instance

section FunctorT
open CategoryTheory.Abelian

universe w

variable {A : Type u} [CommRing A]

/-- **(`lem:additive_functor_module_lift`, ring-hom core)** For an additive functor
`G : ModuleCat A ⥤ AddCommGrpCat` and an object `M`, the map `a ↦ G.map (a • 𝟙 M)`
is a ring homomorphism `A →+* AddMonoid.End (G.obj M)`. Additivity/`one` come from
`G.map_add` / `G.map_id`; multiplicativity uses `G.map_comp` together with the
commutativity of `A` (`(a*b) • 𝟙 = (b • 𝟙) ≫ (a • 𝟙)`). Project-local: Mathlib has
no "additive functor induces a ring hom on `End`" lemma. -/
noncomputable def endRingHom (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{w}) [G.Additive]
    (M : ModuleCat.{u} A) : A →+* AddMonoid.End (G.obj M) where
  toFun a := (G.map (a • 𝟙 M)).hom
  map_one' := by rw [one_smul, G.map_id]; rfl
  map_zero' := by rw [zero_smul, G.map_zero]; rfl
  map_add' a b := by rw [add_smul, G.map_add]; rfl
  map_mul' a b := by
    have : (a * b) • 𝟙 M = (b • 𝟙 M) ≫ (a • 𝟙 M) := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul, mul_comm]
    rw [this, G.map_comp]; rfl

/-- **(`lem:additive_functor_module_lift`, module structure)** The `A`-module
structure on `G.obj M` induced by `endRingHom` via `Module.compHom`: the canonical
`AddMonoid.End (G.obj M)`-action precomposed with the ring hom `endRingHom G M`. -/
noncomputable instance moduleOfLift (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{w}) [G.Additive]
    (M : ModuleCat.{u} A) : Module A (G.obj M) :=
  Module.compHom (G.obj M) (endRingHom G M)

/-- **(`lem:additive_functor_module_lift`)** The End-action lift of an additive
functor `G : ModuleCat A ⥤ AddCommGrpCat` to a functor `ModuleCat A ⥤ ModuleCat A`.
On objects it equips `G.obj M` with the `A`-module structure `moduleOfLift`; on a
morphism `φ` it is `(G.map φ).hom`, which is `A`-linear by naturality of `G`
against `a • 𝟙` (`(a • 𝟙_M) ≫ φ = a • φ = φ ≫ (a • 𝟙_N)`). The general
project-bespoke category-theory infrastructure underlying `functorT`. -/
noncomputable def liftAdditiveToModuleCat (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{w})
    [G.Additive] : ModuleCat.{u} A ⥤ ModuleCat.{w} A where
  obj M := ModuleCat.of A (G.obj M)
  map {M N} φ := ModuleCat.ofHom
    { toFun := (G.map φ).hom
      map_add' := map_add _
      map_smul' := fun a x => by
        change (G.map φ).hom ((G.map (a • 𝟙 M)).hom x)
          = (G.map (a • 𝟙 N)).hom ((G.map φ).hom x)
        rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
            ← AddCommGrpCat.hom_comp, ← AddCommGrpCat.hom_comp,
            ← G.map_comp, ← G.map_comp, Linear.smul_comp, Linear.comp_smul,
            Category.id_comp, Category.comp_id] }
  map_id M := by ext x; change (G.map (𝟙 M)).hom x = x; rw [G.map_id]; rfl
  map_comp φ ψ := by
    ext x
    change (G.map (φ ≫ ψ)).hom x = (G.map ψ).hom ((G.map φ).hom x)
    rw [G.map_comp]; rfl

/-- **(`lem:functorT_additive`, lift half)** The End-action lift
`liftAdditiveToModuleCat G` of an additive `G` is itself additive: its action on
morphisms is `(G.map ·).hom`, which is additive because `G` is. -/
instance liftAdditiveToModuleCat_additive (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{w})
    [G.Additive] : (liftAdditiveToModuleCat G).Additive where
  map_add {M N φ ψ} := by
    ext x
    change (G.map (φ + ψ)).hom x = (G.map φ).hom x + (G.map ψ).hom x
    rw [G.map_add]; rfl

/-- **(`lem:functorT_obj_isZero_iff`, lift half)** `IsZero`-reflection through the
End-action lift: `(liftAdditiveToModuleCat G).obj M` is a zero object of `ModuleCat A`
iff `G.obj M` is a zero object of `AddCommGrpCat`. The lift only re-structures the
underlying abelian group with an `A`-action, so both reduce to subsingleton of the
*same* carrier `↑(G.obj M)` (`ModuleCat.isZero_of_iff_subsingleton` /
`AddCommGrpCat.isZero_iff_subsingleton`). Project-local. -/
lemma liftAdditiveToModuleCat_isZero_obj_iff (G : ModuleCat.{u} A ⥤ AddCommGrpCat.{w})
    [G.Additive] (M : ModuleCat.{u} A) :
    IsZero ((liftAdditiveToModuleCat G).obj M) ↔ IsZero (G.obj M) := by
  have hobj : (liftAdditiveToModuleCat G).obj M = ModuleCat.of A (G.obj M) := rfl
  rw [hobj, ModuleCat.isZero_of_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]

end FunctorT

/-- **(`lem:covariant_ext_functor`)** The covariant Ext functor
`N ↦ Ext^q_Y(I, N)` packaged as `Y.Modules ⥤ AddCommGrpCat.{u+1}`, the missing
functorial form of `extGroup` in its second variable. On a morphism `f : N ⟶ N'`
it is `x ↦ x.comp (Ext.mk₀ f)`; functoriality is `Ext.comp_mk₀_id` (identity),
`Ext.mk₀_comp_mk₀` + `Ext.comp_assoc` (composition), additivity in `x` is
`Ext.add_comp`. Uses the same `HasDerivedCategory.standard` + `hasExt` setup as
`extGroup` / `ext_tensor_halfexact`, so it lands one universe up. Project-local:
Mathlib v4.30.0 packages no covariant Ext functor. -/
noncomputable def covariantExtFunctor {Y : Scheme.{u}} (I : Y.Modules) (q : ℕ) :
    Y.Modules ⥤ AddCommGrpCat.{u+1} :=
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  { obj := fun N => AddCommGrpCat.of (CategoryTheory.Abelian.Ext I N q)
    map := fun {N N'} f => AddCommGrpCat.ofHom
      { toFun := fun x => x.comp (CategoryTheory.Abelian.Ext.mk₀ f) (add_zero q)
        map_zero' := CategoryTheory.Abelian.Ext.zero_comp I q
          (CategoryTheory.Abelian.Ext.mk₀ f) q (add_zero q)
        map_add' := fun x y => CategoryTheory.Abelian.Ext.add_comp x y
          (CategoryTheory.Abelian.Ext.mk₀ f) (add_zero q) }
    map_id := fun N => by
      ext x; exact congrArg CategoryTheory.Abelian.Ext.hom
        (CategoryTheory.Abelian.Ext.comp_mk₀_id x)
    map_comp := fun {N₁ N₂ N₃} f g => by
      ext x; refine congrArg CategoryTheory.Abelian.Ext.hom ?_
      change x.comp (CategoryTheory.Abelian.Ext.mk₀ (f ≫ g)) (add_zero q)
        = (x.comp (CategoryTheory.Abelian.Ext.mk₀ f) (add_zero q)).comp
            (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q)
      rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀ f g]
      exact (CategoryTheory.Abelian.Ext.comp_assoc x
        (CategoryTheory.Abelian.Ext.mk₀ f) (CategoryTheory.Abelian.Ext.mk₀ g)
        (add_zero q) (zero_add 0) (by omega)).symm }

/-- **(`lem:covariant_ext_functor`, additive)** The covariant Ext functor is
additive: `Ext.mk₀ (f + g) = Ext.mk₀ f + Ext.mk₀ g` (`Ext.mk₀_add`) and
`Ext.comp_add`. -/
instance covariantExtFunctor_additive {Y : Scheme.{u}} (I : Y.Modules) (q : ℕ) :
    (covariantExtFunctor I q).Additive where
  map_add {N N' f g} := by
    letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
    haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
    ext x
    change x.comp (CategoryTheory.Abelian.Ext.mk₀ (f + g)) (add_zero q)
      = x.comp (CategoryTheory.Abelian.Ext.mk₀ f) (add_zero q)
        + x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q)
    rw [CategoryTheory.Abelian.Ext.mk₀_add, CategoryTheory.Abelian.Ext.comp_add]

/-- **(`def:functorT`)** The functor `T(M) = Ext¹_X(I, F ⊗_S M~)` of
Altman–Kleiman (1.3), for `A` a commutative ring, `f : X ⟶ Spec A`, and
`I F : X.Modules`. It is the End-action lift (`liftAdditiveToModuleCat`) of the
additive composite `tilde.functor A ⋙ tensorBaseChangeFunctor f F ⋙
covariantExtFunctor I 1` (`M ↦ I, F ⊗_S M~ ↦ Ext¹_X(I, F ⊗_S M~)`).

See the universe note above: the covariant Ext lands in `AddCommGrpCat.{u+1}`, so
`functorT` is `ModuleCat.{u} ↑A ⥤ ModuleCat.{u+1} ↑A`, not yet an endofunctor.
Parametrized over the post-reduction data `(A, f, I, F)`; the reduction to this
affine-Noetherian-local shape is a later 1.3 brick (anchored, not proved here). -/
noncomputable def functorT {X : Scheme.{u}} (A : CommRingCat.{u}) (f : X ⟶ Spec A)
    (I F : X.Modules) : ModuleCat.{u} ↑A ⥤ ModuleCat.{u+1} ↑A :=
  liftAdditiveToModuleCat
    (AlgebraicGeometry.tilde.functor A ⋙ tensorBaseChangeFunctor f F ⋙ covariantExtFunctor I 1)

/-- **(`lem:functorT_additive`)** `functorT A f I F` is additive: it is the
End-action lift (`liftAdditiveToModuleCat_additive`) of a composite of additive
functors (`tilde.functor` is additive as a left adjoint;
`tensorBaseChangeFunctor_additive`; `covariantExtFunctor_additive`). -/
instance functorT_additive {X : Scheme.{u}} (A : CommRingCat.{u}) (f : X ⟶ Spec A)
    (I F : X.Modules) : (functorT A f I F).Additive := by
  unfold functorT; infer_instance

/-- **(`lem:functorT_obj_isZero_iff`)** `IsZero`-reflection through `functorT`: the
lifted `ModuleCat A` object `(functorT A f I F).obj M` is a zero object iff the
underlying `Ext` group `extGroup 1 I (F ⊗_S M~)` is a zero object of `Ab`. `functorT` is
the End-action lift (`liftAdditiveToModuleCat`) of the additive composite
`tilde.functor A ⋙ tensorBaseChangeFunctor f F ⋙ covariantExtFunctor I 1`, whose value on
`M` is — by `rfl` — exactly `extGroup 1 I ((tensorBaseChangeFunctor f F).obj (tilde M))`;
the lift adds only an `A`-action, so `liftAdditiveToModuleCat_isZero_obj_iff` reflects
`IsZero`. Project-local. -/
lemma functorT_obj_isZero_iff {X : Scheme.{u}} (A : CommRingCat.{u}) (f : X ⟶ Spec A)
    (I F : X.Modules) (M : ModuleCat.{u} ↑A) :
    IsZero ((functorT A f I F).obj M) ↔
      IsZero (extGroup 1 I ((tensorBaseChangeFunctor f F).obj (AlgebraicGeometry.tilde M))) := by
  unfold functorT
  rw [liftAdditiveToModuleCat_isZero_obj_iff]
  exact Iff.rfl

/-! ## Strand (a): the representing module `H(I,F)` and local freeness -/

/-- **(1.1)** The `𝒪_S`-module `H(I,F)` representing `M ↦ Hom_X(I, F ⊗_S M)`,
defined as the corepresenting object supplied by `External.H_existence`.
See `def:H`. -/
noncomputable def H (f : X ⟶ S) (I F : X.Modules) (ha : Admissible f I F) : S.Modules :=
  haveI := External.H_existence f I F ha
  (homTensorFunctor f I F).coreprX

/-- **(1.1)** The universal element `h(I,F) ∈ Hom_X(I, F ⊗_S H(I,F))`.
See `def:h`. -/
noncomputable def h (f : X ⟶ S) (I F : X.Modules) (ha : Admissible f I F) :
    I ⟶ tensorBC f F (H f I F ha) :=
  haveI := External.H_existence f I F ha
  (homTensorFunctor f I F).coreprx

/-- **(1.1.1)** Representability: the Yoneda map defined by `h(I,F)` is an
isomorphism, i.e. `coyoneda(H(I,F))` is naturally isomorphic to the functor
`M ↦ Hom_X(I, F ⊗_S M)`. This is the content of base-change compatibility of the
pair `(H, h)`. See `thm:H_represents`. -/
theorem H_represents (f : X ⟶ S) (I F : X.Modules) (ha : Admissible f I F) :
    Nonempty (coyoneda.obj (op (H f I F ha)) ≅ homTensorFunctor f I F) :=
  haveI := External.H_existence f I F ha
  ⟨(homTensorFunctor f I F).coreprW⟩

/-- **(1.1.3 STEP 2.5-b, object-level)** The functorial action of `H(-,F)` in its
**first slot**: a morphism `φ : J ⟶ J'` of `𝒪_X`-modules induces a morphism
`H(J,F) ⟶ H(J',F)` of the corepresenting `𝒪_S`-modules.

Construction (corepresentability/coyoneda reflection): `φ` gives, by precomposition,
a natural transformation `homTensorFunctor f J' F ⟶ homTensorFunctor f J F` of the
corepresented functors (`coyoneda.map φ.op` whiskered into the base-change tensor).
Conjugating by the two corepresentation isos `H_represents` turns it into a map
`coyoneda(H J') ⟶ coyoneda(H J)`, which the full-faithfulness of `coyoneda`
(`Coyoneda.coyoneda_full`/`_faithful`) reflects to a unique `H J ⟶ H J'` (the
direction flips twice: contravariance of precomposition, then of `coyoneda` /
`op`). This is the object-level substrate the `θ`-naturality of (1.1.3) needs;
a *total* functor `X.Modules ⥤ S.Modules` cannot exist because `H f J F` is only
defined where `Admissible f J F` holds (not for every object), so the functorial
action is delivered per-morphism with its two admissibility witnesses threaded.
Project-local. -/
noncomputable def HMapFst (f : X ⟶ S) (F : X.Modules) {J J' : X.Modules}
    (haJ : Admissible f J F) (haJ' : Admissible f J' F) (φ : J ⟶ J') :
    H f J F haJ ⟶ H f J' F haJ' :=
  (coyoneda.preimage
    ((H_represents f J' F haJ').some.hom ≫
      Functor.whiskerLeft (tensorBaseChangeFunctor f F) (coyoneda.map φ.op) ≫
      (H_represents f J F haJ).some.inv)).unop

/-- **(1.1.3 STEP 2.5-b, functoriality)** `HMapFst` carries an identity to an
identity: `H(-,F)` preserves identities in its first slot. -/
@[simp] lemma HMapFst_id (f : X ⟶ S) (F : X.Modules) {J : X.Modules}
    (haJ : Admissible f J F) :
    HMapFst f F haJ haJ (𝟙 J) = 𝟙 (H f J F haJ) := by
  rw [HMapFst]
  have hw : Functor.whiskerLeft (tensorBaseChangeFunctor f F)
      (coyoneda.map (𝟙 J : J ⟶ J).op) = 𝟙 _ := by
    rw [op_id, CategoryTheory.Functor.map_id, Functor.whiskerLeft_id']
  rw [hw]
  erw [Category.id_comp]
  rw [Iso.hom_inv_id, Functor.preimage_id]
  rfl

/-- **(1.1.3 STEP 2.5-b, functoriality)** `HMapFst` carries a composite to a
composite: `H(-,F)` preserves composition in its first slot. The two corepresentation
isos at the middle object `J'` cancel; the precomposition natural transformations
compose via `coyoneda`/`whiskerLeft` functoriality and `(φ ≫ ψ).op = ψ.op ≫ φ.op`. -/
lemma HMapFst_comp (f : X ⟶ S) (F : X.Modules) {J J' J'' : X.Modules}
    (haJ : Admissible f J F) (haJ' : Admissible f J' F) (haJ'' : Admissible f J'' F)
    (φ : J ⟶ J') (ψ : J' ⟶ J'') :
    HMapFst f F haJ haJ'' (φ ≫ ψ)
      = HMapFst f F haJ haJ' φ ≫ HMapFst f F haJ' haJ'' ψ := by
  rw [HMapFst, HMapFst, HMapFst, ← unop_comp]
  congr 1
  rw [← Functor.preimage_comp]
  congr 1
  rw [op_comp, CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rfl

/-- **(1.1.3 STEP 2.5-b)** `H(-,F)` as a covariant functor `X.Modules ⥤ S.Modules`
in its first slot, assembled from the per-morphism action `HMapFst` and its
functoriality (`HMapFst_id`, `HMapFst_comp`).

**Carrier.** `H f J F` is defined only where `Admissible f J F` holds, so a *total*
functor on `X.Modules` requires the admissibility witness for *every* object — the
planner-sanctioned carrier `hAdm : ∀ J, Admissible f J F`. This hypothesis is rarely
satisfiable in full (it forces every `𝒪_X`-module to be locally finitely presented),
so downstream uses must either restrict to a subcategory of objects where
admissibility holds or supply the comparison map per-object via `htensorComparison`;
the functor is recorded here as the structural substrate the (1.1.3) `θ`-naturality
is phrased against. See `def:HFunctorFst`. -/
noncomputable def HFunctorFst (f : X ⟶ S) (F : X.Modules)
    (hAdm : ∀ J : X.Modules, Admissible f J F) : X.Modules ⥤ S.Modules where
  obj J := H f J F (hAdm J)
  map {J J'} φ := HMapFst f F (hAdm J) (hAdm J') φ
  map_id J := HMapFst_id f F (hAdm J)
  map_comp {J J' J''} φ ψ := HMapFst_comp f F (hAdm J) (hAdm J') (hAdm J'') φ ψ

/-- **(1.1.3 STEP 2.5-c)** The domain endofunctor of the (1.1.3) comparison:
`N ↦ H(I ⊗_S N, F)`, realized as the composite
`tensorBaseChangeFunctor f I ⋙ HFunctorFst f F` (`N ↦ I ⊗_S N = tensorBC f I N ↦
H(tensorBC f I N, F)`). Carries the same `∀ J, Admissible` carrier as
`HFunctorFst`. See `def:htensorDomainFunctor`. -/
noncomputable def htensorDomainFunctor (f : X ⟶ S) (I F : X.Modules)
    (hAdm : ∀ J : X.Modules, Admissible f J F) : S.Modules ⥤ S.Modules :=
  tensorBaseChangeFunctor f I ⋙ HFunctorFst f F hAdm

/-! ### (1.1.2 STEP D) first-factor naturality → tensor equivalence → twist iso

The pieces that turn the per-variable naturality layer (STEPs A–C) into the
categorical equivalence `- ⊗ L` for an invertible `L`, then into the `(1.1.2)` twist
isomorphism of `homTensorFunctor`s, and finally close `H_tensor_invertible` by Yoneda. -/

/-- Project-local: an isomorphism `e : L₁ ≅ L₂` of `𝒪_X`-modules induces a natural
isomorphism of the right-tensor endofunctors `tensorRight L₁ ≅ tensorRight L₂`. The
component at `A` is `(tensorLeft A).mapIso e : A ⊗ L₁ ≅ A ⊗ L₂`; naturality in `A` is the
tensor interchange law. This is the "whisker an object iso into `tensorRight`" operation
used to transport the invertibility iso `L ⊗ L' ≅ 𝒪_X` into the equivalence unit/counit. -/
noncomputable def tensorRightMapIso {X : Scheme.{u}} {L₁ L₂ : X.Modules} (e : L₁ ≅ L₂) :
    tensorRight L₁ ≅ tensorRight L₂ :=
  NatIso.ofComponents (fun A => (tensorLeft A).mapIso e) (by
    intro A A' φ
    have key : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val (𝟙 L₁.val)
          ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 A'.val) e.hom.val
        = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 A.val) e.hom.val
          ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val (𝟙 L₂.val) := by
      ext1 Z
      simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
        PresheafOfModules.id_app]
      exact (MonoidalCategory.whisker_exchange _ _).symm
    simp only [tensorRight_map_eq, Functor.mapIso_hom, tensorLeft_map_eq]
    exact ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
      (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).congr_map key).trans
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map_comp _ _)))

/-- Project-local: the left unitor `𝒪_X ⊗ A ≅ A` packaged as a natural isomorphism of
endofunctors `tensorLeft 𝒪_X ≅ 𝟭`. -/
noncomputable def tensorLeftUnitorNatIso {X : Scheme.{u}} :
    tensorLeft (SheafOfModules.unit X.ringCatSheaf) ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun A => tensorLeftUnitor A) (by
    intro A A' φ
    rw [tensorLeft_map_eq]
    simp only [tensorLeftUnitor, Iso.trans_hom, Functor.mapIso_hom, Functor.id_map,
      sheafifyValIso, asIso_hom]
    have hlu : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) φ.val
          ≫ (presheafLeftUnitor (R := X.presheaf) A'.val).hom
        = (presheafLeftUnitor (R := X.presheaf) A.val).hom ≫ φ.val :=
      MonoidalCategory.leftUnitor_naturality
        (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) φ.val
    have step : (PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
            (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) φ.val)
          ≫ (PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map (presheafLeftUnitor (R := X.presheaf) A'.val).hom
        = (PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map (presheafLeftUnitor (R := X.presheaf) A.val).hom
          ≫ (PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map φ.val :=
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
        (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).congr_map hlu).trans
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map_comp _ _))
    have cnat : (PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map φ.val
          ≫ (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).counit.app A'
        = (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).counit.app A ≫ φ :=
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).counit_naturality φ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).counit.app A') step).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
              (𝟙 X.ringCatSheaf.obj)).map (presheafLeftUnitor (R := X.presheaf) A.val).hom) ≫ ·)
              cnat).trans
            (Category.assoc _ _ _).symm))))

/-- Project-local (`lem:tensorRightUnitor_natIso`): the right unitor `A ⊗ 𝒪_X ≅ A`
packaged as a natural isomorphism of endofunctors `𝟭 ≅ tensorRight 𝒪_X`. Derived from the
braiding natural iso `tensorBraidingNatIso 𝒪_X : tensorRight 𝒪_X ≅ tensorLeft 𝒪_X` and the
left-unitor natural iso `tensorLeftUnitorNatIso`, both already natural. -/
noncomputable def tensorRightUnitorNatIso {X : Scheme.{u}} :
    𝟭 X.Modules ≅ tensorRight (SheafOfModules.unit X.ringCatSheaf) :=
  (tensorBraidingNatIso (SheafOfModules.unit X.ringCatSheaf) ≪≫ tensorLeftUnitorNatIso).symm

/-- Index functor `A ↦ (A.val ⊗ L.val, L'.val)`, the first-factor analogue of
`assocIdxL` (here the *first* tensor slot `A` varies, inner factors `L, L'` fixed). -/
private noncomputable def assocIdxL₁ {X : Scheme.{u}} (L L' : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj A := (PresheafOfModules.Monoidal.tensorObj A.val L.val, L'.val)
  map {A A'} φ := (PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val), 𝟙 L'.val)
  map_id A := by
    refine Prod.ext (presheaf_id_tensorHom_id A.val L.val) rfl
  map_comp {A A' A''} φ ψ := by
    refine Prod.ext ?_ (Category.id_comp _).symm
    change PresheafOfModules.Monoidal.tensorHom (φ.val ≫ ψ.val) (𝟙 L.val)
        = PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val)
          ≫ PresheafOfModules.Monoidal.tensorHom ψ.val (𝟙 L.val)
    ext1 Z
    simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
      PresheafOfModules.id_app]
    exact MonoidalCategory.comp_tensor_id _ _

/-- Index functor `A ↦ (A.val, L.val ⊗ L'.val)`, the right-form companion of
`assocIdxL₁`. The fixed inner factor's identity is expressed as `𝟙_L ⊗ 𝟙_{L'}` (as in
`assocIdxL₃`) so the associator-naturality leg matches definitionally. -/
private noncomputable def assocIdxR₁ {X : Scheme.{u}} (L L' : X.Modules) :
    X.Modules ⥤ (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) ×
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) where
  obj A := (A.val, PresheafOfModules.Monoidal.tensorObj L.val L'.val)
  map {A A'} φ := (φ.val, PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val))
  map_id A := by
    refine Prod.ext (SheafOfModules.id_val A) ?_
    exact presheaf_id_tensorHom_id L.val L'.val
  map_comp {A A' A''} φ ψ := by
    refine Prod.ext (SheafOfModules.comp_val φ ψ) ?_
    change PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val)
        = PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val)
          ≫ PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val)
    exact (Category.id_comp _).symm.trans
      (congrArg (· ≫ PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val))
        (presheaf_id_tensorHom_id L.val L'.val).symm)

/-- **(1.1.2 naturality, first factor)** Naturality of the unconditional associator
`tensorAssoc · L L'` in its FIRST factor, packaged as a natural isomorphism of
endofunctors `tensorRight (L ⊗ L') ≅ tensorRight L ⋙ tensorRight L'`
(`A ↦ (A ⊗ (L ⊗ L') ≅ (A ⊗ L) ⊗ L')`). The first-factor mirror of
`tensorAssocNatIso₂`/`tensorAssocNatIso₃`, built as the `.symm` of the three-`NatIso`
composite `tensorRight L ⋙ tensorRight L' ≅ … ≅ tensorRight (L ⊗ L')` (comparison anchors
whiskered by `assocIdxL₁`/`assocIdxR₁` + sheafified associator). The varying factor is now
the first product slot; both comparison legs sheafify fixed inner factors, discharged by the
sheafify-of-identity bridges. See `lem:tensorAssocNatIso1`. -/
noncomputable def tensorAssocNatIso₁ {X : Scheme.{u}} (L L' : X.Modules) :
    tensorRight (tensorMod L L') ≅ tensorRight L ⋙ tensorRight L' :=
  ((NatIso.ofComponents
    (fun A => (External.sheafifyTensorComparison (X := X)).app
      (PresheafOfModules.Monoidal.tensorObj A.val L.val, L'.val)) (by
      intro A A' φ
      have h := (External.sheafifyTensorComparison (X := X)).hom.naturality
        ((PresheafOfModules.Monoidal.tensorHom φ.val (𝟙 L.val), 𝟙 L'.val) :
          (PresheafOfModules.Monoidal.tensorObj A.val L.val, L'.val) ⟶
            (PresheafOfModules.Monoidal.tensorObj A'.val L.val, L'.val))
      simp only [assocIdxL₁, sheafifyFst_map_eq, tensorRight_map_eq, tensorThenSheafify_map_eq,
        Iso.app_hom, Functor.comp_map] at h ⊢
      exact h) :
    tensorRight L ⋙ tensorRight L' ≅ assocIdxL₁ L L' ⋙ tensorThenSheafify X) ≪≫
  (NatIso.ofComponents
    (fun A => (PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).mapIso
        (MonoidalCategory.associator
          (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
          A.val L.val L'.val)) (by
      intro A A' φ
      simp only [assocIdxL₁, assocIdxR₁, Functor.comp_map, tensorThenSheafify_map_eq,
        Functor.mapIso_hom]
      exact ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
        (((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).congr_map
          (MonoidalCategory.associator_naturality
            (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            φ.val (𝟙 L.val) (𝟙 L'.val))).trans
        ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map_comp _ _))) :
    assocIdxL₁ L L' ⋙ tensorThenSheafify X ≅ assocIdxR₁ L L' ⋙ tensorThenSheafify X) ≪≫
  (NatIso.ofComponents
    (fun A => ((External.sheafifyTensorComparisonLeft (X := X)).app
      (A.val, PresheafOfModules.Monoidal.tensorObj L.val L'.val)).symm) (by
      intro A A' φ
      have h := (External.sheafifyTensorComparisonLeft (X := X)).inv.naturality
        ((φ.val, PresheafOfModules.Monoidal.tensorHom (𝟙 L.val) (𝟙 L'.val)) :
          (A.val, PresheafOfModules.Monoidal.tensorObj L.val L'.val) ⟶
            (A'.val, PresheafOfModules.Monoidal.tensorObj L.val L'.val))
      simp only [assocIdxR₁, sheafifySnd_map_eq, tensorRight_map_eq, tensorThenSheafify_map_eq,
        Iso.app_inv, Iso.symm_hom, Functor.comp_map] at h ⊢
      convert h using 4
      exact congrArg
        (fun a => (PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map
            (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val a))
        (((congrArg (fun m => ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).map m).val) (presheaf_id_tensorHom_id L.val L'.val)).trans
            (sheafify_map_id_val _)).symm)) :
    assocIdxR₁ L L' ⋙ tensorThenSheafify X ≅ tensorRight (tensorMod L L'))).symm

/-- **(1.1.2 STEP D)** (`lem:tensorRight_invertible_equiv`): if `L` is invertible, the
endofunctor `tensorRight L` (`- ⊗ L`) is an equivalence of `𝒪_X`-modules, with quasi-inverse
`tensorRight L'` for `L'` the chosen inverse (`L ⊗ L' ≅ 𝒪_X`). Unit and counit are NatIso
composites of the right-unitor naturality `tensorRightUnitorNatIso`, the invertibility iso
whiskered into `tensorRight` (`tensorRightMapIso`), and the first-factor associator naturality
`tensorAssocNatIso₁` (counit via the braided companion `L' ⊗ L ≅ 𝒪_X`); being NatIsos they are
automatically natural, so `Equivalence.mk` needs no triangle/coherence. -/
noncomputable def tensorRightEquivOfInvertible {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertibleMod L) : X.Modules ≌ X.Modules :=
  let L' := hL.choose
  let e : tensorMod L L' ≅ SheafOfModules.unit X.ringCatSheaf := hL.choose_spec.some
  let e' : tensorMod L' L ≅ SheafOfModules.unit X.ringCatSheaf := tensorBraiding L' L ≪≫ e
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight L')
    (tensorRightUnitorNatIso ≪≫ tensorRightMapIso e.symm ≪≫ tensorAssocNatIso₁ L L')
    ((tensorAssocNatIso₁ L' L).symm ≪≫ tensorRightMapIso e' ≪≫ tensorRightUnitorNatIso.symm)

/-- **(1.1.2 STEP E)** (`lem:homTensorFunctor_twist_natIso`): for `L` invertible, the natural
isomorphism of functors `S.Modules ⥤ Type u`
`homTensorFunctor f (I ⊗ L) (F ⊗ L) ≅ homTensorFunctor f I F`.
Built on the `𝒪_X`-side by rearranging the target via `tensorRearrangeNatIso F L`
(`(F ⊗ L) ⊗ Y ≅ (F ⊗ Y) ⊗ L`) and reflecting through the tensor equivalence's
full-faithfulness `coyonedaCompFF` (`Hom(I ⊗ L, - ⊗ L) ≅ Hom(I, -)`), then whiskered by the
pullback `f^*`. -/
noncomputable def homTensorFunctorTwistIso {X S : Scheme.{u}} (f : X ⟶ S) (I F L : X.Modules)
    (hL : IsInvertibleMod L) :
    homTensorFunctor f (tensorMod I L) (tensorMod F L) ≅ homTensorFunctor f I F :=
  let hFF : (tensorRight L).FullyFaithful := (tensorRightEquivOfInvertible hL).fullyFaithfulFunctor
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Functor.isoWhiskerRight (tensorRearrangeNatIso F L).symm
        (coyoneda.obj (op (tensorMod I L))) ≪≫
      Functor.isoWhiskerLeft (tensorLeft F) (coyonedaCompFF hFF I))

/-- **(1.1.2)** Invariance of `H` under twist by an invertible sheaf:
`H(I ⊗ L, F ⊗ L) ≅ H(I, F)`. See `lem:H_tensor_invertible`. -/
theorem H_tensor_invertible (f : X ⟶ S) (I F L : X.Modules)
    (hL : IsInvertibleMod L) (ha : Admissible f I F)
    (ha' : Admissible f (tensorMod I L) (tensorMod F L)) :
    Nonempty (H f (tensorMod I L) (tensorMod F L) ha' ≅ H f I F ha) :=
  ⟨(coyoneda.preimageIso
    ((H_represents f (tensorMod I L) (tensorMod F L) ha').some ≪≫
      homTensorFunctorTwistIso f I F L hL ≪≫
      (H_represents f I F ha).some.symm)).unop.symm⟩

/-- **(1.1.3 STEP 2)** The canonical comparison map `θ` of (1.1.3), directed OUT of
the corepresenting object `H(I ⊗_S N, F)`:
`θ : H(I ⊗_S N, F) ⟶ H(I,F) ⊗_S N`. (The (1.1.3) isomorphism is `θ.symm` once `θ`
is shown to be an iso by right-exactness/Eilenberg–Watts — the deep crux, handed off.)

Construction (verbatim AK (1.1.3), p. 55): by corepresentability of
`M ↦ Hom_X(I ⊗_S N, F ⊗_S M)` by `H(I ⊗_S N, F)`, a map
`H(I ⊗_S N, F) ⟶ W` (here `W = H(I,F) ⊗_S N`) is the same as a universal element
`e ∈ Hom_X(I ⊗_S N, F ⊗_S W)`. We build `e` from the universal element
`h(I,F) : I ⟶ F ⊗_S H(I,F)` by tensoring on the right with `f^*N`, reassociating
(`tensorAssoc`), and folding the two pullbacks back together via the
f^*-monoidality anchor `External.pullbackTensorComparison`:
`I ⊗_X f^*N → (F ⊗_X f^*H) ⊗_X f^*N ≅ F ⊗_X (f^*H ⊗_X f^*N) ≅ F ⊗_X f^*(H ⊗_S N) = F ⊗_S W`.
See `def:htensorComparison`. -/
noncomputable def htensorComparison (f : X ⟶ S) (I F : X.Modules) (N : S.Modules)
    (ha : Admissible f I F) (ha' : Admissible f (tensorBC f I N) F) :
    H f (tensorBC f I N) F ha' ⟶ tensorMod (H f I F ha) N :=
  (H_represents f (tensorBC f I N) F ha').some.inv.app (tensorMod (H f I F ha) N)
    ((tensorRight ((Scheme.Modules.pullback f).obj N)).map (h f I F ha) ≫
      (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
        ((Scheme.Modules.pullback f).obj N)).hom ≫
      (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N).hom)

/-- **(general category theory)** Compose three commuting squares in a row into a
single equation between the two outer fourfold composites. Project-local plumbing
for the `θ`-naturality of (1.1.3): there the three squares are `whisker_exchange`,
the associator naturality, and the `f^*`-monoidality (`pullbackTensorComparison`)
naturality. Chained in **term mode** (`congrArg`/`Category.assoc`): the morphisms
carry non-syntactic sheafification instance paths, so `rw`/`reassoc`/`slice` matching
fails (it works only up to reducible transparency, and `tensorBC`/`tensorMod` unfold
only at default transparency); `congrArg` typechecks via full defeq and so threads
the squares cleanly. -/
private lemma compose_three_squares {Cat : Type*} [Category Cat] {o0 o1 o2 o3 o4 : Cat}
    (A : o0 ⟶ o1) (B : o1 ⟶ o2) (C : o2 ⟶ o3) (D : o3 ⟶ o4)
    {p1 p2 p3 : Cat} (L1 : o0 ⟶ p1) (M1 : p1 ⟶ o2)
    (L2 : p1 ⟶ p2) (M2 : p2 ⟶ o3) (L3 : p2 ⟶ p3) (Q : p3 ⟶ o4)
    (S1 : A ≫ B = L1 ≫ M1) (S2 : M1 ≫ C = L2 ≫ M2) (S3 : M2 ≫ D = L3 ≫ Q) :
    A ≫ B ≫ C ≫ D = (L1 ≫ L2 ≫ L3) ≫ Q :=
  (Category.assoc A B (C ≫ D)).symm.trans
  ((congrArg (· ≫ (C ≫ D)) S1).trans
  ((Category.assoc L1 M1 (C ≫ D)).trans
  ((congrArg (L1 ≫ ·) (Category.assoc M1 C D).symm).trans
  ((congrArg (fun t => L1 ≫ t ≫ D) S2).trans
  ((congrArg (L1 ≫ ·) (Category.assoc L2 M2 D)).trans
  ((congrArg (fun t => L1 ≫ L2 ≫ t) S3).trans
  ((congrArg (L1 ≫ ·) (Category.assoc L2 L3 Q).symm).trans
  (Category.assoc L1 (L2 ≫ L3) Q).symm)))))))

/-- **(1.1.3 STEP 2.5-d)** Per-morphism naturality of the comparison map `θ`
(`htensorComparison`) in the second variable `N`. For `ψ : N ⟶ N'` the square
```
HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ) ≫ htensorComparison f I F N' ..
  = htensorComparison f I F N .. ≫ (tensorLeft (H f I F ha)).map ψ
```
commutes. This is the genuinely reusable θ-naturality substrate (delivered
per-morphism via the non-total `HMapFst`, because the total functorial carrier
`∀ J, Admissible f J F` of `HFunctorFst`/`htensorDomainFunctor` is unsatisfiable
— `Admissible ⊃ IsLFP` — and any `NatTrans` between those total functors is
vacuous). Proof by corepresentation reflection: both sides are maps OUT of the
corepresenting object `H(I⊗N,F)`, so via `H_represents` they reduce to an identity
of universal elements (`star`) that chains (i) `whisker_exchange`, (ii) `tensorAssoc`
naturality (`tensorAssocNatIso₃`), and (iii) the second-slot naturality of the
`f^*`-monoidality anchor `External.pullbackTensorComparison`; `HMapFst`'s defining
`coyoneda.preimage` is expanded via `Functor.map_preimage`. See
`lem:htensorComparison_naturality`. -/
theorem htensorComparison_naturality (f : X ⟶ S) (I F : X.Modules)
    {N N' : S.Modules} (ψ : N ⟶ N') (ha : Admissible f I F)
    (ha' : Admissible f (tensorBC f I N) F)
    (ha'' : Admissible f (tensorBC f I N') F) :
    HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ) ≫ htensorComparison f I F N' ha ha''
      = htensorComparison f I F N ha ha' ≫ (tensorLeft (H f I F ha)).map ψ := by
  -- (★): naturality of the universal element `e` in `N`, after corepresentation reflection.
  have star : (tensorBaseChangeFunctor f I).map ψ ≫
        ((tensorRight ((Scheme.Modules.pullback f).obj N')).map (h f I F ha) ≫
          (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
            ((Scheme.Modules.pullback f).obj N')).hom ≫
          (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N').hom)
      = ((tensorRight ((Scheme.Modules.pullback f).obj N)).map (h f I F ha) ≫
          (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
            ((Scheme.Modules.pullback f).obj N)).hom ≫
          (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N).hom)
        ≫ (tensorBaseChangeFunctor f F).map ((tensorLeft (H f I F ha)).map ψ) := by
    simp only [tensorBaseChangeFunctor, Functor.comp_map]
    -- Square 1: whisker exchange of `h(I,F) ⊗ -` and `id_I ⊗ f^*ψ`.
    have S1 : (tensorLeft I).map ((Scheme.Modules.pullback f).map ψ)
          ≫ (tensorRight ((Scheme.Modules.pullback f).obj N')).map (h f I F ha)
        = (tensorRight ((Scheme.Modules.pullback f).obj N)).map (h f I F ha)
          ≫ (tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
              ((Scheme.Modules.pullback f).map ψ) := by
      have key : PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 I.val)
              ((Scheme.Modules.pullback f).map ψ).val
            ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (h f I F ha).val
              (𝟙 ((Scheme.Modules.pullback f).obj N').val)
          = PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (h f I F ha).val
              (𝟙 ((Scheme.Modules.pullback f).obj N).val)
            ≫ PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
              (𝟙 (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha))).val)
              ((Scheme.Modules.pullback f).map ψ).val := by
        ext1 Z
        simp only [PresheafOfModules.Monoidal.tensorHom_app, PresheafOfModules.comp_app,
          PresheafOfModules.id_app]
        exact MonoidalCategory.whisker_exchange _ _
      change (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map _
          ≫ (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map _
        = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map _
          ≫ (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map key
    -- Square 2: naturality of the associator in its third factor (`tensorAssocNatIso₃`).
    have S2 : (tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
            ((Scheme.Modules.pullback f).map ψ)
          ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj N')).hom
        = (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj N)).hom
          ≫ (tensorLeft F).map ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              ((Scheme.Modules.pullback f).map ψ)) := by
      have hnat := (tensorAssocNatIso₃ F
        ((Scheme.Modules.pullback f).obj (H f I F ha))).inv.naturality
          ((Scheme.Modules.pullback f).map ψ)
      have hb : ∀ Y : X.Modules,
          (tensorAssocNatIso₃ F ((Scheme.Modules.pullback f).obj (H f I F ha))).inv.app Y
            = (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha)) Y).hom := fun _ => rfl
      rw [hb, hb] at hnat
      simp only [Functor.comp_map] at hnat
      exact hnat
    -- Square 3: second-slot naturality of the `f^*`-monoidality anchor.
    have S3 : (tensorLeft F).map ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              ((Scheme.Modules.pullback f).map ψ))
          ≫ (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N').hom
        = (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N).hom
          ≫ (tensorLeft F).map
              ((Scheme.Modules.pullback f).map ((tensorLeft (H f I F ha)).map ψ)) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      have hnat := (External.pullbackTensorComparison f (H f I F ha)).hom.naturality ψ
      simp only [Functor.comp_map] at hnat
      exact hnat
    exact compose_three_squares _ _ _ _ _ _ _ _ _ _ S1 S2 S3
  -- LHS reduction: `HMapFst(ψ) ≫ θ_{N'}` reflects to `θ`'s universal element precomposed by `f^*ψ`.
  have step2 : HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ)
        ≫ htensorComparison f I F N' ha ha''
      = (H_represents f (tensorBC f I N) F ha').some.inv.app (tensorMod (H f I F ha) N')
          ((tensorBaseChangeFunctor f I).map ψ ≫
            ((tensorRight ((Scheme.Modules.pullback f).obj N')).map (h f I F ha) ≫
            (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj N')).hom ≫
            (tensorLeft F).map
              ((External.pullbackTensorComparison f (H f I F ha)).app N').hom)) := by
    have hT : coyoneda.map (HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ)).op
        = (H_represents f (tensorBC f I N') F ha'').some.hom
          ≫ Functor.whiskerLeft (tensorBaseChangeFunctor f F)
              (coyoneda.map ((tensorBaseChangeFunctor f I).map ψ).op)
          ≫ (H_represents f (tensorBC f I N) F ha').some.inv := by
      rw [HMapFst]; exact coyoneda.map_preimage _
    have e1 : HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ)
          ≫ htensorComparison f I F N' ha ha''
        = (coyoneda.map (HMapFst f F ha' ha'' ((tensorBaseChangeFunctor f I).map ψ)).op).app
            (tensorMod (H f I F ha) N') (htensorComparison f I F N' ha ha'') := rfl
    rw [e1, hT, htensorComparison]
    simp only [NatTrans.comp_app, types_comp_apply, Functor.whiskerLeft_app,
      Iso.inv_hom_id_app_apply]
    rfl
  -- RHS reduction: `θ_N ≫ (H(I,F) ⊗ ψ)` reflects via naturality of the `α.inv` of `H_represents`.
  have step3 : htensorComparison f I F N ha ha' ≫ (tensorLeft (H f I F ha)).map ψ
      = (H_represents f (tensorBC f I N) F ha').some.inv.app (tensorMod (H f I F ha) N')
          (((tensorRight ((Scheme.Modules.pullback f).obj N)).map (h f I F ha) ≫
            (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj N)).hom ≫
            (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app N).hom)
          ≫ (tensorBaseChangeFunctor f F).map ((tensorLeft (H f I F ha)).map ψ)) := by
    rw [htensorComparison]
    exact (NatTrans.naturality_apply (H_represents f (tensorBC f I N) F ha').some.inv _ _).symm
  exact step2.trans
    ((congrArg (fun e => (H_represents f (tensorBC f I N) F ha').some.inv.app
        (tensorMod (H f I F ha) N') e) star).trans step3.symm)

/-- **[Eilenberg–Watts; Altman–Kleiman §1 (1.1.3), p. 55, "So we have…"]**
Eilenberg–Watts propagation for the comparison map `θ` of `def:htensorComparison`.

Both functors `N ↦ H(I ⊗_S N, F)` and `N ↦ H(I,F) ⊗_S N` of a quasi-coherent
`𝒪_S`-module `N` are covariant, additive, right exact and sum-preserving, and `θ`
(`htensorComparison`) is the canonical comparison transformation between them (natural by
`htensorComparison_naturality`). If `θ_{𝒪_S}` (the comparison at the unit `N = 𝒪_S`) is an
isomorphism, then `θ_N` is an isomorphism for every quasi-coherent `N`.

This is the general Eilenberg–Watts principle: a natural transformation between two
right-exact, direct-sum-preserving functors on quasi-coherent `𝒪_S`-modules that is an
isomorphism on the unit `𝒪_S` is an isomorphism on every quasi-coherent object (locally
choose a free presentation `𝒪_S^{(J)} → 𝒪_S^{(K)} → N → 0`; `θ` is iso on each free
`𝒪_S^{(•)}` by sum-preservation, hence on the cokernel `N` by right exactness and the five
lemma). Mathlib has neither Eilenberg–Watts nor the free-presentation machinery for
`𝒪_S`-modules, and the source functor is not total (admissibility constrains the objects),
so the principle is recorded here **conditional on `θ_{𝒪_S}` invertible** (`hunit`); the
project supplies that hypothesis directly via `htensorComparison_unit_isIso`. This is
strictly weaker than `H_tensor` (which is unconditional) — it is the general theorem
Altman–Kleiman cite, not a restatement of it. See `thm:ew_htensorComparison`. -/
axiom External.eilenbergWatts_htensorComparison {X S : Scheme.{u}} (f : X ⟶ S)
    (I F : X.Modules) (ha : Admissible f I F)
    (hau : Admissible f (tensorBC f I (SheafOfModules.unit S.ringCatSheaf)) F)
    (hunit : IsIso (htensorComparison f I F (SheafOfModules.unit S.ringCatSheaf) ha hau))
    {N : S.Modules} (hN : N.IsQuasicoherent)
    (ha' : Admissible f (tensorBC f I N) F) :
    IsIso (htensorComparison f I F N ha ha')

/-- **(1.1.3 STEP 3 helper)** The base-change unit collapses `I ⊗_S 𝒪_S` to `I`:
`tensorBC f I 𝒪_S ≅ I`. Built from `External.pullbackUnit` (`f^*𝒪_S ≅ 𝒪_X`) and the
right unitor `tensorRightUnitor` (`I ⊗_X 𝒪_X ≅ I`). -/
noncomputable def tensorUnitBC (f : X ⟶ S) (I : X.Modules) :
    tensorBC f I (SheafOfModules.unit S.ringCatSheaf) ≅ I :=
  (tensorLeft I).mapIso (External.pullbackUnit f) ≪≫ tensorRightUnitor I

/-- **(1.1.3 STEP 3 helper)** Admissibility of `I ⊗_S 𝒪_S` follows from admissibility of
`I`: the only nontrivial field, `IsLFP (I ⊗_S 𝒪_S)`, transports from `IsLFP I` along the
unit iso `tensorUnitBC` (finite presentation is closed under isomorphism). -/
lemma admissible_tensorUnit (f : X ⟶ S) (I F : X.Modules) (ha : Admissible f I F) :
    Admissible f (tensorBC f I (SheafOfModules.unit S.ringCatSheaf)) F where
  proper := ha.proper
  finitePresentation := ha.finitePresentation
  lfp_I := ObjectProperty.prop_of_iso (SheafOfModules.isFinitePresentation X.ringCatSheaf)
            (tensorUnitBC f I).symm ha.lfp_I
  lfp_F := ha.lfp_F
  flat_F := ha.flat_F

/-- **(1.1.3 STEP 3, the θ_𝒪 sanity check formalized)** The comparison map `θ` of
`htensorComparison` is an isomorphism at the unit `N = 𝒪_S`. This is the load-bearing
hypothesis discharging `External.eilenbergWatts_htensorComparison`: under the
identifications `I ⊗_S 𝒪_S ≅ I` (`tensorUnitBC`) and `H(I,F) ⊗_S 𝒪_S ≅ H(I,F)`
(`tensorRightUnitor`), the defining universal element of `θ_𝒪` reduces to `h(I,F)`, so
`θ_𝒪` is the canonical iso `H(I ⊗_S 𝒪_S, F) ≅ H(I,F) ≅ H(I,F) ⊗_S 𝒪_S`.
See `lem:htensorComparison_unit_isIso`. -/
theorem htensorComparison_unit_isIso (f : X ⟶ S) (I F : X.Modules)
    (ha : Admissible f I F)
    (hau : Admissible f (tensorBC f I (SheafOfModules.unit S.ringCatSheaf)) F) :
    IsIso (htensorComparison f I F (SheafOfModules.unit S.ringCatSheaf) ha hau) := by
  haveI hcI := External.H_existence f I F ha
  -- The corepresenting iso `α` for `I ⊗_S 𝒪` used in `htensorComparison`.
  set 𝒪 := SheafOfModules.unit S.ringCatSheaf with h𝒪
  set α := (H_represents f (tensorBC f I 𝒪) F hau).some with hα
  -- The explicit comparison iso `Ψ : coyoneda(H(I,F) ⊗ 𝒪) ≅ homTensorFunctor(I ⊗ 𝒪)`,
  -- assembled from the right unitor `i`, the genuine corepresentation `coreprW` of
  -- `homTensorFunctor(I,F)`, and the unit collapse `u : I ⊗ 𝒪 ≅ I`.
  set i := tensorRightUnitor (H f I F ha) with hi
  set u := tensorUnitBC f I with hu
  set Ψ : coyoneda.obj (op (tensorMod (H f I F ha) 𝒪)) ≅ homTensorFunctor f (tensorBC f I 𝒪) F :=
    coyoneda.mapIso i.symm.op ≪≫ (homTensorFunctor f I F).coreprW ≪≫
      Functor.isoWhiskerLeft (tensorBaseChangeFunctor f F) (coyoneda.mapIso u.op) with hΨ
  -- Main identity: `coyoneda(θ_𝒪) ≫ α.hom = Ψ.hom`, proved by Yoneda (value at `𝟙`).
  have hmain : coyoneda.map (htensorComparison f I F 𝒪 ha hau).op ≫ α.hom = Ψ.hom := by
    have hθ : htensorComparison f I F 𝒪 ha hau
        = α.inv.app (tensorMod (H f I F ha) 𝒪)
            ((tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha) ≫
              (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                ((Scheme.Modules.pullback f).obj 𝒪)).hom ≫
              (tensorLeft F).map
                ((External.pullbackTensorComparison f (H f I F ha)).app 𝒪).hom) := rfl
    apply coyonedaEquiv.injective
    rw [coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map, hθ, Iso.inv_hom_id_app_apply, hΨ]
    simp only [Iso.trans_hom, coyonedaEquiv_comp, NatTrans.comp_app, Functor.mapIso_hom,
      Iso.symm_hom, Iso.op_hom, coyonedaEquiv_coyoneda_map, types_comp_apply,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [Functor.coreprW_hom_app (homTensorFunctor f I F) (tensorMod (H f I F ha) 𝒪) i.inv]
    -- Reduced (definitionally) to the unit-coherence equation `star_unit`:
    --   the universal element `e_𝒪` equals `h(I,F)` transported along the unit collapse
    --   `u : I ⊗ 𝒪 ≅ I` and the right unitor `i⁻¹ : H ≅ H ⊗ 𝒪`.
    change (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
          ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj 𝒪)).hom
          ≫ (tensorLeft F).map ((External.pullbackTensorComparison f (H f I F ha)).app 𝒪).hom
        = u.hom ≫ h f I F ha ≫ (tensorBaseChangeFunctor f F).map i.inv
    -- REDUCTION of `star_unit` toward the sanctioned `f^*` right-unitality anchor
    -- `External.pullback_rightUnitality` (anchor (A), landed this iter). The full route
    -- (each piece verified in isolation — see `task_results`):
    --   (i)   ν-naturality of the right-unit collapse `ν_A = (A ◁ ε) ≫ ρ_A` at `h(I,F)`
    --         (a `whisker_exchange` square `tensorRightMapIso (pullbackUnit f)` plus the
    --         `tensorRightUnitorNatIso` naturality square, mirroring the `S1`/`S2` legs of
    --         `htensorComparison_naturality`);
    --   (ii)  associator naturality in the third slot at `ε` (via `tensorAssocNatIso₃`,
    --         exactly the `S2` leg of `htensorComparison_naturality`);
    --   (iii) the `f^*` anchor reformulated as `m = ν_{f^*H} ; f^*(i⁻¹)` (`hm'`, landed); and
    --   (iv)  the INTERNAL right-unitor triangle of the hand-built `tensorMod`/`tensorAssoc`
    --         monoidal structure — the one genuinely irreducible residual (see below).
    -- Step (iii): reformulate the anchor to solve for the laxity `m = (μ.app 𝒪).hom`.
    have hanch : ((External.pullbackTensorComparison f (H f I F ha)).app 𝒪).hom
          ≫ (Scheme.Modules.pullback f).map i.hom
        = (tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              (External.pullbackUnit f).hom
          ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom :=
      External.pullback_rightUnitality f (H f I F ha)
    have hm' : ((External.pullbackTensorComparison f (H f I F ha)).app 𝒪).hom
        = ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              (External.pullbackUnit f).hom
            ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
          ≫ (Scheme.Modules.pullback f).map i.inv :=
      (Iso.eq_comp_inv ((Scheme.Modules.pullback f).mapIso i)).mpr hanch
    -- Substitute the anchor (step iii): the laxity `m` becomes the `ν`-collapse of `f^*H`
    -- followed by `f^*(i⁻¹)`, exposing the universal element as the `ν`-collapse whiskered by `F`.
    rw [hm']
    -- RESIDUAL. The goal now reads
    --   `(tR f^*𝒪).map h ≫ assoc ≫ ((F ◁ ν_{f^*H}) ≫ (BC F).map i⁻¹) = u.hom ≫ h ≫ (BC F).map i⁻¹`,
    -- where `ν_{f^*H} = ((f^*H ◁ ε) ≫ ρ_{f^*H})` (`ε = External.pullbackUnit f`). It closes by
    -- (ii) associator naturality at `ε`, (iv) the INTERNAL right-unitor triangle (the new anchor
    -- `External.tensorMod_rightUnitality`), and (i) ν-naturality of `(- ◁ ε) ≫ ρ` at `h`.
    -- (ii) associator naturality in the third slot at `ε` (the `S2` leg, here with `ε` directly).
    have hS2 : (tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
            (External.pullbackUnit f).hom
          ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              (SheafOfModules.unit X.ringCatSheaf)).hom
        = (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj 𝒪)).hom
          ≫ (tensorLeft F).map ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              (External.pullbackUnit f).hom) := by
      have hnat := (tensorAssocNatIso₃ F
        ((Scheme.Modules.pullback f).obj (H f I F ha))).inv.naturality (External.pullbackUnit f).hom
      have hb : ∀ Y : X.Modules,
          (tensorAssocNatIso₃ F ((Scheme.Modules.pullback f).obj (H f I F ha))).inv.app Y
            = (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha)) Y).hom := fun _ => rfl
      rw [hb, hb] at hnat
      simp only [Functor.comp_map] at hnat
      exact hnat
    -- (iv) the INTERNAL right-unitor triangle, instantiated at `M := F, N := f^*H` (new anchor).
    have htri : (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              (SheafOfModules.unit X.ringCatSheaf)).hom
            ≫ (tensorLeft F).map
                (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom
          = (tensorRightUnitor (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).hom :=
      External.tensorMod_rightUnitality F ((Scheme.Modules.pullback f).obj (H f I F ha))
    -- (P): combine `Functor.map_comp`, `hS2` and the triangle into the collapse of the inner
    -- `ν_{f^*H}` whiskered by `F`: `α_{f^*𝒪} ; (F ◁ ν_{f^*H}) = ((F⊗f^*H) ◁ ε) ; ρ_{F⊗f^*H}`.
    have hP : (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj 𝒪)).hom
            ≫ (tensorLeft F).map
                ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                    (External.pullbackUnit f).hom
                  ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
          = (tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
                (External.pullbackUnit f).hom
            ≫ (tensorRightUnitor (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).hom :=
      -- term-mode (`rw [Category.assoc]`/`simp` stall on the sheafification `≫`): split the
      -- whiskered `ν_{f^*H}` via `map_comp`, reassociate, then apply `hS2` and the triangle.
      (congrArg ((tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
            ((Scheme.Modules.pullback f).obj 𝒪)).hom ≫ ·)
          ((tensorLeft F).map_comp
            ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
              (External.pullbackUnit f).hom)
            (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (· ≫ (tensorLeft F).map
                (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
              hS2.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg ((tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
                  (External.pullbackUnit f).hom ≫ ·) htri))))
    -- ν-naturality legs, typed directly in `tensorMod F (f^*H)` form (the naturality squares
    -- come out in the defeq `tensorBC f F (H ..)` form, reconciled by `exact` up to defeq).
    have happ : ∀ A : X.Modules, (tensorRightMapIso (External.pullbackUnit f)).hom.app A
        = (tensorLeft A).map (External.pullbackUnit f).hom := fun _ => rfl
    have hrapp : ∀ A : X.Modules, (tensorRightUnitorNatIso (X := X)).inv.app A
        = (tensorRightUnitor A).hom := fun _ => rfl
    have hu_hom : u.hom = (tensorLeft I).map (External.pullbackUnit f).hom
        ≫ (tensorRightUnitor I).hom := by rw [hu]; rfl
    -- (i.a) whisker exchange of `h(I,F)` with `- ◁ ε`.
    have hw : (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
          ≫ (tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
              (External.pullbackUnit f).hom
        = (tensorLeft I).map (External.pullbackUnit f).hom
          ≫ (tensorRight (SheafOfModules.unit X.ringCatSheaf)).map (h f I F ha) := by
      have t := (tensorRightMapIso (External.pullbackUnit f)).hom.naturality (h f I F ha)
      rw [happ, happ] at t
      exact t
    -- (i.b) right-unitor naturality at `h(I,F)`.
    have hru : (tensorRight (SheafOfModules.unit X.ringCatSheaf)).map (h f I F ha)
          ≫ (tensorRightUnitor (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).hom
        = (tensorRightUnitor I).hom ≫ h f I F ha := by
      have t := (tensorRightUnitorNatIso (X := X)).inv.naturality (h f I F ha)
      rw [hrapp, hrapp] at t
      simp only [Functor.id_map] at t
      exact t
    -- (i) ν-naturality collapse: `(tR f^*𝒪).map h ; ((F⊗f^*H) ◁ ε ; ρ_{F⊗f^*H}) = u.hom ; h`.
    have hν : (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
            ≫ ((tensorLeft (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).map
                  (External.pullbackUnit f).hom
              ≫ (tensorRightUnitor (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).hom)
          = u.hom ≫ h f I F ha :=
      -- term-mode reassociation chain: whisker exchange (`hw`), right-unitor naturality (`hru`),
      -- and the collapse `(I ◁ ε) ; ρ_I = u.hom` (`hu_hom`).
      ((Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ (tensorRightUnitor
              (tensorMod F ((Scheme.Modules.pullback f).obj (H f I F ha)))).hom) hw).trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((tensorLeft I).map (External.pullbackUnit f).hom ≫ ·) hru).trans
              (((Category.assoc _ _ _).symm).trans
                (congrArg (· ≫ h f I F ha) hu_hom.symm)))))
    -- (P) collapses the `α ; (F ◁ ν_{f^*H})` block; (hν) collapses the whole `ν`-naturality.
    have hmaster : (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
          ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
              ((Scheme.Modules.pullback f).obj 𝒪)).hom
          ≫ (tensorLeft F).map
              ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                  (External.pullbackUnit f).hom
                ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
        = u.hom ≫ h f I F ha :=
      (congrArg ((tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha) ≫ ·) hP).trans hν
    -- Final assembly: split `F ◁ (ν_{f^*H} ; f^*i⁻¹)` and append the common `(BC F).map i.inv`
    -- tail to `hmaster`. The `(BC F).map i.inv = (tensorLeft F).map (f^*i.inv)` boundary is rfl.
    have hsplit : (tensorLeft F).map
            (((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                  (External.pullbackUnit f).hom
                ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
              ≫ (Scheme.Modules.pullback f).map i.inv)
        = (tensorLeft F).map
            ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                (External.pullbackUnit f).hom
              ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
          ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv) :=
      (tensorLeft F).map_comp _ _
    -- Final assembly in term mode: split off the common `f^*i⁻¹` tail (`hsplit`), reassociate it
    -- out of the whiskered block, apply `hmaster`, and reassociate back to the goal RHS.
    calc (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
            ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                ((Scheme.Modules.pullback f).obj 𝒪)).hom
            ≫ (tensorLeft F).map
                (((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                      (External.pullbackUnit f).hom
                    ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
                  ≫ (Scheme.Modules.pullback f).map i.inv)
        = (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
            ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                ((Scheme.Modules.pullback f).obj 𝒪)).hom
            ≫ ((tensorLeft F).map
                  ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                      (External.pullbackUnit f).hom
                    ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom)
                ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv)) :=
          congrArg (fun y => (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
              ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                  ((Scheme.Modules.pullback f).obj 𝒪)).hom ≫ y) hsplit
      _ = (tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
            ≫ ((tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                  ((Scheme.Modules.pullback f).obj 𝒪)).hom
                ≫ (tensorLeft F).map
                    ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                        (External.pullbackUnit f).hom
                      ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom))
              ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv) :=
          congrArg ((tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha) ≫ ·)
            (Category.assoc _ _ _).symm
      _ = ((tensorRight ((Scheme.Modules.pullback f).obj 𝒪)).map (h f I F ha)
            ≫ (tensorAssoc F ((Scheme.Modules.pullback f).obj (H f I F ha))
                ((Scheme.Modules.pullback f).obj 𝒪)).hom
              ≫ (tensorLeft F).map
                  ((tensorLeft ((Scheme.Modules.pullback f).obj (H f I F ha))).map
                      (External.pullbackUnit f).hom
                    ≫ (tensorRightUnitor ((Scheme.Modules.pullback f).obj (H f I F ha))).hom))
            ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv) :=
          (Category.assoc _ _ _).symm
      _ = (u.hom ≫ h f I F ha) ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv) :=
          congrArg (· ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv)) hmaster
      _ = u.hom ≫ h f I F ha ≫ (tensorLeft F).map ((Scheme.Modules.pullback f).map i.inv) :=
          Category.assoc _ _ _
  -- Hence `coyoneda(θ_𝒪) = Ψ.hom ≫ α.inv` is iso, so `θ_𝒪` is iso.
  have hfac : coyoneda.map (htensorComparison f I F 𝒪 ha hau).op = Ψ.hom ≫ α.inv := by
    rw [← hmain, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsIso (coyoneda.map (htensorComparison f I F 𝒪 ha hau).op) := by
    rw [hfac]; infer_instance
  haveI : IsIso (htensorComparison f I F 𝒪 ha hau).op := Coyoneda.isIso _
  exact (isIso_op_iff _).mp inferInstance

/-- **(1.1.3)** Right exactness of `H` in the second-variable tensor:
`H(I,F) ⊗ N ≅ H(I ⊗_S N, F)` for a quasi-coherent `𝒪_S`-module `N`.
See `lem:H_tensor`. -/
theorem H_tensor (f : X ⟶ S) (I F : X.Modules) (N : S.Modules)
    (ha : Admissible f I F) (ha' : Admissible f (tensorBC f I N) F)
    (hN : N.IsQuasicoherent) :
    Nonempty (tensorMod (H f I F ha) N ≅ H f (tensorBC f I N) F ha') := by
  haveI hau := admissible_tensorUnit f I F ha
  haveI : IsIso (htensorComparison f I F N ha ha') :=
    External.eilenbergWatts_htensorComparison f I F ha hau
      (htensorComparison_unit_isIso f I F ha hau) hN ha'
  exact ⟨(asIso (htensorComparison f I F N ha ha')).symm⟩

-- **(1.2)** `exists_acyclic_surjection` (`lem:acyclic_surjection`) is defined LATER
-- in the file (after the `extensionByZero` (`j_!`) infrastructure block, which its
-- two `External.*` anchors reference). Lean requires `extensionByZero` to be in scope
-- first. See the `### Acyclic surjection (1.2) anchor-and-assemble` section at the end
-- of the file. (The signature is unchanged from its blueprint statement.)

-- **(1.3)** `H_locallyFree_of_ext_vanishing` (`thm:H_locallyFree`) is defined LATER
-- in the file (after the brick-6 free-conclusion chain `homTensorFunctor_tilde_exact`
-- and `H_free_of_functorT_zero`, which in turn consume the homological heart
-- `functorT_eq_zero` defined near the end). Lean requires those in scope first. See
-- the `### Brick 6 of (1.3): free conclusion + EGA reduction` section at the end.

/-! ## Strand (b): relative local Ext, base-change map, exchange, finiteness -/

-- **(1.4)** `exists_free_resolution_step` (`lem:free_resolution_step`) is defined
-- LATER in the file (after the affine-bridge lemmas `tilde_free`, `tilde_exact`,
-- `tilde_isFP`, `fp_sheaf_affine_tilde`, `exists_finiteFreePresentation_of_noetherian`
-- that its 3-step assembly consumes — Lean requires those defined first). See the
-- `### Free-resolution step (1.4) assembly` section near the end of the file.

/-- **(1.10)(i)** Finiteness and flatness of local Ext. The vanishing locus
`V = { s : sExt^q_{X(s)}(I(s),F(s)) = 0 }` is open and retrocompact; fixing `c`,
the restriction of `sExt^c_X(I,F)` to the locus where `sExt^{c±1}` vanish is
locally finitely presented and flat. See `thm:ext_finite_flat`. -/
theorem ext_finite_flat (f : X ⟶ S) (I F : X.Modules) (q c : ℕ)
    (hfp : LocallyOfFinitePresentation f) (hproper : IsProper f)
    (hF : IsSFlat f F) :
    IsOpen {s : S | FiberExtVanishes q f I F s} ∧
      ∀ V : S.Opens, (∀ s ∈ V, FiberExtVanishes (c + 1) f I F s ∧
          FiberExtVanishes (c - 1) f I F s) →
        IsLFPAndFlatOn c f I F V :=
  ⟨External.ext_vanishing_open q f I F, by
    -- blocked: IsLFPAndFlatOn is opaque (no constructor); needs P1b infra
    sorry⟩

/-
TODO (deferred §1 results — need infrastructure absent from Mathlib):

* `ext_limit`             (lem:ext_limit)            — `lim sExt^q_{X_λ} = sExt^q_X`;
  requires projective limits of schemes and modules.
* `ext_basechange_algebra`(lem:ext_algebra_basechange)— `Ext^q_A(M,N)~ = sExt^q_B`;
  the affine/algebraic incarnation, needs the comparison over `Spec B`.
* `ext_adjunction`        (lem:ext_adjunction)       — adjunction iso (1.7.1) for
  `sExt^q`; requires fibre products `X_T` and pushforward along `1×g`.
* `extBaseChangeMap`      (def:extBaseChangeMap)     — the base-change map
  `b^q(M) : sExt^q_X(I,F) ⊗_S M → sExt^q_{X_T}(I_T, F ⊗_S M)`; requires `X_T`,
  the canonical unit/counit maps and the adjoint of (1.7.1).
* `exchange`              (thm:exchange)             — the property of exchange;
  built on `extBaseChangeMap` and the Nakayama iso, stated at points of fibres.
-/

/-! ## Project-local Mathlib supplement — Affine bridge (P1b-ii′)

The affine equivalence between quasi-coherent `𝒪_{Spec A}`-modules and `A`-modules,
realized through Mathlib's `AlgebraicGeometry.tilde` (`def:tildeMod`). These lemmas
turn module-level facts into sheaf-level ones for the free-resolution step (1.4).

Mathlib (file `Mathlib.AlgebraicGeometry.Modules.Tilde`) already provides a rich API:
`tilde.functor` is fully faithful, additive, a left adjoint to `moduleSpecΓFunctor`
(`tilde.adjunction`, with the unit an iso), preserves finite colimits, and
`tildeFinsupp`/`isIso_fromTildeΓ_of_presentation` give the two facts below directly.
Two further targets (`tilde_exact`, `fp_sheaf_affine_tilde`) remain genuine
Mathlib gaps — see the handoff in `task_results/`. -/

/-- **(`lem:tilde_free`)** Project-local (affine bridge): for a finite index type
`Λ`, the tilde of the free `A`-module `Λ →₀ A` is a free `𝒪_{Spec A}`-module
(`IsFreeMod`). Packages Mathlib's `AlgebraicGeometry.tildeFinsupp`
(`tilde (Λ →₀ A) ≅ SheafOfModules.free Λ`) into the project predicate `IsFreeMod`.
Feeds the free-resolution step (1.4). -/
theorem tilde_free {R : CommRingCat.{u}} (Λ : Type u) [Finite Λ] :
    IsFreeMod (AlgebraicGeometry.tilde (ModuleCat.of ↑R (Λ →₀ ↑R))) :=
  ⟨Λ, ⟨AlgebraicGeometry.tildeFinsupp Λ⟩⟩

/-- **(affine bridge, essential surjectivity given a presentation)** Project-local:
if a `(Spec R).Modules` `M` admits a *global* presentation `P : M.Presentation`
(generators and relations by free sheaves on the trivial cover), then the counit
`M.fromTildeΓ` of the tilde–`Γ` adjunction is an isomorphism, so `M` is the tilde of
its global sections `Γ(M, ⊤)`. Packages Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_of_presentation` as an iso.

This is the half of the affine equivalence that Mathlib *does* supply. Obtaining a
*global* presentation from `SheafOfModules.IsFinitePresentation` (which only carries
*local* quasi-coherent data over a cover) on the affine `Spec R` is the remaining
gap blocking the full `fp_sheaf_affine_tilde` — see `task_results/`. -/
noncomputable def tilde_of_presentation {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (P : M.Presentation) :
    AlgebraicGeometry.tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) ≅ M :=
  haveI := isIso_fromTildeΓ_of_presentation M P
  asIso M.fromTildeΓ

/-! ### Exactness of the tilde functor (affine bridge, step 2)

`AlgebraicGeometry.tilde.functor R : ModuleCat R ⥤ (Spec R).Modules` is an **exact**
functor: it sends a short exact sequence of `R`-modules to a short exact sequence of
quasi-coherent `𝒪_{Spec R}`-modules. This is the reusable exactness half of the affine
equivalence `QCoh(Spec R) ≅ ModuleCat R`, feeding every downstream exactness argument
(e.g. the free-resolution step 1.4).

Mathlib supplies that `tilde.functor R` is additive, a left adjoint (hence preserves
finite colimits), and preserves epimorphisms — i.e. it is *right* exact. The single
genuinely missing ingredient is **left** exactness, which we reduce to
`PreservesMonomorphisms` and prove by hand at the stalk/section level: over each basic
open `D(g)` the section map of `tilde.map f` is the localization-away-of-`g` of `f`
(`tilde.toOpen` is `IsLocalizedModule.Away g`), and localization preserves injectivity
(`IsLocalizedModule.map_injective`). Injectivity on the basic-open basis upgrades to
injectivity on all stalks (`stalkFunctor_map_injective_of_isBasis`), hence the mono is
detected stalkwise (`mono_of_stalk_mono`) and reflected through the fully faithful
`modulesSpecToSheaf`. Right-exactness then upgrades `PreservesMonomorphisms` to
`PreservesFiniteLimits` (`preservesFiniteLimits_iff_forall_exact_map_and_mono`), and the
two finite-(co)limit preservations give exactness of short exact sequences
(`ShortExact.map_of_exact`). None of these instances exist in Mathlib for `tilde`. -/
section TildeExact
open TopologicalSpace TopCat.Presheaf

/-- **(`lem:tilde_mono`)** Project-local (affine bridge): `tilde` preserves monomorphisms.
For an injective `R`-linear map `f`, the sheaf map `tilde.map f` is a monomorphism of
`𝒪_{Spec R}`-modules. Proved stalkwise: over each basic open `D(g)`, `tilde`'s section
map is the localization of `f` (via `tilde.toOpen` being `IsLocalizedModule.Away g`),
injective by `IsLocalizedModule.map_injective`; basic-open injectivity gives stalk
injectivity (`stalkFunctor_map_injective_of_isBasis`), hence mono
(`mono_of_stalk_mono`), reflected through the fully faithful `modulesSpecToSheaf`. -/
theorem tilde_mono {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] :
    Mono (AlgebraicGeometry.tilde.map f) := by
  have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp inferInstance
  haveI hff : (modulesSpecToSheaf (R := R)).Faithful := SpecModulesToSheafFullyFaithful.faithful
  apply modulesSpecToSheaf.mono_of_mono_map (f := AlgebraicGeometry.tilde.map f)
  have hB : Opens.IsBasis (α := ↥(Spec R)) (Set.range PrimeSpectrum.basicOpen) :=
    PrimeSpectrum.isBasis_basic_opens
  have hsec : ∀ U ∈ Set.range (PrimeSpectrum.basicOpen (R := R)),
      Function.Injective
        ⇑((modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app (op U)) := by
    rintro U ⟨g, rfl⟩
    have hsq := AlgebraicGeometry.tilde.toOpen_map_app f (PrimeSpectrum.basicOpen g)
    have hsqlin :
        ((modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app
            (op (PrimeSpectrum.basicOpen g))).hom.comp
          (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom
        = (AlgebraicGeometry.tilde.toOpen N (PrimeSpectrum.basicOpen g)).hom.comp f.hom := by
      have h2 := congrArg ModuleCat.Hom.hom hsq
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
      exact h2
    have hmap :
        ((modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app
            (op (PrimeSpectrum.basicOpen g))).hom
        = IsLocalizedModule.map (.powers g)
            (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom
            (AlgebraicGeometry.tilde.toOpen N (PrimeSpectrum.basicOpen g)).hom f.hom := by
      apply IsLocalizedModule.linearMap_ext (.powers g)
        (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom
        (AlgebraicGeometry.tilde.toOpen N (PrimeSpectrum.basicOpen g)).hom
      rw [hsqlin, IsLocalizedModule.map_comp]
    rw [show (⇑((modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app
        (op (PrimeSpectrum.basicOpen g))))
        = ⇑((modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app
        (op (PrimeSpectrum.basicOpen g))).hom from rfl, hmap]
    exact IsLocalizedModule.map_injective (.powers g) _ _ f.hom hf
  haveI hstalk : ∀ (x : ↥(Spec R)), Mono ((stalkFunctor (ModuleCat ↑R) x).map
      (modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom) := by
    intro x
    exact (ModuleCat.mono_iff_injective _).mpr
      (TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB hsec x)
  exact TopCat.Presheaf.mono_of_stalk_mono _

/-- **(affine bridge)** Project-local: `tilde.functor R` preserves monomorphisms.
Packages `tilde_mono` as a typeclass instance. -/
instance tilde_preservesMono {R : CommRingCat.{u}} :
    (AlgebraicGeometry.tilde.functor R).PreservesMonomorphisms where
  preserves f hf := by rw [AlgebraicGeometry.tilde.functor_map]; exact tilde_mono f

/-- **(affine bridge)** Project-local: `tilde.functor R` preserves finite limits (is left
exact). `tilde` is already right exact (left adjoint ⇒ preserves finite colimits), so by
`preservesFiniteColimits_iff_forall_exact_map_and_epi` every short exact sequence maps to
an exact one with the right map epi; combined with `tilde_preservesMono` this is exactly
the criterion `preservesFiniteLimits_iff_forall_exact_map_and_mono`. -/
instance tilde_preservesFiniteLimits {R : CommRingCat.{u}} :
    PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (AlgebraicGeometry.tilde.functor R)).mp inferInstance S hS).1, ?_⟩
  haveI := hS.mono_f
  exact (AlgebraicGeometry.tilde.functor R).map_mono S.f

/-- **(`lem:tilde_exact`)** Project-local (affine bridge): `tilde` is exact. A short exact
sequence `0 → A → B → C → 0` of `R`-modules is sent by `tilde.functor R` to a short exact
sequence `0 → Ã → B̃ → C̃ → 0` of quasi-coherent `𝒪_{Spec R}`-modules. Immediate from
`tilde` preserving both finite limits (`tilde_preservesFiniteLimits`) and finite colimits
(left adjoint), via `ShortComplex.ShortExact.map_of_exact`. This is the reusable
exactness half of `QCoh(Spec R) ≅ ModuleCat R` feeding the free-resolution step 1.4. -/
theorem tilde_exact {R : CommRingCat.{u}} (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) :
    (S.map (AlgebraicGeometry.tilde.functor R)).ShortExact :=
  hS.map_of_exact (AlgebraicGeometry.tilde.functor R)

/-- **(`lem:functorT_halfexact`, brick (ii) of 1.3)** For `F` `S`-flat, the functor
`T = functorT A f I F` (`M ↦ Ext¹_X(I, F ⊗_S M~)`) is half-exact: it sends every short
exact sequence of `A`-modules to a short complex exact at its middle term.

This is the load-bearing translation between the abstract `ShortComplex.Exact` of
`S.map (functorT A f I F)` (taken in `ModuleCat.{u+1} ↑A`) and the membership form of
middle-exactness of `Ext¹_X(I, F ⊗_S −)` supplied by `ext_tensor_halfexact_of_flat`.

`ShortComplex.moduleCat_exact_iff` reduces exactness to: every `x₂` in the middle module
killed by `(S.map functorT).g` lifts along `(S.map functorT).f`. Unfolding the End-action
lift `liftAdditiveToModuleCat` and `covariantExtFunctor`, `(S.map functorT).g` is
`x ↦ x.comp (Ext.mk₀ ((tensorBaseChangeFunctor f F).map ((tilde.functor A).map S.g)))`,
which is *definitionally* the map in the membership statement of
`ext_tensor_halfexact_of_flat f I F hF 1 (S.map (tilde.functor A)) (tilde_exact S hS)`
(via `(sc.map T).g = T.map sc.g` with `sc = S.map (tilde.functor A)`). The two membership
statements thus coincide and the lift is supplied directly. See `lem:functorT_halfexact`. -/
theorem functorT_halfExact {X : Scheme.{u}} (A : CommRingCat.{u}) (f : X ⟶ Spec A)
    (I F : X.Modules) (hF : IsSFlat f F) : IsHalfExact (functorT A f I F) := by
  intro _ S hS
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  have hsc := tilde_exact S hS
  exact ext_tensor_halfexact_of_flat f I F hF 1 _ hsc x₂ hx₂

/-- **(brick (iv) core of 1.3)** Vanishing of `T = functorT A f I F` on *every*
finitely generated module from vanishing on the residue field. Over a Noetherian local
ring `A`, the half-exactness `functorT_halfExact` (brick (ii)) combines with the OB 2.1
anchor `External.halfexact_free` to upgrade `T(k) = 0` to `T(M) = 0` for all `M`.

This packages the homological heart of the (1.3) proof ("since `T` is half-exact and
`T(k(s)) = 0`, `T(M) = 0` for every finitely generated `A`-module `M`"): it consumes the
fibrewise hypothesis `hk` (to be discharged by brick (iii), `T(k(s)) = Ext¹_X(I, j_*F(s))
= 0`, via `External.adjunction` + the 1.2 SES on the closed fibre) and produces the
input to the free conclusion (the adjacent `Hom`-functor is exact, hence `H` is free).
Axiom-clean modulo the existing anchors `External.flat_tensor_exact` (half-exactness)
and `External.halfexact_free` (OB 2.1). See `lem:functorT_halfexact` / `thm:ob_halfexact_free`. -/
theorem functorT_eq_zero_of_residue {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (hF : IsSFlat f F)
    (hk : IsZero ((functorT A f I F).obj
      (ModuleCat.of ↑A (IsLocalRing.ResidueField ↑A))))
    (M : ModuleCat.{u} ↑A) : IsZero ((functorT A f I F).obj M) :=
  External.halfexact_free ↑A (functorT A f I F) (functorT_halfExact A f I F hF) hk M

/-! ## Project-local Mathlib supplement — contravariant-Ext diagram chase (1.3 brick (iii) core)

The homological heart of Altman–Kleiman's `T(k(s)) = Ext¹_X(I, j_*F(s)) = 0` argument
((1.3) proof, p. 56). AK apply `Hom_X(-, j_*F(s))` to the acyclic short exact sequence
`0 → K → J → I → 0` of `exists_acyclic_surjection` and chase the **contravariant** Ext long
exact sequence: with `Ext¹(J, -) = 0` (the acyclic `J`) and `Hom(J,-) ↠ Hom(K,-)` (the
adjunction ladder), `Ext¹(I, -) = 0` follows. This is a *degree-0* adjunction + a chase, NOT
a degree-1 derived adjunction. The chase needs only Mathlib's contravariant Ext LES
(`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃` and the consecutive-maps-compose-
to-zero fact `ShortComplex.ShortExact.extClass_comp_assoc`), so the core is buildable
axiom-clean. The scheme-side hypotheses (`hJ` from acyclicity, `hsurj` from the adjunction
ladder, and the fibre identification `F ⊗_S k(s)~ ≅ j_*F(s)`) are discharged in later bricks. -/
section AcyclicChase
open CategoryTheory.Abelian

/-- **(1.3 brick (iii) core, `lem:ext1_vanishing_of_acyclic_chase`)** The abstract
contravariant-Ext diagram chase. For a short exact sequence `S = (0 → K → J → I → 0)` in any
abelian category with `Ext` and any object `Y`: if `Ext¹(J, Y) = 0` and the precomposition
map `Hom(J, Y) → Hom(K, Y)` (degree-0 `Ext`, precompose with `S.f`) is surjective, then
`Ext¹(I, Y) = 0`. Project-local: this is the homological core of Altman–Kleiman's
`T(k(s)) = 0` step (1.3), phrased generically so the scheme-side inputs can be supplied later.

Proof (the faithful AK chase): given `x : Ext¹(I, Y)`, its image in `Ext¹(J, Y)` is `0` by
`hJ`, so by exactness of the contravariant LES (`contravariant_sequence_exact₃`) it lifts to
`w : Hom(K, Y)` with `extClass.comp w = x`; surjectivity writes `w = (mk₀ S.f).comp v`, and the
two consecutive LES maps compose to zero (`extClass_comp_assoc`), so `x = 0`. -/
theorem ext1_vanishing_of_acyclic_chase {C : Type*} [Category C] [Abelian C]
    [HasExt C] (S : ShortComplex C) (hS : S.ShortExact) (Y : C)
    (hJ : ∀ y : Ext S.X₂ Y 1, y = 0)
    (hsurj : Function.Surjective
      (fun v : Ext S.X₂ Y 0 => (Ext.mk₀ S.f).comp v (zero_add 0)))
    (x : Ext S.X₃ Y 1) : x = 0 := by
  have hgx : (Ext.mk₀ S.g).comp x (zero_add 1) = 0 := hJ _
  obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₃ hS Y x hgx (n₀ := 0) (by norm_num)
  obtain ⟨v, hv⟩ := hsurj w
  rw [← hw, ← hv]
  exact hS.extClass_comp_assoc v

/-- **(1.3 helper)** Bridge between the `IsZero` form of `extGroup` and the membership form
`∀ y, y = 0`. An object of `Ab` is zero iff it is a subsingleton iff all its elements vanish;
specialized to `extGroup q M N` so the project's `FiberExtVanishes` / acyclicity `IsZero`
conditions translate to the membership hypotheses consumed by `ext1_vanishing_of_acyclic_chase`,
and back. Project-local. -/
lemma isZero_extGroup_iff {Y : Scheme.{u}} (q : ℕ) (M N : Y.Modules) :
    IsZero (extGroup q M N) ↔ ∀ y : (extGroup q M N), y = 0 := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, subsingleton_iff_forall_eq 0]

/-- **(1.3 brick (iii), scheme form)** The contravariant-Ext chase packaged in the project's
`extGroup` `IsZero` notation, over `Y.Modules`. For a short exact sequence `S = (0 → K → J → I
→ 0)` of `𝒪_Y`-modules and an `𝒪_Y`-module `W`: `Ext¹_Y(J, W) = 0` together with surjectivity
of `Hom_Y(J, W) → Hom_Y(K, W)` gives `Ext¹_Y(I, W) = 0`. This is the form that discharges the
homological half of `hk` (`T(k(s)) = Ext¹_X(I, j_*F(s)) = 0`) once the scheme-side SES,
acyclicity (`exists_acyclic_surjection`), and adjunction-ladder surjectivity are supplied.
Project-local; reduces to `ext1_vanishing_of_acyclic_chase` via `isZero_extGroup_iff`. -/
theorem ext1_isZero_of_acyclic_chase {Y : Scheme.{u}} (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) (W : Y.Modules)
    (hJ : IsZero (extGroup 1 S.X₂ W))
    (hsurj :
      letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
      haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
      Function.Surjective
        (fun v : Ext S.X₂ W 0 => (Ext.mk₀ S.f).comp v (zero_add 0))) :
    IsZero (extGroup 1 S.X₃ W) := by
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  rw [isZero_extGroup_iff] at hJ ⊢
  exact fun x => ext1_vanishing_of_acyclic_chase S hS W hJ hsurj x

/-- **(1.3 helper)** `IsZero (extGroup q · N)` transports across an isomorphism of the
first ( contravariant) argument: an iso `e : M ≅ M'` carries `Ext^q(M, N) = 0` to
`Ext^q(M', N) = 0`. Project-local; needed to strip the `pullback (𝟙 X)` wrapper off the
acyclicity output of `exists_acyclic_surjection`. Proved by transporting elements through
`Ext.mk₀ e.hom` / `Ext.mk₀ e.inv` (a two-sided inverse via `mk₀_comp_mk₀` + `inv_hom_id`). -/
lemma isZero_extGroup_of_iso_left {Y : Scheme.{u}} (q : ℕ) {M M' : Y.Modules}
    (e : M ≅ M') (N : Y.Modules) (h : IsZero (extGroup q M N)) :
    IsZero (extGroup q M' N) := by
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  rw [isZero_extGroup_iff] at h ⊢
  intro y
  have key : (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp y (zero_add q)) (zero_add q) = y := by
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.mk₀_id_comp]
  rw [← key, h ((Ext.mk₀ e.hom).comp y (zero_add q))]
  exact Ext.comp_zero _ _ _ _ _

/-- **(1.3 helper, `lem:isZero_extGroup_of_iso_right`)** `IsZero (extGroup q M ·)`
transports across an isomorphism of the second (covariant) argument: an iso `e : N ≅ N'`
carries `Ext^q(M, N) = 0` to `Ext^q(M, N') = 0`. The second-argument mirror of
`isZero_extGroup_of_iso_left`; needed to transport the homological vanishing
`Ext¹_X(I, j_*j^*F) = 0` along the fibre identification `j_*j^*F ≅ F ⊗_S k(s)~`
(`External.fibre_tensor_residue_iso`) into the residue value of `functorT`. Proved by
transporting elements through postcomposition with `Ext.mk₀ e.inv` / `Ext.mk₀ e.hom`
(a two-sided inverse via `mk₀_comp_mk₀` + `inv_hom_id`). Project-local. -/
lemma isZero_extGroup_of_iso_right {Y : Scheme.{u}} (q : ℕ) (M : Y.Modules) {N N' : Y.Modules}
    (e : N ≅ N') (h : IsZero (extGroup q M N)) :
    IsZero (extGroup q M N') := by
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  rw [isZero_extGroup_iff] at h ⊢
  intro y
  have key : (y.comp (Ext.mk₀ e.inv) (add_zero q)).comp (Ext.mk₀ e.hom) (add_zero q) = y := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]
  rw [← key, h (y.comp (Ext.mk₀ e.inv) (add_zero q))]
  exact Ext.zero_comp _ _ _ _ _

/-- **(1.3 brick (iii), discharges `hJ`)** The acyclic `J` produced by
`exists_acyclic_surjection` satisfies `Ext¹_X(J, W) = 0` for every quasi-coherent `W`.
Specialize the acyclicity hypothesis (vanishing of `Ext^q((g^* J), G)` for affine `g`, `q > 0`)
to the identity `g = 𝟙 X` (which is affine), then strip the `pullback (𝟙 X)` wrapper via
`Scheme.Modules.pullbackId` and `isZero_extGroup_of_iso_left`. This is precisely the `hJ`
hypothesis of `ext1_isZero_of_acyclic_chase`, so the homological half of the (1.3)
`T(k(s)) = Ext¹_X(I, j_*F(s)) = 0` step is now assembled up to the adjunction-ladder
surjectivity (`hsurj`) and the fibre identification `F ⊗_S k(s)~ ≅ j_*F(s)`. Project-local. -/
theorem acyclic_ext1_vanishes {X : Scheme.{u}} (J : X.Modules)
    (hac : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
        (_ : G.IsQuasicoherent) (q : ℕ) (_ : 0 < q),
        IsZero (extGroup q ((Scheme.Modules.pullback g).obj J) G))
    (W : X.Modules) (hW : W.IsQuasicoherent) : IsZero (extGroup 1 J W) :=
  isZero_extGroup_of_iso_left 1 ((Scheme.Modules.pullbackId X).app J) W
    (hac (𝟙 X) W hW 1 one_pos)

end AcyclicChase

end TildeExact

/-- **(`lem:fp_sheaf_affine_tilde`)** Project-local (affine bridge, essential
surjectivity): a finitely presented (`IsLFP`) `𝒪_{Spec R}`-module `I` is the tilde
of a finitely presented `R`-module `M` (`M = Γ(Spec R, I)`). This completes the
affine bridge `QCoh(Spec R) ≃ Mod_R` on the finitely presented side: combined with
`tilde_free` and `tilde_exact`, it transports a module-level free presentation of
`M` into the sheaf-level free-resolution step (1.4).

Immediate from the affine quasi-coherence anchor `External.affine_fp_tilde`
(Stacks 01IA + 01PC): `IsLFP I` is by definition `I.IsFinitePresentation`, which is
exactly the instance the anchor consumes. -/
theorem fp_sheaf_affine_tilde {R : CommRingCat.{u}} (I : (Spec R).Modules)
    (hI : IsLFP I) :
    ∃ (M : ModuleCat.{u} ↑R), Module.FinitePresentation ↑R M ∧
      Nonempty (AlgebraicGeometry.tilde M ≅ I) :=
  haveI : I.IsFinitePresentation := hI
  External.affine_fp_tilde I

/-- **(`lem:tilde_isFP`)** Project-local (affine bridge, Stacks 01PC forward): the
tilde `~M` of a finitely presented `R`-module `M` is a finitely presented
(`IsLFP`) `𝒪_{Spec R}`-module. The forward direction of the affine quasi-coherence
equivalence, complementing `fp_sheaf_affine_tilde` (the reverse direction). Used in
the free-resolution step (1.4) to recognize `~K₀` and `~A₀ⁿ` as locally finitely
presented once `K₀` and `A₀ⁿ` are finitely presented `A₀`-modules.

Derives from the anchor `External.tilde_isFP` (the cited Stacks 01PC forward
direction); `IsLFP` is by definition `SheafOfModules.IsFinitePresentation`. -/
theorem tilde_isFP {R : CommRingCat.{u}} (M : ModuleCat.{u} ↑R)
    [Module.FinitePresentation ↑R M] :
    IsLFP (AlgebraicGeometry.tilde M) :=
  External.tilde_isFP M

/-! ### Free presentations on the affine bridge (P1b-ii′, step 3 scaffolding)

The free-resolution step (1.4) consumes a sheaf together with a *free presentation*:
an epimorphism `G ↠ M` from a free `𝒪_{Spec R}`-module whose kernel is, in turn, the
epimorphic image of a free module. Mathlib packages a global presentation of a sheaf
of modules as `SheafOfModules.Presentation` (generators + relations, both
`SheafOfModules.free`); the lemmas here translate that data into the project's
`IsFreeMod` predicate, so that once a global presentation is available — from the
essential-surjectivity brick `affine_global_presentation` (the remaining Mathlib gap;
see `task_results/`) or from the planned `External.affine_essImage` anchor — the
free presentation feeding 1.4 follows by pure assembly.

These are deliberately independent of the (currently blocked) globalization: they take
the presentation as input, exactly as `tilde_of_presentation` does. -/

/-- **(affine bridge)** Project-local: Mathlib's `SheafOfModules.free Λ` is a free
`𝒪_X`-module in the project sense (`IsFreeMod`). The bridge between Mathlib's
free sheaf of modules (used by `SheafOfModules.Presentation`) and the project predicate
`IsFreeMod`; reused wherever a presentation's generators/relations are recognized as
free. -/
theorem free_isFreeMod {X : Scheme.{u}} (Λ : Type u) :
    IsFreeMod (SheafOfModules.free (R := X.ringCatSheaf) Λ) :=
  ⟨Λ, ⟨Iso.refl _⟩⟩

/-- **(affine bridge)** Project-local: a global presentation `P : M.Presentation` of a
quasi-coherent `𝒪_{Spec R}`-module `M` yields a *free presentation* of `M` in project
terms — a free module `G` with an epimorphism `g : G ↠ M`, together with a free module
`K` epimorphically covering `ker g`. This is the 2-term free presentation
`free K → free G → M → 0` re-expressed through `IsFreeMod`; it is the shape the
free-resolution step (1.4) consumes on the affine charts. Built directly from the
`generators`/`relations` epimorphisms of the Mathlib `Presentation`, with both free
covers recognized via `free_isFreeMod`. -/
theorem exists_free_presentation_of_presentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (P : M.Presentation) :
    ∃ (K G : (Spec R).Modules) (_ : IsFreeMod K) (_ : IsFreeMod G)
      (g : G ⟶ M) (_ : Epi g) (k : K ⟶ kernel g), Epi k :=
  ⟨_, _, free_isFreeMod _, free_isFreeMod _,
    P.generators.π, P.generators.epi, P.relations.π, P.relations.epi⟩

/-! ### Module-theoretic free-presentation step over a Noetherian affine (1.4 core)

The module-theoretic heart of the free-resolution step (1.4), over the Noetherian
affine `X₀ = Spec A₀` of the blueprint proof. Over a Noetherian ring a finite module
`M` admits a *finite free presentation* `0 → K → Rⁿ → M → 0`: the kernel `K` of a
surjection from a finite free module is finitely generated (a submodule of a finite
module over a Noetherian ring) hence finitely presented. This sequence
tilde-transports (via `tilde_free`, `tilde_exact`) to the sheaf-level sequence over
`Spec R` feeding (1.4). Pure module theory — no sheaf gaps. -/

/-- **(1.4 core, module step)** Project-local: over a Noetherian ring `R`, a finite
`R`-module `M` admits a surjection `p : Rⁿ ↠ M` from a finite free module whose
kernel is finitely presented. The blueprint's "finite free presentation of `M₀`,
with finitely generated (hence, over the Noetherian `A₀`, finitely presented)
kernel" step of `lem:free_resolution_step`. -/
theorem exists_finiteFreePresentation_of_noetherian {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (n : ℕ) (p : ModuleCat.of R (Fin n →₀ R) ⟶ M),
      Epi p ∧ Module.FinitePresentation R ↑(kernel p) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨n, ModuleCat.ofHom (Finsupp.linearCombination R s), ?_, ?_⟩
  · rw [ModuleCat.epi_iff_surjective]
    simp only [ModuleCat.hom_ofHom]
    apply LinearMap.range_eq_top.mp
    rw [Finsupp.range_linearCombination]
    exact hs
  · -- kernel of `p` is finite (submodule of a finite module over a Noetherian ring),
    -- hence finitely presented over the Noetherian `R`.
    set p : ModuleCat.of R (Fin n →₀ R) ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination R s)
    haveI : Module.Finite R ↑(kernel p) :=
      Module.Finite.equiv (ModuleCat.kernelIsoKer p).toLinearEquiv.symm
    exact Module.finitePresentation_of_finite R _

/-- **(affine bridge)** Project-local: the tilde of a *finite* free module
`A₀^n = Fin n →₀ A₀` (index `Fin n : Type 0`) is a free `𝒪_{Spec A₀}`-module.
A `Fin n`-indexed variant of `tilde_free` (whose index lives in `Type u`): reindex
`Fin n →₀ A₀` along `ULift.{u} (Fin n) ≃ Fin n`, tilde, and apply `tildeFinsupp`.
Feeds the middle term `J = ~A₀ⁿ` of the free-resolution step (1.4). -/
theorem tilde_free_fin {R : CommRingCat.{u}} (n : ℕ) :
    IsFreeMod (AlgebraicGeometry.tilde (ModuleCat.of ↑R (Fin n →₀ ↑R)) : (Spec R).Modules) := by
  refine ⟨ULift.{u} (Fin n), ⟨?_⟩⟩
  refine (AlgebraicGeometry.tilde.functor R).mapIso
    (LinearEquiv.toModuleIso
      (Finsupp.domLCongr (Equiv.ulift.{u, 0} (α := Fin n)).symm)) ≪≫
    AlgebraicGeometry.tildeFinsupp (ULift.{u} (Fin n))

/-- **(1.4 assembly)** Pullback of a free `𝒪_Y`-module along a scheme morphism is a
free `𝒪_X`-module. Thin wrapper over the anchor `External.pullback_isFreeMod`
(the standard `p^* 𝒪_Y ≅ 𝒪_X` + pullback-preserves-coproducts fact invoked implicitly
in the 1.4 Step-3; the underlying structure-sheaf-pullback iso for
`Scheme.Modules.pullback` is absent from Mathlib v4.30.0 for a general scheme morphism,
so the fact is anchored rather than built). -/
theorem pullback_isFreeMod {X Y : Scheme.{u}} (p : X ⟶ Y) {M : Y.Modules}
    (h : IsFreeMod M) : IsFreeMod ((Scheme.Modules.pullback p).obj M) :=
  External.pullback_isFreeMod p h

/-- **(1.4 assembly)** Pullback preserves finite presentation: if `M` is a locally
finitely presented `𝒪_Y`-module then so is its pullback `(pullback p).obj M`. Thin
wrapper over the anchor `External.pullback_isLFP` (standard base-change stability of
finite presentation; the fp-globalization reconstruction for `Scheme.Modules.pullback`
is absent from Mathlib v4.30.0, so the fact is anchored). -/
theorem pullback_isLFP {X Y : Scheme.{u}} (p : X ⟶ Y) {M : Y.Modules}
    (h : IsLFP M) : IsLFP ((Scheme.Modules.pullback p).obj M) :=
  External.pullback_isLFP p h

/-! ### Free-resolution step (1.4) assembly

The 3-step proof of `lem:free_resolution_step` (Altman–Kleiman §1, (1.4)):
descend the data to a Noetherian affine `Spec A₀` (`External.descent_noetherian`),
resolve `I₀ ≅ ~M₀` there by a finite free module (`fp_sheaf_affine_tilde` +
`exists_finiteFreePresentation_of_noetherian`, tilde-d up via `tilde_exact`,
`tilde_free_fin`, `tilde_isFP`), and pull the resulting short exact sequence back to
`X` (`External.flat_pullback_exact`, using that `I ≅ p* I₀` is `S`-flat). The free /
finite-presentation properties of the pulled-back terms use `pullback_isFreeMod` /
`pullback_isLFP` (whose pullback-preservation cores are the residual Mathlib gaps). -/

/-- **(1.4)** Free resolution step over an affine base: an `S`-flat finitely
presented `𝒪_X`-module `I` fits in a short exact sequence `0 → K → J → I → 0`
with `K, J` finitely presented and `J` free. See `lem:free_resolution_step`.

(Relocated below the affine-bridge lemmas it consumes; the strand-(b) section above
carries a pointer.) -/
theorem exists_free_resolution_step (f : X ⟶ S) (haX : IsAffine X) (haS : IsAffine S)
    (hfp : LocallyOfFinitePresentation f) (I : X.Modules) (hI : IsLFP I)
    (hflat : IsSFlat f I) :
    ∃ sc : ShortComplex X.Modules, sc.ShortExact ∧ Nonempty (sc.X₃ ≅ I) ∧
      IsFreeMod sc.X₂ ∧ IsLFP sc.X₁ ∧ IsLFP sc.X₂ := by
  -- Step 1: descend `(X, I)` to a Noetherian affine `Spec A₀`.
  obtain ⟨A₀, hNoeth, p, I₀, hI₀fp, ⟨edesc⟩⟩ :=
    External.descent_noetherian haS f haX I hI hflat
  haveI : IsNoetherianRing ↑A₀ := hNoeth
  -- Step 2: resolve `I₀ ≅ ~M₀` over `Spec A₀` by a finite free module.
  obtain ⟨M₀, hM₀fp, ⟨tM⟩⟩ := fp_sheaf_affine_tilde I₀ hI₀fp
  haveI : Module.FinitePresentation ↑A₀ M₀ := hM₀fp
  obtain ⟨n, q, hq, hKfp⟩ := exists_finiteFreePresentation_of_noetherian M₀
  haveI : Epi q := hq
  haveI : Module.FinitePresentation ↑A₀ ↑(kernel q) := hKfp
  haveI : Module.FinitePresentation ↑A₀ (ModuleCat.of ↑A₀ (Fin n →₀ ↑A₀)) :=
    inferInstanceAs (Module.FinitePresentation ↑A₀ (Fin n →₀ ↑A₀))
  -- the module short exact sequence `0 → ker q → A₀ⁿ → M₀ → 0`.
  have hSES : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_kernel q)
  -- tilde it: `0 → ~ker q → ~A₀ⁿ → ~M₀ → 0` over `Spec A₀`.
  have htilde := tilde_exact (ShortComplex.mk (kernel.ι q) q (kernel.condition q)) hSES
  -- `I ≅ p* (~M₀)` (via `I ≅ p* I₀` and `~M₀ ≅ I₀`).
  have e : I ≅ (Scheme.Modules.pullback p).obj
      (AlgebraicGeometry.tilde M₀ : (Spec A₀).Modules) :=
    edesc ≪≫ ((Scheme.Modules.pullback p).mapIso tM).symm
  -- Step 3: pull back along `p`; flatness keeps it short exact. `sc₀` is inferred from
  -- `htilde` (so the tilde-functor `ShortComplex.map` instance is reused, not re-synthesized).
  have hSEpull := External.flat_pullback_exact f p _ htilde I hflat e
  refine ⟨_, hSEpull, ⟨e.symm⟩, ?_, ?_, ?_⟩
  · -- `IsFreeMod (p* ~A₀ⁿ)` — pullback of free is free.
    apply pullback_isFreeMod
    exact tilde_free_fin n
  · -- `IsLFP (p* ~ker q)` — pullback preserves finite presentation.
    apply pullback_isLFP
    exact tilde_isFP (kernel q)
  · -- `IsLFP (p* ~A₀ⁿ)`.
    apply pullback_isLFP
    exact tilde_isFP (ModuleCat.of ↑A₀ (Fin n →₀ ↑A₀))

end MR0555258CompactifyingPicard

/-! ## Project-local Mathlib supplement — extension by zero `j_!`

For an open immersion `j : U ⟶ X` of schemes, Mathlib (v4.30.0) provides the
restriction functor `Scheme.Modules.restrictFunctor j` (`= j^*`) together with its
*right* adjoint `pushforward j` (`= j_*`) via `restrictAdjunction`, but **no left
adjoint to `j^*`**. We supply that left adjoint — *extension by zero* `j_!` —
together with the adjunction `j_! ⊣ j^*`.

The construction reuses Mathlib's general site-pushforward machinery rather than
the hand-rolled left-Kan-extension + sheafify route: by definition,
`restrictFunctor j` is `SheafOfModules.pushforward φ` for the canonical ring-sheaf
morphism `φ` induced by `j` (see `restrictFunctor_eq_pushforward`). Because the
base sites are the *small* categories `Opens U`, `Opens X`, the presheaf-level
pushforward along `j.opensFunctor` automatically has a left adjoint
(`PresheafOfModules.pushforward.IsRightAdjoint`), which sheafifies to a left
adjoint of the sheaf-level pushforward (`SheafOfModules.pushforward.IsRightAdjoint`
from `PullbackContinuous`). Mathlib packages this left adjoint as
`SheafOfModules.pullback φ` with adjunction
`SheafOfModules.pullbackPushforwardAdjunction φ : pullback φ ⊣ pushforward φ`.
Specializing `φ` to the restriction datum gives `j_! ⊣ j^*` definitionally. -/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits TopologicalSpace SheafOfModules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical morphism of sheaves of rings underlying restriction along an open
immersion `j : U ⟶ X`. This is exactly the datum Mathlib keeps inline inside
`Scheme.Modules.restrictFunctor`, exposed here as a named definition so that the
identification `restrictFunctor j = SheafOfModules.pushforward _` (and hence the
extension-by-zero adjunction) can be stated. Project-local because Mathlib does not
name it. -/
noncomputable def restrictionRingSheafHom :
    U.ringCatSheaf ⟶ (j.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ⟨Functor.whiskerRight ({ app V := (j.appIso V.unop).inv } :
    U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf) (forget₂ CommRingCat RingCat)⟩

/-- `Scheme.Modules.restrictFunctor j` is, definitionally, the sheaf-of-modules
pushforward along the continuous open-immersion site map with the restriction
ring-sheaf datum. This exposes the defeq that powers `extensionByZeroAdjunction`. -/
lemma restrictFunctor_eq_pushforward :
    Scheme.Modules.restrictFunctor j
      = SheafOfModules.pushforward.{u} (restrictionRingSheafHom j) :=
  rfl

/-- **Extension by zero** `j_!` for an open immersion `j : U ⟶ X` of schemes: the
left adjoint of the restriction functor `j^* = restrictFunctor j`. Realized as the
sheaf-of-modules pullback `SheafOfModules.pullback` along the restriction ring-sheaf
datum `restrictionRingSheafHom j`, whose existence as a left adjoint is supplied by
Mathlib's `PullbackContinuous` (small `Opens` sites ⟹ the presheaf-level left
adjoint exists ⟹ it sheafifies). Project-local: this left adjoint is **absent** from
Mathlib v4.30.0. -/
noncomputable def extensionByZero : U.Modules ⥤ X.Modules :=
  SheafOfModules.pullback.{u} (restrictionRingSheafHom j)

/-- The adjunction `j_! ⊣ j^*` for an open immersion `j : U ⟶ X`, i.e.
`extensionByZero j ⊣ restrictFunctor j`. Obtained from Mathlib's
`SheafOfModules.pullbackPushforwardAdjunction` for the restriction ring-sheaf datum,
using that `restrictFunctor j` is definitionally `SheafOfModules.pushforward _`
(`restrictFunctor_eq_pushforward`). Project-local: absent from Mathlib v4.30.0. -/
noncomputable def extensionByZeroAdjunction :
    extensionByZero j ⊣ Scheme.Modules.restrictFunctor j :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (restrictionRingSheafHom j)

/-- Extension by zero is a left adjoint. -/
instance : (extensionByZero j).IsLeftAdjoint :=
  (extensionByZeroAdjunction j).isLeftAdjoint

/-- Extension by zero preserves colimits (it is a left adjoint); in particular it
commutes with arbitrary direct sums, as used in the proof of (1.2). -/
noncomputable instance : PreservesColimitsOfSize.{u, u} (extensionByZero j) :=
  (extensionByZeroAdjunction j).leftAdjoint_preservesColimits

/-- The restriction functor `j^* = restrictFunctor j` preserves limits. It is the
*right* adjoint of the extension-by-zero adjunction `j_! ⊣ j^*`
(`extensionByZeroAdjunction`), hence preserves all (in particular finite) limits.
Combined with the fact that `j^*` is also a *left* adjoint (Mathlib's
`restrictAdjunction` gives `j^* ⊣ j_*`, so it preserves colimits), this exhibits
`j^*` as an **exact** functor of abelian categories — one of the two exactness halves
needed for the Ext-level form of `j_! ⊣ j^*`. Project-local: this limit-preservation
is not in Mathlib v4.30.0 because the left adjoint `j_!` it relies on is itself
project-local. -/
noncomputable instance restrictFunctor_preservesLimits :
    PreservesLimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) :=
  (extensionByZeroAdjunction j).rightAdjoint_preservesLimits

/-- **Reduction of `j_!`-exactness to mono-preservation.** Extension by zero preserves
finite limits as soon as it preserves monomorphisms. Since `j_!` is a left adjoint it
is right exact (preserves finite colimits), so by
`preservesFiniteLimits_iff_forall_exact_map_and_mono` finite-limit preservation is
equivalent to mono-preservation. This is the exact analogue of the affine-bridge
`tilde_preservesFiniteLimits` upgrade. The remaining hypothesis
`(extensionByZero j).PreservesMonomorphisms` is the genuine stalkwise content of the
open immersion — `(j_!M)_x = M_x` for `x ∈ U`, `0` for `x ∉ U`, both injectivity-
preserving — which is absent from Mathlib v4.30.0 (no stalk functor / joint
conservativity for `SheafOfModules` over a scheme, nor a stalk computation of
`SheafOfModules.pullback`). Project-local. -/
theorem extensionByZero_preservesFiniteLimits_of_preservesMono
    [(extensionByZero j).PreservesMonomorphisms] :
    PreservesFiniteLimits (extensionByZero j) := by
  haveI : (Scheme.Modules.restrictFunctor j).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (extensionByZero j).Additive :=
    (extensionByZeroAdjunction j).left_adjoint_additive
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
      (extensionByZero j)).mp inferInstance S hS).1, ?_⟩
  haveI := hS.mono_f
  exact (extensionByZero j).map_mono S.f

/-! ### Reduction of `j_!`-mono-preservation to the presheaf level

The remaining brick for unconditional `j_!` exactness is
`(extensionByZero j).PreservesMonomorphisms`. We reduce it from the *sheaf* level
to the *presheaf* level via Mathlib's `SheafOfModules.pullbackIso`, which factors
`j_! = SheafOfModules.pullback φ` as

  `forget U.Modules ⋙ PresheafOfModules.pullback φ.hom ⋙ PresheafOfModules.sheafification`.

The outer two factors preserve monomorphisms unconditionally — `forget` is a right
adjoint (preserves all limits) and `sheafification` is left exact (preserves finite
limits) — so `j_!` preserves monos as soon as the *middle* factor, the presheaf-level
pullback `PresheafOfModules.pullback φ.hom`, does. This converts the genuine stalkwise
content (the off-`U` vanishing that the `SheafOfModules`-level argument needs) into a
purely presheaf-level statement, where monomorphisms are detected sectionwise. -/
section PreservesMono
open CategoryTheory Limits TopologicalSpace SheafOfModules

set_option maxHeartbeats 1000000 in
-- The instance search for the three-factor `pullbackIso` composite is expensive (the
-- abelian / sheafification typeclass stack is deep), so the synthesis budget is raised.
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Reduction of `j_!`-mono-preservation to the presheaf pullback.** If the
presheaf-of-modules pullback `PresheafOfModules.pullback φ.hom` along the open-immersion
restriction datum `φ = restrictionRingSheafHom j` preserves monomorphisms, then so does
extension by zero `j_! = extensionByZero j`. Proved by factoring `j_!` through
`SheafOfModules.pullbackIso` as `forget ⋙ (presheaf pullback) ⋙ sheafification`, whose
outer factors (`forget`, a right adjoint; `sheafification`, left exact) preserve monos
unconditionally. Project-local: `j_!` is itself absent from Mathlib v4.30.0. -/
theorem extensionByZero_preservesMonomorphisms_of_presheafPullback
    [hp : (PresheafOfModules.pullback.{u} (restrictionRingSheafHom j).hom).PreservesMonomorphisms] :
    (extensionByZero j).PreservesMonomorphisms := by
  have e := SheafOfModules.pullbackIso.{u} (restrictionRingSheafHom j)
  refine (Functor.preservesMonomorphisms.iso_iff e).mpr ?_
  refine @Functor.preservesMonomorphisms_comp _ _ _ _ _ _ _ _ ?_ ?_
  · -- `forget` is a right adjoint, hence preserves (finite) limits, hence monos
    exact preservesMonomorphisms_of_preservesLimitsOfShape _
  · -- presheaf pullback (hypothesis `hp`) followed by sheafification (left exact)
    refine @Functor.preservesMonomorphisms_comp _ _ _ _ _ _ _ _ hp ?_
    exact preservesMonomorphisms_of_preservesLimitsOfShape
      (PresheafOfModules.sheafification (R₀ := X.ringCatSheaf.obj) (𝟙 X.ringCatSheaf.obj))

/-- **Conditional unconditional-style `j_!` exactness.** Combining the presheaf-level
reduction `extensionByZero_preservesMonomorphisms_of_presheafPullback` with the
already-landed `extensionByZero_preservesFiniteLimits_of_preservesMono`: if the presheaf
pullback preserves monomorphisms, then `j_! = extensionByZero j` preserves finite limits,
i.e. is left exact. Together with the colimit-preservation instance (`j_!` is a left
adjoint) this certifies `j_!` exact. This isolates the *single* remaining gap for
unconditional `j_!` exactness as the purely presheaf-level mono-preservation of
`PresheafOfModules.pullback (restrictionRingSheafHom j).hom`. Project-local. -/
theorem extensionByZero_preservesFiniteLimits_of_presheafPullback
    [(PresheafOfModules.pullback.{u} (restrictionRingSheafHom j).hom).PreservesMonomorphisms] :
    PreservesFiniteLimits (extensionByZero j) :=
  haveI := extensionByZero_preservesMonomorphisms_of_presheafPullback j
  extensionByZero_preservesFiniteLimits_of_preservesMono j

end PreservesMono

end AlgebraicGeometry.Scheme.Modules

/-! ### Acyclic surjection (1.2) anchor-and-assemble

`exists_acyclic_surjection` (`lem:acyclic_surjection`) is placed here, after the
`extensionByZero` (`j_!`) infrastructure block, because its two `External.*` anchors
reference `AlgebraicGeometry.Scheme.Modules.extensionByZero` and Lean requires that to
be in scope first. Following the documented **anchor-and-assemble** route (the 1.4
precedent: 6 EGA anchors composed; the `affine_fp_tilde` signal that a multi-iter
bottom-up build has confirmed a genuinely-absent Mathlib swath), the lemma is assembled
from the two general, non-§1 facts Altman–Kleiman invoke without proof in their (1.2)
argument, anchored as axioms and verbatim-sourced to the (1.2) proof text:

* `External.exists_extensionByZero_surjection` — surjection EXISTENCE only (the
  "affine sections generate" fact);
* `External.extensionByZero_coprod_acyclic` — acyclicity of the pullback of a SPECIFIC
  `∐` of extension-by-zeros (no surjection, no `I`).

Neither is (1.2); their conjunction (plus affine acyclicity, used inside the second)
assembles (1.2). The `019–021` bottom-up `j_!`-exactness build reduced to
`(PresheafOfModules.pullback (restrictionRingSheafHom j).hom).PreservesMonomorphisms`,
which is blocked on an absent pointwise Lan formula for the partial-adjoint presheaf
pullback; the conditional infra is kept above as upstreamable Mathlib-gap material. -/

namespace MR0555258CompactifyingPicard

open AlgebraicGeometry

/-- The coproduct `J = ∐_i (j_{U_i})_!(𝒪_{U_i})` of extension-by-zeros of structure
sheaves over a family `(U_i)` of (affine) opens. Shared between the two `(1.2)` anchors
and the assembled witness so that the acyclicity goal — phrased on
`(pullback g).obj (extensionByZeroCoprod ι U)` — unifies with the second anchor's
conclusion by definitional equality (no rewriting needed). Project-local. -/
private noncomputable abbrev extensionByZeroCoprod {X : Scheme.{u}}
    (ι : Type u) (U : ι → X.Opens) : X.Modules :=
  ∐ fun i => (AlgebraicGeometry.Scheme.Modules.extensionByZero (U i).ι).obj
    (SheafOfModules.unit (↑(U i) : Scheme.{u}).ringCatSheaf)

/-- **[AK §1, (1.2) proof]** Every `𝒪_X`-module admits a surjection from a coproduct of
extension-by-zeros of structure sheaves over affine opens. The standard "affine sections
generate" fact: for every germ of `I` there is an affine open `U` over which the germ is
the image of a section `s ∈ Γ(U, I)`, and via the adjunction `j_! ⊣ j^*`
(`extensionByZeroAdjunction`) the section `s` corresponds to a map
`(j_U)_!(𝒪_U) → I`; the coproduct of these is an epimorphism. Altman–Kleiman use this
without proof; anchored as a Mathlib-gap input (no `SheafOfModules` stalkwise
surjectivity in Mathlib v4.30.0). See `thm:exists_extensionByZero_surjection`. -/
axiom External.exists_extensionByZero_surjection {X : Scheme.{u}} (I : X.Modules) :
    ∃ (ι : Type u) (U : ι → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
      (π : extensionByZeroCoprod ι U ⟶ I), Epi π

/-- **[AK §1, (1.2) proof]** The pullback of such a coproduct of extension-by-zeros
along an affine morphism `g` is `Hom_Y(-,G)`-acyclic for quasi-coherent `G`: pullback
commutes with coproducts and with extension by zero, so `g^* J ≅ ∐_i (j_{g^{-1}U_i})_!
(𝒪_{g^{-1}U_i})` with each `g^{-1}U_i` affine, whence `Ext^q_Y(g^* J, G) = ∏_i
H^q(g^{-1}U_i, G|g^{-1}U_i) = 0` for `q > 0`. Bundles the base change, derived
`j_! ⊣ j^*` adjunction and `Ext`-additivity facts AK invoke without proof, together with
affine acyclicity (`External.ext_affine_acyclic`). Mathlib-gap (the `j_!`-exactness route
reduces to an absent presheaf-pullback Lan formula, and the derived adjunction needs
absent derivability data). See `thm:extensionByZero_coprod_acyclic`. -/
axiom External.extensionByZero_coprod_acyclic {X : Scheme.{u}}
    (ι : Type u) (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    {Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
    (hG : G.IsQuasicoherent) (q : ℕ) (hq : 0 < q) :
    IsZero (extGroup q ((Scheme.Modules.pullback g).obj (extensionByZeroCoprod ι U)) G)

/-- **(1.2)** Existence of an acyclic surjection: for any `𝒪_X`-module `I` there
is a surjection `J ⟶ I` with `J` acyclic for `Hom_Y(-,F)` along every affine
morphism `g : Y ⟶ X` and quasi-coherent `F`. See `lem:acyclic_surjection`.

Anchor-and-assemble: the surjection `(J, π)` is the first anchor; `J` is the coproduct
`extensionByZeroCoprod ι U` inferred from `π`'s type, and the per-`g` acyclicity is the
second anchor on the SAME `(ι, U, hU)`, so the goal
`IsZero (extGroup q ((pullback g).obj J) G)` unifies with the anchor's conclusion by
definitional equality. -/
theorem exists_acyclic_surjection {X : Scheme.{u}} (I : X.Modules) :
    ∃ (J : X.Modules) (π : J ⟶ I), Epi π ∧
      ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
        (_ : G.IsQuasicoherent) (q : ℕ) (_ : 0 < q),
        IsZero (extGroup q ((Scheme.Modules.pullback g).obj J) G) := by
  obtain ⟨ι, U, hU, π, hπ⟩ := External.exists_extensionByZero_surjection I
  exact ⟨_, π, hπ, fun {Y} g _ G hG q hq =>
    External.extensionByZero_coprod_acyclic ι U hU g G hG q hq⟩

/-! ## Project-local Mathlib supplement — (1.3) brick (iii) surjectivity bricks

The three buildable bricks that discharge `hsurj` of `ext1_isZero_of_acyclic_chase`
and assemble `Ext¹_X(I, j_*j^*F) = 0` (= `T(k(s)) = 0` up to the fibre
identification). See `lem:acyclic_ses`, `lem:fibre_hom_surjective`,
`lem:adjunction_ladder_surjective`, `lem:ext1_X_pushforward_fibre_vanishes`. -/

open CategoryTheory.Abelian

/-- **(1.3 brick (iii), `lem:acyclic_ses`)** The short exact sequence
`0 → K → J → I → 0` produced from `exists_acyclic_surjection I`: `J` is the acyclic
cover, `π : J ⟶ I` the epimorphism, and `K = ker π`. Packaged as a `ShortComplex`
with a `ShortExact` proof, `X₃` definitionally `I`, `X₂` definitionally `J`, and the
acyclicity of `J` (= `X₂`) carried alongside for the homological `hJ` of the chase.
Project-local. -/
theorem acyclic_ses {X : Scheme.{u}} (I : X.Modules) :
    ∃ (sc : ShortComplex X.Modules) (_ : sc.ShortExact) (_ : sc.X₃ = I),
      ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
        (_ : G.IsQuasicoherent) (q : ℕ) (_ : 0 < q),
        IsZero (extGroup q ((Scheme.Modules.pullback g).obj sc.X₂) G) := by
  obtain ⟨J, π, hπ, hac⟩ := exists_acyclic_surjection I
  haveI : Epi π := hπ
  exact ⟨ShortComplex.mk (kernel.ι π) π (kernel.condition π),
    ShortComplex.ShortExact.mk (ShortComplex.exact_kernel π), rfl,
    fun {Y} g _ G hG q hq => hac g G hG q hq⟩

/-- **(1.3 helper)** Bridge between the degree-0 `Ext` precomposition surjectivity
(the form consumed by `ext1_isZero_of_acyclic_chase`/`contravariant_sequence_exact₁`)
and the plain `Hom`-set precomposition surjectivity (the form produced by the
adjunction ladder). The bijection `Ext.mk₀ : (J ⟶ N) ≃ Ext J N 0`
(`Ext.mk₀_bijective`) conjugates the two precomposition maps via
`Ext.mk₀_comp_mk₀`. Project-local. -/
lemma ext0_precomp_surjective_iff {Y : Scheme.{u}} {K J N : Y.Modules} (φ : K ⟶ J) :
    letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
    haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
    (Function.Surjective (fun v : Ext J N 0 => (Ext.mk₀ φ).comp v (zero_add 0))
      ↔ Function.Surjective (fun v : (J ⟶ N) => φ ≫ v)) := by
  letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard Y.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory Y.Modules
  constructor
  · intro h w
    obtain ⟨ve, hve⟩ := h (Ext.mk₀ w)
    refine ⟨Ext.homEquiv₀ ve, ?_⟩
    have hmk : Ext.mk₀ (φ ≫ Ext.homEquiv₀ ve) = Ext.mk₀ w := by
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]; exact hve
    exact (Ext.mk₀_bijective K N).1 hmk
  · intro h w
    obtain ⟨vh, hvh⟩ := h (Ext.homEquiv₀ w)
    refine ⟨Ext.mk₀ vh, ?_⟩
    simp only at hvh ⊢
    rw [Ext.mk₀_comp_mk₀, hvh, Ext.mk₀_homEquiv₀_apply]

/-- **(1.3 brick (iii), `lem:adjunction_ladder_surjective`)** Transport precomposition
surjectivity through the pullback–pushforward adjunction `j^* ⊣ j_*`. For a morphism
`j : Y ⟶ X`, an `𝒪_Y`-module `G`, and `φ : K ⟶ J` in `X.Modules`: if precomposition
with `j^*φ` is surjective `Hom_Y(j^*J, G) → Hom_Y(j^*K, G)`, then precomposition with
`φ` is surjective `Hom_X(J, j_*G) → Hom_X(K, j_*G)`. The square commutes by
`Adjunction.homEquiv_naturality_left` of `Scheme.Modules.pullbackPushforwardAdjunction j`
(of which `External.adjunction` is the `homEquiv.symm`); conjugating the bottom-row
surjection by the two `homEquiv` bijections gives the top row. Project-local. -/
theorem adjunction_ladder_surjective {X Y : Scheme.{u}} (j : Y ⟶ X)
    {K J : X.Modules} (φ : K ⟶ J) (G : Y.Modules)
    (hsurj : Function.Surjective
      (fun u : (Scheme.Modules.pullback j).obj J ⟶ G =>
        (Scheme.Modules.pullback j).map φ ≫ u)) :
    Function.Surjective
      (fun v : J ⟶ (Scheme.Modules.pushforward j).obj G => φ ≫ v) := by
  intro w
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j
  obtain ⟨u, hu⟩ := hsurj ((adj.homEquiv K G).symm w)
  refine ⟨adj.homEquiv J G u, ?_⟩
  have hnat := adj.homEquiv_naturality_left φ u
  simp only at hu ⊢
  rw [← hnat, hu, Equiv.apply_symm_apply]

/-- **(1.3 brick (iii), `lem:fibre_hom_surjective`)** Surjectivity of the fibre-side
transition map `Hom_{X(s)}(j^*J, j^*F) → Hom_{X(s)}(j^*K, j^*F)` (precomposition with
`j^*(sc.f)`), for the fibre inclusion `j = f.fiberι s`. Given the pulled-back sequence
`0 → j^*K → j^*J → j^*I → 0` short exact (`hSEpull` — produced from `External.flat_pullback_exact`
using that `I = sc.X₃` is `S`-flat) and the fibre Ext-vanishing
`Ext¹_{X(s)}(j^*I, j^*F) = 0` (`FiberExtVanishes 1 f sc.X₃ F s`), the connecting map out of
`Ext⁰(j^*K, j^*F)` lands in the zero group `Ext¹(j^*I, j^*F)`, so by
`Ext.contravariant_sequence_exact₁` every element of `Ext⁰(j^*K, j^*F)` is in the image of
precomposition with `mk₀ (j^*sc.f)`; the `Ext⁰ ↔ Hom` bridge (`ext0_precomp_surjective_iff`)
restates this as `Hom`-precomposition surjectivity. Project-local. -/
theorem fibre_hom_surjective {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (sc : ShortComplex X.Modules) (F : X.Modules)
    (hSEpull : (sc.map (Scheme.Modules.pullback (f.fiberι s))).ShortExact)
    (hs : FiberExtVanishes 1 f sc.X₃ F s) :
    Function.Surjective
      (fun u : (Scheme.Modules.pullback (f.fiberι s)).obj sc.X₂ ⟶
          (Scheme.Modules.pullback (f.fiberι s)).obj F =>
        (Scheme.Modules.pullback (f.fiberι s)).map sc.f ≫ u) := by
  letI : HasDerivedCategory (f.fiber s).Modules :=
    HasDerivedCategory.standard (f.fiber s).Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory (f.fiber s).Modules
  refine (ext0_precomp_surjective_iff
    ((Scheme.Modules.pullback (f.fiberι s)).map sc.f)).mp ?_
  intro x₁
  have hzero : hSEpull.extClass.comp x₁ (show (1:ℕ) + 0 = 1 by norm_num) = 0 :=
    (isZero_extGroup_iff 1 _ _).mp hs _
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hSEpull
    ((Scheme.Modules.pullback (f.fiberι s)).obj F) x₁
    (show (1:ℕ) + 0 = 1 by norm_num) hzero
  exact ⟨x₂, hx₂⟩

/-- **(1.3 brick (iii) assembly, `lem:ext1_X_pushforward_fibre_vanishes`)** The
homological half of `T(k(s)) = 0`: `Ext¹_X(I, j_*j^*F) = 0` for the fibre inclusion
`j = f.fiberι s`. Feeds the contravariant chase `ext1_isZero_of_acyclic_chase` with the
acyclic SES `0 → K → J → I → 0` (`acyclic_ses`), whose `hJ` is discharged by
`acyclic_ext1_vanishes` and whose `hsurj` is assembled from `fibre_hom_surjective`
(fibre-side surjectivity), `adjunction_ladder_surjective` (transport through `j^* ⊣ j_*`),
and the `Ext⁰ ↔ Hom` bridge `ext0_precomp_surjective_iff`.

The single flatness hypothesis `hI : IsSFlat f I` (flatness of the **base term** `I`
over `S`) is the genuine AK input; it is consumed by the iter-029 anchor
`External.flat_fibre_restriction_exact` to keep the fibre-restricted sequence short exact
("since `I` is `S`-flat, the sequence remains exact when restricted to `X(s)`"),
**replacing** the iter-028 named gap `hpullflat` (the bridge `IsSFlat (j ≫ f) (j^*I)` was
shown FALSE). The quasicoherence of `W = j_*j^*F` is supplied by
`External.fibre_pushforward_qcoh` from `hFqc : F.IsQuasicoherent` (pullback then
qcqs-pushforward of a quasi-coherent), replacing the iter-028 named gap `hWqc`.
Project-local. -/
theorem ext1_X_pushforward_fibre_vanishes {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (I F : X.Modules) (hI : IsSFlat f I) (hFqc : F.IsQuasicoherent)
    (hs : FiberExtVanishes 1 f I F s) :
    IsZero (extGroup 1 I ((Scheme.Modules.pushforward (f.fiberι s)).obj
      ((Scheme.Modules.pullback (f.fiberι s)).obj F))) := by
  obtain ⟨sc, hsc, hX3, hac⟩ := acyclic_ses I
  set j := f.fiberι s with hj
  set W := (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F) with hW
  -- quasicoherence of `W = j_*j^*F` (qcqs-pushforward of a quasi-coherent pullback).
  have hWqc : W.IsQuasicoherent := External.fibre_pushforward_qcoh f s F hFqc
  -- the pulled-back SES `0 → j^*K → j^*J → j^*I → 0` stays short exact because `I` is
  -- `S`-flat (the correct flatness mechanism: flatness of the base term `I = sc.X₃`).
  have hSEpull : (sc.map (Scheme.Modules.pullback j)).ShortExact :=
    External.flat_fibre_restriction_exact f s sc hsc (by rw [hX3]; exact hI)
  -- `Ext¹_X(I, W) = 0` follows from the contravariant chase on `sc`.
  rw [← hX3]
  refine ext1_isZero_of_acyclic_chase sc hsc W ?_ ?_
  · -- `hJ`: `Ext¹_X(J, W) = 0` since `J` is acyclic.
    exact acyclic_ext1_vanishes sc.X₂ hac W hWqc
  · -- `hsurj`: precomposition `Hom_X(J, W) → Hom_X(K, W)` is surjective.
    refine (ext0_precomp_surjective_iff sc.f).mpr ?_
    refine adjunction_ladder_surjective j sc.f ((Scheme.Modules.pullback j).obj F) ?_
    exact fibre_hom_surjective f s sc F hSEpull (by rw [hX3]; exact hs)

/-- **(`lem:functorT_residue_eq_zero`, the residue value `T(k(s)) = 0`)** For `A`
Noetherian local with closed point `s` and residue field `k = k(s)`, `f : X ⟶ Spec A`,
and `I, F : X.Modules` with `I` `S`-flat (`hI`), `F` quasi-coherent (`hFqc`), and the
fibre `Ext`-vanishing `Ext¹_{X(s)}(I(s), F(s)) = 0` (`hs`), the value of `T = functorT A
f I F` on the residue field is zero: `(functorT A f I F).obj k~ = 0`. This is exactly the
`hk` hypothesis of `functorT_eq_zero_of_residue`; composing the two yields `T(M) = 0` for
every finitely generated `A`-module `M` — the homological heart of (1.3) at `S = Spec A`.

Route: `functorT_obj_isZero_iff` reduces the claim to `extGroup 1 I (F ⊗_S k~) = 0`; the
fibre identification `External.fibre_tensor_residue_iso` (`j_*j^*F ≅ F ⊗_S k~`) transports
it — via `isZero_extGroup_of_iso_right` in the second `Ext` argument — to
`extGroup 1 I (j_*j^*F) = 0`, which is `ext1_X_pushforward_fibre_vanishes` (using `hI`,
`hFqc`, `hs`). Project-local. -/
lemma functorT_residue_eq_zero {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (hI : IsSFlat f I) (hFqc : F.IsQuasicoherent)
    (hs : FiberExtVanishes 1 f I F (IsLocalRing.closedPoint ↑A)) :
    IsZero ((functorT A f I F).obj (ModuleCat.of ↑A (IsLocalRing.ResidueField ↑A))) := by
  rw [functorT_obj_isZero_iff]
  exact isZero_extGroup_of_iso_right 1 I (External.fibre_tensor_residue_iso A f F)
    (ext1_X_pushforward_fibre_vanishes f (IsLocalRing.closedPoint ↑A) I F hI hFqc hs)

/-- **(`lem:functorT_eq_zero`, the homological heart of (1.3) at `S = Spec A`)** For `A`
Noetherian local with closed point `s`, `f : X ⟶ Spec A`, and `I, F : X.Modules` with `I`
and `F` `S`-flat, `F` quasi-coherent, and the fibre `Ext`-vanishing
`Ext¹_{X(s)}(I(s), F(s)) = 0`, the functor `T = functorT A f I F` vanishes on **every**
finitely generated `A`-module `M`: `(functorT A f I F).obj M = 0`.

This composes the residue value `functorT_residue_eq_zero` (`T(k(s)) = 0`, the `hk`
input) with `functorT_eq_zero_of_residue` (half-exactness + OB 2.1 upgrade `T(k) = 0 ⟹
T(M) = 0 ∀M`). It is the full homological conclusion of the (1.3) argument *after*
reduction to the affine-Noetherian-local base — the input to the free conclusion (brick 6:
`M ↦ Hom_X(I, F ⊗_S M~)` exact ⟹ `H` free at `s`). Project-local. -/
lemma functorT_eq_zero {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (hI : IsSFlat f I) (hF : IsSFlat f F) (hFqc : F.IsQuasicoherent)
    (hs : FiberExtVanishes 1 f I F (IsLocalRing.closedPoint ↑A))
    (M : ModuleCat.{u} ↑A) : IsZero ((functorT A f I F).obj M) :=
  functorT_eq_zero_of_residue A f I F hF (functorT_residue_eq_zero A f I F hI hFqc hs) M

/-! ### Brick 6 of (1.3): free conclusion + EGA reduction

From the homological heart `T(M) = 0` (`functorT_eq_zero`) to local freeness of the
representing module `H`. The free conclusion at `S = Spec A` (Noetherian local) is
**built** below (`homTensorFunctor_tilde_exact` ⟹ `H_free_of_functorT_zero`, with the
commutative-algebra endpoint `Module.free_of_flat_of_isLocalRing` supplied by Mathlib);
the EGA reduction from a general base `S` to `Spec A` is **anchored** (it transports `H`
along base change, requiring the base-change compatibility `H_tensor` which is paused).
-/

/-- **[EGA III₂, 7.7.6]** Local finite presentation (coherence) of the representing
module `H(I,F)` over a Noetherian base. Used in the (1.3) free conclusion (affine
bridge `H ≅ Γ(H)~`) and in the EGA `O_I 5.4.1` free-at-a-point criterion. Absent from
Mathlib; small EGA anchor. See `thm:ega_H_isLFP`. -/
axiom External.H_isLFP {X S : Scheme.{u}} (f : X ⟶ S) (I F : X.Modules)
    (ha : Admissible f I F) : IsLFP (H f I F ha)

/-- **[EGA O_I, 5.4.1, 2.4.1]** A locally finitely presented `𝒪_S`-module that is free
at a point `s` (its pullback along some open neighbourhood `V ∋ s` is a free sheaf) is
locally free of finite rank on an open, retrocompact neighbourhood of `s`. Standard EGA;
no §1 content. See `thm:ega_lfp_free_at_point`. -/
axiom External.lfp_free_at_point_locallyFree {S : Scheme.{u}} (M : S.Modules)
    (hM : IsLFP M) (s : S)
    (hfree : ∃ V : S.Opens, s ∈ V ∧ IsFreeMod ((Scheme.Modules.pullback V.ι).obj M)) :
    ∃ U : S.Opens, s ∈ U ∧ IsRetrocompact U ∧ IsLocallyFreeOfFiniteRankOn M U

/-- **[EGA IV₃, §8; AK §1 (1.3) p. 56]** The EGA reduction step of (1.3): the assertion
is local on `S`, descent to a Noetherian base together with the base-change compatibility
of `H` ((1.1)) reduces to `S = Spec A` with `A` Noetherian local and `s` the closed point.
Given that the representing module is **free at the closed point** for every such reduced
datum (the §1 output `H_free_of_functorT_zero`, supplied as the premise `hfree`), it
produces the open, retrocompact neighbourhood on which `H(I,F)` is locally free of finite
rank. Anchored: it transports `H` along base change, requiring the (paused) base-change
compatibility of `H`. It carries NO §1 content. See `thm:ega_reduce_H_locallyFree`. -/
axiom External.reduce_H_locallyFree_to_spec_local {X S : Scheme.{u}} (f : X ⟶ S)
    (I F : X.Modules) (ha : Admissible f I F) (hI : IsSFlat f I) (s : S)
    (hs : FiberExtVanishes 1 f I F s)
    (hfree : ∀ {X' : Scheme.{u}} (A : CommRingCat.{u}) [IsNoetherianRing ↑A] [IsLocalRing ↑A]
      (f' : X' ⟶ Spec A) (I' F' : X'.Modules) (ha' : Admissible f' I' F'),
      IsSFlat f' I' →
      FiberExtVanishes 1 f' I' F' (IsLocalRing.closedPoint ↑A) →
      IsFreeMod (H f' I' F' ha')) :
    ∃ U : S.Opens, s ∈ U ∧ IsRetrocompact U ∧
      IsLocallyFreeOfFiniteRankOn (H f I F ha) U

/-- **(`lem:homTensorFunctor_tilde_exact`)** From the homological heart `T = 0`
(`functorT_eq_zero`): the functor `M ↦ Hom_X(I, F ⊗_S M~)` on f.g. `A`-modules is right
exact. Concretely, for a short exact sequence `sc` of `A`-modules the map
`(homTensorFunctor f I F).map (tilde sc.g) : Hom_X(I, F ⊗_S sc.X₂~) → Hom_X(I, F ⊗_S sc.X₃~)`
(postcomposition with `F ⊗_S tilde(sc.g)`) is surjective.

Route: `tilde_exact` + `External.flat_tensor_exact` (`F` `S`-flat) give a short exact
sequence `0 → F⊗sc.X₁~ → F⊗sc.X₂~ → F⊗sc.X₃~ → 0` of `𝒪_X`-modules; the covariant `Ext`
LES `Abelian.Ext.covariant_sequence_exact₃` lifts every degree-0 class on `F⊗sc.X₃~` whose
image under the connecting map to `Ext¹_X(I, F⊗sc.X₁~)` vanishes — and that target is
`(functorT A f I F).obj sc.X₁ = 0` by `functorT_eq_zero`, so every class lifts. The
degree-0 Ext bijection `Ext.mk₀_bijective` + `Ext.mk₀_comp_mk₀` translate this into the
Hom-set surjectivity. Project-local. -/
theorem homTensorFunctor_tilde_exact {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (hI : IsSFlat f I) (hF : IsSFlat f F) (hFqc : F.IsQuasicoherent)
    (hs : FiberExtVanishes 1 f I F (IsLocalRing.closedPoint ↑A))
    (sc : ShortComplex (ModuleCat.{u} ↑A)) (hsc : sc.ShortExact) :
    Function.Surjective
      ((homTensorFunctor f I F).map ((AlgebraicGeometry.tilde.functor A).map sc.g)) := by
  letI : HasDerivedCategory X.Modules := HasDerivedCategory.standard X.Modules
  haveI := CategoryTheory.hasExt_of_hasDerivedCategory X.Modules
  haveI : (AlgebraicGeometry.tilde.functor A).PreservesZeroMorphisms := inferInstance
  -- The base-changed short exact sequence of `𝒪_X`-modules.
  have hSEtilde : (sc.map (AlgebraicGeometry.tilde.functor A)).ShortExact := tilde_exact sc hsc
  set scT := (sc.map (AlgebraicGeometry.tilde.functor A)).map (tensorBaseChangeFunctor f F)
    with hscT
  have hSEX : scT.ShortExact :=
    External.flat_tensor_exact f F hF (sc.map (AlgebraicGeometry.tilde.functor A)) hSEtilde
  -- `Ext¹_X(I, scT.X₁) = 0` is the value of `T` on `sc.X₁`.
  have hzero : Subsingleton (CategoryTheory.Abelian.Ext I scT.X₁ 1) := by
    have h0 : IsZero (extGroup 1 I ((tensorBaseChangeFunctor f F).obj
        (AlgebraicGeometry.tilde sc.X₁))) :=
      (functorT_obj_isZero_iff A f I F sc.X₁).mp
        (functorT_eq_zero A f I F hI hF hFqc hs sc.X₁)
    rw [extGroup, AddCommGrpCat.isZero_iff_subsingleton] at h0
    exact h0
  -- Surjectivity via the covariant `Ext` long exact sequence in degree 0.
  intro ψ
  -- `ψ : I ⟶ scT.X₃`.
  have hx₃ : (CategoryTheory.Abelian.Ext.mk₀ ψ).comp hSEX.extClass (zero_add 1) = 0 :=
    hzero.elim _ _
  obtain ⟨x₂, hx₂⟩ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₃ I hSEX
      (CategoryTheory.Abelian.Ext.mk₀ ψ) (zero_add 1) hx₃
  obtain ⟨φ, hφ⟩ := (CategoryTheory.Abelian.Ext.mk₀_bijective I scT.X₂).surjective x₂
  refine ⟨φ, ?_⟩
  have key : CategoryTheory.Abelian.Ext.mk₀ (φ ≫ scT.g) = CategoryTheory.Abelian.Ext.mk₀ ψ := by
    rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hφ]; exact hx₂
  exact (CategoryTheory.Abelian.Ext.mk₀_bijective I scT.X₃).injective key

/-- A natural isomorphism of `Type`-valued functors transports surjectivity of the action
on a morphism: if `G.map φ` is surjective and `α : F ≅ G`, then `F.map φ` is surjective.
Project-local helper isolating the `Type`-category bookkeeping for the (1.3) free
conclusion transport (`coyoneda(H) ≅ homTensorFunctor`). -/
private lemma surjective_of_natIso_map {C : Type u'} [CategoryTheory.Category.{v'} C]
    {F G : CategoryTheory.Functor C (Type w)} (α : F ≅ G) {Y Z : C} (φ : Y ⟶ Z)
    (h : Function.Surjective (G.map φ)) : Function.Surjective (F.map φ) := by
  intro y
  obtain ⟨x, hx⟩ := h (CategoryTheory.ConcreteCategory.hom (α.hom.app Z) y)
  refine ⟨CategoryTheory.ConcreteCategory.hom (α.inv.app Y) x, ?_⟩
  have h1 := CategoryTheory.NatTrans.naturality_apply α.inv φ x
  rw [← h1, hx, ← CategoryTheory.ConcreteCategory.comp_apply, α.hom_inv_id_app,
    CategoryTheory.ConcreteCategory.id_apply]

/-- **(transport core of `thm:H_free_of_functorT_zero`)** Given the representing module
`H(I,F) ≅ Ñ` over `Spec A`, the right-exactness of `M ↦ Hom_X(I, F ⊗_S M~)`
(`homTensorFunctor_tilde_exact`) transports — through the representability iso
`H_represents`, the iso `e : Ñ ≅ H`, and full faithfulness of `tilde` — to right
exactness of `M ↦ Hom_A(N, M)`: for any short exact sequence `sc` of `A`-modules,
postcomposition `(N ⟶ sc.X₂) → (N ⟶ sc.X₃)` with `sc.g` is surjective. Project-local. -/
private theorem hom_postcomp_surjective_of_functorT_zero {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (ha : Admissible f I F) (hI : IsSFlat f I) (hF : IsSFlat f F) (hFqc : F.IsQuasicoherent)
    (hs : FiberExtVanishes 1 f I F (IsLocalRing.closedPoint ↑A))
    (N : ModuleCat.{u} ↑A) (e : (AlgebraicGeometry.tilde.functor A).obj N ≅ H f I F ha)
    (sc : ShortComplex (ModuleCat.{u} ↑A)) (hsc : sc.ShortExact) :
    Function.Surjective (fun φ : N ⟶ sc.X₂ => φ ≫ sc.g) := by
  obtain ⟨α⟩ := H_represents f I F ha
  -- Step 2: transport STEP B through the representability iso `α`, whiskered by `tilde`.
  have s2 : Function.Surjective
      ((AlgebraicGeometry.tilde.functor A ⋙ coyoneda.obj (op (H f I F ha))).map sc.g) :=
    surjective_of_natIso_map
      (CategoryTheory.Functor.isoWhiskerLeft (AlgebraicGeometry.tilde.functor A) α)
      sc.g (homTensorFunctor_tilde_exact A f I F hI hF hFqc hs sc hsc)
  -- Step 3: transport through `e : Ñ ≅ H` (coyoneda is contravariant in the object).
  have s3 : Function.Surjective
      ((AlgebraicGeometry.tilde.functor A ⋙
        coyoneda.obj (op ((AlgebraicGeometry.tilde.functor A).obj N))).map sc.g) :=
    surjective_of_natIso_map (CategoryTheory.Functor.isoWhiskerLeft
      (AlgebraicGeometry.tilde.functor A) (coyoneda.mapIso e.op).symm) sc.g s2
  -- Step 4: descend through full faithfulness of `tilde`.
  intro φ'
  obtain ⟨ρ, hρ⟩ := s3 ((AlgebraicGeometry.tilde.functor A).map φ')
  set FF := AlgebraicGeometry.tilde.fullyFaithfulFunctor (R := A) with hFF
  refine ⟨FF.preimage ρ, ?_⟩
  apply (AlgebraicGeometry.tilde.functor A).map_injective
  rw [CategoryTheory.Functor.map_comp, FF.map_preimage]
  exact hρ

/-- **(`thm:H_free_of_functorT_zero`)** For `A` Noetherian local, `f : X ⟶ Spec A`
admissible, `I` `S`-flat, and the fibre `Ext`-vanishing at the closed point, the
representing module `H(I,F)` is a free `𝒪_{Spec A}`-module.

Route: `homTensorFunctor_tilde_exact` (the homological heart `T = 0`) makes
`M ↦ Hom_X(I, F ⊗_S M~)` right exact; `hom_postcomp_surjective_of_functorT_zero`
transports this through representability and the affine bridge `H ≅ Ñ` to right
exactness of `M ↦ Hom_A(N, M)`, i.e. a finite free cover `Aⁿ ↠ N` splits, so `N` is
projective; `Module.Flat.of_projective` + `Module.free_of_flat_of_isLocalRing` make `N`
free; tilde-ing a basis gives `H ≅ Ñ ≅` a free sheaf. Project-local. -/
theorem H_free_of_functorT_zero {X : Scheme.{u}} (A : CommRingCat.{u})
    [IsNoetherianRing ↑A] [IsLocalRing ↑A] (f : X ⟶ Spec A) (I F : X.Modules)
    (ha : Admissible f I F) (hI : IsSFlat f I)
    (hs : FiberExtVanishes 1 f I F (IsLocalRing.closedPoint ↑A)) :
    IsFreeMod (H f I F ha) := by
  have hF : IsSFlat f F := ha.flat_F
  haveI hFfp : F.IsFinitePresentation := ha.lfp_F
  have hFqc : F.IsQuasicoherent := inferInstance
  haveI hHfp : (H f I F ha).IsFinitePresentation := External.H_isLFP f I F ha
  obtain ⟨N, hNfp, ⟨eHN⟩⟩ := External.affine_fp_tilde (H f I F ha)
  haveI : Module.FinitePresentation ↑A ↑N := hNfp
  haveI : Module.Finite ↑A ↑N := inferInstance
  -- `N` is projective: a finite free cover `Aⁿ ↠ N` splits by the transported right
  -- exactness.
  haveI hNproj : Module.Projective ↑A ↑N := by
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' ↑A ↑N
    set pm : ModuleCat.of ↑A (Fin n → ↑A) ⟶ N := ModuleCat.ofHom p with hpm
    haveI : Epi pm := by
      rw [ModuleCat.epi_iff_surjective]; simpa [hpm] using hp
    have hSES : (ShortComplex.mk (CategoryTheory.Limits.kernel.ι pm) pm
        (CategoryTheory.Limits.kernel.condition pm)).ShortExact :=
      ShortComplex.ShortExact.mk (ShortComplex.exact_kernel pm)
    obtain ⟨s, hsv⟩ := hom_postcomp_surjective_of_functorT_zero A f I F ha hI hF hFqc hs N eHN
      (ShortComplex.mk (CategoryTheory.Limits.kernel.ι pm) pm
        (CategoryTheory.Limits.kernel.condition pm)) hSES (𝟙 N)
    refine (Module.Projective.iff_split_of_projective p hp).mpr ⟨s.hom, ?_⟩
    have h := hsv
    apply_fun ModuleCat.Hom.hom at h
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id, hpm, ModuleCat.hom_ofHom] using h
  haveI : Module.Flat ↑A ↑N := Module.Flat.of_projective
  haveI : Module.Free ↑A ↑N := Module.free_of_flat_of_isLocalRing
  -- `N` free of finite rank ⟹ `Ñ` (hence `H`) is a free sheaf.
  haveI : Finite (Module.Free.ChooseBasisIndex ↑A ↑N) := inferInstance
  obtain ⟨Λ', ⟨gfree⟩⟩ := tilde_free (R := A) (Module.Free.ChooseBasisIndex ↑A ↑N)
  refine ⟨Λ', ⟨eHN.symm ≪≫ (AlgebraicGeometry.tilde.functor A).mapIso
    (LinearEquiv.toModuleIso (Module.Free.chooseBasis ↑A ↑N).repr) ≪≫ gfree⟩⟩

/-- **(1.3)** Local freeness of `H(I,F)`: if `Ext^1_{X(s)}(I(s),F(s)) = 0` for some
`s ∈ S` (with `I` `S`-flat, as `Admissible` carries only flatness of `F`), then `H(I,F)`
is locally free of finite rank on an open, retrocompact neighbourhood of `s`.

Assembly: the EGA reduction `External.reduce_H_locallyFree_to_spec_local` reduces to the
Noetherian-local affine case, whose §1 output — freeness of `H` at the closed point — is
the built `H_free_of_functorT_zero`. See `thm:H_locallyFree`. -/
theorem H_locallyFree_of_ext_vanishing (f : X ⟶ S) (I F : X.Modules)
    (ha : Admissible f I F) (hI : IsSFlat f I) (s : S) (hs : FiberExtVanishes 1 f I F s) :
    ∃ U : S.Opens, s ∈ U ∧ IsRetrocompact U ∧
      IsLocallyFreeOfFiniteRankOn (H f I F ha) U :=
  External.reduce_H_locallyFree_to_spec_local f I F ha hI s hs
    (by intro X' A inst1 inst2 f' I' F' ha' hI' hs'
        exact @H_free_of_functorT_zero X' A inst1 inst2 f' I' F' ha' hI' hs')

end MR0555258CompactifyingPicard
