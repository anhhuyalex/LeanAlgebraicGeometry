/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Cohomology.PresheafCech
import AlgebraicJacobian.Cohomology.FreePresheafComplex

/-!
# Form-B absolute cohomology `H^p(U, F) := Ext^p(jShriekOU U, F)` (P5b input)
-/

universe u

open CategoryTheory Limits CategoryTheory.Abelian

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The standard `HasExt` structure on `X.Modules`, made a section-local instance so the
`Ext`-based absolute cohomology below resolves it without the slow `HasSmallLocalizedHom`
typeclass search. -/
noncomputable local instance hasExtModules : HasExt.{u + 1, u, u + 1} X.Modules :=
  HasExt.standard _

/-! ## Project-local Mathlib supplement — Form-B absolute cohomology -/

noncomputable def jShriekOU (U : TopologicalSpace.Opens X) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))

/-- The sheafification adjunction hom-bijection as an `AddEquiv` (additivity holds because
the right adjoint is an additive functor and composition is bilinear). -/
noncomputable def sheafificationHomAddEquiv (U : TopologicalSpace.Opens X) (F : X.Modules) :
    (jShriekOU U ⟶ F) ≃+
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U) ⟶
        (Scheme.Modules.toPresheafOfModules X).obj F) :=
  { (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)) F with
    map_add' := by
      intro f g
      haveI : (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).Additive := inferInstance
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit]
      erw [Functor.map_add, Preadditive.comp_add]
      rfl }

noncomputable def jShriekOU_homEquiv (U : TopologicalSpace.Opens X) (F : X.Modules) :
    (jShriekOU U ⟶ F) ≃+
      ((Scheme.Modules.toPresheafOfModules X).obj F).presheaf.obj (Opposite.op U) :=
  (sheafificationHomAddEquiv U F).trans (freeYonedaHomAddEquiv U _)

/-- **Form-B absolute cohomology** `H^p(U, F) := Ext^p_{O_X}(jShriekOU U, F)`. -/
noncomputable def absoluteCohomology (p : ℕ) (U : TopologicalSpace.Opens X)
    (F : X.Modules) : AddCommGrpCat :=
  AddCommGrpCat.of (Ext (jShriekOU U) F p)

/-- **`H⁰(U, F) ≅ Γ(U, F)`** as abelian groups: degree-zero `Ext` out of the
corepresenting object `jShriekOU U` recovers the sections of `F` over `U`. This is the
additive corepresentability of global sections specialised to `p = 0`. -/
noncomputable def absoluteCohomologyZeroAddEquiv (U : TopologicalSpace.Opens X)
    (F : X.Modules) :
    Ext (jShriekOU U) F 0 ≃+
      ((Scheme.Modules.toPresheafOfModules X).obj F).presheaf.obj (Opposite.op U) :=
  (AddEquiv.mk' Ext.homEquiv₀ (by
    intro a b
    refine Ext.homEquiv₀.symm.injective ?_
    simp only [Ext.homEquiv₀_symm_apply, Ext.mk₀_add, Ext.mk₀_homEquiv₀_apply])).trans
    (jShriekOU_homEquiv U F)

/-- **Injective vanishing**: positive-degree absolute cohomology of an injective sheaf of
modules vanishes. Direct from `Ext.eq_zero_of_injective` (the injective object is the
*second* `Ext` argument, so no restriction of the coefficient sheaf is needed). -/
theorem absoluteCohomology_eq_zero_of_injective (n : ℕ) (U : TopologicalSpace.Opens X)
    (I : X.Modules) [Injective I] (e : Ext (jShriekOU U) I (n + 1)) : e = 0 :=
  Ext.eq_zero_of_injective e

/-- **Covariant `H^p(U,-)` long exact sequence, surjectivity at `H^{n₁}(U, F₁)`.**
Thin wrapper around `Ext.covariant_sequence_exact₁` at fixed first argument
`jShriekOU U`, for a short exact sequence of `O_X`-modules. -/
theorem absoluteCohomology_covariant_exact₁ (U : TopologicalSpace.Opens X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) {n₁ : ℕ}
    (x₁ : Ext (jShriekOU U) S.X₁ n₁) (hx₁ : x₁.comp (Ext.mk₀ S.f) (add_zero n₁) = 0)
    {n₀ : ℕ} (hn₀ : n₀ + 1 = n₁) :
    ∃ x₃ : Ext (jShriekOU U) S.X₃ n₀, x₃.comp hS.extClass hn₀ = x₁ :=
  Ext.covariant_sequence_exact₁ (jShriekOU U) hS x₁ hx₁ hn₀

/-- **Covariant `H^p(U,-)` long exact sequence, exactness at `H^n(U, F₂)`.**
Thin wrapper around `Ext.covariant_sequence_exact₂` at fixed first argument
`jShriekOU U`. -/
theorem absoluteCohomology_covariant_exact₂ (U : TopologicalSpace.Opens X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) {n : ℕ}
    (x₂ : Ext (jShriekOU U) S.X₂ n) (hx₂ : x₂.comp (Ext.mk₀ S.g) (add_zero n) = 0) :
    ∃ x₁ : Ext (jShriekOU U) S.X₁ n, x₁.comp (Ext.mk₀ S.f) (add_zero n) = x₂ :=
  Ext.covariant_sequence_exact₂ (jShriekOU U) hS x₂ hx₂

/-- **Covariant `H^p(U,-)` long exact sequence, exactness at the connecting map.**
Thin wrapper around `Ext.covariant_sequence_exact₃` at fixed first argument
`jShriekOU U`. -/
theorem absoluteCohomology_covariant_exact₃ (U : TopologicalSpace.Opens X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) {n₀ : ℕ}
    (x₃ : Ext (jShriekOU U) S.X₃ n₀) {n₁ : ℕ} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    ∃ x₂ : Ext (jShriekOU U) S.X₂ n₀, x₂.comp (Ext.mk₀ S.g) (add_zero n₀) = x₃ :=
  Ext.covariant_sequence_exact₃ (jShriekOU U) hS x₃ hn₁ hx₃

/-! ## Project-local Mathlib supplement — naturality of `H⁰ ≅ Γ` -/

/-- **Naturality of `Ext.homEquiv₀` in the second argument.** The degree-zero `Ext`
comparison intertwines composition with the degree-zero Ext class `Ext.mk₀ g` and ordinary
post-composition with `g`. Project-local: Mathlib has the comparison `Ext.homEquiv₀` and the
composite formula `Ext.mk₀_comp_mk₀`, but not this intertwining as a packaged lemma. -/
private lemma homEquiv₀_comp_mk₀ {A B Z : X.Modules} (e : Ext A B 0) (g : B ⟶ Z) :
    Ext.homEquiv₀ (e.comp (Ext.mk₀ g) (add_zero 0)) = Ext.homEquiv₀ e ≫ g := by
  conv_lhs => rw [← Ext.mk₀_homEquiv₀_apply e, Ext.mk₀_comp_mk₀]
  rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]

/-- **Naturality of `freeYonedaHomEquiv` in the coefficient presheaf.** Post-composition by a
morphism of presheaves of modules `q` corresponds, under the free–Yoneda evaluation bijection,
to applying `q` on sections over `V`. Project-local: the underlying bijection is project-local
(`freeYonedaHomEquiv`), so is its naturality. -/
private lemma freeYonedaHomEquiv_naturality (V : TopologicalSpace.Opens X)
    {F₁ F₂ : X.PresheafOfModules}
    (ψ : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⟶ F₁) (q : F₁ ⟶ F₂) :
    freeYonedaHomEquiv V F₂ (ψ ≫ q)
      = (ConcreteCategory.hom (q.app (Opposite.op V))) (freeYonedaHomEquiv V F₁ ψ) := by
  rw [freeYonedaHomEquiv_apply, freeYonedaHomEquiv_apply, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]

/-- **Naturality of `sheafificationHomAddEquiv` in the coefficient sheaf.** This is the
naturality of the sheafification adjunction's hom-bijection in its right (codomain) argument;
the right adjoint is `Scheme.Modules.toPresheafOfModules X` (definitionally the forget–restrict
composite). Project-local because `sheafificationHomAddEquiv` is the project's additive
packaging of that bijection. -/
private lemma sheafificationHomAddEquiv_naturality (U : TopologicalSpace.Opens X)
    {F₁ F₂ : X.Modules} (h : jShriekOU U ⟶ F₁) (g : F₁ ⟶ F₂) :
    sheafificationHomAddEquiv U F₂ (h ≫ g)
      = sheafificationHomAddEquiv U F₁ h ≫ (Scheme.Modules.toPresheafOfModules X).map g :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right h g

/-- **Naturality of `jShriekOU_homEquiv` in the coefficient sheaf.** Composing a map
`jShriekOU U ⟶ F₁` with `g : F₁ ⟶ F₂` corresponds, under corepresentability, to applying `g` on
sections over `U`. Project-local: assembled from the naturality of the two project-local halves
(`sheafificationHomAddEquiv` and `freeYonedaHomEquiv`). -/
private lemma jShriekOU_homEquiv_naturality (U : TopologicalSpace.Opens X)
    {F₁ F₂ : X.Modules} (h : jShriekOU U ⟶ F₁) (g : F₁ ⟶ F₂) :
    jShriekOU_homEquiv U F₂ (h ≫ g)
      = (ConcreteCategory.hom (((Scheme.Modules.toPresheafOfModules X).map g).app (Opposite.op U)))
          (jShriekOU_homEquiv U F₁ h) := by
  change freeYonedaHomEquiv U _ (sheafificationHomAddEquiv U F₂ (h ≫ g)) = _
  rw [sheafificationHomAddEquiv_naturality, freeYonedaHomEquiv_naturality]
  rfl

/-- **Naturality of `H⁰(U,-) ≅ Γ(U,-)` in the coefficient sheaf**
(blueprint `lem:absolute_cohomology_zero_natural`). For `g : F₁ ⟶ F₂` in `X.Modules`, the
functorial action of `g` on `Ext⁰(jShriekOU U, -)` (composition with the degree-zero Ext class
`Ext.mk₀ g`) corresponds under the `H⁰ ≅ Γ` isomorphism to the sections map `g_U` over `U`.
In particular, when `g_U` is surjective so is `H⁰(U, g)` — the transfer used by the
surjectivity step of `lem:absolute_cohomology_one_vanishing`. -/
theorem absoluteCohomologyZeroAddEquiv_naturality (U : TopologicalSpace.Opens X)
    {F₁ F₂ : X.Modules} (g : F₁ ⟶ F₂) (e : Ext (jShriekOU U) F₁ 0) :
    absoluteCohomologyZeroAddEquiv U F₂ (e.comp (Ext.mk₀ g) (add_zero 0))
      = (ConcreteCategory.hom (((Scheme.Modules.toPresheafOfModules X).map g).app (Opposite.op U)))
          (absoluteCohomologyZeroAddEquiv U F₁ e) := by
  change jShriekOU_homEquiv U F₂ (Ext.homEquiv₀ (e.comp (Ext.mk₀ g) (add_zero 0))) = _
  rw [homEquiv₀_comp_mk₀, jShriekOU_homEquiv_naturality]
  rfl

end AlgebraicGeometry
