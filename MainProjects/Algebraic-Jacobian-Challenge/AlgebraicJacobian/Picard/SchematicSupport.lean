/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.PullbackFinitePresentation
import AlgebraicJacobian.Picard.TensorSectionFormula

/-!
# Algebraic bricks for the Γ-fibre base-change over a residue field extension

This leaf file collects the two *field/algebra-level* building blocks feeding the
proof of `AlgebraicGeometry.Scheme.gammaFiber_finrank_baseChange_field`
(`Picard/QuotFunctorDef.lean`, blueprint `lem:gamma_fiber_baseChange_field`), the
flat-base-change core of the fibrewise Hilbert-function invariance
(`Scheme.hilbertFunction_quotBaseMap`, Nitsure §1 / Stacks 02KH at `i = 0`).

* `AlgebraicGeometry.annihilator_le_annihilator_tensorProduct` /
  `annihilator_le_annihilator_tensorProduct_right` — annihilator monotonicity
  under tensoring: `Ann_R M ⊆ Ann_R (M ⊗[R] N)` (and the symmetric statement).
  This is the *sections-level* algebraic content behind the "the support of the
  twist `F ⊗ L^{⊗m}` is contained in the support of `F`" step (attack-plan
  brick (3)): on an affine open the section module of a twist of quasi-coherent
  sheaves is a tensor product of the section modules, and any scalar killing
  `Γ(F, U)` kills every elementary tensor, hence the whole tensor product;
  monotonicity of `Scheme.IdealSheafData.ofIdeals` (`ofIdeals_mono`) then
  propagates the inclusion to the annihilator ideal sheaves
  (`Scheme.Modules.annihilator`) and hence to the schematic supports, giving
  properness of the twisted fibre support from properness of the support of `F`.

* `AlgebraicGeometry.finrank_eq_of_baseChange_linearEquiv` — the dimension
  transport packaging: a `κ'`-linear equivalence `κ' ⊗[κ] V ≃ₗ[κ'] W` forces
  `dim_{κ'} W = dim_{κ} V` (`Module.finrank_baseChange`).  This is the final step
  (attack-plan step (5)): flat base change over the residue field extension
  `κ(t) → κ(t')` produces exactly such an equivalence for `V = Γ(Z, N)` and
  `W = Γ(Z', v^*N)` (`Z` the proper support of the twisted fibre module, `v` the
  base change of `Z` along `Spec κ(t') → Spec κ(t)`), and the equivalence forces
  the finrank equality *unconditionally* — no finiteness case-split is needed,
  since both sides are `Module.finrank` (junk value `0` in the infinite case) and
  the equivalence identifies those junk values too.

Both are universe-monomorphic pure algebra and are axiom-clean
(`propext, Classical.choice, Quot.sound`).

On top of the algebra bricks, the file now also delivers the **scheme-level
support-descent brick** itself (wave 8): for a quasi-coherent `F` on `Y` and any
ideal sheaf `I` with `I(U) ⊆ Ann Γ(F, U)` on affines, the unit
`F ⟶ i_* i^* F` of the pullback–pushforward adjunction along the closed
immersion `i : V(I) ↪ Y` is an isomorphism
(`Scheme.Modules.isIso_unit_subschemeι_of_le_annihilator`); instantiated at the
annihilator ideal sheaf `I := Ann F` this realizes `F ≅ i_* N` with
`N := i^* F` on the schematic support
(`Scheme.Modules.schematicSupportDescentIso`), the geometric half of the
`lem:gamma_fiber_baseChange_field` reduction, with `N` finitely presented when
`F` is (`Scheme.Modules.isFinitePresentation_pullback_schematicSupportι`).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry

open scoped TensorProduct

/-- **Annihilator monotonicity under tensoring (left factor)**: any scalar that
annihilates `M` annihilates `M ⊗[R] N`.  A scalar `a ∈ Ann_R M` kills every
elementary tensor via `a • (m ⊗ n) = (a • m) ⊗ n = 0`, hence the whole tensor
product by `TensorProduct.induction_on`.

This is the sections-level input to the schematic-support monotonicity
`schematicSupport (F ⊗ G) ⊆ schematicSupport F` behind the twisted-fibre proper
support reduction of `lem:gamma_fiber_baseChange_field`. -/
theorem annihilator_le_annihilator_tensorProduct
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.annihilator R M ≤ Module.annihilator R (M ⊗[R] N) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul m n => rw [TensorProduct.smul_tmul', ha m, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- **Annihilator monotonicity under tensoring (right factor)**: any scalar that
annihilates `N` annihilates `M ⊗[R] N`.  Symmetric companion of
`annihilator_le_annihilator_tensorProduct`. -/
theorem annihilator_le_annihilator_tensorProduct_right
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.annihilator R N ≤ Module.annihilator R (M ⊗[R] N) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul m n => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, ha n,
      TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- **Dimension transport across a base-change linear equivalence**: a
`k'`-linear equivalence between the base change `k' ⊗[k] V` of a `k`-vector space
`V` and a `k'`-vector space `W` forces `dim_{k'} W = dim_{k} V`.

Over fields the base-change identity `Module.finrank_baseChange`
(`finrank_{k'} (k' ⊗[k] V) = finrank_k V`) holds unconditionally, and the
equivalence transports finrank (`LinearEquiv.finrank_eq`).  This is the terminal
packaging of `lem:gamma_fiber_baseChange_field`: flat base change over the
residue field extension supplies the equivalence `e`, and the finrank equality
follows with **no** finiteness case-split (both sides are `Module.finrank`, whose
junk value `0` in the infinite-dimensional case is identified by `e` as well). -/
theorem finrank_eq_of_baseChange_linearEquiv
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    {V : Type*} [AddCommGroup V] [Module k V]
    {W : Type*} [AddCommGroup W] [Module k' W]
    (e : (k' ⊗[k] V) ≃ₗ[k'] W) :
    Module.finrank k' W = Module.finrank k V := by
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-! ## The affine-local heart of the support descent

On an affine open `U` of the fibre `X_t`, the section module `M = Γ(F, U)` over
the coordinate ring `R = Γ(X, U)` carries the *annihilator ideal*
`I = Ann_R M`.  By construction `I` kills `M`, so `M` is a module over the
quotient `R ⧸ I` (`Module.quotientAnnihilator`), and this is precisely the
statement that `F|_U` descends to the closed subscheme `V(I) = Spec (R ⧸ I)`
cut out by the annihilator — the schematic support.  The two algebraic facts
the descent needs at this affine level are packaged below:

* `module_finite_quotientAnnihilator` — the *coherence descent*: the descended
  module `M`, viewed over `R ⧸ I`, is still finitely generated.  This is the
  affine content of "`N` is finitely presented on `Z`" in the brick
  `F ≅ i_* N` (over the residue field `κ(t)` the fibre is Noetherian, so finite
  generation is finite presentation).  Assembled from
  `Module.quotientAnnihilator` (the `R ⧸ I`-action), the induced scalar tower
  `R → R ⧸ I → M` (`Module.IsTorsionBySet.isScalarTower`), and
  `Module.Finite.of_restrictScalars_finite` (a finite generating set over `R` is
  a finite generating set over the quotient, along which the action factors).

* `annihilator_quotientAnnihilator_eq_bot` — the *sharpness* of the schematic
  support: over `R ⧸ I` the module `M` is faithful, `Ann_{R⧸I} M = ⊥`.  Any
  `q = mk r` killing `M` has `r • m = mk r • m = 0` for all `m`, so `r ∈ I` and
  `q = 0`.  Equivalently (`Module.annihilator_eq_bot`) `FaithfulSMul (R ⧸ I) M`:
  the closed subscheme `V(I)` is the *smallest* on which `F|_U` lives, i.e.
  `V(Ann_R M)` is the honest schematic support and carries no embedded
  thickening.

Both are universe-monomorphic pure algebra and axiom-clean. -/

/-- **Coherence descent to the schematic support (affine heart)**: a finitely
generated `R`-module `M` remains finitely generated over the quotient
`R ⧸ Ann_R M` by its annihilator (with the canonical `Module.quotientAnnihilator`
action).  This is the affine, sections-level content of "the descended module
`N` on the schematic support `Z = V(Ann F)` is coherent" in the support-descent
brick `F ≅ i_* N`.

The `R ⧸ Ann_R M`-action is `Module.quotientAnnihilator`; the scalar tower
`R → R ⧸ Ann_R M → M` is `Module.IsTorsionBySet.isScalarTower` at `S := R`
(both `R → R` towers being canonical), and
`Module.Finite.of_restrictScalars_finite` transports finite generation upward
along the tower (a finite `R`-spanning set spans over the quotient, since the
`R`-action factors through it). -/
theorem module_finite_quotientAnnihilator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    Module.Finite (R ⧸ Module.annihilator R M) M := by
  letI := Module.quotientAnnihilator (R := R) (M := M)
  haveI : IsScalarTower R (R ⧸ Module.annihilator R M) M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ Module.annihilator R M) M

/-- **Sharpness of the schematic support (affine heart)**: over the quotient
`R ⧸ Ann_R M` by its own annihilator, the module `M` is *faithful* — its
annihilator is trivial.  Any residue class `q = mk r` annihilating `M` has
`r • m = q • m = 0` for every `m` (the `Module.quotientAnnihilator` action is
`mk r • m = r • m` definitionally), so `r ∈ Ann_R M`, i.e. `q = 0`.

Equivalently `FaithfulSMul (R ⧸ Ann_R M) M` (`Module.annihilator_eq_bot`): the
closed subscheme `V(Ann_R M)` is the honest schematic support of `F|_U`, carrying
no embedded component — exactly what makes the closed immersion `i : Z ↪ X_t` of
the brick `F ≅ i_* N` the scheme-theoretic support rather than an arbitrary
thickening. -/
theorem annihilator_quotientAnnihilator_eq_bot
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    Module.annihilator (R ⧸ Module.annihilator R M) M = ⊥ := by
  letI := Module.quotientAnnihilator (R := R) (M := M)
  rw [eq_bot_iff]
  intro q hq
  rw [Module.mem_annihilator] at hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
  intro m
  exact hq m

/-- **Finite presentation of the descended module (affine heart, Noetherian
base)**: over a Noetherian ring `R`, the module `M`, viewed over the quotient
`R ⧸ Ann_R M` by its annihilator (`Module.quotientAnnihilator`), is *finitely
presented*.

This upgrades `module_finite_quotientAnnihilator` (finite generation) to finite
presentation: `R ⧸ Ann_R M` is again Noetherian
(`Ideal.Quotient.isNoetherianRing`), so a finitely generated module over it is
finitely presented (`Module.finitePresentation_of_finite`).  It is the affine,
sections-level content of step (3) of the support-descent brick `F ≅ i_* N` —
"`N` is finitely presented on `Z = V(Ann F)`".  In the Quot consumer the fibre
`X_t` is a scheme of finite type over the residue field `κ(t)`, hence locally
Noetherian, so the schematic support `Z` is Noetherian and the finitely
generated descended module `N` is automatically finitely presented there. -/
theorem finitePresentation_quotientAnnihilator
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    Module.FinitePresentation (R ⧸ Module.annihilator R M) M := by
  letI := Module.quotientAnnihilator (R := R) (M := M)
  haveI : IsScalarTower R (R ⧸ Module.annihilator R M) M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  haveI : Module.Finite (R ⧸ Module.annihilator R M) M :=
    module_finite_quotientAnnihilator
  exact Module.finitePresentation_of_finite _ _

/-- **Faithfulness of the descended module (affine heart), instance form**: over
the quotient `R ⧸ Ann_R M` by its own annihilator the module `M` is *faithful*.

This is `annihilator_quotientAnnihilator_eq_bot` transported through
`Module.annihilator_eq_bot`, packaging the sharpness of the schematic support
(no embedded thickening: `V(Ann_R M)` is the honest scheme-theoretic support)
as the `FaithfulSMul` scalar-action fact directly consumable by downstream
closed-immersion bookkeeping in the brick `F ≅ i_* N`. -/
theorem faithfulSMul_quotientAnnihilator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    FaithfulSMul (R ⧸ Module.annihilator R M) M :=
  letI := Module.quotientAnnihilator (R := R) (M := M)
  Module.annihilator_eq_bot.mp annihilator_quotientAnnihilator_eq_bot

/-! ## The descent isomorphism `F ≅ i_* i^* F`, affine heart

The support-descent brick `F ≅ i_* N` of `lem:gamma_fiber_baseChange_field`
realizes a finitely presented sheaf `F` on `Y` as the pushforward `i_* (i^* F)`
of its restriction to the schematic-support closed immersion
`i : Z = V(Ann F) ↪ Y`.  The comparison is the unit
`η : F ⟶ i_* i^* F` of the pullback–pushforward adjunction, proved an
isomorphism affine-locally on a basis.

On an affine open `U = Spec R` of `Y` the closed immersion restricts to
`Spec (R ⧸ I) ↪ Spec R`, where `I := (annihilator F).ideal U` is the section of
the annihilator ideal sheaf.  The always-available `ofIdeals` direction
`annihilator_ideal_le` gives `I ≤ Ann_R M` for `M := Γ(F, U)` — this inclusion
(not the sharpness reverse, which is blocked on the QCoh localization bridge) is
*all* the descent isomorphism needs.  Under the tilde/pullback section formula
the closed-immersion restriction `Γ(i^* F, i⁻¹ U)` is `(R ⧸ I) ⊗_R M`, and the
unit `η.app U` is the canonical map `m ↦ 1 ⊗ₜ m : M → (R ⧸ I) ⊗_R M`.  The two
lemmas below package its inverse and bijectivity for `I ≤ Ann_R M`:

* `quotTensorEquivOfLeAnnihilator` / `quotTensorEquivOfLeAnnihilator_apply` — the
  `R`-linear equivalence `M ≃ₗ[R] (R ⧸ I) ⊗_R M` whose forward map is
  `m ↦ 1 ⊗ₜ m`.  Since `I` kills `M`, `I • ⊤ = ⊥`, so Mathlib's
  `TensorProduct.quotTensorEquivQuotSMul M I : (R ⧸ I) ⊗_R M ≃ₗ M ⧸ I • ⊤`
  collapses to `M ⧸ ⊥ ≅ M` (`Submodule.quotEquivOfEqBot`);
* `bijective_mk_one_of_le_annihilator` — the resulting bijectivity of the honest
  unit map `(TensorProduct.mk R (R ⧸ I) M) 1`, in the `Function.Bijective` form
  directly consumed by the section-wise iso criterion
  (`Modules.isIso_of_isIso_app_of_isBasis`) when globalizing `η` to the scheme
  isomorphism `F ≅ i_* i^* F`.

Universe-monomorphic pure algebra, axiom-clean. -/

/-- **The descent isomorphism, affine heart**: for an ideal `I ≤ Ann_R M` the
`R`-linear map `m ↦ 1 ⊗ₜ m : M → (R ⧸ I) ⊗_R M` is an equivalence.

`I ≤ Ann_R M` means `I • (⊤ : Submodule R M) = ⊥`, so
`TensorProduct.quotTensorEquivQuotSMul M I : (R ⧸ I) ⊗_R M ≃ₗ M ⧸ (I • ⊤)`
identifies the base change with `M ⧸ ⊥`, which is `M`
(`Submodule.quotEquivOfEqBot`); composing gives `M ≃ₗ[R] (R ⧸ I) ⊗_R M`.

This is the affine, sections-level content of the closed-immersion unit
`F ⟶ i_* i^* F` being an isomorphism in the support-descent brick `F ≅ i_* N`:
on `U = Spec R` the restriction `Γ(i^* F, i⁻¹ U)` is `(R ⧸ I) ⊗_R Γ(F, U)` and the
unit is exactly `m ↦ 1 ⊗ₜ m`.  Only the inclusion `I ≤ Ann_R M`
(`annihilator_ideal_le`, the always-available direction) is used — the reverse
sharpness inclusion, blocked on the QCoh localization bridge, is *not* needed for
the isomorphism, only for identifying `Z` as the honest (minimal) support. -/
noncomputable def quotTensorEquivOfLeAnnihilator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ≤ Module.annihilator R M) :
    M ≃ₗ[R] (R ⧸ I) ⊗[R] M :=
  have hbot : I • (⊤ : Submodule R M) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_bot]
    exact (Module.mem_annihilator.mp (hI hr)) n
  (Submodule.quotEquivOfEqBot (I • ⊤) hbot).symm.trans
    (TensorProduct.quotTensorEquivQuotSMul M I).symm

/-- The forward map of `quotTensorEquivOfLeAnnihilator` is the canonical unit
`m ↦ 1 ⊗ₜ m` — i.e. it *is* the (sections of the) closed-immersion adjunction
unit `F ⟶ i_* i^* F`, the load-bearing identification for globalizing the descent
isomorphism `F ≅ i_* N`. -/
theorem quotTensorEquivOfLeAnnihilator_apply
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ≤ Module.annihilator R M) (m : M) :
    quotTensorEquivOfLeAnnihilator I hI m = (1 : R ⧸ I) ⊗ₜ[R] m := by
  have hcomp := TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ (M := M) I
  simp only [quotTensorEquivOfLeAnnihilator, LinearEquiv.trans_apply]
  rw [show (Submodule.quotEquivOfEqBot (I • (⊤ : Submodule R M)) _).symm m
        = (I • (⊤ : Submodule R M)).mkQ m from rfl]
  exact congrArg (fun (f : _ →ₗ[R] _) => f m) hcomp

/-- **Bijectivity of the closed-immersion unit (affine heart)**: for `I ≤ Ann_R M`
the canonical map `(TensorProduct.mk R (R ⧸ I) M) 1 : M → (R ⧸ I) ⊗_R M`,
`m ↦ 1 ⊗ₜ m`, is bijective.

This is `quotTensorEquivOfLeAnnihilator` read as a `Function.Bijective`
statement about the honest unit map, the form directly consumable by the
section-wise isomorphism criterion `Modules.isIso_of_isIso_app_of_isBasis` when
upgrading the closed-immersion adjunction unit `F ⟶ i_* i^* F` to the scheme
isomorphism `F ≅ i_* N` of `lem:gamma_fiber_baseChange_field`. -/
theorem bijective_mk_one_of_le_annihilator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ≤ Module.annihilator R M) :
    Function.Bijective ((TensorProduct.mk R (R ⧸ I) M) 1) := by
  have hfun : ((TensorProduct.mk R (R ⧸ I) M) 1) =
      (quotTensorEquivOfLeAnnihilator I hI : M → (R ⧸ I) ⊗[R] M) := by
    funext m
    exact (quotTensorEquivOfLeAnnihilator_apply I hI m).symm
  rw [hfun]
  exact (quotTensorEquivOfLeAnnihilator I hI).bijective

/-- **Bijectivity of the closed-immersion unit, quotient-model-free form**: for
an `A`-algebra `B` whose structure map `algebraMap A B` is *surjective* with
kernel contained in `Ann_A M`, the canonical map
`(TensorProduct.mk A B M) 1 : M → B ⊗_A M`, `m ↦ 1 ⊗ₜ m`, is bijective.

This generalizes `bijective_mk_one_of_le_annihilator` from the literal quotient
`B = A ⧸ I` to any surjective presentation of `B`: the first isomorphism theorem
(`Ideal.quotientKerAlgEquivOfSurjective`) identifies `B ≅ A ⧸ ker` as
`A`-algebras, the identification transports the tensor factor
(`TensorProduct.congr`) carrying `1 ⊗ₜ m` to `1 ⊗ₜ m`, and the quotient case
applies.  It is the exact form consumed by the schematic-support descent: on an
affine `U ⊆ Y` the coordinate ring of a closed subscheme `V(I)` is presented by
the *surjection* `Γ(Y, U) → Γ(V(I), i⁻¹U)` with kernel `I(U)`
(`Scheme.IdealSheafData.subschemeι_app_surjective` / `ker_subschemeι_app`), not
as a literal quotient ring. -/
theorem bijective_mk_one_of_surjective_of_ker_le_annihilator
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M]
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) ≤ Module.annihilator A M) :
    Function.Bijective ((TensorProduct.mk A B M) 1) := by
  classical
  set f : A →ₐ[A] B := Algebra.ofId A B with hfdef
  have hf : Function.Surjective f := fun b => by
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, by simpa [hfdef, Algebra.ofId_apply] using ha⟩
  let e : (A ⧸ RingHom.ker f.toRingHom) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  -- `ker (Algebra.ofId A B) = ker (algebraMap A B)` definitionally
  have hquot : Function.Bijective
      ((TensorProduct.mk A (A ⧸ RingHom.ker f.toRingHom) M) 1) :=
    bijective_mk_one_of_le_annihilator (RingHom.ker f.toRingHom) hker
  -- transport along `TensorProduct.congr e.toLinearEquiv (refl)`
  let t : ((A ⧸ RingHom.ker f.toRingHom) ⊗[A] M) ≃ₗ[A] (B ⊗[A] M) :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)
  have hcomp : ∀ m : M, (TensorProduct.mk A B M) 1 m
      = t ((TensorProduct.mk A (A ⧸ RingHom.ker f.toRingHom) M) 1 m) := by
    intro m
    change (1 : B) ⊗ₜ[A] m = t ((1 : A ⧸ RingHom.ker f.toRingHom) ⊗ₜ[A] m)
    rw [show t ((1 : A ⧸ RingHom.ker f.toRingHom) ⊗ₜ[A] m)
        = e.toLinearEquiv 1 ⊗ₜ[A] m from TensorProduct.congr_tmul _ _ _ _]
    rw [show e.toLinearEquiv (1 : A ⧸ RingHom.ker f.toRingHom) = 1 from map_one e]
  rw [show ⇑((TensorProduct.mk A B M) 1)
      = ⇑t ∘ ⇑((TensorProduct.mk A (A ⧸ RingHom.ker f.toRingHom) M) 1)
    from funext hcomp]
  exact t.bijective.comp hquot

/-! ## The scheme-level descent isomorphism `F ≅ i_* i^* F`

The global assembly of the affine hearts above: for a quasi-coherent sheaf of
modules `F` on a scheme `Y` and an ideal sheaf `I` whose affine sections are
contained in the annihilators of the section modules of `F`, the adjunction
unit `F ⟶ i_* i^* F` along the closed immersion `i : V(I) ↪ Y` is an
isomorphism.

The proof is affine-local (`Modules.isIso_iff_isIso_app_affineOpens`): on an
affine `U ⊆ Y` the preimage `i⁻¹U` is affine (closed immersions are affine
morphisms), the quasi-coherent section formula
`pullback_app_isoTensor_baseMap_sectionLinearEquiv` identifies
`Γ(i^* F, i⁻¹U) ≅ Γ(V(I), i⁻¹U) ⊗_{Γ(Y,U)} Γ(F, U)` carrying `1 ⊗ x` to the
adjunction-unit image of `x`, and the unit section map becomes exactly
`m ↦ 1 ⊗ₜ m`, bijective by `bijective_mk_one_of_surjective_of_ker_le_annihilator`
(the coordinate ring of `V(I)` is the surjective image of `Γ(Y, U)` with kernel
`I(U) ⊆ Ann Γ(F, U)`, Mathlib's `subschemeι_app_surjective` +
`ker_subschemeι_app`). -/

namespace Scheme.Modules

open AlgebraicGeometry.Scheme

/-- **The closed-immersion adjunction unit is an isomorphism over the
annihilator** (the support-descent brick of `lem:gamma_fiber_baseChange_field`,
general ideal-sheaf form): for a quasi-coherent `F` on `Y` and an ideal sheaf
`I` with `I(U) ⊆ Ann_{Γ(Y,U)} Γ(F, U)` for every affine open `U`, the unit
`F ⟶ i_* i^* F` of the pullback–pushforward adjunction along the closed
immersion `i = I.subschemeι : V(I) ↪ Y` is an isomorphism.  Only the
always-available `ofIdeals` inclusion direction is consumed at the annihilator
instantiation, so no localization bridge is needed. -/
theorem isIso_unit_subschemeι_of_le_annihilator
    {Y : Scheme.{u}} (I : Y.IdealSheafData) (F : Y.Modules) [F.IsQuasicoherent]
    (hI : ∀ U : Y.affineOpens, I.ideal U ≤ Module.annihilator Γ(Y, U.1) Γ(F, U.1)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F) := by
  refine (Modules.isIso_iff_isIso_app_affineOpens _).mpr fun U => ?_
  -- the affine pair `(U ⊆ Y, i⁻¹U ⊆ V(I))` of the closed immersion
  have hW : IsAffineOpen (I.subschemeι ⁻¹ᵁ U.1) := U.2.preimage I.subschemeι
  letI algInst : Algebra Γ(Y, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) :=
    (I.subschemeι.appLE U.1 (I.subschemeι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  letI modInst : Module Γ(Y, U.1)
      Γ((Scheme.Modules.pullback I.subschemeι).obj F, I.subschemeι ⁻¹ᵁ U.1) :=
    Module.compHom _ (I.subschemeι.appLE U.1 (I.subschemeι ⁻¹ᵁ U.1) le_rfl).hom
  -- the quasi-coherent affine section formula for the pullback
  obtain ⟨f, hf⟩ :=
    (pullback_app_isoTensor_baseMap_sectionLinearEquiv I.subschemeι F hW U.2 le_rfl).some
  -- the base map at `e = le_rfl` *is* the unit section map
  have hbase : ∀ x : Γ(F, U.1),
      pullback_app_isoTensor_baseMap I.subschemeι F le_rfl x
        = (((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).app
            U.1).hom x := by
    intro x
    change ((((Scheme.Modules.pullback I.subschemeι).obj F).presheaf.map
        (homOfLE le_rfl).op).hom)
        ((((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).val.app
          (Opposite.op U.1)).hom x) = _
    rw [show (homOfLE (le_refl (I.subschemeι ⁻¹ᵁ U.1))) = 𝟙 (I.subschemeι ⁻¹ᵁ U.1) from rfl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  -- the algebra heart: `algebraMap = i.app U` is surjective with kernel `I(U)`
  have hsurj : Function.Surjective
      (algebraMap Γ(Y, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)) := by
    change Function.Surjective (I.subschemeι.appLE U.1 (I.subschemeι ⁻¹ᵁ U.1) le_rfl).hom
    rw [Scheme.Hom.appLE_eq_app]
    exact I.subschemeι_app_surjective U
  have hkerle : RingHom.ker (algebraMap Γ(Y, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1))
      ≤ Module.annihilator Γ(Y, U.1) Γ(F, U.1) := by
    change RingHom.ker (I.subschemeι.appLE U.1 (I.subschemeι ⁻¹ᵁ U.1) le_rfl).hom ≤ _
    rw [Scheme.Hom.appLE_eq_app, IdealSheafData.ker_subschemeι_app]
    exact hI U
  -- assemble: the unit section map is `f ∘ (m ↦ 1 ⊗ₜ m)`
  have hcomp : ⇑((((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app
        F).app U.1).hom)
      = ⇑f ∘ ⇑((TensorProduct.mk Γ(Y, U.1)
          Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) Γ(F, U.1)) 1) := by
    funext x
    exact ((hf x).trans (hbase x)).symm
  have hbij : Function.Bijective
      ((((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app F).app
        U.1).hom) := by
    rw [hcomp]
    exact f.bijective.comp
      (bijective_mk_one_of_surjective_of_ker_le_annihilator hsurj hkerle)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- **The schematic-support descent: the unit `F ⟶ i_* i^* F` is an
isomorphism** at the annihilator ideal sheaf (the geometric half of the brick
`F ≅ i_* N` of `lem:gamma_fiber_baseChange_field`): for a quasi-coherent `F`
on `Y` with schematic-support immersion
`i = schematicSupportι F : V(Ann F) ↪ Y`, the adjunction unit is invertible.
Instantiation of `isIso_unit_subschemeι_of_le_annihilator` via the
always-available `ofIdeals` direction `annihilator_ideal_le`. -/
theorem isIso_unit_schematicSupportι
    {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Scheme.Modules.schematicSupportι F)).unit.app F) :=
  isIso_unit_subschemeι_of_le_annihilator (Scheme.Modules.annihilator F) F
    (fun U => Scheme.Modules.annihilator_ideal_le F U)

/-- **The support-descent isomorphism `F ≅ i_* N`** with `N := i^* F` on the
schematic support `Z = V(Ann F)` (`lem:gamma_fiber_baseChange_field`, brick
(1)): packaging of `isIso_unit_schematicSupportι` as an `Iso`, the comparison
being the adjunction unit itself. -/
noncomputable def schematicSupportDescentIso
    {Y : Scheme.{u}} (F : Y.Modules) [F.IsQuasicoherent] :
    F ≅ (Scheme.Modules.pushforward (Scheme.Modules.schematicSupportι F)).obj
      ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι F)).obj F) :=
  @asIso _ _ _ _ _ (isIso_unit_schematicSupportι F)

/-- **The descended module `N = i^* F` is finitely presented on the schematic
support** (`lem:gamma_fiber_baseChange_field`, brick (2)): pullback along the
schematic-support immersion preserves finite presentation
(`Modules.pullback_isFinitePresentation`, valid for arbitrary morphisms). -/
theorem isFinitePresentation_pullback_schematicSupportι
    {Y : Scheme.{u}} (F : Y.Modules) (hfp : F.IsFinitePresentation) :
    ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι F)).obj
      F).IsFinitePresentation :=
  Scheme.Modules.pullback_isFinitePresentation _ F hfp

end Scheme.Modules

/-! ## Support monotonicity under the sheaf tensor product

The twist `F ⊗ L^{⊗m}` (`Scheme.Modules.moduleTensorPow`) has schematic support
contained in that of `F` — step (3) of the `lem:gamma_fiber_baseChange_field`
reduction.  On an affine `U`, any scalar `r` in the annihilator ideal sheaf of
the left factor kills every section `x` of the sheafified tensor product: by
local surjectivity of the sheafification unit
(`CategoryTheory.Presheaf.isLocallySurjective_toSheafify'` through the
`PresheafOfModules` bridge), `x` is locally — on affine basis members `W` — the
image of an honest presheaf-tensor element of `Γ(A, W) ⊗_{Γ(X, W)} Γ(B, W)`,
which the restricted scalar `r|_W` kills
(`annihilator_le_annihilator_tensorProduct`, valid since
`r|_W ∈ (annihilator A).ideal W ≤ Ann Γ(A, W)` by the ideal-sheaf restriction
compatibility `IdealSheafData.ideal_le_comap_ideal`); separatedness of the sheaf
then forces `r • x = 0` globally on `U`.  Consequently
`annihilator A ≤ annihilator (A ⊗ B)` (`ofIdeals` Galois property), the
schematic support of the twist closed-immerses into that of `A`
(`IdealSheafData.inclusion`), and proper support transfers to every twist. -/

open TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **Annihilator sections kill the sheaf tensor product (affine heart)**: on an
affine open `U`, the annihilator ideal sheaf of `A` is contained in the
annihilator of the sections of `sheafTensorObj A B`.  Local surjectivity of the
sheafification unit reduces this to the presheaf-tensor statement
`annihilator_le_annihilator_tensorProduct` on an affine basis, and sheaf
separatedness globalizes the vanishing back to `U`. -/
theorem ideal_annihilator_le_annihilator_sheafTensorObj
    {X : Scheme.{u}} (A B : X.Modules) (U : X.affineOpens) :
    (Scheme.Modules.annihilator A).ideal U
      ≤ Module.annihilator Γ(X, U.1) Γ(Scheme.Modules.sheafTensorObj A B, U.1) := by
  classical
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  -- the sheafification unit of the presheaf tensor is locally surjective
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app (Scheme.Modules.tensorPresheaf A B))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact ((Opens.grothendieckTopology ↥X).W_toSheafify _).isLocallySurjective
  -- for every point of `U` there is an affine `W ∋ p`, `W ≤ U`, with
  -- `(r • x)|_W = 0`
  have key : ∀ p : U.1, ∃ W : X.Opens, ∃ _ : p.1 ∈ W, ∃ hWU : W ≤ U.1,
      ((Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWU).op).hom (r • x) = 0 := by
    intro p
    obtain ⟨V, g, ⟨t, ht⟩, hpV⟩ := hsurj.imageSieve_mem (U := U.1) x p.1 p.2
    -- refine to an affine basis member `W ∋ p` inside `V`
    obtain ⟨W, hWaff, hpW, hWV⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hpV
    have hWU : W ≤ U.1 := hWV.trans g.le
    refine ⟨W, hpW, hWU, ?_⟩
    -- the restricted scalar `r|_W` annihilates the presheaf tensor over `W`
    have hrW : (X.presheaf.map (homOfLE hWU).op).hom r
        ∈ (Scheme.Modules.annihilator A).ideal ⟨W, hWaff⟩ :=
      Scheme.IdealSheafData.ideal_le_comap_ideal (Scheme.Modules.annihilator A)
        (U := ⟨W, hWaff⟩) (V := U) hWU hr
    have hkill : (X.presheaf.map (homOfLE hWU).op).hom r
        ∈ Module.annihilator Γ(X, W) (TensorProduct Γ(X, W) Γ(A, W) Γ(B, W)) :=
      annihilator_le_annihilator_tensorProduct
        (Scheme.Modules.annihilator_ideal_le A ⟨W, hWaff⟩ hrW)
    -- restrict the local presheaf-tensor preimage `t` of `x|_V` to `W`
    have hnat := Scheme.Modules.tensorSectionHom_naturality_apply A B
      (V := W) (W := V) (homOfLE hWV).op t
    -- `(r • x)|_W = r|_W • x|_W` (semilinearity of restriction)
    have hres : ((Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWU).op).hom (r • x)
        = (X.presheaf.map (homOfLE hWU).op).hom r
            • ((Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWU).op).hom x :=
      PresheafOfModules.map_smul _ _ _ _
    rw [hres]
    -- `x|_W` is the image of the restricted presheaf tensor `t|_W`:
    -- restrict in two steps `U ⊇ V ⊇ W` (`congr_map_apply` + `map_comp_apply`),
    -- recognize `x|_V` as the unit image of `t` (`ht`), and pull the last
    -- restriction through the unit (`tensorSectionHom` naturality)
    have e1 : (Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWU).op x
        = (Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWV).op
            ((Scheme.Modules.sheafTensorObj A B).val.map g.op x) :=
      (PresheafOfModules.congr_map_apply (Scheme.Modules.sheafTensorObj A B).val
        (show (homOfLE hWU).op = g.op ≫ (homOfLE hWV).op by
          rw [show (homOfLE hWU : W ⟶ U.1) = (homOfLE hWV : W ⟶ V) ≫ g from
            Subsingleton.elim _ _, op_comp]) x).trans
        (PresheafOfModules.map_comp_apply _ g.op (homOfLE hWV).op x)
    have e2 : (Scheme.Modules.sheafTensorObj A B).val.map g.op x
        = Scheme.Modules.tensorSectionHom A B V t := ht.symm
    have e3 : (Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWV).op
          (Scheme.Modules.tensorSectionHom A B V t)
        = Scheme.Modules.tensorSectionHom A B W
            ((Scheme.Modules.tensorPresheaf A B).map (homOfLE hWV).op t) := hnat.symm
    have hxW : (Scheme.Modules.sheafTensorObj A B).val.map (homOfLE hWU).op x
        = Scheme.Modules.tensorSectionHom A B W
            ((Scheme.Modules.tensorPresheaf A B).map (homOfLE hWV).op t) := by
      rw [e1, e2, e3]
    rw [hxW]
    -- pull the scalar through the (Γ(X, W)-linear) unit and kill it in the
    -- presheaf tensor
    have hlin : (X.presheaf.map (homOfLE hWU).op).hom r
          • Scheme.Modules.tensorSectionHom A B W
              ((Scheme.Modules.tensorPresheaf A B).map (homOfLE hWV).op t)
        = Scheme.Modules.tensorSectionHom A B W
            ((X.presheaf.map (homOfLE hWU).op).hom r
              • (Scheme.Modules.tensorPresheaf A B).map (homOfLE hWV).op t) :=
      (map_smul (Scheme.Modules.tensorSectionHom A B W).hom _ _).symm
    rw [hlin, Module.mem_annihilator.mp hkill _, map_zero]
  choose W hpW hWU hzero using key
  -- separatedness of the sheaf over the pointwise affine cover of `U`
  have hcov : U.1 ≤ iSup W := fun q hq =>
    Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hpW ⟨q, hq⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(Scheme.Modules.sheafTensorObj A B).presheaf,
      (Scheme.Modules.sheafTensorObj A B).isSheaf⟩ : TopCat.Sheaf Ab X)
    W U.1 (fun p => homOfLE (hWU p)) hcov (r • x) 0 (fun p => ?_)
  rw [map_zero]
  exact hzero p

/-- **Annihilator monotonicity for the sheaf tensor product, ideal-sheaf form**:
`annihilator A ≤ annihilator (A ⊗ B)` (`ofIdeals` Galois property applied to the
affine heart `ideal_annihilator_le_annihilator_sheafTensorObj`). -/
theorem annihilator_le_annihilator_sheafTensorObj
    {X : Scheme.{u}} (A B : X.Modules) :
    Scheme.Modules.annihilator A
      ≤ Scheme.Modules.annihilator (Scheme.Modules.sheafTensorObj A B) :=
  Scheme.IdealSheafData.le_ofIdeals_iff.mpr
    (fun U => ideal_annihilator_le_annihilator_sheafTensorObj A B U)

namespace Scheme.Modules

/-- **Proper support descends along annihilator inclusions**: if
`annihilator A ≤ annihilator C` then the schematic support of `C`
closed-immerses into that of `A` (`IdealSheafData.inclusion`), so properness of
the support of `A` over `S` transfers to `C` (closed immersions are proper,
propers compose). -/
theorem HasProperSupport.of_annihilator_le {X S : Scheme.{u}} (f : X ⟶ S)
    {A C : X.Modules}
    (h : Scheme.Modules.annihilator A ≤ Scheme.Modules.annihilator C)
    (hA : Scheme.Modules.HasProperSupport f A) :
    Scheme.Modules.HasProperSupport f C := by
  haveI : IsProper ((Scheme.Modules.annihilator A).subschemeι ≫ f) := hA
  have hfac : Scheme.IdealSheafData.inclusion h
        ≫ ((Scheme.Modules.annihilator A).subschemeι ≫ f)
      = (Scheme.Modules.annihilator C).subschemeι ≫ f := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  change IsProper ((Scheme.Modules.annihilator C).subschemeι ≫ f)
  rw [← hfac]
  infer_instance

/-- **Proper support transfers to sheaf-tensor twists** (left factor): the
schematic support of `A ⊗ B` sits inside that of `A`, so proper support of `A`
over `S` gives proper support of the tensor. -/
theorem hasProperSupport_sheafTensorObj {X S : Scheme.{u}} (f : X ⟶ S)
    {A : X.Modules} (B : X.Modules)
    (hA : Scheme.Modules.HasProperSupport f A) :
    Scheme.Modules.HasProperSupport f (Scheme.Modules.sheafTensorObj A B) :=
  HasProperSupport.of_annihilator_le f
    (annihilator_le_annihilator_sheafTensorObj A B) hA

/-- **Proper support transfers to the twists `F ⊗ L^{⊗m}`**
(`Scheme.Modules.moduleTensorPow`), step (3) of the
`lem:gamma_fiber_baseChange_field` reduction: `moduleTensorPow F L m` is by
definition `sheafTensorObj F (tensorPow L m)`. -/
theorem hasProperSupport_moduleTensorPow {X S : Scheme.{u}} (f : X ⟶ S)
    {F : X.Modules} (L : X.Modules) (m : ℕ)
    (hF : Scheme.Modules.HasProperSupport f F) :
    Scheme.Modules.HasProperSupport f (Scheme.Modules.moduleTensorPow F L m) :=
  hasProperSupport_sheafTensorObj f (Scheme.Modules.tensorPow L m) hF

end Scheme.Modules

/-! ## The Γ-fibre flat base change over a field, via the schematic support

The scheme-level assembly of `lem:gamma_fiber_baseChange_field` for a single
quasi-coherent module with proper support: for a cartesian square

```
Xt' ──b──→ Xt
 │f'        │f
 ↓          ↓
Spec K' ──Spec.map φ──→ Spec K
```

over fields `K`, `K'` and a quasi-coherent `G` on `Xt` whose schematic support
is proper over `K`, the `K'`-dimension of `Γ(Xt', b^* G)` equals the
`K`-dimension of `Γ(Xt, G)` (each via the structural `ΓSpecIso`-composite
scalar action, the shape of `Scheme.Hom.fiberSectionsModule`).

Route: `Xt` is only locally of finite type over `K` — not qcqs — so Stacks
02KH cannot be applied on `Xt` itself.  Descend to the schematic support
`i : Z = V(Ann G) ↪ Xt` (proper over `K` by hypothesis, hence qcqs):

1. `G ≅ i_* N` for `N := i^* G` (`isIso_unit_schematicSupportι`);
2. `b^*(i_* N) ≅ j_* (w^* N)` for the base-changed closed immersion
   `j : W = Z ×_{Xt} Xt' ↪ Xt'` (`flatBaseChangeCohomology` on the
   closed-immersion square — `i` is qcqs, `b` is flat as the base change of
   the field extension `Spec.map φ`);
3. pushing forward to `Spec K'` and evaluating at `⊤` identifies
   `Γ(Xt', b^* G)` with `Γ(Spec K', (j ≫ f')_* (w^* N))`,
   `Γ(Spec K', ⊤)`-linearly (`finrank_eq_of_ringEquiv_addEquiv` transports the
   dimension along `ΓSpecIso K'`), and similarly on the unprimed side;
4. the pasted square `W → Z → Spec K ← Spec K' ← W` is cartesian
   (`IsPullback.paste_vert`) with `i ≫ f` proper — qcqs — so the CLOSED
   02KE heart `pullback_baseMap_sectionLinearEquiv_of_quasiCompact` at
   `V = U = ⊤` yields `Γ(Spec K', ⊤) ⊗ Γ(Z, N) ≃ₗ Γ(W, w^* N)`, and
   `finrank_eq_of_baseChange_linearEquiv` (with the field structures
   transported along `ΓSpecIso` via `MulEquiv.isField`) closes the count. -/

/-- **Dimension transport across a ring isomorphism**: a ring isomorphism
`i : R ≃+* R'` together with an additive equivalence `j : M ≃+ M'`
intertwining the scalar actions transports `Module.finrank`.  This is the
`Cardinal.toNat` image of `rank_eq_of_equiv_equiv`; it is the bookkeeping
device carrying `κ'`-dimensions across the `ΓSpecIso` identification
`Γ(Spec κ', ⊤) ≃+* κ'` in the Γ-fibre base-change assembly. -/
theorem finrank_eq_of_ringEquiv_addEquiv
    {R R' : Type*} {M M' : Type v} [Semiring R] [Semiring R']
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R' M']
    (i : R ≃+* R') (j : M ≃+ M')
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M' :=
  congrArg Cardinal.toNat (rank_eq_of_equiv_equiv i j i.bijective hc)

namespace Scheme

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- pasted-square 02KE + flat-base-change exchange over the scheme-module stack
/-- **Γ-fibre flat base change over a field extension, schematic-support form**
([Stacks 02KH] `i = 0` via the support descent; the scheme-level heart of
`lem:gamma_fiber_baseChange_field`): for a cartesian square
`b : Xt' ⟶ Xt` over `Spec.map φ : Spec K' ⟶ Spec K` with `K`, `K'` fields, and
a quasi-coherent `G` on `Xt` with schematic support proper over `K`, the
`K'`-dimension of the global sections of `b^* G` equals the `K`-dimension of
the global sections of `G` — the scalar actions being the structural
`ΓSpecIso⁻¹ ≫ appTop` composites (the shape of
`Scheme.Hom.fiberSectionsModule`/`fiberResidueMap` at residue fields).  See
the section header for the proof route. -/
theorem finrank_gammaTop_baseChange_of_hasProperSupport
    {K K' : CommRingCat.{u}} (hK : IsField K) (hK' : IsField K')
    {Xt Xt' : Scheme.{u}} {f : Xt ⟶ Spec K} {f' : Xt' ⟶ Spec K'}
    {b : Xt' ⟶ Xt} {φ : K ⟶ K'}
    (sq : IsPullback b f' f (Spec.map φ))
    (G : Xt.Modules) [G.IsQuasicoherent]
    (hps : Scheme.Modules.HasProperSupport f G) :
    (letI := Module.compHom Γ((Scheme.Modules.pullback b).obj G, ⊤)
        ((Scheme.ΓSpecIso K').inv ≫ f'.appTop).hom
     Module.finrank K' Γ((Scheme.Modules.pullback b).obj G, ⊤))
      = (letI := Module.compHom Γ(G, ⊤) ((Scheme.ΓSpecIso K).inv ≫ f.appTop).hom
         Module.finrank K Γ(G, ⊤)) := by
  letI := Module.compHom Γ((Scheme.Modules.pullback b).obj G, ⊤)
      ((Scheme.ΓSpecIso K').inv ≫ f'.appTop).hom
  letI := Module.compHom Γ(G, ⊤) ((Scheme.ΓSpecIso K).inv ≫ f.appTop).hom
  -- field structures on the global sections of the two affine bases
  letI : Field ↥Γ(Spec K, ⊤) :=
    (MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv).toField
  letI : Field ↥Γ(Spec K', ⊤) :=
    (MulEquiv.isField hK' (Scheme.ΓSpecIso K').commRingCatIsoToRingEquiv.toMulEquiv).toField
  -- properness of the schematic support over `Spec K`, hence qcqs instances
  haveI hproper : IsProper (Scheme.Modules.schematicSupportι G ≫ f) := hps
  haveI : QuasiCompact (Scheme.Modules.schematicSupportι G) :=
    inferInstanceAs (QuasiCompact ((Scheme.Modules.annihilator G).subschemeι))
  haveI : IsSeparated (Scheme.Modules.schematicSupportι G) :=
    inferInstanceAs (IsSeparated ((Scheme.Modules.annihilator G).subschemeι))
  -- flatness of the field extension `Spec.map φ` and of its base change `b`
  haveI hφflat : Flat (Spec.map φ) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    letI : Field ↥K := hK.toField
    letI := φ.hom.toAlgebra
    change Module.Flat ↥K ↥K'
    infer_instance
  haveI hbflat : Flat b := MorphismProperty.of_isPullback sq.flip hφflat
  -- quasi-coherence of the descended module `N := i^* G`
  haveI hNqc : ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj
      G).IsQuasicoherent :=
    pullback_isQuasicoherent_hom _ G ‹_›
  -- the closed-immersion base-change square and its pasting over `Spec.map φ`
  have sq1 : IsPullback (pullback.fst (Scheme.Modules.schematicSupportι G) b)
      (pullback.snd (Scheme.Modules.schematicSupportι G) b)
      (Scheme.Modules.schematicSupportι G) b :=
    IsPullback.of_hasPullback _ _
  have sqZ : IsPullback (pullback.fst (Scheme.Modules.schematicSupportι G) b)
      (pullback.snd (Scheme.Modules.schematicSupportι G) b ≫ f')
      (Scheme.Modules.schematicSupportι G ≫ f) (Spec.map φ) :=
    sq1.paste_vert sq
  -- support descent `G ≅ i_* N` and the flat-base-change exchange
  haveI hunit := Scheme.Modules.isIso_unit_schematicSupportι G
  obtain ⟨eEx⟩ := flatBaseChangeCohomology sq1
    ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G)
  -- assembled isos over the two affine bases, and their `⊤`-section equivalences
  let EL : (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback b).obj G)
      ≅ (Scheme.Modules.pushforward
            (pullback.snd (Scheme.Modules.schematicSupportι G) b ≫ f')).obj
          ((Scheme.Modules.pullback
            (pullback.fst (Scheme.Modules.schematicSupportι G) b)).obj
            ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G)) :=
    (Scheme.Modules.pushforward f').mapIso
        ((Scheme.Modules.pullback b).mapIso
          (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
            (Scheme.Modules.schematicSupportι G)).unit.app G)) ≪≫ eEx)
      ≪≫ ((Scheme.Modules.pushforwardComp
            (pullback.snd (Scheme.Modules.schematicSupportι G) b) f').app
          ((Scheme.Modules.pullback
            (pullback.fst (Scheme.Modules.schematicSupportι G) b)).obj
            ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G))).symm
  let ER : (Scheme.Modules.pushforward f).obj G
      ≅ (Scheme.Modules.pushforward (Scheme.Modules.schematicSupportι G ≫ f)).obj
          ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G) :=
    (Scheme.Modules.pushforward f).mapIso
        (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
          (Scheme.Modules.schematicSupportι G)).unit.app G))
      ≪≫ ((Scheme.Modules.pushforwardComp (Scheme.Modules.schematicSupportι G) f).app
          ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G)).symm
  let γL := ((Scheme.Modules.toPresheafOfModules (Spec K') ⋙
      PresheafOfModules.evaluation (Spec K').ringCatSheaf.obj (Opposite.op ⊤)).mapIso
        EL).toLinearEquiv
  let γR := ((Scheme.Modules.toPresheafOfModules (Spec K) ⋙
      PresheafOfModules.evaluation (Spec K).ringCatSheaf.obj (Opposite.op ⊤)).mapIso
        ER).toLinearEquiv
  -- Step A: transport the `K'`-dimension along `ΓSpecIso K'` and `γL`
  have stepA : (Module.finrank K' Γ((Scheme.Modules.pullback b).obj G, ⊤))
      = Module.finrank ↥Γ(Spec K', ⊤)
          Γ((Scheme.Modules.pushforward
              (pullback.snd (Scheme.Modules.schematicSupportι G) b ≫ f')).obj
            ((Scheme.Modules.pullback
              (pullback.fst (Scheme.Modules.schematicSupportι G) b)).obj
              ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G)), ⊤) :=
    finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso K').symm.commRingCatIsoToRingEquiv
      γL.toAddEquiv
      (fun c y => γL.map_smul ((Scheme.ΓSpecIso K').inv.hom c) y)
  -- Step C: transport the `K`-dimension along `ΓSpecIso K` and `γR`
  have stepC : (Module.finrank K Γ(G, ⊤))
      = Module.finrank ↥Γ(Spec K, ⊤)
          Γ((Scheme.Modules.pushforward (Scheme.Modules.schematicSupportι G ≫ f)).obj
            ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G), ⊤) :=
    finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso K).symm.commRingCatIsoToRingEquiv
      γR.toAddEquiv
      (fun c y => γR.map_smul ((Scheme.ΓSpecIso K).inv.hom c) y)
  -- Step B: the CLOSED 02KE heart on the pasted square, at `V = U = ⊤`
  have hVaff : IsAffineOpen (⊤ : (Spec K).Opens) := isAffineOpen_top (Spec K)
  have hUaff : IsAffineOpen (⊤ : (Spec K').Opens) := isAffineOpen_top (Spec K')
  have e0 : (⊤ : (Spec K').Opens) ≤ (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec K).Opens) :=
    le_of_eq rfl
  have e'' : (pullback.snd (Scheme.Modules.schematicSupportι G) b ≫ f')
        ⁻¹ᵁ (⊤ : (Spec K').Opens)
      ≤ (pullback.fst (Scheme.Modules.schematicSupportι G) b)
        ⁻¹ᵁ ((Scheme.Modules.schematicSupportι G ≫ f) ⁻¹ᵁ (⊤ : (Spec K).Opens)) :=
    le_of_eq rfl
  letI : Algebra ↥Γ(Spec K, ⊤) ↥Γ(Spec K', ⊤) :=
    ((Spec.map φ).appLE ⊤ ⊤ e0).hom.toAlgebra
  obtain ⟨eqBC, -⟩ := (pullback_baseMap_sectionLinearEquiv_of_quasiCompact sqZ
    ((Scheme.Modules.pullback (Scheme.Modules.schematicSupportι G)).obj G)
    hVaff hUaff e0 e'').some
  exact stepA.trans ((finrank_eq_of_baseChange_linearEquiv eqBC).trans stepC.symm)

end Scheme

end AlgebraicGeometry
