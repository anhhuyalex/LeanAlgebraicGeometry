/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.PullbackFinitePresentation

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

universe u

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

end AlgebraicGeometry
