/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

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
-/

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

end AlgebraicGeometry
