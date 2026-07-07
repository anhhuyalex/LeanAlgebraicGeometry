/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Cohomology.MayerVietorisCover

/-!
# The 2-cover Čech cokernel `Ȟ¹(D)` for adelic Riemann–Roch (nodes N5–N7)

This file is part of the **adelic Riemann–Roch lane** (see the lane design document).
It realises the degree-`1` cohomology of a curve as the concrete cokernel of a
two-chart cover — the algebraic incarnation of Weil's repartition quotient
`A_K / (A_K(D) + K)`.

## The bridge from genus `H¹` to the Čech `H¹` (node N6)

The project's genus carrier is `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1`.
For a cover `𝒰` of `C` with `⨆ 𝒰 = ⊤` that is a **good** (Leray) cover — i.e. one
for which the Čech-to-derived comparison `HasCechToHModuleIso F 𝒰` holds — there is a
`k`-linear identification
```
HModule k F 1  ≃ₗ[k]  cechCohomology C F 𝒰 1,
```
obtained by chaining the comparison iso `cechToHModuleIso` (iter-050) with the
universe bridge `HModule'_eq_HModule_linearEquiv` (iter-034) at the terminal open
`⊤ = ⨆ 𝒰`.  This is `hModuleOne_linearEquiv_cechCohomology`.

The hypothesis `HasCechToHModuleIso F 𝒰` is the existing project **gate** (a
single-field `Prop` class with no unconditional instance for a 2-affine cover of a
positive-genus curve): the equivalence is delivered *conditional* on that class,
exactly as the design intends.  Note that `IsCechAcyclicCover F 𝒰` for the whole
curve is **not** available (nor true) here: for a genus-`g` curve the degree-`1`
Čech cohomology of a 2-affine cover is `k^g ≠ 0`, so it is deliberately *not*
assumed — the comparison `HasCechToHModuleIso` (which does *not* force the
cohomology to vanish) is the correct and honest hypothesis.

## The concrete section-level cokernel (node N5 target, definition)

For a bundled 2-affine cover `S : X.AffineCoverMVSquare` and a sheaf `F` of
`k`-modules, the **difference-of-restrictions** map
```
δ : Γ(U₁, F) × Γ(U₂, F) →ₗ[k] Γ(U₁ ⊓ U₂, F),   (a, b) ↦ a|_{U₁∩U₂} − b|_{U₁∩U₂}
```
is `AffineCoverMVSquare.sectionDiff`.  Its cokernel `AffineCoverMVSquare.H1Cok`
is the concrete `Ȟ¹`, and its kernel `AffineCoverMVSquare.sectionGlue` is the
`H⁰ = L(D)` sheaf-gluing space (global sections `= { f : agree on the overlap }`).

Because `F` is an arbitrary sheaf of `k`-modules, `H1Cok S F` is *already* the
divisor-twisted `Ȟ¹(D)`: specialising `F := 𝒪_C(D)` once N3's `sectionOfDivisor`
lands recovers the `H¹(D)` of the χ-ledger.  The identification
`H1Cok S F ≃ₗ[k] cechCohomology C F S.cover 1` (node N5 proper) is left to the next
wave; the pieces here (the concrete cokernel and the genus bridge) are what its two
sides need.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-! ## Node N6 — the `k`-linear bridge `HModule k F 1 ≃ₗ[k] cechCohomology C F 𝒰 1` -/

/-- **Node N6 (bridge), abstract sheaf form.** For a sheaf `F` of `k`-modules on a
`Spec k`-scheme `C` and a cover `𝒰` with `⨆ 𝒰 = ⊤` satisfying the Čech-to-derived
comparison gate `HasCechToHModuleIso F 𝒰`, the genus-degree cohomology
`HModule k F n` is `k`-linearly identified with the Čech cohomology
`cechCohomology C F 𝒰 n` of the cover.

The equivalence chains the iter-050 comparison
`cechToHModuleIso n : cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰)` with the
iter-034 universe bridge `HModule'_eq_HModule_linearEquiv` at the terminal open
`⊤ = ⨆ 𝒰` (using `Preorder.isTerminalTop` transported along `h`, exactly the
iter-035 `HModule'_X₄_linearEquiv` pattern), then symmetrises.

This is stated *conditional* on the `HasCechToHModuleIso` gate — no new `sorry` or
gate is introduced.  Downstream (`N5`, the finiteness keystone `N11`/`N12`) the
useful degree is `n = 1`: it reduces `H¹(C, 𝒪_C)` to the concrete Čech `H¹`. -/
noncomputable def hModuleOne_linearEquiv_cechCohomology
    {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) :
    HModule k F n ≃ₗ[k] cechCohomology C F 𝒰 n :=
  ((cechToHModuleIso n).trans
    (HModule'_eq_HModule_linearEquiv k F n
      (h.symm ▸ Preorder.isTerminalTop (TopologicalSpace.Opens C.left.toTopCat)))).symm

/-- **Node N6 (bridge), curve specialisation.** Direct application of
`hModuleOne_linearEquiv_cechCohomology` to the structure sheaf
`F := Scheme.toModuleKSheaf C`.  Mirrors the iter-039/…/iter-050 `_curve` pattern
(dot-notation resolution against the structure sheaf), giving
`HModule k (toModuleKSheaf C) n ≃ₗ[k] cechCohomology C (toModuleKSheaf C) 𝒰 n`. -/
noncomputable def hModuleOne_linearEquiv_cechCohomology_curve
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso (Scheme.toModuleKSheaf C) 𝒰]
    (h : ⨆ i, 𝒰 i = ⊤) (n : ℕ) :
    HModule k (Scheme.toModuleKSheaf C) n
      ≃ₗ[k] cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n :=
  hModuleOne_linearEquiv_cechCohomology (Scheme.toModuleKSheaf C) 𝒰 h n

/-! ## Node N5 target — the concrete section-level difference map and cokernel -/

section ConcreteCokernel

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))

/-- The restriction `k`-linear map `Γ(V, F) →ₗ[k] Γ(U, F)` for an inclusion of opens
`U ≤ V`, extracted from the underlying presheaf of the sheaf of `k`-modules `F`. -/
noncomputable def sectionRestrict {U V : TopologicalSpace.Opens X.toTopCat} (h : U ≤ V) :
    F.obj.obj (Opposite.op V) →ₗ[k] F.obj.obj (Opposite.op U) :=
  (F.obj.map (homOfLE h).op).hom

/-- **Node N5 target — the difference-of-restrictions map** of a 2-affine cover.
For `S : X.AffineCoverMVSquare`, this is the `k`-linear map
`Γ(U₁, F) × Γ(U₂, F) →ₗ[k] Γ(U₁ ⊓ U₂, F)` sending `(a, b)` to `a|_{U₁∩U₂} − b|_{U₁∩U₂}`.
Its image is the "coboundary" subspace `Γ(U₁) + Γ(U₂)` inside `Γ(U₁ ⊓ U₂)`. -/
noncomputable def AffineCoverMVSquare.sectionDiff (S : X.AffineCoverMVSquare) :
    (F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) →ₗ[k]
      F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂)) :=
  (sectionRestrict F (inf_le_left)).comp (LinearMap.fst k _ _)
    - (sectionRestrict F (inf_le_right)).comp (LinearMap.snd k _ _)

/-- **The concrete Čech `Ȟ¹` of a 2-affine cover** as the cokernel of the
difference-of-restrictions map:
`Ȟ¹ = Γ(U₁ ⊓ U₂, F) ⧸ (Γ(U₁, F) + Γ(U₂, F))`.
For `F` an arbitrary sheaf of `k`-modules this is the divisor-twisted `Ȟ¹(D)`;
specialising `F := 𝒪_C(D)` recovers Weil's `A_K/(A_K(D)+K)`. -/
noncomputable def AffineCoverMVSquare.H1Cok (S : X.AffineCoverMVSquare) : Type u :=
  F.obj.obj (Opposite.op (S.U₁ ⊓ S.U₂)) ⧸ LinearMap.range (S.sectionDiff F)

noncomputable instance AffineCoverMVSquare.instAddCommGroupH1Cok
    (S : X.AffineCoverMVSquare) : AddCommGroup (S.H1Cok F) :=
  inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range (S.sectionDiff F)))

noncomputable instance AffineCoverMVSquare.instModuleH1Cok
    (S : X.AffineCoverMVSquare) : Module k (S.H1Cok F) :=
  inferInstanceAs (Module k (_ ⧸ LinearMap.range (S.sectionDiff F)))

/-- **The `H⁰ = L(D)` gluing space** as the kernel of the difference-of-restrictions
map: a pair `(a, b)` lies in the kernel iff `a` and `b` agree on the overlap
`U₁ ⊓ U₂`, i.e. glue to a single global section (`= { f ∈ K : div f + D ≥ 0 }` in the
twisted case).  This is the `Submodule` incarnation of `L(D)`. -/
noncomputable def AffineCoverMVSquare.sectionGlue (S : X.AffineCoverMVSquare) :
    Submodule k (F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) :=
  LinearMap.ker (S.sectionDiff F)

/-- **The gluing/`L(D)` condition is agreement on the overlap.** A pair of sections
`(a, b) ∈ Γ(U₁, F) × Γ(U₂, F)` lies in the `H⁰`-gluing space `sectionGlue` exactly
when the two restrictions to `U₁ ⊓ U₂` coincide.  In the twisted case `F = 𝒪_C(D)`
this is `L(D) = { f ∈ K : div f + D ≥ 0 }`. -/
lemma AffineCoverMVSquare.mem_sectionGlue (S : X.AffineCoverMVSquare)
    (p : F.obj.obj (Opposite.op S.U₁) × F.obj.obj (Opposite.op S.U₂)) :
    p ∈ S.sectionGlue F ↔
      sectionRestrict F (inf_le_left) p.1 = sectionRestrict F (inf_le_right) p.2 := by
  rw [sectionGlue, LinearMap.mem_ker, AffineCoverMVSquare.sectionDiff,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero]

end ConcreteCokernel

end AlgebraicGeometry.Scheme
