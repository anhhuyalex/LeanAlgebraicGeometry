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
lands recovers the `H¹(D)` of the χ-ledger.

## The concrete 2-cover family and the N6 bridge on it (this wave)

`AffineCoverMVSquare.coverFamily : ULift (Fin 2) → Opens X` packages `U₁, U₂` as the
`Type u`-indexed family that `Scheme.cechCohomology` / the N6 bridge consume, with
`iSup_coverFamily : ⨆ i, S.coverFamily i = ⊤` the family-form of the cover totality.
`hModuleOne_linearEquiv_cechCohomology_coverFamily` then lands the N6 bridge on this
concrete family: `HModule k F n ≃ₗ[k] cechCohomology C F S.coverFamily n` (gated on
`HasCechToHModuleIso F S.coverFamily`).  Chaining node N5 (below) into this at `n = 1`
gives the lane's consumable corollary `HModule k F 1 ≃ₗ[k] H1Cok S F`.

## The N5 identification `cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F` (roadmap)

The in-tree `cechCohomology` is the homology of Mathlib's **unnormalized**
`cechComplexFunctor` (`FormalCoproduct.cochainComplexFunctor` of the Čech nerve): in
degree `n` the product runs over **all** `Fin (n+1) → ι` (not just increasing
multi-indices), and the differential `dⁿ = ∑_{i} (-1)^i δⁱ` is the alternating sum of
the cosimplicial cofaces `δⁱ = evalOp(P)(mapPower δ_i)` (a `Pi.lift` of projections to
`x ∘ δ_i` followed by the restriction `P(⨅ U∘(x∘δ_i)) → P(⨅ U∘x)`).  For the 2-element
cover (`ι = ULift (Fin 2)`) this is
```
  M⁰ = Γ(U₀) × Γ(U₁)                         (indices Fin 1 → ι)
  M¹ = Γ(U₀) × Γ(U₀₁) × Γ(U₀₁) × Γ(U₁)       (indices (0,0),(0,1),(1,0),(1,1))
  M² = ∏ over the 8 indices Fin 3 → ι         (incl. the degenerate diagonals)
```
where `Γ(U₀₁) = Γ(U₀ ⊓ U₁)`, and the two diagonal factors of `M¹` are the degenerate
cofaces `U_i ⊓ U_i = U_i`.  Writing a degree-1 cochain as `(p, q, r, s)`:

* `d⁰(a, b) = (0, b|₀₁ − a|₀₁, a|₀₁ − b|₀₁, 0)`, so
  `im d⁰ = { (0, w, −w, 0) : w ∈ range (S.sectionDiff F) }` (note `w = b|₀₁ − a|₀₁` and
  `sectionDiff (a,b) = a|₀₁ − b|₀₁ = −w`, whence the images coincide as subgroups);
* `(d¹ n)_{(x₀,x₁,x₂)} = n_{(x₁,x₂)}| − n_{(x₀,x₂)}| + n_{(x₀,x₁)}|`.  The eight
  components force, after restriction (each triple intersection collapses to `U₀`, `U₁`
  or `U₀ ⊓ U₁`): the diagonals `p = s = 0` (from `x = (0,0,0)` and `(1,1,1)`) and
  `r = −q` (from `x = (0,1,0)` / `(1,0,1)`), the remaining four being automatic.  Hence
  `ker d¹ = { (0, q, −q, 0) : q ∈ Γ(U₀₁) } ≅ Γ(U₀₁)` via `q`.

Therefore `H¹ = ker d¹ / im d⁰ ≅ Γ(U₀ ⊓ U₁) / range (S.sectionDiff F) = H1Cok S F`, the
iso being `[(0, q, −q, 0)] ↦ [q]`.  The identification is **unconditional** (no
acyclicity hypothesis — it is a pure homological-algebra fact about this specific
2-cover complex); the only obstruction to formalising it is the grind of unfolding the
`FormalCoproduct`-based `cechComplexFunctor` down to the concrete `Pi.π`-components and
carrying out the 8-index kernel case-analysis with the `ULift (Fin 2)` bookkeeping.
This is queued for the next wave; the `coverFamily` / N6-bridge pieces here are the
scaffolding both sides of the equiv need.
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

/-! ## Node N5 — the concrete 2-element cover family of an `AffineCoverMVSquare` -/

/-- **The 2-element open cover family `𝒰 : ULift (Fin 2) → Opens X` of an
`AffineCoverMVSquare`.** Indexed by `ULift.{u} (Fin 2)` (the `Type u` two-element
index that `Scheme.cechCohomology`/`hModuleOne_linearEquiv_cechCohomology` consume),
it sends the first index to `U₁` and the second to `U₂`.  This is the family whose
Čech cohomology `cechCohomology C F S.coverFamily 1` is identified with the concrete
cokernel `H1Cok S F` (node N5 proper) and fed into the N6 bridge. -/
noncomputable def AffineCoverMVSquare.coverFamily {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    ULift.{u} (Fin 2) → TopologicalSpace.Opens X.toTopCat :=
  fun i => if i.down = 0 then S.U₁ else S.U₂

@[simp] lemma AffineCoverMVSquare.coverFamily_zero {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.coverFamily ⟨0⟩ = S.U₁ := rfl

@[simp] lemma AffineCoverMVSquare.coverFamily_one {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    S.coverFamily ⟨1⟩ = S.U₂ := rfl

/-- **Cover totality of `coverFamily`.** The 2-element family covers `X`:
`⨆ i, S.coverFamily i = ⊤`.  This is the `ι → Opens`-family incarnation of the
`AffineCoverMVSquare.cover` field `U₁ ⊔ U₂ = ⊤`, and is the hypothesis
`hModuleOne_linearEquiv_cechCohomology` requires to land the N6 bridge on the whole
curve. -/
lemma AffineCoverMVSquare.iSup_coverFamily {X : Scheme.{u}} (S : X.AffineCoverMVSquare) :
    ⨆ i, S.coverFamily i = ⊤ := by
  refine le_antisymm le_top ?_
  have h : S.U₁ ⊔ S.U₂ ≤ ⨆ i, S.coverFamily i :=
    sup_le (le_iSup_of_le ⟨0⟩ (le_of_eq S.coverFamily_zero.symm))
      (le_iSup_of_le ⟨1⟩ (le_of_eq S.coverFamily_one.symm))
  exact S.cover ▸ h

/-- **Node N6 bridge on the concrete 2-cover family.** The specialisation of
`hModuleOne_linearEquiv_cechCohomology` to `S.coverFamily`, discharging the totality
hypothesis with `iSup_coverFamily`: for a sheaf `F` of `k`-modules on the curve `C`
satisfying the Čech-to-derived comparison gate on the 2-affine cover, the
genus-degree cohomology `HModule k F n` is `k`-linearly identified with the Čech
cohomology `cechCohomology C F S.coverFamily n` of the concrete 2-element cover.
Chaining node N5's `cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F` into this (at
`n = 1`) delivers the lane's consumable `HModule k F 1 ≃ₗ[k] H1Cok S F`. -/
noncomputable def AffineCoverMVSquare.hModuleOne_linearEquiv_cechCohomology_coverFamily
    {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
    (S : C.left.AffineCoverMVSquare)
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasCechToHModuleIso F S.coverFamily]
    (n : ℕ) :
    HModule k F n ≃ₗ[k] cechCohomology C F S.coverFamily n :=
  hModuleOne_linearEquiv_cechCohomology F S.coverFamily S.iSup_coverFamily n

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

/-! ## Node N5 — concrete component formulas for the unnormalized Čech differential

The in-tree `cechCohomology C F 𝒰 n = (cechCochain C F 𝒰).homology n` is the homology of
Mathlib's unnormalized `cechComplexFunctor`, routed through
`FormalCoproduct.cochainComplexFunctor = cosimplicialObjectFunctor ⋙ alternatingCofaceMapComplex`.
There is no cosimplicial dual of `alternatingFaceMapComplex_obj_d` in Mathlib, so the concrete
`Pi.π`-component formulas for the differential are derived here directly by unfolding the
alternating coface sum.  These are the reusable foundation the degree-`1` identification
(`cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F`) is built on:

* `cechCosimplicial_δ_π` — the single-coface component
  `Yδᵢ ≫ πⱼ = π_{j∘δᵢ} ≫ (reindex restriction)`;
* `prodOpens_eq_iInf` — the abstract Čech product object `∏ᶜ (𝒰∘j)` is the concrete infimum
  `⨅ₐ 𝒰(j a)` of opens (equality in the poset `Opens X`), the bridge to `Γ(⨅ₐ Uₐ)`;
* `alternatingCofaceMapComplex_objD` — the differential is the alternating coface sum (the
  missing Mathlib dual);
* `cechCochain_d01_π` / `cechCochain_d12_π` — the degree-`0`/degree-`1` differentials,
  componentwise.
-/

section CechDifferential

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat)
  (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))

/-- **The alternating coface differential (Mathlib dual, project-local).** The degree-`n`
differential of `alternatingCofaceMapComplex` is the alternating sum of coface maps
`objD Y n = ∑ᵢ (-1)ⁱ • Yδᵢ`.  Mathlib has `alternatingFaceMapComplex_obj_d` but no cosimplicial
dual; this recreates it (the same one-line `CochainComplex.of` unfolding). -/
theorem alternatingCofaceMapComplex_objD {D : Type*} [Category D] [Preadditive D]
    (Y : CosimplicialObject D) (n : ℕ) :
    ((alternatingCofaceMapComplex D).obj Y).d n (n + 1)
      = AlternatingCofaceMapComplex.objD Y n := by
  simp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj, CochainComplex.of_d]

/-- The cosimplicial object underlying the Čech complex `cechCochain C F 𝒰`: it sends `⦋n⦌` to
`∏_{i : Fin (n+1) → ι} Γ(⨅ₐ 𝒰(i a), F)`.  `cechCochain C F 𝒰` is by definition
`alternatingCofaceMapComplex.obj (cechCosimplicial 𝒰 F)`. -/
noncomputable def cechCosimplicial : CosimplicialObject (ModuleCat.{u} k) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ 𝒰).cech).obj
    ((sheafToPresheaf _ _).obj F)

lemma cechCochain_eq :
    AlgebraicGeometry.Scheme.cechCochain C F 𝒰
      = (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (cechCosimplicial 𝒰 F) :=
  rfl

/-- **Single-coface component of the Čech cosimplicial object.** The `i₀`-th coface map
`Yδ_{i₀} : Č^n ⟶ Č^{n+1}`, projected to the factor indexed by `j : Fin (n+2) → ι`, is the factor
`j ∘ δ_{i₀}` of the source followed by the reindexing restriction
`Γ(⨅ₐ 𝒰(j(δ_{i₀} a))) ⟶ Γ(⨅ₐ 𝒰(j a))`.  Derived by unfolding
`cosimplicialObjectFunctor` (`evalOp` of the Čech nerve) and `Pi.lift ≫ Pi.π`. -/
theorem cechCosimplicial_δ_π (n : ℕ) (i₀ : Fin (n + 2)) (j : Fin (n + 2) → ι) :
    (cechCosimplicial 𝒰 F).δ i₀ ≫ Pi.π _ j
      = Pi.π _ (j ∘ (Fin.succAboveOrderEmb i₀)) ≫
          ((sheafToPresheaf _ _).obj F).map
            (Pi.lift (fun a => Pi.π ((FormalCoproduct.mk _ 𝒰).obj ∘ j)
              ((Fin.succAboveOrderEmb i₀) a))).op := by
  simp only [cechCosimplicial, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  erw [Limits.Pi.lift_π]
  rfl

/-- **The abstract Čech product is the concrete infimum of opens.** In the poset `Opens X` the
categorical product `∏ᶜ (𝒰∘j)` of the family `a ↦ 𝒰 (j a)` equals its infimum `⨅ₐ 𝒰 (j a)`.
This is the bridge identifying the Čech section groups `Γ(∏ᶜ 𝒰∘j, F)` with the concrete
`Γ(⨅ₐ 𝒰(j a), F)` (and, for the 2-cover, with `Γ(U₁ ⊓ U₂)`). -/
theorem prodOpens_eq_iInf {m : ℕ} (j : Fin m → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat)
      = ⨅ a, 𝒰 (j a) :=
  le_antisymm (le_iInf fun a => (Limits.Pi.π ((FormalCoproduct.mk _ 𝒰).obj ∘ j) a).le)
    (Limits.Pi.lift (fun a => homOfLE (iInf_le (fun a => 𝒰 (j a)) a))).le

/-- **Degree-`0` differential `d⁰` of the Čech complex as an alternating coface difference.**
`d⁰ = Yδ₀ − Yδ₁` (the two cofaces `Fin 1 → Fin 2` of the alternating sum). -/
theorem cechCochain_d01_eq :
    (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 0 1
      = (cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1 := by
  have h : (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 0 1
      = AlternatingCofaceMapComplex.objD (cechCosimplicial 𝒰 F) 0 :=
    alternatingCofaceMapComplex_objD (cechCosimplicial 𝒰 F) 0
  rw [h, AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  abel

/-- **Degree-`1` differential `d¹` of the Čech complex as an alternating coface sum.**
`d¹ = Yδ₀ − Yδ₁ + Yδ₂` (the three cofaces `Fin 2 → Fin 3` of the alternating sum). -/
theorem cechCochain_d12_eq :
    (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 1 2
      = (cechCosimplicial 𝒰 F).δ 0 - (cechCosimplicial 𝒰 F).δ 1 + (cechCosimplicial 𝒰 F).δ 2 := by
  have h : (AlgebraicGeometry.Scheme.cechCochain C F 𝒰).d 1 2
      = AlternatingCofaceMapComplex.objD (cechCosimplicial 𝒰 F) 1 :=
    alternatingCofaceMapComplex_objD (cechCosimplicial 𝒰 F) 1
  rw [h, AlternatingCofaceMapComplex.objD, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    Even.neg_pow, even_two]
  abel

end CechDifferential

end AlgebraicGeometry.Scheme
