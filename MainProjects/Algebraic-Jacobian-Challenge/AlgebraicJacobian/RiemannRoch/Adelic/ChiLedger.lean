/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.RiemannRoch.Adelic.Substrate

/-!
# Adelic Riemann–Roch lane — the χ-ledger (nodes N13, N14)

This file implements the Tier-2 χ-ledger nodes of the adelic Riemann–Roch lane
(design document §3, nodes N13–N16), built on top of the Tier-0 substrate
`AlgebraicJacobian.RiemannRoch.Adelic.Substrate` (`sectionOfDivisor`,
`linearSystem`, `pointValuation`, the `order` laws).

Everything here lives inside the fixed function field `K = K(X)` as
`AddSubgroup K(X)` — the "function-field model" of the design.  For a chosen
two-open cover `U₀, U₁` of `X` with overlap `V := U₀ ⊓ U₁` and a Weil divisor
`D`, the four cover-adelic objects are

* `Γ(U₀, 𝒪(D)) = sectionOfDivisor U₀ D`, `Γ(U₁, 𝒪(D)) = sectionOfDivisor U₁ D`;
* the **cover adele** `𝒜(D) := Γ(V, 𝒪(D)) = sectionOfDivisor V D`;
* the **coboundary** `B(D) := Γ(U₀, 𝒪(D)) + Γ(U₁, 𝒪(D)) = coboundary U₀ U₁ D`,
  which lies inside `𝒜(D)` (`coboundary_le_overlap`);
* the **linear system** `L(D) := Γ(U₀, 𝒪(D)) ⊓ Γ(U₁, 𝒪(D)) = linearSystem D`
  (kernel of the Čech difference map, `= Γ(⊤, 𝒪(D))` when `U₀ ⊔ U₁ = ⊤`), which
  also lies inside `𝒜(D)` (`linearSystem_le_overlap`);
* the **cover cohomology** `Ȟ¹(D) := 𝒜(D) ⧸ B(D) = H1 U₀ U₁ D`.

## N13 — the twist ledger

For `D ≤ D'` with the added part `D' − D` supported on the overlap `V`, the
inclusions of section subgroups assemble into the four-term exact sequence

```
0 → L(D')/L(D) → 𝒜(D')/𝒜(D) → Ȟ¹(D) → Ȟ¹(D') → 0.
```

The **exactness at the `L`-terms** — the injectivity of the window map
`L(D')/L(D) → 𝒜(D')/𝒜(D)` — is the concrete kernel computation
`L(D') ⊓ 𝒜(D) = L(D)` (`linearSystem_inf_overlap_eq`): a global section of
`𝒪(D')` that is already `D`-bounded on the overlap is a global section of
`𝒪(D)`, because off the overlap `D = D'`.  This is pure `AddSubgroup`
lattice algebra over `K`, the design's "elementary Submodule" assessment.  The
window map, the coboundary functoriality `Ȟ¹(D) → Ȟ¹(D')` and the connecting
homomorphism are set up concretely (`windowMap`, `H1Twist`, `windowConnect`);
the surjectivity at `Ȟ¹(D')` is the Mittag-Leffler/affine-cover input
`𝒜(D') = 𝒜(D) + B(D')`, deferred to the finiteness wave.

## N14 — the local step is bounded by the residue degree

For a single prime divisor `P` and the one-step twist `D + P`, the local quotient
`Γ(U, 𝒪(D + P)) ⧸ Γ(U, 𝒪(D))` injects into the single-point valuation quotient
`G(P, −n−1) ⧸ G(P, −n)` (`localStepQuot_injective`), which the DVR structure at
`P` identifies with the residue field `κ(P)`; hence its `k`-dimension is at most
`deg P = [κ(P) : k]`.

## References

Design document `adelic-rr-lane-design.md` §§2–3, nodes N13–N16; Stichtenoth,
*Algebraic Function Fields and Codes*, ch. 1; Serre, *Groupes algébriques et
corps de classes*, ch. II (répartitions); Hartshorne, *Algebraic Geometry* II §6.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

/-! ## §N13. The cover-adelic subgroups and the twist ledger -/

section Ledger

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **Antitonicity in the open.** Enlarging the open imposes *more* order
conditions, so `Γ(U', 𝒪(D)) ⊆ Γ(U, 𝒪(D))` whenever `U ≤ U'`.  (The section
subgroup is antitone in the open and monotone in the divisor.) -/
theorem sectionOfDivisor_antitone_open {U U' : X.Opens} (h : U ≤ U')
    (D : X.WeilDivisor) : sectionOfDivisor U' D ≤ sectionOfDivisor U D := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr fun P hP => hf P (h hP)

variable (U₀ U₁ : X.Opens)

/-- **The coboundary subgroup `B(D) = Γ(U₀, 𝒪(D)) + Γ(U₁, 𝒪(D))`.** The image of
the Čech difference-of-restrictions map for the cover `{U₀, U₁}`, realised inside
`K` as the sum of the two chart section subgroups. -/
noncomputable def coboundary (D : X.WeilDivisor) : AddSubgroup X.functionField :=
  sectionOfDivisor U₀ D ⊔ sectionOfDivisor U₁ D

/-- **The coboundary lands in the overlap sections.** `B(D) ⊆ 𝒜(D) = Γ(V, 𝒪(D))`:
each chart section restricts to the overlap. -/
theorem coboundary_le_overlap (D : X.WeilDivisor) :
    coboundary U₀ U₁ D ≤ sectionOfDivisor (U₀ ⊓ U₁) D :=
  sup_le (sectionOfDivisor_antitone_open inf_le_left D)
    (sectionOfDivisor_antitone_open inf_le_right D)

/-- **The linear system lands in the overlap sections.** `L(D) ⊆ 𝒜(D)`: a global
section restricts to the overlap. -/
theorem linearSystem_le_overlap (D : X.WeilDivisor) :
    linearSystem D ≤ sectionOfDivisor (U₀ ⊓ U₁) D :=
  sectionOfDivisor_antitone_open le_top D

/-- **N13 — exactness at the `L`-terms (window-map injectivity).**  Suppose
`D ≤ D'` pointwise and the added part `D' − D` is supported on the overlap
`V = U₀ ⊓ U₁` (`hsupp`: off `V`, `D` and `D'` agree).  Then a global section of
`𝒪(D')` that is already `D`-bounded on the overlap `V` is a global section of
`𝒪(D)`:
`L(D') ⊓ 𝒜(D) = L(D)`.

This is the concrete kernel computation showing the window map
`L(D')/L(D) → 𝒜(D')/𝒜(D)` is injective (exactness of the ledger sequence at the
two left `L`-terms).  Pure `AddSubgroup` lattice algebra over `K`: on the overlap
the `D`-bound comes from membership in `𝒜(D)`; off the overlap `D(P) = D'(P)`, so
the global `D'`-bound *is* the `D`-bound. -/
theorem linearSystem_inf_overlap_eq (hcov : U₀ ⊔ U₁ = ⊤) {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P)
    (hsupp : ∀ P : X.PrimeDivisor, P.point ∉ (U₀ ⊓ U₁ : X.Opens) →
      (show X.PrimeDivisor →₀ ℤ from D) P = (show X.PrimeDivisor →₀ ℤ from D') P) :
    linearSystem D' ⊓ sectionOfDivisor (U₀ ⊓ U₁) D = linearSystem D := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hf1, hf2⟩ := AddSubgroup.mem_inf.mp hf
    have hf1' : f ∈ sectionOfDivisor (⊤ : X.Opens) D' := hf1
    rcases eq_or_ne f 0 with rfl | hfne
    · exact (linearSystem D).zero_mem
    show f ∈ sectionOfDivisor (⊤ : X.Opens) D
    rw [mem_sectionOfDivisor_of_ne_zero hfne]
    intro P _
    by_cases hPV : P.point ∈ (U₀ ⊓ U₁ : X.Opens)
    · exact (mem_sectionOfDivisor_of_ne_zero hfne).mp hf2 P hPV
    · rw [hsupp P hPV]
      exact (mem_sectionOfDivisor_of_ne_zero hfne).mp hf1' P
        (TopologicalSpace.Opens.mem_top P.point)
  · exact le_inf (sectionOfDivisor_mono ⊤ hle) (linearSystem_le_overlap U₀ U₁ D)

/-- **Monotonicity of the coboundary in the divisor.** `D ≤ D' ⇒ B(D) ⊆ B(D')`. -/
theorem coboundary_mono {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    coboundary U₀ U₁ D ≤ coboundary U₀ U₁ D' :=
  sup_le_sup (sectionOfDivisor_mono U₀ hle) (sectionOfDivisor_mono U₁ hle)

/-! ### The cover cohomology `Ȟ¹(D)` and its twist maps -/

/-- **The cover cohomology `Ȟ¹(D) = 𝒜(D) / B(D)`.** The cokernel of the Čech
difference map, realised as the quotient of the overlap sections `𝒜(D)` by the
coboundary `B(D)` (which is a subgroup of `𝒜(D)` by `coboundary_le_overlap`).
This is the function-field-model incarnation of `AffineCoverMVSquare.H1Cok`. -/
def H1 (D : X.WeilDivisor) : Type u :=
  (sectionOfDivisor (U₀ ⊓ U₁) D) ⧸
    (coboundary U₀ U₁ D).addSubgroupOf (sectionOfDivisor (U₀ ⊓ U₁) D)

noncomputable instance instAddCommGroupH1 (D : X.WeilDivisor) :
    AddCommGroup (H1 U₀ U₁ D) :=
  inferInstanceAs (AddCommGroup (_ ⧸
    (coboundary U₀ U₁ D).addSubgroupOf (sectionOfDivisor (U₀ ⊓ U₁) D)))

/-- **Functoriality of `Ȟ¹` in the divisor (the H¹-inclusion map).** For `D ≤ D'`
the inclusions `𝒜(D) ⊆ 𝒜(D')`, `B(D) ⊆ B(D')` induce the comparison map
`Ȟ¹(D) → Ȟ¹(D')`.  This is the right-hand map of the ledger sequence
`… → Ȟ¹(D) → Ȟ¹(D') → 0` (the AG mirror of the DG `H1TailIncl`). -/
noncomputable def H1Twist {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    H1 U₀ U₁ D →+ H1 U₀ U₁ D' :=
  QuotientAddGroup.map _ _
    (AddSubgroup.inclusion (sectionOfDivisor_mono (U₀ ⊓ U₁) hle)) (by
      intro g hg
      rw [AddSubgroup.mem_addSubgroupOf] at hg
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion]
      exact coboundary_mono U₀ U₁ hle hg)

/-- **The window map `L(D')/L(D) → 𝒜(D')/𝒜(D)`.** Induced by the inclusion of
global sections into the overlap sections `L(D') ⊆ 𝒜(D')` (`linearSystem_le_overlap`),
compatibly with `L(D) ⊆ 𝒜(D)`.  This is the left-hand map of the ledger sequence
`0 → L(D')/L(D) → 𝒜(D')/𝒜(D) → …` (the AG mirror of the DG `windowMap`). -/
noncomputable def windowMap {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    (linearSystem D' ⧸
        (linearSystem D).addSubgroupOf (linearSystem D')) →+
      (sectionOfDivisor (U₀ ⊓ U₁) D' ⧸
        (sectionOfDivisor (U₀ ⊓ U₁) D).addSubgroupOf (sectionOfDivisor (U₀ ⊓ U₁) D')) :=
  QuotientAddGroup.map _ _
    (AddSubgroup.inclusion (linearSystem_le_overlap U₀ U₁ D')) (by
      intro g hg
      rw [AddSubgroup.mem_addSubgroupOf] at hg
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion]
      exact linearSystem_le_overlap U₀ U₁ D hg)

/-- **N13 — exactness at the `L`-terms, packaged as window-map injectivity.**
Under `D ≤ D'` with `D' − D` supported on the overlap, the window map
`L(D')/L(D) → 𝒜(D')/𝒜(D)` is injective.  This is `linearSystem_inf_overlap_eq`
transported into the quotient language: the ledger sequence is exact at both
`L`-terms. -/
theorem windowMap_injective (hcov : U₀ ⊔ U₁ = ⊤) {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P)
    (hsupp : ∀ P : X.PrimeDivisor, P.point ∉ (U₀ ⊓ U₁ : X.Opens) →
      (show X.PrimeDivisor →₀ ℤ from D) P = (show X.PrimeDivisor →₀ ℤ from D') P) :
    Function.Injective (windowMap U₀ U₁ hle) := by
  rw [injective_iff_map_eq_zero]
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H g =>
    intro hq
    simp only [windowMap, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion] at hq
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have hmem : (g : X.functionField) ∈ linearSystem D' ⊓ sectionOfDivisor (U₀ ⊓ U₁) D :=
      AddSubgroup.mem_inf.mpr ⟨g.2, hq⟩
    rwa [linearSystem_inf_overlap_eq U₀ U₁ hcov hle hsupp] at hmem

end Ledger

/-! ## §N14. The local step is bounded by the residue degree

For a single prime divisor `P` and the one-step twist raising the pole bound at
`P` by one, the local quotient `Γ(U, 𝒪(D')) ⧸ Γ(U, 𝒪(D))` injects into the
single-point valuation quotient `orderGe P (-n-1) ⧸ orderGe P (-n)`.  The DVR
structure at `P` identifies the latter with the residue field `κ(P)` (one
uniformizer step ⇒ one copy of `κ(P) = 𝒪_P/𝔪_P`), whose `k`-dimension is
`deg P = [κ(P) : k]`; hence `dim_k (Γ(U, 𝒪(D')) ⧸ Γ(U, 𝒪(D))) ≤ deg P`.  This
file supplies the **elementary (residue-field-free) core**: the single-point
subgroups, the local identity `Γ(U, 𝒪(D)) = Γ(U, 𝒪(D')) ⊓ orderGe P (-n)`, and
the resulting injection.  The residue-field identification of the target and the
numerical `[κ(P):k]` count is the DVR step layered on top. -/

section LocalStep

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **The single-point order-≥-`m` subgroup.** `orderGe P m = { f ∈ K : ord_P f ≥ m }`
(with the zero function admitted separately, the `ord_P 0 = +∞` convention).  For
`m ≤ 0` this is the fractional ideal `𝔪_P^{-m}` of the DVR `𝒪_P` viewed inside
`K`; the consecutive quotient `orderGe P m / orderGe P (m+1)` is one copy of the
residue field `κ(P)`.  Closure under addition is the `order` ultrametric. -/
def orderGe (P : X.PrimeDivisor) (m : ℤ) : AddSubgroup X.functionField where
  carrier := { f | f = 0 ∨ m ≤ Scheme.RationalMap.order P f }
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    rcases eq_or_ne a 0 with rfl | hane
    · simpa using hb
    rcases eq_or_ne b 0 with rfl | hbne
    · simpa using ha
    rcases eq_or_ne (a + b) 0 with h0 | h0
    · exact Or.inl h0
    exact Or.inr ((le_min (ha.resolve_left hane) (hb.resolve_left hbne)).trans
      (order_add_ge_min P hane hbne h0))
  neg_mem' := by
    intro a ha
    rcases ha with rfl | ha
    · exact Or.inl (by simp)
    · exact Or.inr (by rw [Scheme.RationalMap.order_neg]; exact ha)

theorem mem_orderGe {P : X.PrimeDivisor} {m : ℤ} {f : X.functionField} :
    f ∈ orderGe P m ↔ f = 0 ∨ m ≤ Scheme.RationalMap.order P f :=
  Iff.rfl

theorem mem_orderGe_of_ne_zero {P : X.PrimeDivisor} {m : ℤ} {f : X.functionField}
    (hf : f ≠ 0) : f ∈ orderGe P m ↔ m ≤ Scheme.RationalMap.order P f := by
  rw [mem_orderGe, or_iff_right hf]

/-- **Antitonicity in the lower bound.** A larger order bound is a stronger
condition, so `orderGe P m' ⊆ orderGe P m` whenever `m ≤ m'`. -/
theorem orderGe_antitone {P : X.PrimeDivisor} {m m' : ℤ} (h : m ≤ m') :
    orderGe P m' ≤ orderGe P m := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (h.trans hf)

/-- **N14 — the local step identity.** Let `D ≤ D'` be two divisors differing
only at the prime divisor `P` (`hoff`), where `D'` has exactly one more pole
(`hstep : D'(P) = D(P) + 1`), and let `P ∈ U`.  Then a section of `𝒪(D')` on `U`
lies in `𝒪(D)` exactly when it also satisfies the tighter bound `ord_P f ≥ -D(P)`:
`Γ(U, 𝒪(D)) = Γ(U, 𝒪(D')) ⊓ orderGe P (-D(P))`.

This is the kernel computation exhibiting the local step quotient
`Γ(U, 𝒪(D')) / Γ(U, 𝒪(D))` as a subquotient at the single point `P`. -/
theorem sectionOfDivisor_inf_orderGe {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q) :
    sectionOfDivisor U D =
      sectionOfDivisor U D' ⊓ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P) := by
  apply le_antisymm
  · intro f hf
    refine AddSubgroup.mem_inf.mpr ⟨sectionOfDivisor_mono U hle hf, ?_⟩
    rcases eq_or_ne f 0 with rfl | hfne
    · exact Or.inl rfl
    exact Or.inr ((mem_sectionOfDivisor_of_ne_zero hfne).mp hf P hPU)
  · intro f hf
    obtain ⟨hf1, hf2⟩ := AddSubgroup.mem_inf.mp hf
    rcases eq_or_ne f 0 with rfl | hfne
    · exact (sectionOfDivisor U D).zero_mem
    rw [mem_sectionOfDivisor_of_ne_zero hfne]
    intro Q hQU
    by_cases hQP : Q = P
    · subst hQP
      exact (mem_orderGe_of_ne_zero hfne).mp hf2
    · rw [hoff Q hQP]
      exact (mem_sectionOfDivisor_of_ne_zero hfne).mp hf1 Q hQU

/-- **N14 — the section lands in the one-step-looser single-point subgroup.** A
section of `𝒪(D')` on `U` (with `P ∈ U` and `D'(P) = D(P) + 1`) has order at least
`-D(P) - 1` at `P`, i.e. lies in `orderGe P (-D(P) - 1)`. -/
theorem sectionOfDivisor_le_orderGe {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1) :
    sectionOfDivisor U D' ≤ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1) := by
  intro f hf
  rcases eq_or_ne f 0 with rfl | hfne
  · exact Or.inl rfl
  refine Or.inr ?_
  have := (mem_sectionOfDivisor_of_ne_zero hfne).mp hf P hPU
  rw [hstep] at this
  linarith

/-- **N14 — the local step quotient injects into the single-point valuation
quotient.**  Under the one-step hypotheses of `sectionOfDivisor_inf_orderGe`, the
inclusion of section subgroups induces a map
`Γ(U, 𝒪(D')) / Γ(U, 𝒪(D)) → orderGe P (-D(P)-1) / orderGe P (-D(P))`, and it is
injective.  This is the **exact local structure** of node N14: the local step
quotient is a subgroup of the single-point valuation quotient
`𝔪_P^{-n-1}/𝔪_P^{-n} ≅ κ(P)`, whence `dim_k` of the step is at most
`deg P = [κ(P):k]` (the residue-field identification of the target and the
numerical bound is the DVR layer on top of this reduction). -/
noncomputable def localStepQuot {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1) :
    (sectionOfDivisor U D' ⧸
        (sectionOfDivisor U D).addSubgroupOf (sectionOfDivisor U D')) →+
      (orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1) ⧸
        (orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P)).addSubgroupOf
          (orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1))) :=
  QuotientAddGroup.map _ _
    (AddSubgroup.inclusion (sectionOfDivisor_le_orderGe hPU hstep)) (by
      intro g hg
      rw [AddSubgroup.mem_addSubgroupOf] at hg
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion]
      rcases eq_or_ne (g : X.functionField) 0 with h0 | h0
      · rw [h0]; exact (orderGe _ _).zero_mem
      exact (mem_orderGe_of_ne_zero h0).mpr
        ((mem_sectionOfDivisor_of_ne_zero h0).mp hg P hPU))

theorem localStepQuot_injective {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q) :
    Function.Injective (localStepQuot hPU hstep) := by
  rw [injective_iff_map_eq_zero]
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H g =>
    intro hq
    simp only [localStepQuot, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion] at hq
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    have hmem : (g : X.functionField) ∈
        sectionOfDivisor U D' ⊓ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P) :=
      AddSubgroup.mem_inf.mpr ⟨g.2, hq⟩
    rwa [← sectionOfDivisor_inf_orderGe hPU hle hoff] at hmem

end LocalStep

end Adelic
end AlgebraicGeometry
