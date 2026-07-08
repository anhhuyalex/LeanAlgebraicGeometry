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

/-! ## §N14b. The residue-degree bound on the local step

The `LocalStep` section reduced the local step quotient to the single-point
valuation quotient `orderGe P m ⧸ orderGe P (m+1)` (with `m = -n-1`).  We now
identify this target with the residue field `κ(P)` of the DVR stalk `𝒪_P` and
read off the numerical bound `dim_k ≤ deg P = [κ(P) : k]`.

The DVR bridges below connect the additive order `ord_P = -log ∘ v_P` to
integrality in the stalk `𝒪_P = 𝒪_{X,P}`: a nonzero rational function has
nonnegative order at `P` exactly when it is a section of the stalk. -/

section LocalDegree

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **Order-nonnegativity is stalk-integrality.** For a nonzero rational function
`f`, `ord_P f ≥ 0` exactly when `f` lifts to the DVR stalk `𝒪_P = 𝒪_{X,P}`, i.e.
`f = a` for some `a ∈ 𝒪_P` (viewed in `K` via the fraction-field embedding). This
is the additive-normalisation reading of `v_P(f) ≤ 1 ⟺ f ∈ 𝒪_P`. -/
theorem exists_stalk_lift_of_order_nonneg {P : X.PrimeDivisor}
    {f : X.functionField} (hf : f ≠ 0)
    (hord : 0 ≤ Scheme.RationalMap.order P f) :
    ∃ a : X.presheaf.stalk P.point,
      algebraMap (X.presheaf.stalk P.point) X.functionField a = f := by
  have hpv : pointValuation P f ≠ 0 := by
    simpa using (Valuation.zero_iff (pointValuation P)).not.mpr hf
  have hlog : WithZero.log (pointValuation P f) ≤ 0 := by
    have := order_eq_neg_log_pointValuation P f
    rw [this] at hord; linarith
  have hle1 : pointValuation P f ≤ 1 := by
    have : WithZero.log (pointValuation P f) ≤ WithZero.log (1 : ℤᵐ⁰) := by
      simpa using hlog
    exact (WithZero.log_le_log hpv one_ne_zero).mp this
  exact IsDiscreteValuationRing.exists_lift_of_le_one hle1

/-- **Order surjectivity: every integer is realised as an order at `P`.**  The DVR
stalk `𝒪_P` has a uniformizer `π` with `ord_P π = 1` — the maximal-ideal
height-one place, whose adic valuation is `exp (-1)` (mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`) — and its integer
powers `π^j` realise every order `j : ℤ`.  This is the surjectivity of
`ord_P : K(X) → ℤ`; only the intrinsic order value of the DVR uniformizer is used,
never a distinguished *global* uniformizer (a fixed rational function). -/
theorem exists_order_eq (P : X.PrimeDivisor) (j : ℤ) :
    ∃ t : X.functionField, t ≠ 0 ∧ Scheme.RationalMap.order P t = j := by
  obtain ⟨π, hπ⟩ :=
    (IsDiscreteValuationRing.maximalIdeal
      (X.presheaf.stalk P.point)).valuation_exists_uniformizer X.functionField
  have hval : pointValuation P π = WithZero.exp (-1 : ℤ) := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  refine ⟨π ^ j, zpow_ne_zero j hπ0, ?_⟩
  rw [order_eq_neg_log_pointValuation, map_zpow₀, hval, WithZero.log_zpow,
    WithZero.log_exp, smul_eq_mul]
  ring

end LocalDegree

/-! ## §N14c/N15/N16. The `k`-linear χ-ledger over a field of constants

The dimension count of the χ-ledger lives over a base field `k` of constants:
`k ↪ K(X)` with every nonzero constant a unit at every prime (order `0`
everywhere).  Under this hypothesis the section subgroups and single-point
subgroups are `k`-subspaces, their subquotients are finite-dimensional `k`-vector
spaces (gated by the keystone/finiteness inputs as `[Module.Finite k …]`
binders), and the twist ledger telescopes numerically.

`k` is the **field of constants** of the curve — algebraically the elements of
`K(X)` integral over the ground field and regular at every point; on a smooth
proper curve over an algebraically closed `k̄` this is `k̄` itself.  We package the
"constants are everywhere-unit" property as the gate `IsConstantField`. -/

section BaseField

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField]

/-- **Field-of-constants gate.** Every nonzero constant `c ∈ k ⊆ K(X)` is a unit
at every prime divisor `P`, i.e. `ord_P c = 0`.  This is the property that makes
`k` a field of constants: constants have neither zeros nor poles.  On a smooth
proper curve over `k̄`, with `k = k̄`, it holds because a nonzero constant is a
unit in every local ring.  No global instance — an honest gate supplied at use
sites (design §4, mirroring `HasDedekindChart`). -/
class IsConstantField (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] : Prop where
  /-- Nonzero constants have order zero at every prime divisor. -/
  order_algebraMap_eq_zero : ∀ (P : X.PrimeDivisor) (c : k), c ≠ 0 →
    Scheme.RationalMap.order P (algebraMap k X.functionField c) = 0

variable [IsConstantField k X]

/-- **The section subspace `Γ(U, 𝒪(D))` as a `k`-vector space.** With `k` a field
of constants, the additive section subgroup `sectionOfDivisor U D` is closed under
multiplication by constants, hence a `k`-submodule of `K(X)`. -/
def sectionSub (U : X.Opens) (D : X.WeilDivisor) : Submodule k X.functionField where
  carrier := sectionOfDivisor U D
  add_mem' := (sectionOfDivisor U D).add_mem
  zero_mem' := (sectionOfDivisor U D).zero_mem
  smul_mem' c f hf := by
    rw [Algebra.smul_def]
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using (sectionOfDivisor U D).zero_mem
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using (sectionOfDivisor U D).zero_mem
    refine Or.inr fun P hP => ?_
    rw [Scheme.RationalMap.order_mul_of_ne_zero P
        (by simpa using (map_ne_zero (algebraMap k X.functionField)).mpr hc) hf0,
      IsConstantField.order_algebraMap_eq_zero P c hc, zero_add]
    exact (mem_sectionOfDivisor_of_ne_zero hf0).mp hf P hP

/-- **The single-point subspace `orderGe P m` as a `k`-vector space.** -/
def orderGeSub (P : X.PrimeDivisor) (m : ℤ) : Submodule k X.functionField where
  carrier := orderGe P m
  add_mem' := (orderGe P m).add_mem
  zero_mem' := (orderGe P m).zero_mem
  smul_mem' c f hf := by
    rw [Algebra.smul_def]
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using (orderGe P m).zero_mem
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using (orderGe P m).zero_mem
    refine Or.inr ?_
    rw [Scheme.RationalMap.order_mul_of_ne_zero P
        (by simpa using (map_ne_zero (algebraMap k X.functionField)).mpr hc) hf0,
      IsConstantField.order_algebraMap_eq_zero P c hc, zero_add]
    exact (mem_orderGe_of_ne_zero hf0).mp hf

@[simp] theorem mem_sectionSub {U : X.Opens} {D : X.WeilDivisor}
    {f : X.functionField} : f ∈ sectionSub k U D ↔ f ∈ sectionOfDivisor U D := Iff.rfl

@[simp] theorem mem_orderGeSub {P : X.PrimeDivisor} {m : ℤ} {f : X.functionField} :
    f ∈ orderGeSub k P m ↔ f ∈ orderGe P m := Iff.rfl

/-- **Monotonicity of `sectionSub` in the divisor.** -/
theorem sectionSub_mono (U : X.Opens) {D D' : X.WeilDivisor}
    (h : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    sectionSub k U D ≤ sectionSub k U D' :=
  fun _ hx => sectionOfDivisor_mono U h hx

/-- **The local step `k`-vector space `Γ(U, 𝒪(D')) ⧸ Γ(U, 𝒪(D))`.** The relative
quotient of the two section subspaces; this is `ℓ(D')/ℓ(D)`-space whose dimension
the χ-ledger telescopes. -/
abbrev localStepDom (U : X.Opens) (D D' : X.WeilDivisor) : Type u :=
  ↥(sectionSub k U D') ⧸ Submodule.comap (sectionSub k U D').subtype (sectionSub k U D)

/-- **The single-point valuation subquotient `orderGe P (m-1) ⧸ orderGe P m`.**
By the DVR structure at `P` this one-uniformizer-step quotient is a copy of the
residue field `κ(P) = 𝒪_P/𝔪_P` (antitone convention: `orderGe P m ⊆ orderGe P (m-1)`). -/
abbrev localStepTgt (P : X.PrimeDivisor) (m : ℤ) : Type u :=
  ↥(orderGeSub k P (m - 1)) ⧸
    Submodule.comap (orderGeSub k P (m - 1)).subtype (orderGeSub k P m)

/-- **The `k`-linear local step map.** The `k`-linear upgrade of `localStepQuot`:
induced by the inclusion `Γ(U, 𝒪(D')) ⊆ orderGe P (-D(P)-1)` on the relative
quotients, mapping the local step subquotient
`Γ(U, 𝒪(D')) ⧸ Γ(U, 𝒪(D))` `k`-linearly into `orderGe P (-D(P)-1) ⧸ orderGe P (-D(P))`. -/
noncomputable def localStepMapₖ {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1) :
    localStepDom k U D D' →ₗ[k]
      localStepTgt k P (-(show X.PrimeDivisor →₀ ℤ from D) P) :=
  Submodule.mapQ _ _
    (Submodule.inclusion (fun x hx => sectionOfDivisor_le_orderGe hPU hstep hx)) (by
      intro g hg
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_sectionSub] at hg
      rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.coe_inclusion, mem_orderGeSub]
      rcases eq_or_ne (g : X.functionField) 0 with h0 | h0
      · rw [h0]; exact (orderGe _ _).zero_mem
      exact (mem_orderGe_of_ne_zero h0).mpr
        ((mem_sectionOfDivisor_of_ne_zero h0).mp hg P hPU))

/-- **The `k`-linear local step map is injective** (N14 — `k`-linear form). The
kernel computation `Γ(U, 𝒪(D)) = Γ(U, 𝒪(D')) ⊓ orderGe P (-D(P))`
(`sectionOfDivisor_inf_orderGe`) transported to the relative quotients. -/
theorem localStepMapₖ_injective {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q) :
    Function.Injective (localStepMapₖ k hPU hstep) := by
  rw [injective_iff_map_eq_zero]
  intro q
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  intro hq
  rw [localStepMapₖ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion,
    mem_orderGeSub] at hq
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
    mem_sectionSub]
  have hmem : (g : X.functionField) ∈
      sectionOfDivisor U D' ⊓ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P) :=
    AddSubgroup.mem_inf.mpr ⟨g.2, hq⟩
  rwa [← sectionOfDivisor_inf_orderGe hPU hle hoff] at hmem

/-- **N14 — the local step dimension is at most the residue degree.**  Given the
DVR residue-field identification of the single-point valuation quotient — packaged
as a `k`-linear embedding `ι : orderGe P (-D(P)-1) ⧸ orderGe P (-D(P)) ↪ V` into a
finite-dimensional `k`-vector space `V` (with `V = κ(P)` and
`dim_k V = deg P = [κ(P):k]` at the use site) — the local step space
`Γ(U, 𝒪(D')) ⧸ Γ(U, 𝒪(D))` has `k`-dimension at most `dim_k V`.

The proof composes the two injections `Γ(U,𝒪(D'))/Γ(U,𝒪(D)) ↪ κ(P)-target ↪ V`:
`localStepMapₖ_injective` (the elementary kernel computation) and the residue
embedding `ι` (the DVR layer), reading off the `finrank` inequality.  The residue
finiteness `Module.Finite k V` is the gated keystone input (`[κ(P):k] < ∞` for a
closed point of a finite-type curve), not re-proved here. -/
theorem localStep_finrank_le_residueEmbedding {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q)
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ι : localStepTgt k P (-(show X.PrimeDivisor →₀ ℤ from D) P) →ₗ[k] V)
    (hι : Function.Injective ι) :
    Module.finrank k (localStepDom k U D D') ≤ Module.finrank k V := by
  haveI : Module.Finite k (localStepTgt k P (-(show X.PrimeDivisor →₀ ℤ from D) P)) :=
    Module.Finite.of_injective ι hι
  refine (LinearMap.finrank_le_finrank_of_injective
    (localStepMapₖ_injective k hPU hstep hle hoff)).trans ?_
  exact LinearMap.finrank_le_finrank_of_injective hι

/-! ### N14b — the residue field `κ(P)` and the residue-degree bound

`localStepTgt k P 1 = orderGe P 0 ⧸ orderGe P 1` is the DVR residue field
`κ(P) = 𝒪_P/𝔪_P`, realised as a `k`-subquotient of `K(X)`; its `k`-dimension is the
residue degree `deg P = [κ(P) : k]`.  For any `m`, multiplication by a rational
function `t` with `ord_P t = 1 - m` (which exists by `exists_order_eq` — the
intrinsic uniformizer-power order, *no* distinguished global uniformizer) carries
`orderGe P (m-1)` into `orderGe P 0` and `orderGe P m` into `orderGe P 1`, hence
descends to the `k`-linear embedding `localStepTgt k P m ↪ κ(P)`.  Feeding it to
`localStep_finrank_le_residueEmbedding` completes node N14:
`dim_k (Γ(U,𝒪(D')) / Γ(U,𝒪(D))) ≤ deg P`. -/

/-- **The residue degree `deg P := [κ(P) : k] = dim_k κ(P)`**, with the residue
field `κ(P) = 𝒪_P/𝔪_P` realised as the single-uniformizer-step valuation quotient
`localStepTgt k P 1 = orderGe P 0 ⧸ orderGe P 1`. -/
noncomputable def residueDeg (P : X.PrimeDivisor) : ℕ :=
  Module.finrank k (localStepTgt k P 1)

/-- **The residue embedding `ι`** completing node N14.  Multiplication by a
rational function `t` of order `1 - m` at `P` carries `orderGe P (m-1)` into
`orderGe P 0` and `orderGe P m` into `orderGe P 1`, hence descends to the
`k`-linear map `localStepTgt k P m → κ(P) = localStepTgt k P 1` between single-point
valuation quotients — the uniformizer-power shift of the fractional-ideal
filtration.  `k`-linearity is automatic: multiplication by a fixed element of
`K(X)` commutes with the `k`-action. -/
noncomputable def residueShift {P : X.PrimeDivisor} {m : ℤ}
    (t : X.functionField) (ht : t ≠ 0)
    (hc : Scheme.RationalMap.order P t = 1 - m) :
    localStepTgt k P m →ₗ[k] localStepTgt k P 1 :=
  Submodule.mapQ _ _
    (LinearMap.restrict (LinearMap.mulLeft k t)
      (p := orderGeSub k P (m - 1)) (q := orderGeSub k P (1 - 1))
      (fun x hx => by
        rw [mem_orderGeSub] at hx
        rw [LinearMap.mulLeft_apply, mem_orderGeSub]
        rcases eq_or_ne x 0 with hx0 | hx0
        · exact Or.inl (by rw [hx0, mul_zero])
        · exact Or.inr (by
            rw [Scheme.RationalMap.order_mul_of_ne_zero P ht hx0, hc]
            have := (mem_orderGe_of_ne_zero hx0).mp hx
            linarith)))
    (by
      intro x hx
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_orderGeSub] at hx
      rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.coe_restrict_apply, LinearMap.mulLeft_apply, mem_orderGeSub]
      rcases eq_or_ne (x : X.functionField) 0 with hx0 | hx0
      · exact Or.inl (by rw [hx0, mul_zero])
      · exact Or.inr (by
          rw [Scheme.RationalMap.order_mul_of_ne_zero P ht hx0, hc]
          have := (mem_orderGe_of_ne_zero hx0).mp hx
          linarith))

/-- **The residue embedding is injective** (node N14, `k`-linear residue form).
If `t · f` lands in `orderGe P 1` then `ord_P(t·f) = (1-m) + ord_P f ≥ 1`, hence
`ord_P f ≥ m` and `f ∈ orderGe P m`: the kernel of the shift is exactly the tighter
single-point subgroup, so the induced map on the local step quotient is injective. -/
theorem residueShift_injective {P : X.PrimeDivisor} {m : ℤ}
    (t : X.functionField) (ht : t ≠ 0)
    (hc : Scheme.RationalMap.order P t = 1 - m) :
    Function.Injective (residueShift k t ht hc) := by
  rw [injective_iff_map_eq_zero]
  intro q
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  intro hq
  rw [residueShift, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply,
    LinearMap.mulLeft_apply, mem_orderGeSub] at hq
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
    mem_orderGeSub]
  rcases eq_or_ne (g : X.functionField) 0 with hg0 | hg0
  · rw [hg0]; exact (orderGe P m).zero_mem
  · refine Or.inr ?_
    rcases hq with h0 | h0
    · exact absurd ((mul_eq_zero.mp h0).resolve_left ht) hg0
    · rw [Scheme.RationalMap.order_mul_of_ne_zero P ht hg0, hc] at h0
      linarith

/-- **The residue embedding is surjective** (node N14, `k`-linear residue form).
Multiplication by the intrinsic uniformizer power `t` (order `1 - m` at `P`) is a
bijection of `K(X)` — inverse multiplication by `t⁻¹` — carrying `orderGe P (m-1)`
*onto* `orderGe P 0` and `orderGe P m` onto `orderGe P 1`.  Hence the descended map
`residueShift` is surjective: an isomorphism
`orderGe P (m-1)/orderGe P m ≅ κ(P) = orderGe P 0/orderGe P 1`. -/
theorem residueShift_surjective {P : X.PrimeDivisor} {m : ℤ}
    (t : X.functionField) (ht : t ≠ 0)
    (hc : Scheme.RationalMap.order P t = 1 - m) :
    Function.Surjective (residueShift k t ht hc) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hmem : t⁻¹ * (y : X.functionField) ∈ orderGe P (m - 1) := by
    rcases eq_or_ne (y : X.functionField) 0 with hy0 | hy0
    · rw [hy0, mul_zero]; exact (orderGe P (m - 1)).zero_mem
    · refine (mem_orderGe_of_ne_zero (mul_ne_zero (inv_ne_zero ht) hy0)).mpr ?_
      have hy : (1 - 1 : ℤ) ≤ Scheme.RationalMap.order P (y : X.functionField) :=
        (mem_orderGe_of_ne_zero hy0).mp y.2
      rw [Scheme.RationalMap.order_mul_of_ne_zero P (inv_ne_zero ht) hy0,
        Scheme.RationalMap.order_inv, hc]
      linarith
  refine ⟨Submodule.Quotient.mk ⟨t⁻¹ * (y : X.functionField),
    (mem_orderGeSub k).mpr hmem⟩, ?_⟩
  rw [residueShift, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  rw [LinearMap.coe_restrict_apply, LinearMap.mulLeft_apply]
  exact mul_inv_cancel_left₀ ht _

/-- **The single-point valuation quotient has dimension `deg P` for every shift.**
Multiplication by an intrinsic uniformizer power intertwines the steps of the
fractional-ideal filtration, so every one-step valuation quotient
`orderGe P (m-1)/orderGe P m` is `k`-isomorphic to the residue field
`κ(P) = orderGe P 0/orderGe P 1`; hence they all share the residue degree
`deg P = [κ(P):k]`.  (`residueShift` is a bijection: injective by
`residueShift_injective`, surjective by `residueShift_surjective`.) -/
theorem finrank_localStepTgt (P : X.PrimeDivisor) (m : ℤ) :
    Module.finrank k (localStepTgt k P m) = residueDeg k P := by
  obtain ⟨t, ht, htord⟩ := exists_order_eq P (1 - m)
  rw [residueDeg]
  exact (LinearEquiv.ofBijective (residueShift k t ht htord)
    ⟨residueShift_injective k t ht htord, residueShift_surjective k t ht htord⟩).finrank_eq

/-- **N14 — the local step dimension is at most the residue degree.**  For the
one-point twist `D' = D + P` (with `P ∈ U`, `D'(P) = D(P) + 1`, `D = D'` off `P`)
the local step space `Γ(U, 𝒪(D')) / Γ(U, 𝒪(D))` has `k`-dimension at most the
residue degree `deg P = [κ(P) : k]`.  This is the honest conclusion of N14: the
composite of the elementary kernel injection (`localStepMapₖ_injective`) with the
uniformizer-power residue embedding (`residueShift_injective`).  The finiteness of
`κ(P)` over `k` — `[κ(P):k] < ∞`, the residue field of a closed point of a
finite-type `k`-curve — is the gated keystone input `[Module.Finite k κ(P)]`, not
re-proved here. -/
theorem localStep_finrank_le {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q)
    [Module.Finite k (localStepTgt k P 1)] :
    Module.finrank k (localStepDom k U D D') ≤ residueDeg k P := by
  obtain ⟨t, ht, htord⟩ :=
    exists_order_eq P (1 - (-(show X.PrimeDivisor →₀ ℤ from D) P))
  exact localStep_finrank_le_residueEmbedding k hPU hstep hle hoff
    (residueShift k t ht htord) (residueShift_injective k t ht htord)

/-! ### N14 (equality direction) — the residue map is onto: strong approximation

The `≤` bound above is the elementary half.  The reverse — that the local step space
`Γ(U,𝒪(D'))/Γ(U,𝒪(D))` fills *all* of the residue field `κ(P)` — is the surjectivity
of the local residue map, i.e. the **strong/weak-approximation** input: any prescribed
residue at `P` (any `y` with `ord_P y ≥ -n-1`) is realised, to residue precision at
`P` (modulo `orderGe P (-n)`), by a global-on-`U` section of `𝒪(D')`.  We take this
existence as the honest hypothesis `hsurj` (discharged at the use site from the
Dedekind-chart CRT / weak approximation for the finitely many constraint places), and
from it obtain the local isomorphism and the exact dimension count `= deg P`. -/

/-- **N14 (equality direction) — the `k`-linear local step map is surjective.**  Given
the strong-approximation existence hypothesis `hsurj` — every rational function of
order `≥ -n-1` at `P` is matched, modulo `orderGe P (-n)` (to residue precision at
`P`), by a section of `𝒪(D')` on `U` — the residue map
`Γ(U,𝒪(D'))/Γ(U,𝒪(D)) → orderGe P (-n-1)/orderGe P (-n)` is onto. -/
theorem localStepMapₖ_surjective {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hsurj : ∀ y : X.functionField,
        y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1) →
        ∃ f ∈ sectionOfDivisor U D',
          f - y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P)) :
    Function.Surjective (localStepMapₖ k hPU hstep) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨f, hf, hfy⟩ := hsurj (y : X.functionField) ((mem_orderGeSub k).mp y.2)
  refine ⟨Submodule.Quotient.mk ⟨f, (mem_sectionSub k).mpr hf⟩, ?_⟩
  rw [localStepMapₖ, Submodule.mapQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    Submodule.subtype_apply, AddSubgroupClass.coe_sub, Submodule.coe_inclusion,
    mem_orderGeSub]
  exact hfy

/-- **N14 (equality direction) — the local step has dimension exactly `deg P`.**  Under
the strong-approximation surjectivity `hsurj`, the `k`-linear local step map
`Γ(U,𝒪(D'))/Γ(U,𝒪(D)) → orderGe P (-n-1)/orderGe P (-n)` is bijective (injective by
`localStepMapₖ_injective`, surjective by `localStepMapₖ_surjective`), so the local step
space is `k`-isomorphic to the single-point valuation quotient, whose dimension is the
residue degree (`finrank_localStepTgt`):
`dim_k(Γ(U,𝒪(D'))/Γ(U,𝒪(D))) = deg P = [κ(P):k]`.  This is the exact one-point count
underlying `χ(D+P) = χ(D) + deg P`; no finiteness gate is needed (a linear equivalence,
whose `finrank` equality is unconditional). -/
theorem localStep_finrank_eq {U : X.Opens} {P : X.PrimeDivisor}
    (hPU : P.point ∈ U) {D D' : X.WeilDivisor}
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hsurj : ∀ y : X.functionField,
        y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1) →
        ∃ f ∈ sectionOfDivisor U D',
          f - y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P)) :
    Module.finrank k (localStepDom k U D D') = residueDeg k P := by
  rw [(LinearEquiv.ofBijective (localStepMapₖ k hPU hstep)
      ⟨localStepMapₖ_injective k hPU hstep hle hoff,
        localStepMapₖ_surjective k hPU hstep hsurj⟩).finrank_eq,
    finrank_localStepTgt]

end BaseField

/-! ## §N15 backbone. The 4-term exact-sequence alternating dimension identity

The χ-additivity of the twist ledger is the alternating-dimension identity of the
four-term exact sequence
`0 → L(D')/L(D) → 𝒜(D')/𝒜(D) → Ȟ¹(D) → Ȟ¹(D') → 0`.  We isolate the pure
linear-algebra content: for any exact sequence of four finite-dimensional
`k`-vector spaces, the alternating sum of dimensions vanishes.  This is the engine
that telescopes `χ(D) := ℓ(D) − h¹(D)`. -/

section ExactDim

variable {k A B C E : Type*} [DivisionRing k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup E] [Module k E]
    [FiniteDimensional k A] [FiniteDimensional k B] [FiniteDimensional k C]
    [FiniteDimensional k E]

/-- **Alternating dimension identity of a 4-term exact sequence.** For a four-term
exact sequence of finite-dimensional `k`-vector spaces
`0 → A --i--> B --p--> C --q--> E → 0`
(`i` injective, exact at `B` and `C`, `q` surjective),
`dim A − dim B + dim C − dim E = 0`.

The proof is a double application of rank–nullity: `dim(ker p) = dim(range i) =
dim A` and `dim(ker q) = dim C − dim E`, and exactness `range p = ker q` matches
`dim B − dim A = dim C − dim E`.  This is the χ-ledger engine (design §3, node
N15): applied to the ledger sequence it is exactly `χ(D+P) = χ(D) + deg P`. -/
theorem finrank_alternating_of_exact4
    (i : A →ₗ[k] B) (p : B →ₗ[k] C) (q : C →ₗ[k] E)
    (hi : Function.Injective i)
    (hB : LinearMap.range i = LinearMap.ker p)
    (hC : LinearMap.range p = LinearMap.ker q)
    (hq : Function.Surjective q) :
    (Module.finrank k A : ℤ) - Module.finrank k B + Module.finrank k C
      - Module.finrank k E = 0 := by
  have hkerp : Module.finrank k (LinearMap.ker p) = Module.finrank k A := by
    rw [← hB, LinearMap.finrank_range_of_inj hi]
  have hrnp := LinearMap.finrank_range_add_finrank_ker p
  have hrnq := LinearMap.finrank_range_add_finrank_ker q
  have hrangeq : Module.finrank k (LinearMap.range q) = Module.finrank k E := by
    rw [LinearMap.range_eq_top.mpr hq]; exact finrank_top k E
  have hkerqp : Module.finrank k (LinearMap.range p) = Module.finrank k (LinearMap.ker q) := by
    rw [hC]
  rw [hkerp] at hrnp
  rw [hrangeq] at hrnq
  omega

end ExactDim

/-! ## §N15/N16. The `k`-dimension χ-ledger and the Riemann inequality

We now assemble the numerical χ-ledger over a field of constants `k`.  With
`ℓ(D) := dim_k Γ(⊤, 𝒪(D))` and `h¹(D) := dim_k Ȟ¹(D)`, the Euler characteristic
`χ(D) := ℓ(D) − h¹(D)` telescopes along the twist ledger: `χ(D + P) = χ(D) +
dim_k(𝒜(D')/𝒜(D))`, and the local dimension `dim_k(𝒜(D')/𝒜(D)) = deg P`
(node N14).  The Riemann inequality `deg D + χ(0) ≤ ℓ(D)` is the elementary
consequence `χ(D) ≤ ℓ(D)` (i.e. `h¹(D) = i(D) ≥ 0`) combined with the telescoped
`χ(D) = χ(0) + deg D`. -/

section ChiLedgerDim

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X]

/-- **The relative-quotient dimension is the difference of dimensions.** For
`Γ(U, 𝒪(D)) ⊆ Γ(U, 𝒪(D'))` finite-dimensional, `dim_k(Γ(U,𝒪(D'))/Γ(U,𝒪(D))) =
ℓ_U(D') − ℓ_U(D)`.  Rank–nullity on the relative quotient. -/
theorem finrank_localStepDom (U : X.Opens) {D D' : X.WeilDivisor}
    (hDD' : sectionSub k U D ≤ sectionSub k U D')
    [Module.Finite k (sectionSub k U D')] :
    (Module.finrank k (localStepDom k U D D') : ℤ)
      = Module.finrank k (sectionSub k U D') - Module.finrank k (sectionSub k U D) := by
  have key : Module.finrank k (localStepDom k U D D')
      + Module.finrank k (sectionSub k U D) = Module.finrank k (sectionSub k U D') := by
    have h1 := Submodule.finrank_quotient_add_finrank
      (Submodule.comap (sectionSub k U D').subtype (sectionSub k U D))
    have h2 : Module.finrank k
        (Submodule.comap (sectionSub k U D').subtype (sectionSub k U D))
        = Module.finrank k (sectionSub k U D) :=
      (Submodule.comapSubtypeEquivOfLe hDD').finrank_eq
    rw [h2] at h1
    exact h1
  omega

variable (U₀ U₁ : X.Opens)

/-- **Antitonicity of `sectionSub` in the open.** -/
theorem sectionSub_antitone_open {U U' : X.Opens} (h : U ≤ U') (D : X.WeilDivisor) :
    sectionSub k U' D ≤ sectionSub k U D :=
  fun _ hx => sectionOfDivisor_antitone_open h D hx

/-- **The coboundary subspace `B(D) = Γ(U₀,𝒪(D)) + Γ(U₁,𝒪(D))` as a `k`-subspace.** -/
noncomputable def coboundarySub (D : X.WeilDivisor) : Submodule k X.functionField :=
  sectionSub k U₀ D ⊔ sectionSub k U₁ D

/-- `B(D) ⊆ 𝒜(D) = Γ(U₀ ⊓ U₁, 𝒪(D))`. -/
theorem coboundarySub_le_overlap (D : X.WeilDivisor) :
    coboundarySub k U₀ U₁ D ≤ sectionSub k (U₀ ⊓ U₁) D :=
  sup_le (sectionSub_antitone_open k inf_le_left D)
    (sectionSub_antitone_open k inf_le_right D)

/-- **The cover cohomology `Ȟ¹(D) = 𝒜(D) / B(D)` as a `k`-vector space.** The
`k`-linear incarnation of `H1`. -/
abbrev H1Mod (D : X.WeilDivisor) : Type u :=
  ↥(sectionSub k (U₀ ⊓ U₁) D) ⧸
    Submodule.comap (sectionSub k (U₀ ⊓ U₁) D).subtype (coboundarySub k U₀ U₁ D)

/-- **`ℓ(D) := dim_k Γ(⊤, 𝒪(D))`**, the dimension of the global Riemann–Roch
space (the linear system `L(D)`). -/
noncomputable def ell (D : X.WeilDivisor) : ℕ := Module.finrank k (sectionSub k ⊤ D)

/-- **`h¹(D) := dim_k Ȟ¹(D)`**, the dimension of the cover cohomology. -/
noncomputable def h1dim (D : X.WeilDivisor) : ℕ := Module.finrank k (H1Mod k U₀ U₁ D)

/-- **The Euler characteristic `χ(D) := ℓ(D) − h¹(D)`** of the χ-ledger. -/
noncomputable def chi (D : X.WeilDivisor) : ℤ := (ell k D : ℤ) - h1dim k U₀ U₁ D

/-- **N15 — the twist-ledger alternating dimension identity.** Given the four-term
ledger exact sequence
`0 → L(D')/L(D) → 𝒜(D')/𝒜(D) → Ȟ¹(D) → Ȟ¹(D') → 0`
(as `k`-linear maps with the stated exactness — the window injectivity is
`localStepMapₖ_injective`/`windowMap_injective`; the connecting map and the
surjectivity at `Ȟ¹(D')` are the deferred Mittag-Leffler/affine-cover inputs,
supplied here as hypotheses), the alternating sum of dimensions vanishes.  This is
the numerical engine of χ-additivity. -/
theorem ledger_alternating {D D' : X.WeilDivisor}
    (window : localStepDom k ⊤ D D' →ₗ[k] localStepDom k (U₀ ⊓ U₁) D D')
    (connect : localStepDom k (U₀ ⊓ U₁) D D' →ₗ[k] H1Mod k U₀ U₁ D)
    (twist : H1Mod k U₀ U₁ D →ₗ[k] H1Mod k U₀ U₁ D')
    (hwin : Function.Injective window)
    (hexactB : LinearMap.range window = LinearMap.ker connect)
    (hexactC : LinearMap.range connect = LinearMap.ker twist)
    (htwist : Function.Surjective twist)
    [Module.Finite k (localStepDom k ⊤ D D')]
    [Module.Finite k (localStepDom k (U₀ ⊓ U₁) D D')]
    [Module.Finite k (H1Mod k U₀ U₁ D)] [Module.Finite k (H1Mod k U₀ U₁ D')] :
    (Module.finrank k (localStepDom k ⊤ D D') : ℤ)
        - Module.finrank k (localStepDom k (U₀ ⊓ U₁) D D')
        + h1dim k U₀ U₁ D - h1dim k U₀ U₁ D' = 0 :=
  finrank_alternating_of_exact4 window connect twist hwin hexactB hexactC htwist

/-- **N15 — χ-additivity (honest gated form).** Under the ledger exact sequence and
`D ≤ D'`, the Euler characteristic bumps by the local dimension
`dim_k(𝒜(D')/𝒜(D))`:
`χ(D') = χ(D) + dim_k(𝒜(D')/𝒜(D))`.
Combined with node N14 (`dim_k(𝒜(D')/𝒜(D)) = deg P` for a one-point bump
`D' = D + P`), this is `χ(D + P) = χ(D) + deg P`. -/
theorem chi_add {D D' : X.WeilDivisor}
    (hDD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P)
    (window : localStepDom k ⊤ D D' →ₗ[k] localStepDom k (U₀ ⊓ U₁) D D')
    (connect : localStepDom k (U₀ ⊓ U₁) D D' →ₗ[k] H1Mod k U₀ U₁ D)
    (twist : H1Mod k U₀ U₁ D →ₗ[k] H1Mod k U₀ U₁ D')
    (hwin : Function.Injective window)
    (hexactB : LinearMap.range window = LinearMap.ker connect)
    (hexactC : LinearMap.range connect = LinearMap.ker twist)
    (htwist : Function.Surjective twist)
    [Module.Finite k (sectionSub k ⊤ D')]
    [Module.Finite k (localStepDom k (U₀ ⊓ U₁) D D')]
    [Module.Finite k (H1Mod k U₀ U₁ D)] [Module.Finite k (H1Mod k U₀ U₁ D')] :
    chi k U₀ U₁ D' = chi k U₀ U₁ D
      + Module.finrank k (localStepDom k (U₀ ⊓ U₁) D D') := by
  haveI : Module.Finite k (localStepDom k ⊤ D D') := inferInstance
  have hwindow := finrank_localStepDom k ⊤ (sectionSub_mono k ⊤ hDD')
  have halt := ledger_alternating k U₀ U₁ window connect twist hwin hexactB hexactC htwist
  simp only [chi, ell, h1dim] at *
  omega

/-- **N15 — the one-step χ-ledger bound `χ(D + P) ≤ χ(D) + deg P`.**  Combining the
gated ledger exact sequence (χ-additivity `chi_add`, giving
`χ(D') = χ(D) + dim_k(𝒜(D')/𝒜(D))`) with node N14 (`localStep_finrank_le`, giving
`dim_k(𝒜(D')/𝒜(D)) ≤ deg P`) for a one-point twist `D' = D + P` with `P` in the
overlap `V = U₀ ⊓ U₁`, the Euler characteristic increases by at most the residue
degree.  This is the honest one-step form of the χ-ledger.

(The reverse bound `deg P ≤ dim_k(𝒜(D')/𝒜(D))` — equality `χ(D+P) = χ(D) + deg P` —
is the *surjectivity* of the local residue map `𝒜(D')/𝒜(D) ↠ κ(P)`, the
strong-approximation input, deferred with the ledger's connecting/surjectivity
data.) -/
theorem chi_add_le_residueDeg {D D' : X.WeilDivisor} {P : X.PrimeDivisor}
    (hPV : P.point ∈ (U₀ ⊓ U₁ : X.Opens))
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q)
    (window : localStepDom k ⊤ D D' →ₗ[k] localStepDom k (U₀ ⊓ U₁) D D')
    (connect : localStepDom k (U₀ ⊓ U₁) D D' →ₗ[k] H1Mod k U₀ U₁ D)
    (twist : H1Mod k U₀ U₁ D →ₗ[k] H1Mod k U₀ U₁ D')
    (hwin : Function.Injective window)
    (hexactB : LinearMap.range window = LinearMap.ker connect)
    (hexactC : LinearMap.range connect = LinearMap.ker twist)
    (htwist : Function.Surjective twist)
    [Module.Finite k (sectionSub k ⊤ D')]
    [Module.Finite k (localStepDom k (U₀ ⊓ U₁) D D')]
    [Module.Finite k (H1Mod k U₀ U₁ D)] [Module.Finite k (H1Mod k U₀ U₁ D')]
    [Module.Finite k (localStepTgt k P 1)] :
    chi k U₀ U₁ D' ≤ chi k U₀ U₁ D + residueDeg k P := by
  have hbump := chi_add k U₀ U₁ hle window connect twist hwin hexactB hexactC htwist
  have hN14 := localStep_finrank_le k hPV hstep hle hoff
  have hcast : (Module.finrank k (localStepDom k (U₀ ⊓ U₁) D D') : ℤ)
      ≤ (residueDeg k P : ℤ) := by exact_mod_cast hN14
  rw [hbump]; linarith

/-- **N15/N16 — the one-step χ-ledger *equality* `χ(D + P) = χ(D) + deg P`.**  The
Riemann–Roch χ-additivity in exact one-point form.  Combining the gated ledger exact
sequence (χ-additivity `chi_add`: `χ(D') = χ(D) + dim_k(𝒜(D')/𝒜(D))`) with the
equality direction of node N14 (`localStep_finrank_eq`: `dim_k(𝒜(D')/𝒜(D)) = deg P`),
whose only extra input beyond the elementary `≤` is the strong-approximation
surjectivity `hsurj` of the local residue map `𝒜(D')/𝒜(D) ↠ κ(P)`, the Euler
characteristic increases by *exactly* the residue degree for a one-point twist
`D' = D + P` with `P` in the overlap `V = U₀ ⊓ U₁`.  This closes the equality direction
of the χ-ledger deferred at the `≤` bound `chi_add_le_residueDeg`. -/
theorem chi_add_eq_residueDeg {D D' : X.WeilDivisor} {P : X.PrimeDivisor}
    (hPV : P.point ∈ (U₀ ⊓ U₁ : X.Opens))
    (hstep : (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P + 1)
    (hle : ∀ Q : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) Q ≤
      (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hoff : ∀ Q : X.PrimeDivisor, Q ≠ P →
      (show X.PrimeDivisor →₀ ℤ from D) Q = (show X.PrimeDivisor →₀ ℤ from D') Q)
    (hsurj : ∀ y : X.functionField,
        y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P - 1) →
        ∃ f ∈ sectionOfDivisor (U₀ ⊓ U₁) D',
          f - y ∈ orderGe P (-(show X.PrimeDivisor →₀ ℤ from D) P))
    (window : localStepDom k ⊤ D D' →ₗ[k] localStepDom k (U₀ ⊓ U₁) D D')
    (connect : localStepDom k (U₀ ⊓ U₁) D D' →ₗ[k] H1Mod k U₀ U₁ D)
    (twist : H1Mod k U₀ U₁ D →ₗ[k] H1Mod k U₀ U₁ D')
    (hwin : Function.Injective window)
    (hexactB : LinearMap.range window = LinearMap.ker connect)
    (hexactC : LinearMap.range connect = LinearMap.ker twist)
    (htwist : Function.Surjective twist)
    [Module.Finite k (sectionSub k ⊤ D')]
    [Module.Finite k (localStepDom k (U₀ ⊓ U₁) D D')]
    [Module.Finite k (H1Mod k U₀ U₁ D)] [Module.Finite k (H1Mod k U₀ U₁ D')] :
    chi k U₀ U₁ D' = chi k U₀ U₁ D + residueDeg k P := by
  have hbump := chi_add k U₀ U₁ hle window connect twist hwin hexactB hexactC htwist
  rw [hbump, localStep_finrank_eq k hPV hstep hle hoff hsurj]

/-- **N16 — nonnegativity of the index of speciality: `χ(D) ≤ ℓ(D)`.** Immediate
from `χ(D) = ℓ(D) − h¹(D)` and `h¹(D) = i(D) ≥ 0`.  This is the `i(D) ≥ 0` half of
the Riemann inequality. -/
theorem chi_le_ell (D : X.WeilDivisor) : chi k U₀ U₁ D ≤ (ell k D : ℤ) := by
  have : (0 : ℤ) ≤ (h1dim k U₀ U₁ D : ℤ) := Int.natCast_nonneg _
  simp only [chi]; linarith

/-- **N16 — the Riemann inequality `deg D + χ(0) ≤ ℓ(D)`.** Given the telescoped
Euler characteristic `χ(D) = χ(0) + deg D` (node N15 `chi_add` iterated along the
divisor: `deg D = Σᵢ deg Pᵢ` the sum of the one-point local residue degrees, an
honest hypothesis packaging the induction on the effective parts), the Riemann
inequality is the elementary `χ(D) ≤ ℓ(D)` (`i(D) ≥ 0`):
`deg D + χ(0) ≤ ℓ(D)`. -/
theorem riemann_inequality {D : X.WeilDivisor} {degD : ℤ}
    (htel : chi k U₀ U₁ D = chi k U₀ U₁ 0 + degD) :
    degD + chi k U₀ U₁ 0 ≤ (ell k D : ℤ) := by
  have h := chi_le_ell k U₀ U₁ D
  rw [htel] at h; linarith

/-! ### N16 — telescoping the one-step equality over an effective divisor

The one-step equality `χ(E + P) = χ(E) + deg P` (`chi_add_eq_residueDeg`) telescopes:
writing an effective divisor `D ≥ 0` as a sum of one-point divisors `D = Σ P∈L 1·P`
(with multiplicity given by repetition in the list `L`), iteration gives the Riemann
shape `χ(D) = χ(0) + Σ P∈L deg P`, the **adelic degree** `deg_k D = Σ nᵢ·[κ(Pᵢ):k]`
weighted by residue degrees (the field-of-constants refinement of the geometric
`degree`, which is this sum with every `[κ(Pᵢ):k] = 1` over `k̄`).  The per-step
equality is supplied as the hypothesis `hbump` — each instance is exactly one
application of `chi_add_eq_residueDeg` (the one-point twist `E ↦ 1·P + E` satisfies
`hstep`/`hle`/`hoff` by `Finsupp.single`), so this is the honest reduction of N16 to
the strong-approximation one-point count. -/

/-- **The one-point effective divisor `1·P`** (`Finsupp.single P 1`), the unit building
block of the effective-divisor telescope. -/
noncomputable def pointDivisor (P : X.PrimeDivisor) : X.WeilDivisor := Finsupp.single P 1

/-- **The effective divisor `Σ P∈L 1·P` of a list of prime divisors** — the generic
effective divisor written as a sum of one-point divisors, with multiplicity encoded by
repetition in the list. -/
noncomputable def divisorOfList : List X.PrimeDivisor → X.WeilDivisor
  | [] => 0
  | P :: L => pointDivisor P + divisorOfList L

/-- **Coordinatewise addition of Weil divisors.** `(D₁ + D₂)(P) = D₁(P) + D₂(P)`;
the `X.WeilDivisor` group law is the pointwise `Finsupp` one. -/
theorem weilDivisor_add_apply (D₁ D₂ : X.WeilDivisor) (Q : X.PrimeDivisor) :
    (show X.PrimeDivisor →₀ ℤ from D₁ + D₂) Q =
      (show X.PrimeDivisor →₀ ℤ from D₁) Q + (show X.PrimeDivisor →₀ ℤ from D₂) Q :=
  Finsupp.add_apply _ _ _

/-- **The one-point bump raises the coefficient at `P` by one** — the `hstep`
hypothesis of `chi_add_eq_residueDeg` for the telescope step `E ↦ 1·P + E`. -/
theorem add_pointDivisor_apply_self (E : X.WeilDivisor) (P : X.PrimeDivisor) :
    (show X.PrimeDivisor →₀ ℤ from pointDivisor P + E) P =
      (show X.PrimeDivisor →₀ ℤ from E) P + 1 := by
  rw [weilDivisor_add_apply, pointDivisor, Finsupp.single_eq_same, add_comm]

/-- **The one-point bump changes nothing off `P`** — the `hoff` hypothesis of
`chi_add_eq_residueDeg` for the telescope step `E ↦ 1·P + E`. -/
theorem add_pointDivisor_apply_of_ne (E : X.WeilDivisor) {P Q : X.PrimeDivisor}
    (h : Q ≠ P) :
    (show X.PrimeDivisor →₀ ℤ from pointDivisor P + E) Q =
      (show X.PrimeDivisor →₀ ℤ from E) Q := by
  rw [weilDivisor_add_apply, pointDivisor, Finsupp.single_eq_of_ne h, zero_add]

/-- **The one-point bump is monotone** — the `hle` hypothesis of
`chi_add_eq_residueDeg` for the telescope step `E ↦ 1·P + E`. -/
theorem le_add_pointDivisor (E : X.WeilDivisor) (P Q : X.PrimeDivisor) :
    (show X.PrimeDivisor →₀ ℤ from E) Q ≤
      (show X.PrimeDivisor →₀ ℤ from pointDivisor P + E) Q := by
  rw [weilDivisor_add_apply, pointDivisor]
  rcases eq_or_ne Q P with rfl | hne
  · rw [Finsupp.single_eq_same]; linarith
  · rw [Finsupp.single_eq_of_ne hne]; linarith

/-- **N16 — the χ-ledger telescopes over an effective divisor.**  Iterating the
one-point χ-equality `χ(E + P) = χ(E) + deg P` (node N15/N16 `chi_add_eq_residueDeg`,
supplied here as the per-step hypothesis `hbump`) along a list `L` of prime divisors
gives the Euler characteristic of the effective divisor `D = Σ P∈L 1·P` as
`χ(D) = χ(0) + Σ P∈L deg P` — the telescoped Riemann shape `χ(D) = χ(0) + deg_k D`,
with `deg_k D = Σ deg Pᵢ` the adelic degree (sum of residue degrees over `k`).  Feeding
the resulting identity to `riemann_inequality` yields `deg_k D + χ(0) ≤ ℓ(D)`. -/
theorem chi_telescope_list (L : List X.PrimeDivisor)
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P) :
    chi k U₀ U₁ (divisorOfList L)
      = chi k U₀ U₁ 0 + ((L.map (residueDeg k)).sum : ℤ) := by
  induction L with
  | nil => simp [divisorOfList]
  | cons P L ih =>
    rw [divisorOfList, hbump, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

end ChiLedgerDim

end Adelic
end AlgebraicGeometry
