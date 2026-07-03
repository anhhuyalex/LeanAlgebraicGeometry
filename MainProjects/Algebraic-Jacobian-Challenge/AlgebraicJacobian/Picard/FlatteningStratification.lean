/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Flattening stratification of a coherent sheaf (A.2.a)

This file is the **A.2.a** file-skeleton sub-build chapter for the project's
positive-genus arm of `nonempty_jacobianWitness`. It packages the
Nitsure~\S4 flattening-stratification theorem — the technical heart that
turns the absolute Quot-functor representability problem on a projective
morphism `π : X ⟶ S` with coherent input `𝓕` into a finite collection of
locally-closed strata over which `𝓕` becomes flat.

## Status (run 0010, T12 r2 — statement repair + dévissage layer)

The iter-176 file-skeleton carried three FALSE pinned statements, repaired
this round (see the per-declaration docstrings for the counterexamples):
`genericFlatness` gained `[QuasiCompact p]` (finite type = qc + locally of
finite type; `⨿_q Spec 𝔽_q → Spec ℤ` refuted the old form),
`flatLocusStratification` now asserts flatness over the *stratum*
(`CoherentSheafFlat (𝟙 (S_ e))`; flatness over ambient `S` fails for any
closed stratum), and `flatteningStratification_universal` now *bundles*
existence with the coproduct-factorisation universal property (the old
form quantified over arbitrary immersion families, refuted by `I = PEmpty`).

Proof state: `flatteningStratification` and `flatLocusAssembly` are proved
from `flatLocusReduction` (their typed content coincides with Lemma 6 up
to conjunct order / a choice of injection). The `GenericFreeness` section
now contains the full *dévissage layer* of Nitsure's algebraic
generic-freeness lemma — splicing under short exact sequences, torsion
base case, localization transport, and the prime-filtration assembly
`genericFlatnessAlgebraic` — with the Noether-normalisation domain core
`genericallyFree_quotient_prime` as its single remaining `sorry`.

Remaining `sorry`s (5, all TRUE statements): `genericallyFree_quotient_prime`,
`genericFlatness`, `flatLocusStratification`, `flatLocusReduction`,
`flatteningStratification_universal`.

The 4 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.CoherentSheafFlat` (def, ~8 LOC) — the
   **coherent-sheaf flatness predicate** for a coherent `𝓕` on `X` over
   `S` via `f : X ⟶ S`. Affine-locally: for `U ⊆ S` and `V ⊆ f⁻¹U` both
   affine, `Γ(𝓕, V)` is a flat `Γ(S, U)`-module via the composite
   `Γ(S, U) → Γ(X, V) → End(Γ(𝓕, V))`. The corresponding Stacks tag is
   00HB (module-level) lifted to a sheaf-level predicate by the
   affine-local descent characterisation.

2. `AlgebraicGeometry.genericFlatness` (theorem, ~15 LOC) — **generic
   flatness** [Nitsure §4 Theorem]: over a noetherian integral base
   `S`, a coherent sheaf on a finite-type `X ⟶ S` is flat over a
   non-empty open `V ⊆ S`.

3. `AlgebraicGeometry.flatteningStratification` (theorem, ~25 LOC) — the
   **flattening-stratification existence theorem** [Nitsure §4]: for `S`
   noetherian and `𝓕` coherent on a proper `π : X ⟶ S`, there exists a
   finite locally-closed stratification `{S_f}` of `S` (set-theoretically
   covering, pairwise disjoint) such that `𝓕` becomes flat on each
   stratum.

4. `AlgebraicGeometry.flatteningStratification_universal` (theorem, ~15 LOC)
   — the **universal property** of the stratification [Nitsure §4 (ii)]:
   any morphism `φ : T ⟶ S` such that `𝓕` pulled back to `X ×_S T` is
   `T`-flat factors uniquely through the stratum coproduct
   `i : ⨿ S_f ⟶ S`.

Additionally, three sub-lemmas decompose the existence proof, plus a
curve-specialisation corollary feeding the Route~A consumer:

5. `AlgebraicGeometry.flatLocusStratification` (lemma, ~12 LOC) — the
   **special case `n = 0`** [Nitsure §4, n=0]: a coherent `𝓕` on `S`
   admits a finite locally-closed stratification by integer "rank"
   strata.

6. `AlgebraicGeometry.flatLocusReduction` (lemma, ~12 LOC) — the
   **Noetherian-induction reduction** [Nitsure §4 general case opening]:
   a finite reduced locally-closed stratification on which `𝓕`
   *already* becomes flat (without polynomial indexing).

7. `AlgebraicGeometry.flatLocusAssembly` (lemma, ~15 LOC) — the
   **assembly step** [Nitsure §4 via direct images]: combining the
   `n = 0` stratification iteratively on the direct images
   `E_i = π_* 𝓕(N+i)` to refine to the Hilbert-polynomial-indexed
   stratification.

8. `AlgebraicGeometry.flatteningStratification.ofCurve` (theorem, ~10 LOC)
   — the **relative-curve specialisation** for the Route~A consumer
   `C ×_k T → T`.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof",
each declaration carries a substantive, non-tautological type:

- `CoherentSheafFlat` reduces to module-theoretic flatness of every
  affine-local section module over the corresponding affine-base ring
  via the `appLE` ring-hom — non-empty content because flatness of a
  module is the standard non-trivial homological condition.
- `genericFlatness` requires the existence of a *non-empty* open `V`
  and substantive flatness on every affine `U ⊆ V`; both quantifiers
  are necessary (without them the statement collapses to `V = ∅`).
- `flatteningStratification` packages a *finite* indexed family of
  *locally-closed-immersions* `ι : S_f ⟶ S` that pairwise *cover*
  `|S|` *disjointly* AND on which the pullback `𝓕|_{X ×_S S_f}` becomes
  `S_f`-flat — all four conjuncts are substantive (any single
  one trivialises if dropped).
- `flatteningStratification_universal` packages the universal property
  via `∃!` (unique existence of factorisation), a substantive Yoneda
  bijection content.

## Mathlib status

Mathlib (master `b80f227`) provides `Module.Flat`,
`AlgebraicGeometry.Flat` (morphism-level), `IsImmersion`,
`IsLocallyNoetherian`, `IsIntegral`, `LocallyOfFiniteType`. It does NOT
provide: a relative projective space `ℙⁿ_S`, an `IsProjective` morphism
property, the flattening-stratification construction, or coherent-sheaf
flatness as a sheaf-level predicate.

The current file-skeleton uses `IsProper π` as the structural stand-in
for "projective `π`" (every projective morphism is proper; the
restriction is harmless in the Route~A consumer setting where `π` comes
from a smooth proper curve, which is automatically projective).
iter-177+ refinement: once Mathlib gains an `IsProjective` morphism
property, the hypothesis tightens.

## References

Blueprint: `blueprint/src/chapters/Picard_FlatteningStratification.tex`
(735 LOC, 4 pins + 4 sub-lemma/corollary names). Source: Nitsure,
"Construction of Hilbert and Quot schemes", §4 (FGA Explained Ch. 5,
arXiv:math/0504020 pp. 5–18); Stacks Project tags 00HB (module flat),
052H (flattening stratification).
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — algebraic generic freeness (finite case)

This section builds the **module-theoretic** generic-freeness statements that
underlie the geometric `genericFlatness` (blueprint
`thm:generic_flatness_algebraic`, Nitsure~\S4 "Lemma on Generic Flatness").

The full algebraic statement — `A` a noetherian domain, `B` a *finite-type*
`A`-algebra, `M` a finite `B`-module ⟹ `∃ f ≠ 0` with `M_f` free over `A_f` —
is a deep theorem (prime-filtration dévissage + Noether normalisation +
clearing denominators). Mathlib does **not** contain it (checked against the
pinned revision; only the spreading-out lemma
`Module.FinitePresentation.exists_free_localizedModule_powers` exists).

This section contains, axiom-clean: the **finite-module / finite-morphism
case** (`exists_free_localizationAway_of_finite`, via
`exists_free_localizedModule_powers` at the generic point), and — added in
run 0010 T12 r2 — the complete **dévissage layer** of Nitsure's proof:
`GenericallyFree` (the property), `free_localizedModule_powers_mul`
(localization transport `M_f` free ⟹ `M_{fg}` free),
`GenericallyFree.of_linearEquiv`, `genericallyFree_of_exact` (splicing
under short exact sequences, via `ModuleCat.free_shortExact`),
`genericallyFree_of_subsingleton`, `genericallyFree_of_torsion` (Nitsure's
`n = -1` base case), and the prime-filtration assembly
`genericFlatnessAlgebraic` via
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`. The single
remaining `sorry` is the Noether-normalisation domain core
`genericallyFree_quotient_prime`. -/

namespace GenericFreeness

/-- **Generic freeness, finite-module case.** For a noetherian integral domain
`A` and a finite `A`-module `M`, there is a non-zero `f ∈ A` such that the
localisation `M_f` is free over `A_f = Localization.Away f`.

This is the `d = 0` (finite-morphism) special case of the algebraic
generic-flatness theorem (`thm:generic_flatness_algebraic`, Nitsure~\S4):
inverting the generic point `Frac A`, the localised module is a finite vector
space hence free, and `Module.FinitePresentation.exists_free_localizedModule_powers`
descends that freeness to a single basic open `D(f) ⊆ Spec A`. -/
theorem exists_free_localizationAway_of_finite
    (A : Type*) (M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers (nonZeroDivisors A)
      (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree⟩

/-- **Generic flatness, finite-module case.** The flatness form of
`exists_free_localizationAway_of_finite`: for a noetherian domain `A` and a
finite `A`-module `M`, there is a non-zero `f` with `M_f` flat over `A_f`.
This is the affine-local content of `genericFlatness` for a finite morphism. -/
theorem exists_flat_localizationAway_of_finite
    (A : Type*) (M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  obtain ⟨f, hf, hfree⟩ := exists_free_localizationAway_of_finite A M
  haveI := hfree
  exact ⟨f, hf, Module.Flat.of_free⟩

/-- **Generic freeness, finite-morphism case.** If `A` is a noetherian domain,
`B` a *module-finite* `A`-algebra, and `M` a finite `B`-module (with the
compatible `A`-module structure), then there is a non-zero `f ∈ A` with `M_f`
free over `A_f`. Reduces to `exists_free_localizationAway_of_finite` via
`Module.Finite.trans` (a finite module over a module-finite algebra is finite
over the base). This is generic flatness for a *finite* morphism `X → S`. -/
theorem exists_free_localizationAway_of_moduleFinite
    (A : Type*) (B : Type*) (M : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Module A M] [IsScalarTower A B M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  haveI : Module.Finite A M := Module.Finite.trans B M
  exact exists_free_localizationAway_of_finite A M

/-! ### The dévissage frame for full algebraic generic freeness

Grothendieck's generic-freeness lemma (blueprint
`thm:generic_flatness_algebraic`, Nitsure §4 "Lemma on Generic Flatness"):
for `A` a noetherian domain, `B` a finite-type `A`-algebra and `M` a finite
`B`-module there is `f ≠ 0` in `A` with `M_f` free over `A_f`.

Nitsure's proof has two layers: a *dévissage* (prime filtration of `M` as a
module over the noetherian ring `B`, reducing to `M = B/𝔭`, via the splicing
fact that generic freeness is stable under extensions), and a *domain core*
(`M = B/𝔭`: Noether normalisation over `Frac A` + clearing denominators +
the generic-rank exact sequence + induction on fibre dimension). This
section proves the dévissage layer completely — the splicing lemma
`genericallyFree_of_exact` (via `ModuleCat.free_shortExact` and the
localization-transport lemma `free_localizedModule_powers_mul`), the torsion
base case `genericallyFree_of_torsion` (Nitsure's `n = -1`), and the
assembly `genericFlatnessAlgebraic` via
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` — leaving the
domain core `genericallyFree_quotient_prime` as the single typed `sorry`. -/

/-- The **generic-freeness property** of an `A`-module `M`: some localization
`M_f` at a single non-zero `f ∈ A` is a free module over `A_f`. This is the
conclusion shared by every statement of this section. -/
def GenericallyFree (A : Type*) (M : Type*) [CommRing A] [AddCommGroup M]
    [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧
    Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

/-- Generic freeness transports along enlarging the inverted element: if `M_f`
is free over `A_f` then `M_{fg}` is free over `A_{fg}` for every `g`. The
proof is base-change associativity
`A_{fg} ⊗_{A_f} (A_f ⊗_A M) ≅ A_{fg} ⊗_A M` together with freeness of base
change (`Module.Free.tensor`); the two tensor legs are identified with the
localized modules by `IsLocalizedModule.isBaseChange`. -/
theorem free_localizedModule_powers_mul (A : Type*) (M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] (f g : A)
    (hf : Module.Free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g))
      (LocalizedModule (Submonoid.powers (f * g)) M) := by
  haveI := hf
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
      (P := Localization.Away (f * g)) f g).toAlgebra
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (f * g)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away f)
        (P := Localization.Away (f * g)) f g a).symm
  have e_f : (Localization.Away f) ⊗[A] M ≃ₗ[Localization.Away f]
      LocalizedModule (Submonoid.powers f) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).equiv
  have e_fg : (Localization.Away (f * g)) ⊗[A] M ≃ₗ[Localization.Away (f * g)]
      LocalizedModule (Submonoid.powers (f * g)) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers (f * g))
      (Localization.Away (f * g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M)).equiv
  have e_cancel : (Localization.Away (f * g)) ⊗[Localization.Away f]
      ((Localization.Away f) ⊗[A] M) ≃ₗ[Localization.Away (f * g)]
      (Localization.Away (f * g)) ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away f)
      (Localization.Away (f * g)) (Localization.Away (f * g)) M
  have e_congr : (Localization.Away (f * g)) ⊗[Localization.Away f]
      ((Localization.Away f) ⊗[A] M) ≃ₗ[Localization.Away (f * g)]
      (Localization.Away (f * g)) ⊗[Localization.Away f]
        (LocalizedModule (Submonoid.powers f) M) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.Away (f * g)) (Localization.Away (f * g))) e_f
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away (f * g))
      ((Localization.Away (f * g)) ⊗[Localization.Away f]
        (LocalizedModule (Submonoid.powers f) M)))
    (e_congr.symm.trans (e_cancel.trans e_fg))

/-- Generic freeness is invariant under `A`-linear equivalence. -/
theorem GenericallyFree.of_linearEquiv {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : GenericallyFree A M) : GenericallyFree A N := by
  obtain ⟨f, hf, hfree⟩ := h
  refine ⟨f, hf, ?_⟩
  haveI := hfree
  have e' : LocalizedModule (Submonoid.powers f) M ≃ₗ[A]
      LocalizedModule (Submonoid.powers f) N :=
    IsLocalizedModule.iso (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N) ∘ₗ e.toLinearMap)
  exact Module.Free.of_equiv' hfree
    (e'.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f))

/-- **Splicing lemma for generic freeness** — the extension step of Nitsure's
dévissage. If the outer terms of a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `A`-modules are generically free, so is the middle
term: localize the sequence at the product of the two witnesses (exactness of
localization) and apply `ModuleCat.free_shortExact`. -/
theorem genericallyFree_of_exact {A : Type*} [CommRing A] [IsDomain A]
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂]
    [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (u : M₁ →ₗ[A] M₂) (v : M₂ →ₗ[A] M₃) (hu : Function.Injective u)
    (hv : Function.Surjective v) (huv : Function.Exact u v)
    (h₁ : GenericallyFree A M₁) (h₃ : GenericallyFree A M₃) :
    GenericallyFree A M₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  refine ⟨f₁ * f₃, mul_ne_zero hf₁ hf₃, ?_⟩
  have hfree₁' := free_localizedModule_powers_mul A M₁ f₁ f₃ hfree₁
  have hfree₃' := free_localizedModule_powers_mul A M₃ f₃ f₁ hfree₃
  rw [mul_comm f₃ f₁] at hfree₃'
  let u' : LocalizedModule (Submonoid.powers (f₁ * f₃)) M₁
      →ₗ[Localization.Away (f₁ * f₃)]
      LocalizedModule (Submonoid.powers (f₁ * f₃)) M₂ :=
    (IsLocalizedModule.map (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      u).extendScalarsOfIsLocalization (Submonoid.powers (f₁ * f₃))
        (Localization.Away (f₁ * f₃))
  let v' : LocalizedModule (Submonoid.powers (f₁ * f₃)) M₂
      →ₗ[Localization.Away (f₁ * f₃)]
      LocalizedModule (Submonoid.powers (f₁ * f₃)) M₃ :=
    (IsLocalizedModule.map (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃)
      v).extendScalarsOfIsLocalization (Submonoid.powers (f₁ * f₃))
        (Localization.Away (f₁ * f₃))
  have hu' : Function.Injective u' :=
    IsLocalizedModule.map_injective (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂) u hu
  have hv' : Function.Surjective v' :=
    IsLocalizedModule.map_surjective (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃) v hv
  have huv' : Function.Exact u' v' :=
    IsLocalizedModule.map_exact (Submonoid.powers (f₁ * f₃))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f₁ * f₃)) M₃)
      u v huv
  let C : ShortComplex (ModuleCat (Localization.Away (f₁ * f₃))) :=
    ShortComplex.mk (ModuleCat.ofHom u') (ModuleCat.ofHom v')
      (ModuleCat.hom_ext (LinearMap.ext fun x => huv'.apply_apply_eq_zero x))
  have hC : C.ShortExact :=
    { exact := C.moduleCat_exact_iff.mpr fun x hx => (huv' x).mp hx
      mono_f := (ModuleCat.mono_iff_injective _).mpr hu'
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hv' }
  haveI : Module.Free (Localization.Away (f₁ * f₃)) C.X₁ := hfree₁'
  haveI : Module.Free (Localization.Away (f₁ * f₃)) C.X₃ := hfree₃'
  exact ModuleCat.free_shortExact hC

/-- Generic freeness of a subsingleton module (with `f = 1`). This is the
degenerate input to the dévissage; the substantive Nitsure base case
(`M_K = 0`, i.e. torsion `M`) is `genericallyFree_of_torsion` below. -/
theorem genericallyFree_of_subsingleton (A M : Type*) [CommRing A]
    [Nontrivial A] [AddCommGroup M] [Module A M] [Subsingleton M] :
    GenericallyFree A M := by
  refine ⟨1, one_ne_zero, ?_⟩
  haveI : Subsingleton (LocalizedModule (Submonoid.powers (1 : A)) M) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rw [Subsingleton.elim m 0]
      exact LocalizedModule.zero_mk s
  infer_instance

/-- **Torsion base case** of generic freeness (Nitsure's `n = -1`, `M_K = 0`):
a finite `A`-module all of whose elements are `A`-torsion is generically free
— the product of annihilators of a finite generating set kills the module,
so the corresponding localization vanishes. -/
theorem genericallyFree_of_torsion (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (htors : ∀ m : M, ∃ a : A, a ≠ 0 ∧ a • m = 0) : GenericallyFree A M := by
  classical
  obtain ⟨s, hs⟩ := (‹Module.Finite A M› : Module.Finite A M).fg_top
  choose a ha haz using htors
  refine ⟨∏ m ∈ s, a m, Finset.prod_ne_zero_iff.mpr fun m _ => ha m, ?_⟩
  have hkill : ∀ m : M, (∏ m' ∈ s, a m') • m = 0 := by
    have hker : Submodule.span A (s : Set M) ≤
        LinearMap.ker (LinearMap.lsmul A M (∏ m' ∈ s, a m')) := by
      rw [Submodule.span_le]
      intro m hm
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply]
      rw [← Finset.mul_prod_erase s a hm, mul_comm, mul_smul, haz m, smul_zero]
    intro m
    have hm : m ∈ Submodule.span A (s : Set M) := by
      rw [hs]; exact Submodule.mem_top
    simpa using hker hm
  haveI : Subsingleton (LocalizedModule (Submonoid.powers (∏ m ∈ s, a m)) M) := by
    apply subsingleton_of_forall_eq 0
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      rw [← LocalizedModule.mk_cancel_common_left
        (⟨∏ m' ∈ s, a m', Submonoid.mem_powers _⟩ : Submonoid.powers (∏ m ∈ s, a m))
        t m, Submonoid.mk_smul, hkill m]
      exact LocalizedModule.zero_mk _
  infer_instance

/-- **The domain core of algebraic generic freeness** [Nitsure §4, "Lemma on
Generic Flatness", normalisation step]: for a noetherian domain `A`, a
finite-type `A`-algebra `B` and a prime `𝔭 ⊆ B`, the quotient domain `B/𝔭`
is generically free over `A`.

This is the single remaining `sorry` of the dévissage: its (future) proof is
Nitsure's induction on the dimension of the generic fibre — if
`ker (A → B/𝔭) ≠ 0` the localization vanishes (`genericallyFree_of_torsion`);
otherwise Noether normalisation of `Frac A ⊗_A B/𝔭` over `Frac A`
(`exists_finite_inj_algHom_of_fg`), clearing denominators to make `(B/𝔭)_g`
module-finite over `A_g[b₁, …, b_m]` (`IsLocalization.exist_integer_multiples`
+ `Polynomial.scaleRoots` integrality), the generic-rank short exact sequence
`0 → A_g[b̄]^r → (B/𝔭)_g → T → 0` with `T` torsion over the polynomial ring,
and the fibre-dimension drop feeding the outer induction. TRUE as stated
(it is a special case of Grothendieck's lemma, Stacks 051R). -/
theorem genericallyFree_quotient_prime (A B : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (p : Ideal B) [p.IsPrime] : GenericallyFree A (B ⧸ p) := by
  sorry

/-- **Algebraic generic freeness, dévissage assembly** [Nitsure §4 "Lemma on
Generic Flatness" / Stacks 051R; blueprint `thm:generic_flatness_algebraic`].

For a noetherian domain `A`, a finite-type `A`-algebra `B` and a finite
`B`-module `M` (with compatible `A`-structure), `M` is generically free over
`A`. The prime-filtration dévissage over the noetherian ring `B`
(`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`) is complete:
the subsingleton case is `genericallyFree_of_subsingleton`, prime quotients
are the domain core `genericallyFree_quotient_prime` (the one remaining
`sorry` of this section), and stability under extensions is the splicing
lemma `genericallyFree_of_exact`. -/
theorem genericFlatnessAlgebraic (A B M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [Module A M]
    [IsScalarTower A B M] : GenericallyFree A M := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := B)
    ‹Module.Finite B M›
    (motive := fun N iACG iMB _ => ∀ (iA : Module A N),
      (@IsScalarTower A B N Algebra.toSMul
        iMB.toDistribMulAction.toMulAction.toSMul
        iA.toDistribMulAction.toMulAction.toSMul) →
      @GenericallyFree A N _ iACG iA)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A B M›
  · intro N _ _ _ _ iA _
    exact @genericallyFree_of_subsingleton A N _ _ _ iA ‹_›
  · intro N _ _ _ p e iA htower
    letI := iA
    haveI : IsScalarTower A B N := htower
    exact (genericallyFree_quotient_prime A B p.1).of_linearEquiv
      (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ u v hu hv huv h₁ h₃ iA₂ htower₂
    letI iA₁ : Module A N₁ := Module.compHom N₁ (algebraMap A B)
    letI iA₃ : Module A N₃ := Module.compHom N₃ (algebraMap A B)
    haveI ht₁ : IsScalarTower A B N₁ :=
      ⟨fun a b n => by
        change (a • b) • n = algebraMap A B a • b • n
        rw [Algebra.smul_def, mul_smul]⟩
    haveI ht₃ : IsScalarTower A B N₃ :=
      ⟨fun a b n => by
        change (a • b) • n = algebraMap A B a • b • n
        rw [Algebra.smul_def, mul_smul]⟩
    letI := iA₂
    haveI : IsScalarTower A B N₂ := htower₂
    exact genericallyFree_of_exact (u.restrictScalars A) (v.restrictScalars A)
      hu hv huv (h₁ iA₁ ht₁) (h₃ iA₃ ht₃)

end GenericFreeness

namespace Scheme

/-! ## §1. Coherent-sheaf flatness over a base

For a morphism `f : X ⟶ S` of schemes and a coherent (more generally:
quasi-coherent) `𝓞_X`-module `𝓕`, the *coherent-sheaf flatness* predicate
`CoherentSheafFlat f 𝓕` captures Stacks 00HB lifted to the sheaf level:
for every point `x ∈ X` the stalk `𝓕_x` is a flat `𝓞_{S, f(x)}`-module
via the composite `𝓞_{S, f(x)} → 𝓞_{X, x} → End(𝓕_x)`.

Affine-locally (Stacks 00HB equivalence): on an affine open `U = Spec A
⊆ S` and an affine open `V = Spec B ⊆ f⁻¹U` with `𝓕|_V = M̃` for a
finite `B`-module `M`, the condition becomes `Module.Flat A M` with the
`A`-module structure inherited via the ring map `A → B`. The
file-internal encoding uses this affine-local form.

Blueprint reference: `def:coherent_sheaf_flat`. -/

/-- A coherent sheaf `𝓕` on `X` is **flat over `S`** for a morphism
`f : X ⟶ S` if, for every affine open `U ⊆ S` and every affine open
`V ⊆ f⁻¹U`, the `𝓞_X`-module of sections `Γ(𝓕, V)` is flat as a
`Γ(S, U)`-module, where the `Γ(S, U)`-action is the restriction of
scalars along the ring morphism `Γ(S, U) → Γ(X, V)` (the `appLE`
morphism of `f`).

This is the affine-local form of Stacks 00HB (a coherent sheaf is flat
over the base if every stalk is flat over the corresponding base
stalk); the affine-local form and stalk form are equivalent for
*quasi-coherent* sheaves on a noetherian base, which is the regime of
the flattening-stratification theorem.

iter-177+: the body of subsequent flat-locus theorems may package this
predicate as an instance-driven typeclass `Module.Flat`-style if the
sheafified-tensor infrastructure lands in Mathlib; for the iter-176
file-skeleton it is encoded as a `Prop` quantifier. -/
def CoherentSheafFlat {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  ∀ {U : S.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U),
    letI : Module Γ(S, U) Γ(F, V) := Module.compHom _ (f.appLE U V e).hom
    Module.Flat Γ(S, U) Γ(F, V)

end Scheme

/-! ## §2. Generic flatness (Nitsure §4)

Over a noetherian integral base `S`, a coherent sheaf on a finite-type
`X ⟶ S` is flat above some non-empty open `V ⊆ S`. This is the inductive
engine of the flattening-stratification theorem: combined with
Noetherian induction on the closed complement `S ∖ V`, it produces the
finite stratification of `S` by flatness loci.

Algebraically (theorem `generic_flatness_algebraic`, no Lean pin): for a
noetherian domain `A`, a finite-type `A`-algebra `B`, and a finite
`B`-module `M`, there exists a non-zero `f ∈ A` such that `M_f` is a
free `A_f`-module. The geometric form (this declaration) restricts to a
non-empty affine open `Spec A ⊆ S` and applies the algebraic form on
each finite-type-algebra patch of `X` above `Spec A`.

Blueprint reference: `thm:generic_flatness` (Nitsure §4). -/

/-- **Generic flatness theorem** (Nitsure §4 / Stacks ?).

For a noetherian integral scheme `S`, a finite-type morphism `p : X ⟶ S`,
and a coherent `𝓞_X`-module `𝓕`, there exists a non-empty open subscheme
`V ⊆ S` such that `𝓕|_{X_V} = 𝓕|_{p⁻¹V}` is flat over `𝓞_V`.

iter-177+: the body follows Nitsure §4: pass to a non-empty affine open
`Spec A ⊆ S` where `A` is a noetherian domain, then apply the algebraic
form (Noether normalisation + Auslander–Buchsbaum-style filtration
argument) to each finite-type-`A`-algebra `B` arising from an affine
cover of `p⁻¹(Spec A)`. The witness `V` is the common basic open
`D(f_1 f_2 ⋯ f_r) ⊆ Spec A` clearing the finitely many
generic-flatness elements `f_i ∈ A` produced on each patch.

Statement repair (run 0010, T12 r2): Nitsure requires `p` of **finite type**
(EGA sense: quasi-compact AND locally of finite type). With
`LocallyOfFiniteType` alone the statement is FALSE: for
`X = ⨿_q Spec 𝔽_q → Spec ℤ` (locally of finite type, not quasi-compact,
structure sheaf finitely presented) every non-empty open `V ⊆ Spec ℤ`
contains all but finitely many primes `q`, and `𝔽_q` is never flat over the
corresponding `ℤ[1/n]`. Quasi-compactness is what bounds the number of
denominators to clear. Hence the `[QuasiCompact p]` hypothesis below. -/
theorem genericFlatness {S X : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (p : X ⟶ S) [QuasiCompact p] [LocallyOfFiniteType p] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (V : S.Opens), (V : Set S).Nonempty ∧
      ∀ {U : S.Opens} (_ : IsAffineOpen U) (_ : U ≤ V) {W : X.Opens}
        (_ : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U),
        letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
        Module.Flat Γ(S, U) Γ(F, W) := by
  sorry

/-! ## §3. Sub-lemmas of the existence proof

The Nitsure §4 proof of the existence theorem decomposes into three
sub-lemmas wired together by Noetherian induction. The first is the
special case `n = 0` (when `ℙⁿ_S = S`); the second is the
Noetherian-induction reduction to a finite stratification where `𝓕`
*already* becomes flat (but without polynomial indexing); the third is
the assembly step that re-introduces the Hilbert-polynomial indexing
via the direct images `E_i = π_* 𝓕(N+i)`.

Blueprint references: `lem:flat_locus_open`, `lem:nonflat_locus_proper`,
`lem:noetherian_induction_strata`. -/

/-- **Lemma 5 (special case `n = 0`).** [Nitsure §4 special case]

For `S` noetherian and `𝓕` a coherent `𝓞_S`-module, there exists a
countable family `S_e ⊆ S` (indexed by `e ∈ ℕ`) of locally-closed
subschemes such that
- each `S_e` is a (locally-closed) immersion `S_e ⟶ S`;
- the underlying sets `|S_e|` partition `|S|`;
- the pullback `𝓕|_{S_e}` is flat over `𝓞_{S_e}` — encoded as
  `CoherentSheafFlat (𝟙 (S_ e))`, i.e. flatness of the section modules of
  the pulled-back sheaf over the section rings of the stratum *itself*.
  (The *rank*-`e` locally-free refinement is future work once the
  locally-free-of-rank-`e` predicate is in scope.)

Statement repair (run 0010, T12 r2): the former conclusion asserted
`CoherentSheafFlat (ι e)` — flatness of the pulled-back sheaf over the
*ambient* `S` via the immersion — which is FALSE for any non-open stratum:
a nonzero module supported on a closed stratum `V(x) ⊆ 𝔸¹` is killed by
`x`, hence torsion, hence not flat over `𝓞_{𝔸¹}`-sections (e.g. the rank
stratification of the skyscraper `k(0)` on `𝔸¹` refutes it). Nitsure's
content is flatness (indeed local freeness) over the stratum, which is
`CoherentSheafFlat (𝟙 (S_ e))`.

The function `s ↦ dim_{κ(s)} 𝓕|_s` is upper-semicontinuous (this is
content (iii) of Nitsure's special case), encoded indirectly by the
fact that the strata are locally-closed and disjoint.

Nitsure's proof: Nakayama produces a local presentation
`𝓞_V^{⊕m} ⟶ 𝓞_V^{⊕e} ⟶ 𝓕|_V ⟶ 0`; the closed subscheme `V_e ⊆ V`
defined by the matrix-entry ideal of the first map represents the
locus of locally-free-of-rank-`e`; gluing over a cover and intersecting
with `V ∖ ⋃_{e' > e} V_{e'}` produces the locally-closed `S_e`. -/
lemma flatLocusStratification {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation] :
    ∃ (S_ : ℕ → Scheme.{u}) (ι : ∀ e, S_ e ⟶ S),
      (∀ e, IsImmersion (ι e)) ∧
      (∀ e e', e ≠ e' → Disjoint (Set.range (ι e).base) (Set.range (ι e').base)) ∧
      (∀ s : S, ∃ e, s ∈ Set.range (ι e).base) ∧
      (∀ e, Scheme.CoherentSheafFlat (𝟙 (S_ e))
        ((Scheme.Modules.pullback (ι e)).obj F)) := by
  sorry

/-- **Lemma 6 (Noetherian-induction reduction).** [Nitsure §4 general
case opening]

For `S` noetherian, `π : X ⟶ S` proper, and `𝓕` coherent on `X`, there
exist finitely many reduced locally-closed immersions `V_i ⟶ S` with
pairwise disjoint set-theoretic images covering `|S|`, such that the
pullback `𝓕|_{X ×_S V_i}` is flat over `V_i`.

Nitsure's proof: peel off non-empty open flat patches by
`genericFlatness` applied to each irreducible component (with its
reduced subscheme structure), induct on the closed complement
`S ∖ V` (which is again noetherian, hence the induction terminates by
Noetherianity).

The substantive content over the special case (Lemma 5) is that the
strata `V_i` are *reduced* and that `𝓕` becomes flat above them (not
merely that strata exist); the polynomial-indexed refinement of the
main theorem (`flatteningStratification`) requires further assembly
(`flatLocusAssembly`). -/
lemma flatLocusReduction {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (V_ : I → Scheme.{u}) (ι : ∀ i, V_ i ⟶ S),
      (∀ i, IsImmersion (ι i)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ι i).base) (Set.range (ι j).base)) ∧
      (∀ s : S, ∃ i, s ∈ Set.range (ι i).base) ∧
      (∀ i, Scheme.CoherentSheafFlat (pullback.snd π (ι i))
        ((Scheme.Modules.pullback (pullback.fst π (ι i))).obj F)) := by
  sorry

/-- **Lemma 7 (assembly via direct images).** [Nitsure §4 assembly step]

For `S` noetherian and `𝓕` coherent on a proper `π : X ⟶ S`, there
exists an integer `N` such that iterating the `n=0` stratification
(Lemma 5) on the direct images `E_i := π_*𝓕(N+i)` on `S`
(`i = 0, 1, …`) produces, after finitely many refinements, the
Hilbert-polynomial-indexed stratification of the main theorem.

The substantive content is the existence of the uniform vanishing
bound `N` together with the finite refinement chain producing the
locally-closed strata `S_f` from the rank-strata `W_{e_0, …, e_n}`.

For the iter-176 file-skeleton this is encoded by the existence of a
finite locally-closed stratification refining Lemma 6, together with
the assertion that the strata carry constant Hilbert polynomial (the
"polynomial-locally-constant" content of Nitsure's statement (A)).
The Hilbert polynomial itself is encoded abstractly as a function
`I → (ℕ → ℤ)` (each numerical polynomial restricted to `ℕ`); the
substantive refinement to `numericalPolynomial` of degree `≤ n` is
iter-177+ work.

Proof status (run 0010, T12 r2): as typed, the `P`-conjunct only demands
*some* injection `I → (ℕ → ℤ)`, which any finite index type admits; the
statement is therefore a formal corollary of `flatLocusReduction`, and is
proved as such below. The genuinely-Hilbert-indexed refinement must
strengthen the statement (tie `P f` to fibre Euler characteristics), which
awaits the coherent-χ substrate. -/
lemma flatLocusAssembly {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S)
      (P : I → ℕ → ℤ),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f, Scheme.CoherentSheafFlat (pullback.snd π (ι f))
        ((Scheme.Modules.pullback (pullback.fst π (ι f))).obj F)) ∧
      (∀ f g, f = g ↔ P f = P g) := by
  obtain ⟨I, hI, V_, ι, himm, hdisj, hcov, hflat⟩ := flatLocusReduction π F
  haveI := hI
  haveI := Fintype.ofFinite I
  refine ⟨I, hI, V_, ι, fun i _ => ((Fintype.equivFin I) i : ℤ), himm, hdisj, hcov, hflat,
    fun f g => ⟨fun h => h ▸ rfl, fun h => ?_⟩⟩
  have h0 : (((Fintype.equivFin I) f : ℕ) : ℤ) = (((Fintype.equivFin I) g : ℕ) : ℤ) :=
    congrFun h 0
  exact (Fintype.equivFin I).injective (Fin.val_injective (by exact_mod_cast h0))

/-! ## §4. Existence of the flattening stratification (Nitsure §4 main)

The main theorem combines the three sub-lemmas above: starting from a
proper morphism `π : X ⟶ S` and a coherent sheaf `𝓕`, one obtains a
finite locally-closed stratification of `S` indexed by Hilbert
polynomials, on each piece of which `𝓕` becomes flat, with all four
properties of Nitsure's Theorem packaged in a single conjunction.

Blueprint reference: `thm:flattening_stratification_exists`
(Nitsure §4; Stacks 052H). -/

/-- **Flattening stratification existence theorem** [Nitsure §4 main /
Stacks 052H].

For a noetherian scheme `S`, a proper morphism `π : X ⟶ S`, and a
coherent `𝓞_X`-module `𝓕`, there exists a finite locally-closed
stratification `{S_f}` of `S` indexed by a finite set `I` such that
- each `ι : S_f ⟶ S` is a (locally-closed) immersion;
- the underlying sets `|S_f|` partition `|S|` (disjoint and covering);
- the pullback `𝓕|_{X ×_S S_f}` is flat over `S_f` for each `f`.

The (intended) substantive refinement is that the index set `I` is in
bijection with the set of Hilbert polynomials arising on fibres, and
that each `S_f` is uniquely determined by its Hilbert polynomial. For
the iter-176 file-skeleton the substantive type captures the
stratification + flatness; the Hilbert-polynomial labeling is encoded
in `flatLocusAssembly`'s `P : I → ℕ → ℤ` injection but elided here for
type-clarity.

Proof status (run 0010, T12 r2): the conclusion as typed is exactly the
conclusion of `flatLocusReduction` (Lemma 6) up to conjunct order, so the
theorem is proved below by that reduction; the remaining mathematical
content of this cone therefore lives in `flatLocusReduction` (Noetherian
induction on `genericFlatness`) and `genericFlatness` itself. The
Hilbert-polynomial-indexed refinement (which would need relative
projective space `ℙⁿ_S`, Castelnuovo–Mumford regularity, direct-image
base change 02KH) is deliberately not part of this statement; see
`flatLocusAssembly` and the blueprint chapter §`Mathlib status`. -/
theorem flatteningStratification {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (π : X ⟶ S) [IsProper π] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat (pullback.snd π (ι f))
        ((Scheme.Modules.pullback (pullback.fst π (ι f))).obj F)) := by
  obtain ⟨I, hI, V_, ι, himm, hdisj, hcov, hflat⟩ := flatLocusReduction π F
  exact ⟨I, hI, V_, ι, himm, hcov, hdisj, hflat⟩

/-! ## §5. Universal property of the stratification

Nitsure's part (ii): the morphism `i : ⨿_f S_f → S` assembled from the
stratum inclusions is universal for "`𝓕` becomes `T`-flat after pullback
along `T → S`": any `φ : T ⟶ S` with `T`-flat pullback factors uniquely
through the coproduct `∐ S_f`.

Statement repair (run 0010, T12 r2): the former statement quantified over
*arbitrary* finite immersion families `(I, S_, ι)` — for which the ∃!
factorisation is FALSE (take `I = PEmpty`, or refine a genuine stratum
into two disjoint pieces: covering/disjointness/flatness survive but a
connected flat `T` straddling the two pieces no longer factors).
Universality is a property of *the* flattening stratification produced by
the construction (maximality of the strata), not of every disjoint flat
family, so it cannot be hypothesised away from the existence statement.
The repaired statement below therefore *bundles* existence and
universality: there exists a stratification with the four structural
properties of `flatteningStratification` AND the unique-factorisation
property against every `T`-flat `φ`. The factorisation target is the
scheme coproduct `∐ S_`, along `Sigma.desc ι : ∐ S_ ⟶ S` — the
single-stratum ∃!-form is false for disconnected `T`, which can hit
several strata.

Blueprint reference: `thm:flattening_stratification_universal`
(Nitsure §4 (ii); Stacks 052H). -/

/-- **Universal property of the flattening stratification**
[Nitsure §4 (ii) / Stacks 052H].

There is a finite locally-closed stratification `{S_f}` of `S` — with the
four structural properties of `flatteningStratification` (immersions,
covering, disjoint, flat pullback on each stratum) — such that every
`φ : T ⟶ S` whose pullback `𝓕|_{X ×_S T}` is `T`-flat factors uniquely
through `Sigma.desc ι : ∐ S_ ⟶ S`.

(The converse direction — every morphism factoring through the coproduct
has flat pullback — is also part of Nitsure's part (ii); it amounts to
stability of `CoherentSheafFlat` under base change and should be added as
a separate lemma when the base-change API for the predicate lands.)

iter-177+: refine to a `Functor.RepresentableBy`-style universal arrow
once the contravariant functor `T ↦ {φ : T ⟶ S | 𝓕|_{X_T} is T-flat}` is
available. -/
theorem flatteningStratification_universal {S X : Scheme.{u}}
    [IsLocallyNoetherian S] (π : X ⟶ S) [IsProper π] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (S_ : I → Scheme.{u}) (ι : ∀ f, S_ f ⟶ S),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ s : S, ∃ f, s ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat (pullback.snd π (ι f))
        ((Scheme.Modules.pullback (pullback.fst π (ι f))).obj F)) ∧
      (∀ {T : Scheme.{u}} (φ : T ⟶ S),
        Scheme.CoherentSheafFlat (pullback.snd π φ)
          ((Scheme.Modules.pullback (pullback.fst π φ)).obj F) →
        ∃! ψ : T ⟶ ∐ S_, ψ ≫ Sigma.desc ι = φ) := by
  sorry

/-! ## §6. Curve specialisation (Route A consumer)

In the Route A consumer setting, the input morphism is the second
projection `pr_T : C ×_k T ⟶ T` of the pullback of a smooth proper
curve `C/k` against a noetherian `k`-scheme `T`. A smooth proper curve
over a field is automatically projective (Hartshorne II.6.7 / II.7.6;
folklore), hence in particular proper; the relative-curve `C ×_k T → T`
inherits properness by base change, hence the hypotheses of the main
theorem are met. This corollary records the specialisation
explicitly. -/

/-- **Flattening stratification for a coherent sheaf on a relative
curve** [Nitsure §4 corollary; Route~A consumer A.2.a entry-point].

Let `k` be a field, `C` a smooth proper curve over `k` (encoded as
`C : Over (Spec k)` with `[SmoothOfRelativeDimension 1 C.hom]` and
`[IsProper C.hom]`), and `T` a noetherian `k`-scheme. For any coherent
sheaf `𝓕` on the relative curve `C ×_k T`, the flattening
stratification conclusion of `flatteningStratification` applies to
`π = pr_T : C ×_k T → T` and `𝓕`: there is a finite locally-closed
stratification `{T_f ⊆ T}` set-theoretically covering `T` disjointly,
such that `𝓕|_{C ×_k T_f}` is flat over `T_f` for each `f`.

iter-177+: the body invokes `flatteningStratification` on the
base-changed morphism `pullback.snd C.hom T.hom : (C ×_k T) ⟶ T`,
using that `IsProper (pullback.snd C.hom T.hom)` holds by base change
of `IsProper C.hom`. For the iter-176 file-skeleton the body is a
typed `sorry`. -/
theorem flatteningStratification.ofCurve {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left]
    (F : (Limits.pullback C.hom T.hom).Modules) [F.IsFinitePresentation] :
    ∃ (I : Type u) (_ : Finite I) (T_ : I → Scheme.{u}) (ι : ∀ f, T_ f ⟶ T.left),
      (∀ f, IsImmersion (ι f)) ∧
      (∀ t : T.left, ∃ f, t ∈ Set.range (ι f).base) ∧
      (∀ f g, f ≠ g → Disjoint (Set.range (ι f).base) (Set.range (ι g).base)) ∧
      (∀ f, Scheme.CoherentSheafFlat
        (pullback.snd (pullback.snd C.hom T.hom) (ι f))
        ((Scheme.Modules.pullback
          (pullback.fst (pullback.snd C.hom T.hom) (ι f))).obj F)) :=
  flatteningStratification (pullback.snd C.hom T.hom) F

end AlgebraicGeometry
