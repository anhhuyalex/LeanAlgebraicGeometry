/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Basic

/-!
# MR2223407: Castelnuovo–Mumford Regularity (Nitsure §2)

This file scaffolds the quantitative engine of the Quot construction, following the
blueprint chapter `chapters/Regularity.tex` (Nitsure §2).

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `IsMRegular`                      — `def:m-regular`
* `isMRegular_restrict_hyperplane`  — `lem:regularity-hyperplane-restriction`
* `castelnuovo_vanishing`           — `lem:castelnuovo-vanishing`
* `castelnuovo_surjective`          — `lem:castelnuovo-surjective`
* `castelnuovo_globally_generated`  — `lem:castelnuovo-globally-generated`
* `castelnuovo`                     — `lem:castelnuovo`
* `mumford_regularity`              — `thm:mumford-regularity`

## Stating-gap convention

The central object of this chapter — coherent sheaf cohomology
`Hⁱ(ℙⁿ_k, F(r))` — is a Mathlib gap (no `Hⁱ`, no Serre twists `O(r)`).  Following
the convention established in `Basic.lean` (see `serre_vanishing`,
`coherent_higher_direct_image`) and in the sibling files, each gap-object is
abstracted as free input data and the intended geometric conclusion is stated about
it, with the proof deferred to a `sorry`:

* the cohomology groups `Hⁱ(ℙⁿ_k, F(r))`, which are finite-dimensional `k`-vector
  spaces, are abstracted as `H : ℕ → ℤ → ModuleCat k`, with `H i r ≈ Hⁱ(ℙⁿ_k, F(r))`
  and "the group vanishes" rendered as `CategoryTheory.Limits.IsZero (H i r)`;
* the Serre twists `F(r)` are abstracted as `twist : ℤ → (ℙⁿ_k).Modules`, exactly as
  in `Basic.serre_vanishing`;
* global generation of `F(r)` is rendered, as in `Basic.serre_vanishing`, as the
  existence of an epimorphism onto `twist r` from a finite free sheaf;
* `H⁰(ℙⁿ_k, O(1))` is abstracted as a `k`-vector space `L`, and the multiplication
  map `H⁰(O(1)) ⊗ H⁰(F(r)) → H⁰(F(r+1))` as `mul r : L ⊗ H 0 r ⟶ H 0 (r+1)`;
* the Euler characteristic / Hilbert polynomial `χ(F(r))` is abstracted as
  `chi : ℤ → ℤ`, with the binomial expansion `χ(F(r)) = Σ aᵢ · C(r,i)` recorded as a
  hypothesis (`Ring.choose` is the integer-valued binomial polynomial).

The base scheme is `Spec k`.  PROGRESS.md lists this file as importing `Functors`
(for `hilbertPolynomial`).  As with the sibling `FlatteningStratification.lean`, we
import only `Basic` to stay decoupled from same-wave sibling timing and unstable
signatures; the Hilbert-polynomial datum is abstracted (`chi` + its binomial
expansion) rather than taken from `Functors`.  No `axiom` is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace MR2223407ConstructionHilbertQuot

/-! ## `m`-regularity -/

/-- **`m`-regular sheaf** (`def:m-regular`).

Let `k` be a field and `F` a coherent sheaf on `ℙⁿ_k`.  `F` is *`m`-regular* if
`Hⁱ(ℙⁿ_k, F(m-i)) = 0` for every `i ≥ 1`.

STATING-GAP: coherent cohomology `Hⁱ` is a Mathlib gap, so the cohomology groups
`Hⁱ(ℙⁿ_k, F(r))` — finite-dimensional `k`-vector spaces — are abstracted as input
data `H : ℕ → ℤ → ModuleCat k`, with `H i r ≈ Hⁱ(ℙⁿ_k, F(r))`.  Vanishing of the
group is `IsZero`.  The defining shift `m - i` is captured faithfully; it is exactly
what makes the property survive restriction to a hyperplane
(`isMRegular_restrict_hyperplane`). -/
def IsMRegular {k : Type u} [Field k] (H : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → IsZero (H i (m - (i : ℤ)))

/-- **Regularity restricts to a generic hyperplane**
(`lem:regularity-hyperplane-restriction`).

If `F` is `m`-regular on `ℙⁿ_k` and `H ⊂ ℙⁿ` is a hyperplane containing no
associated point of `F`, then the restriction `F_H` is again `m`-regular (same `m`)
on `H ≅ ℙⁿ⁻¹`.

STATING-GAP: the genuine input is the hyperplane long exact cohomology sequence
`Hⁱ(F(r)) → Hⁱ(F_H(r)) → Hⁱ⁺¹(F(r-1))` arising from
`0 → F(r-1) → F(r) → F_H(r) → 0`.  Constructing that sequence needs coherent
cohomology (Mathlib gap).  We abstract the cohomology of `F` as `H` and of `F_H` as
`HH`, and take the *consequence* of exactness — vanishing of both flanking groups
forces vanishing of the middle one — as the explicit hypothesis `hles`.  Under that
honest hypothesis the regularity transfer is a genuine (provable) implication. -/
theorem isMRegular_restrict_hyperplane {k : Type u} [Field k]
    (H HH : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) (hF : IsMRegular H m)
    (hles : ∀ (i : ℕ) (r : ℤ),
      IsZero (H i r) → IsZero (H (i + 1) (r - 1)) → IsZero (HH i r)) :
    IsMRegular HH m := by
  intro i hi
  refine hles i (m - (i : ℤ)) (hF i hi) ?_
  have h2 := hF (i + 1) (by omega)
  simpa [Nat.cast_add, Nat.cast_one, sub_sub] using h2

/-! ## Castelnuovo's lemma -/

/-- **Castelnuovo, vanishing of higher cohomology** (`lem:castelnuovo-vanishing`,
part (b)).

If `F` is `m`-regular then `Hⁱ(ℙⁿ_k, F(r)) = 0` whenever `i ≥ 1` and `r ≥ m - i`.
In particular `F` is `m'`-regular for every `m' ≥ m`.

STATING-GAP: the intended statement about the genuine cohomology of `F` (here
abstracted as `H`).  Its proof propagates the diagonal vanishing of `m`-regularity
to the whole region `r ≥ m - i` by induction on `n` via the hyperplane sequence — a
mechanism that needs coherent cohomology (Mathlib gap).  Hence the body is deferred
to `sorry`. -/
theorem castelnuovo_vanishing {k : Type u} [Field k]
    (H : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) (hF : IsMRegular H m) :
    ∀ (i : ℕ) (r : ℤ), 1 ≤ i → m - (i : ℤ) ≤ r → IsZero (H i r) :=
  sorry

/-- **Castelnuovo, surjectivity of multiplication** (`lem:castelnuovo-surjective`,
part (a)).

If `F` is `m`-regular then for every `r ≥ m` the canonical multiplication map
`H⁰(ℙⁿ_k, O(1)) ⊗ H⁰(ℙⁿ_k, F(r)) → H⁰(ℙⁿ_k, F(r+1))` is surjective.

STATING-GAP: `H⁰(O(1))` is abstracted as a `k`-vector space `L`, the global sections
`H⁰(F(r))` as `H 0 r`, and the multiplication map as `mul r : L ⊗ H 0 r ⟶ H 0 (r+1)`
(categorical tensor in `ModuleCat k`).  Surjectivity is `Epi` (which in `ModuleCat k`
is exactly surjectivity).  The proof (induction on `n`, diagram chase with the
restriction maps) needs coherent cohomology; deferred to `sorry`. -/
theorem castelnuovo_surjective {k : Type u} [Field k]
    (H : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) (_hF : IsMRegular H m)
    (L : ModuleCat.{u} k) (mul : ∀ r : ℤ, (L ⊗ H 0 r ⟶ H 0 (r + 1))) :
    ∀ r : ℤ, m ≤ r → Epi (mul r) :=
  sorry

/-- **Castelnuovo, global generation** (`lem:castelnuovo-globally-generated`,
part (c)).

If `F` is `m`-regular then for every `r ≥ m` the twist `F(r)` is generated by its
global sections and `Hⁱ(ℙⁿ_k, F(r)) = 0` for all `i ≥ 1`.

STATING-GAP: as in `Basic.serre_vanishing`, "globally generated" is rendered as the
existence of an epimorphism onto `twist r` (= `F(r)`) from a finite free sheaf; the
higher-cohomology vanishing reuses the abstract `H`.  The proof (iterate
`castelnuovo_surjective`, then descend global generation from Serre vanishing) is
deferred to `sorry`. -/
theorem castelnuovo_globally_generated {k : Type u} [Field k] (n : ℕ)
    (twist : ℤ → (projectiveSpace n (Spec (CommRingCat.of k))).Modules)
    (H : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) (_hF : IsMRegular H m) :
    ∀ r : ℤ, m ≤ r →
      (∃ (j : ℕ)
          (g : SheafOfModules.free
                (R := (projectiveSpace n (Spec (CommRingCat.of k))).ringCatSheaf)
                (ULift.{u} (Fin j)) ⟶ twist r),
          Epi g) ∧
      (∀ i : ℕ, 1 ≤ i → IsZero (H i r)) :=
  sorry

/-- **Castelnuovo's lemma** (`lem:castelnuovo`).

Umbrella statement gathering parts (a), (b), (c) for an `m`-regular sheaf `F` and
all `r ≥ m`:
* (a) the multiplication map `H⁰(O(1)) ⊗ H⁰(F(r)) → H⁰(F(r+1))` is surjective;
* (b) `Hⁱ(F(r')) = 0` for all `i ≥ 1` and `r' ≥ m - i` (so `F` is `m'`-regular for
  all `m' ≥ m`);
* (c) `F(r)` is globally generated with vanishing higher cohomology.

STATING-GAP: identical abstractions as in the three component lemmas above. -/
theorem castelnuovo {k : Type u} [Field k] (n : ℕ)
    (twist : ℤ → (projectiveSpace n (Spec (CommRingCat.of k))).Modules)
    (H : ℕ → ℤ → ModuleCat.{u} k) (m : ℤ) (_hF : IsMRegular H m)
    (L : ModuleCat.{u} k) (mul : ∀ r : ℤ, (L ⊗ H 0 r ⟶ H 0 (r + 1))) :
    (∀ r : ℤ, m ≤ r → Epi (mul r)) ∧
    (∀ (i : ℕ) (r : ℤ), 1 ≤ i → m - (i : ℤ) ≤ r → IsZero (H i r)) ∧
    (∀ r : ℤ, m ≤ r →
      (∃ (j : ℕ)
          (g : SheafOfModules.free
                (R := (projectiveSpace n (Spec (CommRingCat.of k))).ringCatSheaf)
                (ULift.{u} (Fin j)) ⟶ twist r),
          Epi g) ∧
      (∀ i : ℕ, 1 ≤ i → IsZero (H i r))) :=
  sorry

/-! ## Mumford's regularity bound -/

/-- **Mumford's regularity theorem** (`thm:mumford-regularity`).

For all non-negative integers `p` and `n` there is a polynomial `F_{p,n}` in `n+1`
variables with integer coefficients such that: for any field `k`, any coherent sheaf
`F` on `ℙⁿ_k` isomorphic to a subsheaf of `⊕^p O_{ℙⁿ}`, with Hilbert polynomial
written in the binomial basis as `χ(F(r)) = Σ_{i=0}^n aᵢ C(r,i)`, the sheaf `F` is
`m`-regular for `m = F_{p,n}(a₀, …, aₙ)`.  The crucial content is that `F_{p,n}` is a
*single* integer polynomial, uniform in the field `k` and in `F`.

STATING-GAP: `F_{p,n}` is `Fpn : MvPolynomial (Fin (n+1)) ℤ`, evaluated at the
coefficient vector `a` via `MvPolynomial.eval a Fpn`.  The "subsheaf of `⊕^p O`"
hypothesis is a monomorphism `incl : F ⟶ ⊕^p O` (a finite free sheaf).  The Euler
characteristic `χ(F(r))` is abstracted as `chi : ℤ → ℤ`, and the binomial expansion
`χ(F(r)) = Σ aᵢ · C(r,i)` is the hypothesis `hchi`, with `Ring.choose r i` the
integer-valued binomial coefficient `C(r,i)` (`ℤ` is a `BinomialRing`).  The
cohomology of `F` is abstracted as `H`; `m`-regularity is `IsMRegular H`.  The proof
(Mumford's induction on `n`, controlling `h¹` along the hyperplane) needs coherent
cohomology and the Hilbert polynomial; deferred to `sorry`. -/
theorem mumford_regularity (p n : ℕ) :
    ∃ Fpn : MvPolynomial (Fin (n + 1)) ℤ,
      ∀ (k : Type u) [Field k]
        (F : (projectiveSpace n (Spec (CommRingCat.of k))).Modules),
        F.IsQuasicoherent →
        ∀ (_incl : F ⟶ SheafOfModules.free
                  (R := (projectiveSpace n (Spec (CommRingCat.of k))).ringCatSheaf)
                  (ULift.{u} (Fin p))),
        Mono _incl →
        ∀ (H : ℕ → ℤ → ModuleCat.{u} k) (chi : ℤ → ℤ) (a : Fin (n + 1) → ℤ),
        (∀ r : ℤ, chi r = ∑ i : Fin (n + 1), a i * Ring.choose r (i : ℕ)) →
        IsMRegular H (MvPolynomial.eval a Fpn) :=
  sorry

end MR2223407ConstructionHilbertQuot
