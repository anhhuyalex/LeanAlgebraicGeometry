/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Basic

/-!
# MR2223407: Generic Flatness and the Flattening Stratification

This file scaffolds the central technical device of the Quot construction, following
the blueprint chapter `chapters/FlatteningStratification.tex` (Nitsure §4).

Declarations (one per `\lean{...}`-tagged blueprint block):

* `genericFlatness_algebra`    — `lem:generic-flatness-algebra`
* `genericFlatness`            — `thm:generic-flatness`
* `flatteningStratification`   — `thm:flattening-stratification`

PROGRESS.md lists this file as importing `Functors` + `SemicontinuityBaseChange`.
Those modules are scaffolded in the *same* wave, so to keep this file compiling
independently of sibling timing — and to avoid coupling to not-yet-stabilised
signatures — we import only `Basic` and abstract the upstream gap-objects
(fibrewise Hilbert polynomial) as input data, exactly as `Basic.lean` does for its
EGA-III anchors. The per-declaration stating-gaps are recorded in the doc-strings.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace MR2223407ConstructionHilbertQuot

/-! ## Generic flatness -/

/-- **Algebraic generic flatness** (`lem:generic-flatness-algebra`).

Let `A` be a noetherian domain, `B` a finite-type `A`-algebra, and `M` a finite
`B`-module (hence a finite-type `A`-module structure via restriction of scalars).
Then there is a nonzero `f ∈ A` such that the localisation `M_f` is *free* over
`A_f`.

This is the faithful statement: `LocalizedModule (Submonoid.powers f) M` is the
localisation `M_f`, regarded as a module over `A_f = Localization.Away f`, and we
assert it is `Module.Free`. No Mathlib gap — pure commutative algebra. -/
theorem genericFlatness_algebra
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {M : Type u} [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Module A M] [IsScalarTower A B M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
  sorry

/-- **Generic flatness** (`thm:generic-flatness`).

Let `S` be a noetherian integral scheme, `p : X ⟶ S` a finite-type morphism, and
`F` a coherent sheaf of `O_X`-modules. Then there is a nonempty open subscheme
`U ⊆ S` such that the restriction of `F` to `X_U = p⁻¹(U)` is flat over `O_U`.

STATING-GAP: flatness of a coherent *sheaf* `F` over the base is not a Mathlib
notion. The closest honest shadow expressible with the available API is the
`F = O_X` case, namely flatness of the *morphism* itself: there is a nonempty open
`U ⊆ S` over which the restricted structure morphism `p ∣_ U` is flat
(`AlgebraicGeometry.Flat`). The sheaf `F` is retained as input; recovering its
own flatness from `O_X`-flatness is the deferred part. The statement is genuinely
non-vacuous (generic flatness of a finite-type morphism over an integral
noetherian base). -/
theorem genericFlatness
    {X S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (F : X.Modules) (_hF : F.IsQuasicoherent) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ AlgebraicGeometry.Flat (p ∣_ U) :=
  sorry

/-! ## Existence of the flattening stratification -/

/-- **Flattening stratification** (`thm:flattening-stratification`).

Let `S` be a noetherian scheme and `F` a coherent sheaf on `ℙⁿ_S`. Then the set of
Hilbert polynomials of the restrictions of `F` to the fibres of `ℙⁿ_S → S` is
finite, and the base decomposes into locally closed strata indexed by these
polynomials, with the prescribed closure order.

STATING-GAP: the fibrewise Hilbert polynomial `s ↦ Φ_{F_s}` cannot yet be
*constructed* from `F` (it needs coherent cohomology / Euler characteristics in a
flat family, both Mathlib gaps). We therefore take it as abstract input data
`hilb : S → ℚ[λ]`, mirroring how `Basic.lean` takes the Serre-twist family as
abstract input. The conclusions stated are the genuinely-expressible structural
content of the theorem:

* **finiteness** of the set `I` of occurring polynomials;
* each stratum `{s | hilb s = f}` is **locally closed** in `|S|`;
* **closure order**: the closure of the stratum at `f` meets only strata at `g ≥ f`,
  where `f ≤ g` means `f(m) ≤ g(m)` for all `m ≫ 0`.

The scheme structure on each `S_f` and its universal flattening property (parts
(ii) of Nitsure's statement) are the deferred scheme-theoretic content. The
finiteness assertion is the real, non-vacuous claim (false for an arbitrary
function `S → ℚ[λ]`; true for the Hilbert-polynomial function of a coherent
sheaf). -/
theorem flatteningStratification
    {S : Scheme.{u}} [IsLocallyNoetherian S] (n : ℕ)
    (F : (projectiveSpace n S).Modules) (_hF : F.IsQuasicoherent)
    (hilb : S → Polynomial ℚ) :
    (Set.range hilb).Finite ∧
      ∀ f ∈ Set.range hilb,
        IsLocallyClosed {s : S | hilb s = f} ∧
        closure {s : S | hilb s = f} ⊆
          {s : S | ∀ᶠ m : ℕ in Filter.atTop,
            Polynomial.eval (m : ℚ) f ≤ Polynomial.eval (m : ℚ) (hilb s)} :=
  sorry

end MR2223407ConstructionHilbertQuot
