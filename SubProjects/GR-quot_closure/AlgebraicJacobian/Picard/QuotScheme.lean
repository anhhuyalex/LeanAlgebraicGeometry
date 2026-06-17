/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The Quot scheme: Quot-foundations layer

This file packages the Quot-foundations layer of the
Grothendieck–Altman–Kleiman Quot-scheme construction. It introduces the
per-fiber Hilbert polynomial of a coherent sheaf, the Quot functor
`Quot^{Φ,L}_{E/X/S}` of `T`-flat coherent quotients, and the Grassmannian
*scheme* (Mathlib at the pinned commit carries only a linear-algebra
Grassmannian) together with its representability.

The 4 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.hilbertPolynomial` (def) — the
   **Hilbert polynomial function** `s ↦ Φ_{F,s} ∈ ℚ[λ]` of a coherent
   sheaf `F` on `X` over a finite-type `π : X ⟶ S` with respect to a
   line bundle `L`. Encoded as a function `S → Polynomial ℚ`.

2. `AlgebraicGeometry.Scheme.QuotFunctor` (def) — the **Quot
   functor** `Quot^{Φ,L}_{E/X/S} : (Sch/S)^op ⥤ Set` sending an
   `S`-scheme `T ⟶ S` to the set of equivalence classes
   `⟨F, q⟩` of pairs `(F, q)` with `F` a `T`-flat coherent sheaf on
   `X_T`, `q : E_T ↠ F` a surjection, and `F|_{X_t}` having Hilbert
   polynomial `Φ` at every `t ∈ T`.

3. `AlgebraicGeometry.Scheme.Grassmannian` (def) — the
   **Grassmannian functor** `Grass(V, d) : (Sch/S)^op ⥤ Set` of
   rank-`d` quotients of a locally free `O_S`-module `V`.

4. `AlgebraicGeometry.Scheme.Grassmannian.representable` (theorem)
   — the **representability of the Grassmannian** by a smooth projective
   `S`-scheme `Gr_S(V, d)` of relative dimension `d(r-d)`, equipped with
   the Plücker closed embedding into `ℙ_S(⋀^d V)`.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof",
each declaration carries a substantive, non-tautological type:

- `hilbertPolynomial` returns `Polynomial ℚ` keyed by `s : S`, not
  `Unit`; the Hilbert polynomial is a non-trivial invariant of the
  coherent sheaf at the fiber over `s`.
- `QuotFunctor` and `Grassmannian` return contravariant functors into
  `Type u` — substantive presheaves of sets, not constant functors.
- `Grassmannian.representable` packages the
  `Functor.RepresentableBy` Yoneda-bijection structure: existence of a
  scheme `Y` together with a `RepresentableBy Y` witness — substantive
  content (a representable functor is determined by its representing
  object up to canonical isomorphism, and the witness is the data of
  that isomorphism family).

## Mathlib status

Mathlib (master `b80f227`) provides:
- `AlgebraicGeometry.Scheme.Modules` (the category `X.Modules`),
- `Scheme.Modules.pullback`, `Scheme.Modules.pushforward` (the
  pullback–pushforward adjunction at level `i = 0`),
- `CategoryTheory.Functor.RepresentableBy` for representable functors,
- `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.IsLocallyNoetherian`
  (morphism / object property predicates), and
- `Polynomial` for `ℚ[λ]`.

Mathlib does NOT provide (at the pinned commit):
- a Grassmannian *scheme* (only a linear-algebra Grassmannian
  as a finite-rank-quotient variety),
- the Quot/Hilbert functor or its representability,
- Snapper's Lemma for the polynomial property of Euler characteristics.

## References

Blueprint: `blueprint/src/chapters/Picard_QuotScheme.tex`. Source:
Nitsure, "Construction of Hilbert and Quot Schemes", §1 (FGA Explained
Ch. 5, arXiv:math/0504020 pp. 5–35); cf. Hartshorne III.5.2.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Hilbert polynomial of a coherent sheaf

For a finite-type morphism `π : X ⟶ S` with `S` noetherian and a coherent
sheaf `F` on `X` whose schematic support is proper over `S` (here encoded
as plain `X.Modules` for the file-skeleton), the per-fiber Hilbert
polynomial is the function

`s ↦ Φ_{F,s} ∈ ℚ[λ],   Φ_{F,s}(m) = χ(X_s, F|_{X_s} ⊗ L_s^{⊗m})`.

Snapper's Lemma ensures this is a polynomial in `m`; the proof requires
graded-Euler-characteristic infrastructure and is not stated here.

Blueprint reference: `def:hilbert_polynomial` (Nitsure §1; cf. Hartshorne
III.5.2). -/

/-- The **Hilbert polynomial** of a coherent sheaf `F` on `X` over `S` at
the fiber over `s ∈ S` with respect to a line bundle `L` on `X`.

Encoded as a function `s ↦ Φ_{F,s} ∈ ℚ[λ]`. The defining formula

`Φ_{F,s}(m) = χ(X_s, F|_{X_s} ⊗ L_s^{⊗ m})
            = Σ_i (-1)^i dim_{κ(s)} H^i(X_s, F|_{X_s} ⊗ L_s^{⊗m})`

is a polynomial in `m` by Snapper's Lemma; the polynomial coefficients
depend on `s` through the fiber `F|_{X_s}`. When `F` is `S`-flat the
function `s ↦ Φ_{F,s}` is locally constant on `S`.

iter-177+: the body unfolds to the graded-Euler-characteristic
construction once `χ` of a coherent sheaf on a noetherian scheme +
Snapper's polynomial-eventually-property are in scope. For the iter-176
file-skeleton the body is a typed `sorry`. -/
noncomputable def hilbertPolynomial {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (_π : X ⟶ S) [LocallyOfFiniteType _π] (_L _F : X.Modules) (_s : S) :
    Polynomial ℚ :=
  sorry

/-! ## §2. The Quot functor

The Quot functor `Quot^{Φ,L}_{E/X/S}` sends an `S`-scheme `T ⟶ S` to the
set of equivalence classes `⟨F, q⟩` of pairs `(F, q)` where
- `F` is a coherent sheaf on `X_T = X ×_S T` whose schematic support is
  proper over `T` and which is `T`-flat,
- `q : E_T ↠ F` is a surjective `O_{X_T}`-linear homomorphism,
- the fiberwise Hilbert polynomial of `F|_{X_t}` with respect to `L|_{X_t}`
  equals `Φ` at every `t ∈ T`.

Two pairs `(F, q)` and `(F', q')` are equivalent iff `ker(q) = ker(q')`.

The Hilbert scheme is the special case `E = O_X`:
`Hilb^{Φ,L}_{X/S} = Quot^{Φ,L}_{O_X/X/S}`.

Blueprint reference: `def:quot_functor` (Nitsure §1; FGA Explained Ch. 5). -/

/-- The **Quot functor** `Quot^{Φ,L}_{E/X/S}` of coherent quotients of `E`
on `X ×_S -` with Hilbert polynomial `Φ`.

Encoded as a contravariant functor `(Over S)ᵒᵖ ⥤ Type u`, sending an
`S`-scheme `T → S` (i.e. an object of `Over S`) to the set of
equivalence classes `⟨F, q⟩` of pairs `(F, q)` of a `T`-flat coherent
sheaf `F` on `X ×_S T` with proper support and a surjection
`q : E_T ↠ F` whose fiberwise Hilbert polynomial is `Φ`, modulo
`ker(q) = ker(q')`. Functoriality is pullback of the quotient along
`X ×_S T' ⟶ X ×_S T`.

iter-177+: the body packages the on-objects / on-morphisms data using the
`Scheme.Modules.pullback` bifunctor on the relative product
`X ×_S T`, with the equivalence relation `ker(q) = ker(q')` quotiented
out via `Setoid` / `Quotient`. For the iter-176 file-skeleton the body
is a typed `sorry`. -/
noncomputable def QuotFunctor {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (_π : X ⟶ S) [LocallyOfFiniteType _π] (_L _E : X.Modules)
    (_Φ : Polynomial ℚ) :
    (Over S)ᵒᵖ ⥤ Type u :=
  sorry

end Scheme

/-! ## §3. The Grassmannian scheme

Since Mathlib carries no Grassmannian *scheme*, we encode it here as a
contravariant functor on `Over S` together with a representability
statement. The construction proceeds by gluing `binom(r, d)` affine
charts `U^I ≅ A^{d(r-d)}_S` along the Plücker cocycle, yielding a smooth
projective `S`-scheme `Gr_S(V, d)` of relative dimension `d(r-d)`,
equipped with a tautological rank-`d` quotient
`π* V ↠ U` and the Plücker closed embedding into `ℙ_S(⋀^d V)`.

Blueprint references: `def:grassmannian_scheme`,
`thm:grassmannian_representable` (Nitsure §1 Exercise (2),
"Construction of Grassmannian"; FGA Explained Ch. 5). -/

namespace Scheme

/-- The **Grassmannian functor** `Grass(V, d) : (Sch/S)^op ⥤ Set` of
rank-`d` quotients of a locally free `O_S`-module `V` of rank `r ≥ d`.

Encoded as the functor sending an `S`-scheme `T → S` to the set of
equivalence classes `⟨F, q⟩` of pairs `(F, q)` with
`q : V_T ↠ F` a surjection of `O_T`-modules and `F` locally free of
rank `d`, modulo `ker(q) = ker(q')`. Concretely
`Grass(V, d) = Quot^{d, O_S}_{V/S/S}` (the Quot functor for `X = S`,
`E = V`, constant Hilbert polynomial `d`).

iter-177+: the body re-exports `QuotFunctor (𝟙 S) (?) V Φ_d`, where
`Φ_d : Polynomial ℚ` is the constant polynomial `d`. For the iter-176
file-skeleton the body is a typed `sorry`. -/
noncomputable def Grassmannian {S : Scheme.{u}} [IsLocallyNoetherian S]
    (_V : S.Modules) (_d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u :=
  sorry

/-- **Representability of the Grassmannian.**

For a noetherian scheme `S`, a locally free `O_S`-module `V` of rank `r`,
and `1 ≤ d ≤ r`, the Grassmannian functor `Grass(V, d)` of
`Grassmannian` is representable by a smooth projective `S`-scheme
`Gr_S(V, d) ⟶ S` of relative dimension `d(r-d)`, equipped with a
tautological rank-`d` quotient `π* V ↠ U`. The determinant line bundle
`det(U)` is relatively very ample, giving a Plücker closed embedding
`Gr_S(V, d) ↪ ℙ_S(⋀^d V)`.

We package the conclusion as the existence of a representing
`Y : Over S` together with a `Functor.RepresentableBy Y` witness for
`Grassmannian V d`; the additional projective / smooth / Plücker
structure is implicit in the construction and is iter-177+ refinement
work (once the proof body lands).

iter-177+: the body follows Nitsure §1 "Construction of Grassmannian":
glue the `binom(r, d)` affine charts `U^I ≅ A^{d(r-d)}_S` along the
Plücker cocycle, verify separatedness via the diagonal cut, verify
properness by the DVR valuative criterion, build the tautological
quotient `U`, exhibit the Plücker embedding via the determinant line
bundle. For the iter-176 file-skeleton the body is a typed `sorry`. -/
theorem Grassmannian.representable {S : Scheme.{u}} [IsLocallyNoetherian S]
    (V : S.Modules) (d : ℕ) :
    ∃ (Y : Over S), Nonempty ((Grassmannian V d).RepresentableBy Y) := by
  sorry

end Scheme

/-! ## Project-local Mathlib supplement — Quot/Grassmannian predicates

These declarations build the support/freeness predicates of
`blueprint/src/chapters/Picard_QuotScheme.tex`, §"Support and freeness
predicates". Mathlib (at the pinned commit) carries no rank-`d` local
freeness predicate for sheaves of modules on a scheme, so it is built here. -/

namespace SheafOfModules

/-- **Locally free of rank `d`** for a sheaf of modules on a scheme.

A sheaf of modules `M` on a scheme `X` is *locally free of rank `d`* when `X`
admits an open cover `{U i}` on each member of which the restriction
`M|_{U i}` (the pullback of `M` along the open immersion `(U i).ι`) is
isomorphic to the free module of rank `d`, `O_{U i}^{⊕ d}` (encoded as
`SheafOfModules.free (ULift (Fin d))` over the structure-ring sheaf of the
open subscheme `(U i).toScheme`).

This predicate is project-local: Mathlib does not supply a rank-indexed local
freeness predicate for sheaves of modules on a scheme. Blueprint:
`def:is_locally_free_of_rank` (Nitsure §1, Exercise (2)). -/
def IsLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules) (d : ℕ) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens), (⨆ i, U i = ⊤) ∧
    ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj M ≅
      _root_.SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin d)))

end SheafOfModules

/-! ## Project-local Mathlib supplement — annihilator ideal sheaf and schematic support

These declarations build the annihilator ideal sheaf of a sheaf of modules and the
support/properness predicates of `blueprint/src/chapters/Picard_QuotScheme.tex`,
§"Support and freeness predicates". Mathlib (at the pinned commit) carries no
annihilator ideal sheaf for sheaves of modules on a scheme, nor a schematic-support
or proper-support predicate, so they are built here.

The annihilator is packaged via `Scheme.IdealSheafData.ofIdeals`, exactly mirroring
Mathlib's `Scheme.Hom.ker` (which is `ofIdeals fun U ↦ RingHom.ker (f.app U).hom`):
`ofIdeals` produces *the largest ideal sheaf contained in* an arbitrary affine-local
family of ideals, so the structure's `map_ideal_basicOpen` coherence is discharged
internally and need not be supplied at definition time. The basic-open coherence that
makes the local annihilators agree with `ofIdeals` (the analogue of `Hom.ker_apply`,
`def:modules_annihilator`) is the separate characterization lemma `annihilator_ideal`,
which depends on the not-yet-closed QCoh→localization bridge
`isLocalizedModule_basicOpen` (`lem:qcoh_section_localization_basicOpen`) together with
the algebra engine `Module.annihilator_isLocalizedModule_eq_map`
(`lem:annihilator_localization_eq_map`); see the handoff in
`task_results/.../QuotScheme.md`. -/

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The **annihilator ideal sheaf** of a sheaf of modules `F` on a scheme `X`
(`def:modules_annihilator`).

On each affine open `U`, the intended section is the annihilator
`Ann_{Γ(X,U)}(Γ(F,U))` of the `Γ(X,U)`-module of sections `Γ(F,U)`. The ideal sheaf
is assembled with `Scheme.IdealSheafData.ofIdeals`, the largest ideal sheaf contained
in that affine-local family — exactly the construction used for `Scheme.Hom.ker`. This
sidesteps proving the basic-open coherence (`map_ideal_basicOpen`) at definition time;
the identity `(annihilator F).ideal U = Ann_{Γ(X,U)}(Γ(F,U))` is the downstream
characterization lemma (`annihilator_ideal`, blocked on the QCoh localization bridge).

This is a project-local primitive: Mathlib does not carry an annihilator ideal sheaf
for sheaves of modules on a scheme. -/
noncomputable def annihilator (F : X.Modules) : X.IdealSheafData :=
  IdealSheafData.ofIdeals fun U => Module.annihilator Γ(X, U.1) Γ(F, U.1)

/-- The component of the annihilator ideal sheaf at an affine open is contained in the
module annihilator of the sections. This is the always-available (`ofIdeals`) direction
of the characterization; the reverse inclusion is the basic-open coherence blocked on
`isLocalizedModule_basicOpen`. Project-local because `annihilator` is. -/
lemma annihilator_ideal_le (F : X.Modules) (U : X.affineOpens) :
    (annihilator F).ideal U ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) :=
  IdealSheafData.ideal_ofIdeals_le _ _

/-- The **schematic support** of a sheaf of modules `F` on a scheme `X`
(`def:schematic_support`): the closed subscheme of `X` cut out by the annihilator
ideal sheaf `annihilator F`. Project-local because `annihilator` is. -/
noncomputable def schematicSupport (F : X.Modules) : Scheme.{u} :=
  (annihilator F).subscheme

/-- The canonical closed immersion of the schematic support into the ambient scheme,
realizing `schematicSupport F` as a closed subscheme of `X` (`def:schematic_support`).
This is the `IdealSheafData.subschemeι` of the annihilator ideal sheaf; it is a
`IsPreimmersion` + `QuasiCompact` immersion onto the support. Project-local because
`annihilator` is. -/
noncomputable def schematicSupportι (F : X.Modules) : schematicSupport F ⟶ X :=
  (annihilator F).subschemeι

/-- The sheaf of modules `F` **has proper support over `S` along `f`**
(`def:has_proper_support`): the composite of the schematic-support immersion with
`f : X ⟶ S` is a proper morphism. Since `AlgebraicGeometry.IsProper` is stable under
base change, this condition is preserved by pullback, as required by the Quot functor's
pullback action. Project-local because `schematicSupport` is. -/
def HasProperSupport {S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  IsProper (schematicSupportι F ≫ f)

end Scheme.Modules

end AlgebraicGeometry

/-! ## Project-local Mathlib supplement — annihilator under localization

The annihilator ideal sheaf `def:modules_annihilator` of a coherent sheaf is
built from the affine-local data `U ↦ Ann_{O(U)}(F(U))`, packaged as a
`Scheme.IdealSheafData`. The structure's coherence field `map_ideal_basicOpen`
requires the algebraic fact that, for a *finitely generated* module, the
annihilator commutes with localization:
`Ann(S⁻¹M) = (Ann M)·S⁻¹R`. Mathlib (at the pinned commit) does not carry this
-/

namespace Module

/-- For a finitely generated module `M` over a commutative ring `R`, the
annihilator commutes with localization: if `Rₚ` localizes `R` at a submonoid
`S` and `f : M →ₗ[R] Mₚ` localizes `M` at `S`, then the annihilator of `Mₚ`
over `Rₚ` is the extension (`Ideal.map` along `algebraMap R Rₚ`) of the
annihilator of `M` over `R`.

This is the abstract `IsLocalization`/`IsLocalizedModule` form, matching the
shape needed for the affine-basic-open coherence of the annihilator ideal sheaf
(`AlgebraicGeometry.Scheme.Modules.annihilator`, `def:modules_annihilator`):
the structure-sheaf restriction `Γ(X,U) → Γ(X, D(f))` is
`IsLocalization (powers f)`, and for a quasi-coherent `F` the section
restriction is `IsLocalizedModule (powers f)`.

Mathlib has no annihilator-localization lemma, so this is project-local. -/
end Module

/-! ## Project-local Mathlib supplement — quasi-coherent sections localize on a basic open

This section builds, bottom-up, toward the keystone
`lem:qcoh_section_localization_basicOpen`: for a quasi-coherent sheaf of modules `M`
on a scheme `X`, an affine open `U`, and `f ∈ Γ(X,U)`, the restriction
`M(U) → M(D(f))` exhibits `M(D(f))` as `IsLocalizedModule (powers f)` over `Γ(X,U)`.

The substance is the affine (Spec-local) computation: over `Spec R`, a quasi-coherent
sheaf is `Ñ = tilde N` for `N = Γ(M)`, and the basic-open restriction of `Ñ` is the
module localization map. Mathlib's `AlgebraicGeometry.tilde` namespace already carries
the localization fact for `tilde N` *as the map out of `N`* (the instance
`IsLocalizedModule (.powers f) (tilde.toOpen N (basicOpen f)).hom`). The first building
block below repackages this as a statement about the *presheaf restriction map* of `Ñ`
itself (from global sections to `D(f)`), which is the form the downstream scheme-level
argument consumes after the affine identification `M|_U ≅ Ñ`.

Mathlib (at the pinned commit) does **not** prove that an arbitrary quasi-coherent sheaf
on `Spec R` lies in the essential image of `tilde` (the comment in
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` says this "will later be shown"); the
equivalence `QCoh(Spec R) ≃ Mod R` is a genuine gap. Consequently the keystone for an
*arbitrary* quasi-coherent `M` is gated on that bridge (`IsQuasicoherent M → IsIso
M.fromTildeΓ`); the building blocks here are stated for `tilde N` directly, and for a
general `M : (Spec R).Modules` under the explicit hypothesis `[IsIso M.fromTildeΓ]`
(equivalently, `M` in the essential image of `tilde`). -/

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- **Basic-open restriction of a `tilde` sheaf is a module localization.**

For `N : ModuleCat R` and `f : R`, the presheaf restriction map of the associated sheaf
`Ñ = tilde N` from global sections `Γ(Ñ, ⊤)` to the basic open `Γ(Ñ, D(f))` exhibits the
latter as `IsLocalizedModule (powers f)` over `R`.

This is the affine, Spec-local heart of `lem:qcoh_section_localization_basicOpen`. Mathlib
carries the localization fact for the map `tilde.toOpen N (D f) : N → Γ(Ñ, D(f))` out of
`N`; since `tilde.toOpen N ⊤ : N → Γ(Ñ, ⊤)` is an isomorphism and
`tilde.toOpen N (D f) = tilde.toOpen N ⊤ ≫ restriction` (`tilde.toOpen_res`), precomposing
the localization map with the inverse isomorphism (`IsLocalizedModule.of_linearEquiv_right`)
transfers the property to the restriction map. Project-local: Mathlib states the fact only
for the map out of `N`, not for the presheaf restriction of `Ñ`. -/
/-- **Basic-open restriction localizes, for a sheaf in the essential image of `tilde`.**

For a sheaf of modules `M` on `Spec R` whose tilde-Gamma counit `M.fromTildeΓ` is an
isomorphism (equivalently, `M` lies in the essential image of the `tilde` functor — the
honest Spec-affine stand-in for quasi-coherence, see the section header), the presheaf
restriction map of `M` from global sections `Γ(M, ⊤)` to the basic open `Γ(M, D(f))`
exhibits the latter as `IsLocalizedModule (powers f)` over `R`.

This transports `isLocalizedModule_tilde_restrict` across the isomorphism
`M.fromTildeΓ : tilde N ⟶ M` (where `N = Γ(M, ⊤)`): the induced presheaf isomorphism is
natural in the open, so on each of `⊤` and `D(f)` it provides an `R`-linear isomorphism
intertwining the two restriction maps. Post- and pre-composing the localization map for
`tilde N` with these isomorphisms (`IsLocalizedModule.of_linearEquiv`,
`IsLocalizedModule.of_linearEquiv_right`) yields the property for `M`.

Project-local: it is the affine engine of `lem:qcoh_section_localization_basicOpen`. The
general quasi-coherent case additionally requires the (currently Mathlib-absent) bridge
`IsQuasicoherent M → IsIso M.fromTildeΓ`. -/
/-- A morphism of sheaves of `R`-modules on `Spec R` that is an isomorphism on every basic open
`D(f)` is an isomorphism. This is the "isomorphism on a basis ⟹ isomorphism" reduction specialised
to the basic-open basis of `Spec R` (`PrimeSpectrum.isBasis_basic_opens`): injectivity on stalks is
`stalkFunctor_map_injective_of_isBasis`, surjectivity on stalks is the basic-open germ lift, and
`isIso_of_stalkFunctor_map_iso` concludes. Project-local glue used to assemble `IsIso M.fromTildeΓ`
from per-basic-open section data. -/
/-- A linear map intertwining two localizations of the same module at the same submonoid is
bijective: if `f : M →ₗ M'` and `g : M →ₗ M''` both exhibit a localization at `S` and
`h : M' →ₗ M''` satisfies `h ∘ₗ f = g`, then `h` is bijective (it is the canonical localization
isomorphism `IsLocalizedModule.linearEquiv`). Stated with the two `IsLocalizedModule` facts as
explicit hypotheses to avoid typeclass-diamond ambiguity at the call site. -/
/-- **`IsIso M.fromTildeΓ` from per-basic-open section localization** (the cheap stalk/section
assembly of `lem:qcoh_affine_isIso_fromTildeΓ`, the blueprint "G1-assemble" step). If for every
`f : R` the section restriction `Γ(M, ⊤) → Γ(M, D(f))` of a sheaf of modules `M` on `Spec R`
exhibits the target as `IsLocalizedModule (powers f)` over `R` — exactly the conclusion of G1-core
(`lem:qcoh_affine_section_localization`,
`isLocalizedModule_basicOpen_of_isQuasicoherent`) — then the tilde-Gamma counit `M.fromTildeΓ` is
an isomorphism (equivalently `M` lies in the essential image of `tilde`).

On each basic open `D(f)` the component of `modulesSpecToSheaf.map M.fromTildeΓ` is a map between
two localizations of `N = Γ(M, ⊤)` at `powers f`: the source `Γ(tilde N, D(f))` localizes via the
instance `tilde.toOpen N (D f)` and the target `Γ(M, D(f))` localizes by hypothesis, and the two
localization maps are intertwined by `Scheme.Modules.toOpen_fromTildeΓ_app`. Hence the component is
the canonical localization isomorphism (`IsLocalizedModule.linearEquiv`);
`isIso_sheaf_of_isIso_app_basicOpen` upgrades this to an isomorphism of sheaves, and
`modulesSpecToSheaf` being fully faithful reflects it to `IsIso M.fromTildeΓ`.

This turns the remaining keystone obligation into exactly G1-core: combined with the converse engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`, the per-basic-open localization hypothesis is
*equivalent* to `IsIso M.fromTildeΓ`. Project-local: Mathlib has no `IsQuasicoherent → IsIso
fromTildeΓ` bridge. -/
/-- **Characterization of `IsIso M.fromTildeΓ` by section localization.** For a sheaf of modules
`M` on `Spec R`, the tilde-Gamma counit `M.fromTildeΓ` is an isomorphism iff for every `f : R` the
section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as `IsLocalizedModule (powers f)`.

The forward direction is the affine engine `isLocalizedModule_restrict_of_isIso_fromTildeΓ`; the
reverse is `isIso_fromTildeΓ_of_isLocalizedModule_restrict`. Combined with G1-core
(`isLocalizedModule_basicOpen_of_isQuasicoherent`, `lem:qcoh_affine_section_localization`, not yet
formalized) — which supplies the right-hand side for any quasi-coherent `M` — this yields gap1
(`lem:qcoh_affine_isIso_fromTildeΓ`). Project-local. -/
/-! ## Project-local Mathlib supplement — G1-core (Route F) building blocks

The keystone G1-core `lem:qcoh_affine_section_localization` asks: for a *quasi-coherent*
`M : (Spec R).Modules` and `f : R`, the section restriction `Γ(M,⊤) → Γ(M,D(f))` is
`IsLocalizedModule (powers f)`. Via `isIso_fromTildeΓ_iff_isLocalizedModule_restrict` this is
*equivalent* to `IsIso M.fromTildeΓ` — i.e. to the statement that a quasi-coherent sheaf on an
affine scheme lies in the essential image of `tilde` (the `QCoh(Spec R) ≃ Mod R` equivalence). That
equivalence is a genuine Mathlib gap at the pinned commit (Tilde.lean only proves the *globally
presented* case, `isIso_fromTildeΓ_of_presentation`).

The composition lemma below discharges the **globally-presented** sub-case end to end (it is the
Route-F endpoint once a global presentation/tilde identification is in hand). The residual gap is
exactly the production of a global presentation/tilde from local (quasi-coherent) data on `Spec R`;
see the handoff in `task_results/.../QuotScheme.md`. -/

/-- **Basic-open restriction localizes, for a globally presented module.** If `M : (Spec R).Modules`
admits a global `SheafOfModules.Presentation`, then for every `f : R` the section restriction
`Γ(M,⊤) → Γ(M,D(f))` exhibits the target as `IsLocalizedModule (powers f)` over `R`.

This is the composition of Mathlib's `isIso_fromTildeΓ_of_presentation` (a global presentation
forces `M.fromTildeΓ` to be an isomorphism, i.e. `M` is a `tilde`) with the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`. It is the Route-F endpoint for the
globally-presented case; the general quasi-coherent case additionally requires producing a global
presentation/tilde identification from the (Mathlib-absent) affine `QCoh(Spec R) ≃ Mod R` bridge.
Project-local. -/
/-- **`map_units` field of G1-core (Route F), for any sheaf of modules.** For `M : (Spec R).Modules`
and `f : R`, every element of `Submonoid.powers f` acts invertibly on the sections `Γ(M, D(f))` over
`R`. This is exactly the first field `IsLocalizedModule.map_units` of the target
`isLocalizedModule_basicOpen_of_isQuasicoherent`, in the shape the 3-field constructor consumes.

It holds for an *arbitrary* `M` (no quasi-coherence needed): on `D(f)` the element `f` already maps
to a unit of the structure ring `Γ(O_{Spec R}, D(f))` (the away-localization
`IsLocalization.Away.algebraMap_isUnit`), and the `R`-action on `Γ(M, D(f))` factors through it via
the scalar tower `R → Γ(O, D(f)) → Γ(M, D(f))`. Packaged from Mathlib's
`AlgebraicGeometry.tilde.isUnit_algebraMap_end_basicOpen`. Project-local only as the *named* field
of the Route-F decomposition; the substance of G1-core is `surj`/`exists_of_eq` (see handoff). -/
/-- **Finite basic-open cover refining a quasi-coherent presentation cover.** Given a
sheaf of modules `M` on `Spec R` together with quasi-coherent data `q` (a — possibly
infinite — open cover `q.X : q.I → (Spec R).Opens` of `⊤` with a presentation of
`M.over (q.X i)` on each member), there is a *finite* family of elements `t : Finset R`
whose basic opens cover `Spec R` (`Ideal.span t = ⊤`), with each basic open `D(r)`
(`r ∈ t`) contained in some member `q.X i` of the presentation cover.

This is the topological "finite-cover front" of `lem:exists_isIso_fromTildeΓ_basicOpen_cover`:
quasi-compactness of `Spec R` plus the basic-open basis (`PrimeSpectrum.isBasis_basic_opens`)
refine `q.X` to a finite basic-open subcover; the cover condition `q.coversTop` is read off the
`Opens.grothendieckTopology` sieve via `Sieve.mem_ofObjects_iff`, and finiteness is extracted
through `Ideal.span_eq_top_iff_finite`. To obtain `q` from `[M.IsQuasicoherent]`, take
`‹M.IsQuasicoherent›.nonempty_quasicoherentData.some`.

The remaining (heavy) step toward gap1 — transporting each presentation `q.presentation i`
of `M.over (q.X i)` across `D(r) ≅ Spec R_r` to `IsIso ((M|_{D(r)}).fromTildeΓ)` — is the
site-slice ↔ scheme-pullback transport, which has no Mathlib support at the pinned commit.
Project-local: Mathlib has no affine quasi-coherent → finite presentation cover lemma. -/
/-! ## Project-local Mathlib supplement — the over-site ↔ open-subspace sheaf equivalence

The gap1 slice-to-geometric bridge `lem:over_restrict_iso` (`overRestrictIso`) rests on an
equivalence of *sheaf* categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`
induced by the equivalence of underlying sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`. Mathlib carries `Opens.overEquivalence` but leaves
the *continuity* of its two functors and the induced sheaf-category equivalence as an explicit TODO
(see `Mathlib/Topology/Sheaves/Over.lean`: "show that both functors of the equivalence
`overEquivalence U` are continuous and induce an equivalence between
`Sheaf ((Opens.grothendieckTopology X).over U) A` and `Sheaf (Opens.grothendieckTopology U) A`").

This section fills that TODO. The two cover-lifting (`IsCocontinuous`) facts are the substance:
a sieve covers in the Grothendieck-topology-over-`U` exactly when its image under the slice
forgetful functor covers in the ambient space, and that condition matches the pointwise covering
condition on the open subspace `↥U` because `Subtype.val : ↥U → X` is an injective open embedding.
From the two cocontinuities, `Equivalence.isDenseSubsite_inverse_of_isCocontinuous` produces the
dense-subsite hypothesis and `Equivalence.sheafCongr` produces the sheaf equivalence.

It is the foundational (purely topological / topos-theoretic) layer of the slice-to-geometric
transport; the remaining steps toward `overRestrictIso` (identifying the sliced structure sheaf
`O_X.over U` with the open subscheme's structure sheaf `U.toScheme.ringCatSheaf` under this
equivalence, then lifting to sheaves of modules via `pushforwardPushforwardEquivalence` and relating
to `Scheme.Modules.restrictFunctor U.ι`) are the geometric layer above it. -/

section OverSiteSheafEquivalence

open TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] (U : Opens X)

/-- The functor of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
`U`-slice of the ambient Grothendieck topology to the Grothendieck topology of the open
subspace `↥U`. Foundational layer of the gap1 slice-to-geometric bridge `overRestrictIso`;
fills the `Mathlib/Topology/Sheaves/Over.lean` TODO. Project-local. -/
instance overEquivalence_functor_isCocontinuous :
    (Opens.overEquivalence U).functor.IsCocontinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) where
  cover_lift := by
    intro Y S hS
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hxU : x ∈ U := leOfHom Y.hom hx
    have hmem : (⟨x, hxU⟩ : ↥U) ∈ (Opens.overEquivalence U).functor.obj Y := hx
    obtain ⟨V, h, hSh, hxV⟩ := hS ⟨x, hxU⟩ hmem
    have hVle : (V : Set ↥U) ⊆ Subtype.val ⁻¹' (Y.left : Set X) := leOfHom h
    set W : Opens X := ⟨Subtype.val '' (V : Set ↥U),
      (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 V.isOpen⟩ with hWdef
    have hWle : W ≤ Y.left := by
      intro y hy; obtain ⟨z, hzV, rfl⟩ := hy; exact hVle hzV
    refine ⟨W, homOfLE hWle, ?_, ⟨⟨x, hxU⟩, hxV, rfl⟩⟩
    rw [Sieve.overEquiv_iff]
    change S ((Opens.overEquivalence U).functor.map (Over.homMk (homOfLE hWle)))
    have hdomle :
        (Opens.overEquivalence U).functor.obj (Over.mk ((homOfLE hWle) ≫ Y.hom)) ≤ V := by
      intro z hz
      obtain ⟨z', hz'V, hz'eq⟩ := (hz : (z : X) ∈ (W : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'V
    convert S.downward_closed hSh (homOfLE hdomle) using 1

/-- The inverse of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
Grothendieck topology of the open subspace `↥U` to the `U`-slice of the ambient Grothendieck
topology. Foundational layer of the gap1 slice-to-geometric bridge `overRestrictIso`;
fills the `Mathlib/Topology/Sheaves/Over.lean` TODO. Project-local. -/
instance overEquivalence_inverse_isCocontinuous :
    (Opens.overEquivalence U).inverse.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) where
  cover_lift := by
    intro W S hS
    rw [GrothendieckTopology.mem_over_iff] at hS
    intro y hy
    have hpy : (y : X) ∈ ((Opens.overEquivalence U).inverse.obj W).left := ⟨y, hy, rfl⟩
    obtain ⟨P, f, hSf0, hpP⟩ := hS (y : X) hpy
    rw [Sieve.overEquiv_iff] at hSf0
    have hPle : (P : Set X) ⊆ ((Opens.overEquivalence U).inverse.obj W).left := leOfHom f
    set V : Opens ↥U :=
      ⟨Subtype.val ⁻¹' (P : Set X), P.isOpen.preimage continuous_subtype_val⟩ with hVdef
    have hVle : V ≤ W := by
      intro z hz
      obtain ⟨z', hz'W, hz'eq⟩ := hPle (hz : (z : X) ∈ (P : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'W
    refine ⟨V, homOfLE hVle, ?_, hpP⟩
    change S ((Opens.overEquivalence U).inverse.map (homOfLE hVle))
    have hdomle : ((Opens.overEquivalence U).inverse.obj V).left ≤ P := by
      intro p hp; obtain ⟨p', hp'V, rfl⟩ := hp; exact hp'V
    convert S.downward_closed hSf0 (Over.homMk (homOfLE hdomle) ?_) using 1
    · apply Subsingleton.elim

/-- The dense-subsite witness for the inverse of `Opens.overEquivalence U`, assembled from the two
cover-lifting facts above. Project-local glue for `overEquivalence_sheafCongr`. -/
instance overEquivalence_inverse_isDenseSubsite :
    (Opens.overEquivalence U).inverse.IsDenseSubsite
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- The functor of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
inverse and the equivalence adjunction `inverse ⊣ functor`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. Project-local. -/
instance overEquivalence_functor_isContinuous :
    (Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) := by
  haveI : (Opens.overEquivalence U).symm.functor.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs ((Opens.overEquivalence U).inverse.IsCocontinuous _ _)
  exact (Opens.overEquivalence U).symm.toAdjunction.isContinuous_of_isCocontinuous _ _

/-- The inverse of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
functor and the equivalence adjunction `functor ⊣ inverse`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. Project-local. -/
instance overEquivalence_inverse_isContinuous :
    (Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  (Opens.overEquivalence U).toAdjunction.isContinuous_of_isCocontinuous _ _

/-- **The over-site ↔ open-subspace sheaf equivalence.** For a topological space `X`, an open
`U ⊆ X`, and any category `A`, the equivalence of sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`
lifts to an equivalence of sheaf categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

This is exactly the equivalence left as a TODO in `Mathlib/Topology/Sheaves/Over.lean`. It is the
foundational layer of the gap1 slice-to-geometric bridge (`lem:over_restrict_iso`,
`overRestrictIso`): once the sliced structure sheaf `O_X.over U` is identified with the structure
sheaf of the open subscheme `U.toScheme` under this equivalence, a presentation of `M.over U`
transports (via `pushforwardPushforwardEquivalence` + `restrictFunctorIsoPullback`) to a geometric
presentation of `M|_U`. Project-local: Mathlib supplies only the underlying site equivalence. -/
noncomputable def overEquivalence_sheafCongr (A : Type*) [Category A] :
    Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A :=
  (Opens.overEquivalence U).sheafCongr
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) A

end OverSiteSheafEquivalence

/-! ## Project-local Mathlib supplement — the slice-to-geometric module bridge (gap1, C)

This section builds the geometric layer of the gap1 slice-to-geometric bridge
`lem:over_restrict_iso` on top of the topological `overEquivalence_sheafCongr` of the previous
section. It identifies, on the level of *sheaves of modules*, the abstract Grothendieck-slice
restriction `M.over U` (a sheaf of modules over the sliced structure sheaf `O_X.over U` on the slice
site `J.over U`) with the geometric restriction `(restrictFunctor U.ι).obj M` on the small Zariski
site of the open subscheme `U.toScheme`.

The key structural facts, all holding *definitionally* at the pinned commit, are:
* `(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor` (`rfl`): the inverse leg
  of the site equivalence, post-composed with the slice-forgetful functor, is the opens functor of
  the open immersion `U.ι`;
* consequently `U.toScheme.ringCatSheaf = (overEquivalence_sheafCongr U RingCat).functor.obj
  (X.ringCatSheaf.over U)` (`rfl`): the structure sheaf of the open subscheme is the transport of
  the sliced structure sheaf across the ring-valued sheaf equivalence (this is *step 2*, the
  geometric ring-sheaf identification, discharged by `rfl`).

From these, `SheafOfModules.pushforwardPushforwardEquivalence` lifts the site equivalence to an
equivalence of categories of sheaves of modules (`overRestrictEquiv`, *step 3*), under whose functor
the sliced module `M.over U` corresponds to the geometric restriction (`overRestrictIso`, *step 4*).

Mathlib (at the pinned commit) supplies only the underlying site equivalence and the
`pushforward`/`restrictFunctor` machinery; the assembly is project-local. -/

section OverRestrictBridge

open TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The slice-to-geometric equivalence of categories of sheaves of modules** (gap1, C, step 3).

For a scheme `X` and an open `U ⊆ X`, the category of sheaves of modules over the sliced structure
sheaf `O_X.over U` on the slice site `J.over U` is equivalent to the category `U.toScheme.Modules`
of sheaves of modules on the open subscheme `U.toScheme`. The equivalence is obtained by lifting the
topological site equivalence `Opens.overEquivalence U` (and its ring-valued sheaf congruence
`overEquivalence_sheafCongr`) to sheaves of modules via
`SheafOfModules.pushforwardPushforwardEquivalence`; the two ring-sheaf comparison morphisms it
consumes are the (co)unit of `Opens.overEquivalence U` whiskered into the structure presheaf, and
the identity (the geometric structure sheaf being *definitionally* the transport of the sliced one).

Project-local: it is the module-level layer of the gap1 bridge `lem:over_restrict_iso`; Mathlib
supplies only the underlying site equivalence. -/
noncomputable def overRestrictEquiv :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ≌ U.toScheme.Modules :=
  letI eqv := Opens.overEquivalence U
  (SheafOfModules.pushforwardPushforwardEquivalence
      (J := (Opens.grothendieckTopology ↥X).over U) (K := Opens.grothendieckTopology ↥U) eqv
    (S := X.ringCatSheaf.over U) (R := U.toScheme.ringCatSheaf)
    (Sheaf.Hom.mk (Functor.whiskerRight (NatTrans.op eqv.unitIso.inv) (X.ringCatSheaf.over U).obj))
    (Sheaf.Hom.mk (𝟙 _))
    (by ext : 2
        simp only [Sheaf.Hom.mk, Functor.comp_obj, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, NatTrans.op_app, NatTrans.id_app,
          ObjectProperty.homMk_hom, NatTrans.comp_app]
        exact congrArg (Sheaf.over X.ringCatSheaf U).obj.map
          (congrArg Quiver.Hom.op (Equivalence.unitInv_app_inverse eqv _).symm))
    (by ext : 2
        simp only [Sheaf.Hom.mk, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          NatTrans.op_app, ObjectProperty.homMk_hom, NatTrans.comp_app, NatTrans.id_app,
          Functor.comp_obj]
        erw [Category.id_comp, ← Functor.map_comp]
        rename_i x
        have h : (eqv.unitIso.inv.app (Opposite.unop x)).op ≫ (eqv.unit.app (Opposite.unop x)).op
            = 𝟙 _ := by
          rw [← op_comp]
          simp
        exact (congrArg (Sheaf.over X.ringCatSheaf U).obj.map h).trans
          (CategoryTheory.Functor.map_id _ _))).symm

/-- **Step-4 functor identification of the gap1 bridge.** The composite of `SheafOfModules.over · U`
with the slice-to-geometric equivalence `overRestrictEquiv U` is the geometric restriction functor
`restrictFunctor U.ι` along the open immersion `U.ι`. Both are pushforwards along the immersion's
opens functor (`(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor`, `rfl`); the
two ring-sheaf comparison morphisms agree, so the identification is `pushforwardComp` followed by
`pushforwardCongr`. Project-local. -/
noncomputable def overRestrictFunctorIso :
    (SheafOfModules.pushforward (S := X.ringCatSheaf.over U) (𝟙 _)) ⋙
        (overRestrictEquiv U).functor ≅ restrictFunctor U.ι :=
  haveI : ((Opens.overEquivalence U).inverse ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp (Opens.overEquivalence U).inverse (Over.forget U)
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥X)
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr (by cat_disch)

/-- **The slice-to-geometric isomorphism on an object** (gap1, C, step 4): for a sheaf of modules
`M` on `X`, the transport of the abstract Grothendieck-slice restriction `M.over U` under the
slice-to-geometric equivalence `overRestrictEquiv U` is canonically isomorphic to the geometric
restriction `(restrictFunctor U.ι).obj M`. This is the object-level form of
`overRestrictFunctorIso`; composed with `restrictFunctorIsoPullback` it lands the geometric
restriction as the pullback `U.ι^* M`. Project-local: the load-bearing slice-touching ingredient of
the gap1 transport `lem:over_restrict_iso`. -/
noncomputable def overRestrictIso (M : X.Modules) :
    (overRestrictEquiv U).functor.obj (M.over U) ≅ (restrictFunctor U.ι).obj M :=
  (overRestrictFunctorIso U).app M

/-- **The slice-to-geometric isomorphism in pullback form** (gap1, C, step 4'): the transport of the
abstract Grothendieck-slice restriction `M.over U` under `overRestrictEquiv U` is canonically
isomorphic to the inverse-image (pullback) `U.ι^* M` of `M` along the open immersion `U.ι`. This is
`overRestrictIso` composed with Mathlib's `restrictFunctorIsoPullback`; it is the form a
presentation of `M.over U` transports into a presentation of the geometric pullback `U.ι^* M`.
Project-local. -/
noncomputable def overRestrictPullbackIso (M : X.Modules) :
    (overRestrictEquiv U).functor.obj (M.over U) ≅ (Scheme.Modules.pullback U.ι).obj M :=
  overRestrictIso U M ≪≫ (restrictFunctorIsoPullback U.ι).app M

end Scheme.Modules

end OverRestrictBridge

/-! ## Project-local Mathlib supplement — slice-to-geometric presentation transport (gap1, P1)

This section builds the geometric milestone of the gap1 per-element transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U` is transported, across the slice-to-geometric
bridge `overRestrictPullbackIso` (gap1, C), into a `SheafOfModules.Presentation` of the *geometric*
restriction `(Scheme.Modules.pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`.

The load-bearing ingredient is the unit-iso `overRestrictUnitIso`: the slice-to-geometric
equivalence functor `(overRestrictEquiv U).functor` (definitionally a `SheafOfModules.pushforward`
along the equivalence-of-sites inverse with the *identity* ring comparison) sends the
structure-sheaf module `unit` to `unit`. This is exactly the `F.obj (unit R) ≅ unit S` datum that
`SheafOfModules.Presentation.map` consumes; once it is in hand, `Presentation.map` +
`Presentation.ofIsIso` (across `overRestrictPullbackIso`) realise the transport. The unit-iso rests
on the general fact `isIso_unitToPushforwardObjUnit_of_isIso'`: the canonical map
`unit S ⟶ (pushforward ψ).obj (unit R)` is an iso whenever the ring-sheaf comparison `ψ` is
(here `ψ = 𝟙`).

Mathlib (at the pinned commit) supplies `SheafOfModules.unitToPushforwardObjUnit` and proves it iso
only under a finality hypothesis on the site functor (`PullbackFree.lean`); the
`IsIso ψ ⟹ IsIso (unitToPushforwardObjUnit ψ)` route used here, and the slice transport, are
project-local. -/

section SliceGeometricPresentation

open CategoryTheory Limits TopologicalSpace Topology

/-- **`unitToPushforwardObjUnit` is an isomorphism when the ring-sheaf comparison is.**

For a continuous functor `F` of sites and a morphism of ring sheaves
`ψ : S ⟶ (F.sheafPushforwardContinuous …).obj R` that is an isomorphism, the canonical map
`unitToPushforwardObjUnit ψ : unit S ⟶ (pushforward ψ).obj (unit R)` is an isomorphism. Its
component on each object is `(forget₂ RingCat AddCommGrpCat).map (ψ.hom.app _)`, iso as `ψ` is;
the conclusion follows by the reflect-isomorphism functors `SheafOfModules.toSheaf` and
`sheafToPresheaf` together with `NatTrans.isIso_iff_isIso_app`.

Project-local: Mathlib proves `unitToPushforwardObjUnit` iso only under a finality hypothesis on `F`
(`SheafOfModules.PullbackFree`); this `IsIso ψ`-driven form is the one the slice-to-geometric
unit-iso `overRestrictUnitIso` (gap1, P1) consumes (with `ψ = 𝟙`). -/
namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **The slice-to-geometric equivalence functor sends `unit` to `unit`** (gap1, P1).

For an open `U ⊆ X`, the functor of the slice-to-geometric equivalence `overRestrictEquiv U`
(definitionally `SheafOfModules.pushforward` along `(Opens.overEquivalence U).inverse` with the
identity ring comparison) carries the sliced structure-sheaf module `unit (O_X.over U)` to the
structure-sheaf module `unit (U.toScheme.ringCatSheaf)` of the open subscheme. This is the
`F.obj (unit R) ≅ unit S` datum consumed by `SheafOfModules.Presentation.map` in
`overRestrictPresentation`. Project-local. -/
/-- **Slice presentation ⟹ geometric-restriction presentation** (gap1, P1).

Given a sheaf of modules `M` on `X`, an open `U ⊆ X`, and a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U`, there is a `SheafOfModules.Presentation` of the
*geometric* restriction `(pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`. The
transport is `Presentation.map` along the slice-to-geometric equivalence functor (using the unit-iso
`overRestrictUnitIso`) followed by `Presentation.ofIsIso` across the bridge
`overRestrictPullbackIso` (gap1, C).

This closes the slice-touching step of the gap1 per-element transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): with `U = q.X i` and
`P = q.presentation i` it produces a global presentation of `U.ι^* M`; the remaining geometric step
restricts further to a basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. Project-local. -/
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Geometric restriction to a cover member is globally presented** (gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q` and an index `i`, the geometric
restriction `(pullback (q.X i).ι).obj M = (q.X i).ι^* M` of `M` to the open subscheme
`(q.X i).toScheme` admits a `SheafOfModules.Presentation`. It is `overRestrictPresentation` applied
to the slice presentation `q.presentation i : (M.over (q.X i)).Presentation` supplied by the
quasi-coherence datum.

This is the per-cover-member output that feeds the affine descent of the gap1 transport
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent` (P1): for `D(r) ≤ q.X i` one further restricts this
presentation to the basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. The heartbeat headroom tames the slice-site
`IsRightAdjoint`/`HasSheafify` synthesis blow-up that `Presentation.map` triggers across the
equivalence functor (the same `backward.isDefEq.respectTransparency false` incantation Mathlib's own
`QuasicoherentData.bind` uses). Project-local. -/
end Scheme.Modules

end SliceGeometricPresentation

/-! ## Project-local Mathlib supplement — basic-open presentation descent (gap1, P1 keystone)

This section assembles the gap1 per-element keystone
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent`
(`isIso_fromTildeΓ_restrict_basicOpen`): on a basic open `D(r)` contained in a cover member
`q.X i` of the quasi-coherence data, the restricted sheaf `M|_{D(r)}` is a geometric tilde, i.e.
its `fromTildeΓ` counit is an isomorphism.

The route follows the affine descent of the recipe, building on the slice-to-geometric presentation
transport of the previous section:

1. `presentationPullbackιOfQuasicoherentData M q i` is a *global* `Presentation` of the geometric
   restriction `N := (q.X i).ι^* M` on the open subscheme `Z := (q.X i).toScheme`.
2. For any open `W ⊆ Z`, the global presentation `PN` slices to a slice presentation `N.over W` via
   the single `Presentation.map` of the over-functor `pushforward (𝟙 …)` (the
   `QuasicoherentData.ofPresentation` template — no iterated-slice equivalence is needed because
   `PN` is already a global presentation on the genuine scheme `Z`).
3. `overRestrictPresentation W N PNW` transports it to a global presentation of the geometric
   restriction `(pullback W.ι).obj N` on the open subscheme `W.toScheme`.
4. For `W` *affine*, `IsAffineOpen.isoSpec` identifies `W.toScheme ≅ Spec Γ(Z, W)`; transporting the
   presentation across this iso (whose `Opens.map` is `Final`, so `pullbackObjUnitToUnit` is an iso)
   lands a global presentation on the genuine affine `Spec Γ(Z, W)`.
5. A global presentation forces `fromTildeΓ` to be an isomorphism
   (`isIso_fromTildeΓ_of_presentation`).

Mathlib (at the pinned commit) carries no `QCoh(Spec R) ≃ Mod R` essential-image bridge; this descent
is project-local. -/

section BasicOpenPresentationDescent

open CategoryTheory Limits TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Presentation of the geometric restriction of `M` to an open `W` of a cover member** (gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and *any* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction
`(pullback W.ι).obj ((pullback (q.X i).ι).obj M)` of `M` (pulled back to `Z := (q.X i).toScheme`,
then to `W`) admits a `SheafOfModules.Presentation` on the open subscheme `W.toScheme`.

It slices the *global* presentation `presentationPullbackιOfQuasicoherentData M q i` of
`N := (q.X i).ι^* M` on `Z` down to the slice `N.over W` (a single `Presentation.map` of the
over-functor — the `QuasicoherentData.ofPresentation` template, no iterated-slice equivalence
needed since `PN` is global on the genuine scheme `Z`), then geometrizes via
`overRestrictPresentation`. Project-local: feeds the affine descent of the gap1 keystone
`isIso_fromTildeΓ_restrict_basicOpen`. -/
/-- **The opens functor of an iso of schemes is an equivalence of opens sites.** For `φ : Y ≅ Z`,
the inverse-image functor `Opens.map φ.inv.base : Opens ↥Y ⥤ Opens ↥Z` is an equivalence (with
inverse `Opens.map φ.hom.base`), assembled from the pseudofunctoriality isos `Opens.mapComp` /
`Opens.mapId`. Its purpose is to supply the `Final` instance that makes `pullbackObjUnitToUnit` an
isomorphism in `pullbackSchemeIsoUnitIso`. Project-local. -/
/-- **The opens functor of an iso of schemes is final.** Immediate from
`opensMapEquivOfIso` (an equivalence is final); the `Final` fact needed by
`pullbackObjUnitToUnit`. Supplied via `haveI` at use sites (instance resolution cannot invert
`φ.inv.base`). Project-local. -/
/-- **Pullback along an iso of schemes sends the unit module to the unit module** (gap1, P1).

For an isomorphism of schemes `φ : Y ≅ Z`, the pullback functor along `φ.inv : Z ⟶ Y` carries the
structure-sheaf (unit) module of `Y` to that of `Z`. The underlying canonical comparison
`pullbackObjUnitToUnit` is an isomorphism because the site functor `Opens.map φ.inv.base` of an iso
of schemes is `Final` (`opensMap_final_of_schemeIso`). This is the `F.obj (unit R) ≅ unit S` datum
consumed by `Presentation.map` along `pullback φ.inv` in `presentationPullbackOfSchemeIso`.
Project-local. -/
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **A presentation transports across the pullback by an iso of schemes** (gap1, P1, step 4).

Given an isomorphism of schemes `φ : Y ≅ Z` and a `SheafOfModules.Presentation` of a module `N` on
`Y`, the geometric pullback `(pullback φ.inv).obj N` of `N` to `Z` admits a presentation. It is
`Presentation.map` along the colimit-preserving pullback functor `pullback φ.inv`, using the unit-iso
`pullbackSchemeIsoUnitIso φ`. This is the affine-identification transport step of the gap1 keystone:
applied with `φ` the `IsAffineOpen.isoSpec` of the affine restriction, it moves the presentation onto
a genuine `Spec`. Project-local. -/
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-coherent restricts to a tilde on every affine open of a cover member** (gap1, P1).

For a sheaf of modules `M` on `X` with quasi-coherence data `q`, an index `i`, and an *affine* open
`W ⊆ (q.X i).toScheme` of the cover-member subscheme, the geometric restriction of `M` to the affine
`Spec Γ((q.X i).toScheme, W) ≅ W` (pulled back to `Z := (q.X i).toScheme`, then to `W`, then across
the affine identification `IsAffineOpen.isoSpec`) has an isomorphism `fromTildeΓ` counit — i.e. it is
a geometric tilde.

This is the geometric heart of the gap1 per-element transport: the slice presentation supplied by
the quasi-coherence datum geometrizes (`presentationPullbackιRestrict`) to a global presentation on
`W.toScheme`, which transports across the affine iso (`presentationPullbackOfSchemeIso`) to a global
presentation on the genuine affine `Spec Γ(Z, W)`; a global presentation forces `fromTildeΓ` to be an
isomorphism (`isIso_fromTildeΓ_of_presentation`). Project-local: Mathlib has no
`QCoh(Spec R) ≃ Mod R` essential-image bridge. -/
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-coherent restricts to a tilde on each basic open of the cover** (gap1, P1 keystone,
`lem:isIso_fromTildeΓ_basicOpen_of_quasicoherent`).

Let `M` be a sheaf of modules on `Spec R` with quasi-coherence data `q`, and let `r : R` with
`D(r) ≤ q.X i` for some cover member. Then the geometric restriction of `M` to the affine basic open
`D(r)` — realised as the preimage `W := (q.X i).ι ⁻¹ᵁ D(r)` inside the cover-member subscheme
`Z := (q.X i).toScheme`, transported across the affine identification `W ≅ Spec Γ(Z, W)` (which is
`Spec R_r` since `D(r)` is affine) — has an isomorphism `fromTildeΓ` counit, i.e. `M|_{D(r)}` is a
geometric tilde.

This is the per-element step of gap1: it is the affine instance `W = (q.X i).ι ⁻¹ᵁ D(r)` of
`isIso_fromTildeΓ_presentationPullback`, with affineness of `W` from
`IsAffineOpen.Spec_basicOpen` (`D(r)` is affine in `Spec R`) and
`IsAffineOpen.preimage_of_isOpenImmersion` (its preimage under the open immersion `(q.X i).ι` is
affine, using `D(r) ≤ q.X i = (q.X i).ι.opensRange`). Project-local. -/
/-! ## Project-local Mathlib supplement — gap1-D: the section-localization descent

The keystone `isLocalizedModule_basicOpen_descent` reduces (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`) to a finite-cover sheaf-gluing argument.  The single geometric input
is the **per-cover-element** fact that on each `D(r)` of a finite cover `{D(r_j)}` of `Spec R`
(with `D(r_j) ≤ q.X i`), the basic-open restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a
localization at `powers f` — this is exactly the P1 local-tilde data transported to sections, and
is the gated hypothesis `Hfr` below.  Given `Hfr` (for every `r` whose `D(r)` sits inside a cover
member, hence also for the overlaps `D(r r')`), the descent is pure sheaf theory: separatedness
gives the `exists_of_eq` field, gluing the patched compatible family gives `surj'`, and the global
`map_units` field holds for arbitrary `M` (`map_units_restrict_basicOpen`). -/

/-- A finite family `t` spanning `R` gives a basic-open cover of `Spec R`: the supremum of the
`D(r)` over `r ∈ t` is `⊤`.  Project-local glue feeding the sheaf-gluing reduction of the
section-localization descent. -/
/-- Restriction maps of `modulesSpecToSheaf.obj M` compose: restricting `A → B → C` equals the
direct restriction `A → C`.  Poset-hom uniqueness makes the two intermediate morphisms compose to
the direct one.  Project-local bookkeeping for the section-localization descent. -/
/-- **Separatedness/torsion field of the section-localization descent.**  Given the
per-cover-element localization data `Hfr` (on each `D(r)` of a finite basic-open cover `{D(r)}` of
`Spec R`, the restriction `Γ(M, D(r)) → Γ(M, D(f) ⊓ D(r))` is a localization at `powers f`), any
global section `x` that restricts to `0` on `D(f)` is killed by a power of `f`.  This is the
`exists_of_eq` engine of `isLocalizedModule_basicOpen_descent`: per cover element a power of `f`
kills `x|_{D(r)}` (`IsLocalizedModule.exists_of_eq` of `Hfr`), the finite sup of these powers kills
every `x|_{D(r)}`, and sheaf separatedness over the cover (`TopCat.Sheaf.eq_of_locally_eq'`) lifts
this to `f^n • x = 0`.  Project-local: the geometric content (`Hfr`) is the gated P1 tilde data. -/
/-- **Overlap agreement for the surjectivity field.**  If a section `br` on `D(r)` satisfies the
normalized identity `ρ[D(r), D(f) ⊓ D(r)] br = f^N • (y|_{D(f) ⊓ D(r)})`, then for any open
`U ≤ D(r)` its restriction to `U`, pushed down to `D(f) ⊓ U`, equals `f^N • (y|_{D(f) ⊓ U})`.
Specializing `U` to an overlap `D(r) ⊓ D(r')` shows the normalized sections of two cover members
agree there after restriction to `D(f) ⊓ (D(r) ⊓ D(r'))`, which (via the per-overlap localization)
makes a common `f`-power glue them.  Project-local bookkeeping for `descent_surj`. -/
/-- **Surjectivity field of the section-localization descent.**  With the per-cover-element (and
per-overlap) localization data `Hfr`, every section `y` over `D(f)` becomes, after multiplying by a
power of `f`, the restriction of a global section.  The classical Hartshorne II.5.3 argument: each
`D(r)` of a finite basic-open cover `{D(r)}` of `Spec R`, `y|_{D(f) ⊓ D(r)}` is `f^{-N}` times the
restriction of a section `b_r` on `D(r)` (`IsLocalizedModule.surj` of `Hfr` at `D(r)`, with a common
power `N`); on overlaps the `b_r` agree after a further power `f^P` (`descent_overlap_agree` +
`IsLocalizedModule.exists_of_eq` of `Hfr` at `D(r) ⊓ D(r')`), so `f^P • b_r` glue
(`TopCat.Sheaf.existsUnique_gluing'`) to a global `x` with `x|_{D(f)} = f^{N+P} • y` (by sheaf
separatedness over the cover `{D(f) ⊓ D(r)}` of `D(f)`).  Project-local: `Hfr` is the gated P1
local-tilde data. -/
/-- **Section-localization descent from a local-tilde cover (gap1 keystone, D), cover form.**  Let
`M` be a sheaf of modules on `Spec R` and `f : R`.  Suppose `{D(r)}_{r ∈ t}` is a finite basic-open
cover of `Spec R` (`Ideal.span t = ⊤`) and for every open `U` contained in some cover member `D(r)`
(in particular each `D(r)` and each overlap `D(r) ⊓ D(r')`) the basic-open restriction
`Γ(M, U) → Γ(M, D(f) ⊓ U)` is a localization at `powers f` (`Hfr` — the gated P1 local-tilde data).
Then the section restriction `Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

This is the project-internal finite-equalizer/flatness descent of Stacks `lemma-invert-f-sections`
(Hartshorne II.5.3), built without the global affine `QCoh(Spec R) ≃ Mod R` equivalence (which is
gap1 itself): `map_units` holds for arbitrary `M` (`map_units_restrict_basicOpen`), `surj'` is
`descent_surj`, and `exists_of_eq` is `descent_smul_eq_zero`.  The named gap1 keystone
`isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma instantiated at the cover
`exists_finite_basicOpen_cover_le_quasicoherentData` once `Hfr` is produced from
`isIso_fromTildeΓ_restrict_basicOpen` (the slice→Spec-`R_r` section transport, the remaining gated
step).  Project-local. -/
/-- **Section-localization descent from a local-tilde cover, basic-open hypothesis form.**

Same conclusion as `isLocalizedModule_basicOpen_descent_of_cover`, but the per-cover-element
localization data `Hfr` need only be supplied for *basic* opens `D(s) ≤ D(r)` (rather than every
open `U ≤ D(r)`).  This is the **instantiable** form of the cover-descent: the per-element P1
transport produces a localization only on the basic opens of the affine slice `Spec R_r` — a general
open of `Spec R_r` need not be quasi-compact, so the global Stacks `lemma-invert-f-sections` is
unavailable for it — while the sheaf-gluing engines `descent_surj`/`descent_smul_eq_zero` only ever
consult `Hfr` at the basic opens `D(r)` and the overlaps `D(r) ⊓ D(r') = D(r·r')`.

It rebuilds the three `IsLocalizedModule` fields directly: `map_units` is
`map_units_restrict_basicOpen` (holds for arbitrary `M`), `surj` is `descent_surj` fed the basic-open
`Hfr` (the open `U` it consults is always `D(s)`, so `Hfr s` supplies the datum after `U = D(s)` is
substituted), and `exists_of_eq` is `descent_smul_eq_zero` fed `Hfr` at each `D(r)`.  Project-local:
the named gap1 keystone `isLocalizedModule_basicOpen_descent` for quasi-coherent `M` is this lemma
instantiated at the cover `exists_finite_basicOpen_cover_le_quasicoherentData`, with the basic-open
`Hfr` produced from the P1 transport `isIso_fromTildeΓ_restrict_basicOpen`. -/
/-! ## Project-local Mathlib supplement — `IsLocalizedModule` transport for gap1-D Hfr

The section-transport iso `gammaPullbackImageIso` is only an additive-group (`Ab`) isomorphism,
semilinear over the *source-scheme* section ring, whereas the `Hfr` hypothesis of
`isLocalizedModule_basicOpen_descent_of_cover` is an `IsLocalizedModule` statement `R`-linear over
the base ring `R`. Two Mathlib-absent transport ingredients bridge the gap:

* **(I)** `isLocalizedModule_of_ringEquiv_semilinear` — transport `IsLocalizedModule S g` across a
  ring-iso-`σ`-semilinear `AddEquiv` pair. Mathlib only has the same-ring `of_linearEquiv` /
  `of_linearEquiv_right`; the section iso crosses a ring iso, so this is the genuine gap.
* **(II)** `isLocalizedModule_restrictScalars_powers_algebraMap` — a localization at
  `powers (algebraMap R Rr f)` over a base-changed ring `Rr` (here `R` localized at `r`) is, after
  restriction of scalars, a localization at `powers f` over `R`.

Both are pure module algebra and Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **(I) Ring-iso-semilinear `IsLocalizedModule` transport.** Given a ring isomorphism
`σ : R ≃+* R'`, two `σ`-semilinear additive isomorphisms `e₁ : M₁ ≃+ N₁`, `e₂ : M₂ ≃+ N₂` (i.e.
`eᵢ (a • x) = σ a • eᵢ x`), and an `R'`-linear map `h : N₁ →ₗ[R'] N₂` intertwining a localization
map `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the map `h` is a localization at the image submonoid
`S.map σ`. Mathlib only provides the same-ring `IsLocalizedModule.of_linearEquiv`; this crosses a
ring iso, the form needed to turn the `Ab`/semilinear section iso `gammaPullbackImageIso` into the
`R`-linear `Hfr` data. Project-local. -/
/-- **(II) Localization at a base-changed submonoid descends to the base ring.** If `g` is
`Rr`-linear and exhibits a localization at `powers (algebraMap R Rr f)` over a base-changed ring
`Rr` (an algebra over `R` — here `R` localized at some `r`), then its restriction of scalars to `R`
is a localization
at `powers f` over `R`. This lets the `R_r`-level localization that P1 (`IsIso fromTildeΓ`) produces
on the slice `Spec R_r` be read back as the `R`-level `Hfr` data the cover-form descent consumes.
Mathlib-absent; project-local. -/
/-! ## Project-local Mathlib supplement — gap1-D Hfr: pullback-section transport

The remaining gated ingredient of the named gap1 keystone
`isLocalizedModule_basicOpen_descent` is the **section-level** analogue of P1's object-level
transport: for an open immersion `f : X ⟶ Y` and a sheaf of modules `M` on `Y`, the sections of the
geometric pullback `(pullback f).obj M` over an open `U ⊆ X` are canonically identified with the
sections of `M` over the image `f ''ᵁ U`.

The construction is `Γ(-, U)` applied to the inverse of Mathlib's `restrictFunctorIsoPullback f`
(`restrictFunctor f ≅ pullback f`) at `M`, using the *definitional* identity
`Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` (`Scheme.Modules.restrict_obj`, `rfl`). Because
both sides are `Γ(-, U)` of a single fixed module isomorphism, naturality in `U` (intertwining the
presheaf restriction maps) is free: it is the naturality of the underlying abelian-presheaf
morphism. Mathlib-absent at the pinned commit; project-bespoke. -/

/-- **Global sections of a pullback along an open immersion are sections over the image**
(gap1, Hfr section transport, general open). For an open immersion `f : X ⟶ Y`, a sheaf of modules
`M` on `Y`, and an open `U ⊆ X`, the additive groups of sections satisfy
`Γ((pullback f).obj M, U) ≅ Γ(M, f ''ᵁ U)`. This is `Γ(-, U)` of `(restrictFunctorIsoPullback f)⁻¹`
at `M`; the codomain is `Γ((restrictFunctor f).obj M, U) = Γ(M, f ''ᵁ U)` definitionally. Naturality
in `U` is `gammaPullbackImageIso_hom_naturality`. -/
/-- **The pullback-section comparison intertwines the restriction maps** (gap1, Hfr, naturality).
For opens `V ≤ U` of `X`, `gammaPullbackImageIso` commutes with the presheaf restriction maps of
`(pullback f).obj M` and of `M` (along the image inclusion `f ''ᵁ V ≤ f ''ᵁ U`). This is the
naturality of the underlying morphism of abelian presheaves. -/
/-- **Global sections of a pullback along an open immersion are sections over the range**
(gap1, Hfr section transport). The `U = ⊤` instance of `gammaPullbackImageIso`:
`Γ((pullback f).obj M, ⊤) ≅ Γ(M, f.opensRange)`, using `f ''ᵁ ⊤ = f.opensRange`. Once this lands the
named-form descent `isLocalizedModule_basicOpen_descent` and gap1 follow. -/
/-- **Open-immersion structure-sheaf ring iso on an image open** (gap1, Hfr semilinearity).
For an open immersion `j : X ⟶ Y` and an open `V ⊆ X`, the immersion is an isomorphism onto its
image `j ''ᵁ V`, so pulling structure-sheaf sections back gives a ring isomorphism
`σ_V : Γ(X, V) ≃+* Γ(Y, j ''ᵁ V)`. This is `(j.appIso V)⁻¹` packaged as a `RingEquiv`; it is the
`σ` along which `gammaPullbackImageIso_hom_semilinear` is semilinear, the form bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear` consumes.

The direction is source `→` image (so `σ_V a` lands in `Γ(Y, j ''ᵁ V)` for `a : Γ(X, V)`, the
section ring acting on the pullback module's sections). Project-local. -/
/-- **Semilinearity of the pullback section transport** (gap1 semilinearity wall). The forward map
of `gammaPullbackImageIso` is `σ_V`-semilinear (`σ_V = gammaImageRingEquiv`): for `a : Γ(X, V)` a
section of the structure sheaf and `x` a section of the pullback module,
`hom (a • x) = σ_V a • hom x`. The pullback-side action is the structure-sheaf action through
the pullback's `mapPresheaf`; the action on the `M` side is `M`'s action through `σ_V`.
Project-local. -/
/-! ## Project-local Mathlib supplement — gap1-D Hfr: combined algebra transport

The two `IsLocalizedModule` bridges (I) `isLocalizedModule_of_ringEquiv_semilinear` and (II)
`isLocalizedModule_restrictScalars_powers_algebraMap` are chained into a single transport lemma:
the localization that P1 (`IsIso fromTildeΓ`) produces on the slice `Spec R_r` (a localization at
`powers f'` over the section ring `S`) is read back, across the `σ`-semilinear section isos and the
base change `R → A` (`A = R_r`), as a localization at `powers f` over the base ring `R`. -/

/-- **(I)+(II) combined: ring-iso-semilinear localization transport descending to the base ring.**

Given a base ring `R`, an `R`-algebra `A`, a ring iso `σ : S ≃+* A` carrying `f' : S` to
`algebraMap R A f`, a localization `g` at `powers f'` over `S`, two `σ`-semilinear additive
isomorphisms `e₁, e₂` onto `A`-modules (also `R`-modules via the scalar tower `R → A`), and an
`A`-linear map `h` intertwining `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the restriction of
scalars of `h` to `R` is a localization at `powers f` over `R`.

This is the algebra core of the gap1 `Hfr` transport: bridge (I)
(`isLocalizedModule_of_ringEquiv_semilinear`) moves the localization across the ring iso to
`powers (algebraMap R A f)` over `A`, then bridge (II)
(`isLocalizedModule_restrictScalars_powers_algebraMap`) descends it to `powers f` over `R`.
Project-local. -/
/-- **`IsIso M.fromTildeΓ` is invariant under isomorphism of modules.** If `M ≅ M'` as sheaves of
modules on `Spec R` and `M.fromTildeΓ` is an isomorphism, then so is `M'.fromTildeΓ`.

Immediate from `isIso_fromTildeΓ_iff` (`IsIso M.fromTildeΓ ↔ M ∈ essImage (tilde.functor R)`) and the
fact that the essential image is closed under isomorphism (`Functor.essImage.ofIso`). This is the
transport that lets P1's `IsIso fromTildeΓ` for the iterated-pullback module
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι).obj M))` be carried to the pullback
`(pullback j).obj M` along the single composite open immersion `j = isoSpec.inv ≫ ι_W ≫ ι` (which is
isomorphic to the iterated one via the `pullbackComp` coherences). Project-local. -/
/-! ## Project-local Mathlib supplement — gap1 section-transport producer

The geometric producer chain manufacturing the basic-open `Hfr` datum from the per-element P1
transport. See blueprint subsection "Section-transport producer for the basic-open Hfr". -/

/-- **Composite open immersion `j : Spec Γ(q.X i, ι⁻¹ᵁ D(s)) ⟶ Spec R`** identifying the affine
slice with the basic open `D(s)`.  It is `isoSpec.inv ≫ ι_W ≫ ι_{q.X i}` where
`W := ι_{q.X i}⁻¹ᵁ D(s)`; the domain is the genuine affine `Spec` of the slice's section ring.
Project-local: the geometric backbone of the section-transport producer. -/
noncomputable def compositeBasicOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    Spec Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ⟶ Spec R :=
  ((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
      (by rw [Scheme.Opens.opensRange_ι]; exact hs)).isoSpec.inv ≫
    Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ≫
    Scheme.Opens.ι (q.X i)

/-- **(producer, a) `fromTildeΓ` iso of the composite-immersion pullback.** For a quasi-coherent
`M` on `Spec R` and a basic open `D(s) ≤ q.X i`, the pullback module `(pullback j).obj M` along the
composite immersion `j = compositeBasicOpenImmersion` has an isomorphism `fromTildeΓ` counit.

The geometric content is the P1 keystone `isIso_fromTildeΓ_restrict_basicOpen`, which supplies
`IsIso fromTildeΓ` for the *iterated* pullback
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι_{q.X i}).obj M))`; the iterated and the
composite pullbacks are identified by the `pullbackComp` pseudofunctor coherences, and
`isIso_fromTildeΓ_of_iso` transports the isomorphism across. Project-local: the critical first
ingredient of the section-transport producer. -/
/-- The composite immersion `j = compositeBasicOpenImmersion` is an open immersion (composite of an
iso and two open immersions). Needed for `.opensRange`, `''ᵁ`, and `gammaImageRingEquiv` on `j`. -/
instance compositeBasicOpenImmersion_isOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsOpenImmersion (compositeBasicOpenImmersion M q s i hs) := by
  unfold compositeBasicOpenImmersion
  infer_instance

/-- **(producer, b) Range of the composite immersion is `D(s)`.** The open range of
`j = compositeBasicOpenImmersion` is exactly the basic open `D(s)`: `isoSpec.inv` is an iso (its
range is `⊤`), so the range is `ι_{q.X i} ''ᵁ (ι_{q.X i}⁻¹ᵁ D(s)) = (q.X i) ⊓ D(s) = D(s)` using
`D(s) ≤ q.X i`. Project-local image bookkeeping for the section-transport producer. -/
/-! ## Project-local Mathlib supplement — gap1 section-transport producer (b-flocus/c/d/TOP)

The remaining producer chain assembling the basic-open `Hfr` datum (consumed by
`isLocalizedModule_basicOpen_descent_of_basicOpen_cover`) from the per-element P1 transport
`pullback_composite_immersion_isIso_fromTildeΓ` via the algebra combiner
`isLocalizedModule_powers_transport`.  See blueprint "Section-transport producer for the basic-open
Hfr". -/

/-- **Image of an affine basic open under an open immersion of affines.** For an open immersion
`j : Spec S ⟶ Spec R` and `f' : S`, the image `j ''ᵁ D(f')` is the `Spec R` scheme basic open of the
transported global section `(j.appIso ⊤).inv ((ΓSpecIso S).inv f')`.  Pure geometry:
`basicOpen_eq_of_affine` turns `D(f')` into the scheme basic open of a global structure section of
`Spec S`, and `Scheme.image_basicOpen` transports it across `j`.  Stated with `j` opaque so the
`rw` does not unfold a concrete composite immersion.  Project-local. -/
/-- **(producer, b-flocus, image of a basic open).** The image under
`j = compositeBasicOpenImmersion`
of a basic open `D(f')` of the affine slice is the `Spec R` basic open of the transported section
`(j.appIso ⊤).inv ((ΓSpecIso _).inv f')`.  Instantiates `image_basicOpen_of_affine` at the concrete
composite immersion.  Project-local. -/
/-- **Image of an affine basic open as an intersection with the range.** If the appIso-transport of
`f'` agrees with the restriction to `j ''ᵁ ⊤` of a global section `g : Γ(Spec R, ⊤)`, then
`j ''ᵁ D(f') = (j ''ᵁ ⊤) ⊓ (Spec R).basicOpen g`.  Combines `image_basicOpen_of_affine` with the
structure-sheaf identity `Scheme.basicOpen_res`.  Project-local. -/
set_option maxHeartbeats 1600000 in
-- Large multi-step assembly (localization combiner + `eqToHom` open-transport); needs headroom.
/-- **(producer, TOP-aux) Basic-open `Hfr` along an abstract affine open immersion.**  For an open
immersion `j : Spec S ⟶ Spec R` with `IsIso (fromTildeΓ ((pullback j).obj M))` (the P1 datum), a
ring element `f : R` and a slice element `f' : S` whose appIso-transport is the restriction of `f`
(`hf'`), and target opens `U = j ''ᵁ ⊤`, `V = j ''ᵁ D(f')`, the section restriction
`Γ(M, U) → Γ(M, V)` is `IsLocalizedModule (powers f)` over `R`.

The proof assembles the P1 object-level `IsIso fromTildeΓ` into a section-level localization via the
algebra combiner `isLocalizedModule_powers_transport`: the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes `Γ(M',⊤) → Γ(M', D(f'))` over the slice
ring `S`; the `σ`-semilinear section isos `e₁ = gammaPullbackImageIso ⊤`,
`e₂ = gammaPullbackImageIso D(f')` (over `σ = (ΓSpecIso S)⁻¹ ≪≫ gammaImageRingEquiv ⊤`) and the
restriction map `h` intertwine it, and the combiner descends the result to `powers f` over `R`.
Finally the `j ''ᵁ`-form opens are transported to `U` / `V` via `eT`, `eB`.  `j` is kept abstract so
the section-ring defeqs stay cheap.
Project-local: the abstract core of the gap1 keystone `Hfr` producer. -/
/-- **(producer, TOP) Basic-open `Hfr` from the per-element P1 transport.**  For a quasi-coherent
`M` on `Spec R`, a basic open `D(s) ≤ q.X i`, and `f : R`, the section restriction
`Γ(M, D(s)) → Γ(M, D(f) ⊓ D(s))` is `IsLocalizedModule (powers f)` over `R`.  This is the gated
basic-open `Hfr` datum consumed by `isLocalizedModule_basicOpen_descent_of_basicOpen_cover`.

Thin wrapper around `section_localization_hfr_aux`: it instantiates the abstract open immersion at
the concrete composite immersion `j = compositeBasicOpenImmersion`, supplies the P1 datum
`pullback_composite_immersion_isIso_fromTildeΓ`, picks `f' = σ⁻¹(algebraMap R A f)` (so `hf'` is
`σ.apply_symm_apply`), and identifies the `j ''ᵁ`-form opens with `D(s)` (`opensRange`) and
`D(f) ⊓ D(s)` (`image_basicOpen_eq_inf`).  Project-local: the geometric producer of the gap1
keystone `Hfr`. -/
/-! ## Project-local Mathlib supplement — gap2 single-chart transport

The general-scheme keystone `lem:qcoh_section_localization_basicOpen`
(`isLocalizedModule_basicOpen`): for a quasi-coherent sheaf of modules `M` on an *arbitrary* scheme
`X`, an affine open `U`, and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, D(f))` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

It is the single-chart affine transport on top of G1-core: pull `M` back along the affine immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X` (range `U`), so the pullback `M'` is quasi-coherent on
`Spec Γ(X, U)`, where gap1 gives `IsIso M'.fromTildeΓ`; the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction over `Γ(X, U)`, and
the `σ`-semilinear section comparison `gammaPullbackImageIso` (bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear`) transports it to the `M`-side restriction. No
cover-and-glue: `U` is already affine, so there is a single chart. -/

/-- **The `Γ(X,U)`-linear section restriction map of a sheaf of modules.** For `M : X.Modules` and
an inclusion of opens `i : V ⟶ U`, the presheaf restriction `Γ(M, U) → Γ(M, V)` is `Γ(X, U)`-linear
when `Γ(M, V)` carries the `Γ(X, U)`-module structure restricted along `X.presheaf.map i.op`
(`Module.compHom`). Linearity is `Scheme.Modules.map_smul`. Project-local: the linear-map packaging
of the section restriction needed to state `IsLocalizedModule` for a general scheme (Mathlib's
presheaf-of-modules restriction is semilinear, not bundled this way). -/
/-- **The `Γ(X,U)`-linear restriction of sections to a basic open `D(f)`** (`f : Γ(X, U)`). The
section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is `Γ(X, U)`-linear, where `Γ(M, X.basicOpen f)`
carries any `Γ(X, U)`-module structure compatible (via `IsScalarTower`) with its native
`Γ(X, X.basicOpen f)`-module structure and the canonical `Γ(X, U)`-algebra map
`Γ(X, U) → Γ(X, X.basicOpen f)` (the restriction `X.presheaf.map`). Linearity combines
`Scheme.Modules.map_smul` with the scalar tower. This is the consumer-facing shape of the gap2
keystone (instances supplied by the caller, matching `Module.annihilator_isLocalizedModule_eq_map`).
Project-local. -/
/-- **`fromSpec`-section coherence** (gap2 transport crux). For an affine open `U` of a scheme `X`,
the `eqToHom`-transport `Γ(X, hU.fromSpec ''ᵁ ⊤) → Γ(X, U)` (along the equality
`hU.fromSpec ''ᵁ ⊤ = U`) equals the composite ring iso
`(hU.fromSpec.appIso ⊤).hom ≫ (ΓSpecIso Γ(X, U)).hom`. Equivalently, the section ring iso
`σ = (ΓSpecIso)⁻¹ ≫ gammaImageRingEquiv (fromSpec) ⊤` underlying the gap2 section comparison is, up to
this `eqToHom` transport, the identity. This is the coherence needed to read the gap2-core
localization (over `Γ(X, hU.fromSpec ''ᵁ ⊤)`, at `powers (σ f)`) back as a localization over
`Γ(X, U)` at `powers f`. Proof: `fromSpec_app_self` + `appIso_hom'` + cancellation of the
`Spec Γ(X, U)`-presheaf maps (all between `⊤`, hence forced by `Subsingleton`). Project-local. -/
/-- **(gap2 core) Basic-open section localization along an abstract affine open immersion.** For an
open immersion `j : Spec S ⟶ X` with the P1 datum `IsIso (fromTildeΓ ((pullback j).obj M))`, a slice
element `f' : S`, and `f : Γ(X, j ''ᵁ ⊤)` with `σ f' = f` (`σ = (ΓSpecIso S)⁻¹ ≫ gammaImageRingEquiv
j ⊤`), the section restriction `Γ(M, j ''ᵁ ⊤) → Γ(M, j ''ᵁ D(f'))` is
`IsLocalizedModule (powers f)` over `Γ(X, j ''ᵁ ⊤)`.

The proof mirrors `section_localization_hfr_aux` but over an arbitrary ambient scheme `X` (so the
localization ring is the *local* section ring `A = Γ(X, j ''ᵁ ⊤)`, not a global `R`): the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction `g` over `S`, the
`σ`-semilinear section comparisons `e₁, e₂` (`gammaPullbackImageIso`) intertwine `g` with the
`M`-side restriction `h = restrictₗ M ii`, and bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear` transports the localization across `σ`, landing
`powers ((powers f').map σ) = powers (σ f') = powers f`. Because the base and target rings coincide
(`R = A`), no `restrictScalars` base-change (bridge II) is needed. Project-local. -/
/-- **(gap1 keystone) Section-localization descent for quasi-coherent `M`.**  For a quasi-coherent
sheaf of modules `M` on `Spec R` and `f : R`, the global-to-`D(f)` section restriction
`Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

Instantiates the cover-form descent `isLocalizedModule_basicOpen_descent_of_basicOpen_cover` at the
finite basic-open cover `exists_finite_basicOpen_cover_le_quasicoherentData` refining the
quasi-coherent data `q`, with the per-element basic-open `Hfr` supplied by the producer
`section_localization_hfr_basicOpen` (each cover overlap `D(s) ≤ D(r) ≤ q.X i` feeds the producer at
`i`).  Project-local: the named gap1 keystone (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`), built without the global affine `QCoh ≃ Mod` equivalence. -/
/-- **(gap1) `IsIso M.fromTildeΓ` for quasi-coherent `M`.**  The tilde-Gamma counit of a
quasi-coherent sheaf of modules on `Spec R` is an isomorphism (equivalently, `M` lies in the
essential image of `tilde`).  This is the affine quasi-coherent ⟺ `tilde` bridge that Mathlib leaves
open at the pinned commit.

Immediate from the keystone `isLocalizedModule_basicOpen_descent` (per-basic-open section
localization for quasi-coherent `M`) via the section-to-counit assembly
`isIso_fromTildeΓ_of_isLocalizedModule_restrict`.  Project-local: closes gap1. -/
/-- **G1-core: section-localization for a quasi-coherent sheaf on `Spec R`**
(`lem:qcoh_affine_section_localization`). For a quasi-coherent sheaf of modules `M` on `Spec R` and
`f : R`, the section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as the localized module
`(powers f)⁻¹ Γ(M, ⊤)`, i.e. it is `IsLocalizedModule (powers f)` over `R`.

This is the clean named form of gap1's downstream corollary: gap1
(`isIso_fromTildeΓ_of_isQuasicoherent`) makes `M.fromTildeΓ` an isomorphism, and the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` then delivers all three `IsLocalizedModule` fields
at once. Project-local: Mathlib has no `QCoh(Spec R) → section-localization` bridge. It is the
affine `X = Spec R`, `U = ⊤` instance of the general-scheme keystone
`isLocalizedModule_basicOpen` (gap2). -/
set_option maxHeartbeats 1600000 in
-- The multi-step eqToHom open-transport + bridge-(I) ring-iso assembly needs heartbeat headroom.
/-- **(gap2, Piece B — the eqToHom bridge)** Basic-open section localization from the gap2-core,
given the P1 datum directly.  For a sheaf of modules `M` on a scheme `X`, an affine open `U`, the P1
hypothesis `hP1 : IsIso (fromTildeΓ ((pullback hU.fromSpec).obj M))`, and `f : Γ(X, U)`, the
consumer-facing basic-open section restriction `restrictBasicOpenₗ M f` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

This is the mechanical eqToHom bridge from `section_localization_hfr_aux_general` (instantiated at
the affine immersion `j = hU.fromSpec`, slice element `f' = f`, image section `f_im = σ f`) to
`restrictBasicOpenₗ`: the open identifications `j ''ᵁ ⊤ = U` (`eT`) and
`j ''ᵁ D(f) = X.basicOpen f` (`IsAffineOpen.fromSpec_image_basicOpen`) plus the section ring iso
`ρ = X.presheaf.map (eqToHom eT.symm).op : Γ(X, j ''ᵁ ⊤) ≃+* Γ(X, U)` transport the localization
across (bridge (I) `isLocalizedModule_of_ringEquiv_semilinear`), the only non-trivial coherence
being `ρ (σ f) = f`, supplied by the crux `fromSpec_image_top_section_coherence`.  Project-local:
separates the genuinely-new QC-pullback (Piece A) from the mechanical transport. -/
/-! ## Project-local Mathlib supplement — pullback of QC along an open immersion (gap2, Piece A)

Route-1 chain L1–L6 building `isQuasicoherent_pullback_fromSpec`: the pullback of a quasi-coherent
sheaf of modules along the affine immersion `hU.fromSpec : Spec Γ(X, U) → X` is again quasi-coherent.
This is the QC-pullback input the gap2 final close `isLocalizedModule_basicOpen` feeds to gap1
(`isIso_fromTildeΓ_of_isQuasicoherent`). -/

/-- **(Piece A, L1) The inverse slice-equivalence functor sends `unit` to `unit`.**
Dual to `overRestrictUnitIso`: the inverse functor of `overRestrictEquiv V` carries the
structure-sheaf (unit) module of the open subscheme `V.toScheme` to the unit module of the
over-site `X.ringCatSheaf.over V`. Built by transport across the equivalence: apply the inverse
functor to `(overRestrictUnitIso V).symm`, then collapse the `functor ⋙ inverse` round trip via the
unit isomorphism of the equivalence. This avoids the `unitToPushforwardObjUnit`/`IsContinuous`
coercion friction of a direct construction. Project-local. -/
/-- **(Piece A, L2) Geometric presentation back-transported to a slice presentation.**
Dual to `overRestrictPresentation`: a presentation of the geometric pullback `(V.ι^*) M` yields a
presentation of the abstract Grothendieck slice `M.over V`. Transport the given presentation across
`(overRestrictPullbackIso V M).inv` (`Presentation.ofIsIso`), `Presentation.map` along the inverse
slice-equivalence functor (using `overRestrictUnitIsoInv V`), then collapse the round trip across the
equivalence unit iso. Project-local. -/
/-- **(Piece A helper) Pullback along an open immersion sends `unit` to `unit`.**
For an open immersion `k : A ⟶ B`, the pullback functor `pullback k` carries the structure-sheaf
(unit) module of `B` to that of `A`. The canonical comparison `pullbackObjUnitToUnit` is an iso
because the site functor `Opens.map k.base` is `Final` — it is a right adjoint, since `k.base` is an
open map (`IsOpenMap.adjunction`). Generalizes `pullbackSchemeIsoUnitIso` from isos to open
immersions. Project-local. -/
/-- **(Piece A, L3 helper) Pseudofunctoriality iso for the preimage square.**
For an open immersion `g : Y ⟶ X`, `M` on `X`, and `U ⊆ X`, the induced open immersion
`k := g.resLE U (g ⁻¹ᵁ U)` (with `k ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g`) gives, by pseudofunctoriality of
pullback (`pullbackComp` / `pullbackCongr`), a natural iso
`(pullback k).obj ((pullback U.ι).obj M) ≅ (pullback (g ⁻¹ᵁ U).ι).obj ((pullback g).obj M)`.
Project-local. -/
set_option maxHeartbeats 2000000 in
-- Heartbeat headroom for the slice-site presentation transport, as elsewhere in this file.
set_option synthInstance.maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- **(Piece A, L3) Presentation of the pullback's restriction to a preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the geometric
restriction `(W_i.ι^*) ((pullback g).obj M)` of `N := (pullback g).obj M` to the preimage
`W_i := g ⁻¹ᵁ (q.X i)` admits a presentation. Build it by mapping the global presentation
`presentationPullbackιOfQuasicoherentData M q i` of `(q.X i).ι^* M` along the pullback of the induced
open immersion `k := g.resLE (q.X i) W_i` (unit datum `pullbackOpenImmersionUnitIso`), then
transporting across the pseudofunctoriality iso `pullbackPreimageιIso`. Project-local. -/
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the slice-site `HasSheafify` synthesis triggered by `over`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **(Piece A, L4) The pulled-back sheaf is quasi-coherent on each preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the abstract
Grothendieck slice `((pullback g).obj M).over (g ⁻¹ᵁ (q.X i))` is quasi-coherent: feed the geometric
presentation `presentationPullbackιPreimage` into the geometric→slice back-transport
`overRestrictPresentationInv` and apply `Presentation.isQuasicoherent`. Project-local. -/
/-- **(Piece A, L5) The preimage family of a quasi-coherence cover covers the source.**
For a morphism `g : Y ⟶ X` and quasi-coherence datum `q` for `M` on `X` (whose cover `{q.X i}` covers
`X`), the preimage family `{g ⁻¹ᵁ (q.X i)}` covers `Y`. Direct from the opens-topology covering
characterization: any `y ∈ W` has `g y ∈ q.X i` for some `i` (since `{q.X i}` covers `⊤`), so
`W ⊓ g ⁻¹ᵁ (q.X i)` is a neighbourhood of `y` in the sieve. Project-local. -/
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the slice-site `of_coversTop` `bind` synthesis.
set_option synthInstance.maxHeartbeats 800000 in
/-- **(Piece A, L6) Pullback of a quasi-coherent sheaf along an open immersion is quasi-coherent.**
For an open immersion `g : Y ⟶ X` and `M` quasi-coherent on `X`, the pullback `(pullback g).obj M` is
quasi-coherent. Choose quasi-coherence data `q` for `M` (index shrunk to the site universe); the
preimage family `{g ⁻¹ᵁ (q.X i)}` covers `Y` (`coversTop_preimage`) and on each member the slice is
quasi-coherent (`isQuasicoherent_over_preimage`), so `IsQuasicoherent.of_coversTop` applies.
Project-local: Mathlib has no QC-pullback lemma. -/
/-- **(Piece A, target) Quasi-coherence is preserved under pullback along `fromSpec`.**
For `M` quasi-coherent on `X` and an affine open `U`, the pullback of `M` along the affine immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X` is quasi-coherent. The `g := hU.fromSpec` instance of
`isQuasicoherent_pullback_of_isOpenImmersion` (`fromSpec` is an open immersion). This is the
QC-pullback input the gap2 close feeds to gap1. Project-local. -/
/-- **gap2 keystone (`lem:qcoh_section_localization_basicOpen`): basic-open section localization for
a quasi-coherent sheaf on an arbitrary scheme.** For `M` quasi-coherent on `X`, an affine open `U`,
and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`. Assembles the QC-pullback (Piece A,
`isQuasicoherent_pullback_fromSpec`) → gap1 (`isIso_fromTildeΓ_of_isQuasicoherent`) → the eqToHom
bridge (Piece B, `isLocalizedModule_basicOpen_of_hP1`). Project-local: closes gap2. -/
/-- **Per-affine coherence of the annihilator family** (the `map_ideal_basicOpen` content for
`def:modules_annihilator`, `lem:modules_annihilator_ideal`). For a quasi-coherent `F`, an affine
open `V`, and `f : Γ(X, V)` with `Γ(F, V)` finitely generated over `Γ(X, V)`, the module annihilator
`Ann_{Γ(X,V)}(Γ(F,V))` maps, under the basic-open restriction `Γ(X, V) → Γ(X, D(f))`, onto
`Ann_{Γ(X,D(f))}(Γ(F,D(f)))`. This is the localized-annihilator identity
(`Module.annihilator_isLocalizedModule_eq_map`, `lem:annihilator_localization_eq_map`) transported
across the quasi-coherent basic-open section localization (gap2, `isLocalizedModule_basicOpen`,
`lem:qcoh_section_localization_basicOpen`). It is exactly the structure field
`Scheme.IdealSheafData.map_ideal_basicOpen` for the annihilator data. Project-local because
`annihilator` is. -/
set_option backward.isDefEq.respectTransparency false in
/-- **The annihilator ideal sheaf agrees with the module annihilator on affine opens**
(`lem:modules_annihilator_ideal`). For a quasi-coherent `F` whose section module `Γ(F, V)` is
finitely generated over `Γ(X, V)` on every affine open `V` (the affine-local finiteness supplied,
for a finite-type `F`, by the G1 base case `lem:gf_qcoh_fintype_finite_sections`), the section over
an affine open `U` of the annihilator ideal sheaf equals the module annihilator of the sections:
`(annihilator F).ideal U = Ann_{Γ(X,U)}(Γ(F,U))`.

The forward inclusion `≤` is `annihilator_ideal_le` (always available from `ofIdeals`). The reverse
inclusion is genuinely *global*: `annihilator F = ofIdeals (V ↦ Ann_{Γ(X,V)}(Γ(F,V)))` is the
**largest** ideal sheaf contained in the annihilator family, and its value at `U` reaches the full
`Ann_{Γ(X,U)}(Γ(F,U))` precisely when that family is itself a coherent ideal sheaf — i.e. when it
satisfies `IdealSheafData.map_ideal_basicOpen` at *every* affine open. That coherence is
`annihilator_map_basicOpen`, which needs finite generation of `Γ(F, V)` at each `V`; hence the
`hfin` hypothesis. With it the family assembles into an honest `IdealSheafData I` whose `ideal` is
the annihilator family, and `IdealSheafData.ofIdeals_ideal` gives `ofIdeals I.ideal = I`, whence the
claim at every `U` at once. This mirrors Mathlib's `Scheme.Hom.ker_apply`, which likewise builds the
full ideal sheaf and reads off the affine value (using `QuasiCompact f` as its global hypothesis).
Project-local because `annihilator` is. -/
end Scheme.Modules

end BasicOpenPresentationDescent

end AlgebraicGeometry
