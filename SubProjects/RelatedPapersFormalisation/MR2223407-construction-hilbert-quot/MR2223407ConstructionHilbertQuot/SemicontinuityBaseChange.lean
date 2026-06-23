/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Basic

/-!
# MR2223407: Semicontinuity and Base Change (Nitsure §3)

This file scaffolds the cohomological base-change machinery of Nitsure §3,
following the blueprint chapter `chapters/SemicontinuityBaseChange.tex`.

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `base_change_without_flatness`            — `lem:base-change-without-flatness`
* `flatness_of_locally_free_direct_image`   — `lem:flatness-from-local-freeness`
* `grothendieck_complex`                    — `thm:grothendieck-complex`
* `cokernel_of_dual`                        — `thm:cokernel-of-dual`
* `semicontinuity_fibre_cohomology`         — `thm:semicontinuity`
* `base_change_for_flat_sheaves`            — `thm:base-change-flat`

The deepest inputs (coherent cohomology `Hⁱ`, fibre cohomology `Hⁱ(X_s,F_s)`,
higher direct images `Rⁱπ_*`, Serre twists `O(r)`, the Grothendieck complex) are
Mathlib gaps.  Following the convention established in `Basic.lean` (see
`serre_vanishing`), each gap-object is abstracted as free input data and the
intended geometric conclusion is stated about it, with the proof deferred to a
`sorry`.  No `axiom` is introduced.  Per-declaration stating-gaps are documented
in the docstrings and in the task result.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace MR2223407ConstructionHilbertQuot

/-! ## Base change without flatness -/

/-- **Base change without flatness** (`lem:base-change-without-flatness`).

Let `φ : T ⟶ S` be a morphism of noetherian schemes, `F` a coherent sheaf on
`ℙⁿ_S`, and `F_T` its pull-back to `ℙⁿ_T`.  With `π_S, π_T` the projections, there
is an integer `r₀` such that the base-change map
`φ^* π_{S*} F(r) → π_{T*} F_T(r)` is an isomorphism for all `r ≥ r₀`.

STATING-GAP: the Serre twists `F(r)` are a Mathlib gap, so — exactly as in
`Basic.serre_vanishing` — the twist family is taken as abstract input data
`twist : ℤ → (ℙⁿ_S).Modules`.  The base change `F_T(r)` is realised through the
fibre product `ℙⁿ_S ×_S T` (whose first projection pulls `twist r` back, whose
second projection pushes it forward), matching the shadow used in
`Basic.cohomology_and_base_change`.  The "`r₀` depends on `φ`" content is captured
by the leading existential.  The `Hⁱ`/Serre-vanishing input that fixes `r₀` is
deferred. -/
theorem base_change_without_flatness {S T : Scheme.{u}} (φ : T ⟶ S) (n : ℕ)
    (F : (projectiveSpace n S).Modules) (_hF : F.IsQuasicoherent)
    (twist : ℤ → (projectiveSpace n S).Modules) :
    ∃ r₀ : ℕ, ∀ r : ℤ, (r₀ : ℤ) ≤ r →
      Nonempty
        ((Scheme.Modules.pullback φ).obj
            ((Scheme.Modules.pushforward
              (projectiveSpace.structureMorphism n S)).obj (twist r)) ≅
          (Scheme.Modules.pushforward
              (pullback.snd (projectiveSpace.structureMorphism n S) φ)).obj
            ((Scheme.Modules.pullback
              (pullback.fst (projectiveSpace.structureMorphism n S) φ)).obj (twist r))) :=
  sorry

/-! ## The Grothendieck complex -/

/-- **Grothendieck complex** (`thm:grothendieck-complex`).

For `π : X ⟶ S` proper with `S = Spec A` affine and `F` coherent and flat over
`O_S`, there is a bounded complex `K⁰ → ⋯ → Kⁿ` of finitely generated projective
`A`-modules with a functorial isomorphism `Hᵖ(X, F ⊗_A M) ≅ Hᵖ(K• ⊗_A M)` for all
`A`-modules `M`.

STATING-GAP: coherent cohomology `Hᵖ` and the complex `K•` are Mathlib gaps.  The
honest expressible shadow is the `p = 0` flat base-change isomorphism (this is the
affine-base, explicit form of the anchor `Basic.cohomology_and_base_change`, which
this block `\uses`).  It is discharged directly from that anchor; the universal
finite-projective-complex / `Hᵖ` form is deferred. -/
theorem grothendieck_complex {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsProper f]
    (F : X.Modules) (hF : F.IsQuasicoherent) {T : Scheme.{u}} (φ : T ⟶ S) :
    Nonempty
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pushforward f).obj F) ≅
        (Scheme.Modules.pushforward (pullback.snd f φ)).obj
          ((Scheme.Modules.pullback (pullback.fst f φ)).obj F)) :=
  cohomology_and_base_change f F hF φ

/-! ## Flatness from local freeness of direct images -/

/-- Stating-gap proxy for "the coherent sheaf pushed forward along `π` is flat over
the base": its underived direct image commutes with arbitrary base change.

This Mathlib rev (`v4.30.0`) has **no** flatness predicate for a sheaf of modules
over a base scheme (there is only `AlgebraicGeometry.Flat` for a *morphism*, i.e.
flatness of the structure sheaf).  The operative geometric meaning of "`F` flat
over `S`" used throughout Nitsure §3 is that the cohomology (here, the underived
`π_*`) commutes with base change; we take that as the honest proxy.  It has the
same shape as the `i = 0` shadow of the anchor `Basic.cohomology_and_base_change`. -/
def DirectImageCommutesBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  ∀ {T : Scheme.{u}} (φ : T ⟶ S),
    Nonempty
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pushforward f).obj F) ≅
        (Scheme.Modules.pushforward (pullback.snd f φ)).obj
          ((Scheme.Modules.pullback (pullback.fst f φ)).obj F))

/-- **Flatness from local freeness of direct images** (`lem:flatness-from-local-freeness`).

If `S` is noetherian and the direct images `π_*F(r)` of a coherent sheaf `F` on
`ℙⁿ_S` are locally free for all `r ≥ N`, then `F` is flat over `S`.

STATING-GAP: the Serre twists `F(r)` and their direct images are Mathlib gaps, so
the direct-image family is abstract input `dirImage : ℤ → S.Modules` (standing for
`π_*F(r)`).  "Locally free of finite rank" is approximated by the available, honest
(and stronger) condition of admitting an isomorphism to a finite free sheaf
`SheafOfModules.free`.  Because no flat-sheaf predicate exists, the conclusion "`F`
is flat over `S`" is expressed through the proxy `DirectImageCommutesBaseChange`
(see its docstring).  The faithful flat-sheaf statement is deferred. -/
theorem flatness_of_locally_free_direct_image {S : Scheme.{u}} (n : ℕ)
    (F : (projectiveSpace n S).Modules) (_hF : F.IsQuasicoherent)
    (dirImage : ℤ → S.Modules)
    (_hlf : ∃ N : ℤ, ∀ r : ℤ, N ≤ r →
      ∃ k : ℕ,
        Nonempty (dirImage r ≅ SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin k)))) :
    DirectImageCommutesBaseChange (projectiveSpace.structureMorphism n S) F :=
  sorry

/-! ## Cokernel of the dual (EGA III 7.7.6) -/

/-- **Cokernel of the dual** (`thm:cokernel-of-dual`, EGA III 7.7.6).

For `π : X ⟶ S` proper between noetherian schemes and `F` coherent flat over `S`,
there is a coherent sheaf `Q` on `S` with a functorial `O_S`-linear isomorphism
`π_*(F ⊗ π^*G) ≅ Hom_{O_S}(Q, G)` for all quasi-coherent `G` on `S`.

STATING-GAP: this Mathlib rev has neither a tensor product nor an internal Hom on
`S.Modules`, so the full `π_*(F ⊗ π^*G) ≅ Hom(Q,G)` cannot be written.  The honest
expressible shadow specialises to `F = O_X` (the *linear scheme* case used
downstream to form `Spec Sym Q`), where `F ⊗ π^*G = π^*G`, and replaces the
internal-Hom isomorphism of sheaves by its corepresentability (Yoneda) shadow on
Hom-*sets*: a quasi-coherent `Q` on `S` together with, for every `G`, a natural
bijection `(Q ⟶ G) ≃ Γ(S, π_*π^*G)`, where global sections `Γ(S, -)` are the
morphisms out of the free rank-one sheaf.  The general-`F` and sheaf-Hom forms are
deferred. -/
theorem cokernel_of_dual {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : X.Modules) (_hF : F.IsQuasicoherent) :
    ∃ Q : S.Modules, Q.IsQuasicoherent ∧
      ∀ G : S.Modules,
        Nonempty
          ((Q ⟶ G) ≃
            (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin 1)) ⟶
              (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G))) :=
  sorry

/-! ## Semicontinuity and base change for flat sheaves -/

/-- **Upper semicontinuity of fibre cohomology** (`thm:semicontinuity`, EGA III 7.7.8–7.7.9).

For `π : X ⟶ S` proper and `F` coherent flat over `S`:
(1) `s ↦ dim_{κ(s)} Hⁱ(X_s, F_s)` is upper semicontinuous;
(2) the Euler characteristic `s ↦ ∑ (-1)ⁱ dim Hⁱ(X_s, F_s)` is locally constant;
(3) if some fibre dimension is globally constant `= d`, then `Rⁱπ_*F` is locally
free of rank `d` (and a comparison map is an isomorphism).

STATING-GAP: fibre cohomology `Hⁱ(X_s, F_s)`, higher direct images `Rⁱπ_*` and the
fibre `F_s` are all Mathlib gaps.  Following the `serre_vanishing` precedent, the
fibre-cohomology dimension function and the Euler characteristic are taken as
abstract input data over the points `↥S` (with `S`'s topology), and the genuine
conclusions (1)–(2) are stated about them.  In (3) the higher direct image
`Rⁱπ_*F` is proxied by the underived pushforward and "locally free of rank `d`" by
an isomorphism to a finite free sheaf.  The construction of these functions from
actual cohomology (via the Grothendieck complex) is the deferred content. -/
theorem semicontinuity_fibre_cohomology {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : X.Modules) (_hF : F.IsQuasicoherent)
    (fibreCohDim : ℤ → ↥S → ℕ) (euler : ↥S → ℤ) :
    (∀ i : ℤ, UpperSemicontinuous (fibreCohDim i)) ∧
      IsLocallyConstant euler ∧
      (∀ (i : ℤ) (d : ℕ), (∀ s : ↥S, fibreCohDim i s = d) →
        Nonempty
          ((Scheme.Modules.pushforward f).obj F ≅
            SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin d)))) :=
  sorry

/-- **Base change for flat sheaves** (`thm:base-change-flat`, EGA III 7.7.8–7.7.9).

Parts (4)–(5) of Grothendieck's base-change theorem, in the form used to construct
the Quot scheme: for `π = π_S : ℙⁿ_S ⟶ S` and `F` coherent flat over `S`, applied
with `i = 0` to the twists `F(r)` for `r ≫ 0` (where higher fibre cohomology of the
flat `F` vanishes), the direct image `π_*F(r)` is locally free **and** commutes with
arbitrary base change.  This is the converse to
`flatness_of_locally_free_direct_image`.

STATING-GAP: the stalk-level statements of parts (4)–(5) — surjectivity of
`(Rⁱπ_*F)_s → Hⁱ(X_s,F_s)`, the open neighbourhood `U ∋ s`, and local freeness of
`Rⁱπ_*F` near `s` — need higher direct images, stalks and fibre cohomology, all
Mathlib gaps.  We state the `i = 0`, `r ≫ 0` payoff that is actually used: the twist
family is abstract input (`twist : ℤ → (ℙⁿ_S).Modules`, standing for `F(r)`), and
the conclusion combines local freeness (finite-free-sheaf isomorphism) with the
base-change isomorphism shadow of `Basic.cohomology_and_base_change`. -/
theorem base_change_for_flat_sheaves {S : Scheme.{u}} (n : ℕ)
    (F : (projectiveSpace n S).Modules) (_hF : F.IsQuasicoherent)
    (twist : ℤ → (projectiveSpace n S).Modules) :
    ∃ r₀ : ℕ, ∀ r : ℤ, (r₀ : ℤ) ≤ r →
      (∃ k : ℕ,
        Nonempty
          ((Scheme.Modules.pushforward (projectiveSpace.structureMorphism n S)).obj (twist r) ≅
            SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin k)))) ∧
        ∀ {T : Scheme.{u}} (φ : T ⟶ S),
          Nonempty
            ((Scheme.Modules.pullback φ).obj
                ((Scheme.Modules.pushforward
                  (projectiveSpace.structureMorphism n S)).obj (twist r)) ≅
              (Scheme.Modules.pushforward
                  (pullback.snd (projectiveSpace.structureMorphism n S) φ)).obj
                ((Scheme.Modules.pullback
                  (pullback.fst (projectiveSpace.structureMorphism n S) φ)).obj (twist r))) :=
  sorry

end MR2223407ConstructionHilbertQuot
