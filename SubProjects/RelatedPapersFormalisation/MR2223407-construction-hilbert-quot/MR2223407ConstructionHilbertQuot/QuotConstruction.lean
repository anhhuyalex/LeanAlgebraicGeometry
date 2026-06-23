/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Functors
import MR2223407ConstructionHilbertQuot.Regularity
import MR2223407ConstructionHilbertQuot.SemicontinuityBaseChange
import MR2223407ConstructionHilbertQuot.FlatteningStratification

/-!
# MR2223407: Construction of the Quot Scheme (Nitsure §5)

This file scaffolds the blueprint chapter `chapters/QuotConstruction.tex` — the
representability of the projective Quot functor, in the Altman–Kleiman form
(`thm:altman-kleiman-quot`, the project goal theorem) and the Grothendieck form
(`thm:grothendieck-quot`), together with the lemma chain assembling the proof.

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `ProjectiveMorphism`      — `def:projective-morphism`
* `StronglyProjective`      — `def:strongly-projective`
* `quot_grothendieck`       — `thm:grothendieck-quot`
* `quot_altmanKleiman`      — `thm:altman-kleiman-quot`  (project goal)
* `quot_projectiveSpace`    — `thm:quot-pn`
* `quot_reduction`          — `lem:quot-reduction`
* `quot_uniformRegularity`  — `lem:quot-uniform-regularity`
* `quot_embedGrassmannian`  — `lem:quot-embed-grassmannian`
* `quot_flatteningStratum`  — `lem:quot-flattening-stratum`
* `quot_properness`         — `lem:quot-properness`

## Conventions and stating-gaps

Representability of a moduli functor `Quot^{Φ,L}_{E/X/S}` "by a scheme `Q` over `S`"
is rendered, following the functor-of-points convention already used in
`Functors.grassmannian_represents`, as the existence of an object `Q : Over S`
together with a natural isomorphism between the moduli functor (valued in
`Type (u+1)`) and the (universe-lifted) functor of points `pointsFunctor Q`.  This
is the genuinely-expressible content of "represents"; naturality in the test scheme
is carried by the natural isomorphism.

The Serre twists `E(ν)`, `F(r)`, the symmetric/exterior powers `Sym^r V`,
`⋀^{Φ(r)}(W ⊗ Sym^r V)`, the relative Grassmannian of a bundle, and coherent
cohomology are all Mathlib gaps (recorded in `Basic.lean`, `Functors.lean`,
`Regularity.lean`, `SemicontinuityBaseChange.lean`, `FlatteningStratification.lean`).
Where a faithful statement would name one of these we either take it as abstract
input data (the established sibling-file convention — e.g. `twist : ℤ → _.Modules`)
or pass to the closest honest geometric shadow (`IsLocallyFreeOfRank` for "vector
bundle", `relativeProj S F` for `ℙ(F)`, `IsImmersion`/`IsClosedImmersion` for
locally-closed/closed embedding).  Per-declaration gaps are documented in the
doc-strings and in the task result.  No `axiom` is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace MR2223407ConstructionHilbertQuot

/-! ## Functor-of-points helper -/

/-- The functor of points of an `S`-scheme `A : Over S`, universe-lifted to land in
`Type (u+1)` so it can be compared with the moduli functors of this development
(`quotFunctorPhi`, valued in `Type (u+1)`).  `A` *represents* a moduli functor `M`
when `M ≅ pointsFunctor A`.  This is a helper, not a blueprint block. -/
noncomputable def pointsFunctor {S : Scheme.{u}} (A : Over S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  yoneda.obj A ⋙ CategoryTheory.uliftFunctor.{u + 1}

/-! ## Notions of projectivity -/

/-- **Projective morphism (Grothendieck)** (`def:projective-morphism`).

A morphism `f : X ⟶ S` is *projective* if there is a coherent (here:
quasi-coherent) sheaf `E` on `S` together with a closed immersion
`i : X ↪ ℙ(E) = relativeProj S E` over `S`.

STATING-GAP: "coherent" ↦ "quasi-coherent" and `ℙ(E)` is the stub `relativeProj`
(relative `Proj` of a graded sheaf is a Mathlib gap, see `Basic.relativeProj`).
The equivalent "proper + relatively very ample line bundle" formulation is
`RelativelyVeryAmple` together with properness; the two are matched in the
blueprint. -/
def ProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules), E.IsQuasicoherent ∧
    ∃ (i : X ⟶ relativeProj S E),
      IsClosedImmersion i ∧ i ≫ relativeProj.structureMorphism S E = f

/-- **Strongly projective morphism (Altman–Kleiman)** (`def:strongly-projective`).

A morphism `f : X ⟶ S` is *strongly projective* if there is a vector bundle `E`
on `S` (locally free of some rank `d`) together with a closed immersion
`i : X ↪ ℙ(E)` over `S`.  This is the special case of `ProjectiveMorphism` in which
the sheaf `E` is required to be locally free.

STATING-GAP: "vector bundle" ↦ `IsLocallyFreeOfRank d` (a Mathlib-gap predicate
stated abstractly in `Functors.lean`); `ℙ(E)` is the stub `relativeProj`.  The
strongly *quasi*-projective variant (locally closed embedding) is not separately
named here. -/
def StronglyProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (d : ℕ), IsLocallyFreeOfRank d E ∧
    ∃ (i : X ⟶ relativeProj S E),
      IsClosedImmersion i ∧ i ≫ relativeProj.structureMorphism S E = f

/-! ## Main existence theorems -/

/-- **Grothendieck Quot scheme** (`thm:grothendieck-quot`).

For `S` noetherian, `π : X ⟶ S` projective with relatively very ample `L`, any
coherent `E` on `X` and any `Φ ∈ ℚ[λ]`, the functor `Quot^{Φ,L}_{E/X/S}` is
representable by a *projective* `S`-scheme.

STATING-GAP: representability is the functor-of-points shadow `≅ pointsFunctor Q`
(see `pointsFunctor`); "projective `S`-scheme" is `ProjectiveMorphism Q.hom`.  The
proof (deferred) reduces to `quot_altmanKleiman` via the noetherian `m`-regularity
of `mumford_regularity` and `flatteningStratification` over an affine cover. -/
theorem quot_grothendieck {S X : Scheme.{u}} [IsLocallyNoetherian S] (π : X ⟶ S)
    (_hπ : ProjectiveMorphism π) (L : X.Modules) (_hL : RelativelyVeryAmple π L)
    (E : X.Modules) (_hE : E.IsQuasicoherent) (Φ : Polynomial ℚ) :
    ∃ Q : Over S, ProjectiveMorphism Q.hom ∧
      Nonempty (quotFunctorPhi π E L Φ ≅ pointsFunctor Q) :=
  sorry

/-- **Altman–Kleiman Quot scheme** (`thm:altman-kleiman-quot`) — *the project goal*.

Let `S` be noetherian, `X` a closed subscheme of `ℙ(V)` for a vector bundle `V` on
`S`, `L = O_{ℙ(V)}(1)|_X`, `E` a coherent quotient of `π^*(W)(ν)` with `W` a vector
bundle on `S` and `ν ∈ ℤ`, and `Φ ∈ ℚ[λ]`.  Then `Quot^{Φ,L}_{E/X/S}` is
representable by a scheme `Q` that embeds over `S` as a closed subscheme of `ℙ(F)`
for some vector bundle `F` on `S` — i.e. `Q ⟶ S` is *strongly projective*.

STATING-GAP: representability is the functor-of-points shadow `≅ pointsFunctor Q`;
"embeds as a closed subscheme of `ℙ(F)`, `F` a vector bundle" is exactly
`StronglyProjective Q.hom`.  The specific bundle `F = ⋀^{Φ(r)}(W ⊗ Sym^r V)` (whose
`⋀`, `⊗`, `Sym^r` are Mathlib gaps) is captured up to its existence inside
`StronglyProjective`.  `V`, `W` vector bundles ↦ `IsLocallyFreeOfRank`; `ℙ(V)` is
the stub `relativeProj`; `L = O(1)|_X` ↦ `RelativelyVeryAmple π L`; the twist
`π^*(W)(ν)` is abstract input `EWν` surjecting onto `E`.  The proof is the
assembly of `quot_reduction`, `quot_uniformRegularity`, `quot_embedGrassmannian`,
`quot_flatteningStratum`, `quot_properness`. -/
theorem quot_altmanKleiman {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (V : S.Modules) (dV : ℕ) (_hV : IsLocallyFreeOfRank dV V)
    (jX : X ⟶ relativeProj S V) (_hjX : IsClosedImmersion jX)
    (π : X ⟶ S) (_hπ : π = jX ≫ relativeProj.structureMorphism S V)
    (L : X.Modules) (_hL : RelativelyVeryAmple π L)
    (W : S.Modules) (dW : ℕ) (_hW : IsLocallyFreeOfRank dW W) (ν : ℤ)
    (EWν E : X.Modules) (_hE : E.IsQuasicoherent) (qE : EWν ⟶ E) (_hqE : Epi qE)
    (Φ : Polynomial ℚ) :
    ∃ Q : Over S, StronglyProjective Q.hom ∧
      Nonempty (quotFunctorPhi π E L Φ ≅ pointsFunctor Q) :=
  sorry

/-- **Quot scheme in projective space** (`thm:quot-pn`).

For `S` noetherian, `X` a closed subscheme of `ℙⁿ_S`, `L = O_{ℙⁿ_S}(1)|_X`, `E` a
coherent quotient of `⊕^p O_X(ν)`, and `Φ ∈ ℚ[λ]`, the functor `Quot^{Φ,L}_{E/X/S}`
is representable by a scheme embedding over `S` as a closed subscheme of `ℙ^r_S`.

STATING-GAP: representability is `≅ pointsFunctor Q`; `ℙⁿ_S`, `ℙ^r_S` are
`projectiveSpace`; the twist `⊕^p O_X(ν)` is abstract input `EOpν` surjecting onto
`E`.  This is the trivial-bundle case `V = O_S^{n+1}`, `W = O_S^p` of
`quot_altmanKleiman`. -/
theorem quot_projectiveSpace {S X : Scheme.{u}} [IsLocallyNoetherian S] (n : ℕ)
    (jX : X ⟶ projectiveSpace n S) (_hjX : IsClosedImmersion jX)
    (π : X ⟶ S) (_hπ : π = jX ≫ projectiveSpace.structureMorphism n S)
    (L : X.Modules) (_hL : RelativelyVeryAmple π L)
    (p : ℕ) (ν : ℤ) (EOpν E : X.Modules) (_hE : E.IsQuasicoherent)
    (qE : EOpν ⟶ E) (_hqE : Epi qE) (Φ : Polynomial ℚ) :
    ∃ (Q : Over S) (r : ℕ) (i : Q.left ⟶ projectiveSpace r S),
      IsClosedImmersion i ∧
      i ≫ projectiveSpace.structureMorphism r S = Q.hom ∧
      Nonempty (quotFunctorPhi π E L Φ ≅ pointsFunctor Q) :=
  sorry

/-! ## Reduction to the model case -/

/-- **Reduction to the model case** (`lem:quot-reduction`).

(i) For any `ν ∈ ℤ`, tensoring by `L^ν` gives an isomorphism of functors
`Quot^{Φ,L}_{E/X/S} ≅ Quot^{Ψ,L}_{E(ν)/X/S}` with `Ψ(λ) = Φ(λ + ν)`.
(ii) For any surjection `φ : E → G` of coherent sheaves on `X`, the induced natural
transformation `Quot^{Φ,L}_{G/X/S} → Quot^{Φ,L}_{E/X/S}` is a closed embedding.

STATING-GAP: in (i) the twist `E(ν)` is a Serre-twist gap; we phrase the claim as
"there exists a sheaf `Eν` (the twist `E(ν)`) making the functors isomorphic", with
`Ψ = Φ.comp(X + C ν)`.  In (ii) "closed embedding of functors" (relative
representability by closed immersions) is shadowed by "the natural transformation is
a monomorphism".  Both are honest, non-vacuous shadows. -/
theorem quot_reduction {S X : Scheme.{u}} (π : X ⟶ S) (E L : X.Modules)
    (Φ : Polynomial ℚ) :
    (∀ ν : ℤ, ∃ Eν : X.Modules,
        Nonempty (quotFunctorPhi π E L Φ ≅
          quotFunctorPhi π Eν L (Φ.comp (Polynomial.X + Polynomial.C (ν : ℚ))))) ∧
      (∀ (G : X.Modules) (φ : E ⟶ G), Epi φ →
        ∃ η : quotFunctorPhi π G L Φ ⟶ quotFunctorPhi π E L Φ, Mono η) :=
  sorry

/-! ## Use of `m`-regularity -/

/-- **Uniform `m`-regularity of the family** (`lem:quot-uniform-regularity`).

Working in the model case on `ℙⁿ` (with `n = rank V - 1`, `p = rank W`),
`mumford_regularity` supplies a single integer `m`, depending only on `rank V`,
`rank W` and `Φ`, so that for every member of every family the source, kernel and
quotient become `m`-regular; after twisting by `r ≥ m` and pushing forward along
`π_T`, the direct images are locally free of fixed rank with vanishing higher direct
images.

STATING-GAP: the Serre twists `E_T(r)`, `F(r)`, `G(r)` are Mathlib gaps, so — as in
`Basic.serre_vanishing` and the sibling files — the twist families are abstract
input data `twistE, twistF, twistG : ℤ → (ℙⁿ_T).Modules`.  "Locally free of fixed
rank" is `IsLocallyFreeOfRank` of the underived pushforward
`Scheme.Modules.pushforward (π_T)`.  The fibrewise `m`-regularity bound, the precise
ranks (`rank π_{T*}F(r) = Φ(r)`, `π_*E(r) = W ⊗ Sym^r V`), the surjectivity of the
evaluation maps and the vanishing of `Rⁱπ_{T*}` are the deferred (gap-blocked)
content recorded for the prover stage. -/
theorem quot_uniformRegularity {S : Scheme.{u}} [IsLocallyNoetherian S]
    (n p : ℕ) (Φ : Polynomial ℚ) :
    ∃ m : ℕ, ∀ (T : Scheme.{u}) (_φT : T ⟶ S)
      (twistE twistF twistG : ℤ → (projectiveSpace n T).Modules)
      (r : ℤ), (m : ℤ) ≤ r →
        (∃ dE : ℕ, IsLocallyFreeOfRank dE
          ((Scheme.Modules.pushforward
            (projectiveSpace.structureMorphism n T)).obj (twistE r))) ∧
        (∃ dF : ℕ, IsLocallyFreeOfRank dF
          ((Scheme.Modules.pushforward
            (projectiveSpace.structureMorphism n T)).obj (twistF r))) ∧
        (∃ dG : ℕ, IsLocallyFreeOfRank dG
          ((Scheme.Modules.pushforward
            (projectiveSpace.structureMorphism n T)).obj (twistG r))) :=
  sorry

/-! ## Embedding Quot into the Grassmannian -/

/-- **Embedding of Quot into a Grassmannian** (`lem:quot-embed-grassmannian`).

For a fixed `r ≥ m`, sending `⟨F, q⟩` to the rank-`Φ(r)` locally free quotient
`π_{T*}(q(r)) : π_{T*}E_T(r) → π_{T*}F(r)` defines an injective morphism of functors
`α : Quot^{Φ,L}_{E/X/S} → Grass(W ⊗ Sym^r V, Φ(r))`, and the Grassmannian functor is
representable (`Functors.grassmannian_represents`).

STATING-GAP: the relative Grassmannian `Grass(W ⊗ Sym^r V, Φ(r))` of a bundle is a
Mathlib gap (`Functors.grassmannianScheme` is the absolute `Grass(r,d)` over `ℤ`);
its representing scheme over `S` is abstracted as `Gr : Over S`, with `α` a
natural transformation into `pointsFunctor Gr`.  "Injective morphism of functors"
↦ `Mono α`.  The recovery of `q` from `π_{T*}(q(r))` (powering the injectivity) is
the deferred content. -/
theorem quot_embedGrassmannian {S X : Scheme.{u}} (π : X ⟶ S) (E L : X.Modules)
    (Φ : Polynomial ℚ) (m : ℕ) :
    ∃ r : ℕ, m ≤ r ∧
      ∃ (Gr : Over S) (α : quotFunctorPhi π E L Φ ⟶ pointsFunctor Gr), Mono α :=
  sorry

/-! ## Use of the flattening stratification -/

/-- **The representing flattening stratum** (`lem:quot-flattening-stratum`).

The morphism `α` of `quot_embedGrassmannian` is relatively representable by locally
closed immersions: its image is the flattening stratum
(`FlatteningStratification.flatteningStratification`) for the universal quotient over
the Grassmannian at Hilbert polynomial `Φ`.  Hence `Quot^{Φ,L}_{E/X/S}` is
represented by a locally closed subscheme, giving a locally closed embedding
`Q ⊂ ℙ(⋀^{Φ(r)}(W ⊗ Sym^r V))`; in particular `Q ⟶ S` is separated and of finite
type.

STATING-GAP: representability is `≅ pointsFunctor Q`; the projective bundle
`ℙ(⋀^{Φ(r)}(W ⊗ Sym^r V))` (whose `⋀`, `⊗`, `Sym^r` are Mathlib gaps) is shadowed
by `relativeProj S F` for an existentially-quantified `F`; "locally closed
embedding" ↦ `IsImmersion`.  Separatedness and finite type are stated directly. -/
theorem quot_flatteningStratum {S X : Scheme.{u}} [IsLocallyNoetherian S] (π : X ⟶ S)
    (E L : X.Modules) (Φ : Polynomial ℚ) :
    ∃ (Q : Over S) (F : S.Modules),
      Nonempty (quotFunctorPhi π E L Φ ≅ pointsFunctor Q) ∧
      (∃ i : Q.left ⟶ relativeProj S F,
        IsImmersion i ∧ i ≫ relativeProj.structureMorphism S F = Q.hom) ∧
      IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom :=
  sorry

/-! ## Valuative criterion for properness -/

/-- **Properness via the valuative criterion** (`lem:quot-properness`).

`Quot^{Φ,L}_{E/X/S}` satisfies the valuative criterion of properness over `S`.
Combined with finite type over the noetherian `S`, the representing scheme `Q ⟶ S`
is proper (via `Basic.valuativeCriterion_proper`, i.e.
`IsProper.of_valuativeCriterion`); hence the locally closed embedding of
`quot_flatteningStratum` into `ℙ(F)` is in fact a closed embedding.

STATING-GAP: the functor-level valuative criterion (bijectivity of
`Quot(Spec R) → Quot(Spec K)` for DVRs `R`) is shadowed by the morphism-level
`ValuativeCriterion Q.hom` hypothesis on the representing scheme `Q`.  Properness is
discharged from `valuativeCriterion_proper`; "a proper locally closed immersion is a
closed immersion" is the remaining deferred geometric fact. -/
theorem quot_properness {S X : Scheme.{u}} [IsLocallyNoetherian S] (π : X ⟶ S)
    (E L : X.Modules) (Φ : Polynomial ℚ)
    (Q : Over S) [QuasiCompact Q.hom] [QuasiSeparated Q.hom] [LocallyOfFiniteType Q.hom]
    (_hrep : Nonempty (quotFunctorPhi π E L Φ ≅ pointsFunctor Q))
    (hvc : ValuativeCriterion Q.hom) :
    IsProper Q.hom ∧
      ∀ (F : S.Modules) (i : Q.left ⟶ relativeProj S F),
        IsImmersion i → i ≫ relativeProj.structureMorphism S F = Q.hom →
        IsClosedImmersion i := by
  -- First conjunct: properness from the valuative criterion over the noetherian base.
  refine ⟨valuativeCriterion_proper Q.hom hvc, ?_⟩
  -- Second conjunct: a proper locally-closed immersion into `ℙ(F)` over `S` is a closed
  -- immersion.  The argument is the standard cancellation: `i ≫ p = Q.hom` is proper and
  -- the structure morphism `p = relativeProj.structureMorphism S F` is separated, so `i`
  -- itself is proper (`IsProper.of_comp_of_isSeparated`); a proper morphism is universally
  -- closed, hence has closed range, and an immersion (= preimmersion) with closed range is a
  -- closed immersion (`IsClosedImmersion.of_isPreimmersion`).
  intro F i hi hcomp
  haveI hi' : IsImmersion i := hi
  haveI hQ : IsProper Q.hom := valuativeCriterion_proper Q.hom hvc
  -- GAP (relativeProj BUILD): separatedness of the relative-`Proj` structure morphism.
  -- `relativeProj` and its structure morphism are EGA-III stubs (`Basic.relativeProj` is
  -- `:= sorry`), so `IsSeparated (relativeProj.structureMorphism S F)` — a genuine theorem
  -- for the real relative `Proj`, which is separated over its base — is not yet derivable.
  -- This is the single named fact this proof is reduced to; everything else below is
  -- discharged from current Mathlib.  Tracked as a relativeProj-separatedness obligation.
  haveI hsep : IsSeparated (relativeProj.structureMorphism S F) := sorry
  -- `i ≫ p = Q.hom` is proper, so by cancellation `i` is proper.
  haveI hcompProper : IsProper (i ≫ relativeProj.structureMorphism S F) := by
    rw [hcomp]; infer_instance
  haveI hiProper : IsProper i :=
    IsProper.of_comp i (relativeProj.structureMorphism S F)
  -- Proper ⟹ universally closed ⟹ closed map ⟹ closed range.
  haveI : UniversallyClosed i := hiProper.toUniversallyClosed
  have hrange : IsClosed (Set.range i.base.hom) := i.isClosedMap.isClosed_range
  -- Immersion ⟹ preimmersion; preimmersion with closed range ⟹ closed immersion.
  exact IsClosedImmersion.of_isPreimmersion i hrange

end MR2223407ConstructionHilbertQuot
