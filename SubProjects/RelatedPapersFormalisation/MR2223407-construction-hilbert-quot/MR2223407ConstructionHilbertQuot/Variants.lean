/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Functors
import MR2223407ConstructionHilbertQuot.QuotConstruction

/-!
# MR2223407: Variants and Applications (Nitsure §6)

This file scaffolds the blueprint chapter `chapters/Variants.tex` (Nitsure §6):
the passage from the projective to the quasi-projective Quot scheme, the Hilbert
scheme, the scheme of morphisms, and the quotient of a scheme by a flat projective
equivalence relation.

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `quot_open_subfunctor`         — `lem:quot-open-subfunctor`
* `stronglyQuasiprojectiveQuot`  — `thm:strongly-quasiprojective-quot`
* `coherent_prolongation`        — `lem:coherent-prolongation`
* `quasiprojectiveQuot`          — `thm:quasiprojective-quot`
* `hilbertScheme`                — `def:hilbert-scheme`
* `hilbertScheme_exists`         — `thm:hilbert-scheme-exists`
* `flatness_local_criterion`     — `lem:flatness-local-criterion`
* `isomorphism_is_open`          — `thm:isomorphism-is-open`
* `schemeOfMorphisms`            — `thm:scheme-of-morphisms`
* `descent_of_subschemes`        — `lem:descent-of-subschemes`
* `projectiveFlatQuotient`       — `thm:projective-flat-quotient`

## Import note (sibling timing)

PROGRESS.md lists this file as importing `QuotConstruction.lean` (for the
representability theorems `thm:altman-kleiman-quot`, `thm:grothendieck-quot` and the
projectivity predicates `def:strongly-projective`, `def:projective-morphism`).  That
file is a *same-wave* sibling that does not yet exist on disk.  Following the
convention established by `FlatteningStratification.lean` and `Regularity.lean`
(import only stable, already-compiling upstreams; abstract not-yet-available
upstream notions), we import only `Functors` (which re-exports `Basic`) and state
each §6 result as a self-contained honest shadow against the confirmed-compiling
Quot/Hilbert *functors* of `Functors.lean`.  The §6 results are downstream
*consequences* of the main theorem, so each body is `sorry`; reconnecting their
proofs to `QuotConstruction.quot_altmanKleiman` / `quot_grothendieck` is deferred to
the prover stage once that file lands.  No `axiom` is introduced.

## Stating-gap conventions

As in `Basic.lean` and the wave-1 files, gap-objects (the Serre twist `(ν)`, the
exterior/symmetric powers giving the bundle `F`, the schematic support of a sheaf,
the scheme structure of the representing object) are taken as free input data or
dropped with a per-declaration note.  *Representability* is rendered, exactly as in
`Functors.grassmannian_represents`, as an objectwise bijection between the functor of
points `T ↦ (T ⟶ Q)` of a representing `S`-scheme `Q` and the moduli functor (the
helper `RepresentsFunctor` below); naturality of the bijection is recorded
informally, because the moduli functors land in `Type (u+1)` while the Hom-sets land
in `Type u`, so no `Type`-valued natural isomorphism is available across the
universe gap.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace MR2223407ConstructionHilbertQuot

/-! ## Representability shadow -/

/-- **Representability shadow.**  An `S`-scheme `Q` *represents* the set-valued
functor `F` on `S`-schemes when, objectwise, its functor of points
`T ↦ (T ⟶ Q)` is in bijection with `F`.  Naturality of the bijection in `T` is
recorded informally (cf. `Functors.grassmannian_represents`): the moduli functors
take values in `Type (u+1)` whereas the Hom-sets `(T ⟶ Q)` lie in `Type u`, so a
`Type`-valued natural isomorphism cannot be formed across the universe gap.  This
is the closest expressible shadow of "the functor `F` is representable by the
scheme `Q`". -/
def RepresentsFunctor {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v) (Q : Over S) : Prop :=
  Nonempty (∀ T : Over S, (T ⟶ Q) ≃ F.obj (Opposite.op T))

/-! ## Quot scheme in the quasi-projective case -/

/-- **Quot of an open is an open subfunctor** (`lem:quot-open-subfunctor`).

Let `π : Z ⟶ S` be a proper morphism of (noetherian) schemes, `Y ⊆ Z` a closed
subscheme and `F` a coherent sheaf on `Z`.  Then there is an open subscheme
`S' ⊆ S` with the universal property that `T → S` factors through `S'` iff the
support of `F_T` is disjoint from `Y_T`.  As a consequence, for `X ⊆ Z` open and
`E` coherent on `Z`, `Quot_{E|X/X/S}` is an open subfunctor of `Quot_{E/Z/S}`.

STATING-GAP: the *schematic support* of a coherent sheaf is a Mathlib gap, so the
support locus is taken as abstract closed-set input `suppF`.  The expressible,
non-vacuous heart of the first exercise is then exactly *properness ⟹ closed map*:
the image `π(suppF ∩ Y)` is closed, hence its complement is the open subscheme `S'`,
and a morphism factors through `S'` (its image lands in the open set) iff its image
avoids that closed image.  The functor-level "open subfunctor" consequence and the
sheaf-restriction bookkeeping are deferred to the prover stage. -/
theorem quot_open_subfunctor {S Z : Scheme.{u}} (π : Z ⟶ S) [IsProper π]
    (Y : Set Z) (_hY : IsClosed Y) (suppF : Set Z) (_hsupp : IsClosed suppF) :
    ∃ U : S.Opens, (↑U : Set S) = (π.base '' (suppF ∩ Y))ᶜ ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (Set.range g.base ⊆ (↑U : Set S)) ↔
          (Set.range g.base ∩ π.base '' (suppF ∩ Y) = ∅) :=
  sorry

/-- **Strongly quasi-projective Quot, Altman–Kleiman**
(`thm:strongly-quasiprojective-quot`).

Let `S` be noetherian, `X` a locally closed subscheme of `ℙ(V)` for a vector bundle
`V` on `S`, `L = O_{ℙ(V)}(1)|_X`, `E` a coherent quotient of `π*(W)(ν)|_X` (with `W`
a vector bundle on `S`, `ν ∈ ℤ`), and `Φ ∈ ℚ[λ]`.  Then `Quot^{Φ,L}_{E/X/S}` is
representable by a scheme that embeds over `S` as a locally closed subscheme of
`ℙ(F)` for some vector bundle `F` on `S`.

STATING-GAP: `L = O_{ℙ(V)}(1)|_X` and `E = (π*(W)(ν)|_X)`-quotient mention the Serre
twist `O(1)`/`(ν)` (Mathlib gap), so `L`, `E` are taken as general modules and `W`,
`ν` are retained as input data only.  "Locally closed subscheme of `ℙ(F)`" is
`IsImmersion` into `relativeProj S F` compatible with the structure morphisms; that
`F` is an exterior power of `W ⊗ Symᵏ V` is not tracked (those functors are gaps). -/
theorem stronglyQuasiprojectiveQuot {S : Scheme.{u}} [IsLocallyNoetherian S]
    (V : S.Modules) (_W : S.Modules) (_ν : ℤ) (X : Scheme.{u})
    (jX : X ⟶ relativeProj S V) (_hjX : IsImmersion jX) (π : X ⟶ S)
    (_hπ : jX ≫ relativeProj.structureMorphism S V = π) (E L : X.Modules)
    (Φ : Polynomial ℚ) :
    ∃ (F : S.Modules) (Q : Over S) (i : Q.left ⟶ relativeProj S F),
      RepresentsFunctor (quotFunctorPhi π E L Φ) Q ∧
        IsImmersion i ∧ i ≫ relativeProj.structureMorphism S F = Q.hom :=
  sorry

/-- **Coherent prolongation** (`lem:coherent-prolongation`).

Any coherent sheaf on an open subscheme `U` of a noetherian scheme `S` can be
prolonged to a coherent sheaf on all of `S`.

STATING-GAP: *coherence* is approximated by *quasi-coherence* (`IsQuasicoherent`),
matching the convention of `Functors.lean`.  The prolongation `G` is a
quasi-coherent sheaf on `S` whose restriction `U.ι^* G` to `U` is isomorphic to the
given `F`. -/
theorem coherent_prolongation {S : Scheme.{u}} [IsLocallyNoetherian S]
    (U : S.Opens) (F : U.toScheme.Modules) (_hF : F.IsQuasicoherent) :
    ∃ G : S.Modules, G.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj G ≅ F) :=
  sorry

/-- **Quasi-projective Quot, Grothendieck** (`thm:quasiprojective-quot`).

Let `S` be noetherian, `X` quasi-projective over `S`, `L` relatively very ample on
`X`, `E` a quotient sheaf and `Φ ∈ ℚ[λ]`.  Then `Quot^{Φ,L}_{E/X/S}` is
representable by a scheme `Q` which is quasi-projective over `S`.

Quasi-projectivity of `X` (resp. of the representing `Q`) is rendered as the
existence of an `IsImmersion` (locally closed immersion) into a projective bundle
`relativeProj S V` compatible with the structure morphism, as in `Basic.lean`. -/
theorem quasiprojectiveQuot {S X : Scheme.{u}} [IsLocallyNoetherian S] (π : X ⟶ S)
    (L E : X.Modules) (_hL : RelativelyVeryAmple π L) (Φ : Polynomial ℚ)
    (_hX : ∃ V : S.Modules, ∃ i : X ⟶ relativeProj S V,
      IsImmersion i ∧ i ≫ relativeProj.structureMorphism S V = π) :
    ∃ Q : Over S, RepresentsFunctor (quotFunctorPhi π E L Φ) Q ∧
      (∃ V : S.Modules, ∃ i : Q.left ⟶ relativeProj S V,
        IsImmersion i ∧ i ≫ relativeProj.structureMorphism S V = Q.hom) :=
  sorry

/-! ## The Hilbert scheme -/

/-- **The Hilbert functor / Hilbert scheme** (`def:hilbert-scheme`).

The Hilbert functor `Hilb^{Φ,L}_{X/S}` is by definition the Quot functor of the
structure sheaf `O_X`, namely `Quot^{Φ,L}_{O_X/X/S}`; here `O_X` is realised as the
rank-one free module `freeModule X 1` (cf. `Functors.hilbertFunctor`).  When it is
representable, the representing scheme is the *Hilbert scheme*
`hilb^{Φ,L}_{X/S} = quot^{Φ,L}_{O_X/X/S}` (its existence is `hilbertScheme_exists`).

We define `hilbertScheme` to be this Hilbert functor; the representing scheme is
recovered, where it exists, via `RepresentsFunctor (hilbertScheme π L Φ) Q`. -/
noncomputable def hilbertScheme {S X : Scheme.{u}} (π : X ⟶ S) (L : X.Modules)
    (Φ : Polynomial ℚ) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  quotFunctorPhi π (freeModule X 1) L Φ

/-- **Existence of the Hilbert scheme** (`thm:hilbert-scheme-exists`).

Let `S` be noetherian, `X` strongly projective over `S` with relatively very ample
`L`, and `Φ ∈ ℚ[λ]`.  Then `Hilb^{Φ,L}_{X/S}` is representable by a scheme `Q` which
is a closed subscheme of a projective bundle `ℙ(F)` over `S`; in particular the
Hilbert scheme is projective over `S`.

"Strongly projective" / "projective over `S`" is rendered as the `IsClosedImmersion`
of the representing scheme into `relativeProj S F`. -/
theorem hilbertScheme_exists {S X : Scheme.{u}} [IsLocallyNoetherian S] (π : X ⟶ S)
    (L : X.Modules) (_hL : RelativelyVeryAmple π L) (Φ : Polynomial ℚ) :
    ∃ (F : S.Modules) (Q : Over S) (i : Q.left ⟶ relativeProj S F),
      RepresentsFunctor (hilbertScheme π L Φ) Q ∧
        IsClosedImmersion i ∧ i ≫ relativeProj.structureMorphism S F = Q.hom :=
  sorry

/-! ## Scheme of morphisms -/

/-- **Local criterion of flatness** (`lem:flatness-local-criterion`).

Foundational flatness facts (noetherian schemes), cited to Altman–Kleiman [A-K 1]
Ch. V; not re-proved here.  We state the two expressible parts as a conjunction:
**(1)** a locally-of-finite-type flat morphism is an open map; **(2)** the flat locus
`{y | π flat at y}` of a locally-of-finite-type morphism `π : Y ⟶ X` is open, where
"`π` flat at `y`" is `O_{Y,y}` flat over `O_{X,π(y)}` along the stalk map, rendered
via `RingHom.Flat (π.stalkMap y).hom`.

STATING-GAP: part **(3)** (the local criterion proper: fibrewise flatness at `y`
implies flatness at `y` for a morphism over a flat base) requires the scheme-theoretic
fibre `Y_s` and flatness there; the fibre construction is deferred, so (3) is omitted
here and treated as a literature citation. -/
theorem flatness_local_criterion :
    (∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsLocallyNoetherian X] [LocallyOfFiniteType f] [Flat f],
        IsOpenMap f.base) ∧
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsLocallyNoetherian X] [LocallyOfFiniteType f],
        IsOpen {y : Y | RingHom.Flat (f.stalkMap y).hom}) := by
  refine ⟨?_, ?_⟩
  · -- (1) A locally-of-finite-type flat morphism (to a locally noetherian target) is open.
    -- Over a locally noetherian base, `LocallyOfFiniteType` upgrades to
    -- `LocallyOfFinitePresentation` (Mathlib instance), and a flat morphism that is
    -- locally of finite presentation is universally open, hence an open map.
    intro X Y f _ _ _
    have : LocallyOfFinitePresentation f := inferInstance
    have : UniversallyOpen f := inferInstance
    exact f.isOpenMap
  · -- (2) Openness of the flat locus of a finite-type morphism over a noetherian base.
    -- GAP (EGA IV 11.1.1 / 11.3.1, "openness of flatness"): the set of points where a
    -- morphism locally of finite type over a noetherian base is flat is open.  This is NOT
    -- yet in Mathlib: only the *smooth* locus (`Algebra.isOpen_smoothLocus`) and the
    -- locally-*free* locus of a finitely-presented module (`Module.freeLocus`,
    -- `Module.isOpen_freeLocus`) are available, neither of which yields openness of the
    -- *flat* locus of the stalk maps `O_{Y,y}`-over-`O_{X,f(y)}`.  The standard proof
    -- (reduce to affine charts, then the ring-theoretic openness of the flat locus of a
    -- finitely-presented algebra over a noetherian ring via the local criterion of flatness
    -- and noetherian induction) is a substantial development, well beyond a ~100 LOC helper.
    -- No informal-agent key is available in this environment.  See
    -- `informal/flatness_local_criterion_flat_locus.md` for the precise missing statement.
    intro X Y f _ _
    sorry

/-- **Flat-locus and isomorphism-locus are open** (`thm:isomorphism-is-open`).

Let `S` be noetherian, `f : X ⟶ S` and `g : Y ⟶ S` proper flat, and `π : Y ⟶ X`
projective with `g = f ∘ π`.  Then `S` has open subschemes `S₂ ⊆ S₁ ⊆ S` such that
for any `S`-scheme `T → S` with base change
`π_T : Y_T = T ×_S Y ⟶ X_T = T ×_S X`:
**(a)** `π_T` is flat iff `T → S` factors through `S₁`; **(b)** `π_T` is an
isomorphism iff `T → S` factors through `S₂`.

"Projective" `π` is approximated by `[IsProper π]`.  The base change `π_T` is the
canonical `pullback.map`; "factors through the open `Sᵢ`" is rendered as the point-set
condition `Set.range φ.base ⊆ Sᵢ`. -/
theorem isomorphism_is_open {S X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g] [Flat f] [Flat g]
    (π : Y ⟶ X) [IsProper π] (hπ : π ≫ f = g) :
    ∃ S₁ S₂ : S.Opens, S₂ ≤ S₁ ∧
      (∀ {T : Scheme.{u}} (φ : T ⟶ S),
        (Set.range φ.base ⊆ (↑S₁ : Set S)) ↔
          Flat (pullback.map φ g φ f (𝟙 T) π (𝟙 S) (by simp) (by simp [hπ]))) ∧
      (∀ {T : Scheme.{u}} (φ : T ⟶ S),
        (Set.range φ.base ⊆ (↑S₂ : Set S)) ↔
          IsIso (pullback.map φ g φ f (𝟙 T) π (𝟙 S) (by simp) (by simp [hπ]))) :=
  sorry

/-- **The functor of `S`-morphisms** `Mor_S(X, Y)`.

`T ↦ {T-morphisms X_T ⟶ Y_T}`, where `X_T = X ×_S T`, `Y_T = Y ×_S T` and a
`T`-morphism is a scheme map commuting with the projections to `T`.  The functorial
action (pullback of morphisms) is stubbed, as for the Quot/Hilbert functors. -/
noncomputable def morFunctor {S : Scheme.{u}} (X Y : Over S) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := { h : pullback X.hom T.unop.hom ⟶ pullback Y.hom T.unop.hom //
              h ≫ pullback.snd Y.hom T.unop.hom = pullback.snd X.hom T.unop.hom }
  map _ := sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- **Scheme of morphisms** (`thm:scheme-of-morphisms`).

Let `S` be noetherian, `X` projective and flat over `S`, and `Y` quasi-projective
over `S`.  Then `Mor_S(X, Y)` is representable by an open subscheme `M` of the
Hilbert scheme of graphs `Hilb_{X×_S Y/S}`.

"Projective `X`" is `[IsProper X.hom]`; "quasi-projective `Y`" is `_hY` (an
`IsImmersion` into a projective bundle).  The Hilbert scheme of graphs is rendered
via `RepresentsFunctor (hilbertScheme π_{X×Y} L Φ) H` for some choice of relatively
very ample `L` and `Φ`; `M` embeds into it as an `IsOpenImmersion`. -/
theorem schemeOfMorphisms {S : Scheme.{u}} [IsLocallyNoetherian S] (X Y : Over S)
    [IsProper X.hom] [Flat X.hom]
    (_hY : ∃ V : S.Modules, ∃ i : Y.left ⟶ relativeProj S V,
      IsImmersion i ∧ i ≫ relativeProj.structureMorphism S V = Y.hom) :
    ∃ M : Over S, RepresentsFunctor (morFunctor X Y) M ∧
      ∃ (L : (pullback X.hom Y.hom).Modules) (Φ : Polynomial ℚ) (H : Over S),
        RepresentsFunctor (hilbertScheme (pullback.fst X.hom Y.hom ≫ X.hom) L Φ) H ∧
        ∃ i : M.left ⟶ H.left, IsOpenImmersion i ∧ i ≫ H.hom = M.hom :=
  sorry

/-! ## Quotient by a flat projective equivalence relation -/

/-- **Descent of closed subschemes** (`lem:descent-of-subschemes`).

**(1)** Any faithfully flat quasi-compact morphism `f : X ⟶ Y` is an effective
epimorphism: `f` is the coequaliser of the two projections
`p₁, p₂ : X ×_Y X ⇉ X`.  **(2)** For a faithfully flat quasi-compact `p : D ⟶ H`
and a closed `Z ⊆ D` with `p₁⁻¹Z = p₂⁻¹Z` in `D ×_H D`, there is a unique closed
`Q ⊆ H` with `Z = p⁻¹Q`.

STATING-GAP: in **(2)** the *scheme structure* descent (the ideal sheaf descending
along fppf, the `faithfullyFlatDescent` gap of `Basic.lean`) is deferred; we state
the topological shadow at the level of underlying sets — the closed set `Z` with the
set-level descent condition `p₁⁻¹Z = p₂⁻¹Z` descends to a unique closed `Q` with
`Z = p⁻¹Q`.  Part **(1)** is stated faithfully as `IsColimit` of the coequaliser
cofork. -/
theorem descent_of_subschemes :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
        (_hf : Function.Surjective f.base),
        Nonempty (IsColimit (Cofork.ofπ f (pullback.condition (f := f) (g := f))))) ∧
      (∀ {D H : Scheme.{u}} (p : D ⟶ H) [Flat p] [QuasiCompact p]
        (_hp : Function.Surjective p.base) (Z : Set D) (_hZ : IsClosed Z)
        (_hdesc : (pullback.fst p p).base ⁻¹' Z = (pullback.snd p p).base ⁻¹' Z),
        ∃! Q : Set H, IsClosed Q ∧ Z = p.base ⁻¹' Q) := by
  refine ⟨?_, ?_⟩
  · -- (1) A faithfully flat quasi-compact morphism is an effective epimorphism, hence the
    -- coequaliser of its kernel pair `p₁, p₂ : X ×_Y X ⇉ X`.  Surjective + Flat + QuasiCompact
    -- give `EffectiveEpi f` (Mathlib `Sites/Fpqc`), and an effective epi with a kernel pair is
    -- the colimit of the induced cofork (`isColimitCoforkOfEffectiveEpi`).
    intro X Y f _ _ hf
    have : Surjective f := ⟨hf⟩
    have : EffectiveEpi f := inferInstance
    exact ⟨isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit f f)⟩
  · -- (2) Set-level descent of a closed subset along a faithfully-flat quasi-compact `p`.
    -- The unique closed `Q` with `Z = p⁻¹Q` is `Q := p '' Z`.  Two ingredients:
    -- * `p` is a topological quotient map (`Flat.isQuotientMap_of_surjective`: flat + qc +
    --   surjective), so `Q` is closed iff `p⁻¹Q` is, and surjectivity forces uniqueness;
    -- * the underlying space of the scheme pullback `D ×_H D` surjects onto the set-theoretic
    --   fibre product (`exists_preimage_pullback`), which turns the descent hypothesis
    --   `p₁⁻¹Z = p₂⁻¹Z` into saturation of `Z`: `p⁻¹(p '' Z) = Z`.
    intro D H p _ _ hp Z hZ hdesc
    have hsurj : Surjective p := ⟨hp⟩
    have hq : Topology.IsQuotientMap (⇑p) := Flat.isQuotientMap_of_surjective p
    obtain ⟨_, hqcl⟩ := Topology.isQuotientMap_iff_isClosed.mp hq
    -- Saturation of `Z`: `p⁻¹(p '' Z) = Z`.
    have hsat : p.base ⁻¹' (p.base '' Z) = Z := by
      apply Set.Subset.antisymm
      · rintro d ⟨d', hd', hpd⟩
        obtain ⟨z, hz1, hz2⟩ :=
          Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) d d' hpd.symm
        have hzZ : z ∈ (pullback.snd p p).base ⁻¹' Z := by
          change (pullback.snd p p).base z ∈ Z
          rw [hz2]; exact hd'
        have hzZ' : z ∈ (pullback.fst p p).base ⁻¹' Z := hdesc ▸ hzZ
        have : (pullback.fst p p).base z ∈ Z := hzZ'
        rwa [hz1] at this
      · exact Set.subset_preimage_image _ _
    refine ⟨p.base '' Z, ⟨?_, ?_⟩, ?_⟩
    · -- `p '' Z` is closed: its preimage `p⁻¹(p '' Z) = Z` is closed and `p` is a quotient map.
      exact (hqcl (p.base '' Z)).mpr (by rw [hsat]; exact hZ)
    · -- `Z = p⁻¹(p '' Z)`.
      exact hsat.symm
    · -- Uniqueness: any closed `Q'` with `Z = p⁻¹Q'` equals `p '' Z` by surjectivity of `p`.
      rintro Q' ⟨_, hZQ'⟩
      rw [hZQ', Set.image_preimage_eq _ hp]

/-- **Quotient by a flat projective equivalence relation**
(`thm:projective-flat-quotient`).

Let `S` be noetherian and `X ⟶ S` quasi-projective.  Let `f : R ⟶ X ×_S X` be a
schematic equivalence relation whose projections `f₁, f₂ : R ⇉ X` are proper and
flat.  Then a schematic quotient `q : X ⟶ Q` exists over `S`; `Q` is quasi-projective
over `S`, `q` is faithfully flat and projective, and `(f₁, f₂) : R ⟶ X ×_Q X` is an
isomorphism (the quotient is effective).

The schematic equivalence relation is encoded by `f : R ⟶ X ×_S X` (the pullback of
`sX` with itself) with `f₁ = f ≫ pr₁`, `f₂ = f ≫ pr₂` proper and flat, and `f` a
monomorphism (functorial injectivity).  Quasi-projectivity of `X`/`Q` is the
`IsImmersion`-into-`relativeProj` shadow; "projective" `q` is approximated by
`IsProper q`; "faithfully flat" is `Flat q ∧ Function.Surjective q.base`;
"effective" is `IsIso` of the induced `R ⟶ X ×_Q X`; and "`q` is the quotient" is
`IsColimit` of the coequaliser cofork of `f₁, f₂`. -/
theorem projectiveFlatQuotient {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (sX : X ⟶ S)
    (_hX : ∃ V : S.Modules, ∃ i : X ⟶ relativeProj S V,
      IsImmersion i ∧ i ≫ relativeProj.structureMorphism S V = sX)
    (R : Scheme.{u}) (f : R ⟶ pullback sX sX) (_hf : Mono f)
    [IsProper (f ≫ pullback.fst sX sX)] [IsProper (f ≫ pullback.snd sX sX)]
    [Flat (f ≫ pullback.fst sX sX)] [Flat (f ≫ pullback.snd sX sX)] :
    ∃ (Q : Over S) (q : X ⟶ Q.left),
      q ≫ Q.hom = sX ∧
      (∃ V : S.Modules, ∃ i : Q.left ⟶ relativeProj S V,
        IsImmersion i ∧ i ≫ relativeProj.structureMorphism S V = Q.hom) ∧
      Flat q ∧ Function.Surjective q.base ∧ IsProper q ∧
      ∃ hq : (f ≫ pullback.fst sX sX) ≫ q = (f ≫ pullback.snd sX sX) ≫ q,
        Nonempty (IsColimit (Cofork.ofπ q hq)) ∧
        IsIso (pullback.lift (f ≫ pullback.fst sX sX) (f ≫ pullback.snd sX sX) hq) :=
  sorry

end MR2223407ConstructionHilbertQuot
