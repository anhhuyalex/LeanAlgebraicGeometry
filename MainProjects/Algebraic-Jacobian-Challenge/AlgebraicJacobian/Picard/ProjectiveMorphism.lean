/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.SerreTwist
import AlgebraicJacobian.Picard.QuotFunctorDef

/-!
# Projective morphisms carrying a very ample line bundle

Mathlib v4.31 has no projective-morphism class and no (very) ampleness
vocabulary.  Following the encoding settled in inbox `I-0118` (comment
`C-0002`), this file defines:

* `ProjectiveSpace.twistingSheaf n₀ S m` — the Serre twist `O(m)` on the
  relative projective space `ℙ(n₀; S)`, the pullback of
  `ProjTwist.serreTwist` from the integral model along `toProjInt`;
* `ProjectiveSpace.twistingSheafBaseChange` — `O(m)` commutes with base
  change of the ambient projective space;
* `Scheme.Hom.IsProjectiveWith π L` — the **projective-with-`L`** predicate:
  `π : X ⟶ S` factors through a closed immersion `i : X ↪ ℙ(Fin (d+1); S)`
  over `S` with `L ≅ i^* O(1)`;

with the stability facts the Quot-scheme endgame consumes:

* `Scheme.Hom.IsProjectiveWith.isProper` — projective morphisms are proper;
* `Scheme.Hom.IsProjectiveWith.comp_isClosedImmersion` — a closed immersion
  into a projective scheme is projective (carrying the restricted bundle);
* `Scheme.Hom.IsProjectiveWith.baseChange` — stability under base change
  (carrying the pulled-back bundle).

Everything is at `Scheme.{0}`: the Serre twist rests on the descent engine
`Scheme.Modules.glue`, which is universe-monomorphic at `Scheme.GlueData.{0}`
(`GlueDescent.lean:934`).

Blueprint: `def:twisting_sheaf`, `def:projective_with`,
`lem:projective_with_proper`, `lem:projective_with_closed_immersion`,
`lem:projective_with_base_change`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (n₀ : Type) (S : Scheme.{0})

/-- The Serre twist `O(m)` on the relative projective space `ℙ(n₀; S)`:
the pullback of the glued twisting sheaf on the integral model. -/
def twistingSheaf (m : ℕ) : (ℙ(n₀; S)).Modules :=
  (Scheme.Modules.pullback (toProjInt n₀ S)).obj (ProjTwist.serreTwist n₀ m)

variable {S} {S' : Scheme.{0}}

/-- The Serre twist commutes with base change of the ambient projective
space: `(map g)^* O(m) ≅ O(m)`. -/
def twistingSheafBaseChange (g : S' ⟶ S) (m : ℕ) :
    (Scheme.Modules.pullback (map n₀ g)).obj (twistingSheaf n₀ S m) ≅
      twistingSheaf n₀ S' m :=
  Scheme.pullbackTriangleIso (map_toProjInt n₀ g) (ProjTwist.serreTwist n₀ m)

end ProjectiveSpace

/-- `π : X ⟶ S` is a **projective morphism carrying the line bundle `L`**
([Nitsure] §5, [EGA II] 5.5): there are a closed immersion
`i : X ↪ ℙ(Fin (d+1); S)` over `S` and an isomorphism of `L` with the
pullback of the Serre twist `O(1)`.  This is the faithful encoding of
"projective with relatively very ample `L`" settled in inbox `I-0118`. -/
def Scheme.Hom.IsProjectiveWith {X S : Scheme.{0}} (π : X ⟶ S) (L : X.Modules) :
    Prop :=
  ∃ (d : ℕ) (i : X ⟶ ℙ(Fin (d + 1); S)),
    IsClosedImmersion i ∧ i ≫ (ℙ(Fin (d + 1); S) ↘ S) = π ∧
      Nonempty (L ≅ (Scheme.Modules.pullback i).obj
        (ProjectiveSpace.twistingSheaf (Fin (d + 1)) S 1))

namespace Scheme.Hom.IsProjectiveWith

variable {X S : Scheme.{0}} {π : X ⟶ S} {L : X.Modules}

/-- **Projective morphisms are proper**: a closed immersion is proper, the
structural morphism of projective space is proper, and properness is stable
under composition. -/
theorem isProper (h : π.IsProjectiveWith L) : IsProper π := by
  obtain ⟨d, i, hi, hcomp, -⟩ := h
  haveI := hi
  rw [← hcomp]
  infer_instance

/-- **Projective morphisms are locally of finite type**: immediate from
`isProper`, since properness extends `LocallyOfFiniteType`.  This lets the
Quot-scheme endgame and the Hilbert-polynomial existence theorem derive finite
type from projectivity instead of carrying it as a separate hypothesis. -/
theorem locallyOfFiniteType (h : π.IsProjectiveWith L) : LocallyOfFiniteType π :=
  haveI := h.isProper; inferInstance

/-- **Projective morphisms are separated** (properness extends `IsSeparated`). -/
theorem isSeparated (h : π.IsProjectiveWith L) : IsSeparated π :=
  haveI := h.isProper; inferInstance

/-- **Projective morphisms are universally closed** (properness extends
`UniversallyClosed`). -/
theorem universallyClosed (h : π.IsProjectiveWith L) : UniversallyClosed π :=
  haveI := h.isProper; inferInstance

/-- **Transfer along an isomorphism of the carried bundle**: `IsProjectiveWith`
depends on `L` only up to isomorphism (it records the comparison `L ≅ i^* O(1)`
through `Nonempty`), so if `π` is projective carrying `L` and `L ≅ L'`, then `π`
is projective carrying `L'`.  Useful for consumers that only have the bundle up
to isomorphism. -/
theorem of_iso (h : π.IsProjectiveWith L) {L' : X.Modules} (e : L ≅ L') :
    π.IsProjectiveWith L' := by
  obtain ⟨d, i, hi, hcomp, ⟨eL⟩⟩ := h
  exact ⟨d, i, hi, hcomp, ⟨e.symm ≪≫ eL⟩⟩

/-- **Composition with a closed immersion**: if `π` is projective carrying
`L` and `j` is a closed immersion into `X`, then `j ≫ π` is projective
carrying `j^* L`. -/
theorem comp_isClosedImmersion (h : π.IsProjectiveWith L) {Y : Scheme.{0}}
    (j : Y ⟶ X) [IsClosedImmersion j] :
    (j ≫ π).IsProjectiveWith ((Scheme.Modules.pullback j).obj L) := by
  obtain ⟨d, i, hi, hcomp, ⟨e⟩⟩ := h
  haveI := hi
  refine ⟨d, j ≫ i, inferInstance, by rw [Category.assoc, hcomp], ?_⟩
  exact ⟨(Scheme.Modules.pullback j).mapIso e ≪≫
    Scheme.pullbackTriangleIso (rfl : j ≫ i = j ≫ i)
      (ProjectiveSpace.twistingSheaf (Fin (d + 1)) S 1)⟩

/-- The comparison morphism from the base-changed total space into the
base-changed projective space. -/
private def baseChangeLift {S' : Scheme.{0}} (g : S' ⟶ S) {d : ℕ}
    (i : X ⟶ ℙ(Fin (d + 1); S)) (hcomp : i ≫ (ℙ(Fin (d + 1); S) ↘ S) = π) :
    pullback π g ⟶ ℙ(Fin (d + 1); S') :=
  (ProjectiveSpace.isPullback_map (Fin (d + 1)) g).lift
    (pullback.fst π g ≫ i) (pullback.snd π g)
    (by rw [Category.assoc, hcomp, pullback.condition])

/-- **Stability under base change**: if `π : X ⟶ S` is projective carrying
`L` and `g : S' ⟶ S`, then the base change `X ×_S S' ⟶ S'` is projective
carrying the pullback of `L`. -/
theorem baseChange (h : π.IsProjectiveWith L) {S' : Scheme.{0}} (g : S' ⟶ S) :
    (pullback.snd π g).IsProjectiveWith
      ((Scheme.Modules.pullback (pullback.fst π g)).obj L) := by
  obtain ⟨d, i, hi, hcomp, ⟨e⟩⟩ := h
  haveI := hi
  refine ⟨d, baseChangeLift g i hcomp, ?_, ?_, ?_⟩
  · -- the comparison square exhibits the lift as the base change of `i`
    have h1 : baseChangeLift g i hcomp ≫ (ℙ(Fin (d + 1); S') ↘ S')
        = pullback.snd π g := IsPullback.lift_snd _ _ _ _
    have hsq : IsPullback (baseChangeLift g i hcomp) (pullback.fst π g)
        (ProjectiveSpace.map (Fin (d + 1)) g) i := by
      have hbig : IsPullback
          (baseChangeLift g i hcomp ≫ (ℙ(Fin (d + 1); S') ↘ S'))
          (pullback.fst π g) g (i ≫ (ℙ(Fin (d + 1); S) ↘ S)) := by
        rw [h1, hcomp]
        exact (IsPullback.of_hasPullback π g).flip
      exact IsPullback.of_right hbig
        (IsPullback.lift_fst _ _ _ _)
        (ProjectiveSpace.isPullback_map (Fin (d + 1)) g).flip
    exact MorphismProperty.of_isPullback hsq.flip hi
  · exact IsPullback.lift_snd _ _ _ _
  · refine ⟨(Scheme.Modules.pullback (pullback.fst π g)).mapIso e ≪≫
      Scheme.pullbackTriangleIso (IsPullback.lift_fst _ _ _ _ :
        baseChangeLift g i hcomp ≫ ProjectiveSpace.map (Fin (d + 1)) g
          = pullback.fst π g ≫ i).symm
        (ProjectiveSpace.twistingSheaf (Fin (d + 1)) S 1) ≪≫ ?_⟩
    -- collapse `(lift ≫ map)^* O(1)` to `lift^* (map^* O(1))`, then use the
    -- base-change isomorphism of the twist
    exact (Scheme.pullbackTriangleIso
        (rfl : baseChangeLift g i hcomp ≫ ProjectiveSpace.map (Fin (d + 1)) g
          = _) (ProjectiveSpace.twistingSheaf (Fin (d + 1)) S 1)).symm ≪≫
      (Scheme.Modules.pullback (baseChangeLift g i hcomp)).mapIso
        (ProjectiveSpace.twistingSheafBaseChange (Fin (d + 1)) g 1)

end Scheme.Hom.IsProjectiveWith

namespace ProjectiveSpace

/-- **The structural morphism of relative projective space is itself
projective**, carrying the Serre twist `O(1)`: the canonical inhabitant of
`IsProjectiveWith`, with the identity closed immersion.  This exhibits
`ℙ(Fin (d+1); S) ↘ S` as the universal projective morphism and shows the
predicate is non-vacuous. -/
theorem isProjectiveWith_over (d : ℕ) (S : Scheme.{0}) :
    (ℙ(Fin (d + 1); S) ↘ S).IsProjectiveWith (twistingSheaf (Fin (d + 1)) S 1) :=
  ⟨d, 𝟙 _, inferInstance, Category.id_comp _,
    ⟨((Scheme.Modules.pullbackId _).app _).symm⟩⟩

end ProjectiveSpace

end AlgebraicGeometry
