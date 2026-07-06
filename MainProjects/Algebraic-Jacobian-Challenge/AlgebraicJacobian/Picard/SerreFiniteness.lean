/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveMorphism

/-!
# Serre finiteness for the section graded module (statement)

The deep remaining input of the Hilbert-polynomial lane
(`lem:sectionGradedModule_fg`, inbox `I-0109`): for a projective scheme over
a field carrying a very ample line bundle `L` and a coherent sheaf `F`, the
section graded ring `R(X, L) = ⊕ₘ Γ(X, L^{⊗m})` is Noetherian, the section
graded module `M(X, F, L) = ⊕ₘ Γ(X, F ⊗ L^{⊗m})` is a finite module over it,
and each graded component is a finite-dimensional `κ`-vector space.

This file gives the **honest statement** against the projectivity vocabulary
of `Picard/ProjectiveMorphism.lean` (the `IsProjectiveWith` closed-immersion
predicate — very ampleness in the encoding settled in inbox `I-0118`), as a
named typed `sorry` leaf: the proof is Serre's theorem ([Hartshorne] II.5.17
ff., [Nitsure] §1) and is genuinely deep (multi-session; it needs the
pushforward-to-projective-space reduction and cohomological finiteness on
`ℙⁿ`).

Compared with the blueprint node, which hypothesises an *ample* `L` and
passes to a Veronese power, the Lean statement hypothesises the very ample
form directly (`IsProjectiveWith`) — this is the form in which the
Quot-scheme endgame ([Nitsure] §5) consumes it.

Blueprint: `lem:sectionGradedModule_fg`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

/-- The structural `κ`-algebra structure on the global sections of a scheme
over `Spec κ` (the absolute analogue of `Scheme.Hom.fiberResidueMap`). -/
def Scheme.Hom.structuralSectionsHom {X : Scheme.{0}} {κ : Type} [CommRing κ]
    (π : X ⟶ Spec (CommRingCat.of κ)) : κ →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv ≫ π.appTop).hom

/-- **Serre finiteness for the section graded module**
(`lem:sectionGradedModule_fg`; [Nitsure] §1, [Hartshorne] II.5.17 ff.):
for `π : X ⟶ Spec κ` projective carrying the very ample line bundle `L`
and a coherent (finitely presented) sheaf `F` on `X`,

1. the section graded ring `⊕ₘ Γ(X, L^{⊗m})` is Noetherian;
2. the section graded module `⊕ₘ Γ(X, F ⊗ L^{⊗m})` is a finite module
   over it;
3. each component `Γ(X, F ⊗ L^{⊗m})` is a finite-dimensional `κ`-vector
   space (via the structural `κ`-action).

NAMED LEAF (`sorry`): the geometric heart of the Hilbert-polynomial lane
(inbox `I-0109`), awaiting the pushforward-to-`ℙⁿ` reduction and
cohomological finiteness of coherent sheaves on projective space. -/
theorem sectionGradedModule_fg {X : Scheme.{0}} {κ : Type} [Field κ]
    (π : X ⟶ Spec (CommRingCat.of κ)) (L F : X.Modules)
    (hproj : π.IsProjectiveWith L) (hF : F.IsFinitePresentation) :
    (letI := Scheme.Modules.sectionGradedRing_gsemiring L
     IsNoetherianRing (DirectSum ℕ (Scheme.Modules.sectionDeg L)))
    ∧ (letI := Scheme.Modules.sectionGradedRing_gsemiring L
       letI := Scheme.Modules.sectionGradedModule_gmodule F L
       Module.Finite (DirectSum ℕ (Scheme.Modules.sectionDeg L))
         (DirectSum ℕ (Scheme.Modules.moduleSectionDeg F L)))
    ∧ ∀ m : ℕ,
        letI := Module.compHom (Scheme.Modules.moduleSectionDeg F L m)
          π.structuralSectionsHom
        FiniteDimensional κ (Scheme.Modules.moduleSectionDeg F L m) := by
  sorry

end AlgebraicGeometry
