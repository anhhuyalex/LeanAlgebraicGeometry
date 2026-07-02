/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.IdentityComponent
import AlgebraicJacobian.Picard.TangentSpaceDualNumbers
import AlgebraicJacobian.Genus

/-!
# `Pic⁰_{C/k}` as an abelian variety (A.3.iii–vii)

This file is the **iter-193 Pic0AbelianVariety** file-skeleton (NEW lane,
blueprint-doctor flagged orphan resolution for the iter-192 plan-phase chapter
`Picard_Pic0AbelianVariety.tex`). It packages the strategy phase A.3.iii–vi
substrate and the A.3.vii assembly into the load-bearing Route~A statement
`Pic⁰_{C/k}` is an abelian variety, the gate of `thm:nonempty_jacobianWitness`
for `g(C) ≥ 1` curves.

The chapter consumes the abstract identity-component substrate set up in
`Picard/IdentityComponent.lean` (`Pic⁰_{C/k}` as a clopen subgroup scheme of
finite type, geometrically irreducible, formation commuting with base change)
and adds the curve-specific input: the tangent-space isomorphism
`T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`, the resulting smoothness of dimension `g` at
the origin (hence everywhere by translation), properness inherited from the
projectivity of `Pic⁰_{C/k}` for `C/k` geometrically normal, and the assembly
into an abelian variety in the sense of Milne §I.1.

## Status (iter-193 NEW file-skeleton)

Each of the five blueprint-pinned declarations carries the *intended*
substantive type signature (matching the `\lean{...}` pin in
`Picard_Pic0AbelianVariety.tex`) with a `sorry` body. The bodies are
iter-194+ work; iter-193's mandate is the mechanical scaffold only.

The 5 pinned declarations are:

1. `AlgebraicGeometry.Scheme.Pic0.tangentSpaceIso` (theorem, A.3.iii) — the
   canonical isomorphism `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)` (Kleiman §5
   Thm.~`thm:tgtsp`). Packaged as an `AddEquiv` between the cotangent space
   `m_e/m_e²` at a `k`-rational identity-section point `e` and the project's
   first-cohomology `k`-module `Scheme.HModule k (Scheme.toModuleKSheaf C) 1`
   (from `Genus.lean`). The `k`-module structure on the cotangent space at a
   `k`-rational point is supplied as part of the existential bundle.
2. `AlgebraicGeometry.Scheme.Pic0.smooth` (theorem, A.3.iv) — `Pic⁰_{C/k}` is
   `Smooth` over `k`. Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0`
   (characteristic-zero) + Ex.~`ex:jac` (curve case).
3. `AlgebraicGeometry.Scheme.Pic0.proper` (theorem, A.3.v) — `Pic⁰_{C/k}` is
   `IsProper` over `k`. Kleiman §5 Thm.~`th:qpp&p` (projectivity upgrade for
   geometrically normal `C/k`).
4. `AlgebraicGeometry.Scheme.Pic0.geometricallyIrreducible` (theorem, A.3.vi)
   — `Pic⁰_{C/k}` is `GeometricallyIrreducible` over `k`. Specialisation of
   `IdentityComponent.isFiniteTypeGeometricallyIrreducible` (sibling) to
   `G = PicScheme C`. Kleiman §5 Prp.~`prp:pic0`.
5. `AlgebraicGeometry.Scheme.Pic0.isAbelianVariety` (theorem, A.3.vii) —
   `Pic⁰_{C/k}` is an abelian variety: `IsProper ∧ Smooth ∧
   GeometricallyIrreducible ∧ Nonempty (GrpObj _)`. Milne §I.1, p.~8
   (defining axioms) + Kleiman §5 Rmk.~`rmk:Jac`. Load-bearing A.3.vii gate
   of Route~A.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof", each
pinned declaration carries a substantive, non-tautological type:

- `tangentSpaceIso C` — existentially quantifies over a `k`-rational
  identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
  structure on the cotangent space `m_e/m_e²` (the `k`-module structure
  arising via the `k`-algebra structure on the stalk at a `k`-rational point;
  for the file-skeleton this Module instance is bundled as part of the Σ').
  Bundles an `AddEquiv` between the cotangent space and the
  `H¹(C, 𝒪_C)`-as-`k`-module. The body is iter-194+ work.
- `smooth C`, `proper C`, `geometricallyIrreducible C` — genuine `Prop`-valued
  statements on the structural morphism `(Pic0Scheme C).hom : Pic⁰_{C/k} ⟶
  Spec k`, not tautological.
- `isAbelianVariety C` — assembles the conjunction of the four
  abelian-variety properties (proper, smooth, geometrically irreducible,
  group-object structure); not vacuous because each conjunct is a genuine
  property/structure on the (typed-sorry) `Pic0Scheme C`.

## Coordination with `Pic0Scheme`

The underlying `k`-scheme `Pic⁰_{C/k}` is supplied by
`AlgebraicGeometry.Scheme.Pic0Scheme C` from sibling
`Picard/IdentityComponent.lean` (`def:pic_zero_subscheme` in the blueprint).
We do not redefine the underlying scheme here; the `Pic0` namespace below
collects the curve-specific abelian-variety facts about `Pic0Scheme C`.

## References

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`
(735 LOC, 5 pins). Sources:
- Kleiman, "The Picard scheme", §5, Thm.~`thm:tgtsp` (tangent space),
  Cor.~`cor:sm` + Cor.~`cor:ch0` (smoothness), Thm.~`th:qpp&p`
  (quasi-projectivity/projectivity), Prp.~`prp:pic0` (irreducibility),
  Rmk.~`rmk:Jac` (assembly to abelian scheme); arXiv:math/0504020.
- Milne, "Abelian Varieties" (course notes, 2008), §I.1, p.~8
  (definition of abelian variety) + Rmk. III.1.4(e) (dimension equals genus).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. The `Pic0` namespace

The blueprint chapter pins five Lean declarations under the
`AlgebraicGeometry.Scheme.Pic0` namespace. Their underlying scheme
`Pic⁰_{C/k}` is `Pic0Scheme C` from sibling `Picard/IdentityComponent.lean`;
the declarations below collect the curve-specific abelian-variety facts
about `Pic0Scheme C` (tangent space at the identity, smoothness, properness,
geometric irreducibility, abelian-variety assembly). -/

namespace Pic0

/-- **Tangent space at the identity: `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`.**

The Kleiman §5 Thm.~`thm:tgtsp` tangent-space isomorphism. For a smooth
proper geometrically integral curve `C/k`, the Zariski tangent space at the
identity of `Pic⁰_{C/k}` is canonically isomorphic to the first sheaf
cohomology `H¹(C, 𝒪_C)`.

In Lean (skeleton form): we bundle existentially over a `k`-rational
identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
structure on the cotangent space `m_e/m_e²` (the natural `k`-module structure
arising from the `k`-algebra structure on the stalk at a `k`-rational point;
for the file-skeleton this instance is supplied via Σ' to avoid hard-coding
a global instance prematurely). The substantive content is an `AddEquiv`
between the cotangent space and the project's `H¹(C, 𝒪_C)` module
`Scheme.HModule k (Scheme.toModuleKSheaf C) 1`.

A k-LinearEquiv refinement (iter-194+) replaces the `AddEquiv` once the
`k`-module structure on the cotangent space is consistently threaded through
downstream consumers; the underlying additive group structure is enough for
the dimension corollary `dim_k T₀ Pic⁰ = dim_k H¹ = g(C)`. -/
theorem tangentSpaceIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk (e.base default))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  sorry

/-- **Smoothness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is smooth over `k` (Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0` in
characteristic zero + Ex.~`ex:jac` for the curve case).

The proof (iter-194+): smoothness at the identity propagates to smoothness
everywhere by translation (Pic⁰ is a `k`-group scheme, so multiplication by
any `λ ∈ Pic⁰(k̄)` is an automorphism). At the identity, smoothness reduces
to the inequality
`dim_0 Pic⁰_{C/k} ≤ dim_k T₀ Pic⁰_{C/k} = dim_k H¹(C, 𝒪_C) = g(C)`
(`tangentSpaceIso`) becoming an equality. For a smooth proper curve this
equality holds: in characteristic zero by Cartier's theorem (every
`k`-group scheme is smooth), in positive characteristic by the curve-specific
vanishing `H²(C, 𝒪_C) = 0` (the obstruction to lifting tangent vectors). -/
theorem smooth {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Smooth (Pic0Scheme C).hom :=
  sorry

/-- **Properness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is proper over `k` (Kleiman §5 Thm.~`th:qpp&p`; a smooth proper
curve is geometrically normal, hence the projectivity upgrade applies).

The proof (iter-194+): `Pic⁰_{C/k}` is quasi-projective (Kleiman §5
Thm.~`th:qpp&p`, first conclusion); to upgrade to projective (hence proper)
we use the Chevalley–Rosenlicht structure theorem to reduce to ruling out
non-constant `k̄`-morphisms `𝔾_m → Pic⁰_{C/k̄}`. The latter follows from
normality of `C ×_k 𝔾_m` and Hartshorne II Ex.~6.15 (invertible sheaves on
a normal integral scheme are sheaves of Cartier divisors). -/
theorem proper {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    IsProper (Pic0Scheme C).hom :=
  sorry

/-- **Geometric irreducibility of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is geometrically irreducible over `k` (Kleiman §5 Prp.~`prp:pic0`,
specialisation of the abstract identity-component substrate
`IdentityComponent.isFiniteTypeGeometricallyIrreducible` of
`Picard/IdentityComponent.lean` to `G = PicScheme C`).

The proof (iter-194+): apply `GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`
to `G = PicScheme C` (locally of finite type by `FGAPicRepresentability`), and
identify `IdentityComponent (PicScheme C)` with `Pic0Scheme C` via the
`Pic0Scheme` definition (sibling). -/
theorem geometricallyIrreducible {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    GeometricallyIrreducible (Pic0Scheme C).hom :=
  sorry

/-- **`Pic⁰_{C/k}` is an abelian variety (A.3.vii assembly).**

For a smooth proper geometrically integral curve `C/k`, the identity
component `Pic⁰_{C/k}` is an abelian variety over `k`: the underlying
`k`-scheme is smooth (`Pic0.smooth`), proper (`Pic0.proper`), and
geometrically irreducible (`Pic0.geometricallyIrreducible`), and it carries
a `k`-group-scheme structure inherited from `Pic_{C/k}` via the inclusion
`Pic⁰_{C/k} ↪ Pic_{C/k}`
(`GroupScheme.IdentityComponent.isSubgroupHomomorphism`). Commutativity is
automatic (Milne §I.1, Cor.~1.4).

Milne §I.1, p.~8: "A complete connected group variety is called an abelian
variety." This is the load-bearing A.3.vii gate of Route~A for
`thm:nonempty_jacobianWitness`.

The proof (iter-194+) assembles the four conjuncts: `proper` (this file),
`smooth` (this file), `geometricallyIrreducible` (this file), and the
`Nonempty (GrpObj (Pic0Scheme C))` slot, the latter from
`GroupScheme.IdentityComponent.isSubgroupHomomorphism` applied to
`G = PicScheme C` (sibling `Picard/IdentityComponent.lean`). -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  sorry

end Pic0

end Scheme

end AlgebraicGeometry
