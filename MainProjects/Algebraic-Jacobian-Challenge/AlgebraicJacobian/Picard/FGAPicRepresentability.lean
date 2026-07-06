/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.DivFunctorDef

/-!
# FGA representability of the Picard scheme (A.2.c)

This file is the **A.2.c** assembly chapter for the project's positive-genus
arm of `nonempty_jacobianWitness`. It states the FGA representability of the
relative Picard functor of a smooth proper geometrically integral curve
`C/k`, following Kleiman, "The Picard scheme", §2 and §4 (cf. FGA Explained
Ch. 9; arXiv:math/0504020).

## Status (run-0008 rewire — `picSharp` is now the REAL relative functor)

The former §0 placeholder (`picSharp` as a `Classical.choice` extraction from
a `⟨sorry⟩`-backed `Nonempty` typeclass, with **no defining property**) has
been replaced: `picSharp C` is now **defined** as the honest relative Picard
functor

```
picSharp C := PicSharp.relPresheaf C ⋙ forget AddCommGrpCat
```

on the `H_T`-coset carrier `T ↦ Pic(C ×_k T)/π_T^* Pic(T)` of sibling
`Picard/RelPicFunctor.lean` (§4b there; blueprint
`def:rel_pic_sharp` after the coordinated repin). Consequently the
representability statements below have actual mathematical content: the
`RepresentableBy` witness extracted from `representable C` is a genuine
natural bijection `(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)`, which is
what the downstream tangent-space computation (`AJC.pic0av`,
`Pic0.tangentSpaceIso`) attaches to.

## The étale-sheafification route: Kleiman §2 Thm 2.5 (route (b))

Kleiman §4 represents the **étale-sheafified** functor `Pic_{(C/k)ét}`.
Mathlib at the pinned revision has no étale Grothendieck topology on
schemes, so instead of sheafifying we use Kleiman §2 **Thm 2.5**: when
`f : X → S` has a **section** and `O_S = f_* O_X` holds universally (true
for our proper geometrically integral `C/k`), the comparison maps

```
Pic_{X/S}(T) → Pic_{(X/S)ét}(T) → Pic_{(X/S)fppf}(T)
```

are all **bijective**. Hence, under a `k`-rational-point hypothesis
(`HasRationalPoint C` below), the *plain* relative functor `picSharp C` is
itself representable, and the FGA statement can be made against it directly
— no étale topology needed. Without a section the plain functor is NOT
representable in general (it need not even be a Zariski sheaf), which is why
the representability sorry `instHasPicScheme` below is **conditional on
`[HasRationalPoint C]`**: an unconditional instance would assert a false
statement. (Run-0008 memory `I-0061`: the same trap ruled out wiring
`picSharp` to the *absolute* functor `PicSharp.presheaf`.)

## Sorry accounting after the rewires (run 0008 `picSharp`, run 0010 fga-div)

The file has exactly **two** remaining sorry sites, both `⟨sorry⟩` instance
constructors of `Prop`-valued classes:

1. `instHasPicScheme` — the single genuine **FGA sorry**: existence of a
   representing scheme for `picSharp C`, **locally of finite type over `k`**,
   given a rational point (Kleiman §4 Thm `th:main`(1) + Cor `cor:algsch`,
   transported through §2 Thm 2.5). Run 0010 strengthened the existential to
   also carry local finiteness — part (1) of the same Kleiman theorem, one
   existence package — absorbing the former separate
   `instPicSchemeLocallyOfFiniteType` sorry.
2. `instHasAbelMap` — the `Nonempty` statement is true (the pointwise-zero
   natural transformation into the group-valued target witnesses it), but
   the extracted carrier stays opaque until the substantive Abel map
   `D ↦ [O_{C ×_k T}(D)]` lands.

Everything else is REAL or PROVED:

* `picSharp` — REAL (run 0008), the relative Picard functor.
* `divFunctor` — REAL (run 0010): the relative-divisor functor
  `Scheme.DivFunctor C.hom` of `Picard/DivFunctorDef.lean` (Kleiman §3
  Def. `df:div`, invertible-kernel quotient encoding); consequently
  `instHasDivFunctor` is **PROVED** (witness: `divFunctor C`).
* `instPicSharpRepresentable` — **PROVED** (`Exists.choose_spec.1`): the
  scheme chosen by `PicScheme` represents `picSharp C` by construction.
* `instPicSchemeLocallyOfFiniteType` — **PROVED** (run 0010,
  `Exists.choose_spec.2`): local finiteness is the second component of the
  strengthened `HasPicScheme` existential.
* `groupSchemeStructure` — **PROVED** via `GrpObj.ofRepresentableBy`:
  Yoneda transport of the abelian-group structure of `relPresheaf`.
* `smoothProperQuotient` — the Altman–Kleiman quotient lemma is kept as a
  theorem extracting from an explicit **use-site hypothesis class**
  `HasSmoothProperQuotient`. The former GLOBAL `⟨sorry⟩` instance was
  **deleted in run 0008**: it asserted `P.IsRepresentable` for *every*
  presheaf morphism `α : Z ⟶ P`, which is flagrantly false. Even the
  theorem's hypothesis list is weaker than Kleiman §4 Lem `lm:qt` (it
  omits quasi-projectivity of the representing scheme `Y`, not currently
  expressible in Mathlib — no `QuasiProjective` vocabulary), and with the
  étale-local lift hypothesis a Hironaka-type free ℤ/2-action on a smooth
  proper 3-fold gives a smooth proper equivalence relation whose quotient
  sheaf is an algebraic space that is NOT a scheme. The class must
  therefore be supplied at the use site, where quasi-projectivity of the
  Abel-map slice is available.

## References

Blueprint: `blueprint/src/chapters/Picard_FGAPicRepresentability.tex`.
Source: Kleiman, "The Picard scheme" (arXiv:math/0504020): §2 Thm 2.5
(`th:comp` comparison under a section), §3 Def `dfn:Abel` + Thm `th:repDiv`,
§4 Thm `th:main` + Cor `cor:algsch` + Lem `lm:qt`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- **`C` has a `k`-rational point**: the structural morphism `C.hom` admits a
section `σ : Spec k ⟶ C.left`. For the smooth proper geometrically integral
curves of this project this is the pointing `P : 𝟙_ (Over (Spec k)) ⟶ C`
already threaded through the Albanese statements (`AlgebraicJacobian.IsAlbanese`).

This is the hypothesis of Kleiman §2 **Thm 2.5**: together with
`O_S = f_* O_X` universally (automatic for proper geometrically integral
fibers), a section forces the comparison maps
`Pic_{X/S}(T) → Pic_{(X/S)ét}(T) → Pic_{(X/S)fppf}(T)` to be bijective, so
the *plain* relative Picard functor is already the étale sheaf that FGA
representability (Kleiman §4) represents. -/
class HasRationalPoint {k : Type u} [Field k] (C : Over (Spec (.of k))) : Prop where
  nonempty_section :
    Nonempty {σ : Spec (.of k) ⟶ C.left // σ ≫ C.hom = 𝟙 (Spec (.of k))}

namespace PicScheme

/-! ## §0. The relative Picard functor and the divisor functor

`picSharp` is the honest relative Picard functor of sibling
`Picard/RelPicFunctor.lean` (Kleiman §2 Def `df:Pfs`), with the group
structure forgotten (representability is a statement about the underlying
set-valued functor; the group structure is transported back onto the
representing scheme by `groupSchemeStructure` below).

`divFunctor` (the relative-effective-divisor functor `Div_{C/k}`, Kleiman §3
Def `df:div`) is, since run 0010, the REAL functor `Scheme.DivFunctor C.hom`
of sibling `Picard/DivFunctorDef.lean` (A.2.b), replacing the former
`⟨sorry⟩`-backed opaque carrier. -/

/-- **The relative Picard functor** `Pic^♯_{C/k} : (Sch/k)^op ⥤ Type (u+1)`,
`T ↦ Pic(C ×_k T)/π_T^* Pic(T)` — the set-valued shadow of the group-valued
presheaf `PicSharp.relPresheaf` of `Picard/RelPicFunctor.lean` (the honest
`H_T`-coset carrier of Kleiman §2 Def `df:Pfs`).

Run-0008 rewire: this replaces the former opaque
`Classical.choice`-of-`⟨sorry⟩` placeholder; it is now a REAL definition with
computational content, so `RepresentableBy` witnesses against it carry a
genuine natural bijection `(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)`.

Universe note: the values live in `Type (u+1)` because the line-bundle
carrier `LineBundle.OnProduct` is a quotient of (large) sheaves of modules.
`Functor.RepresentableBy` is universe-polymorphic, so representability by a
(`Type u`-homed) scheme remains a well-formed — and, under a rational point,
true — statement. -/
noncomputable def picSharp {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1) :=
  PicSharp.relPresheaf C ⋙ CategoryTheory.forget AddCommGrpCat.{u+1}

/-- Typeclass asserting existence of the relative-divisor functor `Div_{C/k}`.
Run 0010: with the real functor `Scheme.DivFunctor` available
(`Picard/DivFunctorDef.lean`), the instance `instHasDivFunctor` below is
PROVED (witness: `divFunctor C = DivFunctor C.hom`), so this class carries no
sorry any more; it survives only as the blueprint-pinned existence carrier
(`def:has_div_functor`). -/
class HasDivFunctor {k : Type u} [Field k] (C : Over (Spec (.of k))) : Prop where
  has_div_functor : Nonempty ((Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1))

/-- **The relative-divisor functor** `Div_{C/k} : (Sch/k)^op ⥤ Type (u+1)`,
sending a `k`-scheme `T` to the set of relative effective Cartier divisors on
`C ×_k T` flat over `T` (Kleiman §3 Def. `df:div`).

Run-0010 rewire (following the run-0008 `picSharp` pattern): this is now
**defined** as the honest relative-divisor functor

```
divFunctor C := Scheme.DivFunctor C.hom
```

of sibling `Picard/DivFunctorDef.lean` — `T`-flat invertible-kernel quotients
of `O_{C ×_k T}` modulo `ker q = ker q'`, i.e. Kleiman's set of relative
effective divisors — replacing the former OPAQUE
`Classical.choice`-of-`⟨sorry⟩` extraction. Natural transformations out of it
(the Abel map `abelMap` below) therefore have actual mathematical content.
The former `[HasDivFunctor _C]` argument is dropped: the class survives above
as the (now proved) blueprint-pinned existence carrier, but the definition no
longer routes through it. -/
noncomputable def divFunctor {k : Type u} [Field k]
    (C : Over (Spec (.of k))) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1) :=
  DivFunctor C.hom

/-- Existence instance for `HasDivFunctor` — **PROVED** (run 0010): the real
relative-divisor functor `divFunctor C = Scheme.DivFunctor C.hom` witnesses
the existential. Formerly the `⟨sorry⟩`-carrying site for the `divFunctor`
carrier; the sorry is closed by the A.2.b engine. -/
instance instHasDivFunctor {k : Type u} [Field k]
    (C : Over (Spec (.of k))) : HasDivFunctor C :=
  ⟨⟨divFunctor C⟩⟩

end PicScheme

/-! ## §1. The Picard scheme

The Picard scheme `Pic_{C/k}` of a smooth proper geometrically integral curve
`C/k` **with a `k`-rational point** is the `k`-scheme representing the
relative Picard functor `picSharp C` (which, under the rational point, agrees
with the étale-sheafified functor of Kleiman §4 Thm `th:main` by Kleiman §2
Thm 2.5). The scheme is separated, locally of finite type over `k`, and a
disjoint union of open quasi-projective `k`-subschemes; the
abelian-group-scheme structure is `groupSchemeStructure` below.

Blueprint reference: `def:pic_scheme` (Kleiman §4 Def. `df:Psch`). -/

/-- Typeclass asserting existence of a scheme over `Spec k` that represents
the relative Picard functor `picSharp C` **and is locally of finite type over
`k`**. The single sorry-carrying site for `PicScheme` is the `⟨sorry⟩`
instance below, **conditional on `[HasRationalPoint C]`** — without a section
the plain relative functor is not representable in general, so an
unconditional instance would assert a false statement. Consumers that
quantify over `[HasPicScheme C]` as a hypothesis remain kernel-clean.

Run 0010 strengthening: the existential also carries
`LocallyOfFiniteType X.hom`. This is truth-preserving because Kleiman §4 Thm
`th:main`(1) makes local finiteness part of the SAME existence package as
representability (`Pic_{C/k}` is a disjoint union of open quasi-projective
`k`-subschemes), so the strengthened statement is exactly as true as the old
one; it lets the local-finiteness carrier `instPicSchemeLocallyOfFiniteType`
be PROVED by extraction instead of carrying its own sorry. -/
class HasPicScheme {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : Prop where
  has_pic_scheme : ∃ (X : Over (Spec (.of k))),
    Nonempty ((PicScheme.picSharp C).RepresentableBy X) ∧ LocallyOfFiniteType X.hom

/-- The **Picard scheme** `Pic_{C/k}` of a smooth proper geometrically
integral curve `C/k`, encoded as an object of `Over (Spec (.of k))`.

Extracted (`Classical.choose`) from the `HasPicScheme` existence field, so it
carries the substantive identity "this scheme represents the relative Picard
functor `picSharp C`" through `representable` below — which, after the
run-0008 rewire, is a genuine natural bijection onto
`Pic(C ×_k T)/π_T^* Pic(T)`, not an opaque placeholder. -/
noncomputable def PicScheme {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    Over (Spec (.of k)) :=
  (HasPicScheme.has_pic_scheme (C := C)).choose

/-- Existence instance for `HasPicScheme` — **the single genuine FGA sorry of
this file**. Mathematical content: Kleiman §4 Thm `th:main` + Cor
`cor:algsch` (the étale-sheafified relative Picard functor of a smooth proper
geometrically integral curve is representable by a separated `k`-scheme
locally of finite type), combined with Kleiman §2 Thm 2.5 (under the
`k`-rational point of `[HasRationalPoint C]`, the plain relative functor
`picSharp C` coincides with the étale-sheafified one, so the same scheme
represents it).

Run 0010: this sorry now also carries Kleiman §4 Thm `th:main`(1) — the
representing scheme is **locally of finite type** over `k` (a disjoint union
of open quasi-projective `k`-subschemes) — since the strengthened
`HasPicScheme` existential packages local finiteness together with
representability; the former separate `instPicSchemeLocallyOfFiniteType`
sorry is absorbed into this one.

The conditionality on `[HasRationalPoint C]` is essential for truth: without
a section, `Pic(C ×_k T)/π_T^* Pic(T)` need not even be a Zariski sheaf. -/
noncomputable instance instHasPicScheme {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasRationalPoint C] : HasPicScheme C :=
  ⟨sorry⟩

namespace PicScheme

/-! ## §2. The Abel map — line-bundle / Quot correspondence

The bridge from line bundles on `C ×_k T` to the Quot scheme is the **Abel
map**: a relative effective divisor `D ⊆ C ×_k T` over `T` determines a
`T`-point of `Div_{C/k}`, and the dual ideal sheaf
`O_{C ×_k T}(D) := I_D⁻¹` represents a class in `Pic^♯_{C/k}(T)`.

Blueprint reference: `lem:line_bundle_quot_correspondence` (Kleiman §3
Def. `dfn:Abel` + Thm. `th:repDiv`). -/

/-- Typeclass asserting existence of the Abel map `Div_{C/k} ⟶ Pic^♯_{C/k}`.
The single `⟨sorry⟩` instance below is the unique sorry-carrying site for
`abelMap`. (The bare `Nonempty` statement is true — the pointwise-zero
natural transformation into the group-valued target witnesses it — but the
carrier stays opaque until the substantive Abel map arrives with the
Quot-scheme engine.) -/
class HasAbelMap {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : Prop where
  has_abel_map : Nonempty (divFunctor C ⟶ picSharp C)

/-- The **Abel map** `A_{C/k} : Div_{C/k} ⟶ Pic^♯_{C/k}`, sending a relative
effective Cartier divisor `D ⊆ C ×_k T` over `T` to its associated invertible
sheaf `[O_{C ×_k T}(D)] = [I_D⁻¹]`.

The run-0008 rewire made the TARGET the real relative Picard functor, and the
run-0010 rewire made the SOURCE the real relative-divisor functor
(`divFunctor C = Scheme.DivFunctor C.hom`), so both endpoints now have
mathematical content; the natural transformation ITSELF is still extracted
from `HasAbelMap.has_abel_map` via `Classical.choice` and remains without
defining property until the substantive Abel map
`⟨F, q⟩ ↦ [(ker q)⁻¹]` is constructed. -/
noncomputable def abelMap {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasAbelMap C] :
    divFunctor C ⟶ picSharp C :=
  Classical.choice (HasAbelMap.has_abel_map (C := C))

/-- Existence instance for `HasAbelMap`. This is the single sorry-carrying
site for `abelMap`. -/
noncomputable instance instHasAbelMap {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : HasAbelMap C :=
  ⟨sorry⟩

/-! ## §3. The smooth-proper quotient lemma — Altman–Kleiman descent

The structural lemma underlying Step 4 of Kleiman §4 Thm. `th:main`: given a
surjection `α : Z ⟶ P` of étale sheaves with `R := Z ×_P Z` representable,
`Z` representable **by a quasi-projective scheme**, and the first projection
`R ⟶ Z` smooth and proper, the quotient `P` is representable.

**Run-0008 restructure (truth audit).** The former global instance
`instHasSmoothProperQuotient : ∀ α, HasSmoothProperQuotient α := ⟨sorry⟩`
asserted that EVERY presheaf receiving any natural transformation is
representable — flagrantly false — and was deleted. Moreover the theorem's
own hypothesis list is strictly weaker than Kleiman §4 Lem `lm:qt`: it lacks
**quasi-projectivity of `Y`** (not currently expressible — Mathlib has no
`QuasiProjective` vocabulary), and without it the statement is false: a
Hironaka-type free `ℤ/2`-action on a smooth proper non-projective 3-fold
gives a smooth proper equivalence relation satisfying hypotheses (1)–(4)
whose quotient étale sheaf is an algebraic space that is not a scheme.

`HasSmoothProperQuotient α` therefore survives only as an **explicit
use-site hypothesis**: the intended consumer (the FGA assembly, Step 4 of
`th:main`) instantiates it for the Abel-map slice `Z ⟶ P^{φ_0}_0`, where `Z`
is a quasi-projective open of `Div_{C/k}` and Altman–Kleiman descent
genuinely applies. Supplying that instance is part of the `instHasPicScheme`
obligation, not a standalone global fact.

Blueprint reference: `lem:smooth_proper_quotient` (Kleiman §4 Lem. `lm:qt`). -/

/-- Hypothesis class packaging the CONCLUSION of the Altman–Kleiman
smooth-proper quotient lemma for a specific étale-sheaf surjection `α`:
that the target presheaf is representable.

There is deliberately NO global instance (run-0008: the former global
`⟨sorry⟩` instance was a false statement — see the section header). The
class is supplied at the use site, where the Kleiman `lm:qt` hypotheses —
including the quasi-projectivity of the representing scheme, which the
`smoothProperQuotient` statement below cannot yet express — actually hold. -/
class HasSmoothProperQuotient {k : Type u} [Field k]
    {Z P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1)}
    (_α : Z ⟶ P) : Prop where
  is_representable : P.IsRepresentable

/-- **The smooth-proper quotient lemma — Altman–Kleiman descent of an
étale-sheaf surjection** (Kleiman §4 Lem. `lm:qt`).

Let `Z, P : (Sch/k)^op ⥤ Type (u+1)` be presheaves and `α : Z ⟶ P` a natural
transformation with: (1) `Z` representable by `Y`; (2) `R := Z ×_P Z`
representable by `R`; (3) the first projection `π : R ⟶ Y` smooth and proper;
(4) `α` an étale-local surjection (every `T`-point of `P` lifts along some
test morphism). Then, granting the use-site hypothesis
`[HasSmoothProperQuotient α]` (which additionally encodes Kleiman's
quasi-projectivity of `Y` — see the section header for why it cannot yet be
stated internally), `P` is representable.

The Lean body extracts the conclusion from the hypothesis class; the
mathematical content (Altman–Kleiman effective-equivalence-relation descent
+ EGA IV 8.11.5) lives at the use site supplying the instance. -/
theorem smoothProperQuotient {k : Type u} [Field k]
    {Z P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1)}
    (α : Z ⟶ P)
    (Y : Over (Spec (.of k)))
    (_hZ : Z.RepresentableBy Y)
    (R : Over (Spec (.of k)))
    (_hR : (Limits.pullback α α).RepresentableBy R)
    (π : R ⟶ Y)
    [Smooth π.left] [IsProper π.left]
    (_hα : ∀ ⦃T : (Over (Spec (.of k)))ᵒᵖ⦄ (p : P.obj T),
        ∃ (T' : (Over (Spec (.of k)))ᵒᵖ) (e : T ⟶ T') (z : Z.obj T'),
          α.app T' z = P.map e p)
    [HasSmoothProperQuotient α] :
    P.IsRepresentable :=
  HasSmoothProperQuotient.is_representable (_α := α)

/-! ## §4. The FGA representability theorem

Grothendieck's existence theorem for the Picard scheme (Kleiman §4 Thm.
`th:main`, specialised via Cor. `cor:algsch` to `S = Spec k`, `X = C`),
transported through Kleiman §2 Thm 2.5 to the plain relative functor under
the rational-point hypothesis: `picSharp C` is representable by `PicScheme C`.

Blueprint reference: `thm:fga_pic_representability`. -/

/-- Typeclass asserting that `picSharp C` is representable by `PicScheme C`.

Run-0008: this is now PROVED from `HasPicScheme` (the representing witness is
`Classical.choose`-extracted, so its `choose_spec` is exactly this
statement); the class survives only to preserve the blueprint-pinned
consumer signature of `representable`. -/
class PicSharpRepresentable {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : Prop where
  has_representable : Nonempty ((picSharp C).RepresentableBy (PicScheme C))

/-- Existence instance for `PicSharpRepresentable` — **proved** (run 0008):
`PicScheme C` is `Classical.choose` of the `HasPicScheme` existential, and
the first component of `Exists.choose_spec` says precisely that the chosen
scheme represents `picSharp C` (the second component, since the run-0010
strengthening, is local finiteness — see
`instPicSchemeLocallyOfFiniteType`). The FGA content lives upstream in
`instHasPicScheme`. -/
instance instPicSharpRepresentable {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : PicSharpRepresentable C :=
  ⟨(HasPicScheme.has_pic_scheme (C := C)).choose_spec.1⟩

/-- **FGA representability of the Picard scheme.**

Let `k` be a field and `C` a smooth proper geometrically integral curve over
`k` (with, through the `HasPicScheme` hypothesis chain, a `k`-rational
point). Then the relative Picard functor `Pic^♯_{C/k}` is representable by
the Picard scheme `PicScheme C`: there is a natural bijection

```
(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)
```

for every `k`-scheme `T`. After the run-0008 rewire this `RepresentableBy`
structure is a genuine comparison against the real relative Picard functor
(not an opaque placeholder), so downstream consumers (tangent-space
computation at the identity, `Pic⁰` degree theory) can compose with its
`homEquiv` to transfer line-bundle data to scheme points. -/
noncomputable def representable {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] [PicSharpRepresentable C] :
    (picSharp C).RepresentableBy (PicScheme C) :=
  Classical.choice (PicSharpRepresentable.has_representable (C := C))

/-! ## §5. The abelian group-scheme structure

The Picard scheme `Pic_{C/k}` inherits an abelian group-scheme structure from
the tensor product of invertible sheaves on `C ×_k T`: the relative Picard
presheaf is group-valued (`PicSharp.relPresheaf`), and a representing object
of (the set-valued shadow of) a group-valued presheaf is canonically a group
object, by Yoneda transport (`GrpObj.ofRepresentableBy`).

Run-0008: with `picSharp` now REALLY equal to `relPresheaf ⋙ forget`, this
transport is a genuine proof, replacing the former `⟨sorry⟩`-backed
`PicSchemeGroupObject` carrier class (deleted).

Blueprint reference: `thm:pic_is_group_scheme` (Kleiman §2 Def. `df:Pfs` +
§4 Def. `df:Psch`). -/

/-- The multiplicative (`CommGrpCat`-valued) avatar of the relative Picard
presheaf, used to feed `GrpObj.ofRepresentableBy` (whose API is
multiplicative). Carrier-level it is the same functor: `Multiplicative` is a
type synonym. -/
noncomputable def picSharpCommGrp {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u+1} :=
  PicSharp.relPresheaf C ⋙ AddCommGrpCat.toCommGrp

/-- The set-valued shadows of `picSharpCommGrp` and `picSharp` agree up to
the canonical `Multiplicative.ofAdd` bijection (a natural isomorphism, since
`Multiplicative` is carrier-preserving). -/
noncomputable def picSharpCommGrpForgetIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    picSharp C ≅ picSharpCommGrp C ⋙ CategoryTheory.forget CommGrpCat.{u+1} :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Multiplicative.ofAdd
      (α := ((PicSharp.relPresheaf C).obj T : Type (u+1)))))
    (fun _ => rfl)

/-- **The Picard scheme is a commutative `k`-group scheme** — a canonical
`CommGrpObj` structure (i.e. `GrpObj` + `IsCommMonObj`) on `PicScheme C`,
obtained by Yoneda transport (`CommGrpObj.ofRepresentableBy`) of the
abelian-group structure of the relative Picard presheaf
`PicSharp.relPresheaf` along the representability witness `representable C`.
Concretely: `[L] + [M] = [L ⊗ M]`, `-[L] = [L⁻¹]`, unit `[O_{C ×_k T}]`,
transported through `(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)`.

Run-0008: this is now a real construction (the former `⟨sorry⟩`-backed
`PicSchemeGroupObject` carrier class is deleted), and it is STRONGER than
the old pinned statement: commutativity comes for free from the transport,
so the full abelian-group-scheme refinement promised by the blueprint
(`thm:pic_is_group_scheme`) lands in one step. -/
noncomputable instance groupSchemeStructure {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    CommGrpObj (PicScheme C) :=
  CommGrpObj.ofRepresentableBy (PicScheme C) (picSharpCommGrp C)
    ((representable C).ofIso (picSharpCommGrpForgetIso C))

/-! ## §6. Local finiteness of the Picard scheme

Kleiman §4 Thm `th:main`(1): the Picard scheme is separated and locally of
finite type over the base. Since the run-0010 strengthening, `HasPicScheme`
packages local finiteness together with the representability existential
(one existence package, as in Kleiman's theorem), so the carrier below is
PROVED by extraction. It is what the identity-component substrate
(`Picard/IdentityComponent.lean`, `GroupScheme.IdentityComponent`) consumes
to specialise to `G = PicScheme C`. -/

/-- Typeclass asserting that the structural morphism of the Picard scheme is
locally of finite type (Kleiman §4 Thm `th:main`(1): `Pic_{C/k}` is a
disjoint union of open quasi-projective `k`-subschemes, hence locally of
finite type). Run 0010: the instance below is PROVED — the strengthened
`HasPicScheme` existential carries local finiteness, so the property of the
`Classical.choose` witness is its second `choose_spec` component; the class
survives only to preserve the blueprint-pinned consumer signature. -/
class PicSchemeLocallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : Prop where
  locallyOfFiniteType : LocallyOfFiniteType (PicScheme C).hom

/-- Existence instance for `PicSchemeLocallyOfFiniteType` — **PROVED** (run
0010): Kleiman §4 Thm `th:main`(1) makes local finiteness part of the same
existence package as representability, so the strengthened `HasPicScheme`
existential carries it and the property of the chosen witness is the second
component of its `choose_spec`. The instance hypothesis is now
`[HasPicScheme C]` rather than `[HasRationalPoint C]`: the rational-point
conditionality lives entirely in `instHasPicScheme` (which supplies
`HasPicScheme C`), and any consumer able to name `PicScheme C` already
quantifies over `[HasPicScheme C]`. -/
instance instPicSchemeLocallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    PicSchemeLocallyOfFiniteType C :=
  ⟨(HasPicScheme.has_pic_scheme (C := C)).choose_spec.2⟩

/-- Projection of `PicSchemeLocallyOfFiniteType` to the Mathlib morphism
property, so that instance search finds `LocallyOfFiniteType (PicScheme
C).hom` whenever the carrier class is in scope (as the identity-component
substrate requires). -/
instance {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicSchemeLocallyOfFiniteType C] :
    LocallyOfFiniteType (PicScheme C).hom :=
  PicSchemeLocallyOfFiniteType.locallyOfFiniteType

end PicScheme

end Scheme

end AlgebraicGeometry
