# Analogy: encoding for `Scheme.RelativeSpec` (Spec_X(𝒜))

## Mode
api-alignment

## Slug
relativespec-encoding

## Iteration
178

## Question

What is the right Mathlib-aligned shape for the body of
`AlgebraicGeometry.Scheme.RelativeSpec (𝒜 : X.QcohAlgebra) : Scheme`
and its `structureMorphism`?

The iter-176 "closure" set `RelativeSpec 𝒜 := X`, `structureMorphism _ := 𝟙 X`,
silently discarding `𝒜`. The lean-auditor iter-177 marked both
declarations CRITICAL "weakened-wrong" and the progress-critic flagged
Route 2 CHURNING with the corrective "Mathlib-analogist consult on
RelativeSpec encoding BEFORE another body fill". Four candidate
encodings were proposed: (a) `QcohAlgebra` carrier + `Scheme.GlueData`;
(b) `Spec` of a relative graded ring; (c) functor-of-points; (d) some
other Mathlib-aligned shape. The first three are wrong or expensive;
the right answer is (d) — Mathlib already ships the construction.

## Project artifact(s)

- `AlgebraicJacobian/Picard/RelativeSpec.lean:172-173` — `RelativeSpec 𝒜 := X` (placeholder body, must-fix).
- `AlgebraicJacobian/Picard/RelativeSpec.lean:192-194` — `structureMorphism 𝒜 := 𝟙 X` (placeholder body, must-fix).
- `AlgebraicJacobian/Picard/RelativeSpec.lean:131-136` — `QcohAlgebra` Encoding I (sheaf + unit, *no quasi-coherence overlay yet*).
- `AlgebraicJacobian/Picard/RelativeSpec.lean:227-237`, `260-267`, `295-311` — the 3 downstream theorems that trivialize against `RelativeSpec := X`.
- `blueprint/src/chapters/Picard_RelativeSpec.tex` — Stacks 01LL/01LM/01LO/01LQ/01LR/01LS.

## Mathlib status at pinned commit `b80f227`

| Looked-for | Present? | Reference |
|---|---|---|
| `Scheme.RelativeSpec` / `AlgebraicGeometry.RelativeSpec` / `Spec_X` (named) | NO (no symbol) | — |
| **The construction itself**, under a different name | **YES** | `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:293` (`relativeGluingData`) |
| `Scheme.Cover.RelativeGluingData` (relative gluing API, Stacks 01LH) | YES | `Mathlib/AlgebraicGeometry/RelativeGluing.lean:74` |
| `RelativeGluingData.glued` (the glued scheme) | YES | `Mathlib/AlgebraicGeometry/RelativeGluing.lean:102` |
| `RelativeGluingData.toBase` (the structure morphism) | YES | `Mathlib/AlgebraicGeometry/RelativeGluing.lean:114` |
| `RelativeGluingData.cover` (affine open cover by `Spec(𝒜(U))`) | YES | `Mathlib/AlgebraicGeometry/RelativeGluing.lean:107` |
| `RelativeGluingData.isPullback_natTrans_ι_toBase` (universal-property building block) | YES | `Mathlib/AlgebraicGeometry/RelativeGluing.lean:172` |
| `NatTrans.Coequifibered` (Stacks 01LL form of quasi-coherence for algebras) | YES | `Mathlib/CategoryTheory/Limits/Shapes/Pullback/Equifibered.lean:93` |
| `coequifibered_iff_forall_isLocalizationAway` | YES | `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:266` |
| `Scheme.AffineZariskiSite` + `toOpensFunctor` + `directedCover` | YES | `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:51,85,212` |
| `Hom.normalization` (a *consumer* of `relativeGluingData`) | YES | `Mathlib/AlgebraicGeometry/Normalization.lean:120` |
| `Scheme.GlueData` (classical gluing) | YES | `Mathlib/AlgebraicGeometry/Gluing.lean:90` |

### The smoking gun

`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:240-255` carries
the section header

```
## "Quasi-coherent `𝒪ₓ`-algebras"

A presheaf `F` of rings on `X.AffineZariskiSite` with a structural
morphism `α : 𝒪ₓ ⟶ F` is said to be `Coequifibered` if
`F(D(f)) = F(U)[1/f]` for every open `U` and any section `f : Γ(X, U)`.

Under this condition we can construct a family of gluing data (See
`relativeGluingData`) and glue `F` into a scheme over `X` via
`(relativeGluingData _).glued`.
[...] This is closely related to the notion of quasi-coherent
`𝒪ₓ`-algebras, and we shall link them together once the theory of
quasi-coherent `𝒪ₓ`-algebras are developed.
```

Mathlib has packaged exactly the Stacks 01LL/01LM/01LP construction —
they just haven't *named* it `RelativeSpec` because the qcoh-algebra
theory linking the input shape to "QcohAlgebra" hasn't landed yet. The
already-shipped consumer `Hom.normalization`
(`Mathlib/AlgebraicGeometry/Normalization.lean:120`) shows the exact
usage pattern:

```lean
def normalizationGlueData := relativeGluingData f.coequifibered_normalizationDiagramMap
def normalization : Scheme := f.normalizationGlueData.glued
```

This is the canonical relative-Spec template the project should
consume verbatim.

## Decisions identified

### Decision 1: choice of body for `RelativeSpec`

- **Mathlib idiom**: `(AffineZariskiSite.relativeGluingData H).glued` where
  `H : (affineUnit 𝒜).Coequifibered` is the qcoh predicate after
  projecting `𝒜 : X.QcohAlgebra` to the (presheaf-on-`AffineZariskiSite`,
  natural-transformation) form Mathlib accepts. Cite:
  `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:293-299` +
  `Mathlib/AlgebraicGeometry/RelativeGluing.lean:102` (`.glued`). Why
  Mathlib chose it: the affine-cover construction (Stacks 01LM/01LP)
  is exactly a `Cover.RelativeGluingData` over the canonical directed
  affine open cover `Scheme.AffineZariskiSite.directedCover X`, with
  fibres `Spec(𝒜(U))` and transition isomorphisms induced by
  `IsLocalization.Away`. The locally-directed gluing of
  `RelativeGluing.lean` is the cleaner colimit-shaped restatement of
  the classical `Scheme.GlueData` (avoids the cocycle bookkeeping).

- **Project's current path**: `RelativeSpec 𝒜 := X` (the base scheme
  itself). The `_𝒜` argument is silently discarded.

- **Gap**: divergent-and-wrong. The carrier is wrong — it does not
  depend on `𝒜` at all, so every downstream theorem that quantifies
  over the relative spectrum is trivialized.

- **Cost of divergence**: total. Auditor verdict iter-177 stands —
  Picard, line-bundle moduli, and the rest of the positive-genus arm
  cannot build a substantive `PicardFunctor` against a `RelativeSpec`
  that ignores its argument. Refactor obligation, not stylistic
  preference.

- **Verdict**: **ALIGN_WITH_MATHLIB** (critical, must-fix-this-iter).

### Decision 2: shape of `QcohAlgebra` carrier (does it currently support the Mathlib construction?)

- **Mathlib idiom**: the Mathlib `relativeGluingData` input is a
  *triple* `(F, α, H)`:
  1. `F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat`,
  2. `α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F` (the algebra unit
     restricted to the affine Zariski site),
  3. `H : α.Coequifibered` (the qcoh predicate, equivalent to "every
     restriction-to-basic-open is `IsLocalization.Away`").

  The project's `QcohAlgebra` (`RelativeSpec.lean:131-136`) currently
  packages `(sheaf : TopCat.Sheaf CommRingCat X, unit : X.sheaf ⟶ sheaf)` —
  exactly the data needed for parts (1) + (2) once restricted via
  `(toOpensFunctor X).op ⋙ -`. **Part (3), the `Coequifibered`
  predicate, is MISSING** — this is the quasi-coherence overlay that
  `analogies/qcohalgebra-structure.md` flagged as iter-175+ work.

  However the upstream-gap concern in that analogy was specifically
  about `SheafOfModules.IsQuasicoherent` (which would need the
  sheafified-tensor infrastructure). **`NatTrans.Coequifibered` is a
  weaker, equation-shaped predicate that DOES NOT need sheafified-tensor
  machinery** — it just asserts each restriction-to-basic-open is an
  `IsLocalization.Away`. This is provable directly from a sheaf-of-rings
  structure (`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:266`
  is the equivalence with `IsLocalization.Away`).

- **Project's current path**: Encoding I without the `coequifibered`
  field. The `iter-175+` plan in `RelativeSpec.lean:122-129` mentions
  *"add a third field `isQcoh : Prop`"* but the file has not yet been
  updated.

- **Gap**: divergent-with-cost. The carrier IS upgradable to support
  the Mathlib construction with a single new field; the present
  carrier alone is not.

- **Cost of divergence**: one missing structure field. Until added,
  `relativeGluingData` cannot fire and the body of `RelativeSpec`
  cannot be the Mathlib value. ~10 LOC fix.

- **Verdict**: **ALIGN_WITH_MATHLIB** — add the `Coequifibered` field
  (in the `IsLocalization.Away` equivalent form via
  `coequifibered_iff_forall_isLocalizationAway` for readability).

### Decision 3: choice of body for `structureMorphism`

- **Mathlib idiom**: `(AffineZariskiSite.relativeGluingData H).toBase`.
  Cite: `Mathlib/AlgebraicGeometry/RelativeGluing.lean:114`. The
  structure morphism is constructed as the colimit descent of the
  natural transformation `Xᵢ → Uᵢ` along the directed affine cover.

- **Project's current path**: `structureMorphism _ := 𝟙 X`. Wrong:
  identity has nothing to do with the algebra unit, and downstream
  theorems mentioning `pullback g (structureMorphism _𝒜)` collapse to
  `pullback g (𝟙 X) ≅ T`, which is the *wrong* substantive object.

- **Gap**: divergent-and-wrong (same as Decision 1).

- **Verdict**: **ALIGN_WITH_MATHLIB** (critical, must-fix-this-iter).

### Decision 4: shape of the four downstream theorems

- **Mathlib idiom**: each one is a *direct consequence* of the
  Mathlib-provided lemmas on `RelativeGluingData`:

  - `UniversalProperty` (currently `IsAffineHom`): use
    `RelativeGluingData.cover` + the fact that each restriction is
    `Spec(F U) → U`, which is affine; then the
    `HasAffineProperty.iff_of_iSup_eq_top` criterion
    (`Mathlib/AlgebraicGeometry/Morphisms/Affine.lean:146`) closes
    affineness. Once the project elevates `UniversalProperty` to a
    `Functor.RepresentableBy` statement, the building block is
    `RelativeGluingData.isPullback_natTrans_ι_toBase`
    (`Mathlib/AlgebraicGeometry/RelativeGluing.lean:172`), which
    matches the Yoneda statement of Stacks 01LQ on each affine.

  - `affine_base_iff` (Spec R case): when `X = Spec R`,
    `Scheme.AffineZariskiSite` has a top element `⊤ = X` and the
    glued scheme reduces to `Spec(F ⊤) = Spec(Γ(X, 𝒜))`. The
    `isColimit_cocone` lemma at
    `SmallAffineZariski.lean:343` is the affine-base instance of
    exactly this argument (with `α = 𝟙`); the project's
    affine-base reduction is the same proof with a non-trivial `F`.

  - `base_change`: pullback the qcoh algebra to `T` (via the
    sheaf pullback adjunction `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:151`
    upgraded to sheaves of CommRings), use that `IsLocalization.Away`
    is stable under base change of rings, conclude the resulting
    natural transformation is again `Coequifibered`, then use Mathlib's
    universal property of the gluing.

  - `functor` (object-level): `fun 𝒜 => Over.mk (structureMorphism 𝒜)`
    — already correct in shape.

- **Project's current path**: each of the three theorems hides behind
  the trivial body. After the carrier swap, each theorem is provable
  by referencing the Mathlib lemma.

- **Verdict**: **ALIGN_WITH_MATHLIB** — replace the trivializing
  proofs with the Mathlib-builder-based proofs. (For `UniversalProperty`
  the iter-178+ refinement to `Functor.RepresentableBy` is unblocked
  by the carrier swap because the per-affine Yoneda fact is now
  available as a Mathlib lemma.)

## Recommendation

**Adopt Mathlib's `relativeGluingData` as the carrier verbatim.**
This is not a refactor; it is a *replacement*. The placeholder body
`RelativeSpec := X` is destroyed and the value is given by the
Mathlib builder.

Concrete refactor for `AlgebraicJacobian/Picard/RelativeSpec.lean`:

```lean
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.RelativeGluing

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent sheaf of O_X-algebras: sheaf of CommRings, an O_X-algebra
unit, and the quasi-coherence overlay in Stacks-01LL form. -/
structure QcohAlgebra (X : Scheme.{u}) where
  sheaf : TopCat.Sheaf CommRingCat.{u} X.toPresheafedSpace
  unit : X.sheaf ⟶ sheaf
  /-- Stacks 01LL: on every affine open U, restriction to a basic open
  D(f) ⊆ U is the localization-away-from-f. -/
  coequifibered : NatTrans.Coequifibered (X := X.AffineZariskiSite)
    (F := (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf)
    (G := (AffineZariskiSite.toOpensFunctor X).op ⋙ sheaf.val)
    (whiskerLeft (AffineZariskiSite.toOpensFunctor X).op unit.val)

namespace QcohAlgebra

/-- The affine restriction of a qcoh algebra: its sheaf restricted to
the affine Zariski site, viewed as a presheaf to CommRingCat. -/
abbrev affinePresheaf (𝒜 : X.QcohAlgebra) :
    X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineZariskiSite.toOpensFunctor X).op ⋙ 𝒜.sheaf.val

/-- The affine restriction of the unit. -/
abbrev affineUnit (𝒜 : X.QcohAlgebra) :
    (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ 𝒜.affinePresheaf :=
  whiskerLeft (AffineZariskiSite.toOpensFunctor X).op 𝒜.unit.val

end QcohAlgebra

/-- The relative spectrum scheme. Built from Mathlib's
`AffineZariskiSite.relativeGluingData`. -/
noncomputable def RelativeSpec (𝒜 : X.QcohAlgebra) : Scheme.{u} :=
  (AffineZariskiSite.relativeGluingData 𝒜.coequifibered).glued

/-- The structure morphism Spec_X(𝒜) → X. -/
noncomputable def RelativeSpec.structureMorphism (𝒜 : X.QcohAlgebra) :
    X.RelativeSpec 𝒜 ⟶ X :=
  (AffineZariskiSite.relativeGluingData 𝒜.coequifibered).toBase
```

Each downstream theorem follows from the corresponding Mathlib lemma:

- `UniversalProperty` (affine form): use the open cover
  `RelativeGluingData.cover`. Each fiber is `Spec(F U)` (affine by
  `AlgebraicGeometry.AffineScheme`), each restriction is
  `Spec(α.app (op U))` (an `IsAffineHom` between affines). Combine via
  `HasAffineProperty.iff_of_iSup_eq_top` (`Mathlib/AlgebraicGeometry/Morphisms/Affine.lean:146`).

- `affine_base_iff`: on `Spec R`, `X.AffineZariskiSite` has a top
  element. The Mathlib `isColimitCocone` proof in
  `SmallAffineZariski.lean:343-366` shows the structure: the gluing
  collapses to `Spec(F ⊤) = Spec(𝒜.sheaf.val.obj (op ⊤))`. Adapt to
  non-trivial `F`.

- `base_change`: pullback of qcoh algebras (via `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` upgraded
  to CommRings) preserves `Coequifibered` (because `IsLocalization.Away`
  is preserved by ring base change — `Mathlib/RingTheory/Localization/BaseChange.lean`).
  Then the universal property of the gluing gives the iso
  `T ×_X RelativeSpec(𝒜) ≅ RelativeSpec(g^* 𝒜)`.

- `functor`: keep as-is, body is now substantive because
  `structureMorphism` is.

## Pivot plan (iter-178 → iter-179+)

**Block A — carrier upgrade (~25 LOC, iter-178 if a body-skeleton lane
can land it, else iter-179)**:
1. Add `Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski` + `Mathlib.AlgebraicGeometry.RelativeGluing` imports (already brought in via `import Mathlib`).
2. Add `affinePresheaf` and `affineUnit` helpers (~10 LOC).
3. Add `coequifibered` field to `QcohAlgebra` (~5 LOC) — definition uses Mathlib's `NatTrans.Coequifibered`, NO new project axioms.
4. Replace `RelativeSpec` body with `(relativeGluingData _).glued` (~3 LOC).
5. Replace `structureMorphism` body with `.toBase` (~3 LOC).

**Block B — downstream theorem rewrites (~60 LOC, iter-179)**:
6. `UniversalProperty (affine form)`: ~15 LOC via `HasAffineProperty.iff_of_iSup_eq_top`.
7. `affine_base_iff`: ~25 LOC adapting `SmallAffineZariski.isColimitCocone`.
8. `base_change`: ~30 LOC using `Coequifibered` stability under pullback.

**Block C — upgrade `UniversalProperty` to `Functor.RepresentableBy` (~40 LOC, iter-180+)**:
9. Build the Yoneda functor (the `O_X`-algebra Hom functor on schemes-over-`X`).
10. Use `RelativeGluingData.isPullback_natTrans_ι_toBase` to prove the Yoneda
    bijection on the affine cover.
11. Glue via Mathlib's locally-directed cover hom-extension.

## LOC estimate

- **Minimum substantive landing** (Blocks A + B, removing the
  placeholder for good): **~85 LOC** net (about half of the current
  file is the existing structure header + docstrings, which mostly
  carry over).
- **Full alignment including representability** (A + B + C): **~125 LOC**.

This is *materially smaller* than the 680-LOC estimate from
`analogies/qcohalgebra-structure.md` because Mathlib has already done
the gluing — the project does not need to invoke `Scheme.GlueData`
explicitly, nor build a sheafified-tensor monoidal structure.

## Caveat on the `Coequifibered` field

The `Coequifibered` predicate references natural transformations on
`X.AffineZariskiSite`, not on all of `X.Opens`. This is *strictly weaker*
than the full sheaf-of-modules quasi-coherence predicate
`SheafOfModules.IsQuasicoherent`. For a sheaf of CommRings on `X.Opens`,
the two are equivalent under the dense-subsite equivalence
`Scheme.AffineZariskiSite.sheafEquiv`
(`SmallAffineZariski.lean:203`), so no information is lost. The project
should `Coequifibered`-ize because that is the Mathlib idiom for the
input to `relativeGluingData`; the sheaf-of-modules predicate remains
the *long-term* form (Encoding II) but is not on the critical path
since `Coequifibered` already produces the correct geometric object.

## Hard NO

- **(a) `QcohAlgebra` carrier + `Scheme.GlueData`**: would duplicate
  Mathlib's `Cover.RelativeGluingData` (which is the colimit-shaped,
  locally-directed restatement of `Scheme.GlueData` *specifically* for
  this case). Reject — parallel API.

- **(b) `Spec` of a relative graded ring**: only applies to *graded*
  algebras (`Proj`-construction, Stacks 01M3). The project needs the
  general `Spec_X` case for ungraded `𝒜`. Reject — narrower than the
  blueprint requires.

- **(c) Functor-of-points**: the *output* shape (`UniversalProperty`)
  is functor-of-points. But the *carrier* should be a concrete scheme,
  not a representable functor's section, because every other piece of
  the file (open cover, base change, affine-base reduction) wants a
  concrete scheme. Reject as carrier; use as the *type* of the
  upgraded `UniversalProperty`.
