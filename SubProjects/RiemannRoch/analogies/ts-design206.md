# Analogy: lighter idiom for the line-bundle group law (vs full MonoidalCategory on all modules)

## Mode
api-alignment

## Slug
ts-design206

## Iteration
206

## Question
To equip the relative Picard functor with its `AddCommGroup` (the group law
"tensor of line bundles") the project is building the FULL symmetric monoidal
category `Scheme.Modules X` (= `sheafification ∘ PresheafOfModules.Monoidal.tensorObj`),
which has bottomed out in the verified-absent `MonoidalClosed (PresheafOfModules R₀)`
(needed for the `whiskerLeft` stability of the localizing morphism property).
Is the full `MonoidalCategory (Scheme.Modules X)` the right Mathlib-aligned shape
for obtaining only the group law on LINE BUNDLES, or does Mathlib have a lighter
idiom that yields the `AddCommGroup` on line-bundle iso-classes WITHOUT the full
monoidal (let alone monoidal-closed) structure on all modules?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean`:113–152 — `Scheme.Modules.tensorObj`
  and the `monoidalCategory : MonoidalCategory X.Modules` instance (`:= sorry`).
- `TensorObjSubstrate.lean`:249–304 — `tensorObj_restrict_iso`, `tensorObj_isLocallyTrivial`,
  `exists_tensorObj_inverse` (the line-bundle cone).
- `TensorObjSubstrate.lean`:399–454 — `isMonoidal_W_of_whiskerLeft` /
  `monoidalCategoryOfIsMonoidalW`: the transport reducing the whole substrate to the
  lone `whiskerLeft` fact `W g → W (F ◁ g)` for ALL `F`.
- `RelPicFunctor.lean`:235–269 — the `addCommGroup` sorry the cone discharges.
- `LineBundlePullback.lean`:115–131 — `IsLocallyTrivial` (the project's self-described
  "stand-in for the missing Mathlib `IsInvertible` predicate") and `OnProduct` carrier.

## Decisions identified

### Decision A: full `MonoidalCategory (Scheme.Modules X)` (→ `MonoidalClosed (PresheafOfModules R₀)`) as the substrate for the group law

- **Mathlib idiom**. Mathlib's Picard group is `CommRing.Pic R := Shrink (Skeleton (SemimoduleCat R))ˣ`
  with the `CommGroup` transported from `Units` of the skeleton `CommMonoid`
  (`Mathlib.RingTheory.PicardGroup`, `CommRing.Pic` def:407, `instCommGroupPic`:412;
  `CategoryTheory.Skeleton.instCommMonoid` from `Mathlib.CategoryTheory.Monoidal.Skeleton`).
  The invertibility carrier is a **Prop predicate** `Module.Invertible R M`
  (PicardGroup.lean:78), NOT a bundled monoidal object. Crucially the monoidal
  category underlying the skeleton there is `ModuleCat R` over a **fixed** ring
  (`ModuleCat.monoidalCategory`, `ModuleCat.MonoidalCategory.symmetricCategory`,
  `Mathlib.Algebra.Category.ModuleCat.Monoidal.{Basic,Symmetric}`) — which needs **no**
  sheafification, localization, or `MonoidalClosed`.
- **Project's path**. Build `MonoidalCategory` on ALL quasi-coherent modules
  `Scheme.Modules X`, whose only remaining gap is `whiskerLeft : W g → W (F ◁ g)`
  for an ARBITRARY presheaf-of-modules `F`, provable (à la Mathlib's
  `GrothendieckTopology.W.whiskerLeft`) only through `MonoidalClosed (PresheafOfModules R₀)`
  — verified absent and a multi-file Mathlib-PR-scale build.
- **Gap**: divergent-with-cost (over-building). The consumer (`RelPicFunctor`
  `addCommGroup`) only ever tensors **line bundles** (`IsLocallyTrivial`, locally free
  rank 1). Line bundles are **flat** — in Mathlib, `Module.Invertible R M` already
  yields `instance : Module.Finite`, `instance : Projective` (PicardGroup.lean:195–196),
  hence flat. For a FLAT `F`, `F ◁ g` is locally bijective whenever `g` is, by ordinary
  exactness: flat ⇒ `lTensor` preserves injectivity
  (`Module.Flat.lTensor_preserves_injective_linearMap`, used in PicardGroup.lean:205–207;
  packaged as `Module.Invertible.lTensor_bijective_iff`, PicardGroup.lean:223–229), and
  `⊗` is always right-exact so it preserves surjectivity. So the ENTIRE reason the project
  needs `MonoidalClosed` — that `whiskerLeft` is false elementwise for non-flat `F` — evaporates
  once the scope is the flat/line-bundle subcategory. The directive's "elementwise exactness
  (needs flatness)" dead-end was a dead-end ONLY because the target was all modules; the
  flatness it "needs" is automatic for line bundles.
- **Cost of divergence**: a verified-absent multi-file `MonoidalClosed (PresheafOfModules R₀)`
  build (the relative internal hom over a varying base ring; the module analogue of
  `Mathlib.CategoryTheory.Sites.Monoidal`), to obtain coherence (pentagon/triangle/hexagon
  + monoidal-closedness) that the group law never consumes — the group axioms on iso-classes
  are *propositions* (`Nonempty (… ≅ …)`), insensitive to coherence.
- **Verdict**: ALIGN_WITH_MATHLIB — abandon the all-modules monoidal-closed route; build the
  group law on the line-bundle (flat) subcategory, where `whiskerLeft`/`tensorObj_restrict_iso`
  reduce to elementary flat-exactness already in Mathlib.

### Decision B: shape of the group-law assembly (`addCommGroup_via_tensorObj` hand-roll vs `Units ∘ Skeleton` + invertibility predicate)

- **Mathlib idiom**. `Pic = Units (Skeleton C)` for a braided monoidal `C`
  (`CommRing.Pic`, `instCommGroupPic`); the iso-class arithmetic is the family
  `Pic.mk_tensor` ([M⊗N]=[M]·[N]), `Pic.mk_dual` ([Mᵛ]=[M]⁻¹), `mul_eq_tensor`,
  `mk_eq_one_iff_free` (PicardGroup.lean:480–496) — i.e. pure *existence-of-iso* facts.
  The invertibility carrier is the Prop `Module.Invertible`, exactly mirrored by the
  project's `IsLocallyTrivial` (LineBundlePullback.lean:106 says so verbatim).
- **Project's path**. `addCommGroup_via_tensorObj` (TensorObjSubstrate.lean:339) and the
  RelPicFunctor L245–264 plan hand-build the quotient `AddCommGroup` from a global monoidal
  category + dual + `QuotientAddGroup` transport — a parallel API to `Units (Skeleton …)`.
- **Gap**: divergent-equivalent, but only because scheme-level Pic is genuinely not in Mathlib
  (PicardGroup.lean TODO:59 explicitly lists "connect to invertible sheaves" as unbuilt). Some
  project construction is unavoidable; the alignment point is to mirror the *shape*: a Prop
  invertibility predicate (`IsLocallyTrivial`, have it) + the group as units/iso-classes of the
  **line-bundle** subcategory, assembled from the four existence-of-iso lemmas
  (assoc/unit/braiding/inverse) — NOT from a coherent monoidal category on all modules.
- **Verdict**: ALIGN_WITH_MATHLIB (shape), NEEDS_MATHLIB_GAP_FILL (scheme Pic itself is absent;
  the project supplies it, lightly).

## Recommendation

Stop building `MonoidalCategory (Scheme.Modules X)` and `MonoidalClosed (PresheafOfModules R₀)`.
The relative Picard group law needs only the *group axioms on iso-classes of line bundles*, which
are propositions (`Nonempty (… ≅ …)`) and therefore require no coherence and no closed structure —
just four existence-of-iso lemmas (associativity, unit `O⊗L≅L`, commutativity, and inverse
`exists_tensorObj_inverse`) plus well-definedness (`tensorObjIsoOfIso`, already have). The single
hard ingredient `tensorObj_restrict_iso` / `whiskerLeft` is genuinely needed even for line bundles
(local triviality alone does NOT give a *global* associator), BUT only for FLAT `F` = line bundles,
where it is elementary exactness (`Module.Flat.lTensor_preserves_injective_linearMap` +
right-exactness), not `MonoidalClosed`. Two realizations, both bypassing the blocker:
(1) **Minimal (recommended first):** prove the four iso lemmas on `OnProduct` directly via the
flat-restricted `whiskerLeft`, then assemble `AddCommGroup` on the quotient — no monoidal category
at all. (2) **Packaged (cleaner long-term):** equip the *full subcategory of line bundles* with a
(symmetric) monoidal structure (flat ⇒ `whiskerLeft` elementwise) and define
`Pic := Units (Skeleton (LineBundles X))`, exactly Mathlib's `CommRing.Pic` idiom transported to
schemes. Either way `IsLocallyTrivial` stays as the `Module.Invertible`-shaped predicate it already
mirrors. Do NOT reopen elementwise exactness for arbitrary `F` (the real dead-end); the move is to
change the *scope* to flat objects so the flatness hypothesis is free.
