# Analogy: affine-basis-to-X sheaf-condition bridge for `relativeDifferentialsPresheaf`

## Slug
affine-basis-sheaf-bridge

## Iteration
114

## Question
For an underlying type-valued presheaf `F : Opens X^op ⥤ Type u` on a scheme `X`,
does Mathlib b80f227 expose an off-the-shelf API that converts "`F` satisfies a
sheaf condition on the affine opens of `X` (or on a base of basic opens of each
affine chart)" into "`F` is a sheaf in the Zariski topology on `X`"? Is
`Scheme.PresheafOfModules`-as-sheaf the right *predicate* for the iter-113
unique-gluing route, or should the project shift to a different infrastructure
(`SheafOfModules.{u}` / `PresheafOfModules.sheafification` /
`Scheme.OpenCover`-indexed gluing) for the sheaf-condition closure of `Ω_{X/S}`?

## Project artifact(s)
- `AlgebraicJacobian/Differentials.lean:127–175` — `relativeDifferentialsPresheaf_isSheafUniqueGluing_type` (load-bearing sorry).
- `AlgebraicJacobian/Differentials.lean:59–62` — `relativeDifferentialsPresheaf` definition via `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`.
- `AlgebraicJacobian/Differentials.lean:209–284` — helper #1 / #2 / main theorem; framework-only after iter-113 pivot.
- `blueprint/src/chapters/Differentials.tex:28–53` — Route (a) prose with explicit `[gap]` callout at L51.

## Decisions identified

### Decision 1: Is there an off-the-shelf "sheaf-on-basis ⇒ sheaf" theorem in Mathlib b80f227?

- **Mathlib idiom (closest found)**:
  - **None at the predicate level for `Opens X`-valued presheaves.** The search located neither
    `TopCat.SheafOnBasis`, `TopCat.Presheaf.isSheaf_of_isSheaf_on_basis`,
    `TopCat.Presheaf.IsSheafOnOpens.toSheaf`, nor a
    `Scheme.PresheafOfModules.IsSheaf.{ofAffineCover, ofAffineBasis, ofOpenCover}` /
    `Scheme.AffineOpenCover.isSheaf` declaration. The names do not exist in Mathlib.
  - The closest analogues are:
    - `TopCat.Sheaf.restrictHomEquivHom` (`Mathlib/Topology/Sheaves/SheafCondition/Sites.lean:231`) —
      morphisms from a presheaf to a sheaf are equivalent to their restrictions to a basis. This is
      for hom-sets, not for the sheaf predicate on the presheaf.
    - `TopCat.Opens.coverDense_iff_isBasis` (`Mathlib/Topology/Sheaves/SheafCondition/Sites.lean:126`) /
      `TopCat.Opens.coverDense_inducedFunctor` (line 135) — a basis-indexed functor into `Opens X` is
      cover-dense in the Grothendieck topology.
    - `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`
      (`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:784`) — equivalence
      `Sheaf J A ≌ Sheaf K A` between *sheaf categories* on a dense subsite. This gives
      "every sheaf on the basis extends uniquely to a sheaf on the full topology", but its action
      on a presheaf is via sheafification — i.e. it gives `F^a`, not `F`, on non-basis opens.
    - `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`
      (`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:~250`) — packages a basis-restricted
      morphism into a presheaf morphism *when the codomain is already a sheaf*. Not applicable to
      lifting a basis-restricted sheaf condition into a global one.
- **Project's path**: `relativeDifferentialsPresheaf_isSheafUniqueGluing_type` (sorry-bodied) attempts
  to prove the type-level sheaf condition directly via `IsSheafUniqueGluing`. The body intends to use
  the universal derivation `d : O_X → Ω_{X/S}` to push compatible Ω-families to compatible
  O_X-families, glue via `X.ringCatSheaf`, then lift back via the `KaehlerDifferential` universal
  property.
- **Gap**: **divergent-and-wrong** for the literal recipe at L148–167 of `Differentials.lean`:
  the recipe's Step (1) "project compatible Ω-families to compatible O_X-families via `d`" is not a
  well-defined operation — `d` is a multilinear map of modules, not an inverse-able sectionwise
  function, so you can't go from `sf i ∈ Ω_{X/S}(U i)` to a corresponding `Section_i ∈ O_X(U i)`
  in a way that recovers `sf i` after the lift. The classical proof goes through *Kähler
  differentials' base-change compatibility* (commutes-with-localisation), not through the universal
  derivation directly.
- **Cost of divergence**: the iter-113 unique-gluing pivot is a framework reformulation but not a
  mathematical advance. Closing the sorry as stated would require either rewriting the recipe to
  use base-change identification (Step 2 of the old Route (a) recipe) or accepting that the genuine
  gap is the basis-to-X bridge with no Mathlib lemma.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — the bridge "sheaf-on-affine-basis-of-X ⇒ sheaf on X"
  is genuinely missing in Mathlib b80f227. The project must build the descent step.

### Decision 2: Is `IsSheafUniqueGluing` (the iter-113 pivot) the right framework reformulation?

- **Mathlib idiom**: four equivalent sheaf-condition predicates exist:
  - `TopCat.Presheaf.IsSheaf` (canonical, Grothendieck-topology form).
  - `TopCat.Presheaf.IsSheafEqualizerProducts` (`Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts`).
  - `TopCat.Presheaf.IsSheafPairwiseIntersections` (`Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections`).
  - `TopCat.Presheaf.IsSheafOpensLeCover` (`Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover`).
  - `TopCat.Presheaf.IsSheafUniqueGluing` (`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`).

  All linked by named equivalences (e.g. `isSheaf_iff_isSheafUniqueGluing_types`,
  `isSheaf_iff_isSheafOpensLeCover`, `IsSheaf.isSheafPairwiseIntersections`).
- **Project's path**: `IsSheafUniqueGluing` for Type-valued presheaves. Reasonable; the mathematical
  content is identical across all four.
- **Gap**: identical/equivalent.
- **Verdict**: **PROCEED** on the choice of reformulation — `IsSheafUniqueGluing` is fine.

### Decision 3: Should the project keep `relativeDifferentialsPresheaf : X.PresheafOfModules` + prove-IsSheaf, or pivot to `PresheafOfModules.sheafification`?

- **Mathlib idiom**: `PresheafOfModules.sheafification`
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:54`) provides a functor
  `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R` (when the comparison `α : R₀ → R.val` is
  locally bijective; the identity-on-the-structure-sheaf case `α = 𝟙 X.ringCatSheaf.obj` gives the
  vanilla sheafification). The adjunction `sheafificationAdjunction` and counit-iso instance are
  provided.
- **Project's path**: `relativeDifferentials f : X.Modules := ⟨relativeDifferentialsPresheaf f, IsSheaf-proof⟩` — i.e., bundle a presheaf with a sheaf-condition proof. This mirrors Mathlib's
  `AlgebraicGeometry.tilde` (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean:87`), which builds
  `Spec R.Modules` as `⟨moduleStructurePresheaf, isSheaf-via-forget-and-subsheafToTypes⟩`.
- **Gap**: divergent-equivalent. The two routes are categorically equivalent — sheafification of a
  presheaf that *is* a sheaf returns the same object (up to unit-iso). But:
  - The sheafification route does NOT bypass the mathematical content. The sheafification computes
    sections on non-basis opens by gluing the basis sections (limit over a dense subsite). To use
    `Ω_{X/S}(U) ≅ Ω_{B/A}` downstream, the project still needs the affine-restriction
    identification (Step 2 of Route (a)) AND proof that the unit `F → F^a` is iso on affine opens.
    The latter is the *same* sheaf-on-basis fact in different clothing.
  - The Mathlib `tilde` pattern (subsheafToTypes via locally-fraction predicate + forget reduction)
    is the canonical idiom; it works for `Spec R` because sections are locally fractions and the
    `LocalPredicate` framework converts that into a sheaf for free. For `relativeDifferentialsPresheaf`
    on an arbitrary scheme `X`, no analogous LocalPredicate is currently formalized — though one
    could in principle define it (sections of `Ω_{X/S}` on `U` as functions `U → ⨆_x Ω_{X/S, x}`
    locally of the form `germ_x(b•dc)`).
- **Verdict**: **DIVERGE_INTENTIONALLY** — keep the explicit IsSheaf-proof pattern (matches `tilde`),
  but recognize that switching to `PresheafOfModules.sheafification` is a *valid alternative
  framing* that converts the obligation from "prove F is a sheaf" to "prove sheafification-unit is
  iso on affine opens", which is the same mathematical work under a different name.

### Decision 4: Does `AlgebraicGeometry.tilde` + Mathlib gluing constitute an off-the-shelf Route (d)?

- **Mathlib idiom**: `AlgebraicGeometry.tilde : ModuleCat R ⥤ (Spec R).Modules`
  (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean:87`) produces a quasicoherent sheaf of
  `O_{Spec R}`-modules on a single affine. There is **no off-the-shelf `Tilde.fromAffineCover`,
  `Tilde.glue`, or `glueAffineSheaves`** declaration that combines `tilde`-pieces on an affine
  cover of `X` into a sheaf on `X`.
- The neighborhood: `IsQuasicoherent.of_coversTop`
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:377`) shows quasicoherence is
  local for a `SheafOfModules`. `QuasicoherentData.bind` (line 360) glues quasicoherent *data*.
  These operate on a SheafOfModules *that already exists* — they do not construct one from
  affine pieces.
- `Scheme.GlueData.oneHypercover` (`Mathlib/AlgebraicGeometry/GluingOneHypercover.lean`) +
  `Functor.IsOneHypercoverDense` infrastructure (`Mathlib/CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean`)
  provide a categorical equivalence `Sheaf K A ≌ Sheaf J A` for 1-hypercover-dense subsites. In
  principle, an affine cover of `X` defines a 1-hypercover, and the affine-open subsite gives a
  1-hypercover-dense subsite. So `Sheaf (affine subsite) X.Modules ≌ Sheaf (full topology) X.Modules`
  holds at the level of categories. But constructing the affine-side `Sheaf` object — a presheaf
  on affines satisfying the affine-restricted sheaf condition — still requires a per-affine sheaf
  condition argument that has no Mathlib closure for Kähler differentials.
- **Project's path**: Route (a) — prove sheaf condition directly via `IsSheafUniqueGluing`.
- **Gap**: divergent-with-cost. Route (d) (tilde + cover gluing) sketches as cleaner but has no
  closed Mathlib path: tilde-gluing-on-cover requires the project to build the gluing morphism
  data (overlap-isos satisfying cocycle conditions), which is a different non-trivial chunk.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — Route (d) is not off-the-shelf. The Mathlib affine-cover-gluing
  for `Scheme.Modules` is genuinely missing.

## Recommendation

**Top-level verdict: PROCEED with iter-115+ closure on the current Route (a)**, with two concrete
corrections:

1. **Rewrite the recipe in `relativeDifferentialsPresheaf_isSheafUniqueGluing_type` docstring**
   (Differentials.lean:148–167). The current Step (1) "project Ω-families to O_X-families via d" is
   not well-defined as written. Replace with the classical recipe:
   - On the **affine basis** (basic opens of each affine chart `V_α = Spec B_α ⊂ X` over
     `U_α = Spec A_α ⊂ S`): identify `relativeDifferentialsPresheaf f` on `D(g) ⊂ V_α` with
     `Ω_{B_α[1/g]/A_α} ≅ Ω_{B_α/A_α} ⊗_{B_α} B_α[1/g]` via
     `KaehlerDifferential.isLocalizedModule_map` [verified]. This identifies the affine-restricted
     presheaf with `tilde Ω_{B_α/A_α}`, which is a sheaf-on-`V_α` by `AlgebraicGeometry.tilde`
     [verified].
   - **Globalisation**: refine an arbitrary open cover by intersecting with the affine basis, lift
     the `OpensLeCover` cone condition for the refined cover from the affine-restricted sheaf
     property, and conclude via cofinality of the refinement against `isSheaf_iff_isSheafOpensLeCover`
     [verified].

2. **Acknowledge in the blueprint** (Differentials.tex:51 `[gap]`) that the basis-to-X bridge is
   genuinely missing from Mathlib; the explicit cofinality argument is the project's
   responsibility. The iter-113 unique-gluing reformulation does not eliminate this gap — it just
   relocates it from `IsSheafOpensLeCover` to `IsSheafUniqueGluing`. Either form requires
   constructing the descent step from affine basis to all opens by hand.

**Alternative considered and rejected**: switch to `PresheafOfModules.sheafification`. This is
categorically valid but does *not* bypass the affine-restriction identification — the unit
`F → F^a` is iso on affine opens iff `F` is a sheaf there, which is the same Step 2 obligation.
The sheafification route also slightly degrades the directness of the affine-section
identification `Ω_{X/S}(V) ≅ Ω_{B/A}` (now derived through a colimit/limit comparison rather
than holding by `rfl`).

**Alternative considered and rejected**: switch to a tilde-glue-on-affine-cover construction
(Route (b)/Route (d)). Cleaner in principle but requires the project to build the gluing-of-modules
infrastructure, which is *also* missing from Mathlib. Net workload is comparable to Route (a)
with the corrected recipe.

The strategic-critic-iter114 audit was therefore correct: the iter-113 pivot does not close a
mathematical gap, and the blueprint's `[gap]` callout at Differentials.tex:51 stands. The Mathlib
analogist confirms: no off-the-shelf Mathlib bridge exists. The project must construct the descent
step.
