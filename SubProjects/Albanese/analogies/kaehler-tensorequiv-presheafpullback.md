# Analogy: sheaf-level promotion of `KaehlerDifferential.tensorKaehlerEquiv`

## Slug

kaehler-tensorequiv-presheafpullback-iter137

## Iteration

137

## Question

How should the algebra-side base-change-of-Ω equivalence
`KaehlerDifferential.tensorKaehlerEquiv`
(`Mathlib.RingTheory.Kaehler.TensorProduct`) be promoted to a sheaf-level
natural iso of presheaves of modules — specifically to close

```
Scheme.relativeDifferentialsPresheaf (fst G G).left ≅
  (PresheafOfModules.pullback
      (Scheme.Hom.toRingCatSheafHom (snd G G).left).hom).obj
    (Scheme.relativeDifferentialsPresheaf G.hom)
```

at `AlgebraicJacobian/Cotangent/GrpObj.lean:480–488` (piece (i.b) Step 2,
load-bearing for `mulRight_globalises_cotangent`)?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:480–488` —
  `relativeDifferentialsPresheaf_basechange_along_proj_two` (iter-135
  honest-scaffold sorry; iter-137 prover target).
- `AlgebraicJacobian/Differentials.lean:51–66` —
  `Scheme.relativeDifferentialsPresheaf` + `_obj_kaehler` chart chart-level
  rfl-identification.
- `AlgebraicJacobian/Cotangent/GrpObj.lean:508–551` —
  `relativeDifferentialsPresheaf_restrict_along_identity_section` (Step 3,
  iter-136 closed; consumes the Step 2 signature shape).
- `blueprint/src/chapters/RigidityKbar.tex:423–481` —
  `lem:GrpObj_omega_basechange_proj` (informal proof prose + Mathlib-name
  inventory).
- `analogies/mulright-globalises-cotangent.md` Decision 2 — iter-133
  identified the gap and gave a 150–300 LOC envelope.
- `analogies/phi-compatibility-morphisms.md` — iter-135 verdict on the
  φ-compatibility morphism (canonical Mathlib shape is
  `(Scheme.Hom.toRingCatSheafHom _).hom`); the iter-136 Step 3 closure
  consumed this verdict.

## Signature audit (iter-135 scaffold sign-off)

Blueprint claim (`RigidityKbar.tex:464–468`): "view `G ×_k G` as a
`G`-scheme via `pr_1`. Then `Ω_{(G ×_k G)/G} ≅ pr_2^* Ω_{G/k}` as
presheaves of modules on `G ×_k G`."

The Lean signature:

- LHS `relativeDifferentialsPresheaf (fst G G).left` — uses `pr_1.left =
  (fst G G).left : (G ⊗ G).left ⟶ G.left` as the source morphism for
  relative differentials. Both `(fst G G).left` (and its target `G.left`)
  inhabit `Scheme.{u}`, so the LHS lives in `(G ⊗ G).left.PresheafOfModules`
  and exactly realises "Ω of `G ⊗ G` viewed as a `G`-scheme via `pr_1`". ✓
- RHS `(PresheafOfModules.pullback (toRingCatSheafHom (snd G G).left).hom)
  .obj (relativeDifferentialsPresheaf G.hom)` — starts from
  `relativeDifferentialsPresheaf G.hom : G.left.PresheafOfModules`
  (the cotangent of `G/Spec k`), pulls back along
  `pr_2.left = (snd G G).left : (G ⊗ G).left ⟶ G.left`. Lands in
  `(G ⊗ G).left.PresheafOfModules`. ✓
- φ shape `(Scheme.Hom.toRingCatSheafHom _).hom` is the canonical Mathlib
  φ for `PresheafOfModules.pullback` per iter-135 verdict
  (`Mathlib.AlgebraicGeometry.Modules.Presheaf:42–45`). ✓
- Used downstream by Step 3 (`_restrict_along_identity_section`, lines
  508–551, iter-136 closed) exactly in this form. Refactoring the
  signature would invalidate Step 3.

**Verdict: signature is correct — proceed.** The two sides agree on the
target presheaf, the asymmetry in `fst` vs `snd` correctly encodes the
blueprint asymmetry (LHS structure morphism vs RHS pullback morphism),
and Step 3's iter-136 closure already consumes this exact shape.

## Decisions identified

### Decision 1: Mathlib idiom for sheaf-level base-change-of-Ω

- **Mathlib idiom**: NONE PACKAGED. Search of Mathlib via
  `lean_leansearch` ("PresheafOfModules pullback differentials",
  "differentials tensor product presheaf") and `lean_loogle`
  (`PresheafOfModules.pullback _ ≅ _`) yields only
  `PresheafOfModules.pullbackId` and `PresheafOfModules.pullbackComp`,
  not a base-change-of-Ω lemma. The chart-level
  `KaehlerDifferential.tensorKaehlerEquiv`
  (`Mathlib/RingTheory/Kaehler/TensorProduct.lean:249`,
  signature `B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S]` under `Algebra.IsPushout R S A B`)
  is the closest pre-built artefact, and it has no sheaf-level
  promotion in Mathlib. Per `analogies/mulright-globalises-cotangent.md`
  Decision 2, Mathlib has no scheme-level relative cotangent **sheaf**
  at all — only the chart-level Kähler module and the project's
  home-grown `Scheme.relativeDifferentialsPresheaf` (built on
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean:189`).

- **Project's path**: build the iso by hand. Chain
  `KaehlerDifferential.tensorKaehlerEquiv` (chart-level value identity)
  with `PresheafOfModules.isoMk`
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf.lean:118`, the
  Mathlib idiom for assembling a chart-wise `app + naturality` pair
  into a `PresheafOfModules` iso) to deliver the natural iso.

- **Gap**: NEEDS_MATHLIB_GAP_FILL — divergence is mandatory, Mathlib
  has the gap.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**, confirmed from iter-133. The
  project is correctly building the missing infrastructure.

### Decision 2: `Algebra.IsPushout`-from-affine-product source

- **Mathlib idiom**: NO ONE-SHOT LEMMA. The chain available is:
  - `CommRingCat.isPushout_iff_isPushout`
    (`Mathlib/Algebra/Category/Ring/Constructions.lean:133`): bridges
    `CategoryTheory.IsPushout` in `CommRingCat` with `Algebra.IsPushout`.
  - `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`
    (`Mathlib/AlgebraicGeometry/Pullbacks.lean:771`): gives a pullback
    in `Scheme` from a pushout in `CommRingCat`.
  - `AlgebraicGeometry.pullbackSpecIso`
    (`Mathlib/AlgebraicGeometry/Pullbacks.lean:703`):
    `Spec (S ⊗[R] T) ≅ Spec S ×_{Spec R} Spec T`.
  These give the chart-level `Algebra.IsPushout k Γ(G,V_1) Γ(G,V_2)
  Γ(G⊗G, W)` when `V_1, V_2` are affine charts of `G` over `Spec k` and
  `W = V_1 ×_{Spec k} V_2` is the affine chart of `G ⊗ G` cut out from
  them. But this only works on affine subcovers — not on the whole
  presheaf — and is not packaged.

- **Project's path**: must build the `Algebra.IsPushout` chart-level
  lemma by hand from the universal property of binary products in
  `Over (Spec k)`. Envelope: ~80–150 LOC if the affine-chart
  combinatorics can be discharged uniformly via `pullbackSpecIso`;
  more if affine-cover bookkeeping bleeds into the closure.

- **Gap**: NEEDS_MATHLIB_GAP_FILL — the chart-level `Algebra.IsPushout`
  helper does not exist and must be built.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**.

### Decision 3: Naturality assembly idiom

- **Mathlib idiom**: `PresheafOfModules.isoMk`
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf.lean:118`):
  ```
  def isoMk (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
      (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
        M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y).hom =
          (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂
  ```
  The auto-generated simp lemmas `isoMk_hom_app`, `isoMk_inv_app` make
  the constructed iso amenable to downstream `simp`.

- **Project's path**: use `isoMk`. For each open `V ⊆ (G ⊗ G).left`, the
  `app V` component is the composition

  1. `relativeDifferentialsPresheaf_obj_kaehler` (`Differentials.lean:60`)
     identifies LHS sections over `V` as `Ω[Γ((G⊗G).left, V) ⁄
     ((fst G G).left⁻¹ O_{G.left})(V)]`.
  2. For affine `V`, `tensorKaehlerEquiv` (with chart-level
     `Algebra.IsPushout`) gives a `Γ((G⊗G).left, V)`-linear iso
     `Γ((G⊗G).left, V) ⊗_{Γ(G.left, pr_2(V))} Ω[Γ(G.left, pr_2(V)) ⁄ k]
       ≃ Ω[Γ((G⊗G).left, V) ⁄ Γ(G.left, pr_1(V))]`.
  3. The RHS pulled-back presheaf is, by `PresheafOfModules.pullback`'s
     left-adjoint definition, the universal `Γ((G⊗G).left, V)`-module
     receiving `Ω[Γ(G.left, pr_2(V)) ⁄ k]` after restricting scalars
     along `(toRingCatSheafHom pr_2.left).hom.app V`. For affine V,
     this is exactly the tensor product on the LHS of step 2.
  - For non-affine V, the same identification holds by colimit-of-
    affine-charts naturality (this is where the work concentrates —
    presheaf vs sheaf, see Decision 4).

- **Gap**: ALIGN_WITH_MATHLIB on the iso constructor (use `isoMk`).
  The naturality square then reduces to commutativity of the
  `tensorKaehlerEquiv` value identity with the restriction-of-Kähler-
  modules map, which is `KaehlerDifferential.tensorKaehlerEquiv_tmul_D`
  (`Mathlib/RingTheory/Kaehler/TensorProduct.lean:283`) applied
  pointwise — itself a finite check.

- **Verdict**: **ALIGN_WITH_MATHLIB**. Use `PresheafOfModules.isoMk`,
  not a hand-built `Iso.mk { hom, inv, ... }`.

### Decision 4: `presheaf` vs `sheaf` and the non-affine-V hazard

This is a CRITICAL observation the iter-133 verdict did not surface
explicitly.

- The project's `Scheme.relativeDifferentialsPresheaf f` is built on
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  which over each open `V` (affine or not) gives sections
  `Ω[Γ(X,V) ⁄ (f⁻¹ O_S)(V)]` — i.e. Kähler differentials of an
  algebra map that, for non-affine V, has no particular
  geometric interpretation. The presheaf is `relativeDifferentialsPresheaf`
  not `relativeDifferentialsSheaf`; there is no sheafification.

- For affine V, both sides are computable Kähler modules of the
  natural algebra map (and `tensorKaehlerEquiv` connects them).
  For non-affine V, both sides are still defined (as Kähler modules
  of the corresponding non-affine ring map), but
  `tensorKaehlerEquiv`'s hypothesis (`Algebra.IsPushout`) is not
  generally satisfied on non-affine opens — affine pushout-of-rings
  is a property special to spectra, not arbitrary opens.

- **Implication**: the chart-wise `app` of `isoMk` cannot just be
  "`tensorKaehlerEquiv` of the V-sections"; it must be derived
  from the universal property of Kähler differentials at the
  presheaf level. Concretely: define a `Derivation` of the LHS
  ring map into the RHS module at the presheaf level (one
  derivation per open V, plus naturality across V → W restrictions),
  invoke `KaehlerDifferential.lift` to produce the LHS-to-RHS map,
  and analogously construct the inverse. This is the same strategy
  Mathlib uses to construct `tensorKaehlerEquiv` itself
  (`Kaehler/TensorProduct.lean:225–283`), lifted from a ring to a
  presheaf of rings.

- The alternative (affine-cover-and-glue + sheafification) requires
  the project to either (i) sheafify `relativeDifferentialsPresheaf`
  (which is itself a non-trivial separate piece of infrastructure)
  or (ii) restrict to the affine-open subcategory before applying
  `isoMk`. Both are heavier than the universal-property-at-presheaf
  approach.

- **Gap**: divergent-with-cost. The "chart-wise + glue" mental model
  (which the blueprint at `RigidityKbar.tex:474–478` hints at) is
  not directly executable on `relativeDifferentialsPresheaf` since
  the presheaf hasn't been sheafified.

- **Verdict**: **PROCEED** with the universal-property-at-presheaf
  approach; the chart-affine-cover narrative in the blueprint is
  informal motivation, not the actual Lean proof recipe.

### Decision 5: LOC envelope refinement

- iter-133 envelope: **~150–300 LOC**.
- Findings that pressure the envelope upward:
  - `PresheafOfModules.pullback` has no chart-wise unfolding lemma
    in Mathlib (`pullback` is `(pushforward φ).leftAdjoint`, opaque
    on `.obj` / `.map`). The project will need a ~30–60 LOC helper
    describing `(PresheafOfModules.pullback φ).obj M` on each V
    (likely via the pushforward-adjunction unit/counit unfolding).
  - No `Algebra.IsPushout`-from-affine-product helper (Decision 2):
    ~80–150 LOC chart-level helper.
  - Universal-property-at-presheaf-level naturality (Decision 4):
    ~100–200 LOC for the derivation construction + `lift` invocation +
    `tensorKaehlerEquiv`-style inverse + verification.
  - The `isoMk`-level naturality square: ~30–80 LOC.
- **Revised envelope: ~250–500 LOC** (upper bound widened by ~200 LOC
  vs iter-133). If the project decides to factor out the
  `PresheafOfModules.pullback`-unfolding helper as a stand-alone
  reusable lemma (recommended), the core proof envelope tightens
  to ~150–300 LOC and the helper adds ~50 LOC separately.
- **Verdict**: refined envelope **~250–500 LOC** for the body alone;
  ~300–550 LOC if the pullback-unfolding helper is co-shipped
  in the same file.

## Recommendation

**Verdict on iter-135 scaffold signature: PROCEED — signature is
correct.** The `(fst G G).left` / `(snd G G).left` asymmetry between
LHS structure morphism and RHS pullback morphism correctly encodes
the blueprint claim. The φ-compatibility shape
`(Scheme.Hom.toRingCatSheafHom _).hom` matches iter-135's verdict
and Step 3's iter-136 closure (no convention drift).

**Closure recipe (5-step prose outline)**:

1. **Chart-level `Algebra.IsPushout`** (~80–150 LOC):
   Build a helper lemma — for affine `V_1 ⊆ G.left`, `V_2 ⊆ G.left`
   over a common affine `U ⊆ Spec k`, with `W = V_1 ×_{U} V_2 ⊆
   (G ⊗ G).left` (the affine chart of `G ⊗ G` cut out via
   `pullbackSpecIso`), conclude
   `Algebra.IsPushout Γ(Spec k, U) Γ(G.left, V_1) Γ(G.left, V_2)
     Γ((G ⊗ G).left, W)`.
   Uses `CommRingCat.isPushout_iff_isPushout`
   (Constructions.lean:133), `pullbackSpecIso` (Pullbacks.lean:703),
   `isPullback_SpecMap_of_isPushout` (Pullbacks.lean:771).
   (Stand-alone reusable lemma — file in `Differentials.lean` or
   a new utility section in `Cotangent/GrpObj.lean`.)

2. **`PresheafOfModules.pullback` chart-level unfolding** (~30–60 LOC):
   Build a helper unfolding
   `((PresheafOfModules.pullback φ).obj M).presheaf.obj V ≃
     Γ(R, V) ⊗_{((Opens.map F).op ⋙ S).obj V} M.presheaf.obj (F.op.obj V)`
   for a `PresheafOfModules` `M`. Derive from the left-adjoint definition
   of `pullback` (Pullback.lean:44–45) and the
   `pullbackPushforwardAdjunction` counit/unit
   (Pullback.lean:50). This is the load-bearing infrastructure
   gap caught in Decision 4 + general-purpose agent's finding 4.

3. **Chart-wise derivation `D_V`** (~50–80 LOC):
   For each open `V ⊆ (G ⊗ G).left`, define an `S_1`-derivation
   `D_V : Γ((G ⊗ G).left, V) → (pullback presheaf).obj V`
   where `S_1 = ((Opens.map pr_1.base).op ⋙ G.left.presheaf).obj V`.
   Concretely, `D_V(b)` is the image of `1 ⊗ d_{pr_2(V)}(b)` under
   the `tensorKaehlerEquiv` value identity composed with the
   helper from Step 2.

4. **Apply `KaehlerDifferential.lift`** (~30–50 LOC):
   On each V, the universal property of Kähler differentials gives
   a unique `Γ((G⊗G).left, V)`-linear map
   `Ω[Γ((G⊗G).left, V) ⁄ S_1(V)] → (pullback presheaf).obj V`
   extending `D_V`. By naturality of `lift`, these glue into a
   morphism of presheaves of modules `LHS → RHS`.

5. **Inverse + `PresheafOfModules.isoMk` assembly** (~80–150 LOC):
   Construct the inverse the same way (`tensorKaehlerEquiv` is
   computable from `D_S`, so the inverse `D'_V` is defined by
   sending `b ⊗ ω` to the universal-derivation image). Invoke
   `PresheafOfModules.isoMk` (Presheaf.lean:118) to package the
   chart-wise iso `app V` plus the naturality square (commutativity
   of `lift`-of-derivation with restriction maps, follows from
   `relativeDifferentials'_map_d` at
   `Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean:201`).

**Critical caveat (Decision 4)**: do NOT attempt the "chart-affine-
cover + glue + sheafification" route the blueprint sketches at
`RigidityKbar.tex:474–478`. That route requires sheafifying
`relativeDifferentialsPresheaf` (not currently in the project) and
fights the presheaf-level naturality requirement of `isoMk`. The
universal-property-at-presheaf-level route (steps 3–5 above) is the
direct path.

**Revised LOC envelope: ~250–500 LOC** for the body, plus the
chart-level `Algebra.IsPushout` helper (~80–150 LOC) and the
`PresheafOfModules.pullback`-unfolding helper (~30–60 LOC), each
factorable into stand-alone reusable lemmas. Total piece (i.b)
Step 2 budget: ~360–710 LOC. If the iter-137 prover lane stalls past
the 400-LOC mark, dispatch a follow-up mathlib-analogist call on
sub-strategy choice (universal-property vs. affine-cover-glue).
