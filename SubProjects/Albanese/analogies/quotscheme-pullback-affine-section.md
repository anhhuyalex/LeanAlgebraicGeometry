# Analogy: affine-open section formula for `Scheme.Modules.pullback`

## Mode
api-alignment

## Slug
quotscheme-pullback-affine-section

## Iteration
182

## Question

For a morphism `g : S' ⟶ S` of schemes, `N : S.Modules`, and an
affine open `U : S'.Opens`, is there a Mathlib lemma identifying
`Γ((Scheme.Modules.pullback g).obj N, U)` with
`Γ(S', U) ⊗_{Γ(S, V)} Γ(N, V)` for any compatible affine `V ⊆ S`?

## Project artifact(s)

- `AlgebraicJacobian/Picard/QuotScheme.lean:430–434` —
  `pushforward_pullback_section_eq_pullback_section` (rfl, axiom-clean
  iter-181; closes the *trivial* RHS bridge).
- `AlgebraicJacobian/Picard/QuotScheme.lean:468–499` —
  `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`,
  body `:= sorry`. ~30 LOC of docstring spelling the substantive Mathlib
  gap; transitively taints downstream
  `canonicalBaseChangeMap_app_app_isIso` and `flatBaseChangeCohomology`.
- `AlgebraicJacobian/Picard/QuotScheme.lean:527–549` —
  `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen` (general-base
  helper) waits on the base-side Mayer-Vietoris (gap (b) below).
- `blueprint/src/chapters/Picard_QuotScheme.tex:740–795` —
  `thm:flat_base_change_cohomology` (Stacks 02KH); explicitly identified
  in `Picard_QuotScheme.tex:851–856` as a project-side bridge ("Mathlib
  carries a partial form … the full `R^i f_*` statement is a project-side
  bridge if not present at the pinned commit").

## Mathlib precedents examined

| Mathlib symbol | Location | What it gives | Why it doesn't close the gap |
|---|---|---|---|
| `AlgebraicGeometry.Scheme.Modules.pullback` | `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:167` | `Y.Modules ⥤ X.Modules`, defined as `SheafOfModules.pullback f.toRingCatSheafHom` | abstract; no closed-form `pullback_obj_obj` simp lemma analogous to `pushforward_obj_obj` |
| `SheafOfModules.pullback` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53` | `(pushforward φ).leftAdjoint` | constructed via `partial adjoint`; sections are not exposed |
| `SheafOfModules.pullbackIso` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:105` | `pullback φ ≅ forget S ⋙ PresheafOfModules.pullback ⋙ sheafification` | factors through sheafification, which destroys per-affine-open identification |
| `SheafOfModules.sheafificationCompPullback` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:117` | `sheafification ⋙ pullback ≅ PresheafOfModules.pullback ⋙ sheafification` | tells us "pullback commutes with sheafification" — still does not give the affine-open section formula |
| `SheafOfModules.pullbackObjFreeIso` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:122` | `(pullback φ).obj (free I) ≅ free I` | **only for FREE sheaves** — too restrictive for arbitrary `N : S.Modules` |
| `PresheafOfModules.pullback` | `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:44` | `(pushforward φ).leftAdjoint` | also abstract; sections still not exposed (only `pushforward_obj_obj` has a closed form, not `pullback_obj_obj`) |
| `AlgebraicGeometry.pullbackSpecIso` | `Mathlib/AlgebraicGeometry/Pullbacks.lean` | scheme-level iso `Spec S ×_{Spec R} Spec T ≅ Spec (S ⊗_R T)` | base-scheme pullback, NOT module-pullback. Provides ring data for the target but does not identify `(g')*F` at sections |
| `Module.Flat.isBaseChange` | `Mathlib/RingTheory/Flat/Stability.lean:90` | `IsBaseChange S f → Flat S N` | the *algebraic atom* — confirms preservation of flatness once the iso is in hand, but does not produce the iso itself |
| `IsBaseChange.equiv` | `Mathlib/RingTheory/IsTensorProduct.lean:375` | `S ⊗[R] M ≃ₗ[S] N` from `IsBaseChange S f` | the actual linear iso; this is what one would *consume* once the LHS bridge yields an `IsBaseChange` witness |
| `AlgebraicGeometry.Flat.flat_appLE` | `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` | flatness of `Scheme.Hom.appLE g U V _ : Γ(S, V) →+* Γ(S', U)` for affine opens | the ring-level flatness hypothesis the affine-base helper would feed `Module.Flat.isBaseChange` |
| `Module.Flat.casesOn` — same file | per-affine flat ring map hypothesis | matches `Flat.mk` pattern of `[Flat g]` | extracts the hypothesis, not the iso |

Direct LSP search via `lean_leansearch` ("pullback of sheaf of modules
sections affine tensor product", "scheme modules pullback section affine
open", "tilde tensor product base change quasi-coherent module") returned
*no* lemma producing the section identification. The only closed-form
section lemma for `Scheme.Modules.pullback` is `pullbackObjFreeIso` at
free sheaves.

A search of Mathlib for Stacks-02KH/02KE references confirms only one
hit (`Mathlib/RingTheory/IntegralClosure/GoingDown.lean:47:@[stacks 00H8]`,
unrelated to sheaf pullback). The scheme-level Stacks 02KH cohomology
base-change is genuinely absent.

## Decisions identified

### Decision 1: Affine-open section formula for `Scheme.Modules.pullback`

- **Mathlib idiom**: There is **none**. `Scheme.Modules.pullback g` is
  abstract (`pushforward g`'s `leftAdjoint`), built through partial-adjoint
  machinery. The only closed-form section lemma is `pullbackObjFreeIso`
  *at free sheaves*. Cited:
  `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:167`,
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53`,
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:122`. The
  blueprint explicitly identifies this as a project-side bridge
  (`Picard_QuotScheme.tex:851–856`).
- **Project's current path**:
  `canonicalBaseChangeMap_app_app_isIso_of_isAffineOpen_of_isAffineBase`
  carries a typed `sorry` waiting for the bridge. The intended use is
  `IsBaseChange.equiv` applied to a witness produced from the ring map
  `Scheme.Hom.appLE g ⊤ U _ : Γ(S, ⊤) →+* Γ(S', U)` (flat by
  `Flat.flat_appLE`).
- **Gap**: divergent-and-wrong (in the sense that **no Mathlib idiom
  exists**, so consuming it as a `sorry` is the only option until the
  bridge is built).
- **Cost of divergence**: TWO bodies sit on this gap (`_of_isAffineOpen_of_isAffineBase`
  AND, transitively, the general-base `_of_isAffineOpen`, plus
  `canonicalBaseChangeMap_app_app_isIso`, `canonicalBaseChangeMap_isIso`,
  and `flatBaseChangeCohomology`). 4 helpers, 2 iters of lane work, no
  payoff. Each iter another helper appears around the gap, not closing it.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL → BUILD_PROJECT_HELPER.** The
  helper required is a new project-side definition:
  ```lean
  /-- Sections of the pullback of `Scheme.Modules` over a compatible
  affine pair `(V ⊆ S, U ⊆ S')` identify with the tensor product. -/
  noncomputable def Scheme.Modules.pullback_app_isoTensor
      {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
      {U : Y.Opens} {V : X.Opens}
      (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (e : U ≤ (Opens.map g.base).obj V) :
      Γ((Scheme.Modules.pullback g).obj N, U) ≃ₗ[Γ(Y, U)]
        TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) := sorry
  ```
  (or the analogous `IsBaseChange` statement). The fact that **the
  presheaf-level pullback is also abstract** (`PresheafOfModules.pullback`
  is also a partial-adjoint construction with no `pullback_obj_obj`
  closed form, cf.
  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:44`) means
  one cannot collapse the proof through the presheaf level either —
  the body has to be built directly. The standard Mathlib trick for
  affine targets is the **Tilde** route
  (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`): on `Spec R`,
  `tilde M` is the QC sheaf with `Γ(tilde M, ⊤) = M` (`tilde.isoTop`),
  and `(pullback g).obj (tilde N) ≅ tilde (Γ(S', U) ⊗_R N)` would be the
  corresponding identification on Spec rings. Promoting this from the
  Spec/tilde setting to a general affine open in `S'` is essentially
  Stacks tag 01I8 / 01HQ machinery — also absent at the pinned commit.

### Decision 2: `Module.Flat.isBaseChange` consumer-side packaging

- **Mathlib idiom**: `IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N`
  (`Mathlib/RingTheory/IsTensorProduct.lean:375`) **is** the right
  consumer. Once an `IsBaseChange (algebraMap R S) (η.toLinearMap)`
  witness is in hand for the affine-open ring data, this single
  declaration produces the iso. `Module.Flat.isBaseChange`
  (`Mathlib/RingTheory/Flat/Stability.lean:90`) is sound for the
  flatness *consequence* but is not the iso witness.
- **Project's current path**: The blueprint and the lemma docstring
  already plan to use `IsBaseChange.equiv`. Good fit.
- **Gap**: identical.
- **Verdict**: PROCEED. Once Decision 1's helper lands, this is a
  3–5 LOC consumption (compose `pullback_app_isoTensor` with
  `IsBaseChange.equiv.symm`, then conclude `IsIso` via
  `LinearEquiv.toEquiv.bijective` and reflective comparison with the
  Beck-Chevalley arrow).

### Decision 3: Base-side Mayer-Vietoris reduction (general `S`)

- **Mathlib idiom**: Mathlib has `Scheme.Modules.Hom.isIso_iff_isIso_app`
  (`Sheaf.lean:131-135`) which reduces "iso of `S'.Modules` morphism" to
  "iso on every `U : S'.Opens`". It does NOT reduce "iso on every open"
  to "iso on a basis" for `Scheme.Modules`. For sheaves on topological
  spaces, "iso on stalks ⟹ iso" (`TopCat.Presheaf.stalkFunctor` +
  `ReflectsIsomorphisms`) is the canonical route, but our morphism is
  in `Scheme.Modules`, not stalks. There is currently no
  `Scheme.Modules.Hom.isIso_iff_isIso_app_isAffineOpen` lemma.
- **Project's current path**: Body of `_of_isAffineOpen` is a typed
  `sorry` planning a refinement of affine `U` along affine cover of `S`,
  then descent via `QuasiSeparated f`. The project already has the
  *target-side* dual (`_of_affineCover` — also a sorry) which is the
  exact symmetric problem.
- **Gap**: divergent-and-wrong (no idiom exists; symmetric to gap (b)).
- **Verdict**: **BUILD_PROJECT_HELPER.** Two routes:
  1. Build a project-side `Scheme.Modules.Hom.isIso_iff_isIso_app_isAffineOpen`
     (general-purpose), then apply it on both target and base sides. This
     subsumes the existing `_of_affineCover` helper as well — best ROI.
  2. Direct route: build base-side `_of_baseAffineCover` paralleling
     the existing `_of_affineCover`, both still as project-side helpers.

## Cost estimates

| Helper | LOC | Dependencies | Notes |
|---|---|---|---|
| `Scheme.Modules.pullback_app_isoTensor` (gap (a)) | **~120–200** | `pullbackIso`, `PresheafOfModules.pullback` machinery, `Tilde` route, `IsBaseChange.of_lift_unique` | The hard part. Body needs to either: (a) trace through `pullbackIso` + sheafification = identity on affine opens (because affine opens are sheafification-stable; reduces to the presheaf-pullback identification), OR (b) use the universal property of `pullback` via `pullbackPushforwardAdjunction` and exhibit the tensor product as the universal `Γ(Y, U)`-module receiving a `Γ(X, V)`-linear map from `Γ(N, V)` |
| `_of_isAffineOpen_of_isAffineBase` body (consumes (a)) | ~15–25 | (a), `IsBaseChange.equiv`, `Flat.flat_appLE`, `Module.Flat.isBaseChange` | Composes `pullback_app_isoTensor` (LHS) with `pushforward_pullback_section_eq_pullback_section` (RHS, already rfl) and the canonical Beck-Chevalley arrow comparison |
| `Scheme.Modules.Hom.isIso_iff_isIso_app_isAffineOpen` (gap (b), general-purpose route) | ~40–70 | affine opens form a basis (`Scheme.affineOpens` + `Opens.isBasis`), `Scheme.Modules.Hom.isIso_iff_isIso_app`, `Mathlib.CategoryTheory.IsIso.of_isIso_image` for sheaf-restricted morphisms | Mathlib has `TopCat.Sheaf.hom_ext` + `Hom.isIso_of_isIso_on_basis`-style lemmas; need to lift to `SheafOfModules` and adapt to `Scheme.Modules` |
| `_of_isAffineOpen` body (consumes (b)) | ~10–15 | (b), `_of_isAffineOpen_of_isAffineBase`, restriction `g \|_{(g)⁻¹V}` flat-preserved | Refines `U` along base affine cover, applies (b) |

**Total project-side build for the lane to close**: ~185–310 LOC (gap (a)
is the load-bearing 120–200 LOC chunk).

## Recommendation: DO NOT dispatch a prover lane on `_of_isAffineOpen_of_isAffineBase` this iter

The bodies cannot close without `Scheme.Modules.pullback_app_isoTensor`
existing as a project-side declaration. The pattern of "4 helpers, 2
iters, +1 sorry" is a textbook indicator that the lane is chasing a
Mathlib gap by structural decomposition without a concrete tool to
discharge the load-bearing leaf. **Pivot the lane**: instead of another
helper around `_of_isAffineOpen_of_isAffineBase`, dispatch a prover lane
to **CREATE `Scheme.Modules.pullback_app_isoTensor`** as a new
declaration in `AlgebraicJacobian/Picard/QuotScheme.lean` (or a new
helper file `AlgebraicJacobian/Picard/PullbackAffineSections.lean`), with
the signature above and a typed `sorry`.

Once that helper *exists* (even with a sorry body), the affine-base
helper body collapses to ~15–25 LOC of book-keeping AND the lane stops
accumulating peripheral helpers — only one new sorry is born, but it
is precisely the substantive gap, *named and reusable*.

The body of `pullback_app_isoTensor` itself is iter-183+ work; it is the
genuine 120–200 LOC build. Strategically, this is a Mathlib lemma owed
to upstream — it would be reasonable to prepare a Mathlib PR for it once
the project body lands (the precedent
`analogies/kaehler-tensorequiv-presheafpullback.md` for relative
differentials is structurally analogous and faced the same gap).

## Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| 1. Pullback affine-open section formula | NEEDS_MATHLIB_GAP_FILL → BUILD_PROJECT_HELPER | critical |
| 2. `IsBaseChange.equiv` consumer | PROCEED | informational |
| 3. Base-side Mayer-Vietoris | NEEDS_MATHLIB_GAP_FILL → BUILD_PROJECT_HELPER | high |

The lane is genuinely blocked on Mathlib gaps that require project-side
helpers. A prover lane this iter should pivot to **introducing the
load-bearing project-side declaration as a named (sorry-bodied) helper**
rather than producing yet another decomposition helper.
