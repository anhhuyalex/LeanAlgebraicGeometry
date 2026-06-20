# Analogy: is `PresheafOfModules.pullback` strong monoidal (δ iso)?

## Mode
api-alignment

## Slug
presheaf-pullback-strong

## Iteration
244

## Question
Is the comparison morphism `δ` of `PresheafOfModules.pullback φ` an isomorphism (i.e.
is `PresheafOfModules.pullback` STRONG monoidal, not merely oplax) in the pinned Mathlib —
via an existing `Functor.Monoidal`/`CoreMonoidal` instance, or via a short provable route
from sectionwise `ModuleCat.extendScalars.Monoidal` (`distribBaseChange`)? Can the project's
`pullbackTensorMap` (sheaf-level `f^*(M⊗N) ⟶ f^*M ⊗ f^*N`) be upgraded to an iso for general
`M,N` at bounded cost?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1220` — `pullbackTensorMap` (δ_sheaf), the
  4-step composite; step 2 is `a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') …)`.
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1159` — `presheafPullbackOplaxMonoidal`
  (the oplax mate from `leftAdjointOplaxMonoidal`).
- `analogies/pullback-tensor.md` (iter-242, same arc).

## Pinned-Mathlib facts established this iter (all cited, all verified on disk)

1. **`PresheafOfModules.pullback φ := (pushforward φ).leftAdjoint`** — an ABSTRACT left adjoint,
   defined for a *general* functor `F : C ⥤ D`, with **no sectionwise / colimit / stalk formula
   exposed**. `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:44`. It is NOT defined
   as sectionwise `extendScalars`. (Same shape as the sheaf-level pullback analysed in iter-242.)

2. **No strong instance, no `IsIso δ` lemma.** Grep of `ModuleCat/Presheaf/**` and `ModuleCat/**`
   finds NO `(pullback φ).Monoidal` / `.CoreMonoidal` and NO `IsIso (Functor.OplaxMonoidal.δ
   (pullback φ) …)`. The only monoidal structure on `pullback` is the project's own *oplax* mate.

3. **The presheaf tensor is SECTIONWISE**: `(M₁ ⊗ M₂).obj X = M₁.obj X ⊗ M₂.obj X`.
   `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` (`tensorObj`, `@[simps obj]`).

4. **Decomposition (decisive):** `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`.
   `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:86-87`. Taking left adjoints:
   `pullback φ ≅ extendScalars φ ⋙ pullback₀`, where `pullback₀ = (pushforward₀).leftAdjoint`.
   - `extendScalars` is **STRONG** (`distribBaseChange`, an iso) — the scalar part is fine.
   - So **presheaf δ is iso ⟺ `pullback₀` δ is iso** — i.e. the question collapses to the
     *inverse-image / left-Kan-extension* part `pullback₀`, the topological piece.

5. **`pushforward₀OfCommRingCat F R` is STRONG monoidal with μ = `Iso.refl`** (pure reindexing
   commutes strictly with sectionwise tensor). `…/Presheaf/PushforwardZeroMonoidal.lean:33`.
   And `pushforward₀ ⋙ toPresheaf ≅ toPresheaf ⋙ (whiskeringLeft).obj F.op` (Pushforward.lean:75)
   — so `pushforward₀` is "restriction along `F.op`" and `pullback₀ = Lan F.op` (left Kan
   extension) on underlying presheaves.

6. **No general categorical shortcut.** `Adjunction.leftAdjointOplaxMonoidal`
   (`Mathlib/CategoryTheory/Monoidal/Functor.lean:1009`) gives ONLY oplax. The sole upgrade to
   strong is `Functor.Monoidal.ofOplaxMonoidal` (line 704) which *requires* `[∀ X Y, IsIso (δ)]`
   as a hypothesis — no free "right adjoint strong ⟹ left adjoint strong". (The only place lax
   becomes automatically strong is `…laxMonoidalEquivOplaxMonoidal` for an *equivalence*, line
   1107 — `pullback` is not an equivalence.) There is **no monoidal Kan-extension API**
   (`CategoryTheory/Functor/KanExtension/*` has zero `monoidal`) and **no `ModuleCat` "filtered
   colimit commutes with tensor" lemma** surfaced.

## The mathematical truth (and why it does not help cheaply)

`pullback₀ = Lan F.op`, so `pullback₀(M⊗N)(d) = colim_{(F↓d)} (M(c) ⊗ N(c))` while
`(pullback₀ M ⊗ pullback₀ N)(d) = (colim M(c)) ⊗ (colim N(c))`. The comparison is iso **iff the
comma category `(F↓d)` is sifted/filtered** (tensor preserves filtered colimits; the diagonal is
final). For a *general* `F` this fails — hence no general strong instance (consistent with fact 2).
For the geometric `F = Opens.map f.base`, `(F↓V)` is the poset of opens `U` with `f⁻¹U ⊆ V`,
which is up-directed (`U₁∪U₂` is an upper bound) — **so the presheaf δ genuinely IS an iso for
the scheme pullback.** The directive's "pullbackTensorMap iso ⟺ presheaf δ iso" is therefore
*true*, and the iso is *real geometric content* — but its proof requires the filtered-comma-category
input, which the abstract-adjoint `pullback` does not expose.

## Decisions identified

### Decision: existing strong/CoreMonoidal instance for `PresheafOfModules.pullback`?
- **Mathlib idiom**: strong monoidal functors carry `Functor.Monoidal`/`CoreMonoidal`; the
  endorsed pattern (PR #36599) builds the LEFT adjoint's strong structure *concretely*
  (`extendScalars.Monoidal` via `distribBaseChange`) and derives the right adjoint's lax via the
  adjunction. Cite: `…/ModuleCat/Monoidal/Adjunction.lean`, `…/Monoidal/Functor.lean:704,1009`.
- **Project's path**: relies on the abstract-adjoint `pullback` + `leftAdjointOplaxMonoidal`
  (oplax only), then *hopes* δ is iso.
- **Gap**: divergent-and-wrong-to-hope-for-free. Mathlib supplies oplax only; strong requires
  an explicit `IsIso δ` proof that the abstract adjoint cannot furnish.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: short provable route to presheaf δ iso from sectionwise `extendScalars.Monoidal`?
- **Mathlib idiom**: would need a monoidal left-Kan-extension API or a concrete inverse-image
  functor of presheaves of modules with a pointwise colimit formula + filtered-colimit/tensor
  interchange. **None exist** at the pin (facts 6).
- **Project's path**: `extendScalars` strong reduces the problem to `pullback₀`, but `pullback₀`
  is the abstract `(pushforward₀).leftAdjoint` with no `Lan` colimit formula to run the filtered
  argument on.
- **Gap**: divergent-with-cost = Mathlib-scale. The reduction is clean, but the residual
  `pullback₀`-δ-iso is the genuine multi-hundred-LOC build (concrete inverse-image-of-modules
  model + filtered-colimit interchange + identification with the abstract adjoint).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: is the directive's reduction "pullbackTensorMap iso ⟺ presheaf δ iso" the operative one?
- The operative requirement is `a_Y.map(δ)` iso = **sheafify(δ) iso**, which is implied by δ being
  merely *locally bijective* (stalkwise iso) — strictly WEAKER than δ iso. Mathlib's
  `J.W_of_isLocallyBijective` (`…/Presheaf/Sheafify.lean:398`) inverts locally-bijective maps under
  sheafification, so this is the one bounded *handle* — BUT it needs δ's local sections / stalks,
  and (a) the abstract adjoint exposes none, (b) **Mathlib has no stalk functor for presheaves of
  modules** (empty grep). So this route hits the same wall.
- **Verdict**: PROCEED (the reduction is correct for the geometric case) but **does not unlock a
  cheap proof** — every route bottoms out at the same missing concrete inverse-image model.

## Recommendation
Do **not** re-route Lane 1 to "prove `pullbackTensorMap` iso in a few lemmas, then
`IsInvertible.pullback` in 3 lines." The load-bearing `lemma-tensor-product-pullback` (pullback
strong monoidal) is *exactly* the standard-but-unformalized content: in pinned Mathlib `pullback`
is an abstract left adjoint that is only oplax, the lone oplax→strong upgrade demands an explicit
`IsIso δ`, and proving that δ-iso (true for the geometric `f` via a filtered-comma-category /
filtered-colimit-commutes-with-tensor argument, or via a stalkwise local-iso argument after
sheafification) requires a concrete inverse-image-of-presheaves-of-modules model + monoidal-Kan /
stalk infrastructure that Mathlib does not have. This reaffirms iter-242 Analogue 2: the honest cost
is the concrete strong-monoidal pullback model transported via `leftAdjointUniq` — HIGH /
multi-hundred-LOC, no shortcut. The "3-line Stacks proof" assumes a formalized strong-monoidal
pullback the project does not possess. If the planner wants the *cheapest* path to
`IsInvertible.pullback`, weigh this Mathlib-scale strong-monoidality build against the iter-243
local-trivialization route on equal footing — the directive's framing of local-trivialization as a
"detour" is not supported: both are multi-hundred-LOC, and neither is the bounded win the directive
hoped δ-iso would be.
