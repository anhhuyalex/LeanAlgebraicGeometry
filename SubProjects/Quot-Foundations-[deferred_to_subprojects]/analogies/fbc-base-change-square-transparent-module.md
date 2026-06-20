# Analogy: transparent `R'`-module action for a base-change-square `ModuleCat` iso

## Mode
cross-domain-inspiration

## Slug
fbc-base-change-square-transparent-module

## Iteration
009

## Structural problem (abstracted)
We need an isomorphism of `ModuleCat R'` objects realising a ring base-change /
restriction-extension square (`(A⊗_R R')⊗_A M ≅ R'⊗_R M`), built so that the `R'`-action on
the carriers is *usable by typeclass resolution* — i.e. `smul_zero`/`smul_add` fire — rather
than being an opaque `_aux` `Module` def produced by Mathlib's `ModuleCat.ExtendScalars` /
`RestrictScalars` functor objects. The question is the canonical Mathlib idiom for stating and
consuming such a square iso transparently.

## Empirical root cause (confirmed this iter, not merely suspected)
At the `refine LinearEquiv.toModuleIso (e := { g with map_smul' := ?_ })` site of
`base_change_mate_regroupEquiv` (`FlatBaseChange.lean:909`), the `R'`-module instances on the
carriers are the opaque
`base_change_mate_regroupEquiv._aux_3 / ._aux_5 : Module ↑R' ↑((ModuleCat.extendScalars …).obj M)`.
The two `r' • 0 = 0` zero branches of the `TensorProduct.induction_on` proof of `map_smul'`
**cannot close by any of** `simp only [smul_zero, map_zero]` ("simp made no progress"),
`rw [smul_zero]` ("did not find pattern `?a • 0`"), or `erw [smul_zero]`
("**failed to synthesize `SMulZeroClass ↑R' ↑((ModuleCat.extendScalars …).obj M)`**").
The headline is the last: `SMulZeroClass R'` does not synthesize *from* the opaque `_aux_3`
`Module R'` instance, so the `smul_zero` lemma cannot even be stated against the goal, let
alone rewritten. By contrast, the `add`/`tmul` branches close by `erw [smul_add]` /
`erw [ExtendScalars.smul_tmul]` because those lemmas unify against `r' • (a+b)` / `r' • (a⊗s)`
subterms already present in the goal (whose `SMul` instance is fixed by the term), needing no
fresh class synthesis. The asymmetry is intrinsic: `smul_zero`'s `0` carries no `SMul` subterm
to pin the instance, so the elaborator falls back to synthesising `SMulZeroClass` and dies on
the opaque `_aux`. `letI`/`inferInstanceAs`/`.toDistribMulAction` re-supply a *fresh* `_aux`
that TC still ignores or that `whnf`-times-out. **The in-place `map_smul'`-over-functor-object
route is therefore structurally dead, not merely hard.**

Note also: the optimistic note at `FlatBaseChange.lean:851` ("`exact LinearEquiv.toModuleIso
(base_change_regroup_linearEquiv ↑M)` typechecks once the helper is in a separate compiled
module") is **stale/wrong**; the detailed note at `:911` is **correct**. Tested directly: the
imported helper has type `(A⊗[R]R')⊗[A]M ≃ₗ[R'] R'⊗[R]M` with the *canonical* `Module A (A⊗R')`
(`Algebra.TensorProduct.leftAlgebra`) and `Module R M`, and `exact … .toModuleIso` fails with
"Application type mismatch … `(A⊗[R]R')⊗[A]M ≃ₗ[R'] …` but expected
`↑((ModuleCat.extendScalars includeLeftRingHom).obj M) ≃ₗ[R'] …`". The `⊗[A]` carriers differ
by the `Module A (A⊗R')` diamond (`includeLeftRingHom.toAlgebra` as used by `extendScalars`
vs `leftAlgebra` as used by `cancelBaseChange`); unifying them forces `whnf` of the opaque
object instance and does not go through.

## Failed approaches (from directive)
- Hand-built `g : LinearEquiv` over the bare functor-object carriers, `LinearEquiv.toModuleIso` →
  `map_smul'` zero branches blocked on opaque `Module ↑R'` (confirmed above).
- `erw [ExtendScalars.smul_tmul]` + `show` reductions → close `tmul`/`add`, leave the two `zero`
  branches with no tensor head to rewrite and no `SMulZeroClass` to synthesize.
- `letI`/`haveI`/`inferInstanceAs` re-supplying `SMulZeroClass`/`DistribMulAction` → fresh opaque
  `_aux`, ignored by TC; `.toDistribMulAction` projection `whnf`-times-out.

## Analogues found (ranked by porting cost, lowest first)

### Analogue: `Algebra.IsPushout.cancelBaseChange` (`Mathlib.RingTheory.IsTensorProduct`)
- **Domain**: commutative algebra / ring base change (pushout of `CommRing`s).
- **Same structural problem there**: the *pushout-form* base-change cancellation. With
  `[Algebra.IsPushout R S A B]`,
  `cancelBaseChange R S A B M : B ⊗[A] M ≃ₗ[S] S ⊗[R] M`.
  Instantiated at `R=R, S=R', A=A, B=A⊗[R]R', M=M` it is **exactly the regroup equiv**
  `(A⊗[R]R') ⊗[A] M ≃ₗ[R'] R' ⊗[R] M`, and the `Algebra.IsPushout R R' A (A⊗[R]R')` instance
  it needs is supplied for free by `TensorProduct.isPushout'` (`Algebra.IsPushout R T S (R⊗S T)`
  with `S=A, T=R'`). Companions: `cancelBaseChange_tmul`, `cancelBaseChange_symm_tmul`,
  `toLinearEquiv_cancelBaseChangeAlg`.
- **Technique**: the equivalence is **natively `≃ₗ[S] = ≃ₗ[R']`** — Mathlib already discharges
  `R'`-linearity inside the bundled `LinearEquiv`. There is **no hand-written `map_smul'`**, hence
  **no `TensorProduct.induction_on`, hence no `r' • 0 = 0` zero branch at all**. This is the
  decisive structural improvement over the project's current core
  `TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M R'`, which is only `≃ₗ[A]` (its `B`
  slot is taken as `A`), forcing the project to *re-bundle* `R'`-linearity by hand via
  `rightAlgebra` + `comm` + a manual `map_smul'` — the exact source of the dead zero branches.
- **Mapping to project**: replace the `RegroupHelper.lean` core
  `base_change_regroup_linearEquiv` (`comm ≪≫ ATM.cancelBaseChange ≪≫ comm` + hand `map_smul'`)
  by `Algebra.IsPushout.cancelBaseChange ↑R ↑R' ↑A (↑A ⊗[↑R] ↑R') ↑M` (or keep the helper but
  swap its body). Then `base_change_mate_regroupEquiv` is `LinearEquiv.toModuleIso` of it, modulo
  the **one** residual obstruction shared by every approach: the `Module A (A⊗R')` diamond between
  `cancelBaseChange`'s canonical carrier and `extendScalars`'s functor-object carrier.
- **Porting cost**: low-to-medium. The R'-linearity problem evaporates; the only remaining work is
  the A-diamond carrier bridge (see "How to resolve the residual diamond" below), which is an
  *object-level* `≃ₗ`/`eqToIso` reconciliation that never writes an element-level `r' • 0`.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `ModuleCat.restrictScalarsComp'App` / `restrictScalarsId` / `extendScalarsComp` / `extendScalarsId` / `restrictScalarsCongr` (`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`)
- **Domain**: category theory of change-of-rings functors.
- **Same structural problem there**: building a change-of-rings *tower* iso transparently. The key
  fact is that `restrictScalarsComp'App_hom_apply` / `_inv_apply` are **`= x` (the identity on
  the carrier set)** — the iso relabels the `Module` structure while fixing the underlying
  element. Hence an iso assembled from these never produces an element-level `r' • 0` goal: all
  module-action coherence is internal to the bundled `Iso`.
- **Technique**: assemble the comparison as a composite of `Iso`s in `ModuleCat R'`
  (`restrictScalarsComp'App` ×n, `extendScalarsId`/`Comp`, `restrictScalarsCongr` from a ring
  equation, `eqToIso`, `Functor.mapIso` of a smaller iso) — **never** `LinearEquiv.toModuleIso`
  of a hand `AddEquiv` + `map_smul'`. The project's own `gammaPushforwardIso`
  (`FlatBaseChange.lean:288`) is the existence proof that this route closes **axiom-clean** for a
  restrict-tower (`restrictScalarsComp'App` ×2 + `restrictScalarsCongr` + `eqToIso` from
  `globalSectionsIso_hom_comp_specMap_appTop`).
- **Mapping to project**: use this family to (i) build the A-diamond bridge as an object-level
  iso, and (ii) if/when the square is restated functorially, glue the extend/restrict pieces.
  Caveat: a base-change *square* (Beck–Chevalley) mixes `extend` and `restrict`, so these tower
  isos alone do **not** produce the square — `cancelBaseChange` (analogue 1) supplies the genuine
  associativity content; this family supplies the transparent *packaging*.
- **Porting cost**: low (already in the project's toolbox; `gammaPushforwardIso` is the template).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CommRingCat.moduleCatRestrictScalarsPseudofunctor` (`Mathlib.Algebra.Category.ModuleCat.Pseudofunctor`) and `CategoryTheory.TwoSquare` / Guitart-exactness (`Mathlib.CategoryTheory.GuitartExact.KanExtension`, `isIso_lanBaseChange_app_iff`)
- **Domain**: 2-category theory / pseudofunctors / mate-of-a-square (Beck–Chevalley) calculus.
- **Same structural problem there**: restriction of scalars as a *pseudofunctor*
  `CommRingCatᵒᵖ → Cat` (`mapId = restrictScalarsId`, `mapComp = restrictScalarsComp`) — the
  canonical "coherent gluing of module categories across ring maps" — and the abstract
  base-change *square* as a `TwoSquare` whose mate is invertible iff the square is Guitart-exact.
- **Technique**: phrase the square iso as a 2-cell / mate in the pseudofunctor, so coherence is
  inherited from the (already proven) pseudofunctor/`TwoSquare` laws rather than recomputed.
- **Mapping to project**: this is the "right" long-run home for a reusable `ModuleCat`-level
  Beck–Chevalley square iso (which Mathlib does **not** currently ship for restrict∘extend — a
  genuine upstream gap). For *this* obligation it is over-engineered; cited as the principled
  target if the square iso is ever needed in more generality.
- **Porting cost**: high (would build a `TwoSquare`/pseudofunctor-mate layer).
- **Verdict**: PARTIAL_ANALOGUE.

## How to resolve the residual `Module A (A⊗R')` diamond (shared by all routes)
The diamond is `includeLeftRingHom.toAlgebra` (used by `ModuleCat.extendScalars includeLeftRingHom`)
vs `Algebra.TensorProduct.leftAlgebra` (used by `cancelBaseChange`). They are equal-as-data but
distinct instance terms, so the two `⊗[A]` carrier *types* differ. Critically, with analogue 1 the
diamond is the **only** thing left, and it lives at the *object/carrier* level, where it can be
discharged **without** any element-level `r' • 0`:
- as an `≃ₗ[R']` carrier-swap that is `id` on elements with `map_smul' := fun _ _ => rfl`
  (both sides' `R'`-action are `restrictScalars includeRight` definitionally — the prover's
  existing `eT` is the `A`-linear version of this; the `R'`-linear version composes directly with
  the Mathlib-proven `cancelBaseChange` and needs no induction), or
- absorbed into the `moduleSpecΓFunctor.mapIso`/tilde-dictionary chains the consumers
  (`base_change_mate_codomain_read`, `…domain_read`) already build, via the
  `restrictScalarsComp'App` family (analogue 2).
The point is that the **only** place `R'`-linearity is computed is now inside Mathlib's
`Algebra.IsPushout.cancelBaseChange`; the project writes at most a `rfl`-`map_smul'` identity
bridge, never a `TensorProduct.induction_on` over the opaque carrier.

## Verdict on the directive's two routes
- Directive **(a)** — "retype `g`'s domain/codomain at genuine restrict/extend objects so the
  action is transparent (prover's route (b))": **RECOMMENDED, in the refined form above.**
  Retyping at the *same* functor objects does NOT help (they ARE the opaque carriers — confirmed:
  the goal at `:909` already is between functor objects). What helps is switching the *core* to the
  natively-`≃ₗ[R']` `Algebra.IsPushout.cancelBaseChange`, eliminating the hand `map_smul'`
  entirely, and resolving the A-diamond at the object level.
- Directive **(b)** — "abandon the mate equiv, reduce both sides through the tilde dictionaries to
  `cancelBaseChange` directly": **NOT RECOMMENDED as a primary.** The consumers
  `base_change_mate_domain_read`/`codomain_read` are *typed at the functor objects*, so the same
  A-diamond bridge is unavoidable whether or not a named `regroupEquiv` exists — option (b) inlines
  the identical obstruction into `base_change_mate_generator_trace_eq` while discarding the clean
  blueprint-referenced named declaration. Moreover `generator_trace_eq`/`_trace` are `sorry` for an
  *unrelated* reason (the adjoint-mate unwinding of `pushforwardBaseChangeMap`), which option (b)
  does not advance. Keep the named `regroupEquiv`; fix its construction per (a-refined).

## Top suggestion
Swap the regroup core to `Algebra.IsPushout.cancelBaseChange ↑R ↑R' ↑A (↑A ⊗[↑R] ↑R') ↑M`
(`Mathlib.RingTheory.IsTensorProduct`; `IsPushout` from `TensorProduct.isPushout'`), which is
natively `≃ₗ[R']` and so carries no hand `map_smul'` and no `r' • 0` zero branch. Promote it with
`LinearEquiv.toModuleIso`, reconciling the lone `Module A (A⊗R')` diamond against
`(ModuleCat.extendScalars includeLeftRingHom).obj M` with an object-level `id`/`eqToIso` carrier
bridge (the `R'`-linear analogue of the existing `eT`, `map_smul' := fun _ _ => rfl`), modelled on
the axiom-clean element-free assembly of `gammaPushforwardIso`. First file to touch:
`AlgebraicJacobian/Cohomology/RegroupHelper.lean` (replace `base_change_regroup_linearEquiv`'s
body), then `FlatBaseChange.lean:854` (`base_change_mate_regroupEquiv`).
