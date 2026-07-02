# `dual_restrict_iso` — the C-bridge residual (iter-230 diagnostic, OUTCOME (ii))

## Goal (the C-bridge `dual_isLocallyTrivial` needs this)

For an open immersion `f : Y ⟶ X` and `M : X.Modules`:
```
dual_restrict_iso : (Scheme.Modules.dual M).restrict f ≅ Scheme.Modules.dual (M.restrict f)
```
With it, `dual_isLocallyTrivial` follows mechanically (mirror of `tensorObj_isLocallyTrivial`):
`(dual M)|_U ≅ dual (M|_U) ≅ dual 𝒪_U ≅ 𝒪_U` using `(dualIsoOfIso eM).symm` and a
`dual_unit_iso : dual 𝒪 ≅ 𝒪`.

## What was verified live this iter (Steps 1–3 + H1 all TYPECHECK)

Mirroring `tensorObj_restrict_iso` verbatim, swapping
`PresheafOfModules.Monoidal.tensorObj M.val N.val` → `PresheafOfModules.dual M.val`:

- Step 1 `Scheme.Modules.restrictFunctorIsoPullback f` — OK
- Step 2 `SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom` — OK
- Step 3 strip outer sheafification (`(sheafification (𝟙 …)).mapIso ?_`) — OK
- Step 4 H1 `pushforwardPushforwardAdj ∘ leftAdjointUniq` (the SAME `hadj`/`H1` block
  as `tensorObj_restrict_iso`) — OK

Residual goal produced by Lean (verified via `lean_goal`):
```
⊢ (PresheafOfModules.pushforward β).obj M.val.dual ≅ (M.restrict f).val.dual
```
`change`-confirmed defeq to:
```
⊢ (PresheafOfModules.pushforward β).obj (PresheafOfModules.dual M.val)
    ≅ PresheafOfModules.dual ((PresheafOfModules.pushforward β).obj M.val)
```
i.e. **the open-immersion pushforward commutes with the presheaf dual** — the residual
the iter-228/229 plan predicted.

## Why the shared root `overSliceSheafEquiv` does NOT discharge it — OUTCOME (ii)

`overSliceSheafEquiv U A : Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

Three independent type/structure mismatches, all confirmed live:

1. **Sheaf vs presheaf.** The root's domain/codomain are `Sheaf` categories. Step 3 of the
   mirror already stripped the OUTER sheafification, so the residual lives in
   `PresheafOfModules (Y.presheaf ⋙ forget₂ …)`. Direct application fails on type
   (`overSliceSheafEquiv` is not even in scope at the proof site — it is defined later in
   the file, and its codomain is `Sheaf`, not `PresheafOfModules`).

2. **Fixed value-cat vs varying-ring module fibration.** The root is parametric in a FIXED
   value category `A`. The residual is an iso of `ModuleCat` over the VARYING ring
   `𝒪_Y(V) = R_Y(V)`. The per-`V` module action (`internalHomObjModule` over `Over V`) is
   exactly what a fixed-value-cat site equivalence does not transport for free. This is the
   "module fibration" cost strategy-critic ts230 flagged.

3. **Whole-`U` slice site vs per-open slices.** The dual's value uses
   `restr W = pushforward₀ (Over.forget W)` — the slice over a SINGLE open `W` — whereas the
   root is built over `(Opens.grothendieckTopology X).over U`, the whole-`U` slice site.

## Precise missing ingredient (the genuine new build — the substrate's 4th growth)

A **PRESHEAF-level, `𝒪_Y(V)`-linear slice-internal-hom comparison**, natural in `V`:
```
Hom_{Over_X (f.opensFunctor V)} (restr (f.opensFunctor V) A, restr (f.opensFunctor V) 𝟙_X)
  ≅  Hom_{Over_Y V} (restr V ((pushforward β).obj A), restr V 𝟙_Y)
```
induced by:
- the **per-`V` slice equivalence** `Over_Y V ≌ Over_X (f.opensFunctor V)` — the per-`V`
  shadow of `TopologicalSpace.Opens.overEquivalence`, valid because `f.opensFunctor` is fully
  faithful with image `{W ≤ U}` and `f.opensFunctor V ≤ U` (range of the open immersion);
- the identification `restr (f.opensFunctor V) A ≅ G^* (restr V ((pushforward β) A))` under
  that equivalence `G` (since `A(f W'') = ((pushforward β) A)(W'')`);
- the **ring-iso transport** `β = (toRingCatSheafHom f).hom`, sectionwise `f.appIso`, carrying
  the `𝒪_X(fV)`-module structure to the `𝒪_Y(V)`-module structure (the H2′-flavoured step;
  `restrictScalarsRingIsoDualEquiv` is the ModuleCat-level shadow but it does NOT by itself
  bridge the SLICE-internal-hom value, only the sectionwise dual).

This is the presheaf+module analogue of `overSliceSheafEquiv` (which is sheaf+fixed-value-cat).
The sheaf-level root, while genuinely needed elsewhere (the A-engine `homOfLocalCompat`, value
cat `Type`, IS cleanly served by it), does **not** cover the C-bridge's presheaf+module need.

Conceptually this is the standard fact "restriction to an open commutes with internal Hom of
sheaves" `f^* ℋom(A,B) ≅ ℋom(f^*A, f^*B)`; the obstacle is purely that this file's bespoke
`PresheafOfModules.internalHom` (slice/end construction over `Over W`) has NO Mathlib API
relating it to `pushforward`/`pullback`, so the comparison must be built by hand over the
per-`V` slice equivalence + ring-iso transport. Estimated ~150–300 LOC, with real `Over.map`
pseudofunctor-coherence risk (unlike the sheaf root, where thinness of `Opens` trivialised it —
here the slice presheaves carry the module structure that thinness does NOT kill).

## Informal-agent status
`MOONSHOT_API_KEY`/Kimi key present but returns `401 Invalid Authentication`; no other relevant
key (`DEEPSEEK`/`OPENROUTER`/`OPENAI`/`GEMINI_API_KEY`) set. Informal agent UNAVAILABLE this iter.

## Recommendation
Per the iter-230 HARD TRIPWIRE (progress-critic ts230): C wired = outcome (ii), the substrate
grew a 4th time, the binding probe did NOT move 80→79. No further autonomous infra round on this
lane — escalate the divisor/`Pic⁰` fork to the USER (lift the ROUTE C PAUSE to switch to the
Abel–Jacobi route, or sanction building this presheaf+module slice comparison as a multi-iter
sub-build).
