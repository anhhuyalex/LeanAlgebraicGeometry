# Missing ingredient: `pullbackTensorMap` is an iso for open immersions (K1)

## Statement (project-local, `TensorObjSubstrate.lean`, ~L4139)

```lean
private lemma pullbackTensorMap_isIso_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) :
    IsIso (pullbackTensorMap f M N)
```

This is the **sole open brick** of seed-1 D4′ `pullbackTensorIsoOfLocallyTrivial`
(`lem:pullback_tensor_iso_loctriv`). The whole chart-chase (the cover argument
`isIso_of_isIso_restrict` + the two `pullbackTensorMap_restrict` base-change splits + the
trivial-base case K2) is now CLOSED and compiles; it reduces the entire D4′ `IsIso` obligation
to exactly this one lemma, instantiated at the two open immersions `(f⁻¹W).ι` and `W.ι`.

## Why it is true

`pullbackTensorMap f M N` reduces (via `isIso_pullbackTensorMap_of_isIso_sheafifyDelta`) to
`IsIso (a_Y.map δ)` where `δ` is the presheaf-level oplax comparison of
`PresheafOfModules.pullback φR`, `φR = (Hom.toRingCatSheafHom f).hom`. Sheafification preserves
isos, so it suffices that the **presheaf-level `δ` is an iso**. Mathlib already provides
`instance [F.Monoidal] : IsIso (Functor.OplaxMonoidal.δ F X Y)`
(`Mathlib/CategoryTheory/Monoidal/Functor.lean:396`). So the residual is precisely:

> **`(PresheafOfModules.pullback φR).Monoidal`** (strong monoidal) for an OPEN immersion `f`.

Geometric content: pullback along an open immersion is restriction, which is *strong* monoidal
(it is sectionwise the structure-ring ISO `f.appIso`). This is exactly the H1/H2 model already
used in `tensorObj_restrict_iso` (CLOSED, axiom-clean):

- `β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj`,
  `β.app U = forget₂.map (f.appIso U.unop).inv`, sectionwise **bijective**.
- `pushforward β = pushforward₀OfCommRingCat ⋙ restrictScalars β'` is **strong monoidal**
  (`restrictScalarsMonoidalOfBijective` + `pushforward₀OfCommRingCat.Monoidal`).
- `H1 := hadj.leftAdjointUniq (pullbackPushforwardAdjunction φR) : pushforward β ≅ pullback φR`
  (`hadj` from `pushforwardPushforwardAdj` on `f.isOpenEmbedding.isOpenMap.adjunction`).
- `Functor.Monoidal.transport H1 : (pullback φR).Monoidal` (Mathlib
  `Mathlib/CategoryTheory/Monoidal/Functor.lean:1321`).

## What I tried (and the two precise blockers)

I built the full `β`, `hadj`, `H1`, the strong-monoidal `pushforward β`, and attempted
`Functor.Monoidal.transport H1`. It does NOT elaborate, for two Mathlib-absent reasons (both
ARCHON_MEMORY-flagged):

1. **Carrier diamond.** `MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)` is not
   *globally* synthesizable: the instance is keyed on the syntactic carrier
   `X.presheaf ⋙ forget₂ CommRingCat RingCat`, only DEFEQ (not syntactically equal) to
   `X.ringCatSheaf.obj`. `tensorObj_restrict_iso` dodges this by working IN-PROOF with a `letI`
   bridge + a `β'`-defeq-cast and producing an iso at the **object** level. But
   `Functor.Monoidal.transport` needs the **functor-level** `(pushforward β).Monoidal` instance,
   whose statement mentions `MonoidalCategory` on the bare `X.ringCatSheaf.obj` carrier — and that
   instance is not synthesizable at the top level. Error:
   `failed to synthesize MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)`.

2. **OplaxMonoidal diamond.** Even granting `(pullback φR).Monoidal`, the goal's `δ` uses
   `presheafPullbackOplaxMonoidal φR = (pullbackPushforwardAdjunction φR).leftAdjointOplaxMonoidal`
   (the adjunction mate), whereas `transport`'s `Monoidal.toOplaxMonoidal` is built via
   `coreMonoidalTransport`. These are not defeq, so the Mathlib `IsIso (δ)` instance does not match
   the goal's `δ` without a `Functor.Monoidal.transport_δ` bridge.

## Precise missing ingredient (for `mathlib-build` mode)

A **functor-level strong-monoidal model of `PresheafOfModules.pullback` along an open immersion**,
exposed so that `(PresheafOfModules.pullback φR).Monoidal` is obtainable WITHOUT triggering the
`MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)` carrier diamond, plus a reconciliation
that the resulting `δ` agrees (defeq or via a stated lemma) with the adjunction-mate
`presheafPullbackOplaxMonoidal` `δ`. Concretely one of:

- a `Functor.Monoidal`-transport lemma that operates up to the carrier defeq (a `letI`-localized
  variant of `Functor.Monoidal.transport` for the `⋙ forget₂` carrier), **and** a
  `transport_δ`-based bridge to `presheafPullbackOplaxMonoidal`; or
- a direct `lemma : IsIso (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φR) A B)` for
  `[IsOpenImmersion f]`, proved by the H1/H2 strong-monoidal model with the carrier handled
  in-proof (mirroring `tensorObj_restrict_iso`'s object-level closure but at the `δ` level).

Estimated ~80–150 LOC, mate-calculus + carrier-bridging style.
