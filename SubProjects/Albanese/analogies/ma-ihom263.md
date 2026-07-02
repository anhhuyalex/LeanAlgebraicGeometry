# Analogy: the `internalHomObjModule`-add ↦ `Hom`-add bridge (sliceDualTransport map_add'/map_smul')

## Mode
api-alignment

## Slug
ma-ihom263

## Iteration
263

## Question
Does Mathlib have a canonical idiom that exposes the pointwise `+`/`•` on an internal-hom /
`Hom` object so `map_add` fires WITHOUT a manual `change`?  What is the cleanest bridge for the
`sliceDualTransport` `map_add'`/`map_smul'` fields?  And is `internalHomObjModule` a parallel-API
smell (the progress-critic's "design-shape suspected"), or is only a thin bridge missing?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate/DualInverse.lean:336-346` — `sliceDualTransport`
  `map_add'`/`map_smul'` typed sorries (the blocked `≃ₗ`-packaging fields).
- `AlgebraicJacobian/Picard/TensorObjSubstrate/PresheafInternalHom.lean:628-642` — `homModule`
  (the `Module` instance that `internalHomObjModule` reduces to).
- `AlgebraicJacobian/Picard/TensorObjSubstrate/PresheafInternalHom.lean:669-674` —
  `internalHomObjModule`.

## Decisions identified

### Decision: is `internalHomObjModule` a parallel re-implementation of a Mathlib module-on-Hom?

- **Mathlib idiom**: the module structure on a `Hom`-type is built by supplying ONLY the
  scalar action on top of the *ambient* additive group; `add`/`0`/`neg` are NOT re-declared, they
  come from the category's `Preadditive` instance (`CategoryTheory.Preadditive`,
  `Mathlib/CategoryTheory/Preadditive/Basic.lean`).  This is exactly how Mathlib's own
  `Module.End`, `ModuleCat.restrictScalars`-images, and the fixed-ring internal hom work: the
  `+` on `M ⟶ N` is one canonical `AddCommGroup`, and a `Module R (M ⟶ N)` only adds `smul`.
- **Project's path**: `homModule` (PresheafInternalHom.lean:628) is a `Module … (M ⟶ N) where`
  that supplies **only** `smul := fun f φ => φ ≫ globalSMul hT N f` and the eight `smul`-axiom
  fields.  It declares NO `add`/`zero`/`neg`.  The `AddCommGroup (M ⟶ N)` is the ambient
  `PresheafOfModules.Hom` Preadditive group.  `internalHomObjModule` is just `homModule`
  specialised to the slice terminal `Over.mkIdTerminal`.
- **Gap**: identical.  The `+` carried by `internalHomObjModule` IS the `PresheafOfModules.Hom`
  add — verified: `(x + y).app W = x.app W + y.app W` closes by `rfl` against the real objects
  (see Verified).  There is **no second add**; nothing parallel exists to unify.
- **Cost of divergence**: none — there is no divergence.
- **Verdict**: PROCEED.  `internalHomObjModule`/`homModule` is the Mathlib-aligned shape
  (scalar-only `Module` over a shared Preadditive group).  The `smul` (post-composition with
  `globalSMul`) is the mathematically-canonical action and mirrors `Module.End`/`LinearMap`
  composition; this is the right new structure, not a copy.

### Decision: what bridge unblocks map_add' (and how far does it generalise)?

- **Mathlib idiom**: when an `_app` / `_apply` rewrite (here `PresheafOfModules.add_app`) refuses
  to fire because the operand's `+` is on a `ModuleCat` *carrier* wrapped through
  `pushforward`/`restrictScalars`/`ofPresheaf` (rather than a literal `M ⟶ N` Hom add), the
  standard move is to **reshape the goal with `change`/`show` to the bare composite form first**,
  then let the additive-functor lemmas fire.  This carrier-vs-`Hom` defeq friction is endemic to
  all `PresheafOfModules`/`ModuleCat` work in Mathlib; `change` (not a new lemma) is the idiom.
- **Project's path (recommended)**: the directive's hypothesised "defeq bridge" is correct and is
  literally `rfl`.  No standalone helper lemma is required — an inline `show … from rfl` suffices.
  The load-bearing step is the `change` that precedes it.
- **Gap**: identical to the Mathlib idiom.
- **Verdict**: PROCEED (thin, rfl-level bridge; no API change).

## Recommendation

`map_add'` closes outright with the following VERIFIED recipe (reduces the goal to `[]`,
`lean_multi_attempt` at DualInverse.lean:343):

```lean
· intro x y
  apply PresheafOfModules.hom_ext
  intro W
  -- LOAD-BEARING: `change … = _` reshapes BOTH sides so `Functor.map_add` can match the
  -- `(restrictScalars _).map (·)` application.  Without it (e.g. `simp only [add_app]`),
  -- `Functor.map_add` reports "pattern not found" even though the term displays identically.
  change (ModuleCat.restrictScalars _).map ((x + y).app _) ≫ _ = _
  rw [show (x + y).app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)))
        = x.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)))
          + y.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom))) from rfl,
      Functor.map_add, Preadditive.add_comp]
```

Why each piece: the inline `show … from rfl` is the `internalHomObjModule`-add ↦ `Hom`-add bridge
(rfl); `ModuleCat.restrictScalars φ` is `Additive` (verified) so `Functor.map_add` applies; the
codomain swap `dualUnitRingSwap` is post-composed, so `Preadditive.add_comp` distributes it.

**Generalisation**: the `change`-reshape front-half generalises to `map_smul'`, but the bridge
itself does NOT — `m • x` on the domain is the `homModule` post-composition action (`φ ≫ globalSMul`)
with the scalar at the `V`-level, NOT a pointwise `(β.app W m) • x.app W` (that naive `rfl` bridge
FAILS — verified).  `map_smul'` therefore needs the genuine smul argument: unfold the `homModule`
`smul` to `≫ globalSMul`, split with `comp_app`, evaluate via `globalSMul_hom_apply`, and intertwine
through `dualUnitRingSwap` (the presheaf shadow of `restrictScalarsRingIsoDualEquiv`'s `map_smul'`).
It is more than a defeq bridge, but the same `change (ModuleCat.restrictScalars _).map ((m • x).app _) ≫ _ = _`
reshaping is the correct first step (verified to apply).

The other sub-holes (`invFun`, `left_inv`, `right_inv`) are `Iso.inv_hom_id`/`hom_inv_id`
round-trips + down-set bijection; the add bridge does not bear on them (they are not additivity
obligations).  So the critic's "this recurs on every sub-hole" is only true for the `change`-reshape
pattern, which does recur and is cheap; the additive `rfl` bridge specifically recurs only where
additivity is at stake.

Net: PROCEED.  No refactor.  The design is Mathlib-aligned; ship the verified `map_add'` recipe and
build `map_smul'` from the `homModule.smul`/`globalSMul` definition with the same `change` opener.
