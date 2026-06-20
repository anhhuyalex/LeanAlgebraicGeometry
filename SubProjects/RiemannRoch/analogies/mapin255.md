# Analogy: how to apply `δ_natural` when the oplax functor's domain ring is spelled non-canonically (`X.ringCatSheaf.obj` vs `X.presheaf ⋙ forget₂ CommRingCat RingCat`)

## Mode
api-alignment

## Slug
mapin255

## Iteration
255

## Question
`pullbackTensorMap_natural` (D1′, TensorObjSubstrate.lean L2004) is blocked: after
`simp only [pullbackTensorMap]`, applying `Functor.OplaxMonoidal.δ_natural (F := PresheafOfModules.pullback φ')`
fails with `failed to synthesize MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)`, because the
Mathlib monoidal instance is registered only on `X.presheaf ⋙ forget₂ CommRingCat RingCat`
(`Presheaf/Monoidal.lean:32,104-105`), which is DEFEQ-but-not-syntactic to `X.ringCatSheaf.obj`.
Rank fixes (A) light proof-side / (B) medium def retype / (C) heavy restatement.

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean`:L2004–2064 — `pullbackTensorMap_natural`, blocked δ-commutation (Square 2), sorry at L2064.
- `…`:L1210–1226 — `pullbackTensorMap` def; `let φ'` canonically ascribed at L1214-1215 but **zeta-inlined by `simp only`**.
- `…`:L1848 — `pullbackTensorMap_unit_isIso` (D2′), must stay green.

## Decisions identified

### Decision: how to spell `F` so `δ_natural`'s domain `MonoidalCategory` synthesizes

- **Mathlib idiom**: Mathlib's monoidal instance on `PresheafOfModules` keys on the **composite-functor
  spelling** `P ⋙ forget₂ CommRingCat RingCat` (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`,
  ~line 32 for the instance, 104-105 for the tensorator). Mathlib has no `.obj`-of-`Sheaf` spelling in
  its monoidal API at all — it works uniformly in the `⋙ forget₂` presentation. When a defeq spelling
  must be re-presented to trigger instance synthesis, the Mathlib-idiomatic device is a **local type
  ascription** (`show T from e` / `(e : T)`) on the value whose type drives the instance search — NOT a
  bundled extra instance on the alternate spelling (which would create a defeq-diamond the kernel
  rejects; this project already hit that with `ringCatSheaf.obj`-form monoidal instances, see
  [[ts-assoc-flatness-gap]] iter-217 "avoid local MonoidalCategory instances on ringCatSheaf.obj form").

- **Project's current path (the blocker)**: the iter-254 prover applied `δ_natural (F := Fp)` with `Fp`
  spelled `PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom`. The ring-hom `(Hom.toRingCatSheafHom f).hom`
  has source `X.ringCatSheaf.obj`, so `pullback`'s domain category is `PresheafOfModules X.ringCatSheaf.obj`,
  and the registered instance (on `⋙ forget₂`) never fires. The prover concluded "there is no place to
  inject the instance into δ_natural's domain-ring argument" and demanded a structural spelling-pin
  refactor (option C). **This conclusion is empirically FALSE** (see below).

- **Gap**: divergent-but-recoverable purely proof-side. No shipped-code misalignment that needs a refactor.

- **Verdict**: **PROCEED via option (A)** — re-present `F`'s ring-hom at the canonical spelling with a
  `show … from …` ascription inside the `δ_natural` application. Tested live (iter-255), it works.

## Recommendation

**Option (A), LIGHT, single PROVER lane, D2′ NOT at risk.** Replace the `sorry` at L2064 with:

```lean
erw [← Functor.OplaxMonoidal.δ_natural
  (F := PresheafOfModules.pullback
    (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
      from (Hom.toRingCatSheafHom f).hom))
  a.val b.val]
```

**Why it works** (verified with `lean_multi_attempt` at L2064, iter-255):
1. Building the term `δ_natural (F := pullback (show <canonical> from (Hom.toRingCatSheafHom f).hom)) a.val b.val`
   **elaborates** — the `show … from …` ascription forces `pullback`'s domain category to
   `PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)`, so the registered monoidal instance
   synthesizes. The instance hurdle is GONE. (This is the injection point the iter-254 prover missed:
   you don't inject the instance into `δ_natural` — you control the SPELLING of `F`'s defining ring-hom,
   and the domain category, hence the instance search key, follows from it.)
2. A plain `rw` then fails on a **syntactic** mismatch (the ascription pretty-prints as
   `have this := (Hom.toRingCatSheafHom f).hom; this`, not the bare hom in the goal), but `erw`'s
   reducible-defeq matching bridges the `have this := …; this` ⇝ bare-hom zeta gap and fires.
3. After the `erw`, Square 2 is done: the goal's `δ` moves from `M'.val N'.val` to `M.val N.val` and the
   `(Fp.map a.val ⊗ₘ Fp.map b.val)` factor appears — exactly the δ-commutation the proof needed.

**Blast radius**: zero. No definition changes → `pullbackTensorMap_unit_isIso` (D2′, L1848) and every
helper iso are untouched and stay green. The fix lives entirely inside `pullbackTensorMap_natural`.

**Remaining work after the erw** (already-closed helpers, same lane): Square 3 =
`sheafifyTensorUnitIso_hom_natural` (CLOSED), Square 4 = `pullbackValIso_hom_natural` (CLOSED) +
`tensorHom_comp_tensorHom`/bifunctoriality. The only friction is the cosmetic `have this := …; this`
wrapper the `erw` leaves in the goal; it is defeq to the bare hom and is dischargeable with
`show`/`change`/`dsimp only []`/`erw` exactly as the surrounding steps already do. No new helper lemma
is needed (stating one would re-hit the synth wall at the lemma's own type elaboration unless its type
also used the `show … from` functor, which buys nothing over the inline `erw`).

**On the deeper api-alignment question** (is `X.ringCatSheaf.obj` itself a misalignment worth fixing at
the source?): mildly yes, but NOT worth a refactor. Mathlib works uniformly in the `⋙ forget₂` spelling;
the project's `Hom.toRingCatSheafHom` leaks the `ringCatSheaf.obj` spelling into ring-hom sources, which
is why the canonical monoidal instance keeps needing re-presentation. A full option-(C) restatement of
`pullbackTensorMap` + `pullbackValIso` + the `sheafifyTensorUnitIso` family on the `⋙ forget₂` spelling
would remove the friction permanently but costs ~80–150 LOC and risks D2′ and several `IsIso` consumers
(`isIso_pullbackTensorMap_of_isIso_sheafifyDelta`, the unit-pair lemma). Since the targeted `show … from`
device is itself the Mathlib-idiomatic minimal re-presentation and clears the blocker in one line, the
source-level cleanup is DEFERRABLE, not required. Do (A) now.
