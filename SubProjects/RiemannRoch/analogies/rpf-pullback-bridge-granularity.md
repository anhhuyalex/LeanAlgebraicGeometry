# Analogy: what granularity must the `IsInvertible.pullback` bridge expose for the relative Picard functor's functoriality?

## Mode
api-alignment

## Slug
rpf-bridge

## Iteration
245

## Question
For the relative Picard functor `RelPicFunctor` / `PicSharp` on the `IsInvertible`
iso-class carrier, must the `IsInvertible.pullback` bridge be (A) a bare Prop
`IsInvertible M → IsInvertible (f^* M)` relying on Mathlib's existing pullback
pseudofunctor coherence (`pullbackComp`, `pullbackId`), or (B) must it additionally
expose the monoidal comparison iso `f^*(M⊗N) ≅ f^*M ⊗ f^*N` (and/or `pullbackComp`)
*as data* because the group-hom and functoriality fields cannot be assembled from
the bare Prop alone?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:168` — `IsInvertible M : Prop := ∃ N, Nonempty (tensorObj M N ≅ unit)`; the RPF carrier. Group law on iso-classes (`picSetoid`, L772), every axiom a `Nonempty(≅)`.
- `AlgebraicJacobian/Picard/RelPicFunctor.lean:208-377` — `PicSharp.addCommGroup` / `PicSharp` / `PicSharp.functorial` (the `AddMonoidHom` per morphism). Current bodies are dishonest placeholders (`const PUnit`, `0`) to be rewritten on the `IsInvertible` carrier.
- `AlgebraicJacobian/Picard/LineBundlePullback.lean:103-156` — `IsLocallyTrivial`; `IsLocallyTrivial.pullback` (axiom-clean chart-chase, the cheap unit-comparison template).

## Decisions identified

### Decision 1 (Q1 + Q2): is the bridge primitive a bare invertibility Prop, or the monoidal comparison ISO?

- **Mathlib idiom — the exact analogue exists.** `CommRing.Pic` is the iso-class
  Picard group (`Shrink (Skeleton (SemimoduleCat R))ˣ`), and Mathlib ships the
  full *functor* the project is reinventing:
  - `CommRing.Pic.mapAlgebra : Pic R →* Pic A` — `Mathlib/RingTheory/PicardGroup.lean:528`. **This is the precise analogue of `PicSharp.functorial`** (a group hom `[M] ↦ [base-change of M]` on iso-classes; project uses the additive `AddMonoidHom`/`AddCommGrpCat` packaging, Mathlib the multiplicative `MonoidHom`/`CommGrpCat` — same content).
  - `CommRing.Pic.mapRingHom : (R →+* S) → Pic R →* Pic S` — `PicardGroup.lean:554`.
  - `CommRing.Pic.functor : CommSemiRingCat ⥤ CommGrpCat` — `PicardGroup.lean:580` — the analogue of `PicSharp.presheaf`.

  **How the group-hom fields are actually built** (`mapAlgebra`, `PicardGroup.lean:528-534`):
  ```
  toFun  M    := .mk A (A ⊗[R] M)                       -- [M] ↦ [f^*M]
  map_one' := mk_eq_one_iff.mpr (free_iff_linearEquiv.mp _)  -- UNIT iso A⊗_R R ≅ A
  map_mul' _ _ := by rw [← mk_tensor, mk_eq_mk_iff]
                     refine ⟨ … ≪≫ₗ distribBaseChange R A ..⟩  -- TENSOR iso, as data
                     simp_rw [mk_tensor, mk_eq_self]
  ```
  The load-bearing datum in `map_mul'` is
  `TensorProduct.AlgebraTensorModule.distribBaseChange R A`
  (`Mathlib/LinearAlgebra/TensorProduct/Tower.lean`): a genuine **`≃ₗ`** (iso)
  `A ⊗_R (M ⊗_R N) ≅ (A ⊗_R M) ⊗_A (A ⊗_R N)` — i.e. exactly
  `f^*(M⊗N) ≅ f^*M ⊗ f^*N`. It is fed to `mk_eq_mk_iff`
  (`Pic.mk M = Pic.mk N ↔ Nonempty (M ≃ₗ N)`, `PicardGroup.lean:462`). The same
  `distribBaseChange` iso is *literally* the strong-monoidal tensorator
  `δ`/`μ` of `ModuleCat.extendScalars.Monoidal` (`extendScalars_δ`/`_μ`,
  `Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`). `map_one'`
  rests on the **unit** comparison iso `A ⊗_R R ≅ A` (via freeness).

  Decisive structural facts:
  1. The bare predicate "base change of an invertible module is invertible"
     (`Module.Invertible.instLocalizationLocalizedModule`, `PicardGroup.lean`,
     the localization-stability instance = the `IsInvertible.pullback` analogue)
     is used **only** to make `toFun M := .mk A (A ⊗ M)` typecheck (`mk` needs a
     `Module.Invertible` instance on its argument). It is **never** sufficient for
     `map_one'`/`map_mul'` — those consume the comparison **isos** as data.
  2. **No coherence square / pentagon / naturality is ever invoked.** `map_mul'`
     builds ONE linear equiv and hands it to `mk_eq_mk_iff`. The iso-class quotient
     washes out coherence — confirming [[ts-picard-direct-216]] (`mul_assoc := hC ⟨α⟩`).
     But it does NOT wash out **invertibility** of the comparison: `mk_eq_mk_iff`
     demands `Nonempty (M ≃ₗ N)`, an iso, not a map.
  3. The pullback **pseudofunctor** coherence (`pullbackComp`/`pullbackId`,
     present at the pin as `SheafOfModules.pullbackComp`/`pullbackId`,
     `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`) is the
     analogue of `mapAlgebra_comp_mapAlgebra`/`mapAlgebra_self`
     (`PicardGroup.lean:542,548`) — it feeds the **functor's** `map_comp`/`map_id`
     fields (`functor`, `PicardGroup.lean:583-584`), i.e. functoriality in the
     *morphism* `f`. Those too are ISOS (`cancelBaseChange`, `lid`) washed through
     `mk_eq_mk_iff`. Composition coherence is **orthogonal** to the monoidal-in-⊗
     comparison and cannot supply `map_add`.

- **Project's proposed path (option A)**: expose only the bare Prop
  `IsInvertible.pullback : IsInvertible M → IsInvertible (f^* M)` and hope the
  `AddMonoidHom` fields fall out of `pullbackComp`/`pullbackId`.
- **Gap**: **divergent-and-wrong.** The bare Prop is the *weakest* of the facts the
  functor needs and is in fact a downstream **corollary** of the comparison isos,
  not a peer: given `M ⊗ N ≅ 𝟙`,
  `f^*M ⊗ f^*N ≅ f^*(M⊗N) ≅ f^*𝟙 ≅ 𝟙`, so
  `pullbackTensorIso` + `pullbackUnitIso` ⊢ `IsInvertible.pullback` in ~3 lines.
  The reverse implication is false (a Prop carries no ⊗-comparison). `pullbackComp`/
  `pullbackId` give functoriality-in-`f`, never the ⊗-comparison `map_add` needs.
- **Cost of divergence**: if the bridge ships as the bare Prop, `PicSharp.functorial`'s
  `map_add` field is **unconstructible** — there is no term of type
  `f^♯(a+b) = f^♯ a + f^♯ b` derivable from `IsInvertible (f^*M)` + pseudofunctor
  coherence. The lane would harden a second dishonest placeholder (`functorial := 0`)
  exactly where the present one already sits, and the blueprint rewrite + prover round
  would chase a target that cannot close. The honest cost is paid once, in the
  comparison iso.
- **Verdict**: **ALIGN_WITH_MATHLIB** — the bridge primitive must be the monoidal
  comparison **iso** (existence form), mirroring `mapAlgebra`'s `distribBaseChange`-
  driven `map_mul'`. `IsInvertible.pullback` is a derived corollary, not the bridge.

### Decision 2 (Q3): does the group-hom follow from the comparison MAP (`pullbackTensorMap`) + iso-class washing?

- **Mathlib idiom**: `map_mul'` feeds `distribBaseChange` — an `≃ₗ` — to
  `mk_eq_mk_iff`, which requires `Nonempty (M ≃ₗ N)`. An equality of iso-classes is
  produced **only** by an iso.
- **Project's proposed path**: rely on the already-built comparison MAP
  `pullbackTensorMap : f^*M ⊗ f^*N → f^*(M⊗N)` (or its oplax reverse) + the
  quotient.
- **Gap**: **divergent-and-wrong.** A map that is not known to be an isomorphism does
  not yield `[f^*(M⊗N)] = [f^*M] + [f^*N]`. The iso-class quotient washes out
  *coherence*, not *invertibility*. Independently confirmed by the project's own
  negative result [[pullback-tensor]] / [[pullback-monoidal]]: the oplax `δ` is a map,
  not an iso (Γ(P¹,O(1)) = 0 kills "lax functors preserve invertibles"); promotion to
  an iso is genuine geometric content.
- **Cost of divergence**: same as Decision 1 — `map_add` is unconstructible from a
  bare map.
- **Verdict**: **ALIGN_WITH_MATHLIB** — the comparison must be promoted to an iso.
  For **invertible** `M,N` (the only case Pic touches) this promotion is the cheap
  chart-chase, not general strong monoidality (see Recommendation).

## Recommendation

Adopt **option B, in its precise refined form**. The `IsInvertible.pullback` *bridge*
this iter should NOT be the bare Prop; the load-bearing primitives are the two
comparison **isos**, exposed in existence form because the whole consumer is
iso-class-quotiented (project's `preimage_subgroup`/`picSetoid`, Mathlib's
`mk_eq_mk_iff`):

```
-- the distribBaseChange analogue — load-bearing for map_add
theorem pullbackTensorIso  …(f)(M N) : Nonempty (tensorObj (f^*M) (f^*N) ≅ f^*(tensorObj M N))
-- the A⊗_R R ≅ A analogue — load-bearing for map_zero
theorem pullbackUnitIso    …(f)      : Nonempty (f^*(unit) ≅ unit)
```

Then **derive** the bare Prop as a corollary (do not sorry it as a peer):
`IsInvertible.pullback hM := let ⟨N, ⟨e⟩⟩ := hM; ⟨f^*N, ⟨pullbackTensorIso.. ≪... using e, unit iso⟩⟩`.
`map_zero`/`map_add` of `PicSharp.functorial` come straight from `pullbackUnitIso` /
`pullbackTensorIso` fed to the `preimage_subgroup`-quotient soundness (the
`mk_eq_mk_iff` analogue). Coherence (naturality, pentagon, the strict
`pullbackComp`/`pullbackId` identities) is **not** needed as bridge data — it is
washed by the quotient, exactly as Mathlib's `map_mul'` never touches a coherence
square. For the **functor's** `map_id`/`map_comp` (functoriality in the test scheme),
use the existing Mathlib `SheafOfModules.pullbackId`/`pullbackComp` isos
(`PullbackContinuous.lean`) washed through the quotient — the `mapAlgebra_self`/
`mapAlgebra_comp_mapAlgebra` analogue.

**Cheapest honest realization of the two isos:** restrict the comparison to invertible
arguments (mirroring `Module.Invertible.instLocalizationLocalizedModule`, the
base-change-of-invertible-is-invertible stability — NOT a general tensorator). For
locally-trivial `M,N`, on a common trivializing cover both restrict to `unit`, so the
tensor comparison reduces to the **unit** comparison, which is already reachable today
by mirroring the axiom-clean `IsLocallyTrivial.pullback` chart-chase
(`LineBundlePullback.lean:156`, `pullbackObjUnitToUnit` glued over a cover; see
[[pullback-monoidal]] Phase 1/2). This is far cheaper than the general strong-monoidal
`pullbackObjTensorToTensor` and is the move Mathlib's invertibility-restricted
stability endorses.
