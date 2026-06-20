# Analogy: `pushforwardComp_lax_μ` — monoidality of `PresheafOfModules.pushforward` across composition

## Mode
api-alignment

## Slug
ana-pclm260

## Iteration
260

## Question
For the lone D3′ residual `pushforwardComp_lax_μ` (the lax tensorator `μ` of `pushforward ψ ⋙ pushforward φ`
equals the `μ` of the single `pushforward (φ ≫ F.op ◁ ψ)`): does Mathlib already have this coherence;
what is the canonical PROOF SHAPE; is `pushforwardComp = Iso.refl` enough to make it reduce to
`μ_natural`/`map_comp`; and if not, what is the most economical project-local construction?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:2143` — `pushforwardComp_lax_μ` (the open `sorry`).
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1124` — `presheafPushforwardLaxMonoidal` (the RHS's LaxMonoidal instance; `exact h` of `(pushforward₀OfCommRingCat F R₀ ⋙ restrictScalars φ').LaxMonoidal`).
- `AlgebraicJacobian/Picard/TensorObjSubstrate/PresheafInternalHom.lean:306,323` — `restrictScalarsLaxμ` / `restrictScalarsLaxMonoidal` (presheaf `restrictScalars` μ, **defined sectionwise** as the ModuleCat μ).
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1674` — `epsilonPresheafToSheafUnit` (the ε-twin; the working sectionwise template).

## Decisions identified

### Decision 1: Does Mathlib have "pushforward is (lax) monoidal pseudofunctorially"?

- **Mathlib idiom**: NONE. Mathlib's `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean`
  has **zero monoidal content** — `pushforward` is just `pushforward₀ F R ⋙ restrictScalars φ` (line 86),
  and `pushforwardComp φ ψ := Iso.refl` (line 135) is only the **underlying-functor** iso
  (`pushforward ψ ⋙ pushforward φ ≅ pushforward (φ ≫ whiskerLeft F.op ψ)`), with `pushforward_assoc`
  / `pushforward_comp_id` / `pushforward_id_comp` (lines 142–157) the pseudofunctor coherences — all
  about the *functors*, none about a *lax tensorator*. The lax-monoidal structure on
  `PresheafOfModules.pushforward` is **entirely project-built** (`presheafPushforwardLaxMonoidal`,
  resting on the project's `restrictScalarsLaxMonoidal`). So there is no Mathlib lemma "pushforward is
  monoidal across composition" to cite, and none of `restrictScalarsComp` / `extendScalarsComp` /
  `homEquiv_extendScalarsComp` proves it (those concern the change-of-rings *functors'* associativity,
  not the lax tensorator μ).
- **Project's path**: build `pushforwardComp_lax_μ` as a project-local supplement.
- **Gap**: NEEDS_MATHLIB_GAP_FILL — but a *small* one (the workhorse, `restrictScalars_μ_tmul`, is in Mathlib).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision 2: Is the proof a ~150-LOC `extendScalarsComp` change-of-rings build, or a short sectionwise reduction?

- **Mathlib idiom (the workhorse)**: `ModuleCat.restrictScalars_μ_tmul`
  (`Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean:116`):
  `μ (restrictScalars f) M₁ M₂ (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂`. The lax tensorator of `restrictScalars`
  is the **identity on pure tensors**. Combined with `pushforward₀OfCommRingCat F R`.Monoidal having
  `μIso := Iso.refl` (`Mathlib/.../Presheaf/PushforwardZeroMonoidal.lean:33`, so its μ is `𝟙`), and
  `Functor.LaxMonoidal.comp` being `@[simps]` (`Mathlib/CategoryTheory/Monoidal/Functor.lean:221`,
  giving `comp_μ : μ (F⋙G) X Y = μ G _ _ ≫ G.map (μ F X Y)`), **both μ's collapse, sectionwise on a
  pure tensor, to `m ⊗ₜ n`.** So the proof is a SHORT sectionwise tensor-induction, NOT a 150-LOC
  `extendScalarsComp`/`homEquiv_extendScalarsComp` build. The docstring's feared route (and the
  directive's Q1/Q2 candidates `extendScalarsComp`, `homEquiv_extendScalarsComp`) is a **red herring**:
  those are needed for change-of-rings *associativity isos*, never touched here.
- **Project's current path**: docstring (L2127–2142) predicts "~150-LOC ModuleCat change-of-rings
  coherence (`restrictScalarsComp` / `homEquiv_extendScalarsComp`)". This over-estimates by ~3×.
- **Gap**: divergent-with-cost (the project's own size/route estimate is wrong; following it would
  waste a prover dispatch building unnecessary `extendScalarsComp` machinery).
- **Verdict**: ALIGN_WITH_MATHLIB (use `restrictScalars_μ_tmul`; drop the `extendScalarsComp` plan).

### Decision 3 (directive Q3): Does `pushforwardComp = Iso.refl` reduce μ-equality to `μ_natural`/`map_comp`?

- **Answer: NO.** `pushforwardComp = Iso.refl` is a statement about the **underlying functor**
  (`pushforward ψ ⋙ pushforward φ` and `pushforward χ` are defeq as functors). But the two μ's are two
  **different `LaxMonoidal` instances on that (defeq-)same functor**: the LHS instance is the
  Lean-synthesized `Functor.LaxMonoidal.comp (pushforward ψ) (pushforward φ)` (CONFIRMED in the goal),
  the RHS instance is `presheafPushforwardLaxMonoidal (φ ≫ F.op ◁ ψ)`. Their agreement is genuine
  content, NOT a `μ_natural` consequence. EMPIRICALLY CONFIRMED: `rfl` fails even on a single pure
  tensor `m ⊗ₜ n` (because `restrictScalars`'s μ is built by adjunction transpose
  `rightAdjointLaxMonoidal`, equal-but-not-defeq to the identity — it only *equals* `m⊗ₜn` via the
  proven `restrictScalars_μ_tmul`). The `d3sq2b258` "rfl/short ext" prediction is correctly refuted.
- **Verdict**: PROCEED (Q3 answered NO; not the route).

## Recommendation

Build it as a SHORT sectionwise proof via Mathlib's `ModuleCat.restrictScalars_μ_tmul`, funnelled
through ONE project-local helper that unfolds the opaque `presheafPushforwardLaxMonoidal` μ. Do NOT
build `extendScalarsComp` machinery. The helper is necessary because the `presheafPushforwardLaxMonoidal`
instance is `exact h`-cast (not syntactic `comp`), so neither `simp [comp_μ]` nor a direct
`erw [restrictScalars_μ_tmul]` fires on `μ (pushforward _)` — and the direct `erw` **whnf-explodes**
(>200000 heartbeats, even with `respectTransparency false`), exactly the catastrophic-whnf hazard the
project's memory repeatedly flags. See the concrete recipe in the report (`task_results/...`).

## Empirical findings (iter-260, via `lean_multi_attempt` on the live goal)

1. `ext W x; induction x using TensorProduct.induction_on` SPLITS cleanly (zero / tmul / add). ✓
2. LHS instance is synthesized as `Functor.LaxMonoidal.comp (pushforward ψ) (pushforward φ)`; `simp only
   [Functor.LaxMonoidal.comp_μ]` UNFOLDS it to
   `μ(pushforward φ) (Pψ X)(Pψ Y) ≫ (pushforward φ).map (μ(pushforward ψ) X Y)`. ✓
3. The inner `μ(pushforward φ)`, `μ(pushforward ψ)`, and RHS `μ(pushforward χ)` all carry the
   `presheafPushforwardLaxMonoidal` instance and DO NOT unfold under `simp`/`comp_μ` (the `exact h`
   cast hides the `comp`). ← the central obstacle.
4. Direct `erw [ModuleCat.restrictScalars_μ_tmul]` on these → **whnf timeout** (>200000), even with
   `set_option backward.isDefEq.respectTransparency false in`. So a dedicated small-goal helper is
   mandatory; the explosion is from `erw` whnf-ing the heavy ambient term, not from the lemma itself.
5. `restrictScalarsLaxμ` (PresheafInternalHom.lean:306) defines the presheaf `restrictScalars` μ
   sectionwise (`app X := μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X)`), and its
   `.naturality` (lines 313–318) already closes with `erw [..., ModuleCat.restrictScalars_μ_tmul, ...]`
   under `respectTransparency false` — the proven in-file pattern the helper should mirror.
