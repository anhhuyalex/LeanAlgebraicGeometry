# Analogy: `IsBaseChange.of_equiv` path + 5-step Tilde-isoTop Mathlib alignment for Lane F

## Mode
api-alignment

## Slug
lane-f-isbasechange

## Iteration
189

## Question

(from iter-189 directive) Three sub-questions:

1. Is `IsBaseChange.of_equiv` the correct Mathlib API path for proving
   `IsBaseChange e (pullback_app_isoTensor_baseMap g N e)` at Lane F, or
   should the project switch to `IsBaseChange.of_lift_unique` or a
   different constructor?
2. What is the cleanest Mathlib-aligned recipe for the `Nonempty Σ-pair`
   signature of `pullback_app_isoTensor_baseMap_sectionLinearEquiv`?
3. What are the Mathlib lemmas behind each of the 5 steps of the Tilde-
   isoTop route (Steps 1 = `N|_V ≅ tilde Γ(N,V)`; 2 = pullback-tildeIso;
   3 = `hU.isoSpec` transport; 4 = `tilde.isoTop`; 5 = adjunction-unit
   naturality)?

Verdict needed: (A) STRUCTURAL OK / (B) STRUCTURAL ALIGN / (C) STRUCTURAL
BLOCKED.

## Project artifact(s)

- `AlgebraicJacobian/Picard/QuotScheme.lean:597-649` —
  `pullback_app_isoTensor_baseMap_sectionLinearEquiv` (iter-188 NAMED
  helper, body = typed `sorry`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:651-695` —
  `pullback_app_isoTensor_baseMap_isBaseChange` (iter-188 axiom-clean
  body using `IsBaseChange.of_equiv`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:543-571` —
  `pullback_tildeIso` (Step-2 typed-sorry pin).
- `AlgebraicJacobian/Picard/QuotScheme.lean:573-595` —
  `pushforward_isQuasicoherent` (Stacks 01XJ, typed-sorry pin).
- Pre-existing analogy: `analogies/quotscheme-isbasechange-tilde.md`
  (iter-187 verdict).

## Mathlib precedents examined (b80f227)

| Mathlib symbol | Location | What it gives |
|---|---|---|
| `IsBaseChange.of_equiv` | `Mathlib/RingTheory/IsTensorProduct.lean:394` | `(e : S ⊗[R] M ≃ₗ[S] N) → (∀ x, e (1 ⊗ₜ x) = f x) → IsBaseChange S f` |
| `IsBaseChange.of_lift_unique` | same file:428 | takes universal property `∀ Q [...], ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, ...` |
| `IsBaseChange.ofEquiv` (capital E) | same file:473 | `(e : M ≃ₗ[R] N) → IsBaseChange R e.toLinearMap` — only for the trivial `R → R` base change |
| `IsBaseChange.iff_lift_unique` | same file:461 | the iff version of `of_lift_unique` |
| `TensorProduct.isBaseChange` | same file:363 | `IsBaseChange S (TensorProduct.mk R S M 1)` — the canonical witness |
| `IsBaseChange.equiv` | same file:375 | `IsBaseChange S f → S ⊗[R] M ≃ₗ[S] N` — the consumer used by `pullback_app_isoTensor_isBaseChange.equiv.symm` |
| `AlgebraicGeometry.tilde.isoTop` | `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:177` | `M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤)` |
| `AlgebraicGeometry.tilde.adjunction` | same file:279 | `tilde.functor R ⊣ moduleSpecΓFunctor`; unit is `IsIso` (instance at 307) |
| `AlgebraicGeometry.tilde.fullyFaithfulFunctor` | same file:312 | `tilde` is fully faithful |
| `AlgebraicGeometry.isIso_fromTildeΓ_iff` | same file:340 | `IsIso M.fromTildeΓ ↔ essImage tilde M` |
| `AlgebraicGeometry.isIso_fromTildeΓ_of_presentation` | same file:398 | `(M : (Spec R).Modules).Presentation → IsIso M.fromTildeΓ` |
| `SheafOfModules.IsQuasicoherent` | `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249` | typeclass: `Nonempty (QuasicoherentData M)` (∃ cover + presentations on EACH cover element) |
| `SheafOfModules.QuasicoherentData.presentation` | same file:208 | per-cover-element presentation; NO direct extraction on a specific affine open V |
| `AlgebraicGeometry.IsAffineOpen.isoSpec` | `Mathlib/AlgebraicGeometry/AffineScheme.lean:380` | `U ≅ Spec Γ(X, U)` for `U` affine |
| `AlgebraicGeometry.IsAffineOpen.fromSpec` | same file:414 | `Spec Γ(X, U) ⟶ X` (open immersion) |

## Decisions identified

### Decision 1: `IsBaseChange.of_equiv` vs `of_lift_unique` vs `ofEquiv`

- **Mathlib idiom**: For "I have an explicit equiv `S ⊗[R] M ≃ₗ[S] N`
  and a 1-tensor intertwining property", the canonical constructor is
  `IsBaseChange.of_equiv` (`IsTensorProduct.lean:394`). The 1-tensor
  intertwining `∀ x, e (1 ⊗ₜ x) = f x` is exactly the data needed.

  `IsBaseChange.of_lift_unique` is for the *universal-property* path:
  you must produce, for every target `Q`, a unique extension of every
  `R`-linear `M → Q` to an `S`-linear `N → Q`. That is structurally
  harder to discharge when the equiv is constructed concretely on the
  Spec side.

  `IsBaseChange.ofEquiv` (capital E) only handles `e : M ≃ₗ[R] N`
  (same scalar ring) — gives `IsBaseChange R e.toLinearMap`. Inapplicable
  to Lane F's `R = Γ(X,V) → S = Γ(Y,U)` setup.

- **Project's current path** (`QuotScheme.lean:672-695`): produces a
  `Nonempty {f : Γ(X,V) ⊗ Γ(N,V) ≃ₗ[Γ(Y,U)] Γ((pullback g).obj N, U) //
   ∀ x, f (1 ⊗ₜ x) = pullback_app_isoTensor_baseMap g N e x}` via the
  named helper, then dispatches `IsBaseChange.of_equiv equiv hApp`.

- **Gap**: identical. The project's path is exactly the Mathlib idiom.

- **Verdict**: **PROCEED** — `IsBaseChange.of_equiv` is the correct API
  path. The other constructors are structurally heavier or inapplicable.

### Decision 2: `Nonempty Σ-pair` packaging idiom

- **Mathlib idiom**: Mathlib has no `LinearEquiv.intertwines` predicate.
  The closest idioms are:
  (a) Return data + Prop as TWO declarations (a `noncomputable def`
      producing the equiv, a `theorem` recording the intertwining).
  (b) Return `∃ f : LinearEquiv ..., ∀ x, ...` (a Prop with a Type-valued
      witness — perfectly legal since `LinearEquiv` is a `Type`, not
      `Prop`).
  (c) Return `Nonempty {f : LinearEquiv // ∀ x, ...}` — the project's
      current choice. Definitionally a heavier wrapping of (b).

- **Project's current path**: option (c). Consumer in
  `pullback_app_isoTensor_baseMap_isBaseChange` (L691) unpacks via
  `obtain ⟨equiv, hApp⟩ := ...` then feeds into `IsBaseChange.of_equiv`.

- **Gap**: divergent-equivalent. (c) and (b) are interchangeable; (c)
  is mildly noisier (an extra `Subtype.mk` layer when constructing).
  Mathlib leans toward (b) for pure-existence statements (`∃ e, ...`).
  Once the helper body is closed, the natural endpoint is *not* (b)
  or (c) but (a): a `noncomputable def` for the equiv + a `simp` lemma
  for `(1 ⊗ₜ x) = baseMap x`. But while the body is a typed sorry,
  packaging as `Nonempty` (which only asserts inhabitedness, not
  computability) is the right hygiene.

- **Verdict**: **PROCEED** with current `Nonempty {f // ...}` packaging.
  Optionally consider switching to bare `∃ f, ...` for syntactic
  parsimony (saves ~1 LOC in consumer obtain pattern). NOT a blocker.

### Decision 3: 5-step Tilde-isoTop Mathlib lemmas per step

| Step | Project description | Mathlib lemma(s) at b80f227 | Status |
|---|---|---|---|
| 1 | `N\|_V ≅ tilde Γ(N, V)` on `Spec Γ(X, V)` | Composition: `isIso_fromTildeΓ_iff` (`Tilde.lean:340`) ↔ `essImage tilde`; OR `isIso_fromTildeΓ_of_presentation` (`Tilde.lean:398`) from a `Presentation`. The "extract a presentation of `(N\|_V).overSpec` from `[N.IsQuasicoherent]`" sub-step is a **Mathlib gap** (Stacks 01I8: QC ⟺ tilde on every affine open). `IsQuasicoherent` only supplies a cover + presentations on COVER elements (`Quasicoherent.lean:208`), not on a chosen affine open `V`. | NEEDS_MATHLIB_GAP_FILL |
| 2 | Pullback via `Spec.map φ`: `(pullback (Spec.map φ)).obj (tilde M) ≅ tilde (B ⊗_A M)` | None at b80f227. Direct LSP searches (`pullback.*tilde`, `tilde.*pullback`, `baseChange.*tilde`) return zero matches. Project pin: `pullback_tildeIso` (Stacks 01HQ / 0BJ8). | NEEDS_MATHLIB_GAP_FILL (project pin in place) |
| 3 | Transport via `hU.isoSpec` back to `U`-sections | Combines `IsAffineOpen.isoSpec` (`AffineScheme.lean:380`), `IsAffineOpen.fromSpec` (`AffineScheme.lean:414`), and "module-pullback along an open immersion is restriction" — the LAST piece is a **Mathlib gap**: there is no `Scheme.Modules.pullback_of_openImmersion_iso_restriction` lemma at b80f227. The conceptual content is that `Scheme.Modules.pullback U.ι ≅ Scheme.Modules.restrictionToOpen U`. | NEEDS_MATHLIB_GAP_FILL (no project pin yet) |
| 4 | Evaluate at `⊤` via `tilde.isoTop` | `AlgebraicGeometry.tilde.isoTop` (`Tilde.lean:177`). **MATHLIB HAS.** | OK |
| 5 | Naturality of adjunction unit (1-tensor intertwining) | `AlgebraicGeometry.tilde.adjunction` (`Tilde.lean:279`) + `IsIso (tilde.adjunction.unit)` instance (`Tilde.lean:307`). The specific compatibility with `pullback_app_isoTensor_unitAtV` is project-side glue (~20-40 LOC). | OK (Mathlib supplies the adjunction; specific intertwining is project glue) |

- **Verdict per step**:
  - Step 4: **PROCEED** — Mathlib lemma in place.
  - Step 5: **PROCEED** — Mathlib adjunction in place; intertwining is
    project glue (no Mathlib gap; just naturality bookkeeping).
  - Steps 1, 2, 3: **NEEDS_MATHLIB_GAP_FILL**. Of these, Step 2 has a
    project pin (`pullback_tildeIso`). Steps 1 and 3 currently do NOT
    have separate pins — their substantive content is bundled into the
    body of `pullback_app_isoTensor_baseMap_sectionLinearEquiv`.

### Decision 4: Pin Steps 1 and 3 as separate typed sorries (refactor)

- **Mathlib idiom**: Mathlib's pattern for substantive missing
  infrastructure is one named declaration per Stacks tag, so future
  porting-to-Mathlib lands one PR per tag.

- **Project's current path**: All three Mathlib gaps (Steps 1, 2, 3)
  are conceptually independent, but only Step 2 is split out. Steps 1
  and 3 are buried inside `_sectionLinearEquiv`'s body sorry, making
  the `K=4 iters / 9→11 sorry creep / 6 helpers / PARTIAL×4` STUCK
  pattern (per iter-188 progress-critic) hard to break: the prover
  cannot make progress on `_sectionLinearEquiv` because closing it
  requires *three* substantive Stacks lemmas, only ONE of which has a
  name to put in scope.

- **Gap**: divergent-with-cost. Cost: provers iterate on the bundled
  helper without a way to localize which Stacks gap is the residual
  obstruction; the typed-sorry budget keeps growing without progress.

- **Verdict**: **ALIGN_WITH_MATHLIB** — split out Step 1 and Step 3 as
  separately-named typed-sorry pins, parallel to `pullback_tildeIso`
  for Step 2. After this refactor, the body of `_sectionLinearEquiv`
  becomes pure compositional glue with no internal Mathlib gaps, and
  prover work can focus on the three named pins independently.

## Recommendation

**iter-189 blueprint + prover dispatch for Lane F**:

1. **Confirm**: the `IsBaseChange.of_equiv` API path taken in iter-188
   is correct. No pivot needed. The structural choice is the right
   Mathlib idiom. (Decisions 1, 2.)

2. **Refactor (high priority)**: split out two new typed-sorry pins
   in `Picard/QuotScheme.lean`, parallel to the existing
   `pullback_tildeIso`:

   - `tildeIso_of_isQuasicoherent_isAffineOpen` (Step 1):
     given `[N.IsQuasicoherent]` and `hV : IsAffineOpen V`, produce
     `Nonempty (N|_V ≅ tilde Γ(N, V) /* on Spec Γ(X, V) */)`.
     Stacks 01I8 content. ~20-40 LOC body.

   - `pullback_of_openImmersion_iso_restrict` (Step 3):
     given an open immersion `j : U ⟶ X` (specifically `U.ι`), produce
     `Nonempty (Scheme.Modules.pullback j ≅ Scheme.Modules.restrictionToOpen U)`,
     or equivalently a section-level naturality lemma packaging the
     `hU.isoSpec` transport. Stacks gap. ~30-50 LOC body.

3. **After the refactor**, the body of `_sectionLinearEquiv` becomes
   pure glue: chain Step 1 + Step 2 (`pullback_tildeIso`) + Step 3
   transport + Step 4 (`tilde.isoTop`) + Step 5 (naturality), using
   `LinearEquiv.trans`. Estimated ~50-80 LOC of glue. The single typed
   sorry on `_sectionLinearEquiv` then evaporates — its body closes
   axiom-clean given the three named-pin Mathlib gaps.

4. **Blueprint expansion** (`Picard_QuotScheme.tex`): add Lean-4-
   friendly decomposition matching the three named pins. The blueprint
   currently has `def:pullback_app_isoTensor_sigma` as a plan-phase pin;
   expand it to explicitly enumerate the three Mathlib-gap steps and
   the two Mathlib-supplied steps (4 & 5).

5. **Do NOT** switch to `IsBaseChange.of_lift_unique`. The universal-
   property hypothesis would require the same Mathlib gaps (no shortcut)
   AND introduce an extra layer of `∃!` bookkeeping. The project's
   `of_equiv` path is strictly cleaner.

## Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| 1. `IsBaseChange.of_equiv` API path | PROCEED (identical to Mathlib idiom) | informational |
| 2. `Nonempty Σ-pair` packaging | PROCEED (divergent-equivalent; bare `∃ f, ...` slightly cleaner but not a blocker) | informational |
| 3. 5-step Tilde route — Steps 4, 5 | PROCEED (Mathlib supplies the lemmas) | informational |
| 3. 5-step Tilde route — Steps 1, 2, 3 | NEEDS_MATHLIB_GAP_FILL (Step 2 has a project pin; Steps 1 & 3 do NOT) | high |
| 4. Pin Steps 1 and 3 separately | ALIGN_WITH_MATHLIB (refactor) | critical (unbundles the STUCK helper) |

**Overall verdict**: **(A) STRUCTURAL OK** with a critical refactor
recommendation. The `IsBaseChange.of_equiv` choice is structurally
correct and does NOT need a pivot. The reason iter-188's helper has
been STUCK across 4 iters is *not* because the API path is wrong, but
because three independent Mathlib gaps are bundled into one named
helper, leaving provers without separate targets. Pinning Steps 1 and
3 separately (parallel to Step 2's existing `pullback_tildeIso` pin)
breaks the STUCK pattern and makes the `_sectionLinearEquiv` body
axiom-clean glue.
