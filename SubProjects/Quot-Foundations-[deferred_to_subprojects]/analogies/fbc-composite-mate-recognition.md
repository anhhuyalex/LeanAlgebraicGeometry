# Analogy: composite-adjunction mate/conjugate recognition — turnkey lemma vs explicit adjL/adjR/β

## Mode
api-alignment

## Slug
fbc-composite-mate

## Iteration
044

## Question
Is there a Mathlib idiom that produces the composite-adjunction mate/conjugate recognition for
`base_change_mate_fstar_reindex_legs_conj` WITHOUT manually assembling the two ~5-layer composite
adjunctions `adjL`/`adjR` and a right-adjoint comparison `β`, then `(conjugateEquiv adjL adjR).injective`?
Specifically: does `Adjunction.comp` + `conjugateEquiv`/`mateEquiv` have a ready lemma
`conjugateEquiv (adj₁.comp adj₂) … = …` that telescopes a composite into single-pair factors
automatically; do the `CompositionIso.lean` lemmas remove the assembly; can `simp`-with-the-conjugate-set
do the recognition without an explicit `β`?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:1757-1848` — `_legs_conj`, the open `sorry` (sole gap = assembly).
- `…:1652-1724` — conj-2d `base_change_mate_reindex_conj_crossLayer`: ALREADY builds a **depth-2** `adjL`/`adjR`/`β` and closes with `unit_conjugateEquiv_symm`. This is the working template at one layer.
- `…:1625-1635` — conj-2b `base_change_mate_reindex_conj_pullbackLeg` = `conjugateEquiv_leftAdjointCompIso_inv`.
- `…:1736-1747` — conj-2c `base_change_mate_reindex_conj_pushforwardCollapse` (three Γ-collapses).

## Decisions identified

### Decision: is there a turnkey composite-mate recognition lemma (no adjL/adjR/β assembly)?

- **Mathlib idiom**: NO turnkey lemma exists; the entire `conjugateEquiv`/`leftAdjointCompIso` API is
  *parameterized by* `adjL`, `adjR`, `β` as **explicit mandatory inputs**, never inferred:
  - `conjugateEquiv adj₁ adj₂` (`Mates.lean`, `section conjugateEquiv`) takes the two adjunctions as
    explicit args; `.symm`/`.injective` are methods on that already-built equiv.
  - `Adjunction.comp` is **binary** — there is no n-ary `compₙ` and no `conjugateEquiv_compₙ`. A 5-layer
    `adjL` is `a.comp (b.comp (c.comp (d.comp e)))`, built by hand (mechanical).
  - `leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ := (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm τ`
    (`CompositionIso.lean:` def) and `leftAdjointCompIso … e := (conjugateIsoEquiv …).symm e.symm` —
    both take the right-adjoint comparison `τ`/`e` (= the project's `β`) as an explicit input.
  - So `β` is a **required argument**, not a byproduct. There is no `conjugateEquiv_telescope` that
    eats a bare section-level composite and hands back the recognition.

- **What DOES telescope a composite into single-pair factors** (the directive's literal sub-question),
  all in `Mates.lean`/`CompositionIso.lean`, each peeling exactly **one** `.comp` layer:
  - `conjugateEquiv_comp` (`Mates.lean`, `@[reassoc (attr := simp)]`):
    `conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β = conjugateEquiv adj₁ adj₃ (β ≫ α)` —
    fuses a **vertical** stack of conjugates over the SAME pair of categories (C,D). This is the
    workhorse simp lemma for chaining the legs.
  - `conjugateEquiv_symm_comp` (`Mates.lean`, `@[reassoc (attr := simp)]`):
    `(conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = (conjugateEquiv adj₁ adj₃).symm (α ≫ β)`.
    THIS is the lemma that lets the LHS composite be discharged as a **composition of the three already-proven legs** without ever materializing a single monolithic `β`.
  - `conjugateEquiv_whiskerLeft` / `conjugateEquiv_whiskerRight` (`Mates.lean`):
    `conjugateEquiv (adj.comp adj₁) (adj.comp adj₂) (whiskerLeft L τ) = whiskerRight (conjugateEquiv adj₁ adj₂ τ) R`
    (and dual). These peel ONE outer/inner functor layer off a `.comp` conjugate — the per-layer engine.
  - `conjugateEquiv_associator_hom` (`Mates.lean`): reassociates a depth-3 `.comp` conjugate.
  - `conjugateEquiv_leftAdjointCompIso_inv` (`CompositionIso.lean:82`, `@[simp]`):
    `conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂ (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).inv = e₀₁₂.hom`.
    The **direct composite-vs-single recognition** — but only fires if the LHS factor was *built* as
    `leftAdjointCompIso` (which conj-2b/conj-0′ already arrange via `pullbackComp_eq_leftAdjointCompIso`).
  - `leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm` / `₀₂₃_eq_conjugateEquiv_symm`
    (`CompositionIso.lean:130/140`): the ONLY genuine "telescope a multi-functor composite into one
    `(conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm (…)`" lemmas — but **hard-capped at
    depth 3** (4 categories C₀→C₁→C₂→C₃) and require each leg pre-encoded as `leftAdjointCompNatTrans`.
    Proof shape is the template: `obtain ⟨τ,rfl⟩ := (conjugateEquiv …).surjective τ` ×2 →
    `apply (conjugateEquiv …).injective` → one `simp [leftAdjointCompNatTrans, ← conjugateEquiv_whiskerLeft …]`
    (or a short `rw` chain through `_associator_hom`, `_whiskerRight`, `_comp`).

- **Project's current path**: build one monolithic depth-~5 `adjL`/`adjR`/`β` and `apply .injective`
  once. Resisted 7 iters because the raw section-level LHS (mix of `gammaPushforwardTildeIso.inv`,
  `Γ.map(unit ≫ pushforwardComp ≫ pushforwardCongr ≫ pushforwardComp.inv)`, `gammaPushforwardIso`,
  `restrictScalars.mapIso`) is not syntactically a single `conjugateEquiv` value, and the matching β is
  a large bespoke object.

- **Gap**: divergent-with-cost (one-shot monolith) vs the Mathlib idiom (factor-at-a-time via
  `conjugateEquiv_symm_comp`). The monolithic β is the multi-hundred-LOC trap; the factored route reuses
  the three axiom-clean legs and needs NO single β.

- **Cost of divergence**: assembling a depth-5 `β` as one term + proving its `conjugateEquiv.symm`
  identity is the bespoke build that has failed across iters 037–041. The factored route's cost is
  bounded: nested `.comp` for `adjL`/`adjR` (mechanical) + chaining the legs by `conjugateEquiv_symm_comp`.

- **Verdict**: NEEDS_MATHLIB_GAP_FILL is FALSE — Mathlib's API is sufficient; ALIGN_WITH_MATHLIB on the
  **factored** route. No turnkey lemma; `adjL`/`adjR` assembly is unavoidable but mechanical; a single
  monolithic `β` is NOT required — `conjugateEquiv_symm_comp` composes the per-leg comparisons.

### Decision: can `simp`-with-the-conjugate-set replace an explicit β construction?

- **Mathlib idiom**: YES for the *closing* step, NO for the *staging* step. Once the goal is phrased as
  an equation between `(conjugateEquiv …).symm (…)` values, the `@[reassoc (attr := simp)]` set
  (`conjugateEquiv_comp`, `conjugateEquiv_symm_comp`) + `conjugateEquiv_whiskerLeft/Right` +
  `conjugateEquiv_associator_hom` + `conjugateEquiv_leftAdjointCompIso_inv` closes it in one `simp`
  (exemplar: `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm`). But `simp` will NOT *create* the
  `adjL`/`adjR` nor recognize the raw section composite as a `.symm` value — that staging needs
  `Adjunction.comp_unit_app` (to split each composite unit, as conj-2d's `hunitL`/`hunitR` do) and the
  per-leg `leftAdjointCompIso`/`pullbackComp` encodings. So `simp` removes the β *algebra*, not the
  `adjL`/`adjR` *naming*.
- **Verdict**: PROCEED — the conjugate simp-set is the closer; explicit `adjL`/`adjR` (not a monolithic β) remain.

## Recommendation
**No turnkey composite-mate lemma exists; the explicit `adjL`/`adjR` naming is genuinely required, but a
monolithic depth-5 `β` is NOT.** The Mathlib-aligned target for a future build lane is the **factored**
route, generalizing conj-2d one layer at a time rather than rebuilding a 5-pair monolith:

1. **adjL/adjR (mechanical, unavoidable)** — define, mirroring conj-2d:1667-1670 but two layers deeper:
   `adjL = (tilde.adjunction (R:=R)).comp ((pullbackPushforwardAdjunction (Spec.map φ)).comp (pullbackPushforwardAdjunction (Spec.map ψ?)))`
   — i.e. nest `Adjunction.comp` over the layers `tilde⊣Γ_R`, `(Spec φ)^*⊣(Spec φ)_*`, `g'^*⊣g'_*`;
   `adjR = (extendScalars⊣restrict_ψ).comp (tilde.adjunction (R:=R'))` with the Spec-φ/Spec-ψ pieces.
   There is no shortcut — `Adjunction.comp` is binary; nest it. Cost: a few `set … with` lines.
2. **NO single β** — instead split the section-level LHS into per-layer conjugate factors with
   `conjugateEquiv_symm_comp` (and `Adjunction.comp_unit_app` to expose each composite unit, exactly as
   conj-2d's `hunitL`/`hunitR`), so the goal becomes a **composition of the three legs**:
   conj-2b (`conjugateEquiv_leftAdjointCompIso_inv`, pullback leg),
   conj-2c (Γ-collapses), conj-2d (`unit_conjugateEquiv_symm`, cross-layer). The extra `(Spec φ)_*`
   layer enters as a `conjugateEquiv_whiskerLeft`/`_whiskerRight` (the layer is a right-adjoint, so the
   "transport through `(Spec φ)_*`" is a whisker, NOT a positional naturality rewrite under the diamond).
3. **Recognition lemma to apply**: imitate `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm`
   (`CompositionIso.lean:140`) — `surjective` to lift each locked factor to a free preimage,
   `apply (conjugateEquiv adjL adjR).injective`, then `simp`/`rw` over
   `[conjugateEquiv_symm_comp, conjugateEquiv_comp, conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
   conjugateEquiv_associator_hom, conjugateEquiv_leftAdjointCompIso_inv, unit_conjugateEquiv_symm]`
   plus the three legs. NEVER positional `rw`/`simp`/`erw` under the `X.Modules` diamond — the diamond
   never bites because every lock-prone factor is a metavariable via `surjective … rfl`.

Concrete first move for the build lane: read `CompositionIso.lean:130-179` (the `₀₁₃`/`₀₂₃`/`_assoc`
template trio) and `Mates.lean` `conjugateEquiv_symm_comp`/`_whiskerLeft`/`_whiskerRight`; then in
`base_change_mate_fstar_reindex_legs_conj`, after the existing `rw [base_change_mate_codomain_read_legs_conj]`
+ `simp only [… gammaMap_pushforwardComp_inv_eq_id, gammaMap_pushforwardCongr_hom]`, introduce `adjL`/`adjR`
as in conj-2d and drive the LHS to `(conjugateEquiv adjL adjR).symm (…)` via `conjugateEquiv_symm_comp`,
discharging each factor by the matching leg. The verdict is (a): a precise Mathlib-aligned shape exists;
(b) is FALSE in its strong form (no multi-hundred-LOC monolith is forced) but TRUE in the weak form
(the `adjL`/`adjR` naming and per-layer chaining are genuinely required — there is no zero-assembly lemma).
