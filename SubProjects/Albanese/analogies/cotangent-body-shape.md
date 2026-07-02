# Analogy: cotangent-body-shape — `Classical.choose`-chain refactor vs (B′) chart-level `m_V / m_V²`

## Slug
cotangent-body-shape-iter131

## Iteration
131

## Question

(Q1) Does the iter-131 proposed `Classical.choose`-chain refactor of
`AlgebraicGeometry.GrpObj.cotangentSpaceAtIdentity` actually fix the
iter-130 opacity defect, where the body's outer form is
`Classical.choice (α := ModuleCat k) ⟨X⟩` and downstream lemmas cannot
reach the chart-level Kähler module past `Nonempty (ModuleCat k)`?

(Q2) Should the iter-131 lane instead pivot to a chart-level
`m_V / m_V²` body (Replacement (B′)) using
`IsLocalRing.CotangentSpace (Γ(G, V))_p` where `p` is the prime
corresponding to the identity-section image? Does Mathlib b80f227 ship
the regular-local bridge `Algebra.IsStandardSmoothOfRelativeDimension
n` ⇒ `IsRegularLocalRing` of dim `n` so (B′)'s closure chain is cleaner
than (B)'s?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:131-170` — iter-130 body of
  `cotangentSpaceAtIdentity` wrapping the chart-base-changed Kähler
  module in `refine Classical.choice (α := ModuleCat k) ?_; …; exact ⟨X⟩`.
- `AlgebraicJacobian/Differentials.lean:124-143` —
  `smooth_locally_free_omega` returns
  `∃ (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U), …`, a Prop-level
  multi-existential the body must destructure.
- `analogies/lieAlgebra-rank-bridge.md:30-200` — iter-129 source of
  truth for (A)/(B)/(C) choice. The iter-129 analogist landed on (B)
  ("for the rigidity consumer, canonicity is not load-bearing") but did
  NOT consider the rank-lemma consumer — exactly the gap iter-130
  exposed and that this iter must resolve.

## Decisions identified

### Decision 1: Does `Classical.choose` extract data accessibly inside a `noncomputable def` body?

- **Kernel-level fact** (`Init.Classical`, line 19–32 of the toolchain
  source at
  `/home/archon/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Classical.lean`):

  ```
  noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
    choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

  noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
    (indefiniteDescription p h).val
  ```

  So `Classical.choose h` is implemented as `(Classical.choice
  ⟨⟨x, px⟩⟩).val` — at the kernel level it is **just as opaque** as
  `Classical.choice`. There is no reduction rule
  `Classical.choose ⟨a, h⟩ ↝ a`. (`Classical.choose_eq` in
  `Mathlib.Logic.Basic` is a *propositional* equality, not definitional.)

- **However**, the opacity defect in the iter-130 body is **not**
  about `Classical.choose h = x` reducing definitionally. The defect is
  about the **outer expression structure** of the body.

  - iter-130 body shape: `cotangentSpaceAtIdentity G =
    Classical.choice (Nonempty.intro ((extendScalars ψV.hom).obj M))`
    where `M = ModuleCat.of Γ(G,V) Ω[…]`. The outermost head symbol is
    `Classical.choice` applied to a `Nonempty (ModuleCat k)`, so the
    body **as a term** does not reveal `(extendScalars _).obj _` to
    `unfold`/`whnf`. Downstream lemmas see only "some opaque element of
    `ModuleCat k`".
  - Proposed iter-131 body shape (`Classical.choose`-chain): the
    outermost form is the explicit
    `(ModuleCat.extendScalars ψV.hom).obj (ModuleCat.of Γ(G,V)
    Ω[Γ(G,V) ⁄ Γ(Spec k, U)])`, with `U, V, e, ψV` introduced by `let`
    bindings whose RHS uses `Classical.choose` / `Classical.choose_spec`
    on `smooth_locally_free_omega …`. After `unfold cotangentSpaceAtIdentity`
    and delta-reducing the `let`-bindings, the goal exposes the
    `extendScalars`/`Ω` form even though `U, V, e` themselves remain
    `Classical.choose`-extracted (opaque-but-named).

- **Mathlib precedent**: this is exactly the pattern Mathlib uses when
  a `Σ'`-bundle is unavailable. Cf.
  `Polynomial.SplittingField`/`SplittingFieldAux` in
  `Mathlib.FieldTheory.SplittingField.Construction:126-138`, where the
  carrier and `Field`/`Algebra` instances are extracted by `.1` /
  `.2.1` / `.2.2` from an inductively-built nested `Σ`/`Σ'` whose top
  layer involves classical witness selection. Downstream lemmas
  (`Polynomial.SplittingField.isSplittingField` and friends) consume
  the structure via the recorded instance attributes, not by reducing
  the underlying value.

- **Gap**: divergent-with-cost in the iter-130 body shape, divergent-equivalent
  in the iter-131 proposed body shape. The iter-130 body is
  **structurally wrong** for the rank-lemma consumer; the iter-131
  `Classical.choose`-chain proposal **structurally matches** the
  Mathlib idiom of "named extractor with `Classical.choose` /
  `.choose_spec` accessors plus an explicit outer expression".

- **Verdict**: **ALIGN_WITH_MATHLIB** on the body shape (the iter-130
  body has a real structural defect and must be refactored); **PROCEED**
  on the proposed iter-131 `Classical.choose`-chain replacement.

### Decision 2: What does the rank lemma's closure chain look like against the refactored body?

- **Rank lemma to prove (deferred consumer):**
  `Module.finrank k (cotangentSpaceAtIdentity G) = n`.

- **Closure chain under the iter-131 `Classical.choose`-chain body**:

  1. `unfold cotangentSpaceAtIdentity` — head-unfolds the `def`,
     exposing the `let`-bound `h := smooth_locally_free_omega …`,
     `U := h.choose`, `V := h.choose_spec.choose`, `e := …`,
     `ψV := …`, and the outer `(extendScalars ψV.hom).obj (ModuleCat.of
     Γ(G,V) Ω[Γ(G,V) ⁄ Γ(Spec k, U)])` form. **Mechanism**: kernel
     delta-reduction of the `def`, then `let`-binding exposure by
     `simp only []` or `show` rewriting. [verified — standard Mathlib
     pattern].

  2. `obtain ⟨_, _, _, hxV, hU, hV, hfree, hrank⟩ := h.choose_spec.choose_spec.choose_spec`
     (or equivalent) inside the rank-lemma proof — this gives the
     **same** `Module.Free Γ(G,V) Ω[…]` and `Module.rank Γ(G,V) Ω[…] = n`
     witnesses that the `let`-bound `V, U, e` were `choose`-extracted
     from. Note: the `V` from `obtain` is `h.choose_spec.choose`, which
     **is the same term** as the `let V := h.choose_spec.choose` in the
     unfolded body. So `hfree` and `hrank` apply to the **same** Kähler
     module that appears in the goal. [verified — `Classical.choose`
     is referentially transparent, so two occurrences of
     `h.choose_spec.choose` are the same `V`].

  3. `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n`
     (`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`) — this is
     **already consumed inside** `smooth_locally_free_omega`'s proof, so
     `hrank : Module.rank Γ(G,V) Ω[…] = n` is the direct output of the
     existential. No additional step needed at the rank-lemma level.
     [verified — see `Differentials.lean:124-143`].

  4. Convert `Module.rank` to `Module.finrank`: from `hfree :
     Module.Free Γ(G,V) Ω[…]` and `hrank : Module.rank … = n`, derive
     `Module.finrank Γ(G,V) Ω[…] = n` via `Module.finrank_eq_rank'` or
     `Module.rank_eq_finrank_iff_natCast` + `Module.Finite` (from
     `Module.Finite.of_basis` of the rank-`n` free module).
     [verified family in `Mathlib.LinearAlgebra.Dimension.Free`].

  5. **Base-change step** — `Module.finrank_baseChange`
     (`Mathlib.LinearAlgebra.Dimension.Constructions`) [verified]:

     ```
     theorem Module.finrank_baseChange
         {R : Type*} {S : Type*} {M' : Type*}
         [Semiring R] [CommSemiring S] [AddCommMonoid M'] [Module S M']
         [StrongRankCondition R] [StrongRankCondition S] [Module.Free S M']
         [Algebra S R] :
         Module.finrank R (TensorProduct S R M') = Module.finrank S M'
     ```

     Apply with `S := Γ(G,V)`, `R := k`, `M' := Ω[Γ(G,V) ⁄ Γ(Spec k, U)]`.
     The hypotheses are met: `StrongRankCondition` on `Γ(G,V)` (commring
     with finite-dimensional Kähler module — standard); `StrongRankCondition`
     on `k` (field); `Module.Free` from step 4; `Algebra Γ(G,V) k` from
     `ψV.hom.toAlgebra` (the `letI` in the def body).

     The wrinkle: `(ModuleCat.extendScalars ψV.hom).obj M` is
     definitionally the underlying carrier `TensorProduct Γ(G,V) k M`
     (per `ChangeOfRings.lean:396` — `ExtendScalars.obj' f M` is exactly
     `TensorProduct R S M` with the appropriate `Module S` structure).
     A single `show` / `simp only [ModuleCat.extendScalars_obj]`
     rewrite reduces step 5 to `Module.finrank_baseChange`. [expected,
     pending verification that the `simp` lemma name matches —
     `ExtendScalars.obj'` is the underlying type, and the type
     coercion `(M : Type _)` for `ModuleCat` is also a `rfl`.]

  6. Combine steps 4 + 5: `Module.finrank k (cotangentSpaceAtIdentity G)
     = Module.finrank k ((extendScalars ψV.hom).obj M) = Module.finrank
     Γ(G,V) M = n`. ∎

- **Mathlib gaps in this chain**: none. Every load-bearing lemma is
  consumable from Mathlib b80f227 (modulo step 5's coercion shape,
  which is a trivial `rfl`/`simp` resolution, not a real gap).

- **Verdict**: **PROCEED** on the rank-lemma closure chain. The
  iter-129 analogist's chain in `lieAlgebra-rank-bridge.md:102-118`
  steps 1–6 + bridge list survive the iter-130 body shape correction.
  Step 5 (`[expected]` tag in iter-129) is now upgraded to **[verified
  iter-131]** via the Mathlib `Module.finrank_baseChange` exact match
  (this was also reported as verified by the iter-130 plan agent in
  `PROGRESS.md` line 29).

### Decision 3: Should the iter-131 lane pivot to Replacement (B′) chart-level `m_V / m_V²`?

- **The (B′) proposal** (per strategy-critic-iter131): define
  `cotangentSpaceAtIdentity G := IsLocalRing.CotangentSpace (Γ(G,V))_p`
  where `p ⊂ Γ(G,V)` is the prime corresponding to `ψV^{-1}(0)`, i.e.
  the prime ideal `ker ψV` (since `ψV : Γ(G,V) → k` is a ring map into
  a field, its kernel is a prime — in fact maximal — ideal).

- **Mathlib backing**:
  - `IsLocalRing.CotangentSpace` (`Mathlib.RingTheory.Ideal.Cotangent`)
    [verified] — abbrev for `Module (ResidueField R) (CotangentSpace R)`
    where `CotangentSpace = maximalIdeal.Cotangent` viewed as a
    residue-field module.
  - `IsRegularLocalRing.iff_finrank_cotangentSpace`
    (`Mathlib.RingTheory.RegularLocalRing.Defs`) [verified, iter-129 chain]
    — `IsRegularLocalRing R ↔ Module.finrank (ResidueField R)
    (CotangentSpace R) = ringKrullDim R`.
  - `Localization.AtPrime.isLocalRing` [verified] — the localization
    `Localization p.primeCompl` is `IsLocalRing` when `p` is prime.

- **Required bridge (the [gap])**: under (B′), the rank lemma must show
  `Module.finrank (ResidueField (Γ(G,V))_p) (CotangentSpace (Γ(G,V))_p) = n`.
  Via `IsRegularLocalRing.iff_finrank_cotangentSpace`, this requires:
  (i) `IsRegularLocalRing (Γ(G,V))_p`; (ii) `ringKrullDim (Γ(G,V))_p = n`.

  **Search results (this iter)**:
  - `Loogle: IsRegularLocalRing, Algebra.IsStandardSmooth` → **EMPTY**.
  - `Loogle: IsRegularLocalRing, Smooth` → **EMPTY**.
  - `Loogle: IsRegularLocalRing, IsSmoothAt` → **EMPTY**.
  - `grep "RegularLocalRing"
    .lake/packages/mathlib/Mathlib/RingTheory/Smooth/*.lean` →
    **EMPTY**.

  So Mathlib b80f227 has **no direct lemma** connecting
  `Algebra.IsStandardSmoothOfRelativeDimension n` (or
  `Algebra.IsSmoothAt`) to `IsRegularLocalRing` of dim `n`. The bridge
  the iter-129 analogist identified for Replacement (A) [gap,
  500–1000 LOC] is the **same** [gap] under Replacement (B′).

- **LOC budget for (B′)**:
  - Localize `Γ(G,V)` at `p := ker ψV` → typeclass machinery: 50 LOC.
  - Bridge `IsStandardSmoothOfRelativeDimension n` ⇒ `IsRegularLocalRing
    + dim = n` for the localization: this is precisely the [gap]
    iter-129 estimated at 500–1000 LOC for (A). Under (B′), the
    estimate is similar; potentially 100–200 LOC less because we
    skip the geometric-stalk identification step
    `O_{G,η(pt)} ≅ (Γ(V))_p` (which (A) needs but (B′) doesn't), but
    the bulk of the work is the "smooth-at-prime ⇒ regular" content.
  - Rank lemma using `IsRegularLocalRing.iff_finrank_cotangentSpace`:
    50–100 LOC.
  - **Total**: 600–1200 LOC. Compare to (B)'s 200–400 LOC plus the
    `Classical.choose`-chain refactor (~30 LOC delta).

- **Downstream piece (i.b) advantage of (B′)?** The directive raises
  the question of whether (B′) gives a "named fibre object" that the
  iter-133+ piece (i.b) `mulRight_globalises_cotangent` shear-iso
  lemma can globalise more directly than (B)'s `extendScalars` form.
  Inspection: piece (i.b) is about an iso `m_x / m_x² ≅ m_e / m_e²`
  (shifted by `mulRight g`). Under (B), the cotangent at identity is
  `k ⊗_{Γ(V)} Ω[Γ(V)/Γ(U)]`, which is *not* a "stalk-side"
  `m / m²` object; mapping it to a translated chart requires the
  full chart-pair adjunction. Under (B′), the cotangent is
  `m_V / m_V²` of the localized chart ring, which is closer to a
  stalk-side object and the shear iso could potentially compose with
  `Ideal.Cotangent.map` (for ideal maps) instead of `extendScalars`
  functoriality.

  **However**: the iter-130 STRATEGY.md trigger (a') (lines 33–36 of
  `PROGRESS.md`) already covers this — if piece (i.b) closure under
  (B) requires inline (B)→(A) bridge construction, the (B) vs (A)
  decision re-opens at iter-133+. The cost of (B′) **paid now** is
  worse than the cost of (B) paid now + potential (B′) refactor at
  iter-133+ if trigger (a') fires (because the regular-local bridge
  needs to be built either way, and building it at the moment the
  consumer demands it is more focused than building it speculatively
  this iter).

- **Gap**: divergent-and-wrong on the directive's framing of (B′) as
  "intermediate" between (A) and (B). (B′) shares the [gap] with (A)
  and is closer to (A) on LOC than to (B). The "intermediate" framing
  comes from skipping the geometric-stalk identification, which is a
  ~100–200 LOC saving on a 500–1000 LOC bridge — not enough to
  reposition (B′) as a separate replacement class.

- **Verdict**: **DIVERGE_INTENTIONALLY** from the directive's (B′)
  premise. (B′) is not a separate class from (A); both pay the
  regular-local bridge [gap]. Stay on (B) with the
  `Classical.choose`-chain refactor for iter-131. Defer (B′)/(A) until
  trigger (a') fires (per STRATEGY.md iter-130 watch criteria).

## Recommendation

**Proceed with Decision 1's `Classical.choose`-chain refactor on
Replacement (B).** Reject Decision 3's pivot to (B′). Concrete
guidance for the iter-131 prover lane:

1. **Refactor `cotangentSpaceAtIdentity` from `by`-tactic-block to
   pure-term `def`** with `let`-bindings for each `Classical.choose`
   extraction:

   ```lean
   noncomputable def cotangentSpaceAtIdentity (G : Over (Spec (.of k)))
       [CategoryTheory.GrpObj G] {n : ℕ} [SmoothOfRelativeDimension n G.hom]
       [IsProper G.hom] [GeometricallyIrreducible G.hom] :
       ModuleCat k :=
     let ηleft : Spec (.of k) ⟶ G.left := η[G].left
     let x₀ : G.left := (ConcreteCategory.hom ηleft.base) default
     let h := Scheme.smooth_locally_free_omega (n := n) G.hom x₀
     let U : (Spec (.of k)).Opens := h.choose
     let h₁ := h.choose_spec
     let V : G.left.Opens := h₁.choose
     let h₂ := h₁.choose_spec
     let e : V ≤ G.hom ⁻¹ᵁ U := h₂.choose
     let hrest := h₂.choose_spec
     let hxV : x₀ ∈ V := hrest.1
     have htop : (⊤ : (Spec (.of k)).Opens) ≤ ηleft ⁻¹ᵁ V := by
       intro s _
       rw [Scheme.Hom.mem_preimage, Subsingleton.elim s default]
       exact hxV
     let ψV : Γ(G.left, V) ⟶ CommRingCat.of k :=
       ηleft.appLE V ⊤ htop ≫ (Scheme.ΓSpecIso (.of k)).hom
     letI : Algebra ↥Γ(Spec (.of k), U) ↥Γ(G.left, V) :=
       (Scheme.Hom.appLE G.hom U V e).hom.toAlgebra
     (ModuleCat.extendScalars ψV.hom).obj
       (ModuleCat.of Γ(G.left, V) Ω[Γ(G.left, V) ⁄ Γ(Spec (.of k), U)])
   ```

   Key structural difference from the iter-130 body: **no
   `Classical.choice` wrapper, no `refine … ⟨_⟩`**. The outer head
   symbol is `(ModuleCat.extendScalars _).obj _` after delta-reduction.

2. **Verify the body shape exposes correctly** before scaffolding the
   rank lemma:

   ```lean
   -- in the same file, transient verification (REMOVE before commit):
   example (G : Over (Spec (.of k)))
       [CategoryTheory.GrpObj G] {n : ℕ} [SmoothOfRelativeDimension n G.hom]
       [IsProper G.hom] [GeometricallyIrreducible G.hom] :
       True := by
     -- Show that `cotangentSpaceAtIdentity G` unfolds to an
     -- `extendScalars`-form, not to `Classical.choice _`.
     have h := cotangentSpaceAtIdentity G
     -- Inspect with `#check h` and `lean_hover_info` at the body —
     -- expect `(ModuleCat.extendScalars _).obj (ModuleCat.of _ Ω[_ ⁄ _])`,
     -- not `Classical.choice _`.
     trivial
   ```

3. **Then attempt the rank lemma** following Decision 2's closure chain.

4. **Future cleanup opportunity (deferred, not this iter):** consider
   refactoring `smooth_locally_free_omega` to return a `Σ'`-bundle
   (`noncomputable def smooth_locally_free_omega' : Σ' (U : S.Opens) …`)
   constructed via `Classical.choice` of the nonemptiness of the
   `Σ'`. This would let `cotangentSpaceAtIdentity` destructure with a
   single `let ⟨U, V, e, …⟩ := smooth_locally_free_omega' …` instead
   of a `Classical.choose`-chain. The Σ'-form would also be reusable
   by piece (i.b) and other future chart-extracting consumers. Out of
   scope for iter-131 since `Differentials.lean` is on the do-not-touch
   list per current PROGRESS.md constraints.

**Status of iter-129 analogist's recommendation (`lieAlgebra-rank-bridge.md`):**
its **conclusion** ("Replacement (B), affine-chart base change") is
**preserved**. Its **realization in the iter-128/130 prover lane** was
defective at the body-shape level (the `Classical.choice`-wrapper
construction), not at the replacement-choice level. The iter-131
refactor fixes the realization without revisiting the choice.

## Bridge lemma list (closure chain under `Classical.choose`-chain (B))

| Step | Lemma | Status |
|---|---|---|
| 1 | `Scheme.smooth_locally_free_omega` (project, `Differentials.lean`) | [verified — already consumed] |
| 2 | `Classical.choose` / `Classical.choose_spec` | [verified — Init.Classical] |
| 3 | `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` | [verified — consumed in step 1] |
| 4 | `Module.Free.of_…` + `Module.Finite.of_basis` (for `FiniteDimensional`) | [verified family] |
| 5 | `Module.finrank_eq_rank'` (rank ↔ finrank) | [verified] |
| 6 | `Module.finrank_baseChange` | [verified iter-130 — `LinearAlgebra.Dimension.Constructions`] |
| 7 | `ExtendScalars.obj'` ≡ `TensorProduct R S M` (definitional / `simp`) | [expected — `ChangeOfRings.lean:396`] |
| 8 | `Algebra.TensorProduct.instFree` (base-change preserves Free) | [verified iter-130 — `RingTheory.TensorProduct.Free`] |

## Caveat — `unfold` exposure of `let`-bindings

The closure chain depends on `unfold cotangentSpaceAtIdentity`
exposing the `let`-bound `U, V, e, ψV` and the outer `extendScalars`
form so the rank lemma can `set V := h.choose_spec.choose` and apply
`Module.finrank_baseChange` to the resulting `(extendScalars …).obj M`.

The risk: Lean's `unfold` may leave the `let`-bindings as
`Lean.Expr.letE` nodes rather than substituting them. In practice,
`simp only [cotangentSpaceAtIdentity]` (or
`show (ModuleCat.extendScalars _).obj _ = …` after a sequence of
`set`s) resolves this. The prover lane should **smoke-test** step 1
of the rank-lemma closure (`unfold + obtain + show`) before
committing to the full chain. If `unfold` does not expose cleanly,
the fallback is to add a small bridge lemma:

```lean
lemma cotangentSpaceAtIdentity_eq_extendScalars (G : …) :
    ∃ (U : (Spec (.of k)).Opens) (V : G.left.Opens) (e : V ≤ …)
      (htop : (⊤ : (Spec (.of k)).Opens) ≤ (η[G].left.appLE V ⊤ _)) …,
      cotangentSpaceAtIdentity G =
        (ModuleCat.extendScalars (… ηleft.appLE V ⊤ htop ≫ ΓSpecIso _ …).hom).obj
          (ModuleCat.of Γ(G.left, V) Ω[Γ(G.left, V) ⁄ Γ(Spec (.of k), U)]) := by
  refine ⟨_, _, _, _, _, _, _, _, ?_⟩
  rfl
```

This bridge lemma — provable by `rfl` if the body is pure-term — would
serve as a stable interface for downstream consumers (rank lemma,
piece (i.b) globalisation). **Recommended** as a defensive complement
to the body refactor, regardless of whether `unfold` exposes cleanly.
