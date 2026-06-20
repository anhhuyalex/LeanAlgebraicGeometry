# Analogy: proper-Γ flat-base-change for constants_integral_over_base_field step (e)

## Mode
api-alignment

## Slug
step-e-iter148

## Iteration
148

## Question

Does Mathlib have the proper-scheme Γ-flat-base-change statement
`Γ(X, ⊤) ⊗_k \bar k ≃ Γ(X_{\bar k}, ⊤)` (for `X / Spec k` proper,
geometrically irreducible, reduced, smooth), in any form that could be
re-exported, specialised, or alias'd to discharge step (e) of the
iter-147 closure chain for `constants_integral_over_base_field`?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/ChartAlgebra.lean:220–294` —
  `constants_integral_over_base_field` declaration body, with step (e)
  occurring inside the structured-`sorry` (a)–(g) closure chain
  documented in the comment block at 251–293.

## Decisions identified

### Decision A: Does Mathlib already have proper-Γ-flat-base-change?

- **Mathlib idiom**: There is **no Mathlib idiom for this statement**.
  Searches across:
  - `Mathlib.AlgebraicGeometry.IsBaseChange` — *no such file*; the
    `IsBaseChange` predicate (`Mathlib.RingTheory.IsTensorProduct`)
    lives at the algebra layer and has no scheme-level proper-pushforward
    counterpart.
  - `Mathlib.AlgebraicGeometry.Cohomology.*` — *no such directory*.
    `Mathlib.AlgebraicGeometry.Sites.ElladicCohomology` covers the
    site-cohomology basis for étale topology and `CategoryTheory.Sites.
    SheafCohomology.{Basic, Cech, MayerVietoris}` give generic
    site-level cohomology, but none of these connect to `Γ(Scheme)` +
    base-change-along-flat for proper morphisms.
  - `Mathlib.AlgebraicGeometry.Morphisms.{Proper, Flat,
    UniversallyClosed}` — `IsProper` (`Proper.lean:42`),
    `Flat.isStableUnderBaseChange` (`Flat.lean`), and
    `isField_of_universallyClosed` /
    `finite_appTop_of_universallyClosed` (`Proper.lean:143, 154`) are
    all present, but no theorem of the form
    `Γ(X_T, ⊤) ≃ Γ(X, ⊤) ⊗_R T`.
  - `Mathlib.AlgebraicGeometry.Pullbacks` —
    `pullbackSpecIso` (`Pullbacks.lean:703`) gives
    `pullback (Spec.map (alg R S)) (Spec.map (alg R T)) ≅ Spec (S ⊗[R] T)`
    in the **affine** case only.
  - `Mathlib.AlgebraicGeometry.Modules.{Presheaf, Sheaf}` —
    `Scheme.Modules.pullback`, `Scheme.Modules.pushforward` exist as
    functors, but no theorem identifying `π_* O_X` under base change for
    proper `π`.
  - `Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1` /
    `Mathlib.Algebra.Homology.LocalCohomology` — generic algebraic
    homology, no scheme-level base-change interface.
  - `Mathlib.RingTheory.Nilpotent.GeometricallyReduced` defines
    `Algebra.IsGeometricallyReduced k A` as
    `IsReduced (TensorProduct k (AlgebraicClosure k) A)` — **algebra
    level only**, applies to a chart-ring but not to `Γ(X, ⊤)` of a
    non-affine `X` without the very base-change-of-Γ statement we are
    chasing.

  **Near-misses (none bridges the gap in 1–2 lines):**
  - `pullbackSpecIso` (`Pullbacks.lean:703`). Distance: AFFINE-ONLY. To
    bridge to proper-Γ-base-change, one must (a) reduce the
    not-necessarily-affine `X` to a finite affine cover (`X` is
    quasi-compact since `IsProper ⇒ UniversallyClosed ⇒ QuasiCompact`),
    (b) form the Čech complex `Č(X, O_X)`, (c) prove H⁰ of the Čech
    complex equals `Γ(X, ⊤)`, (d) prove tensor-with-flat commutes
    term-by-term and exact-on-cohomology. **Conceptual distance: same
    theorem; LOC distance: 400–600.**
  - `Module.Flat.isBaseChange` (`Mathlib.RingTheory.Flat.Stability`).
    Distance: algebra-level only; would only feed the
    "tensor-with-flat-is-exact" step inside the proof above.
    **LOC distance to bridge: 0 on its own; ~30 in a chained proof.**
  - `Algebra.IsGeometricallyReduced` / `Algebra.TensorProduct.
    isField_of_isAlgebraic` (`FieldTheory.LinearDisjoint`). Distance:
    algebra-level instance, NOT a scheme-level proper-Γ statement.
    Would feed the *conclusion* once we know
    `Γ(X, ⊤) ⊗_k \bar k ≃ Γ(X_{\bar k}, ⊤)` (since
    `Γ(X_{\bar k}, ⊤) = \bar k` forces the tensor to be a domain ⇒
    `Γ(X, ⊤)` is algebraic over `k` of dim 1).
    **LOC distance to bridge: 0 on its own; ~20 once the gap is closed.**
  - `GeometricallyIrreducible` /
    `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`
    (`Geometrically/Irreducible.lean:42, 98`). Distance: this is the
    *hypothesis-side* topological statement, NOT a Γ-side base-change
    statement. Stable under base change (`Geometrically/Irreducible.
    lean:49`), so it transfers cleanly to `X_{\bar k}` ⇒
    `IrreducibleSpace X_{\bar k}` (used in step (b) of the closure
    chain, NOT step (e)). **Doesn't bridge step (e).**
  - `Algebra.IsPushout` (`Mathlib.RingTheory.IsTensorProduct`). Distance:
    ring-level only. **LOC distance to bridge: doesn't bridge — wrong
    direction (it's the Spec side, not the Γ side).**

- **Project's current path**: An in-tree thin wrapper around an
  `AlgebraicGeometry.IsBaseChange`-namespace lemma that the project's
  iter-147 prover lane assumed exists. Per the comment block at
  `ChartAlgebra.lean:270–287`, the iter-147+ continuation supplies the
  step (e) gap-fill via "a thin in-tree wrapper around the
  `AlgebraicGeometry.IsBaseChange` namespace + the
  `Spec.map_isPullback_of_isPushout` chain". **This assumed namespace
  does not exist.**

- **Gap**: divergent-and-wrong / NEEDS_MATHLIB_GAP_FILL. The project's
  closure chain assumes a Mathlib namespace
  (`AlgebraicGeometry.IsBaseChange`) and a coupling lemma
  (proper-Γ-flat-base-change) neither of which is present.

- **Cost of divergence**: If the project commits to the thin-wrapper
  story, it will write a `sorry` for the missing Mathlib lemma and
  silently inflate the proof debt. The "50–100 LOC thin wrapper" budget
  in the iter-147 prover-lane note is unrealisable; the genuine LOC
  cost is 400–600 LOC of new infrastructure (Čech complex of `O_X`
  along a finite affine cover, tensor-with-flat-term-wise commutativity,
  H⁰-equals-Γ identification, the resulting base-change-of-Γ iso) plus
  ~30 LOC of consumer-side wrapping.

- **Verdict**: NEEDS_MATHLIB_GAP_FILL (i.e. **BUILD IT** in the
  directive's vocabulary, with the caveat below).

### Decision B: What is the canonical idiom to build the gap?

- **Mathlib idiom**: There is **no Mathlib canonical idiom** for
  proper-base-change of cohomology at any degree. The pieces that *could*
  feed one if assembled:

  1. Čech cohomology infrastructure for schemes — `CategoryTheory.
     Sites.SheafCohomology.Cech` exists but is generic; one would have
     to specialise it to the Zariski site on a scheme and identify
     H⁰_Čech with `Γ(X, O_X)`.
  2. Tensor-with-flat is exact — `Module.Flat.lTensor_exact` and
     friends (`Mathlib.RingTheory.Flat.Basic`).
  3. Affine pullback compatibility — `pullbackSpecIso` and the affine
     `(Spec A → Spec R) ×_{Spec R} (Spec T → Spec R) ≅ Spec (A ⊗_R T)`
     identification (`Pullbacks.lean:703`).
  4. `IsBaseChange` (`Mathlib.RingTheory.IsTensorProduct`) for the
     final iso `Γ(X) ⊗_k T ≃ Γ(X_T)` reformulated as an
     `IsBaseChange` predicate, so the result composes with mathlib's
     ring-level base-change API.
  5. Quasi-coherent module category on a scheme
     (`Mathlib.AlgebraicGeometry.Modules.Sheaf`) for the
     `π_* O_X = Γ(X)`-as-`O_S`-module reformulation. **Caveat: the
     project would have to bridge the Stacks "quasi-coherent" notion
     to mathlib's `SheafOfModules.isQuasicoherent` (the latter is
     site-level and not yet plumbed through to scheme cohomology in
     the way needed).**

  - **Verdict**: NEEDS_MATHLIB_GAP_FILL.

- **Project's current path**: Per the iter-147+ note, the project
  intended to assemble `IsBaseChange` + flatness + Čech, but the actual
  scheme-level wiring is missing in Mathlib.

- **Gap**: identical-conceptually-but-the-pieces-are-not-assembled.

- **Cost**: 400–600 LOC to assemble correctly. ~250–300 LOC if a
  cruder, less reusable, less idiomatic proof is acceptable (a direct
  ad hoc Čech computation specialised to the project's hypotheses, not
  factored as a general framework).

- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision C: Cross-utility with M3 Route A

- M3 Route A (Picard scheme via FGA, iter-170+) needs **H¹** of the
  multiplicative group `R¹π_*(O_X^*)` for the Picard scheme
  representability. The iter-148 step (e) wrapper would only deliver
  **H⁰** = `Γ`. The shared infrastructure (Čech complex, flat-base-
  change-on-term-by-term-tensor) is the *abstract* part, but the
  iter-148 lemma's proof, factored carefully, would let M3 inherit at
  most ~30–50 LOC of reusable lemmas. The remaining ~400 LOC of M3's
  derived-functor + spectral-sequence infrastructure is separate
  work.

- **Verdict**: minor cross-utility (10–15%); not a strategic reason
  to "build it now to amortise across M3".

## Recommendation

The verdict is **BUILD IT** in the directive's vocabulary —
*qualified* by a strong recommendation that the planner first audit
whether the M2.a consumer of `constants_integral_over_base_field`
actually requires the over-`k` formulation, or whether reformulating
the consumer over `\bar k` from the start would sidestep step (e)
entirely.

If the over-`\bar k` reformulation is viable for M2.a, take that
route: the lemma `Γ(X, ⊤) = k` becomes immediate once `k` is
algebraically closed (`K/k` finite integral with `k` alg closed ⇒
`K = k`), no base-change-of-Γ needed.

If the over-`k` formulation is structurally required (consumer cannot
be reformulated), then build the gap. Honest LOC estimate:

- **400–600 LOC** for an idiomatic, defensible, future-Mathlib-PR-able
  proof of the proper-Γ-flat-base-change isomorphism via Čech
  reduction + tensor-with-flat exactness.
- **~250 LOC** for an ad hoc proof specialised hard to the project's
  hypotheses (`X` smooth proper geom irreducible reduced over a field,
  base change along the algebraic-closure map), trading reusability for
  brevity. *This* is what the project's "thin wrapper" estimate would
  produce, but it would *not* be a "wrapper" — it would be a genuine
  in-tree construction.

The "50–100 LOC thin wrapper" estimate in the iter-147 prover-lane
note is **wrong**: there is no Mathlib API to wrap.

Cross-utility with M3 Route A is modest (~10–15% of M3's needed
infrastructure). Building it now is not justified on cross-utility
grounds alone.

## Strategic recommendation to the planner

1. **First-choice option (PROCEED via consumer reformulation)**:
   audit the M2.a consumer site. If it can be reformulated over
   `\bar k`, do so; step (e) collapses to a 5-line proof using
   `IsAlgClosed.ringHom_bijective_of_isIntegral` (or equivalent
   integral-extension-of-alg-closed lemma).

2. **Second-choice option (BUILD IT)**: if the over-`k` formulation
   is structurally required, budget **~300 LOC** for an ad hoc proof
   (the higher 400–600 LOC budget being for an idiomatic Mathlib-PR
   version; the project does not need to push to Mathlib for this
   iter's purposes). The proof factors as:
   - Reduce `X` to a finite affine cover using `IsProper ⇒
     QuasiCompact` (`AffineCover`).
   - Form the Čech equaliser
     `0 → Γ(X, O_X) → ∏ Γ(U_i, O_X) ⇒ ∏ Γ(U_i ∩ U_j, O_X)`.
   - Tensor termwise with `\bar k` (flat); the tensored equaliser is
     still exact at H⁰.
   - Identify the tensored Čech complex with the Čech complex of the
     pulled-back scheme `X_{\bar k}` along the pulled-back cover.

3. **Third-choice option (DEFER)**: leave step (e) as a structured
   `sorry`, document the gap in `STRATEGY.md`, ship the iter-148
   reduction-to-`sorry` of the surrounding closure chain.

The planner should pick (1) if at all possible; (2) only if (1) is
ruled out; (3) only if (2) exceeds budget for iter-148–150.
