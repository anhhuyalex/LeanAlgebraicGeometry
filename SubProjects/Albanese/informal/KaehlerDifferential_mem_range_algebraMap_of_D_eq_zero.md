# KDM lemma `mem_range_algebraMap_of_D_eq_zero`: false as stated, and the fix

**File:** `AlgebraicJacobian/Cotangent/ChartAlgebra.lean`
**Found:** iter-151 prover lane (the bounded (C.d) transfer-step convergence test).

## Current (false) statement

> Let `k` be a field of characteristic 0, `B` a finite-type `k`-algebra that is
> standard smooth of relative dimension `n`, and `b ∈ B` with `D_{B/k} b = 0`.
> Then `b ∈ range (algebraMap k B)`.

## Why it is false

`IsStandardSmoothOfRelativeDimension n k B` means only "`B` admits a submersive
presentation of relative dimension `n`" — it implies `Ω[B/k]` is locally free of
rank `n`, but imposes **no connectedness**, and crucially no **geometric**
connectedness (no condition that `k` be algebraically/separably closed in `B`).

Two counterexamples, each satisfying every hypothesis:

1. **`B = k × k`, `n = 0`** (any char-0 `k`). `B ≅ k[x]/(x²−x)`; the Jacobian
   `2x−1` is a unit, so `B` is standard smooth of relative dimension `0` (finite
   étale). Étale ⟹ `Ω[B/k] = 0` ⟹ `D = 0`, so `D b = 0` for *all* `b`. But
   `range(algebraMap k B)` is the diagonal, and `(1,0)` is not in it.

2. **`k = ℚ`, `B = ℚ(√2)`, `n = 0`.** Finite separable ⟹ étale ⟹ `Ω = 0` ⟹
   `D = 0`; `D b = 0` for all `b`. `Spec B` is one point (connected) and `B` is
   a field (a domain), yet `range(algebraMap ℚ B) = ℚ ⊊ ℚ(√2)`.

Counterexample 1 kills "just add connectedness"; counterexample 2 kills "just add
`IsDomain B`". The real missing hypothesis is **`k` algebraically closed in `B`**
(equivalently: `B` geometrically integral / `Spec B` geometrically connected
over `k`).

## The correct statement (recommended fix)

> Let `k` be a field of characteristic 0, `B` a finite-type standard-smooth
> `k`-algebra of relative dimension `n` **that is geometrically integral over
> `k`** (equivalently `k` is algebraically closed in `B`). If `D_{B/k} b = 0`
> then `b ∈ range(algebraMap k B)`.

Sketch (char 0): `Ω[B/k]` free with coordinate derivations `∂_i`; `D b = 0 ⟹
∂_i b = 0 ∀ i`. Lift to the polynomial presentation `P = k[x_i]`, `π : P ↠ B`,
`I = ker π`. The FREE-case fact (already proved in Lean as
`_mvPoly_mem_range_C_of_D_eq_zero`) gives kernel-equals-constants on `P`. Geometric
integrality of `B` is what makes the transfer back along `π` land in `k` rather
than in a larger separable/disconnected constant subring — it forces the
"`pderiv_i α ∈ I` ⟹ `α` constant mod `I`" step that fails in counterexample 2.

## Why this was lost

At the scheme level the obligation
(`GrpObj.df_zero_factors_through_constant_on_chart`) carries
`GeometricallyIrreducible` + `IsReduced` on the curve `C`. When it was reduced to
the abstract `B`-only algebra lemma `mem_range_algebraMap_of_D_eq_zero`, the
geometric hypotheses were dropped — `B` became an arbitrary standard-smooth
algebra disconnected from `C`. The geometric content must be re-introduced as an
explicit hypothesis on `B`.

## Coupling to the open user decision

This is the same geometric-connectedness content as the pending TO_USER
`[IsAlgClosed kbar]` / flat-base-change-of-Γ question (`PROGRESS.md` §
"TO_USER", asked iter-150). A coherent resolution should decide the geometric
hypothesis once and thread it through both `mem_range_algebraMap_of_D_eq_zero`
and `df_zero_factors_through_constant_on_chart`.

## Lean status

`sorry` retained at (C.d) with the intended (currently false) signature
preserved, so the mathematician's signature-correction decision is unobstructed.
Scaffolding (C.a)–(C.c) — the four `_mvPoly_*` helpers and the `_hFunct`
functoriality reduction — is correct and reusable for the corrected lemma.
