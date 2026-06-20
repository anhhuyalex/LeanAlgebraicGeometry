# Analogy: ℙ¹-specific hedge for the `C(k) ≠ ∅` branch of `genusZeroWitness`

## Slug
p1-hedge-iter138

## Iteration
138

## Question

For the `C(k) ≠ ∅` branch of M2.b genus-0 witness specifically, is there a
viable ℙ¹-specific rigidity argument — cheaper than the general over-k shared
cotangent-vanishing pile (pieces (i)+(ii)+(iii)) — that uses a **weak ℙ¹
identification** of `C` with `ℙ¹_k` via elementary projective-embedding +
low-order-pole-existence (NOT full Serre duality), and that collapses the
dependence on scheme-level absolute Frobenius (piece (iii), ~800–1500 LOC) to
ring-side `k[t]` / `k[1/t]` instances?

## Project artifact(s)

- `AlgebraicJacobian/Jacobian.lean:193-197` — `genusZeroWitness C h` scaffold;
  body `sorry`, consumes `rigidity_over_kbar` on the `C(k) ≠ ∅` branch.
- `AlgebraicJacobian/RigidityKbar.lean:75-87` —
  `AlgebraicGeometry.rigidity_over_kbar`; body `sorry`, gated on the shared
  cotangent-vanishing pile (i)+(ii)+(iii).
- `blueprint/src/chapters/RigidityKbar.tex` § C.2.d + § sec:RigidityKbar_shared_pile —
  decomposition of the pile into pieces (i.a)–(i.c), (ii), (iii); LOC budgets
  800–1500 (i, total) + 250–500 (ii) + 300–600 (iii).

## Decisions identified

### Decision 1: Does Mathlib `b80f227` ship a "weak ℙ¹ identification" chain  smooth proper geom-irr genus-0 k-curve with a k-point ⇒ `C ≅ ℙ¹_k`?

- **Mathlib idiom**: **NONE EXISTS.** Exhaustive verification:
  - `lean_leansearch "genus zero curve isomorphic to projective line"` → returns
    only `WeierstrassCurve.*` results (genus-1 elliptic curves) and no genus-0
    classification. Cite: no Mathlib hit.
  - `lean_leansearch "smooth curve genus zero one rational map"` → only
    `Scheme.RationalMap` infrastructure (which is generic rational maps, not the
    genus-0 classification). Cite: `Mathlib.AlgebraicGeometry.RationalMap`.
  - `lean_leansearch "ProjectiveSpace Pn scheme over base"` → confirms Mathlib
    has **no `ProjectiveSpace n S : Scheme.CanonicallyOver S`** packaging. The
    closest is `AlgebraicGeometry.Proj 𝒜` (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`),
    the general Proj of a graded ring, with no specialised ℙⁿ_S wrapper. (The
    iter-126 refactor agent already encountered this hole — see
    `AlgebraicJacobian/RigidityKbar.lean:38-46` "Encoding choice".)
  - `lean_leansearch "Brauer Severi variety trivial rational point"` → zero
    Brauer-Severi infrastructure.
  - `lean_leansearch "algebraic curve genus formula divisor class group"` → only
    Dedekind-domain `ClassGroup` and `WeierstrassCurve.Affine.CoordinateRing.XYIdeal'`;
    NO `CartierDivisor` / `WeilDivisor` / `Pic(C)` for general smooth curves.
  - `lean_leansearch "Riemann Roch theorem curve linear equivalence divisor"` →
    `Module.nonempty_linearEquiv_of_finrank_eq_one` and PicardGroup material; no
    Riemann–Roch on a smooth proper curve.
- The mathematically required chain to produce the weak identification is
  Riemann–Roch on a genus-0 curve plus a degree-1 divisor: with `P ∈ C(k)`,
  `dim H⁰(C, O(P)) ≥ 2 - 0 = 2`, hence the linear system `|P|` gives a
  degree-1 map `C → ℙ¹_k` which is an isomorphism since `C` is smooth + integral.
  **Every ingredient of this chain (Riemann–Roch, Cartier divisors, linear
  systems, projective embedding) is absent from Mathlib b80f227.**
- Pre-existing analogist verdict already in tree: `analogies/serre-duality.md`
  (iter-110) verified Mathlib has zero coherent-cohomology infrastructure on
  schemes — no Serre duality, no dualizing sheaf, no canonical sheaf, no trace
  morphism, no Riemann–Roch, no `RiemannHurwitz`. Estimated build for
  full Serre duality + Riemann-Roch is 3000–8000 LOC. A genus-0 specialisation
  saves a constant factor but stays in the same order of magnitude:
  ~1500–3000 LOC for Cartier divisors on smooth curves + linear systems +
  the degree-1 case of Riemann–Roch + projective-embedding.
- **Project's path**: the current `rigidity_over_kbar` blueprint
  (iter-127 over-k commitment) deliberately AVOIDS the identification — the
  signature uses the abstract `SmoothOfRelativeDimension 1 + IsProper +
  GeometricallyIrreducible + genus = 0` characterisation. Per the
  `RigidityKbar.lean:38-46` encoding note, this was a deliberate choice because
  no `ProjectiveSpace` exists, and the C.2.b–C.2.d cotangent-vanishing route
  consumes only the abstract characterisation.
- **Gap**: divergent-and-wrong if attempted: the hedge would require an
  in-tree build of Riemann–Roch-on-genus-0 from scratch.
- **Cost**: ~1500–3000 LOC of de-novo Cartier divisor + linear system +
  Riemann–Roch genus-0 + Brauer-Severi-triviality-for-genus-0 infrastructure.
  Sits at the same order as the iter-110 deferred Serre duality build.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — the prerequisite is structurally
  absent from Mathlib. The "weak ℙ¹ identification" cannot be cheap.

### Decision 2: If the weak identification existed, would the ring-side `k[t]` / `k[1/t]` instances replace piece (iii) Frobenius cheaply?

- **Mathlib idiom — ring-level Frobenius**: PRESENT, cheaply usable.
  `Mathlib.Algebra.CharP.Frobenius` ships `frobenius` and `iterateFrobenius`
  as RingHoms on any `[CommRing R] [ExpChar R p]`. Specialises to `k[t]` and
  `k[1/t]` (= `k[t, t⁻¹]` = `Localization.Away (t : k[t])`) without further
  work. The ring-level Frobenius savings argument is sound here.
- **Mathlib idiom — `Differential.ContainConstants k (Polynomial k)`**: **NOT
  AN INSTANCE.** Cite: `Mathlib/RingTheory/Derivation/DifferentialRing.lean:72-76`.
  The ONLY registered instance is the trivial `Differential.ContainConstants A A`
  (every element of `A` is in `algebraMap A A`'s range — vacuous).
  - In characteristic 0: `ContainConstants k k[t]` is true and provable
    quickly (~30–80 LOC) via `Polynomial.derivative_eq_zero_iff`'s degree
    argument.
  - In characteristic `p > 0`: **`ContainConstants k k[t]` is FALSE with the
    standard derivative**: any `f(t)^p = f(t^p)` (no, wait, the derivative of
    `t^p` is `p t^(p-1) = 0`, but `t^p ∉ k`). So a flat ring-level
    `ContainConstants` is **not** the right statement; one must use the
    iterated Frobenius descent ("if `f' = 0` then `f ∈ k[t^p]`; iterate to
    descend to a constant"). This is EXACTLY the piece (iii) Frobenius
    iteration, transposed to the ring level on `k[t]`.
- **Project's path** (if hedge taken): would need to build a `k[t]`-specific
  + `k[1/t]`-specific "iterated Frobenius descent ⇒ ContainConstants k k[t^{p^∞}]"
  argument, then glue across the affine cover of ℙ¹_k. Per the iter-126 cotangent
  pile analysis, this transposed version of piece (iii) is structurally the same
  argument run on `k[t]` and `k[1/t]` instead of on a scheme `X`, with the same
  Frobenius descent ratchet. Net savings vs scheme-level (iii): the local-stalk
  bookkeeping disappears, but the Frobenius descent ladder remains. Estimated
  cost: ~150–400 LOC (vs ~800–1500 LOC for scheme-level piece (iii)).
- **Gap**: divergent-with-cost. The hedge's headline "replace (iii) with
  ring-side instances" REQUIRES de-novo work to prove a per-chart Frobenius-
  iterated `ContainConstants` (Mathlib's trivial `instContainConstants A A`
  cannot discharge this). The savings vs. the scheme-level (iii) are real but
  not free: ~150–400 LOC, not ~30 LOC.
- **Verdict**: **PROCEED conditional on Decision 1**. The ring-side Frobenius
  hedge IS cheaper than scheme-level (iii) **conditional on the weak
  identification being available**, but Decision 1 rules that out.

### Decision 3: Does the hedge eliminate pieces (i.b) and (i.c)?

- **Project artifact**: pieces (i.b) and (i.c) of the shared cotangent-vanishing
  pile (`blueprint/src/chapters/RigidityKbar.tex` § subsec:RigidityKbar_piece_i_decomposition)
  state cotangent triviality of the **target** group scheme `A` (Ω_{A/k} is
  free of rank `dim A`), via the shear iso + functorial globalisation. This is
  needed because the rigidity argument's signature is `f : C → A` with `A` a
  smooth proper geom-irr group scheme over `k` of arbitrary dimension `g`.
- **Hedge claim**: the weak ℙ¹ identification works on the **source** side
  (`C ≅ ℙ¹_k`). It does NOT touch the target side. The target `A` remains
  an arbitrary abelian variety; its cotangent must still be trivialised.
- **Gap**: hedge identification is irrelevant to pieces (i.b)+(i.c). They
  remain irreducible in the hedge scenario.
- **Verdict**: **PROCEED with pieces (i.b)+(i.c) regardless of hedge.** The
  hedge cannot save the target-side cotangent-triviality work.

### Decision 4: LOC envelope comparison (hedge vs bundled pile)

Using the iter-126 / iter-133 / iter-137 estimated budgets:

**Bundled pile** (current strategy):
- (i.b) `mulRight_globalises_cotangent` + helpers: ~210–440 LOC (iter-133 v.).
- (i.c) `omega_free` + `omega_rank_eq_dim`: ~600–1100 LOC (iter-126).
  Combined (i.b) + (i.c) sub-total: ~810–1540 LOC.
- (ii) Scheme-level `ext_of_diff_zero`: ~250–500 LOC.
- (iii) Scheme-level Frobenius iteration: ~800–1500 LOC.
- **Bundled pile total: ~1860–3540 LOC** (approximately matches the
  directive's 1850–3600 LOC quote).

**Hedge** (proposed alternative):
- Weak ℙ¹ identification (Riemann–Roch genus-0 + linear systems +
  Brauer-Severi triviality + projective embedding, all NEEDS_MATHLIB_GAP_FILL):
  ~1500–3000 LOC (Decision 1).
- Pieces (i.b)+(i.c) STILL needed for target `A` (Decision 3):
  ~810–1540 LOC.
- Affine-chart-glued (ii) on Spec k[t] ∪ Spec k[1/t]: ~150–300 LOC. (Saves
  vs scheme-level (ii)'s ~250–500 LOC.)
- Ring-side Frobenius iteration on k[t]/k[1/t] (Decision 2): ~150–400 LOC.
- **Hedge total: ~2610–5240 LOC** — **strictly more than the bundled pile**.

Even if the weak identification could be built in half the lower-bound
estimate (~750 LOC, optimistic), the hedge total ~1860–4490 LOC overlaps the
pile range but with much wider spread; the most likely outcome is the hedge
costs **more** than the pile by 500–1500 LOC, with a much larger build-risk
tail because none of the identification ingredients exist upstream.

- **Verdict**: **NOT-VIABLE on LOC grounds alone.** The hedge does not save
  cost in expectation; it adds a structurally new infrastructure burden (the
  identification) without retiring the pieces it claimed to retire.

## Recommendation

**NOT-VIABLE.** The hedge fails on three independent grounds:

1. **Prerequisite gap (Decision 1):** Mathlib `b80f227` has zero infrastructure
   for the weak ℙ¹ identification — no Riemann–Roch, no Cartier/Weil divisors
   on smooth proper curves, no line-bundle global sections, no Brauer-Severi
   triviality, no `ProjectiveSpace n S`. Building the identification from
   first principles costs ~1500–3000 LOC (the genus-0 specialisation of the
   already-deferred Serre-duality / Riemann–Roch stack from
   `analogies/serre-duality.md` iter-110).

2. **Target-side residual (Decision 3):** The identification lives on the
   source side `C`. Pieces (i.b)+(i.c) of the pile trivialise the cotangent of
   the **target** group scheme `A`; the hedge does not touch them. Those
   ~810–1540 LOC remain on the critical path either way.

3. **Ring-side `ContainConstants k k[t]` is itself a non-trivial gap
   (Decision 2):** Mathlib's only `Differential.ContainConstants` instance is
   the trivial diagonal one (`Mathlib/RingTheory/Derivation/DifferentialRing.lean:75-76`).
   In characteristic `p > 0`, the ring-level `ContainConstants k k[t]` with
   the standard derivation is **false**; the hedge must replicate the piece
   (iii) Frobenius descent at the ring level on `k[t]` and `k[1/t]`. The
   savings vs scheme-level (iii) are real but only ~400–1100 LOC, not the
   full ~800–1500 LOC.

The hedge's headline appeal ("avoid scheme-level Frobenius by going to
ring-side k[t] instances") is real for the Frobenius savings in isolation,
but the savings are dominated by the new identification build cost. The most
likely outcome is the hedge ships ~500–1500 LOC more than the bundled pile,
with much wider tail risk.

**Sequencing recommendation** (per directive question 5): N/A — the hedge is
not on a viable path. **Continue with the bundled pile (i.b)+(i.c)+(ii)+(iii)
as the iter-138+ build target.** The iter-137 PARTIAL on (i.b) Step 2 (per
`analogies/kaehler-tensorequiv-presheafpullback.md`) is the active prover lane
and remains the right next step; (i.c), (ii), (iii) follow in their already-
scheduled sequence.

**Alternative recommendation:** if the cotangent pile stalls on (iii) at
iter-140+, the cheaper escape hatch is to **keep `rigidity_over_kbar` as a
named-gap sorry** in the same family as `serre_duality_genus`
(`analogies/serre-duality.md` recommended outcome). Going via the hedge's
de-novo identification build would be strictly more expensive than either
closing the bundled pile or accepting a named gap; it should NOT be revisited
without a structural shift in Mathlib (e.g., upstream Riemann–Roch landing,
or a `ProjectiveSpace n S` package becoming canonical).
