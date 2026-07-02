# Analogy: Over-k variant of the shared cotangent-vanishing pile — does it carry, eliminating M2.c?

## Slug
cotangent-vanishing-pile-over-k-iter127

## Iteration
127

## Question

Can the shared cotangent-vanishing pile — iter-126's pieces (i)+(ii)+(iii)
documented in [[cotangent-vanishing-pile]] — be built **directly over an
arbitrary base field `k`** (no algebraic closure assumed), eliminating
the Galois-descent step M2.c (300–500 LOC / 4–8 iter)? Per-piece
sub-questions:

1. **Piece (i) over k vs over k̄.** Does the construction
   `Lie-algebra-of-GrpObj → mulRight-globalisation →
   relative-cotangent-presheaf trivialisation` work over any base
   field k, or does some step force algebraic closure?

2. **Piece (ii) over k vs over k̄.** Is `Differential.ContainConstants`
   a typeclass over arbitrary commutative rings/algebras admitting a
   char-0 instance without requiring k alg-closed?

3. **Piece (iii) Frobenius iteration over k vs over k̄.** Does the
   iteration argument work over an arbitrary characteristic-p field
   k, or does it require perfectness / alg-closure?

4. **Meta: is M2.c truly avoidable** under the over-k route, or does
   some other downstream consumer still need Galois descent of
   morphism equality?

## Project artifact(s)
- `analogies/cotangent-vanishing-pile.md` (iter-126 over-`k̄`
  analogist) — settled over-`k̄` baseline; this file is the over-k
  delta.
- `blueprint/src/chapters/RigidityKbar.tex:57–77` — current over-`k̄`
  framing.
- `blueprint/src/chapters/Jacobian.tex` § C.2.b–C.2.g — proof
  decomposition, including the C.2.f Galois-descent step the over-k
  route would eliminate.
- `AlgebraicJacobian/Rigidity.lean:91` — `Scheme.Over.ext_of_eqOnOpen`
  (iter-125 refactor; declared over `[Field k]`, no alg-closure
  hypothesis).
- `AlgebraicJacobian/RigidityKbar.lean:75–87` — `rigidity_over_kbar`
  iter-126 scaffold. **Signature carries only `[Field kbar]`, not
  `[IsAlgClosed kbar]`.** The variable name `kbar` is the only thing
  forcing the over-`k̄` reading; the type-class hypothesis is
  k-agnostic.

## Mathlib snapshot

`b80f227` (project's pinned `lake-manifest.json`).

## Decisions identified

The directive asks one design question but compresses **four** orthogonal
sub-decisions: piece-by-piece over-k viability (i), (ii), (iii), plus
the meta-decision on whether M2.c is genuinely eliminated.

### Decision (i): Cotangent triviality of a group scheme over arbitrary k

- **Mathlib's closest precedent**:
  `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`
  (`Mathlib/AlgebraicGeometry/Group/Smooth.lean:38–60`) requires
  `[IsAlgClosed K]` — but it proves the *wrong direction* for our
  needs (smoothness from reducedness, not cotangent triviality from
  smoothness). **The alg-closure hypothesis there is a feature of
  Mathlib's specific proof, not an inherent feature of the theorem.**
  The proof uses `pointEquivClosedPoint` (a Nullstellensatz-style
  identification: closed points of `G` over alg-closed `K` correspond
  bijectively to `K`-rational points), plus pointwise translation by
  `GrpObj.mulRight` at two arbitrary closed points. Over non-alg-closed
  k, this specific argument fails because closed points may have
  non-trivial residue fields. **However**, this is orthogonal to our
  cotangent-triviality argument [verified by reading the full proof].

  A second precedent is more revealing:
  `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
  (`Mathlib/AlgebraicGeometry/Group/Abelian.lean:128–145`, `@[stacks 0BFD]`)
  is stated over an arbitrary field `K` and **internally uses the
  "go to k̄ then descend" pattern** via `(Over.pullback f).map_injective`
  (line 140). The descent step there is comparatively cheap — it's a
  one-line application — because the project's M2.c Galois-descent
  obligation **already exists as a Mathlib idiom for `Over (Spec (.of k))`
  pullback along `Spec k̄ → Spec k`**. (This is a tangential observation
  for the iter-126 over-`k̄` analogist's M2.c cost estimate too: M2.c may
  be cheaper than the 300–500 LOC iter-124 spot-check estimate, in the
  worst case, because the project could mimic `Group/Abelian.lean`'s
  use of `Over.pullback.map_injective` directly. But this isn't germane
  to the over-k path's verdict.)

  For cotangent triviality specifically, **no Mathlib idiom exists at
  the scheme level** (per [[cotangent-vanishing-pile]] Decision (i) and
  [[cotangent-presheaf-design]]): the project has its own
  `relativeDifferentialsPresheaf`, no Lie-algebra-of-`GrpObj`, no
  scheme-side shear iso, no `GrpObj.omega_free`.

- **Project's proposed path (over-k variant)**: build the iter-126
  chain — Lie-algebra-of-`GrpObj` definition + mulRight-globalisation
  via shear iso + relative-cotangent-presheaf trivialisation — over an
  arbitrary base field `k`, with no `[IsAlgClosed k]` hypothesis. The
  iter-126 chain's steps must be **formulated functorially** (via the
  shear scheme map `A ⊗ A → A ⊗ A`, `(a, b) ↦ (a, a·b)`, valid over
  any base) rather than pointwise (via translation by k̄-rational
  points). The Lie algebra at the identity is `(η[A])^* Ω_{A/k}` — a
  k-vector space — well-defined for any base field k (the identity
  section `η[A] : 1 → A` is canonical and the cotangent presheaf
  is intrinsic).

- **Gap**: identical (over k vs over k̄). The iter-126 chain's
  prerequisites and proof strategy are unchanged. The verbatim build
  directive carries; only the hypothesis pattern relaxes from
  `[IsAlgClosed k̄]` (which is absent from the iter-126 scaffold
  already!) to just `[Field k]`.

  **Sub-piece check**:
  - **Lie-algebra-of-`GrpObj` definition**: k-agnostic. `(η[A])^* Ω_{A/k}`
    is a k-vector space for any field k. [expected]
  - **Shear isomorphism `A ⊗ A ≅ A ⊗ A`**: k-agnostic. The shear map
    `(a, b) ↦ (a, a·b)` is a scheme map built from `GrpObj.mul` and
    projections; no point-wise lifting needed. The inverse is built
    from `GrpObj.inv`. Both work over any base. [expected]
  - **Relative-cotangent-presheaf trivialisation**: k-agnostic. The
    formula `Ω_{A/k} ≅ pr_1^* (η[A]^* Ω_{A/k}) ⊗_k O_A` holds at the
    presheaf level for any base k. [expected]
  - **Mathlib's `pointEquivClosedPoint` / `dense_smoothLocus_of_perfectField`
    (the alg-closure-using parts of `smooth_of_grpObj_of_isAlgClosed`)**:
    NOT NEEDED here — we are given smoothness as a hypothesis, not
    proving it. [verified]

- **Verdict**: **OK_OVER_K**. The iter-126 build directive carries
  verbatim. LOC estimate unchanged at 800–1500 LOC per
  [[cotangent-vanishing-pile]] Decision (i). The over-k variant adds
  **zero** to piece (i) cost. **Naming refinement**: the iter-126
  recommended names `AlgebraicGeometry.GrpObj.omega_free` and
  `AlgebraicGeometry.GrpObj.omega_rank_eq_dim` should be **kept**
  (they were already k-agnostic; the iter-126 analogist correctly
  avoided baking `_over_kbar` into the names).

### Decision (ii): scheme-level `df = 0 ⇒ f` factors through `Spec k`, over arbitrary k

- **Mathlib idiom**: `Differential.ContainConstants`
  (`Mathlib/RingTheory/Derivation/DifferentialRing.lean:62–66`) is
  defined for arbitrary `[CommRing A] [CommRing B] [Algebra A B]
  [Differential B]` — **no alg-closure requirement** [verified by
  reading the class definition]. The instance
  `[CommRing A] [Differential A] : Differential.ContainConstants A A`
  (line 75) is the trivial self-instance; **no `[IsAlgClosed]` instance
  exists** [verified by grep across Mathlib b80f227].

  The Liouville-style usage in `Mathlib.FieldTheory.Differential.Liouville`
  (line 57, 81 onwards) uses `[Differential.ContainConstants F K]`
  as a hypothesis only — it doesn't force alg-closure of `F`. The
  `isLiouville_of_finiteDimensional_galois` lemma (line 123) requires
  `[CharZero F]` and `[IsGalois F K]`, NOT `[IsAlgClosed F]` [verified
  by reading the proof]. The whole Liouville stack is k-agnostic on
  the base field side.

- **Scheme-level idiom**: NONE. Per [[cotangent-vanishing-pile]]
  Decision (ii), no Mathlib precedent for "scheme morphism with zero
  differential factors through a point" exists at any generality.

- **Project's proposed path (over-k variant)**:
  - **Ring-level**: register the char-0 instance
    `[CharZero B] [Algebra A B] [IsIntegralDomain B] ⇒
    Differential.ContainConstants A B`. The proof — kernel of `d_{B/A}`
    on a char-0 integral domain extension is `A` — is k-agnostic
    (no alg-closure used). [expected]
  - **Scheme-level lift**: use `AlgebraicGeometry.Scheme.Over.ext_of_eqOnOpen`
    (`AlgebraicJacobian/Rigidity.lean:91`, iter-125 refactor) — which
    is declared over `[Field k]` already, no alg-closure [verified].
    The scheme-level "df = 0 ⇒ f factors through Spec k" lift is
    intrinsic to k: no k̄-rational point lifting, no Galois action,
    no base change.

- **Gap**: identical (over k vs over k̄). The iter-126 build directive
  carries verbatim.

- **Verdict**: **OK_OVER_K**. The Mathlib `Differential.ContainConstants`
  typeclass is k-agnostic; the project's iter-125-refactored
  `Scheme.Over.ext_of_eqOnOpen` is already declared over `[Field k]`;
  Liouville-style consumers don't bake in alg-closure. LOC estimate
  unchanged at 250–500 LOC per [[cotangent-vanishing-pile]] Decision (ii).
  The over-k variant adds **zero** to piece (ii) cost.

### Decision (iii): Frobenius iteration over arbitrary char-p k

- **Mathlib idiom**: `frobenius R p` and `iterateFrobenius R p n`
  (`Mathlib/Algebra/CharP/Frobenius.lean`, declarations referenced
  from `Mathlib/Algebra/CharP/Lemmas.lean`) are defined for any
  `[CommSemiring R] [ExpChar R p]` — **no perfect / alg-closed
  requirement** [verified by reading the file header and first 80
  lines: `variable {R : Type*} [CommSemiring R] ... [ExpChar R p]`].
  Key lemmas:
  - `frobenius_def : frobenius R p x = x ^ p` (line 32)
  - `iterateFrobenius_def : iterateFrobenius R p n x = x ^ p ^ n` (line 34)
  - `iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R` (line 57)
  - `iterateFrobenius_add` (lines 60–66)
  All hold over arbitrary char-p commutative rings.

  `Mathlib.FieldTheory.Perfect` exists (line 22: `class PerfectRing R p`;
  line 23: `class PerfectField K`) but is **not used inside the
  Frobenius file** — the Frobenius machinery is layered below
  perfectness. [verified]

- **Project's proposed path (over-k variant)**: build a thin
  scheme-side `AlgebraicGeometry.Scheme.absoluteFrobenius` on top of
  `frobenius R p` (per [[cotangent-vanishing-pile]] Decision (iii)
  recommendation), then run Mumford's iteration argument: if
  `df = 0` then `f` factors as `f̃ ∘ F_X` (absolute Frobenius of
  source); iterate to get `f = f^(n) ∘ F_X^n` with
  `f^(n)` constant; conclude `f` constant via composition.

  **Key over-k observation**: the absolute Frobenius `F_X : X → X`
  is intrinsic to `X` (identity on the topological space, p-th power
  on the structure sheaf) and **does NOT depend on the base k** — it
  exists for any char-p scheme, perfect base or not [verified
  mathematically]. The iteration argument's descent step ("`f^(n)`
  constant ⇒ `f` constant") goes:
  ```
  f = f^(n) ∘ F_X^n  →  if f^(n) = const_y for y ∈ Y(k), then
                       f = const_y ∘ F_X^n = const_y
  ```
  because constancy is preserved under precomposition with any map
  to `Spec k`. **No perfect-base hypothesis is required for this
  descent**: we don't need `F_X^n` to be surjective in any geometric
  sense; we just need the formal equation `f = f^(n) ∘ F_X^n`, which
  holds in `Hom_k(X, Y)` regardless of k's perfectness.

  (The temptation to use the relative Frobenius `F_{Y/k}` — which
  would require perfectness of k for descent — is unnecessary. The
  absolute Frobenius `F_X` suffices.)

- **Gap**: identical (over k vs over k̄). The iter-126 build directive
  carries verbatim.

- **Verdict**: **OK_OVER_K**. Mathlib's ring-level Frobenius is
  k-agnostic (no perfect-base requirement); the scheme-level absolute
  Frobenius `F_X` is intrinsic to X (independent of base); the
  iteration argument's descent step uses only formal precomposition,
  not surjectivity of relative Frobenius. LOC estimate unchanged at
  300–600 LOC per [[cotangent-vanishing-pile]] Decision (iii). The
  over-k variant adds **zero** to piece (iii) cost.

### Decision (iv) [meta]: M2.c avoidability

- **C.2.f Galois descent consumers in `Jacobian.tex`**: grep across
  the chapter for `Galois descent`, `descent`, and `base change` finds
  references at lines 275, 280 (Picard side, unrelated to M2.c — would
  affect Route A but Route B doesn't use it), 319, 352, 358, 367, 376,
  387, 398. All of these are about transporting the rigidity conclusion
  from k̄ to k, i.e. they are the **same** use of C.2.f from M2.a /
  M2.b. **No other in-tree consumer of "Galois descent of morphism
  equality of schemes" exists in the project's M2 critical path.**
  [verified]

- **M2.c.aux `geomIrred.exists_kalg_pt`** (STRATEGY.md:486): this is
  the "k̄-rational point existence" lemma needed when base-changing
  C from k to k̄ before applying the over-k̄ rigidity. If rigidity is
  proven directly over k (which needs only `p : 1 → C` as a k-rational
  point, supplied directly by the C(k) ≠ ∅ hypothesis), M2.c.aux is
  also unnecessary.

- **Iter-126 scaffold reveals**: `AlgebraicJacobian/RigidityKbar.lean:56`
  declares only `[Field kbar]`, NOT `[IsAlgClosed kbar]` [verified by
  reading the file]. The variable name `kbar` is a *labelling*, not a
  *constraint*. The iter-126 scaffold's signature **already supports
  the over-k variant** — only the body closure differs.

- **Verdict**: M2.c is **truly avoidable** under the over-k route.
  The only consumer of "Galois descent of morphism equality" in the
  M2 critical path is the C(k) ≠ ∅ branch's k̄-to-k transport of the
  rigidity conclusion, which is **eliminated** if rigidity is proven
  directly over k. Both M2.c (300–500 LOC, 4–8 iter) and M2.c.aux
  (200–400 LOC, 3–5 iter) become unnecessary. **Total savings:
  500–900 LOC / 7–13 iter.**

  Note on the over-k̄ baseline's M2.c being cheaper than the iter-124
  spot-check estimate: even if the project keeps the over-`k̄` baseline,
  `Group/Abelian.lean:140`'s use of `(Over.pullback f).map_injective`
  shows the descent step can be done in roughly one line — so the
  iter-124 spot-check's 300–500 LOC for M2.c may be a high-water-mark
  estimate. But this doesn't change the verdict: the over-k path
  eliminates the descent step ENTIRELY, which is strictly cheaper than
  any cheaper M2.c bound, however cheap.

## Recommendation

**Adopt the over-k variant decisively.** All three pieces of the
shared cotangent-vanishing pile build over an arbitrary base field
`k` with the iter-126 directive carrying over verbatim:

- **Piece (i) cotangent triviality**: 800–1500 LOC, k-agnostic. Formulate
  the mulRight-globalisation step functorially via the shear iso
  (not via point-wise k̄-translation). The Lie-algebra-of-`GrpObj`
  definition `(η[A])^* Ω_{A/k}` is intrinsic to any base k.
- **Piece (ii) `df = 0 ⇒ factors through Spec k`**: 250–500 LOC,
  k-agnostic. Align with `Differential.ContainConstants` typeclass
  (already k-agnostic in Mathlib); register the char-0 instance for
  integral domains. The scheme-level lift uses the project's existing
  `Scheme.Over.ext_of_eqOnOpen` (iter-125 refactor, already declared
  over `[Field k]`).
- **Piece (iii) Frobenius iteration**: 300–600 LOC, k-agnostic. Build
  a thin scheme-side `AlgebraicGeometry.Scheme.absoluteFrobenius` on
  top of Mathlib's `frobenius R p` (which has no perfect-base
  requirement). The iteration descent uses absolute (intrinsic)
  Frobenius, not relative Frobenius — no perfectness needed.

**Pile total over-k**: 1350–2600 LOC over 7–14 iter, **identical to
the over-`k̄` baseline** per [[cotangent-vanishing-pile]] Decision (v).

**M2.c savings**: under the over-k route, M2.c (300–500 LOC, 4–8
iter) and M2.c.aux (200–400 LOC, 3–5 iter) are both **eliminated**.
**Total project savings: 500–900 LOC / 7–13 iter.**

**Action items for the project to adopt the over-k path**:

1. **Rename the iter-126 scaffold**: `rigidity_over_kbar` → `rigidity`
   (or `rigidity_over_k` to preserve the existing name pattern).
   Rename `kbar` → `k` throughout `AlgebraicJacobian/RigidityKbar.lean`
   and `blueprint/src/chapters/RigidityKbar.tex`. The Lean signature
   is unchanged modulo the variable rename (the `[Field kbar]`
   hypothesis was already k-agnostic).
2. **Update `RigidityKbar.tex` § "The shared cotangent-vanishing
   Mathlib pile"** to reflect the over-k framing: pieces (i)+(ii)+(iii)
   are proven directly over k; piece (iv) Serre duality remains
   DEFERRED as a named gap per [[serre-duality]].
3. **Update `Jacobian.tex` § C.2** to drop the C.2.f Galois-descent
   sub-step: the over-k rigidity is invoked directly in the
   C(k) ≠ ∅ branch (with `p : 1 → C` as the marked point) without
   base-change to k̄.
4. **Update `STRATEGY.md` § M2** to drop M2.c (Galois descent) and
   M2.c.aux (k̄-rational point existence) from the iter-129+
   sequencing. The new sequencing is: pieces (i)+(ii)+(iii) →
   M2.a body closure → M2.b body closure → M2 closure. **Honest M2
   closure estimate revised downward**: iter-143 to iter-157 (was
   iter-150 to iter-170+), saving 7–13 iter.
5. **Keep [[cotangent-vanishing-pile]] iter-126's per-piece naming
   recommendations**: `AlgebraicGeometry.GrpObj.omega_free`,
   `AlgebraicGeometry.GrpObj.omega_rank_eq_dim`,
   `AlgebraicGeometry.Scheme.Over.ext_of_diff_zero`,
   `AlgebraicGeometry.Scheme.absoluteFrobenius`. These names are
   already k-agnostic and require no over-k vs over-`k̄` disambiguation.

**Risk register**:

- **Piece (i) sub-piece subtlety**: the iter-126 chain's step 3
  ("mulRight-globalisation") is *worded* in [[cotangent-vanishing-pile]]
  in a way that could be misread as requiring k̄-rational points
  ("show they globalise the Lie-algebra-at-identity to a global frame
  of `Ω_{G/k}`"). The over-k formulation MUST use the functorial
  shear iso `A ⊗ A → A ⊗ A`, not pointwise translation. This is a
  worded-clarification, not a substantive cost increase. **Cost
  impact: zero**.
- **Piece (iii) misreading risk**: if a future prover or planner is
  tempted to use relative Frobenius `F_{Y/k}` (which over non-perfect
  k would require `[PerfectField k]`), the argument would falsely
  appear to require perfectness. The over-k formulation MUST use
  absolute Frobenius `F_X`, which is intrinsic. **Cost impact: zero**,
  but worth a code comment in the iter-129+ blueprint chapter
  pointing this out.
- **Over-`k̄` baseline is still mathematically correct**: if the
  over-k path runs into a verification gap during iter-129+ build
  (e.g. discovery that some intermediate Mathlib API in fact requires
  alg-closure), the project can revert to the over-`k̄` + M2.c path
  with no loss. The two paths are not mutually exclusive; the over-k
  path is strictly cheaper if it lands.

## Verdict summary

| Piece | Verdict | LOC delta vs over-`k̄` |
|---|---|---|
| (i) cotangent triviality | OK_OVER_K | 0 |
| (ii) `df = 0 ⇒ const` | OK_OVER_K | 0 |
| (iii) Frobenius iteration | OK_OVER_K | 0 |
| **Meta (M2.c avoidability)** | **AVOIDED** | **−500 to −900 LOC, −7 to −13 iter** |

**Overall**: **adopt over-k**.

## Severity

**high-stakes** — the verdict directly determines whether the project's
iter-129+ build target is "over-`k̄` then descend" or "over-k directly",
with a 7–13 iter / 500–900 LOC delta. The verdict is **OK_OVER_K on
all three pieces**, so the project should adopt the over-k route and
drop M2.c / M2.c.aux from the sequencing.
