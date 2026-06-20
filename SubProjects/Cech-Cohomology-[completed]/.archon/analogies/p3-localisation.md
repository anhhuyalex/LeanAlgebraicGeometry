# Analogy: representing & proving P3 (standard-cover Čech acyclicity on affines)

## Mode
api-alignment

## Slug
p3-localisation

## Iteration
010

## Question

How should the project represent and prove **P3** — positive-degree exactness of the
standard-cover Čech complex of an affine scheme — for `Scheme.Modules`? Two coupled
decisions: (a) the Lean *encoding* of "a standard affine open cover of `Spec A`"
(bespoke `Fin n` structure / predicate on an `OpenCover` / Mathlib affine-cover API);
(b) how to represent the complex-and-exactness: (1) does Mathlib already have the
algebra-level Čech-of-localizations exactness (`Algebra.lemma-cover-module`)? (2) the
idiomatic "exact after localizing at every prime" certifier? (3) contracting homotopy
via `Homotopy`/`HomotopyEquiv` on a `CochainComplex`, or via an augmented-simplicial
extra degeneracy Mathlib already knows is exact?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:764-774` — `CechAcyclic.affine`
  (the P3 `sorry`; currently a *general* `𝒰 : X.OpenCover` signature). NOT protected.
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:737-745` — `CechComplex`
  (takes general `OpenCover`; built abstractly via `relativeCechComplexOfNerve`).
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:801-811` —
  `cech_computes_higherDirectImage` (**PROTECTED**, general `𝒰 : X.OpenCover`).
- `blueprint/.../Cohomology_CechHigherDirectImage.tex` — `lem:cech_acyclic_affine`,
  `lem:cech_augmented_resolution`, `lem:cech_to_cohomology_on_basis`.

## Decisions identified

### Decision (a): encoding of "standard affine cover of Spec A"

- **Mathlib idiom**: `AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop`
  (`Mathlib.AlgebraicGeometry.Cover.Open`):
  ```
  affineOpenCoverOfSpanRangeEqTop {R : CommRingCat} {ι : Type*}
    (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤) : (Spec R).AffineOpenCover
  ```
  with the proven defining equation
  `affineOpenCoverOfSpanRangeEqTop_f : (… ).f i = Spec.map (algebraMap R (Localization.Away (s i)))`
  and the projection `AffineOpenCover.openCover : X.OpenCover`. So Mathlib already
  encodes "standard cover of `Spec R` from a spanning family" as exactly the data
  `(s : ι → R, hs : Ideal.span (Set.range s) = ⊤)`. Supporting API:
  `PrimeSpectrum.iSup_basicOpen_eq_top_iff' : (⨆ i ∈ s, basicOpen i = ⊤) ↔ Ideal.span s = ⊤`
  and `IsAffineOpen.self_le_iSup_basicOpen_iff`.
- **Project's current path**: general `𝒰 : X.OpenCover` on `CechAcyclic.affine`; the
  directive proposes narrowing. Of the three options floated: (i) bespoke
  `(f : Fin n → A) + hspan`; (ii) predicate on an existing `OpenCover`; (iii) Mathlib's
  affine-cover API.
- **Gap**: divergent-with-cost for options (i)/(ii); option (iii) is identical to idiom.
- **Cost of divergence**: the decisive point is that the **same** spanning-family bundle
  `(s, hs : Ideal.span (Set.range s) = ⊤)` is what the algebra-side certifier
  `exact_of_isLocalized_span` *also* consumes (see (b2)) — it wants `Ideal.span s = ⊤`
  and `IsLocalizedModule.Away (s i)`. So if `CechAcyclic.affine` carries `(s, hs)` and
  builds the cover via `affineOpenCoverOfSpanRangeEqTop s hs |>.openCover`, one data
  bundle drives **both** the geometry (cover) and the algebra (exactness) with zero
  bridge lemmas. A bespoke `Fin n` structure (option i) would need two conversion lemmas
  (to `affineOpenCoverOfSpanRangeEqTop` and to the `exact_of_isLocalized_span` shape).
  A predicate on an arbitrary `OpenCover` (option ii) is worst: it forces a
  "this cover is iso to the standard one" comparison at every use site and re-derives
  the `D(f_i)`-structure that Mathlib already packages.
- **Verdict**: ALIGN_WITH_MATHLIB (option iii). Take `(s : ι → Γ(X,O), hs)` as the
  hypotheses; obtain the cover from `affineOpenCoverOfSpanRangeEqTop`.
- **Frozen-signature note**: `cech_computes_higherDirectImage` is protected with a
  general `𝒰 : X.OpenCover`, and `CechComplex` takes a general `OpenCover` — both stay
  as-is. The narrowing is ONLY on the non-protected `CechAcyclic.affine`. This is
  consistent with the existing blueprint design: the protected consumer reaches affine
  acyclicity through the basis-comparison on *standard* covers
  (`cech_eq_cohomology_of_basis` / `affine_serre_vanishing`), not through the user's
  `𝒰` directly, so `CechAcyclic.affine` is free to be stated for the standard cover.

### Decision (b1): does Mathlib have the algebra Čech-of-localizations exactness?

- **Mathlib idiom**: NONE. Searched leansearch/loogle for the `Algebra.lemma-cover-module`
  analogue — exactness of `0 → M → ∏ M_{f_i} → ∏ M_{f_i f_j} → ⋯`. Mathlib has only:
  the degree-≤1 *sheaf condition* for the structure sheaf
  (`TopCat.Presheaf.IsSheafEqualizerProducts`, `StructureSheaf` gluing, structure-sheaf
  `objSupIsoProdEqLocus`), which is the `M → ∏ M_{f_i} ⇉ ∏ M_{f_i f_j}` *equalizer*
  (kernel/H⁰+H¹ only), and the local-to-global certifiers of (b2). The full positive-degree
  complex exactness is absent.
- **Project's current path**: build it from scratch (the `CechAcyclic.affine` sorry).
- **Gap**: divergent-and-necessary — there is no idiom to align to here.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. This is the genuinely from-scratch core of P3.

### Decision (b2): "exact after localizing" certifier

- **Mathlib idiom** (HIGHEST-VALUE FIND): `Mathlib.RingTheory.LocalProperties.Exactness`:
  ```
  exact_of_isLocalized_span (s : Set R) (hs : Ideal.span s = ⊤)
    (Mₚ Nₚ Lₚ : ↑s → Type*) … (f r : IsLocalizedModule.Away ↑r) …
    (F : M →ₗ[R] N) (G : N →ₗ[R] L) :
    (∀ r : s, Function.Exact (map (powers ↑r) (f r) (g r) F)
                             (map (powers ↑r) (g r) (h r) G)) →
    Function.Exact ⇑F ⇑G
  ```
  This is the Mathlib analogue of Stacks `algebra-lemma-characterize-zero-local`, but
  localizing at the **spanning elements** (`Away ↑r` = `M_{f_r}`) rather than at primes —
  a strictly better match to the Čech setting. Sibling `exact_of_isLocalized_maximal`
  (localize at every maximal ideal, `AtPrime`) is the literal prime-local version;
  `exact_of_localized_span` / `exact_of_localized_maximal` are the `Localization`-typed
  variants. Also present: `injective_/surjective_/bijective_of_isLocalized_span` and the
  `_maximal` family.
- **Project's current path**: blueprint proof currently phrased via primes
  ("localising at an arbitrary prime 𝔭", Stacks). The element-localization certifier is
  cleaner and Mathlib-native.
- **Gap**: identical (this IS the idiom for local-to-global exactness).
- **Verdict**: ALIGN_WITH_MATHLIB. Apply `exact_of_isLocalized_span` with `s = Set.range f`
  node-by-node: positive-degree homology vanishing of the cochain complex at degree `p`
  is `Function.Exact (d^{p-1}) (d^p)`; reduce it to `Function.Exact` of each `Away (f_r)`
  localization. After inverting `f_r` itself, the cover member `D(f_r)` is the whole space,
  so the contracting homotopy with `i_fix = r` exists *globally on the localization* — no
  passage to a prime needed. (Needs: localization of the finite product term commutes,
  `(∏_σ M_{f_σ})_{f_r} ≅ ∏_σ M_{f_σ f_r}` — available via `IsLocalizedModule`/finite `Pi`,
  e.g. `IsLocalization.instForallPiUniv`.)

### Decision (b3): contracting-homotopy idiom

- **Mathlib idiom**: `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy` +
  `ExtraDegeneracy.homotopyEquiv` (`Mathlib.AlgebraicTopology.ExtraDegeneracy`): an extra
  degeneracy on an augmented **simplicial** object yields a `HomotopyEquiv` between its
  `AlternatingFaceMapComplex` (a *chain* complex) and the point — precisely the Stacks
  homotopy `h(s)_{i₀…i_p} = s_{i_fix i₀…i_p}`. BUT two mismatches:
  (1) it is the **simplicial**/chain-complex (`AlternatingFaceMapComplex`) statement; the
      project's `CechComplex` is **cosimplicial** + `alternatingCofaceMapComplex` (a
      *cochain* complex), and Mathlib has **no cosimplicial dual** of `ExtraDegeneracy`;
  (2) there is no *global* `i_fix` — the extra degeneracy exists only after localizing at
      `f_{i_fix}`.
- **Gap**: divergent-with-cost if routed through the simplicial API; the dualization plus
  the global-vs-local mismatch makes a direct dependency heavy.
- **Verdict**: PARTIAL → NEEDS_MATHLIB_GAP_FILL (build a small local homotopy, don't port).
  Recommendation: do the contracting homotopy at the **algebra/module level** on the
  localized cochain complex of `M_{f_σ f_r}`'s — either as a `CategoryTheory.Homotopy` on
  the `CochainComplex`, or (simpler) just prove the 3-term `Function.Exact` per node from
  the explicit `dh + hd = id` computation and feed `exact_of_isLocalized_span`. The
  explicit module homotopy is a few lines and sidesteps the cosimplicial-extra-degeneracy
  infrastructure Mathlib lacks. Keep `ExtraDegeneracy.homotopyEquiv` in mind as the
  *template* for the formula, not as a code dependency.

## Recommendation

Narrow `CechAcyclic.affine` to carry the spanning-family data `(s : ι → A, hs :
Ideal.span (Set.range s) = ⊤)` and build its cover with
`affineOpenCoverOfSpanRangeEqTop s hs |>.openCover` (Decision a, ALIGN). The protected
`cech_computes_higherDirectImage` / `CechComplex` keep their general-`OpenCover`
signatures untouched — the basis-comparison route already isolates standard covers, so
only the non-protected `CechAcyclic.affine` changes. For the proof, the three-layer
bridge is: (L1, gap-fill) identify `CechComplex` on the standard cover with the module
complex `∏_σ M_{f_σ}` via `Γ(D(f_σ)) = M_{f_σ}`; (L2, ALIGN) feed each positive-degree
node to `exact_of_isLocalized_span` with `s = Set.range f`; (L3, gap-fill) supply the
explicit `Away (f_r)`-local contracting homotopy `h(s)_{i₀…i_p} = s_{r i₀…i_p}` giving
`Function.Exact` of the localized differentials. Mathlib provides L2 and the cover
constructor outright — do NOT reinvent them; the genuinely from-scratch work is L1 (the
geometry↔algebra section-localization bridge) and the L3 module homotopy. Avoid routing
through Mathlib's *simplicial* `ExtraDegeneracy` — it is the wrong variance (chain vs.
cochain) and has no cosimplicial dual.
