# LeanAG — Scope Roadmap (condensed)

A high-level, mathematical checklist across the scope's member projects.

**Legend:**

- [x] proved / sorry-free (or, for a theme, its keystone declarations are sorry-free)
- [~] in progress (declarations exist, residual `sorry`)
- [ ] not started (no Lean yet — blueprint only, or theme not begun)

**Status snapshot** *(open `sorry` counts measured over each project's `AlgebraicJacobian/`
source tree, comments/docstrings excluded; 2026-06-18):*

| Project | Stage | Open `sorry` |
| --- | --- | --- |
| Algebraic-Jacobian-Challenge | prover | 93 |
| Cech-Cohomology | ✅ complete | 0 |
| Line-Bundle-Comparison-Iso | prover | 2 |
| Quot-Foundations | prover | 21 |
| GR-quot_closure | prover | 13 |
| FBC-B_SNAP-chain | prover | 14 |
| 26 related-paper projects | 📝 blueprint only | 0 Lean (stub aggregators) |

---

## Dependency spine

### Core algebraic-geometry engine

- `Line-Bundle-Comparison-Iso` → `Algebraic-Jacobian-Challenge` (largest leverage: unblocks the Picard / comparison-iso substrate; merges back the `A.1.c.sub` package)
- `Cech-Cohomology` ↔ `Algebraic-Jacobian-Challenge` (the Čech `Rⁱf_*` engine is the cohomological substrate; proved sorry-free here, **merged into the AJC tree** 2026-06-18)
- `GR-quot_closure`, `FBC-B_SNAP-chain` → `Quot-Foundations` (extracted work packages of the Quot/Picard-representability cone; share the SNAP section-graded-ring foundation `Picard/SectionGradedRing.lean`)
- `Quot-Foundations` → `Algebraic-Jacobian-Challenge` (the H⁰ Picard-representability cone — flat base change, Grassmannian, Quot — merges back)

### Related papers that consume the AG base

These declare (or directly reference) infrastructure from the core engine. Only
`MR4213770` and `MR4228499` carry an explicit `*_PeerDependencies` blueprint chapter;
the rest reference the base informally.

- `Algebraic-Jacobian-Challenge` (H^i scheme cohomology), `Cech-Cohomology` (Rⁱf_*), `Quot-Foundations` (flat base change, stalkwise module-iso criterion) → **`MR4213770`** *(explicit PeerDependencies chapter)*
- `Algebraic-Jacobian-Challenge` (Jacobian, Weil divisors, symmetric powers Cⁿ, canonical differentials), `Cech-Cohomology` (Rⁱf_*) → **`MR4228499`** *(explicit PeerDependencies chapter)*
- `Algebraic-Jacobian-Challenge` (Jacobian, principal polarization, Torelli) → **`MR4276287`** *(informal references)*
- AG base (spectral curves / Jacobians, geometric Satake, arc spaces — not yet pinned to specific peers) → **`MR4433079`** *(aspirational)*
- `Algebraic-Jacobian-Challenge` (abelian varieties, curve geometry) → **`MR4665779`** *(conceptual; the blueprint is currently self-contained — the earlier `MR4199442+MR4213770+MR4228499 → MR4665779` paper-to-paper edges are **not** present in the blueprints and have been dropped)*

### Self-contained papers

The remaining 20 related-paper projects are **independent blueprint formalizations**: they
share the scope's conventions and tooling but declare **no dependency on the AG base**. See
the per-paper sections below.

---

## Algebraic-Jacobian-Challenge  *(core engine — prover stage, 93 open `sorry`)*

**Goal:** the Jacobian of a smooth proper geometrically-irreducible curve — smooth of
relative dimension = genus, proper, geometrically irreducible, and the Albanese variety
(`exists_unique_ofCurve_comp`). Spine = pointed vs. unpointed; 0 project axioms.

- [x] **Kähler-differential / cotangent substrate** — `Cotangent/GrpObj`, `Cotangent/ChartAlgebra`, `Differentials` (cotangent iso, chart algebra) **sorry-free**
- [x] **Rigidity & Abel–Jacobi scaffolding** — `Rigidity`, `RigidityLemma`, `Genus`, `AbelJacobi` **sorry-free**
- [x] **Line-bundle coherence substrate** — `Picard/LineBundleCoherence`, `Picard/LineBundlePullback`, `Picard/RelPicFunctor`, `Picard/RelativeSpec` **sorry-free** (local triviality, pullback-tensor compatibility)
- [x] **Čech higher-direct-image engine (A.2.c)** — the comparison theorem `cech_computes_higherDirectImage` and `pushPull` functoriality (`pushPullFunctor`, `pushPullMap_comp`) are **proved sorry-free in `Cech-Cohomology`** and merged in; `cechHigherDirectImage` is sorry-free in the AJC tree. *(The Čech theorem itself has no open mathematical gap.)*
- [~] **Čech merge clean-up & flat base change** — the AJC copy still carries **9 `sorry`**, but these are **not** gaps in the Čech engine: 7 are **MERGE-STUBs** — proofs proved upstream / preserved in-file, `sorry`-ed only to dodge build-time elaboration blow-ups during the merge (`CechSectionIdentificationLeg` ×5, `CechToHigherDirectImage` ×2), pending a clean restore — and 2 are the genuinely-open **flat base change** consumer (Stacks 02KH: `flatBaseChange_pushforward_isIso` in `FlatBaseChange`, `cech_flatBaseChange` in `CechHigherDirectImageUnconditional`) that *uses* the Čech infra
- [~] **Group schemes** — `Ga`, `Gm`, `ProjectiveLineBar` (ℙ¹) **defined**; `Genus0BaseObjects` carries **2 residual `sorry`** (`BareScheme`, `GmScaling`) *(was previously mismarked "not started")*
- [~] **Tensor/dual comparison substrate + Picard group (A.1.c.sub)** — `Picard/TensorObjSubstrate` defines `PicGroup`/`picCommGroup` and the slice-dual transport; **3 residual `sorry`** *(shared with `Line-Bundle-Comparison-Iso`)*
- [~] **Weil divisors & Riemann–Roch core** — order valuation, degree homomorphism, principal divisors, skyscraper SES (`RiemannRoch/*`, **15 `sorry`**: `RationalCurveIso`, `OcOfD`, `OCofP`, `WeilDivisor` ×3 each; `H1Vanishing` ×2; `RRFormula` ×1)
- [~] **Albanese / abelian-variety leg** — `Albanese/*` (**12 `sorry`**: `AlbaneseUP` ×7, `CodimOneExtension` ×3, `Thm32RationalMapExtension` ×2; `AuslanderBuchsbaum`, `CoheightBridge` sorry-free)
- [~] **Picard representability cone** — `Picard/QuotScheme` (×12), `IdentityComponent` (×9), `FGAPicRepresentability` (×7), `FlatteningStratification` (×7), `Pic0AbelianVariety` (×5) *(consumes the `Quot-Foundations` H⁰ leg)*
- [~] **Flatness & generic flatness** — flat-locus open → Noetherian stratification (`FlatteningStratification`; shared root with `Quot-Foundations`)
- [ ] **Smooth proper curves** — projectivity, normalization iso, function-field equivalence *(held: classically RR-dependent; Route C paused)*
- [ ] **Top goal: `Pic_{C/k}` representability + Jacobian = Albanese** *(once the substrate + engine themes close)*

## Cech-Cohomology  *(✅ complete — 0 open `sorry`)*

**Goal:** `cech_computes_higherDirectImage` — for a separated quasi-compact `f : X ⟶ S`,
a quasi-coherent `F`, and a finite affine open cover, the cohomology of the relative Čech
complex computes `Rⁱf_* F`. Unconditional (no enough-injectives appeal).

- [x] **Combinatorial / free Čech engine** — alternating coface complex, homotopy contraction, exactness
- [x] **Section Čech complex & localization comparison** — `AwayComparison`, `phi/phiL` naturality
- [x] **Affine acyclicity (Serre vanishing)** — tilde-vanishing ⇒ affine Čech vanishing
- [x] **Cover/nerve combinatorics** — Čech nerve, wide pullbacks, `pushPull` sigma iso, finitary-extensive distributivity
- [x] **Quasi-coherence on opens** — over-equivalences, restrict-to-basic-open, modules-over-opens equivalence
- [x] **Higher direct image & acyclicity** — injective resolutions, horseshoe lemma, pushforward acyclicity
- [x] **PushPull functoriality** — `pushPullMap` composition, leg coherence, pentagon
- [x] **Comparison theorem `cech_computes_higherDirectImage`** *(proved iter-079, 0 sorries)*

## Line-Bundle-Comparison-Iso  *(prover stage — extraction hub → Jacobian, 2 open `sorry`)*

**Goal:** the comparison-isomorphism substrate giving `Pic♯_{C/k}` its abelian-group
structure (the A.1.c.sub package; merges back into the Jacobian challenge).

- [x] **Stalk-tensor / internal-hom machinery** — `TensorObjSubstrate/StalkTensor`, `PresheafInternalHom` **sorry-free**
- [x] **Slice-dual transport iso (DUAL route)** — `TensorObjSubstrate/DualInverse`, `DualInverse/SliceTransport` **sorry-free**
- [x] **Line-bundle pullback / relative Pic functor** — `LineBundlePullback`, `RelPicFunctor` **sorry-free**
- [~] **Tensor unitors & Picard-group assembly** — `TensorObjSubstrate` (PicGroup/picCommGroup wiring), **2 residual `sorry`**

## Quot-Foundations  *(prover stage — 21 open `sorry`)*

**Goal:** the Čech-independent (i = 0) leg of FGA Picard representability — flat base
change, generic flatness, and Quot/Grassmannian foundations. The Grassmannian-quotient
representability endgame and the flat-base-change/SNAP legs are carved into the sibling
extractions `GR-quot_closure` and `FBC-B_SNAP-chain` (below); proofs merge back here.

- [x] **Grassmannian construction & gluing** — `GrassmannianCells`, `GlueDescent` **sorry-free** (rank-quotient setoid, charts, transition cocycle, effective descent)
- [x] **RelativeSpec / flattening stratification** — `RelativeSpec`, `FlatteningStratification` **sorry-free**
- [x] **Graded Hilbert–Serre helper** — `GradedHilbertSerre`, `RegroupHelper` **sorry-free**
- [~] **Flat base change (degree 0)** — `Cohomology/FlatBaseChange` (×4), `FlatBaseChangeGlobal` (×1); pushforward Mayer–Vietoris / finite-generation criteria
- [~] **Tautological / universal quotient** — `GrassmannianQuot` (×3): `represents` done, `tautologicalQuotient_epi` closing
- [~] **Quot scheme** — `QuotScheme` (×4): `RepresentableBy` upgrade + Quot-representability core
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×9): cast coherence → Hilbert polynomial *(shared with the sibling extractions)*

## GR-quot_closure  *(prover stage — 13 open `sorry`)*

**Goal:** representability of the relative Grassmannian — the Čech-independent (H⁰) leg that
builds `Grass(V, d)` from affine charts via the `GL_d` cocycle and proves it represents the
rank-`d`-quotient functor. Extracted from `Quot-Foundations`; merges back as a three-way merge.

- [x] **Grassmannian cells, gluing & descent** — `GrassmannianCells`, `GrassmannianQuot`, `GlueDescent`, `GradedHilbertSerre`, `RelativeSpec` **sorry-free**
- [~] **Quot scheme** — `QuotScheme` (×4): representability endgame
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×9) *(shared with `FBC-B_SNAP-chain`)*

## FBC-B_SNAP-chain  *(prover stage — 14 open `sorry`)*

**Goal:** the flat-base-change (FBC-B) leg of the Quot/Picard-representability cone, sharing the
SNAP section-graded-ring foundation with `GR-quot_closure`. *(Lean scaffolding has been
generated — this is no longer an empty extraction skeleton.)*

- [x] **Regroup helper** — `Cohomology/RegroupHelper` **sorry-free**
- [~] **Flat base change (FBC-B)** — `Cohomology/FlatBaseChange` (×4), `FlatBaseChangeGlobal` (×4): pushforward flat base-change leg
- [~] **Section graded ring (SNAP)** — `Picard/SectionGradedRing` (×6): shared foundation with `GR-quot_closure`

---

## Related papers  *(📝 blueprint stage — LaTeX blueprint written, Lean formalization not begun)*

All 26 related-paper projects below are blueprint-only: their Lean targets are stub
aggregators (0 real declarations). The checklist items track the **blueprint chapters**;
every Lean item is therefore `[ ]`.

### A. Papers that consume the AG base

#### MR4213770 — Universal secant bundles and syzygies of canonical curves  ·  needs Jacobian + Čech + Quot
**Main theorem:** generic Green's conjecture for general canonical curves (`K_{k,1}(C,ωC)=0` for general genus 2k/2k+1) and the even-genus geometric-syzygy structure theorem for K3 sections.

- [ ] **Peer dependencies** — Rⁱf_*, H^i scheme cohomology, pushforward base change, stalkwise module-iso *(explicit anchors)*
- [ ] **Universal secant bundles & syzygies** — universal zero locus, secant bundles, local freeness, Voisin's theorem, even-genus structure, geometric syzygy conjecture

#### MR4228499 — Bounds for the stalks of perverse sheaves in characteristic p  ·  needs Jacobian + Čech
**Main theorem:** the Massey stalk bound (stalk dim ≤ polar multiplicity of the characteristic cycle) and the Shende–Tsimerman Betti-number bound for theta-locus intersections in hyperelliptic Jacobians.

- [ ] **Peer dependencies** — Jacobian, Weil divisors, symmetric powers Cⁿ, canonical differentials, Rⁱf_*
- [ ] **Terminology & axioms** — conical cycles, polar multiplicities, transversality; nearby/vanishing cycles, singular support, characteristic cycles (as black boxes)
- [ ] **Massey bound** — polar-multiplicity equivalences, global polar bound
- [ ] **Shende–Tsimerman application** — theta-map characteristic cycle, pushforward decomposition, explicit bound

#### MR4276287 — Uniformity in Mordell–Lang for curves  ·  needs Jacobian
**Main theorem:** uniform bound `c^{1+ρ}` on rational points of genus-`g` curves over number fields of bounded degree (ρ = Mordell–Weil rank of the Jacobian).

- [ ] **Moduli space & Jacobian** — moduli stack of curves, Jacobian abelian variety, principal polarization, Torelli / universal family
- [ ] **Heights & positivity** — Weil heights on varieties and abelian groups, positivity conditions
- [ ] **Arithmetic Bézout & uniform bounds** — intersection-theoretic height estimates, Northcott, Rémond bound, Raynaud–Manin–Mumford, torsion-packet bounds

#### MR4433079 — Intersection complexes and unramified L-factors  ·  needs AG base (aspirational)
**Main theorem:** for type-T affine spherical varieties, the IC function on the arc space equals a ratio of local unramified L-values.

- [ ] **Group data & arc spaces** — reductive data, type-T condition, arc spaces, IC functions
- [ ] **Global models & central fibers** — Zastava spaces, spectral curves, Mirković–Vilonen cycles, Kashiwara crystal structure
- [ ] **Semi-smallness & dimension estimates** — semi-smallness of Zastava maps, central-fiber dimension bounds
- [ ] **IC formula & asymptotics** — nearby-cycle commutation, affine-closure formula, Plancherel decomposition

#### MR4665779 — A Chabauty–Coleman bound for surfaces  ·  conceptually needs Jacobian / abelian varieties
**Main theorem:** the Caro–Pastén Chabauty–Coleman bound for hyperbolic surfaces in abelian varieties of Mordell–Weil rank ≤ 1, with rational/quadratic-points applications.

- [ ] **Geometry interfaces & packages** — curves and surface singularities, abelian varieties and specialization
- [ ] **Local Chabauty–Coleman bound** — bound over Q_p extensions, specialization to Q_p
- [ ] **Number-field transfer & applications** — rational points, density-one and symmetric-square applications

### B. Self-contained blueprint formalizations  *(no AG-base dependency)*

#### MR4199442 — Standard conjectures for abelian fourfolds
**Main theorem:** the standard conjecture of Hodge type for abelian fourfolds in characteristic p (positive signature of the codimension-2 numerical intersection form).

- [ ] **Motives & realizations** — conventions, Chow–Künneth, Lefschetz formalism, CM structures
- [ ] **Exotic classes & quadratic forms** — exotic motives in H⁴, rank-two orthogonal motives, Hilbert symbol
- [ ] **p-adic periods & Clozel** — Hyodo–Kato realization, crystalline periods, num = ℓ-adic hom
- [ ] **Main theorem** — standard conjecture of Hodge type

#### MR4258055 — A refined Brill–Noether theory over Hurwitz spaces
**Main theorem:** for general degree-`k` genus-`g` covers, the Brill–Noether splitting locus is smooth of pure dimension `g − u(⃗e)` (empty when `u > g`).

- [ ] **Splitting types & loci** — bundles on ℙ¹, balanced bundles, expected codimension, degeneracy loci
- [ ] **Degeneration & smoothness** — elliptic pushforward, deformation-theoretic smoothness, Hurwitz conditions

#### MR4372220 — Anticyclotomic Iwasawa theory at Eisenstein primes
**Main theorem:** structure of anticyclotomic Selmer groups / Heegner–Howard–Kolyvagin systems for rational elliptic curves at Eisenstein primes.

- [ ] **Local Iwasawa & Selmer** — local Iwasawa theory, Selmer groups
- [ ] **Algebraic / analytic comparison** — algebraic and analytic Iwasawa comparison
- [ ] **Howard–Kolyvagin & main conjecture** — Kolyvagin construction, main-conjecture applications

#### MR4411733 — Very stable Higgs bundles, equivariant multiplicity and mirror symmetry
**Main theorem:** classification of very stable Higgs bundles (Białynicki-Birula theory), the multiplicity formula, and mirror-symmetry (Fourier–Mukai) isomorphisms.

- [ ] **Classification & BB partition** — very stable Higgs bundles, weight decomposition
- [ ] **Multiplicity & mirror symmetry** — multiplicity formula, mirror bundle / Fourier–Mukai, equivariant Euler pairing

#### MR4413746 — Rigid local systems and the multiplicative eigenvalue problem
**Main theorem:** bijection between rigid irreducible unitary local systems on ℙ¹ and F-vertices of the multiplicative eigenvalue polytope; no rigid irreducibles of rank > 1 when n is prime.

- [ ] **Rigid local systems & polytope** — irreducibility, multiplicative eigenvalue vertices
- [ ] **Parabolic parametrization & duality** — F-line bundles on parabolic bundles, strange duality
- [ ] **Schubert calculus & asymptotics** — quantum Schubert calculus, GW inequalities, nearby cycles

#### MR4419629 — Squarefree values of polynomial discriminants I
**Main theorem:** the density of monic integer polynomials with squarefree discriminant exists and equals an explicit Euler product; maximal-order density is ζ(2)⁻¹.

- [ ] **Densities & local integrals** — height/discriminant definitions, p-adic local densities
- [ ] **Invariant theory & orbit counting** — SO_n invariant theory, geometry-of-numbers (odd/even degree)
- [ ] **Main density theorems** — squarefree-discriminant and maximal-order densities, monogenic fields

#### MR4433080 — Hitchin fibrations, abelian surfaces and the P=W conjecture
**Main theorem:** P=W for genus-2 curves (all rank); the conjecture on the even tautological subalgebra in all genera.

- [ ] **Setup & filtrations** — Hitchin fibration, character variety, NAH diffeomorphism, weight/perverse filtrations
- [ ] **Tautological classes & perverse sheaves** — twisted Chern character, perverse truncation/splitting
- [ ] **Abelian surfaces & genus-2 result** — Hilbert–Chow, Markman monodromy, even/odd tautological perversity

#### MR4448992 — Geometric Bogomolov conjecture in arbitrary characteristics
**Main theorem:** small-points-dense subvarieties of abelian varieties over function fields are special (translate of an abelian subvariety by a torsion point).

- [ ] **Heights & small points** — naive/canonical heights, special subvarieties, K/k-trace
- [ ] **Non-proper intersections** — Chow groups, Bertini, excess locus, comparison inequality
- [ ] **Descent & reduction** — lowering transcendence degree, Yamaki reduction, Manin–Mumford application

#### MR4493324 — The universal p-adic Gross–Zagier formula
**Main theorem:** the p-adic height of the universal Heegner class over a Hida family equals the cyclotomic derivative of the p-adic L-function (with classical-point specializations).

- [ ] **Setup & Galois representations** — Shimura varieties, automorphic reps, Bloch–Kato/Nekovář Selmer complexes
- [ ] **Height pairing & Heegner classes** — p-adic height pairing, Heegner cycles, universal class over Hida families
- [ ] **Main theorems** — p-adic BBK, Gross–Zagier, universal-class interpolation

#### MR4513142 — There is no Enriques surface over the integers
**Main theorem:** the moduli stack of Enriques surfaces over Spec(ℤ) is empty (no flat proper family over ℤ).

- [ ] **Picard schemes & Enriques surfaces** — numerically trivial Picard scheme, exceptional vs non-exceptional
- [ ] **Families & reduction to ℤ** — constant Picard scheme, Minkowski/Brauer vanishing, canonical coverings
- [ ] **Nonexceptional classification** — Weierstrass/Jacobian fibrations, elimination of Kodaira symbols

#### MR4583777 — Tate's thesis in the de Rham setting
**Main theorem:** a canonical DG equivalence `D^!(LLA) ≅ IndCohStar(Y)` between sheaves on the algebraic loop space and ind-coherent sheaves on a moduli of rank-1 de Rham local systems.

- [ ] **Loop spaces & moduli Y** — loop space LLA, rank-1 de Rham local systems, derived equalizer / gauge quotient
- [ ] **Ind-coherent sheaves** — Coh/IndCohStar, t-structure, semi-coherence
- [ ] **Spectral realization & equivalence** — Weyl-algebra convolution, main DG equivalence

#### MR4628606 — Pixton's formula and Abel–Jacobi theory on the Picard stack
**Main theorem:** Pixton's formula computes the universal twisted double-ramification cycle on the Picard stack and vanishes above codimension g.

- [ ] **DR cycles & prestable graphs** — double ramification cycles, decorated graphs
- [ ] **Pixton's formula & vanishing** — modular construction, vanishing above codim g
- [ ] **Twisted differentials & universal formula** — Farkas–Pandharipande Conjecture A, invariance, degree-0 universal formula

#### MR4654610 — Computing Riemann–Roch polynomials and classifying hyper-Kähler fourfolds
**Main theorem:** every hyper-Kähler fourfold of K3^[2] numerical type is of K3^[2] deformation type (O'Grady), with explicit Huybrechts–Riemann–Roch polynomial.

- [ ] **HK fourfolds & BBF form** — numerical/deformation types, Beauville–Bogomolov–Fujiki form, Fujiki constant
- [ ] **Riemann–Roch & Lagrangian fibrations** — Huybrechts–RR polynomial, Lagrangian fibrations, SYZ in dim 4

#### MR4681144 — Purity for flat cohomology
**Main theorem:** for a Noetherian local complete intersection ring and a finite flat group scheme G, flat cohomology `H^i_m(R,G)` vanishes for `i < dim R`.

- [ ] **Absolute cohomological purity** — étale purity/semipurity, perfectoid purity
- [ ] **Perfectoid geometry & prime-to-char aspects** — integral perfectoid rings, Lefschetz hyperplane, excision, André's lemma

#### MR4681148 — Motivic invariants of birational maps
**Main theorem:** construction of motivic invariants `c`, `c̃` for birational maps over an arbitrary field, with structure results on truncated Grothendieck groups and the graded Burnside ring.

- [ ] **Varieties & birational maps** — notation, exceptional sets
- [ ] **Motivic invariant & structure** — invariant `c`, truncated Grothendieck groups, birational-class structure

#### MR4688702 — On the birational section conjecture with strong birationality assumptions
**Main theorem:** every birational Galois section of a smooth geometrically connected curve over a finitely generated field is cuspidal (BSC).

- [ ] **Fundamental gerbes & specializations** — étale fundamental gerbes, root-stack non-unique specializations
- [ ] **Liftable sections & main argument** — t-birationally liftable sections, specializing loops, uniqueness criteria

#### MR4689373 — Higher Siegel–Weil formula for unitary groups: the non-singular terms
**Main theorem:** for Hermitian bundles on `X'`, the r-th derivative of the normalized Eisenstein series equals the degree of the special cycle (higher Siegel–Weil, non-singular terms).

- [ ] **Geometric side** — moduli of Hermitian shtukas, special cycles, virtual fundamental classes
- [ ] **Springer / perverse sheaves** — Hermitian Springer sheaf, perverse sheaves on Herm_2d, Weyl-group reps
- [ ] **Assembly** — sheaf–function correspondence comparison

#### MR4712868 — Virasoro constraints on moduli of sheaves and vertex algebras
**Main theorem:** Virasoro constraints hold for moduli of semistable sheaves on curves and on surfaces with `h^{1,0}=h^{2,0}=0`, as primary-state conditions in Joyce's vertex algebra.

- [ ] **Virasoro operators & VOAs** — weight-zero descendents, vertex operator algebras, primary states
- [ ] **Joyce's vertex algebra & proof** — sheaf-theoretic vertex algebra, lattice VOA iso, wall-crossing, proof via primary states

#### MR4717077 — Canonical representations of surface groups
**Main theorem:** any MCG-finite representation `ρ: π₁(Σ_{g,n}) → GL_r(ℂ)` with `r < √(g+1)` has finite image.

- [ ] **Preliminaries & non-abelian Hodge** — Birman sequence, MCG-finiteness, unitarity from VHS
- [ ] **Period maps & rank bounds** — bilinear pairings, cohomological rank bounds/vanishing
- [ ] **Main proof** — asymptotic Putman–Wieland, cohomological rigidity / integrality

#### MR4736527 — Geometric local systems on very general curves and isomonodromy
**Main theorem:** on a suitably general n-pointed genus-`g` curve, the minimal rank of a non-isotrivial local system of geometric origin is ≥ `2√(g+1)` (Esnault–Kerz / Budur–Wang conjectures).

- [ ] **Foundations & parabolic structures** — hyperbolic pointed curves, Hodge structures, very general points, parabolic bundles
- [ ] **Isomonodromy & Hodge theory** — isomonodromic deformation, variations of Hodge structure, Harder–Narasimhan filtration
- [ ] **Counterexample & main results** — Kodaira–Parshin construction, Hodge-theoretic rank bound

#### MR4792069 — The P=W conjecture for GL_n
**Main theorem:** P=W for `GL_n` character varieties of smooth projective curves of genus ≥ 2 (perverse filtration = weight filtration).

- [ ] **Setup & filtrations** — character varieties, Hitchin fibration, weight/perverse filtrations
- [ ] **Perversity & support** — strong perversity of tautological Chern classes, vanishing cycles, global Springer theory, parabolic support theorem
- [ ] **Comparison** — curious Hard Lefschetz, P=W comparison
