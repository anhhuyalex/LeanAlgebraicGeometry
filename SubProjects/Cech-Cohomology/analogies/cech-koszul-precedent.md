# Čech / Koszul / acyclic-cover precedent audit (iter-059)

## Project context

Iter-053–058 set up the infrastructure for a forthcoming Čech-acyclicity
proof on basic-open covers:

- `class HasAffineCechAcyclicCover F` (iter-053) — for every affine `U`, the
  existence of a cover `𝒰` of `U` such that `[IsCechAcyclicCover F 𝒰]` and
  `[HasCechToHModuleIso F 𝒰]`.
- `basicOpenCover s : s → Opens` and its supremum / membership /
  pairwise- / Finset-`inf'`-intersection identifications
  (iter-054 → iter-058).
- `class IsCechAcyclicCover F 𝒰` (iter-048) — positive-degree
  Čech cohomology subsingleton.
- `class HasCechToHModuleIso F 𝒰` (iter-050) — `Nonempty`-wrapped
  `∀ n, cechCohomology n ≃ₗ[k] HModule' k F n (⨆𝒰)`.

The project now needs, for `F := toModuleKSheaf C`,

1. `IsCechAcyclicCover (toModuleKSheaf C) (basicOpenCover s)` whenever
   `Ideal.span (s : Set Γ(C.left, U)) = ⊤`.
2. `HasCechToHModuleIso (toModuleKSheaf C) (basicOpenCover s)` for the same
   `s`.

Before committing iter-059+ to the project-local construction, this analogy
call audits Mathlib for prior art.

## What `cechComplexFunctor` produces

`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean:65`

```lean
noncomputable def cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech
```

Unfolding the constituents:

- `FormalCoproduct.cochainComplexFunctor E = cosimplicialObjectFunctor E
  ⋙ AlgebraicTopology.alternatingCofaceMapComplex A`
  (`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean:53`)
- `cosimplicialObjectFunctor E = evalOp C A ⋙ (whiskeringLeft _ _ _).obj
  E.rightOp` (same file, L43)
- `(FormalCoproduct.mk _ U).cech.obj ⦋n⦌ = U.power (Fin (n+1))`, whose
  underlying object in `C` is `∏ᶜ (U ∘ i)` indexed by
  `i : Fin (n + 1) → ι` (`Mathlib/CategoryTheory/Limits/FormalCoproducts/Cech.lean:34,186`)

In our setting `C = (Opens C.left.toTopCat)ᵒᵖ`, `A = ModuleCat k`,
`P = (sheafToPresheaf _ _).obj F`, finite products in `Opens` are infima.
The cochain at degree `n` is therefore exactly

```
∏_{x : Fin (n+1) → ι} F(⨅ k : Fin (n+1), 𝒰 (x k))
```

— a `Module k` product (not a Π-type) inside `ModuleCat.{u} k`.
The differential `d^n` is the standard alternating sum
`∑_{j : Fin (n+2)} (-1)^j · δ_j` (Mathlib's `alternatingCofaceMapComplex`,
`Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean:67`).

**Crucial caveat**: this is the *unaugmented* Čech complex. There is no
`F(U) → ∏_i F(𝒰 i)` term sitting in degree `-1`. Standard Čech-acyclicity
for affine covers is usually stated about the *augmented* complex (Stacks
01EJ / 03B1), so the project either has to build the augmentation
explicitly, or carry the equivalent reasoning at the level of the
unaugmented homology (using the sheaf axiom for degree 0).

## What Mathlib has

### Precedent: `CategoryTheory.cechComplexFunctor` (definition only)

`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean:65` — file path
**confirmed unchanged** since iter-047; the import statement in
`AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean:784,796,813`
still resolves.

```lean
noncomputable def cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ
```

Used by iter-012 / iter-047 to define `cechCochain_OC`, `cechCochain`,
`cechCohomology`. No comparison theorem to derived functors is bundled
with the construction.

### Precedent: `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`

`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:328`

```lean
noncomputable def homotopyEquiv [Preadditive C] [HasZeroObject C]
    {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj X))
      ((ChainComplex.single₀ C).obj (point.obj X))
```

Augmented-simplicial-with-extra-degeneracy ⇒ alternating face map complex
is homotopy equivalent to the constant complex on the augmentation. This
is the **engine** for proving that a Čech complex over a "good" cover is
null-homotopic in positive degrees: the work that would otherwise be the
alternating-sum-cancellation argument is encapsulated here. Note this is
on `AlternatingFaceMapComplex` (chain complex) rather than
`alternatingCofaceMapComplex` (cochain complex) — a dual will need to be
spelled out (or extracted by op).

### Precedent: `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech`

`Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean:92`

```lean
noncomputable def extraDegeneracyCech {i₀ : U.I} (d : T ⟶ U.obj i₀) :
    (U.cech.augmentOfIsTerminal (isTerminalIncl _ hT)).ExtraDegeneracy
```

Specialises `homotopyEquiv` to the formal-coproduct Čech object: given a
"vertex" — a section `T ⟶ U.obj i₀` of one of the cover terms from the
terminal — the augmented Čech object has an extra degeneracy. **This is
what fires after localizing at a single `f_i`**: in `D(f_i)`, the basic
open `D(f_i)` is a unit, so the affine `Spec(R[1/f_i]) = D(f_i)` is the
terminal of the cover-of-`D(f_i)` slice, and the inclusion `D(f_i) ⊂
D(f_i)` (i.e. the cover's `i₀ = i` member) supplies the section. Modulo
op-direction bookkeeping, this gives "Čech complex over `D(f_i)` is
null-homotopic in positive degrees" almost for free.

### Precedent: `exact_of_isLocalized_span`

`Mathlib/RingTheory/LocalProperties/Exactness.lean:173`

```lean
lemma exact_of_isLocalized_span (H : ∀ r : s, Function.Exact
    (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G
```

(plus its sibling at L211, `exact_of_localized_span`, which directly
takes `f : M →ₗ N` without prequalifying localization data.)

Hypothesis shape: for each generator `r ∈ s` with `span s = ⊤`,
`map (.powers r) (f r) (g r) F` (the induced map between localizations)
is composed with `map (.powers r) (g r) (h r) G` to be exact. Conclusion:
`F` and `G` are exact unlocalized.

**This is the spanning-set Koszul-style local exactness lemma**. The
iter-057 correction (noting the project's iter-056 docstring referenced a
non-existent `exact_of_localized_span` without the "is" prefix) was an
overcorrection: both `exact_of_localized_span` and
`exact_of_isLocalized_span` exist; the former is the user-facing direct
form, the latter is the explicit-localization-data form. The iter-058
report should clarify both forms exist and which one the iter-059+ work
will actually call.

### Precedent: `IsLocalizedModule.map_exact`

`Mathlib/Algebra/Module/LocalizedModule/Exact.lean:56`

```lean
theorem IsLocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (ex : Function.Exact g h) :
    Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h)
```

Localization preserves exactness chain-level. Used as a sub-lemma in
`exact_of_isLocalized_span`, but on its own it's the converse direction
(unlocalized exact ⇒ localized exact), which is what we need to *transit*
from "all localizations exact" to "complex is exact at each `D(f_i)`":
the project will need `IsLocalizedModule.map_exact` if it wants to
identify each "localized Čech differential" with the Čech differential of
the cover-of-`D(f_i)` slice.

### Precedent: `IsAffineOpen.isLocalization_of_eq_basicOpen`

`Mathlib/AlgebraicGeometry/AffineScheme.lean:716`

```lean
include hU in
theorem isLocalization_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U)
    (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra
```

Given an affine `U` and a section `f`, any open `V ≤ U` definitionally
equal to `X.basicOpen f` is identified with `Localization.Away f Γ(X, U)`
on sections. The morphism arg `(i : V ⟶ U)` is load-bearing because it
installs the `Algebra Γ(X, U) Γ(X, V)` instance via the
`(X.presheaf.map i.op).hom.toAlgebra` algebra structure — i.e. *not* via
the standard `algebra_section_section_basicOpen` instance (L724,
`Mathlib/AlgebraicGeometry/Scheme.lean`), which only fires for the
syntactic form `Γ(X, X.basicOpen f)`.

**Project-side calling pattern** for the n-ary intersection:

```lean
hU.isLocalization_of_eq_basicOpen (∏ i ∈ t, (i.1 : Γ(C.left, U)))
    (homOfLE (basicOpenCover_finset_inf'_le s t h))   -- iter-058
    (basicOpenCover_finset_inf'_eq_basicOpen_prod s t h)  -- iter-057
```

lands `IsLocalization.Away (∏ i ∈ t, i.1) Γ(C.left, t.inf' h
(basicOpenCover s))` directly. The iter-058 `basicOpenCover_finset_inf'_le`
exists precisely to feed this morphism slot.

### Precedent: `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact`

`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean:140`

```lean
lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact
```

The Mayer-Vietoris LES for `Sheaf J AddCommGrpCat`. *No* `ModuleCat k`
version, but iter-014+ provided the iter-014 LES on `HModule'` directly
(blueprint `Cohomology_MayerVietoris.tex`).

This is the *only* derived-functor cohomology spectral-sequence-adjacent
theorem in Mathlib's site-cohomology stack — it does NOT generalise to a
Čech-to-derived comparison.

### Absent precedent: Čech-vs-derived comparison

**Mathlib has no theorem stating that an acyclic cover gives `cechCohomology
≃ Ext`** (i.e. Stacks 01EW / 03F7). I searched:

- `Mathlib/CategoryTheory/Sites/SheafCohomology/` — only `Basic.lean`,
  `Cech.lean`, `MayerVietoris.lean`. The TODO in `Basic.lean:30-34`
  envisions only `Sheaf.H F n ≃ cohomologyPresheaf F n (op terminal)`.
- `Mathlib/Algebra/Homology/SpectralSequence/` — only abstract
  spectral-sequence machinery (Basic.lean, ComplexShape.lean); no Čech
  instance, no Leray spectral sequence.
- `Mathlib/Algebra/Homology/SpectralObject/` — same comment; abstract
  framework only.
- Search for `Stacks "03F7"`, `Stacks "01EW"`, `Stacks "01EO"`,
  `Stacks "03OU"`, `Stacks "03AV"` in `.lake/packages/mathlib`: no hits.

The closest near-miss is the `MayerVietoris.sequence_exact` precedent
above, which gives the LES (and is in fact a degenerate special case of
the Čech-to-cohomology spectral sequence on a 2-element cover), but the
generalisation to `n`-element covers is not there.

### Absent precedent: Koszul complex / Koszul resolution

**Mathlib has no `KoszulComplex` file** (search:
`Mathlib/LinearAlgebra/KoszulComplex.lean`, `Mathlib/Algebra/Homology/Koszul/`,
`*Koszul*` glob — none). The project must either build a Koszul-complex
formalisation (large) **or** go via the localization-at-each-`f` route
described below — which is what the standard pre-Koszul proof of Čech
acyclicity uses anyway.

## Cited references

### Stacks Project §01ED (Čech cohomology)

The acyclicity-on-affine proof in the Stacks Project (tag 01ED, sections
on Čech cohomology of quasicoherent sheaves on affine schemes) goes as
follows, *without* invoking Koszul:

1. For an affine `U = Spec R`, a finite cover `𝒰 = (D(f_i))_i` with
   `(f_i)` generating the unit ideal of `R`, and a quasi-coherent `F`
   with `M = F(U)`, the augmented Čech complex
   `0 → M → ∏_i M[1/f_i] → ∏_{ij} M[1/f_i f_j] → ...` is exact.

2. **Proof**: exactness is local on `D(f_i)` for each `i`. Localising at
   `f_i`, the augmented Čech complex over `D(f_i)` has `D(f_i)` as a cover
   member (`f_i` is a unit in `R[1/f_i]`), giving an extra degeneracy
   via "inclusion of the vertex". By the standard extra-degeneracy
   homotopy, the localised augmented complex is contractible, hence
   exact.

3. By "exact on each open of a spanning cover ⇒ exact globally" (which
   is `exact_of_isLocalized_span` in Mathlib), the original augmented
   complex is exact.

This route is the most economical for our setting: it requires *no*
Koszul-complex machinery; Mathlib's `ExtraDegeneracy.homotopyEquiv`
encapsulates the alternating-sum cancellation; and the local-to-global
step is exactly `exact_of_isLocalized_span`.

### Stacks Project §03OU (Čech-to-cohomology spectral sequence)

The general comparison `H^p(C^•(𝒰, F)) → H^p(U, F)` (Čech-to-derived
edge map) extends to a spectral sequence
`E^{p,q}_2 = Ȟ^p(𝒰, H^q(F)) ⇒ H^{p+q}(U, F)`. When the cover is acyclic
(all `H^q(intersection, F) = 0` for `q > 0`), the spectral sequence
degenerates and the edge map is an isomorphism. Mathlib does not have
this spectral sequence in any form. **For the project, the most
economical substitute** is to construct the edge map directly (without
the spectral sequence) by:

- Producing the augmented Čech complex `C^• : 0 → F(U) → C^0 → C^1 → ...`
  on the affine. By step (1)–(3) above, this is acyclic, hence a
  resolution of `F(U)`.
- Sheaf-evaluating against an injective resolution of `F` (Mathlib does
  not provide injective sheaves in general, so this is the bottleneck).
- Identifying the resulting double-complex bipartite homology with
  `Ext`.

Honest Lean blueprint estimate for the comparison: ~200-400 LOC.

## Comparison with the project

### What the project currently has

- `Scheme.cechCochain` (iter-047): `(cechComplexFunctor 𝒰).obj
  ((sheafToPresheaf _ _).obj F)` — the unaugmented cochain complex,
  matching Mathlib's API.
- `Scheme.cechCohomology` (iter-047): `(Scheme.cechCochain C F 𝒰).homology n`.
- iter-054→058 basic-open identifications: `basicOpenCover_supr_of_span_eq_top`,
  `basicOpenCover_isAffineOpen`, `..._inter_eq_basicOpen_mul`,
  `..._finset_inf'_eq_basicOpen_prod`, `..._finset_inf'_isAffineOpen`,
  `..._finset_inf'_le`. All thin Mathlib wrappers, all needed.
- `HModule k F n` and `HModule' k F n X` as `Abelian.Ext` against the
  constant sheaf.

### What the project must provide

#### Branch A — Čech acyclicity (~150-250 LOC)

For each affine `U` and spanning `s ⊆ Γ(C.left, U)`:

1. **Augmentation lemma** (~30-50 LOC). Define the augmentation
   `F(U) → ∏_i F(𝒰 i)` as the natural sheaf-restriction morphism, and
   produce an *augmented* cochain complex extending iter-047's
   `Scheme.cechCochain`. This is structural; no Mathlib wrapper exists.

2. **Localized identification** (~60-100 LOC). For each `f ∈ s`, identify
   the localization (at `f`) of the degree-`n` Čech cochain
   `∏_x F(⨅ k, 𝒰 (x k))` with the degree-`n` cochain of the
   "cover-of-`D(f)`" Čech complex. The key inputs are
   `IsAffineOpen.isLocalization_of_eq_basicOpen` (each intersection
   identifies as `Localization.Away` of `Γ(U)`) and
   `IsLocalizedModule.map_exact` (chain-level localization-preserves-exactness).

3. **Extra-degeneracy invocation** (~30-60 LOC). The cover-of-`D(f)`
   Čech complex contains `D(f) = D(f ∩ f)` as a member, so applying
   `FormalCoproduct.extraDegeneracyCech` (or its op-dual for cochain
   complexes) gives an extra degeneracy on the augmented complex. By
   `ExtraDegeneracy.homotopyEquiv`, the augmented cochain complex over
   `D(f)` is homotopy equivalent to the constant complex on `F(D(f))`,
   hence the (un-augmented) Čech complex over `D(f)` is exact in
   positive degrees.

4. **Local-to-global** (~30-40 LOC). Per-degree, apply
   `exact_of_isLocalized_span s hs ...` with the per-`f` local exactness
   from step 3 to lift to exactness of the unlocalized differential.
   Repackage as `IsCechAcyclicCover (toModuleKSheaf C) (basicOpenCover s)`.

#### Branch B — Čech-vs-derived comparison (~150-200 LOC)

This is the substantial branch. Possibilities, ranked by economy:

(i) **Direct comparison via augmented complex as resolution** (~150-200
LOC). After Branch A, the augmented Čech complex is exact, hence a
resolution of `F(U)`. Use `Abelian.Ext`'s functoriality (Mathlib has
`Abelian.Ext.linearEquiv₀` and adjacent API) to identify the homology of
`Hom(augmented Čech, F)` with `Ext^n(R, F)`.

(ii) **Inductive Mayer-Vietoris** (~250-400 LOC). For finite covers,
unwind the cover one basic open at a time using the iter-014 LES.
Requires inductive structure and ad-hoc finite-cover reduction. **Not
recommended** — does more work and produces a less reusable artefact.

(iii) **Spectral sequence formalisation** (~600+ LOC). Build Stacks 03OU
in Lean. **Strongly not recommended** — out of scope for the genus
proof.

**Recommendation**: pursue (i). Total Branch B estimate ~150-200 LOC.

### Total project-local LOC estimate

~300-450 LOC across Branches A + B, spanning iter-059 to iter-066+.
This is within the directive's "~350-650 LOC" upper bound — the
mathlib-faithful design comes in at the low end of the plan-agent's
estimate.

## Recommendation

**Do not bypass the Čech-vs-derived comparison.** No Mathlib precedent
exists for "acyclic cover ⇒ Čech = Ext", but the constituent pieces —
`ExtraDegeneracy.homotopyEquiv`, `extraDegeneracyCech`,
`exact_of_isLocalized_span`, `isLocalization_of_eq_basicOpen` — combine
into the standard Stacks 01ED proof of Čech acyclicity (Branch A) with
modest project-local glue (~150-250 LOC). The Čech-vs-derived comparison
(Branch B) is the real obligation; spending ~150-200 LOC on the direct
"augmented Čech complex is a resolution" route gives the cleanest
deliverable.

**The alternating-sum-cancellation argument the directive feared having
to reproduce is NOT needed**: `ExtraDegeneracy.homotopyEquiv` encapsulates
it. The project work is the *bookkeeping* of mapping the localized Čech
complex to a Čech complex over `D(f)` (Branch A step 2), not the cancellation
itself.

**Naming alignment**: all paths and names cited by the project (iter-047
import, iter-053–058 wrappers) remain valid. Recommend the iter-059
plan-agent update the iter-056 docstring at
`AlgebraicJacobian/Cohomology/MayerVietoris.lean:1441` to say
`exact_of_isLocalized_span` (or `exact_of_localized_span`, depending on
which form the project ends up calling — both exist).

## Caveats

- **Op direction**: Mathlib's `extraDegeneracyCech` builds on
  `SimplicialObject.Augmented`, giving an augmented *simplicial* object
  with extra degeneracy. The corresponding alternating face map complex
  is a *chain* complex. Our Čech complex is a *cochain* complex (built
  from an *augmented cosimplicial* object via
  `alternatingCofaceMapComplex`). The op-duality is straightforward but
  takes ~20-30 LOC of routine repackaging.
- **Augmentation construction**: the augmentation `F(U) → ∏_i F(𝒰 i)` is
  natural in `F`, so it should be derivable from the universal property
  of the formal-coproduct construction. But the project will need to
  spell this out — Mathlib does not currently package the augmentation
  alongside `cechComplexFunctor`.
- **Quasi-coherence assumption**: Stacks 01ED is for *quasi-coherent*
  sheaves on affine schemes, where the augmented Čech complex is exact
  *as a complex of `Γ(U)`-modules*. Our `toModuleKSheaf` is not the
  structure sheaf as an `O_C`-module — it's the structure sheaf as a
  *constant `k`-module*. The Stacks proof carries over because the
  alternating-sum cancellation is purely *combinatorial* (lives at the
  level of the simplicial structure, not the algebra structure). But the
  blueprint should note this distinction so future readers don't
  conflate "quasi-coherent sheaves of `O_C`-modules" with "sheaves of
  `k`-modules underlying the structure sheaf".
- **`Subsingleton` vs `IsZero`**: project's `IsCechAcyclicCover` carries
  a `Subsingleton (cechCohomology n)` field. Mathlib's
  `subsingleton_H_of_isZero` (`SheafCohomology/Basic.lean:74`) reduces
  via `IsZero`. The project may want to expose both forms; the
  `Subsingleton` form is the chainable one (matches iter-040's
  `IsAffineHModuleVanishing` consumer).

## Other open questions noticed (not addressed)

- Whether the iter-046 `Functor.const_linear` / `Functor.const_additive`
  instances suffice for the `Linear k`-enrichment on `Sheaf J (ModuleCat
  k)` that Branch B will need (probably yes, but worth a separate sanity
  check).
- Whether the iter-009 `noncomputable abbrev HModule` / iter-014
  `HModule'` design needs adjustment when the Čech-vs-Ext comparison
  starts producing `LinearEquiv`s at universe `u+1`. The iter-049
  universe bridge already handles the `u`-vs-`u+1` step; whether it
  needs to handle the augmentation universe too is a separate audit.

---
*Iteration: 059*
