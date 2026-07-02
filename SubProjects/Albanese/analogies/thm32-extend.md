# Analogy: extend a rational map from a smooth projective surface to a proper group scheme without Weil divisors

## Mode
cross-domain-inspiration

## Slug
thm32-extend

## Iteration
164

## Structural problem (abstracted)
Given a morphism defined on a dense open `U ⊆ X` of an integral regular scheme into a
target `Y` whose structure morphism is proper, decide where it extends. Two sub-shapes:
(1) **codim-1 extension** — extend across every height-1 point (the local ring is a
DVR); (2) **emptiness** — fill the remaining codim-≥2 locus, which for a *proper* target
is only possible when extra structure (a group law on `Y`) is present. The blocker is
that the classical emptiness proof (Milne Lemma 3.3) is phrased with Weil divisors, and
Mathlib has no Weil/Cartier divisor API at scheme generality.

## Failed approaches (from directive context)
- Hand-building Weil-divisor theory (`div(f)`, prime divisors) on `ℙ¹×ℙ¹`: Mathlib has
  no usable scheme-level divisor API; building one is out of scope.

## Key finding up front
Mathlib **already ships the entire codim-1 / "Theorem 3.1" half** as a *different
sub-area of algebraic geometry the project has not been using*: the
`AlgebraicGeometry.RationalMap` + `ValuativeCriterion` + `SpreadingOut` stack. The
"defined at every codim-1 point ⟺ complement has codim ≥ 2" statement is **pure
properness, no group, no divisors**, and is fully portable today. The emptiness step
(Lemma 3.3) is genuinely *not* a valuative side-step — the valuative criterion is
structurally blind to codim-≥2 points (a DVR is *exactly* a codim-1 local ring; there is
no "codim-2 valuative criterion"). For a general proper target the codim-2 locus cannot
be filled (`ℙ²⇢ℙ¹` at `[0:0:1]`), so the group law is essential there.

## Analogues found

### Analogue 1: `AlgebraicGeometry.ValuativeCriterion.Existence` + `Scheme.PartialMap.ofFromSpecStalk`  (Theorem 3.1, codim ≥ 2)
- **Domain**: algebraic geometry — but the *valuative-criterion / spreading-out*
  sub-shelf, distinct from the divisor machinery the project has been chasing.
- **Same structural problem there**: "a morphism `Spec K → X` over a proper `f : X ⟶ Y`,
  given a dominating `Spec R → Y` from a valuation ring `R = Frac⁻¹(K)`, lifts to
  `Spec R → X`." That is *exactly* "extend over the DVR `O_{V,Z}` at a height-1 point."
- **Technique / exact API**:
  - `ValuativeCommSq {X Y} (f : X ⟶ Y)` — `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:53`.
    Bundles `R` (a `ValuationRing`), `K = Frac R`, `i₁ : Spec K ⟶ X`, `i₂ : Spec R ⟶ Y`,
    and the commuting square.
  - `ValuativeCriterion.Existence : MorphismProperty Scheme` (`ValuativeCriterion.lean:78`)
    `:= fun f ↦ ∀ S : ValuativeCommSq f, S.commSq.HasLift`. This is the per-DVR lift
    extractor the directive asked for.
  - `IsProper.eq_valuativeCriterion` (`ValuativeCriterion.lean:328`):
    `@IsProper = ValuativeCriterion ⊓ QuasiCompact ⊓ QuasiSeparated ⊓ LocallyOfFiniteType`.
    `rw` of this on `[IsProper A.hom]` yields `ValuativeCriterion A.hom`, hence
    `ValuativeCriterion.Existence A.hom`. (Forward direction is free; the project usually
    cites the *reverse* `IsProper.of_valuativeCriterion` at line 339.)
  - DVR at the codim-1 point, **no global Dedekind hypothesis**:
    `IsDiscreteValuationRing.tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`
    (`Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:168`) makes a *local* Noetherian
    domain a DVR from `finrank_cotangentSpace ≤ 1` (`Mathlib/RingTheory/Ideal/Cotangent.lean:349`,
    used as `tfae_have 6 ↔ 5`) plus `¬ IsField`. So `O_{V,Z}` regular of dim 1 ⟹ DVR
    ⟹ `ValuationRing` (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:512` /
    `of_isDiscreteValuationRing`). NB the *Dedekind* extractor
    `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`
    (`Mathlib/RingTheory/DedekindDomain/Dvr.lean:131`) is the **wrong generality** — it
    needs the *global* ring dim ≤ 1, which fails for a surface; use the TFAE instead.
  - `IsFractionRing (X.presheaf.stalk x) X.functionField` for integral `X`
    (`Mathlib/AlgebraicGeometry/FunctionField.lean:151`) and
    `IsDomain (X.presheaf.stalk x)` (`:166`) supply `K = K(V)`, `R = O_{V,Z}` directly as
    `i₁ = α.fromFunctionField` (`RationalMap.lean:145`).
  - **Spreading out** the lift back into an open neighbourhood of `Z`:
    `Scheme.PartialMap.ofFromSpecStalk` (`Mathlib/AlgebraicGeometry/RationalMap.lean:179`),
    built on `spread_out_of_isGermInjective'` (`SpreadingOut.lean:367`). Needs
    `[LocallyOfFiniteType A.hom]` (have it) and `X.IsGermInjectiveAt Z`, which is free:
    `IsIntegral X → X.IsGermInjective` (`SpreadingOut.lean:158`).
  - **Gluing** the per-point spreadings into one maximal partial map: `RationalMap.domain`
    (`RationalMap.lean:485`, `sSup` over representatives) and `RationalMap.toPartialMap`
    (`RationalMap.lean:517`, glued via `openCoverDomain` + `glueMorphisms`; uses `Y`
    separated for uniqueness). Each spread-out enlarges `domain`; the union omits only
    codim-≥2 points.
- **Mapping to project**: set `f := A.hom : A ⟶ Spec k̄` (`[IsProper]`,
  `[LocallyOfFiniteType]`). At a height-1 point `Z` of `V` (regular), build a
  `ValuativeCommSq A.hom` with `R := V.presheaf.stalk Z`, `K := V.functionField`,
  `i₁ := α.fromFunctionField`, `i₂ := Spec.map …` to `Spec k̄` (square commutes by
  `Spec k̄`-uniqueness). `Existence` gives the lift `Spec O_{V,Z} ⟶ A`; `ofFromSpecStalk`
  spreads it to a neighbourhood, so `Z ∈ α.domain`. Hence `V ∖ α.domain` has codim ≥ 2.
- **Porting cost**: medium. The decls all exist; the work is the per-`Z` `ValuativeCommSq`
  construction, the DVR instance for `O_{V,Z}` (regular dim-1 via TFAE), and the
  scheme-level "no codim-1 point in the complement ⟹ codim ≥ 2" bookkeeping (Mathlib has
  no `Scheme` codimension API, so this is the one hand-rolled piece).
- **Verdict**: ANALOGUE_FOUND.

### Analogue 2: the ruling / genus-0-rigidity reduction for the surface `ℙ¹×ℙ¹` (avoids Lemma 3.3 entirely)
- **Domain**: algebraic geometry — reuses the project's *own* proven rigidity, a distant
  in-repo tool, in place of divisor theory.
- **Same structural problem there**: "a rational map out of a product of curves is
  constant along each ruling, hence constant, hence extends." Replaces "fill the
  codim-2 locus" with "the map was constant all along."
- **Technique**: for general `t`, `α|_{ℙ¹×{t}} : ℙ¹ ⇢ A` is a rational map from a smooth
  *curve*; the **curve** valuative criterion (Analogue 1 with `dim = 1`, every closed
  point's local ring a DVR) extends it to a genuine morphism `ℙ¹ → A`, which is
  **constant** by the project's `rigidity_over_kbar` (morphism `ℙ¹_{k̄} → A_{k̄}` constant,
  `AlgebraicJacobian/RigidityKbar.lean:75`). So `α(s,t) = c(t)` independent of `s` on a
  dense open; symmetric in `s` ⟹ `α` is constant on a dense open ⟹ extends as the
  constant morphism (a constant `PartialMap` on a dense open is `equiv` to the constant
  morphism on all of `V`).
- **Mapping to project**: this is the cheapest path **iff** the obligation is genuinely
  the surface `ℙ¹×ℙ¹` (as the directive states) and `rigidity_over_kbar` (or at least
  "morphism `ℙ¹→A` constant") is available **upstream** of Theorem 3.2. ⚠ Circularity
  check required: the blueprint (`AbelianVarietyRigidity.tex:43`) currently derives
  "`ℙ¹→A` constant" *through* Thm 3.2 + Cor 1.2/1.5. If the only available proof of
  "`ℙ¹→A` constant" routes through Thm 3.2, this reduction is circular and must instead
  use the differential/`H⁰(ℙ¹,Ω)=0` argument the blueprint mentions
  (`AbelianVarietyRigidity.tex:26`) or `rigidity_lemma` (Mumford Form I, proven
  axiom-clean iter-162) directly. Also: only works for ruled / product-of-curve sources,
  not a general nonsingular `V`.
- **Porting cost**: low–medium *if* the upstream constancy is available; the curve
  valuative step is a special case of Analogue 1 and the genericity ("general fiber meets
  the dense domain") is elementary.
- **Verdict**: ANALOGUE_FOUND (conditional on the circularity check).

### Analogue 3: `RingTheory.OrderOfVanishing.ord` — the divisor-free *local* multiplicity (only substitute for Lemma 3.3's divisor content)
- **Domain**: commutative algebra.
- **Same structural problem there**: "assign a codim-1 multiplicity without a global
  divisor group." `ord R x := Module.length R (R ⧸ span{x})`
  (`Mathlib/RingTheory/OrderOfVanishing/Basic.lean:35`), with `ord_mul`, `ord_pow`,
  `ord_le_ord_of_dvd`, etc. At a DVR this is the valuation; it is the length-theoretic
  order of vanishing along a height-1 prime.
- **Technique**: replaces `div(f)` *locally* (one prime at a time) by a length, dodging a
  global Weil-divisor group.
- **Mapping to project**: if one insisted on Milne's actual Lemma 3.3 difference-map
  argument, `ord` is the only Mathlib tool for "the order of `f` along `Z`." But Lemma 3.3
  also needs **codim-1 = locally principal** = regular local rings are UFDs
  (Auslander–Buchsbaum), which **Mathlib does not have** (no `IsRegularLocalRing →
  UniqueFactorizationMonoid`; confirmed absent). So `ord` alone is insufficient.
- **Porting cost**: high — would still require an Auslander–Buchsbaum gap-fill plus a
  divisor-of-poles construction.
- **Verdict**: PARTIAL_ANALOGUE.

## Direct answer to the open question
**No** — there is no pointwise-valuative side-step that makes the indeterminacy locus
*empty*. The valuative criterion at height-1 primes gives precisely "defined at every
codim-1 point" = complement codim ≥ 2 (Theorem 3.1), for free from properness and with
**no divisors and no group** (Analogue 1). It cannot reach codim 0: a DVR is a codim-1
object, so the criterion never sees codim-≥2 points, and for a general proper target
those points genuinely obstruct extension (`ℙ²⇢ℙ¹`). The emptiness (Lemma 3.3) requires
the group law; Milne's proof of it needs codim-1-is-principal (Auslander–Buchsbaum),
absent from Mathlib. The cheap escape is to *avoid Lemma 3.3 altogether* via the ruling /
genus-0-rigidity reduction (Analogue 2) for the `ℙ¹×ℙ¹` case the directive actually needs.

## Top suggestion
Adopt the `RationalMap` + `ValuativeCriterion` + `SpreadingOut` substrate immediately for
the codim-1 half — it is shipped Mathlib the project is not yet importing (only two
incidental `Scheme.PartialMap.Opens.isDominant_ι` uses exist in
`AbelianVarietyRigidity.lean:700` / `Rigidity.lean:113`). Concretely: phrase
`rationalMap_to_av_extends` against `Scheme.RationalMap` / `RationalMap.domain`, get
codim-≥2 from `ValuativeCriterion.Existence (A.hom)` (via `IsProper.eq_valuativeCriterion`)
+ `ofFromSpecStalk`, with `O_{V,Z}` made a DVR through
`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` + `finrank_cotangentSpace_le_one_iff`.
For the final emptiness, try Analogue 2 (rulings + `rigidity_over_kbar`) **after** clearing
the circularity check, rather than building divisors or Auslander–Buchsbaum. First file to
touch: a new `AlgebraicJacobian/RationalMapExtend.lean` importing
`Mathlib.AlgebraicGeometry.RationalMap` and `Mathlib.AlgebraicGeometry.ValuativeCriterion`.
