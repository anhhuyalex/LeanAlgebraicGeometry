# Analogy: Mathlib-idiomatic Lean encoding of the generic-rank SES + torsion reindex (Nitsure §4 non-torsion step)

## Mode
api-alignment

## Slug
gf-genrank

## Iteration
007

## Question
For the non-torsion inductive step of `GenericFreeness.exists_free_localizationAway_polynomial`
(finite module `N` over `P_d := MvPolynomial (Fin d) A`, `A` a noetherian domain), pin the
Mathlib-idiomatic Lean encoding of three things so a blueprint-writer can fix concretely-typed
sub-lemma signatures:
1. the **generic rank** of `N` over the domain `P_d`;
2. the **generic-rank SES** `0 → P_d^{⊕m} → N → T → 0` with `T` torsion;
3. the **support-dimension-drop reindex** of `T` onto `MvPolynomial (Fin m') A` (`m' < d`).
Plus: re-confirm `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`.

## Project artifact(s)
- `AlgebraicJacobian/Picard/FlatteningStratification.lean:460-513` — `exists_free_localizationAway_polynomial`,
  the `sorry` at line 513 is exactly this non-torsion step.
- `…:168-207` — L1 `exists_free_localizationAway_of_torsion` (torsion leaf; consumes the SES's `T` after reindex).
- `…:360-394` — L3 `exists_free_localizationAway_of_shortExact` (the splice that consumes the SES).
- `…:415-445` — L4 `exists_localizationAway_finite_mvPolynomial` (already `sorry`; **shares the denominator-clearing
  Noether-normalization engine with the reindex** — its signature is the template for `gf_torsion_reindex`).

## Name verification (strategy-critic flag)
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` — **CONFIRMED**, path
`Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness`. Exact shape: for `A` comm + `IsNoetherianRing`,
`M` finite, a motive on finite `A`-modules closed under (i) `Subsingleton N`, (ii) `N ≃ₗ A ⧸ p.asIdeal`
for `p : PrimeSpectrum A`, (iii) short-exact `N₁ ↪ N₂ ↠ N₃` with motive on the ends ⟹ on `N₂`, gives
`motive M`. This is exactly the trichotomy L1 (torsion/subsingleton) + L3 (SES) + the `B/𝔭` leaf were
built to discharge in `genericFlatnessAlgebraic`. The sibling `…exists_relSeries_isQuotientEquivQuotientPrime`
also exists. (Loogle name-substring search missed it; `lean_leanfinder` found it.)

## Decisions identified

### Decision 1: how to express the generic rank `m`

- **Mathlib idiom**: `m := Module.finrank (FractionRing P_d) (LocalizedModule (nonZeroDivisors P_d) N)`.
  `P_d = MvPolynomial (Fin d) A` is a noetherian domain (`MvPolynomial.isDomain`, Hilbert basis), so
  `nonZeroDivisors P_d` localizes `N` to a module over `Localization (nonZeroDivisors P_d) = FractionRing P_d`,
  a finite-dimensional `FractionRing P_d`-vector space (finite, since `N` is finite over `P_d`).
  `Module.finrank` over a field is the right invariant; `Module.rank` (`Cardinal`-valued) is the wrong
  altitude — you want a `ℕ` to index `Fin m`.
- **Choosing `m` lifts of `N` whose images form a basis** — atoms all verified:
  - `Module.finBasis (FractionRing P_d) (LocalizedModule … N) : Basis (Fin m) (FractionRing P_d) (…)`
    (`Mathlib.LinearAlgebra.Dimension.Free`) — the field-vector-space basis indexed by `Fin (finrank)`.
  - `IsLocalizedModule.surj (nonZeroDivisors P_d) (LocalizedModule.mkLinearMap …)` — every basis vector
    is `(1/s) • (image of some n ∈ N)`; `s` a unit in the field, so the **images** `{mk n_i}` are again a
    basis (clear denominators). (`Mathlib.Algebra.Module.LocalizedModule.Basic`.)
  - `LinearIndependent.restrict_scalars` (P_d ↪ FractionRing P_d injective) descends linear independence
    of the lifts from `FractionRing P_d` back to `P_d` — this is what makes `φ` (below) injective.
  - Reverse helper `Module.Basis.ofIsLocalizedModule` / `LinearIndependent.localization`
    (`Mathlib.RingTheory.Localization.Module`) go R→Rₛ; useful for the spanning/surjectivity half.
- **Gap**: divergent-equivalent — Mathlib has every atom but **no single packaged "choose `m` elements
  whose images are a basis of the localization" lemma**. The number is idiomatic; the lift is project glue.
- **Verdict**: ALIGN_WITH_MATHLIB on the number (`Module.finrank (FractionRing P_d) (LocalizedModule …)`),
  NEEDS_MATHLIB_GAP_FILL on the lift (small, all anchors present).

### Decision 2: encoding the generic-rank SES `gf_generic_rank_ses`

- **Mathlib idiom for the map**: `φ := Fintype.linearCombination P_d v` where `v : Fin m → N` are the
  lifts of Decision 1 (`Mathlib.LinearAlgebra.Finsupp.LinearCombination`). Domain `(Fin m → P_d)` **is**
  the concrete `P_d^{⊕m}` (matches the `M'` slot of L3 exactly). Companions: `Fintype.linearCombination_apply`
  (`∑ i, f i • v i`), `Fintype.range_linearCombination` (`range = span (Set.range v)`).
  `φ` injective ⟺ `LinearIndependent P_d v` (got from Decision 1 via `restrict_scalars`).
- **Cokernel / torsion**: `T := N ⧸ LinearMap.range φ`; the surjection is `Submodule.mkQ (range φ)`
  (surjective, and `Function.Exact φ (mkQ (range φ))` holds — `range φ = ker (mkQ)`). `T` torsion encoded
  as `Module.IsTorsion (MvPolynomial (Fin d) A) T` (preferred — it is the literal input of the reindex's
  annihilator anchor) or equivalently `Subsingleton (LocalizedModule (nonZeroDivisors P_d) T)` via
  `LocalizedModule.subsingleton_iff`. Torsion holds because the images of `v` span the localization
  (basis), so `φ ⊗ FractionRing P_d` is surjective, hence `T ⊗ FractionRing P_d = 0`.
- **Important simplification vs the directive**: the SES is constructible over `P_d` **directly — no
  inversion of `g ∈ A` is needed for this step**. `φ` is injective on the nose (`ker φ` is torsion in the
  torsion-free `P_d`-module `P_d^{⊕m}`, hence `0`), and `T` is torsion on the nose. The `g` that Nitsure
  mentions belongs entirely to the *reindex* (Decision 3), not the SES. So `gf_generic_rank_ses` carries
  no `g`. (The "denominator-clearing exactness after inverting one element" API the directive asked about
  is therefore unnecessary here.)
- **Gap**: NEEDS_MATHLIB_GAP_FILL — no packaged generic-rank SES, but every atom exists and the assembly
  is short.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (build `gf_generic_rank_ses` from the atoms above).

### Decision 3: the torsion reindex `gf_torsion_reindex` — and the base-domain induction shape

- **Nonzero annihilator (Mathlib ✓)**: `Submodule.annihilator_top_inter_nonZeroDivisors`
  (`Mathlib.Algebra.Module.Torsion.Basic`): a finite `Module.IsTorsion R M` over comm `R` has
  `(⊤.annihilator ∩ nonZeroDivisors R).Nonempty`. For the domain `P_d` this gives `0 ≠ F ∈ Ann_{P_d}(T)`.
- **Variable drop (Mathlib-ABSENT)**: from `0 ≠ F ∈ Ann(T)`, one wants `T` module-finite over a polynomial
  ring in `m' < d` variables. Cleanest route that **avoids Krull-dimension theory**: a Nagata change of
  variables makes `F` monic in `X_d` up to its leading coefficient `g ∈ A`; after inverting `g`,
  `A_g[X_1..X_d]/(F)` is module-finite (division algorithm) over `A_g[X_1..X_{d-1}] = MvPolynomial (Fin (d-1)) A_g`,
  and `T` (finite over `P_d/(F)`) is finite over it by `Module.Finite.trans`. So `m' = d-1 < d` — **no
  `ringKrullDim` needed**. Mathlib has the *field* Noether normalization `exists_finite_inj_algHom_of_fg`
  (`Mathlib.RingTheory.NoetherNormalization`) and `ringKrullDim` theory (`Mathlib.RingTheory.KrullDimension.*`,
  e.g. `Polynomial.ringKrullDim_le`) but **not** the domain-level single-variable elimination with
  denominator clearing. This is the **same engine** the already-stubbed L4
  `exists_localizationAway_finite_mvPolynomial` needs — build once, reuse.
- **CRITICAL design consequence — the induction must generalize the base domain `A`.** The reindex inverts
  `g ∈ A`, so `T_g` is finite over `MvPolynomial (Fin m') (Localization.Away g)` — base ring `A_g`, **not**
  `A`. The IH of `exists_free_localizationAway_polynomial` as currently written fixes `A`, so
  `IH m' _ T_g` does **not typecheck** (wrong base ring). This is the real cause of the iter-006
  "signatures depend on the generic-rank API" stall: it is not the rank API, it is that the recursion
  changes the base. **Fix**: state/prove the core with the motive universally quantifying the noetherian
  domain — `∀ d, ∀ (A) [CommRing A] [IsDomain A] [IsNoetherianRing A] (N) […], ∃ f : A, f ≠ 0 ∧ Free A_f N_f`,
  by `Nat.strong_induction_on d` with `A` (and its three instances, and all of `N`'s `d`-dependent
  instances) reverted into the motive. `A` is already an explicit argument, so this is a reversion change,
  not a signature change to the public lemma. Apply `IH m' (hm' : m' < d) (Localization.Away g) T_g` at
  base `A_g` (still a noetherian domain: `IsLocalization.isDomain`/`Localization.Away` of a noeth domain).
- **Descent of the IH witness back to `A`**: IH gives `h ≠ 0` in `A_g` with `T_g` free over `(A_g)_h`.
  Since `A_g = Localization.Away g` and `h = a / g^k`, `(A_g)_h ≅ A_{g·a}` and `T_{g·a} ≅ (T_g)_h`, so the
  freeness descends to `f'' := g·a ∈ A`. This is the same localization-tower freeness transport as the
  already-proved L3b `free_localizationAway_of_free_of_eq_mul` (a thin bridge across `A → A_g → (A_g)_h`).
- **The `P_d^{⊕m}` end is free over `A_f` for free (Mathlib ✓)**: `MvPolynomial.instFree`
  (`Module.Free A (MvPolynomial (Fin d) A)`) + `Pi`/localization free, so the `M'` end of L3 is free over
  `A_{f'}` for *any* `f' ≠ 0`. (Note: the file's comment "applied coordinatewise via the d=0 leaf" is
  slightly off — `P_d^{⊕m}` is **not** module-finite over `A`, but it **is** free, which is all L3 needs.)
- **Gap**: NEEDS_MATHLIB_GAP_FILL (variable-drop engine + base-`A` generalization).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

## Recommended sub-lemma signatures (for the blueprint pin)

```lean
/-- `gf_generic_rank_ses` — the generic-rank short exact sequence. No `g`: built over `P_d` directly. -/
theorem gf_generic_rank_ses
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (d : ℕ) (N : Type*) [AddCommGroup N]
    [Module (MvPolynomial (Fin d) A) N] [Module.Finite (MvPolynomial (Fin d) A) N]
    [Module A N] [IsScalarTower A (MvPolynomial (Fin d) A) N] :
    ∃ (m : ℕ) (φ : (Fin m → MvPolynomial (Fin d) A) →ₗ[MvPolynomial (Fin d) A] N),
      Function.Injective φ ∧
      Module.IsTorsion (MvPolynomial (Fin d) A) (N ⧸ LinearMap.range φ)
-- witness: m = finrank (FractionRing P_d) (LocalizedModule (nonZeroDivisors P_d) N);
--          φ = Fintype.linearCombination P_d v, v the denominator-cleared basis lifts.
```

```lean
/-- `gf_torsion_reindex` — re-present a finite torsion `P_d`-module over fewer variables after
inverting `g ∈ A`. Mirrors the existential style of the already-present L4
`exists_localizationAway_finite_mvPolynomial`. -/
theorem gf_torsion_reindex
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (d : ℕ) (hd : 0 < d) (T : Type*) [AddCommGroup T]
    [Module (MvPolynomial (Fin d) A) T] [Module.Finite (MvPolynomial (Fin d) A) T]
    [Module A T] [IsScalarTower A (MvPolynomial (Fin d) A) T]
    (htors : Module.IsTorsion (MvPolynomial (Fin d) A) T) :
    ∃ (g : A) (_ : g ≠ 0) (m' : ℕ) (_ : m' < d)
      (_ : Module (MvPolynomial (Fin m') (Localization.Away g))
              (LocalizedModule (Submonoid.powers g) T))
      (_ : Module (Localization.Away g) (LocalizedModule (Submonoid.powers g) T))
      (_ : IsScalarTower (Localization.Away g)
              (MvPolynomial (Fin m') (Localization.Away g))
              (LocalizedModule (Submonoid.powers g) T)),
      Module.Finite (MvPolynomial (Fin m') (Localization.Away g))
        (LocalizedModule (Submonoid.powers g) T)
-- can fix m' = d - 1 (single-variable elimination); strong induction accepts any m' < d.
```

And the **core's proof must be restructured** to generalize `A`:
```lean
-- helper, then `exists_free_localizationAway_polynomial` is its specialization:
∀ d, ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
       (N : Type*) [AddCommGroup N] [Module (MvPolynomial (Fin d) A) N]
       [Module.Finite (MvPolynomial (Fin d) A) N] [Module A N]
       [IsScalarTower A (MvPolynomial (Fin d) A) N],
     ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) N)
-- proved by `Nat.strong_induction_on d`, A reverted into the motive.
```

## Recommendation
Pin `m := Module.finrank (FractionRing P_d) (LocalizedModule (nonZeroDivisors P_d) N)` as the generic
rank — idiomatic and `ℕ`-valued. Build `gf_generic_rank_ses` (no `g`) from `Fintype.linearCombination`
on denominator-cleared basis lifts (`Module.finBasis` + `IsLocalizedModule.surj` +
`LinearIndependent.restrict_scalars`), with `T := N ⧸ range φ` and `Module.IsTorsion P_d T`. Build
`gf_torsion_reindex` on the L4 existential template, using `Submodule.annihilator_top_inter_nonZeroDivisors`
for `0 ≠ F ∈ Ann(T)` and the **project-side** Nagata single-variable elimination + denominator clearing
(shared with L4) to land over `MvPolynomial (Fin (d-1)) (Localization.Away g)`. **The load-bearing fix is
structural**: generalize the base domain `A` in the `Nat.strong_induction_on`, because the reindex changes
the base ring to `A_g` and the IH must be available there. None of these require weakening any pinned type.

---

## L4 finiteness leaf `exists_localizationAway_finite_mvPolynomial` @754 — iter-021 close recipe

The L4 finiteness conjunct `hfin` is the only remaining L4 sorry. The iter-020 prover scouted the
collapsing tool; this is the concrete close path (witness must be `g := g0 · g1`, NOT `g0` alone — the
`g0`-only `Module.Finite (MvPoly A_g0) B_g0` is generically FALSE-typed until integral denominators clear).

**Collapsing lemma (replaces the manual `gf_clear_one_denominator` Finset-fold):**
```
IsIntegral.exists_multiple_integral_of_isLocalization
  (M : Submonoid R) {S} [Algebra R S] {Rₘ} [Algebra R Rₘ] [IsLocalization M Rₘ]
  [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : S) :
  IsIntegral Rₘ x → ∃ m : M, IsIntegral R (m • x)
```
Apply with `R = MvPoly A_g0`, `Rₘ = MvPoly K`, `S = B_K`, `M = image of A_g0⁰ as constants`,
`x = xᵢ = algebraMap B B_K σᵢ` (integral over `MvPoly K` by `Algebra.IsIntegral.of_finite`, from Step 1's
`Module.Finite (MvPoly K) B_K`). Yields `mᵢ ∈ M` with `mᵢ • xᵢ` integral over `MvPoly A_g0`. Set
`g1 := ∏ (A-parts of the mᵢ)`, `g := g0 · g1`; each `σᵢ` is then integral over `MvPoly A_g` on `im φ_g`.

**Tower / localization facts to confirm on the active bump:**
- `gK.toAlgebra : Algebra (MvPoly K) B_K`; `(MvPolynomial.map ψ).toAlgebra : Algebra (MvPoly A_g0) (MvPoly K)`;
  the tower `IsScalarTower (MvPoly A_g0) (MvPoly K) B_K` holds via the existing `hcomp`
  (`ν.comp φ = gK.toRingHom.comp (MvPolynomial.map ψ)`, lines ~720–731).
- **Needs check:** `IsLocalization M (MvPoly K)` for `M = constants from A_g0⁰` — search
  `MvPolynomial.isLocalization` / IsLocalization of a polynomial ring at a base submonoid `[gap?]`.
- `Algebra.finite_adjoin_of_finite_of_isIntegral (s.Finite) (∀ x∈s, IsIntegral R x) :
   Module.Finite R ↥(Algebra.adjoin R s)` `[verified iter-020]`, then transport
   `Algebra.adjoin (MvPoly A_g) (σ-images) = ⊤` via `Subalgebra.topEquiv`. Generation:
   `Algebra.adjoin A_g (algebraMap B B_g '' σ) = ⊤` (localize `hσ : Algebra.adjoin A ↑σ = ⊤`), bump base to `MvPoly A_g`.

**Witness transfer (g0 → g):** `ν/ψ/b/φ/hνb/hsquare/hφ_inj` (lines ~634–738, inside
`set_option maxHeartbeats 4000000`) transfer VERBATIM with `g0 → g` in the localization types; `hνb` is
unchanged (`den = algebraMap A B g0`, `hgB_unit.unit_spec` still name `g0`). `hgB_unit` for the finer `g`:
`g0 ∣ g` ⟹ `isUnit_of_dvd_unit (map_dvd _ hdvd) hunit`.

**Dead ends:** committing the witness to `g0` (false-typed finiteness); `Module.Finite.of_localizationSpan`
(needs finiteness on a spanning family of opens — wrong direction). Bump `synthInstance.maxHeartbeats`
ONLY if ν/bⱼ synthesis stalls (mirror the L5 blocks) — never to mask a loop.
