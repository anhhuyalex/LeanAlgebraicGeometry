# Missing ingredient: `s ≤ 1` in `chart_ringKrullDim_le_one`

File: `AlgebraicJacobian/RiemannRoch/CurveKrullDim.lean`
Iteration: 012 (prover)
Mathlib rev: leanprover/lean4 v4.30.0-rc2 (project Mathlib).

## Where the gap sits

In `AlgebraicGeometry.chart_ringKrullDim_le_one`:

```
{kbar} [Field kbar] {S} [CommRing S] [Algebra kbar S]
[Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S] [IsDomain S]
⊢ ringKrullDim S ≤ 1
```

The proof is **complete except for one isolated sub-goal**.  Everything around it is
proved and axiom-clean:

1. standard-smooth ⇒ `Algebra.FiniteType kbar S`;
2. Noether normalisation `exists_finite_inj_algHom_of_fg kbar S` gives
   `g : kbar[X₁..X_s] →ₐ[kbar] S` injective and module-finite;
3. the new keystone `ringKrullDim_le_of_moduleFinite_injective`
   (Cohen–Seidenberg upper bound, Stacks 00OJ — **proved this iter, axiom-clean**) gives
   `ringKrullDim S ≤ ringKrullDim kbar[X₁..X_s]`;
4. `MvPolynomial.ringKrullDim_of_isNoetherianRing` + `ringKrullDim_eq_zero_of_field`
   collapse the RHS to `↑s`, so `ringKrullDim S ≤ ↑s`.

The sole open sub-goal is

```
have hs : (s : WithBot ℕ∞) ≤ 1 := by sorry
```

where `s` is the Noether-normalisation variable count.

## The mathematics of the gap

`s = trdeg(Frac S / kbar) = Module.rank S Ω[S⁄kbar] = 1`:

* `s = trdeg(Frac S / kbar)`: the Noether map `kbar[X₁..X_s] ↪ S` is module-finite, so
  `Frac S` is a finite (hence algebraic) extension of `kbar(X₁..X_s)`; therefore the
  transcendence degree of `Frac S` over `kbar` is exactly `s` (Stacks Tag 00P0).
* `trdeg(Frac S / kbar) = Module.rank S Ω[S⁄kbar]`: for a finitely generated, separably
  generated domain over a field the rank of the Kähler module equals the transcendence
  degree.  (`kbar` algebraically closed ⇒ perfect ⇒ the f.g. field extension is
  separably generated.)
* `Module.rank S Ω[S⁄kbar] = 1`: this *is* available —
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1`.  It is stated
  as a `have hrank` inside the `sorry` block so the one concrete ingredient is visible.

## Why it is blocked (searches performed)

No API key for the informal agent (`env | grep -E "DEEPSEEK|MOONSHOT|OPENROUTER|OPENAI|GEMINI"`
empty), so only Mathlib search was used.  Confirmed ABSENT in this Mathlib:

* `loogle "ringKrullDim, Algebra.IsIntegral"`, `"ringKrullDim, Module.Finite"` — no
  dimension-of-integral-extension equality (the `≤` half we needed we proved by hand).
* `loogle "IsStandardSmoothOfRelativeDimension, ringKrullDim"` — empty
  (no smooth-morphism dimension formula).
* `loogle "Algebra.trdeg, ringKrullDim"` — empty (no `dim = trdeg`, Tag 00P0 absent).
* `loogle "Module.rank, KaehlerDifferential, Algebra.trdeg"` — empty
  (no `rank Ω = trdeg`).
* `leansearch "krull dimension finite type domain over field equals transcendence degree"`,
  `"dimension of kahler differentials … equals transcendence degree separably generated"`
  — only sep-degree facts (`Algebra.IsSeparable.sepDegree_eq`), nothing on Ω vs trdeg or
  dim vs trdeg.

This matches the planner analogy `analogies/curve-krulldim-one.md` (gap "G2") and
PROGRESS.md ("DEEP residual `s=trdeg=relDim=1`, `trdeg=relDim` Mathlib-ABSENT").

## Precise statements to add (for a `mathlib-build` lane)

A single lemma suffices to close `hs` (then `exact (by exact_mod_cast hrank ▸ …)`):

```
-- Either of these, specialised at the fraction field, closes `s ≤ 1`:

theorem ringKrullDim_eq_trdeg_of_finiteType_domain
    {k S : Type*} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] :
    ringKrullDim S = Algebra.trdeg k (FractionRing S)        -- Stacks 00P0

-- and the smooth/separable link
theorem trdeg_eq_rank_kaehler_of_smooth_domain
    {k S : Type*} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] [Algebra.Smooth k S] :
    (Algebra.trdeg k (FractionRing S) : Cardinal) = Module.rank S Ω[S⁄k]
```

With the first lemma alone the proof simplifies: `ringKrullDim S = s` (no Noether
bound needed) and then `s = rank Ω = 1` via the second.  Implementing either is a
genuine dimension-theory build (Noether normalisation is already in Mathlib via
`exists_finite_inj_algHom_of_fg`; the trdeg side needs transcendence-basis bookkeeping).
