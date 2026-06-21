# `Scheme.eulerCharacteristic_shortExact_add` — remaining infrastructure gaps

File: `AlgebraicJacobian/RiemannRoch/RRFormula.lean`
Blueprint: `lem:euler_char_shortExact_add` (`RiemannRoch_RRFormula.tex`)

## Status (iter-001, Lane RRFormula)

The monolithic typed-sorry was **replaced by a structured proof**. The proof
is now complete *modulo two precisely-typed gaps*. Everything else is proven:

- **`finrank_alternating_six_term`** (NEW helper, axiom-clean): the pure
  linear-algebra core — for a bounded six-term exact sequence of
  finite-dimensional `k`-vector spaces `0 → V₀ → … → V₅ → 0`, the alternating
  sum of dimensions is `0`. Proven via rank-nullity + `LinearMap.exact_iff`
  + `omega`.
- **Exactness at the four interior LES nodes**: derived from Mathlib's
  `Abelian.Ext.covariant_sequence_exact₁/₂/₃` (the covariant Ext-LES of the
  short exact sequence applied to the constant-sheaf test object
  `L = (constantSheaf J _).obj (ModuleCat.of kbar kbar)`).
- **Injectivity** of the first map: `Abelian.Ext.postcomp_mk₀_injective_of_mono`
  from `_hSE.mono_f`.
- **Surjectivity** of the last map: reduced to the vanishing gap (b) below,
  via `covariant_sequence_exact₃` at degree `1`.
- **Assembly**: `simp only [Scheme.eulerCharacteristic]; linarith` against the
  alternating identity.

## Gap (a) — Serre coherent-cohomology finiteness  [BLOCKING, signature-level]

Six typed sorries of the form
`FiniteDimensional kbar (Scheme.HModule kbar S.Xᵢ n)` for `n ∈ {0,1}`.

**This is unprovable as the lemma is currently stated**: `S` is an *arbitrary*
`ShortComplex (Sheaf J (ModuleCat kbar))` with **no coherence hypothesis**.
Finite-dimensionality of `H⁰`/`H¹` is Serre's finiteness theorem and holds
only for coherent sheaves on the proper `kbar`-scheme `C`. Confirmed: no
finiteness instance synthesizes for a general sheaf (probed iter-001).

**Required action (planner):** either
1. add a coherence / `FiniteDimensional`-of-cohomology hypothesis package to
   `eulerCharacteristic_shortExact_add` (this cascades to the sole consumer
   `eulerCharacteristic_of_shortExact_skyscraper`, which must then discharge
   finiteness for the `sheafOf D` / `sheafOf (single+D)` / skyscraper SES —
   itself needing the Serre-finiteness bridge), **or**
2. supply a project-side Serre finiteness instance
   `[IsCoherent F] → FiniteDimensional kbar (HModule kbar F n)` and a coherence
   producer for the divisor line bundles + skyscraper.

The blueprint's informal statement omits finiteness (implicitly coherent); the
Lean formalization genuinely needs it.

## Gap (b) — Grothendieck vanishing `H²(C, F) = 0`  [BLOCKING, missing Mathlib]

One typed sorry: `Subsingleton (Abelian.Ext L S.X₁ 2)`.

Mathematically TRUE for *any* abelian sheaf `F` on the 1-dimensional
Noetherian space `C` (Grothendieck vanishing III.2.7: `Hⁱ(X,F)=0` for
`i > dim X`). But **not in Mathlib `b80f227`** at the
`Abelian.Ext (constantSheaf …) F i`-cohomology level, and **not in the
project**. No degree-≥2 vanishing infrastructure exists (the project's
`H1Vanishing.lean` only treats flasque H¹ vanishing).

**Required action (planner, `mathlib-build` mode):** a project-side
Grothendieck vanishing bridge
`Subsingleton (Abelian.Ext ((constantSheaf (Opens.grothendieckTopology
C.left.toTopCat) (ModuleCat kbar)).obj (ModuleCat.of kbar kbar)) F i)` for
`i ≥ 2`, gated on cohomological-dimension ≤ 1 of the 1-dimensional curve `C`.

## Notes

- Informal agent NOT called: no API key set
  (`env | grep -E "DEEPSEEK|MOONSHOT|OPENROUTER|OPENAI|GEMINI"` empty).
- Both gaps are off the genus-0 critical path per the blueprint
  (`thm:euler_char_eq_deg_plus_one_minus_genus` is the only consumer in RR.2).
