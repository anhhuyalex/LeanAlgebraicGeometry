Done. Here is my report.

## What I changed

One file edited (and committed as `2b7f0bff45`):
`/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge/blueprint/src/chapters/Picard_FlatteningStratification.tex`

Added a new `\section{The rank-\(e\) stratum as a closed subscheme}` (`\label{sec:flatstrat_rank_stratum}`) between the entry-ideal algebra section and `\section{Universal property of the strata}`, with **24 new nodes**, each `\lean`-anchored 1-to-1 to a declaration in `AlgebraicJacobian/Picard/EntryIdealStratum.lean`, all `\leanok`, all with complete (non-sketched) proofs that split hard steps into `\uses`-linked lemmas. I also wired the proof of `thm:flattening_stratification_universal` to `\uses{def:stratum, def:stratum_immersion, thm:mem_range_stratum, thm:map_strata_ideal_basic_open}`.

## New `\label`s (grouped)

Fibre-rank base change: `thm:fiber_rank_base_change` (`Ideal.fiberRank_baseChange`), `lem:fiber_rank_congr`, `cor:fiber_rank_localized`.

Charts / point rank: `def:presentation_chart`, `def:presentation_basic_open` (`MatrixPresentationBasicOpen`), `lem:entry_ideal_basic_open`, `lem:presentation_chart_basic_open`, `def:chart_fiber_rank`, `lem:chart_fiber_rank_basic_open`, `thm:chart_fiber_rank_eq`, `def:point_rank`, `lem:point_rank_eq_chart_fiber_rank`.

Strata ideal: `lem:mem_entry_ideal_locally`, `lem:entry_ideal_chart_transfer`, `def:strata_ideal`, `thm:strata_ideal_eq_entry_ideal`, `lem:mem_strata_ideal_of_charts`, `def:charts_cover` (`ChartsCover`), `lem:charts_cover_finite`, `thm:map_strata_ideal_basic_open`.

Stratum: `def:strata_data`, `def:stratum`, `def:stratum_immersion`, `thm:mem_range_stratum` (`mem_range_stratumι_iff`).

I node-ified the mathematically meaningful helper declarations too (locality/transfer of entry-ideal membership, finite chart covers, restriction of presentations) so the cone is finite and every proof is complete; I deliberately folded pure Lean plumbing with no math content (presheaf-restriction transitivity `presheaf_res_res`/`presheaf_map_self`, `id_appLE`, `transportOpens`, the `res_mk'_basicOpen` fraction computation) into proof prose rather than making dead nodes. Verified: no duplicate labels, and every `\uses` target resolves.

## Places where the Lean did not match what the prose previously implied

1. **The universal theorem's prose claims a representability the new Lean does not provide.** The proof of `thm:flattening_stratification_universal` narrates that `V_e` *represents* the rank-`e` locus — "for `f : T → V` the pulled-back presentation stays right-exact, so `f*F` is locally free of rank `e` iff `f*ψ = 0` iff `f` factors through `V_e`", and that the strata glue "by this representing property." The formalized `EntryIdealStratum.lean` establishes only the **set-theoretic support** (`mem_range_stratumι_iff`: `x ∈ range(stratumι) ↔ pointRank = e`) plus the closed-subscheme construction — there is **no** functor-of-points / factorization statement for morphisms `T → V`. So the universal theorem's proof remains genuinely unformalized (its `proof` block correctly carries no `\leanok`); I wired its `\uses` to the construction and support nodes only, not to a representability node, because none exists. This is the main gap to hand back to Horizon.

2. **The stratum construction carries an explicit `ChartsCover` hypothesis** (every point lies in an `e`-presentation chart), which I surfaced as `def:charts_cover`. The universal-theorem prose treats the existence of local presentations as automatic (Nakayama prolongation on a noetherian scheme, `thm:nakayama_prolongation`). The Lean does not derive `ChartsCover` from noetherian+coherent — it takes it as input. The bridge lemma "coherent sheaf on a noetherian scheme admits `e`-presentation charts" is not present in this file; worth noting for whoever connects `stratum` to `flatLocusStratification_universal`.

3. No rank `≤ e` vs `= e` mismatch: the new `mem_range_stratumι_iff` gives fibre rank **exactly** `e`, consistent with the pre-existing `thm:entry_ideal_prime_iff` (also stated with `= e`).

I did not touch any Lean file or the `.json` DAG caches under `.archon-horizon/blueprints/`.
