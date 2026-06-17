# Blueprint Writer Report — slug: basic-proofs

## Task

Added `\begin{proof}...\end{proof}` environments to all 16 non-definition declarations
in `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex`.

## Files Modified

- `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex` — proof blocks added

## Files NOT modified

- `blueprint/src/content.tex` — untouched (per directive)
- All `.lean` files — untouched
- No `\leanok` markers added

## Declarations Processed

### Definitions (no proof added — per directive)
- `def:ambient_setup`
- `def:nondegenerate_app`

### Lemmas / Propositions / Theorems (proof blocks added)

| Label | `\uses{}` in proof | Source file |
|---|---|---|
| `lem:moduli_height_comparison` | `def:ambient_setup, thm:silverman_tate` | `intro.tex` |
| `prop:betti_map` | `def:ambient_setup` | `BettiMapForm.tex` |
| `prop:betti_form` | `prop:betti_map` | `BettiMapForm.tex` |
| `prop:betti_map_app` | `def:ambient_setup, prop:betti_map` | `HtIneqFinalVer.tex` |
| `lem:betti_rank_zar_open_app` | `prop:betti_map_app` | `HtIneqFinalVer.tex` |
| `thm:silverman_tate` | `def:ambient_setup` | `silvermantate.tex` |
| `lem:graph_construction` | `def:ambient_setup` | `HtIneq.tex` |
| `prop:aux_ht_ineq` | `prop:betti_form, lem:graph_construction, def:nondegenerate_app` | `HtIneq.tex` |
| `thm:ht_inequality` | `prop:aux_ht_ineq, thm:silverman_tate, lem:graph_construction` | `NTbase.tex` |
| `thm:ht_inequality_full` | `prop:betti_map_app, lem:betti_rank_zar_open_app, def:nondegenerate_app, thm:ht_inequality` | `HtIneqFinalVer.tex` |
| `lem:uniform_degree_bound` | `def:ambient_setup` | `SettingUp.tex` |
| `thm:nondeg_for_bd` | `def:ambient_setup, def:nondegenerate_app, prop:betti_map` | `SettingUp.tex` |
| `lem:vojtamumford` | `thm:silverman_tate, lem:uniform_degree_bound` | `RatPt.tex` |
| `lem:NAlon` | `def:ambient_setup` | `SettingUp.tex` |
| `lem:packets_alternative3` | `def:ambient_setup` | `SettingUp.tex` |
| `prop:alg_pt_far` | `thm:nondeg_for_bd, thm:ht_inequality_full, lem:uniform_degree_bound, lem:NAlon, lem:packets_alternative3` | `DistanceCurve.tex` |

## Citation Discipline

Every `% SOURCE QUOTE PROOF:` comment is verbatim text from a locally-read reference file.
Reference files read in this session:

- `references/MR4276287-mordell-lang-curves-source/intro.tex`
- `references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex`
- `references/MR4276287-mordell-lang-curves-source/HtIneqFinalVer.tex`
- `references/MR4276287-mordell-lang-curves-source/silvermantate.tex`
- `references/MR4276287-mordell-lang-curves-source/HtIneq.tex`
- `references/MR4276287-mordell-lang-curves-source/NTbase.tex`
- `references/MR4276287-mordell-lang-curves-source/SettingUp.tex`
- `references/MR4276287-mordell-lang-curves-source/DistanceCurve.tex`
- `references/MR4276287-mordell-lang-curves-source/RatPt.tex`

No citations were fabricated.

## Constraints Verified

- [x] No new declaration blocks added
- [x] No `\lean{}`, `\label{}`, or `\uses{}` in existing statement blocks changed
- [x] `def:ambient_setup` and `def:nondegenerate_app` left without proof blocks
- [x] No `\leanok` markers added anywhere
- [x] `content.tex` not modified
- [x] All `% SOURCE QUOTE PROOF:` backed by locally-read source files

## Status

DONE — all 16 proof blocks written successfully.
