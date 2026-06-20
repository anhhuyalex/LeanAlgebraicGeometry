# Stacks Project — "Properties of Schemes" (properties.tex)

## Citation
The Stacks Project Authors, "Properties of Schemes", in: *The Stacks Project*, chapter `properties`. Retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex (commit: master).

## Slug
stacks-properties

## Retrieval status
RETRIEVED — 2026-06-07

## Local source files
- references/stacks-properties.tex — LaTeX source, VERIFIED (opens as valid TeX, begins `\input{preamble}`) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex

Supporting file (not saved locally, fetched for tag lookup):
- tags file at https://raw.githubusercontent.com/stacks/stacks-project/master/tags/tags — used to resolve label→tag numbers; not saved.
- /tmp/stacks-modules.tex — Stacks modules.tex (fetched for Definition 01B5 body; not saved under references/).

## Why this source
Backs the blueprint lemma `lem:gf_qcoh_fintype_finite_sections` in `Picard_FlatteningStratification.tex`. That lemma asserts: for a quasi-coherent, finite-type sheaf F on a scheme X and an affine open W ⊆ X, the section module Γ(F,W) is a finite module over Γ(O_X,W). The exact Stacks tag and verbatim statement from this chapter are needed as the `% SOURCE:` / `% SOURCE QUOTE:` citation (keystone G1 bridge of geometric generic flatness).

## Contents map

Sections of `references/stacks-properties.tex` (5424 lines total):

- §"Introduction" — line 17
- §"Constructible sets" — line 27
- §"Integral, irreducible, and reduced schemes" — line 186
- §"Types of schemes defined by properties of rings" — line 294
- §"Noetherian schemes" — line 412
- §"Jacobson schemes" — line 742
- §"Normal schemes" — line 866
- §"Cohen-Macaulay schemes" — line 1047
- §"Regular schemes" — line 1120
- §"Dimension" — line 1196
- §"Catenary schemes" — line 1394
- §"Serre's conditions" — line 1508
- §"Japanese and Nagata schemes" — line 1611
- §"G-schemes" — line 1802
- §"The singular locus" — line 1873
- §"Local irreducibility" — line 1904
- **§"Characterizing modules of finite type and finite presentation"** — line 2075   ← RELEVANT
- §"Sections over principal opens" — line 2145
- §"Quasi-affine schemes" — line 2403
- §"Flat modules" — line 2590
- §"Locally free modules" — line 2626
- §"Locally projective modules" — line 2714
- §"Extending quasi-coherent sheaves" — line 2786
- §"Gabber's result" — line 3500
- §"Sections with support in a closed subset" — line 3707
- §"Sections of quasi-coherent sheaves" — line 3933
- §"Ample invertible sheaves" — line 4231
- §"Affine and quasi-affine schemes" — line 4838
- §"Quasi-coherent sheaves and ample invertible sheaves" — line 4924
- §"Finding suitable affine opens" — line 5133

### Deep: exact tag locations for directive targets

**Target 1 — Definition of finite type O_X-module**

- Stacks tag: **01B5** (`modules-definition-finite-type`)
- Source file: Stacks `modules.tex`, **not** `properties.tex`
- Location in modules.tex: lines 809–817 (in the section on "Finite type and finitely presented modules")
- The definition is referenced in properties.tex at line 2082 as `Modules, Definition \ref{modules-definition-finite-type}`.
- To read verbatim: `Read /tmp/stacks-modules.tex offset:809 limit:9` — or fetch modules.tex from GitHub raw.

**Target 2 — Lemma: finite-type quasi-coherent module on affine ↔ M̃ of finite R-module**

- Stacks tag: **01PB** (`properties-lemma-finite-type-module`)
- Source file: `references/stacks-properties.tex`, **lines 2092–2110**
- Section: §"Characterizing modules of finite type and finite presentation" (tag 01PA), line 2075
- To read verbatim: `Read references/stacks-properties.tex offset:2092 limit:19`

Introductory paragraph of the section (lines 2078–2090) provides the key informal claim verbatim in TeX, bridging both targets: "The following lemma implies that F is of finite type ... if and only if F is on each open affine Spec(A) = U ⊂ X of the form M̃ for some finite A-module M."

## Caveats

- The definition of "finite type" for O_X-modules (tag 01B5) lives in `modules.tex`, not `properties.tex`. The properties chapter references it by `\ref{modules-definition-finite-type}`. If the blueprint citation needs the definition itself, also fetch/cite modules.tex (tag 01B5).
- Lemma 01PB (properties-lemma-finite-type-module) covers precisely the affine case. The section introduction (lines 2078–2090, unnumbered prose tagged under 01PA) provides the global-scheme corollary in informal terms.
- The tags file (`tags/tags` in the stacks-project repo) was used to resolve label→tag; the tag numbers 01PA, 01PB are stable Stacks identifiers.

## Quality / provenance
This is the authoritative primary source (The Stacks Project, master branch). Retrieved directly from the open GitHub repository of the Stacks Project. Tag numbers resolved against the project's own `tags/tags` file, not estimated.
