# Stacks Project — Chapter 27 "Constructions of Schemes" (constructions.tex)

## Citation
The Stacks Project authors, "Constructions of Schemes", Chapter 27 of *The Stacks
Project*, https://stacks.math.columbia.edu/. Chapter source `constructions.tex`
retrieved from the GitHub mirror.

## Slug
stacks-constructions

## Retrieval status
RETRIEVED — 2026-05-22

## Local source files
- `references/stacks-constructions.tex` — LaTeX chapter source, VERIFIED (186080
  bytes, 5168 lines, opens cleanly with `\input{preamble}` on L1 and
  `\title{Constructions of Schemes}` on L7) — retrieved from
  `https://raw.githubusercontent.com/stacks/stacks-project/master/constructions.tex`

Tag→label map cross-checked against the repo's `tags/tags` (also pulled
fresh from `https://raw.githubusercontent.com/stacks/stacks-project/master/tags/tags`).

## Why this source
The iter-171 deliverable `blueprint/src/chapters/Picard_RelativeSpec.tex`
needs verbatim `% SOURCE QUOTE:` LaTeX excerpts from §"Relative spectrum via
glueing" + §"Relative spectrum as a functor" for the construction of the
`Spec_X 𝒜 : QCoh(X)^op → Sch/X` functor — Route A.1's foundational layer
underneath the relative Picard functor. The writer quotes directly from
`stacks-constructions.tex` line-by-line; this pointer maps each named tag to
its exact line so the writer can `Read` with `offset`/`limit` and copy the
source unchanged.

## Tags covered (location in the fetched file)

Each row records the directive's named tag, its `\label{...}` in `tags/tags`,
the corresponding object kind found in `constructions.tex`, and the line
range to read. Note several of the directive's tags are labels for SECTION
headings or an EQUATION — not lemmas/definitions — so the writer should
quote the surrounding block as appropriate.

| Tag | Stacks label | Kind in source | Line(s) in fetched .tex |
| --- | --- | --- | --- |
| **01LL** | `section-spec-via-glueing` | `\section{...}` heading + `\label{...}` (no `\begin{definition}` here — see caveat) | `\section{Relative spectrum via glueing}` **L309**, `\label{section-spec-via-glueing}` **L310** |
| **01LO** | `lemma-transitive-spec` | `\begin{lemma}` (transitivity of the glueing maps for three nested affine opens — NOT the affine base case; see caveat) | `\begin{lemma}` L363, `\label{...}` **L364**, statement L364–374, proof L376–379 |
| **01LQ** | `section-spec` | `\section{...}` heading + `\label{...}` (introduces the functor `F` of pairs `(f,φ)` whose representability gives `Spec_S 𝒜`) | `\section{Relative spectrum as a functor}` **L427**, `\label{section-spec}` **L428** |
| **01LR** | `equation-spec` | `\begin{eqnarray}` numbered equation labelling the functor `F : Sch^{opp} → Sets` definition (NOT a lemma) | inside `\begin{eqnarray}` ... `\end{eqnarray}` L460–465, `\label{equation-spec}` **L461** |
| **01LS** | `lemma-spec-base-change` | `\begin{lemma}` (base-change of the functor `F` along `g : S' → S`) | `\begin{lemma}` L467, `\label{...}` **L468**, statement L468–480, proof L482–489 |

### Adjacent tags the writer is likely to need too (already in fetched file)

The same `tags/tags` lookup turned these up — they sit between the directive's
five tags and are the natural quote targets if the writer's `% SOURCE QUOTE:`
blocks cover the actual existence / affine-case content the directive describes:

| Tag | Stacks label | Kind | Line(s) | Why mention here |
| --- | --- | --- | --- | --- |
| **01LM** | `situation-relative-spec` | `\begin{situation}` defining `S` + quasi-coherent `𝒪_S`-algebra `𝒜` | L312–318 | This is the closest thing to a "definition of a quasi-coherent sheaf of `𝒪_S`-algebras" that the chapter offers — likely what the dispatcher meant by 01LL. |
| **01LP** | `lemma-glue-relative-spec` | `\begin{lemma}` constructing `π : Spec_S(𝒜) → S` by glueing with `iU` isomorphisms | L381–414 (statement L381–405, proof L407–414) | The actual **existence** statement by glueing — likely part of what the dispatcher meant by 01LQ. |
| **01LT** | `lemma-spec-affine` | `\begin{lemma}` "if `S = Spec R`, `F` is representable by `Spec(Γ(S, 𝒜))`" | L491–545 (statement L491–497, proof L499–545) | This is **the affine base case** — the actual content the dispatcher described under 01LO. |
| (no tag visible inline) | `lemma-spec` | `\begin{lemma}` "`F` is representable by a scheme" | L547–600 | The clean **representability** statement for general `S`. |
| (no tag visible inline) | `lemma-glueing-gives-functor-spec` | `\begin{lemma}` identifying the glueing construction with the representing scheme | L602–639 | Bridges the two constructions of `Spec_S 𝒜`. |
| (no tag visible inline) | `definition-relative-spec` | `\begin{definition}` of `π : Spec_S(𝒜) → S` + the "universal family" `𝒜 → π_*𝒪` | L641–656 | This is **the named definition** of the relative spectrum — likely what the dispatcher meant by 01LL. |
| (no tag visible inline) | `lemma-spec-properties` | `\begin{lemma}` 3-part properties: (1) `π^{-1}(U)` affine; (2) **base change**; (3) universal map is iso | L662–691 | Part (2) is the base-change *property* the dispatcher described under 01LS; the dispatcher's 01LS (`lemma-spec-base-change`) is actually the base-change of the functor `F` upstream of representability. |

## Caveats

The dispatcher's directive maps the five tags to functional roles ("definition
of quasi-coherent algebra", "affine base case", "existence + UP", "functoriality
/ adjunction", "base change") that **only partially match** the labels those
tags actually carry in `constructions.tex`. Three concrete mismatches to flag
before the writer quotes:

1. **01LL is a section label, not a definition.** The directive describes 01LL
   as "definition of a quasi-coherent sheaf of algebras". In the source, 01LL
   labels `\section{Relative spectrum via glueing}` (L309–310). The closest
   thing in the chapter to a *definition* of quasi-coherent `𝒪_S`-algebra is
   the situation block 01LM at L312–318; the named `\begin{definition}` of the
   relative spectrum itself is `definition-relative-spec` at L641–656 (no
   inline tag visible). The writer should choose between 01LL (section),
   01LM (situation), and `definition-relative-spec` (definition) according
   to what they actually intend to quote.

2. **01LO is the transitivity glueing lemma, not the affine base case.** The
   directive describes 01LO as "affine base case: when `X = Spec R`, the
   relative spectrum `Spec_X 𝒜 ≅ Spec(Γ(X, 𝒜))`". In the source, 01LO labels
   `lemma-transitive-spec` at L363–379 (composition of two `Spec(A) → Spec(A')`
   open immersions). The affine-base-case lemma the dispatcher describes is
   `lemma-spec-affine`, tag **01LT** at L491–545. If the writer wants the
   affine-case statement, they should `% SOURCE QUOTE:` from 01LT, not 01LO.

3. **01LR is an equation, not a functoriality / adjunction lemma.** The
   directive describes 01LR as "functoriality of the relative spectrum /
   adjunction with pushforward `π_*`". In the source, 01LR labels the
   `\begin{eqnarray}` defining the functor `F : Sch^{opp} → Sets`, L460–465.
   The "universal map" `𝒜 → π_*𝒪_{Spec_S 𝒜}` is part of the
   `definition-relative-spec` block (L650–655) and the `is an isomorphism`
   statement is part (3) of `lemma-spec-properties` (L662–691, no inline tag
   visible). The writer should reach for the right block according to what
   "functoriality / adjunction" actually means in the Picard chapter — quoting
   the equation 01LR alone will not give an adjunction statement.

Tags 01LQ (section-spec) and 01LS (lemma-spec-base-change) match the
directive's descriptions cleanly.

Tag numbers (01LL etc.) are the permanent citation keys; the displayed
chapter/lemma numbering ("Lemma 27.x.y") is auto-generated and snapshot-
dependent and does NOT appear in the `.tex` source — only the inline number
list `tags/tags` would let you reconstruct it. Line numbers are exact for
GitHub master as of 2026-05-22.

## Quality / provenance
Authoritative verbatim source from `stacks/stacks-project` GitHub master;
tag↔label table confirmed against `tags/tags` for all five directive tags
plus the seven adjacent tags/labels flagged in the caveats; every statement
read and confirmed in-file against the line ranges above.
