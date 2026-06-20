# Analogy: cost-scoping `IsInvertible M ⟹ M coherent locally-free rank 1` for the A.2.c Quot embedding

## Mode
api-alignment

## Slug
engine252

## Iteration
252

## Question
For the A.2.c Quot-scheme embedding the project needs
`IsInvertible M ⟹ M is a coherent, locally free 𝒪-module of rank 1`
(Stacks `lemma-invertible-is-locally-free-rank-1`), `M : Scheme.Modules X`, with
`IsInvertible M := ∃ N, Nonempty (M ⊗ N ≅ 𝟙_)`. Three sub-questions: (Q1) does
Mathlib already carry this, or the `Module.Invertible`/`Projective`/finite-locally-free/
`FinitePresentation` machinery that composes into it; (Q2) is the obstacle the same
Mathlib-absent finite-presentation spreading-out the FORWARD bridge needed, or a
strictly cheaper coherence statement; (Q3) realistic LOC/iter band + build sketch.

## Project artifact(s)
- `Picard/TensorObjSubstrate.lean:179` — `IsInvertible M := ∃ N, Nonempty (tensorObj M N ≅ 𝟙_)`.
- `Picard/LineBundlePullback.lean:115` — `IsLocallyTrivial M := ∀x ∃ affine U, M|_U ≅ 𝒪_U`.
- `Picard/LineBundlePullback.lean:130` — `OnProduct := {M // IsLocallyTrivial M}` (RPF/Pic⁰ carrier).
- `Picard/QuotScheme.lean:192,209,308` — Quot functor of **coherent** quotients; points are
  `(F, q : E_T ↠ F)`, `F` coherent + flat; base `S` `IsLocallyNoetherian`/`LocallyOfFiniteType`.
- `analogies/invertible-loctriv-bridge.md` (iter-245) — already ruled the FORWARD bridge
  `IsInvertible ⟹ IsLocallyTrivial` Mathlib-scale **and OFF the A.1.c path**.

## Decisions identified

### Decision 1: Does Mathlib carry "invertible ⟹ coherent loc-free rank 1" for sheaves? (Q1)

- **Mathlib idiom — RING level only, COMPLETE.** `Mathlib.RingTheory.PicardGroup` gives, from
  `Module.Invertible R M`:
  - `Module.Invertible.instProjective` (⟹ `Module.Projective R M`),
  - `Module.Invertible.instFinite` (⟹ `Module.Finite R M`),
  - `Module.Invertible.finrank_eq_one` (over a free/local base, `finrank = 1`),
  - `Module.Invertible.of_isLocalization` (base-change stability),
  - `CommRing.Pic.mk_eq_one_iff_free`.
  Composing `instProjective + instFinite` with `Module.finitePresentation_of_projective`
  (`Mathlib.Algebra.Module.FinitePresentation`) gives `Module.FinitePresentation R M`, i.e. the
  full "invertible ⟹ finite projective rank-1" at the level of a module over a **ring**.
- **Sheaf-level coherence predicates EXIST but are NOT connected to invertibility.** Present:
  `SheafOfModules.IsFiniteType` (`…Sheaf.Generators`), `SheafOfModules.IsFinitePresentation`
  / `QuasicoherentData.IsFinitePresentation` (`…Sheaf.Quasicoherent`),
  `SheafOfModules.IsQuasicoherent`, `SheafOfModules.free` / `ιFree` (`…Sheaf.Free`),
  `instIsFiniteTypeOfIsFinitePresentation`.
- **Verified ABSENT** (LSP: no loogle/leansearch hit):
  1. NO `SheafOfModules.IsLocallyFree` / `Scheme.Modules.IsLocallyFree` predicate at all.
  2. NO "invertible sheaf ⟹ locally free rank 1" at `SheafOfModules` / `Scheme.Modules` level.
  3. NO map from the sheaf-level `IsInvertible` (`∃N, M⊗N≅𝒪`) to ANY coherence predicate
     (`IsFiniteType`/`IsFinitePresentation`): `IsInvertible` supplies **no finite-presentation
     datum** for `M` as a sheaf.
  4. NO stalk-iso ⟹ neighbourhood-iso spreading-out for `SheafOfModules`. (Project's
     `isIso_of_isIso_restrict` is global-from-a-GIVEN-cover, not single-stalk spread-out.)
- **Gap**: divergent-with-cost at sheaf level. **Verdict: NEEDS_MATHLIB_GAP_FILL** (sheaf level).
  Mathlib has the ring-level half complete and the sheaf-level coherence *vocabulary*, but not the
  glue.

### Decision 2: Same Mathlib-scale spreading-out as the forward bridge, or cheaper? (Q2)

The statement **factors**, and the two halves have completely different cost:

- **HARD half — `IsInvertible M ⟹ M finitely presented (loc-triv)`.** This IS the same
  Mathlib-absent finite-presentation spreading-out that iter-245 priced for the forward bridge
  `IsInvertible ⟹ IsLocallyTrivial`. To realise it you must: pass to a stalk `𝒪_{X,x}`, show
  `M_x` invertible over the local ring (⟹ free rank 1 via `Module.Invertible` + `finrank_eq_one`),
  THEN spread the stalk-freeness to a Zariski neighbourhood. The spreading-out engine
  (`Module.isOpen_freeLocus`, `Module.basicOpen_subset_freeLocus_iff`,
  `Module.freeLocus_eq_univ`, all in `…Spectrum.Prime.FreeLocus`) **requires
  `[Module.FinitePresentation R M]` as a hypothesis** — and `IsInvertible` gives no way to
  produce it for the sheaf. So the chicken-and-egg is real: bespoke, Mathlib-scale. **Matches
  iter-245's NEEDS_MATHLIB_GAP_FILL exactly; off the A.1.c path.**
- **CHEAP half — `IsLocallyTrivial M ⟹ coherent loc-free rank 1`.** Once `M` is loc-triv,
  on each chart `M.restrict U.ι ≅ 𝒪_U` (rank-1 free, definitional from
  `LineBundlePullback.lean:115`). Rank 1 is then free, flatness is free (`𝒪_U` flat), and
  "coherent" = `SheafOfModules.IsFinitePresentation` is assembled by handing the trivialising
  cover to `QuasicoherentData` with each chart's presentation = the trivial free presentation of
  `𝒪_U`. No spreading-out, no stalks, no Mathlib gap.
- **THE COST-COLLAPSING FACT.** The Quot embedding's input is NOT a bare `IsInvertible` object —
  it is a point of `Pic⁰_{C/k}`, the representing scheme of RPF, whose carrier is
  **`IsLocallyTrivial`** (`OnProduct = {M // IsLocallyTrivial M}`, STRATEGY "RPF carrier =
  IsLocallyTrivial (DECIDED on merits)"; `exists_tensorObj_inverse` already returns a loc-triv
  witness). So the embedding never has to cross the HARD half: it starts already loc-triv.
- **Gap**: the literal `IsInvertible ⟹ …` is divergent-with-cost (Mathlib-scale); the
  loc-triv-routed `IsLocallyTrivial ⟹ …` is divergent-equivalent-but-cheap.
- **Verdict**: **DIVERGE_INTENTIONALLY** — do NOT build the literal `IsInvertible` statement.
  Build `IsLocallyTrivial ⟹ IsFinitePresentation (+ rank-1 record)` and feed the embedding from
  the loc-triv carrier. The deepest-unquantified-risk framing dissolves: it is the SAME hard
  spreading-out as the forward bridge **only if you insist on the `IsInvertible` entry point**,
  which the consumer does not require.

### Decision 3: cost band + build sketch (Q3)

- **If forced from `IsInvertible`** (NOT recommended): same Mathlib-scale bespoke spreading-out
  as iter-245's forward bridge — order ~300–600 LOC of genuinely new sheaf finite-presentation
  spreading-out, or pin with a typed `sorry`. Budget as Mathlib-scale.
- **From `IsLocallyTrivial`** (recommended; the real cost): **~120–250 LOC / ~3–6 iters.**
  Bulk is bookkeeping, not deep mathematics.
  - **C1 — cover extraction** (~30–60 LOC): turn the pointwise `IsLocallyTrivial M`
    (`∀x ∃ affine U, M|_U ≅ 𝒪_U`) into an indexed affine cover + per-index trivialisation iso.
    Watch: the `J.over X` site instances `QuasicoherentData` demands
    (`HasWeakSheafify`/`WEqualsLocallyBijective`/`HasSheafCompose`) must be discharged for
    `X.ringCatSheaf`; the project already inhabits the `SheafOfModules X.ringCatSheaf` world, so
    these should resolve, but confirm at build entry (chief unknown).
  - **C2 — per-chart free presentation** (~30–60 LOC): from `M|_U ≅ 𝒪_U = free {*}` produce
    `(M|_U).Presentation` / `QuasicoherentData.presentation i` via `SheafOfModules.free` +
    `ιFree`; the presentation of a rank-1 free is trivial.
  - **C3 — assemble `M.IsFinitePresentation`** (~30–60 LOC): package C1+C2 into
    `SheafOfModules.QuasicoherentData` + `IsFinitePresentation.mk`; `IsFiniteType` is then free
    (`instIsFiniteTypeOfIsFinitePresentation`).
  - **C4 — rank-1 / flat records + Quot-point wrapper** (~20–40 LOC): rank 1 and flatness are
    chart-local (`𝒪_U`); expose whatever the embedding consumes (Hilbert-poly input / coherent
    quotient datum).
- **Named gap that must be built first**: none Mathlib-scale on the loc-triv route — the only
  bespoke piece is C1's cover-to-`QuasicoherentData` adaptor, which is project-local plumbing,
  not a missing Mathlib theorem. The Mathlib-scale gap (sheaf finite-presentation spreading-out)
  is needed ONLY on the abandoned `IsInvertible` entry point.

## Recommendation
Re-estimate the A.2.c "Quot embedding line-bundle coherence" row at **~120–250 LOC / ~3–6 iters,
NOT Mathlib-scale**, on the firm condition that the embedding is fed from the `IsLocallyTrivial`
carrier (the RPF/Pic⁰ representing-object carrier) rather than from bare `IsInvertible`. The
project should build `IsLocallyTrivial M ⟹ M.IsFinitePresentation` (Mathlib
`SheafOfModules.IsFinitePresentation` via `QuasicoherentData` from the trivialising cover) plus a
rank-1/flat record, and NOT build `IsInvertible ⟹ IsLocallyTrivial` (the Mathlib-scale
finite-presentation spreading-out from iter-245, which is off-path). An engine prover lane on the
loc-triv coherence half can safely run in parallel with the substrate — its only nontrivial
dependency is the `J.over X` site instances for `X.ringCatSheaf`, which should be checked in the
lane's first iter (the chief de-risking step). Do NOT open a lane on the `IsInvertible` entry
point. The strategy critic's "deepest unquantified risk" is real for the literal statement but is
retired by the carrier choice the project already made.
