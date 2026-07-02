# Analogy: Mathlib coverage of Serre duality for the genus equality `dim H⁰(Ω) = dim H¹(O)`

## Slug
serre-duality-iter110

## Iteration
110

## Question

Does Mathlib b80f227 have infrastructure that bridges Serre duality to a
`Module.rank` / `Module.finrank`-style equality on a smooth proper geometrically
irreducible curve `C / k`, at a level the project can consume to close
`AlgebraicGeometry.Scheme.serre_duality_genus` at
`AlgebraicJacobian/Differentials.lean:877`?

```lean
theorem serre_duality_genus {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left] [IsProper C.hom]
    (hsmooth : Smooth C.hom) :
    Module.rank k (HModule k (toModuleKSheaf C) 0) =
      Module.rank k
        (HModule k (moduleKSheafOfModules C (relativeDifferentials C.hom)) 0) := by
  sorry
```

## Project artifact(s)

- `AlgebraicJacobian/Differentials.lean:871-877` — the variance-flagged sorry.
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean:248-253` — the
  project-local `HModule k F n := Abelian.Ext (constantSheaf … (ModuleCat.of k k)) F n`,
  the `ModuleCat k`-flavoured cohomology that the LHS / RHS both consume.
- `blueprint/src/chapters/Differentials.tex:175-185` — the blueprint statement
  (carries `\leanok` flag for the statement; no proof block).

## Decisions identified

The directive is one design question, but the closure path compresses three
sub-decisions: (A) does Mathlib have the *abstract* Serre duality theorem,
(B) does it have the *partial pieces* (dualizing sheaf, canonical sheaf,
trace map for proper morphisms) so the project can compose them, and
(C) is the project's `HModule` the right interface for whatever bridge gets
written.

### Decision A: Does Mathlib have a `SerreDuality` / `serre_duality` API?

- **Mathlib idiom**: **NONE EXISTS.** Exhaustive verification:
  - `lean_local_search` for `SerreDuality` → `[]` (zero hits).
  - `lean_local_search` for `serre_duality` → only the project's own
    `AlgebraicGeometry.Scheme.serre_duality_genus` and its iter-067/069/075/078/079
    snapshot copies.
  - File-system `grep -rE "[Ss]erre[Dd]uality|[Ss]erre.*duality"
    .lake/packages/mathlib/Mathlib/AlgebraicGeometry` → **no files found**.
  - File-system `grep -rE "[Ss]erre"` across all of Mathlib returns only
    `SerreClass` (Serre subcategories of abelian categories — totally
    unrelated; a Bousfield-localisation device, not duality),
    `Algebra/Lie/SerreConstruction.lean` (Serre's presentation of semisimple
    Lie algebras), and incidental references to "Serre" in number-theory
    files (modular forms / valuation theory). **No Serre duality on
    schemes, varieties, projective spaces, or curves.**
- **Project's path**: the existing `serre_duality_genus` has the right
  dimension-equality statement (no shortcut available; this *is* the
  theorem the project wants).
- **Gap**: divergent-and-wrong only in the sense that there is nothing in
  Mathlib to align with; the project's statement is correct.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**. Mathlib has *no Serre duality
  whatsoever*. Direct closure via a Mathlib lemma is impossible.

### Decision B: Does Mathlib have partial pieces (canonical sheaf, dualizing complex, trace map for proper morphisms)?

- **Mathlib idiom — canonical sheaf / dualizing sheaf**: **NONE EXISTS.**
  - `lean_local_search` for `DualizingSheaf` and `dualizing` → `[]` (zero hits).
  - `grep -rE "canonical[Bb]undle|canonicalSheaf|canonical.*[Ss]heaf|relative[Dd]ualizing|RelativeDualizing"
    .lake/packages/mathlib/Mathlib` → only six occurrences in
    `AlgebraicGeometry`, all using "canonical" in unrelated senses (the
    canonical morphism `X → Spec Γ(X, ⊤)`, the subcanonical Grothendieck
    topology, the canonical map from a localisation). **No "canonical
    bundle / canonical sheaf" object in the Serre-duality sense.**
  - `Mathlib.AlgebraicGeometry.Modules.*` and
    `Mathlib.Algebra.Category.ModuleCat.Sheaf.Differentials` give the
    *relative* differentials sheaf `Ω_{X/S}` (which the project already
    consumes via `relativeDifferentials`), but *no identification of
    `Ω_{C/k}` with a dualizing sheaf*.
- **Mathlib idiom — trace map for proper morphisms**: **NONE EXISTS.**
  - `grep -rE "[Tt]race[Mm]orphism|trace_morphism"` → only seven files,
    all algebraic (`RingTheory/Trace`, `LinearAlgebra/Trace`,
    `LinearAlgebra/Matrix/Trace`, `FieldTheory/Finite/Trace`,
    `Algebra/Lie/Weights/Chain`, `Algebra/DirectSum/LinearMap`, plus a
    `Tactic/FunProp/Core` reference). **No `f_*ω_X → ω_S` trace morphism
    for a proper morphism `f : X → S`.**
- **Mathlib idiom — coherent cohomology of proper schemes**: **NONE EXISTS.**
  - `grep -rE "[Cc]ohomology"` in `Mathlib.AlgebraicGeometry` returns only
    five files: `Properties.lean`, `Sites/BigZariski.lean`,
    `Sites/ElladicCohomology.lean`, `Modules/Sheaf.lean`,
    `AffineTransitionLimit.lean`. The first four are infrastructure files
    where "cohomology" is mentioned only in passing (e.g. as
    `IsCohomological`-style booleans on Grothendieck topologies); only
    `ElladicCohomology.lean` actually *defines* a cohomology theory
    (ℓ-adic, on the *pro-étale* site, valued in `Type (u+1)`) — and this is
    the **only place in Mathlib's algebraic geometry that consumes
    `CategoryTheory.Sheaf.H`**. There is **no Zariski coherent cohomology
    infrastructure** built on top of `Sheaf.H` in Mathlib b80f227.
  - `lean_leansearch "cohomology of structure sheaf and Kahler differentials are dual"`
    surfaces only ring-level Kähler-rank lemmas
    (`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`),
    not sheaf-cohomology dualities.
  - `lean_leansearch "rank cohomology equals rank cohomology dual sheaf"`
    surfaces only `Module.dual_rank_eq` (rank V* = rank V for
    finite-dimensional free `V`) and the Erdős-Kaplansky theorems —
    **abstract linear algebra, not sheaf-theoretic**.
- **Mathlib idiom — Riemann–Roch / Riemann–Hurwitz**: **NONE EXISTS.**
  - `grep -rE "RiemannRoch|riemann_roch|RiemannHurwitz|riemann_hurwitz"` →
    no files found.
- **Project's path**: would have to *build* the trace map + duality
  pairing + perfect-pairing argument from first principles, on top of the
  project's `HModule` cohomology infrastructure plus the
  `relativeDifferentials` cotangent sheaf and a tensor product on
  `SheafOfModules`.
- **Gap**: not "divergent" — there is simply **no precedent at all**.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**. There are no partial pieces
  worth composing; the entire Serre-duality stack is a structural
  absence in Mathlib's algebraic geometry, comparable in scope to the
  Hilbert/Quot scheme gap that drives the project's C3 deferral
  (cf. `STRATEGY.md` § "Phase C3 exit policy").

### Decision C: Is the project's `HModule` the right interface, or a parallel API that should align with Mathlib's `Sheaf.H`?

- **Mathlib idiom**: `CategoryTheory.Sheaf.H` at
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic:57-60`:
  ```lean
  def H (n : ℕ) : Type w' :=
    Ext ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F n
  deriving AddCommGroup
  ```
  This is the `AddCommGrpCat`-valued canonical sheaf-cohomology definition,
  for a sheaf `F : Sheaf J AddCommGrpCat`.
- **Project's path**: `Scheme.HModule` at
  `AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean:248-253`:
  ```lean
  noncomputable abbrev HModule (k : Type u) [Field k] {C} [Category C]
      {J : GrothendieckTopology C} [HasSheafify J (ModuleCat.{u} k)]
      [HasExt (Sheaf J (ModuleCat.{u} k))]
      (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) : Type (u+1) :=
    Abelian.Ext ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k)) F n
  ```
- **Gap**: divergent-equivalent (a deliberate, necessary specialisation,
  not a parallel API). Specifically:
  - Mathlib's `Sheaf.H` is **specifically for `AddCommGrpCat`-valued sheaves**
    (the constant sheaf is `constantSheaf J AddCommGrpCat`). It cannot host
    a `Module k` instance, hence cannot be the LHS of a `Module.rank k`
    statement.
  - The project needs `Module k` on the cohomology to write `Module.rank k`,
    so the natural change is `AddCommGrpCat` → `ModuleCat k` and
    `(ULift ℤ)` → `k`. Mathlib's `Abelian.Ext.instModule` (from the
    `Linear k`-enrichment of `Sheaf J (ModuleCat k)`, auto-inferable via
    `Sheaf.linear` from `HasSheafify J (ModuleCat k)`) supplies the
    `Module k` instance automatically once the constant sheaf is
    `ModuleCat`-valued.
  - The `noncomputable abbrev` (rather than `def`) is required so instance
    synthesis sees through to find `Module k (HModule k F n)` and
    `AddCommGroup (HModule k F n)` — `def` would have broken
    `Module.rank` / `Module.finrank` typechecking, exactly per the iter-009
    design rationale documented inline.
  - Bridge to Mathlib's `Sheaf.H` (e.g. via `forget₂ (ModuleCat k) AddCommGrpCat`)
    is *possible* but unnecessary for the present statement, because
    `Sheaf.H` cannot host the `Module k` rank-equality at all; the
    bridge would lose information.
- **Verdict**: **PROCEED**. The project's `HModule` is the correct
  Mathlib-aligned `ModuleCat k`-flavoured copy of `Sheaf.H`, structurally
  identical modulo the universally-needed `AddCommGrpCat → ModuleCat k`
  change. No refactor obligation; no parallel-API risk. The `HModule`
  abstraction is what *would* be upstreamed if Mathlib eventually adds a
  `Linear R`-flavoured sheaf-cohomology API (cf. the existing
  `Linear R`-enrichment of `Abelian.Ext.linearEquiv₀` that the project
  already consumes in `HModule_zero_linearEquiv` at L266-273).

## Closure cost estimate

The directive asks for three scenarios (a) / (b) / (c). Findings collapse
the choice space to **only (c)**:

- **(a) Mathlib has full Serre duality**: NOT APPLICABLE. Zero
  infrastructure. LOC estimate: vacuous.
- **(b) Mathlib has partial pieces and project must compose**: NOT
  APPLICABLE. The only "partial pieces" findable are (i) `Module.dual_rank_eq`
  for finite-dim vector spaces (zero geometric content; sees neither sheaf
  nor cohomology nor curves) and (ii) the project's own `relativeDifferentials`
  (already consumed; no duality bridge attaches to it). LOC estimate: vacuous
  — a "compose"-style proof would have to reconstruct the geometric content
  from scratch, indistinguishable from scenario (c).
- **(c) Mathlib has neither and project must redefine + prove from first
  principles**: the only realistic scenario. To close `serre_duality_genus`
  honestly (no `axiom`, no `sorry`), the project must build:
  1. **Trace map for the structure morphism of a smooth proper curve**
     `Tr_{C/k} : H¹(C, Ω_{C/k}) → k`. This is the heart of the construction
     and requires the residue-based local description of `H¹(C, ω_C)`
     plus the global integral-over-curve identification. (Hartshorne III.7
     for the abstract setup; III.7.14 for the curve case.)
  2. **Duality pairing** `H⁰(C, F) × H¹(C, ω_C ⊗ F^∨) → k` for a coherent
     sheaf `F`, specialising at `F = O_C` to give
     `H⁰(C, O_C) × H¹(C, Ω_{C/k}) → k`.
  3. **Perfect-pairing theorem**: the pairing in (2) is non-degenerate
     on both sides, *and* both sides are finite-dimensional; the
     finite-dimensionality piece partially exists in the project's
     `IsHModuleHomFinite` / `IsAffineHModuleVanishing` infrastructure
     (`StructureSheafModuleK.lean:418-487`) but only for `H⁰` and only
     for the structure sheaf; the `Ω_{C/k}` finiteness needs
     `module_finite_HModule_zero` instantiated against the cotangent
     sheaf, which itself needs the `Differentials.lean` Phase B
     infrastructure (`relativeDifferentialsPresheaf_isSheaf` L122 +
     `smooth_iff_locally_free_omega` L718) to land first.
  4. **Bridge to the rank equality**: with (3) in hand, `Module.dual_rank_eq`
     gives `dim H¹(C, ω_C) = dim H⁰(C, O_C)*` (which by perfect pairing
     equals `dim H⁰(C, ω_C) = dim H⁰(C, Ω_{C/k})`), and the same pairing
     specialised at `F = Ω_{C/k}` gives `dim H¹(C, O_C) = dim H⁰(C, Ω_{C/k})*`,
     yielding the project's target rank-equality after composing.

  **LOC estimate**: **3,000–8,000 LOC** total spread across (1)–(4).
  Multi-dozen iterations. Comparable in scope to the Hilbert / Quot scheme
  gap that drives Phase C3's deferral (cf. `STRATEGY.md` L19 "5,000–10,000
  LOC each", L72 "Hartshorne-chapter-sized undertaking"). The project's
  ~10–20 prover-iteration / ~280–500 LOC remaining budget
  (`STRATEGY.md` L22) cannot absorb this.

  Note: this estimate assumes the project would build *only what's needed
  for the curve case*, not abstract Serre duality on smooth proper schemes
  of arbitrary dimension (which would balloon to ~20,000 LOC by analogy
  with the existing Mathlib coherent-cohomology footprint of zero).
  Even with that restriction, the trace map alone (item 1) is a multi-iter
  build out — analogous in difficulty to the existing project work on
  Mayer-Vietoris LES (`Cohomology_MayerVietoris.tex`), which has
  consumed ~10+ iters of formalisation effort and remains gated.

## Recommendation

**Defer `serre_duality_genus` indefinitely as a named Mathlib-gap sorry,
joining the existing 6 named gaps in the project's end-state disclosure
surface (`STRATEGY.md` L24-30).**

The recommendation aligns with the project's existing exit policies:

1. **Same shape as `JacobianWitness` (Phase C3 exit policy,
   `STRATEGY.md` L67-73)**: a named existence sorry that bottoms out in a
   structural Mathlib gap of Hartshorne-chapter scope, kept honest as a
   single inline `sorry` rather than diffused via false-progress workarounds.
2. **Same shape as `instIsMonoidal_W` (`Modules/Monoidal.lean` L173)**:
   a single named-deferred sorry that becomes load-bearing for the downstream
   arc; honest disclosure paragraph in End-state preserves accountability.
3. **Same shape as `cotangentExactSeq_structure.h_exact`
   (`Differentials.lean` L636)**: a named-deferred parallel sorry whose
   Mathlib gap is the missing stalkwise-exactness criterion for `SheafOfModules`.

**Concrete plan-agent action items** (not directives — the plan agent decides):

- **Update `STRATEGY.md`**: append a 7th named-gap entry under L24-30:
  `7. serre_duality_genus (Differentials.lean L877) — Serre duality for
   smooth proper curves. Mathlib b80f227 has no Serre-duality, no dualizing
   sheaf, no canonical sheaf, no trace morphism for proper morphisms, no
   coherent cohomology of proper schemes, no Riemann-Roch. Closure requires
   ~3,000–8,000 LOC of first-principles construction (trace map +
   duality pairing + perfect-pairing argument), comparable in scope to the
   Hilbert/Quot gap driving Phase C3 deferral.`
- **Update `Mathlib gaps in scope` table** (`STRATEGY.md` L97-106): add
  a row `Serre duality / dualizing sheaf / trace morphism for proper
  morphisms | B | Defer indefinitely. Single named sorry at L877.`
- **Update End-state disclosure** (`STRATEGY.md` L75-87): the named-gap
  count moves from 6 → 7. Phase B closure becomes "L122, L718, L735
  prover-viable in parallel; L877 deferred via named-gap exit policy
  (mathlib-analogist-serre-duality-iter110 verdict)."
- **Add `% NOTE:` in `blueprint/src/chapters/Differentials.tex`** at
  the `\begin{theorem}` for `serre_duality_genus`: clarify that closure
  is structurally blocked by Mathlib's absence of Serre-duality
  infrastructure; the statement is correct and consumed downstream by
  `genus`-rank instances; the proof body remains `sorry` as a named
  Mathlib gap.
- **Iter-111 prover lane scoping**: `serre_duality_genus` (L877) stays
  out of scope for Phase B prover work. L122, L718, L735 remain
  prover-viable in parallel per `STRATEGY.md` L124.
- **No `HModule` refactor needed**: the project's cohomology interface is
  the right Mathlib-aligned shape; do NOT absorb effort into bridging it
  to `Sheaf.H` (which cannot carry the `Module k` rank-equality anyway).

The variance flag carried across iter-107/108/109 should be cleared by the
plan agent on the basis of this verdict: the route is *not* a "discover-then-
accrete" L1846/L1120 anti-pattern risk because the closure is structurally
infeasible at this point in Mathlib's evolution. The honest move is the
named-gap deferral now, not opening a prover lane in iter-111+.
