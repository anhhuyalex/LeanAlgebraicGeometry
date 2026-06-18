# Project Progress

## Current Stage

prover  (GR-seed cone DELIVERED iter-001; SNAP-S0 graded-section residue ACTIVE iter-006)

## Stages
- [x] init
- [x] autoformalize
- [ ] prover — GR-seed cone delivered (iter-001). SNAP-S0 residue (9 sorries in
      `SectionGradedRing.lean`) now ACTIVE (iter-006, user-directed). χ-blocked nodes remain
      DEFERRED (need a cohomology engine absent here).
- [ ] polish — after SNAP residue closes.

## End-state overview

**ACHIEVED (iter-001):** the goal seed `AlgebraicGeometry.Grassmannian.represents` is sorry-free
and axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`). The
GR-quot representability cone (Nitsure §1/§5; FGA Explained Ch. 5) is delivered and merge-ready.

**ACTIVE (iter-006):** the SNAP-S0 H⁰ section graded ring `Γ_*(X,L)=⊕_{n≥0}Γ(X,L^{⊗n})`
(Stacks 01CV) residue. Foundations (`tensorPow`, `sectionsMul`, `tensorObjAssoc`, `tensorPowAdd`)
already proved axiom-clean in-leg. Strategy-critic confirmed (iter-006) the four coherence laws are
sound graded-monoid laws and that closing them only removes `sorryAx` — it cannot add a `\uses`
edge into the delivered seed cone (disjointness preserved).

## Current Objectives

1. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — Fill the 9 SNAP-S0 residue sorries, in
   dependency order:
   - `sectionsCast` (L1841) — `def`. Image under `Γ(X,−)` of the canonical `L^{⊗i}≅L^{⊗j}` along
     `h:i=j` via `tensorPow`. Refl-case collapses via `eqToIso_refl`+`map_id`.
   - `sectionsCast_refl` (L1847) — `= LinearEquiv.refl` (mirrors `TensorPower.cast_refl`).
   - `gradedMonoid_eq_of_cast` (L1854) — repackage a transport-mediated component equality into an
     equality of dependent pairs (mirrors Mathlib `gradedMonoid_eq_of_cast`).
   - `GradedMonoid.GMul (sectionDeg L)` instance (L1861) — `mul a b =
     (tensorPowAdd L i j).hom.val.app (op ⊤) ∘ sectionsMul (tensorPow L i) (tensorPow L j)` on `a⊗ₜb`.
   - `GradedMonoid.GOne (sectionDeg L)` instance (L1866) — image of `1∈Γ(X,𝒪_X)` in `sectionDeg L 0`.
   - `sectionsMul_one_mul` (L1872), `sectionsMul_mul_one` (L1880), `sectionsMul_mul_assoc` (L1887),
     `sectionsMul_mul_comm` (L1897) — the four `lem:sectionMul_coherent` component laws, mirroring
     `TensorPower.{one_mul,mul_one,mul_assoc,mul_comm}`. Reduce to the presheaf level where eval at
     the top open `op ⊤` is STRICT monoidal; ride the sheafification unit η through
     `tensorObjAssoc`/`tensorObjUnitIso`/`tensorPowAdd`. Pass each through `gradedMonoid_eq_of_cast`.

   Blueprint: `chapters/Picard_SectionGradedRing.tex` — `def:sectionsCast`, `lem:sectionsCast_refl`,
   `lem:gradedMonoid_eq_of_cast`, `def:sectionGradedGMul`, `def:sectionGradedGOne`,
   `lem:sectionMul_coherent` (gate-cleared complete+correct, iter-006).
   References (standing directive — reference-driven proofs):
   - `Γ_*(X,L)` graded ring: Stacks **01CV** (`references/stacks-modules.tex`, §17.25, line 4269);
     tensor product `F⊗G` & bilinearity: Stacks **01CA** (§17.16, line 2271).
   - Cast/coherence idiom: Mathlib `Mathlib.LinearAlgebra.TensorPower.Basic`
     (`TensorPower.cast`, `cast_refl`, `gradedMonoid_eq_of_cast`, `one_mul`, `mul_one`, `mul_assoc`,
     `mul_comm`) — the section-level analogues being formalized here.

   Hazard (ARCHON_MEMORY): value-`ModuleCat` diamond — never positional `rw`/`simp`/`erw`; use
   term-mode (`.trans`/`congrArg`/applied `map_smul`) + `change`-to-nested-application; after a `rw`
   yielding syntactic `X = X`, append explicit `rfl`. `sectionMul_coherent` = FOUR cast-mediated
   component Eqs, NOT one `GradedMonoid` Eq/HEq. Merge discipline: do NOT rename kept decls/labels;
   reuse byte-identical sibling signatures so the `FBC-B_SNAP-chain` merge is a dedup.
   [prover-mode: prove]

## Deferred (NOT objectives this iter)

- **χ-blocked (`QuotScheme.lean`, 4 sorries):** `hilbertPolynomial` (χ-semantic
  `Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`), `QuotFunctor`, `Grassmannian` functor. Need a higher-cohomology engine
  this i=0 leg lacks; filled from the cohomology leg at merge. NEVER fabricate an H⁰ `Φ_s` under the
  χ label. (Genuine mathematical gap — no in-leg informal proof route; not blind-formalizable.)
- **`RelativeSpec.lean`:** Route-A (relative Picard) sibling chapter, no phase in this leg's
  STRATEGY; its real sorries are gated on `structureMorphism` being a typed sorry. Out of scope.
- **Out-of-cone debt:** weak `Scheme.Grassmannian.representable` skeleton; the goal does not rely on it.

## Blueprint health (non-gating, deferred to merge-back)

blueprint-reviewer (iter-006) flagged dangling refs in DEFERRED chapters: `Cohomology_FlatBaseChange.tex`
(15 refs + covers 2 non-existent files), `QuotScheme.tex` (13 crefs), `GlueDescent.tex` (2 sublemma
wire-up blocks). All target labels outside the active SNAP cone — extraction artifacts that resolve at
merge-back. Do NOT edit (byte-identical-to-parent discipline). The active chapter is clean.

## Standing notes

- **Prover model:** `opus`.
- **Cold-build validation:** `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP hides
  `(kernel) deterministic timeout`); do NOT add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **Merge-back discipline (load-bearing):** never rename kept decls/labels/paths; never add `\leanok`
  by hand. Lean names byte-identical to parent + sibling so SNAP merge is a dedup.
