# Analogy: invertibility hypothesis + trivial self-braiding for the section graded ring

## Mode
api-alignment

## Slug
invertible

## Iteration
011

## Question
Re-signing `sectionsMul_mul_comm` / `tensorPowAdd_comm` to carry an invertibility hypothesis.
(1) Mathlib's canonical idiom for "object invertible under ⊗ in a (symmetric) monoidal category" —
what to thread into `sectionsMul_mul_comm (L : X.Modules) [?]`? (2) Is there a Mathlib result that an
invertible object has `β_{L,L} = 𝟙` (FALSE in general — super vector spaces — so must use concrete
structure of sheaves of modules)? (3) Confirm general object = `DirectSum.GSemiring`, commutative
upgrade `DirectSum.GCommSemiring` carries invertibility.

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:2531` — `sectionsMul_mul_comm` (currently `sorry`, FALSE for general `L`).
- `:2305` `tensorBraiding_hom_sectionsMul` (PROVEN: braiding at ⊤ is the swap `a⊗ₜb ↦ b⊗ₜa`).
- `:173` `tensorBraiding F G := sheafification.mapIso (presheaf braiding)`; presheaf braiding at open `U` is `TensorProduct.comm (𝒪_X(U)) (F(U)) (G(U))`.
- `:2079` `tensorPowAdd` (μ comparison family).
- `analogies/snap-gcomm.md` — established GSemiring/GCommSemiring assembly mirroring `TensorPower.Basic`.

## Decisions identified

### Decision 1: invertibility predicate to thread into `(L : X.Modules) [?]`
- **Mathlib idiom — categorical level (X.Modules)**: NONE. There is **no** typeclass for "invertible
  object in a (symmetric) monoidal category" in Mathlib. The only categorical handle is *bare data*
  `h : m ⊗ n ≅ 𝟙_` (cf. `CategoryTheory.unitOfTensorIsoUnit`, `Mathlib.CategoryTheory.Monoidal.End`,
  which takes `(h : m ⊗ n ≅ tensorUnit)` as an explicit hypothesis — no class). No Picard-groupoid /
  `Pic` of a general monoidal category, no `AlgebraicGeometry` invertible-sheaf / locally-free-rank-1
  predicate (searched: only `Module.Invertible` (affine) and topological `VectorBundle` exist).
- **Mathlib idiom — affine level (single ring)**: `Module.Invertible R M : Prop`
  (`Mathlib.RingTheory.PicardGroup`), field `bijective : Function.Bijective (contractLeft R M)`
  (evaluation `M ⊗ M* → R` bijective ⇔ finite projective rank 1). Packaged into `CommRing.Pic R`
  (the Picard group), `CommRing.Pic.mk`, `CommRing.Pic.inv_eq_dual`. Implies `Module.Finite` +
  `Module.Projective`. This is the **affine/local** notion — over ONE `CommRing`, not a sheaf over a
  scheme. NOT directly threadable into `(L : X.Modules)` (different categorical level).
- **CRITICAL constraint (couples to Decision 2)**: pure categorical tensor-invertibility is
  **insufficient** to give `β_{L,L}=𝟙` (super vector spaces: odd line is ⊗-invertible yet `β=−1`).
  So the threaded hypothesis MUST encode more than "has a tensor inverse" — it must encode enough of
  the concrete sheaf-of-modules structure to kill the sign.
- **Project's path**: thread a project-local hypothesis. Two viable layers:
  - (weakest sufficient) the iso-level equation `tensorBraiding L L = Iso.refl (tensorObj L L)`
    (≡ `β_{L,L}=𝟙`). Everything downstream (`tensorPowAdd_comm`, `sectionsMul_mul_comm`) follows from
    this single fact via the already-proven `tensorBraiding_hom_sectionsMul` — no `Module.Invertible`
    needed at all. Cleanest to thread; honest about exactly what is used.
  - (geometric, implies the above) a project-local `class IsInvertible (L : X.Modules)` = "locally
    free of rank 1" (a trivializing open cover with `L|_{Uᵢ} ≅ 𝒪_{Uᵢ}`), the standard invertible-sheaf
    def (Stacks 01CR). This DISCHARGES the iso-level equation via a local check + Decision 2's lemma.
- **Gap**: divergent — Mathlib has no idiom at this categorical level. `Module.Invertible` is the
  affine shadow, reusable only locally (on trivializing opens), not as the `(L : X.Modules)` hypothesis.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. Build a project-local predicate. Recommend threading the
  geometric `IsInvertible` (locally-free-rank-1) class; optionally expose the iso-level
  `tensorBraiding L L = Iso.refl` as the immediate lemma it yields.

### Decision 2: Mathlib path to `β_{L,L} = 𝟙` for an invertible sheaf
- **Mathlib idiom (DECISIVE)**: `Module.Invertible.tensorProductComm_eq_refl`
  (`Mathlib.RingTheory.PicardGroup`):
  `∀ (R) (M) [CommRing R] [AddCommGroup M] [Module R M] [Module.Invertible R M],
    TensorProduct.comm R M M = LinearEquiv.refl R (M ⊗[R] M)`.
  This is **exactly** `β_{M,M}=𝟙` at the module level — the swap on `M ⊗ M` is the identity for an
  invertible module. It uses the CONCRETE structure (the literal swap `TensorProduct.comm`), precisely
  as the directive demands — NOT abstract monoidal invertibility (which would be false: super VS).
  Type constraints (`CommRing`, `AddCommGroup`) match the project's `𝒪_X(U)` (CommRing) and `L(U)`
  (AddCommGroup) exactly.
- **Why abstract invertibility is not enough**: confirmed — Mathlib has no abstract
  "invertible-object ⟹ β=𝟙" lemma (none exists; it is false). The result is specifically about
  `Module.Invertible` + the swap `TensorProduct.comm`.
- **Sheaf-level wrapper (the gap)**: the project's `tensorBraiding L L` is
  `sheafification.mapIso` of the presheaf braiding, whose component at open `U` is
  `TensorProduct.comm (𝒪_X(U)) (L(U)) (L(U))`. To get `tensorBraiding L L = Iso.refl`:
  (a) equality of sheaf morphisms is LOCAL — check on a trivializing cover `{Uᵢ}` of the
      `IsInvertible` hypothesis; (b) on each `Uᵢ`, `L(Uᵢ)` is free of rank 1 over `𝒪_X(Uᵢ)`, hence
      `Module.Invertible (𝒪_X(Uᵢ)) (L(Uᵢ))`, so the component is `refl` by `tensorProductComm_eq_refl`;
      (c) descend through `sheafification.mapIso`. Then evaluate at `⊤`: even though `Γ(L)` need NOT be
      `Module.Invertible (Γ(𝒪_X))` (global sections of a line bundle are not an invertible module in
      general), the *sheaf-morphism* identity gives the section-level swap-triviality at `⊤` for free.
  ⚠ Do NOT try to apply `tensorProductComm_eq_refl` at `⊤` directly — `Module.Invertible (Γ𝒪) (ΓL)`
  is generally FALSE. The local-to-global step is mandatory.
- **Gap**: divergent-with-cost. Algebraic kernel present in Mathlib; sheaf wrapper is project-local
  (cheap given existing `tensorBraiding`=sheafification-of-presheaf-comm machinery + a trivializing
  cover from `IsInvertible`).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for the sheaf-level wrapper; the hard core
  (`Module.Invertible.tensorProductComm_eq_refl`) is ALIGN_WITH_MATHLIB — reuse it verbatim on
  trivializing opens.

### Decision 3: ring-structure shape (general vs invertible)
- **Mathlib idiom**: `Mathlib.LinearAlgebra.TensorPower.Basic` — `⨂[R]^n M` builds
  `GradedMonoid.GMonoid → DirectSum.GSemiring` (assoc + units, NO comm) on `fun n => ⨂[R]^n M`,
  with `DirectSum.GCommSemiring` reserved for the commutative case. Already documented in
  `analogies/snap-gcomm.md`. The free tensor algebra is the non-commutative general object; comm is
  an upgrade. No Mathlib idiom packages "section ring of an invertible sheaf" (none exists; build it).
- **Project's path**: general object `DirectSum.GSemiring (sectionDeg L)` (assoc via
  `sectionsMul_mul_assoc`, TRUE for all `L`); `DirectSum.GCommSemiring` carrying invertibility
  (`mul_comm` via `sectionsMul_mul_comm`, needs `[IsInvertible L]`).
- **Gap**: identical to the `TensorPower.Basic` precedent.
- **Verdict**: ALIGN_WITH_MATHLIB. Exactly correct: GSemiring general, GCommSemiring invertible-only.

## Recommendation
Thread a **project-local** invertibility hypothesis — Mathlib has no categorical invertible-object
typeclass and no scheme-level invertible-sheaf predicate (`Module.Invertible`/`CommRing.Pic` are
affine-only). Recommended shape: a `class IsInvertible (L : X.Modules) : Prop` = locally free of rank
1 (trivializing cover `L|_{Uᵢ} ≅ 𝒪_{Uᵢ}`, Stacks 01CR). Re-sign
`sectionsMul_mul_comm (L : X.Modules) [IsInvertible L] …` and
`sectionGradedRing_gcommSemiring … [IsInvertible L]`; keep `sectionGradedRing_gsemiring` (assoc+units)
hypothesis-free. The proof of `mul_comm` factors through ONE iso-level lemma
`tensorBraiding L L = Iso.refl _` (= `β_{L,L}=𝟙`), discharged by: locality of sheaf-morphism equality
→ reduce to trivializing opens → `Module.Invertible.tensorProductComm_eq_refl` (Mathlib, reused
verbatim; `L(Uᵢ)` free rank 1 ⟹ `Module.Invertible`) → descend through `sheafification.mapIso` → eval
at `⊤` via existing `tensorBraiding_hom_sectionsMul`. Do NOT attempt `Module.Invertible (Γ𝒪) (ΓL)` at
`⊤` — false in general; the local-to-global detour is required. GSemiring/GCommSemiring split matches
`TensorPower.Basic` exactly (snap-gcomm).
