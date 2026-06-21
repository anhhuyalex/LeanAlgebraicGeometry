# Analogy: stalk of a sub-presheaf-of-modules of a constant module sheaf (= directed union of section submodules)

## Mode
api-alignment

## Slug
stalk-colimit

## Iteration
016

## Question
Compute `stalk (carrierSheaf D).val P.point ≅ ModuleCat.of kbar (orderAtPSubmodule D P)`,
where `carrierSheaf D` is a `ModuleCat kbar`-valued sheaf on `C.left` whose sections
`Γ(U)` are `kbar`-submodules of the fixed module `K(C) = C.left.functionField` and whose
restriction maps are `Submodule.inclusion` (the identity on `K(C)`), the zero map only at `⊥`.
Is there a canonical Mathlib idiom this should ALIGN with rather than a 200–400 LOC raw-colimit build?

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/OcOfD.lean:412` — `sheafOf.carrierPresheaf`: `obj U = ModuleCat.of kbar ↥(carrierSubmoduleSheaf D U)`, `map = Submodule.inclusion` (away from `⊥`), `0` at `⊥`.
- `…OcOfD.lean:893` — `sheafOf.carrierSheaf` (bundled `Sheaf`).
- `…OcOfD.lean:1040` — `sheafOf.orderAtPSubmodule`: `{f | f = 0 ∨ -(D P) ≤ ord_P f}` ⊆ `K(C)`.
- `…OcOfD.lean:1139` — `sheafOf.carrierSheaf_stalk_eq` — **STUBBED `sorry`**, the binding leaf.

## Decisions identified

### Decision: how to express / compute the stalk

- **Mathlib idiom**: stalk = filtered colimit over `OpenNhds`, manipulated through the **germ API**, not raw colimit terms.
  - `TopCat.Presheaf.stalk ℱ x` = `colimit ((OpenNhds.inclusion x).op ⋙ ℱ)` — `Mathlib.Topology.Sheaves.Stalks`. (verified hover)
  - `TopCat.Presheaf.germ`, and the three workhorses:
    - `TopCat.Presheaf.germ_exist (F) (t : F.stalk x) : ∃ U m s, F.germ U x m s = t` — every stalk elt is a germ of a section.
    - `TopCat.Presheaf.germ_eq (F) … (h : germ U … s = germ V … t) : ∃ W hxW iU iV, F.map iU.op s = F.map iV.op t` — equal germs ⇒ agree on a smaller nbhd.
    - `TopCat.Presheaf.germ_ext` — converse packaging (agree on `W` ⇒ equal germ).
    - `TopCat.Presheaf.section_ext (F : Sheaf …) (s t) (h : ∀ x hx, germ … s = germ … t) : s = t` — separatedness (sheaf germ-injectivity). All in `Mathlib.Topology.Sheaves.Stalks`. (verified)
  - Functorial stalk maps (if a presheaf morphism is available): `TopCat.Presheaf.stalkFunctor C x`, `stalkFunctor_map_germ`. (verified)
- **Project's current path**: typed `sorry`; the plan flagged a feared "200–400 LOC raw-colimit build".
- **Gap**: **divergent-with-cost iff built raw**; identical-to-idiom if built via germ API. There is **no** Mathlib lemma that computes the stalk of a sheaf-of-submodules — that part is genuinely new — but the *method* must reuse the germ API; a hand-rolled quotient-of-`Σ`/raw `colimit.ι` manipulation would duplicate `Stalks.lean`.
- **Cost of divergence (if raw)**: re-deriving `germ_exist`/`germ_eq` by hand (~100+ LOC duplicating Mathlib), brittle `colimit` defeq juggling, no reuse in the sibling `cokernel_stalk_at_iso_kbar` / `cokernel_skyscraper_hom_isIso` leaves (which also need stalk maps).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the *statement* (no submodule-stalk lemma in Mathlib) **+ ALIGN_WITH_MATHLIB** for the *method* (germ API + `ConcreteCategory.isIso_iff_bijective`).

### Decision: realise the directed colimit of submodules as a supremum

- **Mathlib idiom**: `Submodule.mem_iSup_of_directed (S : ι → Submodule R M) (H : Directed (· ≤ ·) S) {x} : x ∈ iSup S ↔ ∃ i, x ∈ S i` — `Mathlib.LinearAlgebra.Span.Defs`. (verified)
  The family `U ↦ carrierSubmoduleSheaf D U` over `(OpenNhds P.point)` is directed under `≤` (any `U,V ∋ P.point` ⇒ `U⊓V ∋ P.point`, with `Γ(U),Γ(V) ≤ Γ(U⊓V)`; index nonempty via `⊤`). So `⨆_{U∋P.point} Γ(U)` is the genuine union inside `K(C)`.
- **Project's current path**: none yet.
- **Gap**: identical — this IS Mathlib's directed-supremum idiom.
- **Verdict**: **ALIGN_WITH_MATHLIB**.

### Decision: "subsheaf of a constant module sheaf" — does Mathlib already compute it?

- **Mathlib idiom**: `CategoryTheory.Subpresheaf (F : C ⥤ Type w)` — `Mathlib.CategoryTheory.Subfunctor.Basic`. **Type-valued only.** No `ModuleCat`-valued subsheaf-of-constant-sheaf, and no stalk computation for it. `TopCat.Presheaf.stalkToFiber` exists only for `Type v` sheafification. (verified — `Subpresheaf` is `F : C ⥤ Type w`)
- **Project's current path**: bespoke `ModuleCat kbar` presheaf-of-submodules.
- **Gap**: divergent-and-justified — the Type-valued `Subpresheaf` cannot carry the `kbar`-module structure the downstream `HModule`/`Ext` ladder needs.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (justified parallel; do NOT try to route through `CategoryTheory.Subpresheaf`).

## Recommendation

Build the iso as a **bijective colimit-descent**, reusing the germ API; do not hand-roll the colimit.

Factor into two leaves (each ~80 LOC), so the reusable half is available to the sibling cokernel leaves:

**(A) Reusable: `stalk ≅ ⨆ section-submodules` for an inclusion-restriction presheaf.**
1. Containment legs: for `U ∋ P.point`, `carrierSubmoduleSheaf D U ≤ orderAtPSubmodule D P` — take `Q = P` in the order constraint (`P.point ∈ U`). Use `Submodule.inclusion` for `ℓ_U`.
2. Forward `φ : stalk … ⟶ ModuleCat.of kbar (orderAtPSubmodule D P)` via `Limits.colimit.desc` of the cocone whose legs are `ℓ_U` (compatible because every map is an inclusion inside `K(C)`); equivalently `φ ∘ germ U _ _ = ℓ_U`.
3. **Injective**: post-compose with `Submodule.subtype` (orderAtP ↪ K(C)); `Submodule.subtype_comp_inclusion` collapses `φ`-then-coerce to "germ ↦ underlying `K(C)` element". `germ_exist` writes stalk elts as `germ U s`; equal underlying ⇒ `germ_eq`/`germ_ext` (restrictions are injective `Submodule.inclusion`, `Submodule.inclusion_injective`, `Submodule.coe_inclusion`) ⇒ equal germ. (`section_ext` is the sheaf-level shortcut.)
4. **Surjective**: given `f ∈ orderAtPSubmodule D P`, the **finite-poles** fact gives `U ∋ P.point` with `f ∈ carrierSubmoduleSheaf D U` (shrink `U` off the finitely many `Q ≠ P` where `D`'s order constraint fails — reuse the project's finite-support machinery, cf. memory `weildivisor-finite-order-affine`/`finite_order_support_affine`). Then `φ (germ U ⟨f,_⟩) = f`.
5. Conclude `IsIso φ` from bijectivity: `CategoryTheory.ConcreteCategory.isIso_iff_bijective` + `ModuleCat.instReflectsIsomorphismsForget` (+ `ModuleCat.hom_bijective` to move between hom/underlying); take `asIso φ`. (Alternative packaging: assemble a `LinearEquiv` and use `LinearEquiv.toModuleIso` — same work, both verified.)

**(B) Geometric: `⨆_{U∋P.point} carrierSubmoduleSheaf D U = orderAtPSubmodule D P`** via `Submodule.mem_iSup_of_directed` (≤ from step 1's `iSup_le`; ≥ from step 4's finite-poles). This is the mathematical heart; everything else is plumbing.

Net: the feared 200–400 LOC shrinks to ~120–180, of which only the finite-poles surjectivity carries real content (not Mathlib duplication). **Flag for the planner: forbid a raw `colimit.ι`/quotient build; mandate the germ API + `isIso_iff_bijective`.**
