# Analogy: 01I8 — `[IsQuasicoherent F] → IsIso F.fromTildeΓ` route selection

## Mode
api-alignment

## Slug
o1i8route

## Iteration
031

## Question
For `F : (Spec R).Modules`, the project needs `[IsQuasicoherent F] → IsIso F.fromTildeΓ`
(equivalently `F ∈ essImage (tilde.functor R)`), the last input to upgrade
`qcoh_iso_tilde_sections` to its unconditional quasi-coherent form (Stacks 01I8). Pick the
Mathlib-aligned route, name the first atomic sub-lemma, flag genuinely missing API — or find a
Mathlib shortcut the prover's grep missed.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/QcohTildeSections.lean:62-133` — conditional structure theorem
  + the ready-to-consume `isIso_fromTildeΓ_of_genSections` (two GLOBAL `GeneratingSections`
  → `Presentation` → Mathlib's `isIso_fromTildeΓ_of_presentation`).
- `AlgebraicJacobian/Cohomology/QcohTildeSections.lean:135-180` — the Handoff prose decomposing
  the gap into steps (1) global generation, (2) kernel qcoh, (3) feed to genSections.

## Shortcut check (ranked item 1) — NEGATIVE
There is **no** `[IsQuasicoherent F] → IsIso F.fromTildeΓ` / `→ essImage tilde` /
`QCoh(Spec R) ≃ Mod R` in Mathlib. Verified:
- `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` — the entire `IsQuasicoherent` section
  (lines 344-410) ends at `isIso_fromTildeΓ_of_presentation` (line 398). The only producers of
  `IsIso fromTildeΓ` are: the structure sheaf (352), free sheaves (366), and a **global**
  `Presentation` (398). No qcoh hypothesis anywhere produces it.
- `isIso_fromTildeΓ_iff` (340) reduces the goal to `essImage`, but nothing then connects
  `IsQuasicoherent` to `essImage`.
- `Mathlib/AlgebraicGeometry/QuasiAffine.lean` is about quasi-*affine schemes*, unrelated.
- `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`: the only "glue" is
  `QuasicoherentData.bind` (360) + `IsQuasicoherent.of_coversTop` (377) — these glue *local
  qcoh data into global qcoh* (the existence/closure direction), the **opposite** of what we need
  (global *presentation* out of local data). No abelian-subcategory / kernel-cokernel closure.
- `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean`: `LocalGeneratorsData` (113) exists
  but there is **no** `LocalGeneratorsData → GeneratingSections` globalization lemma.

So 01I8 is genuinely absent from Mathlib and must be built.

## Decisions identified

### Decision: which proof route (G gluing vs P global-generation vs descent)

- **Mathlib idiom**: none — the affine equivalence is not in Mathlib. The closest reusable
  Mathlib anchors are `isIso_fromTildeΓ_of_presentation` (needs a *global* presentation) and the
  faithfully-flat module-descent stub.
- **Route G (module gluing, Stacks `algebra-lemma-glue-modules`)**: REJECTED.
  `grep` confirms **no `Module.GlueData`** anywhere in `RingTheory`/`Algebra`. The only descent
  available, `Mathlib/Algebra/Category/ModuleCat/Descent.lean`, proves *only* that extension of
  scalars along a faithfully flat map is **comonadic** (`comonadicExtendScalars`); the effective
  descent **equivalence** is an explicit `TODO` in that file's header. Route G would require
  building (a) faithfully-flatness of `R → ∏ R_{fᵢ}`, (b) the effective-descent equivalence
  Mathlib has flagged as not-yet-done, and (c) a translation of the sheaf `F` into comonad descent
  data — a categorical-infrastructure build, the largest and riskiest of the three.
- **Route P (global generation, Hartshorne II.5.14-17)**: CHOSEN. Its missing pieces are ordinary
  commutative-algebra / sheaf statements (localization of sections, quasicompact patching, kernel
  locality), each independently provable, and it lands directly on the project's *already-built*
  `isIso_fromTildeΓ_of_genSections`. Crucially, the local→tilde step is **free**: a
  `QuasicoherentData` presentation of `F.over (basicOpen f)` is a presentation on `Spec R_f`, so
  `isIso_fromTildeΓ_of_presentation` already gives `F.over D(f) ≅ tilde Mᵢ` with no new work.
- **Gap**: divergent-and-must-build (NEEDS_MATHLIB_GAP_FILL). Route P minimizes new LOC and
  maximizes reuse of the two Mathlib/project presentation anchors.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — build Route P.

## Route P decomposition (the gap-fill chain)

Reusable anchors (all verified, axiom-clean in Mathlib / project):
- `isIso_fromTildeΓ_of_presentation` (Tilde.lean:398) — global presentation ⟹ IsIso.
- `instance IsLocalizedModule (.powers f) (tilde.toOpen M (basicOpen f)).hom` (Tilde.lean:115) —
  sections of `tilde M` over `D(f)` ARE `M_f` (the localized-sections fact, but only for tilde).
- `IsQuasicoherent.of_coversTop` (Quasicoherent.lean:377) — qcoh is local-to-global on a cover.
- `PrimeSpectrum.compactSpace` (Topology.lean:291), `iSup_basicOpen_eq_top_iff` (Topology.lean:628),
  `isBasis_basic_opens` (Topology.lean:587) — finite standard-cover extraction.
- Project: `isIso_fromTildeΓ_of_genSections` / `free_isQuasicoherent` (QcohTildeSections.lean).

The chain (each a separately-dispatchable lane; first one named below):

- **P0 (FIRST LANE) — finite trivializing standard cover.** Pure topology, no `SheafOfModules`.
  From any open cover refine to a finite family of basic opens, each inside a cover member.
- **P1 — localized sections (Hartshorne 5.14):** for qcoh `F`, `f : R`, the restriction
  `Γ(X,F) → Γ(D(f),F)` is `IsLocalizedModule (.powers f)`. Load-bearing core; proved by covering
  by the P0 basic opens on which `F ≅ tilde Mᵢ` (sections localize via Tilde.lean:115) and
  patching with the sheaf condition over the finite cover. **GENUINE MATHLIB GAP.**
- **P2 — global generation:** each local generator (on `D(fⱼ)`) extends, after multiplying by a
  power of `fⱼ` (P1 surjectivity half), to a global section; finitely many opens (P0) ⟹ a global
  `F.GeneratingSections` σ. **GENUINE MATHLIB GAP** (depends on P1).
- **P3 — kernel is qcoh, then globally generated:** `kernel σ.π` is locally `tilde(ker)` (reduces
  to **`tilde` preserving kernels / exactness** — itself NOT in Mathlib; tilde is only known
  additive + colimit-preserving), hence qcoh by `IsQuasicoherent.of_coversTop`, hence (P2 again)
  globally generated → τ. **GENUINE MATHLIB GAP** (tilde-exactness sub-gap).
- **P4 — assemble:** feed σ, τ to the project's `isIso_fromTildeΓ_of_genSections`. Already built.

## First atomic sub-lemma (ranked item 3)

Dispatch a `mathlib-build` prover at this **pure-topology** brick (no sheaf math, fully
axiom-clean-able from the three cited PrimeSpectrum lemmas), the common prerequisite of P1/P2/P3:

```lean
/-- Refine an open cover of `Spec R` to a FINITE standard (basic-open) subcover, each member
contained in a cover element.  `Spec R` quasicompact + basic opens form a basis + cover ↔ unit
ideal. -/
lemma exists_finite_basicOpen_subcover {ι : Type*} (U : ι → (Spec R).Opens)
    (hU : ⨆ i, U i = ⊤) :
    ∃ (n : ℕ) (f : Fin n → R) (φ : Fin n → ι),
      (∀ j, PrimeSpectrum.basicOpen (f j) ≤ U (φ j)) ∧ Ideal.span (Set.range f) = ⊤
```
Builds on: `PrimeSpectrum.isBasis_basic_opens`, `PrimeSpectrum.compactSpace`
(`IsCompact.elim_finite_subcover` / `CompactSpace`), `PrimeSpectrum.iSup_basicOpen_eq_top_iff`.
The `φ` + `basicOpen (f j) ≤ U (φ j)` clauses are essential: lane two restricts the
`QuasicoherentData` presentation on `U (φ j)` down to `D(f j)` (via `SheafOfModules.over` /
`Presentation.map` along the open immersion), giving `F.over D(f j) ≅ tilde Mⱼ` for free.

## Mathlib API genuinely missing (ranked item 4 — log as a gap chain, not blind sorries)
1. **Localized sections for qcoh** `Γ(D(f),F) = Γ(X,F)_f` (P1). Present only for `tilde M`
   (Tilde.lean:115); absent for general qcoh F.
2. **`tilde` preserves kernels / is exact** (sub-gap of P3). Mathlib has additive +
   colimit-preserving + preserves-cokernels for `tilde.functor`, but no `PreservesFiniteLimits`.
3. **qcoh closed under kernels** (P3) — no abelian/Serre-subcategory structure on qcoh in Mathlib;
   recover the specific case via gap (2) + `IsQuasicoherent.of_coversTop`.
4. **(Route G only, hence avoided)** module gluing `Module.GlueData` / effective faithfully-flat
   descent equivalence — both absent (the latter a Mathlib TODO).

## Recommendation
Build **Route P** (global generation). It is NEEDS_MATHLIB_GAP_FILL but its gaps are standard
lemmas, it reuses both presentation anchors and the project's `isIso_fromTildeΓ_of_genSections`,
and avoids the categorical effective-descent equivalence Mathlib itself has not done. Dispatch
iter-032's first QcohTilde lane at the pure-topology `exists_finite_basicOpen_subcover`, then
sequence P1 → P2 → P3 → P4. Treat P1, tilde-exactness, and kernel-qcoh as an explicit gap-fill
chain with named obligations, not a single blind sorry.
