# Analogy: stalk of relative module tensor ≅ tensor of stalks over the stalk ring (d.2)

## Mode
cross-domain-inspiration

## Slug
ts-d2-215

## Iteration
215

## Structural problem (abstracted)

A filtered-colimit functor commutes with a *relative* tensor product over a *varying* base
ring. Concretely: for a filtered diagram of rings `R : C ⥤ RingCat`, two diagrams of modules
`F, M : C ⥤ Ab` that are pointwise `R(i)`-modules, and the diagram `i ↦ F(i) ⊗_{R(i)} M(i)`,
one wants a natural iso `colim_i (F(i) ⊗_{R(i)} M(i)) ≅ (colim F) ⊗_{colim R} (colim M)` of
modules over the colimit ring `colim R`. Specialised to `C = (OpenNhds x)ᵒᵖ` this is the stalk
statement `(F ⊗ᵖ_R M)_x ≅ F_x ⊗_{R_x} M_x`, and downstream `(F ◁ g)_x ≅ lTensor F_x (g_x)`.
This is "the stalk functor (a filtered colimit) is strong-monoidal for the relative tensor."

## Failed approaches (from directive)
- Section-level injectivity alone (needs Tor₁ / flatness) — dead end.
- `MonoidalClosed (PresheafOfModules R)` — verified absent.
- Fixed-base `Sites/Monoidal.lean` / `Sites/Point/IsMonoidalW.lean` *instances* — template only;
  they need a *fixed* monoidal-closed `A`, not modules over a varying ring.

## Analogues found

Ranked by porting cost (lowest first).

### Analogue: `Mathlib/Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean` (Joël Riou)

- **Domain**: category theory / module-presheaf colimits (same project area — the load-bearing one).
- **Same structural problem there**: builds the colimit of a presheaf of modules over a *cofiltered*
  `C` as a module over the colimit ring `cR.pt`. `ModuleColimit hcR hcM` (L68) is the type;
  `coconeSMul` (L79) and `smul_eq` (L103) define/characterise the scalar action by descending the
  scalar multiplication through the **`AddCommGrp` `IsColimit.tensor` of the underlying colimit
  cocones** (`(isColimitOfPreserves (forget _) hcR).tensor (isColimitOfPreserves (forget _) hcM)`).
  Provides joint surjectivity in 1/2/3 variables: `ιM_jointly_surjective` (L109),
  `jointly_surjective₂` (L147), `jointly_surjective₃` (L159), `jointly_surjective₃'` (L172), plus the
  universal property `homEquiv` (L240) realising `colimitFunctor ⊣ constFunctor`.
- **Technique**: define a map *out of* the colimit module by the universal property (`homEquiv` /
  joint surjectivity), then verify equalities/iso-ness by reducing to a finite stage via
  joint-surjectivity and the explicit `smul_eq`. The varying-ring scalar action is already carried
  by the same underlying `IsColimit.tensor` cocone the comparison map for d.2 would reuse.
- **Mapping to project**: d.2's comparison `δ : (F ⊗ᵖ M)_x → F_x ⊗_{R_x} M_x` is built exactly as the
  scalar action is: take the `AddCommGrp` colimit cocones of `F.presheaf`, `M.presheaf`, form
  `(forget-colim F).tensor (forget-colim M)`, and the bilinear `germ ⊗ germ` descends. Iso-ness:
  surjectivity from `jointly_surjective₂`; injectivity by the filtered-colimit relation lemma. The
  file's own TODO (header, ~L22): **"Define fiber functors on categories of (pre)sheaves of modules"**
  and **"Refactor Stalk.lean so that it uses this more general construction"** — i.e. d.2 *is* the
  named, intended-but-absent next step.
- **Porting cost**: medium. The colimit-with-scalar plumbing (the usual swamp) is pre-built; the new
  work is the comparison map + its iso proof, plus reconciling the stalk's `(OpenNhds x)ᵒᵖ` colimit
  (Stalk.lean uses `colimit.isColimit`) with `ModuleColimit`'s arbitrary-cocone API so
  `jointly_surjective₂/₃` apply.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib/CategoryTheory/Sites/Point/Monoidal.lean` (Joël Riou)

- **Domain**: category theory / sheaf-point fiber functors (the exact proof template, fixed base).
- **Same structural problem there**: the presheaf fiber functor `Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A`
  (a filtered colimit) is strong monoidal when `A` is a fixed monoidal category whose tensor commutes
  with filtered colimits.
- **Technique**: `OplaxMonoidal` structure with `δ` defined by the fiber's colimit universal property
  (`presheafFiberDesc`, L38-39); then `δ` is shown **iso** by exhibiting the target as a colimit via
  `(Φ.isColimitPresheafFiberCocone P₁).tensor (Φ.isColimitPresheafFiberCocone P₂)`
  (`IsColimit.tensor`, `Monoidal/Limits/Colimits.lean:73`) and `coconePointUniqueUpToIso` (L95-98);
  upgrade to `Monoidal` by `.ofOplaxMonoidal` (L100). Hypotheses: `PreservesFilteredColimitsOfSize
  (tensorLeft X)` / `(tensorRight X)` for the **fixed** `A` (L79-80).
- **Mapping to project**: this is the *shape* to follow (define `δ` by universal property; prove iso
  via "tensor of colimit cocones is a colimit cocone"). **Why it does not port verbatim**: the
  relative tensor `F(U) ⊗_{R(U)} M(U)` is not the tensor of one fixed monoidal category — the cocones
  to be `IsColimit.tensor`-ed live in different `ModuleCat (R(U))`. The portable move is to apply
  `IsColimit.tensor` to the **underlying `AddCommGrp`** cocones (which `ColimitFunctor.lean` already
  does for the scalar action) and then check the comparison is `R_x`-linear — i.e. fuse this template
  with the `ColimitFunctor` analogue above.
- **Porting cost**: medium (as the structural skeleton); the linearity/iso bookkeeping is the cost.
- **Verdict**: ANALOGUE_FOUND (skeleton) / PARTIAL_ANALOGUE (the `IsColimit.tensor`-on-relative-tensor
  step is the one that genuinely doesn't transfer and must be replaced by the AddCommGrp descent).

### Analogue: `Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean` (Jujian Zhang)

- **Domain**: commutative algebra (fixed-ring direct limits).
- **Same structural problem there**: `directLimitLeft` (L78): `DirectLimit G f ⊗[R] M ≃ₗ[R]
  DirectLimit (G · ⊗[R] M) (f ▷ M)` — tensor commutes with a directed colimit, over a **fixed**
  `CommSemiring R`. `directLimitRight` (L97) is the right-hand version.
- **Technique**: build both directions explicitly (`toDirectLimit`/`fromDirectLimit`) from
  `Module.DirectLimit.lift` and `TensorProduct.lift`, then `LinearEquiv.ofLinear` with `ext; simp`
  on generators (L78-80). This is the cleanest model of the *element-level* iso proof.
- **Mapping to project**: directly usable only after base-change to the colimit ring (the ring is
  fixed here). The varying-ring case is the gap: `F(U)` is an `R(U)`-module, not an `R_x`-module, so
  `F(U) ⊗_{R_x} (…)` does not type-check without `R_x ⊗_{R(U)} F(U)` base changes diagram-wise. A
  base-change reduction (`AlgebraTensorModule.cancelBaseChange`-style) to `directLimitLeft` is an
  *alternative* assembly, but it spends several change-of-rings lemmas per stage — likely costlier
  than the direct `ColimitFunctor` build.
- **Porting cost**: high (because of the varying-ring base-change overhead).
- **Verdict**: PARTIAL_ANALOGUE.

## Building blocks confirmed present (project's pinned Mathlib, rev b80f227)

- `PresheafOfModules` stalk as `R.stalk x`-module: `ModuleCat/Stalk.lean` instance L165 (RingCat) /
  L190 (CommRingCat), `germ_smul` L200, built on `CategoryTheory.Limits.IsColimit.module` (L123),
  `colimit.smul` (L42), `IsColimit.ι_smul` (L135). Exposes the colimit presentation + germ-smul law.
- Relative sectionwise tensor: `Presheaf/Monoidal.lean` `tensorObj` L62, `tensorObj_obj`
  ((F⊗M)(X) = F(X) ⊗_{R(X)} M(X) by **rfl**) L169.
- **`PreservesColimitsOfSize (tensorLeft F)` / `(tensorRight F)` for the relative tensor**:
  `Presheaf/Monoidal.lean` L237 / L243 (proved sectionwise via `evaluation`). The analogue of the
  fixed-base template's preservation hypothesis — already discharged for the varying-ring presheaf.
- `IsColimit.tensor` (`CategoryTheory/Monoidal/Limits/Colimits.lean:73`, needs `PreservesColimit₂` +
  `IsSifted J`; filtered ⟹ sifted via `IsFiltered.isSifted`) and `Cocone.tensor` (L65).
- Fixed-ring colimit-tensor `directLimitLeft`/`Right` (`TensorProduct/DirectLimit.lean` L78/L97).

## Genuinely absent (the gap)

- No comparison map `(F ⊗ᵖ M)_x → F_x ⊗_{R_x} M_x` and no proof it is iso. This is Joël Riou's
  written TODO in `ColimitFunctor.lean`. No varying-ring colimit-tensor lemma exists (only
  fixed-ring `directLimitLeft`). `Module.DirectLimit` is fixed-ring.

## Buildability verdict: (b) buildable, requires a substantial new sub-construction

Not (a) routine: there is no single lemma to instantiate; the comparison map and its iso proof must
be authored, and the varying ring blocks verbatim reuse of both `directLimitLeft` (fixed ring) and
`IsColimit.tensor` on the relative tensor. Not (c) blocked: every load-bearing ingredient
(`ModuleColimit` + `jointly_surjective₂/₃` + `smul_eq` + `homEquiv`; `PreservesColimits (tensorLeft
F)`; `IsColimit.tensor`; the `germ_smul` law) is present and recent. The named sub-construction is
**"the relative-tensor comparison map on `ModuleColimit` / the module stalk, plus its iso proof"** =
the varying-ring analogue of `presheafFiber.Monoidal`. The ~150–250 LOC estimate is realistic, risk
MODERATE (not a swamp), because the colimit-scalar plumbing that would otherwise be the swamp is
pre-built in `ColimitFunctor.lean`. Concrete first sub-task: reconcile the stalk's `(OpenNhds x)ᵒᵖ`
colimit with `ColimitFunctor.ModuleColimit` so `jointly_surjective₂/₃` apply (this is Riou's
"refactor Stalk.lean" TODO, done project-locally).

**One-iter-gate tension (for the planner's escalate decision):** d.2 is a new ~150–250 LOC monoidal
construction with a fiddly linear iso proof; it will realistically NOT close `…whiskerLeft_of_W`
axiom-clean within a single prover iter. The progress-critic's FINAL gate (sorry must decrease this
iter, no soft-land) is therefore in direct tension with d.2's true size. The feasibility is real;
the schedule is not one iter.

## Top suggestion

Build d.2 against `ColimitFunctor.lean`'s `ModuleColimit`, NOT raw `Stalk.lean`. Read
`Sites/Point/Monoidal.lean:35-100` for the skeleton (define `δ` by the colimit universal property;
prove iso via tensor-of-colimit-cocones), but replace its `IsColimit.tensor`-on-the-monoidal-tensor
step with `IsColimit.tensor` on the **underlying `AddCommGrp` cocones** — exactly the cocone
`ColimitFunctor.lean` already forms in `coconeSMul`/`jointly_surjective₂` — then prove the resulting
comparison is `R_x`-linear and bijective using `jointly_surjective₂` (surjectivity) + a filtered
relation lemma (injectivity). First project file to touch: `AlgebraicJacobian/Picard/
TensorObjSubstrate.lean`, extending the existing `stalkLinearMap` (L535) layer with the bilinear
`stalkTensorComparison` and `stalkLinearMap g x = lTensor F_x (g_x)` identification feeding
`isLocallyInjective_whiskerLeft_of_W` (L411).
