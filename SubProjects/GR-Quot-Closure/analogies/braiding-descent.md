# Analogy: local-to-global descent for `β_{L,L} = 𝟙` of an invertible sheaf

## Mode
api-alignment

## Slug
braiding-descent

## Iteration
027

## Question
The planned proof of `tensorBraiding_self_eq_id_of_isInvertible (L) [IsInvertible L] :
tensorBraiding L L = Iso.refl (tensorObj L L)` is local-to-global: on a trivializing cover `L` is
free rank 1, presheaf braiding = `TensorProduct.comm` = id (invertible module), descend through
sheafification — NOT checked at `⊤`. Find Mathlib's idiom for: (1) obtain the trivializing cover
from `IsInvertible L`; (2) prove equality of sheaf-of-module morphisms by a LOCAL check on a cover;
(3) the cleanest overall route to `β_{L,L}=𝟙` / any existing "braiding trivial on invertible" result.

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:137` — `class IsInvertible (L : X.Modules)` =
  **categorical ∃-inverse** (`∃ N, Nonempty (tensorObj L N ≅ unitModule X)`). NOT "locally free
  rank 1 + stored cover". NOT protected (`archon-protected.yaml` empty) ⇒ re-signable.
- `:187` `tensorBraiding F G := sheafification.mapIso (BraidedCategory.braiding …)` — presheaf
  braiding component at open `U` is `TensorProduct.comm 𝒪(U) (L(U)) (L(U))`.
- `:3429` `tensorBraiding_self_eq_id_of_isInvertible` (sorry; the target).
- `:3464` `sectionsMul_mul_comm` (consumer; factors through the above via `tensorBraiding_hom_sectionsMul`).

## Decisions identified

### Decision 1: obtain the trivializing cover (local freeness rank 1) from `IsInvertible L`
- **Mathlib idiom — scheme level**: NONE. No `AlgebraicGeometry` invertible-sheaf / line-bundle /
  locally-free / `Pic(X)` / "locally ≅ free" predicate in pinned Mathlib. `SheafOfModules.free`,
  `.unit`, `.freeHomEquiv`, `.ιFree` (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`) give the FREE
  sheaf of modules on a site, but there is **no `LocallyFree`/trivializing-cover predicate** and no
  cover-extraction lemma. `Topology.VectorBundle` is normed-field/topological — wrong category.
- **Mathlib idiom — affine/stalk kernel (PRESENT, Stacks 01CR core)**:
  `CommRing.Pic.instSubsingletonOfIsLocalRing (R)[IsLocalRing R] : Subsingleton (Pic R)`,
  `CommRing.Pic.instFreeOfSubsingleton [Module.Invertible R M][Subsingleton (Pic R)] : Module.Free R M`,
  `Module.Invertible.finrank_eq_one`/`rank_eq_one`/`free_iff_linearEquiv` (all
  `Mathlib.RingTheory.PicardGroup`). ⇒ invertible module over a LOCAL ring is free of rank 1.
- **The bridge categorical-∃-inverse → cover is the blocker**: deriving "L(U) free rank 1 on a cover"
  (or "L_x invertible/free on stalks") from `∃ N, L⊗N≅𝒪` is exactly Stacks 01CR and needs, ALL
  ABSENT in pinned Mathlib: (a) module-sheaf stalks `L_x` as `𝒪_{X,x}`-modules; (b) stalk-of-tensor
  `(L⊗N)_x ≅ L_x ⊗ N_x`; (c) descent "invertible on every (local-ring) stalk ⟹ locally free on a
  cover" (Nakayama + finite presentation). The affine kernel above is present, but (a)-(c) are a large
  genuine build (same stalk-infra gap flagged in `analogies/snap-route.md`).
- **Gap**: divergent-and-blocking. The shipped class supplies NO cover; the planned proof CANNOT start.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for the categorical→cover bridge (large). **Recommended fix:
  re-sign `IsInvertible` to carry the trivializing cover as DATA** (the equivalent Stacks-01CR
  definition: a cover `{Uᵢ}` of `X` with isos `L|Uᵢ ≅ 𝒪_X|Uᵢ`, or `≅ unitModule` restricted). No
  instances/consumers exist yet (all gated future work) ⇒ the re-sign is downstream-free. This
  DISSOLVES gap 1; gaps 2–3 then close with present bricks. See [[invertible]] (iter-011 already
  recommended the cover-carrying class; it was NOT adopted — this is the cost).

### Decision 2: prove equality of sheaf-of-module morphisms by a LOCAL check
- **TRAP (do not use alone)**: `AlgebraicGeometry.Scheme.Modules.hom_ext`/`hom_ext_iff`
  (`Mathlib.AlgebraicGeometry.Modules.Sheaf`): `f = g ↔ ∀ U, app f U = app g U`. This is objectwise
  at EVERY open INCLUDING `⊤` — using it directly forces the forbidden `⊤` check (where `Γ(L)` need
  not be invertible). It is the natural-transformation extensionality, NOT a cover-local criterion.
- **Genuine local idiom (PRESENT)**:
  - `TopCat.Sheaf.hom_ext` (`Mathlib.Topology.Sheaves.SheafCondition.Sites`): for `F'` a sheaf and
    `B` a **basis** of opens, `(∀ i, α.app (op (B i)) = β.app (op (B i))) → α = β`. The cover/basis
    morphism check — exactly the planned move, restricted to a trivializing basis.
  - `TopCat.Presheaf.IsSheaf.section_ext` (`Topology.Sheaves.Sheaf`) — sections of a sheaf agreeing
    locally are equal (separatedness, section level).
  - Site level: `CategoryTheory.Sheaf.isSeparated` ⇒ `Presheaf.IsSeparated J F.val`, with
    `Presieve.IsSeparated` / `PreZeroHypercover.ext_of_isSeparatedFor` (sections equal if equal on a
    covering presieve). For `𝒪_X`: `AlgebraicGeometry.Scheme.zero_of_zero_cover`.
- **Bridge cost (project-local)**: the braiding morphisms live in `X.Modules`; to invoke
  `TopCat.Sheaf.hom_ext`/separatedness, pass to the underlying `TopCat.Sheaf AddCommGrp` (or the
  underlying presheaf) and use `Scheme.Modules.hom_ext_iff`'s objectwise reduction combined with
  per-open separatedness over the cover. Cheap-to-medium plumbing; no absent Mathlib brick.
- **Gap**: divergent-with-minor-cost (right idiom exists; the obvious-looking `Scheme.Modules.hom_ext`
  is the wrong one).
- **Verdict**: ALIGN_WITH_MATHLIB — use basis `TopCat.Sheaf.hom_ext` / sheaf separatedness, NOT raw
  `Scheme.Modules.hom_ext`.

### Decision 3: the algebraic kernel `β_{L,L}=𝟙` and "braiding trivial on invertible"
- **Mathlib idiom (DECISIVE, PRESENT)**: `Module.Invertible.tensorProductComm_eq_refl (R)(M)
  [CommRing R][AddCommGroup M][Module R M][Module.Invertible R M] : TensorProduct.comm R M M =
  LinearEquiv.refl R (TensorProduct R M M)` (`Mathlib.RingTheory.PicardGroup`). Exactly `β_{M,M}=𝟙`
  at the module level, via the CONCRETE swap — matches the presheaf braiding component verbatim.
- **free-rank-1 ⟹ Module.Invertible (1-liner)**: `Module.Invertible.congr (e : M ≃ₗ[R] N)
  [Module.Invertible R M] : Module.Invertible R N` + `Module.Invertible.inst : Module.Invertible R R`.
  So `L(U) ≃ₗ 𝒪(U)` (trivialization on a basis open) ⇒ `Module.Invertible 𝒪(U) (L(U))`. No project
  lemma needed.
- **No abstract "invertible object ⟹ β=𝟙"**: confirmed absent — and FALSE in general (super vector
  spaces: odd line ⊗-invertible yet β=−1). Mathlib correctly only has the concrete-`TensorProduct.comm`
  result. The project MUST go through the concrete module swap, never abstract monoidal invertibility.
- **Gap**: identical to Mathlib for the kernel.
- **Verdict**: ALIGN_WITH_MATHLIB — reuse `tensorProductComm_eq_refl` + `Invertible.congr` verbatim.

## Recommendation
**Route A (recommended, feasible with present bricks).** Re-sign `IsInvertible` (line 137,
unprotected, no consumers) to bundle a trivializing cover/basis as data — the equivalent Stacks-01CR
definition `{Uᵢ}` with `L|Uᵢ ≅ 𝒪_X|Uᵢ`. Then:
1. cover/basis from the class field (gap 1 dissolved);
2. on each trivializing basis open `V`: `L(V) ≃ₗ 𝒪(V)` ⇒ `Module.Invertible 𝒪(V) (L(V))` via
   `Module.Invertible.congr`+`.inst`; presheaf-braiding component = `TensorProduct.comm` = id via
   `Module.Invertible.tensorProductComm_eq_refl` (gap 3, verbatim Mathlib);
3. descend: presheaf braiding agrees with `𝟙` on the trivializing basis ⇒ sheafified braiding = `𝟙`
   via basis `TopCat.Sheaf.hom_ext` / sheaf separatedness on the underlying `TopCat.Sheaf AddCommGrp`
   (gap 2). Note `sheafification.mapIso (Iso.refl) = Iso.refl`, so it suffices that the presheaf
   braiding and `𝟙` become equal after sheafification, i.e. agree on the trivializing basis (W-locality
   of the sheafification localization). **Never** evaluate at `⊤`.
Cost: medium project plumbing for steps 2-3 (relate the class's trivializing iso to the section-level
comm and run the basis descent); zero absent Mathlib bricks.

**Route B (NOT this phase).** Keep the categorical `IsInvertible` and build Stacks-01CR stalk
machinery (module-sheaf stalks, stalk-of-tensor, Nakayama stalk→cover) to derive the cover. Large
genuine build of absent infra (same gap as `snap-route` Analogue-2). Infeasible for SNAP-S0 budget.

**Feasibility gate for SNAP-S0 (ii) `GCommSemiring`**: feasible IFF Route A is taken (class carries
the cover). Under the current categorical class the upgrade is blocked on the Route-B stalk build —
do NOT commit prover budget to `tensorBraiding_self_eq_id_of_isInvertible` until the class is re-signed.

---

## Exact re-sign shape (iter-028)

All four pinning questions resolved against pinned Mathlib (read from
`.lake-packages/mathlib`). Net: Route A is fully buildable with present bricks; the section ring is
`CommRing` for free; the cover field must be a **basis** (not a bare `iSup=⊤` cover); local
invertibility is carried as `Module.Invertible` (candidate (a)); the descent has NO absent brick.

### Type facts established (cite-grade)
- `X.Modules = SheafOfModules X.ringCatSheaf` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:37`).
- `X.ringCatSheaf := (sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`
  (`…/Modules/Presheaf.lean:34`) ⇒ a `TopCat.Sheaf RingCat`.
- **The section ring is `CommRing` for free.** Notation `Γ(X, U) := X.presheaf.obj (op U)`
  (`…/AlgebraicGeometry/Scheme.lean:103`) is a **`CommRingCat`** carrier, so `[CommRing Γ(X,U)]` is
  found by inference — exactly what `tensorProductComm_eq_refl` needs. (The RingCat presentation
  `X.ringCatSheaf.val.obj (op U)` is the *same carrier*, defeq, but only exposes `Ring`; ALWAYS phrase
  the field over `Γ(X,U)` so `CommRing` resolves.)
- Section module: `Γ(L, U) := (Scheme.Modules.presheaf L).obj (op U)` (`…/Modules/Sheaf.lean:91`),
  an `Ab`/`AddCommGroup` object, with the canonical `instance : Module Γ(X, U) Γ(L, U) :=
  (L.val.obj (op U)).isModule` (`…/Modules/Sheaf.lean:93`). So `Γ(L,U)` already carries
  `[AddCommGroup]` + `[Module Γ(X,U)]` — the remaining two `tensorProductComm_eq_refl` hypotheses.
- The presheaf monoidal structure (`PresheafOfModules.monoidalCategory`,
  `…/Presheaf/Monoidal.lean`) lives on `PresheafOfModules (R ⋙ forget₂ _ _)` with `R : Cᵒᵖ ⥤
  CommRingCat`; the project's `MonoidalPresheaf X` (`SectionGradedRing.lean:87`) instantiates
  `R := X.sheaf.obj`, and `R.obj (op U) ≡ Γ(X,U)` (defeq). Line-33 of that file registers
  `instance : CommRing ((R ⋙ forget₂ _ RingCat).obj X)` — same `CommRing` the field will use.

### Point 1 — cover field type → **indexed basis** (VERDICT: ALIGN_WITH_MATHLIB)
Use an indexed family that is a **basis** of the topology, NOT a bare `iSup=⊤` cover:
```lean
{ι : Type u}                                   -- or carry existentially (see shape below)
(U : ι → X.Opens)                              -- X.Opens = TopologicalSpace.Opens X
(isBasis : TopologicalSpace.Opens.IsBasis (Set.range U))
```
Why a basis, not a cover: the descent (point 4) needs `β^{pre}.app = 𝟙` on a *neighbourhood basis of
every point* (sheafification sections at `U_i` are computed from opens `≤ U_i`), and the agreement
brick `TopCat.Sheaf.hom_ext` (`…/SheafCondition/Sites.lean:243`) literally takes
`B : ι → Opens X` with `Opens.IsBasis (Set.range B)`. This is NOT over-strong: for a genuine line
bundle the trivializing opens are **downward-closed** (a sub-open of a trivializing open is
trivializing), and a downward-closed cover is automatically a basis; `IsBasis` of the whole space
also gives the cover (`⊤` is a union of basis opens), so `iSup=⊤` is subsumed. `Set.range U` is the
exact form `hom_ext` consumes (zero adapter). Do **not** use `AlgebraicGeometry.Scheme.OpenCover`
(open-immersion subschemes — far heavier, wrong granularity).

### Point 2 — local-invertibility field → **candidate (a)** (VERDICT: ALIGN_WITH_MATHLIB)
Carry section-module invertibility directly:
```lean
(localInvertible : ∀ i, Module.Invertible Γ(X, U i) Γ(L, U i))
```
`Module.Invertible : Prop` (`Mathlib/RingTheory/PicardGroup.lean:78`), hypotheses
`[CommRing R][AddCommGroup M][Module R M]` — ALL satisfied verbatim by `Γ(X,U i)`/`Γ(L,U i)` per the
type facts above. This is *exactly* the antecedent the descent brick `tensorProductComm_eq_refl`
consumes — zero conversion.
- **Directive's premise is WRONG on one point**: a restriction-to-open functor for `X.Modules` DOES
  exist — `AlgebraicGeometry.Scheme.Modules.restrictFunctor (f) [IsOpenImmersion f]`
  (`…/Modules/Sheaf.lean:319`, pullback along an open immersion). So candidate (b) `L|Uᵢ ≅ 𝒪_X|Uᵢ`
  *is* statable (`restrictFunctor U.ι L ≅ unitModule …`). But (b) is strictly heavier — it needs the
  open subscheme `X∣U`, the immersion `U.ι`, the unit module on the subscheme, and then a *second*
  lemma to extract section-level `Module.Invertible` for the actual descent. Candidate (a) is the
  minimal data the descent uses. **Recommend (a).**
- Free-rank-1 instances feed (a) for free: a trivialization `e : Γ(L,Uᵢ) ≃ₗ[Γ(X,Uᵢ)] Γ(X,Uᵢ)` gives
  `Module.Invertible.congr e` (PicardGroup.lean:164) using `instance Module.Invertible R R` (:158).

### Point 3 — brick applies to the section module (VERDICT: identical / PRESENT)
The presheaf braiding component at `op U` is, by
`PresheafOfModules.Monoidal.braiding_hom_app` (`…/Presheaf/Monoidal.lean:225`):
`(braiding M₁ M₂).hom.app (op U) = (ModuleCat.MonoidalCategory.braiding (M₁.obj (op U))
(M₂.obj (op U))).hom`, and `ModuleCat.MonoidalCategory.braiding A B =
(TensorProduct.comm R A B).toModuleIso` (`…/ModuleCat/Monoidal/Symmetric.lean:26,115`). At
`M₁=M₂=L.toPresheaf`, `Mᵢ.obj (op U) = L.val.obj (op U) = Γ(L,U)`, `R = Γ(X,U)`, so the component is
`(TensorProduct.comm Γ(X,U) Γ(L,U) Γ(L,U)).toModuleIso.hom`. With `localInvertible i :
Module.Invertible Γ(X,Uᵢ) Γ(L,Uᵢ)`, `Module.Invertible.tensorProductComm_eq_refl Γ(X,Uᵢ) Γ(L,Uᵢ)`
(`PicardGroup.lean:606`, sig `(R)(M)[CommRing R][AddCommGroup M][Module R M][Module.Invertible R M] :
TensorProduct.comm R M M = LinearEquiv.refl R (M ⊗ M)`) rewrites `comm → refl`, and
`LinearEquiv.refl.toModuleIso = Iso.refl`, `.hom = 𝟙`. So **`β^{pre}.hom.app (op Uᵢ) = 𝟙`** on every
basis open. (Minor defeq nudge `Γ(X,U) ≡ R.obj (op U)` may need `erw`/`show`; same carrier.)

### Point 4 — descent reachability (VERDICT: REACHABLE, no absent brick)
Target: `tensorBraiding L L = Iso.refl`, where `tensorBraiding L L =
sheafification.mapIso β^{pre}` (`SectionGradedRing.lean:188`). The presheaf braiding is NOT `𝟙`
(false at `⊤`), so work post-sheafification via the unit. Cleanest chain (η = sheafification unit):
1. `β^{pre}.app (op Uᵢ) = 𝟙` on the trivializing basis — Point 3. [section-level, PRESENT]
2. `β^{pre} ≫ η = η` as maps `T → T^#` (`T = L.toPresheaf ⊗ L.toPresheaf`): both land in the **sheaf**
   `T^#`; forget to the underlying `TopCat.Sheaf Ab` via `Scheme.Modules.toPresheaf` (a `Faithful`
   functor, `…/Modules/Sheaf.lean`); they agree on every basis open `Uᵢ`
   (`(β^{pre} ≫ η).app Uᵢ = β^{pre}.app Uᵢ ≫ η.app Uᵢ = 𝟙 ≫ η.app Uᵢ`, by step 1); conclude equal by
   **`TopCat.Sheaf.hom_ext`** (`…/SheafCondition/Sites.lean:243`, basis form) — alt
   `TopCat.Presheaf.IsSheaf.section_ext` (`…/Topology/Sheaves/Sheaf.lean:150`). [PRESENT — this is the
   load-bearing separatedness step; needs the BASIS from Point 1]
3. `sheafification.map β^{pre} = 𝟙`: from step 2 and `𝟙 ≫ η = η`, the two sheaf maps
   `sheafification.map β^{pre}, 𝟙 : T^# → T^#` satisfy `η ≫ (—) = β^{pre} ≫ η = η`; precomposition
   with the unit η is injective on maps into a sheaf (universal property of
   `PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)` — the SAME adjunction the file
   already uses for `sheafificationCounitIso`/`sectionsMul`). [PRESENT]
4. `(sheafification.mapIso β^{pre}).hom = sheafification.map β^{pre}.hom = 𝟙`, and an iso with
   `.hom = 𝟙` is `Iso.refl` by `Iso.ext`. [PRESENT]

**Load-bearing lemmas (all present):** `PresheafOfModules.Monoidal.braiding_hom_app`;
`ModuleCat.MonoidalCategory.braiding` (= `TensorProduct.comm`); `Module.Invertible.tensorProductComm_eq_refl`;
`TopCat.Sheaf.hom_ext` (basis) / `TopCat.Presheaf.IsSheaf.section_ext`; `Scheme.Modules.toPresheaf`
(Faithful); `PresheafOfModules.sheafificationAdjunction`; `Iso.ext`. **No absent brick.** Plumbing
cost: medium (forget-to-Ab, basis `hom_ext`, unit-injectivity), but every step is pinned-Mathlib.

### Recommended concrete signature (drop `: Prop`? NO — keep `Prop`, existential cover)
Since `Module.Invertible` is `Prop` and the sole consumer
(`tensorBraiding_self_eq_id_of_isInvertible`) proves an **equality** (a `Prop`), the cover can be
carried existentially and the class stays a `Prop` (subsingleton — no data-class instance diamonds,
mirrors the current `: Prop`). The descent `obtain`s the witnesses inside the proof:
```lean
class IsInvertible (L : X.Modules) : Prop where
  exists_trivializing_basis :
    ∃ (ι : Type u) (U : ι → X.Opens),
      TopologicalSpace.Opens.IsBasis (Set.range U) ∧
      ∀ i, Module.Invertible Γ(X, U i) Γ(L, U i)
```
(Alternative, if the planner prefers the cover *accessible as data* — the directive's "data class":
drop `: Prop`, make `{ι : Type u}` / `U` / `isBasis` / `localInvertible` plain fields. Equivalent
buildability; only needed if a downstream consumer must name the cover outside a `Prop` goal — none
does yet. Prop-existential is lighter; recommend it.) `Γ(…)` here is the
`AlgebraicGeometry`-scoped notation, in scope after `open AlgebraicGeometry`. The class is
unprotected and consumer-free (all three consumers are gated `sorry`s) ⇒ the re-sign is
downstream-free.

**Blueprint `def:isInvertible` prose** should state: *L is invertible iff there is a basis of opens
`{Uᵢ}` of `X` on each of which the sections `Γ(L,Uᵢ)` form an invertible `Γ(X,Uᵢ)`-module* (equiv.
locally free of rank 1, [Stacks 01CR]) — and note the single arithmetic consequence consumed is
`β_{L,L}=𝟙`, proved by the basis-local descent above, never at `⊤`.
