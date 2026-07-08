# Interface map: building `HasCechToHModuleIso (Scheme.toModuleKSheaf C) S.coverFamily` from `IsAffineHModuleVanishing k C F`

Target class: `AlgebraicGeometry.Scheme.HasCechToHModuleIso` — `AlgebraicJacobian/Cohomology/MayerVietorisCover.lean:490`, content `∀ n, cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ i, 𝒰 i)`.

## 1. Mayer–Vietoris LES core (`MayerVietorisCore.lean`)

All the following are stated for a **generic** Grothendieck-topology square `S : J.MayerVietorisSquare` (Mathlib's abstract 4-corner square X₁ = pullback, X₂, X₃, X₄ = pushout), not yet specialized to opens. They mirror `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` verbatim with `AddCommGrpCat.free → ModuleCat.free k`.

- **`Abelian.Ext.chgUnivLinearEquiv`** — `MayerVietorisCore.lean:101` (`noncomputable def`, `namespace` = top-level, i.e. `Abelian.Ext.chgUnivLinearEquiv`).
  ```
  {R} [Ring R] {C} [Category C] [Abelian C] [Linear R C]
  [HasExt.{w} C] [HasExt.{w'} C] {X Y : C} {n : ℕ} :
  Abelian.Ext.{w} X Y n ≃ₗ[R] Abelian.Ext.{w'} X Y n
  ```
  Project-local **upgrade** of Mathlib's bare `Equiv` `Abelian.Ext.chgUniv` (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:540`) to a `LinearEquiv`, via helper lemmas `Abelian.Ext.chgUniv_add`/`chgUniv_smul` (lines 60, 79). This is the **universe bridge** used throughout (`Ext.{u} ↔ Ext.{u+1}`).

- **`HModule'_cohomologyPresheafFunctor` / `HModule'_cohomologyPresheaf`** — lines 128, 147. `F ↦ (X ↦ HModule' k F n X)` as `Cᵒᵖ ⥤ AddCommGrpCat`. Requires `[HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]` — single-universe `HasExt` (whatever universe is asked for at the call site; `HModule'` itself lives in `Type u` so this is `HasExt.{u}` in practice).

- **`HModule'_toBiprod`** — line 171: `(HModule'_cohomologyPresheaf k F n).obj (op S.X₄) ⟶ obj(op S.X₂) ⊞ obj(op S.X₃)` (sum of the two restrictions, `biprod.lift`).
- **`HModule'_fromBiprod`** — line 195: `obj(op S.X₂) ⊞ obj(op S.X₃) ⟶ obj(op S.X₁)` (difference of restrictions, `biprod.desc` with a negation).
- **`HModule'_toBiprod_fromBiprod`** — line 230, `@[reassoc (attr:=simp)]`: composite is `0`.
- **`HModule'_shortComplex`** — line 303, `@[simps]`: the `ShortComplex (Sheaf J (ModuleCat.{u} k))` of **sheafified free presheaves** on the four corners (`X₁ → X₂ ⊞ X₃ → X₄`), `f`/`g` the difference/sum of `yoneda ⋙ free k` maps sheafified.
- **`HModule'_shortComplex_f_mono` / `_g_epi` / `_exact` / `_shortExact`** — lines 355, 372, 387, 405: the free-sheaf short complex is short-exact, via `HModule'_isPushoutModuleCatFreeSheaf` (line 270, the pushout-of-free-sheaves fact) and `ModuleCat_free_isLeftAdjoint`/`ModuleCat_free_preservesMonomorphisms` (lines 250, 341, Mathlib gap-fills).
- **`HModule'_δ`** — line 439, the connecting hom:
  ```
  (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k)) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (HModule'_cohomologyPresheaf k F n₀).obj (op S.X₁) ⟶ (HModule'_cohomologyPresheaf k F n₁).obj (op S.X₄)
  ```
  = `AddCommGrpCat.ofHom ((HModule'_shortComplex_shortExact k S).extClass.precomp _ (by omega))`, using `[HasExt (Sheaf J (ModuleCat.{u} k))]`.
- **`HModule'_sequence`** — line 464 (`noncomputable abbrev`): 
  ```
  (S) (F) (n₀ n₁ : ℕ) (h : n₀+1=n₁) : ComposableArrows AddCommGrpCat 5
    = mk₅ (toBiprod n₀) (fromBiprod n₀) (δ n₀ n₁ h) (toBiprod n₁) (fromBiprod n₁)
  ```
  i.e. the 6-object chain `Hⁿ⁰(X₄) → Hⁿ⁰(X₂)⊞Hⁿ⁰(X₃) → Hⁿ⁰(X₁) → Hⁿ¹(X₄) → Hⁿ¹(X₂)⊞Hⁿ¹(X₃) → Hⁿ¹(X₁)`.
- **`HModule'_sequenceIso`** — line 565: iso to `Abelian.Ext.contravariantSequence (HModule'_shortComplex_shortExact k S) F n₀ n₁ (by omega)` (Mathlib's `Ext.contravariantSequence`).
- **`HModule'_sequence_exact`** — line 591 (**the exactness statement**):
  ```
  (S : J.MayerVietorisSquare) (F : Sheaf J (ModuleCat.{u} k)) (n₀ n₁ : ℕ) (h : n₀+1=n₁) :
    (HModule'_sequence k S F n₀ n₁ h).Exact
  ```
  `ComposableArrows.Exact` is `Mathlib/Algebra/Homology/ExactSequence.lean:128` (`structure Exact extends IsComplex`), exactness **at each of the four internal objects** (indices 1,2,3,4 of the 6-object chain), i.e. gives exactness of the two adjacent 3-term windows `toBiprod(n₀)/fromBiprod(n₀)`, `fromBiprod(n₀)/δ`, `δ/toBiprod(n₁)`, `toBiprod(n₁)/fromBiprod(n₁)`.
- **`HModule'_δ_toBiprod`** (line 604) / **`HModule'_fromBiprod_δ`** (line 616): `@[reassoc(attr:=simp)]` zero-composite companions, extracted from `.zero 2` / `.zero 1` of the exactness structure.

**Universe**: `HModule'_sequence`/`_exact` are single-universe, parametric in whatever `[HasExt (Sheaf J (ModuleCat.{u} k))]` is supplied (in practice instantiated at `Ext.{u}`, matching `HModule' : Type u`). The `u ↔ u+1` bridge (`Abelian.Ext.chgUnivLinearEquiv`) is only used separately, to connect `HModule'` at the top open to `HModule` (`Type u+1`); it is **not** baked into `HModule'_sequence_exact` itself.

## 2. `AffineCoverMVSquare`

- **Structure** — `MayerVietorisCover.lean:50`:
  ```
  structure AffineCoverMVSquare (X : Scheme.{u}) where
    U₁ U₂ : X.Opens
    isAffineOpen_U₁ : IsAffineOpen U₁
    isAffineOpen_U₂ : IsAffineOpen U₂
    isAffineOpen_inf : IsAffineOpen (U₁ ⊓ U₂)
    cover : U₁ ⊔ U₂ = ⊤
  ```
- **`AffineCoverMVSquare.toMayerVietorisSquare`** — line 71: `S.toMayerVietorisSquare := Opens.mayerVietorisSquare S.U₁ S.U₂`, with corners **definitionally** (`rfl`) `X₁ = U₁⊓U₂` (line 79), `X₂ = U₁` (85), `X₃ = U₂` (91); `X₄ = ⊤` needs the `cover` field (`toMayerVietorisSquare_toSquare_X₄`, line 99, proved *by* `S.cover`, not `rfl`).
- **`AffineCoverMVSquare.coverFamily`** — `Cokernel.lean:173`: `ULift.{u} (Fin 2) → X.Opens`, `fun i => if i.down = 0 then S.U₁ else S.U₂`. `coverFamily ⟨0⟩ = U₁`, `coverFamily ⟨1⟩ = U₂` (`rfl`, simp lemmas lines 177/180).
- **`AffineCoverMVSquare.iSup_coverFamily`** — `Cokernel.lean:188`: `⨆ i, S.coverFamily i = ⊤` (proved from `S.cover : U₁ ⊔ U₂ = ⊤` via `sup_le`+`le_iSup_of_le`; **not** `rfl`).
- **`AffineCoverMVSquare.overlapOpen`** — `Cokernel.lean:646` (`noncomputable abbrev`): `S.coverFamily ⟨0⟩ ⊓ S.coverFamily ⟨1⟩`, defeq to `U₁ ⊓ U₂` (docstring notes it is kept as a separate abbrev purely for transparency-uniformity in later rewriting, not for a semantic difference).

So `S.coverFamily` (the `ULift(Fin 2)`-indexed family used by `cechCohomology`) and `S.toMayerVietorisSquare` (the 4-corner `MayerVietorisSquare` used by `HModule'_sequence`) are **two independently-built views of the same `U₁,U₂`**: `coverFamily` feeds the concrete Čech complex (`Scheme.cechCochain`), `toMayerVietorisSquare` feeds the abstract MV biproduct LES. Bridging the *two representations degree-by-degree* is exactly what is missing (see gap list).

## 3. Degree 0

- **No** in-project identification of `cechCohomology C F 𝒰 0` with `HModule' k F 0 (⨆𝒰)`, `H⁰`, or "sections" exists anywhere (`Cokernel.lean`, `Carriers.lean`, `MayerVietorisCover.lean` all searched; zero hits for `cechCohomologyZero`/`H0`/`zeroEquiv`-style names).
- **`HModule'_zero_linearEquiv`** — `Carriers.lean:120`:
  ```
  (F : Sheaf J (ModuleCat.{u} k)) (X : C) :
    HModule' k F 0 X ≃ₗ[k]
      ((presheafToSheaf _ _).obj ((yoneda ⋙ (whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X) ⟶ F)
  ```
  i.e. `HModule'` in degree 0 is `Abelian.Ext.linearEquiv₀`-identified with a **Hom group from the sheafified free presheaf on `X`**, *not yet* collapsed further to `F.obj.obj (op X)`. This further collapse is a genuine missing brick; the Mathlib names that would build it (found by search, none of them chained together in-project for the `Sheaf J (ModuleCat k)` apparatus — the in-project uses of this pattern, `CechBridge.lean`/`AbsoluteCohomology.lean`, are all for the *different* `X.PresheafOfModules`/`X.Modules` apparatus, `PresheafOfModules.sheafificationAdjunction`/`PresheafOfModules.freeHomEquiv`, not usable verbatim here) are:
  - `CategoryTheory.sheafificationAdjunction J D : presheafToSheaf J D ⊣ sheafToPresheaf J D` (`Mathlib/CategoryTheory/Sites/Sheafification.lean:80`) — `.homEquiv` gives `((presheafToSheaf J D).obj P ⟶ F) ≃ (P ⟶ F.val)`.
  - `ModuleCat.adj k : ModuleCat.free k ⊣ forget (ModuleCat k)` (already used at `MayerVietorisCore.lean:250`) whiskered via `CategoryTheory.Adjunction.whiskerRight` (`Mathlib/CategoryTheory/Adjunction/Whiskering.lean:32`, `protected def whiskerRight (adj : F ⊣ G) : (whiskeringRight C _ _).obj F ⊣ (whiskeringRight C _ _).obj G`) to strip `ModuleCat.free k` off `yoneda.obj X ⋙ free k ⟶ F.val`, landing at `yoneda.obj X ⟶ F.val ⋙ forget (ModuleCat k)`.
  - `CategoryTheory.yonedaEquiv : (yoneda.obj X ⟶ G) ≃ G.obj (op X)` (`Mathlib/CategoryTheory/Yoneda.lean:723`) to collapse to `(F.val ⋙ forget).obj (op X) = F.obj.obj (op X)` (underlying carrier).

  None of this three-step chain is assembled in-project for `Sheaf J (ModuleCat.{u} k)`; it is a genuine missing brick for degree 0.
- **`HModule_zero_linearEquiv`** — `Carriers.lean:70`, parallel statement at the whole-sheaf level: `HModule k F 0 ≃ₗ[k] ((constantSheaf J _).obj (ModuleCat.of k k) ⟶ F)`.
- Related sheaf-axiom-style ingredients that *are* present but only for `Sheaf.Γ`/`⊤`, not for the Čech complex: `SheafGammaObj_linearEquiv_top` (`Carriers.lean:393`), using Mathlib's `Sheaf.ΓNatIsoSheafSections` + `Preorder.isTerminalTop`.

## 4. Degree 1

- **`AffineCoverMVSquare.H1Cok`** — `Cokernel.lean:243`: `F.obj.obj (op (U₁⊓U₂)) ⧸ LinearMap.range (S.sectionDiff F)`, where `sectionDiff` (line 232) is the difference-of-restrictions map `Γ(U₁,F)×Γ(U₂,F) → Γ(U₁⊓U₂,F)`.
- **`AffineCoverMVSquare.cechCohomologyOneEquivH1Cok`** — `Cokernel.lean:1232`:
  ```
  (S : X.AffineCoverMVSquare) (F : Sheaf (...) (ModuleCat.{u} k)) :
    cechCohomology C F S.coverFamily 1 ≃ₗ[k] S.H1Cok F
  ```
  **Unconditional** — no `IsAffineHModuleVanishing`/`HasCechToHModuleIso` hypotheses, no `[HasExt]` at all. Pure homological algebra about the concrete 3-term truncation of the 2-cover unnormalized Čech complex (`isoSc' 0 1 2` + `moduleCatHomologyIso` + `overlapKerEquiv`/`map_range_pairDiff`). This is a solid, reusable brick.
- **`H1Cok ≃ HModule'¹` (i.e. a genuine "`HModule'_one` from the MV LES") does NOT exist anywhere.** Searched for `hModuleOne`, `HModule'_one` (bare, non `_curve`/`_coverFamily`): zero hits besides the already-gated wrappers below. The docstring of `Cokernel.lean` (lines 16–37, 63–108) and of `CechAcyclicInstance.lean` (lines 24–43) both **describe** the intended MV-LES-based identification `H1Cok S F ≃ₗ[k] HModule' k F 1 ⊤` as future/missing work ("*which uses the degree-0/degree-1 slice of the MV LES together with the affine H¹-vanishing on U₁, U₂*") — it is **not built**.
- **`AffineCoverMVSquare.hModuleOne_linearEquiv_cechCohomology_coverFamily`** — `Cokernel.lean:204`:
  ```
  (S : C.left.AffineCoverMVSquare) (F : Sheaf (...) (ModuleCat.{u} k))
  [HasExt.{u}(...)] [HasExt.{u+1}(...)] [HasCechToHModuleIso F S.coverFamily] (n : ℕ) :
    HModule k F n ≃ₗ[k] cechCohomology C F S.coverFamily n
  ```
  **Confirmed: this ALREADY consumes the gate `[HasCechToHModuleIso F S.coverFamily]` as an instance hypothesis** — it is a *downstream consumer* of the target class, not a producer of it, and hence cannot be used to build the target. It is a thin wrapper around `hModuleOne_linearEquiv_cechCohomology` (line 136, same signature abstractly) which itself just chains `cechToHModuleIso n` with `HModule'_eq_HModule_linearEquiv` (the `u↔u+1` bridge) at the terminal `⊤`.
- **`AffineCoverMVSquare.hModuleOneEquivH1Cok`** — `Cokernel.lean:1248`: `[HasCechToHModuleIso F S.coverFamily] → HModule k F 1 ≃ₗ[k] S.H1Cok F`, again gated on the target class (composes `hModuleOne_linearEquiv_cechCohomology_coverFamily` at `n=1` with `cechCohomologyOneEquivH1Cok`). Consumed by `Adelic.module_finite_hModule_one_of_finiteMapToP1` (`GenusFiniteness.lean:64`) and `..._of_cechGate` (`CechComparisonGate.lean:155`).

## 5. Degree ≥ 2

**No** in-project lemma asserts vanishing (or any other identification) of `cechCohomology C F S.coverFamily n` for `n ≥ 2`. Searched `Cokernel.lean` (declaration list lines 136–1257 fully enumerated: nothing past the degree-1 `cechCohomologyOneEquivH1Cok`/`hModuleOneEquivH1Cok`), `CechAcyclicInstance.lean`, `CechComparisonGate.lean` — the only occurrences of "`n ≥ 2`"/"vanish" are in **docstring prose** describing the intended (unbuilt) argument:
> *"`n ≥ 2`: both sides vanish — the Čech complex of a 2-element cover is `3`-term, and the derived side vanishes by the MV LES together with the affine vanishing on `U₁`, `U₂`, `U₁⊓U₂`."* (`CechAcyclicInstance.lean:41-43`, `CechComparisonGate.lean:62`)

No lemma backs this claim. As the task notes, the terms are **not** structurally zero (they're products over `Fin(n+1) → ULift(Fin 2)`, nonzero in every degree); the vanishing would have to come from an actual homology computation of the (degenerate-index-heavy) `n`-truncation, mirroring the degree-1 `sc' 0 1 2`/`moduleCatHomologyIso` argument one level up, or from a genuinely different route (e.g. showing the augmented Čech complex is split-exact past degree 1 using the degenerate/repeated-index structure — Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex`/`FormalCoproduct` machinery has no such "acyclic cover ⟹ complex quasi-iso to sheaf" theorem at all, confirmed by reading `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean` in full — it only *defines* `cechComplexFunctor`, no comparison theorem). This is the single largest structural gap.

`Scheme.IsCechAcyclicCover` (`Carriers.lean:612`) is the `Prop`-class that would package exactly "`Subsingleton (cechCohomology C F 𝒰 n)` for `n>0`" (both degree 1 and degree ≥2 combined) but **no instance producer for it exists** for `𝒰 = S.coverFamily` anywhere; it is consumed abstractly by `subsingleton_HModule'_supr_of_isCechAcyclicCover` (line 635) but never instantiated.

## 6. Shape of the MV LES across all degrees

`HModule'_sequence_exact` (item 1) gives, for **each fixed consecutive pair** `(n₀,n₁ = n₀+1)`, exactness of the 6-object window
```
Hⁿ⁰(X₄) → Hⁿ⁰(X₂)⊞Hⁿ⁰(X₃) → Hⁿ⁰(X₁) → Hⁿ¹(X₄) → Hⁿ¹(X₂)⊞Hⁿ¹(X₃) → Hⁿ¹(X₁)
```
at its 4 internal vertices. There is **no single in-project theorem packaging the full infinite LES** `... → Hⁿ(X₄) → Hⁿ(X₂)⊞Hⁿ(X₃) → Hⁿ(X₁) → Hⁿ⁺¹(X₄) → ...`; it must be assembled by **chaining `HModule'_sequence_exact k S F n n' h` over all consecutive `n`** (each call re-proves the exactness at `Hⁿ⁺¹(X₄)`/`Hⁿ⁺¹(X₂)⊞Hⁿ⁺¹(X₃)` that the *next* call also proves at its left end — the individual windows overlap by one vertex, so the family covers every consecutive triple). This chaining is not itself written anywhere in-project (no `HModule'_sequence_exact_all` / induction wrapper).

Specialized to `S : AffineCoverMVSquare` via `AffineCoverMVSquare.HModule'_sequence`/`_exact` (`MayerVietorisCover.lean:111`/`121`) and `_curve` (lines 135/146), with corners `X₁=U₁⊓U₂, X₂=U₁, X₃=U₂, X₄=⊤` (item 2). This is the biproduct-shaped LES on `U₁,U₂` directly — it is **not indexed by `S.coverFamily`'s `ULift(Fin 2)`**, so bridging it degree-by-degree to `cechCohomology C F S.coverFamily n` (the actual quantity `HasCechToHModuleIso` compares) is itself unaddressed work (beyond the degree-1 case, which sidesteps this by computing `cechCohomology...1` directly as `H1Cok`, a quantity built from `U₁,U₂` sections without reference to the abstract biproduct sequence at all).

## 7. Other consumables (`CechAcyclicInstance.lean`, `CechComparisonGate.lean`, `Cokernel.lean`, `GenusFiniteness.lean`)

- **`AffineCoverMVSquare.isAffineOpen_coverFamily`** (`CechAcyclicInstance.lean:105`) / **`isAffineOpen_overlapOpen`** (114): `IsAffineOpen (S.coverFamily i)` / `IsAffineOpen S.overlapOpen`, unconditional, from the structure fields.
- **`AffineCoverMVSquare.subsingleton_hModule'_coverFamily`** (137) / **`subsingleton_hModule'_overlapOpen`** (144): under `[IsAffineHModuleVanishing k C F]` (the exact hypothesis the task grants), `Subsingleton (HModule' k F i (S.coverFamily j))` / `Subsingleton (HModule' k F i S.overlapOpen)` for `i > 0`. These are single-universe (`HasExt.{u}` only) and are precisely the per-piece vanishing inputs an MV-LES-based assembly would feed at each corner `X₁,X₂,X₃` (but **not** `X₄=⊤`, which is what's being computed).
- **Universe-note (`CechAcyclicInstance.lean:80-88`, explicitly flagged)**: the affine vanishing lives at `HModule' = Abelian.Ext.{u}`, but `AffineCoverMVSquare.HModule'_sequence` bakes its `[HasExt]` at `Abelian.Ext.{u+1}` in the way it's normally invoked downstream (via `_curve`, which is unconstrained in universe but the genus-carrier consumer chain uses `u+1`). Any assembly must explicitly instantiate `HModule'_sequence`/`_exact` at `HasExt.{u}` (it is universe-parametric, so this is legal) to match `IsAffineHModuleVanishing`'s universe, **or** transport via `Abelian.Ext.chgUnivLinearEquiv` as the docstring anticipates.
- **`module_finite_hModule_one_unconditional`** (`CechAcyclicInstance.lean:174`), **`module_finite_hModule_one_of_finiteMapToP1_of_cechGate`** (`CechComparisonGate.lean:155`), **`module_finite_hModule_one_of_finiteMapToP1`** (`GenusFiniteness.lean:64`) — all three are downstream consumers taking `[∀ S, HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily]` (or the unquantified single-`S` form) as instance hypothesis; none help build it.
- **Gate 3 discharge** (`CechComparisonGate.lean:114-138`): `isGrothendieckAbelian_moduleKSheaf`, `enoughInjectives_moduleKSheaf`, `hasExt_moduleKSheaf`, `hasExt_succ_moduleKSheaf` — all `inferInstance` one-liners confirming `[HasExt.{u}]`/`[HasExt.{u+1}]` for `Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)` are **free** (via `IsGrothendieckAbelian`/`EnoughInjectives`/`HasExt.standard`), so any assembly can freely use both universes of `Ext`.

## Gap list — bricks MISSING for the degreewise assembly of `HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily`

1. **Degree 0**: no identification `cechCohomology C F S.coverFamily 0 ≃ₗ[k] HModule' k F 0 ⊤` (sheaf-axiom step). Even the pure algebraic sub-step `Hom(sheafify(free∘yoneda X), F) ≃ₗ[k] F(X)` (needed to finish `HModule'_zero_linearEquiv`) is unbuilt in the constant-`k` apparatus (Mathlib pieces identified: `sheafificationAdjunction`, `Adjunction.whiskerRight (ModuleCat.adj k)`, `yonedaEquiv` — none chained together here).
2. **Degree 1**: `H1Cok S F ≃ₗ[k] HModule' k F 1 ⊤` via the degree-0/1 slice of `HModule'_sequence_exact` fed by `subsingleton_hModule'_coverFamily` on `U₁,U₂` — described in docstrings, **not proved**. (`cechCohomology...1 ≃ H1Cok` itself, `cechCohomologyOneEquivH1Cok`, *is* available unconditionally.)
3. **Degree ≥ 2**: no vanishing statement for `cechCohomology C F S.coverFamily n`, `n≥2`, exists at all (neither the Čech side nor an `HModule'` side); Mathlib's `Sites/SheafCohomology/Cech.lean` supplies no acyclic-cover-computes-cohomology comparison theorem to lean on generically either.
4. **Structural bridge**: `S.coverFamily : ULift(Fin 2) → Opens` (feeding `cechCohomology`/`Scheme.cechCochain`) and `S.toMayerVietorisSquare` (feeding `HModule'_sequence`, biproduct-shaped on `U₁,U₂` directly) are two independent representations; no degreewise comparison map/iso between the `Fin(n+1)→ULift(Fin 2)`-indexed Čech complex and the abstract MV biproduct sequence is constructed beyond the ad hoc degree-1 `sc' 0 1 2` computation.
5. **Full LES packaging**: `HModule'_sequence_exact` only proves one consecutive-pair window at a time; no chained/inductive full-LES theorem exists (needed to reach `HModule'¹(⊤)` from vanishing at all corners, or degree ≥2 vanishing which needs two consecutive windows: `(1,2)` for the `X₄` vertex at degree 2, using vanishing at `X₁,X₂,X₃` degree 1 *and* 2).
6. No instance producer anywhere for `Scheme.IsCechAcyclicCover (toModuleKSheaf C) S.coverFamily` (the class that would directly package "positive-degree Čech cohomology of this cover vanishes"), which — combined with the (missing) `HasCechToHModuleIso`-independent degree-0 sheaf-axiom identification — is the other route to the target class via `subsingleton_HModule'_supr_of_isCechAcyclicCover`.
