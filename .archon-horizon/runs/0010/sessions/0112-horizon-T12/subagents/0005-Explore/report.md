I have all the information needed. Here is the structured report.

---

# Report

All paths under `/home/Axel/LeanAlgebraicGeometry-Horizon/.lake-packages/mathlib/`.

---

## 1. `Mathlib/RingTheory/Flat/Localization.lean` (read in full, 130 lines)

**Imports:** `Mathlib.RingTheory.Flat.Stability`, `Mathlib.RingTheory.LocalProperties.Exactness`.
**Opened namespaces (line 29):** `IsLocalizedModule LocalizedModule LinearMap TensorProduct`.

### Variable blocks (in scope order)

**Top-level file variables (lines 31–33)** — in scope for `IsLocalization.flat`, `Localization.flat`, and the whole `Module` namespace:
```
variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
```
So: `R` implicit CommSemiring, `S` explicit CommSemiring with `Algebra R S`; `p : Submonoid R` with `[IsLocalization p S]`; `M` an `R`- and `S`-module with `[IsScalarTower R S M]`.

**Added inside `namespace Module` for `flat_of_isLocalized_maximal` (lines 56–62):**
```
variable (Mₚ : ∀ (P : Ideal S) [P.IsMaximal], Type*)
  [∀ (P : Ideal S) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module S (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], IsScalarTower R S (Mₚ P)]
  (f : ∀ (P : Ideal S) [P.IsMaximal], M →ₗ[S] Mₚ P)
  [∀ (P : Ideal S) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
```

**Added for `flat_of_isLocalized_span` (lines 79–87):**
```
variable (s : Set S) (spn : Ideal.span s = ⊤)
  (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  [∀ r : s, Module S (Mₛ r)]
  [∀ r : s, IsScalarTower R S (Mₛ r)]
  (g : ∀ r : s, M →ₗ[S] Mₛ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
include spn
```
Note: the localization submodules `Mₛ r`/`Mₚ P` are localizations of the `S`-module `M` (maps are `M →ₗ[S] …`), but the flatness conclusion/hypotheses are over the **base ring `R`**.

### Exact statements

`IsLocalization.flat` (line 36), with `include p in`:
```lean
theorem IsLocalization.flat : Module.Flat R S
```

`Localization.flat` (line 44):
```lean
instance Localization.flat [Module.Flat R S] (p : Submonoid S) : Module.Flat R (Localization p)
```
(Here the section `p : Submonoid R` is shadowed by this new `p : Submonoid S`.) Proof:
```lean
  have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _
```

`Module.flat_iff_of_isLocalization` (line 51), with `include p in`:
```lean
theorem flat_iff_of_isLocalization : Flat S M ↔ Flat R M :=
  have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_isLocalizedModule S p .id⟩
```

`Module.flat_of_isLocalized_maximal` (line 65), with `include f in`:
```lean
theorem flat_of_isLocalized_maximal (H : ∀ (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M
```

`Module.flat_of_localized_maximal` (line 74):
```lean
theorem flat_of_localized_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl M)) :
    Flat R M :=
  flat_of_isLocalized_maximal _ _ _ (fun _ _ ↦ mkLinearMap _ _) h
```

`Module.flat_of_isLocalized_span` (line 90), with `include g in` (and `spn` already `include`d), **full proof quoted**:
```lean
theorem flat_of_isLocalized_span (H : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N ↦ injective_of_isLocalized_span s spn _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _ fun r ↦ ?_
  simpa [IsLocalizedModule.map_lTensor] using H r N
```
Technique: reduce flatness to `lTensor` injectivity via `Flat.iff_lTensor_injectiveₛ`; rewrite `lTensor` as the `AlgebraTensorModule.coe_lTensor` over `S`; then apply the local-to-global injectivity lemma `injective_of_isLocalized_span` (from `RingTheory.LocalProperties.Exactness`), feeding the localized maps `AlgebraTensorModule.rTensor R _ (g r)` and closing each stalk goal with `IsLocalizedModule.map_lTensor` + the hypothesis `H`. The `_maximal` variant is identical but uses `injective_of_isLocalized_maximal`. No private helpers are defined in this file; the key imported helpers are `injective_of_isLocalized_span` / `injective_of_isLocalized_maximal` and `IsLocalizedModule.map_lTensor`.

`Module.flat_of_localized_span` (line 99):
```lean
theorem flat_of_localized_span
    (h : ∀ r : s, Flat S (LocalizedModule.Away r.1 M)) :
    Flat S M :=
  flat_of_isLocalized_span _ _ _ spn _ (fun _ ↦ mkLinearMap _ _) h
```

Also present (lines 106–129, `variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]`):
- an anonymous instance giving `Module.Flat (Localization.AtPrime p) (Localization.AtPrime P)` from `[Module.Flat A B]` (proof: `rw [Module.flat_iff_of_isLocalization …]; exact Module.Flat.trans A B _`);
- `IsSMulRegular.of_isLocalizedModule` and `IsSMulRegular.of_isLocalization`.

**There is no `Module.Flat.of_isLocalizedModule` in this file** — that name lives in `Flat/Stability.lean` (see §2). `flat_iff_of_isLocalization` uses it as `.of_isLocalizedModule`.

---

## 2. Flatness of a localized module over the ORIGINAL base ring — `Mathlib/RingTheory/Flat/Stability.lean` (read in full, 135 lines)

**Imports:** `Flat.Basic`, `RingTheory.IsTensorProduct`, `LinearAlgebra.TensorProduct.Tower`, `RingTheory.Localization.BaseChange`, `Algebra.Module.LocalizedModule.Basic`. Everything is in `namespace Module.Flat`.

### Composition section (variables lines 56–58: `R S M`, `[CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]`)

`Module.Flat.trans` (line 62), **full proof quoted**:
```lean
open AlgebraTensorModule in
theorem trans [Flat R S] [Flat S M] : Flat R M := by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S), ← EquivLike.injective_comp (cancelBaseChange R S S _ _),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  iterate 2 apply Flat.lTensor_preserves_injective_linearMap
  exact Subtype.val_injective
```
(So `[Flat R S] [Flat S M] → Flat R M`.)

`Module.Flat.ulift_left_iff` (line 73): `Flat (ULift.{t} R) M ↔ Flat R M`.
`Module.Flat.ulift_right_iff` (line 81): `Flat R (ULift.{t} M) ↔ Flat R M`.

### BaseChange section (variables lines 95–97: `R S M`, `[CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M]`)

`Module.Flat.baseChange` (line 100):
```lean
instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := inferInstance
```
→ result is flat over **`S`** (the algebra), the top ring.

`Module.Flat.isBaseChange` (line 103) — the equiv-transfer lemma:
```lean
theorem isBaseChange [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Flat S N :=
  of_linearEquiv (IsBaseChange.equiv h).symm
```

### Localization section (variables lines 112–114)
```
variable {R : Type u} {M Mp : Type*} (Rp : Type v)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring Rp] [Algebra R Rp]
  [AddCommMonoid Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]
```

`Module.Flat.localizedModule` (line 116):
```lean
instance localizedModule [Flat R M] (S : Submonoid R) :
    Flat (Localization S) (LocalizedModule S M)
```
→ flat over `Localization S` (localization of the **base** ring `R`). `S` is a submonoid **of `R`** (the ring `M` is flat over).

`Module.Flat.of_isLocalizedModule` (line 123):
```lean
theorem of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp := by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h
```
→ flat over `Rp` (localization of base `R`).

Anonymous instance (line 128): `[CommSemiring A] [Algebra R A] [Flat R A] (S : Submonoid R) → Flat (Localization S) (Localization (Algebra.algebraMapSubmonoid A S))`.

### On the exact lemma you asked for (M flat over R, p a submonoid of the TOP ring S, conclude `Flat R (LocalizedModule p M)`)

**No single lemma of that exact shape exists.** Every localized-module flatness lemma in Mathlib (`localizedModule`, `of_isLocalizedModule`) localizes at a submonoid of the ring the module is flat over, and concludes flatness over the *localization* of that ring — never over the original bottom ring `R` when `p ⊆ S ≠ R`. The relevant building blocks to assemble it yourself:
- `IsLocalization.flat` (§1): `Localization p` is `S`-flat.
- `Module.Flat.trans` (§2): flatness composes.
- `Localization.flat` (§1): `[Module.Flat R S] → Module.Flat R (Localization p)` for `p : Submonoid S` — the analogue for the ring itself.
- `Module.Flat.of_isLocalizedModule` / `LocalizedModule.equivTensorProduct` (§3) to identify `LocalizedModule p M ≃ Localization p ⊗[S] M`, then transfer flatness via `of_linearEquiv`/`equiv_iff`.

No `instLocalizedModuleFlat`-style instance covers the cross-ring case.

---

## 3. `IsLocalizedModule.isBaseChange` and `IsBaseChange.equiv`

`IsLocalizedModule.isBaseChange` — `Mathlib/RingTheory/Localization/BaseChange.lean:34` (section variables lines 26–30):
```
variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')
```
```lean
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f
```
Companion iff (line 47): `theorem isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange A f`.
Also `LocalizedModule.equivTensorProduct` (line 63): `LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[R] M`.

`IsBaseChange` definition — `Mathlib/RingTheory/IsTensorProduct.lean:325` (section variables lines 317–320: `S : Type*` with `[CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]`, `f : M →ₗ[R] N`):
```lean
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M →ₗ[R] N)).flip f).restrictScalars R)
```
Then `variable {S f} (h : IsBaseChange S f)`.

`IsBaseChange.equiv` — line 400 (direction: `S ⊗[R] M → N`):
```lean
noncomputable nonrec def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N
```
Supporting simp lemmas: `IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • f m` (line 412); `IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m` (line 416). Constructor: `IsBaseChange.of_equiv (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ x) = f x) : IsBaseChange S f` (line 419). `IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q` (line 338).

---

## 4. "Basic opens cover an affine open" ⇔ `Ideal.span = ⊤` — `Mathlib/AlgebraicGeometry/AffineScheme.lean`

Section context: `namespace IsAffineOpen` with `variable {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))` (line 379).

**The names in the task (`basicOpen_union_eq_self_iff`, `self_le_basicOpen_union_iff`) do not exist in this Mathlib version.** They were renamed to the `iSup` forms:

`IsAffineOpen.iSup_basicOpen_eq_self_iff` (line 909, `include hU in`):
```lean
theorem iSup_basicOpen_eq_self_iff {s : Set Γ(X, U)} :
    ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal.span s = ⊤
```

`IsAffineOpen.self_le_iSup_basicOpen_iff` (line 936, `include hU in`):
```lean
theorem self_le_iSup_basicOpen_iff {s : Set Γ(X, U)} :
    (U ≤ ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s = ⊤
```

Inverse direction without affineness — `AlgebraicGeometry.iSup_basicOpen_of_span_eq_top` (line 1002):
```lean
lemma iSup_basicOpen_of_span_eq_top {X : Scheme} (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) : (⨆ i ∈ s, X.basicOpen i) = U
```

`IsAffineOpen.exists_basicOpen_le` (line 622, `include hU in`, with `set_option backward.isDefEq.respectTransparency false`):
```lean
theorem exists_basicOpen_le {V : X.Opens} (x : V) (h : ↑x ∈ U) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f
```

`AlgebraicGeometry.exists_basicOpen_le_affine_inter` (line 750, `include hU in`):
```lean
theorem _root_.AlgebraicGeometry.exists_basicOpen_le_affine_inter
    {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ U ⊓ V) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f
```

---

## 5. Affine basic opens, localization at basic open, preimages — `AffineScheme.lean`

`IsAffineOpen.isLocalization_basicOpen` (line 659, `include hU in`):
```lean
theorem isLocalization_basicOpen :
    IsLocalization.Away f Γ(X, X.basicOpen f)
```
(Recall `f : Γ(X, U)` from the section variables.) Non-namespaced instance `isLocalization_away_of_isAffine` (line 673): `[IsAffine X] (r : Γ(X, ⊤)) → IsLocalization.Away r Γ(X, X.basicOpen r)`.

`IsAffineOpen.basicOpen` (line 597, `include hU in`) — basic open of an affine open is affine:
```lean
theorem basicOpen :
    IsAffineOpen (X.basicOpen f)
```
Related: `Spec_basicOpen` (line 605): `IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen f)`; instance (line 609): `[IsAffine X] (r : Γ(X, ⊤)) → IsAffine (X.basicOpen r)`.

Preimage/affineness lemmas:
- `IsAffineOpen.preimage_of_isIso` (line 518): `{U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ⁻¹ᵁ U)`.
- `IsAffineOpen.preimage_of_isOpenImmersion` (line 523): `{U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsOpenImmersion f] (hU' : U ≤ f.opensRange) : IsAffineOpen (f ⁻¹ᵁ U)`.
- `IsAffineOpen.ι_basicOpen_preimage` (line 613, `include hU in`): `(r : Γ(X, ⊤)) : IsAffineOpen ((X.basicOpen r).ι ⁻¹ᵁ U)`.
- `IsAffineOpen.basicOpen_basicOpen_is_basicOpen` (line 736, `include hU in`): `(g : Γ(X, X.basicOpen f)) : ∃ f' : Γ(X, U), X.basicOpen f' = X.basicOpen g`.
- `IsAffineOpen.isLocalization_of_eq_basicOpen` (line 726): `{V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) : @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra`.

Bonus (basic-open `appLE` = `IsLocalization.Away.map`), lines 678–723:
- `appLE_eq_away_map` (line 678): `f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) _ = CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U V e).hom r)`.
- `IsAffineOpen.app_basicOpen_eq_away_map` (line 693); `IsAffineOpen.appBasicOpenIsoAwayMap` (line 714).

---

## 6. Flatness transfer along ring iso / restriction of scalars

`Module.Flat.of_linearEquiv` — `Mathlib/RingTheory/Flat/Basic.lean:181` (same ring `R`):
```lean
lemma of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : Flat R N :=
  of_retract e.toLinearMap e.symm (by simp)
```
`Module.Flat.equiv_iff` (line 186):
```lean
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ ↦ of_linearEquiv e.symm, fun _ ↦ of_linearEquiv e⟩
```
`Module.Flat.of_retract` (line 172): `[Flat R M] (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N`.

**There is no `Module.Flat.of_ringHom`, `Module.Flat.of_ringEquiv`, or `Module.Flat.of_equiv` (ring-iso variant) in `Flat/Basic.lean`.** For transferring flatness of a *fixed module* along a ring isomorphism `e : R ≃+* R'` (action through `e`), the relevant machinery is `Module.compHom` (used at `Flat/FaithfullyFlat/Basic.lean:563`: `let _ : Module R N := Module.compHom N (algebraMap R S)`) — but no packaged lemma exists; you would restrict scalars and use `of_linearEquiv`/`equiv_iff`.

For **ring homomorphisms** (`RingHom.Flat`), transfer along isomorphisms IS packaged — `Mathlib/RingTheory/RingHom/Flat.lean`:
```lean
/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize Module.Flat]
def RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Flat R S                                             -- line 27
```
```lean
lemma RingHom.Flat.of_bijective {f : R →+* S} (hf : Function.Bijective f) : Flat f  -- line 50
lemma RingHom.Flat.respectsIso : RespectsIso Flat                                    -- line 60
lemma RingHom.Flat.comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f)  -- line 45
```
`of_bijective`'s proof is the template for the ring-iso case: `algebraize [f]; exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm`.

---

## 7. `Scheme.Hom.appLE` and composition/restriction lemmas

`Mathlib/AlgebraicGeometry/Scheme.lean` — section variables `(f : X ⟶ Y)` etc.:

`appLE` def (line 196):
```lean
def appLE (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.app U ≫ X.presheaf.map (homOfLE e).op
```

`appLE_map` (line 200, `@[reassoc (attr := simp)]`):
```lean
lemma appLE_map (e : V ≤ f ⁻¹ᵁ U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e)
```
`map_appLE` (line 211, `@[reassoc (attr := simp)]`):
```lean
lemma map_appLE (e : V ≤ f ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le)
```
`appLE_eq_app` (line 226): `f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U`. `app_eq_appLE` (line 222): `f.app U = f.appLE U _ le_rfl`.
`appLE_congr` (line 230):
```lean
lemma appLE_congr (e : V ≤ f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
    (P : ∀ {R S : CommRingCat.{u}} (_ : R ⟶ S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (e₁ ▸ e₂ ▸ e))
```
`appLE_comp_appLE` (line 395, `@[reassoc]`):
```lean
theorem appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le)
```
`comp_appLE` (line 403, `@[simp, reassoc]`): `(f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e`.
(Also `Spec.map_appLE` at Scheme.lean:562.)

### `resLE` — `Mathlib/AlgebraicGeometry/Restrict.lean`

`resLE` def (line 746):
```lean
def resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme :=
  X.homOfLE e ≫ f ∣_ U
```
Then `variable (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)`.

`resLE_app_top` (line 795, `@[simp]`, with `set_option backward.isDefEq.respectTransparency false`):
```lean
@[simp] lemma resLE_app_top : (f.resLE U V e).app ⊤ =
    U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv
```

`resLE_appLE` (line 799, `set_option backward.isDefEq.respectTransparency false`):
```lean
lemma resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) (e' : W ≤ resLE f U V e ⁻¹ᵁ O) :
    (f.resLE U V e).appLE O W e' =
      f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_resLE_preimage_iff f e O W).mp e')
```
Other useful ones: `resLE_eq_morphismRestrict` (751), `resLE_id` (755), `resLE_comp_ι` (760), `resLE_comp_resLE` (764), `map_resLE` (770), `resLE_map` (775), `resLE_congr` (780), `resLE_preimage` (784), `le_resLE_preimage_iff` (789), `coe_resLE_apply` (809).

---

## 8. `cancelBaseChange` and `Module.Flat.baseChange`

`TensorProduct.AlgebraTensorModule.cancelBaseChange` — `Mathlib/LinearAlgebra/TensorProduct/Tower.lean:436`. In-scope module instances (CommSemiring section, lines 379–388, plus the section's own `variable [Algebra A B] [IsScalarTower A B M]` at line 432): `[CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]`, `M` with `[Module R M] [Module A M] [Module B M] [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]`, `N` with `[Module R N]`, and `[Algebra A B] [IsScalarTower A B M]`. Explicit args `R A B M N`:
```lean
def cancelBaseChange : M ⊗[A] (A ⊗[R] N) ≃ₗ[B] M ⊗[R] N :=
  letI g : (M ⊗[A] A) ⊗[R] N ≃ₗ[B] M ⊗[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g
```
Simp lemmas: `cancelBaseChange_tmul (m n a) : cancelBaseChange R A B M N (m ⊗ₜ (a ⊗ₜ n)) = (a • m) ⊗ₜ n` (line 447); `cancelBaseChange_symm_tmul (m n) : (cancelBaseChange R A B M N).symm (m ⊗ₜ n) = m ⊗ₜ (1 ⊗ₜ n)` (line 452); `lTensor_comp_cancelBaseChange` (line 456, used in `Flat.trans`). The `B = A` specialization is the common case (see docstring).

`Module.Flat.baseChange` — `Flat/Stability.lean:100` (repeated for locality):
```lean
instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := inferInstance
```
Variables: `[CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M]`. **The result `S ⊗[R] M` is flat over `S`** (the algebra / top ring), given `M` flat over `R`.
