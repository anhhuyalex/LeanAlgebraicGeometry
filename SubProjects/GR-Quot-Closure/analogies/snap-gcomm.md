# Analogy: how to STATE `sectionsMul_assoc_unit` + assemble `sectionGradedRing` as `GCommSemiring`/`Gmodule`

## Mode
api-alignment

## Slug
snap-gcomm

## Iteration
080

## Question
How should `sectionsMul_assoc_unit` (and the surrounding graded-ring assembly) be STATED so that
`sectionGradedRing` can be packaged as a `DirectSum.GCommSemiring` / `DirectSum.Gmodule`? The prior
scaffolder (`snap-coherent`) DIED unable to state `sectionsMul_assoc_unit` — the obstacle was the
SIGNATURE SHAPE against the `GCommSemiring` fields, not a proof.

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:196` — `sectionsMul F G` (lax mult, codomain
  `(tensorObj F G).val.obj (op ⊤)`), `:1785` `tensorPowAdd` (μ, DONE), `:1609` `tensorObjAssoc` (DONE),
  `:148` `tensorObjUnitIso`, `:102` `unitModule X`.
- `AlgebraicJacobian/Picard/QuotScheme.lean` — assembly targets `sectionGradedRing_gcommSemiring`,
  `sectionGradedModule_gmodule`, `sectionGradedRing` (NOT yet present; this is the scaffold).
- Blueprint `Picard_SectionGradedRing.tex:1290` `lem:sectionMul_coherent`
  (`…Modules.sectionsMul_assoc_unit`), `:1368` `lem:sectionGradedRing_gcommSemiring`, `:1427`
  `lem:sectionGradedModule_gmodule`.

## THE PRECEDENT (decisive): `Mathlib.LinearAlgebra.TensorPower.Basic`
`TensorPower` = `⨂[R]^n M`, the ℕ-indexed tensor powers of a module, is the field-for-field
analogue of the section graded ring. It builds `GradedMonoid.GMonoid` → `DirectSum.GSemiring` →
`DirectSum.GAlgebra` on `fun i => ⨂[R]^i M` from EXACTLY the data the project has:
a degreewise mult landing in the index-sum, plus tensor associativity/unit isos. Mirror it.

Field shapes (verified by `#print` this iter):
- `GradedMonoid.GMul A` : `mul : {i j} → A i → A j → A (i+j)`.
- `GradedMonoid.GOne A` : `one : A 0`.
- `GradedMonoid.GMonoid A` (extends GMul,GOne): `one_mul/mul_one/mul_assoc : ∀ (a b c : GradedMonoid A), …`
  — these are `Eq`s in the **sigma type** `GradedMonoid A = Σ i, A i`, with `* ` defined by
  `GradedMonoid.mk_mul_mk : mk i a * mk j b = mk (i+j) (GMul.mul a b)` (rfl). `gnpow`/`gnpow_zero'`/
  `gnpow_succ'` have DEFAULTS (`gnpowRec`) — OMIT them (TensorPower does: `Basic.lean:192`).
- `DirectSum.GSemiring A` (needs `∀ i, AddCommMonoid (A i)`): adds `mul_zero/zero_mul/mul_add/add_mul`
  (bilinearity, FREE from linearity of the degreewise mult) + `natCast/natCast_zero/natCast_succ`.
- `DirectSum.GCommSemiring A` (needs `AddCommMonoid ι`): adds `mul_comm : ∀ (a b : GradedMonoid A), a*b=b*a`.
- `DirectSum.Gmodule A M` (over `GMonoid A`, `VAdd ιA ιM`): `GSMul.smul : A i → M j → M (i +ᵥ j)`,
  `one_smul/mul_smul : ∀ (… : GradedMonoid …), …` (sigma Eqs), `smul_add/smul_zero/add_smul/zero_smul`
  (bilinearity, FREE).

## Decisions identified

### Decision: the type of `sectionsMul_assoc_unit` (the crux that killed `snap-coherent`)
- **Mathlib idiom** (`TensorPower.Basic.lean:147,159,169`): the coherences are NOT raw `HEq`, NOT
  hand-written sigma `Eq`s. They are **`cast`-mediated `Eq`s in a single component module**, where
  `cast R M (h : i = j) : ⨂[R]^i M ≃ₗ[R] ⨂[R]^j M` is the index-equality transport:
  ```
  theorem one_mul  {n}        (a) :              cast R M (zero_add n)     (ₜ1 ₜ* a)      = a
  theorem mul_one  {n}        (a) :              cast R M (add_zero n)     (a ₜ* ₜ1)      = a
  theorem mul_assoc{na nb nc} (a b c) :          cast R M (add_assoc …)    (a ₜ* b ₜ* c)  = a ₜ* (b ₜ* c)
  ```
  Then the `GMonoid` sigma-`Eq` fields are produced by the bridge
  `gradedMonoid_eq_of_cast (h : a.fst=b.fst) (h2 : cast h a.snd = b.snd) : a = b`
  (`Basic.lean:123`), used as
  `mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _)` (`:194-197`).
- **Why this shape**: on ℕ, `(i+j)+k` is NOT defeq to `i+(j+k)`, so the two sides of the sigma `Eq`
  live in different `A _`. A bare carrier-level `Eq` does not typecheck; a raw `HEq` is unworkable in
  proofs. The `cast` (an `eqToHom`/transport linear-equiv) moves one side into the other's type,
  giving a HONEST `Eq` in ONE module — provable by `⊗`-induction — which the bridge repackages as the
  required `GradedMonoid` `Eq`. This is precisely "an `Eq` mediated by the index-transport iso".
- **Project's path** (proposed): state `sectionsMul_assoc_unit` as the SAME three (four) cast-mediated
  `Eq`s, with the project's index transport in place of `TensorPower.cast` (see Recommendation).
- **Gap**: divergent-and-wrong if the scaffolder writes a single GradedMonoid Eq or a raw HEq;
  identical-to-Mathlib once it adopts the cast-mediated form.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: which typeclass(es) to build
- **Idiom**: `GradedMonoid.GMul`+`GOne` (instances) → `GradedMonoid.GMonoid` → `DirectSum.GSemiring`
  → `DirectSum.GCommSemiring`; separately `DirectSum.Gmodule` for the twisted sections. `DirectSum.toSemiring`
  / `GradedAlgebra` / `HomogeneousLocalization` are for INTERNAL (submodule) gradings — NOT applicable
  here (the pieces `Γ(L^⊗m)` are external standalone modules). Use the EXTERNAL `DirectSum.G*` API
  (blueprint already cites `DirectSum.GCommSemiring`/`DirectSum.Gmodule`).
- **Verdict**: ALIGN_WITH_MATHLIB (`DirectSum.G*`, external), NEEDS_MATHLIB_GAP_FILL only for the
  project-local `cast` + `gradedMonoid_eq_of_cast` analogues (trivial, below).

## Recommendation — concrete signatures the next scaffolder should write

Carrier family (`Γ(X,𝒪_X)`-module = underlying type of the ModuleCat object at the top open):
```
abbrev sectionDeg (L : X.Modules) (m : ℕ) : Type u := ↥((tensorPow L m).val.obj (Opposite.op ⊤))
-- AddCommGroup + Module Γ(X,𝒪_X) inherited from the ModuleCat object.
```

Index transport (the project's `TensorPower.cast` analogue — Γ applied to `eqToIso` on `tensorPow L`):
```
def sectionsCast (L) {i j} (h : i = j) : sectionDeg L i ≃ₗ[Γ𝒪] sectionDeg L j
  := -- the linear equiv underlying ((eqToIso (congrArg (tensorPow L) h)).val.app (op ⊤))
@[simp] lemma sectionsCast_refl … : sectionsCast L (rfl : i = i) = LinearEquiv.refl …  -- (eqToIso rfl = Iso.refl)
```

Degreewise data (instances):
```
instance : GradedMonoid.GMul (sectionDeg L) where
  mul {i j} a b := (Γmap (tensorPowAdd L i j).hom) (sectionsMul _ _ (a ⊗ₜ b))   -- Γ(μ_{i,j}) ∘ sectionsMul
instance : GradedMonoid.GOne (sectionDeg L) where
  one := -- image of (1 : Γ𝒪) in sectionDeg L 0 = Γ(unitModule X), via the canonical Γ𝒪 ≅ Γ(L^⊗0)
```

`sectionsMul_assoc_unit` (split, mirroring `TensorPower.{one_mul,mul_one,mul_assoc}`; add `mul_comm`):
```
theorem sectionsMul_one_mul   {n} (a : sectionDeg L n) :
    sectionsCast L (zero_add n)   (GradedMonoid.GMul.mul GradedMonoid.GOne.one a) = a
theorem sectionsMul_mul_one   {n} (a : sectionDeg L n) :
    sectionsCast L (add_zero n)   (GradedMonoid.GMul.mul a GradedMonoid.GOne.one) = a
theorem sectionsMul_mul_assoc {na nb nc} (a b c) :
    sectionsCast L (add_assoc na nb nc)
      (GradedMonoid.GMul.mul (GradedMonoid.GMul.mul a b) c)
      = GradedMonoid.GMul.mul a (GradedMonoid.GMul.mul b c)
theorem sectionsMul_mul_comm  {na nb} (a b) :
    sectionsCast L (add_comm na nb) (GradedMonoid.GMul.mul a b) = GradedMonoid.GMul.mul b a
```
(`sectionsMul_assoc_unit` in the blueprint = these collectively; mathematical content = blueprint
`lem:sectionMul_coherent` proof: reduce to presheaf top-open where eval is STRICT monoidal, ride
naturality of the sheafification unit η through `tensorObjAssoc`/`tensorObjUnitIso`/`tensorPowAdd`.)

Bridge (project-local `gradedMonoid_eq_of_cast`; trivial since `sectionsCast` is `eqToHom`-transport):
```
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid (sectionDeg L)}
    (h : a.fst = b.fst) (h2 : sectionsCast L h a.snd = b.snd) : a = b := by
  cases a; cases b; cases h; simpa [sectionsCast_refl] using congrArg (GradedMonoid.mk _) h2
```

Assembly (verbatim TensorPower shape; `gnpow`/`natCast` defaults/degree-0 image; bilinearity FREE):
```
instance : GradedMonoid.GMonoid (sectionDeg L) :=
  { (inferInstance : GradedMonoid.GMul _), (inferInstance : GradedMonoid.GOne _) with
    one_mul  := fun _     => gradedMonoid_eq_of_cast (zero_add _)   (sectionsMul_one_mul _)
    mul_one  := fun _     => gradedMonoid_eq_of_cast (add_zero _)   (sectionsMul_mul_one _)
    mul_assoc:= fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (sectionsMul_mul_assoc _ _ _) }
    -- gnpow defaulted (do NOT supply), exactly as TensorPower.Basic:192-197
instance sectionGradedRing_gsemiring : DirectSum.GSemiring (sectionDeg L) :=
  { (inferInstance : GradedMonoid.GMonoid _) with
    mul_zero := fun _ => map_zero _ ;  zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add  := fun _ _ _ => map_add _ _ _ ;  add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => (n : Γ𝒪) • GradedMonoid.GOne.one ;  natCast_zero := …; natCast_succ := … }
instance sectionGradedRing_gcommSemiring : DirectSum.GCommSemiring (sectionDeg L) :=
  { sectionGradedRing_gsemiring with
    mul_comm := fun _ _ => gradedMonoid_eq_of_cast (add_comm _ _) (sectionsMul_mul_comm _ _) }
-- ⇒ Semiring (⨁ m, sectionDeg L m) by DirectSum.instCommSemiring; this IS sectionGradedRing.
```
(NB: bilinearity fields are FREE because the degreewise mult `Γ(μ)∘sectionsMul` is `Γ𝒪`-bilinear — see
TensorPower.Basic:225-231 for the exact `map_zero/map_add/map_zero₂/map_add₂` discharges.)

`Gmodule` for twisted sections (`def:sheafModuleTwist`, `moduleTensorPow F L m`):
```
abbrev twistDeg (F L) (m : ℕ) : Type u := ↥((moduleTensorPow F L m).val.obj (op ⊤))
instance : GradedMonoid.GSMul (sectionDeg L) (twistDeg F L) where
  smul {i j} a x := (Γ <reassoc+merge iso, blueprint :1454>) (sectionsMul _ _ (a ⊗ₜ x))
instance sectionGradedModule_gmodule : DirectSum.Gmodule (sectionDeg L) (twistDeg F L) :=
  { …GdistribMulAction (smul_add/smul_zero FREE) with
    one_smul := fun _   => gradedMonoid_eq_of_cast (zero_add _) (twist_one_smul _)
    mul_smul := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (twist_mul_smul _ _ _)
    add_smul := …; zero_smul := … }   -- same cast-mediated-Eq idiom; +ᵥ = + on ℕ
```
Precedent for the `GMulAction` sigma-Eq fields: `GradedMonoid.GMulAction` (`Mathlib.Algebra.GradedMonoid`),
same `gradedMonoid_eq_of_cast` discharge.

**Bottom line for the scaffolder**: `sectionsMul_assoc_unit` is NOT one declaration of an exotic type.
It is the FOUR cast-mediated component-level `Eq`s above (the `TensorPower.{one_mul,mul_one,mul_assoc}`
+ `mul_comm` analogues). The single new brick is `sectionsCast` (Γ of `eqToIso`) and the trivial
`gradedMonoid_eq_of_cast` bridge. Everything else is the verbatim `TensorPower.Basic` assembly.
