# Analogy: Need#1 geometric transport — `hjt` (jShriekOU) and `hqc` (quasi-coherence) under the spectrum equivalence

## Mode
api-alignment

## Slug
need1-finish

## Iteration
060

## Question
Discharge the two `sorry` holes in `OpenImmersionPushforward.lean` (lines 484/485) for the
`pushforwardEquivOfIso`-transport `Φ = Scheme.Modules.pushforwardEquivOfIso φ`, `φ : U ≅ Spec R`:

- **`hjt`** : `Φ.functor.obj (jShriekOU V) ≅ jShriekOU (φ.inv ⁻¹ᵁ V)`.
- **`hqc`** : `(Φ.functor.obj H).IsQuasicoherent`, for quasi-coherent `H : U.Modules`.

---

## `hjt` — SOLVED, compiles axiom-clean (verbatim proof below)

**Status: DONE.** The proof below was compiled in this iteration via `lean_run_code` against
`import AlgebraicJacobian.Cohomology.OpenImmersionPushforward` +
`import AlgebraicJacobian.Cohomology.AbsoluteCohomology`. `#print axioms q2` returns exactly
`[propext, Classical.choice, Quot.sound]` — axiom-clean.

```lean
noncomputable def q2 {R : CommRingCat.{u}} (U : Scheme.{u}) (φ : U ≅ Spec R) (V : U.Opens) :
    (Scheme.Modules.pushforwardEquivOfIso φ).functor.obj (jShriekOU V)
      ≅ jShriekOU (φ.inv ⁻¹ᵁ V) := by
  set Φ := Scheme.Modules.pushforwardEquivOfIso φ
  set A := jShriekOU V
  have e1 : coyoneda.obj (Opposite.op (Φ.functor.obj A))
      ≅ Φ.inverse ⋙ coyoneda.obj (Opposite.op A) :=
    (Φ.toAdjunction.compCoyonedaIso).app (Opposite.op A)
  have cV : coyoneda.obj (Opposite.op A)
      ≅ AlgebraicGeometry.sectionsFunctor V ⋙ forget AddCommGrpCat :=
    (Functor.isoWhiskerRight (sectionsFunctorCorepIso V) (forget AddCommGrpCat)).symm
  have cV' : AlgebraicGeometry.sectionsFunctor (φ.inv ⁻¹ᵁ V) ⋙ forget AddCommGrpCat
      ≅ coyoneda.obj (Opposite.op (jShriekOU (φ.inv ⁻¹ᵁ V))) :=
    Functor.isoWhiskerRight (sectionsFunctorCorepIso (φ.inv ⁻¹ᵁ V)) (forget AddCommGrpCat)
  have big : coyoneda.obj (Opposite.op (Φ.functor.obj A))
      ≅ coyoneda.obj (Opposite.op (jShriekOU (φ.inv ⁻¹ᵁ V))) :=
    e1 ≪≫ Functor.isoWhiskerLeft Φ.inverse cV ≪≫
      (eqToIso (by rfl : Φ.inverse ⋙ (AlgebraicGeometry.sectionsFunctor V ⋙ forget AddCommGrpCat)
        = AlgebraicGeometry.sectionsFunctor (φ.inv ⁻¹ᵁ V) ⋙ forget AddCommGrpCat)) ≪≫ cV'
  exact (Coyoneda.fullyFaithful.preimageIso big).symm.unop
```

**Open context required** for this to elaborate as-is:
`open CategoryTheory Limits AlgebraicGeometry Scheme.Modules Opposite`.

### Why it works (the load-bearing facts, all verified)
1. **`preadditiveCoyoneda.obj X ⋙ forget AddCommGrpCat = coyoneda.obj X` is `rfl`.** So the
   project's `sectionsFunctorCorepIso V : sectionsFunctor V ≅ preadditiveCoyoneda.obj (op (jShriekOU V))`
   (already built in `OpenImmersionPushforward.lean:160`) whiskered by `forget AddCommGrpCat` gives an
   iso `coyoneda.obj (op (jShriekOU V)) ≅ sectionsFunctor V ⋙ forget` — the corepresentability of the
   *Type-valued* sections functor by `jShriekOU V`.
2. **`Scheme.Modules.pushforward f ⋙ sectionsFunctor V = sectionsFunctor (f ⁻¹ᵁ V)` is `rfl`**
   (sections of a pushforward are, definitionally, the sections over the preimage open —
   `pushforward_obj_obj` is `rfl`). This is why the `eqToIso (by rfl : …)` in `big` typechecks:
   `Φ.inverse = pushforward φ.inv`, so `Φ.inverse ⋙ sectionsFunctor V = sectionsFunctor (φ.inv ⁻¹ᵁ V)`
   on the nose, hence also after whiskering with `forget`.
3. **`Adjunction.compCoyonedaIso`** is the Mathlib equivalence-coyoneda iso:
   `(Φ.toAdjunction.compCoyonedaIso).app (op A) : coyoneda.obj (op (Φ.functor.obj A)) ≅ Φ.inverse ⋙ coyoneda.obj (op A)`.
   It packages "a representable transported across an equivalence is corepresented on the other side
   by the inverse-image object."
4. **`Coyoneda.fullyFaithful : (coyoneda (C := …)).FullyFaithful`** reflects isos:
   `Coyoneda.fullyFaithful.preimageIso big : op (Φ.functor.obj A) ≅ op (jShriekOU (φ.inv ⁻¹ᵁ V))`,
   then `.symm.unop` lands the desired iso in the original (un-opped) direction.

### FRAMING CORRECTION (important — supersedes prior prover/blueprint notes)
Earlier notes (`analogies/deepbridge.md`, blueprint, prover journals) described `hjt` as a
"deep adjunction-mate / high-LOC / confirmed Mathlib gap." **That is WRONG.** `hjt` is a short
(~12-line) corepresentability argument built entirely from existing Mathlib API
(`Adjunction.compCoyonedaIso`, `Coyoneda.fullyFaithful`, `Functor.isoWhiskerLeft/Right`) plus the
project's already-built `sectionsFunctorCorepIso`. The only "geometry" is the two `rfl`s above. No
mate-of-an-adjunction transposition, no naturality square to hand-prove. The prover should drop
`hjt` straight in.

---

## `hqc` — minimal residual: "pushforward along a scheme iso preserves quasi-coherence" (Mathlib GAP)

**Verdict: NEEDS_MATHLIB_GAP_FILL.** There is no Mathlib lemma "pushforward (or pullback) of a
quasi-coherent module along a morphism preserves quasi-coherence" — the entire AG layer instantiates
`IsQuasicoherent` only for `tilde` (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` is the *sole* AG
file mentioning `IsQuasicoherent`). Confirmed gaps this iteration:
- `infer_instance` for `(Φ.functor.obj H).IsQuasicoherent` from `[H.IsQuasicoherent]` — FAILS.
- No `SheafOfModules.pushforward`/`pullback` + `IsQuasicoherent` lemma in Mathlib (loogle empty).

### Why no shortcut exists
`IsQuasicoherent M` (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249`) is
`Nonempty (QuasicoherentData M)`, where `QuasicoherentData` (line 201) is a **local** datum:
a cover `X : I → C` of `⊤` in the *site* `C = Opens U` plus a `Presentation` of `M.over (X i)` for
each `i`. Two facts kill every "easy" route:
- **No global presentation of `H`.** `H` is qcoh on the *abstract affine* `U`, so it carries only
  *local* presentations. `Presentation.map` (line 178: transports a **global** `Presentation` across
  any colimit-preserving `F` with `η : F.obj (unit) ≅ unit`) is therefore inapplicable to `H`
  directly — there is no `H.Presentation` to feed it. Mathlib has `presentationTilde`
  (`Tilde.lean:376`, a global presentation of `tilde M` on `Spec R`) but only on the *target*,
  which is circular (it needs `Φ.functor.obj H ≅ tilde M`, i.e. qcoh, already).
- **`QuasicoherentData.ofIsIso` / iso-closure is same-site only.** `isQuasicoherent` IS closed under
  isomorphism — `SheafOfModules.instIsClosedUnderIsomorphismsIsQuasicoherent` (Quasicoherent.lean:330),
  used in the project as `(SheafOfModules.isQuasicoherent.{u} (Spec R).ringCatSheaf).prop_of_iso`
  (`QcohTildeSections.lean:108`). But this transports qcoh only **within one fixed site**
  `(Spec R).Modules`; it cannot bridge `U.Modules ⟶ (Spec R).Modules`, which is where `Φ` lives.

So `hqc` genuinely requires moving `H`'s **local** qcoh data across the equivalence, and a functor
transport of a *local* condition needs the functor to commute with **restriction to opens** (the
over-site) — exactly the content that `QuasicoherentData.bind` (Quasicoherent.lean:360) internalises
via `pushforwardPushforwardEquivalence` + `Over.iteratedSliceEquiv`.

### The shortest correct route (the residual lemma + its proof skeleton)

Minimal residual lemma (state it generically in the scheme iso; instantiate at `φ := U.isoSpec`):

```lean
lemma isQuasicoherent_pushforwardEquivOfIso {X Y : Scheme.{u}} (φ : X ≅ Y)
    (H : X.Modules) [H.IsQuasicoherent] :
    ((Scheme.Modules.pushforwardEquivOfIso φ).functor.obj H).IsQuasicoherent
```

Proof skeleton (mirrors the `presentation` field of `QuasicoherentData.bind`):

1. `obtain ⟨q⟩ := (IsQuasicoherent.nonempty_quasicoherentData (M := H))` — a cover
   `q.X : q.I → Opens X` of `⊤` with `q.presentation i : (H.over (q.X i)).Presentation`.
2. Apply `SheafOfModules.IsQuasicoherent.of_coversTop` (Quasicoherent.lean:377) with the **image
   cover** `fun i => φ.inv ⁻¹ᵁ (q.X i) : q.I → Opens Y`.
   - `CoversTop` of the image cover: transport `q.coversTop` along the homeomorphism `φ.inv.base`
     (`φ` is an iso of schemes ⇒ `φ.inv.base` is a homeomorphism). Residual sub-fact **R3** (cheap).
   - **Sidestep the `of_coversTop` timeout** (directive note): supply each per-`i`
     `(((Φ.functor.obj H)).over (φ.inv ⁻¹ᵁ (q.X i))).IsQuasicoherent` as an explicit `haveI`
     (term-mode), NOT via class search, so synthesis never recurses into the nested over-site
     instances. The ambient doubly-over-site `HasSheafify`/`WEqualsLocallyBijective` instances on
     `Opens (Spec R)` are available (the project already runs the full qcoh theory on `Spec R`).
3. Each per-`i` qcoh witness — the **geometric heart**, residual sub-fact **R1**:
   - Build the over-site equivalence `eᵢ : (X.Modules ⇂ q.X i) ≌ (Y.Modules ⇂ φ.inv ⁻¹ᵁ q.X i)`
     via `SheafOfModules.pushforwardPushforwardEquivalence`
     (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:305`) for the
     opens-site equivalence `Opens (q.X i) ≌ Opens (φ.inv ⁻¹ᵁ q.X i)` induced by the restricted
     homeomorphism. (`bind` builds the analogous `eᵢ` from `Over.iteratedSliceEquiv`; here use the
     homeomorphism `φ` restricted to the open.)
   - The **comparison iso** `eᵢ.functor.obj (H.over (q.X i)) ≅ (Φ.functor.obj H).over (φ.inv ⁻¹ᵁ q.X i)`:
     "pushforward along `φ` commutes with restriction to the open." This is the genuinely new content.
   - Transport: `(q.presentation i).map eᵢ.functor ηᵢ : (eᵢ.functor.obj (H.over (q.X i))).Presentation`
     (needs **R2** `ηᵢ : eᵢ.functor.obj (unit) ≅ unit`, the structure-sheaf compatibility — routine
     for a site equivalence, cf. `Presentation.quasicoherentData` uses `(by rfl)` for the identity
     case), then `Presentation.ofIsIso (comparison iso).hom` (Quasicoherent.lean:132) to land a
     `Presentation ((Φ.functor.obj H).over (φ.inv ⁻¹ᵁ q.X i))`, hence `.isQuasicoherent`.

### Residual sub-facts, ranked by cost
- **R1 (medium–high, the real work):** the over-site equivalence `eᵢ` and the comparison iso
  `eᵢ.functor.obj (H.over Vᵢ) ≅ (Φ_*H).over (φ.inv⁻¹Vᵢ)`. ~40–100 LOC; adapt the `presentation`
  field of `QuasicoherentData.bind` (Quasicoherent.lean:369–375), replacing `Over.iteratedSliceEquiv`
  with the homeomorphism-induced opens-site equivalence from `φ`.
- **R2 (low):** `ηᵢ : eᵢ.functor.obj (SheafOfModules.unit) ≅ SheafOfModules.unit`. A pushforward
  equivalence sends the structure-sheaf-as-module to itself; for the identity-base case it is `rfl`
  (see `Presentation.quasicoherentData` line 314, `P.map (pushforward (𝟙 _)) (by rfl)`).
- **R3 (low):** the image cover `fun i => φ.inv ⁻¹ᵁ (q.X i)` covers `⊤` — transport `q.coversTop`
  along the homeomorphism `φ.inv.base`.

### API inventory (all confirmed present)
- `SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData` — extract the local datum.
- `SheafOfModules.IsQuasicoherent.of_coversTop` — assemble qcoh from a cover with qcoh restrictions.
- `SheafOfModules.Presentation.map` / `.mapGenerators` / `.mapRelations` — transport a global
  presentation across a colimit-preserving functor with `η : F.obj (unit) ≅ unit`.
- `SheafOfModules.Presentation.ofIsIso` — move a presentation across an iso (same site).
- `SheafOfModules.Presentation.isQuasicoherent` — a global presentation ⇒ qcoh (trivial cover).
- `SheafOfModules.pushforwardPushforwardEquivalence` — the site-equivalence-induced module
  equivalence (the over-site transport vehicle).
- `SheafOfModules.QuasicoherentData.bind` — the template whose `presentation` field is exactly the
  per-piece transport to copy.
- `(SheafOfModules.isQuasicoherent _).prop_of_iso` — same-site iso-closure (final clean-up if needed).

## Recommendation
Drop `hjt = q2` in verbatim (axiom-clean, ~12 lines) — it is NOT a hard gap and the old
"deep-mate" framing should be deleted. For `hqc`, formalize `isQuasicoherent_pushforwardEquivOfIso`
as above: a `QuasicoherentData`/`of_coversTop` transport whose single non-trivial input is R1 (the
"pushforward commutes with restriction to an open" comparison iso), structurally a copy of
`QuasicoherentData.bind`'s `presentation` field with the homeomorphism-induced opens-site
equivalence in place of `Over.iteratedSliceEquiv`. This is moderate, self-contained infrastructure —
not circular, and not blocked on any further Mathlib gap beyond R1's own construction.
