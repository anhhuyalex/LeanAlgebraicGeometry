# Analogy: rewriting across a `def`-synonym category that carries its own (rfl-defeq) comp instance

## Mode
cross-domain-inspiration

## Slug
comp-instance-diamond

## Iteration
015

## Structural problem (abstracted)
A type synonym `S := B` carries its *own* instance (here `Category`/`CategoryStruct.comp`) that is
`inferInstanceAs`-copied from the base `B`. The two instances are **rfl-defeq but syntactically
distinct terms**. A single goal interleaves morphisms typed with *both* comp heads (`@comp S _` and
`@comp B _`), so positional `rw [Category.assoc]` / `simp [Category.assoc]` never match
("did not find `(?f ≫ ?g) ≫ ?h`"), and the only thing that bridges one step — `erw` — runs a full
cross-defeq `isDefEq` per step and times out when chained ~25–30×.

Concrete instance: `LocalizedMonoidal L W ε := D` (`D = X.Modules`), with
`monoidalCategory : MonoidalCategory X.Modules := inferInstanceAs (… (LocalizedMonoidal …))`
(SectionGradedRing.lean:1644, `@[instance_reducible]`). `Localization.Monoidal.μ/associator_hom_app`
produce `LocalizedMonoidal`-comp morphisms; `tensorObjAssoc`/`sheafification.map` produce
`X.Modules`-comp ones; the goal of `tensorObjAssoc_eta_factor_sheaf` (~2458) mixes them.

## Failed approaches (from directive)
- `repeat erw [Category.assoc]`: bridges one step each but ~25–30 chained → `isDefEq` heartbeat timeout.
- `rw`/`simp only [Category.assoc]`: never match across the syntactic instance mismatch.
- `change`/`show` to erase the `restrictScalars 𝟙` decoration: wrong target (decoration already gone).
- Restating the lemma with `forget`/`sheafification`: broke the internal `rw [key]` in `hα`.

## The governing lesson (verified against Mathlib source + the live goal)
Mathlib's **own** `Localization.Monoidal` development (`Mathlib/CategoryTheory/Localization/Monoidal/
Basic.lean`) never hits this wall because it **never mixes the two comp heads**: every lemma
(`μ_natural_left/right(_assoc)`, `associator_hom_app`, `associator_naturality`, `pentagon`, `triangle`)
is stated and proved *entirely inside* `LocalizedMonoidal L W ε`-comp, reaching the base `C` only
through the functor `(L').map`/`(L').obj` — never via raw `D`-defeq. There is **no base-comp μ-helper**
because Mathlib never leaves the synonym. The project created the diamond by composing a `D`-typed
`tensorObjAssoc`/`sheafification.map` with `LocalizedMonoidal`-typed `μ`.

So the universal fix is **collapse the goal onto ONE comp head, then reuse Mathlib's in-synonym recipe**
— not bridge the defeq step-by-step.

## Analogues found (ranked by porting cost)

### Analogue 1 — `CategoryTheory.Localization.Monoidal` (THE in-domain model)
- **Domain**: category theory / localization.
- **Same problem there**: identical synonym `LocalizedMonoidal L W ε := D` with copied `Category`.
- **Technique**: stay inside the synonym; prove coherence via the `@[reassoc (attr := simp)]` set
  `μ_natural_left_assoc`, `μ_natural_right_assoc`, `μ_inv_natural_*_assoc`, `associator_naturality`,
  `Iso.inv_hom_id_assoc`, `whisker(Left/Right)_comp` — exactly the `pentagon`/`triangle` proofs.
- **Mapping**: once the project's goal is uniformly `LocalizedMonoidal`-comp, those very lemmas apply
  verbatim (the goal's μ-factors are already `Localization.Monoidal.μ …`).
- **Porting cost**: low. **Verdict**: ANALOGUE_FOUND.

### Analogue 2 — `CategoryTheory.Opposite` (`Cᵒᵖ`) — precise category-synonym precedent
- **Domain**: category theory.
- **Same problem there**: `Cᵒᵖ` carries its own `Category` instance; a composite can mix `Cᵒᵖ`- and
  `C`-typed morphisms.
- **Technique**: an explicit transport map `Quiver.Hom.op`/`.unop` plus a **simp normal form**
  (`op_comp : (f ≫ g).op = g.op ≫ f.op`, `unop_comp`, `op_id`, `unop_id`) that pushes a composite
  fully onto one side *before* any positional rewriting. Mathlib never `erw`s across `Cᵒᵖ := C`.
- **Mapping**: the analogue of `op_comp` here is a one-line **rfl comp-bridge** (below) used as a simp
  lemma to normalize every `≫` to the `LocalizedMonoidal` head.
- **Porting cost**: low. **Verdict**: ANALOGUE_FOUND.

### Analogue 3 — `OrderDual`/`Multiplicative`/`Additive`/`MulOpposite` — type-synonym idiom
- **Domain**: order theory / algebra.
- **Same problem there**: `def OrderDual α := α` (resp. `Multiplicative`, `Additive`, `MulOpposite`)
  carries its own (rfl-defeq) instance; `toDual`/`ofDual`, `toMul`/`ofMul`, `op`/`unop` are
  `Equiv.refl`-defeq markers.
- **Technique**: never rely on the defeq inside a proof — always cross through the explicit transport
  marker, with all lemmas restated on the synonym side.
- **Mapping**: confirms the *principle* (marker + normal form, not raw defeq); the category-comp
  specifics come from Analogues 1–2.
- **Porting cost**: n/a (principle only). **Verdict**: PARTIAL_ANALOGUE.

### Analogue 4 — `CategoryTheory.Monoidal.Transported` (`def Transported (e : C ≌ D) := D`)
- **Domain**: monoidal category theory.
- **Same problem there**: monoidal structure transported onto a type synonym of the base — the closest
  shape to `LocalizedMonoidal := D`. Crossing via `toTransported`/`fromTransported` monoidal functors.
- **Verdict**: ANALOGUE_FOUND (same lesson as Analogue 1).

## VALIDATED fix (tested via `lean_multi_attempt` on the live goal, iter-015)
The whole diamond is **pure rfl** (`LocalizedMonoidal := D`, `Category … := inferInstanceAs (Category D)`,
`monoidalCategory := inferInstanceAs (… LocalizedMonoidal …)`). So a one-line comp-bridge typechecks
by `rfl`, and `simp only` with it normalizes every base-comp to the synonym head:

```lean
have hc : ∀ {P Q R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R),
    f ≫ g = @CategoryStruct.comp
      (LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X)) _ P Q R f g :=
  fun f g => rfl
simp only [hc]            -- every ≫ is now LocalizedMonoidal-comp; the diamond is gone
rw [Category.assoc]       -- ✅ FIRES (verified) — no erw, no isDefEq timeout
```

Verified facts:
- `hc := fun f g => rfl` elaborates (diamond is rfl; both sides even pretty-print identically as `f ≫ g`).
- `simp only [hc]; rw [Category.assoc]` runs with **no diagnostics** and the goal re-associates — i.e.
  positional rewriting fires after the bridge.
- `rw [hc]` (instead of `simp only [hc]`) is **insufficient** — it rewrites only one occurrence, leaving
  the rest mixed; `Category.assoc` then still fails. Must use `simp only [hc]` (all occurrences).
- `simp/dsimp +instances [monoidalCategoryStruct]` handles struct-*projection* defeq but does NOT
  collapse the comp-head diamond — not a substitute for `hc`.

After `simp only [hc]`, finish with Mathlib's in-synonym recipe (Analogue 1):
`simp only [Category.assoc, Localization.Monoidal.μ_natural_left_assoc,
  Localization.Monoidal.μ_natural_right_assoc, Localization.Monoidal.μ_inv_natural_left_assoc,
  Localization.Monoidal.μ_inv_natural_right_assoc, Localization.Monoidal.associator_naturality,
  Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]` (exact lemma set to be tuned by the prover).

## Answers to the directive's three questions
1. **Canonical transport idiom**: yes — the rfl comp-bridge `hc` used as `simp only [hc]` IS the
   "normalizing simp lemma base-comp → LocalizedMonoidal-comp". It is the single-pass, defeq-free
   replacement for `repeat erw`. (Mirrors `op_comp` for `Cᵒᵖ`, `toDual` for `αᵒᵈ`.)
2. **Does Mathlib's `Localization.Monoidal` need a base-comp helper?** No — it never leaves the synonym,
   so no such helper exists. The project must do the same: pull the whole sheaf-core equation onto the
   `LocalizedMonoidal` head (via `hc`) and then use the existing in-synonym naturality/`reassoc` lemmas.
3. **Source-retype plan — refined**: the prover's *direction* was backwards. Retyping the μ-factors
   DOWN to `X.Modules`-comp strips the `[reassoc]`/`μ_natural_*`/`associator_naturality` API (all stated
   in `LocalizedMonoidal`-comp). Push the `D`-typed factors UP into `LocalizedMonoidal`-comp instead —
   which is exactly what `simp only [hc]` does, tactic-locally, with **no source change**. A wrapper-iso
   `def` (new blueprint entry) is NOT warranted: the bridge is a one-line rfl `have`, strictly cheaper.

## Recommendation
Drop `repeat erw`. Insert the `hc` comp-bridge + `simp only [hc]` immediately after the existing
`simp only [Localization.Monoidal.toMonoidalCategory]` (SectionGradedRing.lean:2570), then close with
the in-synonym `μ_natural_*_assoc`/`associator_naturality`/`Iso.inv_hom_id_assoc` simp set, reproducing
Mathlib's `pentagon`/`triangle` proof style. Zero new defs, no blueprint obligation, no `maxHeartbeats`.
