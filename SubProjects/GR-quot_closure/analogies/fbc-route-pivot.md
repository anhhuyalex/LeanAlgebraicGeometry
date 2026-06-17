# Analogy: KEEP-vs-PIVOT for the affine i=0 base-change iso (the mate coherence)

## Mode
cross-domain-inspiration

## Slug
fbc-route-pivot

## Iteration
038

## Structural problem (abstracted)
A canonical comparison `g^* f_* F ⟶ f'_* g'^* F` (Stacks 02KH, i=0) is **defined as the
adjoint mate** of a unit, for `Spec`-affine schemes. We must prove it is an isomorphism. Iso-ness
of the *abstract algebraic* conjugate (`conjugateIsoEquiv adjL adjR` of `gammaPushforwardNatIso`,
all four functors left adjoints) is free; the open obligation is the **coherence** equating that
abstract conjugate with the value of the geometric mate — i.e. the geometric `g^*`-counit,
conjugated by the `tilde`/`Γ` dictionaries, equals the algebraic extend/restrict counit. Stuck 5+
iters (`base_change_mate_gstar_transpose`, fed by `base_change_mate_fstar_reindex_legs_conj`).

## Failed approaches (from directive)
- Element/`ext` evaluation: `pushforwardBaseChangeMap` is defined as a transpose; any eval unfolds
  (`Adjunction.homEquiv_counit`) back to the mate form — renames the gap.
- Positional `rw`/`subst` at the locked literal: `codomain_read_legs` carried `hfst/hsnd`
  leg-equality proofs → "motive is not type correct".
- `huce` master identity + inline assembly: step-(a) reindex re-lands on the `_legs` motive wall.
- The fbc-mate-reencode.md proof-free re-cut: never executed as a "cascade"; partially executed as
  a *contained* scaffolding (see below).

## Key finding: the "risky cascade" the directive feared is ALREADY NEUTRALIZED
The directive's Q1 worry — that re-typing `codomain_read_legs` proof-free would cascade through
`_legs`, `inner_value_eq`, and everything `gstar_transpose` consumes — does **not** apply, because
the project already implemented exactly the *contained* idiom Q1 asks for:

- `base_change_mate_codomain_read_legs_param` (FlatBaseChange.lean:1427) abstracts the single
  pullback-composition factor as an explicit iso argument `Pcomp`.
- `conjPullbackFactor` (:1489) = `Adjunction.leftAdjointCompIso` of the free legs.
- `conjPullbackFactor_eq_pullbackComp` (:1520) and `pullbackComp_eq_leftAdjointCompIso` (:1198):
  the abstract factor equals the concrete `pullbackComp` (proved via
  `conjugateEquiv_pullbackComp_inv` + `conjugateEquiv_leftAdjointCompIso_inv`).
- `base_change_mate_codomain_read_legs_conj` (:1563) = `_param` at `conjPullbackFactor`
  (proof-free, no `hfst/hsnd` in its pullback factor).
- `base_change_mate_codomain_read_legs_conj_eq` (:1594): the conjugate read **equals** the concrete
  read (by `rfl` + the factor equality) — the bridge.

Consequence: `base_change_mate_codomain_read_legs` is **unchanged** (still proof-carrying), the
conjugate version lives **alongside** it, and `gstar_transpose` consumes the *no-legs*
`base_change_mate_codomain_read` (Θ_tgt) — a **different object** — so it is fully insulated. The
re-encoding is done at the def level and compiles. The single remaining sorry in the chain,
`base_change_mate_fstar_reindex_legs_conj` (:1700), is **not a re-typing cascade** — it is the
genuine conjugate-side coherence proof (conj-2a). Q1's answer is therefore: the cascade is
contained to one lemma already; nothing further to re-type.

## Analogues found (ranked by porting cost)

### Analogue: `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean` + `Mates.lean` — the conjugate-component calculus (KEEP route)
- **Domain**: composite-adjunction conjugate calculus (one shelf over alg-geom).
- **Same structural problem there**: identify the comparison of a composite of three adjunctions
  with a conjugate of a right-adjoint comparison, and discharge coherence equations among such
  comparisons without positional rewrites.
- **Technique (verified present)**: `Adjunction.leftAdjointCompIso` (hover-confirmed, signature
  `(adj₀₁)(adj₁₂)(adj₀₂)(e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) : F₀₁ ⋙ F₁₂ ≅ F₀₂`),
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv` (confirmed in CompositionIso.lean),
  `CategoryTheory.conjugateEquiv_counit_symm` (confirmed in Mates.lean). Discharge idiom:
  `obtain ⟨τ, rfl⟩ := (conjugateEquiv …).surjective τ` (lift each locked nat-trans to a free var on
  the right-adjoint side) → `apply (conjugateEquiv …).injective` → close with the reassoc conjugate
  simp set. **No positional `rw` on a locked literal**, so the `X.Modules` diamond never bites.
- **Mapping to project**: this is the route the project is ON. Remaining for `_legs_conj`:
  conj-2b `base_change_mate_reindex_conj_pullbackLeg` (UNBUILT —
  `conjugateEquiv_leftAdjointCompIso_inv` + `conjugateEquiv_pullbackComp_inv` on the isolated
  pullback leg), conj-2d `base_change_mate_reindex_conj_crossLayer` (UNBUILT — `unit_conjugateEquiv_symm`
  raised by `conjugateEquiv_comp`, survivor = the Seam-1 ρ), and the **single-`conjugateEquiv`-
  component reframing** of the section-level composite so `.injective` applies (the heaviest, risky
  step). conj-2c `base_change_mate_reindex_conj_pushforwardCollapse` (:1626) is PROVED.
- **Porting cost**: medium — but it is the *only* route to the irreducible coherence (see below).
- **Verdict**: ANALOGUE_FOUND.

### Analogue (PIVOT a): module-level direct iso via `regroupEquiv`/`cancelBaseChange`, "never form the mate"
- **Domain**: commutative-algebra base change (`Algebra.TensorProduct.cancelBaseChange`,
  `IsBaseChange`, `Module.Flat.isBaseChange`).
- **Why it does NOT bypass the coherence**: `pushforwardBaseChangeMap` is *the* target object and is
  **defined** as `homEquiv.symm(inner) = g^*(inner) ≫ counit`. The deliverable
  `pushforward_base_change_mate_cancelBaseChange` is `IsIso (Γ.map pushforwardBaseChangeMap)` — it
  must connect to that definition. Any unwinding (`Adjunction.homEquiv_counit`) returns the mate
  form (directive failed-approach #1, dead-end at :2097). Iso-ness cannot be obtained by
  "whisker an iso": the `(g^* ⊣ g_*)` counit is **not** an iso even for affine `Spec ψ`, and an
  adjunction transpose of an iso is not an iso. So in the affine case iso-ness genuinely requires
  *identifying the value* (= cancelBaseChange⁻¹), which IS the coherence. The variable-legs `subst`
  already performs the "transport to the nice `Spec(A⊗R')` apex" that this pivot would attempt, so
  there is no additional saving. **The coherence is irreducible given the definition.**
- **Porting cost**: N/A (does not bypass).
- **Verdict**: NO_USEFUL_ANALOGUE.

### Analogue (PIVOT b/c): a Mathlib/Lean geometric base-change package for pushforward of QC sheaves
- **Domain**: algebraic geometry / sheaves of modules.
- **Finding (searched)**: ABSENT. `lean_leansearch` for "base change map pushforward pullback
  quasi-coherent sheaf isomorphism flat" returns only **module-level** results
  (`Module.Flat.isBaseChange`, `RingHom.Flat.isStableUnderBaseChange`,
  `KaehlerDifferential.tensorKaehlerEquiv`) and unrelated `SheafOfModules.pushforwardCongr`.
  `SheafOfModules.pushforward` search is empty. There is no standalone `BeckChevalley` namespace
  (per fbc-mate-reencode.md, the only carrier is `iterated_mateEquiv_conjugateEquiv`, which needs
  **all four functors left adjoint** — the *geometric* square has pushforward = right adjoint, so it
  does **not** apply; that is exactly why the general base-change map needs flatness). No Lean
  formalization of Stacks 02KH exists to port. Mathlib stops at module-level `cancelBaseChange`.
- **Porting cost**: N/A (does not exist).
- **Verdict**: NO_USEFUL_ANALOGUE.

## Top suggestion
**KEEP** — finish the conjugate re-encode; there is no route that bypasses the mate coherence
(PIVOT a is blocked by the definition; PIVOT b/c do not exist in Mathlib or any Lean project). The
cascade risk Q1 feared is already neutralized by the `_param`/`_conj`/`_conj_eq` scaffolding, so the
bounded remaining work is the *proof* of `base_change_mate_fstar_reindex_legs_conj` (:1700), not any
re-typing. Concrete plan, lowest-risk ordering:
1. Build conj-2b `base_change_mate_reindex_conj_pullbackLeg` standalone (diamond-free; just
   `Adjunction.conjugateEquiv_leftAdjointCompIso_inv` + `Scheme.Modules.conjugateEquiv_pullbackComp_inv`
   on the isolated leg — both confirmed present).
2. Build conj-2d `base_change_mate_reindex_conj_crossLayer` standalone (Seam-1 template:
   `unit_conjugateEquiv_symm` raised one functor layer by `conjugateEquiv_comp`).
3. Then attempt the single-`conjugateEquiv`-component reframing of the section composite and close
   `_legs_conj` by `.injective` + the reassoc conjugate simp set + conj-2b/2c/2d. Once `_legs` is
   axiom-clean, `gstar_transpose` can **cite** `base_change_mate_fstar_reindex` for step (a) instead
   of reproving inline (its inline-reproof comment at :2089 is conditioned solely on `_legs` being
   sorry-backed); step (b) is already proved (`base_change_mate_extendScalars_inner_value_counit`)
   and `huce` is assembled, leaving only the dictionary cancellation.

**Two strategic caveats the planner must weigh (these temper the KEEP, but no pivot avoids them):**
- *The reframing in step 3 is the genuine risk.* If it resists one more focused iter after conj-2b/2d
  are in hand, that is the real tripwire — but escalation means "accept a documented `sorry` / change
  the deliverable scope", NOT "switch routes", because no alternative route exists.
- *`gstar_transpose` is necessary but NOT sufficient for the headline theorem.*
  `affineBaseChange_pushforward_iso` (:2317) has a **second, independent** sorry at :2348 — the affine
  *reduction* (arbitrary cartesian square → affine charts, plus section-level→sheaf-level), described
  in-file as "multi-hundred-LOC, Mathlib-absent". This is comparable in size to the whole coherence
  grind and is untouched. The planner should not treat closing the section coherence as "finishing
  affine base change". If iteration budget is the real constraint, the higher-leverage open question
  is whether the :2348 reduction has a cheaper Mathlib-backed path (restriction-compatibility of
  `pushforwardBaseChangeMap` along affine opens) — a separate api-alignment query worth dispatching.
</content>
</invoke>
