# Project Status

This file was reset on extraction into the **Line-Bundle Comparison Iso**
subproject. The parent's accumulated iteration narrative (iter-099…iter-303,
much of it about files now out of scope) was dropped; this subproject's own
`archon` run regenerates status as it makes progress. Per-iter narrative lives
in `iter/iter-NNN/review.md`; this file carries the cumulative Knowledge Base only.

Current scope and live state live in [`PROGRESS.md`](PROGRESS.md) and
[`STRATEGY.md`](STRATEGY.md). Summary:

- **Seeds:** `lem:pullback_tensor_iso_loctriv`, `lem:dual_isLocallyTrivial`,
  `thm:rel_pic_addcommgroup_via_tensorobj` (108-node cone).
- **Open targets (post iter-017):** TensorObjSubstrate.lean GREEN, 2 sorries —
  `exists_tensorObj_inverse` (L719, import-cycle, deferred) and `pullbackTensorMap_restrict`
  (decl L3144; residual `hcore2` at L3626). Steps (i) [iter-015], (ii) [iter-016 `sheafifyMap_δcomp_split`],
  and (iii)-a/b.1/b.2 [iter-017, the S1^h slide + prefix-cancel + slide-of-V] all CLOSED+spliced. **Residual
  = `hcore2` only:** the folded Sq3/Sq4 **presheaf** identity (D1′-level chase). Sq3/Sq4 are NOT built
  standalone (`sheafifyTensorUnitIso_comp`/`pullbackValIso_comp` are orphaned blueprint targets, merged
  into `hcore2`). `sheafificationCompPullback_comp_tail`/`_comp`/`_comp_natTrans`/`hδ` CLOSED iter-006.
  **DualInverse/SliceTransport.lean GREEN, 0 sorries — DUAL route CLOSED** (`sliceDualTransport` incl.
  left_inv/right_inv proved, axiom-clean). Full chain builds green together.
- **Stage:** prover.

## Knowledge Base

### Proof Patterns (reusable across targets)
- **Unit-naturality fold + generic-`exact` device (the D3′ Sq4 leaf unblock — CLOSED iter-019):** for a
  goal carrying leading sheafification units (`η`) + `forget` over the `SheafOfModules` carrier, apply
  `η` unit naturality on EACH leg to factor out a common leading `η ≫ forget(·)`, collapsing to a clean
  carrier-level cocycle. Then `slice_lhs`/`slice_rhs` to align and `exact comp_forget_cocycle (forget …) …`
  — a generic single-`[Category C]` lemma applied by `exact` (the documented instance-crossing device:
  `rw`/`simp`/`erw`/`reassoc_of%` ALL whnf-bomb on the `Sheaf.val`↔`ObjectProperty.obj` deprecated-alias
  defeq boundary, even plain `Category.assoc`/`← Functor.map_comp`). ⚠ pass `forget` EXPLICITLY (else
  "typeclass instance problem is stuck"). Sub-coherences likewise as generic helpers by `exact`:
  `inv_telescope` (3-pair iso telescope, replaces failing `simp`), `cocycle_assemble` (cocycle skeleton).
  The (T) adjunction triangle `L.map(η ≫ R k) ≫ ε = k` is cleanest as the TERM `(adj.homEquiv P M).left_inv k`
  (NOT `left_triangle_components`/`homEquiv_unit` rewriting). Name-clash: bare `Functor.map_id` in `rw` can
  hit the Haskell `Functor` → use `CategoryTheory.Functor.map_id`. `set b := …` to localize a `pullbackValIso`
  unfold so `simp only [pullbackValIso, Iso.trans_hom, …]` rewrites only the targeted legs.
- **Composite-adjunction cocycle at the NatTrans level (the D3′ keystone — CLOSED iter-006):** prove
  the whole-transformation equation, NOT the `.app P` component — the dependent `eqToHom`/reindex junk
  that blocks every `rw` exists ONLY post-`.app`. Build it from `Adjunction.leftAdjointCompNatTrans_assoc`
  (Mathlib `CompositionIso.lean`) instances with outer comparisons trivialized via `conjugateEquiv_symm_id`;
  evaluate `.app P` exactly ONCE at the end. To close a *consumer* (`comp_tail`): take the `P`-component
  of the NatTrans lemma (= the caller's statement), transpose FORWARD via `homEquiv`, and replay the
  caller's reduction script **`at` the hypothesis** (not the goal). Mirrors the project's own working
  `pullbackObjUnitToUnit_comp`. Recipe: `analogies/d3cocycle006.md`.
- **`erw` for cross-elaboration / `Sheaf.val`-spelled / `show`-pinned rewrites (D3′ region):** a term
  elaborated standalone (e.g. simp lemma `J1`, a `show`-pinned `δfh`) carries a hidden instance-level
  defeq mismatch with the same term elaborated inside a `leftAdjointCompNatTrans_assoc` paste —
  `rw`/`simp only` silently no-op (watch for the unused-simp-arg warning); `erw` defeq-matches. The
  leftover `𝟙`-junk sits at a defeq-but-not-syntactic object spelling, so `Category.id_comp` also needs
  `erw`. ⚠ `erw [Functor.map_comp]` on an oplax `δ` catastrophically UNFOLDS it into its mate expansion —
  never. To fold instead, `rw [← Functor.map_comp]` (explicit `aZ.map _ ≫ aZ.map _` heads match) then
  `exact congrArg aZ.map …`. Pre-elaborate context-sensitive instances (`IsLocallyInjective (𝟙 …)`)
  via a private abbrev (`sheafifyIdOf`) so a multi-scheme statement doesn't re-run synthesis.
- **Thin-poset `subsingleton` close (dual-valued only):** an `isoMk` naturality square whose
  connecting Hom-space is *dual-valued* (maps into the unit) over a thin poset (`Opens Y`) is a
  `Subsingleton`; `subsingleton` closes it in one line (e.g. `dual_restrict_iso` isoMk naturality,
  DualInverse ~L786). ⚠ It does NOT close a square whose codomain is a *restriction of the unit*
  (`sliceDualTransport.naturality` L553, `sliceDualTransportInv.naturality` L407) — that codomain is
  not a Subsingleton; `subsingleton` errors `could not synthesize Subsingleton (… ⟶ …)`. The two
  cases look identical but differ in codomain. Verify the instance is genuine (not sorry-induced)
  before trusting an opaque `subsingleton`; prefer `exact Subsingleton.elim _ _`.
- **Slice-transport naturality via pointwise `_apply` rotation (CONFIRMED iter-007 — closed the
  forward `sliceDualTransport.toFun.naturality`; OVERTURNS the old `restrictScalarsLaxε` recipe):**
  the naturality field reduces (via `intro …; apply ModuleCat.hom_ext; refine LinearMap.ext fun z => ?_`)
  to a pointwise ε-commutation equation. Do NOT close it with a `restrictScalarsLaxε` natTrans (the
  prover never found/used one). Instead: (1) EXTRACT a standalone sorry-free lemma
  `sliceDualTransport_naturality_apply` — the parent def is at its heartbeat limit, so it cannot be
  proved inline; (2) close the square pointwise via `appIso_hom_naturality_apply` (ring-level
  naturality of `(f.appIso).hom`) + `dualUnitRingSwap_apply`/`dualUnitRingSwapHom_apply` (the `inv ε`
  legs evaluated WITHOUT `whnf`) + `PresheafOfModules.naturality_apply` of the dual section at the
  `f`-image of `f₁`; (3) delegate the field to it. The inv direction (`sliceDualTransportInv`) is the
  mirror — same extraction, plus `unitRelabelSwap` for the codomain unit and the `hβ` ring-compat
  hyp discharged by `Iso.hom_inv_id`. ⚠ Applying `inv ε` pointwise through `whnf` reproduces the
  ≥6-iter deterministic-timeout (seen again iter-007) — always route through the proven `_apply` lemmas.
- **Composite-adjunction-unit cocycle (do not fine-grain):** `sheafificationCompPullback_comp_tail`
  is an irreducible mate-assembly; whiskered comparison factors (`(pullback h)`-whiskered /
  `forget`-wrapped) expose no `homEquiv` head for `leftAdjointUniqUnitEta_app`. Consume the staged
  `hwr` (`conjugateEquiv_whiskerRight`) via the surjective/injective reduction of
  `leftAdjointCompNatTrans_assoc` (`CompositionIso.lean:155`), mirroring Mathlib's
  `SheafOfModules.pullback_assoc`. ~40–60 LOC; a cross-domain escalation, not a helper round.
- **Unit-swap pointwise helper:** `dualUnitRingSwap_apply` proves
  `(dualUnitRingSwap f W').hom x = (Scheme.Hom.appIso f W').hom.hom x` by composing with the inverse
  appIso map and using injectivity + `hom_inv_id`. Use this helper rather than unfolding the lax unit
  inside large structure fields.
- **Reassociate mate-morphism composites at the NatTrans level, NEVER at `.app` level (iter-014):** the
  `.app` of a `mateEquiv`/`leftAdjointUniq` iso composite is a non-canonical `CategoryStruct.comp` —
  `Category.assoc` cannot key-match it (`rw` "did not find", `simp only` "no progress") and `erw` crosses
  it only by whnf-unfolding the mate machinery, which deterministically bombs (3.2M heartbeats) after a
  few crossings. Move the reassociation BEFORE `.app` (work with the NatTrans/`_comp_natTrans` form) where
  the composite is canonical, then evaluate `.app` exactly once. Same lesson as the D3′ cocycle keystone.
  Also: `rw [lemma]` ≠ `erw [lemma]` when the lemma RHS pretty-prints identically to the goal but carries
  a hidden defeq instance — only `erw` splices (D3′ `erw [h1]`).
- **Strip a `restrictScalars` functor wrapper by defeq (iter-014):** use `erw`/`show` to see through
  `(restrictScalars g).map h |>.hom x = h.hom x`, NOT `rw [ModuleCat.restrictScalars.map_apply]` (the
  latter is pattern-fragile and "did not find pattern"; it was the DUAL `left_inv` L890 bug).
- **D3 associativity scaffold:** For `sheafificationCompPullback_comp`, instantiate
  `Adjunction.leftAdjointCompNatTrans_assoc` with `τ012`/`τ013` identity-shaped forget/pushforward
  comparisons, `τ123 = SheafOfModules.pushforwardComp.inv`, `τ023` the forget-whiskered
  `PresheafOfModules.pushforwardComp.inv`, and `hτ := by ext A; rfl`. Pin pushforward universes as
  `.{u}`; `Adjunction` has no `.right`/`.rightAdjoint` projection.

- **Cross a defeq-but-not-syntactic instance boundary by a generic single-instance lemma + `exact`
  (iter-015 — CLOSED D3′ step (i), the wall of iters 012–015; OVERTURNS the iter-014 "refactor to NatTrans
  level" prescription):** when two morphisms join through a `CategoryStruct.comp` whose two sides carry
  defeq-but-spelled-differently instances (the `Scheme.Modules`-vs-`SheafOfModules` / `pullback φ_{h≫f}`-vs-
  `pullback(φf≫wh)` family), NO `rw`-based reassociation key-matches the boundary and `erw [Category.assoc]`
  whnf-unfolds the `mateEquiv`/`TwoSquare` guts and bombs (3.2M heartbeats). FIX: state the
  reassociation/cancellation as a GENERIC single-instance lemma (`comp_cancel_mid`:
  `(r0≫r1≫r5≫d)≫e≫rest = r0≫r1≫r5≫rest` given `d≫e=𝟙`, proved by plain `Category.assoc`) and discharge the
  concrete mixed-instance goal by **`exact`** (defeq unification) — NOT `rw`/`erw`. Also: to make `rw [h1]`
  fire when the lemma-applied instance differs from the goal's, re-state `h1` as `h1'` with a freshly
  elaborated type accepted up to defeq (`have h1' : <LHS verbatim> = <RHS verbatim> := h1`). Then splice the
  packaged brick by `erw [reassoc_of% hmain]`. This is the general tool for any further instance-boundary
  cancellation in the D3′ four-square merge.
- **Inline multi-field `≃ₗ`/structure defs need a raised `maxHeartbeats` (iter-015):** a `(deterministic)
  timeout at elaborator/whnf` on a six-field `≃ₗ` def — even with a *sorry* field present — is a heartbeat
  budget issue (`set_option maxHeartbeats 1600000 in`), NOT a proof gap. Was the real (mis-diagnosed) blocker
  of DUAL `right_inv`. Also the `(Y ≫ e.inv) ≫ e.hom = Y` CommRingCat-composition quirk (both `rw` and
  `simp [Category.assoc, Iso.inv_hom_id]` no-op): close term-mode via
  `(Category.assoc _ _ _).trans ((congrArg (Y ≫ ·) e.inv_hom_id).trans (Category.comp_id _))`; and prefer the
  targeted `rw [eqToHom_map F.op pf]` over `simp only [eqToHom_map]` (which over-collapses sibling factors).

- **`comp_δ` of a composite of oplax functors is DEFINITIONAL (iter-016):** the
  `Functor.OplaxMonoidal.comp` instance sets `δ(F⋙G) := G.map(δ F) ≫ δ G` definitionally, so an
  `a.map (δ (F⋙G) M N)` split closes by `rw [← Functor.map_comp]; congr 1` — `congr 1` finishes by `rfl`,
  no `Functor.OplaxMonoidal.comp_δ` lemma invocation (writing `exact comp_δ …` there is redundant, "No
  goals"). ⚠ Never `erw [Functor.map_comp]` on an oplax δ — it unfolds the mate (catastrophic). To fold,
  `rw [← Functor.map_comp]` (explicit `a.map _ ≫ a.map _` heads match). Stated as `sheafifyMap_δcomp_split`.
- **`reassoc_of%`-splicing a defeq-proved `have` needs the goal-VERBATIM LHS spelling (iter-016):** a slide
  `have hslide := (…naturality …).symm` typechecks against a hand-written goal-spelling type by defeq, but
  `rw`/`erw [reassoc_of% hslide]` then reports `Did not find an occurrence of the pattern` if the goal's
  actual spelling differs (`((F).app P).hom` vs `F.hom.app P`; `Functor.comp_map`-unfolded `G.map(F.map ·)`
  vs `(F⋙G).map ·`). FIX: extract the live goal (forced type-mismatch `exact (rfl : (0:Nat)=0)`) and copy
  the LHS verbatim into the `have`'s type. Do not hand-spell from the naturality lemma's pretty-print.
- **The `comp_cancel_mid`+`exact` device is a FAMILY — the general tool for the whole D3′ merge (iter-017,
  SPLICED steps iii-a/b.1/b.2):** to cross the `SheafOfModules`-vs-`Scheme.Modules` defeq-but-not-syntactic
  instance boundary that whnf-bombs EVERY `simp`/`rw`/`erw` (incl. `reassoc_of%`), state the move as a
  generic single-`[Category C]` lemma whose conclusion MIRRORS the goal's literal `≫`-nesting, and apply it
  by `refine`/`exact` (assignment-only unification). Four landed (`comp_slide_nested` = buried-pair slide;
  `comp_cancel_three_lr` = 3-prefix L/R cancel, leaf defeqs by `rfl` as args — no big-composite whnf;
  `comp_slide_three` = slide-then-cancel skeleton; `map_comp_slide` = merge-then-slide over an abstract
  functor `G`). The associativity/`map_comp` algebra runs on CLEAN ABSTRACT VARS inside the lemma, never on
  the concrete goal. The math content lives in the hypotheses (`hslide`/`hcomb`/`hcore`) passed in, so the
  lemmas are blueprint-EXEMPT (instance-plumbing, like `comp_cancel_mid`). Two concrete gotchas: `⊗ₘ` on a
  `Sheaf.val` carrier can't synthesize the monoidal instance — pin `(C := PresheafOfModules …)`; and
  `a.map_comp _ _` (defeq `exact`) folds `a.map x ≫ a.map y` where `rw [Functor.map_comp]` reports "did not
  find pattern" (the `≫` lives in the `forget₂`-carrier instance).
- **`hcore2` — the folded Sq3/Sq4 presheaf core: CLOSED iter-018.** Fold both sides into ONE `a_Z.map Ψ`
  (`sheafifyTensorUnitIso_hom_eq'` for the S3 legs) via the NEW generic merge lemma **`map_comp4_eq_comp5`**
  (4-vs-5 `F.map`-fold; `refine`, NOT `rw [← Functor.map_comp]` which no-progresses on the `SheafOfModules`
  instance) → presheaf eqn `Ψ_L=Ψ_R` over Z. Close by: a **CONCRETE fully-applied** `have hδnat := δ_natural
  F u v` (OplaxMonoidal instance pinned ONCE via `show … from`; `presheaf_pullback_oplaxmonoidal`) spliced by
  `erw [← reassoc_of% hδnat]` — ⚠ the metavar `erw [reassoc_of% δ_natural]` whnf-times-out (3.2M heartbeats);
  then `congr 1` cancels the shared `δ_h` head; then the NEW generic **`tensorHom_collapse_3_4`** (3-vs-4
  bifunctorial `tensorHom` collapse, `refine` — `simp/rw [tensorHom_comp_tensorHom]` no-progress on the
  non-canonical monoidal instance) → two per-leg identities = `pullbackValIso_comp_leg`.
- **Generic-lemma + `refine`/`exact` is the UNIVERSAL instance-boundary device (now 5-deep across the merge):**
  `comp_cancel_mid`, `comp_slide_nested`/`comp_cancel_three_lr`/`comp_slide_three`/`map_comp_slide` (iter-017),
  `map_comp4_eq_comp5`, `tensorHom_collapse_3_4` (iter-018). State the fold/cancel/collapse as a generic
  single-`[Category C]`/`[MonoidalCategory C]` lemma whose conclusion MIRRORS the goal's literal `≫`-nesting;
  apply by assignment-only unification. Algebra runs on clean abstract vars; math lives in the passed
  hypotheses; all are blueprint-EXEMPT plumbing. Pin `(C := PresheafOfModules (… ⋙ forget₂ …))` for `⊗ₘ`/
  monoidal carriers.
- **Carrier-instance trap (iter-018):** content in the `PresheafOfModules X.ringCatSheaf.obj` carrier CANNOT
  be lifted to a top-level lemma — its `MonoidalCategoryStruct`/`MonoidalCategory` are only synthesizable in
  the `… ⋙ forget₂` spelling, and the in-place proof's `letI := inferInstance` bridges can't live in a
  signature. Keep such reductions in-place. (Killed the `pullbackTensorMap_restrict_core` extraction.) iter-020
  confirms the wall also blocks `Functor.Monoidal.transport` (it needs a functor-level `.Monoidal` instance
  mentioning the non-synthesizable carrier) → see K1 blocker below.
- **D4′ chart-chase to promote a comparison map to an iso (iter-020 — seed-1 assembly):** to show a global
  comparison `δ^f(M,N)` is iso for locally-trivial `M,N`: cover `Y` by `{f⁻¹W y}` for common trivialising
  affine charts `W` (`exists_isAffineOpen_mem_and_subset` + `restrictIsoUnitOfLE`), reduce by
  `isIso_of_isIso_restrict`, then per-chart use the D3′ base-change identity (`pullbackTensorMap_restrict`)
  on BOTH factorisations of `j' ≫ f = g ≫ W.ι` and isolate the wanted middle factor with a generic
  `isIso_of_isIso_comp4_mid` (composite-hyp FIRST, iso proofs as explicit args). ⚠ Nat-iso inverse
  components `(pullbackComp _ _).inv.app T` are NOT found by `inferInstance` → `inferInstanceAs (IsIso
  (((pullbackComp _ _).app T).inv))`; `IsIso (a≫b≫c≫d)` is not auto → chain `IsIso.comp_isIso'`. The
  flanking factors are comparisons along the OPEN-immersion chart inclusions, so the chase bottoms out on
  the open-immersion δ-iso (K1), NOT directly on the unit pair — the unit-pair case (`...unit_isIso` via
  `pullbackTensorMap_natural`) only handles trivial-base modules (helper K2 `...isIso_of_base_unit`).
- **Presheaf-δ-iso via strong-monoidal mate witness (the K1 scaffold — iter-021, PARTIAL):** to show
  `IsIso (Functor.OplaxMonoidal.δ (pullback φ') M.val N.val)` for an open immersion (dodging the
  monoidal-carrier diamond): (STEP A) `apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta` then close the
  sheafify wrapper with `exact Functor.map_isIso _ (…δ…)` — ⚠ pass the `δ` term EXPLICITLY (`[IsIso f]` else
  becomes a metavar); need `haveI hRA : (pushforward φ').IsRightAdjoint` in scope; `δ` only elaborates with a
  fully type-annotated `letI φ' : … := (f.toRingCatSheafHom).hom`, BUT the outer instance must register against
  the LITERAL `(f.toRingCatSheafHom).hom`, not the let-var (zeta mismatch). (STEP B) mirror
  `tensorObj_restrict_iso`: `H1 : pushforward β ≅ pullback φ'` (`hadj.leftAdjointUniq (pullbackPushforwardAdjunction φ')`),
  upgrade `pushforward β` strong-monoidal (`restrictScalarsMonoidalOfBijective`, `β` = sectionwise `f.appIso⁻¹`),
  witness `e := (H1.app (M⊗N)).symm ≪≫ μIsoβ.symm ≪≫ tensorIso (H1.app M) (H1.app N)`; `rw [hcompat]; exact e.isIso_hom`.
  `hcompat : δ = e.hom` transposes by `rw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]`
  then `unit_leftAdjointUniq_hom_app`. Residual leaf = the two-monoidal-structures reconciliation (see Known Blockers).

### Known Blockers (do not retry without a structural change)
- **K1 `pullbackTensorMap_isIso_of_isOpenImmersion` residual `hcompat` (L4219, OPEN iter-021):** the scaffold
  (above) reduces it to the strong-monoidal mate compatibility — `μIsoβ.inv` (strong tensorator of `pushforward β`)
  = the `hadj`-mate of `μ (pushforward φ')`; equivalently `presheafPushforwardLaxMonoidal φ'` agrees through `hadj`
  with `rightAdjointLaxMonoidal hadj` (= `(Adjunction.leftAdjointOplaxMonoidal hadj).δ = μIsoβ.inv`). ⚠ Do NOT
  `prove`-pass it (not a tactic-search gap) and do NOT retry functor-level `Functor.Monoidal.transport` (carrier
  diamond, dead 4×). `Adjunction.IsMonoidal.leftAdjoint_μ` CANNOT fire (μ only at pushed-forward objects `G X, G Y`,
  not arbitrary `M.val, N.val`); `instIsMonoidal hadj` gives only the mate lax structure, not the project's explicit
  composite. Route: `mathlib-build`/`effort-breaker` on the named reconciliation lemma (likely via
  `laxMonoidalEquivOplaxMonoidal` + `natTransIsMonoidal_of_transport`). δ-side analogue of D2′ `presheafUnit_comp_map_eta`.
- ~~**`DualInverse.lean` is RED**~~: RESOLVED iter-007 (repaired to GREEN + split into
  `DualInverse/SliceTransport.lean`; forward naturality then closed). The DUAL chain is now an
  ordinary proving task, not a regression. Dead approaches that remain DEAD: `ext z`+`exact hφ z`
  (applies an equality as a function); pointwise `ext z; simp [dualUnitRingSwap_apply]` / any
  `inv ε` through `whnf` (the ≥6-iter deterministic-timeout, reproduced again iter-007). Use the
  pointwise `_apply` rotation pattern above instead.
- ~~`pullbackTensorMap_restrict` (D3′ outer)~~: **BODY CLOSED iter-018** (steps i@015, ii@016,
  iii-a/b.1/b.2@017, hcore2@018; recipe in the `hcore2` Proof-Pattern entry above). Sorry-free in its own
  body; delegates its sole residual by `exact` to the leaf brick `pullbackValIso_comp_leg`. ⚠ Do NOT
  re-assign the standalone extraction `pullbackTensorMap_restrict_core` — it does NOT elaborate at top level
  (carrier-instance trap above); content is realized in-place, its blueprint `\lean{}` pin was dropped.
- ~~`pullbackValIso_comp_leg` (blueprint `lem:pullback_val_iso_comp`, Sq4)~~: **CLOSED iter-019,
  axiom-clean** (`propext, Classical.choice, Quot.sound`; no `sorryAx`). The 5-iter wall broke via the
  **unit-naturality fold** (Proof Pattern below): `η^Z` naturality on both legs factors out a common
  `η ≫ forget(·)` → clean carrier-level cocycle `hH` → `slice` folds + `exact comp_forget_cocycle …`;
  `hH` via Sq4a inverse (`inv_telescope`) + `pullbackComp` naturality at counit + (T) triangle
  `(adj.homEquiv …).left_inv`. The ENTIRE D3′ comparison-iso cone is now sorry-free. Do NOT re-open.
- ~~`sliceDualTransport` left_inv / right_inv~~: **BOTH CLOSED (left_inv iter-014, right_inv iter-015).**
  `sliceDualTransport` is now sorry-free + axiom-clean; the **DUAL route is CLOSED** (verified green, full
  chain 8322 jobs). right_inv = 3-step mirror of left_inv (ring-identity collapse via
  `appIso_inv_naturality` → ψ-naturality `hψ` → `Y.presheaf` round-trip `hmaps`); the real blocker turned
  out to be a heartbeat overflow, not a math wall (see Proof Patterns). Retire the DUAL lane.
- `exists_tensorObj_inverse` (L734): import-cycle — closes downstream via a refactor-MOVE downstream of
  DualInverse (RelPicFunctor sole consumer), never by direct in-place assignment.
- **`pullbackTensorMap_isIso_of_isOpenImmersion` (K1, L4172) — open-immersion δ-iso (iter-020):** the
  sole open D4′ brick. Do NOT retry the in-file `Functor.Monoidal.transport` route: it fails on two
  Mathlib-absent instance diamonds — (1) `MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)` not
  globally synthesizable (carrier keyed on syntactic `X.presheaf ⋙ forget₂`, only defeq — the standing
  monoidal-carrier wall, now at FUNCTOR level), (2) goal `δ` = `presheafPullbackOplaxMonoidal` (adjunction
  mate) vs `transport.toOplaxMonoidal.δ` (via `coreMonoidalTransport`) not defeq → no `transport_δ` bridge.
  The math is settled (object-level fact CLOSED in `tensorObj_restrict_iso`); missing piece = a
  functor-level strong-monoidal pullback model = Mathlib-scale. Route to mathlib-analogist/mathlib-build;
  ingredient in `informal/pullbackTensorMap_isIso_of_isOpenImmersion.md`.
- ~~`sheafificationCompPullback_comp_tail`~~ / ~~`_comp`~~: CLOSED iter-006 (NatTrans-cocycle pattern above).
- `sliceDualTransport.naturality`: CONFIRMED iter-007 — do NOT inline the elementwise proof in the
  monolithic `LinearEquiv` (it closes in isolation but pushes later fields past heartbeat limits).
  Factor into a standalone helper (`sliceDualTransport_naturality_apply`) and call it from the field.
  The forward direction is now CLOSED this way; the inv-naturality root (L444) awaits the same mirror.
- `sheafificationCompPullback_comp`: do not retry raw `aesop_cat`, reassociation, `← Functor.map_comp`,
  or sectionwise `hom_ext`. The remaining blocker is the mixed comparison
  (`sheafificationCompPullback h` followed by sheafified `PresheafOfModules.pullbackComp.hom`) and
  functor-associator cleanup.

### Extraction mechanics (non-obvious gotchas)
- **Confirmed truncation bug:** the extraction's Lean-decl remover truncated DualInverse.lean's
  entire §C tail mid-`/-- … -/` docstring, committing a non-compiling file (`unterminated comment`)
  that broke the whole downstream cone. The parent repo
  `/home/archon/FormalizationProjects/Algebraic-Jacobian-Challenge/` is the last-known-good source
  of truth: diff the byte-identical prefix and restore the lost tail. **Other extracted files may be
  similarly truncated — worth a one-shot sweep.**

## Last Updated
2026-06-18T10:25:00Z (iter-021 review — K1 scaffolded; session narrative in `iter/iter-021/review.md`,
Knowledge Base updated above with the presheaf-δ mate-witness pattern + the `hcompat` blocker.)

2026-06-18T09:15:00Z (iter-020 review — **D4′ CHART-CHASE BUILT**: seed-1 `pullbackTensorIsoOfLocallyTrivial`
has a sorry-free chart-chase body (5 new decls; `isIso_of_isIso_comp4_mid` + K2 axiom-clean). Sole open D4′
residual = K1 `pullbackTensorMap_isIso_of_isOpenImmersion` (L4172) — `Functor.Monoidal.transport` route hit
the functor-level monoidal-carrier wall (pre-authorized reversal signal) → mathlib-analogist/mathlib-build,
NOT a retry. File sorry 2→2 (K1 + deferred terminal). aud020 0 must-fix/2 major (stale .lean comments→next
prover). tos020 1 must-fix = blueprint omits the K1 node + wrong "only D3′ is new" claim→blueprint-writer.
Stale `% NOTE:` on loctriv block rewritten (pin now resolves). gaps=0, unmatched=108, sync +2 (711be2f),
doctor clean. Next: unblock K1 + add its blueprint node; terminal `exists_tensorObj_inverse` MOVE.)

(iter-019 — **D3′ CONE CLOSED**: `pullbackValIso_comp_leg` (the 5-iter-stuck
Sq4 leaf) CLOSED + axiom-clean via the unit-naturality fold + generic-`exact` device (5 new non-vacuous
`private` helpers: `comp_forget_cocycle`, `inv_telescope`, `cocycle_assemble`,
`sheafificationCompPullback_comp_inv`, `adj_unit_map_counit`). sorry 2→1 (sole remaining =
`exists_tensorObj_inverse`, import-cycle deferred). File GREEN 8321 jobs. aud019 PASS (both leaf +
`pullbackTensorMap_restrict` axiom-clean, helpers used; 3 stale `.lean` comments → next prover). tos019
PASS (signature + proof match blueprint; scpb pinned to `sheafificationCompPullback_comp_inv`; counit
NOTE corrected). `archon dag-query gaps`=0 ∞-holes. sync +2 `\leanok` (023f2ca). dag unmatched 105.
Next iter = PIVOT to downstream consumers `pullbackTensorIsoOfLocallyTrivial` → `pullback_tensorObj_iso`
→ chain to `exists_tensorObj_inverse` (consuming file).
clean convergence test on the brick; effort-breaker if it stalls. exists_tensorObj_inverse untouched.)
