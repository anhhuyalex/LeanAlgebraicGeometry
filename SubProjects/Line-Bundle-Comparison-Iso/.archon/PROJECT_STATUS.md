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
- **Conjugate-telescope CLOSED Bridge B2 (iter-050) — the leg-by-leg recipe, fully landed.** Confirms the
  iter-049 prediction (`mateEquiv_hcomp`/`vcomp` NOT needed). To prove a NatTrans equality between two left
  adjoints of a common right adjoint G whose RHS chain has fixed `(C,D)`: `apply (conjugateEquiv (pPA …)
  (rA …)).injective`; collapse the LHS to `𝟙` with the keystone **`conjugateEquiv_restrictFunctorIsoPullback_hom`**
  (`conjugateEquiv … (leftAdjointUniq …).hom = 𝟙`, itself proved by `Equiv.apply_eq_iff_eq_symm_apply` +
  `simp only [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq, conjugateIsoEquiv_symm_apply_inv,
  Iso.refl_inv]`); then **N explicit `← conjugateEquiv_comp` splits** through the intermediate adjunctions
  G₀..G₆ (Lean can't infer the middle adj₂ — thread each explicitly); rewrite each leg with its
  pushforward-world value (comp legs ↦ `conjugateEquiv_restrictFunctorComp_inv` / `conjugateEquiv_pullbackComp_hom`;
  whisker legs c₃/c₄ ↦ `conjugateEquiv_whiskerRight/Left` + the LHS keystone + `Functor.whisker{Left,Right}_id'`;
  congruence legs c₁/c₆ ↦ `conjugateEquiv_reindexCongr` = `subst h; simp only [pullbackCongr, eqToIso_refl,
  conjugateEquiv_id, Iso.symm_hom]; convert conjugateEquiv_id …; ext; simp`); cancel the `pushforwardComp`
  hom/inv pair with `Iso.inv_hom_id_assoc`; finish with `conjugateEquiv_reindexCongr`. Build EXIT 0,
  axiom-clean (both auditors confirmed). The `pushforwardComp_reindex_telescope` "5th lemma" was done INLINE,
  never extracted (its blueprint `\lean{}` is dangling).
- **`conjugateEquiv` distributes LEG-BY-LEG when the whole comparison chain has fixed `(C,D)` (iter-049,
  the B2-helper/B1-crux telescope recipe — supersedes `b2mate045.md`):** when proving a NatTrans identity
  between two left adjoints of a common right adjoint, where EVERY intermediate functor in the RHS chain
  lives over the SAME `(C,D)` (here `X.Modules ⥤ V.Modules`), apply `conjugateEquiv`-injectivity onto the
  shared right adjoint, then distribute the conjugate **leg-by-leg via `← conjugateEquiv_comp`** through the
  explicit intermediate adjunctions — `mateEquiv_hcomp`/`mateEquiv_vcomp`/`iterated_mateEquiv_conjugateEquiv`
  are **NOT needed** (the b2mate045 hcomp plan was wrong). Per-leg conjugate targets are all existing lemmas:
  composition-comparison legs ↦ `conjugateEquiv_restrictFunctorComp_inv` (restrict) / inverse of
  `conjugateEquiv_pullbackComp_inv` (pullback); whisker legs ↦ `unit_leftAdjointUniq_hom_app`; congruence
  (eqToHom/`*Congr`) legs ↦ `pushforwardCongr`/eqToHom. The product telescopes to `𝟙` (comp·comp⁻¹ cancel;
  congruences cancel against the reindex). Lean can't infer the intermediate adj₂ from a bare `rw` — thread
  each `← conjugateEquiv_comp` split explicitly (~60–100 LOC bookkeeping, no missing ingredient). To reduce
  the `.hom.app A` statement to the bare NatTrans identity first: `have hNat … := …; have happ := congr_app
  hNat A; simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using happ`.
- **Carrier-diamond map-level finish: `rw [helper, Functor.map_comp ×N] + rfl`, NOT `congrArg (F).map`
  (iter-049):** to discharge a `(pushforward V.ι).map (LHS) = (pushforward V.ι).map (RHS)` goal across the
  heavy sheafification-laden `pushforward` carrier diamond, use `congr 1` (cancel the shared unit prefix)
  then `rw [<hom-level helper>, Functor.map_comp, …×N]; rfl`. `exact congrArg (pushforward V.ι).map (helper …)`
  blows the recursion/whnf depth limit on the heavy functor. (Pairs with `unit_leftAdjointUniq_hom_app.symm`
  to replace `pullbackPushforwardAdjunction.unit` by `restrictAdjunction.unit ≫ pushforward.map (…)`.)
- **Restrict-side conjugate-of-composition via ABSTRACT `leftAdjointCompIso` instantiation (iter-048,
  closes `conjugateEquiv_restrictFunctorComp_inv`):** to prove `conjugateEquiv adj_comp adj_fg
  (restrictFunctorComp f g).hom = (pushforwardComp f g).hom` — the restrict-world mirror of Mathlib's
  `conjugateEquiv_pullbackComp_inv` — **never `ext` the conjugate-headed goal** (it whnf-bombs the
  `SheafOfModules.pushforward` carrier diamond, root AND terminal alike, even at 1.6M hb +
  `respectTransparency false`). Instead: `rw [show (restrictFunctorComp f g).hom =
  (Adjunction.leftAdjointCompIso (restrictAdjunction g) (restrictAdjunction f) (restrictAdjunction
  (f≫g)) (pushforwardComp f g)).inv from ?_]`; the main goal closes by `exact
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _` (Mathlib `CompositionIso.lean`). The
  residual `(restrictFunctorComp f g).hom = (leftAdjointCompIso …).inv` is a CONCRETE iso-hom equality
  — the conjugate head is gone, so `ext M U : 3` is safe — discharged sectionwise by `simp only
  [Adjunction.leftAdjointCompIso, conjugateIsoEquiv_symm_apply_inv, …, pushforwardComp_hom_app_app]`
  + `erw [Hom.comp_app, restrictAdjunction_unit/counit_app_app, pushforward_map_app]` (every
  `SheafOfModules ≫` / `.app`-value seam needs `erw`, plain `rw`/`simp only [Hom.comp_app]` MISSES),
  merged at MAP level (`← M.presheaf.map_comp`, carrier never forced) and closed by `all_goals first
  | rfl | (congr 1; exact Subsingleton.elim _ _)` (thin-poset; the closing `rfl` is heartbeat-flaky
  through the diamond so the `Subsingleton.elim` branch is the robust fallback). KEY INSIGHT: the
  iter-046 "circular / no abstract shortcut" claim was wrong — `leftAdjointCompIso` is *instantiated
  on `pushforwardComp`*, not equated definitionally with `restrictFunctorComp`. Private `:= rfl`
  helper `restrictFunctor_map_app'` (`((restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U)`) drives the
  reduction.
- **Functor-image tensor distribution across carrier diamonds — `exact map_tensorHom_comp3 (C := …⋙ forget₂) …`
  (B1 keystone close, iter-045):** to split `a.map ((η;p;ρ⁻¹) ⊗ (η;p;ρ⁻¹))` into the three-factor
  `a.map(η⊗η) ; a.map(p⊗p) ; a.map(ρ⁻¹⊗ρ⁻¹)` form, **pin the monoidal category `(C := _root_.PresheafOfModules
  (… ⋙ forget₂ CommRingCat RingCat))` and apply by `exact`**. `rw`/`simp only [← Functor.map_comp]` FAIL
  ("did not find pattern" — the object between `η` and `forget p` is a defeq-not-syntactic carrier diamond);
  `erw [← Functor.map_comp]`/`erw [← tensorHom_comp_tensorHom]` WHNF-BOMB (unfold `η` into `toSheafify`
  internals); `rw [tensorHom_comp3]` fails `MonoidalCategory` synth. `exact` lets the kernel discharge every
  diamond (incl. `𝟙 _.obj` vs `𝟙 _.val`) by defeq. ⚠ LSP reported this clean while `lake build` caught the
  real `MonoidalCategory` synth failure — trust only `lake build`.
- **`leftAdjointUniq` adjoint-uniqueness equation → `homEquiv`-injectivity + TERM `unit_leftAdjointUniq_hom_app`
  (iter-045):** to prove `(adj₁.leftAdjointUniq adj₂).inv.app X = <RHS>`, `apply adj₂.homEquiv _ _ |>.injective;
  rw [leftAdjointUniq_inv_app]; simp only [homEquiv_unit]; refine Eq.trans (unit_leftAdjointUniq_hom_app _ _ X) ?_`
  reduces to a unit identity. `unit_leftAdjointUniq_hom_app` works ONLY as a term (`Eq.trans`), never as `rw`
  (defeq-not-syntactic carrier; same as root `htri'`). The residual is pure mate-calculus
  (`conjugateEquiv_comp`/`mateEquiv_hcomp`/`leftAdjointUniq_trans` + `leftAdjointUniqUnitEta`).
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
- **Carrier-diamond RESOLVED via defeq-composite re-ascription (iter-023 — broke the 5-iter K1 wall, OVERTURNS
  the iter-018/020/022 "carrier diamond is a hard substrate wall" verdict):** when a goal needs a
  `MonoidalCategory`/`Functor.Monoidal` instance on the BAD carrier `PresheafOfModules X.ringCatSheaf.obj`
  (not synthesizable; the global instance is keyed on `(_ ⋙ forget₂)`), do NOT `letI`/`inferInstanceAs`/
  `transport` the bad instance in (they ADD the bad carrier). Instead **normalize it away**: rewrite the
  off-carrier functor as a DEFEQ COMPOSITE that the global instance fires on syntactically — here
  `Gβ := pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙ restrictScalars β'` (its strong tensorator IS
  `μIsoβ`, so `δ Gβ = μIsoβ.inv` by `rfl`) — then re-ascribe every off-carrier term onto the good carrier by
  defeq: `have hadj' : Gβ ⊣ pushforward φ' := hadj`, `have H1' : Gβ ≅ pullback φ' := H1`. Run the mate
  calculus on the unified carrier. ⚠ Rewriting gotchas (the diamond persists at the TACTIC level):
  plain `rw`/`simp only` key-FAIL on the defeq-but-not-syntactic `≫`/tensor instances; full `simp`
  **zeta-unfolds** the carrier-normalizing `let`s and reintroduces the diamond (→ `simp (config := {zeta := false})`);
  `simp` refuses `reassoc_of% hstar` on orientation grounds (→ `erw` is the ONLY tactic that fires `hstar` +
  the trailing `μ_natural`/`hU` steps). This is the general escape for any remaining off-carrier monoidal goal.
- **Data-instance opacity trap — `haveI`/`have` block `exact`/ascription unification (iter-025):** `Monoidal`
  and `Adjunction` are **DATA, not Prop**. A `haveI hMonβ := restrictScalarsMonoidalOfBijective β' hβ` (or
  `have hadj := pushforwardPushforwardAdj …`) makes the value **opaque**; two distinct opaque copies of the
  same data are NOT defeq, so a lemma that *rebuilds* the instance in its statement fails to apply by `exact`
  / type-ascription — it surfaces as a hard **type-mismatch ERROR** (e.g. `η Gβ`/`δ Gβ` mismatch), diagnosable
  by `convert … using 2` splitting into leaf `rfl`-failures. FIX: convert the EXISTING `haveI→letI` / `have→let`
  in place (transparent), so the rebuilt instances reduce to the same value. ⚠ This is SAFE and does NOT
  reintroduce the carrier diamond — the diamond came from introducing a *second* copy via
  `letI`/`inferInstanceAs`/`transport`; making the *existing* one transparent does not. Verified by `δ Gβ =
  μIsoβ.inv := rfl` + the full mate block still compiling.
- **Oplax-monoidal-unit-on-`1` plumbing (K1 η-collapse CLOSED iter-028):** to discharge a goal where the
  oplax unit `η (restrictScalars α)` must send the section ring `1 ↦ 1`, state the helper's unit element
  through the **genuine ring** `(S ⋙ forget₂ CommRingCat RingCat).obj W` — NOT `𝟙_ .obj W` (else `OfNat`/`One`
  won't synthesise). Helper proof = lax `ε(1)=1` (`ModuleCat.restrictScalars_η` + `RingHom.map_one`) then
  `ε ≫ η = 𝟙` via `Functor.Monoidal.ε_η` fed through `show … = 𝟙 _ from … ; rfl`. Close the use site with
  `erw [helper, map_one]; rfl` — the `erw` defeq-matches the `(restrictScalars β').map 𝟙 ≫ η` composite
  against the helper's bare `η`. ⚠ NEVER pre-apply `rw [Functor.map_id]`/`Category.id_comp` (dependent
  motive failure: the `1` argument's type mentions the rewritten object). `ModuleCat.hom_comp_apply` does
  NOT exist (two-step `hom_comp` + `comp_apply`). Recipe: `analogies/eta-plumbing.md`.
- **Carrier-diamond iso-equation collapse (`X.ringCatSheaf.val` vs `X.presheaf ⋙ forget₂` — B2 iter-028):**
  to push a presheaf-level coherence through `sheafification.map` when the middle object carries the
  `forget unit` vs `𝟙_` diamond: `erw [Functor.map_comp]` for the sheafification leg + `exact congrArg (· ≫ _)
  hmap` (defeq-tolerant) for the final collapse. Plain `rw` FAILS on the middle-object diamond. (Used in
  `tensorObjIsoOfIso_comp_unit_iso`.)
- **Contravariant-`symm` leg sidestep (B1 N-leg iter-028):** to produce a `(dualIsoOfIso t).symm`-shaped leg,
  take `congrArg Iso.symm` of the FORWARD identity + `simpa` (with `Iso.trans_symm`/`Iso.symm_symm`), rather
  than rewriting `(dualIsoOfIso t).symm = dualIsoOfIso t.symm`. The latter is DEAD — `Iso.self_symm_id`
  reports "pattern not found" on `dualIsoOfIso (t ≪≫ t.symm)` though the subterm is present.
- **⚠ UNQUALIFIED-NAME SHADOWING = false-green pitfall (iter-029, cost a whole iter + 29 stripped markers):**
  a proof that closes under `lean_diagnostic_messages` (LSP) AND under an isolated `lake env lean <scratch>`
  can STILL fail the real `lake build` of its owning module, when the proof uses an UNQUALIFIED lemma name
  that a project-local declaration shadows ONLY under the full import set. Concrete instance:
  `linearEndo_apply_comm` (DualInverse.lean:219) `rw [← smul_eq_mul, ← map_smul, …]` — `map_smul` resolved to
  the project-local `AlgebraicGeometry.Scheme.Modules.map_smul` instead of `LinearMap.map_smul` (absent from
  the thin scratch's imports) → "did not find an occurrence of the pattern". FIX: always **fully-qualify**
  lemma names in closing rewrites that touch Mathlib generics (`← LinearMap.map_smul`), and VERIFY a closure
  with a real `lake build <Module>` of the owning module, NOT just LSP + a minimal scratch.
- **B1 eval-core ★' `presheafDualUnitIso_naturality` close (iter-029 recipe, honest mod the L219 fix):**
  `apply Iso.ext; apply PresheafOfModules.hom_ext; intro X; apply ModuleCat.hom_ext; ext φ; simp only
  [Iso.trans_hom, PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]` → two defeq `change`s
  reshape to `evalLin φ ((ŝ.app X) 1) = (ŝ.app X) (evalLin φ 1)` → `exact linearEndo_apply_comm _ _` (S-linear
  endos of the regular module `S` commute on `1`; needs `LinearMap.map_smul` qualified).
- **hN N-square close (`dualUnitIso_dualIsoOfIso`, iter-029, verified `goals:[]`):** `apply Iso.ext; unfold
  dualIsoOfIso dual_unit_iso; simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]; have hcore :=
  congrArg Iso.hom (presheafDualUnitIso_naturality …); simp only [Iso.trans_hom] at hcore; rw [← Category.assoc];
  erw [← Functor.map_comp, hcore, Functor.map_comp, Category.assoc]; erw [counit.naturality s.hom]; simp`.
  ⚠ `erw` (NOT `rw`) is required to combine/split the two `sheafification.map` legs (defeq, not syntactic);
  every `rw [← Functor.map_comp/map_comp_assoc/mapIso_trans, hcore]` fails to key-match.
- **Pure-tensor μ-value lemma binder trap (iter-029):** a `((LaxMonoidal.μ F M₁ M₂).app W).hom (m ⊗ₜ n) = m ⊗ₜ n`
  lemma elaborates ONLY with ABSTRACT object binders (`M₁ M₂ : PresheafOfModules (T₀ ⋙ forget₂ …)`, `m : M₁.obj W`)
  + `set_option backward.isDefEq.respectTransparency false in`. Concrete `functor.obj X .obj W` binders fail
  `Module`-synth. The K1 application threads through by defeq (`pushforward_μ_eq` is `rfl`). For the LHS mate
  side, package as a per-section morphism COMPARISON with `tensor_ext` inside; the parent assembles via
  `PresheafOfModules.hom_ext`. (Used: `pushforward_lax_mu_comparison_{rhs,lhs}_tmul`.)
- **Abstract-helper extraction to dodge zeta-`let`/whnf friction (K1 μ/δ-collapse CLOSED iter-031):** when a
  category-theoretic identity must be proved on a goal whose terms are zeta-reduced statement-`let`s
  (`Gβ`/`φ'`/`hadj'` fully unfolded) over heavy functor-composition sections (`pushforward₀OfCommRingCat`),
  inline mate-calculus fails (every `erw` whnf-explodes → 200000-heartbeat timeout; plain `rw` won't
  key-match the unfolded `≫`). FIX: state the identity as a SEPARATE abstract lemma with clean `Type*`
  fvars (`deltaConjOfMuComparison`: two adjunctions `adj₁ adj₂ : Fᵢ ⊣ G` sharing a lax `G`, plus a μ
  comparison hyp → the oplax tensorator of `F₁` = the `leftAdjointUniq`-conjugate of `F₂`'s), prove it on
  the clean fvars (no friction), and discharge the concrete goal by a one-line `exact helper hadj' adj₀ A B
  (comparison)`. The mate `μ(rightAdjointLaxMonoidal adj₁)` is forced via a LOCAL
  `letI := rightAdjointLaxMonoidal adj₁; letI : adj₁.IsMonoidal := inferInstance` (the canonical scoped
  instance — NON-circular, does NOT reference the consumer's `hadj'.IsMonoidal`). Axiom-clean.
- **Instance-heavy `adjᵢ.unit ≫ G.map(…)` silent-no-match (iter-031, generalises iter-014):** in an
  instance-heavy adjunction-mate context, `rw`/`simp`/`simp only`/`erw`/`slice`/`reassoc_of%`/`Category.assoc`
  ALL silently fail to match `adjᵢ.unit.app x ≫ G.map(…)` — even a char-for-char-identical local `have` with
  the exact type, and even on FULLY ABSTRACT fvars (so it is NOT a let-fold issue). Workarounds that DO fire:
  (1) FULL `simp` (not `simp only`) runs `@[reassoc(attr:=simp)]` `_assoc` forms (`unit_leftAdjointUniq_hom_app_assoc`,
  `unit_app_tensor_comp_map_δ_assoc`) — but ONLY when there is a `≫ ?h` tail; (2) `conv` fires `← μ_natural`
  (the COMBINED `Functor.LaxMonoidal.μ_natural` — the `@[simp]` `_left`/`_right` whiskering variants never
  fire on the `⊗ₘ` form), `← Category.assoc`, `tensorHom_comp_tensorHom`; (3) `congr_arg₂ (·≫·) (congr_arg₂
  tensorHom h₁ h₂) hμ` assembles the final TAILLESS 2-factor equality defeq when neither `rw` nor `simp` can
  contract it. A load-bearing `show` to the clean instance form is needed before `rw [hLHS]` will key-match.
- **fvar-keyed-`have` + `erw` fires a blocked `rfl` value-lemma (WALL #1 CRACKED, iter-036 — the 4-iter
  `lhs_tmul` unit-leg blocker):** an `rfl` value-lemma (`pushforwardPushforwardAdj_unit_app_app_apply`:
  `((adj.unit.app M).app U).hom x = (M.map (adj.counit.app U.unop).op).hom x`) refuses to fire on a heavy
  tensor object `M = G(Gβ A) ⊗ G(Gβ B)` through a `hadj'`/`hadj` let-fvar. ALL of these are DEAD: bare
  `rw [lemma]` ("did not find pattern"), `simp only [lemma]` ("no progress"), `simp only [hadj',hadj,lemma]`
  (unfolds the fvar but lemma stays unused), a fresh `have … (Z := …⊗…)` (WALL #2: synthInstance
  `MonoidalCategoryStruct (PresheafOfModules X.ringCatSheaf.obj)` — writing `⊗` re-elaborates the base ring
  to the bad carrier head), explicit `M`/`x` from `m⊗ₜn` ("application type mismatch, ?M uninferable"), and
  the fvar-keyed `have` + plain `rw` ("did not find pattern"). **WORKS:** state a ∀-`have hU` whose LHS is
  keyed on the goal's OWN fvar (`(hadj'.unit.app M).app U`, with NO `⊗` written → dodges WALL #2), prove it
  `fun M U x => lemma _ _ _ _ _ M U x` (defeq through the fvar, leading args inferred from expected type),
  then **`erw [hU]`** — `erw` supplies the coercion/instance defeq that `rw` lacks. General recipe for any
  value-lemma blocked by the *let-fvar-shadow + heavy-object* combination; earmarked to also fire
  `tensorObj_map_tmul` and the future counit `rfl`-dual in the `lhs_tmul` outer telescope.
- **Instantiate-then-`erw` template for carrier-diamond value lemmas (iter-037 — generalizes wall-#1; fired
  `tensorObj_map_tmul` on the heavy `⊗`).** When a value-lemma must fire on objects typed
  `PresheafOfModules X.ringCatSheaf.obj` (defeq-not-syntactic to `_ ⋙ forget₂ _ _`): state a ∀-`have h1` over
  an ABSTRACT ring functor `R` so `R ⋙ forget₂ _ _` matches the `MonoidalCategoryStruct` instance head
  *syntactically* (dodges the diamond), prove it `by intro …; exact <lemma> …`, INSTANTIATE at the goal's
  concrete objects (`h1c := h1 <GX> <GY> …`), then **`erw [h1c]`** (bridges the residual `X.presheaf` vs
  `(sheafToPresheaf …).obj X.sheaf` defeq). DEAD: bare `rw`/`erw`/`simp only` (silent no-op); `set GA := …`
  to fold tensor factors (infers the bad `X.ringCatSheaf.obj` type → `MonoidalCategoryStruct` synth FAILS).
- **Counit/δ helper TYPE fixes on the `pushforwardPushforwardAdj`/`restrictScalars` seam (iter-037).** (a) The
  presheaf counit value-lemma `pushforwardPushforwardAdj_counit_app_app_apply` is NOT a symmetric mirror of the
  unit: its input comes from the BIG composite object — binder `(y : ((pushforward ψ ⋙ pushforward φ).obj N).obj U)`,
  NOT `N.obj U` (naive mirror → lake 4149/4150 application type mismatch); closes by `rfl` (mirrors Mathlib
  `…_counit_app_val_app`). (b) For `restrictScalars_δ_app_tmul` (δ-twin of the μ lemma, `δ = inv μ` via
  `Functor.Monoidal.μ_δ`) the RHS `m ⊗ₜ n` is ILL-TYPED bare (`m` is an S-module; the R-structure exists only
  via `restrictScalars` → lake 2146 `failed to synthesize Module (R.obj W) (M₁.obj W)`) — ASCRIBE it to the
  codomain object: `(m ⊗ₜ n : ↑(((restrictScalars α).obj M₁ ⊗ (restrictScalars α).obj M₂).obj W))`. (The μ
  version dodges this because its `m ⊗ₜ[R] n` is the INPUT, elaborated against μ's domain.)
- **LSP STALE-GREEN on the >4800-LOC `TensorObjSubstrate.lean` (iter-037 — cost a near-miss).**
  `mcp__archon-lean-lsp__lean_diagnostic_messages` reported ZERO errors at three checkpoints while `lake build`
  was actually RED (the new helpers had ill-typed statements). The LSP returns a stale/partial result on this
  heavy file. **ALWAYS confirm with `lake build` before declaring green** — do not trust LSP "no errors" alone.
- **`SheafOfModules` rewrite-by-category-lemma is a DEAD tactic class → reduce to hom-level + term-mode
  `exact` (iter-038, repaired TensorObjInverse `have ht`).** In the `SheafOfModules` category `≫` /
  `Iso.hom` / `Iso.inv` composites are **defeq-but-not-syntactic**, so EVERY `rw`/`simp` of a category or
  `Iso` lemma (`← Iso.trans_assoc`, `Iso.self_symm_id`, `Iso.hom_inv_id_assoc`, even `← Category.assoc`)
  silently fails to pattern-match even when the goal *displays as exactly that pattern*. FIX: `apply
  Iso.ext` + `simp only [Iso.trans_hom, Iso.symm_hom]` to lower to the hom-level goal, then close with a
  **term-mode `exact <category lemma>`** (`exact Iso.hom_inv_id_assoc eMi eMj.hom`) — unification crosses
  the defeq that `rw`/`simp`/`erw` cannot key-match. (Iso-level instance of the `comp_cancel_mid` /
  apply-by-`exact` device.)
- **Tactic-block indentation discipline (iter-038 — caused TensorObjInverse parse error 399:38, RED for
  ~8 iters).** A tactic indented deeper than its `by`-block's tactic column is swallowed as the *previous*
  tactic's argument; the resulting parse error is reported at the **following** line, not at the indent.
  Keep all derivation tactics at the block column (here: dedent L429–473 from 9 to 6 spaces).
- **`lhs_tmul` telescope closure — Steps 3–4 + triangle-cancel (iter-039, CLOSED the K1 seam):** the durable
  recipe for collapsing an adjunction-mate pure-tensor value over the carrier diamond.
  (1) **δ/μ/counit composite-peel by direct `erw` under `respectTransparency false`:** to peel one factor of
  a composite oplax `δ Gβ = (rs β').map(δ pf0) ≫ δ(rs β')` (with `δ pf0 = 𝟙`), `erw [pushforward_map_app_apply,
  restrictScalars_δ_app_tmul …]` defeq-matches the SINGLE-factor helper against the whole composite directly —
  manual identity-factor peeling (`comp_δ`+`map_id`+`id_comp`) silently no-ops / motive-fails in the carrier
  diamond. (2) **counit pair:** `erw [Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]`
  splits the pure tensor, then a fvar-keyed ∀-`have hC` (binder over the BIG composite object, `U : (Opens
  Y)ᵒᵖ`) discharges each leg via `pushforwardPushforwardAdj_counit_app_app_apply` — **pin ALL three explicit
  args (`N`,`U`,`y`)**, any metavar → `erw` whnf heartbeat explosion; cumulative cost forces `maxHeartbeats
  1600000`. (3) **closing:** `erw […rhs_tmul]; congr 1` splits `a ⊗ₜ b = m ⊗ₜ n` into factor equalities; each
  factor closes via an abstract-`P` `have hfac`: `ConcreteCategory.congr_hom (P.map_comp co uo) z` forms the
  `ModuleCat` `≫` INDIRECTLY (manual `P.map co ≫ P.map uo` fails to typecheck through the defeq-not-syntactic
  `restrictScalars`-codomain intermediate), `Subsingleton.elim` on the `Opens Y` poset collapses `co ≫ uo = 𝟙`
  (far cheaper than the literal adjunction-triangle identity), `conv` handles the dependent motive, and
  `P.map_id` collapses as a TERM (`(ConcreteCategory.congr_hom (P.map_id _) z).trans (id_apply z)`). DEAD (do
  not retry): `← ConcreteCategory.comp_apply` / `← LinearMap.comp_apply` / `← ModuleCat.hom_comp` / `←
  CategoryTheory.comp_apply` to combine `P.map uo (P.map co z)` — ALL fail (the `≫` lives behind a
  defeq-through-`⋙` that won't unfold); abstract `pushforward₀_restrictScalars_δ_app_tmul` helper (composite
  input-tmul un-elaborable as `TensorProduct`).
- **Restriction-naturality square via the restrict↔pullback bridge (S4c CLOSED iter-041 — the reframe that
  the squares route through the project's own base-change laws).** To prove a `restrict V.ι`-square commutes
  with the chart `j` (`j ≫ U.ι = V.ι`), do NOT chase the `restrict`-world directly (no `restrictFunctorComp`
  naturality gives it — iter-040). Instead **route through the `pullback` world via a reindex-coherence
  bridge** B2 `restrictFunctorIsoPullback_comp_compat` (`(restrictFunctorIsoPullback V.ι).app A =
  restrictCompReindex j hjι A ≪≫ (restrictFunctor j).mapIso ((rfip U.ι).app A) ≪≫ (rfip j).app _ ≪≫
  (pullbackComp j U.ι).app A ≪≫ (pullbackCongr hjι).app A`). For the UNIT square (S4c): `simp only
  [unitRestrictIso, Functor.mapIso_trans]; rw [B2 …]` cancels the shared restrict-prefix, leaving (i) a
  naturality slide `(restrictFunctorIsoPullback j).hom.naturality (pullbackUnitIso U.ι).hom` applied via
  `reassoc_of%`, and (ii) the pullback-side unit composition law = the PROVEN root
  `pullbackObjUnitToUnit_comp j U.ι` (`(pullbackUnitIso f).hom = pullbackObjUnitToUnit f` defeq). Close:
  `apply Iso.ext; simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.app_hom];
  rw [reassoc_of% hslideH]; rw [← hunitH]; rfl` — **trailing `rfl` mandatory** (`rw`'s reducible auto-rfl
  leaves the `SheafOfModules`-defeq goal). ⚠ The `pullbackCongr hjι` eqToHom shim: `subst hjι` FAILS (`V.ι`
  not a variable) → package as `∀ {Yv} (f₁ f₂) (h : f₁ = f₂), …` then `subst h; simp [pullbackCongr]` (the
  morphisms must be genuine variables for `subst`). B2 itself stays an open sorry (RHS `leftAdjointUniq`
  unit chase); S4c is "CLOSED mod B2". The ⊗-squares (S2) also need bridge B1
  `tensorObj_restrict_iso_eq_pullbackTensorMap` (iso↔map) which is ROOT-PRIVACY blocked — see Known Blockers.

### Known Blockers (do not retry without a structural change)
- **~~Bridge B2 (`restrictFunctorIsoPullback_comp_compat`/`_hom`)~~ — CLOSED iter-050.** The multi-iter
  (044–049) terminal blocker is gone: `_hom` is sorry-free + axiom-clean, consumer already closed. The
  fine-grained conjugate-telescope corrective worked (see Proof Patterns). Sorry 7→6. Do NOT re-open or
  re-dispatch any B2 round.
- **LIVE: B1 crux `H1inv_app_eq_pullbackVal_restrict` (TensorObjInverse L437, sorry@493) — sheafification
  boundary, NOT the B2 family.** It is now the sole "engine" sorry; squares S2–S4b + cocycle all ride it.
  Advanced to the isolated unit-coherence goal (`refine Eq.trans (unit_leftAdjointUniq_hom_app _ hadj
  M.val) ?_`). The residual crosses the presheaf/sheaf boundary (`pushforwardPushforwardAdj` vs
  `pullbackPushforwardAdjunction` vs `sheafificationAdjunction`) — do NOT chase it as a verbatim B2 copy.
  Route: `rw [pullbackValIso, restrictFunctorIsoPullback]` + `simp` + `sheafificationCompPullback_eq_leftAdjointUniq`
  + `leftAdjointUniqUnitEta`. First real `prove` attempt is warranted (single isolated goal); fine-grain the
  sheafification leg only if it churns one round.
- **~~CARRIER-DIAMOND GAP-FILL ESCALATION (iter-046, HARD STOP)~~ — RESOLVED iter-048.**
  `conjugateEquiv_restrictFunctorComp_inv` is **PROVED, public, axiom-clean in root
  `TensorObjSubstrate.lean`** (L4943; `lake build` EXIT 0 8321 jobs; `#print axioms` =
  {propext, Classical.choice, Quot.sound}, no `sorryAx` — independently re-verified this review).
  **The iter-046 "irreducible to library algebra" verdict was WRONG.** The working route never
  sectionwise-chases the conjugate goal: rewrite `(restrictFunctorComp f g).hom` to
  `(Adjunction.leftAdjointCompIso (restrictAdjunction g) (restrictAdjunction f)
  (restrictAdjunction (f≫g)) (pushforwardComp f g)).inv`, close the conjugate head by
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv`, and the residual is a CONCRETE iso-hom
  equality whose `ext M U : 3` no longer whnf-bombs (the conjugate head is gone). The bomb was
  **at `ext` on the conjugate-headed goal** — AVOID it; do the abstract rewrite first. The "no
  abstract shortcut / circular" reasoning failed to spot that `leftAdjointCompIso` can be
  *instantiated on `pushforwardComp`* rather than equated definitionally with `restrictFunctorComp`.
  See Proof Patterns below. **DOWNSTREAM (iter-049 must-fix):** the public root decl now COLLIDES
  with a leftover `private` sorry-stub of the same FQ name in `TensorObjInverse.lean` (L216) →
  terminal file is RED (`error: a non-private declaration … has already been declared`). Delete the
  stub (L207–259 docstring+lemma+sorry) and consume the root lemma; this restores terminal to
  green-mod-sorry (7) and immediately enables B2 + B1-crux via the conjugate-distribution recipe.
- **ROOT PRIVACY GATE — the route surfaces these ONE AT A TIME; B1 advances per de-private (iter-041→044 history).**
  `tensorObj_restrict_iso_eq_pullbackTensorMap` (TensorObjInverse L270) bottoms out on root sheafification/
  comparison internals that are `private` in the frozen `TensorObjSubstrate.lean`. **GATE #1 (δ-conjugation):
  RESOLVED iter-044** — `pushforward_mu_appIso_collapse` (L4678) + chain de-privatized → now PUBLIC; B1's
  proof body GENUINELY discharges the δ-conjugation (compiles, L280–327). **GATE #2 (current, iter-044): the
  per-leg residual** (`sorry` L328) needs `sheafifyTensorUnitIso` (def L1040) + `sheafifyTensorUnitIso_hom_eq'`
  (lemma L1837) to collapse the `sheafifyTensorUnitIso.hom` factor — BOTH still `private` (grep-confirmed).
  Public `sheafifyTensorUnitIso_hom_natural` (L1896) only *commutes* the factor, cannot *remove* it. UNBLOCK =
  ADDITIVE de-`private` via a `refactor` SOLO lane (root churn → build-race; freeze downstream). **Lesson: the
  iter-041→043 "witness public ≠ equation accessible" gate is REAL and RECURS — de-private a BATCH of the root
  internals (`sheafifyTensorUnitIso`/`_hom_eq'` + the `pullbackValIso`/`sheafificationCompPullback` helpers the
  per-leg close needs) rather than chasing one gate per iter.** After GATE #2: close via
  `sheafifyTensorUnitIso_hom_eq'` + `← Functor.map_comp` + `tensorHom_comp_tensorHom` → per-leg
  `H1.inv.app = η ≫ forget pullbackValIso.hom ≫ forget ρ.inv` (PUBLIC `pullbackValIso_hom_natural` L1861 +
  `sheafificationCompPullback_eq_leftAdjointUniq` L1511). B2/S3/S4a are independent of this gate. DEAD
  downstream: `subst hjι`/`clear_value j` on the `j ≫ U.ι = V.ι` chart shim; coherence `simp` alone on B2's RHS;
  B2 via `unit_leftAdjointUniq_hom_app` (CIRCULAR — goal becomes B2 itself, iter-044).
- **Sorry count: trust `lake build`, NOT LSP — in BOTH directions (iter-043).** The lean-auditor (Sonnet/LSP)
  claimed the real count was "likely 9" (asserting sorry must propagate through `rw`/`erw` into S4c L372 +
  cocycle L586). `lake build` is authoritative: exactly **7** sorry-using decls; L372/L586 carry NO transitive
  sorry. LSP over-counted. Settle every sorry-count claim with `lake build … | grep 'uses \`sorry\`'`.
- **⚠ plan-validate NOOPs a build-fix objective whose TARGET DECLARATION is sorry-free (iter-030 — cost a
  whole iter, twin of the iter-026 connector dispatch bug).** The DualInverse L219 one-token fix
  (`← map_smul` → `← LinearMap.map_smul`) lives inside `linearEndo_apply_comm` / `presheafDualUnitIso_naturality`,
  both sorry-free (a *build error*, not a sorry). plan-validate dropped the lane (`meta.json:
  planValidate.objectivesNoop = [DualInverse.lean]`) even though the file has 9 sorries ELSEWHERE — the
  validator keys on the assigned-target's sorry status, not the file's. Result: the unblocking lane never ran,
  the import chain stayed RED a 2nd consecutive iter, ~29 markers stayed stripped. **Do NOT route a
  deterministic build-fix on a sorry-free target through a plain prover lane** — it WILL be noop'd. Apply it
  outside a sorry-gated lane (deterministic edit / structural subagent / user) OR bundle it with a target in
  the same file that carries a sorry. The fix is verified (`goals:[]`) and lands `presheafDualUnitIso_naturality`,
  hN `dualUnitIso_dualIsoOfIso`, `tensorObj_unit_self_duality_collapse` + ~29 markers — but NOT
  `exists_tensorObj_inverse` (gated on the sorry'd `trivialisation_restrict_compat`, below).
- **`trivialisation_restrict_compat` (TensorObjInverse L244) — the TRUE cocycle critical-path blocker;
  STUCK, confirmed math/infra not infra (iter-032).** `exists_tensorObj_inverse`'s typed cocycle rewrites
  THROUGH this lemma, so the cocycle cannot earn `\leanok` even with a green window — the iter-029/030
  "verify-and-unwrap the cocycle hedge" framing is WRONG. iter-032 gave the route its first clean green-window
  SOLO lane and it STILL only closed S1 (the reindexing scaffold): chart morphism `j = Scheme.Hom.resLE (𝟙 X)
  U V` with `hjι : j ≫ U.ι = V.ι`, reindex endpoints `hobjU`/`hobjV` via `image_preimage_of_le` (all proved,
  but currently DEAD — they sit before the L244 `sorry`). The genuine residual is **5 per-constituent
  `restrict`-naturality squares** against `j`, each a *composite* iso through `pullback`+`sheafification` with
  NO codebase precedent: (1) `tensorObj_restrict_iso` (a 4-step chart-chase — the structural template, build
  FIRST), (2) `dual_restrict_iso ≫ dualIsoOfIso eM`, (3) `dual_unit_iso`, (4) `tensorObj_unit_iso`, (5) the
  `uι = restrictFunctorIsoPullback ≫ pullbackUnitIso` leg the **blueprint OMITS** (lvb-inverse032; target lands
  in the *restricted global unit*, so this 5th square is mandatory) — then the telescope. This is a sizeable
  formalization sub-project, not a tactic gap. SEQUENCE: **effort-break the blueprint into the 5 named squares
  + telescope** (the sketch still asserts they "commute routinely" — wrong) → prove the `tensorObj_restrict_iso`
  square first → … → only then verify+unwrap the cocycle `first|…|sorry`. Do NOT re-dispatch a blind prover
  lane (3 iters non-progress). Dead-ends (do not retry): `subst`/`rcases` on `hVU : V ≤ U` (not an equation);
  `simp only [restrictIsoUnitOfLE]` (no cancellation); `congr 1`/`Iso.eq_inv_comp`/`SheafOfModules.Hom.ext`
  (no match — goal already at `.val.app` section level). Mirror `restrictIsoUnitOfLE` (TensorObjSubstrate L424),
  `analogies/cocycle-a.md` §A.
  **iter-038 UPDATE — file REPAIRED to green-mod-sorry; keystone identified = ONE missing iso, not the
  squares.** TensorObjInverse.lean was RED-at-source iters ~030–038 (parse error + unsolved goals — the
  whole downstream chain never compiled); iter-038 repaired it (`lake build` EXIT 0, 8324 jobs) so the
  cocycle `exists_tensorObj_inverse` now closes modulo this lone honest sorry (NO `first|…|sorry` hedge —
  the iter-033 dead-code-hedge concern is GONE). The blocking residual is now precisely ONE missing
  declaration: a restriction-**composition** iso `M.restrict (j ≫ f) ≅ (M.restrict f).restrict j` for
  `Scheme.Modules`, on which ALL 5 square *signatures* depend. **Verified ABSENT** from project + Mathlib
  `Algebra/Category/ModuleCat/Sheaf/` (grep: no `restrictFunctorComp`/`restrictComp`/`restrict_comp`;
  `loogle "SheafOfModules.restrict (?g ≫ ?f)"` → no results) — may reduce to a Mathlib `pullbackComp`.
  SEQUENCE (iter-040 Route-B even slot, root frozen): build that keystone iso FIRST → scaffold the 5 stub
  signatures with it + `eqToHom (image_preimage_of_le …)` for ϱ → prove S2 (`tensorObj_restrict_iso`,
  blueprint ~6502–6563) as template → S3/S4a/S4b/S4c → wire telescope. Do NOT add precedent-less stub
  signatures before the keystone exists (re-RED's the now-green file).
  **iter-040 UPDATE — 5 squares + 2 helper defs SCAFFOLDED green-mod-sorry; the "squares come FREE"
  premise is DISPROVEN (type-error).** Route B SOLO decomposed the monolith (sorry 1→6): the 5 named
  square-lemmas (S2 `tensorObj_restrict_iso_restrict_compat`, S3 `dual_restrict_iso_restrict_compat`
  [clean core, RENAMED from blueprint's bundled `…_dualIsoOfIso_…`], S4a `dual_unit_iso_restrict_compat`,
  S4b `tensorObj_unit_iso_restrict_compat`, S4c `trivialisation_uIota_restrict_compat`) all TYPECHECK
  (`lake build` EXIT 0), proofs all `sorry`, none yet wired into the target (orphaned). **The reindex iso
  `ρ` is the ONLY thing the keystone gives:** `restrictCompReindex j hjι A : A.restrict V.ι ≅
  (A.restrict U.ι).restrict j` := `(restrictFunctorCongr hjι).symm.app A ≪≫ (restrictFunctorComp j U.ι).app A`.
  Plus `unitRestrictIso f : restrict 𝒪_X f ≅ 𝒪_Y` := `restrictFunctorIsoPullback f ≫ pullbackUnitIso f`.
  ⚠ **DEAD (do not retry): `(restrictFunctorComp j U.ι).hom.naturality φ` does NOT give the constituent
  squares** — it is naturality in a MORPHISM `φ` of X-modules (the restrict-COMPOSITION square); the
  constituent `.hom` is a morphism of `(U:Scheme)`-modules → literal type error. Each square needs the
  immersion-naturality of its constituent iso (a 4-leg `restrictFunctorIsoPullback ≫ sheafificationCompPullback
  ≫ leftAdjointUniq ≫ restrictScalars-δ` chart-chase) — genuine depth, NOT free. ⚠ `IsOpenImmersion j` for
  `j = resLE (𝟙 X) U V` is NOT auto-synthesized → `haveI := by rw [hj, Scheme.Hom.resLE_id]; infer_instance`.
  iter-042 SEQUENCE: prove S4c FIRST (most tractable — reduces to a finite `pullbackUnitIso`/`pullbackComp`/
  `pushforwardComp` coherence, no chart-chase) → S2 (Stacks "pullback ⊗ functorial") → S3/S4a/S4b mirror →
  wire all 5 + section-level `eqToHom` telescope into the target (a 6th obligation). ESCALATION: the
  keystone-optimism deflated 2 iters running (iter-039 promised ~1–2, iter-040 produced statements only) —
  consider effort-breaker on S4c or mathlib-analogist (cross-domain) on immersion-naturality of composite
  pullback/sheafification isos before another raw prove-round. Blueprint debt: S3 `\lean{}` now DANGLES
  (names a comment-only decl); `restrictCompReindex`/`unitRestrictIso` need `\lean{}` blocks.
  **iter-041 UPDATE — S4c CLOSED (mod B2); the "squares route through TWO new bridges" reframe WORKS;
  ⊗-side now gated on ROOT-PRIVACY, not a tactic gap.** Route B SOLO added two named bridge lemmas and
  closed one square (file sorry 6→7, but one square eliminated): **B2** `restrictFunctorIsoPullback_comp_compat`
  (the restrict↔pullback reindex coherence — LHS discharged in-body, RHS `leftAdjointUniq`-across-composition
  unit chase ~40–60 LOC is the residual sorry; lynchpin S2/S3/S4c all `\cref` it) and **B1**
  `tensorObj_restrict_iso_eq_pullbackTensorMap` (iso↔map promotion). **S4c `trivialisation_uIota_restrict_compat`
  is now a SORRY-FREE body** (lean-auditor + lvb-checker confirm honest) via B2 alone — recipe in Proof Patterns
  below. **B1 is BLOCKED ONLY by ROOT PRIVACY:** its deep content `δ = e.hom` is the `hcompat` `have` *inside*
  the `private` `pullbackTensorMap_isIso_of_isOpenImmersion` (root L4812, FROZEN); B1 had to take
  `(hiso : IsIso (pullbackTensorMap f M N))` as an EXPLICIT hyp because the witness can't be cited. **iter-042
  unblock = a thin ADDITIVE root edit** (de-`private` the isIso witness, or export `hcompat`/`δ=e.hom`) → B1
  closes → S2 → S4b; schedule via the `refactor` subagent in the plan phase (sorry-free-decl edits don't
  dispatch as prover lanes). S3/S4a (dual gap, route b) are independent of the B1/B2 chain. DEAD: re-deriving
  `δ=e.hom` downstream in TensorObjInverse (>100-LOC mate calculus — strictly cheaper as the root extraction).
- **K1 `pushforward_lax_mu_comparison` — mate route CIRCULAR (re-confirmed iter-028):** the lemma compares
  the adjunction **mate** `Adjunction.rightAdjointLaxMonoidal hadj'` (LHS) against the **composition**
  structure `presheafPushforwardLaxMonoidal φ'` (RHS) on the SAME functor `pushforward φ'`. Unfolding the
  mate (`rightAdjointLaxMonoidal_μ` + `homEquiv_unit`) gives a residual = `Adjunction.IsMonoidal.leftAdjoint_μ`
  = K1's `hmon`, which CONSUMES this lemma → any `IsMonoidal`/`unit_app_tensor_comp_map_δ` route is circular.
  Also it is NOT a 1-to-1 port of `pushforwardComp_lax_μ` (that compares two *composition* structures, so
  mirroring it only reduces the RHS). ONLY route: compute BOTH sides sectionwise to `m ⊗ₜ n` independently
  (reduce RHS at morphism level via `pushforward_μ_eq` BEFORE `hom_ext`; the mate LHS via unit/δ/counit value
  lemmas). Genuine multi-hundred-LOC seam.
  **iter-029 UPDATE — DECOMPOSED; residual narrowed to ONE sub-lemma.** `pushforward_lax_mu_comparison` is now
  PROVEN as an assembly (`hom_ext` to per-section, defer to `lhs_tmul`); the RHS half
  `pushforward_lax_mu_comparison_rhs_tmul` is PROVEN (`= restrictScalars_μ_app_tmul φ'` by defeq). The SOLE
  open μ-side residual is `pushforward_lax_mu_comparison_lhs_tmul` (sorry@L4362) = the LHS mate
  (adjoint-transported) pure-tensor value: unfold `rightAdjointLaxMonoidal_μ` + `homEquiv_unit` to
  `unit ≫ map(δ Gβ ≫ counit⊗counit)`, evaluate at `m ⊗ₜ n`.
  **iter-031 UPDATE — `pushforward_mu_appIso_collapse` CLOSED (axiom-clean), so the μ-side is now ONE sorry
  from done.** The collapse was bypassed by the new abstract helper `deltaConjOfMuComparison` (see Proof
  Patterns) — a one-line `exact deltaConjOfMuComparison hadj' (pullbackPushforwardAdjunction φ') A B
  (pushforward_lax_mu_comparison f A B)`. The SOLE remaining μ-side sorry is `lhs_tmul` (L4362), now
  ADVANCED with a verified sectionwise split (`rw [rightAdjointLaxMonoidal_μ, homEquiv_unit]` then
  `rw [comp_app, hom_comp, comp_apply]`) → opaque mate-μ is the explicit three-leg form
  `(G.map (δ Gβ ≫ (ε⊗ₘε))).app W (unit.app Z .app W (m⊗ₜn))`. BLOCKER: the inner unit value lemma
  `pushforwardPushforwardAdj_unit_app_app_apply` won't fire via `simp only` — the `hadj'` let-binding shadows
  the `pushforwardPushforwardAdj …` form the lemma keys on. NEXT: un-`let` `hadj'` (or local `show`/`change`)
  to expose that form, apply the unit value lemma, then reduce the `δ Gβ`/counit legs via the
  `restrictScalars_μ_app(_tmul)`/`forget₂_restrictScalars_μ_hom_tmul` family (mirror `..._rhs_tmul`). Do NOT
  route through `hadj'.IsMonoidal` (circular). Coverage debt: `deltaConjOfMuComparison` needs a blueprint block.
  **iter-033 UPDATE — `lhs_tmul` is a confirmed DOUBLE wall; the explicit-args bypass is DEAD; the SOLO
  lane committed RED (−141 markers, NET REGRESSION).** The escalation condition is LIVE (no more helper
  cycles — pivot to user/signature-relax). Two now-DEAD bypasses of the `hadj'` let-binding shadow (do NOT
  retry): (1) `simp only [hadj', hadj]; rw [pushforwardPushforwardAdj_unit_app_app_apply]` — let-unfold does
  NOT expose the keyed bare-unit form (`rewrite failed: did not find pattern (unit.app ?M).app ?U) ?x`);
  (2) building the value lemma with EXPLICIT args `have hunit := pushforwardPushforwardAdj_unit_app_app_apply
  … (Z := pushforward A ⊗ pushforward B) … W (m⊗ₜn); erw [hunit]` — `synthInstanceFailed:
  MonoidalCategoryStruct (PresheafOfModules X.ringCatSheaf.obj)` (carrier-diamond on the `⊗`), and per-factor
  `show _root_.PresheafOfModules (X.presheaf ⋙ forget₂ …) from …` ascriptions do NOT redirect the outer
  tensor's instance. lean-auditor: the `have hunit` block (TensorObjSubstrate L4365–4379) is NON-recoverable
  in place (even past synthInstance, `erw [hunit]` still fails the let-shadow). RECOVERY: revert L4365–4379
  to bare `sorry` via the `refactor` route in PLAN phase (objectivesNoop drops the sorry-adjacent fix from a
  prover lane) — restores green + the 141 markers. A real corrective needs un-`let`-ing `hadj'` in the
  *statement* (signature relax) or a value-lemma variant keyed on the `pushforward₀ ⋙ restrictScalars`
  composite form; flagged for user (mathlib-analogist cross-domain on "let-bound composite-functor
  adjunction-unit mate on a pure tensor").
  **NEW iter-033 (lean-auditor): SOLO-lane committed-RED regression mode.** A SOLO prover lane (no race)
  can still regress the tree by ending ON an elaboration error without reverting to the prior
  green-mod-sorry state — the final `have`/`erw` block didn't elaborate and the lane exited RED. sync then
  strips every dependent `\leanok`. Mitigation: a lane that cannot close should leave the bare `sorry`
  (green-mod-sorry), never a half-built failing `have`. **NEW iter-033: TensorObjInverse `first | <derivation>
  | sorry` — the `| sorry` is DEAD CODE** (the first branch always fires; sorry-proved lemmas are valid
  rewrite sources in Lean 4), so `exists_tensorObj_inverse` is sorry-contaminated via the rewrite through the
  sorry'd `trivialisation_restrict_compat`; the L469–472 comment misdescribes it.
  **iter-036 UPDATE — WALL #1 CRACKED; `lhs_tmul` is now an unblocked outer telescope, NOT a stuck wall.**
  The iter-033 escalation/"no more helper cycles" verdict is OVERTURNED. The SOLO Route A lane discharged
  the inner unit leg in committed green-mod-sorry code (build 8321 jobs clean; sync +125 markers) via the
  fvar-keyed-`have` + `erw [hU]` recipe (see Proof Patterns). The iter-035 directive's "abstract `{C D :
  Type*}` helper" model was WRONG (the unit value is irreducibly PresheafOfModules-specific `.app W`/`⊗ₜ`);
  the prover correctly attacked the double-wall directly. Residual = the OUTER δ/counit telescope (4 steps,
  documented in-code @ TensorObjSubstrate L4356–4378): (1) `tensorObj_map_tmul` on the pure tensor (fvar-keyed
  `have`+`erw`, head `…Monoidal.tensorObj` ≠ `⊗`); (2) `Functor.map_comp` split + `pushforward_map_app_apply`
  reindex; (3) δ Gβ collapse via `restrictScalars_μ_app`/`forget₂_restrictScalars_μ_hom_tmul`; (4) NEW helper
  `pushforwardPushforwardAdj_counit_app_app_apply` (counit `rfl`-dual of the unit lemma) via the same recipe;
  then `pushforward_lax_mu_comparison_rhs_tmul` (PROVEN) closes. RE-CONFIRMED CIRCULAR (do not retry): the
  whole-morphism `(★)` route = `Adjunction.map_μ_comp_counit_app_tensor` needs `hadj'.IsMonoidal` which
  consumes this lemma. Coverage debt: the new counit helper needs a blueprint `\label`/`\lean`/`\uses` block
  BEFORE its prover lane (lvb-substrate036 flagged its absence).
  **iter-039 — ✅ CLOSED, axiom-clean, lake EXIT 0 (verified by review, 8324-job whole tree).**
  `pushforward_lax_mu_comparison_lhs_tmul` is sorry-free → seed-1 `pullbackTensorIsoOfLocallyTrivial`
  transitively sorry-free; project-wide sorry 2→1 (sole leaf now Route B `trivialisation_restrict_compat`).
  Steps 3–4 + closing landed (see the new Proof Pattern "lhs_tmul telescope closure"). No new top-level
  declarations (one abstract δ helper tried then removed); only config add = `set_option maxHeartbeats
  1600000`. lvb-substrate039 PASS (faithful both ways, `lean_verify` no sorryAx); lean-auditor iter039
  proof HONEST (all 4 local `have`s real/used/non-circular). **Route A is DONE — do NOT re-open
  `TensorObjSubstrate.lean` for proving.** Residual coverage/cleanup: 6 stale `.lean` header/doc comments
  still call `lhs_tmul`/closed sorries "active" (auditor iter039 MAJOR; deterministic refactor-route fix).
- ~~**K1 `pullbackTensorMap_isIso_of_isOpenImmersion` carrier diamond**~~: **RESOLVED iter-023** — see the
  "Carrier-diamond RESOLVED via defeq-composite re-ascription" Proof Pattern above (Gβ composite +
  `zeta:=false` + `erw`). The full K1 mate calculus is now PROVEN and compiles; the SOLE residual is
  `hmon : hadj'.IsMonoidal` (L~4226) — GENUINE math (δ/μ-side twin of the proved D2′ η-bridge
  `presheafUnit_comp_map_eta`; open-immersion analogue of `pushforwardComp_lax_μ`), NOT a wall. NORMAL
  ~100–200 LOC sectionwise prove: `refine ⟨?_,?_⟩` the two fields (`leftAdjoint_ε`, `leftAdjoint_μ`), each
  via `PresheafOfModules.hom_ext` + `ModuleCat.MonoidalCategory.tensor_ext`, reusing the in-file D3′
  machinery `pushforward_μ_eq`/`restrictScalars_μ_app`/`forget₂_restrictScalars_μ_hom_tmul`/
  `pushforward_map_restrictScalars_μ_app_tmul` (Gβ is the same `restrictScalars`-composite shape they
  collapse on pure tensors). Do NOT re-open the diamond / `transport` / `letI`-the-bad-carrier — exhausted
  AND unnecessary. (The two iter-022 "substrate exits" are obsolete; the composite-re-ascription beat both.)
  **iter-024 UPDATE — `hmon` mate-transport is a DEAD-END (circular); do NOT repeat it.** iter-024 did NOT
  prove the two `IsMonoidal` fields directly; it transported them across `H1 = leftAdjointUniq` from known
  `adj₀.IsMonoidal` (reusing `presheafUnit_comp_map_eta` for ε), leaving residuals `hηcompat` (L~4244) /
  `hδcompat` (L~4262) = "`H1` is a monoidal natural iso". The prover honestly confirms `hδcompat ⟺ the
  original `hcompat`** — a RE-EXPRESSION, not a reduction. The fundamental obligation is unchanged = the
  sectionwise pure-tensor `f.appIso` collapse. CRUX WRINKLE blocking the direct route too: `Gβ.obj (A⊗B)` is
  a **pushforward of a tensor, NOT a syntactic tensor**, so `tensor_ext` does NOT fire after `hom_ext`
  ("CommRing metavar stuck") — the pure-tensor extensionality must thread through `pushforward₀OfCommRingCat`
  sections (the `pushforwardComp_lax_μ` helper family), exactly as that sibling composite did. Next: close
  `hδcompat`/`hηcompat` sectionwise on pure tensors via those helpers; effort-break `hmon` into ε/μ fields if
  it stalls. NO more mate-transport / carrier reshuffles.
  **iter-025 UPDATE — K1 body now FULLY PROVED; obstacle cleanly reduced to TWO top-level collapse lemmas.**
  The effort-breaker extracted `hmon`'s two obligations to top-level lemmas `pushforward_eta_appIso_collapse`
  (η-side, L~4158, effort 765) and `pushforward_mu_appIso_collapse` (μ/δ-side, L~4239, the multi-hundred-LOC
  load-bearing residual). Their first wiring ERRORED (data-instance opacity — see Proof Pattern); fixed by
  `haveI→letI` (×5) + `have hadj→let hadj`. Now `hmon : hadj'.IsMonoidal` is a REAL proof (L4380) consuming
  the two lemmas, so K1 is transitively sorry ONLY through their bodies. **Prove the μ-collapse DIRECTLY**
  (goal confirmed `δ(pullback φ') A B = e.hom` per A B; mirror `pushforwardComp_lax_μ` ONE-TO-ONE) — routing
  it through `hmon`/`Adjunction.IsMonoidal` is **CIRCULAR** (`hmon` consumes it). η-twin is the smaller
  `𝟙_`-module collapse; thread `pushforward₀OfCommRingCat` sections, NOT `tensor_ext`.
  **iter-026 UPDATE — μ-circularity EMPIRICALLY CONFIRMED; η-side NEARLY CLOSED.** The mate route
  (`Adjunction.unit_app_tensor_comp_map_δ (adj := hadj')` / η-twin `unit_app_unit_comp_map_η hadj'`) FAILS:
  both error "failed to synthesize `hadj'.IsMonoidal`" = the very `hmon` they'd build. **Do NOT attempt the
  mate route for either collapse lemma.** The genuine μ-residual (L4287) = the BARE tensorator comparison
  `μ(rightAdjointLaxMonoidal hadj') = μ(presheafPushforwardLaxMonoidal)` on `Gβ A, Gβ B`, proved DIRECTLY
  sectionwise on `pushforward₀OfCommRingCat` pure tensors (mirror `pushforwardComp_lax_μ` L2197; multi-hundred
  LOC; mathlib-analogist / effort-break first). **η-side (L4182) is one step from done:** transposed across
  `hadj'` (needs `have hadj`→`let hadj` so `erw` key-matches the zeta-unfolded `H1`) + `presheafUnit_comp_map_eta`
  + `epsilonPresheafToSheafUnit` reduce it to the single ring identity `LHS(1)=(φ'.app U)(1)`; the only missing
  piece is a presheaf-level `pushforwardPushforwardAdj.unit` sectionwise value lemma (`rfl`-shaped, orientation
  per `PresheafInternalHom.lean:442`), then `erw` it + `ModuleCat.restrictScalars_η` + `map_one`.
  **iter-027 UPDATE — η STILL NOT CLOSED (13th iter at sorry~3); blocker is now pure Lean PLUMBING, not
  math.** The presheaf-level unit value lemma was added as a `rfl` helper
  `pushforwardPushforwardAdj_unit_app_app_apply` (generic `adj`, ~L4094): `(((unit.app M).app U).hom x =
  (M.map (adj.counit.app U.unop).op).hom x)`. ⚠ At the η use site (L4211) the `simp only
  [pushforwardPushforwardAdj_unit_app_app_apply]` is a **NO-OP** (auditor: unused simp arg; goal identical
  before/after) — the prior `pushforward_map_app_apply` already landed the goal in the form the next
  `erw [unit_map_one]` closes. So the helper is NOT load-bearing here; the genuine residual after the
  reduction chain is the single ring-unit identity
  `((restrictScalars β').map 𝟙 ≫ η (restrictScalars β')).app W).hom 1 = (φ'.app U) 1` (`W := op (f ⁻¹ᵁ U)`),
  both sides `= 1`. TWO independent STATING/COERCION obstacles block it (math is settled — `Functor.Monoidal.ε_η`
  + injective `ε.app W` + `restrictScalars_η`): (a) `map_one` won't fire on `ConcreteCategory.hom (φ'.app U)`
  (RingCat-coercion `DFunLike.coe (fun X Y ↦ RingHom.instFunLike)`) — need a RingCat-flavoured `map_one` or
  expose the bare `RingHom`; (b) cannot even STATE `1 : (𝟙_ _).obj W` (`OfNat` synth won't reduce `𝟙_ =
  unit _`) — a drafted `restrictScalars_oplaxMonoidal_η_app_one` could not be written for this reason; FIX =
  phrase the unit element via `PresheafOfModules.unit` (carrier `R.obj W`, a real ring), transport along
  `𝟙_ = unit` defeq. **NEXT: effort-break η into these two sub-lemmas (do NOT re-run a plain prove lane —
  3 iters no close). Also DELETE the dead simp step + fix the inaccurate crediting comments L4208–4214.**
  μ-side untouched iter-027 (`pushforward_lax_mu_comparison` still a bare ORPHANED sorry — not wired to its
  consumer `pushforward_mu_appIso_collapse`; mirror `pushforwardComp_lax_μ`, multi-hundred LOC; NEVER via `hmon`).
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
- **`exists_tensorObj_inverse` — MOVED to `TensorObjInverse.lean` iter-023 (import-cycle resolved); descent
  skeleton built, TWO residuals.** The refactor-MOVE (downstream of DualInverse; RelPicFunctor repointed,
  build GREEN) un-gated the proof; the bare sorry is now the full `rem:dual_discharges_inverse` descent
  (object `dual L` + C-bridge `dual_isLocallyTrivial` CLOSED; local data `eM`/`eN`/`e`/`uι`/`f` + glued `ε`
  via `homOfLocalCompat` + B-bridge `isIso_of_isIso_restrict` + `asIso` all built and compile). Residuals:
  (A) cocycle `hf` (L~121) — the `g·g⁻¹=1` transition-unit cancellation through `tensorObj_restrict_iso`/
  `tensorObjIsoOfIso`/`dualIsoOfIso`; GENUINE ab-group section maps, `subsingleton` is the WRONG tool
  (verified); large, self-contained, d.2-free. Cleaner abstract route (iter-024): `dualIsoOfIso`
  contravariant functoriality + `tensorObjIsoOfIso` bifunctoriality + unit self-duality cancellation
  (`a ⊗ dual(a)⁻¹ ≫ tensorObj_unit_iso = tensorObj_unit_iso`) — candidate for effort-break. (B)
  restriction-connector — iter-024 REDUCED to the exact equation `key` (L~139): `rw [key]; exact hfiso x`
  compiles, so B is **one line from done**. `key`'s body = the missing lemma in `DualInverse.lean`:
  `homOfLocalCompat_restrictFunctor_map : (restrictFunctor (U i).ι).map (homOfLocalCompat U hU f hf) = f i`
  (~40–80 LOC reusing the def's internal `hconn`/`IsGluing`; frontier node `lem:hom_of_local_compat_restrict`).
  **It was scheduled iter-024 but the lane produced NO edit — still does not exist; re-dispatch it standalone
  on `DualInverse.lean` (cheapest remaining win).** Type trap: `(SheafOfModules.unit …).restrict` dot-notation
  resolves to the `SheafOfModules` head → use function form `restrict (unit …) (U x).ι`.
  **iter-025 UPDATE — connector STILL undelivered (3rd consecutive iter: 023/024/025); DualInverse.lean was
  never edited again.** This is now an EXECUTION-DISPATCH failure, not a math wall — force a dedicated,
  non-co-assigned prover onto DualInverse.lean and confirm it runs. Progress made on residual A instead: the
  6 abstract-route ingredients (1)(2) now EXIST as axiom-clean helpers in `TensorObjInverse.lean`
  (`tensorObjIsoOfIso_{trans,refl}`, `presheaf_dualIsoOfIso_{trans,refl}`, `dualIsoOfIso_{trans,refl}` — contra-
  variant `dualIsoOfIso` functoriality + bifunctorial `tensorObjIsoOfIso`). Residual A's remaining hard core =
  ingredient (3), the eval-pairing self-duality cancellation at the `dualPrecompEquiv`/`internalHomEval`
  SECTION level (global eval map deliberately never built), + an iso→section bridge. Reusable: functoriality
  rewrites on `(SheafOfModules.forget _).mapIso e` (carrier `presheaf⋙forget₂`) need `erw`+trailing `rfl`.
  **iter-026 UPDATE — connector RESOLVED + residual B CLOSED.** Root cause of the 3-iter connector
  non-delivery: plan-validate DROPPED the DualInverse objective every iter because the file had 0 sorries
  (prover never dispatched, not "delivered nothing"). FIX: scaffold the stub in the SAME plan phase so the
  lane dispatches. The prover then CLOSED `homOfLocalCompat_restrictFunctor_map` (axiom-clean) — reconstruct
  the gluing internals defeq + `change` to `g`-form + a morphism-level `key` lemma collapsing the
  eqToHom-conjugation via `eqToHom_comp_iff` + `exact`-matched `naturality` (`rw` of naturality fails on
  X-vs-restrict defeq; `(U i).ι ''ᵁ P ≤ U i` is `Scheme.Opens.ι_image_le`, NOT `image_le_range` which doesn't
  exist). Residual B then closed one-line: `exact homOfLocalCompat_restrictFunctor_map U _ f _ x`. **Residual
  A (cocycle) is now the SOLE terminal residual — and it is BLUEPRINT-GATED, not prover-ready:** ingredient
  (3) decomposes into two helper lemmas that exist ONLY as prose in `rem:dual_discharges_inverse` (lvb-inverse026
  major) — (A) further-restriction compatibility of `tensorObj_restrict_iso`/`restrictFunctorIsoPullback`/
  `pullbackUnitIso`, (B) the unit self-duality eval collapse `tensorObjIsoOfIso t (dualIsoOfIso t)⁻¹ ≫
  tensorObj_unit_iso = tensorObj_unit_iso`. Author their `\lean{}` blocks (blueprint-writer) BEFORE any prover
  lane; a plain prover re-hits the section-vs-iso-level wall (verified: `rfl`/`simp[_trans/_refl]`/`congr 1`/
  `hom_ext` all fail on the post-`simp` cocycle goal — distinct opaque trivialisations `eM i.some`/`eM j.some`).
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

### Name-collision RED (iter-048 gotcha)
- A `private lemma Foo.bar` in file B whose FULL qualified name equals a **non-private** decl
  `Foo.bar` imported from file A does NOT get safely name-mangled away — Lean errors
  `a non-private declaration 'Foo.bar' has already been declared` and file B goes RED. So once a
  scaffolded gap-fill is promoted to a public root decl, the terminal's `private` stub of the SAME
  name MUST be deleted in the same/next iter or the consumer file stops building. (Confirmed via
  `lake build`, NOT LSP — LSP also flagged it but the authoritative signal is the build error.)

### Extraction mechanics (non-obvious gotchas)
- **Confirmed truncation bug:** the extraction's Lean-decl remover truncated DualInverse.lean's
  entire §C tail mid-`/-- … -/` docstring, committing a non-compiling file (`unterminated comment`)
  that broke the whole downstream cone. The parent repo
  `/home/archon/FormalizationProjects/Algebraic-Jacobian-Challenge/` is the last-known-good source
  of truth: diff the byte-identical prefix and restore the lost tail. **Other extracted files may be
  similarly truncated — worth a one-shot sweep.**

## Last Updated
2026-06-21T11:50:00Z (iter-050)

2026-06-21T10:30:00Z (iter-049 review — **collision RED cleared; B2 PROVED mod helper; sorry 8→7.**
`lake build …TensorObjInverse` EXIT 0 (8324 jobs, 7 sorries, 0 axioms, re-verified). Deleted the iter-046
collision stub (green); **B2 `restrictFunctorIsoPullback_comp_compat` now sorry-free in its own body**,
delegating the mate-calculus to a NEW extracted helper `restrictFunctorIsoPullback_comp_compat_hom`
(1 sorry L260 = the `hNat` conjugate telescope). Residual fully planned: `conjugateEquiv_comp` distributes
LEG-BY-LEG over 7 fixed-`(C,D)` adjunctions (NO `mateEquiv_hcomp`/`vcomp`; overturns `b2mate045.md`);
per-leg targets all present (c₂=keystone, c₅=inv `conjugateEquiv_pullbackComp_inv`, c₃/c₄=`unit_leftAdjointUniq_hom_app`,
c₁/c₆=`pushforwardCongr`/eqToHom); ~60–100 LOC bookkeeping, shared with B1-crux. NEXT = effort-break `hNat`
into per-leg sub-lemmas; do NOT re-dispatch a plain whole-`hNat` round. lean-auditor iter049 (0 must-fix,
2 major = stale B1/B2 docstrings — `.lean` cleanup is prover-domain), lvb iter049 (signatures faithful, no
drift/laundering; MAJOR coverage debt = both cruxes lack a blueprint block → writer dispatch next iter).
Manual marker: B2 prose `% NOTE: (iter-049)` mechanism-drift (`conjugateEquiv_comp`, not `mateEquiv_vcomp`).
sync_leanok +27/−0 (8015931). doctor clean. Narrative in `iter/iter-049/review.md`.)
2026-06-21T17:30:00Z (iter-048 review — **KEYSTONE CLOSED; iter-046 "irreducible" verdict OVERTURNED.**
`conjugateEquiv_restrictFunctorComp_inv` PROVED, public, axiom-clean in root `TensorObjSubstrate.lean`
(L4943; `lake build` EXIT 0 8321 jobs; #print axioms = propext/Classical.choice/Quot.sound, no sorryAx —
independently re-verified). Working route = abstract `leftAdjointCompIso` instantiation +
`conjugateEquiv_leftAdjointCompIso_inv`; NEVER `ext` the conjugate-headed goal. Root stays sorry-free.
**SIDE EFFECT (iter-049 must-fix, VERIFIED via `lake build`):** the public root decl now COLLIDES with the
leftover `private` sorry-stub of the same FQ name in `TensorObjInverse.lean` L216 → terminal RED
(`non-private declaration … already declared`). Delete stub L207–259 → restores terminal to 7 sorries
green-mod-sorry + unblocks B2/B1-crux. lean-auditor iter048 (2 must-fix = the collision build error + the
stub's false "irreducible" comment, BOTH resolved by the same deletion; 4 major stale-comments), lvb
substrate048 PASS (keystone faithful, signature verbatim, `\leanok` correct). Manual markers: keystone
`\leanok` override (sync withheld it due to the name collision resolving `\lean{}` to the sorry-stub),
stale iter-046 `% NOTE:` replaced, prose-route `% NOTE:` added. sync_leanok −27/+0 (collision-driven).
gaps=0, unmatched=106, doctor clean. Narrative in `iter/iter-048/review.md`.)
2026-06-21T08:05:00Z (iter-046 review — **HARD STOP TRIGGERED; obstruction localized to one out-of-lane gap-fill.**
Sorry 7→8 (REGRESSION by the directive's Step-0 scaffold; no original sorry closed). `lake build …TensorObjInverse`
EXIT 0 (green-mod-sorry, 8). Prover scaffolded `conjugateEquiv_restrictFunctorComp_inv` (restrict-side mirror of
`conjugateEquiv_pullbackComp_inv`, the lemma BOTH B2 + B1-crux reduce to), LSP-verified its sectionwise reduction
to a trivial thin-poset identity — but it `whnf`-BOMBS in real `lake build` through the `SheafOfModules.pushforward`
carrier diamond (4×, incl. 1.6M hb + respectTransparency false) AND is irreducible to library algebra
(`restrictFunctorComp` ≠ `leftAdjointCompIso`). Both audits confirm honest sorry (no laundering); exactly 8, no
transitive hiding. ESCALATE: root/`mathlib-build` lane — make `restrictFunctorComp` a `leftAdjointCompIso` ⇒ gap-fill
by `rfl`, or prove in root. Do NOT dispatch a 7th plain terminal prover. Details: `iter/iter-046/review.md`.)

2026-06-21T06:35:00Z (iter-045 review — **B1 KEYSTONE CLOSED (body sorry-free); GATE #2 cleared; residual = 1 mate crux.**
Sorry 7→7, `lake build …TensorObjInverse` EXIT 0 (8324 jobs). Refactor `deprivate-sheafunit045` made
`sheafifyTensorUnitIso`/`_hom_eq`/`_hom_eq'` PUBLIC; B1 (`tensorObj_restrict_iso_eq_pullbackTensorMap`)
body now SORRY-FREE (both reviewers confirm), via `sheafifyTensorUnitIso_hom_eq'` collapse + new helper
`H1inv_app_eq_pullbackVal_restrict` + `map_tensorHom_comp3`. Residual EXTRACTED into that helper, reduced
(verified) to ONE `leftAdjointUniq`/mate-calculus unit crux — SAME family as B2. Flat-7 = sorry relocated.
Reviewers: must-fix none; stale B1 `% NOTE:` PRUNED this review; stale B1 Lean docstring + S4c comment →
next prover (review can't edit .lean). REC: shared `leftAdjointUniqUnitEta`-style helper closes the B1
crux AND B2 together (7→5). Details: `iter/iter-045/review.md`.)

2026-06-21T05:00:00Z (iter-044 review — **δ-conjugation GATE RESOLVED (de-private worked); B1 advanced; GATE #2 found.**
Sorry 7→7, `lake build …TensorObjInverse` EXIT 0 (8324 jobs). `pushforward_mu_appIso_collapse` now PUBLIC
(grep-confirmed L4678); B1's δ-conjugation GENUINELY discharged in a ~25-line compiling proof (L280–327),
residual isolated to ONE per-leg `sorry` (L328) hard-blocked on the NEXT private pair `sheafifyTensorUnitIso`
(L1040) + `sheafifyTensorUnitIso_hom_eq'` (L1837). B2 confirmed CIRCULAR under `unit_leftAdjointUniq` shortcut.
Reviewers: B1 honest/0-must-fix (vs-bp); auditor 1 must-fix elsewhere (`RelPicFunctor.PicSharp` PUnit stub).
Stale B1 `% NOTE:` corrected. Recommend BATCH de-private refactor before next B1 round. Details:
`iter/iter-044/review.md`.)

2026-06-21T03:51:00Z (iter-043 review — **0 closed; ROOT-PRIVACY gate VERIFIED, "B1 unblocked" premise FALSE.**
Sorry 7→7, `lake build …TensorObjInverse` EXIT 0. B1 signature corrected to blueprint form (dropped stale
`hiso`, cites public IsIso witness); B2 reduced to explicit mate-coherence residual (~80-120 LOC, the one
fully-unblocked sorry). Grep-confirmed the δ-conjugation chain (`pushforward_mu_appIso_collapse` etc.) is ALL
`private` in the frozen root — B1/S2/S4b/telescope blocked; unblock = additive de-`private` root edit. Auditor
LSP "likely 9 sorries" REFUTED by lake build (exactly 7). `% NOTE:` added to B1 blueprint proof block. Details:
`iter/iter-043/review.md`.)

2026-06-20T13:30:00Z (iter-041 review — **S4c CLOSED mod B2; bridge reframe validated; ⊗-side now gated on
ROOT-PRIVACY.** Route B SOLO closed the unit square `trivialisation_uIota_restrict_compat` (sorry-free body)
via new bridge B2 `restrictFunctorIsoPullback_comp_compat`; added B1 `tensorObj_restrict_iso_eq_pullbackTensorMap`
(iso↔map, ROOT-PRIVACY blocked — needs iter-042 thin additive root extraction of the `private`
`pullbackTensorMap_isIso_of_isOpenImmersion`). File sorry 6→7 (−1 square, +2 bridges). lake EXIT 0. Both
reviewers confirm honest; review fixed the B1 `\lean{}` pin mismatch. Details: `iter/iter-041/review.md`.)

2026-06-20T12:08:55Z (iter-040 review — **DECOMPOSITION, no closure; keystone over-sold.** Route B SOLO
split the monolith `trivialisation_restrict_compat` into 5 named square-lemmas (S2–S4c) + 2 reusable
helper defs (`restrictCompReindex` ρ, `unitRestrictIso` uι) + the `IsOpenImmersion j` chart instance — all
TYPECHECK, `lake build …TensorObjInverse` EXIT 0 (8324 jobs), green-mod-sorry. Active sorry **1→6**
(intended fine-grain; 0 closed, squares orphaned). **KEY: the iter-039 "squares come FREE via
`restrictFunctorComp.hom.naturality`" premise was DISPROVEN by the prover (type-error) — the keystone gives
only the reindex iso ρ; each square is a genuine 4-leg immersion-naturality chart-chase.** Keystone-optimism
deflated 2 iters running → ESCALATION live (iter-039 plan's "2nd consecutive PARTIAL" trigger). Reviewers:
lean-auditor iter040 HONEST (0 axioms; 1 must-fix = target sorry load-bearing; 2 major = orphaned squares +
stale iter-206/218/225/226 docstrings); lvb-tensorobjinverse040 5/6 faithful, 2 must-fix (S3 `\lean{}`
DANGLES → blueprint-side restate; S2–S4c sketches mis-sell residual as free) + 1 major (ρ/uι coverage debt).
sync +4/−0 (5e8a0e8). Doctor clean. iter-042: prove S4c FIRST (finite pullback coherence), then S2; consider
effort-breaker/mathlib-analogist first. Narrative in `iter/iter-040/review.md`.)
2026-06-20T11:20:00Z (iter-039 review — **MILESTONE: seed-1 CLOSED, no regression.** SOLO Route A closed
`pushforward_lax_mu_comparison_lhs_tmul` (the 4-iter K1 bottleneck, open since iter-032) → seed-1
`pullbackTensorIsoOfLocallyTrivial` transitively **sorry-free**; project-wide active sorry **2→1** (sole leaf
now Route B `trivialisation_restrict_compat`). Review independently verified: `lake build …TensorObjSubstrate`
8321 jobs + whole-tree `…TensorObjInverse` 8324 jobs, both EXIT 0; `lean_verify` axiom-clean (no sorryAx).
Landed Steps 3–4 + triangle-cancel closing (new Proof Pattern "lhs_tmul telescope closure": direct-`erw`
composite-peel under `respectTransparency false`; fvar-keyed `hC` all-args-pinned + `maxHeartbeats 1600000`;
abstract-`P` `hfac` via `ConcreteCategory.congr_hom`+`Subsingleton.elim` on the `Opens Y` poset). No new
top-level decls (one abstract δ helper tried then removed). sync +67/−0 (2f5b626). Reviewers 0 must-fix:
lvb-substrate039 PASS (faithful both ways; 4 minor prose-precision — closing uses the poset route not the
literal triangle identity, unit displayed as `hadj'.counit` but Lean uses the geometric opens-adjunction
counit), lean-auditor iter039 proof HONEST (6 MAJOR = stale `.lean` header/doc comments calling closed
sorries "active" → refactor-route; TensorObjInverse clean). Doctor clean, gaps=0, unmatched=106 (no new
debt). No manual markers. **Route A DONE — pivot to Route B iter-040 (de-risked via `restrictFunctorComp`).**
Narrative in `iter/iter-039/review.md`.)
2026-06-20T08:51:00Z (iter-038 review — **STRUCTURAL REPAIR, no regression.** SOLO Route B (repair-first)
took `TensorObjInverse.lean` from RED-at-source (parse error 399:38 + unsolved goals — never compiled in
project history, ~iters 030–038) to **green-mod-sorry** (`lake build` EXIT 0, 8324 jobs; sync +17 / 0bf1584).
The cocycle `exists_tensorObj_inverse` now closes modulo the lone honest `trivialisation_restrict_compat`
sorry — no `first|…|sorry` hedge. Fixes: dedent cocycle block L429–473 to the 6-space tactic column (parse
err) + rewrite `have ht` via term-mode `exact Iso.hom_inv_id_assoc` (SheafOfModules `≫` defeq-not-syntactic).
Active sorry 2→2 (none closed). KB: SheafOfModules term-mode-`exact` device, indentation parse trap,
trivialisation_restrict_compat keystone = ONE missing restriction-composition iso (absent project+Mathlib).
Reviewers 0 must-fix (tensorobjinverse038 FAITHFUL 12/12; iter038 1 major = stale comment). Narrative in
`iter/iter-038/review.md`.)
2026-06-20T08:00:00Z (iter-037 review — **REAL PARTIAL PROGRESS, no regression.** SOLO Route A landed BOTH
missing helpers (`pushforwardPushforwardAdj_counit_app_app_apply` rfl, `restrictScalars_δ_app_tmul`) + 2
verified `lhs_tmul` telescope moves, committed green-mod-sorry (build 8321 jobs; sync +1 ee78653). Residual =
telescope steps 3–4 (tools now in-file). KB updated: instantiate-then-`erw` template, counit/δ type fixes,
LSP stale-green trap. Reviewers 0 must-fix (substrate037 / iter037). Narrative in `iter/iter-037/review.md`.)
2026-06-20T06:05:00Z (iter-036 review — **REAL PARTIAL PROGRESS; WALL #1 CRACKED, no regression.** SOLO
Route A lane discharged the `lhs_tmul` inner unit leg in committed green-mod-sorry code (build 8321 jobs;
sync +125/−0 0f45496 — recovers the iter-033 −141 strip) via the fvar-keyed-`have` + `erw [hU]` recipe
(new Proof Pattern). The 4-iter double-wall #1 is broken; iter-033 escalation OVERTURNED. Sorry 2→2;
residual = outer δ/counit telescope (4 documented steps, needs new counit `rfl`-helper). Route B untouched
(SOLO-only; root-churn race). Reviewers: lvb-substrate036 CLEAN (0 red flags; minor coverage debt = no
`\lean{}` for the future counit helper), lean-auditor iter036 (`have hU`/`erw` block SOUND, comment a legit
roadmap; 2 MAJOR stale TensorObjSubstrate file-headers L161/L162 → refactor route). Doctor clean, gaps=0,
unmatched=106. No manual markers. Full narrative → `iter/iter-036/review.md`.)
2026-06-20T04:10:00Z (iter-033 review — **NET REGRESSION; SOLO `lhs_tmul` lane committed RED.** The single
corrective test (`pushforward_lax_mu_comparison_lhs_tmul` SOLO) left TensorObjSubstrate RED
(synthInstanceFailed L4369) ⇒ sync −141/+0 (b3a0e11) stripped every dependent `\leanok`. The added
`have hunit := …; erw [hunit]` block (L4365–4379) is NON-recoverable (carrier-diamond synthInstance on the
`⊗` + `hadj'` let-shadow); revert to bare `sorry` via the PLAN-phase `refactor` route to restore green +
the 141 markers. Route A escalation is LIVE (no more helper cycles → user/signature-relax). Terminal route
untouched (effort-broken into 5 squares in plan phase; S2 = iter-034 template AFTER the revert). Reviewers:
lean-auditor iter033 (1 must-fix = the RED block; NEW: TensorObjInverse `| sorry` dead-code + mis-comment
L469–472, stale excuse-comment :778 on a complete proof, DualInverse docstring L362–406 contradiction),
lvb substrate033 CLEAN (0 must-fix; blueprint adequate, blocker is prover-side Lean mechanics). Doctor clean,
gaps=0, unmatched=106 (no new decls). No manual markers. Full narrative → `iter/iter-033/review.md`.)
2026-06-19T18:30:00Z (iter-032 review — **PARTIAL, no net sorry elimination; Terminal route confirmed
STUCK (math/infra, not infra).** TensorObjInverse SOLO fine-grained lane closed only S1 of
`trivialisation_restrict_compat` (chart morphism `j`/`hjι` + reindex endpoints `hobjU`/`hobjV`, all proved
but currently DEAD before the L244 sorry); replaced the bare sorry with a scaffold + roadmap. Sorry 2→2,
sync +0/−0 (008e366), build green-mod-sorry, root untouched, no regression. The route got its FIRST clean
green-window SOLO lane and still only landed scaffold ⇒ the residual is genuine infra: **5 per-constituent
restrict-naturality squares** (incl. the blueprint-OMITTED `uι` leg) — see Known Blockers. Reviewers:
lean-auditor iter032 FAIL (4 must-fix on TensorObjInverse: dead-scaffolding bare sorry, NEW L237
"verified this iter" excuse-comment, L470–476 "next prover should strip" excuse-comment,
`first|derivation|sorry` sorry-laundering; 6 major incl. stale module headers across
DualInverse/Vestigial/LineBundlePullback describing PROVED decls as open; 2 critical excuse-comments),
lvb inverse032 (signatures faithful both ways, sorries honest/no shape-masking; 2 major: sketch
under-specifies the 5 squares + omits `uι`, stale inline prose L1482–1490). Doctor clean, gaps=0,
frontier=3, unmatched=106 (no new decls). No manual markers. CORRECTIVE: effort-break the blueprint into
the 5 squares + telescope (NOT a 4th blind lane); refactor-cleanup the excuse-comments + stale headers;
parallel options = `lhs_tmul` (Substrate SOLO) + 3 OnProduct frontier nodes. Full narrative →
`iter/iter-032/review.md`.)
2026-06-19T17:15:00Z (iter-031 review — **STRONG RECOVERY + K1 critical-path closure.** Import chain GREEN
again (the iter-029/030 L219 blocker resolved via the plan-phase refactor route, NOT a prover lane);
sync_leanok +34/−0 (recovers the iter-029 −29 strip + new closures). `pushforward_mu_appIso_collapse` CLOSED
(axiom-clean) via the NEW abstract helper `deltaConjOfMuComparison` (Proof Patterns above). Project-wide
term-position sorries = **exactly 2**: `pushforward_lax_mu_comparison_lhs_tmul` (advanced, verified split) +
`trivialisation_restrict_compat` (cocycle gate, blueprint roadmap now expanded). Reviewers: lean-auditor
iter031 (2 must-fix = STALE headers L46/L162 only; closures honest+clean, non-circular; 7 minor), lvb
substrate031 (0 must-fix / 2 major: helper missing blueprint block + lhs_tmul value-vs-section prose drift /
1 minor stale collapse sketch). Doctor clean, gaps=0, frontier=3, unmatched=106 (+`deltaConjOfMuComparison`
coverage debt). Manual marker: `% NOTE` on `lem:pushforward_mu_appiso_collapse` proof block. Full narrative →
`iter/iter-031/review.md`.)
2026-06-19T14:59:58Z (iter-030 review — **ZERO buildable progress; build still RED, ~29 markers still
stripped (sync +0/−0). PROCESS failure, not math.** The plan was correct & tiny (Obj-1 = the deterministic
one-token L219 fix that unblocks the whole import chain; Obj-2 = type the cocycle on the green window). But
**plan-validate NOOP'd Obj-1** because the L219 target declarations are sorry-free (new Known Blocker above) —
only the TensorObjInverse lane ran, and it spent the session polling for a green window that, by construction,
never came. It typed `exists_tensorObj_inverse` hedged `first|…|sorry` (sub-steps abstract-verified via
`lean_run_code`; honest hedge per lvb, no shape-mask) but the cocycle is GATED on the still-sorry
`trivialisation_restrict_compat` — NOT verify-and-unwrap. L219 unchanged on disk (2nd consecutive iter the
one-token fix failed to land). Reviewers: lean-auditor iter030 (3 must-fix: L219 build error + cocycle
laundering-hedge + excuse-comment, NEW DualInverse L199-201 inaccurate comment [subsingleton@L206 closes the
goal]; 6 major/10 minor), lvb inverse030 (2 must-fix [2 sorries] / 1 major [thin trivialisation_restrict_compat
sketch]; 12/12 signatures faithful both directions). pc030 verdict CHURNING(TensorObjInverse — PARTIAL→STUCK
if again)/UNCLEAR-fast-track(DualInverse). Doctor clean, gaps=0, frontier=5, unmatched=105. KB: new plan-validate
NOOP blocker + trivialisation_restrict_compat-is-the-real-blocker. Narrative → `iter/iter-030/review.md`.)
2026-06-19T13:45:00Z (iter-029 review — **NET REGRESSION: build went RED, sync_leanok +3/−29.** A single
unqualified-name bug in the new helper `linearEndo_apply_comm` (DualInverse.lean:219 — `← map_smul` resolves
to project-local `Scheme.Modules.map_smul`, not `LinearMap.map_smul`, under full imports) broke DualInverse →
TensorObjInverse → RelPicFunctor. The math in all lanes is HONEST + structurally correct (lean-auditor), but
the intended closures (B1 eval-core `presheafDualUnitIso_naturality`, hN `dualUnitIso_dualIsoOfIso`, cocycle-A
assembly) are written-but-RED and did NOT land; they land with the one-token fix `← LinearMap.map_smul`. Only
buildable progress: TensorObjSubstrate μ-decomposition — `pushforward_lax_mu_comparison_rhs_tmul` PROVEN +
`pushforward_lax_mu_comparison` assembly PROVEN (mod `lhs_tmul`), narrowing the μ-side to ONE residual
(`pushforward_lax_mu_comparison_lhs_tmul`, the LHS mate pure-tensor value). TensorObjSubstrate builds
green-mod-sorry (lhs_tmul + mu_appIso_collapse). Reviewers: lean-auditor iter029 (1 must-fix L219 root cause/2
major premature-closed comments/2 minor), lvb substrate029 (0 must-fix/1 major lhs_tmul statement-shape drift
value-vs-comparison/1 minor). KB updated: shadowing pitfall + B1/hN recipes + binder trap + μ-decomposition.
Doctor clean, gaps=0, frontier=5, unmatched=105 (+`linearEndo_apply_comm` coverage debt). Narrative →
`iter/iter-029/review.md`.)
2026-06-19T11:30:00Z (iter-028 review — **η CLOSED**: `pushforward_eta_appIso_collapse` sorry-free + axiom-clean (first K1 elimination since ~14-iter η stall); cocycle-A collapse mechanism PROVEN mod B1 (2 new helpers `tensorHom_inv_comp_leftUnitor`+`tensorObjIsoOfIso_comp_unit_iso`); B1 reduced to a single naturality square (N); μ-comparison mate route re-confirmed CIRCULAR. KB updated above. Narrative → `iter/iter-028/review.md`.)
2026-06-19T09:45:31Z (iter-027 review — **no sorry eliminated; 13th iter at "sorry ~3".** η must-close
REDUCED but not closed: a new `rfl` helper `pushforwardPushforwardAdj_unit_app_app_apply` was added but is a
NO-OP at its η use site (auditor: dead simp arg L4211); residual is one ring-unit identity blocked by pure
PLUMBING — (a) RingCat-coercion `map_one` won't fire, (b) `1 : (𝟙_ _).obj W` won't `OfNat`-synth (can't even
STATE the fix). Math settled (`ε_η`+injective `ε`+`restrictScalars_η`). **Effort-break η into the two
sub-lemmas; do NOT re-run a plain prove lane (3 iters no close); delete the dead simp step.** μ pair untouched
(`pushforward_lax_mu_comparison` a bare ORPHANED sorry, not wired to its consumer; mirror `pushforwardComp_lax_μ`,
multi-hundred LOC, never via `hmon`). Build GREEN, axiom-clean, sync +1/−0 (new μ-comparison stmt block), doctor
clean, gaps=0, frontier=5, unmatched=105 (+new helper `pushforwardPushforwardAdj_unit_app_app_apply`, coverage
debt). Reviewers: lean-auditor iter027 (0 crit/3 major: dead simp step, orphaned μ-comparison, stale header
L46-50/3 minor; NO circularity — no collapse lemma touches `hmon`), lvb substrate027 (0 must-fix/3 honest
sorries/2 minor: helper no `\lean{}` block, targets `private` but pinned). No manual markers. Narrative in
`iter/iter-027/review.md`.)
2026-06-19T07:33:00Z (iter-026 review — **FIRST sorry elimination after ~12 iters: leaf sorries 5→3.** The
3-iter connector "non-delivery" was a DISPATCH bug (plan-validate dropped the 0-sorry DualInverse objective so
the prover never ran); fixed by scaffolding the stub in-phase. Prover then CLOSED the connector
`homOfLocalCompat_restrictFunctor_map` (axiom-clean) → terminal residual B closed one-line via it. K1: η-collapse
reduced to one `rfl`-shaped residual (nearly closed); μ-collapse mate route EMPIRICALLY CONFIRMED circular →
real residual is the bare sectionwise μ-comparison (mirror `pushforwardComp_lax_μ`). Remaining 3 leaf sorries:
terminal cocycle A (blueprint-gated: author 2 helper `\lean{}` blocks first), K1 η (short lane), K1 μ
(mathlib-analogist/effort-break). Build GREEN, axiom-clean, sync +2/−0, doctor clean, gaps=0, frontier=3,
unmatched 110→104. Reviewers: lean-auditor iter026 (0 crit/11 major all STALE comments/4 minor — no live defect),
lvb dualinverse026 (faithful, 1 major stale comments), lvb inverse026 (faithful, 1 major: A's helpers prose-only),
lvb substrate026 (PASS). K1 `% NOTE` refreshed to iter-026. Narrative in `iter/iter-026/review.md`.)
2026-06-19T13:45:00Z (iter-025 review — **no sorry eliminated; 11th iter at "sorry ~2".** Real structural
progress: K1 wiring bug (data-instance opacity — `haveI` opaque `Monoidal`/adjunction not defeq to the rebuilt
lemma's; fixed `haveI→letI` ×5 + `have hadj→let hadj`) → K1 body now FULLY PROVED, transitively sorry ONLY via
the two extracted collapse lemmas `pushforward_{eta,mu}_appIso_collapse` (μ-side = the load-bearing residual,
prove DIRECTLY not via `hmon` — circular). Terminal: 6 axiom-clean functoriality helpers delivered (residual A
ingredients 1&2); residual A still needs ingredient 3 (eval-cancellation, section-level); residual B one-line
from done. **Connector `homOfLocalCompat_restrictFunctor_map` UNDELIVERED 3rd iter — DualInverse never edited;
execution-dispatch failure, force a dedicated prover.** Builds GREEN, axiom-clean, sync +3/−0, doctor clean,
gaps=0, frontier=4, unmatched=110 (+6 helpers, coverage debt). Reviewers: aud iter025 (0 must-fix/1 major stale
header/1 minor), lvb substrate025 (0 must-fix/3 minor), lvb inverse025 (0 must-fix/2 major: helpers no `\lean{}`
nodes, `rem:dual_discharges_inverse` thin). K1 `% NOTE` refreshed to iter-025. Narrative in `iter/iter-025/review.md`.)
2026-06-19T12:00:00Z (iter-024 review — **no sorry eliminated; 10th iter at "sorry ~2".** K1 `hmon` 1→2: the
prover transported the two `IsMonoidal` fields across `H1=leftAdjointUniq` instead of proving them directly,
leaving `hηcompat`/`hδcompat` — but `hδcompat ⟺ the prior `hcompat`** (re-expression, not reduction). KB K1
blocker updated: mate-transport is a DEAD-END, the real obligation is the sectionwise pure-tensor collapse with
the `Gβ.obj(A⊗B)`-not-syntactic-tensor wrinkle. Terminal: B reduced to a one-line `key` swap pending the
connector; A cocycle reduction added. **Connector lane (`homOfLocalCompat_restrictFunctor_map`, frontier, cheapest
win) was scheduled but produced NO edit — re-prioritised.** Builds GREEN, axiom-clean, sync +0/−0, doctor clean,
gaps=0, unmatched=0. Reviewers aud024 (0 must-fix/3 major stale-comments), substrate024 (prose describes wrong
residual route), inverse024 (PASS). K1 `% NOTE` refreshed to iter-024. Narrative in `iter/iter-024/review.md`.)
2026-06-19T11:00:00Z (iter-023 review — **5-iter K1 CARRIER DIAMOND BROKEN.** Resolved via defeq-composite
re-ascription (Gβ + `zeta:=false` + `erw`); new Proof Pattern added, K1 Known-Blocker marked RESOLVED, sole
residual now the sectionwise `hmon : hadj'.IsMonoidal`. Terminal `exists_tensorObj_inverse` MOVED to
`TensorObjInverse.lean` + descent skeleton built (2 residuals: cocycle + a needed `DualInverse.lean`
connector). Sorry 2→3, both files GREEN, 0 axioms. Reviewers aud023/substrate023/inverse023 all 0 must-fix.
Carrier-diamond `% NOTE` refreshed to iter-023. Session narrative in `iter/iter-023/review.md`.)
2026-06-18T11:45:00Z (iter-022 review — recon022 K1 mate route EXHAUSTED; `hcompat` reduced to ★ but blocked
by the carrier diamond at instance synthesis. Known Blockers K1 entry rewritten with the two substrate exits;
session narrative in `iter/iter-022/review.md`.)
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
