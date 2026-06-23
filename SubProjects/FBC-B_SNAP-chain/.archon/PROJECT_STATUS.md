# Project Status — Knowledge Base

<!-- Reset at extraction (2026-06-05). The parent project's knowledge base
     concerned lanes outside this subproject's scope. The review agent
     rebuilds this file from this subproject's own sessions. -->

## Knowledge Base

### Proof Patterns (reusable across targets)

- **`exact <abstract-lemma> <heavy-carriers…>` does NOT dodge a whnf bomb (iter-026 REFUTES the iter-025
  conjecture below).** The iter-026 probe tested exactly this: a fully carrier-free cocycle skeleton
  `ring_square_cocycle_probe` (`{𝒵}[Category 𝒵]{X1..X6}`, six Isos, `sorry` body) folded into the heavy FBC glue
  via `exact ring_square_cocycle_probe (chartBaseChangeGeometricComparison …) …`. Cold build → whnf 200k-hb timeout
  at the FOLD seam (FlatBaseChange.lean:2235), build RED. ROOT CAUSE: the `exact`-binds-carriers-to-metavars premise
  is FALSE — unification of the abstract conclusion against the CONCRETE goal still forces whnf of the GOAL side
  whenever the goal is not already syntactically in the lemma's conclusion shape (here the concrete RHS last factor
  is `pullback_spec_tilde_iso …`, not syntactically `_.symm`, so the kernel reduces to test the shape).
  Carrier-abstraction helps the lemma's PROOF; it never helps the FOLD's unification. To use a cocycle fold the goal
  must FIRST be made SYNTACTICALLY a cocycle instance (all legs one shape, no defeq-not-syntactic mismatch) — which
  is the original wall. → the iso/functor-level FBC ring-square glue is STUCK on both sub-routes (carrier-bearing
  iter-024, carrier-free iter-026); pivot to a pointwise sheaf-free proof or a syntactic re-shape.
- **(iter-025 conjecture, NOW REFUTED — see above) Escape a carrier-whnf kernel bomb by ABSTRACTING the carrier
  out of the statement, then `exact`.**
  When a coherence equation between composites over a heavy carrier (`tilde` sheafification, `pullback (Spec _)`,
  `extendScalars`) is well-typed but over-budget (elaborates @800k-hb, bombs @200k-hb; `maxHeartbeats` forbidden),
  the term is fine — every TACTIC that forces a defeq across the carrier (`simp`/`rw`/`congr`/`congrArg (Iso.app ·)`)
  is what bombs (motive re-check over the carrier). The PROPOSED fix (abstract cocycle, prove by mate calculus, close
  with a SINGLE `exact cocycle … hyps`) was conjectured kernel-light because unification was thought to BIND the
  carriers to metavars without reducing them — **iter-026 cold-build refuted this** (the fold whnf-bombs anyway).
  Still-valid residue: the closed Iso-level telescoping primitives Mathlib LACKS — `conjugateIsoEquiv_comp` /
  `conjugateIsoEquiv_symm_comp` (project-side, iter-025, carrier-free, `Iso.ext`+`conjugateIsoEquiv_apply_hom`+
  `conjugateEquiv_comp`); the COLD `lake build`-only test discipline (LSP/`lean_run_code` hide the timeout); and the
  real Mathlib mate API (`Adjunction.Mates`: `mateEquiv_vcomp`/`_hcomp`, `iterated_mateEquiv_conjugateEquiv`;
  `CatCommSq.hComp`) — usable for a cocycle's PROOF, just not for a carrier-dodging fold.

- **Make an object-def's `.app (tilde M)` fold SYNTACTIC by re-basing the def body on its `…Nat.app (tilde M)`
  form (iter-024 `fbc-geom-reorder`, landed cold-green).** When an object-level comparison `comparison M` is
  the distributed three-factor `≪≫` of an `.app (tilde M)` over a functor-level nat-iso, folding it against
  the nat form forces a defeq over `pullback (Spec _).obj (tilde M)` → sheafification whnf kernel bomb.
  FIX (plan-phase refactor, NOT a prover): reorder the functor-level `comparisonNat` (+ its deps) BEFORE the
  object def, then redefine the object def body as `exact (comparisonNat ψ φ ρ).app (tilde M)` (same type,
  defeq to the distributed form; all existing statement/`exact`-delegation uses are defeq-tolerant). The fold
  then closes by `rfl`/defeq on that leg. CAVEAT (iter-024): this only fixes ONE leg — a glue with multiple
  legs crossing `.obj (tilde M)` needs EVERY leg re-based, else the un-rebased legs still whnf-bomb (the
  three non-geom `pullbackSpecTildeNatIso` legs were the residual wall). Companion kernel-safe bridge for
  `extendScalars`-carrier (no sheafification) legs: `chartBaseChangeModuleReassoc_eq_natApp` (`congr 1` close).

- **FBC mate-leg at NAT-TRANS level = hom-level reading of a CLOSED Iso mate leg (iter-023, CLOSED
  `ring_square_glue_geom_leg_nat` + `ring_square_glue_alg_leg_nat` cold-green, axiom-clean; CORRECTS iter-022's
  "leg-nat lemmas not independently closable" claim).** To state the natural-transformation form of a mate
  coherence consumed by a telescope, do NOT chase the blueprint's abstract `vcomp`-phrasing
  (`conjugateEquiv_mateEquiv_vcomp` / `mateEquiv_conjugateEquiv_vcomp`). State it as the **hom-level
  `conjugateEquiv` reading of the already-closed Iso-level mate leg** and close in 3 lines:
  `have h := congrArg Iso.hom (<closed_Iso_mate_lemma> …); rw [conjugateIsoEquiv_apply_hom] at h; exact h`
  (`conjugateIsoEquiv` is `@[simps]` ⇒ `conjugateIsoEquiv_apply_hom : (conjugateIsoEquiv adj₁ adj₂ α).hom =
  conjugateEquiv adj₁ adj₂ α.hom`). KERNEL-LIGHT: no component evaluated, no `tilde M` carrier whnf. Same recipe
  for geom (`chartBaseChangeGeometricComparison_mate`) and alg (`chartBaseChangeModuleReassoc_extendScalarsComp`)
  legs. Companion functor-level dictionary: `pullbackSpecTildeNatIso := conjugateIsoEquiv.symm
  (gammaPushforwardNatIso φ)` with `pullbackSpecTildeNatIso_app : (…).app M = pullback_spec_tilde_iso φ M := rfl`.

- **FBC iterated-mate LINCHPIN via `iterated_mateEquiv_conjugateEquiv` specialization (iter-022, CLOSED
  `ring_square_glue_pst_iterated_mate` cold-green + axiom-clean).** The conjugate of a TwoSquare over a
  BINARY composite adjunction equals the iterated single-step mate: `conjugateEquiv adjL adjR α =
  ((mateEquiv adj₄ …) ((mateEquiv adj₁ …) α)).natTrans`, closed simply as
  `(iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α).symm`. Adjunction matching MUST be verified:
  here `adj₁ = tilde.adjunction R`, `adj₂ = tilde.adjunction R'`, `adj₃ = extendRestrictScalarsAdj φ.hom`,
  `adj₄ = pullbackPushforwardAdjunction (Spec.map φ)`, with `adj₁.comp adj₄ = adjL`, `adj₃.comp adj₂ = adjR`.
  CONFIRMED REAL (`Mathlib/CategoryTheory/Adjunction/Mates.lean` L450,456, pinned b80f227):
  `iterated_mateEquiv_conjugateEquiv` + inverse companion `iterated_mateEquiv_conjugateEquiv_symm` (the tool
  for a RIGHT-adjoint square, e.g. `gammaPushforwardNatIso`) + `conjugateEquiv_symm_comp` (telescope fusion)
  + the TwoSquare-valued `conjugateEquiv_mateEquiv_vcomp` / `mateEquiv_conjugateEquiv_vcomp` (whiskerings are
  `TwoSquare.whiskerLeft/Right/Top/Bottom` pastings, NOT `Functor.whisker*`; recover NatTrans via `.natTrans`
  / `TwoSquare.equivNatTrans`). Definitional whisker-app folds: `H.map (Φ.app M) = (Functor.whiskerRight Φ H).app M`
  and `Φ.app (F.obj M) = (Functor.whiskerLeft F Φ).app M`, both `:= rfl` — name is `Functor.whiskerRight`/
  `Functor.whiskerLeft`, NOT `CategoryTheory.whiskerRight` (unknown identifier in this toolchain). This is the
  decomposition engine for the remaining four-leg natTrans telescope (`ring_square_glue_natTrans`) that gates
  the glue.
- **SNAP unitor bridge over the localized-monoidal boundary — `tensorObjUnitIso_eq_localizedLeftUnitor`
  (iter-021, CLOSED sorry-free, cold-green, axiom-clean; the leandag-READY net-progress bridge NOT gated on
  the blocked associator).** To prove `(hand-built unitor iso) = (object iso) ≫ (localized λ^loc)` between the
  `modulesLocalizedMonoidal X` synonym and the `LocalizedMonoidal` comp-instance: `apply Iso.ext`; `symm; rw
  [← Iso.eq_inv_comp]` isolate the localized unitor; `cancel_epi (𝟙 ◁ c_G)`; **`erw [MonoidalCategory.leftUnitor_naturality]`**
  to bridge `unitModule X` vs `𝟙_` and reduce a GENERAL object `G` to `L'G♭` along the counit `c_G` (REQUIRED —
  `Localization.Monoidal.leftUnitor_hom_app`/`rightUnitor_hom_app` fire ONLY at `(L').obj _`); then `rw
  [leftUnitor_hom_app]`; collapse the `c_G`/`c_G⁻¹` pair via `← id_tensorHom` + **`erw [tensorHom_comp_tensorHom_assoc]`**
  + `Iso.hom_inv_id` + `tensorHom_id`; `rfl` closes the light residual (`toMonoidalCategory=sheafification`,
  `𝟙_psh=(unitModule X)♭`, μ object-args). **REUSABLE:** the `unitModule X`↔`𝟙_` token-divergence AND the
  `modulesLocalizedMonoidal`↔`LocalizedMonoidal` comp-instance divergence BOTH block `rw`/`cancel_epi`/`Category.assoc`
  EXACTLY like the μ-divergence; **`erw` bridges both**, and the final assoc/object residual closes by plain `rfl`
  because the goal is LIGHT (no deep μ nesting — contrast the associator wall). `MonoidalCategory.braiding_leftUnitor
  (X) : (β_ X 𝟙).hom ≫ (λ_ X).hom = (ρ_ X).hom` is REAL — the key for the right-unitor bridge.
- **FBC mate-leg engine — `← conjugateEquiv_comp` split over per-piece coherences (iter-018, CLOSED BOTH b2
  mate legs `chartBaseChangeGeometricComparison_mate` + `chartBaseChangeModuleReassoc_extendScalarsComp`
  cold-green + axiom-clean, review-verified sorryAx-free).** To prove a 3-factor mate identity
  `conjugateEquiv(comparison).hom = pushforward/restrict composite`: (1) `apply Iso.ext; rw
  [conjugateIsoEquiv_apply_hom]`; (2) **KEY unfold** `simp only [<the Nat defs>, eq_mpr_eq_cast, cast_eq,
  Iso.trans_hom, Iso.symm_hom (, eqToIso.hom)]` — **`eq_mpr_eq_cast, cast_eq` DISSOLVE the `letI : Algebra …`-
  induced `Eq.mpr` casts** that were the iter-011..017 "cast blocker" (they vanish under these simp lemmas, NOT
  a residual cast to strip); (3) `set` the ring maps + composite/midpoint adjunctions; (4) split the right-assoc
  conjugate with `← CategoryTheory.conjugateEquiv_comp` (×2, midpoints supplied EXPLICITLY); (5) discharge
  per-factor by the REAL per-piece coherences — geom: `Scheme.Modules.conjugateEquiv_pullbackComp_inv` (REAL
  Mathlib, Sheaf.lean:238, @[simp]); alg: `conjugateEquiv_extendScalarsComp` (iter-017) — plus a tiny congruence
  helper (`conjugateEquiv_pullbackCongr` / `conjugateEquiv_extendScalars_eqToHom`, latter needs `h` supplied
  explicitly since bare `rw` can't infer the Prop) + an inverted `f3` iso-calc. **TRAP (algebraic leg): you MUST
  re-declare the three `letI : Algebra …` instances at the proof head or `includeLeftRingHom`'s `(R:=)(A:=)(B:=)`
  cannot synthesize and every `set` silently breaks to `CommRingCat.ofHom sorry`.** Drive entirely by CLOSED
  coherences — NEVER `unit_conjugateEquiv` over the composite (that is the 200k-hb whnf bomb).
- **SNAP statement-pin BREAKS the 7-iter reassoc wall — `tensorObjAssoc_hK_lhs_native` (iter-018; the
  `rw [Category.assoc]` wall is DOWN; the reassoc chain proves bomb-free, cold-build GREEN 2441 jobs).** The
  iter-017 reassoc-wall `(W≫T)≫α → W≫(T≫α)` is defeated by STATEMENT-level object-pinning: state the lemma with
  every comparison-μ object-arg in **unfolded image form** `sheafification.obj (tensorObj (C := MonoidalPresheaf X)
  A♭ B♭)`, never folded `A.tensorObj B`. Then `rw [Category.assoc, Localization.Monoidal.associator_naturality]`
  (NO explicit args — explicit args make `rw` miss) → `erw [associator_hom_app]` → `simp only [sheafification,
  toMonoidalCategory, tensorHom_id, id_tensorHom, Category.assoc]` → `erw [← whiskerRight_comp_assoc]` →
  `conv_lhs => enter [2,1]; rw [Category.assoc]; erw [Iso.inv_hom_id]` + `erw [Category.comp_id]` ALL fire
  bomb-free. **CONFIRMED:** in-proof `simp only [tensorObj]; rw [...]` on the FOLDED goal STILL bombs — the pin
  MUST be at STATEMENT level (refutes inlining). (Residual = the final head-lemma application over the full-`tail`
  goal still bombs — see Known Blockers.)

- **Adjoint-mate UNIQUENESS via the unit transpose — `natTrans_ext_of_unit` (iter-017, FBC, CLOSED
  `conjugateEquiv_extendScalarsComp` cold-green + NEW reusable general helper).** To prove an adjoint-mate
  identity `conjugateEquiv … (f).hom = g` between two natTrans `R₁ ⟶ R₂` of right adjoints, do NOT go
  element-wise (the `∘ₗ`/`restrictScalars`-nesting value-diamond blocks `LinearMap.comp_apply`/`rw`/`simp`;
  `erw` over-unfolds the counit to raw `TensorProduct.lift` — DEAD) and do NOT use the counit transpose
  (CIRCULAR — `conjugateEquiv_counit` rewrites back to the original goal). The UNIT form is the one with
  Mathlib content: prove the general lemma `natTrans_ext_of_unit` — two natTrans with the SAME unit transpose
  against a fixed `α` are equal (each pinned to the triangle-identity formula
  `adj₂.unit.app (R₁.obj Y) ≫ R₂.map (α.app _) ≫ R₂.map (adj₁.counit.app Y)`) — then discharge the two unit
  relations: the `conjugateEquiv` side by `unit_conjugateEquiv`, the target side by Mathlib's
  `ModuleCat.homEquiv_extendScalarsComp` (read off via `Adjunction.comp_unit_app` + `homEquiv_unit`).
  TOOLING (reusable, ABSTRACT category): `rw`/`simp only` mysteriously FAIL to match `≫`-subterms with
  `.app`/`.map` heads (`right_triangle_components`, `NatTrans.naturality`) — surface form defeq-obscured;
  only FULL `simp` matches. Idiom: `have e1 : … := by simp` (insert the triangle), `rw [e1, Category.assoc]`,
  then `simp [reassoc_of% (hδ (R₁.obj Y))]`.
- **Bomb-free transformer principle for localized-tensor-μ goals (iter-017, SNAP, committed step (a) of
  `hK_lhs` cold-green).** On a goal carrying `Localization.Monoidal.μ` at folded localized-tensor objects,
  the ONLY transformation that does not isDefEq/whnf-bomb (200k hb) is an equation whose TWO SIDES ARE EXACT
  CURRENT-GOAL SUBTERMS, applied by `congrArg`-peel of the whole surrounding context written with holes:
  `refine (congrArg (fun t => μ.inv ≫ t ≫ _) hsplit).trans ?_`. Build that equation as a standalone
  `have hsplit` whose RHS type FLOWS FROM the goal (so it elaborates) and whose proof is `rw [← tensorHom_id,
  ← tensor_comp]; congr 1` — `congr 1`/term-mode is bomb-free where `rw [Category.assoc]`/`Category.id_comp`
  BOMB even isolated. Substituting via `rw [hsplit]`/`conv => rw [hsplit]` MOTIVE-bombs — only the
  `congrArg`-peel works. ANY generic lemma (`Category.assoc`, `associator_naturality` on the main goal,
  `Category.id_comp`) introduces fresh implicit OBJECT args that whnf `μ` → `Localization.fac` → bomb.
- **DUAL-`MonoidalCategory`-instance μ-token-identity cancel (iter-016, SNAP, CLOSED `tensorObjAssoc_hK_lhs_head`
  cold-green — defeated the 5-iter μ-syntactic-identity wall).** The 5-iter wall was NOT a hidden
  `Localization.fac`/`IsIso` witness (`Localization.Monoidal.μ` has none → Subsingleton/convert VACUOUS) and NOT
  a missing cancel lemma (`Iso.hom_inv_id_assoc` IS right) — it is a **project-local DUAL `MonoidalCategory`
  instance** (`pshModMonoidal` bare L1402 vs the `MonoidalPresheaf X` synonym the keystone uses) making the two
  μ object-args token-divergent. FIX (analogist `snap-mu-identity` + prover): pin inner tensors to
  `(C := MonoidalPresheaf X)` at **STATEMENT** level. Pinning is NECESSARY but NOT sufficient — two more facts:
  (1) μ-pairs stay defeq-but-token-divergent even after pinning (divergence under pp `⋯` truncation, invisible
  via pp.all) → cancel fires with **`erw [Iso.hom_inv_id_assoc]`** (reducible), NOT `rw` (pattern-not-found);
  (2) the cancel/triangle rewrite BOMBS in the full goal (motive re-typechecks surrounding μ → isDefEq 200k hb)
  → must **ISOLATE each step in `slice`/`have`** (local motive, no μ). Same idiom defeats the interchange MERGE
  wall: `slice_lhs i j => erw [← Localization.Monoidal.tensor_comp]`. In-proof `show`/`rfl`/`convert` pinning
  isDefEq-BOMBS — pinning must be at the STATEMENT. Durable fix (queued) = delete the bare dual instance.
- **FBC morphism-level identity-bridge close across a category-instance junction (iter-016, CLOSED
  `gammaPushforwardIso_comp_bridge` cold-green).** When `F.map (iso.inv.app N)` must reduce to `𝟙` but
  `F`'s domain and the `𝟙`'s ambient category are defeq-not-syntactic (`(Spec (CommRingCat.of ↑R)).Modules`
  vs `(Spec R).Modules`), naive `rw [Functor.map_id]`/`[eqToHom_map]`/`[F.map_id]` all FAIL "pattern not found".
  FIX: rewrite the inner morphism to `eqToHom rfl` via `hom_ext` + a per-open rfl-lemma (`pushforwardComp_inv_app_app`)
  + `Hom.id_app`, then `rw [eqToHom_refl]; exact Category.comp_id _` (TERM mode — `comp_id` unifies up to defeq
  cheaply because the identity carries NO value-ModuleCat content, so NO kernel bomb); residual `eqToHom = eqToHom`
  by proof-irrelevance. This is the route that finally beat the iter-011..014 RHS-reduction kernel bomb.
- **VALIDATED μ-cancel across the localized-synonym / `X.Modules` comp-instance boundary (iter-013, SNAP
  analogist, cold-LSP-verified on the real `hK_rhs` goal, 0 errors).** When a keystone composite (internal
  `≫` = `modulesLocalizedMonoidal X` = `LocalizedMonoidal` comp) is `erw`'d into an `X.Modules`-comp context
  (e.g. the `μ.inv` from `tensorObjLocalizedIso`), the two `≫` are defeq-but-DISTINCT instance terms and the
  `μ.hom ≫ μ.inv` pair will not cancel by `rw`/`simp [Category.assoc]` (pattern-not-found / no-progress),
  by `Iso.hom_inv_id_assoc` without a peel (adjacency not reached), or by a 2nd unshielded `erw [Category.assoc]`
  (catastrophically whnf-unfolds `Localization.Monoidal.μ` → `Functor.curry.mapIso (Localization.fac …)`).
  THE CLOSE: `erw [Category.assoc]; refine congrArg (fun t => _ ≫ t) ?_  -- MANDATORY leading-μ.inv peel/shield;
  erw [Category.assoc, Iso.hom_inv_id_assoc]`. `erw` absorbs BOTH the comp-instance and the μ-object-arg defeqs
  up-to-reducible. No new lemma / no comp-unification needed (the "restate keystones to unify comps" idea is
  REFUTED). Residual closes by `μ_natural_right`/`_left` + counit triangle `L'η ≫ c = 𝟙`. Authority:
  `analogies/snap-localized-comp-cancel.md`. The `congrArg` peel is the proof's own existing idiom and is
  non-optional (prevents the μ-unfold blow-up).
- **`show`-to-uniform-localized-form unblock for the MIXED `⊗ₘ`(localized)/`≫`(X.Modules) comp-instance
  (iter-014, SNAP, LANDED `hK_rhs` sorry-free, cold-build green; REUSABLE for `hK_lhs` + the 5 cascade
  coherences).** After the μ-cancel above, the residual counit-coherence goal is mixed-instance: the `⊗ₘ`
  is the `modulesLocalizedMonoidal X` tensorHom but the joining `≫` is the (defeq) `X.Modules` comp. Then
  EVERY interchange/assoc/whisker lemma refuses to fire — plain `rw`/`simp` find no pattern; bare `erw`
  resolves `C := X.Modules` which has NO `MonoidalCategory(Struct)` instance (synth fail); a
  `(C := modulesLocalizedMonoidal X)`-pinned `erw` whnf-BOMBS the μ. FIX: re-elaborate the whole goal into a
  UNIFORM all-localized form with a single `show` (one defeq cross, kernel-safe here), writing the whiskering
  and counit-`⊗ₘ`s with explicit `MonoidalCategoryStruct.whiskerLeft/tensorHom (C := modulesLocalizedMonoidal X)`
  (bare `◁`/`⊗ₘ` otherwise re-resolves the absent `X.Modules` monoidal instance). AFTER `show`, every `≫` is
  the localized comp, so: `simp only [← MonoidalCategory.id_tensorHom]; simp only [tensorHom_comp_tensorHom,
  Category.id_comp, Category.comp_id]` (merge), `congr 1` (first `⊗ₘ` factor `c_A` closes by congr-rfl),
  `simp only [sheafificationCounitIso]; erw [(…sheafificationAdjunction …).left_triangle_components_assoc]; rfl`.
  **NON-OBVIOUS: the merge MUST be `simp only [tensorHom_comp_tensorHom]`, NOT `rw`** — `rw` isDefEq-times-out
  on the localized-monoidal instance args even with uniform comp; `simp`'s discrimination-tree matching
  sidesteps it.
- **`slice`+`erw` junction idiom for `tensorObj`/`sheafification.obj` defeq (iter-010, SNAP).** When a
  rewrite target straddles a defeq junction between a hand-built object (`A.tensorObj (B.tensorObj C)`,
  from `tensorObjAssoc`'s codomain) and its sheafified form (`sheafification.obj (…)` /
  `toMonoidalCategory`-mapped), plain `rw`/`simp`/`reassoc_of%` report "did not find pattern" and
  full-goal `erw` deterministically times out at `whnf` (200000 hb). FIX: `slice_lhs/rhs i j => erw [h]`
  isolates the small composite so `erw` discharges only the LOCAL codomain defeq — cheap and reliable at
  every junction. Companion moves: state a collapse `have` with codomain explicitly ascribed to the goal's
  surface syntax (`… : _ ⟶ tensorObj A (tensorObj B C)`) so the later `erw` matches; and
  `simp only [Category.assoc]; rw [Iso.eq_inv_comp, asIso_hom]` to slide an `s.inv` onto the other side
  (prefixing by `s`), exposing counit/unit cancellations. LIMIT: this does NOT cancel a defeq `μ` hom-inv
  pair whose two occurrences carry different internal `⋙`-nesting — the matcher still cannot unify them in
  a giant goal, so `Iso.hom_inv_id_assoc` never fires. Canonicalize the `μ` object argument first (restate
  the producing lemma with the counit-object form `(toPresheafOfModules X).obj (sheafification.obj _)`).
- **μ-object fold via `simp only [tensorObj]` (iter-011, SNAP — UPDATES the canonicalization note above).**
  After restating the producing keystone in counit-object form (`…_eq_mu'` defeq wrappers), the two μ's
  become object-identical but still print via different unfoldings. The WINNING fold is `simp only
  [tensorObj]` (folds `tensorObjLocalizedIso`'s `A.tensorObj B` to the same `sheafification.obj (a⊗b)`) —
  verified both μ's then print identically. **DEAD END (do not retry): `rw [show μ_obj1 = μ_obj2 from rfl]`
  fails `motive is not type correct`** (the μ object sits in the *type* of an adjacent dependent whiskering
  morphism); `simp only [tensorObj]` sidesteps it. The object fold alone is necessary-not-sufficient — see
  the Known Blocker on the assembly cancel.
- **MORPHISM-LEVEL composition coherence beats the value-`ModuleCat`/`X.Modules` junction kernel bomb
  (iter-015, FBC, COLD-BUILD VERIFIED — 8318 jobs, closes `gammaPushforwardIso_comp` own body sorry-free).**
  When proving a `Γ`-comparison composition law `map(φ≫ρ) = map(φ) ≫ restr_φ(map(ρ)) ≫ restrictScalarsComp.inv`
  whose ring/coherence content is ALREADY baked into the single-map isos (`gammaPushforwardIso φ/ρ`), the
  composite law is pure BOOKKEEPING — do NOT descend to elements over the whole composite (that distributes
  the junction whnf past the kernel limit = the iter-011..014 bomb). Instead: (1) isolate the lone junction
  crossing in a standalone bridge lemma `Γ.map(cast ≫ pushforwardComp.inv) = eqToHom` (cross the junction
  ONCE); (2) `rw [bridge]`; (3) the RHS tail is identity-on-carrier by a SINGLE kernel-light rfl
  (`have htail : ∀ y, (…tail…) y = y := fun y => rfl`) that never touches the `φ≫ρ` junction; (4) collapse
  the LHS by `gammaPushforwardIso_hom_apply`; (5) close the residual `eqToHom` cast by
  `moduleCat_eqToHom_concreteCategory_apply` + `cast_heq`/proof-irrelevance. NO ring coherence
  (`globalSectionsIso_hom_comp3…`) is invoked at the composite level — it is absorbed defeq inside the per-map
  isos. Recipe: `analogies/fbc-morphism-comp.md`. (The leftover bridge sorry is a SEPARATE small goal — see
  Known Blocker.)
- **Kernel-light NatIso composition coherence (iter-011, FBC, reusable & cold-build verified).** To prove a
  natural-iso composition-coherence equality without a kernel bomb: `apply Iso.ext; apply NatTrans.ext;
  funext N` → a PURELY STRUCTURAL `simp only` (`Iso.trans_hom`, `NatTrans.comp_app`,
  `Functor.isoWhiskerRight/Left_hom`, `Functor.associator_{hom,inv}_app`, `Functor.whisker{Right,Left}_app`,
  `Category.{id_comp,comp_id,assoc}`, `NatIso.ofComponents_hom_app`) collapses the RHS pasting to the
  concrete per-component composite (associators become `𝟙`) → `exact <per_component_lemma> φ ρ N` (the `𝟙`s
  absorb by cheap `id_comp`, NOT the sheaf `whnf`). Bounds the kernel term to a single component. AVOID
  `ext N x` (element expansion = kernel bomb) and `change`/`rfl` defeq collapse (= cold-build `whnf`
  deterministic timeout). Closed `gammaPushforwardNatIso_comp`'s monolithic sorry this way.
- **Localized-monoidal synonym wiring (iter-004, SNAP, axiom-clean).** To get a symmetric monoidal
  structure on a localization `E` of a symmetric monoidal `D` (when a direct instance on `E` collides),
  instantiate Mathlib `CategoryTheory.LocalizedMonoidal L W ε`. Load-bearing engineering facts:
  (1) the bare presheaf-of-modules form does NOT synthesize `MonoidalCategory` — only the
  `PresheafOfModules (R ⋙ forget₂ …)` form does; add private `inferInstanceAs` re-export instances
  (`pshModMonoidal`/`Braided`/`Symmetric`). (2) `L`/`W` fed to `LocalizedMonoidal` must be the **literal**
  `PresheafOfModules.sheafification (𝟙 …)` / `inverseImage` class — wrapping in an `abbrev` (or
  domain-ascribing `L`) breaks the `IsLocalization` discr-tree key. (3) the synonym lives at `Type (u+1)`.
  (4) `ε` = `sheafificationCounitIso (unitModule X)` works because the unit module's underlying presheaf
  is the presheaf monoidal unit by `rfl`. (5) the only project obligation is `W.IsMonoidal`, got from the
  proved `ztensor_whisker_localIso` (whiskerRight) + braiding conjugation (whiskerLeft) via
  `isMonoidal_of_braided_whiskerRight`. CAVEAT: the synonym's `⊗` is NOT defeq to a hand-built
  `sheafification.obj(F.toPr ⊗_p G.toPr)` — transferring coherences needs explicit μ-transport bridge
  lemmas (object iso `tensorObj F G ≅ F ⊗_loc G`), not just `rw`.
- **Index-0 tensor-power rewriting (iter-004, SNAP).** `rw [show tensorPow L 0 = unitModule X from rfl]`
  FAILS "motive not type correct" (object in a dependent iso type); use a leading whole-goal
  `show … unitModule X …` (defeq) BEFORE any `rw`. `eqToIso` Nat-reindexers close by `congr 1` (proof
  irrelevance); blind `simp [← eqToIso_trans]` hits max-recursion. `β_{𝟙,𝟙}=𝟙` via
  `braiding_tensorUnit_left`+`MonoidalCategory.unitors_equal` then `sheafification.mapIso` = `Iso.refl`.
- **Crux-extraction to break a CHURNING monolith (iter-004, FBC).** When a frontier theorem churns
  (PARTIAL across iters, sorry won't shrink), move its post-`Iso.ext` residual into its own
  blueprint-pinned lemma and close the host by `exact <newlemma> args`. The host becomes sorry-free
  (transitively backed) AND the next prover gets a smaller named frontier target. The 2-categorical
  `pullback_spec_tilde_iso` naturality reduces via: `Iso.ext` → `.hom` cleanup → `Iso.eq_comp_inv` →
  `pullbackPushforwardAdjunction.homEquiv.injective` → `Adjunction.homEquiv_unit`; the deep tail is the
  per-leg identification of the dictionary's transpose with `gammaPushforwardNatIso` via
  `unit_conjugateEquiv` — effort-break it, don't re-run the monolith.
- **Per-chart base-change iso = `pullback_spec_tilde_iso` + reuse of `base_change_mate_regroupEquiv`, NOT bare
  `cancelBaseChange` (iter-003, FBC `baseChange_chart_tensorIso`, axiom-clean).** To build
  `Γ(V_B,F_B) ≅ Γ(V,F)⊗_A B` on an affine chart `V=Spec R` over `A`: step1 reads `Γ(V_B,F_B)≅(R⊗_AB)⊗_RM`
  via `(restrictScalars includeRight).mapIso (moduleSpecΓFunctor.mapIso (pullback_spec_tilde_iso ι M) ≪≫
  (tilde.toTildeΓNatIso.app _).symm)`; step2 cancels the base change B-linearly to `B⊗_AM` via
  `≪≫ base_change_mate_regroupEquiv ψ φ M`. TWO traps: (i) `tilde.toTildeΓNatIso.app N : N ≅ Γ(tilde N)`
  so the unit needs `.symm`; (ii) `TensorProduct.AlgebraTensorModule.cancelBaseChange` does NOT apply
  directly to `(R⊗_AB)⊗_RM → B⊗_AM` (it cancels the *second* tensor arg and forces `[Algebra A B]`; no
  `R→B` map exists) — route through `regroupEquiv`'s proved `comm ≫ cancelBaseChange ≫ comm`. Reuse (don't
  re-derive) the mate-region deliverable even though it sits below the use site.
- **`simp only [gMul_def]` unfolds nested graded-mult where positional `rw [gMul_def a b, …]` FAILS (iter-003,
  SNAP `sectionsMul_mul_assoc`).** Positional `rw [gMul_def a b]` errors "Did not find an occurrence of
  `GMul.mul ?m ?b`" on a doubly-nested `GMul.mul (GMul.mul a b) c`; `simp only [gMul_def]` unfolds all
  occurrences at once. Braiding rewrites: `rw [← Hbraid]` on the goal FAILS (TensorProduct instance mismatch
  CommRing-base vs RingCat-base) — use `Hel.symm.trans (congrArg (sectionsMul G F).hom Hbraid)`;
  `erw [ModuleCat.MonoidalCategory.braiding_hom_apply]` raises a spurious `CommRing ringCatSheaf` synth
  failure — the braiding-on-tmul is just `rfl` after `rw [happ]`. The μ-branch+section-core template
  (`rw [gMul_def, tensorPowAdd_<branch>, Iso.trans_hom]; show <N-app form>; sectionsCast_eqToIso_cancel;
  exact <section-core>`) reliably wires `sectionsMul_mul_one`/`_mul_comm` once the `tensorPowAdd_*` branch exists.
- **Adjunction-transpose section core — closes `Γ(structural-iso)(η(elementary tensor)) = …` (iter-002,
  SNAP `unitor_sectionsMul`, the engine that closed `sectionsMul_one_mul` axiom-clean).** For a sheaf-of-
  modules structural iso built as `sheafification.map (presheaf-iso) ≫ counitIso` (unitor/associator/
  braiding), proving its `Γ`-image sends the section multiplication `η(x⊗y)` to the expected value reduces
  to a transpose identity. Idiom: `have H := (adj.homEquiv _ _).apply_eq_iff_eq_symm_apply.mpr
  (Adjunction.homEquiv_counit adj _ _ _).symm` — the `homEquiv.symm` form **IS** the composite
  `map(presheaf-iso)^# ≫ ε`, and the `.mpr`'s defeq check silently absorbs `sheafification = adj.left` and
  `sheafificationCounitIso.hom = adj.counit.app G` (do NOT `rw [show … from rfl]` — it fails to match under
  `homEquiv`). Then `rw [Adjunction.homEquiv_unit] at H`; `congrArg (fun m => (m.app ⊤).hom (x⊗y)) H`
  (annotate the lambda's morphism type); `exact Hel.trans Hunit`. The presheaf-iso value at `⊤` is pinned by
  a `happ := rfl` over the **CommRingCat** ring `X.sheaf.obj.obj ⊤` (NOT the RingCat `X.ringCatSheaf`), then
  `erw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul]`. GOTCHA: `Adjunction.homEquiv_counit`
  takes `(adj X Y g)` EXPLICITLY — `(Adjunction.homEquiv_counit).symm` fails. The braiding case is simpler
  (unit-naturality only, no counit/triangle). This SUPERSEDES the iter-001 `:= rfl` whnf-timeout dead end.
- **`show` (default transparency) splits `Γ(f≫g)(x)` AND realigns elements where `rw` can't (iter-002,
  SNAP `sectionsMul_one_mul` outer reduction).** Under the `tensorObj`/`sheafification.obj` diamond,
  positional `rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]` binds `?x` at reducible
  transparency and fails ("Did not find pattern `(?f ≫ ?g).val`"); `rw [show tensorPow L 0 = unitModule X
  from rfl, …]` on a unit index gives "motive is not type correct". FIX: a single `show` at default
  transparency that both splits the composite application `Γ(A≪≫B)(s) = Γ(B)(Γ(A)(s))` and realigns the
  element to its `unitModule`/`(1:ring)` form; then `rw [sectionsCast_eqToIso_cancel]` cancels the reindex
  (proof-irrelevance makes `(zero_add n).symm` defeq the def's `(Nat.zero_add n).symm`). `val_app_top_comp`
  (term-mode `rfl`) is the standalone split lemma if needed.
- **FBC: wrap an `eqLocus` codomain in `ModuleCat.of <explicit groundRing carrier> (…)` (iter-002,
  `baseChange_sheafConditionFork_tensorIso` wiring).** Slotting a `≃ₗ` whose codomain is a
  `LinearMap.eqLocus` (a `Submodule`) into a `(ModuleCat.restrictScalars φ).obj (…)` fails "failed to
  synthesize AddCommMonoid" if you write `ModuleCat.of _ (eqLocus …)`; supply the carrier explicitly
  (`ModuleCat.of (groundRing (pullback X.toSpecΓ (Spec.map …))) (LinearMap.eqLocus …)`).

- **Value-ModuleCat tmul-bilinearity diamond — `← map_add; congr 2; exact tmul_lemma` (iter-001, SNAP
  SectionGradedRing GSemiring fields).** The section graded mult is `Γ(μ)(sectionsMul (a ⊗ₜ[CommRingCat ↑(X.sheaf.obj.obj ⊤)] b))`.
  The tmul scalar ring MUST be the **CommRingCat** carrier (only it has `CommSemiring`, needed by `TensorProduct`),
  but the `Module` instance on `sectionDeg L i` is keyed to the **RingCat** carrier (defeq, different keys). So
  standalone `TensorProduct.add_tmul/tmul_add/tmul_zero/zero_tmul` rewrites FAIL (`rw` leaves ring as `?m`; `simp only`
  "made no progress"; a `have` of the equality can't synth `Module (CommRingCat-ring) (sectionDeg L i)`). WORKING IDIOM:
  peel the two `ModuleCat.Hom.hom` maps with `← map_add`/`← map_zero`, then `congr 2`, then
  `exact TensorProduct.add_tmul a b c` (expected-type-driven elaboration binds the goal's bundled instances,
  sidestepping fresh synthesis). For zero fields, first expose RHS `0 = f (g 0)` via
  `conv_rhs => rw [← map_zero …, ← map_zero …]`. Closes all 4 bilinearity + 2 zero `GSemiring` fields. See [[snap-section-tmul-diamond]].
- **`ModuleCat.restrictScalars` FUNCTOR as B-linear transport when no scalar tower (iter-001, FBC
  `baseChangeEqLocusToPullbackGamma`).** To transport a `≃ₗ[groundRing X']`-equiv `eX'` to `≃ₗ[B]` when B acts only
  through a ring hom `φ = pullbackGroundRingAlg B` (so there is NO `IsScalarTower B (groundRing X') _` and
  `LinearEquiv.restrictScalars B` is "typeclass instance problem is stuck"): use the functor
  `((ModuleCat.restrictScalars φ).mapIso eX'.symm.toModuleIso).toLinearEquiv`. `ModuleCat.of R ↑M` is defeq `M`, so
  no `ofSelfIso` (absent this pin) is needed — the `.toModuleIso ≫ restrictScalars`-functor route lands on the
  bundled object directly.
- **Base-changed cover `iSup = ⊤` via FORWARD `Opens.map_iSup` (iter-001, FBC).** `rw [← TopologicalSpace.Opens.map_iSup]`
  fails HO-matching the `∘`-form. Instead: `have hmap := TopologicalSpace.Opens.map_iSup f.base U; rw [hU, TopologicalSpace.Opens.map_top] at hmap; exact hmap.symm`.
- **`:= rfl` split of `Γ((A ≪≫ B).hom)(s)` whnf-TIMEOUTS — do-not-retry (iter-001, SNAP `sectionsMul_one_mul`).**
  Stating `Γ(A≪≫B)(s) = Γ(B)(Γ(A)(s))` at `.val.app ⊤` as `:= rfl` unfolds `tensorPowAdd`'s match through the whole
  sheafification composite → `(deterministic) timeout at whnf` (200000 hb), build-verified. Use explicit
  `Iso.trans_hom` + `SheafOfModules.comp_val` (`Sheaf.lean:61`, rfl) + `NatTrans.comp_app` + term-mode ModuleCat
  comp-apply (the value-ModuleCat diamond). The companion `sectionsCast_eqToIso_cancel` (reindex cancellation) IS
  proven by `subst; rfl` and is reusable for all 4 coherence Eqs.

- **Triple-overlap C2 collapse via abstract-category folds (iter-080, GlueDescent keystone
  `glueChartComponent_leg_compat`).** The closing move for the conjugated-cocycle keystone: fold EACH leg of
  the fully-transposed component equation over the triple overlap `V_ipq` to a canonical N-factor `≫`-chain
  (`map_fold₅` = 5-factor functor-image fold stated in abstract categories, applied by unification;
  `side_collapse_left/right`), then discharge the whole equality by the SINGLE C2 cocycle hypothesis:
  `exact hL.trans ((final_cancel hC2h hcc hbb haa).trans hR.symm)`. Sequence intermediate regroupings with
  `reassoc_of%` / `← reassoc_of%`. Pair-level triangle step = `glueChartComponent_overlap_collapse`
  (`dsimp only [glueChartComponent]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl`).
  Under the X.Modules diamond, positional `rw` on the composite first-leg regroup fails (`Did not find an
  occurrence of R₁ ≫ R₂ ≫ R₃ ≫ R₄`) and `whnf` heartbeat-200000 timeouts appear mid-search — use the
  solved-form fold lemmas + `erw` for comp-node patterns. Realized `isIso_glueRestrictionHom` /
  `glueRestrictionIso` at 0 sorry. Consumes the [[Pair→triple verbatim transcription]] toolkit.
- **Pair→triple verbatim transcription (iter-079, GlueDescent triple-overlap toolkit).** Build a
  triple-overlap lemma family by copying the existing pair-level proofs verbatim under the substitution
  `ι_j ↦ f_pq ≫ ι_p`, `t_ij ≫ f_ji ↦ τ`, `f_ij ↦ q` (`τ = t'_ipq ≫ fst`, `q = fst ≫ f_ip`). ~13 lemmas
  (`glueData_triple_square`, `glueData_preimage_image_eq₃`, `glueTripleBaseChangeIso`,
  `glueTripleFactor_transpose/_mate`, `glueLegA/B_component_transpose`) compiled first/second try this way.
  `_app_app` iso-lemmas close by `ext x; rfl`. `glueData_preimage_image_eq₃` needs `ι_eq_iff` applied
  TWICE (at (i,p) AND (i,q)) — the second certifies the lift point is in `range fst`.
- **Post-`rw` X.Modules diamond escape (iter-079, recurs in BOTH GlueDescent + GrassmannianQuot).** After
  ANY `rw` under the `X.Modules`/composite-functor diamond, `simp only [Category.assoc]` makes NO progress
  (comp nodes acquire mixed-provenance instances) and bare `inv`/`infer_instance` fail to synthesize even
  when the `IsIso` is a same-lemma binder/`haveI`. Go term-mode: `congrArg (· ≫ g) h` for a calc step (`rw`'s
  closing `rfl` is reducible-transparency and misses proof-irrelevant/instance-path hidden args);
  `@CategoryTheory.inv _ _ _ _ (...) hinst` for the inverse; `IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 …)`
  (explicit-proof variant) for composites; `NatIso.isIso_map_iff (Scheme.Modules.pullbackComp p a) c` for
  pullback-map-comp IsIso. `rw [hε]` (counit = 𝟙) misses when codomain carries a `(𝟭 _).obj` wrapper — use
  `(eq_whisker hε _).symm.trans h`. Inside the `Modules` namespace, bare `pullback` resolves to
  `Scheme.Modules.pullback` — spell `Limits.pullback` explicitly.
- **Unused-`[Field K]` generalization (iter-079, `chart_point_eq`).** When a `[Field K]` lemma in a file you
  may not edit never touches field structure in its proof, copy the statement+proof verbatim over an
  arbitrary `CommRing K` (e.g. `existence_chart_kpoint_eq` → `chart_point_eq`).
- **Epi of free sheaves splits on affines via `tilde` + projectivity — the substitute for
  Mathlib's ABSENT `SheafOfModules` `Epi → IsLocallySurjective` / module-sheaf stalk theory
  (iter-078, GR `chartLocus_isOpenCover`).** To split an epi `φ : free ι ↠ free κ` over `Spec R`:
  conjugate through `AlgebraicGeometry.tildeFinsupp : tilde (ι →₀ R) ≅ free ι`; the fully-faithful
  `tilde.functor` reflects the epi to `ModuleCat R` where epi = surjective
  (`ModuleCat.epi_iff_surjective`); `Module.projective_lifting_property` (free ⇒ projective) gives a
  module-level section; transport back through `tilde.map`. KEY defeq: `CommRingCat.of ↥R = R` is `rfl`,
  so `tildeFinsupp` applies literally over `(Spec R).ringCatSheaf`. Downstream matrix right-inverse:
  `exists_rightInverse_of_epi_matrixEndRect` (Spec) → affine via `S.isoSpec` conjugation; the
  open-cover step needs `exists_isUnit_submatrix` (pure linear algebra: right-invertible matrix over a
  field has an invertible d-column minor — `Matrix.linearIndependent_cols_iff_isUnit` +
  `exists_linearIndependent` + basis cardinality), then `RingedSpace.isUnit_res_basicOpen` cuts the
  iso locus. This whole pipeline REPLACES the blueprint's stalkwise-Nakayama sketch on affines.
- **`asIso` deep in a long `≪≫` chain fails `IsIso` synthesis even with the `haveI` present — pass it
  EXPLICITLY (iter-078, SNAP `tensorObjAssoc`).** Inside a multi-segment iso composite, instance search
  runs in a metavariable-laden context and drops a `haveI`'d `IsIso` fact; use
  `@asIso _ _ _ _ f h` (h the explicit `IsIso` proof), never `asIso f` relying on synthesis. Companion
  (iter-078, `tensorPowAdd`): `MonoidalCategory.whiskerRightIso` with an ISO-valued first arg typed in
  `X.PresheafOfModules` breaks `(C := MonoidalPresheaf X)` unification ("failed to synthesize
  MonoidalCategory (MonoidalPresheaf X)"); rebuild as `Iso.mk` over the morphism-level
  `whiskerRight (C := MonoidalPresheaf X) ((toPresheafOfModules X).map e.hom)` with term-mode congruence
  identity proofs. `whiskerLeftIso` is fine (its first explicit arg is an object, not an iso).
  `include` directives must PRECEDE the docstring, not sit between docstring and `lemma` (else
  `unexpected token 'include'`).
- **Joint faithfulness of chart restrictions on a glued sheaf — `pullback_map_jointly_faithful`
  (iter-078, GlueDescent; the `lem:gr_modules_glue_unique` engine).** To prove `u = v` for two morphisms
  out of a `Scheme.Modules.glue` from `∀ i, ι_i^* u = ι_i^* v`: transfer pullback-agreement to
  `restrictFunctor` by `NatIso.naturality_2` conjugation, then `ext O x` +
  `TopCat.Sheaf.eq_of_locally_eq'` on the target's `Ab`-sheaf over the chart cover
  `{ι_i''(ι_i⁻¹O)}` (`D.ι_jointly_surjective`), with `mapPresheaf.naturality` moving the restriction
  inside the apps. This is the cancellation reduction lane-2 `tautologicalQuotient_epi` needs.

- **`Scheme.Hom.appTop (Y := Spec (CommRingCat.of …))` named-arg ascription dissolves the
  Γ(chart)/Γ(Spec) print-identical defeq mismatch — closed the GR C2 base-change bridges (iter-064).**
  When a statement mixes `appTop` of a morphism into a chart-`def` (e.g. `chartOverlap`) with `ΓSpecIso`
  terms, the two global-section objects are defeq but NOT syntactic, and `Matrix.map_map` /
  `rw [← Category.assoc]` / positional `rw [hp]` silently fail DOWNSTREAM. Pin the `Spec`-typed
  representation at the STATEMENT level with the `(Y := Spec (CommRingCat.of (Localization.Away …)))`
  ascription on `appTop`. Companions: (i) `rw [hp]` on a composite under `appTop` still misses (comp-node
  instance mismatch) — transport via `refine (congrArg (fun m => ΓSpecIso.inv ≫ appTop m) hp).trans ?_`;
  (ii) after a `simp` produces `↥(CommRingCat.of R)` vs `R` carrier mismatches, switch to a `calc` whose
  sub-goals are freshly elaborated; (iii) `simp only [RingHom.coe_comp, ← Matrix.map_map]` OVER-splits a
  fused `Θ ∘ ιR` and breaks the match with the Cramer cocycle L1 — split exactly the outer σ-layer;
  (iv) the matrix product recombines via bare `Matrix.map_mul.symm` (it is an equation, not a function).
- **Generic-context `glueLift` next to `glue` — `equalizer.lift` at the CONCRETE glued instantiation
  fails instance synthesis (iter-064, GR `tautologicalQuotient` skeleton).** Lifting a compatible family
  `k i : W ⟶ (ι_i)_* M_i` into `Scheme.Modules.glue …` by applying `equalizer.lift` at the concrete
  target fails `HasProduct`/`HasEqualizer` synth on the glue-unfolded beta-redex families (local `haveI`
  does not rescue). Build the lift as a GENERIC `def Scheme.Modules.glueLift` in the same elaboration
  environment as `glue` (where the instances resolve), via `equalizer.lift (Pi.lift k)` + `Pi.hom_ext` +
  `simp only [Category.assoc, Limits.Pi.lift_π, Limits.Pi.lift_π_assoc]`. GOTCHA: `limit.lift_π` does
  NOT see through the `Pi.π` def — use `Limits.Pi.lift_π`/`Pi.lift_π_assoc`.
- **`pullbackCongr` endpoint-cast collapse: generic `subst`-lemmas, then plain `rw` fires (iter-064,
  GR hom-level C2).** The `glueData_bridge_*` casts interleaved with free-pullback comparisons collapse
  via three generic lemmas (`pullbackFreeIso_inv_congr_hom`, `pullbackCongr_hom_app_free`,
  `pullbackFreeIso_inv_congr`: `Q_φ⁻¹ ≫ pullbackCongr(h).app(free) ≫ Q_ψ = 𝟙` etc.), each proved by
  `subst`+simp generic in the (equal) morphisms — the `pullbackFreeIso_trans_symm_eqToIso` discipline —
  so the kernel never whnfs a concrete immersion and the lemmas fire as ordinary `rw`s. The remaining
  matrixEnd fusion needs pure term-mode (`(Category.assoc _ _ _).symm.trans (congrArg (· ≫ Q.inv)
  ((matrixEnd_comp _ _).trans (congrArg matrixEnd hbridge))))` — `rw [reassoc_of% matrixEnd_comp]` hits
  mixed-provenance comp nodes and `rw [← Category.assoc]` grabs the scheme-level composite inside
  `pullbackFreeIso`'s argument. Budget `set_option maxHeartbeats 1600000` on the transport AND on the
  final `Iso.ext`-reduction (isDefEq/whnf cost of unifying inferred `.app _` instances across the
  diamond; kernel-validated at 40s cold build, no OOM).

- **`erw` bridges the `free`/`∐` value-diamond; `rw [← coherence_legs]; rfl` closes long associativity-equal
  `SheafOfModules` composites — closed GR `matrixEnd_pullback` (a) + `pullbackBaseChangeTransport_matrixToFreeIso`
  (c-core), iter-063.** When a subterm sits under `(pullback p).map (…)` or involves `free (Fin d) = ∐ unit`,
  the displayed term is identical but elaborated in a defeq-but-not-syntactic object form: `rw`/`simp` miss
  `ιFree_matrixEnd`/`Functor.map_comp`/`Functor.map_sum`/`Preadditive.comp_sum`/`Category.assoc`, but `erw`
  (defeq matching) fires. Per-entry matrix reduction: `reassoc_of% scalarEnd_pullback p (M k i)`. To distribute
  pullback over a `matrixEnd` row sum, reduce to one free injection with
  `Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback p) _ _ (SheafOfModules.isColimitFreeCofan (Fin d)))`
  + `simp only [cofan_mk_inj, Cofan.mk_pt]`; the cofan colimit needs `haveI := opensMap_final p` (Final instance).
  ASSEMBLY trick: `rw [Functor.map_comp, Functor.map_comp, matrixEnd_pullback]` matches with PLAIN `rw`, then
  build the two comparison legs as `have hfront`/`hback` and finish `rw [← hfront, ← hback]; rfl` — `rfl` closes
  the residual associativity where EVERY `Category.assoc` rewrite is obstructed (diamond / slice mis-index).
  **DANGER: never `erw [Category.assoc]` with a `pullbackComp.app.hom` leftmost factor** — it whnf's the OPAQUE
  `pullbackComp` into its full pseudofunctor definition (near-OOM). `pullbackFreeIso_comp` arg order: pass `(a)`
  then `(p)` to get `pullbackComp p a` / `p ≫ a`.

- **Functor-category (co)limit promotion via `evaluationJointlyReflectsColimits` + `isColimitMapCoconeCoforkEquiv`
  — closed SNAP `relativeTensorCoequalizerIso` (iter-063).** To exhibit a presheaf-level cofork as a colimit when
  every objectwise component is a known coequalizer: `evaluationJointlyReflectsColimits _ fun U => (isColimitMapCoconeCoforkEquiv ((evaluation _ _).obj U) <cofork-cond>).symm <objectwise IsColimit>`.
  `isColimitMapCoconeCoforkEquiv` is the crux — it commutes `evaluation.mapCocone` with `Cofork.ofπ`, dissolving
  the `parallelPair ⋙ G` vs `parallelPair (G.map f) (G.map g)` diagram-reindex friction (do NOT hand-build a
  `diagramIsoParallelPair`). Defeq does all apex/parallel-pair matching (`ev_U.map (relTensorActL) = aL` etc.).
  `CategoryTheory.Limits.evaluationJointlyReflectsColimits` (the colimit version) DOES exist
  (`Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean`) — leansearch fuzzy-misses it (only surfaces the
  `…Limits` version). Cofork condition reduces to objectwise by `ext U : 2` then the component `coeq_condition`
  (component coforks are defeq: NatTrans `.app U` ≡ the objectwise morphism; codomain ≡ `AddCommGrpCat.of (M⊗N)`
  via `PresheafOfModules.tensorObj_obj`).

- **`change`-to-nested-application bypasses the value-level ModuleCat diamond — closed the GR-quot L3 ATOM
  `scalarEnd_pullback` (iter-062, the hard-gate make-or-break).** When proving an equality of two
  composites evaluated at an element and EVERY `comp_apply` spelling fails to fire (`ModuleCat.hom_comp`,
  `CategoryTheory.comp_apply`, `ConcreteCategory.comp_apply`, `DFunLike.coe (ConcreteCategory.hom (f≫g))`
  — "pattern not found"), the value-level `SheafOfModules`/`ModuleCat` diamond is hiding the `f ≫ g` head
  (e.g. the unfolded `unitHomEquiv (f≫p)` is `sectionsMap p (unitHomEquiv f)`, no composite head). FIX:
  `change` the WHOLE goal directly into the fully **nested-application** form
  `g.val.app Y (f.val.app Y (1 : <explicit carrier>))` on both sides — dropping the comp heads makes the
  two sides defeq-navigable, and the residual closes by per-map computation lemmas
  (`scalarEnd_val_app_one`, `unitToPushforwardObjUnit_val_app_apply`, `map_one`,
  `pushforward_map_app_apply'`) + a comorphism naturality square (`ConcreteCategory.congr_hom` of
  `(toRingCatSheafHom p).hom.naturality (homOfLE le_top).op`). GOTCHAS: (1) the numeral `1` needs an
  explicit carrier ascription `(1 : S.ringCatSheaf.obj.obj Y)` (OfNat won't infer on the pushforward
  carrier); (2) sign the lemma `Scheme.{0}`, NOT `Scheme.{u}` — a `{u}` signature breaks
  `unitHomEquiv`/`sectionsMap` `DFunLike.coe` universe unification (universe-0 trap). The outer
  `scalarEnd_pullback` then closes by adjunction transpose: `apply (pullbackPushforwardAdjunction
  p).homEquiv _ _ |>.injective`, `homEquiv_naturality_left` for the LHS transpose, the RHS transpose
  `homEquiv_naturality_right` supplied as an explicit fully-applied TERM (positional `rw` can't match the
  identical-printing `homEquiv` under the `X.Modules` diamond — the standing `grquot-functor-dropped-termmode`
  discipline now also covers `Adjunction.homEquiv` naturality), then
  `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` + `exact unitToPushforward_scalarEnd_comm`.
- **A "missing base change" between affine section rings is usually NOT missing — build it from `Algebra.IsEpi`
  (iter-056, GF; dissolved a 5-iter STUCK).** The open-immersion flat-epimorphism base change
  `IsBaseChange Γ(S,V) (id)` framed as "Mathlib-absent" was fully constructible. Two reusable bricks:
  (1) `gf_isEpi_restrict_of_affine_le`: for affine `U ≤ V`, `Γ(S,V)→Γ(S,U)` is `Algebra.IsEpi`. Route:
  `rw [← CommRingCat.epi_iff_epi]`; `IsAffineOpen.map_fromSpec` gives `Spec.map ρ ≫ hV.fromSpec = hU.fromSpec`
  with `hU.fromSpec` an open-immersion **mono** ⟹ `Mono (Spec.map ρ)` (`mono_of_mono`); reflect through the
  fully-faithful `Scheme.Spec` (`Spec.fullyFaithful.faithful` → `Functor.mono_of_mono_map`) to `Mono ρ.op`, then
  `unop_epi_of_mono`. (2) `gf_flat_of_isEpi`: `[Algebra.IsEpi A R][Module.Flat A M]` (tower `A→R→M`) ⟹
  `Module.Flat R M`, 3 lines: `IsBaseChange.of_equiv (TensorProduct.lid' A R M)` (`lid'` from
  `Mathlib.Algebra.Algebra.Epi`) + `Module.Flat.isBaseChange`. Lesson: before accepting a "Mathlib-absent base
  change" verdict, search `Algebra.Epi`/`TensorProduct.lid'`/`CommRingCat.epi_iff_epi`.
- **Effective descent of a glued sheaf of modules = equalizer of pushforwards, NOT a hand-built
  compatible-families presheaf (iter-056, GR; closed the multi-iter `glue` keystone).** Build
  `Scheme.Modules.glue` as `Limits.equalizer a b` of two maps `∏ᶜ i, (D.ι i)_* (M i) ⇉ ∏ᶜ (i,j), (j_ij)_* (f_ij^* M i)`
  (`j_ij = D.f i j ≫ D.ι i`). Leg `a`: project to factor `i`, apply `pullbackPushforwardAdjunction (f_ij)` **unit**,
  push by `D.ι i`, reassoc via `pushforwardComp`. Leg `b`: factor `j`, adjunction unit for `t_ij ≫ f_ji`, push by
  `D.ι j`, `pushforwardComp`, transport across `(g i j).inv`, `pushforwardCongr` along the glue condition
  `(t_ij ≫ f_ji) ≫ ι_j = f_ij ≫ ι_i`. `X.Modules` `HasLimits` (Mathlib `AlgebraicGeometry/Modules/Sheaf.lean`), so
  the equalizer exists abstractly and is automatically a sheaf (pushforward + limits preserve the sheaf condition).
  The cocycle hyps `_hC1`/`_hC2` are NOT needed to construct the object (they pin downstream
  `glueRestrictionIso`/`glue_unique`). The hand-built compatible-families presheaf IS this equalizer — building it
  by hand re-derives the same object at far greater cost.
- **PresheafOfModules ℤ-tensor naturality is blocked by an `obj`-carrier vs `presheaf.obj`-carrier syntactic gap
  (iter-056, SNAP; `relTensorActL` blocker, NOT yet resolved).** The `tmul` induction element `m ⊗ₜ …` from
  `TensorProduct.induction_on` on `↥(P.obj U)` lives in the `P.obj`-carrier tensor; the only ℤ-linear restriction
  Mathlib provides (`(P.presheaf.map f).hom.toIntLinearMap`) has domain `↥((P.presheaf).obj U)`. These are rfl-defeq
  but syntactically distinct, so `TensorProduct.map_tmul`'s LHS won't unify. The reduction succeeds in isolation
  WHENEVER carriers agree. Changing the `obj` carriers to `(P.presheaf).obj ·` CASCADES (breaks proven
  `relTensorDomainPresheaf.map_id`/`map_comp`). Untried handle: build a DISTINCT `↥(P.obj ·)`-carrier ℤ-linear
  restriction (from `P.map f`/`ModuleCat.Hom.hom`) and use it uniformly so element & map carriers agree by
  construction. See [[snap-presheaf-promotion-carrier-gap]]. **RESOLVED iter-058** — the untried handle WORKED:
  `private def objRestrict P f` (a `↥(P.obj U)`-carrier ℤ-linear restriction) + `objRestrict_id`/`objRestrict_comp`
  laws. Follow-ons: (a) for *functoriality* avoid element-level `map_tmul` — collapse each ⊗-factor to
  `LinearMap.id`/comp at the LinearMap level (`objRestrict_id`/`_comp` + inline `hR` for the ring factor), then
  `TensorProduct.map_id`/`map_comp` + `rfl`; the diamond never bites at LinearMap level. (b) for *naturality*
  (actL/actR) close the tmul leaf by `change`-to-fully-reduced-form + `congr 1` + `PresheafOfModules.map_smul`
  (the single math fact); `objRestrict_apply` bridges to the abelian restriction by defeq. GOTCHA: `P.presheaf`
  is `Ab`/`AddCommGrpCat`-valued ⇒ use `AddCommGrpCat.hom_id`/`hom_comp`, NOT `ModuleCat.*`. The carrier gap
  reappears on the MIDDLE ring factor of nested triple/projection tensors (`objRestrict` only fixes P/Q).
- **Flatness transfers across a ring-iso + semilinear additive-iso via base change — `flat_of_ringEquiv_semilinear`
  (iter-058, GF; the general workhorse for `eqToHom`/presheaf-iso flatness transport).** Given `e : R ≃+* R'`,
  `l : M ≃+ M'` with `l (r•x) = e r • l x`, and `Module.Flat R M`: `M'` is the base change `R'⊗[R]M` (lift of `l`
  is `R'`-linear, explicit inverse `y↦1⊗l⁻¹y`), so `Module.Flat.isBaseChange` descends flatness. Companion
  `flat_localization_models` makes flatness model-independent (two localizations `Rₛ,Mₛ` vs `Rₛ',Mₛ'` of the same
  `A`-module) via `IsLocalization.algEquiv`(`.toRingEquiv`) + `IsLocalizedModule.linearEquiv` semilinearity. Pitfalls:
  (i) `open scoped TensorProduct in` goes on the line ABOVE the docstring (not between docstring and `theorem`,
  else "expected token"); (ii) route the ring-iso through `IsLocalization.algEquiv … .toRingEquiv` to dodge a
  `MulActionHomClass (Rₛ≃+*Rₛ') …` synth failure. To transport flatness along a presheaf-section equality
  `hbg : D g' = D g` whose target type DEPENDS on `D g` (`rw [←hbg]`/`hbg ▸` give an ill-typed motive), use
  `flat_of_ringEquiv_semilinear (RingEquiv.refl _) (F.presheaf.mapIso (eqToIso …)).addCommGroupIsoToAddEquiv ?_`.
- **Mathlib packages the whole cross-chart basic-open realisation — `exists_basicOpen_le_affine_inter` (iter-055,
  GF; closed a 2-iter STUCK).** To produce, at `x ∈ W ⊓ Wᵢ` (two affine charts), sections `g ∈ Γ(X,W)`,
  `ḡ ∈ Γ(X,Wᵢ)` with `D g = D ḡ`, `x ∈ D g`, and `D g ≤ W ⊓ Wᵢ`: do NOT hand-build via `b`/`IsLocalization.surj''`/
  `basicOpen_mul`. `AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hV x hx` returns exactly this
  (`basicOpen_basicOpen_is_basicOpen` under the hood); containments follow from `X.basicOpen_le` on each chart +
  the common-open equality (rewrite with `hbo.symm ▸ …` / `hbo ▸ …`). Used in `gf_common_basicOpen_basis`.
- **Modules-category diamond: `rw` cannot find right-associated sub-composites — term-mode only (iter-055, GR-quot;
  this closed `pullbackObjUnitToUnit_comp` + `functor.map_comp`, completing `functor`).** Under the `SheafOfModules`/
  `Scheme.Modules` category diamond, `rw` systematically fails to locate visibly-present right-associated composites
  (even on generic categories, even `← Category.assoc` on `a ≫ b ≫ c`). Discipline that works: (1) pure term-mode
  `calc`/nested `.trans` with explicit `Category.assoc _ _ _`, `CategoryTheory.whisker_eq`, `CategoryTheory.eq_whisker`,
  `congrArg`; (2) append a bare `rfl` to absorb a `rw`-left `X = X` that is defeq-but-not-syntactic; (3) **avoid
  `set`** — it injects metavar-unification conflicts (`?m := ιi` vs assigned `ιFree i`); inline the term instead;
  (4) `pullbackFreeIso φ I .hom` vs `pullbackObjFreeIso φ.toRingCatSheafHom I .hom` are defeq but block `congrArg` —
  restate the cofan-comparison `key_*` lemmas with explicit `pullbackFreeIso` types; (5) each pullback shifts the
  base ring sheaf `Tx ↝ Ty ↝ Tz`, so the trailing `ιFree (R := …)` indices DIFFER — getting them wrong yields
  "identical-looking `X = X`" mismatches. The `_comp` keystone itself: transpose under the composite
  pullback–pushforward adjunction (`apply comp.homEquiv.injective`), collapse LHS via new helper
  `homEquiv_conjugateEquiv_app` (mate/conjugate compatibility of `Adjunction.homEquiv`) used `refine hL.trans ?_`
  so opaque `pullbackComp` matches up to defeq; conjugate of `(pullbackComp b a).hom` = `(pushforwardComp b a).inv`
  via `conjugateEquiv_pullbackComp_inv` + `conjugateEquiv_comm` + `Iso.hom_comp_eq_id`; final section identity is
  `rfl` (`pushforwardComp_inv_app_app = 𝟙`). Resolves the open `_comp` obstruction noted in the `_id` pattern below.
- **Presheaf-of-modules apex CommRing routing — use `R ⋙ forget₂` form (iter-055, SNAP; de-risked the whole
  presheaf promotion).** `CommRing ↑(X.ringCatSheaf.obj.obj U)` is NOT synthesizable (the RingCat-level structure
  sheaf carries only `Ring`). FIX: `Mathlib/.../ModuleCat/Presheaf/Monoidal.lean` (L31) declares
  `instance : CommRing ((R ⋙ forget₂ _ RingCat).obj X)` for `R : Cᵒᵖ ⥤ CommRingCat`. So phrase the apex with the
  `R ⋙ forget₂ CommRingCat RingCat` form (= file-local `MonoidalPresheaf X`, with `R := X.sheaf.obj`); then
  `CommRing (R₀.obj U)` fires and `PresheafOfModules.Monoidal.tensorObj_obj` matches the objectwise
  `RelativeTensorCoequalizer.cofork` at `S := R₀.obj U` with NO instance diamond. **Do NOT** hand-roll
  `inferInstanceAs (CommRing ↑(X.sheaf.obj.obj U))` on the ringCatSheaf carrier — that creates a Module-instance
  diamond (`Module ↑S ↑(P.obj U)` then fails to synthesize).
- **Source-localization preserves flatness over a fixed base — `gf_flat_localizedModule_sameBase` (iter-053).**
  Tower `R → B → N`, `T : Submonoid B`, `[Module.Flat R N]` ⟹ `Module.Flat R (LocalizedModule T N)`. Mathlib's
  `Module.Flat.localizedModule`/`.of_isLocalizedModule` localize the *base* `R` (wrong direction); this localizes
  the *source* ring `B` while keeping `R` fixed — the one genuine gap of the GF source-span descent. Proof:
  `Module.Flat.iff_lTensor_injectiveₛ` (universe-of-`R` test, no `Small` side condition); for `N₀ ≤ P`,
  `(N₀.subtype).lTensor (LocalizedModule T N)` is the `T`-localization of `(N₀.subtype).lTensor N`
  (`IsLocalizedModule.map_lTensor` + `AlgebraTensorModule.coe_lTensor`); the latter injective
  (`Module.Flat.lTensor_preserves_injective_linearMap`), localization preserves injectivity
  (`IsLocalizedModule.map_injective`). GOTCHA: the canonical `Module R (LocalizedModule T N)` + `IsScalarTower`
  instances already exist — do NOT supply your own (diamond, `IsScalarTower` synth fails). Companion B1.0
  `gf_localizedModule_baseChange_tensor_comm` (`LocalizedModule T (N⊗[R]K) ≃ₗ[R] (LocalizedModule T N)⊗[R]K`):
  transport the Mathlib *instance* `IsLocalizedModule.rTensor` through `IsLocalizedModule.iso` + `.restrictScalars R`;
  needs `open TensorProduct`, drop the `≃ₗ` type annotation (Semiring inferInstance miss).
- **General `f^* free ≅ free` for ANY scheme morphism — `opensMap_final` (iter-053, GR-quot).** `pullbackObjFreeIso`
  needs `[F.Final]` for `F = Opens.map φ.base`; previously discharged only for open immersions/isos. `opensMap_final
  (φ : T'⟶T) : (Opens.map φ.base).Final` proves it for EVERY morphism: over each open `V` of the target the
  structured-arrow category `{U : V ≤ φ⁻¹U}` has terminal `⊤`, hence connected (`zigzag_isConnected` + terminal
  `StructuredArrow`). Unlocks `pullbackFreeIso` (general `f^* free ≅ free`) and `pullback_isLocallyFreeOfRank`
  (cover `{φ⁻¹U_i}` + `pullbackComp` + `morphismRestrict_ι` factorisation via `Scheme.Hom.iSup_preimage_eq_top`).
  Broadly reusable (likely GF/QUOT too). NOTE: `functor`'s two laws then reduce to the unit coherence
  `pullbackObjUnitToUnit (𝟙) = (pullbackId).app unit` — keep `pullbackId` OPAQUE (`simp [pullbackId]`
  whnf-times-out), navigate via `Adjunction.homEquiv_unit` + `conjugateEquiv_pullbackId_hom` + `leftAdjointIdIso`.
- **Conjugate-coherence defeq bridge closes `pullbackObjUnitToUnit_id` ⟹ `functor.map_id` (iter-054, GR-quot).**
  The unit coherence `pullbackObjUnitToUnit (𝟙 T) = (pullbackId T).hom.app unit` lands axiom-clean via:
  `rw [← pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit, Equiv.symm_apply_eq,
  Adjunction.homEquiv_unit]`, then `unit_conjugateEquiv Adjunction.id adj (pullbackId T).hom unit`. **KEY GOTCHA:**
  `conjugateEquiv_pullbackId_hom` is stated scheme-folded but the goal carries the `SheafOfModules`-UNFOLDED
  adjunction — direct `rw` fails. Fix: `have key : (conjugateEquiv …unfolded…) = (pushforwardId T).inv :=
  Scheme.Modules.conjugateEquiv_pullbackId_hom T` (Lean accepts the scheme lemma at the unfolded type BY DEFEQ),
  then `rw [key]` fires. `id_comp` via term-mode `Eq.trans ?_ (Category.id_comp _).symm` (positional `rw` hits
  the `T.Modules` diamond); finish `ext Y; rfl`. **Free upgrade `pullbackFreeIso_id`:** free-cofan ext reducing
  to the unit lemma — the cofan MUST be built over `SheafOfModules.pullback (toRingCatSheafHom (𝟙 T))`, NOT the
  `Scheme.Modules.pullback (𝟙 T)` wrapper (def-wrapped form diverges `PreservesColimit` instance search on a
  universe constraint, cf. `gf-seam1-1b1c-done`); two forms defeq-bridged. Use `cofan_mk_inj` (not `Cofan.mk_inj`);
  close the per-`i` goal term-mode (`exact (lemma).trans (…)`) — `rw`/`simp` fail on identical-printing terms with
  different implicit instances. **`map_comp` analogue DOES NOT yet close:** `pullbackComp = leftAdjointCompIso`
  whnf-times-out (200000) under `Iso.eq_inv_comp`/`simp [pullbackComp]`; must keep `pullbackComp` OPAQUE and go
  through `conjugateEquiv_pullbackComp_inv` — same defeq-bridge shape as `_id`, still open.
- **`Module.Flat` of a restriction algebra via the identity flat morphism (iter-054, GF B2.3).** To prove
  `Module.Flat Γ(S,V) Γ(S,U)` for affine `U ≤ V` (restriction algebra `(S.presheaf.map (homOfLE e).op).hom.toAlgebra`):
  `𝟙 S` is a flat morphism (`AlgebraicGeometry.Flat.instOfIsOpenImmersion`), so `Flat.flat_appLE (𝟙 S) hV hU e'`
  gives `((𝟙 S).appLE V U e').hom.Flat`, and `Scheme.Hom.appLE (𝟙 S) V U e' = S.presheaf.map (homOfLE e).op` (via
  `Scheme.Hom.id_app` — NOT `Scheme.id_app` — then `Category.id_comp` as a term `exact Category.id_comp _`, not
  positional `rw`); `RingHom.Flat` is DEFEQ `Module.Flat` for the restriction algebra so `exact` closes. GOTCHA:
  `.appLE` dot-notation fails on `𝟙 S` ("field projection on `CategoryStruct.toQuiver.1 S S`") — use the
  `Scheme.Hom.appLE (𝟙 S)` prefix form. This is the WEAKER form of the blueprint's `IsLocalization` claim, but
  flatness is all the flat-locality assembly consumes.
- **GF cross-chart matched pairs: restriction-match `g|_O=ḡ|_O` is NOT constructible — use basic-open equality
  (iter-054, do-not-retry).** Sections over an overlap `O=W⊓Wⱼ` need not extend to both affine charts; the standard
  cross-chart construction (`g|_{D(b)}=ḡ'/bⁿ` via `IsAffineOpen.isLocalization_basicOpen`+`IsLocalization.surj`,
  `ḡ:=b·ḡ'`) only yields `ḡ=unit·g` ON the overlap, giving `X.basicOpen g = X.basicOpen ḡ` (`Scheme.basicOpen_mul`)
  — NOT `g|_O=ḡ|_O`. The basic-open equality `D(g)=D(ḡ)` is the achievable AND sufficient invariant (it identifies
  `Γ(F,D(g))` as one group, all the two-leg transport B2.2 needs). State `gf_crossChart_spanning_cover` /
  `gf_common_basicOpen_basis` with basic-open equality.
- **`T.Modules` def-diamond breaks file-context category tactics (iter-053, GR-quot `functor`).** Under a
  `T.Modules`-typed goal, positional `rw`/`simp`/`Epi`-instance synth all fail in the FILE context (laxer in
  `lean_run_code`): `← Category.assoc`, `rw [hf]` inside `map (...)`, `haveI := x.epi` won't register. Fixes:
  term-mode `congrArg`/`.trans`/`Category.assoc` for setoid lemmas; fully-`@`-explicit `epi_comp`/`Functor.map_epi
  (… inferInstance … x.epi)` for the pullback-action epi; `Type`-cat functor `map` must be `TypeCat.ofHom`-wrapped
  (bare `Quotient.map`, a `→`, is rejected); law goals need `ext`/`Quotient.ind` (raw `funext` fails on
  `TypeCat.ofHom _ = 𝟙`). A `RankQuotient` bundling `F : T.Modules` lands in `Type 1`, not `Type`.
- **Relative tensor `M ⊗[S] N` as an `AddCommGrpCat` coequalizer — `TensorProduct.liftAddHom` (iter-053, SNAP).**
  Mathlib has NO categorical tensor-as-coequalizer, but `TensorProduct.liftAddHom` (`f : M →+ N →+ P`,
  `S`-balanced ⟹ `M ⊗[S] N →+ P`) IS the abelian universal property. Build `M⊗[S]N` as the objectwise
  coequalizer of the two `S`-action maps `M⊗[ℤ](S⊗[ℤ]N) ⇉ M⊗[ℤ]N` via `Cofork.IsColimit.mk`: existence =
  `liftAddHom` of the cofork map (balancedness from `s.condition`); uniqueness = `cancel_epi piMor` (epi via
  `ConcreteCategory.epi_of_surjective` + the projection's surjectivity) — PREFER this over `ext`+`induction`
  (which hits `AddCommGrpCat.Hom.hom` coercion-normalization friction on zero/add). Action maps via
  `TensorProduct.map` + `TensorProduct.assoc`; ℤ-scalar conditions in `LinearMap.mk₂` reduce to
  `smul_assoc`/`smul_comm` via canonical `IsScalarTower ℤ S M`; tmul-compute lemmas are `rfl`. Category is
  `AddCommGrpCat` (with `Ab` a reducible abbrev), NOT `AddCommGrp`. Presheaf promotion route (next step):
  `evaluationJointlyReflectsColimits` (objectwise colimits in functor cat) + `PresheafOfModules.Monoidal.tensorObj_obj`.
- **Flatness across a localized base — `IsLocalization.flat` + `Module.Flat.trans` (iter-052,
  `gf_stalk_flat_localBase`).** If `R'` is a localization of `R` at `S` (`IsLocalization S R'`) and `N` is
  `R'`-flat over a tower `R → R' → N` (`IsScalarTower R R' N`), then `N` is `R`-flat: `IsLocalization.flat R' S`
  gives `Flat R R'`, then `Module.Flat.trans R R' N`. This is the stalk-FREE algebraic core of a "stalk flat
  over local base" statement — no sheaf/stalk needed (see Known Blockers: `SheafOfModules.stalk` absent).
- **Source-side maximal-localization flatness — `Module.flat_of_isLocalized_maximal` (iter-052,
  `gf_flat_base_local_on_source`).** To prove `Module.Flat R N` for a `B`-module `N` (`B` an `R`-algebra),
  localize at the maximal ideals of the SOURCE ring `B` (not the base `R`): supply
  `∀ (Q : Ideal B) [Q.IsMaximal], Module.Flat R (LocalizedModule Q.primeCompl N)` with localized maps
  `fun _ _ => LocalizedModule.mkLinearMap _ _`. Mirrors Mathlib's `flat_of_localized_maximal` but over `B`.
- **Whnf-safe module base-change transport — `pullbackBaseChangeTransport` via `pullbackComp` (iter-052,
  GR-quot).** Given `g : a^*Mᵢ ≅ b^*Mⱼ` over `V` and `p : W ⟶ V`, build `(p≫a)^*Mᵢ ≅ (p≫b)^*Mⱼ` as
  `(pullbackComp p a).symm.app Mᵢ ≪≫ (pullback p).mapIso g ≪≫ (pullbackComp p b).app Mⱼ`. Arg order:
  `Scheme.Modules.pullbackComp p a : pullback a ⋙ pullback p ≅ pullback (p ≫ a)`. Whnf-safe because the
  morphisms are ABSTRACT glue-datum legs (cured the iter-051 `eqToHom` runaway). Triple-overlap endpoint
  alignment `glueData_bridge_{src,mid,tgt}` are pure Scheme-cat morphism equalities (`pullback.condition`,
  `t_fac`, `t_inv`, `cocycle_assoc`) where plain `rw` IS safe (no module diamond); insert them into a C2 Iso
  equation via `(pullbackCongr <bridge-eq>).app (M ?)`.
- **Sheafification-is-iso ⇔ underlying-map-in-`J.W` — `isIso_sheafification_map_iff` (iter-052, SNAP).**
  Specialise `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` to get
  `IsIso (sheafification.map f) ↔ J.W (toPresheaf.map f)`. GOTCHA: the `rw [e]` needs the `isomorphisms`
  argument written as `SheafOfModules X.ringCatSheaf` (NOT `X.Modules`, a non-reducible `def` `rw` won't match);
  bridge `X.Modules ↔ SheafOfModules X.ringCatSheaf` by a defeq `have h' : … := h` ascription. The unit half:
  `toPresheaf_map_sheafificationAdjunction_unit_app` is `rfl` (= `toSheafify`), then `GrothendieckTopology.W_toSheafify`.
- **Non-reducible-`def` form unification before instance synthesis (iter-051, GR-quot `chartQuotientMap_ιFree`).**
  A `def` that is *defeq* to `Spec (CommRingCat.of …)` but **non-reducible** (e.g. `affineChart d r I`) is NOT
  unfolded by instance search — `HasBiproduct (fun _ => unit (affineChart …).ringCatSheaf)` fails to synth while
  the `Spec`-form succeeds. A `scalarEnd ((ΓSpecIso A).inv …)` term forces the `Spec` form on the matrix, so a
  `change` that leaves the free/isoCoproduct legs in `affineChart` form mixes the two and the synth dies. **Fix:**
  `set A := CommRingCat.of …; set S := AlgebraicGeometry.Spec A` at the VERY TOP (initial goal has no
  `CommRingCat.of` syntactically, so `set` is safe), and write the whole `change` in `S.ringCatSheaf` form. `set A`
  AFTER the rewrite chain rewrites the def's innards and corrupts `affineChart`.
- **`epi_comp' inferInstance proof.epi` — explicit-args escape (iter-051, GF-G1 `gf_qcoh_finite_sections_of_genSections`).**
  When `Epi (f ≫ g)` instance synth fails because one factor's `Epi` is unfindable (here `Epi σ'.π` under a
  `let`-bound `σ'`, a `GeneratingSections.π`-abbrev reducibility quirk — fails even with a local `haveI`), use
  `CategoryTheory.epi_comp'` (the form taking the two `Epi` proofs as EXPLICIT arguments). `σ'.epi :
  Epi (freeHomEquiv.symm σ'.s)` is accepted for `Epi σ'.π` by defeq.
- **Instance-diamond goals → proof TERMS, not `rw`/`erw` (iter-051, GR-quot `chartQuotientMap_epi`).** On a goal
  whose `≫`/`𝟙`/`ιFree` carry instances baked by an opaque-elaborated context (`chartQuotientMap`), category
  `rw`/`simp only` fail to MATCH (`ιFree_freeMap`, `Category.comp_id`, `Sigma.ι_desc` all "pattern not found") and
  `erw` triggers a >200k-heartbeat `whnf` runaway. Build the equality as a defeq-tolerant **proof term**
  (`(ιFree_freeMap_assoc _ k _).trans (chartQuotientMap_ιFree …)).trans (Category.comp_id _).symm`). A single
  isolated `erw [Sigma.ι_desc_assoc]` is safe ONLY inside a helper with no opaque term in scope (post-`change`,
  consistent `Spec` form). Also: `scalarEnd_one`/`zero` — `map_one`/`map_zero` do NOT `rw` through the
  `ConcreteCategory.hom` coe; `change` to the `.val`-level then `exact map_one _` / `refine (map_zero _).trans ?_`.
- **Semilinear `Module.Finite` transport (iter-051, `module_finite_of_ringEquiv_semilinear`).** Mathlib has
  `Module.Finite.equiv` (same-ring linear) and `Module.Free.of_ringEquiv` (free across a ring iso) but NOT
  `Module.Finite` across a ring iso σ + a σ-semilinear additive iso `e` (`e (a•x) = σ a • e x`). Build it by
  `Submodule.span_induction` on a finite `R`-spanning set: its image `R'`-spans `M'`, using `he` in the `smul`
  case. (Mirrors `finite_localizedModule_of_isLocalizedModule`.)
- **Transport a `GeneratingSections` along a colimit/unit-preserving functor (iter-050, GF seam-1a engine
  `SheafOfModules.GeneratingSections.map`).** Analogue of Mathlib `Presentation.mapGenerators`: generator map
  `(mapFree F η σ.I).inv ≫ F.map σ.π`, epi via `preservesColimitsOfSize_shrink` → `PreservesColimitsOfShape
  WalkingSpan` + `epi_comp`; index type unchanged ⇒ `map_I` is `rfl`, finiteness via `map_isFiniteType`.
  **CRITICAL design fix:** take the colimit-preservation witness `hF : PreservesColimitsOfSize.{u,u} F` as an
  **EXPLICIT argument, not an instance** — instance search does NOT fire reliably through the
  `X.Modules := SheafOfModules.{u} X.ringCatSheaf` abbreviation (def, semireducible; instance registered under
  `Modules` form, search wants `SheafOfModules.{u}` form). **Universe gotcha:** `leftAdjoint_preservesColimits`
  shape-universe metavars pin ONLY when the term is an explicit arg whose expected type drives unification —
  they FAIL to pin in `haveI : T := term`. State finiteness-transport as a separate THEOREM (not instance): the
  anonymous `⟨…⟩` constructor for `IsFiniteType` defaults universes to 0; the theorem return type pins `{u,u,u}`.
  seam-1a route then = two `map` stages (slice→geometric via `overRestrictEquiv.functor`+`overRestrictUnitIso`+
  `equivOfIso overRestrictPullbackIso`, then geometric restriction via `pullback (open immersion)`+
  `pullbackOpenImmersionUnitIso`). DEAD ENDS: slice `pushforward` (right adjoint) does NOT preserve epi;
  `freeFunctorCompPullbackIso`/`pullbackObjFreeIso` need a separate `F.Final` (packaged by
  `pullbackOpenImmersionUnitIso` instead).
- **Linear combinations of sheaf-of-modules sections go through BIPRODUCTS, not `freeHomEquiv` (iter-050,
  GR-quot `chartQuotientMap`).** `(SheafOfModules.unit R).sections` has NO `AddCommGroup`/`Module` instance, so
  the "function-of-sections" `freeHomEquiv` route cannot express a matrix product. Realise a morphism of free
  sheaves `free (Fin r) ⟶ free (Fin d)` via `(biproduct.isoCoproduct _).symm.hom ≫ biproduct.matrix M ≫
  (biproduct.isoCoproduct _).hom` (bridging `free (Fin n) = ∐ unit` to `⨁ unit`). `HasFiniteBiproducts
  (SheafOfModules R)` is NOT a global instance — supply locally via `HasFiniteBiproducts.of_hasFiniteProducts`.
  Matrix entries `M i' p : End (unit R)` from ring elements via `Scheme.ΓSpecIso A |>.inv.hom` (→ `Γ(X,⊤)`) then
  `scalarEnd` (`unitHomEquiv` + a global unit section built by `PresheafOfModules.sectionsMk` with
  `fun Y => R.obj.map (homOfLE le_top).op a`, compatibility closing via `rw [← comp_apply, ← R.obj.map_comp];
  congr 1`). `End (unit R)` IS a `Ring`.

- **Affine Γ-epi from the `tilde.adjunction` counit — no H¹-vanishing / global exact functor (iter-047, GF
  seam 2 `gf_affine_qcoh_Gamma_epi`).** For qcoh `G,F` over `Spec R` and `π : G ⟶ F` `[Epi π]` with
  `[IsIso G.fromTildeΓ] [IsIso F.fromTildeΓ]`, `(moduleSpecΓFunctor.map π).hom` is surjective. Mechanism:
  `Scheme.Modules.fromTildeΓNatTrans.naturality` gives `tilde(Γπ) ≫ F.fromTildeΓ = G.fromTildeΓ ≫ π`; the
  app is only DEFEQ (not syntactic) to `M.fromTildeΓ`, so use `change … at hnat` (NOT `‹›`/`simp`) to rewrite
  the square into `…fromTildeΓ` form. Cancel the iso as a TERM `(IsIso.eq_comp_inv F.fromTildeΓ).mpr hnat`
  (`eq_comp_inv` takes the iso EXPLICIT; `Category.assoc`/`IsIso.hom_inv_id` `rw`/`simp only` silently fail to
  fire on the `(Spec R).Modules` diamond). Final epi via explicit `epi_comp (G.fromTildeΓ ≫ π) (inv F.fromTildeΓ)`
  + `haveI : Epi (inv …) := inferInstance` (`infer_instance` for `Epi (_≫_≫_)` TIMES OUT at 20k hb). Then
  `tilde.functor R` Fully Faithful ⟹ `ReflectsEpimorphisms` ⟹ `Functor.epi_of_epi_map` ⟹
  `ModuleCat.epi_iff_surjective`. Free-epi specialisation `gf_qcoh_finite_sections_of_free_epi`: discharge
  `[IsIso (tilde N).fromTildeΓ]` (= counit of fully-faithful LEFT adjoint at `tilde N`, `tilde.adjunction.counit
  = fromTildeΓNatTrans` by rfl) + `[Module.Finite R Γ(tilde N)]` (via the unit iso `N ≅ Γ(tilde N)`, needing
  `haveI : Module.Finite R ((𝟭 _).obj N) := inferInstanceAs …` — `(𝟭).obj N` only DEFEQ `N`). Recipe
  `analogies/gf-gamma-exact.md`.
- **Sheaf-of-modules tensor on `X.Modules` = sheafify the objectwise presheaf tensor (iter-047, SNAP layer 1
  `tensorObj`).** Mathlib's `PresheafOfModules.monoidalCategory` is stated for `PresheafOfModules (R ⋙ forget₂
  CommRingCat RingCat)`; instance resolution on `X.PresheafOfModules` FAILS (higher-order: can't solve
  `X.ringCatSheaf.obj =?= ?R ⋙ forget₂ _ _`). Fix: `abbrev MonoidalPresheaf X := _root_.PresheafOfModules
  (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)` — defeq `X.PresheafOfModules` but in the exact `_⋙ forget₂_`
  form so the monoidal instance fires first-order. TRAP: unqualified `PresheafOfModules` inside namespace
  `…Scheme.Modules` resolves to the SCHEME abbrev (takes a `Scheme`!) — use `_root_.PresheafOfModules`. Then
  `tensorObj F G := sheafification.obj (MonoidalCategory.tensorObj (C := MonoidalPresheaf X) F.toPsh G.toPsh)`,
  `sheafification := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`. Counit iso `sheafification.obj
  G.toPsh ≅ G` via `counit_isIso_of_R_fully_faithful` (the WHOLE-NatTrans iso instance — the per-component
  `IsIso (adj.counit.app G)` from `Adjunction/FullyFaithful.lean:90` does NOT synthesize). Unitors/braiding =
  `sheafification.mapIso (λ_/ρ_/β_ (C := MonoidalPresheaf X) …) ≪≫ sheafificationCounitIso` (the `(C := …)`
  ascription is required). Braiding needs NO strong-monoidality (does not nest sheafification in a tensor factor).
- **GF seam-1 affine finite standard subcover + free-epi repackaging (iter-049).** (ii)
  `gf_affine_finite_standard_subcover`: refine an arbitrary open cover `U : ι → X.Opens` of an affine `W` to a
  finite standard-basic-open subfamily. Per `x : W`, `TopologicalSpace.Opens.mem_iSup.mp (hcov x.2)` picks a
  member `U i ∋ x`; `hW.exists_basicOpen_le ⟨x,hi⟩ x.2` yields `f : Γ(X,W)` with `X.basicOpen f ≤ U i` and
  `x ∈ D(f)`; `choose` → `f : W → Γ(X,W)`; basic opens cover (`hW.self_le_iSup_basicOpen_iff`) ⟹
  `Ideal.span (range f) = ⊤`; `Ideal.span_eq_top_iff_finite` extracts the finite `t`. GOTCHA: inside
  `namespace AlgebraicGeometry`, `Opens.mem_iSup` is "unknown identifier" — must write
  `TopologicalSpace.Opens.mem_iSup`. (iii) `gf_finite_gen_iff_free_epi`: pure definitional repackaging of
  Mathlib's `SheafOfModules.GeneratingSections` — fwd `⟨σ,hσ⟩ ↦ ⟨σ.I, hσ.finite, σ.π, σ.epi⟩`; rev builds
  `GeneratingSections` with `s := M.freeHomEquiv π`, `epi` field recovered via `Equiv.symm_apply_apply`. State
  it in abstract `SheafOfModules.{u} R` generality (with `HasWeakSheafify`/`WEqualsLocallyBijective`/
  `HasSheafCompose` + explicit `.{v',u'}` universes) so it applies to the sliced `F.over Y` in the assembly.
- **SectionGradedRing `sectionsMul` — keep it a `ModuleCat ⟶`, never a `→ₗ`/`TensorProduct` (iter-049).** The
  lax-monoidal global-section multiplication is the Γ(⊤)-component of the sheafification-unit at the objectwise
  presheaf tensor: `((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op ⊤)` with
  `P = F.toPsh ⊗ G.toPsh` (objectwise = `Γ(F) ⊗_{Γ(𝒪)} Γ(G)`), codomain `(tensorObj F G).val.obj (op⊤)`
  (defeq by `rfl`). DEAD ENDS (ring-expression diamond — do NOT retry): a `TensorProduct R₀ Γ(F) Γ(G) →ₗ[R₀]`
  signature, or `.hom`-extracting to `→ₗ`. The native `Module` instance on `F.val.obj (op⊤)` is over
  `↑(X.ringCatSheaf.obj.obj (op⊤))` while the only firing `CommRing` is on `↑((X.sheaf.obj ⋙ forget₂).obj
  (op⊤))` (defeq but synthesis won't bridge); adding a local `CommRing` makes a Semiring diamond that BREAKS
  the ModuleCat instance. The `ModuleCat`-morphism form typechecks because the two object categories are defeq;
  `.hom` recovers the linear map downstream consistently in the `⋙ forget₂` ring world.
- **`IdealSheafData.ofIdeals` is the largest COHERENT sub-sheaf — single-`U` characterization is unprovable;
  use a GLOBAL hypothesis (iter-046, QUOT `annihilator_ideal`).** `annihilator F = ofIdeals (V ↦ Ann_{Γ(X,V)}
  Γ(F,V))`. The forward `(annihilator F).ideal U ≤ Ann …` is free (`annihilator_ideal_le` /
  `ideal_ofIdeals_le`). The REVERSE inclusion at a single affine `U` is NOT provable from finiteness at `U`
  alone: `ofIdeals` is `sSup {J | J.ideal ≤ family}`, so reaching the full `Ann_{Γ(X,U)}` value requires the
  family to be a coherent ideal sheaf (`map_ideal_basicOpen` at EVERY affine open) — a global condition.
  Correct deliverable = take `hfin : ∀ V : X.affineOpens, Module.Finite Γ(X,V) Γ(F,V)`, assemble the honest
  `I : IdealSheafData := ⟨fun V => Ann …, ?_, _, rfl⟩` (discharge `map_ideal_basicOpen` per-`V` with
  `annihilator_map_basicOpen F V f`), then `congr($(IdealSheafData.ofIdeals_ideal I).ideal U)` reads off the
  value at every `U` at once. Mirrors Mathlib `Scheme.Hom.ker_apply` (global `QuasiCompact`, not one-open).
  Needs `set_option backward.isDefEq.respectTransparency false` for the structure-literal defeq. The per-affine
  engine `annihilator_map_basicOpen` = `(Module.annihilator_isLocalizedModule_eq_map (powers f)
  (restrictBasicOpenₗ F f)).symm` after the local `compHom`-module + `IsScalarTower.of_algebraMap_smul` +
  `isLocalizedModule_basicOpen` (gap2) instance setup. DEAD END (do not retry): single-`U` reverse inclusion
  via `le_of_isLocalized_span` over a basic-open cover of `U` is CIRCULAR (reduces to the same reverse
  inclusion at each `D(fᵢ)`); the "section over `U` = ⨅ comap of local annihilators" formula is FALSE for
  `ofIdeals`. Single-`U` would need Mathlib-absent ideal-sheaf restriction-along-`U↪X` infra.
- **Composite-adjunction conjugate recognition — build adjR/β as standalone axiom-clean defs, NON-monolithic
  (iter-045).** For a depth-≥2 conjugate pair, do NOT assemble a monolithic depth-5 comparison `β` (the
  7-iter trap). Instead: (1) build the right adjunction `adjR` as a top-level `def` via `.comp` of the
  component adjunctions (`extendRestrictScalarsAdj.comp (tilde.adjunction.comp pullbackPushforwardAdjunction)`),
  (2) build the comparison nat-iso `β : R₁ ≅ R₂` by whiskering EXISTING legs
  (`isoWhiskerRight (pushforwardComp …).symm Γ ≪≫ associator ≪≫ isoWhiskerLeft … (gammaPushforwardNatIso …)
  ≪≫ associator.symm`), (3) confirm `conjugateEquiv adjL adjR` typechecks (pair well-formed) and
  `unit_conjugateEquiv_symm adjL adjR β.hom M` (`Mathlib.CategoryTheory.Adjunction.Mates`) gives the
  object-level coherence. Each piece `#print axioms`-clean before assembly. This RESOLVES the structural
  "can the pair be built / is it conjugate-comparable?" question independent of the downstream transport.
- **Local `letI`/`haveI` compHom module per basic open — NEVER a global instance (iter-045).** A global
  `instance : Module Γ(X,U) Γ(F, X.basicOpen f)` via `Module.compHom` causes a typeclass resolution LOOP
  (head unifies `U := X.basicOpen f`, recurses on the same goal). Set the compHom module + `IsScalarTower`
  as local `letI`/`haveI` inside the per-`g` block of an `of_localizationSpan_finite` proof.
- **Model-independence of localized-module finiteness is project-local (iter-045).** To transfer
  `Module.Finite Rₚ N` (an arbitrary localized model) to `Module.Finite (Localization S) (LocalizedModule S M)`
  (the canonical model), Mathlib has NO direct lemma (`Module.Finite.of_isLocalizedModule` is global→local
  only). Build it: `e := IsLocalizedModule.linearEquiv` (module side), `ψ := IsLocalization.algEquiv` (ring
  side), prove `e` is `ψ`-semilinear (clear the denominator via `Module.End.isUnit_iff` +
  `IsLocalization.mk'_spec` + `IsScalarTower.algebraMap_smul`), transport a spanning set by
  `Submodule.span_induction`. The section-localization keystone `isLocalizedModule_basicOpen` +
  `IsAffineOpen.isLocalization_basicOpen` feed this for the geometric G1 locality reduction (Stacks 01PB).
- **FBC i=0 is Čech-free.** `H⁰` of a quasi-coherent sheaf is the sheaf-condition
  equalizer, and flat `−⊗B` preserves equalizers — so flat base change at i=0 needs no
  Čech cohomology / spectral sequences (Mathlib-absent). Verified Mathlib inputs:
  `Module.Flat.ker_lTensor_eq`, `eqLocus_lTensor_eq`, `LinearMap.tensorKerEquiv`,
  `tensorEqLocusEquiv`, `cancelBaseChange`.
- **FBC affine close orientation:** the section-level map identifies as
  `Γ(α) = cancelBaseChange⁻¹` (inverse orientation). State helper lemmas in this provable
  orientation, not the reverse, or the sorry is unprovable as signed.
- **Locality-criterion lemmas are `.mpr` one-liners.** A "reduce to affine opens" lemma
  (e.g. `base_change_map_affine_local`) is just the backward direction of an existing
  `Modules.isIso_iff_isIso_app_affineOpens`-style criterion; body = `(criterion …).mpr H`.
  The real content is the per-open hypothesis `H` (the affine–affine section assertion),
  which is a *separate* objective. Cheap to extract; sharpens the residual.
- **Formalize the consumable consequence when the equality needs the blocked plumbing.**
  For the FBC mate lemma, formalizing `IsIso (Γ(α))` (rather than the literal equality
  `Θ_tgt ∘ Γ(α) ∘ Θ_src⁻¹ = cancelBaseChange⁻¹`) is faithful and non-vacuous (verified:
  `unfold` exposes the real base-change map; `moduleSpecΓFunctor` does not trivially reflect
  isos). Stating the equality needs the same `pullbackSpecIso` identification of
  `pullback.fst/snd` with `Spec`-of-tensor inclusions that blocks the proof — so the `IsIso`
  form sidesteps a circular dependency. Confirmed acceptable by review (lean-auditor + checker).
- **`by_cases Module.Finite A M` splits generic flatness cleanly.** The module-finite-over-`A`
  branch is discharged by the proved helper `exists_free_localizationAway_of_finite`; the
  finite-type-`B` branch is the genuine Nitsure §4 dévissage residue. Its Mathlib-absent core:
  a finite module over the polynomial ring `A[X₁..X_d]` is generically free (verified absent
  via `lean_leansearch` — only `Module.freeLocus` / flat-locality lemmas return).
- **GF geometric globalization — witness `V` is not free.** In `genericFlatness`, do NOT
  `refine ⟨V, …⟩` with a placeholder open: an arbitrary non-empty `V` makes the flatness goal
  *false*. The witness must be `V = D(∏ⱼ f_j)` assembled from the per-affine-patch
  `genericFlatnessAlgebraic` outputs. Start the proof from `IsIntegral.nonempty` →
  `exists_isAffineOpen_mem_and_subset` to get the noetherian-domain base `A := Γ(S, U₀)`.
- **Section-level mate read (FBC, iter-003).** Read an abstract pullback/pushforward
  composite on global sections by chaining the two proved tilde dictionaries
  (`pushforward_spec_tilde_iso`, `pullback_spec_tilde_iso`) + `tilde.toTildeΓNatIso`, which
  reduces "an abstract sheaf-map's Γ is iso" to a concrete tensor-module map. The cone-leg
  identification `pullback.fst/snd = pullbackSpecIso.inv ≫ Spec.map (tensor inclusion)` closes
  by `exact pullbackSpecIso_inv_fst/_snd` once `letI := φ.hom.toAlgebra` makes `Spec.map φ`
  defeq to `Spec.map (ofHom (algebraMap …))`. Uses Mathlib's tensor order `A ⊗[R] R'`.
- **Pullback-along-iso unit-iso (iter-003).** To get a per-object adjunction-unit iso for an
  iso `f : X ⟶ Y`, build `(Scheme.Modules.pullback f).IsEquivalence` (via an
  `Equivalence.mk (pullback f) (pullback (inv f))` whose coherence is discharged by default
  `aesop_cat`) so `instIsIsoFunctorUnitOfIsEquivalence` fires — then use the functor-iso `.app`
  form `(asIso adj.unit).app x`. `asIso (adj.unit.app x)` FAILS (per-object instance doesn't
  auto-fire from `IsIso adj.unit`).
- **A-over-B scalar commutation is NOT free.** `f•(b•x)=b•(f•x)` for `f:A, b:B` over a
  scalar tower `A → B → M` is not an automatic `SMulCommClass`; prove it by routing both
  sides through `algebraMap A B` (`IsScalarTower.algebraMap_smul` + `smul_smul` + `mul_comm`).
- **`induction d` mis-generalizes `d`-dependent module instances.** When the module structure
  on the goal depends on the recursion variable `d` (e.g. `Module (MvPolynomial (Fin d) A) N`),
  `induction d` fails to synthesize the instance; use `rcases Nat.eq_zero_or_pos d` (or a
  ∀-quantified-`N` induction principle). **Caveat (iter-004):** a `rcases` case-split gives NO
  IH in scope — fine for the base/torsion cases, but the generic-rank dévissage step (which needs
  the IH on a smaller-support `T`) genuinely requires restructuring to strong induction on `d`
  with `N` universally quantified. Don't try to fill the IH-needing sorry inside the case-split
  skeleton; restructure first. **RESOLVED (iter-006):** the restructure is
  `induction d using Nat.strong_induction_on generalizing N` — `generalizing N` reverts the module
  AND all its `d`-dependent instances (`AddCommGroup`, `Module (MvPolynomial (Fin d) A)`,
  `Module.Finite`, `Module A`, `IsScalarTower`) into the motive, producing the `∀ m < d, ∀ N [...]`
  IH the dévissage needs. Verified axiom-clean.
- **`letI := inferInstanceAs` opaque-aux-def trap (iter-006).** A module/scalar instance introduced
  by `letI x := inferInstanceAs (Module R' …)` compiles to an opaque auxiliary definition. Typeclass
  search then CANNOT derive downstream classes (`SMulZeroClass`, `DistribSMul`) through it, so smul
  rewrite lemmas (`smul_zero`, `smul_add`, `restrictScalars.smul_def`, `ExtendScalars.smul_tmul`)
  silently fail to fire on the resulting `•` (even `erw`), and a freshly-stated `hsmul` fact's `•`
  won't syntactically match the goal's. For a generator-level `map_smul'`/linearity proof you need a
  *transparent* instance (a real `def`/project-local iso), not an `inferInstanceAs` shim.
- **Re-prove `R'`-linearity by hand for `cancelBaseChange` (iter-004).**
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` is only `B`-linear in the `M`-factor. When
  you need linearity in the *base-change* factor (e.g. `R'`-linearity of
  `(A⊗_R R')⊗_A M ≃ R'⊗_R M`), it is NOT the declared linearity — re-bundle the underlying
  additive equiv as `≃ₗ[R']` by proving `map_smul'` on generators via `TensorProduct.induction_on`,
  using the `Algebra.TensorProduct.rightAlgebra` action `r' • (a⊗s) = a⊗(r'*s)` (key facts:
  `TensorProduct.smul_tmul'`, `algebraMap R' (A⊗[R]R') r' = 1⊗ₜr'` by rfl, `tmul_mul_tmul`).
- **Separately-compiled-module trick — DISPROVEN for the FBC `map_smul'` pin (iter-006).** The
  iter-004 hope (above) was that splitting `base_change_regroup_linearEquiv` into an imported module
  would let `exact LinearEquiv.toModuleIso (base_change_regroup_linearEquiv ↑M)` close
  `base_change_mate_regroupEquiv`'s `map_smul'`. **iter-006 deployed the split (refactor
  `split-regroup`) and the one-liner STILL fails — for a genuine mathematical reason, not a
  reducibility quirk.** The helper's source `(A⊗[R]R')⊗[A]M` tensors over the *canonical*
  `Algebra A (A⊗[R]R')` (leftAlgebra), while the object carrier `(extendScalars includeLeftRingHom).obj M`
  tensors over the `restrictScalars includeLeftRingHom` A-action. Because the A-module is an
  **instance argument of `TensorProduct`**, the two `⊗[A]` carriers are **different TYPES** — not
  defeq, and separate compilation does NOT change that (it normalises the `Module A` *diamond at the
  value level*, never the tensor *type*). 6 spellings all give a type-mismatch. **Lesson: a
  differently-instanced `TensorProduct` is a different type; reconcile only with an explicit
  identity-linear bridge (the `eT` equiv in the FBC code is essential), never with import-boundary
  defeq.** The real residue is then the `map_smul'` generator proof, blocked by an **opaque-instance
  wall**: the object `R'`-module is supplied via `letI := inferInstanceAs (Module R' …)`, which
  compiles to an opaque aux-def (`_aux_3`/`_aux_5`) through which typeclass search cannot derive
  `SMulZeroClass`/`DistribSMul`, so `smul_zero`/`smul_add`/`restrictScalars.smul_def`/
  `ExtendScalars.smul_tmul` never fire. Fix: a *transparent* `Module R'` instance (a project-local
  `ModuleCat`-level base-change iso for the mixed `restrictScalars∘extendScalars` square,
  Beck–Chevalley style), or `@`-explicit smul lemmas — then the settled chain
  `restrictScalars.smul_def → ExtendScalars.smul_tmul → tmul_mul_tmul → (helper simp set)` closes it.
- **`IsBaseChange.of_comp` for localization towers (iter-004).** To transport `Module.Free` across
  `A_{f'} → A_{f'f''}` (i.e. `N_f` is `N_{f'}` localized at the image of `f''`), build the ring map
  via `IsLocalization.Away.awayToAwayLeft` (after `rw [mul_comm]` to supply the
  `IsLocalization.Away (f''*f')` instance), make `N_f` an `A_{f'}`-module via `Module.compHom`, get
  the lift with `IsLocalizedModule.lift` (f' acts invertibly by `Commute.isUnit_mul_iff`), upgrade
  to `A_{f'}`-linear with `LinearMap.extendScalarsOfIsLocalization`, then `IsBaseChange.of_comp` +
  `.free`. This sidesteps the Mathlib-ABSENT converse of `IsLocalization.Away.mul'`.

- **Universe handling for `SheafOfModules.free` predicates (iter-007).** `SheafOfModules.free`
  needs a `Type u` index, so a rank-`d` local-freeness predicate must `ULift.{u}`-lift `Fin d`
  and keep the covering opens in universe `u` via `X.Opens` (`∃ (ι : Type u) (U : ι → X.Opens), …`).
  The `Scheme.OpenCover` formulation FAILS two-universe inference (`PreZeroHypercover.I₀` universe
  metavariables) — do NOT retry it. Landed `IsLocallyFreeOfRank` axiom-clean this way.
- **Annihilator commutes with localization for f.g. modules (iter-007).** `Ann(S⁻¹M) = (Ann M)·S⁻¹R`
  (`Module.annihilator_isLocalizedModule_eq_map`, missing from Mathlib, now project-local) by
  `le_antisymm`: `⊇` via image-annihilates (`mk'_smul_mk'`/`mk'_one`/`mk'_zero`); `⊆` by clearing
  ONE common denominator over a spanning finset — `Module.Finite.fg_top` gives the finset, `∏ uₘ`
  the common denominator (`Finset.dvd_prod_of_mem`), and a `Submodule.span_induction` helper lifts
  "annihilates the spanning set" to "annihilates `M`". `Module.Finite` is load-bearing (false
  without it). Gotcha: `IsLocalization.mk'_surjective`/`IsLocalizedModule.mk'_surjective` return a
  `match`/`Function.uncurry` form — `dsimp only [Function.uncurry]` after `obtain ⟨⟨a,s⟩, rfl⟩`.

- **`erw` past the opaque-instance keyed mismatch (iter-008 — the FBC `map_smul'` unlock).** When a
  smul/linearity rewrite is the *correct* lemma but `rw` reports "Did not find an occurrence of the
  pattern" because the module instance is an opaque `inferInstanceAs`/`letI` aux-def, `erw` matches up
  to defeq and fires: `erw [ModuleCat.ExtendScalars.smul_tmul]` (signature
  `s • s' ⊗ₜ[R] m = (s*s') ⊗ₜ[R] m`). For the final leaf, a `show` of BOTH sides in the transparent
  form lets identity-bridges (the `eT` equiv) drop by defeq, then a plain `rw [cancelBaseChange_tmul,
  …, comm_tmul, smul_tmul', smul_eq_mul]` closes it; `add` nodes also need `erw [smul_add, map_add,
  …]`. CAVEAT: `smul_zero`/`smul_add` on the SAME opaque carrier still fail — that is a *synthesis*
  failure (`SMulZeroClass ↑R'` not derivable through the `_aux` instance), NOT a keying failure, and
  `erw` does not help. That residual is the transparent-instance wall (route (b) — see FBC blocker).
- **Generic-rank SES over a polynomial domain (iter-008, Nitsure §4 — `gf_generic_rank_ses`).**
  `0→P^{⊕m}→N→T→0` with `T` torsion: `m := Module.finrank K NK` over `K = FractionRing P`,
  `NK = LocalizedModule P⁰ N`; basis `Module.finBasis K NK`; lift each basis vector along
  `ℓ = IsLocalizedModule.mkLinearMap` via `IsLocalizedModule.surj` with a unit
  `IsLocalization.map_units`; `LinearIndependent K (ℓ∘v)` by `LinearIndependent.units_smul`, descend
  to `P` via `IsFractionRing.injective` (`restrict_scalars`) + `LinearIndependent.of_comp ℓ`;
  `φ := Fintype.linearCombination P v`, injective by `Fintype.linearIndependent_iff` +
  `LinearMap.ker_eq_bot'`; cokernel torsion by clearing denominators
  (`IsLocalization.exist_integer_multiples`) + `IsLocalizedModule.eq_zero_iff` (the clean kernel
  handle) + `Submodule.Quotient.mk_smul` (bridges the `↥P⁰`-action and `P`-action). Axiom-clean.
- **`IsLocalization.map` for a non-canonical localization→fraction-field map (iter-008).** The literal
  `algebraMap (Localization.Away g) (FractionRing A)` has NO canonical `Algebra` instance. Encode the
  same map as `IsLocalization.map (FractionRing A) (RingHom.id A) hle` with
  `hle : Submonoid.powers g ≤ Submonoid.comap (RingHom.id A) (nonZeroDivisors A)` (from
  `Submonoid.powers_le`). Used in `gf_clear_one_denominator` (proved axiom-clean). Gotcha:
  `rw [← hunit.unit_spec]` for the unit identity fails ("motive not type correct" — `hunit` occurs in
  `hunit.unit⁻¹`'s type); use `Units.inv_mul hunit.unit` then `rwa [hunit.unit_spec]`.
- **Base-domain-generalizing strong induction (iter-008 — completes the iter-006 fix).** When a
  reindex step changes the base ring (`A → A_g = Localization.Away g`), the IH must generalize `A`
  TOGETHER WITH `N`: `induction d using Nat.strong_induction_on generalizing A N`. This REQUIRES a
  SHARED universe `(A N : Type u)` (not `(A : Type*) (N : Type*)`), because
  `LocalizedModule S M : Type (max u_R u_M)` — the reindexed module escapes `N`'s universe and the
  universe-bumping self-recursion is only well-formed when `A`, `N` share one. The geometric target is
  entirely in `Type u` (`Scheme.{u}`), the natural setting. IH verified to quantify over the base
  domain at every `m < d` via `lean_goal`. (Supersedes the iter-006 note that only `N` needed it.)
- **`erw [TensorProduct.zero_tmul]` closes the FBC `map_smul'` zero-branch — the multi-iter
  transparent-instance wall, RESOLVED iter-011.** The two `r' • (0 ⊗ₜ m) = r' • g (0 ⊗ₜ m)`
  zero-branches that blocked `base_change_mate_regroupEquiv` since iter-006 (the `SMulZeroClass ↑R'`
  won't-synthesize-through-`_aux` wall) close with `erw [TensorProduct.zero_tmul]` followed by the
  term closer `(congrArg (⇑g) (smul_zero r')).trans (g.map_zero.trans …)`. `erw` unifies the `0 ⊗ₜ m`
  pattern up to defeq THROUGH the opaque diamond `Module` instance where `rw`, explicit-typed `show`,
  and `convert using n` all fail ("pattern not found" / "stuck metavariable instance"). This made the
  **route-(b) retype unnecessary** — the `eT` identity bridge + `erw` zero-closer suffices.
  `Algebra.IsPushout.cancelBaseChange` as the regroup core was ATTEMPTED and abandoned: it forces the
  canonical `Algebra A (A⊗R')`, re-triggering the `extendScalars` diamond (`failed to synthesize
  Module ↑R' …`).
- **Domain-adapting Mathlib's field-only private machinery (iter-011, Nagata normalization).**
  Mathlib's `RingTheory.NoetherNormalization` builds the triangular Nagata transform `T`/`T1` and
  proves the top coefficient is a unit — but only over a FIELD, as PRIVATE lemmas. Transcribe to a
  noetherian DOMAIN by having the adapted `T_leadingcoeff_eq` return the leading coefficient as
  `MvPolynomial.C (coeff v F)` (non-zero in a domain) instead of asserting it is a unit, then localize
  at that coefficient (`IsLocalization.Away.algebraMap_isUnit`) to recover the unit downstream. The
  field is then NOT silently assumed (lean-auditor-verified). The leading coeff transports under
  `MvPolynomial.map` via `finSuccEquiv_map_comm` + `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`
  (`Nontrivial (Localization.Away g)` from `(IsLocalization.injective … hle).nontrivial`).
- **Namespace shadow + binder gotchas (iter-011).** `open _root_.Polynomial _root_.MvPolynomial
  _root_.Ideal Nat _root_.RingHom List` — a bare `open Polynomial` resolves to the project's
  `AlgebraicGeometry.Polynomial` namespace and shadows the root `Polynomial`/`MvPolynomial` lemma API
  (symptoms: `Unknown identifier degree_lt_degree`/`leadingCoeff_mul`/`natDegree_mul`). Also a literal
  `φ` binder triggered a spurious `unexpected token 'φ'; expected '_' or identifier` parse error in one
  editing context — use `phi`.
- **Grassmannian Cramer-inverse transition map (iter-011 — `def:gr_transition`, STUCK→GREEN).** Build
  bottom-up: `universalMatrix` (the `d×(r∖I)` matrix of coordinate variables) → `minorDet` →
  `universalMinor` → `universalMinorInv` (`Matrix.nonsing_inv`, det-mul-cancel) → `imageMatrix`
  (`X^I · (X^I_J)⁻¹`) → `transitionPreMap` (`MvPolynomial.aeval` of the image entries) →
  `transitionMap` (`IsLocalization.Away.lift` of the pre-hom, available because the pre-hom sends the
  localized denominator to a unit, `isUnit_transitionPreMap_minorDet`). `transitionMap_self` via
  `P^I_I = 1 ⇒ X^I_I = 1` self-inverse: `universalMatrix_submatrix_self` + `Matrix.map_one` + `inv_one`
  + `IsLocalization.ringHom_ext`. Matrix-one idioms: `inv_one` (NOT the non-existent `Matrix.inv_one`/
  `Matrix.nonsing_inv_one`); `change` not `show` for a defeq goal `show` rejects; `IsUnit.of_mul_eq_one
  _ hmul` arity (the deprecated `isUnit_of_mul_eq_one` differs).
- **`rw [Matrix.map_mul]`/`[RingHom.map_det]` fails on `Localization.Away`-base-changed matrices (iter-012).**
  On any matrix carrying a `Localization.Away`-valued `algebraMap` (e.g. Grassmannian `imageMatrix`),
  `rw [Matrix.map_mul]` reports "pattern not found" even when the pattern is textually identical — a
  hidden `algebraMap` instance diamond on `Algebra R^I (Localization.Away …)`. Robust workaround used
  throughout `cocycleCondition`: state the distributed form as a `have hmm : … := by …; exact Matrix.map_mul`
  (the `exact`/elaboration path unifies up to defeq, sidestepping `rw`'s syntactic matcher), then `rw [hmm]`.
  Same trick for `RingHom.mapMatrix` vs `Matrix.map` in `RingHom.map_det` (prove `det … = algebraMap …`
  by `exact (RingHom.map_det _ _).symm`, then `rw`). Matrix-one idioms unchanged from iter-011.
- **Triple-overlap rings: NO generic ring builder (iter-012, GR cocycle).** The blueprint's `S_Z`
  convention lists the *other two* subsets in fixed `I<J<K` order (`S_I = away(P^I_J·P^I_K)`, etc.) and is
  **not permutation-symmetric**; a single generic builder produces the wrong product *order* → a distinct,
  non-defeq `Localization.Away` type. Carry the minor products inline in each `cocycleΘ` def. The two
  single→double localisation maps are `awayInclLeft x y : away x →+* away (x*y)` /
  `awayInclRight x y : away y →+* away (x*y)` (lift of `algebraMap` along the kept/extra factor); cross-factor
  units via `θ̃(P^B_C) = det((X^A_B)⁻¹)·P^A_C` (both units once `P^A_C` is inverted). `lem:gr_cocycle` closed
  axiom-clean by `IsLocalization.ringHom_ext → Away.lift_comp → MvPolynomial.ringHom_ext → matrix identity`.
- **Inline instance-stacking blows `isDefEq`/`whnf` heartbeats — factor into helper lemmas (iter-012, GF/QUOT).**
  Stacking 4+ module/algebra instances on ONE type inside one tactic block (e.g. `LocalizedModule MC T`
  carrying `Module P_g`, `Module (P_g⧸span)`, `Module R` via `compHom`, plus `IsScalarTower`s) times out
  `isDefEq`/`whnf` even at `set_option (synthInstance.)maxHeartbeats 1000000`. The corrective is NOT a bigger
  budget — it is **decomposition into standalone top-level helper lemmas**, each with a minimal instance
  context. Verified GF facts that DID land inline: `IsLocalization MC P_g` (pin σ via `set MC := Submonoid.map C (powers g)`
  or synthesis stalls), `Module P_g Tg'` via **`letI`** `moduleOfIsLocalization` (NOT `haveI` — loses defeq for
  the downstream `IsScalarTower`), `Module.Finite P_g Tg'` via `Module.Finite.of_isLocalizedModule MC (mkLinearMap MC T)`
  (`Rₚ` is implicit — pass only `MC` + `f`), quotient-finiteness via `Module.Finite.of_surjective` + `IsTorsionBySet.mk_smul`.
  (`LocalizedModule.zero_mk`, NOT `mk_zero`.)
- **PowerSeries/Polynomial notation pins (iter-012, QUOT engine).** `open PowerSeries Polynomial in` MUST
  precede the docstring (between docstring and decl → `unexpected token 'open'`). `ℚ[X]` (Polynomial) notation
  did NOT resolve even under `open Polynomial in` here (`GetElem Type`/`Semiring Type` failures) — use spelled-out
  `Polynomial ℚ`; `ℚ⟦X⟧` works. `PowerSeries.C` takes the ring as an **implicit** arg: `(PowerSeries.C (R := ℚ)) c`,
  not `PowerSeries.C ℚ c`. Partial-sum identity for `(invOneSubPow ℚ 1).val * F` via `coeff_mul` +
  `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` + `Finset.sum_range_reflect`.
- **`erw` + `← Functor.comp_map` for functor-composition defeq (iter-014, FBC Seam 1 — the
  `conjugateEquiv` wall RESOLVED).** When a category-theory rewrite is the *correct* lemma but
  `rw`/`simp only` report "Did not find an occurrence of the pattern" because the codomain is written
  `G.obj (F.obj X)` while the lemma's domain is `(F⋙G).obj X` (defeq, not syntactic), normalise with
  `simp only [← Functor.comp_map]` / `Functor.comp_map` and switch to `erw` (defeq matching) for the
  naturality + conjugate-unit rewrites. This unblocked `base_change_mate_unit_value`. The 4-move
  conjugate calculus (`analogies/fbc-mate.md`): Move 1/3 = `Adjunction.comp_unit_app` splits the
  composed-adjunction unit into the geometric/algebraic units; Move 2 = `unit_conjugateEquiv_symm`
  with `((conjugateEquiv adjL adjR).symm β.hom).app M = pullback_spec_tilde_iso.inv` by `rfl` (it IS
  the def via `conjugateIsoEquiv`); Move 4/Claim A = `tilde.adjunction.right_triangle_components`
  (`fromTildeΓ` is the tilde⊣Γ counit). Gotchas: `NatIso.naturality_1` (NOT `_2`) matches
  `(F⋙G).map f = α.inv ≫ f ≫ α.hom`; `Iso.hom_inv_id_app` does NOT fire on `nat.hom.app X ≫ nat.inv.app X`
  — convert via `← Iso.app_hom, ← Iso.app_inv` first then `Iso.hom_inv_id`; `set_option maxHeartbeats
  4000000 in` must precede the DOCSTRING (between docstring and decl → "unexpected token 'set_option'").
  The opaque-`conjugateIsoEquiv`-element-chase the analogy warned against is a confirmed dead end; the
  abstract calculus closes it. Axiom-clean.
- **`IsLocalization.ringEquivOfRingEquiv` over `algEquivOfAlgEquiv` on doubly-indexed rings + the
  canonical `OreLocalization`-action diamond (iter-014, GF `gf_torsion_reindex` RESOLVED).** Base-changing
  a ring automorphism `e` on `MvPolynomial (Fin n) A` to its `Localization.Away g`-coefficient version:
  `algEquivOfAlgEquiv` FAILS (needs `Algebra A (MvPolynomial … A_g)`, won't synthesize on the
  doubly-indexed ring); `ringEquivOfRingEquiv` only needs `Algebra P Pg` + `IsLocalization MC Pg` (both
  present). `ebar Fg = G` via `ringEquivOfRingEquiv_apply` + `IsLocalization.map_eq`; quotient transport
  via `Ideal.quotientEquiv` + `Ideal.map_span`. **The non-obvious wall:** the goal's existential
  `∃ … [Module A_g T_g] [IsScalarTower A_g R T_g] …` resolves `SMul A_g T_g` to the **canonical
  `OreLocalization.instSMul`** (the global instance beats the anonymous existential binder), IGNORING the
  provided `Module A_g` witness — so any transported action must be proved to agree with the canonical
  localization action on constants (`θ (C (algebraMap A A_g a')) = a' • …`). Resolved with
  `LinearEquiv.extendScalarsOfIsLocalization` (upgrade the `A`-linear `IsLocalizedModule.linearEquiv` to
  `A_g`-linear) + helpers `pullbackModuleAddEquiv`/`finite_of_pullbackModuleAddEquiv`/`pullback_isScalarTower`/
  `finite_of_quotientRingEquiv`/`isLocalizedModule_restrictScalars`. Gotchas: `of_algebraMap_smul fun _ _ => rfl`
  fails on a `compHom` action (use `inferInstance`); `localizedModuleIsLocalizedModule MC T` is "function
  expected" — call `localizedModuleIsLocalizedModule (M := T) MC`; `show`→`change` for defeq goals.
  **Reconfirms iter-012: factoring into helpers (not a bigger budget) is what kills the `isDefEq`/`whnf`
  blow-up; the `maxHeartbeats 4000000` only covers the residual `A_g`-linearity transport.** Axiom-clean.
- **Pullback–pushforward unit pseudofunctoriality, packaged (iter-016, FBC Seam-2 engine
  `pullbackPushforward_unit_comp`).** For composable `a : X₁⟶X₂`, `b : X₂⟶X₃` and a module `N` on the
  **codomain** `X₃`, the `(a≫b)`-unit factors through the `a`- and `b`-units plus the
  `pushforwardComp`/`pullbackComp` coherences. Proof = `unit_conjugateEquiv ((adj b).comp (adj a))
  (adj (a≫b)) (pullbackComp a b).inv N`, then `rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app]`,
  then `rw [← Category.assoc]; exact h`. The bridge is `conjugateEquiv_pullbackComp_inv :
  conjugateEquiv … (pullbackComp f g).inv = (pushforwardComp f g).hom`. **`N` MUST live on the codomain
  `X₃`** (the unit of the left adjoint `pullback` lives on its source = the morphism's codomain); the
  `X₁.Modules` draft type-mismatches. Same conjugate-calculus family as iter-014 Seam 1. Axiom-clean.
- **Localisation-of-localisation `IsLocalizedModule` + free descent across a ring iso of localisations
  (iter-016, GF `free_localizationAway_of_away_tower`).** A packaged route DOES exist: the composite
  `ψ : T →ₗ[A] (T_g)_h` is `IsLocalizedModule (powers (g·a))` via **`IsBaseChange.comp`** through
  `isLocalizedModule_iff_isBaseChange` (compose the two localisation base changes `A→A_g→A_h`). The
  ring identification `Away(g·a) = A_h` is `IsLocalization.Away.mul_of_associated` (the witness is the
  **single product `f := g·a`** via `mul_ne_zero hg ha`, NOT a square). To transport `Module.Free A_h D`
  to `Module.Free Away(g·a) D`: give `D` the `Away(g·a)`-action through `σ := IsLocalization.algEquiv`
  (`Module.compHom`), transport the basis with `Module.Basis.mapCoeffs σ.symm.toRingEquiv` (compat is
  `rfl` after `AlgEquiv.apply_symm_apply`/`AlgEquiv.commutes` — use `change` not `show`), upgrade the
  `A`-linear `IsLocalizedModule.linearEquiv` to `Away(g·a)`-linear with
  `LinearEquiv.extendScalarsOfIsLocalization`, finish with `Module.Free.of_equiv'`. The auto-resolved
  `Module A D` (double `LocalizedModule`) is load-bearing — no manual `restrictScalars`. Honest
  `set_option synthInstance.maxHeartbeats 1000000` (the doubly-localised carrier makes search expensive,
  not looping). Axiom-clean.
- **Subst-able free legs dissolve a "motive is not type correct" wall (iter-017, FBC Seam 2 — the
  iters 014–016 CHURNING wall RESOLVED).** When the rewrite target (here the two pullback legs
  `pullback.fst/snd`) sits in dependent positions — an adjunction index, a `.w` proof arg inside
  `pushforwardCongr`, a `gammaPushforwardIso` arg, and (load-bearing) the *type* of an opaque def
  (`base_change_mate_codomain_read`) — `rw [hfst]` fails `motive is not type correct` and `generalize`
  frees only one slot. Corrective: **restate the lemma with those targets as FREE variables** `g' f'`
  (+ the leg-equality hypotheses `hfst hsnd comm`), so `subst hfst; subst hsnd` acts on a well-typed
  motive (`base_change_mate_codomain_read_legs`, `base_change_mate_fstar_reindex_legs`). To make the
  concrete consumer's term defeq to the variable-legs term, derive the leg equalities via **`.1`/`.2`
  projections, NOT `obtain`** — `obtain` produces a stuck `And.casesOn` that blocks the proof-irrelevant
  defeq; the `exact …_legs …` then closes modulo a `set_option maxHeartbeats 1600000` for the
  change-of-rings dictionary unfoldings. The `pushforwardComp`/`pushforwardCongr` coherences Γ-collapse
  to `𝟙`/`eqToHom` (`(pushforwardComp a b).hom.app M = 𝟙 _` by `rfl`, then `Functor.map_id`); the
  `…hom` collapse misses `simp`'s discrimination tree in the composed-functor position (fires only after
  the step-iii unit rewrite). This is a textbook fine-grained CHURNING corrective: subst-able legs, not
  another opaque helper.
- **Don't bundle CANONICAL (`inferInstance`) typeclass instances as existential witnesses (iter-017, GF
  L5 RESOLVED — the OreLocalization diamond).** `gf_torsion_reindex` returned its canonical `Module A_g
  T_g` as a bundled existential (filled by `inferInstance`); the consumer's `obtain` destructured it
  into an **opaque local hypothesis**, and because the downstream carrier `LocalizedModule (powers h)
  T_g` is an `OreLocalization` quotient whose *type* depends on the `SMul A_g T_g` instance, the IH
  output (over the opaque fvar) and the helper's `hfree` (over the freshly-synthesised canonical
  instance) were defeq-but-unmatched at instance transparency. Fix at the **PRODUCER**: drop the
  redundant canonical existential entirely (retain only genuinely non-canonical instances —
  `MvPolynomial`-action `hmod1`, `IsScalarTower` `htower`) and let the consumer `inferInstance` it, so a
  single `Module A_g T_g` instance is in play on both the IH and helper paths. **Lesson: a canonical
  instance bundled as an existential becomes an opaque fvar at the consumer's `obtain`, breaking
  type-level instance matching on `OreLocalization`/`LocalizedModule` carriers — never bundle it.**
- **Route-2 ambient subquotient calculus is isDefEq-pathology-free (iter-017, QUOT — validates the
  iter-016 pivot).** 13 axiom-clean decls landed with NO `DirectSum.Decomposition`/`IsInternal`/
  `map_iSup` on any quotient/subtype carrier — every object is `Naux ⊓ ℳ n` in the fixed ambient `M`,
  and the documented G2–G4 isDefEq/whnf runaway did NOT fire once. Keystone D6
  `subquotient_degreewise_diff` (`hilb(n+1)−hilb(n) = hilb_C(n+1)−hilb_K(n)`) via a **single κ-linear
  map** `φ = N'.mkQ ∘ x ∘ subtype : ↥(N ⊓ ℳ n) →ₗ[κ] M⧸N'` (+ companion `g` on `(N⊓ℳn).map x`): two
  `LinearMap.finrank_range_add_finrank_ker`, `ker` via `finrank_comap_subtype`, `range φ = range g`,
  inclusion–exclusion (`Submodule.finrank_sup_add_finrank_inf_eq`) rewritten by the ambient image
  identity + distributive law, `omega` then `push_cast; linarith`. The single-map route needs neither
  `N'≤N` nor the blueprint's `Q_n→Q_{n+1}` quotient constructions. Mathlib has NO
  `Submodule.IsHomogeneous` lattice-closure — built project-local (`inf/sup/comap/map_isHomogeneous`),
  all resting on the load-bearing `decompose_raisesDegree` (`↑(decompose ℳ (x m) (i+1)) = x ↑(decompose
  ℳ m i)`). Gotchas: `omit [DirectSum.Decomposition ℳ] in` must precede the docstring; use
  `DFinsupp.notMem_support_iff` (not `not_mem_`), `DirectSum.sum_apply` (not `DFinsupp.finset_sum_apply`).
- **The finiteness-from-commuting-endos encoding needs the POLYNOMIAL ring, not `Algebra.adjoin`
  (iter-017, QUOT — scouted, not yet built).** To get `Module.Finite (MvPolynomial (Fin r) κ) M` from
  `r` commuting degree-1 endos: `Algebra.adjoinCommRingOfComm κ (commuting t) : CommRing ↥(adjoin κ
  (range t))` makes `aeval` legal into the CommRing adjoin `A ⊆ Module.End κ M` (which `MvPolynomial.aeval`
  refuses for noncommutative `End` directly), then `Module.compHom` along `κ[t] ↠ A`. **The IH transfer
  must surject onto the POLYNOMIAL ring `κ[t₀..t_{r-2}]` (free) via `eval(t_{r-1}=0)` +
  `Submodule.FG.restrictScalars_of_surjective`, NOT `Algebra.adjoin κ {t₀..t_{r-2}}`** — `(adjoin)/(t_{r-1})`
  need not equal the smaller adjoin (relations among the `t i` in `End`), which breaks the transfer.
- **`Scheme.Modules.annihilator` via `IdealSheafData.ofIdeals` (iter-011).** The annihilator ideal
  sheaf is `IdealSheafData.ofIdeals (fun U => Module.annihilator Γ(X,U) Γ(F,U))` (mirrors the
  `Scheme.Hom.ker` pattern) — the DEFINITION needs no basic-open coherence and is axiom-clean. The
  always-available `ofIdeals` `≤`-inclusion is `annihilator_ideal_le` (`IdealSheafData.ideal_ofIdeals_le`).
  Only the REVERSE inclusion (forward characterization = module-annihilator on affine opens) needs the
  QCoh→`IsLocalizedModule` bridge — keep that one obligation gated, but the def + support predicates
  (`schematicSupport := annihilator.subscheme`, `schematicSupportι := annihilator.subschemeι`,
  `HasProperSupport := IsProper (schematicSupportι ≫ f)`) all land now.

- **Degreewise `iSupIndep` via ambient membership — ROUTE (b) (iter-020).** To prove the images
  `range (ψ n)` of `N ⊓ ℳ n` form an `iSupIndep` family inside a (polynomial-ring) quotient `Q`,
  do NOT build an outgoing detector map *out of* `Q` (route (a): `Submodule.liftQ` clashes on the
  scalar ring `S = MvPolynomial (Fin r) κ` vs `κ` — confirmed DEAD END). Instead: (1) a ring-agnostic
  lattice helper `iSupIndep_map_of_mem_ker_sup` — if every `a ∈ g i` in `ker π ⊔ ⨆ j≠i, g j` is in
  `ker π`, then `iSupIndep (fun i => map π (g i))` (`iSupIndep_def` + `Submodule.disjoint_def` +
  `map_iSup`); (2) the ambient degree-`i` projection `proj m = ↑(decompose ℳ m i)` (defeq to
  `(ℳ i).subtype ∘ component i ∘ decomposeLinearEquiv ℳ`) shows a homogeneous `x ∈ ℳ i` in
  `N' ⊔ ⨆ j≠i, ℳ j` lies in `N'` (`decompose_of_mem_same`/`_ne` + `IsHomogeneous.mem_iff`); (3) glue
  `range (ψ n) = map Φ (comap N.subtype (N ⊓ ℳ n))`. Keeps every graded fact in ambient `M`; no
  `DirectSum.Decomposition` on a quotient/subtype carrier, no `isDefEq`/`whnf` runaway. This closed the
  SNAP-S2 keystone leaf.
- **Restricted-scalar dévissage motive + propositional instance transport (iter-020).** When running a
  prime-filtration induction (`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B`) whose
  motive needs an `A`-module structure on each `B`-module `N`, equip `N` with
  `letI : Module A N := Module.compHom N (algebraMap A B)` and discharge the scalar tower by
  `IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)` (compHom smul is *definitionally*
  `algebraMap A B a • n`). To reconcile the induction's `compHom` instance on the target `M` with the
  AMBIENT given `Module A M`: they are *propositionally equal* — prove
  `hAinst : (Module.compHom M (algebraMap A B) : Module A M) = ‹Module A M›` via `Module.ext_iff.mpr`
  + `funext` + `change algebraMap A B a • m = a • m` + `rw [Algebra.algebraMap_eq_smul_one, smul_assoc,
  one_smul]`, then `rw [hAinst] at key`. This transports the localization across the instances and
  dissolves the "defeq-compatible `Module A N`" plumbing worry.
- **One-call denominator clearing for integral relations (iter-020 recipe, EXECUTED iter-021 — GF L4
  finiteness leaf CLOSED axiom-clean).** `IsIntegral.exists_multiple_integral_of_isLocalization`
  (`Mathlib.RingTheory.Localization.Integral`): given `IsLocalization M Rₘ`, a tower `R → Rₘ → S`, and
  `x : S` integral over `Rₘ`, returns `m ∈ M` with `m • x` integral over `R`. Apply it **PER GENERATOR**
  `x ∈ σ` (NOT per coefficient polynomial — that was the iter-020 sketch; the per-generator route is
  strictly simpler and is what landed): each `algebraMap B B_K x` is integral over `MvPoly K`
  (`hint.isIntegral`), the lemma yields `a_x ∈ A⁰` with `C a_x • x` integral over `MvPoly A`, set
  `g1 := ∏_{x∈σ} a_x` and the finer witness `g := g0·g1`. Then `hfin` = per-generator integrality over
  `MvPoly A_g` (`isIntegral_algHom_iff νA hν_inj` + `IsIntegral.tower_top` + divide out the unit
  `C(a_x)`) + `adjoin (MvPoly A_g) (image σ) = ⊤` (`Algebra.adjoin_induction` over `A_g` via the
  `IsLocalization.Away.map` square, bumped to `MvPoly A_g` by `restrictScalars`+`adjoin_le`) +
  `Algebra.finite_adjoin_of_finite_of_isIntegral` + `Module.Finite.equiv Subalgebra.topEquiv`.
  Load-bearing facts: `algebraMap (MvPoly A) (MvPoly S) = MvPolynomial.map (algebraMap A S)` by `rfl`
  (the `algebraMvPolynomial` algebraMap); the `C`-pushforward `algebraMap … (C a) = C (algebraMap a)`
  needs `MvPolynomial.map_C`, NOT `rfl`; `MvPolynomial.algebraMvPolynomial` is NOT a global instance
  (`letI`). Gotcha: inside `namespace AlgebraicGeometry`, bare `IsIntegral` resolves to a scheme-typed
  clash — use `_root_.IsIntegral`. (NOTE: the GF chapter's step-2 sketch still describes the obsolete
  per-coefficient `gf_clear_one_denominator` fold — blueprint-writer fix owed, lvb-gf iter-021 major.)

- **§4 dévissage assembly — ambient-instance discipline beats hand-built composites (iter-022,
  `genericFlatnessAlgebraic` CLOSED).** Non-torsion branch over `C := B ⧸ p.asIdeal`: domain
  (`Ideal.Quotient.isDomain`), finite-type via `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A p.asIdeal)
  (Ideal.Quotient.mkₐ_surjective A p.asIdeal)` (FiniteType arg is IMPLICIT; `mkₐ_surjective` needs explicit
  `A p.asIdeal`). `suffices` the goal for `C`, transport to `N` along `a.restrictScalars A` via
  `IsLocalizedModule.mapEquiv … (a.restrictScalars A).symm` + `Module.Free.of_equiv`. Non-torsion from
  `Nontrivial (TensorProduct A (FractionRing A) C)` via `(LocalizedModule.equivTensorProduct …).injective.nontrivial`
  (NOT `Equiv.nontrivial` — wrong direction). **DIAMOND (do NOT retry):** a hand-built `letI algACg :
  Algebra A Cg := ((algebraMap C Cg).comp (algebraMap A C)).toAlgebra` triggers an `isDefEq` heartbeat
  blowup (200000) — it competes with the ambient `OreLocalization`/`Submodule.Quotient` SMul. Use ambient
  `inferInstance` for `Algebra A Cg` / `IsScalarTower A C Cg` everywhere; the bridge is then
  `IsLocalizedModule.iso (powers g) (IsScalarTower.toAlgHom A C Cg).toLinearMap` upgraded by
  `LinearEquiv.extendScalarsOfIsLocalization (powers g) (Away g)`. Honest `maxHeartbeats 1600000` +
  `synthInstance.maxHeartbeats 400000` (assembly-level, not re-elaboration).
- **Strengthen-the-existential to pin an instance the ∃ would erase (iter-022, GF L4 4th conjunct).**
  When a downstream consumer needs an instance bundled inside an existential to be the CANONICAL/compatible
  one (here `Algebra A_g B_g` must agree with the `A→B→B_g` tower so the consumer can build
  `IsScalarTower A A_g C_g`), the bare `∃ (_ : Algebra A_g B_g) …` lets the witness be arbitrary. Add a
  compatibility conjunct `∀ a, algebraMap A_g B_g (algebraMap A A_g a) = algebraMap B B_g (algebraMap A B a)`,
  proved in 3 lines (`change` not `show`; `rw [Localization.awayMap, IsLocalization.Away.map,
  IsLocalization.map_eq]`), and name the instance binder (`algBg`, not `_`).
- **Conjugate-COUNIT dual of a proven unit lemma (iter-022, FBC gstar_transpose step 1).** The counit
  calculus mirrors Seam-1's unit calculus verbatim: `rw [Functor.map_comp]; rw [Iso.inv_comp_eq,
  ← Iso.eq_comp_inv]`, `set adjL/adjR/β`, `hpullinv : ((conjugateEquiv adjL adjR).symm β.hom).app N =
  (pullback_spec_tilde_iso ψ N).inv` by `rw [hβ]; rfl` (DIRECTION TRAP: `.symm β.hom = …inv`, not `.hom`),
  `huce := conjugateEquiv_counit_symm …` then `rw [hpullinv] at huce`, `hcounitL/hcounitR` via
  `Adjunction.comp_counit_app` ⇒ master counit-transport identity. **Trap for the next prover:** `set W`
  does NOT fold the goal's geometric counit `ε_g` (object only defeq, not syntactic) — stage the `ε_g`
  rewrite via `conv`/`change`, not bare `rw`. Whole-goal/per-generator `ext` is a confirmed dead end.
- **Audit a prose-authored frontier signature BEFORE proving it (iter-023, GF-geo — caught a FALSE
  theorem).** Before attempting `genericFlatness` the prover audited the Lean signature against the
  blueprint + the algebraic input and found the theorem **mathematically FALSE**: it carried only
  `[LocallyOfFiniteType p]`, and `LocallyOfFiniteType` does NOT entail `QuasiCompact` in Mathlib
  (counterexample: an infinite disjoint union `⊔_i Spec ℤ → Spec ℤ`, locally of finite type but not
  quasi-compact, with a finite-type torsion sheaf `ℤ/pᵢℤ` on component `i` — no non-empty open is a flat
  locus). Fix = add `[QuasiCompact p]` (matches Nitsure §4's "finite-type morphism"). **Lesson:** any
  signature transcribed from prose ("finite-type morphism") must spell out BOTH `[LocallyOfFiniteType]`
  AND `[QuasiCompact]` — the conjunction is "finite type", neither alone suffices. Audit-before-prove is
  cheap insurance whenever a frontier signature was authored from informal prose.
- **Extract a proven inline coherence into a reusable named lemma, generalizing the spectator object
  (iter-023, FBC Seam-C `gstar_counit_transport` CLOSED axiom-clean).** The counit-transport identity
  that previously lived as an inline `have huce` inside `gstar_transpose` was lifted verbatim into a
  standalone theorem and **generalized over an arbitrary `W : (Spec R').Modules`** — free, because the
  scaffold never used `W`'s specific form. Recipe (counit dual of Seam-1 `unit_conjugateEquiv_symm`):
  `set adjL/adjR/β`; `hpullinv` (`(conjugateEquiv adjL adjR).symm β.hom = pullback_spec_tilde_iso⁻¹`, by
  `rfl`); `conjugateEquiv_counit_symm`; two `Adjunction.comp_counit_app` splits; `exact huce`. When an
  inline `have` is mathematically self-contained, extracting it as a named lemma both de-duplicates and
  often generalizes for free.
- **Effort-breaker atoms close cheaply once frontier-ready (iter-024, FBC inner_eCancel).** The 3 atoms
  from the iter-023/024 decomposition of the `gstar_transpose` wall each closed in 1–3 lines:
  `_eUnit` = `haveI := pullback_isEquivalence_of_iso e; infer_instance`; `_pullbackComp` = bare
  `exact (Scheme.Modules.pullbackComp _ _).hom_inv_id_app (tilde M)` (the signature's `letI`/`let`
  binders are AUTO-introduced — the blueprint `intro _ _` hint FAILS). `_pushforwardComp` needs the
  **term-mode `congr_map`/`map_id` chain** `rw [h]; exact ((moduleSpecΓFunctor).congr_map
  ((pushforward (Spec.map φ)).map_id _)).trans (moduleSpecΓFunctor.map_id _)` — the blueprint
  `rw [Functor.map_id, Functor.map_id]` finisher FAILS (ambiguous with the monadic `Functor.map_id`;
  the `(pushforward φ).map (𝟙 ?X)` pattern won't match through the composed-functor `(Spec φ)_*` layer).
  General lesson: collapse a functor over a `𝟙` through a composed-functor position with term-mode
  `congr_map`/`map_id`, not `rw [Functor.map_id]`.
- **`rfl` beats a conjectured element-lemma re-break (iter-024, FBC Seam B `gstar_generator_close`).**
  The residual element identity `ρ.hom x = regroupEquiv.inv (1 ⊗ₜ x)` (after the existing `ext`/counit
  scaffold) closes by **`rfl`** — both sides reduce definitionally to `(1 : A ⊗_R R') ⊗ₜ[A] x`. The
  iter-023 conjectured re-break into `inner_value_apply` / `regroupEquiv_inv_one_tmul` element lemmas was
  unnecessary. Always `lean_multi_attempt` `rfl` on a residual element identity before authoring helpers.
- **Tilde-localization affine engine — sections localize on a basic open for essImage sheaves (iter-024,
  QUOT, two axiom-clean theorems).** "Basic-open restriction of a `tilde N` sheaf is
  `IsLocalizedModule (powers f)`": Mathlib already supplies `IsLocalizedModule (.powers f)
  (tilde.toOpen N (basicOpen f)).hom` (the localization map *out of N*); since `tilde.toOpen N ⊤` is an
  iso (`tilde.isoTop`) and `tilde.toOpen N (D f) = tilde.toOpen N ⊤ ≫ restriction` (`tilde.toOpen_res`),
  pre-compose with the inverse iso via `IsLocalizedModule.of_linearEquiv_right`. To transport to ANY
  `M : (Spec R).Modules` with `[IsIso M.fromTildeΓ]` (= essImage): `modulesSpecToSheaf.map M.fromTildeΓ`
  is an iso, forget to the presheaf via `(TopCat.Sheaf.forget _ _).map`, its naturality square for
  `D(f) ⟶ ⊤` intertwines the restriction maps, post-/pre-compose the tilde-restrict result with the two
  component isos. **Pitfalls (load-bearing):** (1) `↑e ∘ₗ ↑e.symm = id` does NOT close with `simp`/`rw`
  when `e` is `set`/`let`-bound (simp → `↑(e.symm ≪≫ₗ e)` then stalls) — prove pointwise
  `LinearMap.ext; intro x; change …; rw [e.apply_symm_apply]`; (2) a `TopCat.Sheaf` morphism has NO
  `.val`/`.1` field (it is an `InducedCategory.Hom`) — use `(forget _ _).map φ`; (3) `(forget).obj S` is
  defeq to `S.presheaf` but NOT syntactic, so the final map-identity must close in **term mode**
  (`refine (?_ : _=_).trans hc.symm; congr 1; exact …`), not `rw [hc]`; (4) `of_linearEquiv`/`_right`
  are instances — pass `(S:=)(f:=)(e:=)` by NAME (positional mis-binds `S`); two-deep auto-`inferInstance`
  chaining does NOT fire — build the steps explicitly. These two theorems are the affine engine of the
  keystone but the general QC case is gated on the unbuilt QCoh≃Mod bridge (see Known Blockers).

- **`erw` (defeq match) breaks the post-`subst` literal-form lock where `rw` cannot (iter-026, FBC —
  the 4-iter wall RESOLVED at the tactic level).** After `subst hfst/hsnd`, the `(g')`-unit leg locks
  into the literal `(pullbackSpecIso ↑R ↑A ↑R').hom ≫ Spec.map (CommRingCat.ofHom …)`, which is **defeq**
  to `e.hom ≫ Spec.map inclA` but differs in invisible implicit args, so `rw […_legs_unitExpand …]`
  reports "did not find pattern" even when the search pattern prints IDENTICALLY to the goal subterm.
  `rw` is syntactic; verified to fail in **five** arg-forms (no-arg `?a≫?b` unification, `set`-fvar args,
  exact-literal args, `simp only`, `hfst.symm ▸`). **`erw [base_change_mate_fstar_reindex_legs_unitExpand
  e.hom (Spec.map inclA) (tilde M)]` fires** (definitional matching), expanding the bare unit into the
  four-factor reindex form. CAVEAT (the inline `inner_value_eq` wall): `erw` still cannot cross a
  *propositional* (non-defeq) leg equality — the inline pre-subst route has the leg as `pullback.fst`,
  only `hfst`-equal to `e.hom ≫ Spec ιA`, and all three transport attempts (explicit `have hunit`,
  `hfst.symm ▸`, whole-goal `rw [hfst]`) hit the leg-dependent-motive wall. So: do the expansion
  POST-`subst` inside `_legs` (defeq), then `inner_value_eq := exact base_change_mate_fstar_reindex`.
  Memory `fbc-subst-legs-literal-form-lock` updated. (Distribution after expansion is still blocked by the
  `X.Modules` `CategoryStruct.comp` diamond — route through term-mode `…_gammaDistribute`, not
  `simp [Functor.map_comp]`; see the iter-019 term-mode pattern.)
- **G1-assemble glue: section-localization ⟹ `IsIso M.fromTildeΓ` (iter-026, QUOT, axiom-clean).** Given
  per-basic-open section localization (`∀ f, IsLocalizedModule (powers f) (restriction Γ(M,⊤)→Γ(M,D(f)))`),
  `IsIso M.fromTildeΓ` follows with NO descent: on each `D(f)` the component of
  `modulesSpecToSheaf.map M.fromTildeΓ` intertwines two localizations of `N=Γ(M,⊤)` (source via the
  `tilde.toOpen` instance, target by hypothesis), so it is `IsLocalizedModule.linearEquiv` (bijective);
  upgrade basis-wise iso to a sheaf iso with `isIso_sheaf_of_isIso_app_basicOpen` (= `isBasis_basic_opens`
  + `stalkFunctor_map_injective_of_isBasis` + `germ_exist_of_isBasis` + `isIso_of_stalkFunctor_map_iso`),
  then `SpecModulesToSheafFullyFaithful.isIso_of_isIso_map` reflects. Gotchas: `TopCat.Sheaf` is an
  `InducedCategory` — morphism's presheaf hom is `α.1` (NOT `α.val`); object presheaf is `.presheaf`
  (`.val` deprecated → `ObjectProperty.obj`); the stalk-iso instance must be a separate
  `have : ∀ x, IsIso …`, not supplied via `apply`. **Pass `IsLocalizedModule` facts as EXPLICIT lemma
  hypotheses** (`bijective_comp_of_localizations`): inline `set toO/res` zeta-unfolds and TC fails to find
  the hypothesis-supplied `IsLocalizedModule (powers f) res` instance (it searches the unfolded term where
  no instance is registered — the target localization is a hypothesis `H f`, not an instance). Keep `comp`
  as `set` (no TC) but write the two localization maps inline so `tilde.toOpen` + `H f` are found.
- **Scheme-level GlueData transition layer over generic base rings (iter-026, GR, 11 axiom-clean decls).**
  The "easy" `Scheme.GlueData` fields and the linchpin pullback iso for the Grassmannian: `chartIncl :=
  Spec.map (ofHom (algebraMap R^I (Away P^I_J)))` is an open immersion via
  `inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap … (Away …)))))` — `infer_instance`
  FAILS after `unfold chartIncl`. `f_id` (`chartIncl_self_isIso`): `minorDet_self`⟹`IsUnit`⟹
  `IsLocalization.atUnit` ⟹ `algebraMap` bijective ⟹ `IsIso` via `ConcreteCategory.isIso_iff_bijective`.
  Linchpin `awayPullbackIso : pullback(Spec R[1/x]→Spec R←Spec R[1/y]) ≅ Spec R[1/(xy)]` = `pullbackSpecIso`
  ≪≫ `Spec.mapIso` of `IsLocalization.algEquiv` (tensor ≅ `Away(x*y)` via `IsLocalization.Away.tensor`+`.mul'`);
  leg lemmas reduce to `IsLocalization.ringHom_ext (powers x)` + `AlgEquiv.commutes`. **State all such
  helpers over a GENERIC base ring `A`** — plugging the heavy chart ring `R^I = MvPolynomial (Fin d ×
  {q//q∉I}) ℤ` directly into `IsScalarTower`/tensor TC synthesis **times out** (20000 hb); the generic
  proof term carries the `IsScalarTower` instances. **Product-order subtlety** (load-bearing for `t'`):
  `cocycleΘIJ` has domain `Away(a*b)` but the target `awayPullbackIso` produces `Away(b*a)` — distinct
  propositional types; bridge with `awayMulCommEquiv : Away(a*b) ≃+* Away(b*a)` (`mul_comm`-transported
  `IsLocalization.Away` instance + `IsLocalization.algEquiv`), the reusable `orderSwap`. Need `open
  CategoryTheory` for `IsIso`/`ConcreteCategory`/`Limits`.
- **HasPullback-diamond recipe for the GR glue `t_fac`/`cocycle` (iter-028, `chartTransition'_fac`
  CLOSED).** On the heavy `MvPolynomial …ℤ` localisation pullbacks there is a severe `HasPullback`/Scheme
  instance diamond: the *same literal* `awayPullbackIso (minorDet …)` / `Limits.pullback.snd (chartIncl …)`
  elaborates to **different instance terms** in the `chartTransition'` def body vs a freshly-typed term vs
  the theorem statement, so syntactic `rw [Category.assoc / Iso.inv_hom_id / awayPullbackIso_inv_snd]`
  "fail to match" and `simp only [Category.assoc]` silently no-ops. The working recipe: (1) keep the iso
  from ONE source — `hfst := (Iso.inv_comp_eq _).mp (awayPullbackIso_inv_fst _ _)` so `.hom`/`.inv` share
  the instance; (2) fire the snd-leg with **`erw [awayPullbackIso_inv_snd]`** (defeq-tolerant); (3) close
  the final assoc-laden goal `apᴵᴶ.hom ≫ X = (apᴵᴶ.hom ≫ Y₁) ≫ Y₂` with **`exact congrArg (_ ≫ ·) hXY`**
  (associativity handled by defeq INSIDE `exact`, NOT available to `rw`/`simp`); (4) the pure-ring step
  `hXY` collapses cleanly with `← Spec.map_comp` / `← CommRingCat.ofHom_comp` (no pullback objects → no
  diamond). Honest `set_option maxHeartbeats 1600000`. **Internal iso-pair cancellation goes via `simp
  [Iso.inv_hom_id_assoc]` ONLY when both ends share a source** (GR cocycle: both `apXY.inv ≫ apXY.hom`
  pairs come from the `chartTransition'` def → matched instances → `simp` fires).
- **`map_units` for a section-localization sheaf is FREE via `tilde.isUnit_algebraMap_end_basicOpen`
  (iter-028, QUOT).** Mathlib's `AlgebraicGeometry.tilde.isUnit_algebraMap_end_basicOpen` (Tilde.lean:182)
  proves `IsUnit (algebraMap R (Module.End R Γ(M, D f)) f)` for an **ARBITRARY** `M : (Spec R).Modules`
  (not just `tilde N`). So the `map_units` field of G1-core closes by
  `rintro ⟨x, n, rfl⟩; simpa using (tilde.isUnit_algebraMap_end_basicOpen M f).pow n`. **Dead-end warning:**
  do NOT obtain `Module Γ(O,Df) Γ(M,Df)` by `infer_instance` on a `let`-bound carrier — the
  `modulesSpecToSheaf` carrier forgets scalars to `R` and the `let` hides the scalar tower; use the Mathlib
  lemma directly (it `change`s through the tower internally). The globally-presented sub-case of G1-core
  similarly composes for free: `haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_presentation M P; exact
  isLocalizedModule_restrict_of_isIso_fromTildeΓ M f`.
- **Composite-functor F-form + term-mode `congrArg`/`.trans` splice breaks the FBC `X.Modules`
  distribution wall (iter-030 — the iters 026–029 step-(iii) wall RESOLVED inside the locked goal).**
  The `_legs` distribution `Γ(G((a≫b)-unit)) = Γ(G(a-unit)) ≫ …` could not be rewritten by ANY keyed
  tactic (`rw`/`simp`/`erw`/`conv`/`set`/`dsimp`) — the `X.Modules`/`Functor.comp` instance diamond
  defeats `kabstract` even on a freshly-stated clean lemma whose factor prints IDENTICALLY to the goal
  (reconfirmed conclusively: `rw [hFc]` cannot locate a factor *literally present*). The working route is
  two-part: (1) state a helper lemma with BOTH sides at the **single composite functor**
  `F := (Spec φ)_* ⋙ moduleSpecΓFunctor` (one instance in scope, no diamond), so `simp only [←
  Functor.comp_map]; rw [gammaDistribute (F := F)]` fires; collapse the transparent `pushforwardComp`
  factor (`rfl`-trivially `𝟙`) purely in TERM mode:
  `exact (congrArg (· ≫ _) ((congrArg (_ ≫ _ ≫ ·) hFc).trans (congrArg (_ ≫ ·) (Category.comp_id _)))).trans (Category.assoc _ _ _)`.
  (2) Splice the verified helper into the locked main goal via a higher-order `congrArg`:
  `refine (congrArg (fun z => _ ≫ (z ≫ _) ≫ _) (helper e.hom (Spec.map inclA) φ (tilde M))).trans ?_`
  — the `congrArg`/`.trans` seam carries the `Functor.comp`/obj-form defeq bridge `rw` structurally
  cannot make. Memory `fbc-legs-termmode-splice-works`. General lesson: cross a category-instance diamond
  by reformulating at a single composite functor + term-mode `congrArg`/`Functor.congr_map`/`.trans`/
  `exact`, never keyed rewriting.
- **Over-site ↔ open-subspace SHEAF equivalence (iter-030, QUOT — fills the Mathlib
  `Topology/Sheaves/Over.lean` TODO).** `Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf
  (Opens.grothendieckTopology ↥U) A` for any category `A`, built from `Opens.overEquivalence U`. Recipe:
  prove both functors `IsCocontinuous` by a direct cover-lift — a sieve covers in `(gT X).over U` iff its
  `Sieve.overEquiv` image covers in `gT X` (`GrothendieckTopology.mem_over_iff`); the
  `Opens.grothendieckTopology` covering condition is the *pointwise* `∀ x ∈ V, ∃ W f, S f ∧ x ∈ W`
  (`CategoryTheory.Sites.Spaces`); transport points/covers across `Subtype.val : ↥U → X` (injective open
  embedding) with `U.isOpenEmbedding'.isOpen_iff_image_isOpen` + `Subtype.val_injective` +
  `Set.preimage_image`, matching the produced arrow to the sieve member by `Sieve.downward_closed` +
  `Subsingleton.elim` (Opens is a THIN category, so morphism equalities are `Prop`-valued — `Subsingleton.elim`
  is legitimate, not a smuggle). Then `Equivalence.isDenseSubsite_inverse_of_isCocontinuous` →
  `Equivalence.sheafCongr` for the equivalence; `Adjunction.isContinuous_of_isCocontinuous` on the two
  equivalence adjunctions gives the `IsContinuous` instances that the downstream module-level
  `SheafOfModules.pushforwardPushforwardEquivalence` needs. This is the topos-theoretic layer of gap1
  bridge C; the remaining steps (ring-sheaf identification, module lift, `restrictFunctorIsoPullback`) are
  geometric. The modules restriction functor (`Scheme.Modules.restrictFunctor`/`pullback`) ALREADY EXISTS
  (`Modules/Sheaf.lean:167,319`) — do NOT hand-roll it.
- **Slice→geometric restriction iso `overRestrictIso` — gap1 bridge C CLOSED, the step-2 "obstacle"
  collapses to `rfl` (iter-031, QUOT).** The abstract Grothendieck-slice `M.over U` is canonically iso to
  the geometric `(restrictFunctor U.ι).obj M`. **Step 2 (the named geometric ring-sheaf identification
  that looked like a wall) is `rfl`:** `U.toScheme.ringCatSheaf = (overEquivalence_sheafCongr U
  RingCat).functor.obj (X.ringCatSheaf.over U)` holds definitionally because `U.toScheme.presheaf =
  U.ι.opensFunctor.op ⋙ X.presheaf` is `rfl` (Mathlib `toScheme_presheaf_obj`/`_map`), and
  `(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor` is `rfl`. **Step 3
  `overRestrictEquiv`:** `SheafOfModules.pushforwardPushforwardEquivalence (Opens.overEquivalence U) φ ψ
  H₁ H₂` with `φ = whiskerRight (NatTrans.op eqv.unitIso.inv) ..`, `ψ = 𝟙` (legal because the ring sheaf
  is *definitionally* the transport); `H₁` via `Equivalence.unitInv_app_inverse`, `H₂` via `erw
  [Category.id_comp, ← Functor.map_comp]` + a separate `have` for the op-comp identity closed by
  `(congrArg map h).trans (Functor.map_id ..)`. **Step 4** = `pushforwardComp ≪≫ pushforwardCongr (by
  cat_disch)` (both sides pushforward along the same `rfl`-equal opens functor); the composition
  `IsContinuous` is NOT auto-synthesised — supply `haveI := Functor.isContinuous_comp`. `cat_disch`
  grinds the `Sheaf.Hom`/`.hom.app`-wrapped ring-morphism equality where manual `ext;simp` stalls.
  **Over/opposite-category syntactic-`rw` trap:** `rw [Category.id_comp]`/`rw [← op_comp]` fail by
  syntactic match even when the subterm is present — use `erw` + the defeq-aware `have`+`congrArg`. The
  pullback form `overRestrictPullbackIso := overRestrictIso ≪≫ restrictFunctorIsoPullback.app M` is what
  the downstream P1 `Presentation.map` transport consumes. `backward.isDefEq.respectTransparency false`
  was NOT needed here.
- **Cocycle-by-telescoping beats a giant generator computation (iter-031, GR `cocyclePhiId` — glue lane
  CLOSED).** The rotated triple-overlap ring cocycle `Φ = Θ_{I,J,K} ∘ swap_J ∘ Θ_{J,K,I} ∘ swap_K ∘
  Θ_{K,I,J} ∘ swap_I = id` is proved by telescoping: `rotMid` (conjugating the rotated `Θ_{J,K,I}` by the
  two order-swaps recovers `cocycleΘJK` in the I,J,K frame, checked on `R^K` by lift uniqueness) →
  existing `cocycleCondition` (`Θ_IJ ∘ Θ_JK = Θ_IK`) → ONE residual inverse pair `Θ_IK ∘ Θ_KI ∘ swap_I =
  id` closed by the matrix collapse `transitionInvImageMatrix` (`(W_K)⁻¹ W` with `W_I = 1`, analogue of
  `cocycle_imageMatrix_eq`'s `hRHS`). **Key insight: a single application of `cocycleCondition` to the
  3-fold loop leaves exactly ONE inverse pair — only that residual needs the matrix engine; the rest is
  composition algebra with the `_comp_algebraMap` lemmas.** The scheme-level cocycle field
  `chartTransition'_cocycle` then: `simp only [chartTransition', Category.assoc, Iso.inv_hom_id_assoc]`
  cancels the two internal `awayPullbackIso` pairs; six `Spec.map`s collapse via
  `←Spec.map_comp`/`←CommRingCat.ofHom_comp` into `Spec.map (ofHom Φ)`; `cocyclePhiId` + `ofHom_id` +
  `Spec.map_id` ⟹ `𝟙`; `rw [reassoc_of% h6, Iso.hom_inv_id]` closes (`reassoc_of%` auto-absorbs the
  `𝟙 ≫`). Needs `set_option maxHeartbeats 1600000` (HasPullback diamond on MvPolynomial away-localisation
  makes the Iso cancellation defeq-expensive). `Scheme.GlueData.glued` assembles the scheme;
  `f_mono`/`f_hasPullback` default `by infer_instance` WORKED (the prior "explicit instances needed"
  warning was wrong).
- **gap1-D section-localization descent in COVER form, sheaf-gluing not affine-equivalence (iter-035,
  QUOT `isLocalizedModule_basicOpen_descent_of_cover` CLOSED axiom-clean).** Hartshorne II.5.3 / Stacks
  `lemma-invert-f-sections` as a direct sheaf argument: for `M : (Spec R).Modules`, `f : R`, a finite
  basic-open cover `{D(r)}_{r∈t}` (`Ideal.span t = ⊤`) and per-cover-element localization data
  `Hfr : ∀ U, (∃ r∈t, U ≤ D(r)) → IsLocalizedModule (powers f) (Γ(M,U)→Γ(M,D(f)⊓U))`, prove
  `IsLocalizedModule (powers f) (Γ(M,⊤)→Γ(M,D(f)))`. Assemble the 3 fields: `map_units` from the
  pre-existing `map_units_restrict_basicOpen` (any `M`); `surj` = per-`D(r)` surjectivity with a common
  power `N`, overlap agreement up to a further power `P` (`IsLocalizedModule.exists_of_eq`), glue the
  `f^P`-scaled family by `TopCat.Sheaf.existsUnique_gluing'`, conclude on `D(f)` by `eq_of_locally_eq'`;
  `exists_of_eq` = per-cover-element `exists_of_eq` + `Finset.sup` + separatedness. **Crucially does NOT
  route through the global affine equivalence `QCoh(Spec R) ≃ Mod R` (which is gap1 itself).** Inputs:
  `existsUnique_gluing'`, `eq_of_locally_eq'`, `TopCat.Presheaf.IsCompatible` (unfolds to
  `Opens.infLELeft/Right` by `rfl`), `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`, `inf_iSup_eq`. The
  `IsLocalizedModule` field is `surj` (NOT `surj'`).
- **ModuleCat sheaf-restriction proofs must be TERM-MODE (iter-035, QUOT — recurring).** `rw
  [LinearMap.map_smul]` / `rw [res_comp …]` / `rw [ms_i]` fail to match the `ModuleCat.Hom.hom
  (….presheaf.map (homOfLE ⋯).op)` coercion even on syntactically identical terms — the elided
  `homOfLE` proofs defeat `rw`. Use fully-applied `LinearMap.map_smul g a x`, `res_comp F` with explicit
  `A B C`, `congrArg`, `.trans`. `res_comp` (restriction maps compose A→B→C = A→C) is itself term-mode
  via poset-hom `Subsingleton`. Power-of-`f` bookkeeping: `(mul_smul (f^P)(f^N) _).symm.trans (congrArg
  (· • _) (pow_add f P N).symm)`; `rw [← pow_add]` leaves a `(fun x => f^x) p` redex. `set g := …` before
  `rw` works but DON'T `set` whole-sheaf expressions (reverts bound vars / refolds in hyps).
- **GR properness — the three cheap valuative-criterion ingredients (iter-035, GR all axiom-clean).**
  `IsProper.of_valuativeCriterion [QuasiCompact][QuasiSeparated][LocallyOfFiniteType] (H : ValuativeCriterion
  f)` over GENERAL valuation rings (no DVR reduction — not in Mathlib, and Nitsure works verbatim).
  `ValuativeCriterion = Existence ⊓ Uniqueness` (`ValuativeCriterion.iff`). Cheap three for `toSpecZ`:
  (1) `compactSpace_scheme` via `GlueData.openCover.compactSpace` — supply `Finite openCover.I₀` and
  `∀ i, CompactSpace (openCover.X i)`; **use `inferInstanceAs (CompactSpace (Spec (CommRingCat.of
  (MvPolynomial …))))`, NOT `(affineChart …)` — the affineChart shim is not unfolded for the
  IsAffine→CompactSpace instance**; then `quasiCompact` via `HasAffineProperty.iff_of_isAffine.mpr`.
  (2) `locallyOfFiniteType` via `IsZariskiLocalAtSource.of_openCover` + `ι_toSpecZ` + `(HasRingHomProperty.Spec_iff
  (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr inferInstance)` — **use `exact …
  .mpr`, NOT `rw [Spec_iff]`** (source shows as `openCover.X i` not `Spec ?R`; the `.mpr` closes the
  defeq); `MvPolynomial.finiteType` does NOT exist. (3) `quasiSeparated` + `valuativeUniqueness` are both
  FREE from `isSeparatedToSpecZ` (`[IsSeparated]→QuasiSeparated` instance; `IsSeparated.valuativeCriterion`).
  `isProper_of_valuativeExistence` bundles all four, reducing `isProper` to the SINGLE obligation
  `ValuativeCriterion.Existence`. **UPDATE (iter-038): the Existence obligation is now DISCHARGED and
  `Grassmannian.isProper` (`lem:gr_proper`) is PROVEN axiom-clean — Gr(d,r) is proper over ℤ.** The
  E1→E2→E3→E4→E5→E6 arc closed via `valuativeExistence_toSpecZ` (see the iter-038 valuative-criterion
  assembly pattern above). The GR PROPERNESS LANE IS COMPLETE — do not re-assign. (GR-quot / GR-repr
  are separate lanes in other files/chapters.)
- **FBC conjugate-chain atomization device: param-then-rfl (iter-035, FBC — isolates but does NOT close
  the crux).** To atomize the `_legs` reindex obstruction: (1) abstract the single pullback-composition
  factor of the variable-legs codomain read as an explicit iso argument (`base_change_mate_codomain_read_legs_param`)
  so the original read RECOVERS BY `rfl` (`_eq_param`); (2) `conjPullbackFactor` packages
  `Adjunction.leftAdjointCompIso` of the free legs and identifies it with the project `pullbackComp` via
  `pullbackComp_eq_leftAdjointCompIso` — needs explicit `letI : Algebra ↑R ↑A := φ.hom.toAlgebra` etc. in
  the TYPE; use `change Adjunction.leftAdjointCompIso _ _ _ _ = _` (NOT `show` — avoids the changed-goal
  linter); (3) the conjugate-native read = param at `conjPullbackFactor`, bridged to the concrete read in
  a 3-line `rw`. Restate transparent-coherence collapses over GENERIC scheme morphisms, not the concrete
  legs (concrete fails `Algebra ↑R ↑A` synthesis). This made `_legs` a sorry-free thin wrapper and landed
  7 axiom-clean decls — but the residual `sorry` only MOVED into the named conjugate identity conj-2a.
- **Determinant of a column-substituted identity matrix — cramer, NO sign (iter-037, GR E3-cofactor).**
  `((1 : Matrix (Fin d) (Fin d) R).updateCol p v).det = v p` (Mathlib has NO `det_updateColumn`/
  `det_succ_column` clean route): `rw [Matrix.cramer_apply]` (reverse — equates `(A.updateCol i v).det` with
  `(A.cramer v) i`) then `have := Matrix.mulVec_cramer (1) v; rwa [Matrix.one_mulVec, Matrix.det_one,
  one_smul] at this`. The result is exactly `v p` — the column-substituted-identity determinant carries **no
  sign**. To then read a free universal-matrix entry `X^J_{p,q}` (`q ∉ J`) as `±` a signed minor `P^J_{K'}`
  (`exists_minorDet_eq_free_entry`): build the column map `colMap k := if k=p then q else (J.orderIsoOfFin hJ
  k)`, show `X^J.submatrix id colMap = (1).updateCol p v` (using `X^J_J = 1`), then `Matrix.det_permute'` +
  `Int.units_eq_one_or (Equiv.Perm.sign σ)` splits into the `= X` / `= -X` disjunction. Pitfalls: `set`-bound
  functions must be `simp only [hdef]`-beta-reduced BEFORE `rw [if_pos/if_neg]`; use `Matrix.ext` (NOT bare
  `ext`, which descends into `MvPolynomial.coeff`); the lemma is `Finset.card_insert_of_notMem` (NOT
  `_not_mem`). Closure of "every generator lands in `R`" via `MvPolynomial.induction_on` with case tags
  **`C` / `add` / `mul_X`** (NOT `h_C`/`h_add`/`h_X` — that errors "Invalid alternative name"); constants via
  `RingHom.ext_int` + `map_intCast`.
- **`IsLocalizedModule` transport across a RING ISO is Mathlib-absent — build it semilinearly (iter-037,
  QUOT gap1-D Hfr ingredients).** Mathlib only has the same-ring `IsLocalizedModule.of_linearEquiv` /
  `of_linearEquiv_right`. To cross a ring iso `σ : R ≃+* R'` (ingredient I,
  `isLocalizedModule_of_ringEquiv_semilinear`): take a pair of σ-semilinear `AddEquiv`s `e₁ e₂` as **plain
  equation hypotheses** `eᵢ (a • x) = σ a • eᵢ x` (avoids semilinear-composition typeclass plumbing) and
  construct the three `IsLocalizedModule` fields directly — `map_units` via `Module.End.isUnit_iff` →
  `Function.Bijective` (the `N₂`-End is conjugate via `e₂` to the unit `M₂`-End: `Module.algebraMap_end_apply`
  + `he₂` + `e₂.apply_symm_apply`), `surj`/`exists_of_eq` pull/push through `eᵢ.symm`/`eᵢ`, image-submonoid
  witness `⟨σ ↑s, ↑s, s.2, rfl⟩`. To descend a localization at `powers (algebraMap R Rr f)` over `Rr` to
  `powers f` over `R` (ingredient II, `isLocalizedModule_restrictScalars_powers_algebraMap`): map
  `f^n ↔ (algebraMap R Rr f)^n` via `map_pow` + `algebraMap_smul` (`(algebraMap R Rr a) • m = a • m`);
  `map_units` again `Module.End.isUnit_iff` (the two `End` maps are the SAME underlying function). Both
  axiom-clean. **Dead-end:** do NOT apply (I) with `σ := (R_r ≅ R)` — `R_r` and `R` are NOT isomorphic; the
  σ's are between section rings of isomorphic opens, the `R_r → R` descent is (II)'s job.
- **Valuative-criterion existence assembly — term-mode glue through the Scheme-category diamond
  (iter-038, GR properness CLOSED).** The whole E4→E5→E6 arc landed axiom-clean.
  (1) **Fillers are DATA → `noncomputable def`, not `theorem`.** `existence_lift` produces
  `sq.LiftStruct` (data); declaring it `theorem` errors "type ... is not a proposition". `fac_left`
  (top triangle) via `existence_chart_kpoint_eq` + term-mode `calc`; `fac_right` (bottom triangle,
  both legs into terminal `Spec ℤ`) = `specZIsTerminal.hom_ext _ _`.
  (2) **Keyed `rw`/`Category.assoc`/`Spec.map_comp` FAIL on `Spec.map (CommRingCat.ofHom …)`
  compositions over heavy `MvPolynomial`/`Localization.Away` objects** — "Did not find an occurrence
  of the pattern" even when the subterm prints verbatim (the Scheme-category instance diamond, same
  as `chartTransition'_fac` @914). Both assoc orientations + `clear_value` fail (the `set`-let on
  `f'` is NOT the root cause). **Fix = term mode:** `(Category.assoc _ _ _).symm`,
  `(Spec.map_comp _ _).symm`, `congrArg (· ≫ h)`, `congrArg Spec.map`, `congrArg (f ≫ ·)`, `calc`.
  The glue step used `congrArg (Spec.map (ofHom f') ≫ ·) hglue`.
  (3) `valuativeExistence_toSpecZ` (E5): chain E1→E2→E3→E4, package `⟨⟨…⟩⟩` (`CommSq.HasLift`). E2
  `existence_minimal_valuation` needs `(R := S.R)` explicitly (R only appears in
  `ValuationRing.valuation R K`, not inferable from `f`). `isProper` (E6) is then the one-liner
  `isProper_of_valuativeExistence d r (valuativeExistence_toSpecZ d r)`.
  (4) **Corestrict-to-base** (`liftToBaseOfMemRange`): a ring hom `φ : A → K` whose image lies in
  `(algebraMap R K).range` corestricts to `A → R` via `RingEquiv.ofBijective (algebraMap R K).rangeRestrict`
  (surjective by `rangeRestrict_surjective` + injective by `IsFractionRing.injective`).
- **`erw` for `ConcreteCategory.hom (Hom.app ψ V)` coercion matching (iter-038, QUOT semilinearity
  wall).** `gammaPullbackImageIso_hom_semilinear` (`hom (a • x) = σ_V a • hom x`) closes in 3 steps:
  `simp only [gammaPullbackImageIso, Functor.mapIso_hom, Functor.comp_map, toPresheaf_map,
  evaluation_obj_map, mapPresheaf_app]` (unfold the iso's forward map to the section map `ψ.app V`),
  then `erw [Scheme.Modules.Hom.app_smul]` (**`erw` not `rw`** — the goal's explicit
  `ConcreteCategory.hom` coercion defeats `rw`'s syntactic match, `erw`'s defeq match fires), then
  `rfl` (the `restrictFunctor = pushforward₀ ⋙ restrictScalars` structure makes `a •_restrict m`
  *definitionally* `(j.appIso V).inv a •_M m`, and `σ_V a = commRingCatIsoToRingEquiv.symm a =
  (j.appIso V).inv a`). **CAVEAT (auditor major):** the final `rfl` is an UNGUARDED defeq — fragile to
  a future `commRingCatIsoToRingEquiv` Mathlib change; consider an explicit rewrite chain when next
  touched. The open-immersion ring iso `σ_V := (j.appIso V).commRingCatIsoToRingEquiv.symm` must be
  oriented **source → image** (`Γ(X,V) ≃+* Γ(Y, j ''ᵁ V)`) to typecheck the statement and feed
  bridge (I) `isLocalizedModule_of_ringEquiv_semilinear` verbatim.
- **Generalize-to-free-legs collapses a conjugate leg to a one-liner (iter-039, FBC conj-2b).** The
  pullback-side leg of the conjugate identity, when stated at the SPECIALIZED composites
  `g' = e∘Spec ιA` / `f' = e∘Spec ιR'`, looks like a bespoke obligation; stated at **free legs `f g`**
  it is exactly the Mathlib coherence `conjugate(leftAdjointCompIso … (pushforwardComp f g)).inv =
  (pushforwardComp f g).hom`, so `base_change_mate_reindex_conj_pullbackLeg` closes by
  `exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _`. Lesson: before hand-proving a
  conjugate/mate leg at specialized morphisms, restate it at free morphisms and check for a direct
  `conjugateEquiv_*`/`leftAdjointCompIso` Mathlib hit.
- **Ring-map-general port of a Seam-1 affine-unit value (iter-039, FBC conj-2d).** The cross-layer
  affine-unit transport `base_change_mate_reindex_conj_crossLayer` is the general-ring-map version of
  Seam-1's `base_change_mate_unit_value`: the surviving geometric `(Spec ψ)`-unit factor, conjugated by
  the two tilde dictionaries (`pullback_spec_tilde_iso`, `pushforward_spec_tilde_iso`), equals the
  algebraic unit. Proof = `erw [reassoc_of% huce]` (the counit master identity
  `unit_conjugateEquiv_symm`) + multi-`simp` on the dictionaries, under `maxHeartbeats 4000000` with a
  controlled `rfl` at `hpullinv`. (Add a heartbeat-justification comment — auditor minor.)
- **`IsLocalizedModule` across a localization ring-iso + powers descent, combined (iter-039, QUOT
  `isLocalizedModule_powers_transport`).** Chain the two project-local bridges into one transport: given
  `σ : S ≃+* A` (`[Algebra R A]`) with `σ f' = algebraMap R A f`, an `IsLocalizedModule (powers f') g`
  over `S`, σ-semilinear `e₁,e₂` into `A`-modules, and `A`-linear `h` with `h(e₁ x) = e₂(g x)`, conclude
  `IsLocalizedModule (powers (algebraMap R A f))`. Composes `isLocalizedModule_of_ringEquiv_semilinear`
  (I) over `isLocalizedModule_restrictScalars_powers_algebraMap` (II); `Submonoid.map_powers` bridges
  `powers (σ f')` and `σ (powers f')`. Axiom-clean.
- **Restrict cover-descent `Hfr` data to BASIC OPENS to make it provable (iter-039, QUOT
  `..._of_basicOpen_cover`).** The general-U section-localization descent `_of_cover` is an unprovable
  trap (the localization data simply does not exist at arbitrary `U`). The usable form threads an
  `(∃ s, U = PrimeSpectrum.basicOpen s)` precondition through `descent_surj`'s `Hfr`, so the cover only
  ever demands localization data where it exists. Both call sites supply the witness: the single-element
  case via `⟨r, rfl⟩`, the overlap `D(i) ⊓ D(j)` via `⟨i*j, (PrimeSpectrum.basicOpen_mul i j).symm⟩`.
- **`IsIso M.fromTildeΓ` is iso-invariant via the essImage characterization (iter-039,
  `isIso_fromTildeΓ_of_iso`).** `IsIso M.fromTildeΓ ↔ M ∈ essImage (tilde.functor R)`
  (`isIso_fromTildeΓ_iff`); `Functor.essImage.ofIso` then transports the property along any `M ≅ M'`.
  One-liner: `rw [isIso_fromTildeΓ_iff]` then `exact (essImage.ofIso …) ‹…›`.
- **Composite-immersion `fromTildeΓ` transport via `pullbackComp` coherences (iter-040, QUOT producer
  (a) `pullback_composite_immersion_isIso_fromTildeΓ`).** To get `IsIso ((pullback j).obj M).fromTildeΓ`
  for a composite immersion `j = isoSpec.inv ≫ ι_W ≫ ι_{q.X i}`: identify the composite pullback with
  the **iterated** pullback (on which the P1 keystone `isIso_fromTildeΓ_restrict_basicOpen` already
  supplies `IsIso fromTildeΓ`) by chaining **two** `Scheme.Modules.pullbackComp` pseudofunctor
  coherences with `≪≫`, then transport via `isIso_fromTildeΓ_of_iso`. Three load-bearing gotchas:
  (1) `≫` is **right-associative**, so the iso order is
  `(pullback A).mapIso ((pullbackComp B C).app M) ≪≫ (pullbackComp A (B ≫ C)).app M`;
  (2) state the goal with the explicit `@Scheme.Modules.fromTildeΓ (Γ(...)) (...)` form (the def is
  over `Spec (.of R)`; bare `.fromTildeΓ` triggers an HOU failure unifying `Γ(...)` with
  `CommRingCat.of ↑?m`); (3) the `[IsIso ·.fromTildeΓ]` instance is in nested-`obj` form while the iso
  source is in `⋙`/`.comp` form — TC won't syntactically match, so **pass it positionally**
  `@isIso_fromTildeΓ_of_iso _ _ _ e (proof)` (term-mode defeq succeeds). lean-auditor certified the
  `@`-positional idiom as legitimate, not defeq abuse.
- **`unfold` (not `rw`) to expand a `noncomputable def`; declare `IsOpenImmersion` before `.opensRange`
  (iter-040, `compositeBasicOpenImmersion_opensRange`).** A `noncomputable def` has no equational lemma
  so `rw [theDef]` fails — use `unfold theDef`. `.opensRange`/`''ᵁ` cannot even be *stated* without an
  `[IsOpenImmersion j]` instance, so declare that instance first (`unfold; infer_instance`). Range of a
  composite-of-(iso + open immersions): `opensRange_comp_of_isIso → opensRange_comp → opensRange_ι →
  image_preimage_eq_opensRange_inf → opensRange_ι`, closing `(q.X i) ⊓ D(s) = D(s)` with
  `inf_eq_right.mpr hs`.
- **The QUOT TOP `Hfr` producer's wall is a structure-sheaf re-basing, not new math (iter-040).** The
  `section_localization_hfr_basicOpen` combiner's `σ : S ≃+* A` is over the **CommRingCat `S`**, but the
  proven `gammaPullbackImageIso_hom_semilinear` is over the **structure-sheaf** action of `Γ(Spec S, V)`
  via `gammaImageRingEquiv j V`. The working `σ` must therefore be the **composite**
  `(Scheme.ΓSpecIso S).symm-as-RingEquiv ≪≫ gammaImageRingEquiv j ⊤` (ΓSpecIso at `Scheme.lean:606`),
  and producer (c) `gamma_image_iso_semilinear_top` must give semilinearity over THAT composite. The
  genuine hard core is how `modulesSpecToSheaf` re-bases the `ModuleCat S`-action along `ΓSpecIso`.
  Algebra side: `A = Γ(Spec R, D(s))` gets `Algebra R A`/scalar tower via restriction-map
  `.hom.toAlgebra` (patterns at `Scheme.lean:725`, `Restrict.lean:200`).
- **Opaque-immersion device closes the gap1 section-transport producer (iter-041 — the gap1 keystone).**
  A heavy `IsLocalizedModule` assembly whose final form-coercion mentions a CONCRETE composite open
  immersion `j = isoSpec.inv ≫ ι_W ≫ ι_{q.X i}` triggers a **>3.2M-heartbeat `whnf` runaway** (the kernel
  unfolds the triple composite) — raising `maxHeartbeats` to 1.6M/3.2M does NOT help. **Fix:** push the
  entire assembly into a helper that takes the immersion as an OPAQUE hypothesis
  (`j : Spec S ⟶ Spec R [IsOpenImmersion j]`), where the SAME coercion is a cheap `rfl`; instantiate
  concretely in a thin wrapper. This resolved BOTH `image_basicOpen_of_affine` (the `rw`-chain on the
  concrete immersion timed out at `isDefEq` even with `backward.isDefEq.respectTransparency false`) and
  the heavy core `section_localization_hfr_aux`, and was the reason gap1 churned ~5 iters. Inside the
  opaque helper: the combiner is `isLocalizedModule_powers_transport`; section isos `e₁/e₂` come from
  `gammaPullbackImageIso_hom_semilinear`; the open-transport across `eqToHom` opens uses
  `IsLocalizedModule.of_linearEquiv_right αU` then `of_linearEquiv αV.symm`, with the final intertwiner
  proven via a forward naturality square using only forward `eqToHom` isos (both `rfl`-identified) — NOT
  via `ModuleCat.hom_ext` (which fails to unify). `set_option maxHeartbeats 1600000` covers the legitimate
  multi-step assembly (lean-auditor certified it not masking fragility). The analogist `quot-sigma-rebasing`
  defeqs (`ModuleCat S`-action vs `Γ(Spec S,⊤)` structure-sheaf action, at `⊤` and `D(f')`) are all `rfl`.

- **`show … from`-ascription is mandatory to state `IsLocalizedModule (powers f) (restrictₗ M i)`
  (iter-042, QUOT gap2-core).** The `Γ(X,U)`-linear section restriction `restrictₗ M i :
  Γ(M,U) →ₗ[Γ(X,U)] Γ(M,V)` carries the codomain module structure `Module.compHom _ (X.presheaf.map
  i.op).hom`. When this map is the second argument of `IsLocalizedModule`, the domain instance `Module
  Γ(X,U) Γ(M,U)` **fails to synthesize** — `M`/`M'` are still metavariables when `IsLocalizedModule`
  fires instance search (elaboration order). Fix: put the SAME `letI : Module … := Module.compHom …` in
  scope AND wrap the map `show Γ(M,U) →ₗ[Γ(X,U)] Γ(M,V) from restrictₗ M i`. Both are load-bearing.
  lean-auditor certified the in-scope instance matches `restrictₗ`'s return type — no defeq weakening.
- **`← eqToHom_map` folding closes a `fromSpec`-section coherence (iter-042, QUOT gap2 crux
  `fromSpec_image_top_section_coherence`).** To prove `X.presheaf.map (eqToHom eT.symm).op =
  (hU.fromSpec.appIso ⊤).hom ≫ (ΓSpecIso Γ(X,U)).hom` (i.e. the eqToHom section transport equals the
  `appIso∘ΓSpecIso` composite — equivalently `ρ(σ f) = f`): `← cancel_epi`; `appIso_hom'` + `appLE`;
  `reassoc_of% fromSpec.naturality`; `fromSpec_app_self`; then **fold the lone Spec-presheaf `eqToHom`
  back into a `presheaf.map` via `← eqToHom_map`** (its side goal `op ⊤ = op (fromSpec⁻¹ᵁ fromSpec''ᵁ⊤)`
  closes by `rw [eT, fromSpec_preimage_self]`), merge with the leftover `homOfLE.op` via `← map_comp_assoc`,
  and the merged `op ⊤ ⟶ op ⊤` Spec morphism is **forced by `Subsingleton.elim _ (𝟙 (op ⊤))`** → `map_id`
  → `Iso.inv_hom_id`. This was the irreducible "sole genuinely new piece" the gap2 blueprint flagged; took
  ~25 iterative rewrite-pattern-not-found attempts before landing. Axiom-clean and reusable.
- **Same-ring shortcut: drop `restrictScalars` when porting a `Spec R` localization-transport to a general
  scheme (iter-042, QUOT `section_localization_hfr_aux_general`).** The iter-041 affine aux
  `section_localization_hfr_aux` needed bridge (II) `restrictScalars` because the localization ring `R`
  differed from `A = Γ(Spec R, …)`. Porting to a general ambient scheme `X` (localization ring taken
  LOCALLY as `A = Γ(X, j ''ᵁ ⊤)`), the base and target rings COINCIDE, so bridge (II) vanishes — only
  bridge (I) `isLocalizedModule_of_ringEquiv_semilinear` (transport across `σ`, landing `(powers f').map σ
  = powers (σ f') = powers f`) is needed. Engine: `isLocalizedModule_restrict_of_isIso_fromTildeΓ` on `M' =
  (pullback j).obj M` over `S`; section isos via `gammaPullbackImageIso(_hom_semilinear)`. Takes the P1
  datum `hP1 : IsIso (fromTildeΓ ((pullback j).obj M))` as a hypothesis (its producer — QC preserved under
  pullback along `hU.fromSpec` — is the remaining gap2 Piece A).
- **QUOT gap2 CLOSED — Piece A route-1 chain L1–L6 (iter-044).** The Mathlib-absent QC-under-pullback gap
  (`isQuasicoherent_pullback_fromSpec`) builds as a `\uses`-linked chain, all axiom-clean, closing gap2
  (`isLocalizedModule_basicOpen`) — the ~16-iter section-localization arc. Reusable techniques:
  (1) **L1 equivalence-transport bypass** — the iter-043 gateway friction (`unitToPushforwardObjUnit` /
  `Functor.IsContinuous` non-synth / `↥V` vs `↥↑V` coercion) is sidestepped, NOT fought:
  `overRestrictUnitIsoInv := (overRestrictEquiv V).inverse.mapIso (overRestrictUnitIso V).symm ≪≫
  (overRestrictEquiv V).unitIso.symm.app _`. The direct `unitToPushforwardObjUnit_of_isIso'` route is a
  DEAD END. (2) **Open-immersion pullback unit-iso via Final** — `Opens.map k.base` is a right adjoint
  (`IsOpenMap.adjunction`, `k.base` open map) hence `Final` (`final_of_isRightAdjoint`), making
  `pullbackObjUnitToUnit` an iso (`pullbackOpenImmersionUnitIso`; generalizes `pullbackSchemeIsoUnitIso`).
  (3) **Dot-notation universe pin** — state a QC conclusion as `(... .over ...).IsQuasicoherent`; the bare
  `SheafOfModules.IsQuasicoherent (...)` form DEFAULTS universes to 0 and fails to unify. (4) **`q.shrink`
  for `of_coversTop`** — `IsQuasicoherent.of_coversTop` needs the index in `Type u`; `QuasicoherentData.
  shrink` lands it there, and a `Nonempty M.QuasicoherentData` ascription pins the universe before
  `obtain`. (5) slice-site machinery (`over`, `of_coversTop` bind, presentation transport) needs
  `maxHeartbeats 1600000–2000000` + `synthInstance.maxHeartbeats 800000` (+ `backward.isDefEq.
  respectTransparency false` for the presentation transport L3).
- **Presheaf-section semilinearity transport, fully worked (iter-059, GF; closed the LAST `genericFlatness`
  sorry, file now axiom-clean).** To discharge `l (c•x) = (RingEquiv.refl _) c • l x` where
  `l = (F.presheaf.mapIso (eqToIso (congrArg op hbg))).addCommGroupIsoToAddEquiv` (the additive iso fed to
  `flat_of_ringEquiv_semilinear`): (1) `simp only [RingEquiv.coe_refl, id_eq, Iso.addCommGroupIsoToAddEquiv_apply,
  Functor.mapIso_hom, eqToIso.hom]` reduces `l y` to `(F.presheaf.map (eqToHom (congrArg op hbg))) y`;
  (2) recognise `eqToHom (congrArg op hbg) = i.op` for `i := homOfLE (le_of_eq hbg.symm)` via `Subsingleton.elim`
  (the opposite-Opens hom-category is thin); (3) rewrite the SOURCE action `c•x` into the native `Γ(X,·)` action
  with two `← IsScalarTower.algebraMap_smul`; (4) `Scheme.Modules.map_smul F i sgb x` (Mathlib
  `AlgebraicGeometry/Modules/Sheaf.lean`) pushes the presheaf map through the smul; (5) the TARGET action is a pure
  `Module.compHom` defeq — `rw [show … from rfl]`, no registered tower; (6) `congr 1` to the scalar-agreement goal,
  which is the SAME `appLE`-square shape as `hsquare`: prove `morLHS`/`morRHS` (via `appLE_map_assoc`/`appLE_map`,
  `map_appLE_assoc`/`appLE_map`), `congrArg (·.hom c)` + `simp only [CommRingCat.hom_comp, RingHom.comp_apply]`,
  `exact hL.trans hR.symm`. Both scalar images collapse to `p.appLE (D f) (D g) hg_pre c` (≤ proof-irrelevant).
  GOTCHA: the `congrArg` fun annotation must be the concrete `Γ(S, S.basicOpen f) ⟶ Γ(X, …)`, NOT `(A : CommRingCat) ⟶ …`.
- **GL_d matrix → automorphism of a free sheaf via `biproduct.matrix` of `scalarEnd`s (iter-059, GR-quot; built the
  bundle-transition realisation + proved C1 `bundleTransition_self`).** Layering: (a) `scalarEnd a : 𝟙 ⟶ 𝟙` =
  `unitHomEquiv.symm (globalUnitSection a)`; its value is multiplication, `scalarEnd_val_app` is a `rfl` + `smul_eq_mul`
  (NOT `rw [scalarEnd_val_app, one_mul]` — that pattern won't be found; use `exact one_smul _ _` / collapse to the smul
  form). Ring-hom laws: `scalarEnd_comp` (=`scalarEnd (a*b)`), `_add`, `_one`, `_zero`, `_sum`. (b) `matrixEnd M` =
  `biproduct.matrix (fun i p => scalarEnd (M p i))` on `⨁ (Fin d) 𝟙`; `matrixEnd_comp` = `matrixEnd (N*M)` via
  `biproduct_matrix_comp` (`simp only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π,
  biproduct.lift_desc, biproduct.ι_matrix, biproduct.lift_π]`; NOTE `biproduct.matrix_components` won't rewrite
  positionally) + `scalarEnd_comp` + `← scalarEnd_sum` + `Matrix.mul_apply` with per-entry `mul_comm` (matrix arg order
  flips: `matrixEnd M ≫ matrixEnd N = matrixEnd (N*M)`); `matrixEnd_one` = 𝟙 via `biproduct.ι_π_self`/`ι_π_ne`.
  (c) `matrixToFreeIso` from an invertible matrix; `bundleTransition` = `pullbackFreeIso ≪≫ matrixToFreeIso(Cramer-inv)
  ≪≫ pullbackFreeIso.symm`. (d) C1 `bundleTransition_self`: `universalMinorInv_self` → `map_one` →
  `erw [matrixEnd_one, Category.id_comp]` (plain `rw [Category.id_comp]` fails "motive not type correct" under the iso;
  `simp only`/`conv` also fail — `erw` is the route) → `Iso.comp_inv_eq` → `pullbackFreeIso_eqToHom`.
  **UPDATE (iter-060): the (d) C1 `.hom`-cast route above is SUPERSEDED — it passes the kernel only under
  `maxHeartbeats 1e6` and drives the cold build to ~227s/~13GB+ (the iters-058/059 OOM). Re-proven at the
  ISO level (22s/~7GB, default heartbeats, override removed): see the OOM-control pattern below.**
- **Kernel-cost / OOM is invisible to the LSP — validate heavy proofs with a real `lake build`, and reduce
  it by a leaner TERM, never a bigger heartbeat budget (iter-060, GR; cleared a 3-iter cold-build/sync_leanok
  ceiling).** Symptom: LSP `lean_goal` reaches `goals_after: []` (elaboration OK) but a real `lake build`
  (olean removed) fails `…:NNN: (kernel) deterministic timeout`; bumping `maxHeartbeats` makes the kernel
  pass but the term is so large the cold build OOM/exit137s. Lesson: a *passing* kernel check uses the same
  memory regardless of the heartbeat ceiling — the fix is a smaller proof term. Recipe that worked for
  `bundleTransition_self`: (1) push all concrete-immersion work into a GENERIC helper with the immersions as
  VARIABLES, proved by `subst` — `lemma pullbackFreeIso_trans_symm_eqToIso {φ ψ : T' ⟶ T} (h : φ = ψ) :
  pullbackFreeIso φ I ≪≫ (pullbackFreeIso ψ I).symm = eqToIso _ := by subst h; simp` — so the kernel never
  whnfs `chartIncl`/`chartTransition` (application is cheap by proof-irrelevance of the `eqToIso` motive);
  (2) collapse the matrix factor in a SMALL context (single overlap free sheaf, no pullback types in scope)
  to `Iso.refl _`; (3) `erw [hB]` (NOT `rw`/`simp` — Modules-diamond: hidden implicit base scheme is
  defeq-but-not-syntactic ⇒ "pattern not found"/"no progress") then `exact <generic helper>`. Was proof-local
  (whole-file build dropped 227s→22s from this one proof) ⇒ NO file split needed.
- **`Ab`-level coequalizer-row naturality: prove the bare-`ℤ` square then transport, don't `⊗`-induct at the
  `Ab` level (iter-060, SNAP; closed `relTensorProj.naturality` + finished the actL/actR/proj rows, file 0
  sorries).** Element-level `induction z using TensorProduct.induction_on` on a `↥(AddCommGrpCat.of (M ⊗[ℤ] N))`
  carrier STALLS in the `add` case: `map_add`/`simp only [map_add]` report `Did not find an occurrence of the
  pattern ?f (?x + ?y)` because the `AddCommGrpCat.of`-wrapped `AddCommGroup` instance does not unify with the
  bare-tensor `AddMonoidHomClass`. (`zero`/`tmul` DO close by `rfl` — the `forget₂ CommRingCat RingCat` carrier
  identity does NOT bite under `rfl`; the obstacle is additivity, not the carrier — the long-feared "forget₂
  blocker" was illusory.) Route that works: state the underlying `ℤ`-linear naturality square as
  `have key : … = …` of bare `ℤ`-linear maps (codomain restriction = `(AddCommGrpCat.Hom.hom (…).map f).toIntLinearMap`),
  prove it by `apply TensorProduct.ext'; intro m n; rfl`, then transport:
  `apply AddCommGrpCat.hom_ext; ext z; have hz := LinearMap.congr_fun key z; simpa only [...] using hz`.
  GOTCHA: a fresh `have` mentioning `(P ⊗ Q)` re-resolves `⊗` to `TensorProduct` and fails synthesis — write
  `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q` explicitly. Mirrors the `relTensorActL`/`actR` recipe.

### Mathlib idioms / pins (this Mathlib pin)

- **No `IsCoherent` predicate** at the pin. Encode coherence as `IsQuasicoherent` +
  `IsFiniteType` (both verified present). Any `genericFlatness`-style signature must carry
  these hypotheses, or it is false-as-written and yields an unprovable sorry. **UPDATE (iter-023):
  these are NECESSARY BUT NOT SUFFICIENT for the geometric form — `genericFlatness` ALSO needs
  `[QuasiCompact p]` (LocallyOfFiniteType ⇏ QuasiCompact; see the audit-before-prove pattern above).**
- **`IsIntegral.component_integral` / `IsLocallyNoetherian.component_noetherian` Nonempty trap
  (iter-023).** `IsIntegral.component_integral (U : X.Opens) [Nonempty ↥↑U] : IsDomain Γ(X,U)` wants the
  instance over the coercion `↥↑U` (Set-coercion then subtype), which matches NEITHER the Opens-CoeSort
  `↥U` NOR `↥(U : Set ↥X)` at instance-resolution reducibility — a plain `haveI : Nonempty ↥U := ⟨…⟩`
  will NOT be picked up. Supply via `@`-application: `@IsIntegral.component_integral X _ U ⟨⟨x,hx⟩⟩`.
  Verified-present tools for the GF-geo base ring `A := Γ(S,U₀)`: `component_integral` (IsDomain) +
  `IsLocallyNoetherian.component_noetherian ⟨U₀,hU₀aff⟩` (IsNoetherianRing). See memory
  `component-integral-nonempty-coercion-trap`.
- **No schematic/proper-support closed-subscheme** and **no rank-`r` local-freeness** at the
  pin (`IsProper` exists but the schematic-support closed subscheme does not;
  `SheafOfModules.IsLocallyFree` is upstream-only and rank-agnostic). QUOT stubs cannot be
  re-signed honestly until these are built project-side. **`IsLocallyFreeOfRank` built
  project-side iter-007** (see universe pattern above), closing the rank-indexed gap.
- **No QCoh→`IsLocalizedModule` section-localization bridge for general `X.Modules` (iter-007).**
  `SheafOfModules.IsQuasicoherent` is a site-level notion (via `QuasicoherentData`); the concrete
  "sections localize at basic opens as `IsLocalizedModule (powers f)`" statement exists ONLY in the
  Spec-specific `ModuleCat.Tilde` development (`Mathlib.AlgebraicGeometry.Modules.Tilde`), not for a
  general quasicoherent `X.Modules`. **Update iter-011:** the annihilator ideal sheaf DEFINITION no
  longer needs this bridge — `Scheme.Modules.annihilator` landed axiom-clean via `IdealSheafData.ofIdeals`
  (no basic-open coherence required; see the `ofIdeals` pattern above). The bridge is now needed ONLY
  for the FORWARD characterization (the reverse `≥` inclusion identifying the annihilator with the
  module-annihilator on affine opens, `lem:qcoh_section_localization_basicOpen`). Build the bridge — with
  a blueprint decomposition first — before attempting that one lemma; the def + support predicates ship
  without it.
  **UPDATE (iter-024): the AFFINE engine is built (2 axiom-clean theorems); keystone gated on 2 named
  gaps.** `isLocalizedModule_tilde_restrict` + `isLocalizedModule_restrict_of_isIso_fromTildeΓ` (see the
  tilde-localization affine-engine pattern above) close the basic-open localization for `tilde`/essImage
  sheaves — the latter takes `[IsIso M.fromTildeΓ]` as hypothesis. The general keystone
  `Scheme.Modules.isLocalizedModule_basicOpen` (general `X`, arbitrary QC `F`) is gated on: **gap1** =
  `IsQuasicoherent M → IsIso M.fromTildeΓ` (the QCoh(Spec R) ≃ Mod R identification — descent-level;
  Mathlib has only `isIso_fromTildeΓ_iff` (essImage) + `isIso_fromTildeΓ_of_presentation` (global
  Presentation); the Tilde source comment confirms QCoh=essImage is unbuilt at the pin) — **this is the
  bottleneck; closing it makes the affine-QC case immediate via the iter-024 engine**; and **gap2** = the
  affine transport `U ↦ Spec Γ(X,U)` reconciling the project's `Ab`-valued `Γ(F,U)` with the
  `ModuleCat R`-valued tilde world (modules analogue of `AffineScheme.isLocalization_basicOpen`). No
  affine shortcut past gap1 exists (confirmed iter-024). Blueprint gap1 (the real math) + gap2 BEFORE any
  keystone prover. The same keystone gates GF-geo G1 (`gf_qcoh_fintype_finite_sections`).
  **UPDATE (iter-026): gap1 reduced to G1-core, and the ENTIRE downstream glue `G1-core ⟹ gap1 ⟹
  keystone` is now BUILT axiom-clean in QuotScheme.lean — only G1-core itself remains.** A mathlib-analogist
  study collapsed gap1 to **G1-core** = `isLocalizedModule_basicOpen_of_isQuasicoherent` (QC `M` on
  `Spec R` ⟹ `Γ(M,⊤)→Γ(M,D(f))` is `IsLocalizedModule (powers f)`, Stacks 01HA), the single irreducible
  Mathlib-absent fact (`IsQuasicoherent`/`fromTildeΓ` connect to nothing outside Tilde/Quasicoherent;
  Route A — global `Presentation` — is strictly harder). The prover then closed the glue:
  `isIso_fromTildeΓ_of_isLocalizedModule_restrict` (= gap1's body, but with the explicit hypothesis
  `H : ∀ f, restriction localizes` in place of `IsQuasicoherent`),
  `isIso_fromTildeΓ_iff_isLocalizedModule_restrict`, + 2 private helpers (see the iter-026 G1-assemble glue
  pattern above). So once G1-core lands, gap1 + the general keystone fall out immediately.
  **G1-core is a multi-session descent**, decomposed by the prover: (1) `quasicoherentFiniteBasicCover`
  (finite basic-open presentation cover from `QuasicoherentData` — heaviest unknown, needs the
  `Scheme.Modules` site/`over` API, full-session step); (2) `localTilde`; (3) `flatEqualizerLocalize`
  (flat-localization of the finite sheaf-equalizer — the substantive content); (4) wrap as
  `IsLocalizedModule`. **Do NOT re-dispatch G1-core as a one-shot.** ⚠ Do NOT re-point
  `lem:qcoh_affine_isIso_fromTildeΓ`'s `\lean{}` to the new reduction (lvb-quot iter-026: signatures
  differ — gap1 takes `IsQuasicoherent`, the reduction takes explicit `H`).
  **UPDATE (iter-029): the topological finite-cover front of G1-core is LANDED axiom-clean; gap1's
  remaining wall is precisely the per-element presentation TRANSPORT, which has zero Mathlib support.**
  `exists_finite_basicOpen_cover_le_quasicoherentData` (QuotScheme.lean:730) is proved (the `quasicoherentFiniteBasicCover`
  step (1) above): from `q : M.QuasicoherentData`, a finite `t : Finset R` with `Ideal.span t = ⊤` and each
  `D(r) ≤ q.X i` (via `q.coversTop` + `Sieve.mem_ofObjects_iff` + `isBasis_basic_opens` +
  `Ideal.span_eq_top_iff_finite` — see the new Proof Pattern). **The wall:** turning
  `q.presentation i : (M.over (q.X i)).Presentation` into a presentation of `M|_{D(r)} : (Spec R_r).Modules`
  needs a scheme-level modules restriction-to-basic-open functor + `over`↔scheme-pullback identification +
  presentation transport — NONE exist (`AlgebraicGeometry/Modules/` = only `Presheaf/Sheaf/Tilde`). Aggravation:
  even STATING `q.presentation i` triggers a synthInstance heartbeat **timeout** (20000) on the slice
  `(sheafToPresheaf (J.over (q.X i)) _).IsRightAdjoint` (probed live). Three routes (cover-transport, stalk,
  section-MV) all funnel through this transport. **Do NOT re-dispatch gap1 directly — build
  `restrictModulesToBasicOpen : (Spec R).Modules ⥤ (Spec R_r).Modules` + Presentation-transport first**
  (recommend a mathlib-analogist consult on any over↔pullback bridge, then an effort-breaker). With the
  transport, per-`r` localization follows from `isLocalizedModule_basicOpen_of_presentation` and this cover
  lemma closes the Mayer–Vietoris loop. (Memory: `quot-quasicoherentdata-slice-transport-wall`.)
  **UPDATE (iter-031): bridge C — the slice→geometric restriction iso — is CLOSED axiom-clean
  (`overRestrictIso`); the transport wall is now P1, no longer C.** The hardest piece of the transport
  (`M.over U ≅ (restrictFunctor U.ι).obj M`, equivalently `≅ U.ι^* M` via `overRestrictPullbackIso`)
  landed: the feared step-2 geometric ring-sheaf identification collapsed to `rfl`, and the synthInstance
  timeout fear did NOT materialise for C (`backward.isDefEq.respectTransparency false` not needed). See the
  Proof Pattern "Slice→geometric restriction iso `overRestrictIso`" above. **Remaining for gap1 = P1**
  (per-element presentation transport, now UNBLOCKED): take `q.presentation i`, push through
  `(overRestrictEquiv (q.X i)).functor` via `SheafOfModules.Presentation.map … (.refl _)`, then `.ofIsIso
  (overRestrictPullbackIso …).hom`, restrict along `D(r) ≅ Spec R_r`, conclude
  `isIso_fromTildeΓ_of_presentation` — THEN the cover lemma closes Mayer–Vietoris. Reassess the
  `respectTransparency` incantation only if P1's `Presentation.map` slice synthesis times out.
  **UPDATE (iter-035): P1 done (iter-034) and gap1-D landed axiom-clean in COVER form
  (`isLocalizedModule_basicOpen_descent_of_cover` — see Proof Patterns) — but the NAMED gap1 keystone
  `isLocalizedModule_basicOpen_descent` (quasi-coherent `M`) is STILL gated, now on producing the cover
  form's `Hfr` per-cover-element data.** The remaining wall is the **slice→`Spec R_r` SECTION transport**:
  `Γ((pullback (Opens.ι (q.X i))).obj M, ⊤) ≅ Γ(M, q.X i)` intertwining the restriction maps — the
  section-level analogue of P1's object-level transport, same Mathlib-absent `Scheme.Modules.pullback`-along-
  open-immersion vs presheaf-restriction comparison. Once that lands, `Hfr` follows (chain through P1's two
  pullbacks + `isLocalizedModule_restrict_of_isIso_fromTildeΓ`) and BOTH the named descent and gap1
  (`isIso_fromTildeΓ_of_isQuasicoherent`) close in two one-liners. Needs a dedicated lane (refactor/dag-walker).
  Dead-end (do NOT retry): `bijective_of_isLocalized_span` is no shortcut — it symmetrically demands
  `Away r`-localizations of the TARGET `Γ(M,D(f))`, which are unavailable.
  **UPDATE (iter-041): gap1 CLOSED axiom-clean — this entire blocker is RESOLVED.** The section-transport
  producer chain landed: `image_basicOpen_of_affine` / `compositeBasicOpenImmersion_image_basicOpen` /
  `image_basicOpen_eq_inf` (geometry) → `section_localization_hfr_aux` (heavy opaque-`j` core) →
  `section_localization_hfr_basicOpen` (TOP) → `isLocalizedModule_basicOpen_descent` (keystone) →
  `isIso_fromTildeΓ_of_isQuasicoherent` (gap1). All `{propext, Classical.choice, Quot.sound}`. The
  load-bearing fix was keeping the affine immersion OPAQUE (see the opaque-immersion proof pattern below);
  the analogist `quot-sigma-rebasing` re-basing defeqs were all confirmed `rfl` (definitional). gap1 now
  unblocks G1-core / GF-G1 / the annihilator forward direction.
- **No tensor/monoidal structure on `SheafOfModules` at the pin (iter-007).**
  `MonoidalCategoryStruct X.Modules` fails to synthesize; no SheafOfModules/PresheafOfModules tensor
  lemmas exist. So tensor powers `L^{⊗m}` cannot be named — blocks `sectionGradedRing`
  (`⊕_{m≥0} Γ(X_s, L_s^{⊗m})`). A deep infra prerequisite (tensor product of sheaves of modules +
  lax-monoidal global sections); do NOT define `L^{⊗m}` ad hoc.
- **Graded-submodule decomposition: state the INDEPENDENCE and SUPREMUM halves separately
  (iter-015).** For an internally graded `M = ⨁ ℳ i` and homogeneous `p`, the two
  axiom-clean facts that go through are `homogeneousSubmodule_inf_iSupIndep`
  (`iSupIndep fun i => ℳ i ⊓ p`, via `iSupIndep.mono`) and `homogeneousSubmodule_iSup_inf_eq`
  (`⨆ i, ℳ i ⊓ p = p`, via `DirectSum.sum_support_decompose` + `IsHomogeneous.mem_iff`).
  Bundling them into `DirectSum.IsInternal (fun i => (ℳ i).comap p.subtype)` or a
  `DirectSum.Decomposition` DOES NOT elaborate — see the matching Known Blocker.
- **Cold-build vs warm-LSP heartbeat gap (iter-015, FlatteningStratification).** A goal can
  elaborate clean under the warm LSP / `lean_diagnostic_messages` yet trip
  `(deterministic) timeout at whnf/isDefEq` on a cold `lake env lean <file>` (seen at
  `algRB2 := ρ.toAlgebra` ~L1146). `lake build <module>` is the authoritative green check
  (it succeeded); trust it over `lake env lean`. Bumping `maxHeartbeats` higher did NOT help
  and shifted the failure — the cost is instance-search depth over doubly-indexed
  `MvPolynomial (Fin (m+1)) (Localization.Away g)`, not raw budget.

- **Polynomial-module over commuting endomorphisms — the Route-2 carrier encoding (iter-018, QUOT).**
  To make a graded `κ`-module `M` a module over the FREE poly ring `MvPolynomial (Fin r) κ` with `X i`
  acting as a commuting endo `t i`: `polyEndHom := (adjoin κ (range t)).val.toRingHom.comp (aeval …)`
  factored through `Algebra.adjoin κ (range t)` (commutative via `Algebra.isMulCommutative_adjoin` +
  an EXPLICIT `letI : CommRing _ := IsMulCommutative.instCommRing` — synthesis will NOT climb
  `CommRing→CommSemiring` from bare `IsMulCommutative` for `aeval`'s target); then
  `polyModule := Module.compHom M polyEndHom`; lift a `t`-stable `κ`-submodule `N` to a `κ[t]`-submodule
  with the SAME ambient carrier via `polySubmodule` (`smul_mem'` by `MvPolynomial.induction_on`). State
  finiteness as `Module.Finite (MvPolynomial (Fin r) κ)` over a quotient of two ambient `polySubmodule`s
  — this AVOIDS the graded subtype/quotient `isDefEq` pathology entirely (no runaway fired). Keep the
  poly ring FREE, never `adjoin κ {x_0..x_{r-1}}` (relations break the `Fin(r+1)↠Fin r` ring surjection
  the finiteness induction needs). Leave `polyModule` un-`@[reducible]` (always supply via `letI`).
- **`Module.End` multiplication is application (iter-018).** `(x * t) m = x (t m)` is DEFEQ; there is NO
  `LinearMap.mul_apply` (unknown constant — do not retry). For a commuting pair, `x (t m) = t (x m)` is
  just `LinearMap.congr_fun hcomm.eq m` (no `simpa [mul_apply]`). `MvPolynomial.induction_on` case names
  are `C` / `add` / `mul_X` (NOT `h_C` / `h_add` / `h_X`).
- **Generic flatness L4 foundation steps (iter-018, GF, all `g`-independent and proved).** `A ↪ B` from
  `B_K = K⊗_A B` nontrivial (nonzero `a` acts as 0 on pure tensors via `← TensorProduct.tmul_smul,
  Algebra.smul_def` yet invertibly through the field unit → subsingleton); `B_K` is a localisation of
  `B` via `IsLocalization.tensorRight` after `letI : Algebra B B_K := Algebra.TensorProduct.rightAlgebra`
  (then scalar towers `inferInstance`); common denominator via `IsLocalization.exist_integer_multiples`;
  `Algebra.IsIntegral K[X] B_K` from module-finiteness (`Algebra.IsIntegral.of_finite`); generator
  algebraic-independence via `algebraicIndependent_iff_injective_aeval` + `MvPolynomial.algHom_ext`.
  `gK.Finite` (`AlgHom.Finite`) is defeq-usable as `Module.Finite K[X] B_K` once `letI := gK.toAlgebra`.
  Note: `example` snippets in `lean_multi_attempt` DROP the ambient section variables — test with bare
  `have`/`let` blocks instead.

- **Term-mode escape from a spurious `X.Modules` instance diamond (iter-019, FBC step-iii sub-lemmas).**
  Under single-file/LSP elaboration a spurious `X.Modules` instance diamond makes **tactic-mode**
  `rw [Category.assoc]`, `rw/simp [Functor.map_comp]`, `rw [Iso.inv_hom_id_app]`, and even `rw [hI]` with
  a freshly-elaborated identical `hI` all FAIL to match ("simp made no progress" / "did not find an
  occurrence of the pattern") despite a literally-present subterm. The **same** steps succeed in **term
  mode** (`congrArg`, `.trans`, `Category.assoc`/`F.map_comp` as terms, `exact`) because elaboration
  unifies the instances up to defeq. Closed `base_change_mate_fstar_reindex_legs_unitExpand` (cancel the
  trailing `(a≫b)_*(pullbackComp.inv ≫ pullbackComp.hom) = 𝟙` via `(congrArg (η ≫ ·) hI).trans
  (Category.comp_id _)` + `Category.assoc` term) and `_gammaDistribute` (distribute a general functor `F`
  over a 4-factor composite via three threaded `(F.map_comp _ _).trans (congrArg …)`). Prefer term-mode
  combinators over `rw`/`simp` for any composition/functoriality/iso-cancellation step on `X.Modules`.
- **σ-semilinear `Module.Finite` transfer on DEFEQ quotient carriers (iter-019, QUOT keystone
  `subquotient_finite_transfer` — the 3-iter blocker RESOLVED, axiom-clean).** To transfer
  `Module.Finite (MvPolynomial (Fin (r+1)) κ) (P/P')` down to `MvPolynomial (Fin r) κ` when the last endo
  `t (Fin.last r)` annihilates the subquotient: the two quotient carriers `↥(polySubmodule t …)⧸…` and
  `↥(polySubmodule (t∘castSucc) …)⧸…` are **defeq** (same underlying κ-submodule), so the transfer map is
  the IDENTITY on elements, σ-semilinear along `lastVarAlgHom` (`X last ↦ 0`, `X castSucc i ↦ X i`). Build
  it via `Submodule.liftQ` whose `map_smul'` delegates to the induction lemma `polyEndHom_lastVar_sub_mem`
  (proved by `MvPolynomial.induction_on`: X_last case → `P'` by annihilation, X_castSucc case = IH), then
  `Module.Finite.of_surjective`. Gotchas: `Submodule.Quotient.mk_eq_mk` does not exist (drop it);
  `change` (not `simp`/`show`) to expose the defeq `polyEndHom … - polyEndHom … (σ s) ∈ P'` membership.
- **`IsLocalization.lift` injectivity helper (iter-019, GF `isLocalization_lift_injective`).**
  `Function.Injective (IsLocalization.lift hg : S →+* P)` when `g : R →+* P` sends `M` to units and both
  `algebraMap R S` and `g` are injective: `rw [IsLocalization.lift_injective_iff]` — but the codomain MUST
  be annotated `(… : S →+* P)` or the `IsLocalization M ?m` instance is stuck on metavariables. Reusable;
  consumed twice in L4 for the comparison maps `ν : B_g→B_K` and `ψ : A_g→K`.
- **Finite basic-open cover from a `QuasicoherentData`/`CoversTop` cover (iter-029, QUOT
  `exists_finite_basicOpen_cover_le_quasicoherentData`, axiom-clean).** From a (possibly infinite) cover
  `q.X : q.I → (Spec R).Opens` with `q.coversTop`, extract a FINITE `t : Finset R` with `Ideal.span t = ⊤`
  and `∀ r ∈ t, ∃ i, D(r) ≤ q.X i`: set `G := {r | ∃ i, basicOpen r ≤ q.X i}`; prove `Ideal.span G = ⊤`
  via `← PrimeSpectrum.iSup_basicOpen_eq_top_iff'` + `eq_top_iff` + `Opens.mem_iSup`, covering each point by
  `q.coversTop ⊤ x trivial` → `Sieve.mem_ofObjects_iff` → `leOfHom` (extracts `U ≤ q.X i`) →
  `Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens` (refines to a basic open `D(r)` with
  `x ∈ D(r) ≤ q.X i`); finitize with `Ideal.span_eq_top_iff_finite`. Universe gotcha: a bundled
  `…_of_isQuasicoherent` corollary over `[M.IsQuasicoherent]` is friction — the existential's
  `QuasicoherentData` index universe is independent of the instance's auto-bound universe and
  `universe w in theorem` is a parse error mid-namespace; have callers do the 2-line
  `obtain ⟨q⟩ := h.nonempty_quasicoherentData` where universes unify.
- **`X.Modules` instance diamond is total against keyed rewriting (iter-029, FBC — sharpens the iter-019
  term-mode escape).** At the `_legs` cancellation crux, `rw`/`simp`/`erw`/`conv`/`set`/`dsimp` ALL fail —
  even on a `rfl`-true fact whose LHS is the goal's own pretty-printed factor, and even `rw [Category.comp_id]`
  on `?f ≫ 𝟙`. Every `≫`/`Functor.map` carries a category/comp instance defeq-but-not-reducibly-equal to a
  fresh elaboration, which `kabstract` cannot see through. The ONLY bridge is whole-term defeq:
  `exact`/`convert`/`change` on separately-elaborated CLEAN terms (single instance ⇒ no diamond), chained
  by `congrArg`/`Functor.congr_map`/`.trans`. (See the matching FBC Known Blocker for the full route.)
- **FBC `_legs` term-mode PFC collapse — the LAST advance before the direct-on-sections route is
  exhausted (iter-033).** The trailing transparent `pushforwardComp(g', Spec φ).hom` factor (whose `=𝟙`
  is `rfl`) DOES collapse to `𝟙` inside the locked `_legs` goal via a term-mode `congrArg` splice
  `refine (congrArg (fun z => … (z ≫ _) …) (gammaMap_pushforwardComp_hom_eq_id (e.hom ≫ Spec.map inclA)
  (Spec.map φ) _)).trans ?_` — re-confirming that whole-term `congrArg`/`exact` is the ONLY vehicle past
  the `X.Modules` diamond. BUT the residual after the collapse is **cross-layer naturality**, not
  adjacency bookkeeping: the F2 (`e.hom`-unit) and F3 (`pullbackComp(e,inclA)`) cancellers live in the
  `(Spec φ)_* ⋙ Γ_R` image (over `Spec R`) while their codomain-read partners live in the
  `Γ_R' → gammaPushforwardIso ψ → restrictScalars ψ` image (over `Spec R'`). Cancelling them needs the
  naturality of `gammaPushforwardIso ψ` as a `conjugateEquiv`/mate coherence (the Seam-1 device), which
  has NO term-mode expression in the explicit-factor route. This is the definitive proof the
  direct-on-sections vehicle is exhausted (see Known Blocker). Full handoff:
  `informal/base_change_mate_fstar_reindex_legs.md`.
- **`TensorProduct ℤ` of `MvPolynomial` rings: no `Semiring`/`Mul` via `inferInstance` (iter-033, GR).**
  `Semiring (TensorProduct ℤ (MvPolynomial _ ℤ) (MvPolynomial _ ℤ))` (and `Mul`/`Monoid`/`HPow`) is NOT
  synthesized by `inferInstance` or by a bare `→ₐ[ℤ]`/`Semiring (...)` type annotation on these rings.
  Fix for `diagonalRingMap := Algebra.TensorProduct.lift …`: DROP the explicit return-type annotation and
  let elaboration infer the `TensorProduct` algebra structure from the `lift`'s output; avoid writing
  arithmetic (`*`, `^`, `1`) directly on tensor elements with type ascriptions. (memory:
  `tensorproduct-mvpolynomial-semiring-inferinstance-miss`)
- **Slice→geometric `SheafOfModules.Presentation` transport (iter-033, QUOT gap1 P1 infra, axiom-clean).**
  `overRestrictEquiv U).functor` is *definitionally* a `SheafOfModules.pushforward` along the
  equivalence-of-sites inverse with the identity ring comparison, so the unit iso it needs
  (`F.obj (unit R) ≅ unit S`, `overRestrictUnitIso`) comes from the **`IsIso ψ`-driven** form
  `isIso_unitToPushforwardObjUnit_of_isIso'` with `ψ = 𝟙` — NOT the `PullbackFree` finality route (the
  finality hypothesis `(Opens.map g.base).Final` does not synthesize on the slice site). Then transport a
  slice presentation: `Presentation.map.{u} P (overRestrictEquiv U).functor (overRestrictUnitIso U)` then
  `Presentation.ofIsIso.{u} (overRestrictPullbackIso U M).hom …` (BOTH need the explicit `.{u}` or
  universe-mismatch). The per-element-over-`QuasicoherentData` form needs the mandatory elaboration triple
  `set_option maxHeartbeats 2000000 / synthInstance.maxHeartbeats 800000 /
  backward.isDefEq.respectTransparency false`, and ALL `set_option` lines must sit ABOVE the doc-comment
  (between docstring and `def` → `unexpected token 'set_option'`). (memory:
  `sheafofmodules-slice-presentation-transport-tricks`)
- **Sheaf-condition fork as a limit, packaged (iter-033, FBC-B).** For `M : X.Modules` and any cover
  `U : ι → X.Opens`, `Modules.gammaIsLimitSheafConditionFork M U : IsLimit
  (TopCat.Presheaf.SheafConditionEqualizerProducts.fork M.presheaf U)` =
  `((isSheaf_iff_isSheafEqualizerProducts M.presheaf).mp M.isSheaf U).some`. A finite affine cover with
  quasi-compact overlaps for a qcqs scheme: `(isCompact_iff_finite_and_eq_biUnion_affineOpens
  (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ (X := ↥X))` for the finite subcover, plus
  `quasiSeparatedSpace_iff_forall_affineOpens.mp ‹_›` for the overlaps. Gotchas: `open TopCat.Presheaf
  SheafConditionEqualizerProducts in` must precede the doc-comment (the `fork`/`piOpens` names are in that
  namespace); the `(lemma (U := …)).mp` form is needed (named-arg `Iff.mp` rejects `U`); dot-projection
  `M.gammaIsLimitSheafConditionFork` fails (it is `SheafOfModules.X.Modules` = `SheafOfModules` namespace)
  — spell `Modules.gammaIsLimitSheafConditionFork M`.
- **No-sorry invariant deletes half-done keystones (iter-033, GR + QUOT).** When a keystone's reduction
  skeleton compiles but leaves a single residual `sorry` for a multi-piece assembly, the prover (correctly,
  per the invariant) builds the sub-ingredients axiom-clean and then DELETES the sorry'd stub — so the
  keystone shows as "decl absent, 0 sorry" rather than "decl present, 1 sorry". Consequence for the
  reviewer/planner: judge these lanes by the infrastructure landed (e.g. GR `diagonalRingMap_surjective`
  + `pullbackιIso`; QUOT `presentationPullbackιOfQuasicoherentData`), NOT by the sorry delta, and read the
  task-result "remaining obligations / route (b)" for the true frontier.
- **Terminal `Spec ℤ` collapses separatedness-glue for `Scheme.{0}` (iter-034).** For a glued
  scheme `X : Scheme.{0}`, `Spec ℤ` is *genuinely terminal* (`AlgebraicGeometry.specZIsTerminal`), so
  the structure morphism `toSpecZ := specZIsTerminal.from X` and per-chart `ι ≫ toSpecZ = Spec.map
  (algebraMap ℤ R)` are pure `IsTerminal.hom_ext` — no `glueMorphisms`, no terminal-vs-`Spec ℤ`
  reconciliation. `IsSeparated X` then = `Scheme.isSeparated_iff` + (separated `toSpecZ`) + `Spec ℤ`
  affine. The morphism-form (`IsSeparated toSpecZ`) is a direct port of `AlgebraicGeometry.Proj.isSeparated`
  (`IsZariskiLocalAtTarget.of_openCover` → per-patch `pullbackDiagonalMapIdIso` →
  `IsClosedImmersion.spec_of_surjective` on the restricted-diagonal comorphism). Used for
  `Grassmannian.isSeparated`. **Porting gotchas:** `pullback.map_fst`/`map_snd` and `convert!` do NOT
  exist in this Mathlib (use `pullback.lift_fst`/`lift_snd` + `Category.comp_id`, and `convert … using 1`);
  leg lemmas need `erw` (goal carries defeq `openCover.f i` vs stated `ι i`); `← Spec.map_comp` bare
  `rw` fails on the Scheme-cat instance diamond over heavy localisation objects (route via `show`-rewrite
  then `exact (Spec.map_comp _ _).symm`). `maxHeartbeats 3200000` + `backward.isDefEq.respectTransparency false`.
- **Element-level sheaf axioms beat the categorical product bridge for H⁰ equalizers (iter-034).**
  To prove `Γ(M,⊤) ≃ₗ[A] eqLocus(leftRes, rightRes)` for a cover with `iSup U = ⊤`, get bijectivity
  from `TopCat.Sheaf.eq_of_locally_eq'` (injectivity) + `TopCat.Sheaf.existsUnique_gluing'`
  (surjectivity) on `⟨M.presheaf, M.isSheaf⟩` with `hcover := hU.ge` — NOT by matching `∏` in `Ab`
  with `Π`-types. Base ring `A := X.presheaf.obj (op ⊤)` (CommRingCat, so `CommRing`/`Algebra` resolve);
  `M.val`-side rings carry only `Ring` but their carriers are defeq through `restrictScalars`
  (load-bearing); `(M.val.map f).hom x = M.presheaf.map f x` by `rfl`. A-linear restriction maps via
  `ModuleCat.restrictScalarsComp'App` with explicit `gf := rhoU V` land directly in `gammaModA`
  (no `eqToHom`). Flat base change payoff = compose with `LinearMap.tensorEqLocusEquiv`
  (`Mathlib.RingTheory.Flat.Equalizer`). Used for `gammaTopEquivEqLocus`/`baseChangeGammaEquiv`.
- **`pullbackComp = leftAdjointCompIso` via `conjugateEquiv.injective` (iter-034).** The project
  pseudofunctor coherence `Scheme.Modules.pullbackComp f g` IS the abstract composite-adjunction iso
  `Adjunction.leftAdjointCompIso …` of `Mathlib.CategoryTheory.Adjunction.CompositionIso`: both invs
  have the same image `(pushforwardComp f g).hom` under `conjugateEquiv (adjg.comp adjf) adj(f≫g)`
  (`conjugateEquiv_pullbackComp_inv` + `conjugateEquiv_leftAdjointCompIso_inv`), so
  `conjugateEquiv.injective` gives the inv-level identity and `Iso.inv_eq_inv`/`Iso.ext` upgrades it.
  The pinned Mathlib has the full `CompositionIso` calculus (`leftAdjointCompIso` @72,
  `conjugateEquiv_leftAdjointCompIso_inv` @82, `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` @140).
  Step-(i) device of the FBC `_legs` conjugate re-encoding.
- **`SheafOfModules.pullback (φ.inv.toRingCatSheafHom)` vs `Scheme.Modules.pullback φ.inv` (iter-034).**
  Defeq, but the latter carries bundled `IsContinuous`/`IsRightAdjoint` instances that make `asIso`'s
  `IsIso` synthesis see a syntactically-different term and FAIL. State unit-iso lemmas
  (`pullbackSchemeIsoUnitIso`) with the `SheafOfModules.pullback` form; it coerces back downstream with
  no friction. The `Final` of `Opens.map φ.inv.base` must be a `haveI` from `opensMapEquivOfIso`
  (resolution cannot invert `φ.inv.base`). Used for QUOT P1's iso-transport (sidesteps the
  open-immersion `Functor.Final (Opens.map j.base)` do-not-retry wall).
- **extendScalars/algebraic-counit composite → bare module value (FBC step b, iter-036).** To prove
  `(extendScalars ψ).map f ≫ (extendRestrictScalarsAdj ψ).counit.app _ = g`, do `ext x` (reduce to the
  `1⊗ₜx` generator of the `R'`-linear span), then `simp only [ModuleCat.extendScalars,
  ModuleCat.extendRestrictScalarsAdj]` + `change (...counit.app _ _) = _` +
  `erw [ExtendRestrictScalarsAdj.counit_app]; rw [ExtendScalars.map']` +
  `erw [ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul]` — this collapses the LHS to the bare
  module value `f(x)`. A residual carrier equality (e.g. `f(x) = g.inv (1⊗ₜx)` where both sides are
  defeq) then closes by `exact congrArg _ rfl`. Landed `base_change_mate_extendScalars_inner_value_counit`
  axiom-clean.
- **`Functor.mapIso` over `asIso (φ.app U)` (QUOT iter-036).** When you have an iso `φ` of presheaves/
  sheaves and want its component-at-`U` as an iso of section objects, `asIso (φ.hom.app U)` can FAIL —
  Lean does not synthesize `IsIso (Hom.app φ U)` even with `haveI : IsIso φ` in scope (the Mathlib
  `[IsIso φ] → IsIso (φ.app U)` instance at `AlgebraicGeometry/Modules/Sheaf.lean:137` does not fire
  through `inferInstance`). Instead build the iso as `(sectionsFunctor).mapIso φ` where
  `sectionsFunctor = toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op U)` — this sidesteps
  instance synthesis entirely. Used for `gammaPullbackImageIso`.
- **`theGlueData` projection instances need explicit help (GR iter-036).** Both
  `IsOpenImmersion ((theGlueData d r).ι I)` (pass `@IsOpenImmersion.lift _ _ _ … hoi …` / `lift_fac`
  explicitly — local `haveI` does not fire) and `Finite (theGlueData d r).J` (supply
  `inferInstanceAs (Finite {I : Finset (Fin r) // I.card = d})` — the `.J` projection blocks
  `inferInstance`). Field `Spec K` is `Subsingleton`+`Nonempty` (inferInstance for a field), giving the
  range-condition + chart-point for E1.
- **gap2 Piece B eqToHom bridge (`isLocalizedModule_basicOpen_of_hP1`, QUOT iter-043).** To go from the
  gap2-core `section_localization_hfr_aux_general` (over `A = Γ(X, j ''ᵁ ⊤)`) to the consumer-facing
  `restrictBasicOpenₗ M f` (over `Γ(X, U)`): instantiate at `j = hU.fromSpec` (so `S = Γ(X,U)`), slice
  elt `f' = f`, image section `f_im := gammaImageRingEquiv j ⊤ ((ΓSpecIso Γ(X,U)).inv f)` (`hf'` = `rfl`);
  the section ring iso is `ρ := (asIso (X.presheaf.map (eqToHom eT.symm).op)).commRingCatIsoToRingEquiv`
  with `eT : j ''ᵁ ⊤ = U` (via `image_top_eq_opensRange ▸ opensRange_fromSpec`),
  `eB : j ''ᵁ D(f) = X.basicOpen f` (Mathlib `IsAffineOpen.fromSpec_image_basicOpen`); `ρ f_im = f` from
  the proven crux `fromSpec_image_top_section_coherence` then two `Iso.inv_hom_id_apply`; finish with
  `isLocalizedModule_of_ringEquiv_semilinear ρ … e₁ e₂` (`e₁/e₂ = M.presheaf.map (eqToHom _).op` as
  `addCommGroupIsoToAddEquiv`; `he₁/he₂` one `Scheme.Modules.map_smul` each; `hh` = `← map_comp ×2` +
  `congrArg (M.presheaf.map ·) (Subsingleton.elim …)` over thin `Opens` morphisms) + `Submonoid.map_powers`.
  **Two elaboration gotchas (both from iter-042 memory, confirmed):** `core` must be stated with the
  `show Γ(M,j''ᵁ⊤) →ₗ[Γ(X,j''ᵁ⊤)] Γ(M,j''ᵁD(f)) from restrictₗ M ii` wrapper AND a matching
  `letI : Module … := Module.compHom …` in scope (else codomain-module synth is stuck), and the SAME
  `show…from` expression must be passed as `g` to `isLocalizedModule_of_ringEquiv_semilinear` so
  `haveI := core` is found by keyed-matching (defeq alone is insufficient). Prefer `change` over `show`
  for the coherence steps (avoids an elaboration reorder). Needs `maxHeartbeats 1600000`.
- **Matrix-cocycle over a triple-overlap localization = take the `I`-minor of an `imageMatrix` cocycle
  (iter-061, GR; closed L1 `bundleTransition_cocycle_matrix` axiom-clean).** To prove the Cramer-inverse
  cocycle `(X^J_K)⁻¹ (X^I_J)⁻¹ = (X^I_K)⁻¹` over `S_I = Localization.Away (minorDet I J * minorDet I K)`,
  extract the `I`-columns minor of the image-matrix cocycle `cocycle_imageMatrix_eq`. Mechanics:
  (1) `Matrix.submatrix_map : (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f` — FORWARD direction
  turns `(map).submatrix` into `(submatrix).map` (using `←` is the common mistake). (2) `imageMatrix_submatrix_I`
  collapses the `I`-minor of an image matrix to the localized Cramer inverse. (3) The non-square product split
  `imageMatrix = (X_J_K)⁻¹ * X^J` won't `rw` (HMul pattern miss on the rectangular factor) — apply it as a
  term: `rw [imageMatrix]; exact mul_submatrix_col' _ _ _`. (4) `map_nonsing_inv' f A h : (A.map f)⁻¹ = A⁻¹.map f`
  (provable in 3 lines from `Matrix.map_mul` + `mul_nonsing_inv` + `inv_eq_right_inv`) pushes a ring-hom through
  a matrix inverse — Mathlib has NO `RingHom.map_nonsing_inv`/`mapMatrix_nonsing_inv`, build it locally.
- **L2 matrix-automorphism composition is a one-liner once `matrixEnd_comp` exists (iter-061, GR; closed
  `matrixToFreeIso_mul`).** `(matrixToFreeIso A …).hom ≫ (matrixToFreeIso B …).hom = matrixEnd (B * A)` proves by
  `rw [matrixToFreeIso_hom, matrixToFreeIso_hom, matrixEnd_comp]` — the column/component contravariance reverses
  the product order to `B * A`. The genuine remaining cocycle work (C2) is the iso-level transport, not this.
- **Cross-file private duplication: 7 GrassmannianCells matrix helpers are `private`, so L1 needed verbatim
  `… '`-suffixed ports into GrassmannianQuot (iter-061).** `cocycle_imageMatrix_eq'`, `imageMatrix_map_eq'`,
  `inv_mul_inv_mul_cancel'`, `isUnit_algebraMap_away_left'`, `map_map_eq_of_comp'`, `map_nonsing_inv'`,
  `mul_submatrix_col'`. No signature drift (known-good code). The clean fix is a visibility-only change: export
  the 7 Cells originals as non-private and delete the ports — see recommendations.

- **Bridge-free section-η associativity — closes `sectionMul_assoc_core` axiom-clean (iter-007, SNAP).**
  To prove `Γ(structural-iso)(iterated η-image of an elementary tensor) = iterated η-image`, do NOT route
  through the iso-level localized-associator bridge (that is a 100–200-line μ-match — see blocker below).
  Instead factor the single unit-naturality square into two reusable engine lemmas:
  `sheafification_map_unit_top f x : Γ(sheafification.map f)(η_P x) = η_Q(f_⊤ x)` (one-line `congrArg` of
  `(sheafificationAdjunction _).unit.naturality f`, `.symm`) + its `IsIso` inverse companion
  `sheafification_map_unit_top_inv` (by `rw [← sheafification_map_unit_top, ← val_app_top_comp,
  IsIso.hom_inv_id]; rfl`). Then `haveI` the segment isos via `isIso_sheafification_whiskerRight_unit`, peel
  the iso's segment definition with `simp only [<tensorObjAssoc>, Iso.trans_hom, val_app_top_comp,
  Iso.symm_hom, asIso_hom, asIso_inv, Functor.mapIso_hom]`, ride η through each segment with **`erw`** of the
  engine lemma, and close with `rfl`. CRITICAL: positional `rw` of the engine lemma FAILS ("Did not find an
  occurrence of the pattern") — the `IsIso` instance baked into the iso's segments is *syntactically* distinct
  from a freshly-synthesised one; only `erw`'s up-to-defeq matching bridges it. The final element identity is
  pure `rfl` (ModuleCat structural maps reduce on elementary tensors). This engine is section-level — it does
  NOT help the iso-level bridges.
- **Instance-threading fix for "failed to synthesize" inside a large `exact` (iter-007, SNAP
  `tensorBraiding_eq_localizedBraiding`).** When `letI mc := inferInstance` finds an instance but an inline
  `Foo (C := …)` inside a big `exact` term *re-synthesises* it and aborts (surfaced as `failed to synthesize
  instance … MonoidalCategory (modulesLocalizedMonoidal X)`, breaking cold `lake build` while the LSP
  error-recovers past it), thread the found instance explicitly: `@Foo … _ mc _ …`. Keep it **inline** — a
  `have h := …` binding makes `.hom` opaque so it stops reducing to `⊗ₘ` and downstream unification against
  the goal's `tensorHom` form fails. Fragile to Mathlib refactors of the instance path (auditor major).

- **`𝟭`-wrapper blocks μ-naturality rewrites — normalize with `simp only [Functor.id_obj]` FIRST (iter-009,
  SNAP, the 4 associator seam lemmas, axiom-clean).** `(sheafificationAdjunction (𝟙 …)).unit.app P` has
  domain printing as `(𝟭).obj P`; this `𝟭`-wrapper makes both `rw [Localization.Monoidal.μ_natural_left]`
  (pattern-not-found) and `Iso.eq_inv_comp` (type mismatch) fail. A leading `simp only
  [CategoryTheory.Functor.id_obj]` on the goal normalizes `𝟭.obj P → P` so `μ_natural_left` (resp.
  `_right`) fires; the residual `sheafification.map = L'.map` closes by `rfl` (default transparency).
  For the braiding-collapse seam, leave the seg-5 braiding object as `_` so Lean infers the exact
  `unit.app P` codomain — then `exact (braiding_naturality_right A (unit.app P)).symm` absorbs the
  `𝟭.obj P` vs `P` discrepancy up to defeq (explicit object → `exact` fails). Template:
  `rw [← map_comp, ← map_comp]; congr 1; … rw [← Category.assoc, Iso.comp_inv_eq]; exact hn.symm`.
- **`whiskerRightIso`/`whiskerLeftIso` fail instance synthesis in STATEMENT position on a
  `backward.isDefEq.respectTransparency false` monoidal instance — use `MonoidalCategoryStruct.*` (iter-009,
  SNAP `tensorObjAssoc_eq_localizedAssociator`).** `MonoidalCategory.whiskerRightIso (C :=
  modulesLocalizedMonoidal X)` needs the full `MonoidalCategory` instance, which won't synthesize in a
  lemma *statement*; restate the bridge as a `.hom` **commuting-square** (`Φ^L ; α^loc = α ; Φ^R`) using
  `MonoidalCategoryStruct.whiskerRight/.whiskerLeft/.associator` (need only `MonoidalCategoryStruct`,
  synthesizes fine). Square ⇔ iso-conjugation by `Iso.ext`; the square IS the blueprint's primary form.
- **`eqToHom`→symbolic-`cast` exposure to dodge a whnf kernel bomb (iter-012, FBC).** When a goal carries
  `ConcreteCategory.hom (eqToHom h) x` over a `ModuleCat` and a `change`/`rfl` defeq collapse is a verified
  kernel bomb (forces whnf of the structure-sheaf machinery), DON'T collapse it — turn it SYMBOLIC:
  `theorem moduleCat_eqToHom_concreteCategory_apply (h : M = N) (x) : ConcreteCategory.hom (eqToHom h) x =
  cast (congrArg (↑·) h) x := by subst h; rfl`. `rw [this]` replaces the eqToHom with a `cast` that no
  longer triggers whnf, isolating the genuine remaining content. Companion `:= rfl` "concreteApply" twins
  (`gammaPushforwardIso_hom_concreteApply`, `restrictScalars_map_concreteApply`,
  `restrictScalarsComp_inv_app_concreteApply`) let `simp` fire AFTER `ModuleCat.comp_apply` has rewritten
  application heads to `ConcreteCategory.hom`. LIMIT: these only fire on SYNTACTIC junctions
  (`restrictScalars.map`); they do NOT cross the value-`ModuleCat`/`X.Modules` object-junction diamond
  (motive-not-type-correct) — see the FBC foundation Known Blocker.
- **SNAP shared-prefix strip via double `congrArg` (iter-012).** To peel a shared composite prefix off both
  sides of a bridge equation before attacking the hard tail: `rw [tensorObjAssoc]; simp only [<unfold>];
  refine congrArg (fun t => _ ≫ t) ?_` (apply twice). Reduces `P ≫ tail_lhs = P ≫ tail_rhs` to
  `tail_lhs = tail_rhs`. Kernel-light (verified cold-build); used to isolate the μ-cancel residual in hK_rhs.
- **`set_option maxHeartbeats … in` is CONSUMED by a following `/-! … -/` section block (iter-011/012, FBC
  latent bug).** `set_option … in` scopes to the IMMEDIATELY-following command, and a `/-! … -/` section
  comment IS a command — so `set_option maxHeartbeats 4000000 in` then a `/-! Seam … -/` block applies the
  budget to the COMMENT, not the theorem after it (which runs at DEFAULT budget → silent timeout when its
  sorry is filled). A `/-- … -/` DOCSTRING is fine (it is part of the next decl). FIX: place the
  `set_option … in` immediately before the theorem, with no `/-! -/` block between. Live at
  FlatBaseChange.lean L1488 + L1523-1526 (on COMPILE-DEAD mate decls; bundle the fix with mate-excision).

### Known Blockers (do not retry without a structural change)

- **FBC ring-square glue `pullback_spec_tilde_iso_ring_square_mate_glue` = both glue sub-routes refuted; do NOT
  author another cocycle/probe variant.** Frontier at sorry=1 for 5 consecutive iters (iter-022→026). (1) The
  carrier-BEARING functor-level `≪≫`-glue (`ring_square_glue_natTrans` telescope) is over-budget at statement +
  fold (iter-024 STUCK). (2) The carrier-FREE abstract cocycle + single-`exact` fold whnf-bombs at the fold seam
  (iter-026, FlatBaseChange.lean:2235, 200k hb) — the `exact`-binds-to-metavars premise is false, unification still
  whnf's the goal side. The ONLY remaining routes are STRUCTURAL: (i) re-shape the glue conclusion so all four legs
  are SYNTACTICALLY one cocycle instance (kill the defeq-not-syntactic `_.symm` mismatch), or (ii) abandon the
  iso/functor-level glue and prove the ring-square naturality pointwise on a sheaf-free carrier. Both large → user
  escalation / strategy consult before committing. NOTE: iter-026 left the temporary `ring_square_cocycle_probe`
  + `exact` fold IN the file → build RED; iter-027 must revert (delete probe @L2017, glue body → plain `sorry`).
- **SNAP monolithic Option-A `⊗_loc` re-base = 4–5-iter FAILED MECHANISM (iter-022→025; do NOT re-attempt
  as one batch).** Re-basing `tensorObj`/unitor/braiding/associator onto `MonoidalCategory.tensorObj
  (C := modulesLocalizedMonoidal X)` (to make bridges `rfl` + delete the associator wall) is the correct
  DESIGN, but the refactor lane cannot land it in one dispatch: iter-022 timed out (0 edits), iter-023
  false-greened via `private`, iter-024 was build-fix-only, iter-025 timed out leaving a HALF-MIGRATED
  consumer that broke the cold build (~25 errors: object/unitor defs partly re-based but consumers still
  call the OLD hand-built API, e.g. `tensorObjAssoc_hK_lhs_head` unknown). NEXT TIME: either per-def
  cold-build-gated micro-refactors (ONE def/lane, mandatory CONSUMER cold-build after each, back up the
  green file first — no git net) OR user escalation. NEVER a multi-def monolithic batch.

- **No git safety net (single untracked `504eef1 first commit`).** A refactor that overwrites a green
  `.lean` loses it permanently if no manual `.backup` exists (iter-025 lost the iter-024 green split
  consumer). ANY structural lane MUST copy the current green file to `<file>.<slug>-backup` BEFORE editing.

- **FBC b2-glue functor-level `≪≫`-chain natTrans route is OVER-BUDGET AT BOTH ENDS (iter-024, decisive
  STUCK; do NOT retry the same phrasing).** The plan made the geometric leg syntactic (re-based
  `chartBaseChangeGeometricComparison` on `(chartBaseChangeGeometricComparisonNat ψ φ ρ).app (tilde M)`,
  defeq — see Proof Patterns), removing 1 of 4 `.obj (tilde M)` crossings. The remaining four-leg telescope
  `ring_square_glue_natTrans` then fails TWICE: (1) its **STATEMENT** does not elaborate within 200000 hb —
  `(deterministic) timeout at isDefEq`(metavar)/`whnf`(pinned) at the
  `Functor.isoWhiskerRight (chartBaseChangeModuleReassocNat ψ φ ρ) (tilde.functor …)` seam (matching the
  alg-reassoc nat-iso codomain `ModuleCat (extendScalars …)` against `tilde.functor`'s source whnf's the
  extendScalars/ModuleCat diamond); confirmed elaborable only at `maxHeartbeats 800000` (forbidden) ⇒
  over-budget, not ill-typed; preserved as a `/- … -/` comment (FlatBaseChange.lean L1911–1970), NOT a typed
  sorry. (2) The **FOLD** `rw [chartBaseChangeModuleReassoc_eq_natApp …]; exact congrArg (Iso.app · M)
  (ring_square_glue_natTrans …)` → `(deterministic) timeout at whnf` @200000hb at the closing `exact`: the
  three NON-geom `pullbackSpecTildeNatIso` legs each cross `pullback (Spec _).obj (tilde M)` sheafification
  in the `.app M` distribution. RESOLUTION (iter-025, STRUCTURAL, not a helper round): EITHER give the three
  non-geom legs the same syntactic-`.app M`-by-construction re-base the geom leg got, OR assemble the glue iso
  as one closed (component-free) term so no `.obj (tilde M)` defeq is forced + a statement phrasing that does
  not whnf the extendScalars/ModuleCat diamond at the `tilde.functor` whisker. The 5/6 scaffold + geom re-base
  + `pullbackSpecTildeNatIso`/`_app` + `chartBaseChangeModuleReassoc_eq_natApp` are READY for either route.
  Candidate for a `mathlib-analogist` cross-domain consult ("fold a composite-functor nat-iso to a component
  without whnf'ing a sheafification carrier").

- **File-split refactor that cold-builds only the EXTRACTED module is a FALSE GREEN (iter-023, SNAP
  regression).** The Option-A/file-split lane moved the localized-monoidal infra out of `SectionGradedRing.lean`
  into `SectionGradedRingLocalized.lean` and verified `lake build …SectionGradedRingLocalized` (green, 2441
  jobs) — but NEVER built the consumer `…SectionGradedRing`, which then failed with 30+ `Unknown identifier`
  errors (+2 cascading kernel timeouts). ROOT CAUSE: the extracted decls (`MonoidalPresheaf`,
  `sheafificationCounitIso`, `laxMonoidal_μ_eq`, `oplaxMonoidal_δ_eq`, `Wsheaf`, …) were left **`private`**.
  Lean-4 `private` is FILE-SCOPED — it does NOT survive `import` (the importer sees a mangled name). RULE:
  (1) cross-file-referenced decls must be public; (2) any extraction/split refactor MUST cold-build the
  DOWNSTREAM CONSUMER as its self-check, not just the extracted module (this is the iter-018 mis-cert trap one
  level up). FIX = de-private the 5 consumer-referenced decls + build the consumer, OR revert to
  `SectionGradedRing.lean.presplit-backup` (= iter-021 green). NOTE: the split did NOT advance the associator
  wall (`tensorObjAssoc_hK_lhs_native` L1082 still `sorry`) — Option A as designed (re-base onto ⊗_loc, delete
  the wall) was NOT performed.

- **SNAP `tensorObjAssoc_hK_lhs_native` FINAL STEP — head-lemma application over the full-`tail` goal
  isDefEq-BOMBS (iter-018, 200k hb; the SUCCESSOR to the now-DOWN iter-017 reassoc wall).** The iter-017
  reassoc wall is RESOLVED by the statement-pin (see Proof Patterns: `native` drives the whole reassoc →
  associator-expand → whisker-merge → μ-cancel chain bomb-free, cold-build GREEN). What remains: the reduced
  goal is `μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom ≫ tail = assocCommonForm`, whose head
  3-factor prefix is VERBATIM the proven `tensorObjAssoc_hK_lhs_head`. EVERY way of applying the head lemma
  (`rw`/`erw [...]`/`rw [reassoc_of% hhead]`/`have h2 := reassoc_of% hhead; rw [h2]`/`refine (h2 _).trans ?_`/
  `simp only [h2]`/`conv_lhs => rw [h2]`/`conv_rhs => rw [assocCommonForm]; simp; rw [← hhead]`) hits the
  `(kernel/isDefEq/whnf) deterministic timeout` because the goal STILL CARRIES the full `tail` → unifying the
  head-lemma composite re-checks the `LocalizedMonoidal`↔`modulesLocalizedMonoidal X` comp-instance over heavy
  `Localization.Monoidal.μ` (→ `Localization.fac` whnf). The head lemma itself overcame the analogue on a
  SMALLER goal (`show`-uniform recast); here the full `tail` makes any full-goal op bomb. `hK_lhs`'s
  `simp only [tensorObj]; exact tensorObjAssoc_hK_lhs_native` connection bombs IDENTICALLY. **iter-019: the
  iter-018 suffix-peel FIX is now itself a CONFIRMED DEAD END.** `cancel_mono` does NOT strip the tail — it
  **bombs at the rewrite** (matching `?g ≫ ?f = ?h ≫ ?f` forces an assoc-reconciliation isDefEq over the
  heavy right-associated goal → whnf-unfolds μ). ALL FOUR bridge routes cold-build-verified to bomb: folded
  `_head_assoc A B C _` (whnf), image-form `_head_img_assoc A B C _` (isDefEq — the `simp[toMonoidalCategory]`
  whiskerRight-instance spelling diverges from the `(C := modulesLocalizedMonoidal X)` synonym), `have key :=
  head; simp only […] at key; exact reassoc_of% key` (the `simp at key` bombs — `key` carries the composite-
  object `c_{A⊗B} ≫ μ.inv` the post-native goal no longer has), and `cancel_mono`. Root cause = the dual-
  `MonoidalCategory`-instance μ-token-divergence. **RESOLUTION = iter-020 REFACTOR PIVOT (glue Option A: rewire
  the hand-built `tensorObj*` defs onto the `LocalizedMonoidal` synonym ⊗ so the comp-instance boundary — the
  SOLE source of the spelling divergence — disappears and the bridges become definitional). NOT another prover
  round; NOT dual-instance deletion (refuted load-bearing, 51-site cascade).** `tensorObjAssoc_hK_lhs_head_img`
  (image-form head, `@[reassoc]`, sorry-free) is staged for the pivot. **iter-020 (≈9th iter, 0 elim; refactor
  pivot was PLANNED but a PROVER was dispatched again — re-confirmed exhaustion): 3 MORE routes cold/LSP-dead,
  pinning the SOLE mechanism. (1) `congr 1` splits prefix/tail and LSP closes it, but cold build whnf-bombs at
  the decl head (`rfl` re-incurs the divergence). (2) Dropping `toMonoidalCategory` from the merge `simp only`
  (to keep the goal `▷` folded-synonym, matching head_img) — `toMonoidalCategory` is LOAD-BEARING: the
  `erw [← whiskerRight_comp_assoc]` merge + μ-cancel then break. (3) `simp [<native set>] at h` to match the
  head equation's `▷` spelling to the goal's — the `simp … at h` ITSELF whnf-bombs. **MECHANISM (definitive):
  the goal's divergent `toMonoidalCategory`-unfolded `▷` is an ARTEFACT of the PRODUCTIVE native-chain simp
  redexes (`μ.hom⊗1→▷` / `1⊗μ.inv→◁` from `associator_hom_app`) which simp rewrites WITHOUT whnf'ing deep μ;
  head_img has no such redexes, so any `toMonoidalCategory` unfold on it goes structural over μ → bomb. The
  divergent spelling is therefore producible ONLY via the productive native chain and NEVER reproducible on the
  head equation in isolation → NEITHER side is matchable without a μ-unfold. No tactic route survives; only the
  refactor.** iter-021 MUST dispatch the `refactor` subagent, NOT a prover. **iter-021 (≈10th iter, 0 elim;
  a prover was dispatched AGAIN for the net-progress fallback — see below — but ALSO re-probed the wall):
  the most-surgical remaining route is cold-build DEAD — an ISOLATED local `change` of JUST the single
  `c_{A⊗B} ▷ L'C♭` whisker to the `(C := modulesLocalizedMonoidal X)` synonym instance (no μ syntactically
  inside it) times out at `isDefEq` (200000 hb) ALL BY ITSELF. So reconciling the two `whiskerRight`
  INSTANCES is the irreducible bomb, INDEPENDENT of any heavy tail (`toMonoidalCategory`'s `whiskerRight`
  field is the localization lift → comparing it to the synonym whnf's the localized μ). iter-022 = REFACTOR
  PIVOT, no exceptions.**
- **FBC iterated-mate glue — TwoSquare vcomp lemmas BOMB over the whole combined goal (iter-019).** The glue
  `pullback_spec_tilde_iso_ring_square_mate_glue` stages cleanly into uniform conjugate form (via the new `rfl`
  bridges `pullback_spec_tilde_iso_{inv,hom}_conjugateEquiv`: `apply Iso.ext; rw [← Iso.inv_eq_inv]; simp only
  [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, …both bridges]` → all 4 `pst` legs uniform). But applying
  `iterated_mateEquiv_conjugateEquiv(_symm)` / `{conjugateEquiv,mateEquiv}_conjugateEquiv_vcomp` (all REAL,
  Mates.lean L450-485) over the COMBINED 4-leg goal forces the composite-adjunction unit to whnf → 200k-hb
  kernel bomb. FIX: telescope PER-FACTOR via `← conjugateEquiv_comp` splits with explicit midpoint adjunctions
  (mirror the iter-018 closed legs), substitute the 2 closed mate legs, close residual on `gammaPushforwardNatIso_comp`.
  **iter-020: also confirmed the one-shot leg→Nat staging bridges KERNEL-BOMB.** Exposing the closed mate legs
  via `hg : chartBaseChangeGeometricComparison .. = (…Nat).app (tilde M) := by apply Iso.ext; rfl` + `hr := rfl`
  + `rw [hg, hr]` ELABORATES in the REPL (and both mate facts `have`-elaborate) but cold `lake build` →
  `1757:8 (kernel) deterministic timeout`: `hg`'s `.hom`-`rfl` term forces the `tilde M`/pullback `X.Modules`-
  junction whnf at kernel-check (LSP hides it). The bridges are real-in-elaborator, NOT kernel-safe. The genuine
  remaining work is the multi-hundred-step NAT-TRANS-level telescoping (never force `.app (tilde M)`; lift each
  factor to `whiskerLeft`/`whiskerRight`, `suffices` a NatTrans eq over the two composite functors, drive by
  closed coherences) — a DEDICATED lane (+ effort-breaker), not a one-shot prover round. `lean_goal` times out
  on this theorem; use `lean_multi_attempt` (line-based) to drive it; cold-build EVERY candidate.
  **iter-021 SHARPENING (kernel-verified, supersedes the iter-020 framing): the GEOMETRIC `.app (tilde M)`
  Nat-bridge is kernel-unsafe by ANY tactic** (`simp only […NatIso.trans_app, Iso.app_hom/inv, eqToHom_app];
  congr 1` / `rfl` / `rw`) — the LSP shows a single proof-irrelevance residual (`pullbackCongr P₁ =
  pullbackCongr P₂`, `goals_after=[]`) but cold `lake build` `(kernel) deterministic timeout`s regardless of
  the close tactic, because the residual morphism types are `tilde M`-EVALUATED (`(pullback (Spec _)).obj
  (tilde M)`) → the kernel must whnf the heavy `pullback ∘ tilde` sheafification. It **bombs even with `M` a
  FREE VARIABLE**, so the "prove generically at variable `N`, instantiate at `tilde M`" escape is REFUTED.
  Only carriers WITHOUT sheafification (`ModuleCat.extendScalars` — the ALGEBRAIC leg) admit the structural
  bridge: `chartBaseChangeModuleReassoc_eq_natApp` (NEW iter-021, KEPT, kernel-safe, axiom-clean) is the
  algebraic half. A direct `exact <closed-lemma> ψ φ ρ M` over a `.obj (tilde M)` type IS kernel-light — only
  `simp`/`congr`/`rw`/`rfl` defeq-CHECKS at that type bomb → the assembly must be PURE TERM-MODE / nat-level
  with a SINGLE final `.app M` `exact`, never an intermediate `.app (tilde M)` rewrite.
  **iter-022: the 6-lemma scaffold is the agreed churn-breaker; 3/6 CLOSED cold-green (the 2 whisker-app
  folds + the linchpin `ring_square_glue_pst_iterated_mate` via `iterated_mateEquiv_conjugateEquiv` — see
  Proof Patterns).** The glue `sorry` is now gated SOLELY on `ring_square_glue_natTrans` — the four-leg
  nat-trans telescope, which SUBSUMES `geom_leg_nat`/`alg_leg_nat` (these are NOT independent facts; their
  standalone types are underdetermined until the telescope's two composite functors are pinned — do NOT stub
  them with guessed types). Route (all ingredients verified REAL): recognise the 4 `pst` legs via
  `pst_iterated_mate` (+`_symm`), telescope `(conjugateEquiv …).symm (gammaPushforwardNatIso …)` with
  `conjugateEquiv_symm_comp`, discharge geom leg via `chartBaseChangeGeometricComparison_mate` + alg leg via
  `chartBaseChangeModuleReassoc_extendScalarsComp` (paste with `{conjugateEquiv,mateEquiv}_…_vcomp`), close
  residual on `gammaPushforwardNatIso_comp`; then glue = fold the 2 whisker lifts + evaluate at `M`.
  Multi-hundred-step → effort-break `ring_square_glue_natTrans` FIRST, then a dedicated prover lane. Cold-build
  every candidate (`lean_goal` times out; use `lean_multi_attempt`).
- **SNAP Option-A refactor TIMES OUT — the refactor subagent cannot land the 3341-line re-base in one
  dispatch (iter-022, 3rd consecutive timeout).** Option A (re-base `tensorObj*` onto Mathlib `⊗_loc` so the
  `hK_lhs` associator bridge becomes `rfl`) was dispatched THREE times: `snap-optiona`/`snap-optionA`
  (from-scratch full-file rewrites) + `snap-optiona-r3` (explicit SURGICAL in-place edits). ALL timed out;
  r3 made 0 Edit/Write calls (no dispatch_end, no task result). SNAP file stays byte-identical to iter-021
  (no partial application → no broken state). **This is a budget ceiling on the refactor MECHANISM, not the
  math.** FIX (iter-023): DECOMPOSE the re-base into a sequence of small, independently-dispatched,
  cold-build-gated refactor steps (effort-breaker / staged: foundation-reorder → re-base `tensorObj` alone →
  unitor → braiding → associator → downstream `sorry`s), OR surface the in-budget impossibility to the user.
  Do NOT dispatch a 4th monolithic refactor. Dual-instance deletion stays REFUTED; Option-B prover ABANDONED.
- **FBC `base_change_mate_gstar_transpose` sorry body carries a FALSE-STATUS comment + dangling refs — do NOT
  trust it (iter-020, STILL UNRESOLVED iter-022, auditor CRITICAL ×3 + lvbc-fbc020).** `FlatBaseChange.lean`
  (now ~L2267-2268; line refs drift as the file grows) asserts crux sub-(b) is "PROVEN and axiom-clean as the
  standalone lemma `base_change_mate_extendScalars_inner_value_counit`" — that lemma DOES NOT EXIST anywhere in
  the project (grep: only this comment). Nearby (now ~L2263-2265) names ~3 more non-existent decls
  (`…_fstar_reindex_legs_unitExpand` @~1273, `…_gammaDistribute` @~1304, `pullbackPushforward_unit_comp`
  @~1144). A prover reading these would hunt phantom theorems. **ALSO (NEW iter-022): dead `set_option
  maxHeartbeats` cluster at ~L2127-2130** — 4 stacked `set_option … in` are consumed by the following
  `/-! ### Seam 3 -/` doc-comment command (in Lean 4 `set_option … in` binds the NEXT command; a doc-comment
  IS a command), so they never reach any declaration and Seam-3 decls silently run at the default heartbeat.
  **STRATEGIC TENSION:** ARCHON_MEMORY records the `base_change_mate_*` apparatus as SHEAF-LEVEL-route DEAD /
  slated for excision, yet `base_change_mate_gstar_transpose` (sorry) is STILL wired into the LIVE seeds via
  `pushforward_base_change_mate_cancelBaseChange` (and the chapter's dead phantom
  `lem:pushforward_base_change_mate_sections_direct` is still cited by the live `cancelBaseChange` proof,
  chapter L1770). Either excise the apparatus AND re-route the seeds onto the concrete-tilde/glue path, or the
  "dead" classification is stale. Resolve in the dedicated excision iter (planner/refactor decision, NOT a
  prover); fix the false-status comment + dead `set_option` cluster + stale iter-numbers (L184-247) then.
- **[RESOLVED iter-018] FBC geometric leg `chartBaseChangeGeometricComparison_mate` — CLOSED cold-green +
  axiom-clean.** The iter-017 "`conjugateEquiv_pullbackComp_inv` is comment-fiction" claim was FALSE: it IS
  real Mathlib (`Scheme.Modules`, Sheaf.lean:238, @[simp]). The whnf-bomb was avoided by driving via CLOSED
  coherences (the `← conjugateEquiv_comp` split engine — see Proof Patterns), NOT the `unit_conjugateEquiv`
  scaffold over the composite. No longer a blocker.
- **[RESOLVED iter-018] FBC algebraic leg `chartBaseChangeModuleReassoc_extendScalarsComp` — CLOSED cold-green
  + axiom-clean.** The "`Eq.mpr` cast" was NOT a residual to strip: `simp only […, eq_mpr_eq_cast, cast_eq]`
  DISSOLVES the `letI : Algebra`-induced casts outright; then the `← conjugateEquiv_comp` (×2) split closes it
  (see Proof Patterns; note the trap: re-declare the `letI : Algebra` instances at the proof head). No longer a
  blocker.
- **SNAP μ-SYNTACTIC-IDENTITY wall — a fully-reduced single `μ_X.hom ≫ μ_X.inv` cancel still fails
  (iter-015, COLD-PROBED, `hK_lhs` + the new `tensorObjAssoc_hK_lhs_head`).** After mechanizing the head
  reduction down to ONE `Localization.Monoidal.μ` hom-inv pair (`cancel_epi` + keystone
  `sheafification_whiskerRight_unit_eq_mu'` + `show`-uniform + flatten — all GREEN), the two `μ_X`
  occurrences PRINT IDENTICALLY but carry HIDDEN distinct `Localization.fac` proof terms → defeq-NOT-token-
  identical. `rw [Iso.hom_inv_id_assoc]`/`rw [Iso.hom_inv_id]` → pattern-not-found; `slice`/`simp`/`erw` →
  isDefEq-timeout. The SAME wall blocks `hK_lhs` Step-1b (the interchange MERGE `tensorHom_comp_tensorHom`/
  `← tensor_comp` at the `c_{A⊗B} ≫ μ.inv` composite-object junction: plain `rw` reducible-only no-match,
  `conv`/`erw` whnf-timeout) AND `associator_naturality`/`associator_hom_app` are NO-MATCH on `α_ A B C`.
  STRUCTURAL FIX (iter-016, do NOT warm-retry): make the two μ's TOKEN-identical — `Localization.Monoidal`
  μ-cancel API, or `Subsingleton.elim`/proof-irrelevance on the `Localization.fac` witness, or restate the
  keystone with a canonical μ object-arg. The head-cancel tail past the μ-pair is already GREEN. NOT a
  head-algebra gap — the algebra is done; only the token-identity is missing. 5th churning iter on hK_lhs.
- **FBC `gammaPushforwardIso_comp_bridge` residual — `(pushforwardComp …).inv.app N = 𝟙` by rfl/whnf KERNEL-
  BOMBS (iter-015, cold-probed).** The bridge body `rw [Functor.map_comp, eqToIso.hom, eqToHom_app,
  eqToHom_map]` is kernel-safe and reduces to `eqToHom ⋯ ≫ Γ.map((pushforwardComp ρ φ).inv.app N) = eqToHom`.
  But `congr 1`, `rw [show (pushforwardComp …).inv.app N = 𝟙 _ from rfl]; rfl`, and
  `show … = eqToHom rfl from rfl` ALL whnf-reduce `pushforwardComp` (= `Iso.refl` underneath) across the
  junction → `(kernel) deterministic timeout` (LSP-clean, cold-bomb). DO NOT close it by any rfl on the whole
  iso. FIX (iter-016): `SheafOfModules.Hom.ext`/`Scheme.Modules.Hom.ext` (sheaf-hom extensionality at the
  open level) + the per-open identity `pushforwardComp_inv_app_app` (`= 𝟙` at every open, EXISTS) — the iso
  is never whnf'd as a whole. This is the SOLE FBC foundation residual; closing it makes
  `gammaPushforwardIso_comp` axiom-clean. **Do NOT trigger the junction-free `gammaPushforwardIso` refactor —
  the morphism route already defeated the bomb; the refactor's reversal-signal precondition does not hold.**
- **FBC `gammaPushforwardIso_comp` element-wise close via `erw [...concreteApply]` + `erw [Category.comp_id]`
  is a KERNEL BOMB the LSP HIDES (iter-013, VERIFIED — it shipped a non-compiling file).** The chain
  `simp only [...concreteApply]; erw [restrictScalarsComp_inv_app_concreteApply, gammaPushforwardIso_hom_concreteApply];
  rw [Hom.comp_app, pushforwardComp_inv_app_app]; erw [Category.comp_id]` reduces the LSP goal to a clean
  `x = hom (Hom.app ((eqToIso E).hom.app N) ⊤) x`, but the resulting proof TERM gives `(kernel) deterministic
  timeout` under `lake build` (erw crosses the value-`ModuleCat`/`X.Modules` object-junction diamond up-to-defeq,
  emitting a term the kernel can't whnf in budget). RULE: any FBC/SNAP proof closing through that diamond MUST
  be cold-`lake build`-verified before commit — an LSP-clean goal is NOT sufficient. FIX (per cut-off
  diamond-collapse analogist): close the residual `eqToIso (Spec.map_comp)` cast via eqToHom-CALCULUS
  (`eqToHom_map`, `eqToHom_map_comp`, `eqToHom_trans`, `eqToHom_app`, `eqToHom_refl` — all exist), NOT erw;
  ring content already isolated in `globalSectionsIso_hom_comp3_specMap_appTop`.
  **iter-014 DECISIVE CORRECTION (cold-build-localized via 3 builds — corrects the iter-011–013 framing):
  the kernel bomb is the RHS REDUCTION itself, NOT the residual `eqToHom` cast.** Three cold builds pin it:
  (1) clean stub → GREEN; (2) `rw [gammaPushforwardIso_hom_apply (φ≫ρ) N x]` ALONE (one junction rfl on the
  LHS) → GREEN — so a SINGLE heavy identity-on-carrier rfl is kernel-light; (3) add the
  `simp only [ModuleCat.comp_apply, restrictScalars_map_concreteApply, gammaPushforwardIso_hom_concreteApply,
  moduleSpecΓFunctor_map_concreteApply]` distribution (drop the wrappers, BEFORE ever touching the residual)
  → `(kernel) deterministic timeout @743`. Each `_concreteApply` lemma is `rfl` and compiles in isolation, but
  reducing the FULL RHS composite forces the kernel to whnf the value-`ModuleCat`/`X.Modules` junction once
  per wrapper and those reductions COMPOUND past the limit — the residual cast is never even reached. So the
  eqToHom-calculus fix above CANNOT be applied (you can't get TO the residual). The element/sheaf-level family
  is now EXHAUSTED. iter-015 = pre-committed ROUTE PIVOT: refactor `gammaPushforwardIso` to a junction-free
  construction, or find a Mathlib-native pushforward-composition coherence. The committed body reduces only
  the LHS + `sorry` (cold-build green, no bomb term).
- **PROCESS / LATENT (iter-012, re-confirmed iter-014, low-urgency): misplaced `set_option maxHeartbeats` in
  FlatBaseChange.lean.** L1480 (`4000000 in`) and L1515–1518 (four stacked 4M/4M/4M/1.6M) each precede a
  `/-! … -/` doc-section command, NOT a `theorem`, so the budget scopes to the comment and
  `base_change_mate_gstar_transpose` runs at DEFAULT 400000 hb. Inert today (decls are COMPILE-DEAD mate
  apparatus with bare-`sorry` bodies) — fix only when the mate-excision refactor iter touches that region;
  move ONE option to immediately precede the `theorem`.
- **PROCESS: a prover lane that ERRORS mid-edit (idle_timeout / `MCP -32000 Connection closed`) can leave its
  file NON-COMPILING on disk (iter-013, FBC).** sync_leanok then strips ALL `\leanok` from that chapter
  (correct verdict on a broken module, not laundering). The next iter must `lean_diagnostic_messages` / cold
  build the target files and REPAIR before new proof work; treat "both targets cold-build green" as a pre-flight gate.
- **SNAP assembly `tensorObjAssoc_eq_localizedAssociator` is a multi-step μ/counit chase, NOT "one
  `associator_naturality` step from done" (iter-009 premise, DISPROVED iter-010).** The full-goal μ hom-inv
  cancel cannot fire by ANY of `rw`/`simp`/`erw`/`change`-via-`slice`/`rfl`-bridge: the keystones
  (`sheafification_whiskerRight_unit_eq_mu` / `…_whiskerLeft_…`) produce a `μ` over
  `(sheafification ⋙ forget ⋙ restrictScalars).obj (a⊗b)` whereas `tensorObjLocalizedIso`'s `μ` carries
  `(toPresheafOfModules X).obj (A.tensorObj B)` — defeq (bridge `:= rfl` typechecks) but DIFFERENT internal
  `⋙`-nesting, so the matcher cannot unify the two `μ` terms in the giant goal and `Iso.hom_inv_id_assoc`
  never fires. ~60% of a worked closed-form proof is committed & cold-build-verified (collapse to common
  `K = L'(α^p) ≫ μ_{a,b⊗c}⁻¹ ≫ (L'a ◁ μ_{b,c}⁻¹) ≫ (c_A ⊗ₘ (c_B ⊗ₘ c_C))`). DO NOT re-fire a blind warm
  `prove` lane (pc010 reversal signal tripped — sorry dropped 0). STRUCTURAL CHANGE required: either restate
  the two keystones with canonical μ-object nesting `(toPresheafOfModules X).obj (sheafification.obj _)`
  (proofs defeq-tolerant: `simp only [Functor.id_obj]; rw [μ_natural_…, Iso.inv_hom_id_assoc]; rfl`), OR
  effort-break into `hK_lhs : <lhs>=K` / `hK_rhs : <rhs>=K` standalone lemmas (slice+erw throughout) +
  assembly = `hK_lhs.trans hK_rhs.symm`. The 5 gated coherences cascade only after this lands.
  **iter-011 UPDATE:** the object-mismatch half of this blocker is CLEARED — canonical keystones
  (`…_eq_mu'`, defeq wrappers) + `simp only [tensorObj]` make both μ's print identically (verified). But
  the cancel STILL won't fire (`Iso.hom_inv_id_assoc` reported UNUSED): TWO residual causes — (a) ADJACENCY:
  the seg-1 keystone composite is ONE atomic factor (it arrived via `rw [Iso.eq_inv_comp, asIso_hom]`
  wrapping), so `simp [Category.assoc]` never makes μ.hom/μ.inv adjacent; (b) INSTANCE IDENTITY: `⊗_loc`
  not defeq `tensorObj`, so the two object-identical μ's may not be the same `Iso` term to the matcher.
  Both dissolve only under the hK split with **`hK_rhs` built FRESH (NO `Iso.eq_inv_comp` wrapping)** +
  `hK_lhs` via `Localization.Monoidal.associator_hom_app`. **GATING SUB-TASK = derive the WELL-TYPED `K`**
  (the schematic `L'(α^p)` does NOT typecheck — its domain differs from the assembly domain; `K` must absorb
  counit object-glue on all 4 tensor slots). This is prover/effort-breaker work, NOT a blueprint gap (the
  chapter's `K` is mathematically explicit, snap011 checker confirms). 3 iters at 0 net sorry — do NOT
  re-fire the warm monolithic lane.
  **iter-012 UPDATE (GATING CLEARED + the cancel premise REFUTED):** the well-typed `K` is BUILT —
  `assocCommonForm` (SectionGradedRing.lean L1847), a 5-factor composite = the schematic 4 factors PLUS
  a seg-1 inverse-whiskered-unit prefix `(L'(η_{a⊗b} ▷ c))⁻¹` (the counit object-glue re-basing the
  domain to `tensorObj (tensorObj A B) C`); typechecks via `@asIso … (isIso_sheafification_whiskerRight_unit …)`.
  Assembly `tensorObjAssoc_eq_localizedAssociator := hK_lhs.trans hK_rhs.symm` is own-body sorry-FREE.
  hK_rhs (L1960) reduced through prefix-strip (2×`congrArg (fun t => _ ≫ t)`) + braiding-collapse
  (`slice_lhs 1 3 => erw [hcol]`) + keystone (`erw [sheafification_whiskerLeft_unit_eq_mu']`) to the
  single μ-cancel; hK_lhs (L1903) to its isolated localized-side goal. **DECISIVE: the iter-011
  "isolation will let `Iso.hom_inv_id_assoc` fire" premise is FALSE (verified on the small goal).** The
  μ-pair `μ.hom ≫ μ.inv` does NOT cancel because the keystone's inner `≫` is the `Localization.Monoidal`
  localized-category `CategoryStruct.comp` while the boundary `≫ μ.inv` from `tensorObjLocalizedIso` is
  the `X.Modules`-synonym comp — DEFEQ but NOT SYNTACTIC. `Category.assoc` cannot re-associate across the
  boundary (no progress); `rw/erw [Iso.hom_inv_id_assoc]`, `slice … rw [Iso.hom_inv_id]`,
  `rw [← Category.assoc, Iso.eq_comp_inv]` all fail to find the pair; forcing it with
  `simp only [Localization.Monoidal.μ]` (unfold to `tensorBifunctorIso`) TIMES OUT at isDefEq. STRUCTURAL
  FIX (iter-013, BOTH halves share it): a canonical instance-agnostic cancel of `e.hom ≫ e.inv` across the
  `LocalizedMonoidal`-synonym / base-`comp` boundary (a `change` to `(L').obj`-level comp, or a dedicated
  `Localization.Monoidal` cancellation idiom) — get this from a mathlib-analogist consult, NOT another
  prover round. Once available: hK_rhs closes with `+ μ_natural_right + counit triangle`; hK_lhs with
  `+ associator_naturality + associator_hom_app` (the latter won't fire on `α_ A B C` directly — objects
  must be `(L').obj _`) `+ the same cancel`.
- **FBC foundation `gammaPushforwardNatIso_comp` is NOT "pointwise reflexivity" AND the monolithic-simp
  proof OVERFLOWS THE KERNEL (iter-009).** The blueprint recipe claiming pointwise `rfl` is WRONG (prover +
  both reviewers): LHS is indexed by the composite `(Spec(φ≫ρ))^♯_⊤`, RHS factors through
  `(Spec ρ)^♯_⊤ ∘ (Spec φ)^♯_⊤` joined by an `eqToHom` from `Spec.map_comp` — the residual is the 3-fold
  (R→S→T) composite analogue of `globalSectionsIso_hom_comp_specMap_appTop` (= `Scheme.ΓSpecIso_inv_naturality`),
  genuinely non-`rfl` (single-map analogy fails — that square is over a fixed φ). The domain gluing DOES
  collapse (`hpc`: `pushforwardComp.inv.app N = 𝟙` via `ext U:2; simp [pushforwardComp_inv_app_app]; rfl`).
  The natIso-pasting form proven by one structural `simp only` (unfolding `gammaPushforwardIso`)
  deterministically times out the kernel (`lake build` confirms; LSP hides it). REQUIRED route: kernel-light —
  per-component `gammaPushforwardIso` coherence helper via `NatIso`/`Functor.ext` + a 3-fold ring-level
  coherence helper, NOT a monolithic simp. The crux `pullback_spec_tilde_iso_ring_square_natural` is gated
  on this foundation — do NOT scaffold the seams/crux on the unproven base.
  **iter-011 UPDATE:** the kernel-light route LANDED for the natIso level — `gammaPushforwardNatIso_comp`'s
  own body is now CLOSED (see Proof Pattern "Kernel-light NatIso composition coherence"), reducing to the
  new per-component `gammaPushforwardIso_comp`. The 3-fold ring helper `globalSectionsIso_hom_comp3_specMap_appTop`
  is PROVED (= single-map lemma at `φ≫ρ`). `gammaPushforwardIso_comp` now carries the WHOLE remaining content
  in ONE named residual: `Γ(cast) x = x` (the `Spec.map_comp` glue). **DO NOT retry on that residual:** `rfl`
  (not defeq), `change`/`rfl` defeq collapse (**verified cold-build kernel bomb** — whnf timeout even on the
  small per-component goal), element `simp` on `restrictScalarsComp'App_*` (discrimination-tree miss, the
  X.Modules/value-ModuleCat diamond), bare `erw [pushforwardComp_inv_app_val_app]` (doesn't fire —
  `moduleSpecΓFunctor.map g` not syntactically `g.val.app U`). NEEDED (rw-only, kernel-light): 2 exposure
  lemmas — (a) `moduleSpecΓFunctor.map g` underlying `= (modulesSpecToSheaf.map g).val.app (op ⊤)`; (b)
  `ConcreteCategory.hom (eqToHom _) x = x` for `ModuleCat`. This is the CLOSEST-TO-DONE FBC target.
  **iter-012 UPDATE (the residual is BROADER than the cast; element-wise FAMILY exhausted):** the
  exposure lemma (b) was built — `moduleCat_eqToHom_concreteCategory_apply` (L696, `subst h; rfl`) turns
  the `eqToHom` into a SYMBOLIC carrier `cast` without forcing a whnf — plus 3 more `:= rfl` concreteApply
  helpers (L706/713/720). The goal is now fully exposed as `x = B(A(γ_φ(Γ_pc(cast x))))`. **DECISIVE
  REFUTATION:** the residual is NOT just `Γ(cast) x = x` with the outer B/A/γ_φ collapsing freely — every
  wrapper changes the ModuleCat OBJECT (domain ≠ codomain as objects, agreeing ONLY on the carrier). The
  obstruction is the value-`ModuleCat`/`X.Modules` OBJECT-JUNCTION DIAMOND: carrier-defeq is CHEAP
  (`rfl : ↑(Γ(pushforward (Spec(φ≫ρ)) N)) = ↑(Γ(pushforward (Spec ρ ≫ Spec φ) N))` typechecks instantly),
  but per-junction OBJECT-defeq is HEAVY (whnf kernel bomb). `rw/simp [helper]` fails on γ_φ and B
  (motive-not-type-correct: rewriting `γ_φ z → z` retypes z across the diamond); only A and inner-γ_ρ fire
  (they sit under `restrictScalars.map`, a syntactic junction). THREE collapse routes VERIFIED-FAIL on cold
  build — whole-goal defeq (`exact (gammaPushforwardIso_inv_apply _ _ _).symm`), monolithic `rfl`
  (`rw [moduleCat_eqToHom…]; rfl`), term-mode `Eq.trans` chain over the 5 wrappers (>1.6M heartbeats). The
  ENTIRE element-wise-collapse family is provably exhausted. STRUCTURAL FIX (iter-013): route through
  `.val.app (op ⊤)` at the SHEAF level (`SheafOfModules.pushforwardComp_inv_app_val_app` EXISTS, gives
  `(((pushforwardComp φ ψ).inv.app M).val.app U) x = x`) where restrictScalars/globalSections object-
  junctions never form — but expressing B/A/γ_φ (restrictScalars-level) sheaf-level needs a mathlib-analogist
  consult (likely an `Iso.ext`/inverse-comparison route, or a structural lemma identifying the whole
  `gammaPushforwardIso` object-wise). Do NOT re-assign element-wise.

- **FBC crux `pullback_spec_tilde_iso_ring_square_natural` `(★)` = `pst` pseudofunctoriality coherence — do
  NOT re-run as a monolithic prover (iter-008, churn pattern, no sorry progress several iters).** The real
  obligation after the (preserved, compiling) 3-peel partial is the **ring-square pseudofunctoriality
  (cocycle) coherence of the conjugate dictionary `pst`** (the two builds of `pst` for `inclR ≫ ρB =
  ρ ≫ inclR'` agree, mediated by `geom = chartBaseChangeGeometricComparison` / `reassoc =
  chartBaseChangeModuleReassoc`). It is a documented multi-hundred-LOC factored-conjugate-mate build
  ("class resisted 7 iters", `analogies/fbc-composite-mate-recognition.md`). **Three dead-ends eliminated
  as FACT this iter — do not retry:** (1) `moduleSpecΓFunctor` is **NOT Faithful** (global Γ on all
  `(Spec R).Modules`, not just QCoh) ⇒ no `moduleSpecΓFunctor.map_injective` / Γ-injectivity discharge;
  (2) `rfl`/`ext;rfl`/`aesop_cat`/`exact?` all fail (the `pst` legs are genuine conjugate isos, NOT
  identity-on-sections); (3) the inverse-transpose shortcut needs the SAME 3 transposes (source is a triple
  pullback). The 3 `homEquiv.injective` transpose peels are **provably reversible** (`simp[←map_comp];congr`
  round-trips them) — setup-only, not progress. **Required structural move:** effort-break seam4
  (`…ring_square_mate_glue`, effort ~1078) first; prove the cheap foundation sub-lemma (composition
  coherence of `gammaPushforwardNatIso`, likely `ext;rfl` since identity-on-elements per L662), then
  conjugate via the Mathlib `Adjunction.Mates` simp-set (`conjugateEquiv_{symm_comp,comp,whiskerLeft/Right,
  associator_hom,leftAdjointCompIso_inv}`) + per-leg brick `unit_conjugateEquiv_symm`; that yields `pst`
  pseudofunctoriality `pullback_spec_tilde_iso_comp`, whence `(★)`. Reuse proven brick
  `pullback_spec_tilde_iso_inv_unit_triangle` (L707, axiom-clean).
- **SNAP associator bridge `tensorObjAssoc_eq_localizedAssociator` is NOT a "braiding-bridge clone" (iter-007).**
  The 4 remaining SNAP sorries (`tensorPowAdd_{rightUnit,braiding}` succ, `tensorPowAdd_assoc` base+succ,
  `sectionsMul_mul_assoc`) are all gated on this one bridge. The plan premise that each bridge clones the
  working `tensorBraiding_eq_localizedBraiding` (which opens `rw [show tensorBraiding = L'.mapIso β_p from rfl]`
  because it is a bare `mapIso`) is FALSE for the associator: `tensorObjAssoc` is a hand-built 5-segment
  composite (inv whiskered unit · `sheafification.mapIso α_p` · braiding · whiskered unit · braiding) because
  `(A⊗B)⊗C` and `A⊗(B⊗C)` sheafify *different* presheaves. The bridge requires matching that composite against
  `Localization.Monoidal.associator_hom_app`'s μ-formula — a genuine 100–200-line theorem. **Decompose via
  effort-breaker** into seams: (a) keystone — the two whiskered-unit segments EQUAL `Localization.Monoidal.μ`
  (both are the strong-monoidality comparison); (b) `sheafification.mapIso α_p = L'.mapIso α_p` (defeq); (c) the
  two presheaf braidings cancel as in the braiding bridge. Do NOT re-assign as a clone — that reproduces the
  pc007 churn. `sectionMul_assoc_core` itself is now CLOSED bridge-free (see pattern above); only the
  iso-coherences (`tensorPowAdd_*`) remain bridge-gated.
- **SNAP 6 coherence sorries (iter-004): gated on 4 unbuilt bridge lemmas, NOT on hand-proofs.**
  `tensorPowAdd_{rightUnit,braiding}`(succ), `tensorPowAdd_assoc`, `sectionMul_assoc_core`,
  `sectionsMul_mul_assoc` ALL reduce to one obstacle: the hand-built `tensorObj F G =
  sheafification.obj(F.toPr ⊗_p G.toPr)` is NOT definitionally the localized `F ⊗_loc G =
  ((tensorBifunctor L W ε).obj F).obj G`. Do NOT re-attempt as direct Mac Lane hand-proofs (STUCK ≥3
  iters before the iter-004 pivot). Build the 4 bridge lemmas (`tensorObjAssoc_eq_localizedAssociator`,
  `tensorBraiding_eq_localizedBraiding`, `tensorObjUnitIso_eq_localizedLeftUnitor`,
  `tensorObjRightUnitor_eq_localizedRightUnitor`) via μ-transport (Mathlib `Localization.Monoidal.{μ,
  associator_hom_app, leftUnitor_hom_app, rightUnitor_hom_app, braidingNatIso_hom_app,
  μ_natural_left/right}`), then `rw` hand-built→localized + invoke `pentagon`/`triangle`/`hexagon`.
  Fallback Option A = rewire hand-built defs onto the synonym's `⊗` (refactor).
- **FBC dead `base_change_mate_*` apparatus (iter-001…004): DEAD route, DELETE — do not prove.** The MATE
  route is abandoned (memory; goal closure has 0 mate riders per iter-002 leandag).
  `base_change_mate_gstar_transpose`'s sorry body (FlatBaseChange.lean ~1460) contains FALSE
  documentation: it cites three lemmas that exist nowhere (`base_change_mate_unit_value`,
  `base_change_mate_fstar_reindex_legs_unitExpand`, `base_change_mate_extendScalars_inner_value_counit`)
  and an out-of-bounds `@~1999` pointer (file is 1666 lines). Plus dead `set_option maxHeartbeats
  4000000 in` on a `/-!` comment (1312-1315) and 4 `/-!` planning blocks for never-written lemmas. Route
  to the `refactor` subagent for deletion (confirm rider-only via `dag-query ancestors` first); NEVER a
  prover. Flagged audit003 + audit004.
- **FBC `baseChangeGammaPullbackEquiv`/`baseChangeEqLocusToPullbackGamma` (iter-001): NOT provable as typed.**
  Missing `[CompactSpace X] [QuasiSeparatedSpace X]` (qcqs); sub-piece (b) `B ⊗ ∏ ≅ ∏ (B ⊗ −)` needs a FINITE
  cover. Structural fix required before any prover re-send: add the two instance args + switch cover to
  `Scheme.exists_finite_affineCover_inter_isQuasiCompact`. Also gated on `affineBaseChange_pushforward_iso`
  (still `sorry` in FlatBaseChange.lean). Neither decl is protected.
- **SNAP `sectionsMul_one_mul` via `:= rfl` Γ-of-iso-composite split (iter-001): DEAD.** whnf 200000-hb timeout,
  build-verified. Only retry via the explicit functor-composition lemma (`Iso.trans_hom` + `SheafOfModules.comp_val`
  + term-mode ModuleCat comp-apply). The cancellation half `sectionsCast_eqToIso_cancel` is already proven.
  **RESOLVED iter-002** — closed via the `show`-split + adjunction-transpose core (see Proof Patterns).
- **SNAP 3 remaining coherences `sectionsMul_mul_one`/`_mul_assoc`/`_mul_comm` via the `one_mul` template
  (iter-002): WON'T transfer.** `one_mul` only worked because `tensorPowAdd L 0 n` iota-reduces on the
  literal `0` (`tensorPowAdd_zero`, rfl); the other three match a VARIABLE index and are the right-unitor/
  associator/braiding coherences of the recursive `tensorPowAdd`. Structural prerequisite (do this FIRST,
  by induction on the `tensorPowAdd` recursion): `tensorPowAdd_succ_zero`/right-unitor (→ mul_one),
  `tensorPowAdd_assoc` (→ mul_assoc), `tensorPowAdd_braiding` (→ mul_comm). Then the section level closes
  fast via the adjunction-transpose template. Do NOT re-dispatch a prover at the coherences directly.
  **UPDATE iter-003:** the section-level wiring works — `sectionsMul_mul_one`/`_mul_comm` now have sorry-free
  bodies (template confirmed), `_mul_assoc` is unfolded. BUT all 5 residual sorry-bearing decls
  (`tensorPowAdd_rightUnit` succ, `tensorPowAdd_braiding`, `tensorPowAdd_assoc`, `sectionMul_assoc_core`,
  `sectionsMul_mul_assoc`) reduce to ONE obstacle: **Mac Lane symmetric-monoidal coherence
  (triangle/hexagon/pentagon) transferred from `PresheafOfModules.monoidalCategory` to `X.Modules` through the
  `isIso_sheafification_whiskerRight_unit` comparison isos baked into the 5-segment `tensorObjAssoc` composite.**
  No sheaf-level monoidal coherence API exists in file (~hundreds of LOC). This is now a STRUCTURAL decision,
  NOT a helper round: before re-dispatching, run mathlib-analogist (does Mathlib have a "transport monoidal
  coherence across a comparison iso / equivalence" idiom — `Monoidal.transport`/`Equivalence` family — or does
  `X.Modules` inherit a monoidal structure from Mathlib more directly?). SNAP sorry went 3→8 raw this iter
  purely from this decomposition — do NOT mistake further helper-splitting for progress. The
  `tensorPowAdd_rightUnit` base case is separately gated on `tensorBraiding 𝟙 𝟙 = Iso.refl` (Mathlib name
  unknown; `BraidedCategory.braiding_tensorUnit_left` does NOT exist; try `β_𝟙 𝟙 = λ_𝟙 ≪≫ ρ_𝟙.symm` +
  `unitors_equal`). `sectionsMul_mul_assoc` also needs `sectionsMul_whiskerRight/_whiskerLeft_naturality`
  bricks (mirror `sectionMul_braiding_core`'s η-naturality template) — independently addable.
- **FBC `baseChange_sheafConditionFork_tensorIso` / separated / mayerVietoris (iter-002): blocked on
  per-chart infra, no in-file shortcut.** `baseChange_sheafConditionFork_tensorIso` is the IRREDUCIBLE
  module-level base-change content (proven ⇔ `baseChangeGammaPullbackEquiv`). It needs the per-chart
  `pullback_spec_tilde_iso` (Stacks 01I9) restriction-compatibility over a finite cover of non-affine `X`
  + tensor-commutes-with-finite-products — the SAME multi-hundred-LOC Mathlib-absent infra
  `affineBaseChange_pushforward_iso` is blocked on. Separated + MV transitively need it. Scope an infra
  lane (dag-walker/effort-breaker on `lem:base_changed_equalizer_diagram`) BEFORE any prover attempt. The
  one ready FBC node is the bridge REVERSE direction (forward already proven) — but verify
  qcqs-pushforward-quasicoherent exists in Mathlib first.
- **FBC `pullback_spec_tilde_iso_restriction_naturality` crux (iter-003): scaffolding done, ONE residual sorry.**
  All bricks proved sorry-free (`chartBaseChangeGeometricComparison`, `chartBaseChange_ring_square` (b1),
  `chartBaseChangeModuleReassoc` (b2-alg)); after `apply Iso.ext` the residual is the naturality of the OPAQUE
  `pullback_spec_tilde_iso` (= `conjugateIsoEquiv` of `gammaPushforwardNatIso`) across the base-change ring
  square. `rfl`/`aesop_cat`/`simp only [chart…]` do NOT close it (verified). Route (not a dead end): naturality
  of `gammaPushforwardNatIso` under the ring square transported through `conjugateEquiv`/`conjugateIsoEquiv`
  naturality. This is the live FBC frontier — consider effort-breaker into (i) gammaPushforwardNatIso ring-square
  naturality, (ii) conjugateIsoEquiv transport.
- **FBC `base_change_mate_gstar_transpose` (iter-003 caveat): OFF-PATH, do not dispatch — despite a "viable
  route" Lean read.** lean-auditor (no-strategic-bias by design) flags this sorry as the open residual of a
  "viable conjugate-counit route", NOT a dead end, and disputes the "DEAD" label. That is a LOCAL-Lean judgment
  only. Strategically the whole MATE route is dead (Archon memory) and OFF the goal-closure cone (iter-002
  leandag: goal closure = 22 nodes, ZERO mate riders; the concrete-tilde chain replaces it). Its sorry comment
  also carries STALE cross-refs to lemmas/line-numbers that no longer exist (`…fstar_reindex_legs_unitExpand`,
  `base_change_mate_unit_value`, `…inner_value_counit @~1999` past EOF). Do NOT revive it.

- **INFRA: prover phase instant-death (iters 068–077) — `roles.prover` was `fable` (no entitlement on this
  login) → every prover died on `401 Invalid authentication credentials` BEFORE any session log was written.**
  Fingerprint: `meta.json prover.durationSecs:0`, `parallel.jsonl` = `failed:N`, `logs/iter-NNN/provers/` dir
  EMPTY (no `*.jsonl`), `attempts_raw.jsonl` = `no_prover_lane:true`. Plan iter-077 fixed `config.json
  roles.prover` fable→opus, BUT the fix did NOT take effect that iter — the prover role is resolved at
  iter-START, so a config edit during the plan phase lands one iter LATE (iter-078 is the first opus prover).
  **If iter-078 ALSO shows `durationSecs:0` / empty `provers/` on opus, the role was not the (sole) cause —
  the bug is in the prover-dispatch path; escalate to user, stop re-dispatching prove lanes into a broken pipe.**
  None of iters 068–077 produced math evidence; GR/SNAP/GlueDescent routes are un-attempted, NOT falsified.
- **[RESOLVED iter-064 — C2 CLOSED axiom-clean; see the `appTop (Y := Spec …)` ascription pattern in Proof
  Patterns.]** ~~GR-quot C2 (`bundleTransition_cocycle`) — do NOT re-assign until decl-ordering + (b)
  `baseChange_bridge` are staged.~~ Both items landed iter-064 (the prover did the relocation itself after the
  refactor subagent was killed mid-plan-phase; the (b) bridges closed via ΓSpecIso naturality + the `Y :=`
  ascription). C2, `bundleTransition_cocycle_transport`, and rider `universalQuotient` all axiom-clean.

- **[RESOLVED iter-060 — see the kernel-OOM-control pattern in Proof Patterns.]** ~~GrassmannianQuot.lean cold
  `lake build` SIGKILLed (exit 137) — resource ceiling (iter-059).~~ The prime suspect was confirmed:
  `set_option maxHeartbeats 1000000` on `bundleTransition_self`. The old `.hom`-cast term hit `(kernel)
  deterministic timeout` at default heartbeats and OOM'd at 1e6. Re-proven at the iso level (generic
  `subst`-helper `pullbackFreeIso_trans_symm_eqToIso` + small-context matrix collapse): cold build 227s→22s,
  ~7GB, axiom-clean, override removed; OOM was proof-local so NO file split was needed. `sync_leanok` ran
  this iter (+13). GR-quot C2 lane is now unblocked against the fast file.
- **[RESOLVED iter-056 — NOT a blocker; see the `Algebra.IsEpi` pattern in Proof Patterns.]** ~~Open-immersion
  flat-epimorphism base change ABSENT from Mathlib~~ — the base change was fully constructible from `Algebra.IsEpi`
  (`gf_isEpi_restrict_of_affine_le` + `gf_flat_of_isEpi`); `genericFlatness` now reduces to the STEP-3 semilinearity
  equation only (iter-058). Original (stale) note retained below for the counterexample it records.
  (iter-055, GF; FlatteningStratification L3192).** After the source-span descent reduces the per-`(U,W)` flatness
  to per-piece `Module.Flat Γ(S,U) Γ(F, X.basicOpen g)`, the close needs `IsBaseChange Γ(S,U) (id : M →ₗ[Γ(S,V)] M)`
  — i.e. the open immersion `U ↪ V` makes `Γ(S,V) → Γ(S,U)` a flat ring epimorphism (`R ⊗_{A_f} R ≅ R`). The
  consumer `gf_flat_of_isBaseChange_id` is BUILT and waiting; only this ingredient is missing. Searched
  `Module.Flat.of_isLocalizedModule`, `flat_iff_of_isLocalization`, `Module.Flat.isBaseChange`, `RingHom.Flat`,
  `IsOpenImmersion` — none supply it. A general affine `U ≤ V` need NOT be a *basic* open, so localization-descent
  lemmas (which `gf_base_localization_comparison` already gives flatness from) do not apply. **Counterexample (gap
  is real):** "`M` flat/`A_f` + tower `A_f → R → M` ⟹ `M` flat/`R`" is FALSE in general (`A_f=k`, `R=k[x]`,
  `M=k[x]/(x)`); it holds precisely because `A_f → R` is a flat epimorphism. **Do NOT re-queue an identical prover
  round on `genericFlatness`** — escalate this one ring/module lemma as a dedicated mathlib-build lane. Precise
  statement: `informal/gf_openImmersion_isBaseChange.md`.
- **SNAP `relTensorProj.naturality` BLOCKED on a `forget₂ CommRingCat→RingCat` carrier mismatch (iter-058;
  SectionGradedRing L658).** The projection row's component `app` is PROVEN (apex-carrier identification via
  `tensorObj_obj` defeq landed sorry-free), but naturality reduces to `projL_V ∘ (ℤ-tensor restriction) =
  (apex restriction) ∘ projL_U`, where the apex uses the relative-tensor base ring
  `R(V)=(X.sheaf.obj⋙forget₂ CommRingCat RingCat).obj V` while `projL` is built over the `CommRingCat` carrier
  `X.sheaf.obj.obj V`. Any `show`/`change` to the peeled form re-elaborates `projL` and demands the `RingCat`-carrier
  `Module ↑(R.obj V) ↑(P.obj V)` instance (defeq but not syntactically registered). Mathlib's
  `tensorObj_map_tmul` is stated for the `ModuleCat`-presheaf restriction, not the `Ab` one. Dead ends: (i)
  `simp [hom_comp, hom_ofHom, comp_apply]` doesn't peel the categorical `≫` here; (ii) `show`/`change`. **Do NOT
  re-queue a bare prover round** — FIX = a `restrictScalars`/`forget₂` carrier-transport lemma OR (likely cleaner)
  prove naturality at the `ModuleCat`-presheaf level BEFORE forgetting to `Ab`. Blueprint-expand
  `lem:relativeTensor_as_coequalizer` step-2 first.
- **SNAP triple-tensor presheaf `T` via bare `simp; rfl` element induction — 200k-heartbeat `whnf` wall (iter-055).**
  The nested triple tensor `P.obj U ⊗_ℤ (R₀.obj U ⊗_ℤ Q.obj U)` makes the per-element `tmul => simp; rfl` closing
  step time out (perf, NOT a math gap). Do NOT re-dispatch the naive form. Use `maxHeartbeats 800000` + explicit
  `simp only [tensorObj_map_tmul, …]` lists, OR build `T` by re-using the Step-1 `relTensorDomainPresheaf` functor
  twice. The construction is feasible (apex CommRing routing solved, all categorical ingredients present).
- **`SheafOfModules.stalk` ABSENT from Mathlib — kills the blueprinted `genericFlatness` stalk route (iter-052,
  GF-G3).** G3.2 (`gf_stalk_flat_over_base`) and `gf_flat_locality_assembly` are both phrased over sheaf-module
  stalks `F_x`; loogle returns 0 for `SheafOfModules.stalk`/`Scheme.Modules.stalk`, so they cannot even be
  TYPED. **Do NOT retry the stalk route.** Re-spec the close around **source-span descent**: feed
  `Module.flat_of_isLocalized_span` (`Mathlib.RingTheory.Flat.Localization`, source-side span criterion) on a
  basic-open cover of `W` aligned to the patch cover `{W_j}`, via two bridges — (1) the same-base
  localized-module flatness lemma below, (2) chart-independent section-localization `Γ(F,D(g)) ≅ (M_j)_g`. 2–3
  iter descent build, NOT a one-iter close. The 3 pure-algebra G3 anchors (G3.1/G3.3/G3.4) DID land axiom-clean.

- **`gf_flat_localizedModule_sameBase` Mathlib GAP (iter-052, GF-G3.2 kernel).** Needed:
  `[Module.Flat R N] → Module.Flat R (LocalizedModule T N)` for `T : Submonoid B` over a tower `R → B → N`
  (localize the SOURCE B-action, base R fixed). True (localization commutes with `lTensor` + exact) but ABSENT —
  loogle `Module.Flat, IsLocalizedModule` returns only `of_isLocalizedModule` (the WRONG-base version: it
  localizes base and module by the same submonoid of the base). Build via the iso
  `(LocalizedModule T N) ⊗_R K ≅ LocalizedModule T (N ⊗_R K)` + localization exactness.

- **SNAP crux abelian residue `J.W (toPresheaf.map (η_P ▷ Q))` — all 3 routes Mathlib-blocked (iter-052,
  SectionGradedRing).** The crux `isIso_sheafification_whiskerRight_unit` reduces (via the now-landed
  `isIso_sheafification_map_iff`) to exactly: *relative-⊗ right-whiskering of an abelian local iso (`J.W`) by `Q`
  stays in `J.W`*. `GrothendieckTopology.W.whiskerRight` does NOT close it (it is the abelian ℤ-tensor; here the
  map is the relative `R(U)`-tensor). Blocked routes: (a) coequalizer-transfer — needs the natural presentation
  `P ⊗_R Q ≅ coequalizer(P ⊗_ℤ R ⊗_ℤ Q ⇉ P ⊗_ℤ Q)` in `Cᵒᵖ ⥤ AddCommGrp`, ABSENT (grep-confirmed); (b) Day's
  closed — needs `MonoidalClosed (PresheafOfModules R₀)`, ABSENT; (c) stalkwise — needs module-sheaf stalks,
  ABSENT. Lowest-cost is (a): build the coequalizer presentation as a multi-step next-iter brick.

- **`Scheme.Modules.glue` C2 (triple-overlap multiplicativity) — RESOLVED at the SIGNATURE level (iter-052,
  GR-quot).** The iter-051 whnf-runaway was cured exactly as predicted: build `pullbackBaseChangeTransport`
  (`pullbackComp`-style) + three `glueData_bridge_{src,mid,tgt}` endpoint identities, then state `_hC2` as an
  `Iso`-equality with `pullbackCongr (bridge)` insertions as type-aligners. The well-typed `_hC2` now lives on
  `glue` and typechecks (validated as a standalone `example`). The whnf hazard does NOT recur because the
  morphisms stay ABSTRACT glue-datum legs (no concrete `compositeBasicOpenImmersion` to unfold). **Remaining:**
  `glue` BODY is still `sorry` (the descent construction, planner-deferred to iter-053+); it bottlenecks 4/5
  GR-quot scaffolds. `functor` is glue-independent and parallelizable. Route for the body: open-immersion
  pullback equivalence (`overRestrictPullbackIso`) + `existsUnique_gluing'`, term-mode under the X.Modules diamond.

- **GF-G1 — RESOLVED iter-051 (whole arc closed axiom-clean).** Base case `gf_qcoh_finite_sections_of_genSections`
  (the X.Modules↔Spec transport) + assembly `gf_qcoh_fintype_finite_sections` + helper
  `module_finite_of_ringEquiv_semilinear` all landed. `genericFlatness` now gated SOLELY on G3
  (`gf_flat_locality_assembly`). Historical detail of the (now-cleared) seam-1/transport blockers retained below.

- **GF-G1 finite-type base case — the Γ-epi crux is now SOLVED; remaining blockers are seam 1 + the
  X.Modules↔Spec transport (iter-047 update of iter-045 entry).** RESOLVED iter-047 (the iter-045 "no Γ-level
  corollary" worry is now bypassed for the affine case): the section-surjectivity crux is the affine
  `tilde.adjunction` counit, NOT a stalkwise bridge — `gf_affine_qcoh_Gamma_epi` (seam 2),
  `gf_qcoh_finite_sections_globally_generated` (seam 3), and `gf_qcoh_finite_sections_of_free_epi` (free-epi
  base case over `Spec R`) all DONE axiom-clean (see the "Affine Γ-epi from the `tilde.adjunction` counit"
  proof pattern). The locality reduction `gf_finite_sections_of_basicOpen_finite_cover` (Stacks 01PB,
  iter-045) is also DONE. STILL blocked (so `gf_qcoh_fintype_finite_sections` / `genericFlatness` remain
  open) on TWO Mathlib-absent pieces: **(seam 1)** refine `SheafOfModules.IsFiniteType`'s abstract open
  cover (`σ.X : σ.I → X.Opens`, arbitrary opens, each with a finite `GeneratingSections`) to a FINITE
  BASIC-OPEN cover `{D(g)}` of a given affine `W`, preserving finite generation under restriction — 3 missing
  primitives: (i) restriction of a `GeneratingSections`/`LocalGeneratorsData` along `D(g) ↪ σ.X i`,
  (ii) topological refinement of an arbitrary open cover of affine `W` to a FINITE standard-basic-open
  subfamily (`PrimeSpectrum.isBasis_basic_opens` + quasi-compactness), (iii) re-express "finite generation on
  D(g)" as a free epi `O_{D(g)}^{⊕I} ↠ F|_{D(g)}`; **(transport)** move the `Spec`-level base case
  `gf_qcoh_finite_sections_of_free_epi` to `X.Modules|_{D(g)} ↝ (Spec Γ(X,D(g))).Modules` (the
  QUOT `overRestrictEquiv`/opaque-immersion plumbing — keep the affine immersion OPAQUE to dodge whnf
  runaway, memories `quot-gap1-closed-opaque-immersion`). **Do NOT send a prover at the full G1 form** —
  decompose seam 1 into the 3 sub-lemmas (start with (ii), most self-contained) + build the `X.Modules`
  affine-local restatement first. Recommended next-iter decomposition is in
  `task_results/.../FlatteningStratification.md`.
  **iter-049 UPDATE:** seam-1 primitives (ii) + (iii) are now DONE axiom-clean —
  `gf_affine_finite_standard_subcover` (ii, affine cover→finite standard-basic-open subfamily via
  `IsAffineOpen.exists_basicOpen_le` + `self_le_iSup_basicOpen_iff` + `Ideal.span_eq_top_iff_finite`) and
  `gf_finite_gen_iff_free_epi` (iii, definitional repackaging of `SheafOfModules.GeneratingSections`, stated
  in abstract `SheafOfModules.{u} R` generality). Primitive (i) `gf_localGenerators_restrict` is the ONLY
  remaining seam-1 blocker, now precisely characterized: restriction-of-generation ≡ the slice restriction
  functor PRESERVING EPIMORPHISMS. Generic `pushforward` (RIGHT adjoint) does NOT; the left-adjoint
  `pullback` route needs a Beck–Chevalley iso `pullback φ (F.over Y) ≅ F.over V` + a Finality proof for
  `Over.map f` (both absent — do NOT retry either abstract route). SOUND route (iter-050): transport `σ.π`
  along the project's geometric bridge `Scheme.Modules.overRestrictPullbackIso` (epi+free-preserving
  geometric `pullback U.ι`, the QUOT gap1 plumbing). The assembly
  `gf_finiteType_affine_finite_cover_generated` reduces entirely to (i) and lands mechanically once (i) does.
  **iter-050 UPDATE — seam-1 CLOSED.** Primitive (i) `gf_localGenerators_restrict` DONE axiom-clean via the
  predicted `overRestrictPullbackIso` route (two `GeneratingSections.map` stages: A slice→geometric on Y via
  `overRestrictEquiv.functor`+`overRestrictUnitIso`+`equivOfIso overRestrictPullbackIso`; B geometric Y→V via
  `pullback (X.homOfLE hVY)`+`pullbackOpenImmersionUnitIso`, objects identified by `pullbackComp`+`pullbackCongr`).
  New reusable engine `SheafOfModules.GeneratingSections.map`/`map_I`/`map_isFiniteType` (analogue of Mathlib
  `Presentation.mapGenerators`; pass `PreservesColimitsOfSize` EXPLICIT, see proof patterns). Assembly
  `gf_finiteType_affine_finite_cover_generated` DONE axiom-clean (dropped unused `[F.IsQuasicoherent]`).
  **G1 `gf_qcoh_fintype_finite_sections` now reduces EXACTLY to ONE per-`g` base case** —
  `gf_qcoh_finite_sections_of_genSections : IsAffineOpen D → F.IsQuasicoherent →
  (σ : ((pullback D.ι).obj F).GeneratingSections) → [σ.IsFiniteType] → Module.Finite Γ(X,D) Γ(F,D)`: the
  gap1-hard `X.Modules ↔ Spec` transport of a finite free epi across `IsAffineOpen.isoSpec`, sub-steps
  (a) transport to `(Spec Γ).Modules` via `isoSpec.inv` + `IsIso fromTildeΓ`; (b) free epi → `tilde N` epi
  (`N = R^{σ.I}` finite, iso-pullback finality + tilde-preserves-coproducts); (c) `moduleSpecΓFunctor.obj F' ≅
  Γ(F,D)`. Then `gf_qcoh_finite_sections_of_free_epi` (DONE) closes it. EFFORT-BREAK (a)/(b)/(c) into separate
  sub-lemmas; dedicate a full iter; do NOT send a prover at the full G1 form.
- **`Scheme.Modules.glue` scaffold signature is INCOMPLETE — fix before any body-fill (iter-050, GrassmannianQuot).**
  The `_g` transition-iso parameter `(_g : ∀ i j, (pullback (D.f i j)).obj (M i) ≅ (pullback (D.t i j ≫ D.f j i)).obj (M j))`
  lacks the module cocycle hypotheses (`g_ii = id`; triple-overlap multiplicative cocycle `g_{jk}∘g_{ij}=g_{ik}`);
  as written it would accept logically incoherent gluing data (lean-auditor + lvb-checker MAJOR). The signature
  must be CORRECTED (add cocycle hypotheses — an honest signature fix, not a proof) before scheduling a body-fill.
  No Mathlib turn-key module descent exists; construction = `overRestrictPullbackIso`/`overRestrictEquiv` chart
  restriction + `existsUnique_gluing'`/`eq_of_locally_eq'` section descent. Bottleneck for `universalQuotient`/
  `tautologicalQuotient`/`represents` (4 of 5 GR-quot scaffolds ride on it).
- **SNAP `tensorPowAdd` (`lem:sheafTensorPow_add`) — blocked on the sheaf-level ASSOCIATOR / strong-monoidality
  of module sheafification (iter-047 onward; both routes re-confirmed blocked iter-049).** Equivalent to
  `IsIso (sheafification.map (η_P ▷ Q))`. Route A (principled `CategoryTheory.LocalizedMonoidal`): sole
  obligation `(J.W.inverseImage (toPresheaf R₀)).IsMonoidal` reduces (Day reflection) to
  `MonoidalClosed (PresheafOfModules R₀)` — search-CONFIRMED ABSENT in the pin (the single missing brick;
  building internal-hom-of-presheaves + "internal hom into a sheaf is a sheaf" is a multi-iter infra task).
  Route B (bespoke local-iso, snap-assoc Analogue 4): needs (i) an `IsLocallyFreeOfRank`/invertibility
  predicate for `X.Modules` (also flagged absent by GR-quot analogist) AND (ii) a "morphism of `X.Modules` is
  iso iff locally iso" criterion — both absent; additionally forming `η_P ▷ Q` itself errors (`whiskerRight`
  needs `MonoidalCategoryStruct (PresheafOfModules X.ringCatSheaf.obj)`, but the instance lives on the defeq
  `MonoidalPresheaf X = PresheafOfModules (X.sheaf.obj ⋙ forget₂ …)` and synthesis won't bridge). Route C
  (generic `IsIso (sheafification.map (η_P ▷ Q))`): mathematically FALSE for non-locally-free `Q` (tensor only
  right-exact ⟹ no local injectivity). DEAD ENDS: full `MonoidalCategory (SheafOfModules R)` directly;
  objectwise/locally-bijective `W.IsMonoidal`. iter-050 must build EITHER Route A's `MonoidalClosed
  (PresheafOfModules R₀)` OR Route B's `{IsLocallyFreeOfRank, X.Modules local-iso criterion, line-bundle
  trivialising cover}` BEFORE the associator → `tensorPowAdd` → graded-ring assembly is reachable.
- **FBC keystone `_legs_conj` — PARKED iter-045 (structural unknowns RESOLVED, residual is a dedicated
  build).** The 8-iter "can the conjugate pair be built / is it conjugate-comparable?" question is now
  closed in Lean: `keystoneAdjR` + `keystoneBeta` are axiom-clean defs, `conjugateEquiv adjL keystoneAdjR`
  typechecks, `unit_conjugateEquiv_symm` holds in-proof. The keystone is STILL open (sorry @1949): the
  residual is a two-stage φ/ψ-Spec-layer transport over `R` (front `gammaPushforwardTildeIso φ`, end
  `gammaPushforwardIso ψ` + the 6-iso read) + the ring-equation bridge `inclA·φ=inclR'·ψ`, replaying
  conj-2d's `hClaimA`/`hgPTI`/`hβapp` TWICE — multi-hundred-LOC, structurally known, NOT an open search.
  PARKED per the armed kill-criterion (no second reprieve); FBC is off the critical path. Resume is a
  user-steer decision; the scaffolds are the launching pad. Do NOT retry within it: monolithic depth-5 β;
  `sections_direct` pivot (illusory); positional `rw`/`simp`/`erw`/`conv` on factor-3
  `(pushforwardComp g' (Spec φ)).hom` under the `X.Modules` diamond.
- **FBC "affine tilde-transport" pivot is ILLUSORY — verified iter-043; do NOT add `sections_direct`.**
  The iter-042-planned bypass (a direct `TensorProduct.induction_on` of `Θ_src⁻¹ ≫ Γ(α) ≫ Θ_tgt` on a
  generator `r'⊗m`, landing on `cancelBaseChange⁻¹` without the conjugate calculus) does NOT bypass the
  section-level mate. In the concrete affine square the inner `g^*(f_*M)`-unit is the `g' = pullback.fst`
  unit — NOT a `Spec`-map — and the geometric unit/counit/pullback have **no element normal form**
  (iter-035, FlatBaseChange.lean:2245). Evaluating `Γ(α)` on a generator forces transit through the tilde
  dictionaries (`pullback_spec_tilde_iso`/`pushforward_spec_tilde_iso`), and "geometric-map-conjugated-by-
  dictionaries = algebraic-map" IS the conjugate intertwining. Concretely `sections_direct` needs
  `base_change_mate_inner_value_eq` (@2061) → `base_change_mate_fstar_reindex_legs` → the open keystone
  `_legs_conj` (@1848). **BOTH routes funnel through the single keystone.** Do NOT formalize
  `pushforward_base_change_mate_sections_direct` (any honest statement is sorry-backed through the
  keystone). The conjugate route is ~90% done (conj-2b/2c/2d + `gstar_counit_transport` /
  `gstar_generator_close` / `extendScalars_inner_value_counit` ALL axiom-clean); the sole open node is the
  keystone's bespoke 5-adjunction-layer `conjugateEquiv adjL adjR` reframing + assembled `β`. This is a
  dedicated multi-hundred-LOC build (or park FBC) — NOT an in-loop polish. FBC `cancelBaseChange` is not a
  dependency of the QUOT/GF/GR lanes; parking it does not block them.
- **FBC `_legs_conj` — factor-3 is UN-COLLAPSIBLE by any positional tactic (iter-044, root cause pinned).**
  Inside the keystone, the coherence factor `(pushforwardComp g' (Spec φ)).hom` is `rfl`-equal to `𝟙` but
  NO positional tactic collapses it: `rw`/`simp only`/`conv_lhs => rw`/`conv in (PATTERN)`/`change`/`erw`
  ALL fail — even a `have h3 := gammaMap_pushforwardComp_hom_eq_id …` whose LHS pretty-prints
  CHARACTER-FOR-CHARACTER identically to the goal still fails `rw [h3]` "did not find an occurrence". Root
  cause = `X.Modules` **instance-path divergence**: `simp only [Functor.map_comp]` produces the factor via
  one `Module`/`Over`-instance synthesis path; `gammaMap_pushforwardComp_hom_eq_id` produces the defeq-but-
  not-syntactic other path. The factor must be ABSORBED into the `conjugateEquiv` recognition (a whiskered
  component), never collapsed. Do NOT spend an iter on a "defeq `change`/`conv`-to-𝟙" step. ALSO ruled out:
  `pullbackPushforward_unit_comp` for the g'-unit reindex (shape mismatch — its middle is
  `P_b(unit_a.app(pullback b N))` but the keystone's `unit_{g'}` applies to `tilde M`). iter-044 landed
  verified `adjL` (DEPTH-2: `(tilde⊣Γ_A).comp (pullback g'⊣push g')` — the Spec-φ layer enters via
  `gammaPushforwardIso φ`, NOT a 3rd `Adjunction.comp`; the recipe's "two layers deeper" was WRONG) +
  `hunitL` (unit-split, `Adjunction.comp_unit_app` + `rfl`). Remaining = `adjR` + comparison `β` + the
  `(conjugateEquiv adjL adjR).injective` discharge via conj-2b/2c/2d. 8-iter wall (037–044).
- **QUOT `subquotient_base_eventuallyZero` `iSupIndep` leaf — RESOLVED iter-020 via route (b).** The
  leaf is closed axiom-clean and the `gradedModule_hilbertSeries_rational` keystone chain is fully
  proved. Route (b) (ambient degree-`i` homogeneous-component membership + the ring-agnostic
  `iSupIndep_map_of_mem_ker_sup` helper) is recorded under Proof Patterns above. **Retain the route-(a)
  warning**: building a κ-linear detector `Φ : Q →ₗ[κ] M⧸N'` via `Submodule.liftQ` is a DEAD END —
  `liftQ` produces an `S = MvPolynomial (Fin r) κ`-semilinear map but `M⧸N'` is only a κ-module
  (scalar-ring clash). Do not revive route (a) for analogous degreewise-independence goals.
- **FBC `base_change_mate_fstar_reindex_legs` assembly — OBVIATED by route swap (iter-019/020); now
  DEAD CODE.** The 6-iter-stuck leg-lock-at-MATCHING wall was resolved not by closing the crux but by
  rendering it unnecessary: the iter-019 `decouple-legs` refactor landed `base_change_mate_domain_read`
  (axiom-clean) which, with the existing `codomain_read`, derives `base_change_mate_section_identity`
  directly modulo Seam-3 `gstar_transpose`. The public `fstar_reindex` apparatus is consumed by nothing
  live (grep → comments only). **Do NOT re-attempt `fstar_reindex` (whole goal OR fine-grained) — it is
  dead code awaiting a removal refactor.** The live FBC crux is now `gstar_transpose`. (The iter-018
  literal-form lock below is part of the same obviated apparatus.)
- **FBC Seam A `base_change_mate_inner_value_eq` — the literal-form-lock RECURRED, now the LIVE FBC wall
  (iter-024).** After the step-(ii) Γ-collapse (`Functor.map_comp ×3` + `simp only
  [gammaMap_pushforwardComp_inv_eq_id, gammaMap_pushforwardCongr_hom, Category.assoc]`), the surviving
  `moduleSpecΓFunctor.map ((pushforwardComp (pullback.fst …) (Spec.map φ)).hom.app …)` factor prints
  **verbatim identical** to the LHS of `gammaMap_pushforwardComp_hom_eq_id` (= the proved atom 2), yet
  `rw`, `simp only`, AND `have h := gammaMap_pushforwardComp_hom_eq_id …; rw [h]` (with `h`'s LHS
  printing the same) ALL fail "did not find an occurrence of the pattern" — invisible implicit-argument
  divergence (`memory/fbc-subst-legs-literal-form-lock`). The 3 atoms are correct but cannot be APPLIED
  BY PATTERN against the locked goal. **DO NOT re-dispatch a Seam A prover on the current thin blueprint
  block** — it churns on this lock. Corrective is a blueprint-writer round prescribing ONE of: (a) a
  `conv`/`Eq.mpr` congruence targeting the factor by POSITION not pattern; or (b) re-derive the inner
  composite via `pullbackPushforward_unit_comp e.hom (Spec.map inclA) (tilde M)` BEFORE the legs lock
  into `pullback.fst/snd` (distribute the `(g')`-unit while still the free composite `e.hom ≫ Spec inclA`),
  so the atoms apply to free-form factors. lean-vs-blueprint-checker `fbc-iter024` flagged the block as
  under-specified on exactly this tactical detail (major). Seam A gates `gstar_transpose`.
  **UPDATE (iter-026): the literal-form lock is BROKEN at the tactic level — `erw` fires where `rw`
  cannot.** Route (b) was executed: the unit expansion now lands POST-`subst` inside
  `base_change_mate_fstar_reindex_legs` via `erw [base_change_mate_fstar_reindex_legs_unitExpand e.hom
  (Spec.map inclA) (tilde M)]` (the leg is defeq there; `erw` matches up to defeq through the invisible
  implicit-arg divergence — see the iter-026 `erw` pattern above). The INLINE pre-subst route on
  `inner_value_eq` stays walled (the leg is `pullback.fst`, only propositionally `hfst`-equal, dependent
  motive). Residual on `_legs`: distribute the four expanded factors via term-mode `…_gammaDistribute`
  (NOT `simp [Functor.map_comp]` — `X.Modules` diamond), UNFOLD `base_change_mate_codomain_read_legs`,
  reassociate, apply the 3 proved `inner_eCancel` atoms, Seam-1 the survivor `η^{Spec ιA}` (~100 LOC,
  now unblocked). Closing `_legs` cascades to `fstar_reindex` → `inner_value_eq` (free `exact`) →
  `gstar_transpose`. The escalation-to-consult is NO LONGER needed.
  **UPDATE (iter-029): the `erw` unlock does NOT extend to the `_legs` cancellation assembly — ALL keyed
  rewriting (incl. `erw`/`conv`/`set`/`dsimp`) is conclusively dead at the residual crux (@1446).** The
  prover verified this iter that even `rw [e2]` of a `rfl`-true fact `e2 : <factor-2 LITERAL copied
  verbatim from the printed goal> = 𝟙 _` STILL reports "did not find pattern", and even
  `rw [Category.comp_id]` cannot find `?f ≫ 𝟙` — every `≫`/`Functor.map` in the goal carries an
  `X.Modules` category/comp instance that is defeq-but-not-reducibly-equal to a fresh elaboration, which
  `kabstract` cannot bridge. Defeq map (each `have … := rfl` typechecks): factor-2 / factor-2-under-Γ / G3
  = `rfl`-trivial `𝟙`; G1, G2, G4 = genuine isos. **The ONLY route is a single hand-built ~100–150 LOC
  proof term**: build each cancellation on a SEPARATELY-elaborated CLEAN term (single instance ⇒ no
  diamond), chain with `congrArg`/`Functor.congr_map`/`.trans`, touch the goal only at the final
  `exact`/`convert … using n` (whose defeq check crosses the diamond). All genuine-content helpers exist +
  proven (`_legs_gammaDistribute` @1304, `inner_eCancel_eUnit/_pushforwardComp/_pullbackComp`
  @1523/1535/1552, `unit_value` @987). **Do NOT re-dispatch any rewriting recipe — assign the assembly
  term; if term-mode ITSELF fails to fire (not budget), effort-break `_legs` into per-atom sub-lemmas.**
  Riders done iter-029: de-privatized the 3 atoms (blueprint pins resolve); fixed 2 false "sorry-free"
  docstrings → "transitively sorry-backed through `gstar_transpose`".
  **UPDATE (iter-031): two NEW structural blockers on `_legs` (not yet attempted) — fix BOTH before any
  term-mode splice round.** (1) **Declaration ordering:** the 3 eCancel atoms
  (`base_change_mate_inner_eCancel_eUnit/_pushforwardComp/_pullbackComp`) and `..._inner_value_eq` are all
  defined AFTER `_legs` in the file, so they are OUT OF SCOPE at the `_legs` sorry (`Unknown identifier`
  confirmed). Either move them (+ `base_change_mate_unit_value`) above `_legs`, OR inline their content
  (≤3 lines each: eUnit via `pullback_isEquivalence_of_iso`; pullbackComp via `(pullbackComp _
  _).hom_inv_id_app`; pushforwardComp via the pre-`_legs` `gammaMap_pushforwardComp_hom_eq_id`). (2)
  **`Eq.mpr` casts:** the RHS codomain read is wrapped in 3 `Eq.mpr` casts from the leg-`subst`, leaving
  the cancellers not in plain composition position — collapse via the concrete-legs
  `base_change_mate_codomain_read` before splicing. iter-031 ADVANCE: a verified `simp only
  [base_change_mate_codomain_read_legs, …]` now unfolds the codomain read + distributes the LHS into
  atomic factors (build green); re-confirmed keyed `rw`/`simp`/`erw` dead even on the trivial trailing
  `pushforwardComp` factor. This is the documented budget boundary (~13 iters, STRATEGY Open Q2) — if the
  term-mode splice itself fails after the ordering+cast fix, the iter-032 fork is ModuleCat re-encoding vs
  user escalation.
  **UPDATE (iter-033): direct-on-sections is EXHAUSTED — the "one final round" override FAILED; PIVOT to
  ModuleCat re-encoding (do NOT re-assign any direct-on-sections/wrapper/prove round on `_legs`).** The
  ordering+cast fix WAS applied: the eCancel content is now in scope (inlined / pre-`_legs` atoms) and the
  trailing transparent `pushforwardComp(g', Spec φ)` factor collapses to `𝟙` via a term-mode `congrArg`
  splice (green). The residual is NOT closable by the explicit-factor route: it is **cross-layer
  naturality** — the F2 (`e.hom`-unit) and F3 (`pullbackComp(e,inclA)`) cancellers live in the
  `(Spec φ)_* ⋙ Γ_R` image (over `Spec R`) while their codomain-read partners live in the
  `Γ_R' → gammaPushforwardIso ψ → restrictScalars ψ` image (over `Spec R'`); cancelling them needs the
  naturality of `gammaPushforwardIso ψ` as a `conjugateEquiv`/mate coherence, which the term-mode
  explicit-factor route cannot express. This satisfies the iter-031 disproof condition ("if the term-mode
  splice itself fails after the ordering+cast fix"). **iter-034 executes STRATEGY Open Q2 arm (a): re-encode
  the base-change map at the ModuleCat/SheafOfModules level so the `X.Modules` diamond never forms.** This
  is a refactor (likely needs a refactor/effort-breaker pass first), not a prove round. `gstar_transpose`
  @1744 is transitively gated on `_legs` (same crux) — do not assign in isolation. Handoff:
  `informal/base_change_mate_fstar_reindex_legs.md`.
  **UPDATE (iter-035): the conjugate re-encoding round ran (effort-breaker atomized chain) and CLOSED
  NOTHING axiom-clean on the crux — the conjugate route is now EXHAUSTED; tripwire FIRED.** 7 axiom-clean
  decls landed (conj-1a `base_change_mate_codomain_read_legs_conj` + conj-1b `_eq`, conj-2c
  `base_change_mate_reindex_conj_pushforwardCollapse`, the `conjPullbackFactor`/`codomain_read_legs_param`
  param-then-`rfl` helpers) and `_legs` became a sorry-free thin wrapper — but the residual `sorry` only
  MOVED into the named conjugate identity conj-2a (`base_change_mate_fstar_reindex_legs_conj` @~1700;
  `_legs` is now TRANSITIVELY sorry-backed through it, confirmed by `lean_verify` sorryAx). The exact
  blocker is unchanged from the 5-iter stall: conj-2a's `subst hfst/hsnd` reduction to the affine model
  lands, but to apply `conjugateEquiv.injective` the whole `gammaPushforwardTildeIso`/`restrictScalars ψ`
  section-level LHS must first be reframed as a SINGLE `conjugateEquiv(…)` component — NOT a missing
  Mathlib lemma; it is what the explicit-factor/section vehicle cannot express (conj-2b/2d cannot even be
  typed until that normal form exists). **iter-036 executes the pre-scheduled affine-local explicit-inverse
  + element-`ext` refactor (STRATEGY Open Q2 fallback / PROGRESS Iter-036 ramp). Do NOT re-assign any
  conjugate/section prove round on `_legs` or conj-2a.** The conjugate scaffolding (conj-1a/1b/2c + param
  helpers) is route-independent proven content that survives the pivot. (lean-auditor `iter035`: FBC has 4
  independent sorry sites — conj-2a @1700, `gstar_transpose` @2122, affine @2303, FBC-B target @2325 — NOT
  one; track them separately.)
- **FBC mate lemmas — dependent leg-equality proofs re-fire the motive wall on re-fold (iter-018).** In
  `base_change_mate_*_legs` (Seam 2/3) the proof does `subst hfst; subst hsnd`, which freezes the
  pullback legs in LITERAL form `(pullbackSpecIso ↑R ↑A ↑R').hom ≫ Spec.map (CommRingCat.ofHom …)`.
  `set e/inclA` silently fail to fold these in the goal; `rw [← he]` / `rw [← hinclA]` fail with "motive
  is not type correct" (the codomain-read carries the leg-equality PROOFS `hfst`/`hsnd` whose types
  mention the literal leg term, so abstracting it yields an ill-typed motive). Consequence: a helper like
  `pullbackPushforward_unit_comp` stated in `e`-form NEVER matches the goal. Fix: literalize the helper
  with `rw [he, hinclA] at key`, never the goal. Even then `rw [← key]` fails (key's RHS is not a goal
  subterm) — the unit must be obtained by INVERTING key (`Iso.inv_hom_id_app`/`Functor.map_id`), not by
  rewriting. See `memory/fbc-subst-legs-literal-form-lock.md`.

- **Graded quotient/subtype `DirectSum.IsInternal` elaborator runaway (iter-015, QUOT graded-API
  G1–G4).** Any goal whose TYPE mentions `DirectSum.IsInternal`, `Submodule.map_iSup`, or an
  `iSup` over a family of `Submodule R ↥p` / `Submodule R (M ⧸ p)` triggers a
  `(deterministic) timeout at isDefEq/whnf` that survives `maxHeartbeats` bumps to 2M+. This
  blocked the bundled G1 (`homogeneousSubmodule_isInternal`) and all of G2–G4 this iter.
  Corrective is NOT a bigger budget: keep every graded fact stated in the AMBIENT `M`
  (independence + supremum halves over `M`, as the two landed G1 sub-lemmas do) and only
  transport to `↥p` / `M⧸p` through a thin `LinearEquiv` at the very end — or get a
  mathlib-analogist consult on the canonical way Mathlib builds `Decomposition` on a
  homogeneous submodule before re-dispatching. See `memory/graded-quotient-module-isdefeq-pathology.md`.

- **`pushforward_base_change_mate_cancelBaseChange` (FBC-A mate trace):** parent's direct proof
  sorry-free; L4 chain decomposed (iter-004). (i) `base_change_mate_regroupEquiv` — **FULLY PROVED,
  axiom-clean iter-011.** Both `r' • 0` zero-branches (the transparent-instance wall open since
  iter-006) closed via `erw [TensorProduct.zero_tmul]` — the route-(b) retype was NOT needed (see the
  iter-011 `erw [TensorProduct.zero_tmul]` pattern above). The `eT` identity bridge stays essential;
  `cancelBaseChange`-as-core was attempted and abandoned (diamond). No longer a blocker. (NOTE: the
  blueprint prose for `lem:base_change_mate_regroupEquiv` still describes the
  `lem:base_change_regroup_linearEquiv` helper route, not the landed inline build — reconcile via a
  writer, lvb-fbc iter-011.) (ii) `base_change_mate_section_identity` (renamed from
  `…generator_trace_eq` iter-011) — the genuine mate-unwinding crux. RHS is now COMPUTABLE
  (regroupEquiv sorry-free; `regroupEquiv.inv (1⊗ₜx) = (1⊗1)⊗x`); the LHS adjoint-mate coherence
  (`pushforwardBaseChangeMap` through `moduleSpecΓFunctor.map` + the two tilde dictionaries over the
  generic pullback square) is the single `sorry` (line 1011), Mathlib-absent. **The blueprint
  section-identity sketch is UNDER-SPECIFIED on the formalization path (lvb-fbc iter-011 major) — a
  raw re-dispatch will churn.** Have a writer decompose the LHS into the 3 named sub-lemmas: (a)
  `pullbackPushforwardAdjunction` unit value = base-change unit; (b) `f_* = restrictScalars φ` reindex
  via the pushforward pseudofunctor identities; (c) `(g*⊣g_*)` transpose for `ψ`. Do NOT re-assign the
  monolithic sorry without that writer round. **UPDATE (iter-012): DECOMPOSED + GLUE VERIFIED.**
  `base_change_mate_section_identity` is now **`sorry`-free in its own body** (closed by
  `unfold pushforwardBaseChangeMap; rw [Adjunction.homEquiv_counit]; exact …gstar_transpose`); the RHS
  helper `base_change_mate_inner_value` (ρ = `m ↦ (1⊗1)⊗m`) is **PROVEN axiom-clean** (transport across
  `inclA∘φ = inclR'∘ψ` via `letI φ.hom.toAlgebra` + `Algebra.algebraMap_eq_smul_one` + `TensorProduct.smul_tmul`).
  The 3 deep coherences are now isolated `sorry`s: `base_change_mate_unit_value` (Seam 1, square-free base —
  try `Adjunction.conjugateEquiv` unit-coherence, NOT `ext`: `conjugateIsoEquiv` element actions are opaque),
  `_fstar_reindex` (Seam 2, +`pullback_fst_snd_specMap_tensor`), `_gstar_transpose` (Seam 3, partial body
  `rw [Functor.map_comp]`, +`pullback_spec_tilde_iso`). Close in order; Seam 3 lands `section_identity`,
  `generator_trace`, `cancelBaseChange`. No deception (lean-auditor + lvb-fbc iter-012 confirm).
  **UPDATE (iter-014): Seam 1 `base_change_mate_unit_value` CLOSED, axiom-clean** via the 4-move
  conjugate calculus (see the `erw`/`← Functor.comp_map` pattern above). **Next FBC critical path =
  Seam 2 `base_change_mate_fstar_reindex`** (generic-pullback-square pseudofunctor reindex — a
  DIFFERENT construction from Seam 1, not an adjunction-unit identity): mirror
  `base_change_mate_codomain_read`'s leg-identification scaffold (`pullback_fst_snd_specMap_tensor` +
  `pullbackSpecIso` + `unit_iso`), transport the 3 pushforward coherences, feed Seam 1. Seam 2 → Seam 3
  → cascades. Expect the same `erw` discipline.
  **UPDATE (iter-016): the Seam-2 leg-reindex ENGINE is proved** (`pullbackPushforward_unit_comp`,
  axiom-clean — see the pattern above) and wired into the body as `have key`, but the Seam-2 `sorry`
  PERSISTS. The residual is NOT the engine: the two pullback legs sit in **dependent positions** (the
  adjunction index, the `(IsPullback…).w` proof inside `pushforwardCongr`, the `gammaPushforwardIso`
  arg, and — load-bearing — inside the TYPE of the opaque def `base_change_mate_codomain_read`), so
  `rw [hfst]`/`rw [hsnd]` both fail `motive is not type correct` (`generalize`-ing the `.w` proof frees
  only the `pushforwardCongr` slot). The outstanding obligation is a multi-hundred-LOC restructure:
  restate the chain AND `codomain_read` with the legs as `subst`-able variables `g' f'`, then after
  `subst` the Γ-transparent coherences collapse to `base_change_mate_inner_value` via Seam 1. **The FBC
  chapter under-specifies this restructure AND the Seam-3 `conjugateEquiv`+`homEquiv_counit` coherence
  (lvb-fbc iter-016 must-fix ×2) — blueprint-writer round required before the next FBC prover.**
- **GF L3 chain — CLOSED (iter-004).** L3a/L3b/L3c + the assembly
  `exists_free_localizationAway_of_shortExact` all proved axiom-clean. No longer a blocker. The
  hard leaf was L3b (`free_localizationAway_of_free_of_eq_mul`, 553-effort) — see the
  `IsBaseChange.of_comp` pattern above.
- **GF L4 `exists_localizationAway_finite_mvPolynomial` — Step 2 residue, denominator-clear primitive
  now available (iter-008).** Step 1 (Noether normalisation over `K`) done; Step 2 still needs the
  Noether-normalisation descent (lift `b̄_j ∈ B_K` to `b_j ∈ B`, module-finiteness descent `K → A_g`),
  but `gf_clear_one_denominator` (PROVED axiom-clean iter-008) now supplies the per-equation
  denominator-clearing primitive for the Finset-fold. Effort-break the descent as its own lemma.
- **GF generic-rank dévissage — 2 sub-lemmas PROVED iter-008, residue isolated to `gf_torsion_reindex`.**
  `gf_generic_rank_ses` (the generic-rank SES `0→P^{⊕m}→N→T→0`) and `gf_clear_one_denominator` both
  landed **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, re-verified via `lean_verify`).
  L5 `exists_free_localizationAway_polynomial` is restructured to
  `Nat.strong_induction_on generalizing A N` (the base-domain-generalizing fix — supersedes the
  iter-006 `generalizing N` form; shared universe `(A N : Type u)`, see the pattern above); the SES
  extraction via `gf_generic_rank_ses` typechecks. **The remaining L5 inner `sorry` is gated ONLY on**
  `gf_torsion_reindex` (created iter-008, `sorry`) + motive plumbing on `N ⧸ range φ` + the `A_g → A`
  witness descent + the L3 splice. `gf_torsion_reindex` is the Mathlib-absent core: single-variable
  Nagata change-of-variables + division algorithm + leading-coeff denominator-clear over `MvPolynomial`
  (first step exists: `Submodule.annihilator_top_inter_nonZeroDivisors`). **EFFORT-BREAK EXECUTED +
  3 sub-lemmas PROVED axiom-clean iter-011:** `gf_torsion_annihilator` (L5b.1, NZD annihilator),
  `gf_nagata_monic_lastVar` (L5b.2, the domain-adapted Nagata transform — see the domain-adaptation
  pattern above), and `mvPolynomial_quotient_finite_of_monic_lastVar` (L5b.3, the shared
  single-variable elimination engine, encoded as `RingHom.Finite`). They chain in `gf_torsion_reindex`
  with the RIGHT TYPES (validating the signatures); ONLY the final assembly `sorry` (line 949) remains
  — the localization/quotient-transport plumbing (double-localization of `T`, `IsTorsionBySet` quotient
  action `Module.IsTorsionBySet.module`, loc-commutes-quotient, `Module.Finite.of_restrictScalars_finite`).
  Each step's Mathlib anchor is scouted. This is the GF critical path; effort-break the plumbing if a
  single pass stalls on diamonds. (L5b.3 is also the engine L4 Step 2 needs — build-once-reuse-twice
  realized.) **UPDATE (iter-012): hard finiteness LANDED, residue is bookkeeping (still 1 sorry).**
  The plumbing pivoted to the **P-localisation** `Tg' := LocalizedModule MC T` (`MC = map C (powers g) ⊆ P`)
  because the goal's A-localisation `LocalizedModule (powers g) T` gets no P-module structure
  (`inferInstance` fails). VERIFIED + compiling: `IsLocalization MC P_g`, `Module.Finite P_g Tg'`,
  and `Module.Finite (P_g⧸span{Fg}) Tg'`. The remaining `sorry` is steps (a)-(e): base-change `e`→`ebar`,
  quotient transport, `Module.Finite R (P_g⧸span)`/`R Tg'`, and **descend** P-loc → the goal's A-loc.
  This chain blew `isDefEq` heartbeats assembled inline (see the inline-instance-stacking pattern above) —
  **iter-013 must effort-break (a)-(e) into helper lemmas first**, NOT re-dispatch the monolith. Missing
  glue for (e): a descent lemma `IsLocalizedModule MC f` (over P) → `IsLocalizedModule (powers g) (f.restrictScalars A)`
  (over A); if absent, build the `A_g`-equiv from `IsLocalizedModule.mk'`/`surj`. Per the iter-012 plan,
  a non-close also escalates to a mathlib-analogist consult on the transport diamonds.
  **UPDATE (iter-014): `gf_torsion_reindex` CLOSED, axiom-clean — no longer a blocker.** The (a)–(e)
  transport was factored into 5 standalone helpers (see the `ringEquivOfRingEquiv` / `OreLocalization`-diamond
  pattern above); the canonical-`A_g`-action diamond was the genuine wall, resolved via
  `extendScalarsOfIsLocalization`. **The residual GF critical path is now L5
  `exists_free_localizationAway_polynomial`** (line ~1267, unblocked): its 5-step assembly (equip
  `T=N⧸range φ`; `gf_torsion_reindex`; base-generalised IH at `A_g`; descend `A_g→A` via
  `free_localizationAway_of_free_of_eq_mul`; splice the localised SES) is dispatchable — but a
  blueprint-writer must first expand the under-specified "Transitivity" sketch + add the 5 helper
  `\lean{}` blocks (lvb-gf iter-014 MAJOR), or the L5 prover churns on a thin guide.
  **UPDATE (iter-016): the tower-descent helper `free_localizationAway_of_away_tower` is CLOSED
  axiom-clean** (the `IsBaseChange.comp` / `Module.Basis.mapCoeffs` pattern above), and L5's 5-line
  assembly is mathematically complete and recorded verbatim in-code. The L5 `sorry` is now ISOLATED to a
  **do-not-retry Lean blocker**: an `OreLocalization` instance-**presentation** diamond between
  `gf_torsion_reindex`'s IH output and the helper's input on `(N⧸range φ)_g`. Three layers are defeq but
  NOT instance-transparent-equal — `CommSemiring A_g` (`OreLocalization.instCommSemiring` vs
  `CommRing.toCommSemiring`), `AddCommMonoid T_g`, `Module/SMul A_g T_g` (`OreLocalization.instModule`
  vs `hmod2`/`DistribMulAction.toDistribSMul.toSMul`). FOUR consumer-site bridging attempts all failed
  (`@IH`-explicit, `letI`/`haveI` ambient, re-ascribe `htower` against `hmod2.toSMul`/`instAg.toSMul`,
  full-defeq `exact`) — even `hmod2.toSMul =?= OreLocalization.instSMul` fails the `haveI` ascription.
  **CORRECTIVE (do NOT re-dispatch a raw L5 prover / bump heartbeats): fix at the PRODUCER** — make
  `gf_torsion_reindex` emit its conclusion over the canonical `OreLocalization.*` instances (final
  `exact` / existential binders, ~lines 1245–1252), OR restate the helper's `hfree` over the
  `CommRing.toCommSemiring`/`hmod2` presentation; then the recorded assembly closes verbatim. **General
  lesson: an `OreLocalization` instance-presentation diamond is irreducible at the *consumer* site —
  align the *producer*'s emitted instances instead.**
  **UPDATE (iter-017): L5 `exists_free_localizationAway_polynomial` CLOSED, axiom-clean — diamond
  RESOLVED, no longer a blocker.** The producer-side fix was even cleaner than "emit canonical
  instances": the offending 6th existential (`Module A_g T_g`) was *canonical* (`inferInstance`), so it
  was DROPPED from `gf_torsion_reindex` entirely and the consumer synthesises it — a single instance in
  play, no diamond. See the "Don't bundle canonical instances as existential witnesses" pattern above.
  **The GF critical path is now L4 `exists_localizationAway_finite_mvPolynomial`** (Noether-normalisation
  descent K→A_g: algebraic-independence descent for φ-injectivity + Finset-fold of
  `gf_clear_one_denominator` for module-finiteness — both scouted, effort-break before dispatch).
  **UPDATE (iter-019): L4 INJECTIVITY HALF CLOSED, axiom-clean — only the module-finiteness conjunct
  remains (line 754).** Witness `g := g0` (F3 common denominator); built `ν : B_g→B_K`, `ψ : A_g→K`
  (both `IsLocalization.lift`, injective via the new `isLocalization_lift_injective` helper +
  `IsLocalization.injective`), generators `b_j` with `ν(b_j)=gK(X_j)`, `φ := aeval b`, the compatibility
  square `hsquare` (`IsLocalization.ringHom_ext (powers g0)` → A-level, both sides collapse to
  `algebraMap A B_K a0`), and `Function.Injective φ` via `ν∘φ = gK∘(map ψ)` (composite of injectives,
  `Function.Injective.of_comp`). Gotchas: `set φ … with hφ_def` + `simp [hφ_def, aeval_X]` for the
  `b`-vs-`φ` defeq (NOT `change`); the nested `Away` localisations need
  `synthInstance.maxHeartbeats 1000000` + `maxHeartbeats 4000000` (mirrors `gf_torsion_reindex`,
  lean-auditor-legitimate). **Finiteness leaf**: refine witness to `g := g0*g1` (`g1≠0` clearing
  `K[X]`-coeffs of the monic integral-dependence equations of generators `σ`; fold
  `gf_clear_one_denominator`), then `Algebra.finite_adjoin_of_finite_of_isIntegral` [verified]; all
  injectivity scaffolding transfers verbatim (unit only needs `g0 ∣ g`). **Negative: NO Mathlib
  generic-fibre→basic-open finiteness descent** (`Module.Finite.of_localizationSpan*` are local→global,
  wrong direction) — the per-generator integral-clearing (Nitsure) is required, no shortcut. Needs a
  blueprint-writer Step-3 round (pin the `g0→g0*g1` recipe) before the prove pass.
  **UPDATE (iter-021): L4 `exists_localizationAway_finite_mvPolynomial` CLOSED, axiom-clean — no
  longer a blocker.** The `g := g0·g1` witness + the per-generator
  `IsIntegral.exists_multiple_integral_of_isLocalization` route landed on the first genuine attempt
  (see the "One-call denominator clearing … EXECUTED iter-021" pattern above). L1/L4/L5 are now ALL
  closed axiom-clean. The GF critical path is now `genericFlatnessAlgebraic` (below).
- **`genericFlatnessAlgebraic` dévissage assembly — CLOSED, axiom-clean (iter-022); no longer a
  blocker.** The full §4 dévissage landed (re-verified `{propext, Classical.choice, Quot.sound}`). The
  ring↔module-localisation bridge that was the last residual resolved NOT by a uniqueness-iso pin but by
  staying on the AMBIENT instances: `IsLocalizedModule.iso (powers g) (IsScalarTower.toAlgHom A C Cg).toLinearMap`
  (`Algebra A Cg` / `IsScalarTower A C Cg` / `IsLocalization (algebraMapSubmonoid …) Cg` all auto-found)
  upgraded to `A_g`-linear by `LinearEquiv.extendScalarsOfIsLocalization`, then `Module.Free.of_equiv`
  → `free_localizationAway_of_away_tower`. Two enabling changes (both NON-protected, no outside
  consumers): L4 gained a 4th existential conjunct (tower-compatibility, see pattern below) and the decl
  narrowed to single-universe `(A B M : Type u)`. **With L1/L4/L5 + this, the entire GF *algebraic*
  route is DONE.** Only the geometric `genericFlatness` @2208 remains (owes a finite-affine-cover
  chapter section). Honest `set_option maxHeartbeats 1600000` + `synthInstance.maxHeartbeats 400000`
  (lean-auditor-judged justified). See the ambient-instance-diamond + strengthen-the-existential
  patterns below.
- **`affineBaseChange_pushforward_iso` affine-reduction (obligation 1):** Mathlib-absent
  restriction-compatibility of `pushforwardBaseChangeMap`; gated on the mate lemma above.
  Keep deferred until L4 lands; do not assign as an independent target.
- **Geometric `genericFlatness` — blueprint-blocked on two missing-Mathlib bridges (iter-023).** The
  signature is now CORRECT (`[LocallyOfFiniteType p] [QuasiCompact p]`, re-signed this iter — decl not
  protected, no downstream consumers) and the algebraic-input instances for `A := Γ(S,U₀)` are
  discharged, but the body's `sorry` (@2264) bottoms out at two genuine missing-Mathlib lemmas that must
  be BLUEPRINTED first (do NOT re-dispatch a GF-geo prover expecting a full close until they exist —
  the witness `V` cannot even be constructed without G1):
  - **G1** `∀ {W}, IsAffineOpen W → Module.Finite Γ(X,W) Γ(F,W)` (quasicoherent + finite-type ⇒ finite
    section module over affine; the affine-local `F|_W ≅ (Γ(F,W))~` identification with finiteness
    preserved — Mathlib has only the abstract `SheafOfModules.IsFiniteType`/`IsQuasicoherent`
    local-generator predicates).
  - **G3** flat-locality assembly: per-patch freeness on a finite affine source cover ⇒ flatness of
    `Γ(F,W)` over `Γ(S,U)` for arbitrary affine `U ≤ V`, `W ≤ p⁻¹U`. Ingredients present
    (`Module.Flat.of_free`, `Module.flat_of_isLocalized_maximal`); missing = the geometric glue across
    the cover + base-restriction along `U ↪ V`.
  Verified-present collapsing tools for the assembly once G1/G3 land: `Scheme.Hom.isCompact_preimage`
  (finite affine cover, now valid via `[QuasiCompact p]`), `LocallyOfFiniteType.finiteType_appLE`
  (per-patch finite-type algebra), `IsAffineOpen.basicOpen` (witness `V := D(∏fⱼ)`).

- **FBC `base_change_mate_fstar_reindex_legs` @1445 — the LIVE root crux, blocked by the `X.Modules`
  instance diamond (iter-028; supersedes the iter-024 literal-form-lock blocker above for the via-`_legs`
  route).** After the iter-026 `erw [...unitExpand]` unlock the eCancel telescoping's first step must
  collapse the surviving `Γ(pushforwardComp(g',Spec φ).hom)` factor. The collapse fact IS available and
  cheaply provable (`hpfc := gammaMap_pushforwardComp_hom_eq_id _ _ _`, elaborates with no timeout — only
  assigns the leg metavariables), but it **cannot be applied**: the fact lives over the COMPOSED functor
  `pushforward(LEG) ⋙ pushforward(Spec φ)` while the goal factor (from the `rw [Functor.map_comp]` split)
  carries the NESTED-`obj` form of the same object — defeq, not syntactic. Verified dead THIS iter (4
  routes): `rw [gammaMap_pushforwardComp_hom_eq_id]` ("no pattern"), `erw [...]` (whnf timeout at 4M),
  `rw [hpfc]` ("no pattern"), `simp only [hpfc]` ("no progress"). **Do NOT assign a 3rd helper round on
  the same recipe** (progress-critic flagged FBC CHURNING). The escalation (planner's tripwire) is a
  **mathlib-analogist consult** on a diamond-robust term-mode congruence (carry `congrArg`/`Functor.map_comp`
  through the whole `Γ∘(Spec φ)_*` composite, no head-symbol `rw`). `gstar_transpose` @1817 sits behind the
  same diamond + is gated on `_legs`. NOTE: `inner_value_eq` was consolidated onto this crux this iter
  (`exact base_change_mate_fstar_reindex ψ φ M`) — the whole FBC Seam-3 residual is now this ONE telescoping.
- **QUOT G1-core collapsed to a single lemma `isIso_fromTildeΓ_of_isQuasicoherent` (iter-028).** The file
  already carries (axiom-clean, iter-026) `isIso_fromTildeΓ_iff_isLocalizedModule_restrict`, so
  **G1-core ≡ gap1 ≡ the single statement** `∀ {R} (M : (Spec R).Modules) [M.IsQuasicoherent], IsIso M.fromTildeΓ`.
  The Route-F "3-field constructor" is OVER-DECOMPOSED: `surj`/`exists_of_eq` are already delivered for the
  iso case by `isLocalizedModule_restrict_of_isIso_fromTildeΓ`. The single irreducible content is the
  `QCoh(Spec R) ≃ Mod R` essential-image gap — verified by source-grep that Mathlib has NO bridge
  (`IsQuasicoherent → IsIso fromTildeΓ`, `→ tilde.essImage`, global-generation-on-compact, or
  global-presentation-from-quasicoherent all absent). **Do NOT re-assign the full G1-core target.** Dispatch
  the named Step-1 sub-build `exists_isIso_fromTildeΓ_basicOpen_cover` (finite basic-open tilde cover from
  `QuasicoherentData` via `PrimeSpectrum.isBasis_basic_opens` + `CompactSpace` + presentation transport
  across `D(g) ≅ Spec R_g` — the site-`over` ↔ scheme-pullback bridge), then the Mayer–Vietoris gluing
  induction (port `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`, QuasiSeparated.lean:306, via
  `existsUnique_gluing`/`eq_of_locally_eq'`). GF-geo @2264 stays gated behind this.
- **FBC `gstar_transpose` step (a) ≡ `_legs_conj` is a SINGLE structural wall — confirmed iter-037,
  do NOT assign another assembly/helper round.** The iter-037 "all atoms proved, just glue" assembly pass
  closed nothing and landed no standalone compiling step-(a) lemma → the pre-set tripwire FIRED. Verified
  this iter that step (a) (inline reindex `Γ_R(θ_in) = ρ`) and the crux `base_change_mate_fstar_reindex_legs_conj`
  (@1647, sorry @1700) are the SAME **dependent-motive obstruction**: `pullback.fst` is only *propositionally*
  `e.hom ≫ Spec ιA`, the codomain-read bakes the leg into its TYPE, so `rw [hfst]`/`subst` (and `rw [← hW]`
  on the main goal) fail "motive is not type correct". The parametrised-leg conjugate discharge needs three
  UNBUILT pieces — the conjugate-injective **reframing keystone** (express the post-`subst` section composite
  as ONE `conjugateEquiv` component so `.injective`/`.surjective` apply), conj-2b `…_reindex_conj_pullbackLeg`,
  conj-2d `…_reindex_conj_crossLayer` (conj-2c @1626 is proved). Building conj-2b/2d in isolation is cosmetic
  until the reframing lands. Step (c) `rw [← Functor.map_comp]` Γ-fusion verified, but the ~100-LOC
  `huce`-substitution glue is unbuilt + off the blind-`rw` route. **Corrective (enforced):** iter-038
  dispatches a `mathlib-analogist` (cross-domain) on the reframing keystone — NOT another assembly/conjugate/
  section prove round on `_legs_conj`/step (a).
  **UPDATE (iter-039): the supporting legs are now ALL BUILT — and the KILL-CRITERION FIRED.** conj-2b
  `base_change_mate_reindex_conj_pullbackLeg` (one-liner: `exact
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _`, once stated at FREE legs `f g` not the
  specialized `e∘Spec ι` composites) and conj-2d `base_change_mate_reindex_conj_crossLayer` (ring-map-general
  port of Seam-1 `base_change_mate_unit_value`: `erw [reassoc_of% huce]` + simp on the two tilde dictionaries,
  `maxHeartbeats 4000000`, controlled `rfl` at `hpullinv`) both landed axiom-clean. With conj-2c already
  proved, `_legs_conj` is now a **pure reframing obstruction — every leg in hand, no missing ingredient** —
  and the single-`conjugateEquiv`-component reframing STILL did not close (sorry now @1822). Per the iter-039
  planner's armed kill-criterion this is the genuine wall after THREE consecutive resisting iters (037
  assembly / 038 analogist / 039 prover). **DO NOT run another conjugate/assembly/reframing round on
  `_legs_conj`.** iter-040 pivots to the fallback: (A) reopen the element-`ext`/explicit-inverse route now
  using conj-2b/2c/2d as the change-of-rings dictionary (the dictionary whose absence sank iter-035's
  element-`ext`), OR (B) a `refactor`-subagent rebuild of the `_legs` comparison from `leftAdjointCompIso`
  primitives. Recommend an api-alignment analogist consult ("section composite ↔ single conjugateEquiv value"
  typing — which `adjL`/`adjR` to pin) to choose A vs B before committing.
  **UPDATE (iter-040→041): the conjugate route is EXHAUSTED in-loop.** iter-040's api-alignment analogist
  chose **Fallback B** (layer-by-layer conjugate transport via `conjugateEquiv_symm_comp` + whiskering, recipe
  in `analogies/fbc-legs-conj-injective-route.md`); element-`ext` (Fallback A) was dropped as the iter-035
  dead end. iter-041 ran Fallback B — the FINAL in-loop conjugate round — and it made VERIFIED partial
  progress (the Γ-collapse `simp only [Functor.map_comp, Category.assoc, gammaMap_pushforwardComp_inv_eq_id,
  gammaMap_pushforwardCongr_hom]` now lands in-proof, collapsing 2 of 3 transparent coherences) but did NOT
  close `_legs_conj`. The HEAVY crux S2 (recognise the cross-layer composite as a `(conjugateEquiv adjL
  adjR).symm β` value spanning strictly MORE adjunction layers than conj-2d's two-pair model + the assembled
  `β`) has now resisted 5 iters (037–041); it is a large bespoke construction, NOT a missing lemma. New
  sub-blocker: the `(pushforwardComp g' (Spec φ)).hom` factor is `rfl`-`𝟙` yet resists `simp`/`rw`
  matching asymmetrically with the `.inv` form (needs a diamond-safe `change`/`conv`, not `erw`). **DECISION
  (armed protocol): NO further conjugate/analogist rounds on `_legs_conj`.** The pivot is the affine
  **tilde-transport** route bypassing `gstar_transpose` at the affine-local level (structurally different;
  needs a new blueprint section + scaffold + user steer). Escalated on TO_USER.md.

### Process notes

- **HARD GATE works as intended.** iter-001 correctly deferred all prover dispatch: no chapter
  was complete+correct and the FBC chapter was mid-pivot. Deferring a no-faithful-work iter is
  the sanctioned outcome, not a stall — provers need real signatures + a passing blueprint gate,
  neither of which existed at iter-001 entry.
- **Frontier placeholders ≠ ready.** A `dag-query frontier` node whose `\lean{...}` is
  `AlgebraicGeometry.TODO.*` is a scaffold objective, not a fill-the-sorry objective. Scaffold
  the real signature before treating it as prover-ready.
- **Blueprint-adequacy gates the prover, not just blueprint-correctness.** iter-002's GF
  lane passed the HARD GATE (complete+correct) yet the lean-vs-blueprint-checker found both
  proof blocks too thin to close the sorries (no named Lean APIs). A `complete+correct`
  blueprint can still be an inadequate *proving guide* — run the checker post-prover and act
  on its blueprint-adequacy findings before re-dispatching the same lane.
- **`CategoryTheory.Sheaf.val` is deprecated** at this pin (use `ObjectProperty.obj`); 22
  inherited sites in `Cohomology/FlatBaseChange.lean` emit warnings. Cosmetic; clear in a
  refactor pass when the file is next owned.
- **Blueprint-gap blocks the prover honestly (iter-008).** A `\lean{}`-pinned sub-lemma with prose
  but no `% LEAN SIGNATURE` block is NOT prover-ready: a good prover declines to guess the Lean type
  (avoiding hollow/mistyped decls) and the lane stalls. iter-008's FBC `generator_trace_eq` blocked
  exactly here (3 mate-trace sub-lemmas). Author `% LEAN SIGNATURE`s in the same iter you intend to
  dispatch the consumer.
- **`sync_leanok` can run against an intermediate non-green tree (iter-008).** The GF chapter lost ALL
  `\leanok` (sync `removed: 12`, sha `c97d3dd` absent from `git log`) even though its lemmas verify
  axiom-clean on the final green tree. Treat a `\leanok` mass-removal that contradicts `lean_verify`
  as a sync-timing artifact, NOT laundering or regression — a clean re-run on the green tree restores
  it. The review agent cannot touch `\leanok`; surface to the planner.
- **A dispatched prover lane can deliver zero output (iter-008).** The GR-cells (`gr_transition`) lane
  was assigned but committed no edits and wrote no task_result (it appears in `provers-combined.jsonl`
  as reads/searches only). Check `attempts_raw.jsonl` `files_edited` against the dispatched objective
  list; an assigned-but-untouched lane should be explicitly re-dispatched or de-scoped, not left to
  silently consume budget.

- **`private` decls with public `\lean{}` pins silently break `sync_leanok` (recurring; iters
  018/019/020).** A `private` Lean declaration gets name-mangled (`_private.…`), so a blueprint
  `\lean{Namespace.foo}` pin to it never resolves and `sync_leanok` cannot mark its `\leanok` — the
  dashboard under-reports. Live instances: 11 GF Nagata-machinery helpers (FlatteningStratification.lean
  `section NagataNormalization`) + the QUOT `IsRatHilb` toolkit + 2 unmatched QUOT helpers. Fix = a
  `refactor` de-`private` pass (recommended; the decls are already documented publicly in the blueprint)
  OR drop the pins to informal references. Until then, a missing `\leanok` on these is a tracking
  artifact, NOT a regression — confirm via `lean_verify` on the green tree.
- **sync_leanok skipped the ENTIRE GF chapter (iter-021 — broader than the private-pin debt).**
  `sync_leanok-state.json` for iter-021 (sha `9834fa4`) lists `chapters_touched: [Picard_QuotScheme.tex]`
  only; `Picard_FlatteningStratification.tex` has **0** `\leanok` markers across ALL blocks — including
  L4 (closed iter-021), L5 (iter-017), `isLocalization_lift_injective` (iter-019), all **public**,
  sorry-free, axiom-clean theorems. So this is NOT just the private-name-mangling issue above (public
  decls are unmarked too): the sync appears to skip the GF chapter wholesale. The dashboard materially
  under-reports GF progress. `\leanok` is sync's domain (not the review agent's) — flagged for the
  sync owner / planner to investigate the chapter-scan / decl→file resolution. Confirm GF closures via
  `lean_verify`, NOT the dashboard, until fixed.
  **UPDATE (iter-022): RECURRED — now systemic, with a strong root-cause hypothesis.** sync ran
  (`iter:22, sha:7e2ae05, added:0, removed:0, chapters_touched:[]`) yet `Picard_FlatteningStratification.tex`
  still has **0 `\leanok` across 43 `\lean{}` pins**, despite `genericFlatnessAlgebraic` (public, @1981)
  AND `exists_localizationAway_finite_mvPolynomial` (public) being `sorry`-free + axiom-clean this iter
  with correct entries in `blueprint/lean_decls`. The all-or-nothing 0/43 pattern + the project's known
  `lake env lean` single-file instance-diamond pathology (memory `lake-build-vs-env-lean-spurious-errors`)
  strongly suggest **sync_leanok verifies via single-file `lake env lean`, which spuriously fails THIS
  file, so no decl in the chapter is ever marked ok**. Recommendation to the sync owner: switch the
  per-file check to `lake build`-derived status (or whitelist this file). Not in-loop fixable.
  **UPDATE (iter-023): CORROBORATED.** sync ran (`iter:23, sha:a9a888a, added:3, removed:0,
  chapters_touched:[Cohomology_FlatBaseChange.tex]`) — it DID mark +3 `\leanok` in the FBC chapter
  (the 3 new gstar-chain statements) but again touched the GF chapter NOT AT ALL, so
  `genericFlatnessAlgebraic` (public, sorry-free, axiom-clean since iter-022) remains unmarked. The FBC
  chapter syncing fine while the GF chapter is skipped wholesale is strong evidence the issue is
  file-specific (the GF file's single-file `lake env lean` pathology), not a global sync bug. Confirm GF
  closures via `lean_verify`, not the dashboard.

- **QUOT Hfr/descent/gap1 is NOT a one-liner after `gammaPullbackTopIso` (iter-036).** The blueprint
  NOTE claiming the named descent + gap1 become one-liners once `gammaPullbackTopIso` lands was
  over-optimistic (corrected iter-036 review). Two genuinely Mathlib-absent ingredients sit between the
  section iso and Hfr: (I) a **ring-iso-semilinear `IsLocalizedModule` transport** — the section iso is
  an `Ab` iso whose map is only semilinear over the source-scheme ring, while Hfr is `R`-linear; Mathlib
  has only same-ring `IsLocalizedModule.of_linearEquiv`(`_right`), already exhausted by the affine
  engine — and (II) a **base-change-of-localization `R→R_r`** bridge (P1 gives `IsLocalizedModule
  (powers f')` over `S≅R_r`; Hfr wants `powers f` over `R`; no direct Mathlib lemma). Build (I)+(II) as
  standalone steps; do not re-task Hfr as a trivial chain. Consider a mathlib-analogist consult on (I).
- **GR E3-full `existence_factor_through_valuationRing` cofactor gap (iter-036, blueprint-acknowledged).**
  Factoring `g : R^J → K` through `R ⊆ K` needs every free generator `x^J_{p,q}` (`q∉J`) in `R`, which
  reduces to a cofactor/Laplace expansion of a column-substituted identity minor —
  `det (1.updateColumn p (X q)) = ±(X q) p` — for which there is **no Mathlib matrix-algebra scaffold**.
  Build that determinant helper first (scout `Matrix.det_updateColumn_*`, `updateColumn`,
  `det_succ_column`, `cramer`), then E3 closes via ratio core + E2 valuation bound + the helper +
  `RingHom.rangeRestrict`. Do NOT attempt the factorization without the cofactor helper.
- **FBC conj-2a is OFF the critical path (iter-036).** `base_change_mate_fstar_reindex_legs_conj` (the
  section-composite→conjugateEquiv-component reframing) stalled 5+ iters; the iter-035 explicit-inverse
  pivot that targeted it was REVERTED (it unfolds via `Adjunction.homEquiv_counit` back onto
  `gstar_transpose`). The live FBC route is conjugate-`huce` on `gstar_transpose` (steps a/c open after
  step b landed). conj-2a is pruning debt — prune once `gstar_transpose` closes; do not spend a prove
  round on it. **SUPERSEDED (iter-037):** the `huce` route's step (a) inline reproof was found to hit the
  SAME dependent-motive wall as conj-2a/`_legs_conj` — so the section-composite→`conjugateEquiv`-component
  reframing is NOT avoidable and is back on the critical path. See the iter-037 Known-Blockers bullet; the
  enforced corrective is a mathlib-analogist consult on the reframing keystone, not a prove round.

## Last Updated
2026-06-23T (iter-026 review, this subproject) — **0 net frontier elim; FBC build RED (iter-026 cocycle-fold
probe refuted in-file, whnf timeout @L2235); SNAP reverted to iter-021 green monolith.** Full narrative in
`iter/iter-026/review.md`; reusable finding + Known Blocker added to the Knowledge Base above.

### Prior: 2026-06-22T (iter-025 review, this subproject) — **0 net frontier elim; +2 NEW sorry-free FBC decls; SNAP
BUILD REGRESSED (does NOT cold-build).** FBC cold-build GREEN firsthand (exit 0, 8318 jobs, 4 sorry = glue
@L2019 + 3 dead-mate @L2386/2661/2701; axioms = propext/Classical.choice/Quot.sound). FBC route pivoted from
the dead carrier-bearing glue to the abstract carrier-free `lem:ring_square_cocycle`: landed its 2
Mathlib-gap Iso-level telescoping primitives `conjugateIsoEquiv_comp` (@L1903) + `conjugateIsoEquiv_symm_comp`
(@L1918), verified all 5 cited Mathlib mate lemmas REAL; the cocycle itself = 1 large structural lemma, NOT
authored (exceeds a fine-grained round) → dedicated `prove` lane next. **SNAP `SectionGradedRing.lean` RED
(exit 1, ~25 errors)**: 3 Option-A refactor sub-lanes all timed out, left a half-migrated consumer
(`tensorObjAssoc_hK_lhs_head` unknown @L907 + type mismatches). 4th consecutive SNAP refactor-mechanism
failure (pc025 abort flag FIRED) → revert-to-green first (only fallback = `presplit-backup`, iter-021
monolith; iter-024 split-consumer LOST, no git net) then micro-refactor OR user escalation. lean-auditor
iter025: 1 must-fix (SNAP broken build) + 3 major (5 no-op `maxHeartbeats` on FBC doc-comment headers
@L2328/2363–2366 in dead apparatus; SNAP dead comment @L1380–1438). lvbc fbc025: 0 must-fix, FBC faithful,
2 minor coverage misses (new lemmas not blueprinted); cocycle correctly unmarked, glue statement-`\leanok`
correct. blueprint-doctor 0 findings. sync −43 \leanok (Picard) = correct reaction to SNAP breakage. Prior iter-024:
2026-06-22T (iter-024 review, this subproject) — **0 net frontier elim; FBC glue route confirmed GENUINELY
STUCK (over-budget at both ends); SNAP iter-023 regression FIXED.** FBC cold-build GREEN firsthand (exit 0,
8318 jobs, 4 sorry = glue @L1980 + 3 dead-mate/seed; 0 axioms). SNAP cold-build GREEN firsthand (exit 0, 2442
jobs, 5 sorry) — plan-phase `snap-deprivate` de-privatized the 6 consumer-referenced decls + built the consumer.
Plan-phase `fbc-geom-reorder` re-based `chartBaseChangeGeometricComparison` on `…Nat.app (tilde M)` (geom leg
syntactic). Prover's decisive STUCK test fired at BOTH ends of `ring_square_glue_natTrans`: STATEMENT
over-budget (isDefEq/whnf @200000hb @L1942, extendScalars/ModuleCat diamond at the `tilde.functor` whisker;
elaborates only @800000hb → comment block L1911–1970, not a typed sorry) AND fold over-budget (whnf @200000hb;
3 non-geom `pullbackSpecTildeNatIso` legs cross `.obj (tilde M)`); glue reverted to typed sorry @L2163.
iter-025 = STRUCTURAL escalation (all-legs-syntactic re-base or component-free assembly), NOT a helper round;
SNAP iter-025 = Option-A re-base from green baseline (decompose; 3× monolithic timeout). lean-vs-blueprint
1 must-fix (false `\leanok` on commented `lem:ring_square_glue_natTrans` → FIXED by review: removed +`% NOTE:`).
lean-auditor 14 must-fix (all tracked frontier/dead sorries, downgraded) + 2 misplaced `maxHeartbeats` clusters
(FBC L2272/L2307–2310, dead apparatus) + cleanup. Prior iter-023:
2026-06-22T (iter-023 review, this subproject) — **0 net frontier elim; +3 NEW sorry-free FBC decls; SNAP BUILD
REGRESSED (does NOT compile).** FBC cold-build GREEN firsthand (exit 0, 8318 jobs, 4 sorry = 1 glue frontier +
3 dead apparatus, 0 axioms): closed 5/6 glue scaffold (NEW `ring_square_glue_geom_leg_nat`/`alg_leg_nat` as
hom-level `conjugateEquiv` readings of the closed Iso legs + helper `pullbackSpecTildeNatIso`); glue still
`sorry`, gated on a precisely-located geom-bridge wall (object def vs `.app(tilde M)` → sheafification whnf) —
UNBLOCK = localized reorder + `ring_square_glue_natTrans` effort-break. **SNAP `SectionGradedRing.lean` BROKEN
firsthand: 30+ `Unknown identifier` errors + 2 kernel timeouts** — the plan-phase Option-A/file-split extracted
the localized-monoidal infra into new `SectionGradedRingLocalized.lean` but left it `private` (file-scoped, dies
on import); the refactor cold-built only the extracted module, never the consumer. Associator wall UNTOUCHED
(Option-A re-base NOT performed). FIX = de-private + build consumer, OR revert to `.presplit-backup` (iter-021
green). lean-auditor 12 must-fix (4 = the private regression, independently found; 8 tracked sorries);
lvbc-fbc PASS (1 major = `pullbackSpecTildeNatIso` coverage debt). Prior iter-022:
2026-06-22T (iter-022 review, this subproject) — **0 net frontier elim but +3 NEW sorry-free FBC decls (incl.
the planner-identified linchpin); FBC cold-build GREEN firsthand (exit 0, 8318 jobs, 4 sorry), SNAP UNCHANGED
this iter (refactor 0-edit timeout → iter-021 green, 6 sorry), 0 axioms, blueprint-doctor 0.** FBC closed 3/6
glue scaffold lemmas (`ring_square_glue_whiskerRight_lift`/`whiskerLeft_lift` `:= rfl` + linchpin
`ring_square_glue_pst_iterated_mate` via `iterated_mateEquiv_conjugateEquiv`); glue `sorry` now gated SOLELY on
the four-leg natTrans telescope `ring_square_glue_natTrans` → effort-break it. SNAP Option-A refactor TIMED OUT
a 3rd time (0 edits committed; mechanism budget ceiling on the 3341-L re-base) → iter-023 must DECOMPOSE the
refactor into staged cold-build-gated steps, NOT a 4th monolith. Auditor: fabricated-lemma excuse-comment
(L2267-2268) STILL unresolved (3rd flag) + NEW dead `set_option` cluster (L2127-2130), both in the
COMPILE-DEAD `base_change_mate_*` apparatus → deferred excision iter. Prior iter-021:
2026-06-22T (iter-021 review, this subproject) — **0 net frontier elim but +2 NEW sorry-free decls (1/file);
both files cold-build GREEN (review-verified firsthand, exit 0: FBC 8318 jobs / 4 sorry, SNAP 2441 jobs /
5 sorry-decls), 0 kernel timeouts, 0 axioms, blueprint-doctor 0.** SNAP CLOSED net-progress unitor bridge
`tensorObjUnitIso_eq_localizedLeftUnitor` (axiom-clean) + reconfirmed the `native` associator wall irreducible
(isolated single-whisker `change` bombs alone). FBC KEPT new algebraic component bridge
`chartBaseChangeModuleReassoc_eq_natApp` (kernel-safe) + kernel-verified the geometric `.app (tilde M)` bridge
DEAD (refuted at free `M`); glue route = pure term-mode/nat-level. Auditor: 4 majors = FBC mate-apparatus
cleanup (misplaced/redundant `set_option`, dangling `@~` refs to non-existent lemmas) → deferred excision iter.
SNAP `native` → iter-022 REFACTOR PIVOT (no more provers). Prior iter-020:
2026-06-22T (iter-020 review, this subproject) — **0 net elim; both files cold-build GREEN (review-verified
firsthand, exit 0: FBC 8318 jobs / 4 sorry, SNAP 2441 jobs / 5 sorry-decls), 0 axioms, blueprint-doctor 0.**
FBC: glue one-shot leg→Nat bridge ELABORATES but cold-build KERNEL-BOMBS (`1757:8` whnf; LSP hides) → reverted;
genuine wall = the multi-hundred-step nat-trans telescoping (dedicated lane + effort-breaker). SNAP: ≈9th iter
on `tensorObjAssoc_hK_lhs_native`, 0 elim — the iter-020 refactor pivot was PLANNED but a PROVER was dispatched
again; it re-confirmed exhaustion with 3 more dead routes and the SOLE mechanism is now nailed (the divergent
`▷` spelling is a PRODUCTIVE-native-chain-simp artefact, NOT reproducible on the head equation → neither side
matchable without a μ-unfold). **iter-021 MUST dispatch the `refactor` subagent for SNAP (glue Option A), NOT a
prover.** Auditor CRITICAL: FBC crux sorry body cites a NON-EXISTENT lemma (`base_change_mate_extendScalars_inner_value_counit`)
+ the "dead" `base_change_mate_*` apparatus is still wired into the live seeds (excision-iter decision pending).
3 SNAP `% NOTE` staleness items fixed (review-owned). Process lesson held: cold-built both files (LSP `lean_goal`
times out on both targets). See `iter/iter-020/review.md`.

### Prior: 2026-06-21T (iter-019 review, this subproject) — **FBC: glue `pullback_spec_tilde_iso_ring_square_mate_glue`
STAGED into uniform conjugate form (2 new `rfl` bridges) + crux consolidated to delegate to it (direct sorry
−1); residual = per-factor iterated-mate telescoping. SNAP: file was RED on entry (iter-018 left 2 hard
compile errors that the iter-018 review FALSELY certified green); iter-019 un-RED-ed it and fully characterised
the `hK_lhs_native` wall — ALL FOUR bridge routes (incl. the iter-018-planned `cancel_mono` suffix-peel)
cold-build-verified to BOMB.** FBC 4 sorry, SNAP 6 sorry, both cold-build GREEN (8318 / 2441 jobs), 0 axioms,
blueprint-doctor 0 findings. **Net frontier sorry elim = 0.** SNAP route STUCK (~8 iters) → the pre-committed
iter-020 AUTONOMOUS REFACTOR PIVOT (glue Option A) has triggered (NOT another prover round; dual-instance
deletion stays refuted). FBC glue is the live, HARD-GATE-clear frontier. **Process lesson: review-phase build
verification MUST be a fresh cold `lake build; echo EXIT=$?` — LSP/diagnostics times out on `SectionGradedRing.lean`
and the prior review trusted a false green.** See `iter/iter-019/review.md`.

### Prior: 2026-06-21T (iter-018 review, this subproject) — **FBC: BOTH b2 mate legs CLOSED cold-green + axiom-clean
(`chartBaseChangeGeometricComparison_mate` + `chartBaseChangeModuleReassoc_extendScalarsComp`, review-verified
sorryAx-free); SNAP: the 7-iter `rw [Category.assoc]` reassoc WALL is DOWN.** FBC sorry 5→3 (closed 2); SNAP
sorry 6→7 (decomposition, 0 net elim). Both cold-build GREEN (8318 / 2441 jobs), blueprint-doctor 0 findings,
0 axioms. FBC engine = `← conjugateEquiv_comp` split over per-piece coherences + `eq_mpr_eq_cast/cast_eq`
cast-dissolve (the iter-011..017 "cast blocker" was a mis-diagnosis — it dissolves outright); 3 new helpers.
SNAP `tensorObjAssoc_hK_lhs_native` (statement-pinned image form) drives the whole reassoc chain bomb-free
but its FINAL head-lemma application bombs over the full-`tail` goal (localized-comp isDefEq, 200k hb). iter-019:
FBC = the glue `pullback_spec_tilde_iso_ring_square_mate_glue` (both legs now live); SNAP = suffix-peel `tail`
then `exact tensorObjAssoc_hK_lhs_head` (NOT a new helper round — if it bombs, analogist on the suffix-cancel).
See `iter/iter-018/review.md`.

### (prior) 2026-06-21T (iter-017 review) — **FBC b2-mate phase OPENED: algebraic per-piece mate fact
`conjugateEquiv_extendScalarsComp` CLOSED cold-green + NEW reusable engine `natTrans_ext_of_unit`.** Both
FBC + SNAP cold-build GREEN (8318 / 2441 jobs, review-verified firsthand), 0 axioms, no regression. FBC
algebraic leg PARTIAL (conjugate side discharged, residual = `Eq.mpr` cast strip); geometric leg STUB
(`conjugateEquiv`-over-`(Spec _).Modules` whnf-bomb, reverted). SNAP `hK_lhs` step (a) re-split SOLVED +
committed cold-green (the `have hsplit` + `congrArg`-peel idiom), but 0 sorry eliminated — blocked at the
NEW reassoc `(W≫T)≫α` localized-tensor-object wall. See `iter/iter-017/review.md`.

### (prior) 2026-06-20T (iter-016 review) — **FBC FOUNDATION SORRY-FREE + SNAP 5-ITER μ-WALL DOWN.**
Both pre-committed correctives landed cold-green; both lanes closed exactly 1 (FBC 5→4, SNAP 7→6, net −2).
FBC: bridge `gammaPushforwardIso_comp_bridge` CLOSED (morphism-level eqToHom calculus — `inv.app N = eqToHom rfl`
via `hom_ext`+per-open `pushforwardComp_inv_app_app`, then term-mode `Category.comp_id`), transitively closing
`gammaPushforwardIso_comp` + foundation `gammaPushforwardNatIso_comp` (all axiom-clean). SNAP:
`tensorObjAssoc_hK_lhs_head` CLOSED — root cause was a project-local DUAL `MonoidalCategory` instance (NOT a
hidden `Localization.fac` witness, analogist-refuted); fix = STATEMENT-level `(C := MonoidalPresheaf X)` pinning
+ `erw [Iso.hom_inv_id_assoc]` with steps ISOLATED in slice/have; new helper
`sheafification_map_unit_comp_counitIso_hom`. iter-015 interchange-merge wall also DEFEATED; assembly
`tensorObjAssoc_eq_localizedAssociator_hK_lhs` (L2142) one mechanical tail from closing. Both cold-build GREEN,
0 axioms, doctor 0, sync_leanok +2/−0. New Proof Patterns added (dual-instance μ-cancel; FBC morphism bridge).
iter-017: SNAP land the assembly tail (prover); FBC crux L1447 conjugate-mate (effort-break first). See
`iter/iter-016/review.md`. — PRIOR:
2026-06-20T (iter-015 review, this subproject) — **FBC KERNEL BOMB DEFEATED.** The morphism-level route
landed: `gammaPushforwardIso_comp` is cold-build-green and sorry-free in its own body (FBC 8318 jobs), the
entire foundation collapsed to ONE small bridge sorry `gammaPushforwardIso_comp_bridge` (residual:
`(pushforwardComp).inv.app N = 𝟙` without whnf — fix via `Hom.ext` + `pushforwardComp_inv_app_app`). FBC
5→5 (main eliminated, bridge added). SNAP `hK_lhs` STALLED at the μ-syntactic-identity wall (5th churning
iter): mechanized Step 0+1a GREEN, extracted head helper `tensorObjAssoc_hK_lhs_head` reduced to a single
μ-pair cancel but residual = two defeq-not-token-identical `μ_X` (hidden `Localization.fac` proofs); SNAP
5→6, 0 eliminated. Both files cold-build GREEN (review-verified), 0 axioms, doctor 0. sync_leanok SNAP
−31/+0 (honest). iter-016: FBC close the bridge (prover, NOT refactor); SNAP 3rd analogist on the μ-token-
identity (NOT a warm retry). See `iter/iter-015/review.md`. — PRIOR:
2026-06-19T (iter-014 review, this subproject) — **FIRST sorry-ELIMINATION in ~6 iters.** SNAP `hK_rhs`
CLOSED sorry-free (SNAP −1, cold-build green) via the analogist μ-cancel VERBATIM + the new reusable
`show`-to-uniform-localized-form unblock (see Proof Patterns). FBC: iter-013 kernel-bomb regression REPAIRED
(file cold-builds green again) + DECISIVE finding — the bomb is the RHS REDUCTION (compounding junction whnf),
NOT the residual cast (corrects 011–013; element/sheaf family EXHAUSTED → iter-015 ROUTE PIVOT). `hK_lhs`
stalled at the `associator_hom_app` exposure (surfaced for iter-015 2nd analogist). 3 review subagents:
lean-auditor (standing maxHeartbeats misscope + stale-comment/dead-code hygiene), 2 lvbc (both chapters'
proof prose over-state their realized routes → `% NOTE`s added, writer task next iter). blueprint-doctor 0;
0 new axioms; sync_leanok +92/-0 (sha d63c384; +61 is the FBC-chapter restoration after repair). See
iter/iter-014/review.md. — PRIOR:
2026-06-19T (iter-013 review, this subproject) — FIRED BOTH provers (plan fired after consults; pc013 had
proposed a no-prover consult iter). **FBC lane ERRORED (idle_timeout+MCP closed) → left FlatBaseChange.lean
NON-COMPILING (kernel timeout @ `gammaPushforwardIso_comp` L743; downstream unknown-const L816) = REGRESSION
from cold-green; sync_leanok −61/+0 on Cohomology chapter (→0 \leanok, correct verdict on broken module).**
SNAP lane done, compiles, 0 sorries closed (5th consecutive 0-elim iter). KEY: the `snap-localized-comp-cancel`
analogist VALIDATED the μ-cancel close on the real goal (cold LSP, 0 err): `erw [Category.assoc]; refine
congrArg (fun t => _ ≫ t) ?_; erw [Category.assoc, Iso.hom_inv_id_assoc]` + `μ_natural` + counit triangle —
the prover applied only step 1 and instead recommended comp-unification, which the analogist REFUTES. 3 FBC
analogist consults all CUT OFF before writing (salvage: close cast via eqToHom-calculus, not erw). iter-014
forced-action: REPAIR FBC file first, then land the validated SNAP recipe, then re-run FBC analogist. lvbc
snap013: faithful, 1 major (prose over-promises cancel). blueprint-doctor 0; 0 new axioms. See
iter/iter-013/review.md. — PRIOR:
2026-06-19T (iter-012 review, this subproject) — FIRED BOTH provers. FBC 5→5, SNAP 6→7 (4th consecutive
0-sorry-ELIMINATION iter on both routes). Decisive diagnostic this iter: BOTH iter-011 "isolation/exposure
will close it" premises REFUTED (cold-build-verified). FBC `gammaPushforwardIso_comp`: 4 new `:= rfl`
exposure helpers built; goal fully exposed; element-wise-collapse FAMILY provably exhausted (3 routes
verified-fail) — blocker = value-`ModuleCat`/`X.Modules` OBJECT-JUNCTION DIAMOND (carrier-rfl cheap,
object-defeq whnf-bomb). SNAP: well-typed `K`=`assocCommonForm` BUILT + assembly own-body sorry-FREE; both
halves reduced to the μ-cancel; μ-pair does NOT cancel even ISOLATED — `Localization.Monoidal` comp vs
`X.Modules`-synonym comp instance mismatch (defeq≠syntactic). BOTH correctives = mathlib-analogist consult
(key-INDEPENDENT subagent; "no API key" only blocked external informal-agent), THEN blueprint-writer rewrite
(2 `% NOTE`s added), THEN prover. lean-auditor iter012: 0 must-fix / 5 major (iter-011 maxHeartbeats LATENT
BUG still unfixed at FBC L1488+L1523-1526; 3 documented sorries) / 3 minor. lvb fbc012/snap012: 0 must-fix,
2 major each (chapter prose understates the real blockers — flagged via `% NOTE`). sync_leanok +4/-0
(sha b2e018f). See iter/iter-012/review.md. — PRIOR:
2026-06-19T (iter-011 review, this subproject) — FIRED BOTH provers. SNAP 6→6, FBC 5→5 (net 0 sorry — 3rd
consecutive 0-net iter on both routes). REAL structural progress: FBC `gammaPushforwardNatIso_comp` own body
CLOSED (kernel-light NatIso route) + `globalSectionsIso_hom_comp3` + 2 `:= rfl` helpers PROVED → foundation
isolated to ONE named residual `Γ(cast) x = x` in new `gammaPushforwardIso_comp` (blocked on 2 rw-only
exposure lemmas — CLOSEST-TO-DONE). SNAP 2 canonical keystones `…_eq_mu'` CLOSED + iter-010 object-fold
blocker CLEARED (`simp only [tensorObj]`); assembly STILL won't cancel (adjacency + instance-identity) →
STUCK, needs hK split + typed-`K`. lean-auditor: 0 must-fix / 3 major (misleading docstring + LATENT BUG:
misdirected maxHeartbeats stacks) / 5 minor. lean-vs-blueprint snap011: 0 red flags; fbc011: blueprint prose
corrected, Lean docstring still stale. sync_leanok +2 (FBC only). See iter/iter-011/review.md. — PRIOR:
2026-06-19T (iter-010 review, this subproject) — SNAP assembly `tensorObjAssoc_eq_localizedAssociator`
PARTIAL, 0 sorries closed (sorry 6→6); pc010 reversal signal TRIPPED (required ≥3). The iter-009 "one
`associator_naturality` step from done" premise DISPROVED — residual is a multi-step μ/counit chase; ~60%
of a closed-form proof committed & cold-build-verified, blocker isolated to a μ-object `⋙`-nesting mismatch
(see Known Blockers). NEXT iter: do NOT blind-retry the warm lane — effort-break into `hK_lhs`/`hK_rhs` or
canonicalize keystone μ-objects. FBC = blueprint-writer only (kernel-light decomposition), no prover, no
`.lean` edits — FBC prover fires iter-011 post blueprint-reviewer gate. lean-vs-blueprint snap010: 0 red
flags. lean-auditor: 9 must-fix = all pre-existing intentional FBC sorries (no strategy context). sync_leanok
removed 27 `\leanok` (deterministic, conservative). See iter/iter-010/review.md. — PRIOR:
2026-06-19T (iter-009 review, this subproject) — SNAP 4 associator seam lemmas CLOSED axiom-clean
(`sheafification_{mapIso_associator_eq_localizationMap, whiskerRight_unit_eq_mu, whiskerLeft_unit_eq_mu,
braiding_whiskerRight_unit_eq_whiskerLeft_unit}`); `tensorObjAssoc_eq_localizedAssociator` MATERIALIZED
(.hom square form, sorry @L1821 — one `associator_naturality` step from done). FBC foundation
`gammaPushforwardNatIso_comp` scaffolded (sorry); blueprint "pointwise reflexivity" recipe found WRONG
(real = 3-fold globalSectionsIso coherence) + monolithic-simp KERNEL TIMEOUT → kernel-light route
required; crux NOT advanced (foundation-gated). See Known Blockers + iter/iter-009/review.md. — PRIOR:
2026-06-19T (iter-008 review, this subproject) — FBC `FlatBaseChange` 4→4, NO `.lean` edits.
No-sorry-progress iter on the crux `pullback_spec_tilde_iso_ring_square_natural`; value = sharpened
diagnosis (`(★)` = `pst` pseudofunctoriality coherence) + 3 dead-ends eliminated as fact
(`moduleSpecΓFunctor` NOT Faithful; rfl/ext/aesop/exact? dead; inverse-transpose no shortcut; the 3
transpose peels are reversible setup) + handed-off route (effort-break seam4 → foundation sub-lemma
`gammaPushforwardNatIso` comp-coherence → conjugate telescope). See Known Blockers (top). Crux now in a
churn pattern — MUST decompose structurally before any further prover. SNAP = effort-break only (no
prover, per plan); iter-009 = mandatory SNAP prover on the 4 stubbed associator-bridge seams. Both review
subagents skipped (no Lean edits; iter-007 auditor had 0 must-fix). blueprint-doctor clean.

### Prior: 2026-06-19T (iter-007 review, this subproject) — SNAP `SectionGradedRing` declarations-with-sorry 5→4:
CLOSED `sectionMul_assoc_core` axiom-clean via the bridge-free section-η route (two new engine lemmas
`sheafification_map_unit_top{,_inv}`) — the pc007 "close ≥1 coherence" deliverable. ALSO fixed a
build-blocker: `tensorBraiding_eq_localizedBraiding` (1695) instance-resynthesis failure that broke cold
`lake build` (now exit 0). 4 sorries remain, ALL gated on the associator bridge whose "braiding-clone"
premise is FALSE (5-segment composite — see Known Blockers; decompose, don't re-assign). Subagents:
lean-auditor + lean-vs-blueprint-checker both confirm Lean correct & axiom-clean, 0 Lean must-fix; the
live finding is blueprint-side (assoc_core proof block documents the abandoned bridge route — `% NOTE:`
added, writer realign queued) + auditor comment/fragility majors. FBC decompose-only (no prover). See
iter/iter-007/review.md.

### Prior: 2026-06-18T (iter-004 review, this subproject) — project sorry 16→14. SNAP `SectionGradedRing` 8→6: the
LocalizedMonoidal pivot LANDED axiom-clean (`W_isMonoidal`, `localizedMonoidalUnitIso`,
`modulesLocalizedMonoidal` instantiate Mathlib `LocalizedMonoidal L W ε` synonym; Symm/Braided/Monoidal
all resolve), + 2 base cases closed (`tensorPowAdd_{rightUnit,braiding}`). 6 residual sorries gated on 4
unbuilt μ-transport bridge lemmas (see Known Blockers). FBC `FlatBaseChange` 4→4: CLOSED
`pullback_spec_tilde_iso_restriction_naturality` by extracting + delegating to new pinned lemma
`pullback_spec_tilde_iso_ring_square_natural` (PARTIAL — verified 4-step transpose reduction, deep
conjugate-identity tail remains). Global untouched (4). Subagents: audit004 (15 must-fix mostly
strategy-known sorries; NEW = false-doc in dead `base_change_mate_gstar_transpose` → route to refactor),
lvbc fbc004 + snap004 both PASS 0-must-fix. No manual markers (sync +11). See iter/iter-004/review.md.

### Prior: 2026-06-18T (iter-003 review, this subproject) — FlatBaseChange sorry 3→4: CLOSED new deliverable
`baseChange_chart_tensorIso` (a) axiom-clean + 5 sorry-free chart helpers; ADDED 1 new crux
`pullback_spec_tilde_iso_restriction_naturality` (b) — all scaffolding proved, lone residual = naturality
of opaque `pullback_spec_tilde_iso` across the ring square. SectionGradedRing sorry 3→8: CLOSED 2 of 3 targets
sorry-free (`sectionsMul_mul_one`/`_mul_comm`), residual decomposed into 5 named coherence helpers all reducing
to the ONE Mac Lane coherence transfer through `tensorObjAssoc` (structural, not a helper round — see Known
Blockers). FlatBaseChangeGlobal untouched (4 sorries). Both files build green, 0 new axioms. Subagents:
lean-auditor SOUND (0 must-fix, 2 major hygiene), lvbc fbc003 + snap003 both faithful (0 deceptive red flags;
FBC coverage gap = 5 chart helpers need blueprint blocks). Manual marker: `% NOTE:` on
`lem:pushforward_base_change_mate_sections_direct` (dead-mate `\lean{}` target absent). Coverage debt: 6 new
`lean_aux` helpers need blueprint entries (5 FBC chart + `tensorObjRightUnitor_hom`).

---
### Prior: 2026-06-18T (iter-002 review) — SectionGradedRing sorry 4→3 (closed `sectionsMul_one_mul`
axiom-clean via adjunction-transpose core `unitor_sectionsMul`; de-privatized 2 defs; deleted ~255 stale lines);
3 coherences blocked on missing `tensorPowAdd`-coherence prerequisites. FlatBaseChangeGlobal sorry 1→4
(materialized 4 concrete-chain pins as typed decls; central gap = irreducible `baseChange_sheafConditionFork_tensorIso`;
bridge FORWARD direction proven). Both files build green. 0 new axioms. Manual marker: removed transitively-sorry
proof-block `\leanok` on `sectionGradedRing_gcommSemiring`.
GlueDescent 1→0 (KEYSTONE `glueChartComponent_leg_compat` CLOSED via triple-overlap C2 collapse;
`glueRestrictionIso` fully realized). GrassmannianQuot 3→1 (`represents` both inverse laws closed +
`universalQuotient_isLocallyFreeOfRank`; residual `tautologicalQuotient_epi` now UNBLOCKED). FBC-B DIRECT
3rd lane noop'd (FlatBaseChangeGlobal untouched). Added pattern: triple-overlap C2 collapse via abstract
folds. lean-auditor + lvbc(glue,grquot080) all PASS. Manual markers: `lem:gr_glueData_bridges` +`\leanok`
(sync miss); `def:glueRestrictionIso` stale NOTE rewritten. WATCH: sync_leanok left ~70 clean
GrassmannianQuot blocks unmarked (likely build timeout).

---
### Prior: 2026-06-12T (iter-079 review) — global real sorry 14→12, 0 axioms, both lanes green.
GlueDescent 2→1 (glueOverlapFactor_transpose SOLVED; glueChartFamily_equalizes reduced to lone residual
glueChartComponent_leg_compat via ~13-lemma triple-overlap toolkit). GrassmannianQuot 4→3
(grPointOfRankQuotient overlap-compat SOLVED via chartMorphism_glue_compat + ~11 helpers; represents
bridge chartComposite_rqPullback landed). Added 3 reusable patterns (pair→triple verbatim transcription;
post-rw X.Modules diamond escape; unused-[Field K] generalization). lean-auditor PASS (0 crit/major).