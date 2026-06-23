# Analogy: folding an abstract `≪≫`-telescope cocycle onto a heavy concrete goal without the per-boundary adjacency whnf

## Mode
cross-domain-inspiration

## Slug
fbc-fold-adjacency

## Iteration
027

## Structural problem (abstracted)
Close a concrete goal `LHS = RHS`, where each side is an `Iso.trans` (`≪≫`) telescope of per-leg
comparison isos in a category whose threaded objects are kernel-heavy (sheafification:
`(pullback (Spec φ)).obj (tilde M)`, `extendScalars`, `tilde.functor _ |>.obj _`). An abstract
carrier-free cocycle `ring_square_cocycle (g pρ qincl dρB sr dincl' : _ ≅ _) : g ≪≫ pρ = qincl ≪≫ …`
was stated, and the goal closed by `exact ring_square_cocycle <6 concrete isos>`.

## Root cause (sharpened iter-026, confirmed here by inspecting the goal at L2032)
The bomb is NOT carrier-binding (the iter-021 "direct `exact` is light" premise) and NOT proving the
abstract lemma. It is the **compounded `≪≫`-adjacency defeq** during unification: the lemma's
conclusion forces arg k's SOURCE object to defeq-match arg (k-1)'s TARGET object. Once X2 is assigned
a heavy `(pullback…).obj (tilde M)` from arg 1, unifying arg 2's source against it whnf's two heavy
carriers. The goal STATEMENT typechecks (cold-green) because those boundary defeqs were checked once,
isolated, within budget at signature-elaboration; the `exact` re-does ALL of them at once (6 args +
conclusion match), compounding past 200000hb. The boundary objects are defeq-but-NOT-syntactic (the
project's own comment @L2185: object-level `chartBaseChangeGeometricComparison … M` vs functor-level
`…Nat.app (tilde M)`; SNAP-side: hidden `Localization.fac` proof terms). Net: the cure must make each
boundary either SYNTACTIC or ISOLATED — relocating the defeq out of the compounded unification.

## Failed approaches (from directive)
- Carrier-bearing functor-level natTrans `≪≫`-chain (`ring_square_glue_natTrans`): whnf-bombs at the
  `isoWhiskerRight … (tilde.functor _)` statement-seam AND the `.app M` fold.
- Abstract carrier-free cocycle + single `exact` fold: REFUTED iter-026 — the per-`≪≫` adjacency
  defeq (above) bombs during unification, not the lemma proof.
- Element/`ext` descent across the `value-ModuleCat`/`X.Modules` junction: bombs per wrapper.

## Analogues found (ranked by porting cost)

### Analogue: `Mathlib.CategoryTheory.EqToHom` (`eqToIso`, `eqToIso_trans`, `eqToHom_trans`, `eqToHom_comp_iff`, `conj_eqToHom_iff_heq`)
- **Domain**: category-theory foundations — Mathlib's CANONICAL discipline for "objects are
  propositionally/defeq-equal but I must NOT make the kernel whnf them inline." Used pervasively in
  `Limits` (`HasLimit.isoOfNatIso`), `Functor` associativity, `ComposableArrows`, simplicial objects.
- **Same structural problem there**: a composite of morphisms/isos whose intermediate objects are only
  *propositionally* equal (`X = Y`, not syntactic) cannot be `≫`/`≪≫`-composed directly. Mathlib
  interposes `eqToHom h` / `eqToIso h` carrying the equality `h : X = Y` as DATA (a Prop, erased), so
  the composition typechecks SYNTACTICALLY (endpoints match the named variables), and the equality is
  discharged separately. `eqToHom_trans`/`eqToIso_trans` collapse adjacent bridges;
  `eqToHom_comp_iff`/`conj_eqToHom_iff_heq` slide a bridge across a morphism without whnf.
- **Technique**: restate the cocycle with an `eqToIso eᵢ` interposed at EVERY telescope boundary:
  `g ≪≫ eqToIso e2 ≪≫ pρ = qincl ≪≫ eqToIso e3 ≪≫ dρB ≪≫ eqToIso e4 ≪≫ sr ≪≫ (eqToIso e6 ≪≫ dincl').symm`
  with fresh, INDEPENDENT object variables `X2 X2' X3 X3' …` for each leg's actual endpoint and
  `eᵢ : Xk = Xk'` as explicit hypotheses. Now every `≪≫`-adjacency is `Xk ≅ Xk` / `Xk' ≅ Xk'` —
  purely SYNTACTIC, zero defeq. The 4–5 boundary defeqs become standalone Prop obligations `eᵢ`,
  discharged ONE AT A TIME at the call site. Per the project's own iter-016/021 finding ("isolate each
  defeq in a `have`/`slice`; the full-goal compounded check is what bombs"), an isolated `eᵢ := rfl`
  (one heavy boundary) is far more likely to fit budget than the 6-fold compounded `exact`. Where even
  isolated `rfl` bombs, prove `eᵢ` STRUCTURALLY: `eᵢ = congrArg (fun x => (pullback (Spec.map χ)).obj x)
  (inner : … = …)` recursing to a shallow/proof-irrelevant (`Subsingleton.elim`, `proofIrrel`)
  position — `congrArg`/`congrArg F.obj` builds `F a = F b` WITHOUT whnf'ing `F a` vs `F b` (unlike
  `congr`/`rw`/`simp`, which emit motive `Eq.mpr` rechecks — the documented bombs). The final fold is
  `exact ring_square_cocycle_bridged a b c d e f e2 e3 e4 e6` with NO adjacency defeq left.
- **Mapping to project**: in `Cohomology/FlatBaseChange.lean`, replace `ring_square_cocycle_probe`'s
  conclusion with the eqToIso-bridged form above (split X2→X2/X2', X3→X3/X3', X4→X4/X4', X6→X6/X6').
  At the glue `pullback_spec_tilde_iso_ring_square_mate_glue` (L2032), close with `exact
  ring_square_cocycle … <6 concrete isos> e2 e3 e4 e6`, each `eᵢ` a separate `have eᵢ : <objA> =
  <objB> := by …` proved/probed in isolation BEFORE the exact. The abstract cocycle's PROOF is
  unchanged (eqToIso bridges vanish via `eqToIso_refl`/`eqToHom_refl` once the abstract objects are
  identified — the bridges only carry weight at the concrete call site).
- **Porting cost**: LOW. ~4 extra object vars + 4 `eqToIso` interpositions in the statement; 4 isolated
  `eᵢ` proofs at the call. No carrier redefinition. Risk: if a boundary differs at a DEEP buried
  position requiring whnf to reach, that `eᵢ` still bombs — but each `eᵢ` is independently probeable
  (small goal), so the planner learns exactly which boundary is hard instead of an all-or-nothing bomb.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.CategoryTheory.CatCommSq` (`CatCommSq`, `hComp`, `vComp`, `hComp_iso_hom_app`)
- **Domain**: `Cat`-level square algebra (one shelf over the project; analogue 1 of prior report, UNTRIED).
- **VERIFIED here (loogle)**: `hComp` has signature `[CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
  CatCommSq (T₁.comp T₂) V₁ V₃ (B₁.comp B₂)`. The composition adjacency is the shared **functor** `V₂`,
  matched STRUCTURALLY (`Functor.comp` congruence on named functors), NOT a heavy OBJECT defeq. This is
  the decisive difference from the `≪≫`-telescope: adjacency lives at the functor level (light/syntactic
  for named `tilde`/`pullback (Spec φ)`/`extendScalars`), and `hComp` builds the whisker STRUCTURALLY —
  so it dodges the `isoWhiskerRight … (tilde.functor _)` statement-seam that killed `ring_square_glue_natTrans`.
- **Technique**: register each of the 4 `pullbackSpecTildeNatIso` legs + the 2 comparison legs as
  `CatCommSq` instances (`CatCommSq.mk <natiso>`); build LHS/RHS routings by `hComp`/`vComp`; the glue
  is equality of the two pastes' `.iso`. Extract `.app M` ONCE at the very end via a single
  `congrArg (·.hom.app M)` (structural). NEVER `simp`/`rw` `hComp_iso_hom_app` against the goal (its RHS
  `B₂.map (….app X)` re-crosses heavy carriers).
- **Mapping to project**: as prior report; the new evidence is that the bundled composition genuinely
  keeps adjacency off the heavy objects. The residual content (equality of the two `.iso`'s) is the mate
  cocycle — still needs proving, but over functor-level natTrans where the seam bomb is gone.
- **Porting cost**: MEDIUM. Wrap 6 legs in `CatCommSq.mk` (mechanical) + the `.iso`-equality proof.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv_vcomp`/`_hcomp`, `iterated_mateEquiv_conjugateEquiv`) + `pullbackSpecTildeNatIso` as one NatIso (Q3)
- **Domain**: Beck–Chevalley mate calculus / `NatIso` naturality.
- **Same structural problem there**: a 2D coherence ("comparison iso respects a base-change square") is
  a single `NatTrans.naturality`/field projection ONCE the comparison is packaged as one natural iso of
  functors — ONE boundary, structural, no telescope. Mathlib's mate `vcomp`/`hcomp` cocycles are
  stated/proved entirely over ABSTRACT adjunctions; instantiation enters by one `exact`.
- **Technique**: keep the four-leg telescope in the `mateEquiv` algebra (already the project's
  `pst_iterated_mate` route); OR package the φ↦comparison assignment as a `Pseudofunctor` so the ring
  square IS `mapComp'` coherence (prior report analogue 3). Either way the heavy carrier is bound by the
  abstract statement, never whnf'd — BUT the FOLD back to the concrete goal STILL hits the `≪≫`-adjacency
  unless combined with the eqToIso bridge (#1) or CatCommSq (#2). So this analogue supplies the cocycle's
  PROOF, not the FOLD; pair it with #1/#2.
- **Porting cost**: MEDIUM (mate route, partly built) — HIGH (full pseudofunctor packaging).
- **Verdict**: PARTIAL_ANALOGUE (proof engine, not the fold mechanism).

## Discarded
- `generalize`/`set`-the-heavy-objects-to-opaque-locals before `exact` (Q1 literal): NO Mathlib
  precedent and CANNOT work. Generalizing the GOAL does not retype the abstract lemma's ARGUMENTS,
  whose heavy types drive the adjacency; and if the boundaries were syntactically identical, no bomb
  would occur in the first place. The correct primitive for "opaque equal objects" is `eqToIso`
  transport (#1), which Mathlib uses pervasively — NOT goal-generalization.
- Full carrier REDEFINITION so boundaries are syntactic `rfl` (Q4): this IS the root cure, but the
  eqToIso bridge (#1) is its LIGHTWEIGHT realization — bridge the boundary (carry `eᵢ` as data) instead
  of redefining the leg defs. iter-024 already showed re-basing ONE leg removed only 1 of 4 crossings;
  re-basing all 4 is laborious and dominated by #1 unless a re-base is needed for other reasons.
- `monoidal_coherence`/`CategoryTheory.Coherence` tactic: square has genuine mate content, not pure
  monoidal coherence; won't fire.

## Top suggestion
Try **#1 (eqToIso boundary-bridge)** first — lowest cost, directly attacks the confirmed root cause
(compounded adjacency defeq), and is independently probeable per boundary. Read
`Mathlib.CategoryTheory.EqToHom` (`eqToIso`, `eqToIso_trans`, `eqToHom_comp_iff`, `conj_eqToHom_iff_heq`).
In `Cohomology/FlatBaseChange.lean`: (a) restate `ring_square_cocycle` with an `eqToIso eᵢ` at each of
the 4 telescope boundaries and split each shared object var into two (`X2`/`X2'` …) tied by `eᵢ`;
(b) prove the abstract lemma as before (bridges collapse via `eqToIso_refl` when objects coincide);
(c) at the glue (L2032), FIRST establish each boundary equality as an isolated `have eᵢ : objA = objB`
(probe `rfl`; if it bombs, `congrArg (fun x => (pullback (Spec.map χ)).obj x) inner` / `Subsingleton.elim`),
THEN `exact ring_square_cocycle … e2 e3 e4 e6` — which now has ZERO adjacency defeq (all syntactic). If a
specific `eᵢ` is itself irreducibly heavy, fall back to **#2 (CatCommSq.hComp)** to move that boundary to
the functor level. The combination eliminates the compounded-unification bomb that refuted the single `exact`.
