# Analogy: telescoping the unit of a composite-morphism (pull/push) adjunction without leg-lock

## Mode
cross-domain-inspiration

## Slug
fbc-mate

## Iteration
020

## Structural problem (abstracted)
Inside a Beck–Chevalley / mate calculation we must expand the adjunction **unit at a composite
morphism** `g' = a ≫ b` via the standard four-factor "unit-of-composite" identity, distribute a
functor over the four factors, then telescope the `pullbackComp`/`pushforwardComp` pseudofunctor
coherence isos against a codomain dictionary. The obstruction is structural, not mathematical: the
target coherence object (`base_change_mate_codomain_read_legs`) is parametrized by the *equality
proofs* `hfst : g' = a ≫ b`, `hsnd : f' = …`, so once `subst`'d the leg becomes a locked literal
`(pullbackSpecIso …).hom ≫ Spec.map (ofHom …)` that no positional `rw [unitExpand]` can re-abstract
(the dependent motive carrying the leg-equality proofs is ill-typed under leg generalization).

## Failed approaches (from directive)
- Tactic-mode `rw [unitExpand]` after `subst hfst hsnd`: pattern `(pullbackPushforwardAdjunction
  (?a ≫ ?b)).unit.app ?N` won't unify against the locked leg (dependent-motive wall, 6 iters).
- `X.Modules` instance diamond defeats `rw`/`simp` of `Category.assoc`/`Functor.map_comp`/
  `Iso.inv_hom_id_app`; worked around in term mode only for the two standalone-stateable links.
- Effort-break into 5 atomic lemmas: 3 (`_eCancel/_affineUnit/_innerMatch`) can't be stated
  standalone because their types only materialize from the mid-assembly goal the leg-lock blocks.

## Root-cause reframing (what the analogues reveal)
The leg-lock is a *symptom*. The disease is that a coherence object is parametrized by an **equality
proof**. **Mathlib's entire pull/push pseudofunctor stack — which the project already imports as
`AlgebraicGeometry.Scheme.Modules.*` — never does this.** Every coherence (`pullbackComp`,
`pushforwardComp`, `pullback_assoc`, …) depends only on *morphisms*, kept as **free variables**, and
is built/telescoped through the conjugate-mate bijection. That is precisely why Mathlib never hits a
leg-lock: there is no proof argument to make the motive dependent, and the composite is manipulated
on the conjugate (right-adjoint) side where it is a free variable, not as a positional `rw` target.

## Analogues found (ranked by porting cost)

### Analogue: `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` (same domain, upstream of the project's own API)
- **Domain**: algebraic geometry / sheaves of modules — the *identical* pull/push setting.
- **Same structural problem there**: identify the pullback of a **composite** continuous map with the
  composite of pullbacks, and prove the associativity/unit pentagon for these comparisons.
- **Technique**: `pullbackComp φ ψ` (line 166) is *defined* as
  `Adjunction.leftAdjointCompIso (adj φ) (adj ψ) (adj (φ≫ψ)) (pushforwardComp φ ψ)` — i.e. the
  conjugate of the right-adjoint comparison. The key reindex identity
  `conjugateEquiv_pullbackComp_inv` (line 176) — `conjugateEquiv ((adj φ).comp (adj ψ)) (adj _)
  (pullbackComp φ ψ).inv = (pushforwardComp φ ψ).hom` — is **one line**:
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _`. The whole associativity pentagon
  `pullback_assoc` (line 192) is **one line**: `Adjunction.leftAdjointCompIso_assoc … (pushforward_assoc …)`.
  Throughout, `φ ψ ψ'` are **free morphism variables** — never `subst`'d, never carried as equality
  proofs. The composite morphism is written *explicitly* as `φ ≫ (sheafPushforward).map ψ`.
- **Mapping to project**: the project already consumes the `Scheme.Modules` mirror of this file
  (`Scheme.Modules.pullbackComp` Sheaf.lean:219, `conjugateEquiv_pullbackComp_inv` Sheaf.lean:238,
  `pullback_assoc` Sheaf.lean:257) and already uses `conjugateEquiv_pullbackComp_inv` inside
  `pullbackPushforward_unit_comp`. The lesson is to extend that same discipline to
  `base_change_mate_codomain_read_legs` / `base_change_mate_fstar_reindex_legs`: build the codomain
  read out of `Scheme.Modules.pullbackComp`/`pushforwardComp`/`pushforwardCongr` of the **free**
  morphisms `e.hom`, `Spec.map inclA/inclR'` (and `pushforwardCongr comm` for the square), so it
  carries **no equality proof** `hfst/hsnd`. Then the composite leg appears as a genuine syntactic
  `e.hom ≫ Spec.map inclA`, `_unitExpand a b N` unifies, and no `subst` is needed.
- **Porting cost**: low–medium. No new Mathlib; re-cut two project definitions to be proof-free.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean` — `leftAdjointCompNatTrans_assoc` (line 155), `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` (line 140)
- **Domain**: generic 2-categorical adjunction calculus (one shelf over).
- **Same structural problem there**: telescope a **four-factor associator/whisker/comparison-iso
  cancellation** among nat-transes induced on left adjoints by right-adjoint comparisons — exactly the
  "telescoping cancellation of associator/unitor/comparison cells" shape of Seam 2.
- **Technique** (this is the portable crux): instead of positionally `rw`-ing a locked composite, the
  proof **lifts every factor to the conjugate side**:
  `obtain ⟨τ, rfl⟩ := (conjugateEquiv …).surjective τ` (lines 135–136, 146–147) rewrites each locked
  nat-trans as the conjugate image of a *fresh free variable*, then `apply (conjugateEquiv …).injective`
  (lines 137, 148) reduces the entire identity to one on the right-adjoint side, where it telescopes by
  the **`@[reassoc (attr := simp)]` conjugate simp set**: `conjugateEquiv_comp` (Mates.lean:337),
  `conjugateEquiv_whiskerLeft/Right` (Mates.lean:525/536), `conjugateEquiv_associator_hom`
  (Mates.lean:501). No positional `rw` on a locked literal anywhere; the diamond/lock never bites
  because the lock-prone object is replaced by a metavariable via `surjective … rfl`.
- **Mapping to project**: at the crux of `base_change_mate_fstar_reindex_legs`, rather than
  `rw [unitExpand]` on the `(Spec φ)_* ⋙ Γ`-image of `(pullbackPushforwardAdjunction g').unit`, use
  `(Scheme.Modules.conjugateEquiv …).injective`/`.surjective` to move the goal to the pushforward
  (right-adjoint) side, where `conjugateEquiv_pullbackComp_inv` turns the `pullbackComp` factor into
  `pushforwardComp.hom` and the project's existing `gammaMap_pushforwardComp_*`/`gammaMap_pushforwardCongr_hom`
  collapse lemmas already fire (they are stated on the pushforward side). The telescoping then runs
  through the reassoc conjugate simp set, not positional `rw`.
- **Porting cost**: medium. Must instantiate the conjugate bijection on the project's specific
  functors and confirm `surjective`/`injective` engage; the reassoc simp set is imported already.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib/CategoryTheory/Adjunction/Mates.lean` — `mateEquiv_vcomp` (167), `conjugateEquiv_comp` (337), `unit_conjugateEquiv(_symm)` (294/305)
- **Domain**: generic mate / Beck–Chevalley calculus.
- **Same structural problem there**: compute the mate/conjugate of a **composite** of squares/adjunctions
  and the unit-transport coherence — `(mateEquiv adj₁ adj₃)(α ≫ₕ β) = mate α ≫ᵥ mate β`.
- **Technique**: the coherence is stated and proven **abstractly over the composite** (`α ≫ₕ β`),
  then specialized to a component with `congr_app vcomp d` (see `conjugateEquiv_comp`, lines 343–351) —
  *never* by destructuring the composite morphism. The internal telescoping uses `slice_rhs i j =>`
  windows + `unit_naturality`/`counit.naturality` + `left_triangle_components` (lines 175–190), the
  reassoc-friendly replacement for positional `rw`. `unit_conjugateEquiv_symm` is the single-step
  unit-transport already cited in `analogies/fbc-mate.md` for Seam 1.
- **Mapping to project**: keep the leg abstract; prove the Seam-2 identity for a generic composite and
  obtain the concrete instance by `congr_app`/instantiation, mirroring how `conjugateEquiv_comp`
  derives the per-object identity from the global `mateEquiv_vcomp`. Use `slice_rhs` + naturality +
  `left_triangle_components` for any residual cancellation rather than positional `rw` through the
  diamond.
- **Porting cost**: medium. Conceptual template; the concrete win is the `congr_app`-from-abstract and
  `slice`+triangle telescoping idioms.
- **Verdict**: ANALOGUE_FOUND.

## Top suggestion
Adopt the `PullbackContinuous.lean` discipline first: **decouple `base_change_mate_codomain_read_legs`
from the equality proofs `hfst/hsnd`** so it is a function of the free morphisms only (built from
`Scheme.Modules.pullbackComp`/`pushforwardComp`/`pushforwardCongr`, with the square entering through
`pushforwardCongr comm` — a Prop arg to a functor, never an `And.casesOn`). With no proof-carrying
object, restate `base_change_mate_fstar_reindex` at the **explicit composite** `e.hom ≫ Spec.map inclA`
(no free `g'`, no `subst`); then `base_change_mate_fstar_reindex_legs_unitExpand a b N` and
`_gammaDistribute` unify on the genuine `(?a ≫ ?b)` and fire. If a residual cancellation still resists
positional `rw` (diamond), port the **conjugate-lift telescoping** from
`leftAdjointCompNatTrans_assoc`: `obtain ⟨_, rfl⟩ := (conjugateEquiv …).surjective` →
`apply (conjugateEquiv …).injective` → close on the pushforward side with
`conjugateEquiv_pullbackComp_inv` + the `@[reassoc (attr := simp)]` conjugate simp set
(`conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft/Right`). First file to touch:
`AlgebraicJacobian/Cohomology/FlatBaseChange.lean`, the `base_change_mate_codomain_read_legs`
definition (lines ~1210) and `base_change_mate_fstar_reindex_legs` (lines 1333–1421).
