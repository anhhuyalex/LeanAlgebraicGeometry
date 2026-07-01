# Analogy: the mate of a pasted square of composite adjunctions (FBC `_legs` re-encoding)

## Mode
cross-domain-inspiration

## Slug
fbc-mate-reencode

## Iteration
034

## Structural problem (abstracted)
Two composite adjunctions `adjL = (tilde ⊣ Γ)_R ∘ (g^* ⊣ g_*)` and
`adjR = (extend ⊣ restrict)_ψ ∘ (tilde ⊣ Γ)_{R'}` are related by a right-adjoint nat-iso
`β = gammaPushforwardNatIso ψ`. The canonical affine flat-base-change comparison
`g^* f_* F ⟶ f'_* g'^* F` (Stacks 02KH, i = 0) is the **mate / conjugate** of `β` for the pasted
square. We must (i) know the comparison is an iso and (ii) prove a *coherence* equation
(`base_change_mate_fstar_reindex_legs`) identifying the abstractly-built conjugate iso with the
concretely-assembled sheaf morphism (built from `pullbackComp`/`pushforwardComp`/unit factors pushed
through `(Spec φ)_*`). The obstruction is that the coherence is being attacked as a *positional*
equation under the `X.Modules` (Spec→ringedspace→modules) instance diamond, where every keyed
`rw`/`simp`/`erw`/`conv` is dead and the surviving term-mode splice bottoms out at the cross-layer
naturality of `gammaPushforwardIso ψ`.

## Failed approaches (from directive)
- Explicit factor telescoping inside the locked `_legs` goal (term-mode `congrArg`/`.trans`): bottoms
  out at cross-layer naturality of `gammaPushforwardIso ψ`.
- Keyed `rw`/`simp`/`erw`/`conv`: uniformly dead under the `X.Modules` instance diamond.

## Headline answers to the directive's two questions

1. **"Does Mathlib express the mate of a pasted square of composite adjunctions, and an
   IsIso-of-mate-from-IsIso-of-2-cell lemma?"**
   - *Mate of a pasted square = paste of the mates*: **YES**, three theorems —
     `mateEquiv_vcomp`, `mateEquiv_hcomp`, `mateEquiv_square` (the last is literally "mate of a 2×2
     grid of squares is the composite of the mates"). The composite-adjunction version is built into
     `mateEquiv_hcomp`/`mateEquiv_square` via `adj₁.comp adj₃`.
   - *IsIso-of-mate from IsIso-of-2-cell*: **NO for the general `mateEquiv`** — Mathlib explicitly
     states (Mates.lean:79 and :269) that a general mate does **not** inherit iso-ness. **YES for
     `conjugateEquiv`** (vertical functors = `𝟭`): `conjugateEquiv_iso`, `conjugateEquiv_symm_iso`
     (instances), `conjugateEquiv_of_iso`, `conjugateEquiv_symm_of_iso`, packaged as
     `conjugateIsoEquiv`. The project already exploits this — `pullback_spec_tilde_iso` is a
     `conjugateIsoEquiv adjL adjR` of `gammaPushforwardNatIso`, so **iso-ness of the comparison is
     already free**; (i) is not the open problem, (ii) the coherence is.

2. **"Is there a Beck–Chevalley / base-change package in Mathlib?"**
   - **No standalone `BeckChevalley` namespace exists.** The Beck–Chevalley iso phenomenon is captured
     by exactly one theorem: **`iterated_mateEquiv_conjugateEquiv`** (Mates.lean:450). Its docstring
     ("This explains why some Beck-Chevalley natural transformations are natural isomorphisms") states
     the principle: when **all four functors of the square are left adjoints**, the iterated mate (the
     Beck–Chevalley 2-cell of the pasted square) **equals the conjugate** of the original 2-cell — and
     conjugates preserve isos. The project's square qualifies (top/bottom `g^*`/`g'^*`, verticals
     `tilde`/`tilde` are all left adjoints), so this is the abstract route that makes (i) hold
     *and* gives the conjugate reformulation that makes (ii) tractable.

## Analogues found (ranked by porting cost)

### Analogue: `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean` — `leftAdjointCompIso` (72), `conjugateEquiv_leftAdjointCompIso_inv` (82), `leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` (140), `leftAdjointCompNatTrans_assoc` (155), `leftAdjointCompIso_assoc` (168)
- **Domain**: generic composite-adjunction conjugate calculus (one shelf over alg-geom; the project's
  own `Scheme.Modules.pullbackComp` / `conjugateEquiv_pullbackComp_inv` (Sheaf.lean:219/238) are
  instances of exactly this file).
- **Same structural problem there**: build the comparison iso for a **composite of three adjunctions**
  as a conjugate of a right-adjoint comparison, and telescope/associate it — i.e. precisely the
  `_legs` shape (`g' = e ≫ Spec ιA`, three constituent adjunctions, one pushforward-composite
  comparison `e₀₁₂`).
- **Technique (the portable crux)**: define the comparison as
  `leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂` (line 72); then its inverse conjugates back in **one
  line**, `conjugateEquiv_leftAdjointCompIso_inv : conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
  (leftAdjointCompIso …).inv = e₀₁₂.hom` (line 82). Coherence equations among such comparisons are
  discharged by the **conjugate-lift idiom**: `obtain ⟨τ, rfl⟩ := (conjugateEquiv …).surjective τ`
  (replace each locked nat-trans by a fresh free variable on the *right-adjoint* side) →
  `apply (conjugateEquiv …).injective` → close with the `@[reassoc (attr := simp)]` conjugate simp
  set (`conjugateEquiv_comp` Mates.lean:337, `conjugateEquiv_symm_comp` :354,
  `conjugateEquiv_whiskerLeft/Right` :525/:536, `conjugateEquiv_associator_hom` :501). **No positional
  `rw` on a locked literal anywhere** — the diamond never bites because the lock-prone object is a
  metavariable via `surjective … rfl`. `leftAdjointCompNatTrans_assoc` (155) and `leftAdjointCompIso_assoc`
  (168) are full pentagon-coherences proven this way in **one `simp` line** each.
- **Mapping to project**: re-cut the `_legs` comparison object so the codomain read is
  `leftAdjointCompIso` of the **free** morphisms `e.hom`, `Spec.map inclA` (with the pushforward
  comparison `e₀₁₂` = `pushforwardComp`/`pushforwardCongr` of the square), carrying **no equality
  proof** `hfst/hsnd`. Then `base_change_mate_fstar_reindex_legs` is a `conjugateEquiv`-component
  identity: `apply (Scheme.Modules.conjugateEquiv …).injective`, rewrite the leg via
  `conjugateEquiv_pullbackComp_inv` (project Sheaf.lean:238) / `conjugateEquiv_leftAdjointCompIso_inv`,
  collapse on the pushforward side with the project's `gammaMap_pushforwardComp_*` /
  `gammaMap_pushforwardCongr_hom`. The cross-layer naturality of `gammaPushforwardIso ψ` becomes
  `unit_conjugateEquiv_symm` + `conjugateEquiv_symm_comp` on the conjugate side — Seam 1's exact tool,
  one functor layer up (the "through `(Spec φ)_*`" transport is a `conjugateEquiv_comp`, not a
  positional rewrite, because `(Spec φ)_*` is itself the right adjoint of `(Spec φ)^*`).
- **Porting cost**: medium. No new Mathlib. Re-cut `base_change_mate_codomain_read_legs` to be
  proof-free and built from `leftAdjointCompIso`/`pullbackComp`; restate `_legs` at the explicit
  composite `e.hom ≫ Spec.map inclA`; engage `conjugateEquiv.injective/.surjective`.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib/CategoryTheory/Adjunction/Mates.lean` — `iterated_mateEquiv_conjugateEquiv` (450), `conjugateIsoEquiv` (412) + the conjugate-iso instances (380/388/396/405)
- **Domain**: generic mate / Beck–Chevalley calculus.
- **Same structural problem there**: the Beck–Chevalley 2-cell of a square whose four functors are
  left adjoints; when is it invertible.
- **Technique**: `iterated_mateEquiv_conjugateEquiv` rewrites the iterated mate as
  `conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α`; iso-ness then follows from
  `conjugateEquiv_iso` (the conjugate of an iso is an iso). This is the **abstract certificate** that
  the comparison is an iso without ever touching its concrete sheaf assembly.
- **Mapping to project**: this is the clean *statement-level* home for "the FBC comparison is an iso".
  But the project already has iso-ness for free via `conjugateIsoEquiv adjL adjR` at
  `pullback_spec_tilde_iso` (FlatBaseChange.lean:696); so this analogue's value is **conceptual /
  documentation** — it confirms the project's `conjugateIsoEquiv` encoding *is* the canonical
  Mathlib Beck–Chevalley reformulation, and that there is nothing further to import for (i).
- **Porting cost**: low (mostly already done). 
- **Verdict**: PARTIAL_ANALOGUE (solves (i), which the project already solved; does not by itself
  close the (ii) coherence — that needs the composite-conjugate idiom in the first analogue).

### Analogue: `unit_conjugateEquiv_symm` (Mates.lean:305), `conjugateEquiv_counit_symm` (287), `conjugateEquiv_comp`/`_symm_comp` (337/354), `Adjunction.comp_unit_app`/`comp_counit_app`
- **Domain**: generic conjugate component calculus — the exact tools that closed Seam 1 and Seam 3.
- **Same structural problem there**: transport a unit/counit across a conjugate of *composite*
  adjunctions, and compose conjugates of composites (= "paste of mates" at the conjugate level).
- **Technique**: `unit_conjugateEquiv_symm adjL adjR β.hom c` is the single-step unit-transport that
  closed `base_change_mate_unit_value`; `conjugateEquiv_comp`/`_symm_comp` (both `@[reassoc (attr :=
  simp)]`) fuse the per-adjunction conjugates of `adjL`/`adjR` into the conjugate of the composite —
  this is the conjugate-side form of `mateEquiv_vcomp`/`mateEquiv_square`. `Adjunction.comp_unit_app`
  (Basic.lean:585) / `comp_counit_app` (:590) split the composite unit/counit into the two
  per-adjunction factors.
- **Mapping to project**: the `_legs` coherence, once moved to the conjugate side by `.injective`, is
  a chain of these. The unit factor `F2` (the `e.hom`-unit through `(Spec φ)_* ⋙ Γ_R`) cancels the
  codomain read's `unit_iso.symm` by `unit_conjugateEquiv_symm` rather than by positional naturality;
  the `(Spec φ)_*`-layer transport is `conjugateEquiv_comp`.
- **Porting cost**: low (already proven idioms in this file — Seam 1/3 are templates).
- **Verdict**: ANALOGUE_FOUND.

## Top suggestion
**Re-encode the comparison object, then prove `_legs` entirely on the conjugate side — never as a
positional equation under the diamond.** Concretely: (1) rebuild
`base_change_mate_codomain_read_legs` proof-free from `Scheme.Modules.leftAdjointCompIso` /
`pullbackComp` / `pushforwardComp` of the free morphisms `e.hom`, `Spec.map inclA` (square enters via
`pushforwardCongr comm`), so no `hfst/hsnd` equality proof is carried; (2) restate
`base_change_mate_fstar_reindex_legs` at the explicit composite `e.hom ≫ Spec.map inclA`; (3) discharge
it by `apply (Scheme.Modules.conjugateEquiv …).injective` then close with the reassoc conjugate simp
set (`conjugateEquiv_comp`, `conjugateEquiv_symm_comp`, `conjugateEquiv_whiskerLeft/Right`,
`conjugateEquiv_associator_hom`) plus `conjugateEquiv_pullbackComp_inv` and the project's
pushforward-side `gammaMap_pushforwardComp_*` collapses, with the cross-layer `gammaPushforwardIso ψ`
naturality entering as `unit_conjugateEquiv_symm` + `conjugateEquiv_comp` (Seam-1 tool, one layer up).
First file to read: `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean` (lines 63–179, especially
`leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm` for the `surjective`→`injective`→reassoc template);
first project file to touch: `AlgebraicJacobian/Cohomology/FlatBaseChange.lean`,
`base_change_mate_codomain_read_legs` (~1210) and `base_change_mate_fstar_reindex_legs` (1381–1495).
Mathlib's API is **sufficient** — the composite-square mate is fully expressible; the only project-side
work is re-encoding the comparison to live natively in this calculus instead of as a hand-assembled
sheaf morphism. No Mathlib gap-fill is needed.
