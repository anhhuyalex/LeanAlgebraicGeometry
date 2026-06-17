# `base_change_mate_fstar_reindex_legs` — the cross-layer naturality crux

File: `AlgebraicJacobian/Cohomology/FlatBaseChange.lean` (`_legs` @~1381, residual `sorry` @~1495).
Status after iter-033: direct-on-sections term-mode splicing has bottomed out. The HARD COMMIT
in PROGRESS.md (iter-033 lane 1) is reached: this is the point to pivot to the ModuleCat / mate
re-encoding (STRATEGY Open Q2 arm a).

## What is now landed in the locked goal (term mode only — keyed `rw`/`simp` is dead)

The proof of `_legs`, after `subst hfst; subst hsnd`, reaches a locked goal under the `X.Modules`
instance diamond where NO keyed `rw`/`simp`/`erw`/`conv` fires (re-verified iter-033: even a
`rfl`-proven `= 𝟙` fact whose LHS is the goal's printed factor is not located). The following are
spliced in via `congrArg`/`.trans` (term mode):

1. `base_change_mate_fstar_reindex_legs_link_distributeCollapse` — distributes the inner
   `(g')`-unit into the three reduced factors `F1 ≫ F2 ≫ F3`
   (`Γ(G η^{Spec ιA}) ≫ Γ(G ((Spec ιA)_* η^{e.hom})) ≫ Γ(G ((e≫Spec ιA)_* pullbackComp.hom))`,
   `G = (Spec φ)_*`).
2. `simp only [base_change_mate_codomain_read_legs, …]` unfolds the codomain read (its `.hom`
   exposes `iso_g = pullbackCongr(hfst) ≫ pullbackComp(e,inclA).symm`, `unit_iso.symm =
   (asIso η^{e.hom}).symm`, `pushforwardComp(e,inclR').symm`, then the two affine tilde dictionaries
   and the tilde–Γ counit).
3. **NEW iter-033:** the trailing transparent `pushforwardComp(g', Spec φ).hom` factor is collapsed
   to `𝟙` via `congrArg … keyPFC` (`keyPFC := gammaMap_pushforwardComp_hom_eq_id …`). This is the
   factor PROGRESS flagged as "even the trivial trailing pushforwardComp resists keyed collapse";
   it is now collapsed in term mode.

Residual goal (schematic):
```
gPTI(φ,M).inv ≫ (F1 ≫ F2 ≫ F3) ≫ (𝟙 ≫ eqToHom ≫ 𝟙) ≫ (gammaPushforwardIso ψ …).hom
  ≫ (restrictScalars ψ).map (CODOMAIN_READ.hom)
  = base_change_mate_inner_value ψ φ M
```

## The genuine remaining obstacle (NOT adjacency bookkeeping)

The cancellation that must happen:
- **F2** (the `e.hom`-unit `Γ(G ((Spec ιA)_* η^{e.hom}))`) lives in the **`(Spec φ)_* ⋙ Γ_R`**
  image (read over `Spec R`).
- It must cancel the codomain read's **`unit_iso.symm = (asIso η^{e.hom}).symm`**, which lives in the
  **`Γ_R' → gammaPushforwardIso ψ → restrictScalars ψ`** image (read over `Spec R'`, then transported
  down to `Spec R`).
- Similarly **F3** (`pullbackComp(e,inclA).hom`) must cancel `iso_g`'s `pullbackComp(e,inclA).symm`
  across the same layer transport.

Because the two members of each cancelling pair sit in **different functor images**
(`(Spec φ)_* ⋙ Γ_R` vs the codomain's `Γ_R'`-then-`gammaPushforwardIso ψ`-then-`restrictScalars ψ`),
the cancellation is **not** a reassociate-and-`Iso.inv_hom_id` step. It requires the **naturality of
`gammaPushforwardIso ψ`** (equivalently `gammaPushforwardNatIso ψ`, already proved @~735) bridging the
`Spec R`-reading of `(Spec φ)_*` to the `Spec R'`-reading used by the codomain read.

This is the SAME `conjugateEquiv`/mate coherence that closed **Seam 1**
(`base_change_mate_unit_value`, @~987, which used `CategoryTheory.unit_conjugateEquiv_symm` on the two
composed adjunctions rather than explicit factor cancellation). The direct factor-by-factor route does
not have access to that coherence at the reindex layer.

## Precise missing ingredient (for `mathlib-build` / re-encoding)

A naturality/conjugate lemma of the form: the leg-reindex composite
`(pullbackPushforwardAdjunction g').unit ≫ pushforward-coherences`, read through `(Spec φ)_* ⋙ Γ_R`
and conjugated by `base_change_mate_codomain_read`, equals `restrictScalars ψ` applied to the
conjugate (`conjugateEquiv`) of the `e.hom`-unit — i.e. the mate of the pasted pullback square,
expressed via `CategoryTheory.mateEquiv` / `conjugateEquiv` for the composite adjunctions
`adjL = (tilde ⊣ Γ)_R . (g^* ⊣ g_*)` and `adjR = (extend ⊣ restrict)_ψ . (tilde ⊣ Γ)_{R'}`,
with `β = gammaPushforwardNatIso ψ`. Concretely this is the Seam-1 `unit_conjugateEquiv_symm`
argument transported one functor layer up (through `(Spec φ)_*`).

### Recommended iter-034 action (STRATEGY Open Q2 arm a)
Re-encode `_legs` at the `ModuleCat`/`SheafOfModules` level so the comparison is assembled directly by
the abstract mate calculus (`conjugateEquiv`/`mateEquiv`), as Seam 1 did, and the `X.Modules` diamond
never forms. The explicit-factor telescoping should be abandoned — every keyed tactic is dead under
the diamond and the surviving term-mode route bottoms out at this cross-layer naturality, which has
no term-mode expression without the conjugate lemma above.
