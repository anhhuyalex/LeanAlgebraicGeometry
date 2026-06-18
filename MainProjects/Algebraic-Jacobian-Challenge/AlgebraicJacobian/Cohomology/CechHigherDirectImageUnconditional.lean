/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Cohomology.CechHigherDirectImage

/-!
# Unconditional `Rⁱ f_*` via Čech + flat base change (target-local roadmap)

These two declarations are **target-local** content preserved across the
enrich merge of the `Cech-Cohomology` subproject (2026-06-18). They originally
lived at the tail of the target's `Cohomology/CechHigherDirectImage.lean`, which
was replaced wholesale by the source library's (more fundamental and more
complete) `CechHigherDirectImage.lean`. The source development does not package
these two specific lemmas, so they are reinstated here on top of the merged
`CechComplex` so that the target's blueprint scope (`def:cech_higher_direct_image`,
`lem:cech_flat_base_change`) is preserved and its `\uses{}` graph stays intact.

* `cechHigherDirectImage` is sorry-free (a one-liner on the merged `CechComplex`).
* `cech_flatBaseChange` remains the target's pre-existing roadmap `sorry`
  (Stacks 02KH) — unchanged from before the merge.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S S' X X' : Scheme.{u}}

/-- **Unconditional higher direct image via Čech.** For a separated quasi-compact
`f : X ⟶ S`, a finite affine open cover `𝒰` of `X`, and a quasi-coherent
`F : X.Modules`, the `i`-th higher direct image is the `i`-th cohomology of the
relative Čech complex. This needs **no** enough-injectives hypothesis on
`O_X`-modules: it is the cohomology of an explicit complex of quasi-coherent
sheaves. By `cech_computes_higherDirectImage` it agrees with the derived-functor
higher direct image wherever the latter is defined, and is independent of the
chosen affine cover up to canonical isomorphism. For `i = 0` one recovers the
ordinary pushforward `R⁰ f_* F = f_* F`. -/
noncomputable def cechHigherDirectImage (f : X ⟶ S) (𝒰 : X.OpenCover)
    (F : X.Modules) (i : ℕ) : S.Modules :=
  (CechComplex f 𝒰 F).homology i

/-- **Flat base change for the Čech higher direct images** (Stacks 02KH,
`lemma-flat-base-change-cohomology`).

Given the cartesian square
```
  X' --g'--> X
  |f'        |f
  v          v
  S' --g---> S
```
with `f` separated and quasi-compact, `F` quasi-coherent, `F' = (g')^* F`, and
`g` flat, for every `i ≥ 0` the canonical base-change map between the
unconditional Čech higher direct images is an isomorphism
```
  g^*(Rⁱ f_* F) ≅ Rⁱ f'_* ((g')^* F).
```
Equivalently, for `S = Spec A`, `S' = Spec B` with `A → B` flat, the comparison
`Hⁱ(X, F) ⊗_A B → Hⁱ(X', F')` of `B`-modules is an isomorphism.

We state the isomorphism as `Nonempty (… ≅ …)`; `𝒰` and `𝒰'` are finite affine
covers of `X` and `X' = X ×_S S'` (the latter the base change of the former). -/
theorem cech_flatBaseChange
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (𝒰' : X'.OpenCover) [Finite 𝒰'.I₀]
    (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ) :
    Nonempty ((Scheme.Modules.pullback g).obj (cechHigherDirectImage f 𝒰 F i) ≅
      cechHigherDirectImage f' 𝒰' ((Scheme.Modules.pullback g').obj F) i) := by
  -- Proof (Stacks 02KH): local on `S'`, reduce to `S = Spec A`, `S' = Spec B`,
  -- `A → B` flat; base change of the cover and the affine `i = 0` base change give
  -- `Č•(𝒰_B, F_B) ≅ Č•(𝒰, F) ⊗_A B`, and flatness makes `- ⊗_A B` commute with
  -- `Hⁱ`. Needs the term-wise affine base change of the Čech complex and exactness
  -- of `- ⊗_A B` on `Scheme.Modules`, currently absent from Mathlib.
  sorry

end AlgebraicGeometry
