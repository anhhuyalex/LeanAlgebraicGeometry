/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Genus0BaseObjects.BareScheme
import AlgebraicJacobian.Genus0BaseObjects.ChartIso
import AlgebraicJacobian.Genus0BaseObjects.Points
import AlgebraicJacobian.Genus0BaseObjects.Cross01Substrate
import AlgebraicJacobian.Genus0BaseObjects.GmScaling

/-!
# Genus-`0` base objects — re-export shim

Iter-175 split this file into four sub-modules. All declarations are re-exported
from their new homes via `import` (Lean has no `export` ceremony for non-namespaced
decls — re-export is automatic from imports).

* `BareScheme.lean` — `ProjectiveLineBar` scheme + the 2-chart affine cover.
* `ChartIso.lean`   — `HomogeneousLocalization.Away 𝒜 (X i) ≃+* k̄[u]` chart-ring iso
                     + its load-bearing helpers.
* `Points.lean`     — `k̄`-points `0`, `1`, `∞` on `ℙ¹`; `Ga`; `Gm`.
* `GmScaling.lean`  — chart-bridge + `σ_× : ℙ¹ × 𝔾_m → ℙ¹` action + product-stability
                     instances on `ℙ¹ ⊗ 𝔾_m`.

Downstream files that `import AlgebraicJacobian.Genus0BaseObjects` see exactly the same
surface as before the split.
-/
