# Blueprint Writer Report: jacobian
**Status:** COMPLETE

## Changes
- Created `blueprint/src/chapters/Jacobian.tex` from scratch (new chapter `\chapter{Jacobian variety of a curve}`, `\label{chap:jacobian}`).
- Added `def:jacobian_av` (`jacobianAV`): Jac(C) as g-dim abelian variety with universal property and Pic^0 identification.
- Added `lem:jacobian_ppav` (`jacobianPpav`): principal polarization θ: Jac(C) → Jac(C)∨; uses `def:jacobian_av`.
- Added `def:abel_jacobi` (`abelJacobi`): Abel–Jacobi map P ↦ [O(P−P_0)]; uses `def:jacobian_av`.
- Added `thm:abel_jacobi_closed_immersion` (`abelJacobi_closedImmersion`): closed immersion for g≥2; uses `def:abel_jacobi`, `def:jacobian_av`.
- Added `def:faltings_zhang` (`faltingsZhang`): D_M on C^{M+1} → Jac(C)^M; uses `def:jacobian_av`, `def:abel_jacobi`.
- Added `lem:curve_generates_jacobian` (`curveGeneratesJacobian`): image of C generates Jac(C); uses `def:abel_jacobi`, `def:jacobian_av`, `lem:jacobian_ppav`.

## Notes / Strategy
- **content.tex must be updated** to add `\input{chapters/Jacobian}` before leandag picks up the new nodes; this file is outside my write-domain and was not edited.
