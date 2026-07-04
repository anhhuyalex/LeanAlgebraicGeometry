You are scouting Mathlib source code inside a Lean 4 project. Working directory: /home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge. The Mathlib source is under .lake/packages/mathlib/Mathlib/.

Find and report EXACT Lean signatures (copy the source text, with file paths and line numbers) for the following, in Mathlib's AlgebraicGeometry ideal-sheaf / closed-immersion API (look in .lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf.lean or similarly named files, and Morphisms/ClosedImmersion.lean):

1. `Scheme.IdealSheafData` — the structure fields, and its lattice/order: how is `≤` between two IdealSheafData defined? Any `le_iff` / ext lemmas.
2. `Scheme.IdealSheafData.subscheme`, `subschemeι`, and every lemma about sections/app of `subschemeι`: e.g. is there `subschemeι_app`, a surjectivity lemma, or a description `Γ(I.subscheme, subschemeι ⁻¹ᵁ U) ≅ Γ(X,U)/I(U)`? Report ALL declarations mentioning `subscheme` in that file (names + full signatures).
3. `Scheme.Hom.ker` — full definition (is it defined via some `ofIdeals`-style largest-ideal-sheaf-below construction?), plus lemmas: `ker_apply` (with what hypotheses, e.g. [QuasiCompact]), any `le_ker_iff`-style lemma, `ker_subschemeι` (or `subschemeι_ker`) stating the kernel of subschemeι equals the ideal sheaf datum.
4. `IsClosedImmersion.lift` and `IsClosedImmersion.lift_fac` (or similarly-named factorization-through-closed-immersion lemmas) — exact signatures, exact hypothesis shape (which direction the `.ker ≤ .ker` condition points), and any uniqueness lemma. Also confirm whether `IsClosedImmersion` gives `Mono` (name of instance).
5. Any `Scheme.IdealSheafData.support` lemmas: `range_subschemeι`, `mem_support_iff_of_mem` — full signatures.
6. `IsAffineOpen.preimage` behavior under closed immersions or affine morphisms: the lemma that says the preimage of an affine open under an affine morphism (or closed immersion) is affine — exact name and signature.
7. In the same area: any `IdealSheafData.ofIdeals` (or similar) with `le_ofIdeals_iff` — exact statement.

Return raw data: for each item, file path, line number, and the verbatim declaration (docstring optional). If something does not exist, say so explicitly and name the closest thing you found.
