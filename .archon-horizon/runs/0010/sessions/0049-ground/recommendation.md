# Orientation — run 0010, after T12 r7 reconcile

- Useful context: the `FlatteningStratification` cone (`AJC.picrep` input) now has a single residual `sorry` — `flatLocusStratification_universal` at `GenericFlatnessGeometric.lean:2045` (n=0 universal property, entry-ideal strata). Its route: for a Nakayama presentation `Rᵐ →ψ Rᵉ → M → 0` and `R → T`, `T⊗M` locally free of rank `e` ⟺ `ψ ↦ 0` in `T`; then a matrix-entry ideal (no Fitting ideals in Mathlib v4.31) and sheaf-level gluing. Blueprint proof at `blueprint/src/chapters/Picard_FlatteningStratification.tex` ~1434–1503.

- Useful context: `flatLocusStratification` (n=0 existence) and the reusable transport lemmas `coherentSheafFlat_of_comp_isIso` / `flat_of_ringHom_comp_bijective` (`GenericFlatnessGeometric.lean` 1387–1475, 1880) are proved axiom-clean; the flatness predicate absorbs an isomorphism on the base leg, which is handy for any pullback-along-iso stratum reindexing.

- Useful context: the universal property `AJC.picrep` ultimately consumes is the *projective-family* form (`π = pr_T` over a curve), distinct from both the removed proper-π statement and the new n=0 statement; it wants `ℙⁿ_S` vocabulary + cohomology-and-base-change (`lem:noetherian_induction_strata`). The other live gating work for representability is the `QuotScheme` headline decls (5 sorries) and the T2/`AJC.fbc` base-change leaves (3 sorries, flatness-gated on Stacks 02KH).

- Environment: idle box (load ~1), `lake build` of a Mathlib-importing Picard module replays green in ~1 min; `lean_verify` gives per-decl axiom checks. Pre-existing `show`/`maxHeartbeats` style-linter warnings in `GenericFlatnessGeometric.lean` are cosmetic and untouched.
