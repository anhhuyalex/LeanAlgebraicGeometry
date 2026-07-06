You are adversarially verifying ONE load-bearing correctness claim from the current Horizon T14 session (project: Algebraic-Jacobian-Challenge), plus the faithfulness of 5 small new lemmas. Do NOT edit files (you are read-only). Report your verdict back to me in your final message, and file a concise `horizon inbox` note only if you find a genuine defect.

## Claim to verify (the important one): the Serre-twist sign convention

File `MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/SerreTwist.lean` defines `ProjTwist.serreTwist n m` on `Proj ℤ[X_i : i ∈ n]` by gluing trivial line bundles `O_{D₊(X_i)}` over the standard cover with transition isomorphisms. Key definitions to read:
- `awayFraction n i j` (~line 187): claimed to be `X_i / X_j` in the degree-0 localization `(ℤ[X]_{X_i X_j})₀`. Verify it really is X_i/X_j (numerator X_i·X_i, denominator (X_i X_j)^1).
- `twistTransition n m i j` (~line 329): `pullbackUnitIso (f i j) ≪≫ unitScalarIso ((overlapUnit i j)^m) ≪≫ (pullbackUnitIso (t i j ≫ f j i)).symm` — i.e. multiplication by `(X_i/X_j)^m`, going from the pullback of the chart-`i` structure sheaf to the pullback of the chart-`j` structure sheaf, in `Scheme.Modules.glue`.

THE QUESTION: does this gluing datum define `O(m)` or `O(-m)`? Derive it INDEPENDENTLY from scratch (do not just re-confirm the session's reasoning). Standard approach: identify the local frame on `D₊(X_i)` implied by the trivialization, express it in the `j`-frame, and compare to the transition `(X_i/X_j)^m`; then compute the global sections `Γ(Proj, serreTwist n m)` as compatible families and check whether they are degree-`m` homogeneous polynomials (⟹ O(m), O(1) very ample) or zero for m>0 (⟹ O(-m)). State clearly: O(m) or O(-m), with the frame identity and the global-sections computation. The session claims O(m) (frame X_i^m, Γ(O(1)) = linear forms). Confirm or refute.

## Also sanity-check (faithfulness / non-vacuity, quick) — 5 new lemmas in `AlgebraicJacobian/Picard/ProjectiveMorphism.lean`:
- `Scheme.Hom.IsProjectiveWith.locallyOfFiniteType`, `.isSeparated`, `.universallyClosed` — each derives the named property from `.isProper`. Check the statements are the intended ones (not vacuous / not mis-stated).
- `Scheme.Hom.IsProjectiveWith.of_iso` — transfer of `IsProjectiveWith π L` to `L'` along `e : L ≅ L'`. Check direction is right.
- `ProjectiveSpace.isProjectiveWith_over (d S)` — `(ℙ(Fin (d+1); S) ↘ S).IsProjectiveWith (twistingSheaf (Fin (d+1)) S 1)` via the identity closed immersion. Check it is genuinely non-vacuous (identity is a closed immersion; the O(1) comparison is pullback-along-identity).

All 5 are already machine-verified axiom-clean, so focus on whether the STATEMENTS are faithful, not the proofs.

Return: a crisp verdict on the sign (O(m) vs O(-m)) with your independent derivation, and a one-line OK/NOT-OK for each of the 5 lemma statements.
