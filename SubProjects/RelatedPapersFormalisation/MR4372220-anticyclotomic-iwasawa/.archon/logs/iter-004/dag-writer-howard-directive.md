# Blueprint Writer Directive

## Slug
iter-004-howard-kolyvagin

## Target chapter
blueprint/src/chapters/Howard_Kolyvagin.tex

## Strategy context
This chapter covers the Howard abstract Selmer-group bound and the Heegner-point Kolyvagin system construction — the two sub-phases of the Howard/Kolyvagin branch in the Greenberg-Vatsal comparison route. These sub-phases were previously vaguely described as "bridge lemmas"; the strategy now decomposes them into concrete blueprint declarations:

Sub-phase 1 (Howard abstract bound): prove the abstract Zp-twisted length bound `thm:Zp-twisted` and its Lambda-adic specialization `thm:howard`. This is the abstract machinery, independent of Heegner points.

Sub-phase 2 (Heegner KS): construct the nonzero Kolyvagin system from Heegner points (`thm:howard-HPKS`) and combine with `thm:howard` to obtain the divisibility `thm:howard-HP` needed by the main conjecture.

The chapter must also define the Selmer triple structure (`def:selmer-triple`) that sets up the local conditions for both sub-phases.

## Required content

The chapter header must include:
```
% archon:covers MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Howard.lean
```

Required declarations (in dependency order), each with `\label{}`, `\lean{}`, `\uses{}`, citation blocks, and `\begin{proof}...\end{proof}`:

1. **Definition `def:selmer-triple`** (`\lean{MR4372220.Howard.selmerTriple}`): Define the Selmer triple (T, F, v) consisting of a Galois representation T, a Selmer structure F (a collection of local conditions), and a distinguished prime v. Include the finite-singular comparison for a local condition at an auxiliary prime ell, and the modified Selmer condition that appears in the Kolyvagin-system Euler-system argument. `\uses{def:iwasawa-algebra}`. Source: Eisenstein.tex §A Kolyvagin system argument, "Selmer structures and Kolyvagin systems".

2. **Theorem `thm:Zp-twisted`** (`\lean{MR4372220.Howard.zpTwistedBound}`): For the Selmer triple associated to a height-one prime P of Lambda, if kappa is a Kolyvagin system for (T mod P, F_P) with kappa_1 nonzero, then length_{Z_p} Sel(K, T^* mod P) <= length_{Z_p} (Z_p / ind(kappa)). This is the Zp-twisted abstract Kolyvagin bound with the explicit error term. `\uses{def:selmer-triple, def:iwasawa-algebra}`. Source: Eisenstein.tex §A Kolyvagin system argument, "Bounding Selmer groups" and "Proof of Theorem thm:Zp-twisted".

3. **Theorem `thm:howard`** (`\lean{MR4372220.Howard.howardBound}`): Lambda-adic specialization of thm:Zp-twisted: for all but finitely many height-one primes P of Lambda, char(Sel(K, M_E)^vee) divides char(H^1_F(K, M_E[P^infty])^vee) in Lambda_P. The bound is stated at the level of characteristic ideals. `\uses{thm:Zp-twisted, def:selmer-triple, def:iwasawa-algebra}`. Source: Eisenstein.tex §A Kolyvagin system argument, "Proof of Theorem thm:howard".

4. **Theorem `thm:howard-HPKS`** (`\lean{MR4372220.Howard.heegnerKolyvaginSystem}`): The Heegner point Kolyvagin system is nonzero: kappa_1(HP) != 0, where HP denotes the Heegner point class. This relies on Cornut--Vatsal non-vanishing of Heegner points over the anticyclotomic tower. `\uses{def:selmer-triple, cor:characters}`. Source: Eisenstein.tex §A Kolyvagin system argument, "Proof of Theorem thm:howard-HPKS" and the Cornut--Vatsal input.

5. **Theorem `thm:howard-HP`** (`\lean{MR4372220.Howard.heegnerHoward}`): Combining the nonzero Heegner KS (thm:howard-HPKS) with the abstract Howard bound (thm:howard): char(X_E) divides char(L_E) (or the appropriate divisibility statement that feeds into the main conjecture). `\uses{thm:howard, thm:howard-HPKS, def:iwasawa-algebra}`. Source: Eisenstein.tex §A Kolyvagin system argument, "Proof of Theorem thm:howard-HP" and "Proof of the Iwasawa main conjectures" (the divisibility it produces).

Each declaration must have a `\begin{proof}...\end{proof}` block (not inline proof text) with a proof sketch sufficient for formalization. Cross-references via `\cref{...}` to blueprint labels.

## Out of scope
- The local Selmer/cohomology setup (Local_Iwasawa_Selmer.tex handles it).
- The analytic p-adic L-functions (Analytic_Iwasawa_Comparison.tex).
- The equivalence of main-conjecture formulations and the downstream applications (Main_Conjecture_Applications.tex).

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §A Kolyvagin system argument — all subsections: "Selmer structures and Kolyvagin systems", "Bounding Selmer groups", "Proof of Theorem thm:Zp-twisted", "Proof of Theorem thm:howard-HPKS", "Proof of Theorem thm:howard-HP". READ these sections verbatim before writing citation blocks.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction "Method of proof and outline of the paper" for the role of the Howard bound.

## Expected outcome
A complete `Howard_Kolyvagin.tex` chapter with 5 declaration blocks (def:selmer-triple, thm:Zp-twisted, thm:howard, thm:howard-HPKS, thm:howard-HP), each with source-backed citations from Eisenstein.tex, proper `\begin{proof}...\end{proof}` blocks, and accurate `\uses{}` edges connecting back to the local Selmer chapter and to each other. The chapter does NOT include content.tex changes.
