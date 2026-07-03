I now have everything needed. Confirmed: Mathlib provides `instance … : IsProper (pullback.snd f g)` automatically, so the `ofCurve` delegation typechecks.

---

# T12 / `AJC.picrep` — sorry triage for FGA Picard-representability cone

## Classification table

| file:line | decl | Stacks / Nitsure ref | class | one-line justification |
|---|---|---|---|---|
| FGAPicRep:185 | `instHasDivFunctor` | Kleiman §3 `th:repDiv` / bp `Picard_QuotScheme` | **B** | target is `Nonempty (functorᵒᵖ ⥤ Type)` — trivially inhabited by a const functor; opaque either way. |
| FGAPicRep:244 | `instHasPicScheme` | Kleiman §4 `th:main`+`cor:algsch`+§2 Thm 2.5 | **C/A** | the actual FGA representability theorem; the file's single genuine deep sorry. |
| FGAPicRep:291 | `instHasAbelMap` | Kleiman §3 `dfn:Abel`+`th:repDiv` | **B** | target `Nonempty (divFunctor ⟶ picSharp)`; `picSharp = relPresheaf ⋙ forget AddCommGrpCat` is group-valued ⇒ zero natural transformation exists. |
| FGAPicRep:508 | `instPicSchemeLocallyOfFiniteType` | Kleiman §4 `th:main`(1) | **C** | property of the `Classical.choose` witness of 244; not provable until 244's construction lands. |
| QuotScheme:173 | `hilbertPolynomial` (body) | `def:hilbert_polynomial`, Nitsure §1 / Hart. III.5.2 | **A** | needs graded Euler characteristic χ + Snapper polynomiality — absent in Mathlib. |
| QuotScheme:212 | `QuotFunctor` (body) | `def:quot_functor`, Nitsure §1 | **A** | flat coherent quotients on relative product + Hilbert-poly cut + Setoid quotient. |
| QuotScheme:248 | `Grassmannian` (body) | `def:grassmannian_scheme` | **A** | re-export of `QuotFunctor` (212); blocked on it. |
| QuotScheme:275 | `Grassmannian.representable` | `thm:grassmannian_representable`, Nitsure §1 | **A** | glue `C(r,d)` charts along Plücker cocycle; deep. |
| QuotScheme:330 | `QuotScheme` | `thm:quot_representable`, Nitsure §5 / FGA | **A** | four-step boundedness→Grassmannian→flattening→valuative; the headline. |
| QuotScheme:596 | `pullback_tildeIso` | Stacks 01HQ / 0BJ8 | **A/hard-B** | "pullback of tilde = tilde of base change"; genuine Mathlib gap, Σ-pair section identity. |
| QuotScheme:620 | `pushforward_isQuasicoherent` | Stacks 01XJ | **A/hard-B** | qcqs pushforward preserves qcoh; Mathlib lacks it, project only has iso-pushforward + unfinished Čech qcqs machinery. |
| QuotScheme:676 | `tildeIso_of_isQuasicoherent_isAffineOpen` | Stacks 01I8 | **B (risky)** | sheaf iso already proved in project (`qcoh_iso_tilde_sections`, `pullbackRestrict_iso_tilde`); residual is the Σ-pair section transport, project-flagged `NEEDS_MATHLIB_GAP_FILL`. |
| QuotScheme:1065 | `pullback_app_isoTensor` (…sectionLinearEquiv Stages 2–6) | Stacks 01HQ / 02KE | **A** | multi-stage section formula; depends on 596 + 676. |
| QuotScheme:1227 | `…isIso_of_isAffineOpen_of_isAffineBase` | Stacks 02KE / 00H8 | **A** | Beck–Chevalley intertwining; depends on 1065 + 596. |
| QuotScheme:1278 | `…isIso_of_isAffineOpen` | Stacks 02KE / 00H8 | **A** | base-side Mayer–Vietoris descent to affine base, not built. |
| QuotScheme:1328 | `…isIso_of_affineCover` | Stacks 02KH(ii) | **A** | needs `Sheaf.Hom.isIso_on_basis` MV descent, not in scope. |
| FlatStrat:294 | `genericFlatness` | `thm:generic_flatness`, Nitsure §4 | **A** | Noether normalisation + generic freeness. |
| FlatStrat:338 | `flatLocusStratification` | `lem:flat_locus_open`, Nitsure §4 (Lem 5) | **A** | Fitting-ideal rank strata. |
| FlatStrat:367 | `flatLocusReduction` | `lem:nonflat_locus_proper`, Nitsure §4 (Lem 6) | **A** | Noetherian induction on closed complement. |
| FlatStrat:399 | `flatLocusAssembly` | `lem:noetherian_induction_strata`, Nitsure §4 (Lem 7) | **A** | direct images `E_i=π_*𝓕(N+i)` + Hilbert-poly indexing. |
| FlatStrat:445 | `flatteningStratification` | `thm:flattening_stratification_exists` / Stacks 052H | **A** | assembles 367+399; the headline. |
| FlatStrat:487 | `flatteningStratification_universal` | Nitsure §4(ii) / 052H | **A** | Yoneda universal property of the strata. |
| FlatStrat:530 | `flatteningStratification.ofCurve` | Nitsure §4 corollary (Route-A) | **C→B** | pure reduction: `exact flatteningStratification (pullback.snd C.hom T.hom) F`; `IsProper (pullback.snd …)` auto from Mathlib. Closable now. |

## Ranked shortlist (most valuable + achievable)

1. **`flatteningStratification.ofCurve` (FlatStrat:530).** *Achievable:* its conclusion is literally `flatteningStratification`'s conclusion with `π := pullback.snd C.hom T.hom`, `S := T.left`; Mathlib's `instance … : IsProper (Limits.pullback.snd f g)` (Proper.lean:78) supplies properness from `[IsProper C.hom]` automatically, so `exact flatteningStratification (pullback.snd C.hom T.hom) F` should close it. This is a *correct* proof (delegation to the main theorem), not a placeholder witness — it removes a leaf sorry and wires the Route-A consumer to the theorem. Low risk. Caveat: it rests on the still-sorry 445, so it does not reduce axiom-debt, only leaf count.

2. **`instHasAbelMap` (FGAPicRep:291).** *Achievable:* `picSharp C = PicSharp.relPresheaf C ⋙ forget AddCommGrpCat` is group-valued, so the zero natural transformation `divFunctor C ⟶ picSharp C` (components `fun _ => 0`, naturality by `map_zero` of the group-hom restrictions) inhabits the required `Nonempty`. Moderate NatTrans plumbing; genuine (if placeholder) Abel-map carrier.

3. **`instHasDivFunctor` (FGAPicRep:185).** *Achievable:* `⟨(CategoryTheory.Functor.const _).obj (ULift Unit)⟩` inhabits `Nonempty (…ᵒᵖ ⥤ Type (u+1))`. Guaranteed one-liner; lowest mathematical value (the functor is opaque by design either way).

Honourable mention (highest math value, **not** a safe one-session close): **`tildeIso_of_isQuasicoherent_isAffineOpen` (676, Stacks 01I8).** The project already owns the unconditional sheaf-level result — `AlgebraicJacobian/Cohomology/QcohTildeSections.lean` (`qcoh_iso_tilde_sections`, 0 sorries) and `CechHigherDirectImageUnconditional.pullbackRestrict_iso_tilde`. But the QuotScheme helper demands a specific `Σ`-pair section-level identity (`iso.inv ∘ tilde.toOpen = pullback_app_isoTensor_baseMap`), which is exactly the "01HQ transport / section-vs-tensor" gap the project flags as un-closed. Real content is there; matching the section identity is likely more than one session.

## Verdict

No headline theorem is realistically closable in one session. `hilbertPolynomial`, `QuotFunctor`/`QuotScheme`, `Grassmannian`/`Grassmannian.representable`, `genericFlatness`, and `flatteningStratification`(+`_universal`) each require machinery Mathlib v4.31 simply does not have — relative ℙⁿ_S, coherent-sheaf χ / Snapper polynomiality, Castelnuovo–Mumford boundedness, Fitting-ideal rank strata, generic freeness — and the project's own supporting engine (the Čech flat-base-change route `cech_flatBaseChange`, Stacks 02KH, in `Cohomology/`) is itself unfinished: `CechHigherDirectImageUnconditional.lean` still carries 41 sorries and `FlatBaseChange`/`FlatBaseChangeGlobal` carry 2/1, so the QuotScheme §5 base-change chain (596/620/1065/1227/1278/1328) cannot yet be discharged from existing infrastructure. The genuinely valuable tilde/base-change helpers all bottom out in the same un-closed "01HQ / 02KE section-vs-tensor transport" gap. Realistic one-session work is therefore limited to (i) the correct leaf reduction `ofCurve → flatteningStratification` (530), and (ii) the FGA `Nonempty` carriers 185 and 291 (const functor / zero natural transformation) — sorry-eliminations of modest but real value, none of which advances a headline result.
