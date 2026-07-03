All committed and clean. Final report:

## Summary

Advanced the `AJC.pic0av` cone per the Ground recommendation: closed the group-structure leg of the Pic⁰ abelian-variety statement (Ground's "provable now" suggestion) and landed the first brick of the `tangentSpaceIso` (Kleiman 5.11) block — the truncated-exponential splitting of dual-number units, natural in the base ring. Full AJC build green (8642 jobs); everything committed (`fff376a`, `c1c933d9a2`).

## Progress

- **`Pic0.grpObj` proved sorry-free**: `Nonempty (GrpObj (Pic0Scheme C))` via `IdentityComponent.isSubgroupHomomorphism (PicScheme C)`; instances came straight from `groupSchemeStructure` + the LFT projection.
- **`Pic0.tangentSpaceCotangentDual`** no longer takes the group-structure hypothesis (now derived internally).
- **`Pic0.geometricallyIrreducible`** proved as the substrate specialisation; the remaining math obligation is consolidated in the sibling's QC∧GeomIrred sorry.
- **`Pic0.isAbelianVariety` assembled sorry-free** from the four conjuncts; **`Pic0Scheme.isAbelianVariety` moved** from `IdentityComponent.lean` to `Pic0AbelianVariety.lean` and proved (blueprint pin unchanged, name-based). Sorry counts: `IdentityComponent.lean` 6→4, `Pic0AbelianVariety.lean` 5→3 (left: `tangentSpaceIso`, `smooth`, `proper`).
- **New `Picard/DualNumberUnits.lean`** (~330 LOC, Mathlib-only imports, axiom-clean = `propext/choice/Quot.sound`): split exact `1 → (R,+) → (R[ε])ˣ → Rˣ → 1`, `unitsEquivProd : (R[ε])ˣ ≃* Rˣ × (R,+)`, functorial `mapRingHom : R[ε] →+* S[ε]` + naturality; registered in the root import list.
- **Blueprint**: new `thm:pic0_group_structure` node; `thm:pic0_tangent_cotangent_dual` rewired onto it; GI + both assembly proofs marked `\leanok`; new `sec:pic0_trunc_exp` subsection (15 nodes) wired into the `thm:pic0_tangent_space_iso` proof. DAG: 2134 nodes, 0 dangling, 1773 proved.
- Reporting: roadmap comment on `AJC.pic0av`, task comment on T5, inbox memory `I-0082` superseding the stale "9 sorries blocked" note.

## Issues

- T5's original extraction mandate (STEP 1) was obsolete — the FGA rewire already made the cone attackable in AJC, and `SubProjects/Picard-IdentityComponent` is out of this session's write scope; it remains stale (re-sync or retire is still open, flagged in the task comment).
- I marked proofs `\leanok` whose own Lean bodies are sorry-free but which `\uses` sorried ancestors (GI, both assemblies) — standard leanblueprint semantics, but Ground should revert if house style reads `\leanok` closure-strictly.
- `Pic0.geometricallyIrreducible` / the assemblies are proved but still sorryAx-tainted through upstream carriers (FGA + the QC∧GeomIrred conjunct) — expected, documented in-file.

## Next

- `tangentSpaceIso` brick 2: dual-number points of `Pic0Scheme` ↔ `ker(picSharp(Spec k[ε]) → picSharp(Spec k))` via `(representable C).homEquiv` (clopen ⟹ Pic vs Pic⁰ dual-number points at the identity agree).
- Brick 3: sheaf-level truncated-exponential sequence on `C_ε = C ×ₖ Spec k[ε]` (identify `O_{C_ε}` sections with `O_C(U)[ε]`, then apply `DualNumberUnits` naturality), then the Čech `H¹(O^×)` cocycle classification.
- Independent: the `smooth`/`proper` conjuncts (Chevalley–Rosenlicht / Kleiman Thm 5.4) and the EGA IV₂ 4.6.1-type input for QC∧GeomIrred remain the other large open legs.
