<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- `X.Modules`/value-ModuleCat diamond: positional `rw`/`simp`/`erw`, `comp_apply`, `hom_comp` all fail → term-mode + `change`-to-nested-application.
- SNAP (ACTIVE): carrier `AddCommGrpCat`; `P⊗Q`=`MonoidalCategory.tensorObj (C:=MonoidalPresheaf X) P Q`. Stalkwise DEAD. iter-007 PIVOT (analogist ALIGN, `analogies/tensorobjassoc.md`): do NOT hand-prove coherence over the obfuscated double-braiding `tensorObjAssoc` — BUILD `(J.W.inverseImage (toPresheaf R₀)).IsMonoidal` (whiskerRight=`ztensor_whisker_localIso` DONE; whiskerLeft=braiding-conjugate via `PresheafOfModules.symmetricCategory`) + `LocalizedMonoidal` ⇒ inherit `MonoidalCategory`/`SymmetricCategory X.Modules` (assoc/pentagon/triangle/hexagon FREE). Module sheafification IS the localization (`ModuleCat/Sheaf/Localization.lean:48`). NOT free: `J.W(AddCommGrpCat).IsMonoidal`, inverseImage-along-monoidal-functor (`toPresheaf` oplax). SNAP layer self-contained, used by no other file ⇒ refactor cannot disturb `represents`.
- χ-BLOCKED: `def:hilbert_polynomial` (`Scheme.hilbertPolynomial`) is χ-semantic (`Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`, verified in QuotScheme.lean), needs higher cohomology this i=0 leg lacks. Keep it + `def:quot_functor` as sorry; fill from cohomology leg. NEVER build an H⁰ `Φ_s` under the χ label. `Scheme.Grassmannian`/`Grassmannian.representable` are χ-COUPLED AS ENCODED (re-export `QuotFunctor`→`hilbertPolynomial`); directive's "closable here" is aspirational — a χ-free re-encode would be a divergent shared body → merge conflict. Keep sorry; do NOT re-probe.
- Build with `lake build <module>` (LSP hides kernel timeouts); never add `maxHeartbeats 1e6`. No LLM API key in env.
- Merge-back: never add `\leanok` by hand. SNAP intentionally DIVERGES from sibling iter-007 (Mathlib-aligned monoidal localization vs hand-rolled; sibling stuck 9 sorries same wall) — merge is reconciliation, not dedup. Blueprint-doctor broken `\ref`/`\uses` + leandag-unmatched are EXTRACTION artifacts (outside the 3-seed cone); do NOT edit — resolve at merge.
- DELIVERED (iter-001): goal seed `Grassmannian.represents` sorry-free + axiom-clean (disjoint from SNAP/χ). Open sorries: 3 SNAP (`SectionGradedRing.lean`, coherence laws — close via inherited monoidal structure) + 4 χ (`QuotScheme.lean`, DEFERRED→cohomology leg) + out-of-cone debt.
