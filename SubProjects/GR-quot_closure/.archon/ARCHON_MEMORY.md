<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- `X.Modules`/value-ModuleCat diamond: positional `rw`/`simp`/`erw`, `comp_apply`, `hom_comp` all fail → term-mode + `change`-to-nested-application.
- SNAP (ACTIVE iter-006, user-directed): carrier `AddCommGrpCat` not `AddCommGrp`; `P⊗Q` = `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`. Stalkwise DEAD. `sectionMul_coherent` = FOUR cast-mediated component Eqs (TensorPower.Basic idiom: cast/cast_refl/one_mul/mul_one/mul_assoc/mul_comm), NOT one GradedMonoid Eq/HEq; reduce to presheaf level (eval @`op ⊤` is STRICT monoidal), ride η through tensorObjAssoc/tensorObjUnitIso/tensorPowAdd, pass through gradedMonoid_eq_of_cast. Foundations done axiom-clean. Reuse sibling-identical Lean names/signatures so `FBC-B_SNAP-chain` merge is a DEDUP not divergence.
- χ-BLOCKED: `def:hilbert_polynomial` (`Scheme.hilbertPolynomial`) is χ-semantic (`Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`, verified in QuotScheme.lean), needs higher cohomology this i=0 leg lacks. Keep it + `def:quot_functor` as sorry; fill from cohomology leg. NEVER build an H⁰ `Φ_s` under the χ label. `Scheme.Grassmannian`/`Grassmannian.representable` are χ-COUPLED AS ENCODED (re-export `QuotFunctor`→`hilbertPolynomial`); directive's "closable here" is aspirational — a χ-free re-encode would be a divergent shared body → merge conflict. Keep sorry; do NOT re-probe.
- Build with `lake build <module>` (LSP hides kernel timeouts); never add `maxHeartbeats 1e6`. No LLM API key in env.
- Merge-back: never rename kept decls/labels/paths; never add `\leanok` by hand. Lean names identical to parent+sibling. Blueprint-doctor broken `\ref`/`\uses` + 326 leandag-unmatched are EXTRACTION artifacts (labels/helpers outside the 3-seed cone); do NOT edit — they resolve at merge.
- DELIVERED (iter-001): goal seed `Grassmannian.represents` sorry-free + axiom-clean (disjoint from SNAP/χ — closing SNAP cannot disturb it). Open sorries: 9 SNAP (`SectionGradedRing.lean`, ACTIVE iter-006) + 4 χ (`QuotScheme.lean`, DEFERRED→cohomology leg, genuine gap) + out-of-cone debt.
