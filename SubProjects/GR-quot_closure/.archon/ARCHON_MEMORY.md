<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- `X.Modules`/value-ModuleCat diamond: positional `rw`/`simp`/`erw`, `comp_apply`, `hom_comp` all fail → term-mode + `change`-to-nested-application.
- SNAP: carrier `AddCommGrpCat` not `AddCommGrp`; `P⊗Q` = `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`. Stalkwise DEAD. `sectionMul_coherent` = FOUR cast-mediated component Eqs (TensorPower.Basic idiom), NOT one GradedMonoid Eq/HEq. SNAP is SHARED with sibling `FBC-B_SNAP-chain` — keep as sorry or import its proofs, don't diverge.
- χ-BLOCKED: `def:hilbert_polynomial` (`Scheme.hilbertPolynomial`) is χ-semantic (`Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`, verified in QuotScheme.lean), needs higher cohomology this i=0 leg lacks. Keep it + `def:quot_functor` as sorry; fill from cohomology leg. NEVER build an H⁰ `Φ_s` under the χ label (the blueprint ENCODING comment claiming H⁰ is wrong; Lean governs).
- Build with `lake build <module>` (LSP hides kernel timeouts); never add `maxHeartbeats 1e6`. No LLM API key in env.
- Merge-back: never rename kept decls/labels/paths; never add `\leanok` by hand. Lean names identical to parent + sibling.
