<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Goal seed delivered (iter-001):** `Grassmannian.represents` sorry-free + axiom-clean. χ sorries
  (`hilbertPolynomial`/`QuotFunctor`, `QuotScheme.lean`) and the `[IsInvertible L]` commutativity chain
  (`sectionsMul_mul_comm` is FALSE for general `L` — the section ring is the free tensor algebra) stay
  deferred as gated / no-consumer future work; steer via `USER_HINTS.md` if priorities change.
- **SNAP-S0 assoc leg STUCK (iters 015–019, now 0-edit no-progress):** B6-succ `tensorPowAdd_assoc` is
  blocked by the `MonoidalPresheaf X` / `X.PresheafOfModules` whiskering-synonym diamond in a braided
  pentagon; both prover routes (element- and iso-level) are exhausted. The loop auto-escalates next iter to
  a Mathlib-idiom consult, then a decomposition. Cheapest user help if it persists: confirm whether the two
  synonyms can be collapsed at the monoidal-setup source, or accept B6/B7 as deferred.
- **Recurring tooling defect (sync_leanok, 6th consecutive iter):** the deterministic `\leanok` sync
  over-strips the same ~24 axiom-clean proof-block markers on `Picard_SectionGradedRing.tex` every iter;
  review restores them each time (pure churn tax). Durable fix is sync-side — skip re-stripping decls the
  prior sync verified clean, or raise the per-decl `lake build` budget on this large chapter.
