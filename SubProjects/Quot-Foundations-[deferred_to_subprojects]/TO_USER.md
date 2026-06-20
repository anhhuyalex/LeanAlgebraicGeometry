<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Proving healthy on `opus`** (iters 078–080 closed 9 sorries → 9 left, 0 axioms, builds green); 3 lanes
  active iter-081. FBC goal leg routes via the DIRECT H⁰-equalizer (Stacks 02KH.2); its capstone
  `baseChangeGammaPullbackEquiv` stub landed this iter (signature analogist-verified). The old adjoint-mate
  apparatus is abandoned/dead-code. Restore a `fable` lane only with valid creds.
- **Scope decision (iter-081, made):** the parent's `def:hilbert_polynomial` is the **Euler characteristic
  χ**, which needs higher cohomology this i=0 / Čech-independent leg does NOT have. So this leg will NOT
  formalize the Hilbert polynomial or the general Quot functor (they belong to the sibling cohomology leg);
  it delivers the χ-independent Grassmannian core (representability via rank-d locally-free quotients).
  Override via `USER_HINTS.md` if the parent intends a different split.
- **Two loop-infra bugs (user-side fix, non-blocking):** (a) `sync_leanok` strips the 22-name multi-decl
  `\lean{}` pin on `lem:relativeTensor_objectwise_coequalizer` when that SNAP chapter is touched (review
  re-applies by hand); (b) the leandag unmatched-decl scan counts `private` decls, inflating coverage debt.
  RelativeSpec Stacks tags (01LM/01LP/01LT) reference-retrieved otherwise.
