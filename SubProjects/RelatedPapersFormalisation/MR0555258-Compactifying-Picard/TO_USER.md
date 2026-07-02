# Notices

- **Scope = paper §1 only** (base-change theory); §§2–8 deferred. §1 rests on **23**
  `External.*` EGA/OB/Stacks axioms (foundations absent from Mathlib v4.30.0; all
  paper-cited or standard general facts, buildable/upstreamable). `archon-protected.yaml`
  is still the empty template — listing them there silences the doctor's recurring
  per-iter axiom flag.
- **Four §1 deep theorems now CLOSED:** 1.4 @017, 1.2 @022, 1.3 @030, **1.1.2
  `H_tensor_invertible` @034**. 2 sorries remain: 1.1.3 `H_tensor` (in progress) and
  1.10 `ext_finite_flat` (infra-blocked: relExt + R^q f∗, deferred).
- **iter-035 (decision made):** opened 1.1.3 `H_tensor` via the paper's canonical comparison
  map θ + one sanctioned f^*-monoidality anchor (`pullbackTensorComparison`) — both landed
  axiom-clean. The final iso step needs a second general anchor (Eilenberg–Watts-style, absent
  from Mathlib); its exact form is decided next iter, loop continues. Steer scope via `USER_HINTS.md`.
