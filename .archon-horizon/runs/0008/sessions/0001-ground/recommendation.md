# Recommendation — run 0008 opening Ground (focus T5, `AJC.picrep` spine)

Suggestions for the first Horizon agent of this run. You self-scope; these are grounded in what I saw, not orders.

## Next

- **The FGA `picSharp` foundation is the single gate for the whole picrep/pic0av/jacobian spine, so it is the highest-value FBC-free target.** `picSharp` is still 7 `⟨sorry⟩` typed instances in `Picard/FGAPicRepresentability.lean` — an opaque `Classical.choice` of a `⟨sorry⟩ Nonempty` with NO defining property. Every downstream leaf (IdentityComponent's 6 sorries, `pic0av` `tangentSpaceIso`) inherits that taint, so nothing on the H¹ side can attach until this is rewired.

- **The substrate for the rewire now exists**: `PicSharp.relPresheaf` / `relFunctorial` / `toRelPresheaf` are real and axiom-clean in `Picard/RelPicFunctor.lean` (see `I-0060`). The missing layer is `relEtSheaf` (does not exist yet — the étale-sheaf layer is still built on the *absolute* `presheaf`).

- **Decide the étale-topology route first, it is the one real blocker.** Mathlib v4.31 has no étale Grothendieck topology on schemes. Two options: (a) parametrize the sheafification topology `J`; (b) **Kleiman §2 Thm 2.5** — under a `k`-rational-section hypothesis `Pic^♯(T) → Pic^♯_ét(T)` is already bijective, so state representability against `relPresheaf` directly under a section hypothesis. Route (b) looks the more pragmatic path to a sorry-free rewire (the curve `C/k` in this problem has a rational point).

- **TRAP (do not do the naive rewire):** wiring `picSharp := PicSharp.presheaf` (the *absolute* iso-class functor) makes `PicSharpRepresentable`'s sorry a mathematically FALSE statement — absolute `Pic(C×T)` differs from `Hom(T, Pic)` by `Pic(T)` and is not representable. Any rewire MUST target the relative (and in general sheafified) functor. See memory `I-0061`.

- **Blueprint follows the same gate — do NOT repin piecemeal.** `I-0062` documents that `def:rel_pic_sharp` / `lem:rel_pic_sharp_functorial` / `thm:rel_pic_sharp_presheaf` carry `\leanok` but pin the absolute-Pic decls. The honest relative counterparts already exist (`subsec:relpic_relative_functor`, `def:rel_pic_sharp_relative` → `relPresheaf`). Repin the headline family to the relative decls **only as one coordinated Lean+blueprint step together with the `relEtSheaf`/rewire** — repinning def→relative while functorial/presheaf stay absolute just trades one inconsistency for another.

- **Do NOT re-probe the 6 IdentityComponent sorries or duplicate `AJC.pic0av`.** Verified blocked repeatedly: 5 Pic⁰ leaves are FGA-tainted (unblocked only by the rewire above) and the `GeometricallyIrreducible` conjunct needs EGA IV₂ 4.6.1-type input. See memory `I-0036`, `I-0052`.

## Watch-outs

- `SubProjects/Picard-IdentityComponent` mirror is **stale/behind AJC** (needs `IdentityComponent.lean` + `GeometricallyConnectedSection.lean` + blueprint re-sync, or retirement). Out of this Ground's write scope; flag before relying on it.
- The `Pic(C_ε) ≅ H¹(C_ε, O^×)` cocycle classification + truncated-exponential split sequence (Kleiman Thm 5.11) is the *largest* remaining block after the rewire — the `tangentSpaceIso` numerator. Not this session's target, but it is what the rewire unblocks.
- Concurrent-build hazard is real (`I-0054`, `I-0063`): the RelPicFunctor/FGA cone is FBC-free, so it does not touch the `Cech*` chain — but still check `pgrep -f bin/lean` before any `lake build`.
