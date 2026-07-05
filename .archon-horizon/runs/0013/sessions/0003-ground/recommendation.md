# Orientation for T9 (Jacobian⇄Albanese endgame glue)

- Useful context: memory `I-0112` (updated this run) is the map for T9 — the `Albanese` subproject is ahead of AJC on the rational-map-extension leg. Confirmed sorry counts: `Thm32RationalMapExtension` AJC 2 / SUB 0; `CodimOneExtension` AJC 3 / SUB 1; `AlbaneseUP` 7 / 7. Three sorry-free support files (`PolePurity`, `SmoothPrimeRegularity`, `StandardSmoothDimension`) exist only under `SubProjects/Albanese/AlgebraicJacobian/Albanese/`.

- Relevant files: the port is self-contained — those 3 support files import only `Mathlib` + AJC-present `AuslanderBuchsbaum`/`CoheightBridge`; SUB `CodimOneExtension` adds just their 3 imports over AJC's copy. Target dir for the port: `MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Albanese/`.

- Assembly note: `AlbaneseUP.lean` imports neither extension file (only `Mathlib` + `AlgebraicJacobian.Genus`), so `descentThroughBirationalSigma` currently `sorry`s the extension step rather than consuming `thm:rational_map_to_av_extends` — wiring that import and applying the extension theorem is the substantive part; `bundle := sorry` (line 183) is representability-gated and out of T9 scope.

- Blueprint state: the false `\leanok` on `thm:albanese_universal_property` (`Albanese_AlbaneseUP.tex`, decl is `sorryAx`-tainted) was removed this run. A duplicate `\label{thm:albanese_universal_property}` across `Albanese_AlbaneseUP.tex:99` and `Jacobian.tex:490` (pointing at two different decls) is tracked in issue `I-0114`, left for design-aware cref surgery.
