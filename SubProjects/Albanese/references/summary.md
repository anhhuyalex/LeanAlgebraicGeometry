# References

<!-- archon:references-summary -->

Sources backing the **Albanese subproject** (extracted from
Algebraic-Jacobian-Challenge). References that backed only carved-out chapters
(the cohomology / Čech engine, Picard tensor substrate, flat-base-change) were
dropped in the extract; what remains backs the Albanese universal property and
its rational-map-extension / commutative-algebra / rigidity substrate.

| File | Description |
| ---- | ----------- |
| `challenge.lean.ref` | Original AI challenge file by Christian Merten — the formal statement of the missing definitions and theorems for the Jacobian of an algebraic curve. Authoritative signatures. |
| [`abelian-varieties.md`](./abelian-varieties.md) → `abelian-varieties.pdf` | Milne, "Abelian Varieties" (course notes, 2008). **Primary source.** **Rigidity Theorem 1.1** (§I.1, p.8); **Thm 3.2** + **Prop 3.10** "rational/unirational → AV is constant" via bare rigidity, NO Serre duality (§I.3, pp.15–20); **Albanese universal property** of `Pic⁰`/Jacobian **Prop 6.1/6.4** (§III.6, p.104) — the seed of this subproject. |
| [`mumford-abelian-varieties.md`](./mumford-abelian-varieties.md) → `mumford-abelian-varieties.pdf` | Mumford, "Abelian Varieties" (TIFR, 1970). Canonical rigidity source. **Rigidity Lemma (Form I)** + Cor.1 (§4, book p.43 / PDF p.54); abelian-variety definition + conventions (§4, p.39). Scanned image PDF — quote from rendered page; body offset +11. |
| [`hartshorne-algebraic-geometry.md`](./hartshorne-algebraic-geometry.md) → `hartshorne-algebraic-geometry.pdf` | Hartshorne, "Algebraic Geometry" (GTM 52, 1977). **Genus-0 curve ≅ ℙ¹**: Example IV.1.3.5 (doc p.297) + Exercise IV.1.3; genus def `g=dim H¹(O_X)` Prop IV.1.1 (doc p.294); Weil-divisor / codimension-one background (Ch. II §6). Scanned image PDF; body offset +17. |
| [`matsumura-commutative-ring-theory.md`](./matsumura-commutative-ring-theory.md) → `matsumura-commutative-ring-theory.pdf` | Matsumura, "Commutative Ring Theory" (CUP CSAM 8, 1987). **Ch. 16–17** depth / regular sequences / Cohen–Macaulay; **Ch. 19** Auslander–Buchsbaum formula / regular local rings. Direct dependency of `AuslanderBuchsbaum.lean` and `CodimOneExtension.lean`. |
| [`atiyah-macdonald-commutative-algebra.md`](./atiyah-macdonald-commutative-algebra.md) → `atiyah-macdonald-commutative-algebra.pdf` | Atiyah–Macdonald, "Introduction to Commutative Algebra" (1969). **Ch. 8** primary decomposition; **Ch. 11** Krull dimension. Lightweight companion to Matsumura for the codimension-one reasoning in `CodimOneExtension.lean` / `CoheightBridge.lean`. |
| [`stacks-algebra.md`](./stacks-algebra.md) → `stacks-algebra.tex` | Stacks ch.10 "Commutative Algebra" — tag **00T7** (standard smooth ⇒ `Ω_{S/R}` free on `dx_{c+1},…,dx_n`). Backs the Kähler-differential / standard-smooth steps feeding Thm 3.2. Large file: jump to line. |
| [`stacks-varieties.md`](./stacks-varieties.md) → `stacks-varieties.tex` | Stacks ch.33 "Varieties" — tags **035U**, **04QM**/**056T** (smooth over fields ⇒ geom regular/normal/reduced), **0BUG**. Backs the reducedness / smoothness inputs (`isReduced_of_smooth_over_field`, geom-irreducibility) in `Thm32RationalMapExtension.lean`. |
| [`stacks-fields.md`](./stacks-fields.md) → `stacks-fields.tex` | Stacks ch.9 "Fields" — tags **09HD**, **030K** (separable/inseparable factorisation). Field-theory background for the codimension-one extension. |
| [`stacks-divisors.md`](./stacks-divisors.md) → `stacks-divisors.tex` | Stacks ch.31 "Divisors" — Cartier/Weil divisors, `c₁ : Pic(X) → Cl(X)`. Backs the kept `RiemannRoch/WeilDivisor.lean` slice (§31.28 Weil-divisor-class-vs-Pic). |
| [`stacks-constructions.md`](./stacks-constructions.md) → `stacks-constructions.tex` | Stacks ch.27 "Constructions of Schemes" — relative Proj / relative spectrum. Backs the `ProjectiveLineBar` Proj substrate kept as compile-time riders in `Genus0BaseObjects/BareScheme.lean`. |
| [`stacks-coherent.md`](./stacks-coherent.md) → `stacks-coherent.tex` | Stacks ch.30 "Cohomology of Schemes" — tag **02KH** (flat base change of `Rⁱf_*`, `H⁰`-with-base-change part). Background for the smooth-curve cohomological inputs referenced by the kept slices. |
| [`kleiman-picard.md`](./kleiman-picard.md) → `kleiman-picard.pdf` / `-src/*.tex` | Kleiman, "The Picard scheme" (FGA Explained / arXiv:math/0504020). Source for the kept `Picard/FGAPicRepresentability.lean` slice: §4 existence, §5 `Pic⁰` (Jacobian, pp.36–51). |
| [`nitsure-hilbert-quot.md`](./nitsure-hilbert-quot.md) → `nitsure-hilbert-quot.pdf` / `-src/*.tex` | Nitsure, "Construction of Hilbert and Quot Schemes" (FGA Explained / arXiv:math/0504590). Quot/Hilbert background behind the Picard representability slice. |
| [`fga-explained.md`](./fga-explained.md) → `fga-explained.pdf` | Fantechi–Göttsche–Illusie–Kleiman–Nitsure–Vistoli, "FGA Explained" (AMS MSM 123, 2005). Collected-volume source for the Picard slice; **Kleiman Picard** = Ch.9 (book p.237), **Nitsure Hilbert/Quot** = Ch.5 (p.107). Body offset +10; has text layer. |
