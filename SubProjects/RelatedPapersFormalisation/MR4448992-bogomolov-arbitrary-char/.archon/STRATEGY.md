# Strategy

## Goal

Formalize the full proof of the **Geometric Bogomolov Conjecture in Arbitrary Characteristics**
(Xie–Yuan, arXiv:2108.09722, MR4448992).

**End-state theorem** (`thm:main`):
Let $k$ be an algebraically closed field, $K/k$ a finitely generated field extension of
transcendence degree $\geq 1$, $A$ an abelian variety over $K$, and $X$ a closed
subvariety of $A_{\overline{K}}$.  If $X$ contains a dense set of small points of
$A/K/k$, then $X$ is special.

The project is **sorry-free modulo three admitted external axioms**:
- `thm:maninMumford` — Manin–Mumford conjecture (Raynaud 1983 / Hrushovski 2001); not in Mathlib.
- `lem:fundamentalInequality` — Zhang–Gubler fundamental inequality; not in Mathlib.
- `thm:yamakiReduction` — Yamaki's reduction theorem (Yamaki 2016a, Thm 1.5); not in Mathlib.

These are declared as `sorry`-marked external anchors and their admission is explicit.
All other sorries are eliminated.

---

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| 1 — Definitions | NOT STARTED | 12 | ~2500 | None available; abelian-scheme API, height, trace must be built from scratch | Large scope; no Mathlib foundation for heights |
| 2a — Algebraic cycles | NOT STARTED | 6 | ~1200 | None | Core infrastructure for Chow groups |
| 2b — Rational equivalence | NOT STARTED | 4 | ~800 | None | Depends on 2a |
| 2c — Intersection product | NOT STARTED | 5 | ~1000 | None | Requires Serre tor-formula |
| 2d — Serre tor formula | NOT STARTED | 4 | ~700 | `CommutativeAlgebra.Tor` partial | Homological algebra depth |
| 2e — Comparison inequality (Prop 2.1) | NOT STARTED | 3 | ~400 | Phase 2a-d | Core §2 result |
| 3 — Transcendence degree reduction | NOT STARTED | 8 | ~1000 | Descent theory partial | Blow-up API absent; must build pencil construction |
| 4 — Line bundles over abelian schemes | NOT STARTED | 5 | ~600 | None confirmed | Depends on Phase 1 + 2a-b |
| 5 — Final proof | NOT STARTED | 8 | ~900 | Northcott partial | Depends on all prior phases + 3 external axioms |

---

## Routes

### Single route — paper's five-section structure (§1–§5)

The proof follows the paper (arXiv:2108.09722) in five sections.  There is no alternative
route: the paper's structure is the formalization structure.

**Phase 1 — Definitions and setup**

Build the infrastructure absent from Mathlib:

- **Abelian schemes**: basic API over a base curve $S$ — multi-sections, torsion
  multi-sections, rigidified line bundles.  *Note*: Mathlib has only
  `AlgebraicGeometry/Group/Abelian.lean` (2 commutativity theorems); no abelian-scheme
  module exists.  The full abelian-scheme API must be constructed from scratch.
- **Canonical heights**: integral models (projective model / polarization / integral
  model of $(A,L)$ over $S$), naive height via intersection numbers, Tate limit for
  canonical height $\hat h$.  *Mathlib gap*: no intersection-number API exists; this
  is entirely new material.
- **$\overline{K}/k$-trace**: definition and basic properties of the trace functor.
  *Mathlib gap*: no `AbelianVariety` namespace exists in the installed Mathlib.
- **Special subvarieties**: torsion subvariety, definition of special.
- **Dense small points**: $X(\epsilon)$ and Zariski-density condition.

**Phase 2 — Non-proper intersections (§2)** — five sub-phases

§2 of the paper proves a key comparison inequality for non-proper intersections in the
Chow group.  Building this requires constructing Chow-group infrastructure from scratch.

- *Phase 2a* — Algebraic cycles: $i$-cycles with $\mathbb{Q}$-coefficients, push-forward,
  pull-back, effective cycles, ordering ($\alpha \geq 0$).
- *Phase 2b* — Rational equivalence: the Chow group $\mathrm{CH}_i(B)_{\mathbb{Q}}$
  as the group of $i$-cycles modulo rational equivalence; functoriality.
- *Phase 2c* — Intersection product: intersection of cycles on smooth projective varieties;
  proper and non-proper intersection; multiplicity via the Serre tor-formula.
- *Phase 2d* — Serre intersection formula: $\mathrm{Tor}$-vanishing over smooth local
  rings; this gives the multiplicity formula and cycle-class bounds used in Prop 2.7.
- *Phase 2e* — Results of §2: Bertini-type result (Prop 2.2), proper-part bound
  (Prop 2.7), strict-transform dimension (Lem 2.8), and the main comparison inequality
  (Prop 2.1 / `pro:strLeqTot`).

**Phase 3 — Lowering the transcendence degree (§3)** — after Phase 1

Prove Prop 3.1 (`pro:changeField`): reduce the conjecture from $\operatorname{trdeg}(K/k) \geq 2$
to $\operatorname{trdeg}(K/k) = 1$.

- Descent results for abelian varieties over composite extensions (Prop 3.2, Lem 3.3,
  Lem 3.6, Cor 3.7).  Basic field theory is in Mathlib; abelian-variety descent may
  require new material.
- Characterization of special subvarieties via $k_{A,X}$ (Prop 3.8).
- Generic hyperplane with height inequality (Lem 3.9): pencil construction via
  Jouanolou's Bertini theorem + blow-up.  *Mathlib gap*: no blow-up API under the
  previously cited name; the standard Mathlib blow-up lives under
  `AlgebraicGeometry.BlowupAlgebra`; existence and properties must be verified and
  the height inequality derived from Phase 1.

**Phase 4 — Line bundles over abelian schemes (§4)** — after Phase 1 AND Phase 2a-b

- Rigidified line bundles: $[m]^*\mathcal{L} \cong m^2 \mathcal{L}$, torsion restriction,
  nefness (Lem 4.1 / `lem:lineBundleProps`).
- Numerical equivalence of torsion multi-sections (Prop 4.2 / `pro:numericalEquivalent`):
  requires Chow groups (Phase 2a-b) and intersection product (Phase 2c).
- Canonical height = naive height for good-reduction abelian schemes.

**Phase 5 — Final proof (§5)** — after all of Phases 1–4

Prove `thm:main` under the three admitted external axioms.

- `thm:maninMumford`, `lem:fundamentalInequality`, `thm:yamakiReduction`: declared
  as explicit `sorry`-marked external anchors; not formalised within this project.
- Northcott property for function fields: `lem:northcott` — likely available in Mathlib
  in restricted form; must be verified.
- Subvarieties generated by addition (Lem 5.3 / `lem:addition`): unique $r$ stabilizing
  the sequence, $X_r$ is torsion.  Requires height quadraticity (Phase 1 + 4).
- Fibers of addition map (Prop 5.4 / `pro:torsionFiber`): combines §2 (comparison
  inequality) with §4 (numerical equivalence).  Core new contribution.
- Dimensional induction: $X$ is torsion by induction on $\dim X$ via Manin–Mumford.

**Parallelism**:
- Phase 2 (sub-phases 2a–2d) and Phase 1 are mutually independent; run in parallel.
- Phase 3 starts after Phase 1 completes (needs heights + abelian-scheme API).
- Phase 4 starts after Phase 1 AND Phase 2a-b complete.
- Phase 5 starts after all of Phases 1–4 complete.

---

## Mathlib gaps & new material

| Item | Phase | Action |
|------|-------|--------|
| Abelian-scheme API (multi-sections, rigidification) | 1 | Build from scratch |
| Canonical heights (Tate limit for subvarieties) | 1 | Build from scratch |
| $\overline{K}/k$-trace of abelian variety | 1 | Build from scratch |
| Intersection numbers on projective varieties | 1 | Build from scratch |
| Algebraic cycles with $\mathbb{Q}$-coefficients | 2a | Build from scratch |
| Rational equivalence / Chow groups | 2b | Build from scratch |
| Intersection product on smooth varieties | 2c | Build from scratch |
| Serre tor-formula for multiplicity | 2d | Build from scratch |
| Blow-up API (pencil construction) | 3 | Locate/extend Mathlib `BlowupAlgebra` |
| Northcott property over function fields | 5 | Verify in Mathlib; extend if needed |
| Manin–Mumford conjecture | 5 | **External axiom** (admitted) |
| Zhang–Gubler fundamental inequality | 5 | **External axiom** (admitted) |
| Yamaki's reduction theorem | 5 | **External axiom** (admitted) |

---

## Open strategic questions

1. **Chow group definition**: use Milnor K-theory / cycles modulo rational equivalence,
   or a more abstract approach (correspondences)?  The paper uses classical algebraic
   cycles — the formalization should match.
2. **Serre formula approach**: the Serre tor-formula is the standard reference (SGA /
   EGA) but requires significant homological algebra.  Alternative: use the moving
   lemma and explicit cycle computations where possible.
3. **Blow-up verification**: confirm the exact Mathlib module for blow-ups
   (`AlgebraicGeometry.BlowupAlgebra` or another path) before Phase 3 starts.
4. **Northcott for function fields**: confirm whether Mathlib's Northcott property
   is strong enough over function fields (not just number fields) for Lem 5.3.
5. **External axioms scope**: should any of the three external axioms (Manin–Mumford,
   Zhang–Gubler, Yamaki) be formalized in a companion project?  Not planned here, but
   worth tracking.
