# Blueprint-clean bc255 — Report

## Status: COMPLETE

---

## Chapter 1: `Picard_TensorObjSubstrate.tex`

### Target lemmas

**`lem:pullback_tensor_map_natural` (D1′) — proof block cleaned:**

| Location | Old (Lean-leakage) | New (mathematical) |
|----------|---------------------|---------------------|
| Square 2 paragraph | `"in a spelling that is \emph{defeq but not syntactically identical} to the canonical one, and on that spelling"` | `"in a form definitionally equal, but not explicitly identical, to the canonical one, and on that form"` |
| Square 2 paragraph | `"matches the goal up to reducible defeq (the residual gap being the zeta-reduction of the unfolded local definition). This is a purely proof-internal device"` | `"matches the goal definitionally. This is a structural device"` |
| Square 2 paragraph | `"spelling as the composite"` | `"form as the composite"` |

**`lem:sheafify_tensor_unit_iso_natural` — statement + proof block cleaned:**

| Location | Old | New |
|----------|-----|-----|
| Statement body | `"by \(\mathtt{TensorProduct}\) induction"` | `"at a time, using bilinearity"` |
| Proof Step 1 | `"the canonical \(\circ\,\mathtt{forget}_2\) presentation --- so that ... two monoidal structures that agree on the nose but are syntactically distinct"` | `"the canonical presentation as a composite with the forgetful functor \(\mathtt{forget}_2\) --- so that ... consistently within one monoidal structure"` |
| Proof Step 3 | `"applied as a term in the single chosen monoidal instance"` | `"applied within the single chosen monoidal structure"` |

### Broader chapter scan (pre-existing content)

Two additional pre-existing Lean-leakage terms were also cleaned from other lemma bodies:

- `lem:presheaf_pushforward_laxmonoidal` proof: `"modulo a defeq transport"` → `"modulo a definitional transport"`
- `lem:restrictscalars_bijectivecomparison` (two occurrences): `"is not syntactically a \((\,\cdot\,)\!.\mathtt{toRingHom}\))"` → `"is not presented as a \((\,\cdot\,)\!.\mathtt{toRingHom}\))"`

**Remaining occurrences not cleaned:** "project-side" (6 occurrences) — retained as a standing description of declarations defined in this project vs. Mathlib, not project-history language. "axiom-clean" (1 occurrence in an enumerated list) — retained as a brief formalization status note. Both are in pre-existing text not modified by bw255-d1. `% NOTE:` / `% iter-` / comment-only occurrences of `whnf` etc. — in comments, not prose.

---

## Chapter 2: `Picard_LineBundleCoherence.tex` (new chapter)

### Lean-leakage removals

| Location | Old | New |
|----------|-----|-----|
| §`sec:lbc_setup`, line 40 | `"This is the project-side substitute for Stacks Definition~17.25.1 (Tag~01CS, an invertible ...) restricted to rank one"` | `"This is the rank-one case of Stacks Definition~17.25.1 (Tag~01CS, invertible ...)"` |
| `lem:lbc_chart_presentation` body | `"In Mathlib terms, the unit sheaf-as-module \(\struct{U_i} = \mathtt{SheafOfModules.unit}\) carries the canonical free presentation built from \(\mathtt{SheafOfModules.free}\) on the one-element generating family, together with its canonical map out of the free module, and no relations;"` | `"The unit sheaf-as-module \(\struct{U_i}\) (Mathlib's \(\mathtt{SheafOfModules.unit}\)) carries a canonical free presentation on one generator with no relations;"` |
| `lem:lbc_rank_flat` proof | `"because, at the pinned Mathlib commit, there is no \(\mathtt{SheafOfModules}\)-level locally free or flat predicate to instantiate globally;"` | `"because there is no \(\mathtt{SheafOfModules}\)-level locally free or flat predicate globally;"` |

### Source-quote validation

All four `% SOURCE QUOTE:` blocks were validated byte-by-byte against `references/stacks-modules.tex`:

| Quote | Source location | Status |
|-------|----------------|--------|
| Tag 01CS (Definition 17.25.1, invertible module) | `stacks-modules.tex` L4046–L4059 | **VERIFIED** — exact match |
| Modules of finite presentation (Definition) | `stacks-modules.tex` L1377–L1392 | **VERIFIED** — exact match (including double space `and  $n, m$`) |
| Lemma 0B8M (Tag 0B8M, Lemma 17.25.4) | `stacks-modules.tex` L4159–L4165 | **VERIFIED** — exact match |
| Locally free sheaves (Definition) | `stacks-modules.tex` L2079–L2094 | **VERIFIED** — exact match |

No retriever spawn was needed.

### Macro audit

All custom macros used in the new chapter are defined in `blueprint/src/macros/common.tex`:
- `\struct{}` → `\mathcal{O}_{#1}` ✓
- `\Sheaf` → `\DeclareMathOperator` ✓
- `\forget` → `\DeclareMathOperator` ✓
- `\RingCat` → `\mathrm{RingCat}` ✓
- `\AddCommGrpCat` → `\mathrm{AddCommGrpCat}` ✓
- `\HasWeakSheafify` → `\mathtt{HasWeakSheafify}` ✓

---

## Invariants preserved

- No `\leanok` or `\mathlibok` markers were added or removed.
- No `\lean{}` or `\uses{}` pins were altered.
- Mathematical statements are unchanged; only expository prose and proof-block text were edited.
