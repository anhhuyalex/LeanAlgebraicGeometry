# Analogy: keystone span-cover descent — non-circularity of the Route B glue

## Mode
api-alignment

## Slug
keystone-descent

## Iteration
041

## Question
Can `qcoh_section_isLocalizedModule (F) [IsQuasicoherent F] (f) : IsLocalizedModule (powers f) ρ_f`
be assembled *non-circularly* from the 5 DONE pieces (`isLocalizedModule_of_span_cover`,
`section_isLocalizedModule_of_presentation`, `qcoh_finite_presentation_cover` (B1),
`presentationModulesRestrictBasicOpen` (B4), `restrict_obj`-rfl), or is a sheaf-gluing / Čech-H⁰
ingredient genuinely missing?

## Project artifact(s)
- `QcohTildeSections.lean:330-378` — `isLocalizedModule_of_span_cover` (algebraic local-global, per-`j`
  hypothesis is about the **abstract** `LocalizedModule (powers (s j)) M`).
- `QcohTildeSections.lean:498-504` — `section_isLocalizedModule_of_presentation` (tile lemma; output is
  about the **sheaf-section** restriction `Γ(⊤,F)→Γ(D(f),F)`).
- `QcohTildeSections.lean:547-604` — B1 + the Handoff comment (already names "sections of qcoh `F` over
  `D(f)` localise — Γ(D(f),F)=Γ(X,F)_f, Stacks 01HV(4)" as "the single genuine remaining blocker … absent
  from Mathlib").
- `QcohRestrictBasicOpen.lean:101-114` — `modulesRestrictBasicOpen`/`Iso` (geometric tile transport
  `F|_{D(f)} ≅ F_{(f)}`; does NOT identify `tilde(ΓF)|_{D(f)}`).
- `CechAcyclic.lean:1165-1605` — the P3 section-Čech bridge (`qcohSectionsAwayLocalized`,
  `qcohRestriction_eq_comparison`, `sectionCech_objD_apply`, the `phi`/`phiL` ladder,
  `sectionCech_homology_exact`) — built **for the tilde sheaf `~M`**, positive degrees.
- `analogies/bridge.md` (iter-037) — B6 claim "section comparison is `restrict_obj`-rfl".

## Decisions identified

### Decision: D1 — the GLUE step (algebraic span-cover descent vs sheaf-axiom equalizer)
- **The circularity is REAL.** Instantiate `isLocalizedModule_of_span_cover` with
  `M = Γ(X,F)`, `N = Γ(D(f),F)`, `g = ρ_f`, `s = {gⱼ}`. The per-`j` hypothesis is
  `h j : IsLocalizedModule (powers f) (IsLocalizedModule.map (powers gⱼ) (mkLinearMap … M) (mkLinearMap … N) ρ_f)`,
  i.e. a statement about the **abstract Mathlib localized module**
  `LocalizedModule (powers gⱼ) Γ(X,F) → LocalizedModule (powers gⱼ) Γ(D(f),F)`.
  The tile lemma `section_isLocalizedModule_of_presentation` (on the B4-presented tile `F_{(gⱼ)}`,
  read through `restrict_obj`) only delivers `IsLocalizedModule (powers f)` of the **sheaf-section**
  restriction `Γ(D(gⱼ),F) → Γ(D(gⱼf),F)`. To transport the latter to `h j` you need two **commuting
  R-linear equivalences**
    α : `LocalizedModule (powers gⱼ) Γ(X,F)  ≅ Γ(D(gⱼ),F)`,
    β : `LocalizedModule (powers gⱼ) Γ(D(f),F) ≅ Γ(D(gⱼf),F)`.
  α is, *definitionally via* `IsLocalizedModule.iso`, the statement
  "`ρ_{gⱼ} : Γ(X,F)→Γ(D(gⱼ),F)` is `IsLocalizedModule (powers gⱼ)`" = **the keystone at `gⱼ`**.
  β is the keystone for the open `D(f)` at `gⱼ` (`Γ(D(f),F)_{gⱼ} ≅ Γ(D(f)∩D(gⱼ),F)`). Neither is a DONE
  piece. So the descent reduces "keystone at `f`" to "keystone at every `gⱼ`" — the *same* statement, no
  progress. `h j` is **un-dischargeable** from the 5 DONE pieces alone.
- **Mathlib idiom (the non-circular glue)**: the equalizer / sheaf axiom, NOT the algebraic local-global
  principle. Stacks 01HV(4)/01I8 derive the keystone by localising the gluing exact sequence
  `0 → Γ(X,F) → ∏ᵢ Γ(D(gᵢ),F) → ∏ᵢⱼ Γ(D(gᵢgⱼ),F)` at `f` (localisation is exact:
  `IsLocalizedModule.map_exact`, `Mathlib.Algebra.Module.LocalizedModule.Exact`) and comparing it with
  the `D(f)`-cover equalizer `0 → Γ(D(f),F) → ∏ᵢ Γ(D(gᵢf),F) → ∏ᵢⱼ Γ(D(gᵢgⱼf),F)`. The two are
  intertwined by the **per-tile** localisations `Γ(D(gᵢ),F)_f ≅ Γ(D(gᵢf),F)` and
  `Γ(D(gᵢgⱼ),F)_f ≅ Γ(D(gᵢgⱼf),F)` — which ARE the DONE tile lemma (the tiles are tilde via B4),
  applied on the cover and overlap elements, **not** on the global object. The kernel comparison then
  gives `Γ(X,F)_f ≅ Γ(D(f),F)`. This glue is non-circular precisely because the only
  "sections-localise" inputs sit on the tiles (where `F` is tilde), and the global statement is recovered
  by the sheaf axiom, never by an abstract-localized-module identification.
- **Gap**: divergent-and-wrong. `isLocalizedModule_of_span_cover` is the wrong glue for this goal.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — supply the sheaf-axiom equalizer gluing (the keystone itself
  is the gap-fill; Mathlib has every primitive except the assembled statement).

### Decision: D2 — is there a Mathlib shortcut that supplies α (or closes 01I8) without the keystone?
- **"Sections of a sheaf-of-modules over a basic open localise"**: does NOT exist in Mathlib. The only
  `IsQuasicoherent`/section-localisation content in `Mathlib/AlgebraicGeometry/` is `Modules/Tilde.lean`
  (`toOpen` for `~M` only); the project grep + the Handoff comment both confirm the absence. For `~M`
  the fact is Mathlib's `tilde.toOpen` instance — but `F = ~(ΓF)` for a general qcoh `F` is *exactly*
  01I8, the goal, so this is not available a priori.
- **"Iso checked on a cover ⟹ iso" on `fromTildeΓ`**: this route checks `IsIso F.fromTildeΓ` tile-by-tile.
  On `D(gⱼ)` it reduces to `tilde(Γ(X,F))|_{D(gⱼ)} ≅ F|_{D(gⱼ)} = tilde(Γ(D(gⱼ),F))`, i.e. again
  `Γ(X,F)_{gⱼ} ≅ Γ(D(gⱼ),F)` (**the same keystone-at-`gⱼ`**) AND it additionally requires
  `tilde(Γ(X,F))|_{D(gⱼ)} ≅ tilde(Γ(X,F)_{gⱼ})` — the **tilde base-change wall** (`tilde_restrict_basicOpen`,
  Route P, deliberately avoided; absent from Mathlib per `analogies/o1i8-route.md:80`). So this route is
  **strictly worse**: it bottoms out on the same keystone and resurrects a second wall.
- **Gap**: divergent — the hoped-for shortcut does not exist and the nearest alternative is worse.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (no shortcut; the keystone is genuinely the missing input).

### Decision: D3 — are the other 4 DONE pieces wasted, or do they feed the correct route?
- **They feed it exactly.** `section_isLocalizedModule_of_presentation` (tile lemma) + B1 (finite cover) +
  B4 (tile is presented ⟹ tilde) + `restrict_obj`-rfl produce precisely the **per-tile localisation
  isos** the sheaf-axiom route consumes: for each cover element `gᵢ` and overlap `gᵢgⱼ`, the tile lemma
  gives `IsLocalizedModule (powers f)` of `Γ(D(gᵢ),F)→Γ(D(gᵢf),F)` resp. `Γ(D(gᵢgⱼ),F)→Γ(D(gᵢgⱼf),F)`.
  Only `isLocalizedModule_of_span_cover` is the wrong tool *for this assembly* (it remains correct algebra,
  just not the glue the keystone needs).
- **Gap**: identical — these four are the right primitives.
- **Verdict**: **PROCEED** (reuse them verbatim; do not rebuild).

## On bridge.md's B6 over-claim
B6 ("section comparison is `restrict_obj`-rfl", Sheaf.lean:328) **conflated two different comparisons**.
`restrict_obj : Γ(M.restrict ι, U) = Γ(M, ι ''ᵁ U)` is rfl and identifies the *tile sheaf's* sections
with `F`'s sections over the image open — a **geometric=geometric** identity. But the span-cover descent's
actual per-`j` obligation is the **abstract↔geometric** identity
`LocalizedModule (powers gⱼ) Γ(X,F) ≅ Γ(D(gⱼ),F)`, which is the keystone, NOT rfl. B6 used the (true) rfl
of the first to claim the descent's section comparison is free; the descent in fact needs the second.
The planner's suspicion is correct — B6 over-claimed.

## Recommendation
**Do NOT close the keystone via `isLocalizedModule_of_span_cover` on global sections — that route is
circular.** Re-shape the glue to the sheaf-axiom equalizer (Stacks 01HV(4)):

1. **[reuse, DONE]** B1 → finite cover `{gⱼ}`, `span = ⊤`; B4 → each tile `F_{(gⱼ)}` is presented;
   tile lemma → per cover/overlap element, `Γ(D(gᵢ…),F)_f ≅ Γ(D(gᵢ…·f),F)` (`section_isLocalizedModule_of_presentation`,
   read via `restrict_obj`).
2. **[new, small]** the 2-term sheaf-axiom equalizer `0→Γ(X,F)→∏Γ(D(gᵢ),F)→∏Γ(D(gᵢgⱼ),F)` as a
   `Function.Exact` (the sheaf condition of `(Spec R).Modules`; degree-0/1 of the project's own
   `sectionCechComplex`, or Mathlib's sheaf equalizer). Same for the cover of `D(f)`.
3. **[new, Mathlib]** localise the X-cover equalizer at `f` with **`IsLocalizedModule.map_exact`**
   (`Mathlib.Algebra.Module.LocalizedModule.Exact`).
4. **[new, bookkeeping]** intertwine the localised equalizer with the `D(f)`-cover equalizer via the
   per-tile isos of step 1 (commutativity = naturality, the analogue of `qcohRestriction_eq_comparison`);
   the kernel comparison yields `Γ(X,F)_f ≅ Γ(D(f),F)` = the keystone.

The project's P3 section-Čech bridge (`sectionCech_objD_apply`, `qcohRestriction_eq_comparison`, the
`phi`/`phiL` ladder, `sectionToModuleAddEquiv`) is the **template** for step 4, but it is currently wired
for the *global* tilde sheaf `~M` and the full positive-degree complex; the keystone needs only **degree
0/1** of a **general qcoh `F` whose tiles are tilde**. Build a degree-0/1 specialisation, not a full reuse.
Estimate: ~150–300 LOC, fiddly equalizer/naturality plumbing, **no** mathematical wall (contrast the two
walls of Route P). The keystone is the load-bearing gap-fill; everything downstream of it (the Handoff
chain in `QcohTildeSections.lean:559-604`) then closes.
