- **Grassmannian properties in progress** (iter-011): separatedness' algebraic core + properness'
  finiteness instances are proven axiom-clean. Two cores remain hard — the separated diagonal step is
  walled by a Mathlib `⊗[ℤ]` instance diamond + the absence of `GlueData → IsSeparated`, and properness
  needs the deep Nitsure DVR valuative criterion. `grassmannian_very_ample` / `grassmannianUniversalQuotient`
  stay stubbed on the locally-free-of-rank / exterior-power-determinant gaps. A hint on a preferred
  diamond-safe product-cover route (`USER_HINTS.md`) would unblock separated; the loop otherwise proceeds.
- **Sole absent-Mathlib piece for relative-`Proj`** (not blocking — worked around): turning an abstract
  `V : S.Modules` into an explicit trivialising affine cover + frame matrices (local triviality of a
  locally-free sheaf / sheaf-`Sym`). Decision of record: assemble `relativeProj` from an EXPLICIT cover +
  `GLₙ₊₁` frame 1-cocycle, mirroring the now-proven Grassmannian GlueData. Point at a preferred Mathlib
  route via `USER_HINTS.md` if you have one; the loop proceeds with the explicit form.
- **Decision made** (iter-002, still live): absent EGA III §7 foundations (coherent cohomology, Serre
  vanishing, cohomology-and-base-change, relative Proj of a graded sheaf) are faithful sorry-stubbed
  `theorem`s — **never `axiom`** — built incrementally; the main theorem stays conditional until they
  discharge.
