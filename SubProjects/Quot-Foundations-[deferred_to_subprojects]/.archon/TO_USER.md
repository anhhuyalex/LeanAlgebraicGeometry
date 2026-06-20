<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **FBC route — decided: FBC-B DIRECT (H⁰-equalizer), mate keystone abandoned** (iter-079, holds). The
  dead `base_change_mate_*` apparatus (FlatBaseChange.lean, off-path) is no longer pursued. Next step is
  mechanical: MOVE the two named legs into FlatBaseChangeGlobal.lean (they currently sit in a file imported
  BY Global, so they can't consume the direct equiv without an import cycle), then fill. The loop proceeds on
  this route; steer via `USER_HINTS.md` if you'd prefer otherwise.
- **Hilbert-poly `Φ_s` (deferred caveat).** Canonical encoding likely needs a Serre `m≫0` agreement; the
  "Hartshorne II.5.17" attribution is unverified — a pointer to the right reference would help when convenient.
