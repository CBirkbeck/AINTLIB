# Reply integration — 2026-05-23 (round 2)

Reply received from senior algebraic geometer / Huber–Wedhorn expert on
2026-05-23.

- Brief: `../2026-05-23-2/brief.md`
- Reply: `../2026-05-23-2/reply.md`

## Interpretation summary

20 substantive reviewer points across the 6 brief questions + tactical
recommendations. **Zero unanswered Qs.**

Key strategic answers:
- Q1 — two-layer parametric propagation: core theorem layer (`[CompleteSpace A]`,
  `[CompatiblePlusSubring A]`) + propagation API layer (`presheafValue_*` instances).
- Q2 — prioritize Spa.comap framework IN FULL; reject Laurent-cover-only.
- Q3 — "fourth option": file-hierarchy split into 4 named files.
- Q4 — keep Lane C tree induction; reject direct Čech rewrite.
- Q5 — push through full Path α; split Spa.comap + propagation as named subprojects.
- Q6 — audit is healthy cleanup; keep `RationalCovering A`; mental `AffinoidTateContext` abstraction.

Tactical:
- Delete `restrictionMapHom_surj` and `restrictionMapHom_injective`.
- Don't make `cor_8_32_clean_via_laurent` the general API.
- `[IsDomain A]` is temporary Path α restriction.
- `CompatiblePlusSubring` belongs in context.
- Prove C3 (Spa.comap) BEFORE W3/L11.

## Changes applied

### 5 NEW parent tickets

- **#121 NEW-A1** Signature hygiene pass — add `[CompleteSpace A]`,
  `[CompatiblePlusSubring A]`; closes B2 #24, #25, #16, #17 cascade.
- **#122 NEW-A2** Spa.comap framework full build (~500 LOC, 5 subtickets
  #126-#130).
- **#123 NEW-A3** presheafValue propagation API batch (~210 LOC, 5 subtickets
  #131-#135). Supersedes #120.
- **#124 NEW-A4** F12 file-hierarchy split (4 files). Supersedes #85.
- **#125 NEW-A5** Delete dead restriction-map lemmas (`restrictionMapHom_surj`,
  `restrictionMapHom_injective`).

### 10 NEW subtickets

A2 chain (Spa.comap framework):
- **#126 NEW-A2.1** `valuation_extends_to_localization_of_rationalOpen` (~80 LOC)
- **#127 NEW-A2.2** `valuation_extends_to_completion_of_continuous` (~120 LOC)
- **#128 NEW-A2.3** Spa.comap image identification (~150 LOC)
- **#129 NEW-A2.4** `IsHuberRing (presheafValue D)` instance (~50 LOC)
- **#130 NEW-A2.5** Headline signature reconciliation + assembly (~100 LOC)

A3 chain (propagation API):
- **#131 NEW-A3.1** `presheafValue_isHuberRing` (~30 LOC)
- **#132 NEW-A3.2** `presheafValue_completeSpace` (~40 LOC)
- **#133 NEW-A3.3** `presheafValue_isStronglyNoetherian` (~50 LOC)
- **#134 NEW-A3.4** `presheafValue_hasLocLiftPowerBounded` (~60 LOC). **Closes old task #38.**
- **#135 NEW-A3.5** `presheafValue_compatiblePlusSubring` (~30 LOC)

### 6 MODIFIED tickets

- **#67 (P7 / W1 / L1)** — restored pending; noted L1 proof runs AFTER #121 (NEW-A1).
- **#114 (L4 replacement)** — noted ordering: after #67 Step B.
- **#38 (T-LOCLIFT-PRESERVATION)** — marked COMPLETED (superseded by #134).
- **#87 (C3 Spa.comap framework skeleton)** — noted full build is now #122; skeleton role only.
- **#85 (F12 move execution)** — marked COMPLETED (superseded by #124).
- **#120 (presheafValue propagation API batch)** — marked COMPLETED (superseded by #123 + subtickets).

### Documentation decisions applied to `.mathlib-quality/decomposition.md`

- DOC-D1, DOC-D2, DOC-D3 + 5-step execution plan added to the top of
  decomposition.md as the "ROUND-2 REVIEWER VERDICT" section.
- The prior post-audit-rewrite content is preserved below the verdict
  section for the per-leaf audits; the verdict takes precedence on conflicts.

### B2 cascade

Once #121 (signature hygiene) + #124 (F12 split) + #122/#123 (Spa.comap +
propagation) + #125 (dead-lemma deletion) land, the following B2s close:
- **#14, #15** (L2/L3 mirrors and L14/L15 — completeness + plus-subring alignment)
- **#16, #17** (dead restriction-map lemmas — removed entirely)
- **#21, #26** (L4, L5 — strengthened L1 + C2 cascade)
- **#22, #27** (L7, L6 — leaf-witness fix; reviewer guidance for upstream
  consumer refactor still applies)
- **#23** (L16 — deletion + Path α typeclass propagation)
- **#24, #25** (L14/L2, L15/L3 — closed by #121)

Net: 9 of the 9 logged critical-path B2s close cleanly.

## Changes rejected by user

(none — full approval)

## Open questions remaining

None from the reviewer. Future round may want to revisit:
- Whether to literally create the `AffinoidTateContext` structure (currently
  treated as mental abstraction per DOC-D2).
- The final removal of `[IsDomain A]` (currently retained as Path α
  restriction per DOC-D1).
- Off-critical-path obligations: structurePresheaf_isSheaf (categorical),
  Stacks 0316 chain, no-hArch Spv(A,I)-spectrality (SCNH:312), Artin-Rees
  no-Noeth (PTS:1783) — left as separable sub-projects.

## Decisions recorded but not actioned

- The "we may assume A is complete" Wedhorn-style reduction is NOT being
  followed; instead `[CompleteSpace A]` is a standing assumption per Q1.
- `RationalCovering A` is kept as primary covering object per Q6.
- Lane C tree induction is kept per Q4; tree-existence atoms (W1, W2, W3,
  I.1) are the open math content.
