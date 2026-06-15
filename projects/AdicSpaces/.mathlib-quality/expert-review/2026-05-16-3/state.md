# Expert-review session state — round 22

- Generated: 2026-05-16
- Audience: ChatGPT Pro (continuing series; round 22, follow-up to rounds 17–21)
- Goal of brief: Specific blocker. Round 21 prescribed proving no-hArch compactness for rational opens via the Boolean-cube argument. We attempted this and found that the natural Boolean-product encoding cannot directly handle continuity for non-mul-archimedean valuations (the natural cofinality encoding is Fσ, not closed, in the product topology). Wedhorn's actual proof of Theorem 7.35 uses a different spectral space Spv(A, I) with refined topology via the characteristic-subgroup retraction c_Γ_v(I). The project doesn't have this infrastructure. This round asks for specific Lean-level guidance: build the spectral infrastructure (~hundreds of lines), use a private-local engineering compromise (round-21 permits), or find an alternative criterion.
- Scope: Implementation strategy for the no-hArch compactness lemma, given the project state and the gap with Wedhorn's framework.
- Reply received: true (2026-05-16)
- Reply integrated: true (2026-05-16)

## Questions in the brief

| # | Question (verbatim from §6 of the brief) |
|---|------------------------------------------|
| Q1 | Next step: (a) build Spv(A, I) spectral infrastructure (~hundreds of lines, faithful to Wedhorn §7.1–§7.4); (b) use round-21 "private TODO" compromise to unblock P3 now and build infrastructure later; (c) find a Lean-friendly direct criterion that doesn't go through cofinality? |
| Q2 | Wedhorn 7.10 case (c_Γ_v = Γ_v) — is the cofinality there essentially the existing project `exists_pow_lt_zero` route in disguise? |
| Q3 | Can the project's `Valuation.isContinuous_of_ideal_pow_lt` (a different continuity criterion, phrased on I^n) be discharged for v ∈ Spv(A, I·A) without hArch, using algebraic boundedness in A rather than value-group statements? |
| Q4 | Should we upstream QuasiSober + PrespectralSpace + QuasiSeparatedSpace on Spv A to mathlib, then use mathlib's `compactSpace_withConstructibleTopology`? Or is the Spv-specific spectral structure too project-bound? |

## Ticket-board snapshot at brief time

- T-LAURENT-REFINEMENT-TREE-EXISTENCE (parent): in_progress.
- P1, P2: done.
- P3 (`relative_ratio_split_transports_to_RatioNodeData`): open. Round-20
  structurally complete; blocked on domination lemma.
- T-COMPACT-NO-HARCH (new this round, from round-21 reviewer prescription):
  open. Target: no-hArch compactness for rational opens. New file
  `SpaCompactNoHArch.lean` contains the lemma statement with sorry.
- P4–P8: open, substantive Wedhorn content (round-20 Q3–Q9 unanswered).
- T-MATHLIB-STACKS-00MA: open mathlib gap.

## Stuck points (from §5 of brief)

1. Building Spv(A, I) as a spectral space in the project: hundreds of
   lines of infrastructure, faithful to Wedhorn §7.1–§7.2 + §7.4.
2. Alternative: refactor the existing closed-image route to bypass
   `exists_pow_lt_zero`. Same need for Wedhorn 7.10 machinery.
3. Engineering compromise: private TODO sub-lemma with hArch for the
   domination lemma only, gated behind a comment marking the
   spectral-infrastructure TODO. Round-21 reviewer explicitly permits
   this kind of local compromise.

## Reference list (from §2 of brief)

- [Wedhorn 2019] §7.1 (Spv(A, I) definition, Lemma 7.4, Lemma 7.5,
  Remark 7.6), §7.2 (Theorem 7.10, Remark 7.11), §7.5 (Theorem 7.35
  Spa quasi-compactness). arXiv:1910.05934.
- Round-21 reviewer reply at `.mathlib-quality/expert-review/2026-05-16-2/reply.md`.

## Architectural changes this round

- Created `Adic spaces/SpaCompactNoHArch.lean` with the target lemma
  statement and documented proof plan (sorry body).
- Added to root import.
- Audited Wedhorn directly: confirmed his proof uses Spv(A, I)
  framework, not Boolean product; confirmed cofinality requirement.
- Confirmed project has none of Spv(A, I) infrastructure.
- Build: clean (3128 jobs, +1 sorry).
