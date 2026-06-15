# Expert-review session state (round 2)

- Generated: 2026-05-23T17:00:00Z
- Audience: Senior algebraic geometer / Huber–Wedhorn expert (same as round 1)
- Goal of brief: Strategic guidance after the full 35-sorry critical-path audit revealed 9 B2s, 3 SUSPECT, 6 BLOCKED, 2 STRUCTURAL, 4 OFF-PATH, 2 DEAD, and **0 clean leaves**. The user wants honest guidance on (a) whether a coordinated parametric-propagation refactor is the right move, (b) whether Spa.comap framework should be prioritized or deferred, (c) whether F12 is still the right structural call, (d) whether the Lane C approach is still sound, (e) whether the project is feasible at current scope or needs rescoping, (f) whether anything signals deeper wrongness.
- Scope: Full IsSheafy_ofStronglyNoetherianTate target. Round 1 was on a single B2 (L4); round 2 is the comprehensive picture.
- Reply received: true (2026-05-23T17:30:00Z)
- Reply integrated: true (2026-05-23T18:00:00Z)

## Questions in the brief

| # | Question (summary) |
|---|--------------------|
| Q1 | Should we extend the Session 27 "Path α" parametric pattern to a broader parametric propagation (`[CompleteSpace A]`, `[CompatiblePlusSubring A]`, the `presheafValue D` typeclass bundle)? Or use the "we may assume complete" reduction? |
| Q2 | Should `Spa_presheafValue_eq_rationalOpen` (~500 LOC) be prioritized in full now, or is there an alternative IsSheafy route (e.g., Laurent-cover-restricted via `_via_normalizedLaurent`) that defers Spa.comap? |
| Q3 | F12 reorganization: pick (a) refactor general `tateAcyclicity` to assume `[LaurentNormalized C.base]`, (b) close legacy faithful-flatness-kernel sorry in place upstream of Cor832, (c) add separate `LaurentNormalized`-specific wrapper and keep legacy `tateAcyclicity` with sorry, or (d) some 4th option (file hierarchy split)? |
| Q4 | Is the Lane C tree-induction approach the right route, or should we switch to a direct Wedhorn-faithful Čech argument using Lemma 8.33 + Prop A.3 explicitly to avoid the propagation API issues? |
| Q5 | Project feasibility: push through (~1500-2000 LOC) / scope down to Laurent-cover-only / hand off Spa.comap + propagation as separable sub-projects / other rescoping? |
| Q6 | Is the audit signaling deeper wrongness (abstraction layer, Lean-mathlib mismatch)? Or is the project substrate healthy and just needs cleanup? |

## Ticket-board snapshot at brief time

Open critical-path tickets:
- #23 T-EMBED-TOPO (split into 3 subtickets)
- #36 T-MATHLIB-STACKS-00MA (off-path)
- #38 T-LOCLIFT-PRESERVATION (BLOCKED on Task #87 + Task #120)
- #60 T-LAURENT-REFINEMENT-TREE-EXISTENCE (in_progress)
- #67 P7 W1 exists_standard_cover_refining (in_progress, Step A done, Step B = L1 proof pending)
- #85 Wave C: F12 move execution (DEFERRED pending decision on F12-a/b/c)
- #88 Wave F: Path α wiring (A3 body, A1 embedding)
- #114 L4 replacement: nonvanishing cover extraction (BLOCKED on L1)
- #120 NEW: presheafValue propagation API batch (~6-10 lemmas)

Recently completed (this session):
- #115 Foreground: L1 predicate update (DONE — added `R({f}/f)` clause to LocalBasisHyp; build clean)

Recently completed (background agents):
- #116 L16 agent: returned B2 #23 (statement false, supersedes via Path α)
- #117 L7 agent: returned B2 #22 (signature underspecified)
- #118 L8 agent: returned BLOCKED on propagation API
- #119 Spa_presheafValue agent: returned BLOCKED (~500 LOC sub-development; file is planning skeleton)

## Stuck points (from §7 of brief)

1. Typeclass-deficiency epidemic: 9 B2s + 3 SUSPECT, several with the same root cause (missing `[CompleteSpace A]`, missing PlusSubring alignment).
2. `presheafValue` propagation API gap: 6 obligations blocked on missing API.
3. Spa.comap framework: foundational ~500 LOC sub-development gating the W3 chain.
4. F12 reorganization is entangled with L-atoms, not standalone.
5. Several previously-named "leaves" do not exist as atomic units in the codebase.

## Reference list (from §3 of brief)

- [Hub93], [Hub94], [Hub96] Huber
- [Wed19] Wedhorn, *Adic Spaces*, arXiv:1910.05934v1
- [Hü21] Hübner, *The adic tame site*, Doc. Math. 26
- [Zav22] Zavyalov, quotients of admissible formal schemes
