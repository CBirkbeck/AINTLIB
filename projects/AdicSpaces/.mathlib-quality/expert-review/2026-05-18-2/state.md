# Expert-review session state — 2026-05-18 (second brief, Session 22)

- Generated: 2026-05-18T10:30:00Z
- Audience: Same mathematical-model reviewer (ChatGPT / Claude class) who answered the 2026-05-18 first brief
- Goal of brief: **Comprehensive accuracy + cascade audit** of ~52 in-scope sorries in the IsSheafy / Tate acyclicity transitive closure
- Scope: Tate acyclicity only (per `feedback_scope_tate_acyclicity` memory; excludes Wedhorn 7.5/7.12, perfectoid, Scottish Book, etc.)
- Reply received: true (date: 2026-05-18T10:30:00Z)
- Reply integrated: true (date: 2026-05-18T11:00:00Z, Session 23)
- Integration record: ./integration.md

## Trigger

Session 22 `/develop --decompose` second pass found that previously ✓-marked leaves A3, B5, F5, I2 are actually load-bearing on the deleted B2/B3/B4 chain (A3, B5) or have edge-case accuracy issues (F5, I2). The prior brief (2026-05-18, see `../2026-05-18/`) asked only about directly-suspect leaves, not their cascade — this brief addresses every in-scope leaf with explicit accuracy + cascade questions.

## Questions in the brief

### Per-leaf questions (in §7 of the brief)

For each of ~52 leaves: Accuracy-Q + Cascade-Q. The most detailed ones are for the SUSPECT leaves A3, B5, F5, I2 (Q-A3.acc/.cas, Q-B5.acc/.cas, Q-F5.acc/.cas, Q-I2.acc/.cas).

### Meta-questions (in §9)

| # | Question |
|---|----------|
| Q-META.1 | Does Wedhorn 8.28(b) Case (b) have a proof in the literature that doesn't route through Wedhorn 6.18 forward / 8.28(a) reduction? Or should A3 be deleted / restated parametric / restricted to BGR 5.2.6 setting? |
| Q-META.2 | Cascade audit policy: what's the right pre-flight diagnostic for surfacing cascade dependencies before a brief? |
| Q-META.3 | Is Wedhorn 8.28(b) a theorem for non-domain strongly noeth Tate rings ($A = k\langle T,U\rangle/(TU)$ etc.)? How does Wedhorn handle non-domain cases? Or is the project's IsDomain hypothesis forced by Laurent splits? |
| Q-META.4 | Cluster E (E1, E2, E3, E4) is orphaned post-Session-21. Delete entirely or salvage for downstream use? |
| Q-META.5 | Among ~30 remaining ⚠P leaves, what's the right priority order for unblocking? Our guess: C1, F4, I1. |
| Q-META.6 | Concrete decision per SUSPECT leaf: A3 / B5 / F5 / I2 — delete, restate parametric, keep sorry'd, case-split? |
| Q-META.7 | Any other ⚠P leaves the reviewer suspects of being load-bearing on something we deleted? |

## Ticket-board snapshot at brief time

Same as `2026-05-18/state.md` (no changes to formal ticket board between briefs; the inter-brief work was deletion + audit, not new ticket creation).

Cluster summary (post-Session-21):
- Cluster A (top-level IsSheafy): 3 leaves (A1 parametric, A2 hSpa-parametric, A3 SUSPECT Wedhorn-exact)
- Cluster B (direct deps): 5 remaining (B2/B3/B4 DELETED; B1, B5 SUSPECT, B6, B7, B8 remain)
- Cluster C (Wedhorn-clean wrappers): 5 (C1-C5)
- Cluster D (Wedhorn 7.40-7.52): 10 (6 closed: D3, D4, D11, D13, D15, D16)
- Cluster E (Wedhorn 6.18 chain, ORPHANED): 4 (E1 false, E2 sig-fixed, E3 stacks 0316, E4)
- Cluster F (refinement tree): 12 (F2/F3 scope-error, F5 SUSPECT)
- Cluster G (restriction-map scaffolding, post-deletion): 1 (G3 only)
- Cluster H (Wedhorn 7.31/7.32/7.35): 4 (H3/H4 out of scope)
- Cluster I (Stacks 023N + 8.33): 3 (I2 SUSPECT)
- Cluster K (mis-located scaffolding): 2 (K1, K2)
- Cluster N (Session-21 cascade sorries): 4 (N1-N4)

Total: ~52 in-scope.

## Stuck points (from §8 of brief)

1. S1 — Wedhorn-exact no-parameter route (A3 + B5 + B1 + C2) may not exist. The cascade of "no noetherian ring of definition implies no proof route" persists in surviving wrappers.
2. S2 — IsDomain hypothesis location is unclear. Used at top (A1/A2) and in F4 Laurent splits; reviewer needed to clarify whether it's removable.
3. S3 — Cluster E orphan: 4 leaves no longer on any IsSheafy path. Delete or salvage?

## Reference list (from §2.2 of brief)

- [Wedhorn] arXiv:1910.05934v1
- [Hu1, Hu2, Hu3] Huber's three papers
- [BGR] Bosch-Güntzer-Remmert §5.2.6 Theorem 1
- [Stacks] tags 023N (descent), 0316 (completion-noetherian)
- [Hübner] arXiv:2405.06435 (refinement trees)
- Prior brief: `../2026-05-18/brief.md`
- Prior reply: `../2026-05-18/reply.md`
