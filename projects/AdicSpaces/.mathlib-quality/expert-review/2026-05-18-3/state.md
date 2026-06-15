# Expert-review session state — 2026-05-18 (third brief, Session 24)

- Generated: 2026-05-18T11:30:00Z
- Audience: Same mathematical-model reviewer (ChatGPT / Claude class) who answered the round-1 and round-2 briefs
- Goal of brief: focused verdict on **4 mathematical questions + 1 meta-question** surfaced by the Session-24 adversarial audit
- Scope: IsSheafy / Tate-acyclicity chain; specifically the 4 implicit-assumption gaps in Wedhorn 8.31 / 8.34 / Ex 6.38 / completeness
- Reply received: true (date: 2026-05-18T13:30:00Z)
- Reply integrated: true (date: 2026-05-18T14:00:00Z, Session 25)
- Integration record: ./integration.md

## Trigger

Session 24 adversarial audit (`.mathlib-quality/adversarial-audit-2026-05-18.md`) found 8 red flags. 4 were resolved by user's Path α commit (parametric noeth pair). 4 remain — these are not deletion-cascade issues but rather implicit-assumption-in-proof-route issues. This brief asks the reviewer to settle them.

## Questions in the brief

| # | Question |
|---|----------|
| Q-S24.1 | Does Wedhorn's Example 6.38 produce a noetherian ring of definition for `O_X(D)` when `A_0` is noetherian? If yes, Path β potentially unblocks. |
| Q-S24.2 | Does Wedhorn 8.31's proof actually need `[IsNoetherianRing A_0]`, or is "noetherian Tate A" sufficient (i.e., A noetherian as abstract ring)? |
| Q-S24.3 | How does Wedhorn 8.34 handle the non-domain case? Project's Laurent split degenerates in non-domain settings (G2 counterexample). |
| Q-S24.4 | Does A3 / Wedhorn 8.28(b) need explicit `[CompleteSpace A]` in the signature? Project's IsTateRing doesn't imply completeness. |
| Q-S24.META | What's the right pre-flight diagnostic for "statement-vs-proof hypothesis mismatch"? The 4 questions above are NOT deletion cascades — they're implicit assumptions in proof routes that prior 2 rounds didn't surface. |

## Ticket-board snapshot at brief time

No ticket-system changes since round 2. Same task list:
- Pending: T-EMBED-TOPO, T-MATHLIB-STACKS-00MA, T-LOCLIFT-PRESERVATION, T-LAURENT-REFINEMENT-TREE-EXISTENCE, P3-P8
- Recently applied (Session 24): Path α — A3/B5'/C1/C2/AuditCleanWrappers all parametrised to take `(P, [IsNoetherianRing P.A₀])`

## Stuck points

S1 — Wedhorn 8.31 hypothesis profile uncertainty (Q-S24.2)
S2 — Ex 6.38 canonical-pair-noetherianity status (Q-S24.1)
S3 — Non-domain Lemma 8.34 (Q-S24.3)
S4 — Missing CompleteSpace in A3 signature (Q-S24.4)

## Reference list

- Wedhorn arXiv:1910.05934v1
  - Lemma 8.31 p.82
  - Lemma 8.34 p.84
  - Example 6.38 p.54
  - Theorem 8.28(b) p.80
- BGR §5.2.6 Theorem 1
- Stacks tag 0316
- Round-1 brief / reply: `../2026-05-18/`
- Round-2 brief / reply: `../2026-05-18-2/`
- Adversarial audit: `../adversarial-audit-2026-05-18.md`
