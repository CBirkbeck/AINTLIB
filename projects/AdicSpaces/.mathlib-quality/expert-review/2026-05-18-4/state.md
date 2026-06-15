# Expert-review session state (Round 4)

- Generated: 2026-05-18T15:55:00Z
- Audience: same external mathematician who replied to round 3 (see ../2026-05-18-3/reply.md)
- Goal of brief: strategic guidance + targeted confirmation on three architectural decisions
- Scope: Session 26 plan only (NEW since round-3 reply, not the whole project)
- Reply received: true (2026-05-18T16:00:00Z)
- Reply integrated: true (2026-05-18T16:05:00Z) — see integration.md

## Questions in the brief

| # | Question | Reviewer verdict |
|---|----------|------------------|
| Q1 | Canonical Huber-field valuation: build constructor or sidestep? | SIDESTEP via Wedhorn 7.45 reduction — open-m trivial valuation, non-open via 7.45 |
| Q2 | F12 straight move? | YES — all 4 declarations as unit |
| Q3 | C3 build in full or parametrize? | BUILD IN FULL; 3 sub-lemmas named |
| Q4 | Krull non-domain — add IsDomain or different argument? | ADD `[IsDomain A]`; document narrower; row-exactness alternative if later remove |
| Q5 | Cluster L complete? | YES — three TateAlgebra replacements suffice; don't reintroduce wrappers |
| Q6 | cor_8_32_clean_via_laurent main API? | NO — write `_via_flat` as main; `_via_laurent` is Laurent-special-case |
| Q7 | Stacks 0316 direct vs gr-route? | DIRECT route (current plan); ~150 LOC optimistic but right |
| Q8 | L5.1.1 encoding has redundant factor? | YES — use `A ⊗[P.A₀] AdicCompletion (...)`; current code already matches |

## Ticket-board snapshot at brief time

(Unchanged from initial state; superseded by integration.md updates below.)

## Stuck points (from §3-§4 of brief)

(See integration.md for post-reply status.)

## Reference list (from §1-§5 of brief)

- Wedhorn, T., *Adic Spaces*, arXiv:1910.05934 (sections cited: 6.18, 6.36, 6.37, 6.38, 7.31-7.32, 7.40-7.52, 7.54, 8.2, 8.28-8.34).
- Stacks Project, tags 0316 (= Lemma 10.97.6), 0306 (= Lemma 10.31.2), 05GH (= Lemma 10.97.5), 023N (faithfully flat descent equaliser).
- Bourbaki, *Commutative Algebra*, Ch. VI §3.5 (composition / specialisation of valuations).
- Engler-Prestel, *Valued Fields* (Springer), §1.3 (lattice of valuations).
- Atiyah-Macdonald, *Introduction to Commutative Algebra*, §10 Theorem 10.27.

## Prior reviewer replies (cross-reference)

- 2026-05-18 (round 1): ../2026-05-18/reply.md (per-leaf catalogue Q&A)
- 2026-05-18-2 (round 2): ../2026-05-18-2/reply.md (cluster verdicts)
- 2026-05-18-3 (round 3): ../2026-05-18-3/reply.md (Path α decision; Q-S24.1-4)
- 2026-05-18-4 (round 4): ./reply.md (this round — Session 26 plan validation + 5-column ledger methodology)
