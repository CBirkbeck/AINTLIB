# Expert-review session state

- Generated: 2026-05-11T13:45:00Z
- Audience: ChatGPT Pro (senior generalist mathematician)
- Goal of brief: Both — reference + route. Confirm which Mathlib infrastructure
  theorem to develop to close the Wedhorn Prop 8.15 blocker, plus identify the
  canonical citation reference.
- Scope: Mathlib infrastructure decision (post-strategy-settled). Specifically:
  which of four candidate routes (Pettis, BGR norm-based, Huber universal-property,
  Stacks completion-localization commutation) closes the `restrictionMapHom_surj`
  sorry and which is the cleanest Mathlib PR target.
- Reply received: true (date: 2026-05-11)
- Reply integrated: true (date: 2026-05-11)
- Reviewer: ChatGPT Pro

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Which of the four candidate Mathlib routes (P = Pettis, B = BGR norm-based, H = Huber universal-property, S = Stacks completion-localization commutation) closes the sorry most directly? We've ruled out P (source map is not surjective). Is S right? |
| Q2 | What is the canonical reference for the completion-localization commutation theorem (Candidate S)? Stacks tag 0AHQ-style. Is there a textbook (BGR, Bosch, Huber, ZS) with the exact PR-ready form? What hypotheses are actually needed — noetherian + adic + f.g., or weaker? |
| Q3 | What's the right generality target for Mathlib? Most-general Pettis-style (P) for reusability, or focused Stacks-style (S) for direct closure? Where's the natural home — `AdicCompletion` namespace, `Localization`, or a new file? |
| Q4 | Are there existing Mathlib hooks we should use? `AdicCompletion`, `IsLocalization.Away`, `UniformSpace.Completion.extensionHom`, `BaireSpace.of_completelyPseudoMetrizable`. Any work-in-progress PRs/branches targeting non-archimedean/adic topology we should know about? |

## Ticket-board snapshot at brief time

Active acyclicity tickets (from `.mathlib-quality/tickets.md`):

DONE (sorry-free):
- T-HYP-AUDIT: `[IsStronglyNoetherian A]` added to acyclicity signatures.
- T-QTATE-1: `IsTateRing.quotient` for closed quotients.
- T-QTATE-2: polynomial density (existing `tateAlgebra_polynomials_dense_canonical`).
- T-NULL-PER-E reframe: `LocalBasisHyp` predicate.
- T-EMBED-TOPO boundary: `productRestrictionSub_isEmbedding` factor.
- T-EX638-SCOPE: one-variable scope documented.
- T-INJ-1-CLEANUP: retired single-map injectivity annotated.
- T-NEW-1 (beast mode): `presheafValue_iteratedOverlap_equiv` — Wedhorn 2.13 overlap transport landed sorry-free, 1350 lines.
- T-NEW-2: bivariate eval continuity landed sorry-free.
- T-NEW-3: tateAcyclicity Part 1 doc-routed.

PENDING (all blocked by Wedhorn Prop 8.15 closure):
- T-NEW-4: tateAcyclicity Part 2 gluing.
- T-NEW-5: isSheafy embedding via topological transfer.

## Stuck points (from §8 of brief)

1. Wedhorn Prop 8.15 surjection-up-to-powers — the sole critical-path sorry.
   Specifically: ∀ z ∈ 𝒪_X(D), ∃ n ∈ ℕ, a ∈ 𝒪_X(D₀), z·u^n = σ(a).

## Reference list (from §2.2 of brief)

Adic spaces / non-arch geometry:
- [Wedhorn 2019] arXiv:1910.05934. Prop 8.15 in §8.1.
- [Huber 1996] Étale Cohomology. §1.1–1.5.
- [BGR 1984] Non-Archimedean Analysis. §2.8.2, §3.7.3, §3.7.5.
- [Bosch 2014] Lectures on Formal and Rigid Geometry. LNM 2105. §4.1, §4.3.
- [Schneider 2002] Nonarchimedean Functional Analysis. §8.

Topological group Open Mapping:
- [Pettis 1950] Annals of Mathematics 52, 293–308.
- [Kechris 1995] Classical Descriptive Set Theory. GTM 156. Thm 9.10, 9.11.
- [Bourbaki TG] Topologie Générale, Ch. IX, §5.3 Théorème 1.

Adic completion / localization commutation:
- [Stacks Project] Tags 00MA, 00MB, 0BNT, 0AHQ.
- [Bourbaki AC] Algèbre Commutative, Ch. III, §2.13–§3.4.
- [ZS II] Zariski-Samuel Commutative Algebra Vol. II, Ch. VIII §4.

## Cross-references to prior briefs

- `.mathlib-quality/expert-review/2026-05-11/brief.md` — first brief, covered the
  overall strategy (3-lane plan). Reviewer confirmed (Q1: Lane B parked, Q2: Lane A
  approach (a), Q3: direct per-E architecture, Q4: critical path). Settled.
  This second brief follows up specifically on the Wedhorn 8.15 / Cor 8.32
  blocker that the first brief's reply mentioned as the residual.
