# Expert-review session state

- Generated: 2026-05-11T00:00:00Z
- Audience: ChatGPT Pro (senior generalist mathematician, familiar with adic spaces / Tate / rigid geometry)
- Goal of brief: Strategic guidance + concrete advice on Lane A blocker (both soundness check on overall 3-lane plan AND concrete advice on reverse round trip)
- Scope: Tate acyclicity (Wedhorn 8.28b) + immediate sheaf-theoretic context (IsSheafy spec, restriction maps, retired single-map injectivity)
- Reply received: true (date: 2026-05-11)
- Reply integrated: true (date: 2026-05-11)
- Reviewer: ChatGPT Pro

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Lane B: confirm parking, or salvageable reformulation? Given Counterexample 8.3, is the right finish that Cor 8.32 enters the critical path only via its product/cover-level form (Theorem 5.9), with the single-map "Jacobson on locSubring" route dead — or is there still a mathematically correct reformulation of single-map faithful flatness worth pursuing as parallel infrastructure (e.g., completion-level Jacobson + faithful descent, or strengthening assuming A is a Jacobson ring)? |
| Q2 | Lane A: cleanest discharge for the reverse round trip density? Of the three approaches — (a) direct pair-of-definition construction on B = A⟨X⟩/(f−X); (b) specialised density lemma bypassing Tate-ring instances; (c) abstract universal-property reformulation that makes density unnecessary — which is the right move? We lean toward (a). |
| Q3 | Lane C architecture: τ-based vs direct per-E — is this the right split? Is the per-E architecture (Laurent split inside each E rather than at the level of D_0) the right formalisation of Wedhorn Lemma 8.34, or is there a cleaner mathematical packaging (closer to Wedhorn's induction on |S|) we should adopt before final assembly? |
| Q4 | Critical-path reality check. Given current state — Lanes A and C in late assembly, Lane B parked at product level, T200-series σ-clearing in active development — is Lane A reverse round trip → Lane C Zavyalov C1 → final assembly still the fastest path? Any missing dependency (Banach OMP on non-metrisable space, Krull intersection where inapplicable, etc.) we haven't identified? |

## Ticket-board snapshot at brief time

The project tracks acyclicity work via these mathematically-named tickets (status as of 2026-05-11):

DONE (sorry-free):
- `row3_exact` — algebraic 3×3 exactness of Laurent diagram
- `tateAlgebra_flat` — A⟨X⟩ flat over A
- `flat_quotient_oneSubfX_general` — A⟨X⟩/(1−fX) flat over A
- `bivariateOverlap_equiv_B12gen` — Step B of Example 6.39 algebraic
- `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` — generic Stacks 00MA
- `tateAcyclicity_gluing_via_refinement_cover_level` — cover-level reduction
- `tateAcyclicity_Part2_direct_per_E` — direct per-E Part 2 assembly (modulo suppliers)
- `refines_by_standard_cover_per_E` — strengthened refinement output (modulo hZavyalov_per_E)
- `iteratedLaurentPlus_swap_rationalOpen`, `per_E_local_covering` — Lane C structural

IN PROGRESS:
- `TA_B1gen_quotient_specialized_equiv` — Lane A reverse round trip (the density issue)
- `presheafValueTateQuotientEquiv_topological` — Example 6.38 as topological iso (full-pair version)
- T197–T212 σ-clearing supplier composition for Lane C C1

OPEN:
- `tateAcyclicity` Part 1 (separation via Cor 8.32 product form)
- `tateAcyclicity` Part 2 (gluing via Lane A + Lane C)

RETIRED / DISPROVED:
- `restrictionMapHom_injective` — Conrad counterexample (Counterexample 8.4 in brief)
- `locIdeal_le_jacobson_bot_unconditional` — locIdeal ⊆ Jac counterexample (Counterexample 8.3)

## Stuck points (from §8 of brief)

1. §8.1 Lane A reverse round trip — quotient-Tate density for B = A⟨X⟩/(f−X)
2. §8.2 Lane C Zavyalov §2.3 candidate-family C1 formula
3. §8.3 Lane B unconditional Jacobson is FALSE (Counterexample 8.3, A = Q_p⟨X⟩)
4. §8.4 Single-map restriction injectivity is FALSE (Counterexample 8.4, Conrad)
5. §8.5 τ-based vs direct per-E architecture (subsidiary)

## Reference list (from §2.2 of brief)

- [W] Wedhorn 2019, Adic Spaces (arXiv:1910.05934) — primary
- [Huber 1996] Étale cohomology of rigid analytic varieties and adic spaces
- [Hübner 2024] On adic geometry over a non-noetherian base (arXiv:2405.06435)
- [Zavyalov §2.3] Quasicoherent sheaves on adic spaces
- [Stacks 00MA] Faithful flatness of I-adic completion when I ⊆ Jac
- [Conrad] Several approaches to non-Archimedean geometry

## Cross-references to prior packets

This brief supersedes / extends:
- `.mathlib-quality/chatgpt-packet-acyclicity-overview-2026-04-21.md` — earlier overview;
  this brief incorporates its content and updates with the (now-confirmed) Lane B falsity
  and the post-2026-04-20 direct per-E architecture.
- `.mathlib-quality/chatgpt-packet-locIdeal-jacobson-falsity.md` — counterexample
  packet; the falsity is now stated as Counterexample 8.3 in the main brief.
- `.mathlib-quality/chatgpt-packet-zavyalov-c1.md` — explicit Zavyalov §2.3
  formula question; remains an open ask, now framed inside the broader Q3.
- `.mathlib-quality/chatgpt-packet-hubner-nondomain.md` — non-domain Laurent
  separation; orthogonal to the four questions in this brief.
