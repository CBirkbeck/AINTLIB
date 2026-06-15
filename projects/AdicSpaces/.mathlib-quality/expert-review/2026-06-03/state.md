# Expert-review session state

- Generated: 2026-06-03
- Audience: Adic-spaces / Huber expert (can cite [Hu2] 3.9 and Wedhorn by number; assumes the machinery)
- Goal of brief: Strategic guidance — does the overall route to IsSheafy (Thm 8.28(b)) hold together? Focus on Prop 7.48 as the one deep external blocker.
- Scope: All of Thm 8.28(b) (flatness → Cor 8.32 → topological embedding → Čech acyclicity)
- Reply received: true (2026-06-03)
- Reply integrated: true (2026-06-03) — see integration.md

## Questions in the brief (§9, verbatim)

| # | Question |
|---|----------|
| Q1 | Is the faithful-flatness route via "Prop 8.30 (flat factors) + maximal-ideal/cover bridge supplied by Prop 7.48" right — and is the *full* homeomorphism Spa Â ≅ Spa A (preserving rational subsets) genuinely needed, or does Cor 8.32 require only a weaker consequence (surjectivity onto the cover's points, or injectivity of the support map on maximal ideals)? |
| Q2 | Cleanest machine-formalisable proof of Spa Â ≅ Spa A (Prop 7.48 / [Hu2] 3.9)? Can the injectivity half (two continuous valuations on the completion agreeing on the dense subring are equal) be proved directly from continuity + density + the valuation-spectrum topology, without reproducing [Hu2] §3? |
| Q3 | Any route to Cor 8.32 / the acyclicity that never invokes the Spa–completion correspondence — e.g. a purely algebraic argument that T·A = A forces faithful flatness of ∏ 𝒪_X(Uᵢ) over 𝒪_X(X) after completion (via the Laurent presentations 6.38/6.39 + a Čech-style computation)? What does Wedhorn mean by Cor 8.32 being "immediate"? |
| Q4 | Is the (embedding = topological embedding) ∧ (gluing = amalgamation) packaging of "sheaf of topological rings" (Remark 8.20) the right target, and is obtaining the inducing a posteriori from acyclicity + the open mapping theorem (Thm 5.1) legitimate (not circular)? |
| Q5 | Are our [He]+[BGR] proofs of Wedhorn 6.16/6.17/6.18 (which [W] marks "Proof. Missing") the ones the reviewer would expect, and is the [He] zero-sequence-of-units open mapping route (rather than a classical σ-compact Banach route) correct for the modules that occur over a general Tate ring? |
| Q6 | Which Huber source actually carries "Spa Â → Spa A is a homeomorphism preserving rational subsets" as Prop 3.9 — *Continuous valuations* (Math. Z. 212, 1993) or the 1990 Habilitationsschrift *Bewertungsspektrum und rigide Geometrie*? |

## Ticket-board snapshot at brief time (8.28(b)-relevant; from .mathlib-quality/tickets.md)

Live critical path is the "FLATNESS SUMMIT" (Tier 1+2). Chain: Thm 8.28(b) ← Lemma 8.34 ← Lemma 8.33 + Cor 7.32[✅] ← Cor 8.32 ← Prop 8.30 ← Remark 7.55 + Example 6.38-over-B + Lemma 8.31[✅] ← Remark 8.29[✅]. Tier-3 (Čech gluing, Appendix A) deferred.

DONE / axiom-clean: T-MVT-1..6 (base-change noetherian via general-n Tate topology + Example 6.38); Lemma 8.31 (both Laurent quotients); Remark 8.29 muMap; Cor 7.32; Banach OMT wedhorn_6_16_of_topNilpUnit + fg_topologicalClosure_isClosed + Wedhorn 6.18(2); Nullstellensatz 7.45/7.52(2); per-step Prop 8.30 flat engine; faithfullyFlat_pi_of_maximal_ne_top (abstract); exists_spa_presheafValue_of_rationalOpen (⊇ direction); T-SUM-1/T-SUM-3.

OPEN sorry leaves on critical path (8 distinct, zero `axiom`):
- prop_8_30_remark755_chain (Remark 7.55 chain assembly) — bookkeeping
- cor_8_32_spaExtendsAlongRestriction (T-SUM-2-RESID) — = Prop 7.48 / [Hu2] 3.9
- comap_coeRingHom_injOn_spa — = Prop 7.48 injectivity
- cor_8_32_productRestrictionSub_isInducing / productRestrictionSub_isInducing_tate — downstream of acyclicity + landed OMT
- lemma_8_34_gluing, lemma_8_33_laurent_cover_gluing — Tier-3 Čech
- presheafValue strong-noeth (T-SUM-6-Rb) via Remark 6.37(1) — replaces FALSE isStronglyNoetherian_of_isNoetherianRing_isTateRing
- example638_multivariate_surjection general-Fin-n eval map (documented construction gap)

## Stuck points (from §8 of the brief)

1. §8.1 — Prop 7.48 = [Hu2] 3.9 (Spa Â ≅ Spa A); the ONE deep blocker. Needed for Cor 8.32 injective via the maximal-ideal/cover bridge. ⊇ direction done; injectivity is the gap. Subject of Q1–Q3.
2. §8.2 — Čech-acyclicity layer (Lemma 8.33/8.34 + Appendix A); substantial but standard; its analytic input (OMT) is already landed. Subject of Q4.
3. §8.3 — two FALSE-as-stated shortcuts identified + rerouted: "noetherian Tate ⟹ strongly noetherian" (fix: Remark 6.37(1) t.f.t.) and "strongly noetherian ⟹ noetherian ring of definition" (fix: migrate off noeth-A₀). Both fail for ℂ_p.
4. §8.4 — deliberately avoided hypotheses (no IsDomain, no noeth ring-of-def, no σ-compactness, no linear topology); the ℂ_p test.

## Reference list (from §2.2)

- [W] Wedhorn, Adic Spaces, arXiv:1910.05934 (2019)
- [Hu2] Huber, Continuous valuations, Math. Z. 212 (1993), 445–477 — Prop 3.9 = Wedhorn 7.48 (bibliographic uncertainty: Q6)
- [Hu3] Huber, A generalization of formal schemes and rigid analytic varieties, Math. Z. 217 (1994), 513–551
- [BGR] Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Springer (1984)
- [He] Henkel, An open mapping theorem for rings which have a zero sequence of units, arXiv:1407.5647 (2014)
- [Bbk] Bourbaki, Topologie Générale Ch. III §3 no. 3 Théorème 1
