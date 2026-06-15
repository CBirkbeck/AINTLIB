# Expert-review session state

- Generated: 2026-06-14
- Audience: adic-spaces / Huber expert (fluent in Spa, affinoid rings, Tate rings, structure presheaf — minimal background needed)
- Goal of brief: all three — (1) validate the K2→K1→A route + overall decomposition's faithfulness to Wedhorn; (2) soundness check on the HasLocLift-on-completions obstruction; (3) reference hunt on the deep keystones (Pettis-lift, faithful HasLocLift, Nullstellensatz)
- Scope: the 3 remaining leaves of Wedhorn Thm 8.28(b) + their shared keystones
- Reply received: true (2026-06-14)
- Reply integrated: true (2026-06-14)

## Questions in the brief (verbatim from §9)

| # | Question |
|---|----------|
| Q1 | Does Wedhorn's Remark 7.55 chain genuinely need (LL) [loc-lift power-boundedness] on the base-changed completion B = 𝒪_X(D), or is there a reformulation transporting back to covers of the original X (via 𝒪_{Spa B}(Xᵢ) ≅ 𝒪_X(Eᵢ)) that sidesteps needing (LL) for a completion? |
| Q2 | Cleanest faithful route to power-boundedness of localization lifts σ(t/s) in 𝒪_X(D') for a complete strongly noetherian Tate ring WITHOUT assuming domain or "A⁺ = A₀"? Is Wedhorn 7.18 the right tool; does it reduce to the affinoid Nullstellensatz, or is there a more direct route via the A⟨X⟩/I presentation? |
| Q3 | For Prop 7.51(2) (Spa point with support a given maximal ideal 𝔪 of a complete affinoid ring): is the correct valuation the canonical rank-1 valuation on the complete non-arch field A/𝔪, rather than the trivial valuation (which is continuous only if 𝔪 is open)? |
| Q4 | Is the open-mapping "Pettis-lift" for Prop 6.18 a standard citable result (Huber/BGR/Henkel 2014/Bourbaki TVS) for products/equalizers of affinoid algebras, or genuinely missing infrastructure? |
| Q5 | Is the planned order (Nullstellensatz → faithful (LL) → fold Remark 7.55 chain (Leaf A); then Leaf C grind, Leaf B Pettis) right? Is the top-level decomposition (embedding = faithfully-flat + open-mapping; gluing = Čech via Lemma 8.34) the one Huber/Wedhorn use, or is there a more economical route? |

## The three leaves (the "in progress" targets)

- LEAF A (separation/flatness): whole-space flatness B → 𝒪_{Spa B}(im E), via the Remark 7.55 basic-Laurent chain. Gated by (LL) on the completion B (the §8.1 obstruction = keystone K1).
- LEAF B (inducing/topological): the restriction is a topological embedding (Prop 6.18 open mapping). Gated by keystone K3 (Pettis-lift).
- LEAF C (gluing): Čech H¹ = 0 for ideal-generating covers (Lemma 8.34 parts i+ii). Gated by keystone K4 (Čech engine residuals).

## Keystones (the obstruction structure surfaced this session)

- K1 = faithful HasLocLiftPowerBounded on completions (gates A). Only case-(a) instance exists (needs domain + A⁺=A₀, false for completions). Splits into K1u (unit, → K2) and K1pb (power-bounded, Wedhorn 7.18/7.41, currently case-(a) only).
- K2 = Nullstellensatz / Spa-point-on-maximal-ideal (Prop 7.51 part 2). Faithful-form, isolated, MOST TRACTABLE. ⚠ soundness concern: trivial-valuation plan may be wrong (Q3).
- K3 = Prop 6.18 Banach-OMT. σ-compact-free core landed; residual = Pettis-lift (Q4).
- K4 = Čech engine. Diffuse combinatorial residuals; lowest risk, most work.

## Stuck points (from §8 of brief)

1. §8.1 — (LL) obstruction on the base-changed completion B (the heart; gates Leaf A).
2. §8.2 — faithful (LL) keystone (K1 = K1u + K1pb).
3. §8.3 — Nullstellensatz construction soundness concern (K2; trivial vs canonical rank-1 valuation).
4. §8.4 — Pettis-lift for the open mapping (gates Leaf B).
5. §8.5 — Čech residuals (gates Leaf C; grind, low risk).

## Reference list (from §2.2 of brief)

- [Wedhorn] Adic Spaces, arXiv:1910.05934v1 (primary).
- [Hu3] Huber, Math. Z. 217 (1994) — Lemma 7.54 = [Hu3] Lemma 2.6.
- [Hu2] Huber, Étale Cohomology of Rigid Analytic Varieties and Adic Spaces, Vieweg 1996.
- [BGR] Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Springer 1984.
- [Henkel] arXiv:1407.5647 (open mapping / Pettis-lift).

## Notes

- wedhorn.txt is ABSENT on this machine (the CLAUDE.md path is stale); brief built from in-repo transcribed docstrings + verified axiom-traces. Full internal feasibility map: docs/SHEAFY-FEASIBILITY-MAP.md.
- Supersedes the 2026-06-09 brief (gluing-leaf-only); this one covers all 3 leaves and centers the (LL) obstruction.

## Follow-up round (2026-06-14) — (LL-bdd)

- Trigger: (LL-unit) landed sorry-free via the criterion route; (LL-bdd) bottoms at the
  IsDomain-free Wedhorn 7.18 (our integral criterion needs [IsDomain]; PlusSubring has no
  integrality axiom).
- Follow-up brief: ./followup-llbdd.md
- Reply received: false
- Questions:
  - Q-bdd-1: cleanest IsDomain-free route to power-boundedness of x with v(x)≤1 on Spa(B,B⁺)
    for a complete strongly-noeth Tate ring B that is NOT a domain (minimal-prime reduction
    vs direct restriction-map-preserves-PB).
  - Q-bdd-2: can Leaf A be structured so (LL-bdd) is only ever invoked with numerators in the
    ring of definition (basic-Laurent), sidestepping the general 7.18 keystone entirely?

## Follow-up round REPLY INTEGRATED (2026-06-14)

- Reply received: true; saved reply-llbdd.md.
- VERDICT: skip general (LL-bdd) for Leaf A; use basic Laurent steps R(f/1),R(1/f) arbitrary f,
  flat by Lemma 8.31(2). General (LL-bdd) = future infra via non-domain Wedhorn 7.18 (NOT
  minimal-prime). PlusSubring API gap flagged (missing B⁺⊆Bᵒ axiom; local hplus fix OK).
- Tasks updated: #65 closed (off critical path), #67 Leaf A revised.
- LEAF A KEYSTONE now pinned: general (non-discrete) basic-Laurent flatness for arbitrary f
  (B⟨X⟩/(f-X), B⟨X⟩/(1-fX) flat over B) — the project's documented-blocked "G2-topo" ticket
  (FlatnessResults:163-186). Pieces: mathlib AdicCompletion.flat_of_isNoetherian +
  presheafValue_ringOfDef_ringEquiv_adicCompletion. Faithful chain encoding needs the source
  (arXiv:1910.05934v1, ABSENT).
