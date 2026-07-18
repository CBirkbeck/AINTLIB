# Expert-review session state (topic-scoped: T-W7 group law)

- Generated: 2026-07-07
- Audience: senior arithmetic geometer, expert in abelian schemes / moduli of elliptic curves
- Goal of brief: specific-blocker + soundness — strategic guidance on the three hard steps of
  constructing (and proving canonical) the group-scheme structure on a locally-Weierstrass elliptic
  curve over an arbitrary base, and a sanity check on the reduce-to-universal reduction strategy
- Scope: T-W7 only (the group law m/ι and its axioms + canonicity); NOT the whole programme
- Reply received: true (2026-07-07; saved verbatim as reply.md)
- Reply integrated: true (2026-07-07, ADVERSARIAL AUDIT — see integration.md; plan v2 + tickets
  updated; follow-up round filed as REVIEW_FOLLOWUP-tw7.md with F1 rigidity-globalization /
  F2 Bosma–Lenstra confirmation / F3 comparison-theorem check)

## Questions in the brief

| # | Question (condensed from §6 of the brief) |
|---|------------------------------------------|
| Q1 | Cleanest construction of the multiplication morphism m_U over the domain R_univ: chord-tangent-via-resultant (total) vs affine-cover-and-glue; covering the diagonal / anti-diagonal / O; does the secant rational map extend across {x₁=x₂}. |
| Q2 | Elementary proof that π_*O_E = O_S universally for a Weierstrass model (avoiding cohomology-and-base-change)? Does it base-change from E_U/U, and with what flatness/constancy input? |
| Q3 | Formalisation-friendly statement + proof of the rigidity lemma (GIT 6.1) over an arbitrary base + "pointed ⇒ homomorphism"; which ingredient is the real obstruction; may the base be assumed reduced/normal without loss for our canonicity application? |
| Q4 | (a) Cleanest statement/proof that m_U restricted to the generic fibre equals the field chord-tangent addition (bridge scheme-morphism ↔ field-point group op); (b) minimal hypotheses for E_U^n integral. |
| Q5 | Soundness of the reduce-to-universal strategy: prove axioms as morphism identities over the integral atlas, obtain over arbitrary (non-reduced) S by base change + gluing, no reducedness of S. Pitfalls? |
| Q6 | Alternative to rigidity for canonicity: construction-level uniqueness (m as the unique morphism restricting to chord-tangent on a dense open, using flatness + closed graph); survives over non-reduced S? |

## Ticket-board snapshot at brief time (T-W7 leaves — see .mathlib-quality/tw7-plan.md)

- T-W7.0a atlasRing_isDomain — provable (1-liner)
- T-W7.0b negHom_U — tractable
- T-W7.0c mulHom_U — **Q1** (construction crux)
- T-W7.0d mulHom_U on-curve/over-U — provable from equation_add/nonsingular_add
- T-W7.0e E_U^n integral — **Q4b**
- T-W7.0f generic-fibre identification — **Q4a** (bridge)
- T-W7.0g atlas group axioms via ext_of_isDominant — provable given 0c–0f, **Q5**
- T-W7.1a chart = base change of E_U — provable
- T-W7.1 negHom / T-W7.2 mulHom (general, glue base-changes via cocycle) — provable given 0b/0c
- T-W7.3 axioms for general E (base change of 0g) — provable, **Q5**
- T-W7.6 assemble GrpObj + abelEnrichment_exists — EXISTENCE MILESTONE (no rigidity)
- T-W7.7a-i properPushforwardStructureSheaf (π_*O=O) — **Q2** (BB-COHBC gap)
- T-W7.7a-ii rigidityLemma (GIT 6.1) — **Q3** (GIT not in refs)
- T-W7.7 abelEnrichment_unique — **Q3/Q6** (canonicity)

## Stuck points (from §5 of brief)

1. m_U as an actual morphism, not a decidable-equality case split (§5.1 / Q1).
2. π_*O_E = O_S — library lacks cohomology-and-base-change (§5.2 / Q2).
3. Rigidity lemma over arbitrary base — GIT source unavailable (§5.3 / Q3).
4. Generic-fibre bridge scheme-morphism ↔ field-point group law; E_U^n integral (§5.4 / Q4).

## Reference list (from §2.2 of brief)

[GIT] Mumford–Fogarty–Kirwan, GIT 3rd ed. 1994 (Prop 6.1 rigidity — NOT in local refs).
[FC] Faltings–Chai, Degeneration of Abelian Varieties 1990 (Ch I §1; cites GIT 6.1).
[KM] Katz–Mazur, Arithmetic Moduli 1985.
[Sil] Silverman, Arithmetic of Elliptic Curves 2nd ed. (III.3.6).
[Del] Deligne, Courbes elliptiques: formulaire, LNM 476 1975.
