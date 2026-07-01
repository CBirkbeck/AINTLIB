# State snapshot — 2026-05-11 T205-d brief

This file records the state of the project at the moment the T205-d-focused brief was sent,
so that a future `/expert-review --reply` invocation can integrate the reviewer's response.

## Brief metadata

- **Date sent:** 2026-05-11 (second brief; follow-up to 2026-05-11 SMO-overview brief).
- **Topic:** T205-d — Petersson adjoint $T_p^* = \langle p \rangle^{-1} T_p$ at level $\Gamma_1(N)$, $p \nmid N$.
- **Audience:** Same frontier LLM reviewer (DS conventions).
- **Reply received:** true (2026-05-11)
- **Reply integrated:** true (2026-05-11)
- **Integration record:** `integration.md` in this directory.
- **Brief file:** `brief.md` in this directory; also `REVIEW_BRIEF.md` in project root.

## Questions asked (numbered)

1. **Q1 — Integrand identity formulation.** Which formulation of Lemma 7.1 (DS Prop 5.5.2(b) pointwise) is cleanest for Lean: symmetric, asymmetric, $M^*$-reformulated, or operator-valued?
2. **Q2 — Obstacle 2 (modular bookkeeping).** Standard organisational principle for the $|c\tau+d|^{-2k} \cdot (c\tau+d)^k \cdot \overline{(c\tau+d)^k} = 1$ cancellation in Lean?
3. **Q3 — 8-layer chain salvage.** Scrap Layers 5–8 or salvage? Are the iUnion-form residuals worth keeping for T209?
4. **Q4 — Tickets for Target 4.3.** Which sub-tickets to plan: (i) pointwise integrand identity, (ii) FD-reconstruction, (iii) cocycle identity matrix arithmetic — or others?
5. **Q5 — Specialisation Step 3.** Is the specialisation from Target 4.3 to Target 4.4 really mechanical, or does the $\sigma_p$ Q-permutation involve hidden bookkeeping?
6. **Q6 — Alternative routes.** Does Atkin–Lehner–Li orthogonality give T205-d for free (we suspect circularity)? Is per-prime $U_p$ decomposition a viable partial substitute?
7. **Q7 — Sanity check on scale.** Is the 500–1000 LOC estimate for Lemma 7.1 realistic?

## Ticket board snapshot at brief time

| Ticket | Statement | Status |
|---|---|---|
| `T205-d-API-1` | Step 1 FD-transport | **DONE** (sorry-free, axiom-clean) |
| `T205-d-API-2` | Step 2 Hecke-correspondence adjoint, parametric in $\alpha$ | **OPEN** (blocker: Lemma 7.1) |
| `T205-d` | Step 3 DS 5.5.3 specialised: $T_p^* = \langle p \rangle^{-1} T_p$ | **OPEN, declared B3 OFF-TRACK in beastmode** |
| `T207` | Spectral theorem (commuting Hecke) | **DONE** (depends on T205-d for input spectrality) |
| `T209` | Atkin–Lehner–Li orthogonality | **OPEN** (depends on T205-d) |
| `T210` | Newform decomposition | **OPEN** (depends on T209) |
| `POST-6` | Miyake Main Lemma 4.6.8 | **OPEN** |
| `POST-7` | Strong Multiplicity One (Miyake 4.6.12) | **OPEN, conditional version landed** |

## Salvageable infrastructure (decisions held pending reviewer feedback)

- **Triple-product identity** (Layer 2 of 8-chain). Algebraic. Will keep regardless.
- **$\sigma_p$ Q-permutation** (Layer 3 of 8-chain). Needed for Step 3 (specialisation). Will keep regardless.
- **`peterssonInner_slash_adjoint_coset`** (Layer 4, level-1 case). Scaffold for Step 2. Will keep.
- **M_∞ stockpile** (Layer 5). ~200 LOC. **Pending Q3** — may delete.
- **iUnion-form bookkeeping** (Layers 6–7). ~250 LOC. **Pending Q3** — may delete.
- **Branch closure** (Layer 8). ~50 LOC. **Pending Q3** — may delete.

## Working hypothesis pre-reply

If reviewer says "drop the 8-layer chain entirely, formalise Lemma 7.1 with the $M^*$-reformulation (option (c) in §9.1)":
- Plan T205-d-API-2-LEMMA-A (cocycle identity matrix arithmetic, Obstacle 1).
- Plan T205-d-API-2-LEMMA-B (Möbius-Im transform, Obstacle 2).
- Plan T205-d-API-2-LEMMA-C (pointwise integrand identity, Lemma 7.1).
- Plan T205-d-API-2-LEMMA-D (FD-reconstruction $\alpha^{-1}\Gamma\alpha \to \Gamma$).
- Plan T205-d-API-2-CLOSURE (assembly of Target 4.3 from A–D + Step 1).
- Plan T205-d-SPEC (specialisation via $\sigma_p$, Step 3 from Target 4.3).

If reviewer says "salvage the iUnion residuals for T209":
- Keep Layer 6 stockpile; rebrand as T209 infrastructure.
- Still need Lemmas A–D + CLOSURE + SPEC.

If reviewer says "try Route A (direct Atkin–Lehner–Li orthogonality)":
- Verify non-circularity (Q6).
- If non-circular: plan T209-DIRECT bypassing T205-d.
- If circular: stick with two-step API.

If reviewer says "your scale estimate is too low":
- Re-evaluate timeline; potentially declare T205-d a long-term project and pursue conditional SMO routes in parallel.

## Files that will need editing after reply integration

- `LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` — primary site for T205-d and helpers.
- `.mathlib-quality/tickets.md` — ticket board updates.
- Potentially `LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean` if reviewer recommends specialisation refactor.
- Potentially new file(s) under `LeanModularForms/HeckeRIngs/GL2/` for pointwise integrand identity and Möbius-derivative bookkeeping.
