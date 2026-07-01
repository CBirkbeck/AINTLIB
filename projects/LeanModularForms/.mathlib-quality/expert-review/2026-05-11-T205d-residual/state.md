# State snapshot — 2026-05-11 T205-d residual closure strategy

This is the third T205-d brief in the same day. Records the post-restructuring state.

## Brief metadata

- **Date sent:** 2026-05-11 (third T205-d brief).
- **Topic:** T205-d post-restructuring; closure strategy for `petN_heckeT_p_symmetric_form`.
- **Audience:** Same frontier LLM reviewer (DS conventions).
- **Goal:** Strategic guidance + soundness check + concrete sub-lemma planning.
- **Prior briefs:** 2026-05-11 (SMO overview), 2026-05-11-T205d (T205-d focused).
- **Reply received:** true (2026-05-11; saved verbatim to `reply.md`)
- **Reply integrated:** true (2026-05-11; audit trail in `integration.md`)

## Questions asked (numbered)

1. **Q1 — Soundness check.** Is the restructuring chain (symmetric form ⇒ unsymmetric ⇒ canonical) mathematically valid?
2. **Q2 — Path selection.** Which of Paths A (direct DS 5.5.2(b)), B (AL-Li orthogonality), C (U_p), D (mathlib wait) should we commit to? Revise the LOC estimate.
3. **Q3 — Sub-lemma plan for Path A.** Is the A1-A5 decomposition correct? Cost distribution realistic?
4. **Q4 — Alternative formulations.** Is there an easier-to-prove equivalent form?
5. **Q5 — σ_p Q-permutation on Hecke reps.** Is there a clean explicit description of the induced β ↔ β' map?
6. **Q6 — Path B circularity.** Does Li's 1975 argument explicitly use DS 5.5.3 as input?
7. **Q7 — Strategic priority.** T205-d closure vs L-function non-vanishing vs mathlib wait?

## Ticket board snapshot at brief time

| Ticket | Statement | Status |
|---|---|---|
| `T205-d-API-1` | FD-transport | DONE |
| `T205-d-API-2-INT` | Domain-level adjugate slash adjoint | DONE (existing) |
| `T205-d-API-2-DC` | Double-coset adjugate correspondence | SUPERSEDED by restructuring |
| `T205-d-API-2-DC-IUNION-M/T/CLOSE` | iUnion-form σ_p absorption residuals | SUPERSEDED |
| `T205-d` | DS 5.5.3 unsymmetric | proven conditionally on T205-d-SYMM |
| `T205-d-SYMM` (= `petN_heckeT_p_symmetric_form`) | DS 5.5.3 symmetric form | **OPEN — sole sorry** |
| `T207` | Spectral theorem | DONE |
| `T209` | AL-Li orthogonality | OPEN, blocked on T205-d |
| `T210` | Newform decomposition | OPEN, blocked on T209 |
| `POST-6` | Miyake Main Lemma 4.6.8 | OPEN, blocked on T205-d+T207 |
| `POST-7` | Strong Multiplicity One | conditional version landed |

## Stuck points

1. The σ_p Q-permutation on Hecke representatives (β ↔ β' map).
2. Per-β sum identity (**) in §7: domains don't match, sum-level absorption needed.
3. Choosing between Paths A/B/C/D given current evidence.

## Key sources

- DS §5.5 (Theorem 5.5.3, Proposition 5.5.2(b)).
- Miyake §4.5 (Theorems 4.5.4, 4.5.5).
- Shimura §3 (Theorems 3.20, 3.24, 3.34).
- Atkin-Lehner 1970, Li 1975.

## What changed since the prior T205-d brief

- Restructuring landed: 14-layer scaffold sorry concentrated into single named theorem.
- Build clean (3092 jobs).
- 5 sub-tickets (IUNION-M/T/CLOSE, SYMM-DIRECT) added then superseded by the restructuring.
- Reviewer's previous "150-300 LOC pointwise + few hundred more" estimate stands, but now applies to the single named residual.

## Outcome of this brief (post-reply)

Reviewer rules against all four originally proposed paths (A direct,
B AL-Li, C U_p, D mathlib wait) and prescribes a five-step chain:

```
ADJ-WRAPPER (30-100) → ADJ-CORR (150-300, real work)
                     → DIAMOND-SPEC (150-250)
                     → UNSYMM (30-50)
                     → SYMM (30-50)
Total: 350-650 LOC
```

Critical reframe: the β ↔ β' map is the WRONG indexing object.
Adjugates of a left transversal collapse as left cosets. The bijection
lives on transposed correspondence / right-left quotient data.

Acceptance for next worker pass: compiling ADJ-CORR theorem for
Γ = Γ₁(N), α = diag(1,p), or one exact blocking FD/integrability/
transversal lemma.

Tickets and tasks updated: see `integration.md` for full audit trail.
