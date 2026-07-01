# Reply integration — 2026-05-11 T205-d follow-up

Reply received on 2026-05-11 (same-day follow-up to morning brief).
Brief: `brief.md`
Reply: `reply.md`

## Interpretation summary

The reviewer's principal correction — "pivot from α⁻¹ to adjugate α*" — was
correct *for the brief's wording* but turned out to already be reflected in
the actual code:

- `peterssonInner_slash_adjoint` (AdjointTheory.lean line 779) is stated with
  `peterssonAdj α`.
- `peterssonInner_slash_adjoint_coset` (line 3730) is also stated with
  `peterssonAdj β`.

The brief mischaracterised our scaffold. The reviewer's positive ticket
structure (4-step decomposition: pointwise → integrated → double-coset →
specialisation) still applies, but the pointwise step is already done.

Verified flags:
- **Risk 3 (index p+1 vs p)**: `Gamma_p_α` is `conjGL Γ₁(N) α ⊓ Γ₁(N)`; for
  α = diag(1,p), p ∤ N, this has index p+1 in Γ₁(N) (Shimura Prop 3.32). ✅
- **Step 3 NOT mechanical**: confirmed. diag(p,1) is not the same Γ₁(N)
  double coset as diag(1,p); we will use σ_p + diamond unitarity.

Unrealised risks (recorded but no action needed):
- Risk 1 (scalar misalignment): brief mismatch, not code. Code is in adjugate form.
- Risk 4 (central scalar λ^{k-2}): will track during T205-d specialisation.

## Changes applied

- **NEW** ticket `T205-d-API-2-INT`: marks `peterssonInner_slash_adjoint`
  (line 779) as the integrated-domain adjugate slash adjoint. Effectively
  DONE; no new work.
- **NEW** ticket `T205-d-API-2-DC`: double-coset assembly into adjugate
  correspondence. 150–250 LOC. Consumes T205-d-API-1 + T205-d-API-2-INT +
  triple-product identity. Currently the real blocker for T205-d.
- **MODIFIED** `T205-d-API-2`: now framed as a parent ticket split into
  T205-d-API-2-INT (✅) + T205-d-API-2-DC (open).
- **MODIFIED** `T205-d`: clarified that the specialisation is NOT mechanical.
  Three concrete bookkeeping items documented (different Γ₁(N) double cosets;
  central scalar action; σ_p + diamond unitarity organisation).
- **NEW** top-of-file section "Reviewer feedback integrated 2026-05-11
  (T205-d follow-up)" summarising the 8 corrections.

## Changes rejected by user

(none — full approval)

## Open questions remaining

(none unanswered — all 7 brief questions addressed)

## Decisions recorded but not actioned

- **Brief correction**: the 2026-05-11 T205-d brief incorrectly stated
  Lemma 7.1 with α⁻¹. The code is in α* form. Future briefs should consult
  the actual code declarations before drafting target identities.
- **Scale estimate revision**: 150–300 LOC for the new pointwise/aggregate
  algebra (was 500–1000), thanks to the reviewer's confirmation that
  `peterssonInner_slash_adjoint` already covers the pointwise/integrated
  identity.
