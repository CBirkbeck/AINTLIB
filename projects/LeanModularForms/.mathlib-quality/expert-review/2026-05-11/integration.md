# Reply integration — 2026-05-11

Reply received from frontier-LLM expert reviewer on 2026-05-11.
Brief: ./brief.md
Reply: ./reply.md

## Interpretation summary

| # | Reviewer point | Maps to | Type |
|---|---|---|---|
| 1 | Γ₀(N)-pivot is correct | Q1 | direct answer (yes) |
| 2 | General-χ abstract ring hom should be parked | Q2 | direct answer (skip) |
| 3 | T205-d should be reframed to finite-index Hecke-correspondence adjoint | Q3 | direct answer + redirect |
| 4 | T205-d is NOT the only critical blocker; mainLemma should not depend on T207 | Q5 | critical correction |
| 5 | **"Newforms have a_n = 0 for (n,N) > 1" is FALSE** | unprompted | **CRITICAL mathematical correction** |
| 6 | POST-5 (nonzero eigenvalue) is NOT necessary for Miyake finite-exception SMO | Q5 | direct correction |
| 7 | 4-track parallel critical path (Adjoint+spectral / Main Lemma / SMO / L-fn) | Q5 follow-up | structural advice |
| 8 | First theorem boundary: `isFundamentalDomain_iUnion_smul_of_finiteIndex` | Q3 follow-up | concrete Lean target |
| 9 | Second theorem boundary: `petN_doubleCoset_adjoint` | Q3 follow-up | concrete Lean target |
| 10 | T207 should use Mathlib commuting-family eigenspace API | Q6 | direct answer |
| 11 | Park POST-1, reverse support, full Atkin-Lehner, L-function nonvanishing-as-blocker | various | direct prioritization |
| 12 | Risk 2: scalar normalization — adjugate ≠ inverse without scalar tracking | defensive | concern raised |
| 13 | Risk 3: diag(1,p) does NOT normalize Γ₁(N); use intersection K = Γ ∩ α⁻¹Γα | defensive | concern raised |
| 14 | Risk 5: don't overgeneralize FD-transport; prove narrow first | defensive | concern raised |
| 15 | Risk 6: distinguish "consumer wrapper compiles" from "foundational proved" | meta | concern raised |
| 16 | Risk 7: SMO across levels needs common primitive character framing | defensive | concern raised |
| 17 | Q4 (Phase 8 sub-tickets) answered: use existing sieve/support, don't restructure | Q4 | direct answer |
| 18 | Q7 (Generality) | Q7 | UNANSWERED — deflected via Risk 5 |

## Changes applied to tickets.md

- **Added** "Reviewer feedback integrated 2026-05-11" summary section after totals
- **Refocused** T205-d block: replaced 100+ lines of per-tile bijection scaffold
  with a three-ticket structure (T205-d-API-1, T205-d-API-2, T205-d as
  specialization)
- **Added** T205-d-API-1 ticket (`isFundamentalDomain_iUnion_smul_of_finiteIndex`)
  with Risk-5 narrowness caveat
- **Added** T205-d-API-2 ticket (`petN_doubleCoset_adjoint`) with Risk-2 and
  Risk-3 defensive notes
- **Refocused** POST-4 (mainLemma): line 2563 sorry, dependencies updated to
  use existing Miyake machinery directly; T207 dependency removed; FALSE
  newform coefficient assertion explicitly removed with critical warning
- **Demoted** POST-5 to "parallel analytic track" (not on critical path)
- **Demoted** POST-3 to "parallel analytic track" (was already partly so)
- **Updated** POST-7 dependencies: now depends on POST-4 + POST-6 only;
  no longer depends on POST-5 or POST-3
- **Added** `final-SMO-character-framing` ticket (per Risk 7)
- **Replaced** dependency graph with corrected 4-track structure
- **Added** "Status accounting" section flagging conditional-vs-foundational
  ticket status (per Risk 6)

## Changes rejected by user

- POST-1 NOT demoted to "architectural cleanup post-SMO" (user wants to keep
  it as a project goal, just off the critical path)
- Reverse support-decomposition NOT demoted to "architectural cleanup post-SMO"
- Full Atkin-Lehner involution NOT demoted to "architectural cleanup post-SMO"

These three remain as project goals; their off-critical-path status is
implicit (they don't appear in the corrected critical path).

## Open questions remaining

- Q7 (generality for GL_n / Hilbert / Maass) — reviewer deflected via
  Risk 5 (prove the narrow theorem first). Consider re-asking in a future
  round once the GL₂ project is closer to completion.

## Decisions recorded but not actioned in tickets.md

- The Γ₀(N)-pivot is correct (Q1 yes).
- The bifurcation (abstract for χ=1, explicit for general χ) is mathematically
  correct, not just a Lean nuisance (Q2 affirmed; POST-1 retained as goal).
- The Mathlib commuting-family eigenspace API is the right choice for T207
  (Q6); a from-scratch construction would be over-engineering.

## Acceptance criteria for the new tickets

**T205-d-API-1** should expose, as corollaries:
- AE-disjointness of the family `{r • D}_{r ∈ R}`
- NullMeasurableSet of `⋃ r • D`
- IntegrabilityOn transfer
- SetIntegral decomposition

**T205-d-API-2** must track the `(det α)^(k-1)` scalar normalization carefully
(Risk 2) and use the intersection `K = Γ ∩ α⁻¹Γα`, not Γ itself (Risk 3).

**POST-4 (`mainLemma`) refocused** must NOT use the false assertion that
newforms have `a_n = 0` for `(n,N) > 1`. Acceptance criterion is direct
proof from the Miyake sieve/conductor/support chain.
