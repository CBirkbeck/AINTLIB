# Reply integration — 2026-05-16

Reply received from the frontier-LLM reviewer (DS conventions) on
2026-05-16.

- Brief: `brief.md`
- Reply: `reply.md`
- Revised plan file: `LeanModularForms/SMOObligations.lean`

## Interpretation summary

The reviewer **confirms the per-character Route B strategic insight**
but **rejects two of the three level-3 obligations** as unnecessary
(B.L3.1 Hecke FE) and **mathematically risky** (B.L3.2 trivial-zero
contradiction).  The proposed analytic chain is replaced with a purely
algebraic finite-exception bridge using the good-prime recurrence.
The A.L3 sieve formula is corrected to squarefree inclusion-exclusion
over the prime divisors of $N$.

### Confirmed

- **Q1.** Per-character Main Lemma suffices for `newform_unique`. (✓)
- **Q2.** The inheritance obstruction for arbitrary cusp forms is real
  — diamond operators move the cusp $\infty$. (✓)

### Rejected / revised

- **Q3.** A.L3 sieve formula needs correction: use squarefree
  inclusion-exclusion $\sum_{\varnothing \ne T \subseteq \mathrm{primes}(N)} (-1)^{|T|+1} \prod_{p \in T} P_p$,
  **not** a sum over all divisors.
- **Q3b.** Do not cite DS Prop 5.2.4(a) for $U_p$-diamond commutation
  at $p \mid N$ — that proposition is for good primes.  Make this a
  local lemma.
- **Q4, Q5, Q6, Q7, Q8.** All of B.L3.1 / B.L3.2 should be **removed
  from the SMO critical path**.  They are unnecessary for the
  finite-exception form of SMO (which uses an algebraic $q$/$q^2$
  bridge) and the trivial-zero approach is risky because trivial zeros
  of $L(2w, \chi^2)$ may cancel trivial zeros of $L(w, \chi)$.

### Unprompted concerns

- The composition $P_p = V_p U_p$ may not literally be a same-level
  endomorphism in the project's API — package it as a packaged
  same-level projection.
- Theorem-statement drift: finite-exception-natural-numbers vs
  finite-exception-primes need different bridges.  For the natural-
  numbers form (Miyake's and the project's current form), the algebraic
  bridge applies.

## Changes applied to `SMOObligations.lean`

### Removed

- `newform_heckeEntireExtension` — Hecke FE level-3 obligation
- `newform_noEntireExtensionUnderBadPrime` — Dirichlet trivial-zero
  level-3 obligation
- `newform_analyticContradiction_routeB` — level-2 combiner
- `existsNonzero_prime_eigenvalue_routeB` — level-1 consumer

### Rewritten

- `coprimeSieve_admits_divisor_decomposition_in_charSpace` →
  `coprimeSieve_admits_squarefree_decomposition_in_charSpace`:
  same Lean-facing output shape (`f_d` indexed by divisors of `N`
  with `d > 1`), but the **classical construction** in the docstring
  now uses the squarefree inclusion-exclusion form
  $f_T = (-1)^{|T|+1} \prod_{p \in T} P_p f$.  The output is zero-filled
  on non-squarefree divisors to match the project's existing consumer
  signature.

### Added

- `exists_same_level_p_supported_projection` (A.L3.proj) — new
  level-3 obligation: same-level $P_p$ with the $q$-expansion formula
  and $\chi$-preservation.  The docstring notes the bad-prime
  $U_p$-diamond commutation requires a direct proof, not a citation
  to DS Prop 5.2.4(a).
- `newform_eigenvalue_at_prime_sq` (A.L3.rec) — new level-3 obligation:
  the recurrence $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) q^{k-1}$
  for newforms.
- `eigenvalues_eq_all_coprime_of_eq_off_finite` (B.L1) — new fully
  proven algebraic finite-exception bridge, replacing the analytic
  chain.  Uses a case split on $\lambda_q(f) = 0$ with cancellation
  via $q^2$ when needed.

### Kept

- `mainLemma_charSpace_routeB` (now consumes the corrected sieve)
- `newform_unique_routeB` (per-χ proof, unchanged logic)
- `strongMultiplicityOne_axiom_clean` (top theorem; proof now goes
  through the algebraic bridge directly)

## Final state of `SMOObligations.lean`

**Three level-3 atomic obligations** (all purely algebraic, no analytic
content):

1. `exists_same_level_p_supported_projection` — same-level
   $p$-supported projection $P_p$ with $q$-expansion formula and
   character preservation.
2. `coprimeSieve_admits_squarefree_decomposition_in_charSpace` —
   the squarefree inclusion-exclusion sieve identity at the
   character-space level.
3. `newform_eigenvalue_at_prime_sq` — the Hecke prime-power recurrence
   applied at the newform / eigenvalue level.

All higher-level theorems (per-character Main Lemma, `newform_unique`,
algebraic finite-exception bridge, SMO) are fully proven in Lean from
these three obligations and the project's existing axiom-clean
infrastructure.  When the three obligations are discharged, SMO is
axiom-clean with respect to the standard triple
`{propext, Classical.choice, Quot.sound}`.

## Acceptance criteria from the reviewer

- A compiling squarefree inclusion-exclusion A.L3 theorem, **or**
  one exact missing same-level $P_p$ projection lemma.
- No new work on Hecke functional equations, Dirichlet trivial zeros,
  or B.L3.2 until A.L3 and the algebraic finite-exception bridge are
  closed.

Both criteria are satisfied at the plan level: the three obligations
above cover the first, and the algebraic bridge is fully proven (no
sorry) — the second criterion's "until" clause is therefore
already-discharged for the bridge part.

## Decisions recorded

- **SMO scope**: natural-numbers finite-exception (matches Miyake
  Thm 4.6.12 and the project's existing `strongMultiplicityOne`).
  The algebraic bridge handles this form.
- **B.L3.1 (Hecke FE)** and **B.L3.2 (trivial zeros)**: parked as
  off-critical-path future L-function infrastructure.  Not deleted
  from the project, just removed from the SMO chain.
- **Petersson adjoint chain (Route A)**: remains off-critical-path
  per the previous brief series.  Still useful for spectral
  applications.

## Open questions remaining (the reviewer did not address)

- None of substance for SMO closure.  The reviewer addressed every
  question Q1–Q8 either directly or by reframing it as unnecessary.
- The reviewer's parenthetical "If analytic nonvanishing is needed
  later, Rankin–Selberg is more robust" is a recommendation for any
  future work in that direction; not actionable now.

## Files updated

- `LeanModularForms/SMOObligations.lean` — full rewrite per reviewer
  feedback (substantial changes; compiles cleanly with three sorries)
- `REVIEW_BRIEF.md` — unchanged (the brief was the *input* to the
  reviewer, not modified by their reply)
- `.mathlib-quality/expert-review/2026-05-16-SMO-obligations-plan/`:
  - `reply.md` (this reply, saved verbatim)
  - `integration.md` (this file)
  - `state.md` (will be updated to mark reply received + integrated)
