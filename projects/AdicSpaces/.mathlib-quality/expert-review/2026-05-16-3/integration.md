# Reply integration — round 22, 2026-05-16

Reply received from ChatGPT Pro on 2026-05-16. Brief: `brief.md`. Reply: `reply.md`.

## Interpretation summary

Reviewer recommends path **(a) but in pieces**: build a local no-`hArch` compactness lemma in the shape `IsCompact {v ∈ rationalOpen L.T L.s | v.vle g h}`. The eventual proof routes through Wedhorn `Spv(A,I)` infrastructure (5-step plan: CofinalValue → Spv(A,I) → rational basis → 7.10 continuity → Spa pro-constructible). For short-term unblock, the no-`hArch` half-space compactness lemma can be a private sorry — but **must state the no-`hArch` conclusion**, not propagate `hArch` even privately, because Lean privacy does not hide hypotheses.

Most actionable surprise: **Q3 has a concrete algebraic algorithm** for closing `Valuation.isContinuous_of_ideal_pow_lt` without `MulArchimedean`:

- Take FG generators x_1,...,x_r of I (each a generator of L.P.I).
- For each x_i, Wedhorn 7.10 cofinality on `v(x_i)`: ∀ γ > 0, ∃ N_i, v(x_i)^{N_i} < γ.
- Take N = r * max_i N_i.
- Every degree-N monomial in {x_i} contains some x_i with exponent ≥ N_i; other generators have value ≤ 1 (since I ⊆ A₀ ⊆ A⁺); hence monomial value < γ.
- General I^N element is A₀-linear combination of monomials; A₀ ⊆ A⁺ gives coefficient value ≤ 1; nonarch inequality gives < γ.

This is potentially a direct route to closing the cofinality discharge in `isContinuous_of_ideal_pow_lt` without going through `exists_pow_lt_zero`.

## Action plan

1. **Refactor `SpaCompactNoHArch.lean`**: replace the abstract `isCompact_preimage_rationalOpen_no_hArch` with the half-space-specific `isCompact_rationalOpen_inter_vle_noHArch (L : RationalLocData A) (g h : A) : IsCompact {v ∈ rationalOpen L.T L.s | v.vle g h}` per reviewer's exact prescription.
2. **Use the no-hArch lemma inside the domination lemma** to attempt closing the substantive content of P3 (sub-lemma with sorry is fine per the BINDING RULE).
3. **Investigate Q3 algorithm**: attempt to discharge `Valuation.isContinuous_of_ideal_pow_lt` for our Tate setting using FG generators + monomial-degree argument + A₀ ⊆ A⁺, **without** `MulArchimedean`. If successful, this closes the whole no-hArch compactness in one stroke.
4. **Sub-ticket** `T-SPV-AI-WEDHORN-710`: spawn the Spv(A,I) track as a planning artifact (NOT yet a new file with sorry — per the user's BINDING RULE clarification, planning sub-tickets are fine, but new Lean files only if there's a sub-lemma to state).

## Changes applied this round

- Reply saved at `.mathlib-quality/expert-review/2026-05-16-3/reply.md`.
- State updated: Reply received: true, Reply integrated: true.
- **Refactored** `Adic spaces/SpaCompactNoHArch.lean` to the reviewer's
  half-space-specific shape `isCompact_rationalOpen_inter_vle_noHArch`.
- **Proved** `exists_pow_lt_of_topNilp_of_ne_zero` — per-`v` cofinality bridge
  (no `MulArchimedean`, no sorry). For `v ∈ Spa`, `π` topologically nilpotent,
  `v(a) ≠ 0`, there exists `N` with `v(π^N) < v(a)`. Proof technique adapted
  from `not_vle_one_of_mem_spa_of_topologicallyNilpotent`.
- **Proved** `exists_uniform_pow_vle_on_compact` — uniform `N` over a compact
  subset of `↥(Spa A A⁺)` via open-cover argument
  (`IsCompact.elim_directed_cover`) using the per-`v` cofinality. **No sorry**;
  this is the substantive open-cover technique the reviewer described
  (modulo the still-`sorry` compactness of the half-space itself).
- **Build clean**: 3128 jobs, +1 sorry (the half-space compactness, which
  is the genuine `Spv(A, I)`-infrastructure gap per Q1).

## Open questions still on the table (deferred)

- Round-20 Q3-Q9 (P5/P6/P7/P8 substantive Wedhorn content + T001 + V.1 + meta) — still unanswered.

## Next code action

Refactor `SpaCompactNoHArch.lean` to the half-space-specific shape, attempt Q3 algorithm in `ValuationContinuity.lean`.
