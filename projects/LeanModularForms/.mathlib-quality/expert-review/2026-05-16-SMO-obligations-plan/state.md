# Expert-review session state

- Generated: 2026-05-16T16:13:39Z
- Audience: Frontier LLM reviewer (DS conventions; same as 2026-05-11 series)
- Goal of brief: Both soundness + strategy on the Route B SMO plan with three level-3 obligations
- Scope: SMO closure plan; covers the strategic pivot from Route A (Petersson adjoint) to Route B (Miyake/Atkin–Lehner induction)
- Reply received: true (2026-05-16)
- Reply integrated: true (2026-05-16)

## Brief metadata

- File: `REVIEW_BRIEF.md` (project root) and `brief.md` (this folder)
- Length: ~10 pages / ~5000 words
- Convention: Diamond–Shurman throughout
- Plan file under review: `LeanModularForms/SMOObligations.lean`
- Build state: compiles cleanly; exactly three `sorry`s; higher-level theorems verify with `{propext, sorryAx, Classical.choice, Quot.sound}` only

## Questions in the brief

| # | Question (verbatim from §10) |
|---|------------------------------|
| Q1 | Soundness of the per-character-only route to `newform_unique`: is applying the per-χ Main Lemma to `h = f - g ∈ S_k(Γ₁(N), χ)` a genuinely complete argument for `h ∈ S_k^old`? Are there hidden hypotheses we need separately for `h = f - g` versus a generic `h ∈ S_k(Γ₁(N), χ)`? |
| Q2 | Inheritance obstruction: for arbitrary `f ∈ S_k(Γ₁(N))` with coprime-to-N Fourier vanishing at ∞, the χ-pieces `π_χ f` do not generally inherit coprime-to-N vanishing because the diamond action moves the cusp. Is this obstruction real, or is there a classical argument that recovers inheritance? |
| Q3 | (A.L3) sieve construction: is the explicit alternating-sum formula for `f_d = Σ (-1)^... ∏ V_p ∘ U_p (f)` correct? Is the character invariance of `U_p`, `V_p` at primes `p ∣ N` (DS Prop 5.2.4(a) covers `p ∤ N`) valid? |
| Q4 | (B.L3.1) Hecke FE: is fitting a cusp form into Mathlib's `StrongFEPair` the right path? Edge cases (k odd, parity-of-character interactions with Fricke law)? |
| Q5 | (B.L3.2) trivial zero strategy: clean systematic choice of trivial-zero index m that avoids parity/numerator collisions? Or case split needed? |
| Q6 | Numerator non-cancellation in T111: elegant way to phrase the "deep enough" dependence on \|T\|, or explicit case split? |
| Q7 | Parity / order assumptions on χ: when bad-prime hypothesis is non-vacuous, is non-triviality of `χ̃` automatic? |
| Q8 | Strategic priority: which of (A.L3), (B.L3.1), (B.L3.2) to tackle first? Cost distribution estimates 200 / 200-400 / 300-600 LOC accurate? Shared sub-lemmas to factor out? |

## Stuck points (from §9)

- 9.1 Per-character Main Lemma's q-support claim — Möbius alternating-sum construction not yet formalised; estimate ~200 lines.
- 9.2 Hecke functional equation (B.L3.1) — Mellin + Fricke + integral split argument; estimate 200–400 lines.
- 9.3 Existence and selection of a trivial zero (B.L3.2) — trivial zero from Γ-factor + non-cancellation; estimate 300–600 lines.
- 9.4 Route soundness (the §5.2 strategic insight) — we want confirmation that per-character is truly enough.
- 9.5 Loose ends from the previous brief series — Route A (Petersson adjoint) remains 2 sorries, but is now off the SMO critical path.

## Strategic pivot from prior briefs

- Previous briefs (2026-05-11 SMO overview, 2026-05-11 T205-d focused, 2026-05-11 T205-d residual): focused on the Petersson adjoint chain (DS Thm 5.5.3 / Miyake Thm 4.5.4) as the genuine analytic content for Route A.
- This brief: pivots to Route B (Miyake/Atkin–Lehner induction via the per-character `SameLevelDivisorProjections` chain), bypassing the Petersson adjoint.
- Key strategic insight: `newform_unique` only needs the per-character Main Lemma, since both newforms in its hypothesis lie in the same Nebentypus character space.
- Consequence: T205-d-SYMM (the σ_p Q-permutation aggregate identity, last brief's target) is **off the SMO critical path** under Route B. It remains useful for downstream spectral applications.

## Plan file structure (for cross-reference)

| Lemma name | Role | Status |
|---|---|---|
| `coprimeSieve_admits_divisor_decomposition_in_charSpace` | (A.L3) per-χ Möbius sieve | sorry (level 3) |
| `newform_heckeEntireExtension` | (B.L3.1) Hecke 1936 FE | sorry (level 3) |
| `newform_noEntireExtensionUnderBadPrime` | (B.L3.2) Dirichlet trivial-zero contradiction | sorry (level 3) |
| `mainLemma_charSpace_routeB` | per-χ Main Lemma | proven from (A.L3) |
| `newform_analyticContradiction_routeB` | combined analytic obligation | proven from (B.L3.1)+(B.L3.2) |
| `existsNonzero_prime_eigenvalue_routeB` | good prime with non-zero eigenvalue | proven from analyticContradiction |
| `newform_unique_routeB` | Atkin–Lehner uniqueness | proven from per-χ Main Lemma + same-χ argument |
| `strongMultiplicityOne_axiom_clean` | SMO (top-level) | proven from newform_unique + existsNonzero |

## Reference list (full citations in §3)

- [DS] Diamond–Shurman, *A First Course in Modular Forms*, Springer GTM 228, 2005.
- [Miy] Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006.
- [Sh] Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton, 1971.
- [AL] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. **185** (1970), 134–160.
- [Li] W.-C. W. Li, "Newforms and functional equations", Math. Ann. **212** (1975), 285–315.
- [He] E. Hecke, "Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung", Math. Ann. **112** (1936), 664–699.
- [Da] H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer GTM 74, 2000.
- [Iwa] H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS GSM 17, 1997.

## Prior briefs in the series (for the reviewer's mental model)

- `.mathlib-quality/expert-review/2026-05-11/` — SMO overview.
- `.mathlib-quality/expert-review/2026-05-11-T205d/` — T205-d focused.
- `.mathlib-quality/expert-review/2026-05-11-T205d-residual/` — T205-d restructured residual (most recent prior to this).
