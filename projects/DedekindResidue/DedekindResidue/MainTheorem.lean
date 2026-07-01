module

public import DedekindResidue.CompletedZeta.GRH
public import DedekindResidue.AuxiliaryFunction

/-!
# Theorem 1 (Belabas–Friedman) — the main effective bound

The statement of the paper's main result: under GRH, `log κ_K` is approximated by the
computable quantity `f_K(X)` with an explicit error `O(log Δ_K / (√X log X))`, where
`κ_K = Res_{s=1} ζ_K(s)` is mathlib's `NumberField.dedekindZeta_residue K`.

`bSum` / `fK` are Belabas–Friedman's `B_K(X)` / `f_K(X)` (p. 2). `fK` is defined in terms
of `bSum`; `bSum`'s prime-ideal-power sum is designed in its own ticket (stub for now).
The proof of `belabas_friedman_thm1` is the whole SP1→SP2→SP3→Tier 3 development.
-/

namespace DedekindResidue

@[expose] public section

open NumberField

/-- The single-field prime-power sum
`Σ_{𝔭^m, N𝔭^m < X} (log N𝔭 / N𝔭^{m/2})·(√X·log X / (N𝔭^{m/2}·log N𝔭^m) − 1)`
over nonzero prime ideals `𝔭 ⊆ 𝓞_K` and exponents `m ≥ 1` with `N𝔭^m < X`; written as a
`finsum` (the support is finite, so no separate finiteness proof is needed to define it).
Here `N𝔭 = Ideal.absNorm 𝔭` and `N𝔭^{m/2}` is the real power `Real.rpow`.

This is the `K`-part of Belabas–Friedman's `B_K(X)`; the paper's `B_K` itself is the
**relative** sum `∑^{K−ℚ}` — see `bSumRel`. -/
noncomputable def bSum (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  ∑ᶠ (p : {p : Ideal (RingOfIntegers K) // p.IsPrime ∧ p ≠ ⊥}) (m : ℕ),
    if 0 < m ∧ (Ideal.absNorm p.1 : ℝ) ^ m < X then
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2)) *
        (Real.sqrt X * Real.log X /
            ((Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2) *
              Real.log ((Ideal.absNorm p.1 : ℝ) ^ m)) - 1)
    else 0

/-- **`B_K(X)`** of Belabas–Friedman (p. 2, verbatim):
`B_K(X) := ∑^{K−ℚ}_{𝔭,m : N𝔭^m < X} (log N𝔭/N𝔭^{m/2})·(√X·log X/(N𝔭^{m/2}·log N𝔭^m) − 1)`,
where "the notation `∑^{K−k}` means that the sum for `k` is subtracted from the corresponding
sum for `K`" — so the rational-prime sum (`k = ℚ`, prime ideals of `ℤ` with `N(p) = p`) is
subtracted from the `K`-sum. -/
noncomputable def bSumRel (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  bSum K X - bSum ℚ X

/-- `f_K(X) = 3·(B_K(X) − B_K(X/9)) / (2·√X·log(3X))` — Belabas–Friedman, p. 2 (with `B_K`
the **relative** `∑^{K−ℚ}` sum `bSumRel`): the computable approximation to `log κ_K` bounded
in Theorem 1. -/
noncomputable def fK (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  3 * (bSumRel K X - bSumRel K (X / 9)) / (2 * Real.sqrt X * Real.log (3 * X))

/-- **Theorem 1** (Belabas–Friedman, arXiv:1305.0035, p. 2). Let `K` be a number field of
degree `n > 1`. Under GRH for `ζ_K` and RH for `ζ_ℚ`, for `X ≥ 69`,
`|log κ_K − f_K(X)| ≤ (2.324 log Δ_K / (√X log 3X)) · ((1 + 3.88/log(X/9))·(1 + 2/√(log Δ_K))²
+ 4.26(n−1)/(√X log Δ_K))`, where `κ_K = dedekindZeta_residue K` and `Δ_K = |disc K|`.
**Proof: the SP1→SP2→SP3→Tier 3 development.** -/
theorem belabas_friedman_thm1 {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) *
              (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                (Real.sqrt X * Real.log (|discr K| : ℝ))) := by
  sorry

end

end DedekindResidue
