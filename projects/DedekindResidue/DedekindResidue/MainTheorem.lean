module

public import DedekindResidue.Theorem1

/-!
# Theorem 1 (Belabas–Friedman) — the main effective bound

The statement of the paper's main result: under GRH, `log κ_K` is approximated by the
computable quantity `f_K(X)` with an explicit error `O(log Δ_K / (√X log X))`, where
`κ_K = Res_{s=1} ζ_K(s)` is mathlib's `NumberField.dedekindZeta_residue K`.

`bSum` / `fK` (Belabas–Friedman's `B_K(X)` / `f_K(X)`, p. 2) live in
`DedekindResidue.Theorem1` together with the endgame bridges. The proof of
`belabas_friedman_thm1` is the whole SP1→SP2→SP3→Tier 3 development.
-/

namespace DedekindResidue

@[expose] public section

open NumberField

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
