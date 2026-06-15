module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseLogDenominators
import Mathlib.Tactic

/-!
# Truncated local logarithm for the Kummer--Artin--Hasse correction

For a completed principal unit `u ∈ U_1`, this file defines the concrete
finite logarithm

```text
log_<p(u) = sum_{1 ≤ n < p} (-1)^(n+1) (u - 1)^n / n
```

inside the completed local integer ring.  Division by `n` is implemented using
the denominator units proved in `KummerArtinHasseLogDenominators`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The local coordinate `u - 1` of a completed principal unit. -/
def lambdaPrincipalUnitCoordinate (u : LambdaPrincipalUnitSubgroup p K 1) :
    LambdaLocalIntegerRing p K :=
  ((u : LambdaUnitGroup p K) : LambdaLocalIntegerRing p K) - 1

theorem lambdaPrincipalUnitCoordinate_mem_maximalIdeal
    (u : LambdaPrincipalUnitSubgroup p K 1) :
    lambdaPrincipalUnitCoordinate p K u ∈ LambdaMaximalIdeal p K := by
  have hu : (u : LambdaUnitGroup p K) ∈ LambdaPrincipalUnitSubgroup p K 1 := u.property
  rw [Reflection.Local.mem_completedPrincipalUnitSubgroup_iff] at hu
  simpa [lambdaPrincipalUnitCoordinate, LambdaMaximalIdeal] using hu

/-- A single signed term `(-1)^(n+1) (u - 1)^n / n` of the truncated logarithm. -/
def lambdaTruncatedLogTerm (u : LambdaPrincipalUnitSubgroup p K 1)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < p) :
    LambdaLocalIntegerRing p K :=
  ((-1 : LambdaLocalIntegerRing p K) ^ (n + 1)) *
    (((lambdaNatDenominatorUnit (p := p) (K := K) hn_pos hn_lt)⁻¹ :
      (LambdaLocalIntegerRing p K)ˣ) : LambdaLocalIntegerRing p K) *
    (lambdaPrincipalUnitCoordinate p K u) ^ n

theorem lambdaTruncatedLogTerm_mem_maximalIdeal
    (u : LambdaPrincipalUnitSubgroup p K 1)
    {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < p) :
    lambdaTruncatedLogTerm p K u hn_pos hn_lt ∈ LambdaMaximalIdeal p K := by
  let M := LambdaMaximalIdeal p K
  let x := lambdaPrincipalUnitCoordinate p K u
  have hx : x ∈ M := lambdaPrincipalUnitCoordinate_mem_maximalIdeal (p := p) (K := K) u
  have hxpow : x ^ n ∈ M := M.pow_mem_of_mem hx n hn_pos
  simpa [lambdaTruncatedLogTerm, x, M, mul_assoc] using
    M.mul_mem_left
      (((-1 : LambdaLocalIntegerRing p K) ^ (n + 1)) *
        (((lambdaNatDenominatorUnit (p := p) (K := K) hn_pos hn_lt)⁻¹ :
          (LambdaLocalIntegerRing p K)ˣ) : LambdaLocalIntegerRing p K))
      hxpow

omit [Fact p.Prime] in
theorem logRange_pos {n : ℕ} (hn : n ∈ Finset.Icc 1 (p - 1)) :
    0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1

omit [Fact p.Prime] in
theorem logRange_lt_p {n : ℕ} (hn : n ∈ Finset.Icc 1 (p - 1)) :
    n < p := by
  have hnpred : n ≤ p - 1 := (Finset.mem_Icc.mp hn).2
  have hn_pos : 0 < n := logRange_pos (p := p) hn
  have hp_pos : 0 < p := by omega
  exact Nat.lt_of_le_pred hp_pos hnpred

/-- The concrete truncated logarithm `log_<p(u)` on completed principal units. -/
def lambdaTruncatedLog (u : LambdaPrincipalUnitSubgroup p K 1) :
    LambdaLocalIntegerRing p K :=
  ∑ n : {n // n ∈ Finset.Icc 1 (p - 1)},
    lambdaTruncatedLogTerm (p := p) (K := K) u
      (logRange_pos (p := p) n.property) (logRange_lt_p (p := p) n.property)

/-- The truncated logarithm of a principal unit is divisible by `lambda`. -/
theorem lambdaTruncatedLog_mem_maximalIdeal
    (u : LambdaPrincipalUnitSubgroup p K 1) :
    lambdaTruncatedLog p K u ∈ LambdaMaximalIdeal p K := by
  rw [lambdaTruncatedLog]
  exact Ideal.sum_mem
    (LambdaMaximalIdeal p K)
    (fun n _ =>
      lambdaTruncatedLogTerm_mem_maximalIdeal (p := p) (K := K) u
        (n := n.1) (logRange_pos (p := p) n.property)
        (logRange_lt_p (p := p) n.property))

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
