module

public import BernoulliRegular.Reflection.Local.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseCompletionMap
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

/-!
# Valuation-completion trace source for the Kummer--Artin--Hasse `A` term

The earlier local logarithm files are written in the project's adic completed
integer ring `LambdaLocalIntegerRing`.  The trace needed for the explicit
Kummer--Artin--Hasse correction, however, is the finite `Q_p`-linear trace on
the valuation completion of `K` at `lambda`.

This file makes the trace-source API use the valuation-completion model from
the start.  The old adic logarithm stack remains useful infrastructure, but it
is not the final source of the `A` term consumed by reciprocity.

The `< p` truncated logarithm is kept as a named summand.  The active finite
approximation to the full p-adic logarithm for the Kummer--Artin--Hasse
`A`-term is `log_≤p(u) = log_<p(u) + (u - 1)^p / p`; the missing `n = p`
term is essential on the `μ_p` torsion direction in `U_1`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The unit group of the valuation-completion integer ring at `lambda`. -/
abbrev LambdaValuedUnitGroup : Type _ :=
  (LambdaValuedIntegerRing p K)ˣ

/-- The maximal ideal of the valuation-completion integer ring. -/
abbrev LambdaValuedMaximalIdeal : Ideal (LambdaValuedIntegerRing p K) :=
  IsLocalRing.maximalIdeal (LambdaValuedIntegerRing p K)

/-- The valuation-completion principal-unit filtration `1 + m^n`. -/
abbrev LambdaValuedPrincipalUnitSubgroup (n : ℕ) :
    Subgroup (LambdaValuedUnitGroup p K) :=
  Ideal.oneUnitsSubgroup ((LambdaValuedMaximalIdeal p K) ^ n)

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
integer ring. -/
def lambdaValuedPiInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1)

/-- The cyclotomic uniformizer `pi = zeta_p - 1` in the valuation-completion
field. -/
def lambdaValuedPi : LambdaValuedCompletion p K :=
  (lambdaValuedPiInteger p K : LambdaValuedCompletion p K)

/-- The distinguished `p`-th root of unity in the valuation-completion integer
ring. -/
def lambdaValuedZetaInteger : LambdaValuedIntegerRing p K :=
  algebraMap (𝓞 K) (LambdaValuedIntegerRing p K)
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/-- The distinguished `p`-th root of unity in the valuation-completion field. -/
def lambdaValuedZeta : LambdaValuedCompletion p K :=
  (lambdaValuedZetaInteger p K : LambdaValuedCompletion p K)

/-- The local coordinate `u - 1`, coerced into the valuation-completion field. -/
def lambdaValuedPrincipalUnitCoordinate
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  (((u : LambdaValuedUnitGroup p K) : LambdaValuedIntegerRing p K) :
      LambdaValuedCompletion p K) - 1

omit [Fact p.Prime] in
theorem valuedLogRange_pos {n : ℕ} (hn : n ∈ Finset.Icc 1 (p - 1)) :
    0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1

omit [Fact p.Prime] in
theorem valuedLogRange_lt_p {n : ℕ} (hn : n ∈ Finset.Icc 1 (p - 1)) :
    n < p := by
  have hnpred : n ≤ p - 1 := (Finset.mem_Icc.mp hn).2
  have hn_pos : 0 < n := valuedLogRange_pos (p := p) hn
  have hp_pos : 0 < p := by omega
  exact Nat.lt_of_le_pred hp_pos hnpred

/-- A single signed term `(-1)^(n+1) (u - 1)^n / n` of the valuation-model
truncated logarithm, computed in the valuation-completion field. -/
def lambdaValuedTruncatedLogTerm
    (u : LambdaValuedPrincipalUnitSubgroup p K 1)
    {n : ℕ} (_hn_pos : 0 < n) (_hn_lt : n < p) :
    LambdaValuedCompletion p K :=
  ((-1 : LambdaValuedCompletion p K) ^ (n + 1)) *
    ((n : LambdaValuedCompletion p K)⁻¹) *
    (lambdaValuedPrincipalUnitCoordinate p K u) ^ n

/-- The valuation-model truncated logarithm
`log_<p(u) = sum_{1 <= n < p} (-1)^(n+1) (u - 1)^n / n`. -/
def lambdaValuedTruncatedLog
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  ∑ n : {n // n ∈ Finset.Icc 1 (p - 1)},
    lambdaValuedTruncatedLogTerm (p := p) (K := K) u
      (valuedLogRange_pos (p := p) n.property)
      (valuedLogRange_lt_p (p := p) n.property)

/-- The valuation-model field expression `pi^{-1} log_<p(u)`. -/
def lambdaValuedPiInvTruncatedLog
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  (lambdaValuedPi p K)⁻¹ * lambdaValuedTruncatedLog p K u

/-- The missing `n = p` term `(u - 1)^p / p` in the finite logarithm needed
for the Kummer--Artin--Hasse `A` term. -/
def lambdaValuedLogLePTail
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  ((p : LambdaValuedCompletion p K)⁻¹) *
    (lambdaValuedPrincipalUnitCoordinate p K u) ^ p

/-- The corrected finite approximation
`log_≤p(u) = log_<p(u) + (u - 1)^p / p`.

This is the finite expression used for the `A` term; `log_<p` alone is
insufficient on all of `U_1` because it does not kill the `μ_p` torsion
direction. -/
def lambdaValuedLogLeP
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  lambdaValuedTruncatedLog p K u + lambdaValuedLogLePTail p K u

/-- The corrected valuation-model field expression `pi^{-1} log_≤p(u)`. -/
def lambdaValuedPiInvLogLeP
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  (lambdaValuedPi p K)⁻¹ * lambdaValuedLogLeP p K u

/-- The legacy valuation-completion argument of the finite `Q_p` trace using
only `zeta_p * pi^{-1} log_<p(u)`.

This is not the active `A`-term argument after the `log_≤p` correction; use
`lambdaValuedCorrectedATraceArgument` for the active route. -/
def lambdaValuedATraceArgument
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  lambdaValuedZeta p K * lambdaValuedPiInvTruncatedLog p K u

/-- The corrected valuation-completion argument of the finite `Q_p` trace in
the Kummer--Artin--Hasse `A` term:
`zeta_p * pi^{-1} log_≤p(u)`. -/
def lambdaValuedCorrectedATraceArgument
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    LambdaValuedCompletion p K :=
  lambdaValuedZeta p K * lambdaValuedPiInvLogLeP p K u

/-- The concrete finite `Q_p`-linear trace map on the valuation completion.

The `Q_p`-algebra structure is deliberately opted into locally via
`lambdaValuedCompletionAlgebraPadic`; there is no global typeclass instance
that could hide a different base field. -/
def lambdaValuedTraceMap :
    letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
      lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
    LambdaValuedCompletion p K →ₗ[ℚ_[lambdaPadicPrime p]] ℚ_[lambdaPadicPrime p] := by
  letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
  letI : Module.Finite ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletion_moduleFinitePadic (p := p) (K := K)
  exact Algebra.trace ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K)

/-- The legacy `< p` trace term.  This is kept for compatibility with earlier
infrastructure, but it is not the active Kummer--Artin--Hasse `A` trace on all
of `U_1`; use `lambdaValuedCorrectedATrace` instead. -/
def lambdaValuedATrace
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    ℚ_[lambdaPadicPrime p] :=
  letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
  letI : Module.Finite ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletion_moduleFinitePadic (p := p) (K := K)
  Algebra.trace ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K)
    (lambdaValuedATraceArgument p K u)

/-- The corrected finite trace term from which the Kummer--Artin--Hasse
function `A : U_1 -> ZMod p` will be obtained after the `p`-divisibility
theorem. -/
def lambdaValuedCorrectedATrace
    (u : LambdaValuedPrincipalUnitSubgroup p K 1) :
    ℚ_[lambdaPadicPrime p] :=
  letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
  letI : Module.Finite ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletion_moduleFinitePadic (p := p) (K := K)
  Algebra.trace ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K)
    (lambdaValuedCorrectedATraceArgument p K u)

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
