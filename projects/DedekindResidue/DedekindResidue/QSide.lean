/-
DedekindResidue: the ℚ-side facts for the relative (K/ℚ) Lemma 4.

Belabas–Friedman's Lemma 4 is applied at `k = ℚ`, so the σ-display must be
instantiated at the rationals: `ζ_ℚ` is the Riemann zeta on `Re s > 1` (there is one
ideal of `ℤ` per positive norm), the completed Riemann zeta is a completed Dedekind
zeta for `ℚ` (so mathlib's `RiemannHypothesis` transfers to our
`GeneralizedRiemannHypothesis ℚ`), and `κ_ℚ = 1`.
-/
module

public import Mathlib
public import DedekindResidue.CompletedZeta.GRH

@[expose] public section

namespace DedekindResidue

open NumberField

/-- `ℤ⧸(n)` has `n` elements, so the principal ideal `(n)` has absolute norm `n`. -/
theorem absNorm_span_natCast (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : ℤ)}) = n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (Int.quotientSpanEquivZMod n).toEquiv]
  exact Nat.card_zmod n

/-- **There is exactly one ideal of `ℤ` of each positive norm.** -/
theorem card_int_ideal_absNorm_eq (n : ℕ) :
    Nat.card {J : Ideal ℤ // Ideal.absNorm J = n} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · -- uniqueness: `ℤ` is a PID and the generator is pinned up to sign by the norm
    refine ⟨fun ⟨J₁, hJ₁⟩ ⟨J₂, hJ₂⟩ => ?_⟩
    obtain ⟨g₁, rfl⟩ := (IsPrincipalIdealRing.principal J₁).principal
    obtain ⟨g₂, rfl⟩ := (IsPrincipalIdealRing.principal J₂).principal
    have e₁ : (Submodule.span ℤ {g₁} : Ideal ℤ) = Ideal.span {g₁} := rfl
    have e₂ : (Submodule.span ℤ {g₂} : Ideal ℤ) = Ideal.span {g₂} := rfl
    have h₁ : Ideal.span ({g₁} : Set ℤ) = Ideal.span {(g₁.natAbs : ℤ)} :=
      (Int.span_natAbs g₁).symm
    have h₂ : Ideal.span ({g₂} : Set ℤ) = Ideal.span {(g₂.natAbs : ℤ)} :=
      (Int.span_natAbs g₂).symm
    have hn₁ : g₁.natAbs = n := by
      rw [e₁, h₁, absNorm_span_natCast] at hJ₁
      exact hJ₁
    have hn₂ : g₂.natAbs = n := by
      rw [e₂, h₂, absNorm_span_natCast] at hJ₂
      exact hJ₂
    refine Subtype.ext ?_
    show (Submodule.span ℤ {g₁} : Ideal ℤ) = Submodule.span ℤ {g₂}
    rw [e₁, e₂, h₁, h₂, hn₁, hn₂]
  · exact ⟨⟨Ideal.span {(n : ℤ)}, absNorm_span_natCast n⟩⟩

end DedekindResidue

end
