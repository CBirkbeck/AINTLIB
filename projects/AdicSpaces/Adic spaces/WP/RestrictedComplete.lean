/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Vendored.CoramMvRestrictedNorm
import «Adic spaces».Vendored.CoramRestrictedIso
import «Adic spaces».ExampleUnitDisc

/-!
# Restricted power series over an arbitrary variable index: completeness and support API

The vendored Coram stack (`Vendored/CoramMvRestricted*.lean`) provides
`MvPowerSeries.Restricted R c` with its Gauss norm for an **arbitrary** index type `σ`,
but proves `CompleteSpace` only for `σ = Fin n` (`Vendored/CoramRestrictedIso.lean`,
`MvRestricted.isCompleteSpace`, by induction on `n`).  The weighted-parity example
([WP] §6.1, eq:parity-algebra) needs countably many variables, so this file supplies:

* `MvRestricted.isCompleteSpace_of_forall` — completeness for arbitrary `σ`, by the
  coefficientwise-Cauchy argument of the univariate proof
  (`Vendored/CoramRestrictedNorm.lean:257`), which is index-uniform;
* `NormOneClass` at radius one for arbitrary `σ` (generalizing
  `FJP/RestrictedGaussAdic.lean:44`);
* the radius-one coefficient API (`norm_coeff_le`, continuity of coefficient
  functionals, finiteness of superlevel sets — generalizing
  `FJP/RestrictedGaussAdic.lean:199,207`);
* the closed-support principle: a coefficient-vanishing condition cuts out a closed
  subset (the pattern behind `FJP/RestrictedLaurent.lean:765` and
  `FJP/Over/JetRings.lean:298`).
-/

@[expose] public section

namespace WeightedParity

open MvPowerSeries Filter

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*}

/-- Radius one is strongly positive, for every index type. -/
instance strongPos_one (σ : Type*) : StrongPos (fun _ : σ => (1 : ℝ)) :=
  strongPos_of_forall_pos _ fun _ => one_pos

/-- **Completeness of restricted power series for an arbitrary variable index.**
Generalizes `Restricted.isCompleteSpace` (univariate,
`Vendored/CoramRestrictedNorm.lean:257`) and `MvRestricted.isCompleteSpace`
(`Fin (n+1)`, `Vendored/CoramRestrictedIso.lean:349`): the coefficientwise-Cauchy
argument never uses the index type.  ([WP] §6.1: "Its completion is 𝒜 = {…}",
eq:parity-algebra — the ambient ring must be complete.) -/
instance isCompleteSpace_general (c : σ → ℝ) [StrongPos c] [CompleteSpace R] :
    CompleteSpace (MvPowerSeries.Restricted R c) := by sorry

/-- `NormOneClass` at radius one, arbitrary index (generalizes the `Fin k` instance of
`FJP/RestrictedGaussAdic.lean:44`; the proof via `t.prod (1 ^ ·) = 1` is
index-uniform). -/
noncomputable instance normOneClass_one {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] [NormOneClass S] {σ' : Type*} :
    NormOneClass (MvPowerSeries.Restricted S (fun _ : σ' => (1 : ℝ))) := by sorry

section RadiusOne

variable (f : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ))) (t : σ →₀ ℕ)

/-- Coefficient bound at radius one (generalizes
`FiniteJet.GraphKoszul.norm_coeff_le_gauss`, `FJP/RestrictedGaussAdic.lean:199`). -/
theorem norm_coeff_le_one_norm : ‖MvPowerSeries.coeff t f.1‖ ≤ ‖f‖ := by sorry

/-- The coefficient functionals are `1`-Lipschitz, hence continuous (the pattern of
`FiniteJetOver.continuous_qCoeff`, `FJP/Over/JetRings.lean:112`). -/
theorem lipschitzWith_coeff :
    LipschitzWith 1 (fun g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) =>
      MvPowerSeries.coeff t g.1) := by sorry

theorem continuous_coeff :
    Continuous (fun g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) =>
      MvPowerSeries.coeff t g.1) := by sorry

/-- Superlevel sets of a restricted series are finite (generalizes
`FiniteJet.GraphKoszul.finite_setOf_le_norm_coeff`, `FJP/RestrictedGaussAdic.lean:207`).
This is the "every nonzero restricted series attains its norm" input of
[WP] prop:parity-uniform-domain. -/
theorem finite_setOf_le_norm_coeff {ε : ℝ} (hε : 0 < ε) :
    {s : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff s f.1‖}.Finite := by sorry

/-- **The closed-support principle**: the set of restricted series whose coefficients
vanish outside a prescribed set of exponents is closed (each condition is the kernel of
a continuous coefficient functional; the pattern of
`FiniteJet.RestrictedLaurent.isClosed_nonnegSubring`,
`FJP/RestrictedLaurent.lean:765`). -/
theorem isClosed_setOf_coeff_eq_zero (S : Set (σ →₀ ℕ)) :
    IsClosed {g : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) |
      ∀ s ∉ S, MvPowerSeries.coeff s g.1 = 0} := by sorry

end RadiusOne

/-- Gauss-norm multiplicativity of the radius-one restricted ring over a normed field
with multiplicative norm, for a linearly ordered index ([WP] prop:parity-uniform-domain:
"The Gauss norm on the countable restricted Tate algebra `k⟨W,U_1,U_2,…⟩` is
multiplicative").  Wrapper around the vendored `MvRestricted.isAbsoluteValue`
(`Vendored/CoramMvRestrictedNorm.lean:270`). -/
theorem norm_restricted_mul_general [LinearOrder σ] {S : Type*} [NormedCommRing S]
    [IsUltrametricDist S] (hnorm : ∀ a b : S, ‖a * b‖ = ‖a‖ * ‖b‖)
    (f g : MvPowerSeries.Restricted S (fun _ : σ => (1 : ℝ))) :
    ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

end WeightedParity
