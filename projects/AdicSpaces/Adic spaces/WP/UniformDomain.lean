/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Algebra
import «Adic spaces».Uniform

/-!
# `𝒜` is a uniform integral domain with `𝒜° = 𝒜₀` ([WP] prop:parity-uniform-domain)

The route is the `JetA` one (`FJP/Over/UniformDomain.lean`): the Gauss norm of the
ambient countable restricted Tate algebra is **multiplicative** (norms are attained;
reduce mod the top coefficient — packaged in the vendored `MvRestricted.isAbsoluteValue`
via `WP/RestrictedComplete.lean`), the support subring inherits multiplicativity
isometrically, and multiplicativity gives both the domain property and
`power-bounded = unit ball`, i.e. `𝒜° = 𝒜₀` and uniformity.

Source: [WP] prop:parity-uniform-domain (lines 789–811): "The Gauss norm on the
countable restricted Tate algebra `k⟨W,U_1,U_2,…⟩` is multiplicative. … The support
algebra `𝒜` embeds isometrically into this Tate algebra, so its Gauss norm is also
multiplicative and it is a domain.  If `x ∈ 𝒜₀`, all powers of `x` remain in `𝒜₀`.
If `x ∉ 𝒜₀`, multiplicativity gives `‖x^m‖ = ‖x‖^m`, which is unbounded.  Hence
`𝒜° = 𝒜₀`."
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver TopologicalRing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

/-- Gauss-norm multiplicativity on the ambient `K⟨W,U_1,U_2,…⟩`
([WP] prop:parity-uniform-domain, first paragraph). -/
theorem norm_amb_mul (f g : Amb K) : ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

/-- Gauss-norm multiplicativity on `𝒜` (isometric restriction of the ambient). -/
theorem norm_wpa_mul (a b : WPA K w) : ‖a * b‖ = ‖a‖ * ‖b‖ := by sorry

theorem norm_wpa_pow (a : WPA K w) (n : ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by sorry

instance : Nontrivial (WPA K w) := by sorry

/-- `𝒜` has no zero divisors (norm multiplicativity; the `instNoZeroDivisorsJetA`
pattern, `FJP/Over/UniformDomain.lean:92`). -/
instance : NoZeroDivisors (WPA K w) := by sorry

/-- `𝒜` is an integral domain ([WP] prop:parity-uniform-domain). -/
instance : IsDomain (WPA K w) :=
  NoZeroDivisors.to_isDomain _

variable {K w} in
/-- Power-boundedness in `𝒜` is exactly the unit ball ([WP]
prop:parity-uniform-domain: "`𝒜° = 𝒜₀`"; the `isPowerBounded_JetA_iff` pattern,
`FJP/Over/UniformDomain.lean:127`). -/
theorem isPowerBounded_wpa_iff (ϖ : Uniformizer K) (a : WPA K w) :
    IsPowerBounded a ↔ ‖a‖ ≤ 1 := by sorry

variable {K w} in
/-- The power-bounded subring of `𝒜` is its unit ball `𝒜₀`
([WP] `𝒜° = 𝒜₀`, prop:parity-uniform-domain). -/
theorem powerBoundedSubring_eq_unitBall (ϖ : Uniformizer K) :
    powerBoundedSubring (WPA K w) = (FiniteJet.unitBall (WPA K w) : Set (WPA K w)) := by
  sorry

variable {K w} in
/-- **`𝒜` is uniform** ([WP] prop:parity-uniform-domain / thm 6.2(1)). -/
theorem isUniform_WPA (ϖ : Uniformizer K) : IsUniform (WPA K w) := by sorry

end WeightedParity
