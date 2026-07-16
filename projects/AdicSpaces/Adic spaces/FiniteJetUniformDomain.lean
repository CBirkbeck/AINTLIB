/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetRings
import «Adic spaces».Uniform

/-!
# 𝓐 is a uniform domain and is not noetherian ([FJP] Propositions 2.3, 2.4, and (5.2))

* **Prop 2.3**: the Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative; `𝓐° = 𝓐₀` is the unit ball;
  hence `𝓐` is a complete uniform Tate ring and an integral domain.
* **(5.2)**: the maximal plus rings of 𝓑 and 𝓓 are `k°⟨W⟩ ⊕ Qk⟨W⟩` resp. `L° ⊕ QL` —
  power-boundedness depends only on the constant-jet component (`(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`).
* **Prop 2.4**: `𝓐` is not noetherian: the ideal `J = Q²𝒞 = ker(jB)` is not finitely
  generated, since `J/KJ ≅ L` over `𝓐/K ≅ k⟨W⟩` and `W⁻¹` is not integral over `k⟨W⟩`.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent TopologicalRing

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### Norm multiplicativity and the domain property ([FJP] Prop 2.3) -/

/-- The Gauss norm on `L = K⟨W,W⁻¹⟩` is multiplicative (specialisation of
`RestrictedLaurent.norm_mul_eq` to the discretely valued `K`). -/
theorem norm_L_mul (f g : L F) : ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

/-- The Gauss norm on `𝒞 = L⟨Q⟩` is multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm
on 𝒞 = L⟨Q⟩ is multiplicative"). -/
theorem norm_JetC_mul (f g : JetC F) : ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

/-- `𝒞` is an integral domain ([FJP] Prop 2.3: "also that 𝒞 is a domain"). -/
instance : IsDomain (JetC F) := by sorry

/-- `𝓐` is an integral domain ([FJP] Prop 2.3: "𝒜 is a domain because it is a subring
of 𝒞"). -/
instance : IsDomain (JetA F) := by sorry

/-! ### The power-bounded subring of 𝓐 is the unit ball ([FJP] Prop 2.3) -/

/-- Power-boundedness in 𝓐 is having norm at most one ([FJP] Prop 2.3: "If `v(a) < 0` …
`a` is not power-bounded. If `v(a) ≥ 0`, all powers of `a` lie in 𝒜₀. Thus the valuation
formulation gives directly `𝒜° = 𝒜₀`"). -/
theorem isPowerBounded_JetA_iff (a : JetA F) :
    TopologicalRing.IsPowerBounded a ↔ ‖a‖ ≤ 1 := by sorry

/-- The power-bounded subring of 𝓐 is bounded — **𝓐 is uniform**
([FJP] Prop 2.3: "The ring 𝒜 is a complete uniform Tate k-algebra"). -/
theorem isUniform_JetA : TopologicalRing.IsUniform (JetA F) := by sorry

/-! ### The plus rings of the jet vertices ([FJP] (5.2)) -/

/-- Power-boundedness in `𝓑` depends only on the constant-jet component
([FJP] (5.2): `ℬ° = k°⟨W⟩ ⊕ Qk⟨W⟩`, via `(f+Qg)ⁿ = fⁿ + nf^{n-1}Qg`). -/
theorem isPowerBounded_JetB_iff (x : JetB F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 := by sorry

/-- Power-boundedness in `𝓓` depends only on the constant-jet component
([FJP] (5.2): `𝒟° = L° + QL`). -/
theorem isPowerBounded_JetD_iff (x : JetD F) :
    TopologicalRing.IsPowerBounded x ↔ ‖x.fst‖ ≤ 1 := by sorry

/-- `𝓑` is **not** uniform: the square-zero line `K·ε` is power-bounded and unbounded
([FJP] (2.1d): "the summand `kQ` is an unbounded line"). -/
theorem not_isUniform_JetB : ¬ TopologicalRing.IsUniform (JetB F) := by sorry

/-! ### 𝓐 is not noetherian ([FJP] Prop 2.4) -/

/-- The scalars `K⟨W⟩` act on `L` through the norm-preserving embedding. -/
noncomputable instance : Algebra (PowerSeries.Restricted K (1 : ℝ)) (L F) :=
  (ofRestricted (R := K)).toAlgebra

/-- `W⁻¹ ∈ L` is not integral over `K⟨W⟩` ([FJP] Prop 2.4: multiplying a monic equation
`(W⁻¹)ⁿ + a_{n-1}(W)(W⁻¹)^{n-1} + ⋯ + a₀(W) = 0` by `Wⁿ` and evaluating at `W = 0`
gives `1 = 0`). -/
theorem winv_not_integral :
    ¬ IsIntegral (PowerSeries.Restricted K (1 : ℝ)) ((Wu (R := K))⁻¹ : (L F)ˣ).val := by
  sorry

/-- `L` is not module-finite over `K⟨W⟩` ([FJP] Prop 2.4: "It would follow that `L` is a
finite `R_W`-module. A module-finite algebra is integral, so `W⁻¹` would satisfy a monic
equation"). -/
theorem not_moduleFinite_L : ¬ Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by
  sorry

/-- If the ideal `J = ker(jB) = Q²𝒞` of 𝓐 were finitely generated, `L` would be
module-finite over `K⟨W⟩` ([FJP] Prop 2.4: `KJ = Q³𝒞`, `J/KJ ≅ 𝒞/Q𝒞 = L` as
`𝒜/K ≅ R_W`-modules, and generators of `J` generate `J/KJ`). -/
theorem moduleFinite_of_ker_jB_fg (h : (RingHom.ker (jB F)).FG) :
    Module.Finite (PowerSeries.Restricted K (1 : ℝ)) (L F) := by sorry

/-- The ideal `Q²𝒞 ⊂ 𝓐` is not finitely generated ([FJP] Prop 2.4). -/
theorem ker_jB_not_fg : ¬ (RingHom.ker (jB F)).FG := by sorry

/-- **𝓐 is not noetherian** ([FJP] Prop 2.4: "The underlying ring 𝒜 is not noetherian"). -/
theorem not_isNoetherianRing_JetA : ¬ IsNoetherianRing (JetA F) := by sorry

end FiniteJet
