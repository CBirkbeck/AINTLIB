import HasseWeil.Curves.ProjectiveDivisor
import HasseWeil.Curves.NoFinitePolesBridge
import HasseWeil.Curves.Divisors

/-!
# Route 2A — functions with trivial divisor are constant (pairing step 7c)

The Weil pairing value `e_ℓ(S,T) = (τ_S^* g)/g` is **constant** because its projective divisor is
zero: a function on a complete (projective) curve with no zeros or poles lies in the base field `F`.

This ships `const_of_projectiveDivisorOf_eq_zero` unconditionally over `K̄`, composing the project's
* `projectiveDivisorOf_apply_affine` / `_infinity` (`div f = 0 ⟹ ord_P f = 0` everywhere),
* `pointValuation_eq_heightOneValuation` (the now-discharged DVR/adic valuation identity),
* `smoothPointToHeightOne_surjective` (every height-one prime is a smooth point),
* `const_of_valuation_le_one_of_ordAtInfty_nonneg` (algebraic Liouville, Silverman II.1.2).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open Curves

set_option linter.style.longLine false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

-- The `(⟨W⟩ : SmoothPlaneCurve F)` curve coercion makes instance/`whnf` elaboration heavy.
set_option maxHeartbeats 1600000 in
/-- **A function with trivial projective divisor is a constant** (Silverman II.1.2, projective form),
unconditional over an algebraically closed field. If `projectiveDivisorOf f = 0` (no zeros or poles,
including at infinity), then `f = algebraMap F _ c` for some `c : F`. -/
theorem const_of_projectiveDivisorOf_eq_zero [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
    (hdiv : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f = 0) :
    ∃ c : F, f = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c := by
  -- div f = 0 ⟹ ord_P f = 0 at every smooth point, and ord_∞ f = 0.
  have hord : ∀ P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint,
      0 ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f := by
    intro P
    have h := DFunLike.congr_fun hdiv (ProjectiveSmoothPoint.affine P)
    rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_affine, Finsupp.coe_zero, Pi.zero_apply] at h
    have hne : (⟨W⟩ : SmoothPlaneCurve F).ord_P P f ≠ ⊤ := ((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff f).not.mpr hf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hn] at h ⊢
    rw [WithTop.untopD_coe] at h
    rw [h]
    exact le_refl _
  have hinf : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f := by
    have h := DFunLike.congr_fun hdiv ProjectiveSmoothPoint.infinity
    rw [(⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf_apply_infinity, Finsupp.coe_zero, Pi.zero_apply] at h
    have hne : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f ≠ ⊤ := ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff f).not.mpr hf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hn] at h ⊢
    rw [WithTop.untopD_coe] at h
    rw [h]
    exact le_refl _
  refine (⟨W⟩ : SmoothPlaneCurve F).const_of_valuation_le_one_of_ordAtInfty_nonneg f ?_ hinf
  intro v
  obtain ⟨P, hP⟩ := smoothPointToHeightOne_surjective W v
  rw [← hP, ← pointValuation_eq_heightOneValuation W P f]
  exact pointValuation_le_one_of_ord_nonneg W hf P (hord P)

/-- **A nonzero function with trivial divisor is a nonzero constant.** Refinement of
`const_of_projectiveDivisorOf_eq_zero` for the Weil-pairing value: `e_ℓ(S,T) = (τ_S^* g)/g` has
trivial divisor and is nonzero, hence equals `algebraMap F _ c` for a **nonzero** `c : F` — a unit,
landing in `μ_ℓ` once `(·)^ℓ = 1` is established. -/
theorem const_unit_of_projectiveDivisorOf_eq_zero [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
    (hdiv : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f = 0) :
    ∃ c : F, c ≠ 0 ∧ f = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c := by
  obtain ⟨c, hc⟩ := const_of_projectiveDivisorOf_eq_zero f hf hdiv
  refine ⟨c, ?_, hc⟩
  rintro rfl
  rw [map_zero] at hc
  exact hf hc

/-- **The Weil-pairing value as a scalar** (pairing step 7d). For a ring automorphism `τ` of the
function field (the translation `τ_S = translateAlgEquivOfPoint W S`) and a nonzero `g`, if the
quotient `τg/g` has trivial divisor (the translation-functoriality hypothesis `div(τ_S^* g) = div(g)`,
which holds for `S ∈ E[ℓ]` by the fibre-shift), then `τg = c · g` for a **nonzero** scalar `c : F`.
This `c` is the pairing value `e_ℓ(S,T)`; once `c^ℓ = 1` (from `g^ℓ = f_T∘[ℓ]`) it lands in `μ_ℓ`. -/
theorem pairing_const_of_transport [IsAlgClosed F] [W.IsElliptic]
    [IsDedekindDomain (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0)
    (htransport : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf (τ g / g) = 0) :
    ∃ c : F, c ≠ 0 ∧ τ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g := by
  have hτg : τ g ≠ 0 := (map_ne_zero_iff τ τ.injective).mpr hg
  obtain ⟨c, hc0, hc⟩ :=
    const_unit_of_projectiveDivisorOf_eq_zero (τ g / g) (div_ne_zero hτg hg) htransport
  exact ⟨c, hc0, (div_eq_iff hg).mp hc⟩

omit [DecidableEq F] in
/-- **The pairing value is an `ℓ`-th root of unity** (pairing step 7d, `μ_ℓ`-membership). Given the
pairing relation `τg = c·g` and that `τ` **fixes** `g^ℓ` (which holds because `g^ℓ = f_T∘[ℓ]` and
`[ℓ](·+S) = [ℓ](·)` for `S ∈ E[ℓ]`, so `τ_S(f_T∘[ℓ]) = f_T∘[ℓ]`), the scalar `c` satisfies
`c^ℓ = 1`. Hence `e_ℓ(S,T) = c ∈ μ_ℓ`. -/
theorem pairing_const_pow_eq_one
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) (ℓ : ℕ) {c : F}
    (hc : τ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g)
    (hfix : τ (g ^ ℓ) = g ^ ℓ) :
    c ^ ℓ = 1 := by
  have h1 : τ (g ^ ℓ) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c ^ ℓ) * g ^ ℓ := by
    rw [map_pow, hc, mul_pow, map_pow]
  rw [hfix] at h1
  have h2 : (1 : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) * g ^ ℓ =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c ^ ℓ) * g ^ ℓ := by
    rw [one_mul]; exact h1
  have h3 := mul_right_cancel₀ (pow_ne_zero ℓ hg) h2
  exact ((algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (by rw [map_one]; exact h3)).symm

omit [DecidableEq F] in
/-- **Bilinearity of the Weil pairing in the first slot** (pairing step 8, Prop 8.1). If the
translations compose (`τ_{S₁+S₂} = τ_{S₁} ∘ τ_{S₂}`, a group action of `E` on `K(E)`) and `τ_{S₁}`
fixes the base field `F`, then the pairing values multiply: `e_ℓ(S₁+S₂, T) = e_ℓ(S₁,T)·e_ℓ(S₂,T)`,
i.e. `c₁₂ = c₁·c₂`. -/
theorem pairing_const_mul
    (τ₁ τ₂ τ₁₂ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) {c₁ c₂ c₁₂ : F}
    (hτ₁F : ∀ a : F, τ₁ (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a)
    (hcomp : ∀ x, τ₁₂ x = τ₁ (τ₂ x))
    (hc₁ : τ₁ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁ * g)
    (hc₂ : τ₂ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₂ * g)
    (hc₁₂ : τ₁₂ g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁₂ * g) :
    c₁₂ = c₁ * c₂ := by
  have hval : τ₁₂ g =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c₁ * c₂) * g := by
    rw [hcomp, hc₂, map_mul, hτ₁F, hc₁, map_mul]; ring
  rw [hc₁₂] at hval
  exact (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (mul_right_cancel₀ hg hval)

omit [DecidableEq F] in
/-- **Value-multiplicativity across DIFFERENT functions related by an invariant factor**
(pairing step 8, Prop 8.1**b** — bilinearity in the *second* slot). This is the engine for
`weilPairing_mul_right`: the three Weil functions `g₁ = g_{T₁}`, `g₂ = g_{T₂}`, `g₁₂ = g_{T₁+T₂}`
are *different* (they depend on the second argument), but the divisor-pullback functoriality
relates them by `g₁₂ = c · g₁ · g₂ · u`, where `u = [ℓ]^* k` is the pullback of the Abel–Jacobi
function for `(T₁+T₂) − (T₁) − (T₂) + (O)` and `c ∈ F^×` is the constant absorbing the equal
divisors. The single automorphism `τ = τ_S` acts on all three by its pairing scalar
(`τ gᵢ = cᵢ · gᵢ`), fixes the base field `F` (`hτF`) and fixes the covariant factor `u`
(`hτu`, the covariance `hcov` for `S ∈ E[ℓ]`). Cancelling `g₁₂ ≠ 0` gives `c₁₂ = c₁ · c₂`. -/
theorem pairing_const_mul_invariant_factor
    (τ : (⟨W⟩ : SmoothPlaneCurve F).FunctionField ≃+*
      (⟨W⟩ : SmoothPlaneCurve F).FunctionField)
    (g₁ g₂ g₁₂ u : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg₁₂ : g₁₂ ≠ 0)
    {c c₁ c₂ c₁₂ : F}
    (hτF : ∀ a : F, τ (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a) =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField a)
    (hτu : τ u = u)
    (hfact : g₁₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * (g₁ * g₂ * u))
    (hc₁ : τ g₁ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁ * g₁)
    (hc₂ : τ g₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₂ * g₂)
    (hc₁₂ : τ g₁₂ = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c₁₂ * g₁₂) :
    c₁₂ = c₁ * c₂ := by
  -- Apply `τ` to the factorization and simplify with the three scalar relations.
  have hval : τ g₁₂ =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField (c₁ * c₂) * g₁₂ := by
    conv_lhs => rw [hfact, map_mul, map_mul, map_mul, hτF, hc₁, hc₂, hτu]
    rw [map_mul, hfact]
    ring
  rw [hc₁₂] at hval
  exact (algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (mul_right_cancel₀ hg₁₂ hval)

omit [DecidableEq F] in
/-- **The Weil pairing is trivial on `O`** (pairing step 8, Prop 8.1): `e_ℓ(O,T) = 1`. The
translation by `O` is the identity (`translateAlgEquivOfPoint W 0 = AlgEquiv.refl`), so `τg = g`
forces the pairing value `c = 1`. -/
theorem pairing_const_refl
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) {c : F}
    (hc : g = algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g) :
    c = 1 := by
  have h2 : (1 : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) * g =
      algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField c * g := by rw [one_mul]; exact hc
  have h3 := mul_right_cancel₀ hg h2
  exact ((algebraMap F (⟨W⟩ : SmoothPlaneCurve F).FunctionField).injective
    (by rw [map_one]; exact h3)).symm

end HasseWeil.WeilPairing
