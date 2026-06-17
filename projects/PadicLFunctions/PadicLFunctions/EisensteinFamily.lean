/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)

The Part-I closer: the Kubota–Leopoldt pseudo-measure interpolates the
*constant* coefficients of the p-stabilised Eisenstein series
`E_k^{(p)} = E_k − p^{k−1}E_k(p·)`, and the non-constant coefficients are
interpolated by elementary divisor-sums of Dirac measures. Bundling
coefficientwise gives the Λ-adic Eisenstein family
`𝐄 = Σ A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧` (RJW Theorem at TeX 2399):
`A₀ = x·ζ_p/2` and `A_n = Σ_{0<d∣n, p∤d} δ_d`, with
`∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for even `k ≥ 4`.

Two deviations from the letter of the source, both recorded:
* **Erratum #11** (`.mathlib-quality/errata.md`): the notes claim "(a) A₀ is
  a pseudo-measure"; with the notes' own Def 3.34 this is false — the pole
  of `x·ζ_p` sits at the character `x⁻¹`, not at the trivial character. We
  prove the corrected claim `(g·[g]−[1])·A₀ ∈ Λ(ℤ_p^×)` for all `g`
  (decomposition replan R8.1).
* The x-twist `τ : [g] ↦ g·[g]` is realised as a ring automorphism of the
  convolution algebra by a pure moments check against the zero-divisor
  lemma (replan R8.2) — no Amice-transform theory is needed.

The complex side (the q-expansion of `E_k^{(p)}` and the σ^p-arithmetic)
lives in `PadicLFunctions/EisensteinComplex.lean`; the two sides meet in
the rational coefficient sequence `stabilisedCoeff` defined here.
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

section diracDivisors

/-- `2` is a unit of `ℤ_p` for odd `p` (its valuation is `0`). -/
theorem isUnit_two_padicInt (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  have hnd : ¬ (p : ℕ) ∣ 2 := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  simpa using PadicInt.isUnit_natCast_of_not_dvd (p := p) hnd

open Classical in
/-- The unit of `ℤ_p^×` attached to a natural number `d` coprime to `p`
(junk value `1` when `p ∣ d`). RJW TeX 2376: "viewing `d` as an element of
`ℤ_p^×`". -/
noncomputable def unitOfNat (d : ℕ) : ℤ_[p]ˣ :=
  if h : IsUnit ((d : ℕ) : ℤ_[p]) then h.unit else 1

theorem unitOfNat_coe {d : ℕ} (hd : ¬ (p : ℕ) ∣ d) :
    ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p]) := by
  rw [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]

/-- R8: the prime-to-`p` divisor power sum
`σ^p_k(n) = Σ_{0<d∣n, p∤d} d^k` (RJW TeX 2393). -/
def sigmaP (k n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d), d ^ k

/-- R8: the divisor-sum measure `A_n = Σ_{0<d∣n, p∤d} δ_d ∈ Λ(ℤ_p^×)`
(RJW TeX 2411). `A_0 = 0` (the family's constant coefficient is instead the
twisted pseudo-measure `twistedZetaHalf`). -/
noncomputable def divisorMeasure (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d),
    PadicMeasure.dirac p (unitOfNat p d)

/-- R8 (RJW TeX 2413): `∫_{ℤ_p^×} x^k · A_n = σ^p_k(n)` — the Dirac measures
evaluate, `∫ x^k δ_d = d^k`. -/
theorem divisorMeasure_moment (n k : ℕ) :
    divisorMeasure p n (PadicMeasure.unitsPowCM p k)
      = ((sigmaP p k n : ℕ) : ℤ_[p]) := by
  rw [divisorMeasure, LinearMap.coe_sum, Finset.sum_apply, sigmaP, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [PadicMeasure.dirac_apply]
  change ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) ^ k = ((d ^ k : ℕ) : ℤ_[p])
  rw [unitOfNat_coe p (Finset.mem_filter.1 hd).2, Nat.cast_pow]

end diracDivisors

section twist

private lemma unitsPowCM_one_mul_unitsPowCM (k : ℕ) :
    PadicMeasure.unitsPowCM p 1 * PadicMeasure.unitsPowCM p k
      = PadicMeasure.unitsPowCM p (k + 1) := by
  refine ContinuousMap.ext fun u => ?_
  simp only [ContinuousMap.mul_apply, PadicMeasure.unitsPowCM, ContinuousMap.coe_mk, pow_one]
  rw [pow_succ']

private lemma invCM_mul_unitsPowCM_one :
    PadicMeasure.invCM p * PadicMeasure.unitsPowCM p 1 = 1 := by
  refine ContinuousMap.ext fun u => ?_
  simp only [ContinuousMap.mul_apply, PadicMeasure.invCM, PadicMeasure.unitsPowCM,
    ContinuousMap.coe_mk, pow_one, ContinuousMap.one_apply]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private lemma unitsPowCM_one_mul_invCM :
    PadicMeasure.unitsPowCM p 1 * PadicMeasure.invCM p = 1 := by
  rw [mul_comm, invCM_mul_unitsPowCM_one]

private lemma unitsCmul_powCM_one_moment (μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) μ (PadicMeasure.unitsPowCM p k)
      = μ (PadicMeasure.unitsPowCM p (k + 1)) := by
  rw [PadicMeasure.unitsCmul_apply, unitsPowCM_one_mul_unitsPowCM]

/-- R8 (replan R8.2): the x-twist `τ : Λ(ℤ_p^×) → Λ(ℤ_p^×)`,
`(τμ)(f) = μ(x·f)` — on Diracs `[g] ↦ g·[g]` — as a ring automorphism of
the convolution algebra. Multiplicativity is a moments check
(`units_mul_apply_unitsPowCM` + the zero-divisor lemma); the inverse is the
twist by `x⁻¹`. -/
noncomputable def unitsTwist : PadicMeasure p ℤ_[p]ˣ ≃+* PadicMeasure p ℤ_[p]ˣ where
  toFun := PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1)
  invFun := PadicMeasure.unitsCmul p (PadicMeasure.invCM p)
  left_inv μ := by
    refine LinearMap.ext fun f => ?_
    rw [PadicMeasure.unitsCmul_apply, PadicMeasure.unitsCmul_apply, ← mul_assoc,
      unitsPowCM_one_mul_invCM, one_mul]
  right_inv μ := by
    refine LinearMap.ext fun f => ?_
    rw [PadicMeasure.unitsCmul_apply, PadicMeasure.unitsCmul_apply, ← mul_assoc,
      invCM_mul_unitsPowCM_one, one_mul]
  map_mul' μ ν := by
    have hzd : PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) (μ * ν)
        - PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) μ
          * PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) ν = 0 := by
      refine PadicMeasure.eq_zero_of_forall_unitsPowCM_eq_zero p _ fun k _ => ?_
      rw [LinearMap.sub_apply, PadicMeasure.units_mul_apply_unitsPowCM,
        unitsCmul_powCM_one_moment, unitsCmul_powCM_one_moment, unitsCmul_powCM_one_moment,
        PadicMeasure.units_mul_apply_unitsPowCM, sub_self]
    exact sub_eq_zero.mp hzd
  map_add' μ ν := by
    refine LinearMap.ext fun f => ?_
    rw [PadicMeasure.unitsCmul_apply, LinearMap.add_apply, LinearMap.add_apply,
      PadicMeasure.unitsCmul_apply, PadicMeasure.unitsCmul_apply]

/-- The twist shifts moments by one: `∫x^k·(τμ) = ∫x^{k+1}·μ`. -/
theorem unitsTwist_moment (μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) :
    unitsTwist p μ (PadicMeasure.unitsPowCM p k)
      = μ (PadicMeasure.unitsPowCM p (k + 1)) :=
  unitsCmul_powCM_one_moment p μ k

/-- The twist sends Diracs to scaled Diracs: `τ(δ_g) = g·δ_g`. -/
theorem unitsTwist_dirac (g : ℤ_[p]ˣ) :
    unitsTwist p (PadicMeasure.dirac p g)
      = (g : ℤ_[p]) • PadicMeasure.dirac p g := by
  refine LinearMap.ext fun f => ?_
  change PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) (PadicMeasure.dirac p g) f
    = ((g : ℤ_[p]) • PadicMeasure.dirac p g) f
  rw [PadicMeasure.unitsCmul_apply, PadicMeasure.dirac_apply, LinearMap.smul_apply,
    PadicMeasure.dirac_apply, ContinuousMap.mul_apply, smul_eq_mul]
  congr 1
  simp [PadicMeasure.unitsPowCM]

/-- A ring automorphism maps the non-zero-divisors onto the
non-zero-divisors. -/
theorem map_nonZeroDivisors_unitsTwist :
    (nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)).map
        (unitsTwist p).toMonoidHom
      = nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) :=
  MulEquivClass.map_nonZeroDivisors (unitsTwist p)

/-- R8: the x-twist extended to the total fraction ring `Q(ℤ_p^×)`. -/
noncomputable def quotientTwist :
    PadicMeasure.QuotientField p ≃+* PadicMeasure.QuotientField p :=
  IsLocalization.ringEquivOfRingEquiv
    (PadicMeasure.QuotientField p) (PadicMeasure.QuotientField p)
    (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)

/-- The extended twist restricts to the measure-twist on `Λ(ℤ_p^×)`. -/
theorem quotientTwist_algebraMap (μ : PadicMeasure p ℤ_[p]ˣ) :
    quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p) μ)
      = algebraMap _ _ (unitsTwist p μ) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ μ

end twist

section family

/-- R8 (RJW TeX 2410): the constant coefficient `A₀ = x·ζ_p/2` of the
Eisenstein family — the x-twist of the Kubota–Leopoldt pseudo-measure,
halved (`2` is a unit of `ℤ_p` for odd `p`). -/
noncomputable def twistedZetaHalf (hp2 : p ≠ 2) : PadicMeasure.QuotientField p :=
  algebraMap _ (PadicMeasure.QuotientField p)
      ((((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
        • (1 : PadicMeasure p ℤ_[p]ˣ))
    * quotientTwist p (PadicMeasure.padicZeta p hp2)

private lemma smul_one_mul' (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) :
    (c • (1 : PadicMeasure p ℤ_[p]ˣ)) * μ = c • μ := by
  have h : (c • (1 : PadicMeasure p ℤ_[p]ˣ)) * μ
      = c • ((1 : PadicMeasure p ℤ_[p]ˣ) * μ) := by
    refine LinearMap.ext fun f => ?_
    rw [PadicMeasure.units_mul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      PadicMeasure.units_mul_apply]
  rw [h, one_mul]

private lemma coe_inv_two (hp2 : p ≠ 2) :
    ((((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p])⁻¹ := by
  set u := (isUnit_two_padicInt p hp2).unit
  have hspec : ((u : ℤ_[p]ˣ) : ℤ_[p]) = 2 := IsUnit.unit_spec _
  have h2 : (2 : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← hspec, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : (2 : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) h2
    push_cast at this
    convert this using 2
    norm_cast
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h3)

private lemma twistedZetaHalf_witness_eq (hp2 : p ≠ 2) (g : ℤ_[p]ˣ)
    (νg : PadicMeasure p ℤ_[p]ˣ)
    (hνg : algebraMap _ (PadicMeasure.QuotientField p) (PadicMeasure.dirac p g - 1)
        * PadicMeasure.padicZeta p hp2 = algebraMap _ _ νg) :
    algebraMap _ (PadicMeasure.QuotientField p)
        ((g : ℤ_[p]) • PadicMeasure.dirac p g - 1) * twistedZetaHalf p hp2
      = algebraMap _ _
          ((((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • unitsTwist p νg) := by
  have hkey : (g : ℤ_[p]) • PadicMeasure.dirac p g - 1
      = unitsTwist p (PadicMeasure.dirac p g - 1) := by
    rw [map_sub, unitsTwist_dirac, map_one]
  have hc : quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p g - 1) * PadicMeasure.padicZeta p hp2)
      = quotientTwist p (algebraMap _ _ νg) := congrArg _ hνg
  rw [map_mul, quotientTwist_algebraMap, quotientTwist_algebraMap] at hc
  set c : ℤ_[p] := (((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  rw [twistedZetaHalf, hkey]
  rw [show algebraMap (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
        (unitsTwist p (PadicMeasure.dirac p g - 1))
      * (algebraMap _ _ (c • (1 : PadicMeasure p ℤ_[p]ˣ))
          * quotientTwist p (PadicMeasure.padicZeta p hp2))
      = algebraMap _ _ (c • (1 : PadicMeasure p ℤ_[p]ˣ))
          * (algebraMap _ _ (unitsTwist p (PadicMeasure.dirac p g - 1))
            * quotientTwist p (PadicMeasure.padicZeta p hp2)) by ring]
  rw [hc, ← map_mul, smul_one_mul']

/-- R8 (replan R8.1, **erratum #11**): the corrected form of RJW TeX 2403(a).
The notes claim `A₀ = x·ζ_p/2` is a pseudo-measure; with Def 3.34 this is
false (the pole of `x·ζ_p` sits at the character `x⁻¹`, not at the trivial
character — see `.mathlib-quality/errata.md` #11). What holds, and what the
family needs, is the x-twisted analogue: `(g·[g] − [1])·A₀ ∈ Λ(ℤ_p^×)` for
every `g`. -/
theorem twistedZetaHalf_isTwistedPseudoMeasure (hp2 : p ≠ 2) (g : ℤ_[p]ˣ) :
    ∃ ν : PadicMeasure p ℤ_[p]ˣ,
      algebraMap _ (PadicMeasure.QuotientField p)
          ((g : ℤ_[p]) • PadicMeasure.dirac p g - 1)
        * twistedZetaHalf p hp2 = algebraMap _ _ ν := by
  obtain ⟨νg, hνg⟩ := PadicMeasure.padicZeta_isPseudoMeasure p hp2 g
  exact ⟨_, twistedZetaHalf_witness_eq p hp2 g νg hνg⟩

/-- R8 (RJW TeX 2412 "A₀ interpolates the constant term"): the moments of
`A₀ = x·ζ_p/2` in the witness encoding — any witness `ν` of
`(b·[b]−[1])·A₀ ∈ Λ` has
`∫x^{k−1}·ν = (b^k−1)·(1−p^{k−1})·ζ(1−k)/2`, the constant coefficient of
`E_k^{(p)}` scaled by the twisted-denominator factor `b^k−1`. -/
theorem twistedZetaHalf_moments (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ}
    (hk : 4 ≤ k) (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (PadicMeasure.QuotientField p)
          ((b : ℤ_[p]) • PadicMeasure.dirac p b - 1)
        * twistedZetaHalf p hp2 = algebraMap _ _ ν) :
    ((ν (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p]) : ℚ_[p])
      = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) / 2 := by
  obtain ⟨νb, hνb⟩ := PadicMeasure.padicZeta_isPseudoMeasure p hp2 b
  set c : ℤ_[p] := (((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  have hνeq : ν = c • unitsTwist p νb := by
    apply IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure.QuotientField p)
    rw [← hν, twistedZetaHalf_witness_eq p hp2 b νb hνb]
  have hmom : ν (PadicMeasure.unitsPowCM p (k - 1))
      = c * νb (PadicMeasure.unitsPowCM p k) := by
    rw [hνeq, LinearMap.smul_apply, smul_eq_mul, unitsTwist_moment,
      Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [hmom, PadicInt.coe_mul, coe_inv_two p hp2,
    PadicMeasure.padicZeta_moments p hp2 b (by omega : 0 < k) νb hνb]
  field_simp

private lemma units_pow_totient_sq_sub_self_mem (u : ℤ_[p]ˣ) :
    ((u : ℤ_[p]) ^ (1 + Nat.totient (p ^ 2)) - (u : ℤ_[p]))
      ∈ (Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p]) := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hcard : Nat.card (ZMod (p ^ 2))ˣ = Nat.totient (p ^ 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have himg : (PadicMeasure.unitsToZModPow p 2 u) ^ Nat.totient (p ^ 2) = 1 :=
    hcard ▸ pow_card_eq_one'
  have hmem1 : ((u : ℤ_[p]) ^ Nat.totient (p ^ 2) - 1)
      ∈ (Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_pow, map_one,
      ← PadicMeasure.unitsToZModPow_coe, ← Units.val_pow_eq_pow_val, himg,
      Units.val_one, sub_self]
  have hfact : (u : ℤ_[p]) ^ (1 + Nat.totient (p ^ 2)) - (u : ℤ_[p])
      = (u : ℤ_[p]) * ((u : ℤ_[p]) ^ Nat.totient (p ^ 2) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.add_comm]
  rw [hfact]
  exact Ideal.mul_mem_left _ _ hmem1

/-- R8 (RJW TeX 2379–2383): the function `k ↦ p^k` can never be interpolated
by a measure on `ℤ_p^×`. Finitary route (replan note in ticket T804): if a
measure `θ` interpolated `k ↦ p^k`, then at the single congruence level
`p²` the exponents `K := 1 + φ(p²)` and `1` agree on `ℤ_p^×` modulo `p²`
(`units_pow_totient_sq_sub_self_mem`), so `‖x^K − x^1‖ ≤ p^{-2}` as a sup
norm; boundedness of `θ` (`norm_apply_le`) forces `‖p^K − p‖ ≤ p^{-2}`.
But `‖p^K − p‖ = ‖p‖·‖p^{K−1} − 1‖ = p^{-1}` (`K − 1 = φ(p²) ≥ 1`, so the
second factor has norm one by the ultrametric isoceles), and `p^{-1} ≤ p^{-2}`
is false. Notably `p = 2` is allowed (no `hp2` is used). -/
theorem noMeasure_interpolates_pPow :
    ¬ ∃ θ : PadicMeasure p ℤ_[p]ˣ, ∀ k : ℕ, 0 < k →
      θ (PadicMeasure.unitsPowCM p k) = (p : ℤ_[p]) ^ k := by
  rintro ⟨θ, hθ⟩
  set K : ℕ := 1 + Nat.totient (p ^ 2)
  have htot2 : 2 ≤ Nat.totient (p ^ 2) := by
    rw [Nat.totient_prime_pow hp.out two_pos, show 2 - 1 = 1 from rfl, pow_one]
    have := hp.out.two_le
    calc 2 = 2 * 1 := (mul_one 2).symm
      _ ≤ p * (p - 1) := Nat.mul_le_mul this (by omega)
  have hKpos : 0 < K := by omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsup : ‖PadicMeasure.unitsPowCM p K - PadicMeasure.unitsPowCM p 1‖
      ≤ (p : ℝ) ^ (-2 : ℤ) := by
    rw [ContinuousMap.norm_le _ (zpow_nonneg (le_of_lt hppos) _)]
    intro u
    rw [ContinuousMap.coe_sub, Pi.sub_apply]
    change ‖(u : ℤ_[p]) ^ K - (u : ℤ_[p]) ^ 1‖ ≤ (p : ℝ) ^ (-2 : ℤ)
    rw [pow_one, show (-2 : ℤ) = (-(2 : ℕ) : ℤ) by norm_num,
      PadicInt.norm_le_pow_iff_mem_span_pow]
    exact units_pow_totient_sq_sub_self_mem p u
  have hmeas : ‖θ (PadicMeasure.unitsPowCM p K) - θ (PadicMeasure.unitsPowCM p 1)‖
      ≤ (p : ℝ) ^ (-2 : ℤ) := by
    rw [← map_sub]
    exact le_trans (PadicMeasure.norm_apply_le p θ _) hsup
  rw [hθ K hKpos, hθ 1 one_pos, pow_one] at hmeas
  have hfactp : (p : ℤ_[p]) ^ K - (p : ℤ_[p])
      = (p : ℤ_[p]) * ((p : ℤ_[p]) ^ (K - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ K)]
  have hnormfac : ‖(p : ℤ_[p]) ^ (K - 1) - 1‖ = 1 := by
    have hlt : ‖(p : ℤ_[p]) ^ (K - 1)‖ < ‖(-1 : ℤ_[p])‖ := by
      rw [norm_pow, norm_neg, norm_one, PadicInt.norm_p]
      have h1lt : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
      have hb : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1lt
      exact pow_lt_one₀ (by positivity) hb (by omega)
    rw [sub_eq_add_neg, PadicInt.norm_add_eq_max_of_ne (ne_of_lt hlt),
      max_eq_right (le_of_lt hlt), norm_neg, norm_one]
  have hnormpK : ‖(p : ℤ_[p]) ^ K - (p : ℤ_[p])‖ = (p : ℝ) ^ (-1 : ℤ) := by
    rw [hfactp, norm_mul, PadicInt.norm_p, hnormfac, mul_one, zpow_neg, zpow_one]
  rw [hnormpK] at hmeas
  have h1lt : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [zpow_le_zpow_iff_right₀ h1lt] at hmeas
  omega

/-- R8: the rational coefficient sequence of the p-stabilised Eisenstein
series `E_k^{(p)}` (RJW TeX 2391): constant term `(1−p^{k−1})·ζ(1−k)/2`,
`n`-th term `σ^p_{k−1}(n)`. This is the pivot between the p-adic family
(`eisensteinFamily_interpolation`) and the complex q-expansion
(`hasSum_stabilisedEisenstein` in `EisensteinComplex.lean`). -/
def stabilisedCoeff (k : ℕ) : ℕ → ℚ := fun n =>
  if n = 0 then (1 - (p : ℚ) ^ (k - 1)) * zetaNeg (k - 1) / 2
  else sigmaP p (k - 1) n

/-- R8 (RJW TeX 2399–2400): the Λ-adic Eisenstein family
`𝐄 = Σ_{n≥0} A_n qⁿ ∈ Q(ℤ_p^×)⟦q⟧`: constant coefficient `A₀ = x·ζ_p/2`,
higher coefficients the divisor-sum measures `A_n`. -/
noncomputable def eisensteinFamily (hp2 : p ≠ 2) :
    PowerSeries (PadicMeasure.QuotientField p) :=
  PowerSeries.mk fun n =>
    if n = 0 then twistedZetaHalf p hp2
    else algebraMap _ _ (divisorMeasure p n)

/-- **RJW §8 Theorem (TeX 2399–2407), p-adic half**: the coefficientwise
interpolation `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for `k ≥ 4` — the `n`-th
moment of the family equals the `n`-th coefficient `stabilisedCoeff p k n`
of the p-stabilised Eisenstein series, with the constant coefficient in the
pseudo-measure witness encoding. (Evenness of `k` is not needed on the
p-adic side; it enters only in the complex identification of
`stabilisedCoeff` with the q-expansion of `E_k^{(p)}`, which is
`hasSum_stabilisedEisenstein` in `EisensteinComplex.lean`.) -/
theorem eisensteinFamily_interpolation (hp2 : p ≠ 2) {k : ℕ} (hk : 4 ≤ k) :
    (∀ (b : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ),
      algebraMap _ (PadicMeasure.QuotientField p)
            ((b : ℤ_[p]) • PadicMeasure.dirac p b - 1)
          * PowerSeries.constantCoeff (eisensteinFamily p hp2)
        = algebraMap _ _ ν →
      ((ν (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p]) : ℚ_[p])
        = ((b : ℚ_[p]) ^ k - 1) * ((stabilisedCoeff p k 0 : ℚ) : ℚ_[p]))
    ∧ ∀ n : ℕ, n ≠ 0 →
      PowerSeries.coeff n (eisensteinFamily p hp2)
          = algebraMap _ _ (divisorMeasure p n)
        ∧ ((divisorMeasure p n (PadicMeasure.unitsPowCM p (k - 1)) : ℤ_[p])
              : ℚ_[p])
          = ((stabilisedCoeff p k n : ℚ) : ℚ_[p]) := by
  refine ⟨fun b ν hν => ?_, fun n hn => ⟨?_, ?_⟩⟩
  · rw [show PowerSeries.constantCoeff (eisensteinFamily p hp2) = twistedZetaHalf p hp2 from rfl]
      at hν
    rw [twistedZetaHalf_moments p hp2 b hk ν hν, stabilisedCoeff, if_pos rfl]
    push_cast
    ring
  · rw [eisensteinFamily, PowerSeries.coeff_mk, if_neg hn]
  · rw [divisorMeasure_moment, stabilisedCoeff, if_neg hn]
    push_cast
    rfl

end family

end PadicLFunctions
