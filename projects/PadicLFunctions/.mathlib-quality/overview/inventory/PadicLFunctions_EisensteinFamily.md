# Inventory: PadicLFunctions/EisensteinFamily.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean`

File goal: the Part-I closer of the project — assembles the Λ-adic Eisenstein family `𝐄 = Σ Aₙ qⁿ ∈ Q(ℤ_p^×)⟦q⟧` with `A₀ = x·ζ_p/2` and `Aₙ = Σ_{0<d∣n, p∤d} δ_d`, and proves the coefficientwise interpolation `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for `k ≥ 4`. Implements decomposition replans R8.1 (corrected pseudo-measure claim, erratum #11) and R8.2 (x-twist as a ring automorphism via moments).

---

### theorem isUnit_two_padicInt
- Type: `(hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p])`
- What: For odd `p`, `2` is a unit in the p-adic integers `ℤ_[p]` (its p-adic valuation is `0`).
- How: Shows `p ∤ 2` (from `Nat.prime_dvd_prime_iff_eq` applied to the two primes `p` and `2`), then invokes the mathlib characterisation `PadicInt.isUnit_natCast_of_not_dvd`.
- Hypotheses: `p` prime (ambient `Fact p.Prime`), `p ≠ 2`.
- Uses from project: []
- Used by: `unitsTwist`? no — used by `twistedZetaHalf`, `twistedZetaHalf_witness_eq`, `coe_inv_two`, `twistedZetaHalf_moments`.
- Visibility: public
- Lines: 43–47 (proof 3 lines)
- Notes: none

### def unitOfNat
- Type: `(d : ℕ) : ℤ_[p]ˣ`
- What: The element of `ℤ_p^×` attached to a natural number `d` coprime to `p`; defined as `h.unit` when `(d : ℤ_[p])` is a unit, with junk value `1` otherwise.
- How: A `dite` on `IsUnit ((d : ℕ) : ℤ_[p])` returning the unit witness or `1`. `noncomputable`, `open Classical`.
- Hypotheses: none beyond ambient `p` prime.
- Uses from project: []
- Used by: `unitOfNat_coe`, `divisorMeasure`, `divisorMeasure_moment`.
- Visibility: public
- Lines: 49–54 (def, no proof)
- Notes: none

### theorem unitOfNat_coe
- Type: `{d : ℕ} (hd : ¬ (p : ℕ) ∣ d) : ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p])`
- What: When `p ∤ d`, the underlying p-adic integer of `unitOfNat p d` is exactly `(d : ℤ_[p])` (the junk branch is not taken).
- How: Unfolds `unitOfNat`, takes the positive `dif_pos` branch via `PadicInt.isUnit_natCast_of_not_dvd hd`, then `IsUnit.unit_spec`.
- Hypotheses: `p ∤ d`.
- Uses from project: [`unitOfNat`]
- Used by: `divisorMeasure_moment`.
- Visibility: public
- Lines: 56–58 (proof 1 line)
- Notes: none

### def sigmaP
- Type: `(k n : ℕ) : ℕ`
- What: The prime-to-`p` divisor power sum `σ^p_k(n) = Σ_{0<d∣n, p∤d} d^k` (RJW TeX 2393).
- How: A `Finset.sum` of `d ^ k` over `n.divisors` filtered to divisors not divisible by `p`.
- Hypotheses: none.
- Uses from project: []
- Used by: `divisorMeasure_moment`, `stabilisedCoeff`.
- Visibility: public
- Lines: 60–63 (def, no proof)
- Notes: none

### def divisorMeasure
- Type: `(n : ℕ) : PadicMeasure p ℤ_[p]ˣ`
- What: The divisor-sum measure `Aₙ = Σ_{0<d∣n, p∤d} δ_d ∈ Λ(ℤ_p^×)`; `A₀ = 0` (the empty sum). The higher coefficients of the Eisenstein family.
- How: A `Finset.sum` of Dirac measures `PadicMeasure.dirac p (unitOfNat p d)` over prime-to-`p` divisors of `n`. `noncomputable`.
- Hypotheses: none.
- Uses from project: [`unitOfNat`, `PadicMeasure.dirac`]
- Used by: `divisorMeasure_moment`, `eisensteinFamily`, `eisensteinFamily_interpolation`.
- Visibility: public
- Lines: 65–70 (def, no proof)
- Notes: none

### theorem divisorMeasure_moment
- Type: `(n k : ℕ) : divisorMeasure p n (PadicMeasure.unitsPowCM p k) = ((sigmaP p k n : ℕ) : ℤ_[p])`
- What: The `k`-th moment of the divisor measure equals the divisor power sum: `∫_{ℤ_p^×} x^k · Aₙ = σ^p_k(n)`, since each Dirac evaluates as `∫ x^k δ_d = d^k`.
- How: Distributes the linear-map evaluation over the sum (`LinearMap.coe_sum`, `Finset.sum_apply`), then per-summand uses `PadicMeasure.dirac_apply` and `unitOfNat_coe` to reduce `((unitOfNat p d)^k = (d^k : ℤ_[p])`; congruence of sums.
- Hypotheses: none.
- Uses from project: [`divisorMeasure`, `sigmaP`, `PadicMeasure.unitsPowCM`, `PadicMeasure.dirac_apply`, `unitOfNat`, `unitOfNat_coe`]
- Used by: `eisensteinFamily_interpolation`.
- Visibility: public
- Lines: 74–81 (proof 5 lines)
- Notes: none

### lemma unitsPowCM_one_mul_unitsPowCM
- Type: `(k : ℕ) : PadicMeasure.unitsPowCM p 1 * PadicMeasure.unitsPowCM p k = PadicMeasure.unitsPowCM p (k + 1)`
- What: In the algebra `C(ℤ_p^×, ℤ_[p])`, the power-character `x^1` times `x^k` is `x^{k+1}`.
- How: `ContinuousMap.ext`; unfolds `unitsPowCM`, `pow_one`, and `pow_succ'`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsPowCM`]
- Used by: `unitsCmul_powCM_one_moment`.
- Visibility: private
- Lines: 87–92 (proof 4 lines)
- Notes: none

### lemma invCM_mul_unitsPowCM_one
- Type: `PadicMeasure.invCM p * PadicMeasure.unitsPowCM p 1 = 1`
- What: The continuous "inverse" character `x⁻¹` times the identity character `x` is the constant `1` in `C(ℤ_p^×, ℤ_[p])`.
- How: `ContinuousMap.ext`; unfolds `invCM`/`unitsPowCM`, reduces to `inv_mul_cancel` on units (`Units.val_mul`, `Units.val_one`).
- Hypotheses: none.
- Uses from project: [`PadicMeasure.invCM`, `PadicMeasure.unitsPowCM`]
- Used by: `unitsPowCM_one_mul_invCM`, `unitsTwist` (right_inv).
- Visibility: private
- Lines: 94–99 (proof 4 lines)
- Notes: none

### lemma unitsPowCM_one_mul_invCM
- Type: `PadicMeasure.unitsPowCM p 1 * PadicMeasure.invCM p = 1`
- What: The commuted form: identity character `x` times inverse character `x⁻¹` is `1`.
- How: `mul_comm` then `invCM_mul_unitsPowCM_one`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsPowCM`, `PadicMeasure.invCM`]
- Used by: `unitsTwist` (left_inv).
- Visibility: private
- Lines: 101–103 (proof 1 line)
- Notes: none

### lemma unitsCmul_powCM_one_moment
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) : PadicMeasure.unitsCmul p (PadicMeasure.unitsPowCM p 1) μ (PadicMeasure.unitsPowCM p k) = μ (PadicMeasure.unitsPowCM p (k + 1))`
- What: Evaluating the `x`-scaled measure `unitsCmul x μ` against `x^k` shifts the moment up by one: it equals `μ(x^{k+1})`.
- How: `PadicMeasure.unitsCmul_apply` (which pulls the multiplier into the test function) then `unitsPowCM_one_mul_unitsPowCM`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.unitsPowCM`, `PadicMeasure.unitsCmul_apply`, `unitsPowCM_one_mul_unitsPowCM`]
- Used by: `unitsTwist` (map_mul'), `unitsTwist_moment`.
- Visibility: private
- Lines: 105–108 (proof 1 line)
- Notes: none

### def unitsTwist
- Type: `PadicMeasure p ℤ_[p]ˣ ≃+* PadicMeasure p ℤ_[p]ˣ` (RingEquiv)
- What: The x-twist `τ` on `Λ(ℤ_p^×)`, `(τμ)(f) = μ(x·f)` (on Diracs `[g] ↦ g·[g]`), realised as a **ring automorphism** of the convolution algebra; its inverse is the twist by `x⁻¹`.
- How: `toFun` = `unitsCmul (unitsPowCM 1)`, `invFun` = `unitsCmul invCM`. `left_inv`/`right_inv` collapse `unitsCmul ∘ unitsCmul` via `unitsCmul_apply` + `mul_assoc` + the inverse-character identities. The crux `map_mul'` is a moments argument: forms the difference `τ(μν) − τμ·τν`, applies `PadicMeasure.eq_zero_of_forall_unitsPowCM_eq_zero` (the zero-divisor / density lemma), and checks each `x^k`-moment vanishes via `PadicMeasure.units_mul_apply_unitsPowCM` and `unitsCmul_powCM_one_moment`. `noncomputable`.
- Hypotheses: none beyond ambient `p` prime.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.unitsPowCM`, `PadicMeasure.invCM`, `PadicMeasure.unitsCmul_apply`, `unitsPowCM_one_mul_invCM`, `invCM_mul_unitsPowCM_one`, `PadicMeasure.eq_zero_of_forall_unitsPowCM_eq_zero`, `PadicMeasure.units_mul_apply_unitsPowCM`, `unitsCmul_powCM_one_moment`]
- Used by: `unitsTwist_moment`, `unitsTwist_dirac`, `map_nonZeroDivisors_unitsTwist`, `quotientTwist`, `quotientTwist_algebraMap`, `twistedZetaHalf_witness_eq`, `twistedZetaHalf_moments`.
- Visibility: public
- Lines: 115–138 (bundled structure; longest field `map_mul'` ~8 lines)
- Notes: none (no single proof block >30; field-by-field)

### theorem unitsTwist_moment
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) : unitsTwist p μ (PadicMeasure.unitsPowCM p k) = μ (PadicMeasure.unitsPowCM p (k + 1))`
- What: The twist shifts all moments by one: `∫ x^k · (τμ) = ∫ x^{k+1} · μ`.
- How: Definitional: it is exactly `unitsCmul_powCM_one_moment`.
- Hypotheses: none.
- Uses from project: [`unitsTwist`, `PadicMeasure.unitsPowCM`, `unitsCmul_powCM_one_moment`]
- Used by: `twistedZetaHalf_moments`.
- Visibility: public
- Lines: 141–144 (term proof, 1 line)
- Notes: none

### theorem unitsCmul_dirac
- Type: `(φ : C(ℤ_[p]ˣ, ℤ_[p])) (g : ℤ_[p]ˣ) : PadicMeasure.unitsCmul p φ (PadicMeasure.dirac p g) = (φ g) • PadicMeasure.dirac p g`
- What: Multiplying a Dirac measure `δ_g` by a continuous function `φ` rescales it by the value `φ(g)`: `φ · δ_g = φ(g) · δ_g`.
- How: `LinearMap.ext`; unfolds `unitsCmul_apply`, `dirac_apply` (both sides), `ContinuousMap.mul_apply`, `smul_eq_mul`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.dirac`, `PadicMeasure.unitsCmul_apply`, `PadicMeasure.dirac_apply`]
- Used by: `unitsTwist_dirac`.
- Visibility: public
- Lines: 149–154 (proof 2 lines)
- Notes: none

### theorem unitsTwist_dirac
- Type: `(g : ℤ_[p]ˣ) : unitsTwist p (PadicMeasure.dirac p g) = (g : ℤ_[p]) • PadicMeasure.dirac p g`
- What: The x-twist sends a Dirac to a scaled Dirac: `τ(δ_g) = g·δ_g`.
- How: Rewrites `unitsTwist` to its `unitsCmul (unitsPowCM 1)` form (`from rfl`), applies `unitsCmul_dirac`, then `congr 1` + `simp [unitsPowCM]` to identify `(unitsPowCM 1) g = (g : ℤ_[p])`.
- Hypotheses: none.
- Uses from project: [`unitsTwist`, `PadicMeasure.dirac`, `PadicMeasure.unitsCmul`, `PadicMeasure.unitsPowCM`, `unitsCmul_dirac`]
- Used by: `twistedZetaHalf_witness_eq`.
- Visibility: public
- Lines: 157–164 (proof 5 lines)
- Notes: none

### theorem map_nonZeroDivisors_unitsTwist
- Type: `(nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)).map (unitsTwist p).toMonoidHom = nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)`
- What: A ring automorphism maps the non-zero-divisor submonoid onto itself.
- How: Term proof: `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`.
- Hypotheses: none.
- Uses from project: [`unitsTwist`]
- Used by: `quotientTwist`.
- Visibility: public
- Lines: 168–172 (term proof, 1 line)
- Notes: none

### def quotientTwist
- Type: `PadicMeasure.QuotientField p ≃+* PadicMeasure.QuotientField p` (RingEquiv)
- What: The x-twist extended from `Λ(ℤ_p^×)` to its total fraction ring `Q(ℤ_p^×)`.
- How: `IsLocalization.ringEquivOfRingEquiv` applied to `unitsTwist` and the non-zero-divisor compatibility `map_nonZeroDivisors_unitsTwist`. `noncomputable`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.QuotientField`, `unitsTwist`, `map_nonZeroDivisors_unitsTwist`]
- Used by: `quotientTwist_algebraMap`, `twistedZetaHalf`, `twistedZetaHalf_witness_eq`.
- Visibility: public
- Lines: 175–179 (def, no proof body)
- Notes: none

### theorem quotientTwist_algebraMap
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) : quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p) μ) = algebraMap _ _ (unitsTwist p μ)`
- What: The extended twist restricts to the measure-twist: it commutes with the localisation `algebraMap` from `Λ` into `Q`.
- How: Term proof: `IsLocalization.ringEquivOfRingEquiv_eq _ μ`.
- Hypotheses: none.
- Uses from project: [`quotientTwist`, `PadicMeasure.QuotientField`, `unitsTwist`]
- Used by: `twistedZetaHalf_witness_eq`.
- Visibility: public
- Lines: 182–185 (term proof, 1 line)
- Notes: none

### def twistedZetaHalf
- Type: `(hp2 : p ≠ 2) : PadicMeasure.QuotientField p`
- What: The constant coefficient `A₀ = x·ζ_p/2` of the Eisenstein family — the x-twist of the Kubota–Leopoldt pseudo-measure `padicZeta`, scaled by `2⁻¹` (`2` a unit for odd `p`).
- How: `algebraMap` of `(2⁻¹ • 1)` (using `isUnit_two_padicInt`) times `quotientTwist (padicZeta p hp2)`. `noncomputable`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.QuotientField`, `isUnit_two_padicInt`, `quotientTwist`, `PadicMeasure.padicZeta`]
- Used by: `twistedZetaHalf_witness_eq`, `twistedZetaHalf_isTwistedPseudoMeasure`, `twistedZetaHalf_moments`, `eisensteinFamily`.
- Visibility: public
- Lines: 191–198 (def, no proof body)
- Notes: none

### lemma smul_one_mul'
- Type: `(c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) : (c • (1 : PadicMeasure p ℤ_[p]ˣ)) * μ = c • μ`
- What: In the convolution algebra, `(c • 1) * μ = c • μ` — scalar-times-unit absorbs into a scalar action.
- How: Proves intermediate `(c • 1) * μ = c • (1 * μ)` via `LinearMap.ext` + `PadicMeasure.units_mul_apply` + `LinearMap.smul_apply`, then `one_mul`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.units_mul_apply`]
- Used by: `twistedZetaHalf_witness_eq`.
- Visibility: private
- Lines: 200–207 (proof 6 lines)
- Notes: none

### lemma coe_inv_two
- Type: `(hp2 : p ≠ 2) : ((((isUnit_two_padicInt p hp2).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p])⁻¹`
- What: The image in `ℚ_[p]` of the p-adic-integer inverse of `2` equals the rational `2⁻¹`.
- How: Sets `u` = the unit of `2`, uses `IsUnit.unit_spec` (`u = 2`), derives `2 * u⁻¹ = 1` in `ℤ_[p]` (`mul_inv_cancel`), casts to `ℚ_[p]` (`push_cast`, `norm_cast`), concludes via `eq_inv_of_mul_eq_one_left`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`isUnit_two_padicInt`]
- Used by: `twistedZetaHalf_moments`.
- Visibility: private
- Lines: 209–220 (proof 10 lines)
- Notes: none

### lemma twistedZetaHalf_witness_eq
- Type: `(hp2 : p ≠ 2) (g : ℤ_[p]ˣ) (νg : PadicMeasure p ℤ_[p]ˣ) (hνg : algebraMap _ _ (dirac p g − 1) * padicZeta p hp2 = algebraMap _ _ νg) : algebraMap _ _ ((g:ℤ_[p])•dirac p g − 1) * twistedZetaHalf p hp2 = algebraMap _ _ (2⁻¹ • unitsTwist p νg)`
- What: Transports a pseudo-measure witness `νg` for `(g·[g]−[1])·ζ_p` (untwisted, written `(δ_g−1)·padicZeta = νg`) into the twisted witness for `A₀`: `(g·δ_g−1)·twistedZetaHalf = 2⁻¹·τ(νg)`.
- How: Key step `hkey`: `(g:ℤ_[p])•δ_g − 1 = unitsTwist (δ_g − 1)` via `map_sub` + `unitsTwist_dirac` + `map_one`. Applies `quotientTwist` to the hypothesis (`hc`), pushing through `map_mul` + `quotientTwist_algebraMap` twice. Then unfolds `twistedZetaHalf`, reassociates the product with `ring`, substitutes `hc`, and finishes with `← map_mul` + `smul_one_mul'`.
- Hypotheses: `p ≠ 2`; `g : ℤ_[p]ˣ`; `νg` is a pseudo-measure witness for `(δ_g − 1)·padicZeta`.
- Uses from project: [`PadicMeasure.dirac`, `PadicMeasure.padicZeta`, `twistedZetaHalf`, `unitsTwist`, `isUnit_two_padicInt`, `unitsTwist_dirac`, `quotientTwist`, `quotientTwist_algebraMap`, `smul_one_mul'`, `PadicMeasure.QuotientField`]
- Used by: `twistedZetaHalf_isTwistedPseudoMeasure`, `twistedZetaHalf_moments`.
- Visibility: private
- Lines: 222–246 (proof ~16 lines)
- Notes: none

### theorem twistedZetaHalf_isTwistedPseudoMeasure
- Type: `(hp2 : p ≠ 2) (g : ℤ_[p]ˣ) : ∃ ν : PadicMeasure p ℤ_[p]ˣ, algebraMap _ _ ((g:ℤ_[p])•dirac p g − 1) * twistedZetaHalf p hp2 = algebraMap _ _ ν`
- What: **Erratum #11 / replan R8.1**: the corrected form of RJW TeX 2403(a). `A₀` is NOT a pseudo-measure (its pole sits at character `x⁻¹`); what holds is the x-twisted analogue `(g·[g] − [1])·A₀ ∈ Λ(ℤ_p^×)` for every `g`.
- How: Obtains a pseudo-measure witness `νg` for `padicZeta` from `PadicMeasure.padicZeta_isPseudoMeasure`, then feeds it through `twistedZetaHalf_witness_eq` to exhibit the required `ν = 2⁻¹·τ(νg)`.
- Hypotheses: `p ≠ 2`; arbitrary `g : ℤ_[p]ˣ`.
- Uses from project: [`PadicMeasure.dirac`, `twistedZetaHalf`, `PadicMeasure.padicZeta_isPseudoMeasure`, `twistedZetaHalf_witness_eq`, `PadicMeasure.QuotientField`]
- Used by: unused in file
- Visibility: public
- Lines: 254–260 (proof 2 lines)
- Notes: none

### theorem twistedZetaHalf_moments
- Type: `(hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : 4 ≤ k) (ν : ...) (hν : algebraMap _ _ ((b:ℤ_[p])•dirac p b − 1) * twistedZetaHalf p hp2 = algebraMap _ _ ν) : ((ν (unitsPowCM p (k−1)) : ℤ_[p]) : ℚ_[p]) = ((b:ℚ_[p])^k − 1) * (1 − (p:ℚ_[p])^(k−1)) * ((zetaNeg (k−1) : ℚ) : ℚ_[p]) / 2`
- What: RJW TeX 2412: any pseudo-measure witness `ν` of `(b·[b]−[1])·A₀ ∈ Λ` has `(k−1)`-th moment `(b^k−1)·(1−p^{k−1})·ζ(1−k)/2` — the constant coefficient of `E_k^{(p)}` scaled by the twisted-denominator factor `b^k−1`.
- How: Gets a `padicZeta` witness `νb`; identifies `ν = 2⁻¹ • τ(νb)` by `IsFractionRing.injective` against `twistedZetaHalf_witness_eq`. Computes the moment: `LinearMap.smul_apply` + `unitsTwist_moment` (shifts `k−1` to `k`, via `Nat.sub_add_cancel`), then `coe_inv_two` and the project's `PadicMeasure.padicZeta_moments`, finishing with `field_simp`.
- Hypotheses: `p ≠ 2`; `k ≥ 4`; `ν` a witness of `(b·δ_b−1)·twistedZetaHalf`.
- Uses from project: [`PadicMeasure.dirac`, `twistedZetaHalf`, `PadicMeasure.unitsPowCM`, `zetaNeg`, `PadicMeasure.padicZeta_isPseudoMeasure`, `isUnit_two_padicInt`, `unitsTwist`, `twistedZetaHalf_witness_eq`, `unitsTwist_moment`, `PadicMeasure.padicZeta_moments`, `PadicMeasure.QuotientField`]
- Used by: `eisensteinFamily_interpolation`.
- Visibility: public
- Lines: 267–286 (proof ~12 lines)
- Notes: none

### lemma units_pow_totient_sq_sub_self_mem
- Type: `(u : ℤ_[p]ˣ) : ((u : ℤ_[p]) ^ (1 + Nat.totient (p ^ 2)) − (u : ℤ_[p])) ∈ (Ideal.span {(p : ℤ_[p]) ^ 2} : Ideal ℤ_[p])`
- What: For any unit `u`, `u^{1+φ(p²)} ≡ u (mod p²)` — a congruence at level `p²` from Euler/Lagrange in `(ZMod p²)ˣ`.
- How: Uses `ZMod.card_units_eq_totient` and `pow_card_eq_one'` to get `(unitsToZModPow u)^{φ(p²)} = 1`, transfers to `u^{φ(p²)} − 1 ∈ span{p²}` via `PadicInt.ker_toZModPow` + `unitsToZModPow_coe`, then factors `u^{1+φ(p²)} − u = u·(u^{φ(p²)} − 1)` (`pow_succ'`) and applies `Ideal.mul_mem_left`.
- Hypotheses: none beyond ambient `p` prime (uses `NeZero (p^2)`).
- Uses from project: [`PadicMeasure.unitsToZModPow`, `PadicMeasure.unitsToZModPow_coe`]
- Used by: `noMeasure_interpolates_pPow`.
- Visibility: private
- Lines: 288–305 (proof ~15 lines)
- Notes: none

### theorem noMeasure_interpolates_pPow
- Type: `¬ ∃ θ : PadicMeasure p ℤ_[p]ˣ, ∀ k : ℕ, 0 < k → θ (PadicMeasure.unitsPowCM p k) = (p : ℤ_[p]) ^ k`
- What: RJW TeX 2379–2383: the function `k ↦ p^k` can **never** be interpolated by a measure on `ℤ_p^×`. (Notably `p = 2` is allowed — no `hp2`.)
- How: Finitary route (ticket T804). Assuming such `θ`, sets `K = 1+φ(p²)`; bounds the sup-norm `‖x^K − x^1‖ ≤ p^{-2}` via `ContinuousMap.norm_le` + `PadicInt.norm_le_pow_iff_mem_span_pow` + `units_pow_totient_sq_sub_self_mem`. Boundedness of `θ` (`PadicMeasure.norm_apply_le`) forces `‖p^K − p‖ ≤ p^{-2}`. But `‖p^K − p‖ = ‖p‖·‖p^{K−1}−1‖ = p^{-1}` (the second factor has norm `1` by `PadicInt.norm_add_eq_max_of_ne`, ultrametric isoceles, since `‖p^{K−1}‖ < 1`), and `p^{-1} ≤ p^{-2}` is impossible (`zpow_le_zpow_iff_right₀` then `omega`).
- Hypotheses: none beyond ambient `p` prime (works for `p = 2`).
- Uses from project: [`PadicMeasure.unitsPowCM`, `units_pow_totient_sq_sub_self_mem`, `PadicMeasure.norm_apply_le`]
- Used by: unused in file
- Visibility: public
- Lines: 316–358 (proof ~42 lines)
- Notes: **long(30-50)** (~42-line proof; candidate for /decompose-proof). No sorry/set_option.

### def stabilisedCoeff
- Type: `(k : ℕ) : ℕ → ℚ`
- What: The rational coefficient sequence of the p-stabilised Eisenstein series `E_k^{(p)}`: constant term `(1−p^{k−1})·ζ(1−k)/2`, `n`-th term `σ^p_{k−1}(n)`. The pivot between the p-adic family and the complex q-expansion.
- How: A function `fun n => if n = 0 then (1 − p^{k−1})·zetaNeg(k−1)/2 else (sigmaP p (k−1) n : ℚ)`.
- Hypotheses: none.
- Uses from project: [`zetaNeg`, `sigmaP`]
- Used by: `eisensteinFamily_interpolation`.
- Visibility: public
- Lines: 365–367 (def, no proof)
- Notes: none

### def eisensteinFamily
- Type: `(hp2 : p ≠ 2) : PowerSeries (PadicMeasure.QuotientField p)`
- What: The Λ-adic Eisenstein family `𝐄 = Σ_{n≥0} Aₙ qⁿ ∈ Q(ℤ_p^×)⟦q⟧`: constant coefficient `A₀ = x·ζ_p/2` (`twistedZetaHalf`), higher coefficients the divisor-sum measures `Aₙ` (`divisorMeasure`, mapped into `Q`).
- How: `PowerSeries.mk` of `fun n => if n = 0 then twistedZetaHalf else algebraMap _ _ (divisorMeasure p n)`. `noncomputable`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.QuotientField`, `twistedZetaHalf`, `divisorMeasure`]
- Used by: `eisensteinFamily_interpolation`.
- Visibility: public
- Lines: 372–376 (def, no proof)
- Notes: none

### theorem eisensteinFamily_interpolation
- Type: `(hp2 : p ≠ 2) {k : ℕ} (hk : 4 ≤ k) :` (conjunction) constant-coefficient witness moment `= (b^k−1)·stabilisedCoeff p k 0`, AND for all `n ≠ 0` the coefficient is `algebraMap (divisorMeasure p n)` and its `(k−1)`-moment in `ℚ_[p]` equals `stabilisedCoeff p k n`.
- What: **RJW §8 main theorem (TeX 2399–2407), p-adic half**: the coefficientwise interpolation `∫_{ℤ_p^×} x^{k−1}·𝐄 = E_k^{(p)}` for `k ≥ 4`. The `n`-th moment of the family equals `stabilisedCoeff p k n`, the constant coefficient given in the pseudo-measure witness encoding. (Evenness of `k` not needed on the p-adic side.)
- How: Splits into three goals. Constant: rewrites `constantCoeff (eisensteinFamily) = twistedZetaHalf`, applies `twistedZetaHalf_moments`, unfolds `stabilisedCoeff` at `0`, then `push_cast`/`ring`. Higher coefficient identity: `eisensteinFamily` + `PowerSeries.coeff_mk` + `if_neg`. Higher moment: `divisorMeasure_moment` + `stabilisedCoeff` at `n` + `push_cast`/`rfl`.
- Hypotheses: `p ≠ 2`; `k ≥ 4`.
- Uses from project: [`PadicMeasure.dirac`, `PadicMeasure.QuotientField`, `eisensteinFamily`, `PadicMeasure.unitsPowCM`, `stabilisedCoeff`, `divisorMeasure`, `twistedZetaHalf`, `twistedZetaHalf_moments`, `divisorMeasure_moment`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 386–409 (proof ~10 lines)
- Notes: none

---

## File Summary

- **Total declarations: 24** — defs: **7** (`unitOfNat`, `sigmaP`, `divisorMeasure`, `unitsTwist`*, `quotientTwist`, `twistedZetaHalf`, `stabilisedCoeff`, `eisensteinFamily` → 8 if `unitsTwist`/`quotientTwist` RingEquivs counted as defs; counting `def`+`noncomputable def`+RingEquiv-`def`: **8**), lemmas+theorems: **15**, instances: **0**, structures/classes/abbrevs/inductives: **0**.
  - Precise breakdown by keyword: `def`/`noncomputable def` = **8** (`unitOfNat`, `sigmaP`, `divisorMeasure`, `unitsTwist`, `quotientTwist`, `twistedZetaHalf`, `stabilisedCoeff`, `eisensteinFamily`); `theorem` = **11**; `lemma` (all `private`) = **5**. Total **24**.
- **Key API (used by ≥3 in-file):**
  - `unitsTwist` — used by ≥7 (`unitsTwist_moment`, `unitsTwist_dirac`, `map_nonZeroDivisors_unitsTwist`, `quotientTwist`, `quotientTwist_algebraMap`, `twistedZetaHalf_witness_eq`, `twistedZetaHalf_moments`).
  - `twistedZetaHalf` — used by ≥4 (`twistedZetaHalf_witness_eq`, `twistedZetaHalf_isTwistedPseudoMeasure`, `twistedZetaHalf_moments`, `eisensteinFamily`).
  - `isUnit_two_padicInt` — used by 4 (`twistedZetaHalf`, `twistedZetaHalf_witness_eq`, `coe_inv_two`, `twistedZetaHalf_moments`).
  - `twistedZetaHalf_witness_eq` — used by 3 (incl. itself's consumers: `twistedZetaHalf_isTwistedPseudoMeasure`, `twistedZetaHalf_moments`; 2 in-file) — borderline.
  - `quotientTwist` — used by 3 (`quotientTwist_algebraMap`, `twistedZetaHalf`, `twistedZetaHalf_witness_eq`).
- **Unused in file (top-level / terminal results):** `twistedZetaHalf_isTwistedPseudoMeasure`, `noMeasure_interpolates_pPow`, `eisensteinFamily_interpolation` (these are the file's public deliverables / exported theorems — expected to be consumed by `EisensteinComplex.lean` or downstream, not within this file).
- **Declarations with `sorry`: NONE.**
- **`set_option`: NONE.** No `TODO` markers (there is an `errata.md` reference and a `replan` note, not code TODOs).
- **Proofs >50 lines (OVER-50): 0.**
- **Proofs 30–50 lines: 1** — `noMeasure_interpolates_pPow` (~42 lines, 316–358) → flagged **long(30-50)**, candidate for `/decompose-proof`.

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_EisensteinFamily.md`
