# Inventory: PadicLFunctions/KubotaLeopoldt/ZetaP.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/ZetaP.lean`

Namespace: `PadicMeasure`. Variables: `(p : ℕ) [hp : Fact p.Prime]`. `noncomputable section`, `open PowerSeries`.

Builds the Kubota–Leopoldt p-adic L-function (RJW §4.3, Thm. 4.1): restricts `μ_a` to `ℤ_p^×`, rescales by `x⁻¹`, divides by `[a]−[1]`, and proves the interpolation + uniqueness theorem.

---

### def muAUnits
- Type: `def muAUnits (a : ℕ) : PadicMeasure p ℤ_[p]ˣ := (muA p a).comp (extendByZero p)`
- What: The restriction of the measure `μ_a` to `ℤ_p^×`, realised as a measure on `ℤ_p^×` by precomposing `μ_a` with extension-by-zero of functions on `ℤ_p^×` to functions on `ℤ_p`.
- How: Direct definition — composition of the linear functional `muA p a` with the extend-by-zero map `extendByZero p`.
- Hypotheses: `a : ℕ`.
- Uses from project: [`muA`, `PadicMeasure`, `extendByZero`]
- Used by: `iota_muAUnits`, `muAUnits_apply_unitsPowCM`, `zetaNum`, `zetaNum_apply_unitsPowCM`
- Visibility: public
- Lines: 31–35 (def, no proof)
- Notes: none

### lemma iota_muAUnits
- Type: `iota p (muAUnits p a) = res p (isClopen_units p) (muA p a)`
- What: Embedding `muAUnits p a` back into measures on `ℤ_p` (via `iota`) recovers the restriction `Res_{ℤ_p^×}(μ_a)` of `μ_a` to the clopen subset `ℤ_p^×`.
- How: `LinearMap.ext`; unfolds both sides to applications of `muA p a` via `change`, then rewrites with `extendByZero_comp_unitsVal` to identify `extendByZero (f ∘ unitsVal)` with multiplication by the characteristic function of the units.
- Hypotheses: `a : ℕ`.
- Uses from project: [`iota`, `muAUnits`, `res`, `isClopen_units`, `muA`, `extendByZero`, `unitsValCM`, `extendByZero_comp_unitsVal`]
- Used by: unused in file
- Visibility: public
- Lines: 37–42 (proof ~5 lines)
- Notes: none

### lemma muAUnits_apply_unitsPowCM
- Type: `muAUnits p a (unitsPowCM p k) = res p (isClopen_units p) (muA p a) (powCM p k)`
- What: Evaluating `muAUnits p a` at the `k`-th power monomial `x^k` on the units equals evaluating the restricted measure `Res_{ℤ_p^×}(μ_a)` at the monomial `x^k` on `ℤ_p`.
- How: Rewrites both sides via `change` to applications of `muA p a`, identifies `unitsPowCM p k` with `(powCM p k) ∘ unitsValCM` (pointwise `rfl` via `ContinuousMap.ext`), then applies `extendByZero_comp_unitsVal`.
- Hypotheses: `a k : ℕ`.
- Uses from project: [`muAUnits`, `res`, `isClopen_units`, `muA`, `powCM`, `unitsPowCM`, `unitsValCM`, `extendByZero_comp_unitsVal`]
- Used by: `zetaNum_moments`
- Visibility: public
- Lines: 44–52 (proof ~7 lines)
- Notes: none

### lemma continuous_units_inv_val
- Type: `Continuous fun u : ℤ_[p]ˣ => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])`
- What: The map sending a unit `u` of `ℤ_p` to the underlying ring element of its inverse `u⁻¹` is continuous.
- How: Realises `u ↦ (u⁻¹ : ℤ_[p])` as a composition: `Units.continuous_embedProduct` (continuity of the embedding into `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`), second projection, and `MulOpposite.continuous_unop`.
- Hypotheses: none beyond `p` prime.
- Uses from project: []
- Used by: `invCM`
- Visibility: public
- Lines: 54–56 (proof 1 line)
- Notes: none

### def invCM
- Type: `def invCM : C(ℤ_[p]ˣ, ℤ_[p]) := ⟨_, continuous_units_inv_val p⟩`
- What: The continuous function `x ↦ x⁻¹` on `ℤ_p^×` valued in `ℤ_p`, packaged as a bundled continuous map.
- How: Bundles the underlying function with the continuity proof `continuous_units_inv_val`.
- Hypotheses: none beyond `p` prime.
- Uses from project: [`continuous_units_inv_val`]
- Used by: `zetaNum`, `zetaNum_apply_unitsPowCM`
- Visibility: public
- Lines: 58–60 (def, no proof)
- Notes: none

### def unitsCmul
- Type: `def unitsCmul (g : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure p ℤ_[p]ˣ := μ.comp (LinearMap.mulLeft ℤ_[p] g)`
- What: Multiplication of a measure on `ℤ_p^×` by a continuous function `g` — the units analogue of `cmul` — defined so that `∫ f · (g·μ) = ∫ (g·f) · μ` (RJW eq. 4.11).
- How: Composes the measure `μ` with the left-multiplication-by-`g` linear map on continuous functions.
- Hypotheses: `g` a continuous map `ℤ_p^× → ℤ_p`; `μ` a measure on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`]
- Used by: `unitsCmul_apply`, `zetaNum`
- Visibility: public
- Lines: 62–66 (def, no proof)
- Notes: none

### lemma unitsCmul_apply
- Type: `@[simp] unitsCmul p g μ f = μ (g * f)`
- What: Evaluating `unitsCmul p g μ` at a continuous function `f` equals evaluating `μ` at the product `g * f`.
- How: Definitional unfolding (`rfl`).
- Hypotheses: `g f` continuous maps `ℤ_p^× → ℤ_p`; `μ` a measure on `ℤ_p^×`.
- Uses from project: [`unitsCmul`, `PadicMeasure`]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 68–70 (proof: `rfl`)
- Notes: none

### def zetaNum
- Type: `def zetaNum (a : ℕ) : PadicMeasure p ℤ_[p]ˣ := unitsCmul p (invCM p) (muAUnits p a)`
- What: The numerator `x⁻¹ · Res_{ℤ_p^×}(μ_a)` of the p-adic zeta function (RJW Def. 4.10).
- How: Applies `unitsCmul` with the inversion map `invCM` to `muAUnits p a`.
- Hypotheses: `a : ℕ`.
- Uses from project: [`PadicMeasure`, `unitsCmul`, `invCM`, `muAUnits`]
- Used by: `zetaNum_apply_unitsPowCM`, `zetaNum_moments`, `padicZeta`, `padicZeta_moments`
- Visibility: public
- Lines: 72–75 (def, no proof)
- Notes: none

### lemma zetaNum_apply_unitsPowCM
- Type: `zetaNum p a (unitsPowCM p k) = muAUnits p a (unitsPowCM p (k - 1))` (for `0 < k`)
- What: Evaluating the numerator measure at the monomial `x^k` (with `k > 0`) equals evaluating `muAUnits p a` at the monomial `x^{k-1}` — the `x⁻¹` factor lowers the exponent by one.
- How: Writes `k = k'+1`; reduces to `muAUnits p a (invCM * x^{k'+1}) = muAUnits p a (x^{k'})` by `congr`/`ext`; pointwise on a unit `u` proves `u⁻¹ · u^{k'+1} = u^{k'}` via a `calc` using `ring` and `inv_mul_cancel` (`Units.val_mul`).
- Hypotheses: `0 < k`.
- Uses from project: [`zetaNum`, `muAUnits`, `unitsPowCM`, `invCM`]
- Used by: `zetaNum_moments`
- Visibility: public
- Lines: 77–87 (proof ~9 lines)
- Notes: none

### theorem zetaNum_moments
- Type: `((zetaNum p a (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = (-1)^k * ((a:ℚ_[p])^k - 1) * (1 - (p:ℚ_[p])^(k-1)) * ((zetaNeg (k-1) : ℚ) : ℚ_[p])` (for `¬ p ∣ a`, `0 < k`)
- What: The `k`-th moment of the numerator measure (RJW TeX line 1561): `∫_{ℤ_p^×} x^k · x⁻¹μ_a = (−1)^k (a^k−1)(1−p^{k−1}) ζ(1−k)`.
- How: Writes `k = k'+1`; rewrites via `zetaNum_apply_unitsPowCM`, `muAUnits_apply_unitsPowCM`, then the key restricted-measure moment formula `res_units_muA_apply_powCM`, expands `pow_succ`, and closes with `ring`.
- Hypotheses: `a : ℕ` with `p ∤ a`; `0 < k`.
- Uses from project: [`zetaNum`, `unitsPowCM`, `zetaNeg`, `zetaNum_apply_unitsPowCM`, `muAUnits_apply_unitsPowCM`, `res_units_muA_apply_powCM`]
- Used by: `padicZeta_moments`
- Visibility: public
- Lines: 89–98 (proof ~4 lines)
- Notes: none

### theorem topGen_pow_ne_one
- Type: `∀ k, 0 < k → (a : ℤ_[p])^k ≠ 1` given `∀ n, Subgroup.zpowers (unitsToZModPow p n a) = ⊤`
- What: A topological generator `a` of `ℤ_p^×` is torsion-free: no positive power of `a` equals `1`, because the order of its image in `(ℤ/p^n)^×` grows without bound.
- How: Suppose `a^k = 1`; then in `(ℤ/p^{k+1})^×` the image has order `= card = totient(p^{k+1}) = p^k(p−1)` (`orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient`, `Nat.totient_prime_pow`), yet `orderOf ∣ k` (`orderOf_dvd_of_pow_eq_one`), giving `card ≤ k`; contradiction via `k < 2^k ≤ p^k ≤ p^k(p−1)` and `omega`.
- Hypotheses: `a : ℤ_[p]ˣ` whose image generates `(ℤ/p^n)^×` for every `n`.
- Uses from project: [`unitsToZModPow`]
- Used by: `padicZeta`, `padicZeta_moments`, `kubotaLeopoldt`
- Visibility: public
- Lines: 100–118 (proof ~15 lines)
- Notes: hinges on `orderOf_eq_card_of_forall_mem_zpowers`, `Nat.totient_prime_pow`, `orderOf_dvd_of_pow_eq_one`. none (under 30)

### theorem exists_nat_topological_generator
- Type: `∃ (m : ℕ) (u : ℤ_[p]ˣ), ¬ p ∣ m ∧ (u : ℤ_[p]) = (m : ℤ_[p]) ∧ ∀ n, Subgroup.zpowers (unitsToZModPow p n u) = ⊤` (for `p ≠ 2`)
- What: For odd `p` there is an integer `m` (with `p ∤ m`) whose associated unit `u` of `ℤ_p` is a topological generator of `ℤ_p^×` — an integer that is a primitive root mod `p²` generates `(ℤ/p^n)^×` for every `n`.
- How: Takes an abstract generator `u₀` (`exists_topological_generator`), sets `m :=` the `ZMod`-value of its image mod `p²`; proves `p ∤ m` (unit argument); lifts `m` to a unit via `PadicInt.isUnit_natCast_of_not_dvd`. Establishes generation at level 2 (matching `u₀`), pushes down via the surjective `ZMod.unitsMap`. For levels `n ≥ 3`: combines a `(p−1)`-part (from level 1) and a `p^{n'}`-part — the latter from `ZMod.orderOf_one_add_mul_prime` applied to `m^{p−1} = 1 + p·c` (Fermat, with `p ∤ c` proved by a mod-`p²` order argument) — and coprimality (`Nat.Coprime.mul_dvd_of_dvd_of_dvd`) to force `orderOf g = card`, hence `⊤` (`Subgroup.eq_top_of_card_eq`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`exists_topological_generator`, `unitsToZModPow`, `unitsToZModPow_coe`, `unitsToZModPow_le`]
- Used by: `padicZeta`, `padicZeta_moments`, `kubotaLeopoldt`
- Visibility: public
- Lines: 120–247 (proof OVER-50, ~120 lines)
- Notes: **OVER-50** (needs /decompose-proof). `classical`. Hinges on `ZMod.orderOf_one_add_mul_prime`, `ZMod.pow_card_sub_one_eq_one` (Fermat), `ZMod.unitsMap_surjective`, `Subgroup.eq_top_of_card_eq`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.

### def padicZeta
- Type: `def padicZeta (hp2 : p ≠ 2) : QuotientField p := IsLocalization.mk' (QuotientField p) (zetaNum p (…).choose) ⟨dirac p (…).choose_spec.choose - 1, dirac_sub_one_mem_nonZeroDivisors p (topGen_pow_ne_one p …)⟩`
- What: RJW Def. 4.10: the p-adic zeta function `ζ_p = (x⁻¹ Res_{ℤ_p^×} μ_a)/([a]−[1]) ∈ Q(ℤ_p^×)`, for a chosen integer topological generator `a` of `ℤ_p^×`.
- How: Forms the localization fraction `IsLocalization.mk'` with numerator `zetaNum p m` and denominator `[a]−[1]` (a `dirac` minus one); the denominator is a non-zero-divisor by `dirac_sub_one_mem_nonZeroDivisors` together with torsion-freeness `topGen_pow_ne_one`. The generator data comes from `exists_nat_topological_generator`'s `.choose`/`.choose_spec`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`QuotientField`, `zetaNum`, `exists_nat_topological_generator`, `dirac`, `dirac_sub_one_mem_nonZeroDivisors`, `topGen_pow_ne_one`]
- Used by: `padicZeta_isPseudoMeasure`, `padicZeta_moments`, `kubotaLeopoldt`
- Visibility: public
- Lines: 249–258 (def, no tactic proof)
- Notes: none

### lemma IsPseudoMeasure.sub
- Type: `IsPseudoMeasure p q₁ → IsPseudoMeasure p q₂ → IsPseudoMeasure p (q₁ - q₂)`
- What: The pseudo-measure property is closed under subtraction: if `q₁` and `q₂` are pseudo-measures, so is `q₁ - q₂`.
- How: Given a continuous `g`, takes witnesses `ν₁`, `ν₂` for `q₁`, `q₂` and produces `ν₁ - ν₂` as the witness for `q₁ - q₂`, using `mul_sub` and `map_sub`.
- Hypotheses: `q₁ q₂ : QuotientField p` both pseudo-measures.
- Uses from project: [`IsPseudoMeasure`, `QuotientField`]
- Used by: `kubotaLeopoldt`
- Visibility: public
- Lines: 260–266 (proof ~5 lines)
- Notes: none

### theorem padicZeta_isPseudoMeasure
- Type: `IsPseudoMeasure p (padicZeta p hp2)` (for `p ≠ 2`)
- What: RJW Prop. 4.11 (first half): the p-adic zeta function `ζ_p` is a pseudo-measure.
- How: Direct application of the general criterion `isPseudoMeasure_mk'` to the localization fraction, feeding it the topological-generator property from `exists_nat_topological_generator`'s choice data.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`IsPseudoMeasure`, `padicZeta`, `isPseudoMeasure_mk'`, `exists_nat_topological_generator`]
- Used by: `kubotaLeopoldt`
- Visibility: public
- Lines: 268–272 (proof ~2 lines)
- Notes: none

### theorem padicZeta_moments
- Type: `((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p]) = ((b:ℚ_[p])^k - 1) * (1 - (p:ℚ_[p])^(k-1)) * ((zetaNeg (k-1) : ℚ) : ℚ_[p])` given `0 < k` and a witness `ν` of `([b]−[1])·ζ_p`
- What: RJW Prop. 4.11 (interpolation): every measure `ν` witnessing `([b]−[1])·ζ_p ∈ Λ(ℤ_p^×)` has `k`-th moment `(b^k−1)(1−p^{k−1}) ζ(1−k)` — i.e. `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)`.
- How: From `IsLocalization.mk'_spec'` gets `([u]−[1])·ζ_p = zetaNum p m` (image), then by `IsFractionRing.injective` lifts `hν` to the measure identity `([u]−[1])·ν = ([b]−[1])·zetaNum p m`; applies the `k`-th moment functional (`units_mul_apply_unitsPowCM`, `dirac` moments, `units_one_def`), substitutes `zetaNum_moments`, and closes by `mul_left_cancel₀` (using `topGen_pow_ne_one` for `(u^k−1)≠0`) and `linear_combination` against `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`.
- Hypotheses: `p ≠ 2`; `b : ℤ_[p]ˣ`; `0 < k`; `ν` satisfying `algebraMap (dirac p b − 1) · padicZeta = algebraMap ν`.
- Uses from project: [`PadicMeasure`, `QuotientField`, `padicZeta`, `dirac`, `unitsPowCM`, `zetaNeg`, `exists_nat_topological_generator`, `zetaNum`, `units_mul_apply_unitsPowCM`, `units_one_def`, `topGen_pow_ne_one`, `zetaNum_moments`, `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`]
- Used by: `kubotaLeopoldt`
- Visibility: public
- Lines: 274–320 (proof OVER-50, ~34 lines)
- Notes: long(30–50) — ~34 lines. `classical`. Hinges on `IsLocalization.mk'_spec'`, `IsFractionRing.injective`, `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`, `mul_left_cancel₀`.

### theorem kubotaLeopoldt
- Type: `∃! q : QuotientField p, IsPseudoMeasure p q ∧ ∀ (b : ℤ_[p]ˣ) (k : ℕ), 0 < k → ∀ ν, algebraMap (dirac p b − 1) · q = algebraMap ν → ((ν (unitsPowCM p k):ℤ_[p]):ℚ_[p]) = ((b:ℚ_[p])^k−1)(1−(p:ℚ_[p])^(k−1))((zetaNeg (k−1):ℚ):ℚ_[p])` (for `p ≠ 2`)
- What: RJW Thm. 4.1 (Kubota–Leopoldt): there is a unique pseudo-measure `ζ_p` on `ℤ_p^×` with `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1}) ζ(1−k)` for all `k > 0`.
- How: Existence is `padicZeta` with `padicZeta_isPseudoMeasure` and `padicZeta_moments`. Uniqueness: for any other `q` with these properties, shows `q − padicZeta` is a pseudo-measure (`IsPseudoMeasure.sub`) with all moments zero, hence `= 0` by `pseudoMeasure_eq_zero_of_moments` (using `topGen_pow_ne_one`); the moment-zero check splits a witness as `ν₁ − ν₂` (`IsFractionRing.injective`) and subtracts `q`'s moment hypothesis from `padicZeta_moments`. Concludes via `sub_eq_zero`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`QuotientField`, `IsPseudoMeasure`, `dirac`, `PadicMeasure`, `unitsPowCM`, `zetaNeg`, `exists_nat_topological_generator`, `padicZeta`, `padicZeta_isPseudoMeasure`, `padicZeta_moments`, `IsPseudoMeasure.sub`, `pseudoMeasure_eq_zero_of_moments`, `topGen_pow_ne_one`]
- Used by: unused in file (main theorem)
- Visibility: public
- Lines: 322–357 (proof OVER-50, ~25 lines)
- Notes: long(30–50)? No — proof body ~25 lines. `classical`. Hinges on `pseudoMeasure_eq_zero_of_moments`, `IsFractionRing.injective`, `IsPseudoMeasure.sub`.

---

## File Summary

- **Total declarations: 16** — defs: 5 (`muAUnits`, `invCM`, `unitsCmul`, `zetaNum`, `padicZeta`); lemmas+theorems: 11 (`iota_muAUnits`, `muAUnits_apply_unitsPowCM`, `continuous_units_inv_val`, `unitsCmul_apply`, `zetaNum_apply_unitsPowCM`, `zetaNum_moments`, `topGen_pow_ne_one`, `exists_nat_topological_generator`, `IsPseudoMeasure.sub`, `padicZeta_isPseudoMeasure`, `padicZeta_moments`, `kubotaLeopoldt` — note: 12 here; correction below); instances: 0.
  - Recount: defs 5, lemmas/theorems 11, instances 0 → **16 total**. (Lemma/theorem members: `iota_muAUnits`, `muAUnits_apply_unitsPowCM`, `continuous_units_inv_val`, `unitsCmul_apply`, `zetaNum_apply_unitsPowCM`, `zetaNum_moments`, `topGen_pow_ne_one`, `exists_nat_topological_generator`, `IsPseudoMeasure.sub`, `padicZeta_isPseudoMeasure`, `padicZeta_moments`, `kubotaLeopoldt` = 12 → **total 17**.) **Authoritative total: 17 declarations (5 defs / 12 lemmas+theorems / 0 instances).**
- **Key API (used by ≥3 within this file):**
  - `topGen_pow_ne_one` — used by `padicZeta`, `padicZeta_moments`, `kubotaLeopoldt` (3).
  - `exists_nat_topological_generator` — used by `padicZeta`, `padicZeta_moments`, `kubotaLeopoldt` (3).
  - `zetaNum` — used by `zetaNum_apply_unitsPowCM`, `zetaNum_moments`, `padicZeta`, `padicZeta_moments` (4).
  - `padicZeta` — used by `padicZeta_isPseudoMeasure`, `padicZeta_moments`, `kubotaLeopoldt` (3).
  - `muAUnits` — used by `iota_muAUnits`, `muAUnits_apply_unitsPowCM`, `zetaNum`, `zetaNum_apply_unitsPowCM` (4).
- **Unused within file (terminal/exported API):** `iota_muAUnits`, `unitsCmul_apply` (simp), `kubotaLeopoldt` (main theorem). These are the file's external-facing results.
- **Declarations with `sorry`: none.**
- **`set_option`: none.** **`TODO`/`admit`: none.**
- **Proofs > 50 lines (count: 1):** `exists_nat_topological_generator` (lines 120–247, ~120-line proof) — **needs /decompose-proof**.
- **Proofs 30–50 lines (count: 1):** `padicZeta_moments` (lines 274–320, ~34-line proof).
- (Borderline near 30: `kubotaLeopoldt` ~25 lines; `topGen_pow_ne_one` ~15 lines — both under 30.)

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_KubotaLeopoldt_ZetaP.md`
