# Inventory: PadicLFunctions/Interpolation/NonTame.lean

File implements RJW §5.2, Thm 5.7: p-adic measures `μ_η` for primitive tame
conductors `D > 1` coprime to `p`, their moments (= L-values), ψ-invariance,
unit-restricted moments, character twists, and the existence+uniqueness of the
interpolating measure (RJW Theorem 5.7). All declarations live in
`namespace PadicLFunctions.MeasureR`, in a `noncomputable section`.

Ambient variables: `p : ℕ` `[Fact p.Prime]`; `K` a complete normed field,
ultrametric, `ℚ_[p]`-algebra, char 0; `integerRing K` its ring of integers.

---

### theorem isUnit_root_mul_one_add_X_sub_one
- Type: `{ζ : integerRing K} {D : ℕ} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) {c : ℕ} (hc : ¬ D ∣ c) : IsUnit (C (ζ^c) * (1 + X) - 1 : PowerSeries (integerRing K))`
- What: For `ζ` a primitive `D`-th root of unity (`p ∤ D`, `D ∤ c`), the power series `ζ^c·(1+X) − 1` is a unit of `R⟦X⟧`.
- How: A power series is a unit iff its constant coefficient `ζ^c − 1` is a unit; reduces to `‖ζ^c − 1‖ = 1` in `K` via `integerRing.isUnit_of_norm_eq_one`, then `IsPrimitiveRoot.norm_pow_sub_one_eq_one`.
- Hypotheses: `ζ` primitive `D`-th root in `integerRing K`; `p ∤ D`; `D ∤ c`.
- Uses from project: `integerRing`, `integerRing.isUnit_of_norm_eq_one`, `norm_natCast_eq_one_of_not_dvd`
- Used by: `isUnit_root_mul_pow_one_add_X_sub_one` (indirectly, sibling), `muEta_term_exp_identity`, `rescale_exp_sub_one_mul_muEta_term`, `mahlerTransform_charTwist_muEtaCleared`, `psi_symm_inverse_denom`
- Visibility: public
- Lines: 36-50 (proof ~7 lines)
- Notes: none. `omit [CompleteSpace K] [CharZero K]`.

### theorem gaussSum_isUnit_of_coprime
- Type: `{D : ℕ} [NeZero D] {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) : IsUnit (gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one))`
- What: The Gauss sum `G(η⁻¹)` of a primitive character of conductor `D` coprime to `p` is a unit of the integer ring.
- How: Reduces (`integerRing.isUnit_of_norm_eq_one`) to `‖G‖ = 1` in `K` via `coe_gaussSum_zmodChar` and `norm_gaussSum_eq_one`; uses `DirichletCharacter.isPrimitive_ringHomComp_iff` to transport primitivity to the field character and `DirichletCharacter.conductor_inv`.
- Hypotheses: `η` primitive of conductor `D`; `ζ` primitive `D`-th root; `p ∤ D`.
- Uses from project: `integerRing`, `integerRing.isUnit_of_norm_eq_one`, `coe_gaussSum_zmodChar`, `toFieldChar`, `norm_gaussSum_eq_one`
- Used by: unused in file
- Visibility: public
- Lines: 52-68 (proof ~9 lines)
- Notes: none. `omit [CompleteSpace K] [CharZero K]`.

### def muEtaCleared
- Type: `{D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K} (_hζ : IsPrimitiveRoot ζ D) (_hD : ¬ p ∣ D) : MeasureR K ℤ_[p]`
- What: The (Gauss-cleared) measure `μ_η` of RJW §5.2: the inverse Mahler transform of `−∑_c η⁻¹(c)·((ζ^c)(1+X) − 1)⁻¹`, stated unnormalised (the Gauss-sum factor `−G(η⁻¹)` carried in the statements).
- How: Definition via `(mahlerRingEquiv p K).symm` applied to the negated finite sum of `Ring.inverse` of the denominator series.
- Hypotheses: `D ≠ 0`; `ζ` primitive `D`-th root; `p ∤ D` (roots/coprimality only needed to make the denominators units in the lemmas).
- Uses from project: `MeasureR`, `mahlerRingEquiv`
- Used by: `mahlerTransform_muEtaCleared`, `mahlerTransform_charTwist_muEtaCleared`, `X_mul_muEtaCleared_subst`, `muEtaCleared_moments`, `psi_muEtaCleared`, `res_units_muEtaCleared_moments`, and all twist/zeta lemmas
- Visibility: public
- Lines: 72-83 (def body 4 lines)
- Notes: none. The central object of the file.

### lemma mahlerTransform_muEtaCleared
- Type: `(η …) (hζ …) (hD …) : mahlerTransform p K (muEtaCleared …) = -(∑ c ∈ range D, C (η⁻¹ c) * Ring.inverse (C (ζ^c) * (1+X) - 1))`
- What: The Mahler transform of `muEtaCleared` is its defining series `−G(η⁻¹)F_η` (cleared of the Gauss-sum denominator).
- How: `(mahlerRingEquiv p K).apply_symm_apply`.
- Hypotheses: as `muEtaCleared`.
- Uses from project: `mahlerTransform`, `muEtaCleared`, `mahlerRingEquiv`
- Used by: `mahlerTransform_charTwist_muEtaCleared`, `X_mul_muEtaCleared_subst`, `muEtaCleared_moments`
- Visibility: public, `@[simp]`
- Lines: 87-98 (proof 1 line)
- Notes: none. `omit [CharZero K]`.

### theorem isUnit_root_mul_pow_one_add_X_sub_one
- Type: `(hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) {c} (hc : ¬ D ∣ c) {w : integerRing K} (hw : ‖(w:K) - 1‖ < 1) : IsUnit (C (ζ^c * w) * (1 + X) - 1)`
- What: For `w` close to `1` (`‖w−1‖<1`, e.g. a `p`-power root of unity), the product denominator `ζ^c·w·(1+X) − 1` is a unit of `R⟦X⟧`.
- How: Constant coefficient `ζ^c·w − 1 = (ζ^c − 1) + ζ^c(w − 1)`; ultrametric dominance (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) gives norm 1 since `‖ζ^c−1‖=1` strictly dominates the small term; reduces to `integerRing.isUnit_of_norm_eq_one`.
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `D ∤ c`; `‖w−1‖ < 1`.
- Uses from project: `integerRing`, `integerRing.isUnit_of_norm_eq_one`, `norm_natCast_eq_one_of_not_dvd`
- Used by: `rescale_exp_sub_one_mul_twist_term`
- Visibility: public
- Lines: 100-131 (proof ~21 lines)
- Notes: none. `omit [CompleteSpace K] [CharZero K]`.

### lemma map_ring_inverse_of_isUnit
- Type: `{R S} [Semiring R] [Semiring S] (f : R →+* S) {u : R} (hu : IsUnit u) : f (Ring.inverse u) = Ring.inverse (f u)`
- What: A ring homomorphism commutes with `Ring.inverse` at units.
- How: Apply `f` to `Ring.mul_inverse_cancel`, then `mul_left_cancel` against the image unit.
- Hypotheses: `f` a ring hom; `u` a unit.
- Uses from project: [] (general algebra)
- Used by: `mahlerTransform_charTwist_muEtaCleared`
- Visibility: public
- Lines: 133-140 (proof ~4 lines)
- Notes: none.

### lemma mahlerTransform_charTwist_muEtaCleared
- Type: `(η …) (hζ …) (hD …) {N} {ε} (hε : IsPrimitiveRoot ε (p^N)) (b : ℕ) : mahlerTransform p K (twist p K (charCM (ε^b−1) …) (muEtaCleared …)) = -(∑ c ∈ range D, C (η⁻¹ c) * Ring.inverse (C (ζ^c · ε^b) * (1+X) - 1))`
- What: The `ε^b`-line twist of `μ̃_η` has the product-root denominators `ζ^c·ε^b·(1+X)−1` (L5.2.6's CRT bookkeeping).
- How: Rewrites by `mahlerTransform_charTwist_eq_substAffine` and `mahlerTransform_muEtaCleared`; per-term `substAffine_C` / `substAffine_one_add_X` computes the image; the `c=0` line is `0=0` (both `X` and the norm-small denominator are non-units via `norm_pow_sub_one_lt_one`); the `D∤c` lines use `map_ring_inverse_of_isUnit`.
- Hypotheses: as `muEtaCleared`; `ε` a primitive `p^N`-th root; `b : ℕ`.
- Uses from project: `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `muEtaCleared`, `mahlerTransform_charTwist_eq_substAffine`, `mahlerTransform_muEtaCleared`, `substAffine`, `substAffine_C`, `substAffine_one_add_X`, `isUnit_root_mul_one_add_X_sub_one`, `map_ring_inverse_of_isUnit`, `norm_pow_sub_one_lt_one`
- Used by: `twist_subst_S_eq`
- Visibility: public
- Lines: 142-189 (proof ~32 lines)
- Notes: long(30-50). `omit [CharZero K]`.

### lemma unit_denom_exp_identity
- Type: `{w : integerRing K} (hw : IsUnit (C w * (1+X) - 1)) : (C (w:K) * exp K - 1) * (map subtype (Ring.inverse (C w * (1+X) - 1))).subst (exp K - 1) = 1`
- What: The unit identity `(w(1+X)−1)·(…)⁻¹ = 1` transported to `K⟦t⟧` by the coefficient inclusion and `X ↦ e^t − 1`: `(w·e^t − 1)·G_w = 1`.
- How: From `hasSubst_exp_sub_one_K` get `substAlgHom` sends `X ↦ exp K − 1` and fixes constants; apply `map subtype` to `Ring.mul_inverse_cancel`, then the substitution alg-hom, and simplify `1 + (exp−1) = exp`.
- Hypotheses: `w(1+X)−1` is a unit.
- Uses from project: `integerRing`, `hasSubst_exp_sub_one_K`
- Used by: `muEta_term_exp_identity`, `rescale_exp_sub_one_mul_unit_denom`
- Visibility: public
- Lines: 191-220 (proof ~18 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma muEta_term_exp_identity
- Type: `(hζ …) (hD …) {c} (hc : ¬ D ∣ c) : (C ((ζ:K)^c) * exp K - 1) * (map subtype (Ring.inverse (C (ζ^c) * (1+X) - 1))).subst (exp K - 1) = 1`
- What: The `μ_η`-instance of the previous lemma: `(ζ^c·e^t − 1)·G_c = 1`.
- How: Specialise `unit_denom_exp_identity` at the unit `isUnit_root_mul_one_add_X_sub_one`; coerce `ζ^c` via `SubmonoidClass.coe_pow`.
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `D ∤ c`.
- Uses from project: `integerRing`, `unit_denom_exp_identity`, `isUnit_root_mul_one_add_X_sub_one`
- Used by: unused in file
- Visibility: public
- Lines: 222-232 (proof ~2 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma rescale_exp_sub_one_mul_unit_denom
- Type: `{w} {M} (hwM : w^M = 1) (hw : IsUnit (C w * (1+X) - 1)) : (rescale (M:K) (exp K) - 1) * (map subtype (Ring.inverse (C w * (1+X) - 1))).subst (exp K - 1) = ∑ j ∈ range M, C ((w:K)^j) * rescale (j:K) (exp K)`
- What: Clearing `e^{Mt} − 1` against `G_w` recovers the geometric numerator `Σ_{j<M} w^j·e^{jt}`, for any `M`-torsion `w`.
- How: `e^{Mt} = (w·e^t)^M` (via `exp_pow_eq_rescale_exp` and `w^M=1`); factor `geom_sum_mul`, cancel the unit term via `unit_denom_exp_identity`, recognise each summand `(w·e^t)^j` as `w^j·e^{jt}`.
- Hypotheses: `w^M = 1`; `w(1+X)−1` a unit.
- Uses from project: `integerRing`, `unit_denom_exp_identity`
- Used by: `rescale_exp_sub_one_mul_muEta_term`, `rescale_exp_sub_one_mul_twist_term`
- Visibility: public
- Lines: 234-275 (proof ~20 lines)
- Notes: none. `omit [CompleteSpace K]`. (`calc`-based.)

### lemma rescale_exp_sub_one_mul_muEta_term
- Type: `(hζ …) (hD …) {c} (hc : ¬ D ∣ c) : (rescale (D:K) (exp K) - 1) * (map subtype (Ring.inverse (C (ζ^c) * (1+X) - 1))).subst (exp K - 1) = ∑ j ∈ range D, C ((ζ:K)^(c·j)) * rescale (j:K) (exp K)`
- What: The `μ_η`-instance: clearing `e^{Dt} − 1` against `G_c` recovers `Σ_{j<D} ζ^{cj}·e^{jt}`.
- How: Specialise `rescale_exp_sub_one_mul_unit_denom` at `w = ζ^c`, `M = D` (with `(ζ^c)^D = 1`), the unit from `isUnit_root_mul_one_add_X_sub_one`; rewrite `(ζ^c)^j = ζ^{cj}`.
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `D ∤ c`.
- Uses from project: `integerRing`, `rescale_exp_sub_one_mul_unit_denom`, `isUnit_root_mul_one_add_X_sub_one`
- Used by: `X_mul_muEtaCleared_subst`
- Visibility: public
- Lines: 277-295 (proof ~5 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma subst_map_C_mul
- Type: `(w : integerRing K) (F : PowerSeries (integerRing K)) : (map subtype (C w * F)).subst (exp K - 1) = C (w:K) * (map subtype F).subst (exp K - 1)`
- What: Distributing the coefficient inclusion and the exponential substitution over a constant multiple.
- How: `map_mul`, `map_C`, then `substAlgHom` commutes with constants.
- Hypotheses: none beyond ambient.
- Uses from project: `integerRing`, `hasSubst_exp_sub_one_K`
- Used by: `X_mul_muEtaCleared_subst`, `twist_subst_S_eq`, `twist_subst_gaussSum_smear`
- Visibility: public
- Lines: 297-313 (proof ~8 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma subst_map_sum
- Type: `{ι} (s : Finset ι) (F : ι → PowerSeries (integerRing K)) : (map subtype (∑ i ∈ s, F i)).subst (exp K - 1) = ∑ i ∈ s, (map subtype (F i)).subst (exp K - 1)`
- What: Distributing the coefficient inclusion and exponential substitution over a finite sum.
- How: `map_sum` for `map subtype` then for `substAlgHom`.
- Hypotheses: none beyond ambient.
- Uses from project: `integerRing`, `hasSubst_exp_sub_one_K`
- Used by: `X_mul_muEtaCleared_subst`, `twist_subst_S_eq`, `twist_subst_gaussSum_smear`
- Visibility: public
- Lines: 315-325 (proof ~3 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma subst_map_neg
- Type: `(F : PowerSeries (integerRing K)) : (map subtype (-F)).subst (exp K - 1) = -(map subtype F).subst (exp K - 1)`
- What: Distributing the coefficient inclusion and exponential substitution over a negation.
- How: `map_neg` for both `map subtype` and `substAlgHom`.
- Hypotheses: none beyond ambient.
- Uses from project: `integerRing`, `hasSubst_exp_sub_one_K`
- Used by: `X_mul_muEtaCleared_subst`, `twist_subst_S_eq`
- Visibility: public
- Lines: 327-337 (proof ~3 lines)
- Notes: none. `omit [CompleteSpace K]`.

### lemma rescale_exp_sub_one_ne_zero
- Type: `{M : ℕ} [NeZero M] : (rescale (M:K) (exp K) - 1 : PowerSeries K) ≠ 0`
- What: For `M ≠ 0`, the rescaled exponential `e^{Mt} − 1` is a nonzero power series over `K` (its degree-1 coefficient is `M ≠ 0`).
- How: Apply `coeff 1`; the constant term cancels and the linear term is `M`, nonzero by `NeZero M`.
- Hypotheses: `M ≠ 0`.
- Uses from project: [] (PowerSeries/exp API only)
- Used by: `X_mul_muEtaCleared_subst`, `X_mul_twist_subst_eq`
- Visibility: public
- Lines: 339-351 (proof ~9 lines)
- Notes: none. `omit [IsUltrametricDist K] [CompleteSpace K]`.

### lemma X_mul_muEtaCleared_subst
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη : η.IsPrimitive) {ζ} (hζ : IsPrimitiveRoot ζ D) (hζK : IsPrimitiveRoot (ζ:K) D) (hD : ¬ p ∣ D) : X * (map subtype (mahlerTransform p K (muEtaCleared …))).subst (exp K - 1) = -(C (gaussSum (toFieldChar η)⁻¹ …) * mk (k ↦ (toFieldChar η).genBernoulli k / k!))`
- What: The master identity `X·H_η = −G(η⁻¹)·genBPS_{η_K}` in `K⟦t⟧` — the η⁻¹-weighted geometric numerators collapse through the Gauss sum and the generating-function identity.
- How: (1) substituted transform as η̄⁻¹-weighted `G_c`-sum (`subst_map_*`, `MulChar.ringHomComp_inv`); (2) clear `e^{Dt}−1` via `rescale_exp_sub_one_mul_muEta_term`, collapse Gauss sums via `sum_inv_char_zeta_pow` and `Finset.sum_comm`; (3) multiply by `X`, insert T504 `X_mul_sum_char_rescale_exp`, cancel the regular factor with `mul_right_cancel₀ (rescale_exp_sub_one_ne_zero)`.
- Hypotheses: `1 < D`; `η` primitive; `ζ` primitive `D`-th root in `integerRing K` and its image `ζK` in `K`; `p ∤ D`.
- Uses from project: `mahlerTransform`, `muEtaCleared`, `toFieldChar`, `DirichletCharacter.isPrimitive_ringHomComp_iff` (via toFieldChar), `mahlerTransform_muEtaCleared`, `subst_map_neg`, `subst_map_sum`, `subst_map_C_mul`, `rescale_exp_sub_one_mul_muEta_term`, `sum_inv_char_zeta_pow`, `X_mul_sum_char_rescale_exp`, `rescale_exp_sub_one_ne_zero`, `genBernoulli`
- Used by: `muEtaCleared_moments`
- Visibility: public
- Lines: 353-454 (proof ~85 lines)
- Notes: OVER-50 (needs /decompose-proof). Three internal `have`s (`hHsum`, `hclear`, final `calc`). `classical`.

### theorem muEtaCleared_moments
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη : η.IsPrimitive) {ζ} (hζ …) (hD …) (k : ℕ) : ((muEtaCleared … (powCM p K k) : integerRing K) : K) = ((gaussSum η⁻¹ …) : K) * LvalNeg (toFieldChar η) k`
- What: RJW Lem 5.9 — the `k`-th moment of `μ_η` equals (Gauss-cleared) `G(η⁻¹)·L(η,−k)`.
- How: Express the moment as `k!·[t^k] H_η` (`apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`); take the `(k+1)`-st coefficient of the master identity `X_mul_muEtaCleared_subst` (`coeff_succ_X_mul`, `coeff_C_mul`, `coeff_mk`); identify with `LvalNeg` and clear factorials by `field_simp`.
- Hypotheses: `1 < D`; `η` primitive; `ζ` primitive `D`-th root; `p ∤ D`; `k : ℕ`.
- Uses from project: `muEtaCleared`, `powCM`, `gaussSum`(field, via `coe_gaussSum_zmodChar`), `LvalNeg`, `toFieldChar`, `X_mul_muEtaCleared_subst`, `mahlerTransform`, `apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`, `del`, `coe_gaussSum_zmodChar`
- Used by: `res_units_muEtaCleared_moments`
- Visibility: public
- Lines: 456-491 (proof ~32 lines)
- Notes: long(30-50).

### lemma symm_denom_eq
- Type: `(w : integerRing K) : (mahlerRingEquiv p K).symm (C w * (1+X) - 1) = w • dirac K ℤ_[p] 1 - 1`
- What: The denominator series `w·(1+X) − 1` read back through the Mahler isomorphism is the measure `w·δ_1 − δ_0`.
- How: Apply `mahlerRingEquiv` injectively; compute the transform of `w•δ_1` via `mahlerTransform_smul`, `mahlerTransform_dirac`, `binomialSeries_nat` at `1`.
- Hypotheses: none beyond ambient.
- Uses from project: `mahlerRingEquiv`, `dirac`, `mahlerTransform`, `mahlerTransform_smul`, `mahlerTransform_dirac`, `binomialSeries_nat`
- Used by: `psi_symm_inverse_denom`
- Visibility: public
- Lines: 493-506 (proof ~10 lines)
- Notes: none. `omit [CharZero K]`.

### lemma psi_symm_inverse_denom
- Type: `(hζ …) (hD …) {m} (hm : ¬ D ∣ m) : psi p K ((mahlerRingEquiv p K).symm (Ring.inverse (C (ζ^m) * (1+X) - 1))) = (mahlerRingEquiv p K).symm (Ring.inverse (C (ζ^(p·m)) * (1+X) - 1))`
- What: ψ of the inverse-denominator measure shifts the exponent: `ψ(γ_m) = γ_{pm}` (decomposition L5.2.4).
- How: (i) geometric telescope `φ(A)·γ = Σ_{j<p} ζ^{mj}·δ_j` proved through the Mahler transform (`geom_sum_mul`, `binomialSeries_nat`); (ii) `ψ` of the telescope is `δ_0 = 1` via `psi_sum`, `psi_dirac_of_isUnit` (units killed) and `psi_dirac_zero`; (iii) cancel the unit `A = ζ^{pm}δ_1 − δ_0` using `psi_phi_mul` and `symm_denom_eq`.
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `D ∤ m`.
- Uses from project: `psi`, `mahlerRingEquiv`, `dirac`, `isUnit_root_mul_one_add_X_sub_one`, `MeasureR`, `phi`, `mahlerTransform_injective`, `mahlerTransform`, `mahlerTransform_mul`, `mahlerTransform_sub`, `mahlerTransform_smul`, `mahlerTransform_dirac`, `mahlerTransform_one`, `mahlerTransformₗ`, `binomialSeries_nat`, `binomialSeries`, `psi_sum`, `psi_smul`, `psi_dirac_zero`, `psi_dirac_of_isUnit`, `psi_phi_mul`, `symm_denom_eq`
- Used by: `psi_muEtaCleared`
- Visibility: public
- Lines: 508-622 (proof ~108 lines)
- Notes: OVER-50 (needs /decompose-proof). Three labelled stages (i)/(ii)/(iii) with internal `calc`. `omit [CharZero K]`.

### theorem psi_muEtaCleared
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} {ζ} (hζ …) (hD …) : psi p K (muEtaCleared …) = η (p : ZMod D) • muEtaCleared …`
- What: RJW Lem 5.10 — `ψ(μ_η) = η(p)·μ_η` (the ξ-free route; primitivity of `η` not needed).
- How: Write `μ̃` as the `ZMod D`-indexed weighted sum `−∑_x η⁻¹(x)·g(x)` (reindex via `Finset.sum_nbij'`); ψ acts on the family by the index shift `x ↦ p·x` (`psi_symm_inverse_denom`); the unit `p` reindexes the sum (`ZMod.isUnit_iff_coprime`), twisting the weight by `η(p)` (`MulChar.inv_apply`); reassemble with `Finset.smul_sum`.
- Hypotheses: `1 < D`; `ζ` primitive `D`-th root; `p ∤ D`.
- Uses from project: `psi`, `muEtaCleared`, `mahlerRingEquiv`, `MeasureR`, `psi_symm_inverse_denom`, `mahlerLinearEquiv`
- Used by: `res_units_muEtaCleared_moments`, `zetaEta_twisted_moments`
- Visibility: public
- Lines: 624-735 (proof ~105 lines)
- Notes: OVER-50 (needs /decompose-proof). Multiple `Finset.sum_nbij'` reindexings + `show … from by` rewrites. `classical`. `omit [CharZero K]`.

### theorem res_units_muEtaCleared_moments
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη : η.IsPrimitive) {ζ} (hζ …) (hD …) (k : ℕ) : ((res p K (isClopen_units p) (muEtaCleared …) (powCM p K k) : integerRing K) : K) = ((gaussSum η⁻¹ …) : K) * (1 − η(p)·p^k) * LvalNeg (toFieldChar η) k`
- What: RJW Lem 5.11 — the unit-restricted moment carries the Euler factor: `∫_{ℤ_p^×} x^k dμ_η = G(η⁻¹)·(1 − η(p)p^k)·L(η,−k)` (cleared).
- How: `res_units_eq` rewrites `Res = 1 − φ∘ψ`; `psi_muEtaCleared` supplies `ψ`, `phi_apply_powCM` the φ-term picking up `η(p)·p^k`; coerce `algebraMap` of `p^k`, insert `muEtaCleared_moments`, finish with `ring`.
- Hypotheses: `1 < D`; `η` primitive; `ζ` primitive `D`-th root; `p ∤ D`; `k : ℕ`.
- Uses from project: `res`, `PadicMeasure.isClopen_units`, `muEtaCleared`, `powCM`, `gaussSum`, `LvalNeg`, `toFieldChar`, `res_units_eq`, `psi_muEtaCleared`, `phi_apply_powCM`, `muEtaCleared_moments`
- Used by: unused in file
- Visibility: public
- Lines: 737-765 (proof ~19 lines)
- Notes: none.

### lemma toFieldChar_prod_natCast
- Type: `{D} {η} {n} {χ} {θ} (hθ : θ = changeLevel … η * changeLevel … χ) (j : ℕ) : (toFieldChar θ) (j : ZMod (D·p^n)) = (toFieldChar η) (j : ZMod D) * (toFieldChar χ) (j : ZMod (p^n))`
- What: The product character `θ = η·χ` (coprime moduli `D`, `p^n`) evaluates at naturals as the product of component values (both sides vanish off the units by coprimality).
- How: Case split on whether `(j : ZMod (D·p^n))` is a unit; unit case uses `changeLevel_eq_cast_of_dvd` and `ZMod.cast_natCast`; non-unit case splits via `Nat.coprime_mul_iff_right` (`ZMod.isUnit_iff_coprime`) and uses `map_nonunit`.
- Hypotheses: `θ` the change-level product of `η` and `χ`; `j : ℕ`.
- Uses from project: `toFieldChar`
- Used by: `twist_char_factor_sum`, `zetaEta_twisted_moments`
- Visibility: public
- Lines: 767-801 (proof ~30 lines)
- Notes: long(30-50). `omit [hp] [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [CharZero K]`.

### private lemma twist_subst_S_eq
- Type: `{D} [NeZero D] {η} {ζ} (hζ …) (hD …) {n} {ε} (hε : IsPrimitiveRoot ε (p^n)) (b : ℕ) : (map subtype (mahlerTransform p K (twist p K (charCM (ε^b−1) …) (muEtaCleared …)))).subst (exp K - 1) = -∑ c ∈ range D, C ((toFieldChar η)⁻¹ c) * (map subtype (Ring.inverse (C (ζ^c · ε^b) * (1+X) - 1))).subst (exp K - 1)`
- What: The exp-substituted `ε^b`-line of the twist of `μ̃_η`: the `η̄⁻¹`-weighted sum of substituted product-root inverses.
- How: `simp` with `mahlerTransform_charTwist_muEtaCleared`, `subst_map_neg/sum/C_mul`; per-term `MulChar.ringHomComp_inv`.
- Hypotheses: as `muEtaCleared`; `ε` primitive `p^n`-th root; `b : ℕ`.
- Uses from project: `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `muEtaCleared`, `toFieldChar`, `mahlerTransform_charTwist_muEtaCleared`, `subst_map_neg`, `subst_map_sum`, `subst_map_C_mul`
- Used by: `rescale_exp_sub_one_mul_twist_line`
- Visibility: private
- Lines: 803-827 (proof ~7 lines)
- Notes: none.

### private lemma rescale_exp_sub_one_mul_twist_term
- Type: `{D} [NeZero D] {ζ} (hζ …) (hD …) {n} {ε} (hε …) {b c} (hcd : ¬ D ∣ c) (a₁ a₂ : K) : (rescale ((D·p^n):K) (exp K) - 1) * (C a₁ * (C a₂ * (map subtype (Ring.inverse (C (ζ^c·ε^b) * (1+X) - 1))).subst (exp K - 1))) = C (a₁·a₂) * ∑ j ∈ range (D·p^n), C (((ζ:K)^c · (ε:K)^b)^j) * rescale (j:K) (exp K)`
- What: Clearing `e^{D·p^n·t} − 1` against the substituted product-root inverse `G_{ζ^c·ε^b}` recovers the geometric numerator scaled by `a₁·a₂`.
- How: `ζ^c·ε^b` is `D·p^n`-torsion (`hζ/hε.pow_eq_one`) and its denominator is a unit (`isUnit_root_mul_pow_one_add_X_sub_one`, with `norm_pow_sub_one_lt_one`); apply `rescale_exp_sub_one_mul_unit_denom` and pull the constants out (`map_mul`).
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `ε` primitive `p^n`-th root; `D ∤ c`; scalars `a₁ a₂`.
- Uses from project: `integerRing`, `isUnit_root_mul_pow_one_add_X_sub_one`, `norm_pow_sub_one_lt_one`, `rescale_exp_sub_one_mul_unit_denom`
- Used by: `rescale_exp_sub_one_mul_twist_line`
- Visibility: private
- Lines: 829-872 (proof ~38 lines)
- Notes: long(30-50). `omit [CompleteSpace K]`.

### private lemma twist_char_factor_sum
- Type: `{D} [NeZero D] {η} (hηK : (toFieldChar η).IsPrimitive) {ζ} (hζK : IsPrimitiveRoot (ζ:K) D) {n} [NeZero (p^n)] {χ} (hχK : (toFieldChar χ).IsPrimitive) {ε} (hε …) (hεK …) {θ} (hθ : …) (j : ℕ) : ∑ b ∈ range (p^n), ∑ c ∈ range D, C (χ̄⁻¹(b)·η̄⁻¹(c)·((ζ:K)^c·(ε:K)^b)^j) * rescale (j:K) (exp K) = C (G(χ⁻¹)·G(η̄⁻¹)·θ̃(j)) * rescale (j:K) (exp K)`
- What: The inner `(b,c)`-double sum factors as a product of the two Gauss collapses (T509 (v-a)) at coprime moduli `p^n`, `D`, times the product character `θ̃(j)`.
- How: Factor the summand into `b`- and `c`-parts (`mul_pow`, `pow_mul`); `Finset.sum_mul_sum`; apply `sum_inv_char_zeta_pow` to each factor, `coe_gaussSum_zmodChar`, and `toFieldChar_prod_natCast`; `ring_nf`.
- Hypotheses: `η̄`, `χ̄` (field characters) primitive; `ζK`, `εK` primitive roots in `K`; `θ` the product; `j : ℕ`.
- Uses from project: `toFieldChar`, `sum_inv_char_zeta_pow`, `coe_gaussSum_zmodChar`, `toFieldChar_prod_natCast`, `gaussSum`
- Used by: `rescale_exp_sub_one_mul_twist_smear`
- Visibility: private
- Lines: 874-931 (proof ~33 lines)
- Notes: long(30-50). `omit [hp] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`. (`calc`-based.)

### private lemma twist_subst_gaussSum_smear
- Type: `{D} [NeZero D] {η} {ζ} (hζ …) (hD …) {n} [NeZero (p^n)] {χ} (hχ : χ.IsPrimitive) {ε} (hε …) : C (G(χ⁻¹)) * (map subtype (mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared …)))).subst (exp K - 1) = ∑ b ∈ range (p^n), C ((toFieldChar χ)⁻¹ b) * (map subtype (mahlerTransform p K (twist p K (charCM (ε^b−1) …) (muEtaCleared …)))).subst (exp K - 1)`
- What: RJW step (A), T508 smearing: the `G(χ⁻¹)`-scaled substituted transform of the twist `μ_θ` is the `χ̄⁻¹`-weighted sum of its `ε^b`-lines.
- How: `mahler_twist_formula` (T508) expresses `G(χ⁻¹)·transform` as the `χ⁻¹`-weighted sum of `ε^b`-line transforms; push `map subtype`+`subst` through the sum (`subst_map_C_mul/sum`); convert `χ⁻¹` to `(toFieldChar χ)⁻¹` (`MulChar.ringHomComp_inv`).
- Hypotheses: `ζ` primitive `D`-th root; `p ∤ D`; `χ` primitive mod `p^n`; `ε` primitive `p^n`-th root.
- Uses from project: `gaussSum`, `mahlerTransform`, `twist`, `DirichletCharacter.toContinuousMapZp`, `muEtaCleared`, `toFieldChar`, `charCM`, `tendsto_pow_pow_sub_one`, `mahler_twist_formula`, `mahlerTransform_smul`, `mahlerTransformₗ`, `subst_map_C_mul`, `subst_map_sum`
- Used by: `rescale_exp_sub_one_mul_twist_smear`, `X_mul_twist_subst_eq`
- Visibility: private
- Lines: 933-985 (proof ~33 lines)
- Notes: long(30-50). (`show … from rfl` rewrites for the linear-map coercion.)

### private lemma rescale_exp_sub_one_mul_twist_line
- Type: `{D} [NeZero D] [Fact (1<D)] {η} {ζ} (hζ …) (hD …) {n} {ε} (hε …) (b : ℕ) (a : K) : (rescale ((D·p^n):K) (exp K) - 1) * (C a * (map subtype (mahlerTransform p K (twist p K (charCM (ε^b−1) …) (muEtaCleared …)))).subst (exp K - 1)) = -∑ c ∈ range D, C (a·(toFieldChar η)⁻¹ c) * ∑ j ∈ range (D·p^n), C (((ζ:K)^c·(ε:K)^b)^j) * rescale (j:K) (exp K)`
- What: RJW step (B) per-`ε^b`-line: clearing `e^{D·p^n·t} − 1` against the `a`-scaled `ε^b`-line gives the `η̄⁻¹`-weighted sum of `(b,c)` geometric numerators.
- How: Rewrite the line via `twist_subst_S_eq`; per `c`, the `c=0` term vanishes (`map_nonunit`), the `D∤c` terms come from `rescale_exp_sub_one_mul_twist_term`.
- Hypotheses: `1 < D` (Fact); `ζ` primitive `D`-th root; `p ∤ D`; `ε` primitive `p^n`-th root; `b : ℕ`; scalar `a`.
- Uses from project: `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `muEtaCleared`, `toFieldChar`, `twist_subst_S_eq`, `rescale_exp_sub_one_mul_twist_term`
- Used by: `rescale_exp_sub_one_mul_twist_smear`
- Visibility: private
- Lines: 987-1015 (proof ~9 lines)
- Notes: none.

### private lemma twist_smear_reindex
- Type: `{D} {η} {ζ} {n} {χ} {ε} : ∑ b ∈ range (p^n), ∑ c ∈ range D, C (χ̄⁻¹(b)·η̄⁻¹(c)) * (∑ j ∈ range (D·p^n), …) = ∑ j ∈ range (D·p^n), ∑ b ∈ range (p^n), ∑ c ∈ range D, C (χ̄⁻¹(b)·η̄⁻¹(c)·((ζ:K)^c·(ε:K)^b)^j) * rescale (j:K) (exp K)`
- What: RJW step (B) bookkeeping: merge each `(b,c)` character coefficient into its `j`-sum and reorder the triple sum to put `j` outermost.
- How: `Finset.mul_sum`/`map_mul` to absorb the coefficient; two `Finset.sum_comm` to swap `j` outward.
- Hypotheses: none beyond ambient (purely formal sum manipulation).
- Uses from project: `toFieldChar` (in statement)
- Used by: `rescale_exp_sub_one_mul_twist_smear`
- Visibility: private
- Lines: 1017-1066 (proof ~30 lines)
- Notes: long(30-50). `omit [hp] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.

### private lemma rescale_exp_sub_one_mul_twist_smear
- Type: `{D} [NeZero D] [Fact (1<D)] {η} (hηK …) {ζ} (hζ …) (hζK …) (hD …) {n} [NeZero (p^n)] {χ} (hχ …) (hχK …) {ε} (hε …) (hεK …) {θ} (hθ …) : (rescale ((D·p^n):K) (exp K) - 1) * (C (G(χ⁻¹)) * (map subtype (mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared …)))).subst (exp K - 1)) = -(C (G(χ⁻¹)·G(η̄⁻¹)) * ∑ j ∈ range (D·p^n), C ((toFieldChar θ) j) * rescale (j:K) (exp K))`
- What: RJW step (B) double collapse: clearing `e^{D·p^n·t} − 1` against the `G(χ⁻¹)`-smeared twist, collapsing the two coprime Gauss sums line by line into `θ̃`.
- How: `twist_subst_gaussSum_smear` for the smear; per-`b` clearing via `rescale_exp_sub_one_mul_twist_line`; `Finset.sum_neg_distrib`, `twist_smear_reindex`; absorb constants and apply `twist_char_factor_sum` to each `j`-line.
- Hypotheses: `1 < D` (Fact); `η̄`,`χ̄` primitive; `ζ`,`ε` primitive roots (in `integerRing K` and `K`); `p ∤ D`; `χ` primitive; `θ` the product.
- Uses from project: `gaussSum`, `mahlerTransform`, `twist`, `DirichletCharacter.toContinuousMapZp`, `muEtaCleared`, `toFieldChar`, `twist_subst_gaussSum_smear`, `rescale_exp_sub_one_mul_twist_line`, `twist_smear_reindex`, `twist_char_factor_sum`
- Used by: `X_mul_twist_subst_eq`
- Visibility: private
- Lines: 1068-1127 (proof ~33 lines)
- Notes: long(30-50).

### private lemma X_mul_twist_subst_eq
- Type: `{D} [NeZero D] [Fact (1<D)] {η} (hηK …) {ζ} (hζ …) (hζK …) (hD …) {n} [NeZero (p^n)] [NeZero (D·p^n)] (hM1 : 1 < D·p^n) {χ} (hχ …) (hχK …) {ε} (hε …) (hεK …) {θ} (hθ …) : X * (C (G(χ⁻¹)) * (map subtype (mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared …)))).subst (exp K - 1)) = -(C (G(χ⁻¹)·G(η̄⁻¹)) * mk (k ↦ (toFieldChar θ).genBernoulli k / k!))`
- What: RJW step (C): multiply the smeared/cleared identity by `X`, insert T504 at level `D·p^n`, cancel the regular factor `e^{D·p^n·t} − 1`.
- How: `mul_right_cancel₀ (rescale_exp_sub_one_ne_zero)`; `calc` reassociates, applies `rescale_exp_sub_one_mul_twist_smear`, then `X_mul_sum_char_rescale_exp` (T504) and `ring`.
- Hypotheses: as `rescale_exp_sub_one_mul_twist_smear` plus `NeZero (D·p^n)`, `1 < D·p^n`.
- Uses from project: `gaussSum`, `mahlerTransform`, `twist`, `DirichletCharacter.toContinuousMapZp`, `muEtaCleared`, `toFieldChar`, `genBernoulli`, `rescale_exp_sub_one_ne_zero`, `rescale_exp_sub_one_mul_twist_smear`, `X_mul_sum_char_rescale_exp`
- Used by: `X_mul_twist_muEtaCleared_subst`
- Visibility: private
- Lines: 1129-1186 (proof ~31 lines)
- Notes: long(30-50). (`calc`-based.)

### lemma X_mul_twist_muEtaCleared_subst
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη : η.IsPrimitive) {ζ} (hζ …) (hζK …) (hD …) {n} {χ} (hχ : χ.IsPrimitive) {ε} (hε …) (hεK …) {θ} (hθ …) : X * (map subtype (mahlerTransform p K (twist p K χ.toContinuousMapZp (muEtaCleared …)))).subst (exp K - 1) = -(C (G(η̄⁻¹)) * mk (k ↦ (toFieldChar θ).genBernoulli k / k!))`
- What: RJW Lem 5.12, twisted master identity in cleared exp-substituted form: `X·H_θ = −G(η⁻¹)·genBPS_{θ_K}` for `μ_θ = (μ̃_η)_χ`.
- How: Derive instances/Facts (`NeZero (D·p^n)`, `1 < D·p^n`, `toFieldChar` primitivity); set `H`, `GχR := G(χ⁻¹)`; obtain `X_mul_twist_subst_eq` (steps A/B/C); `G(χ⁻¹) ≠ 0` (`gaussSum_inv_ne_zero`), so cancel the common `C(G(χ⁻¹))` via `mul_left_cancel₀`.
- Hypotheses: `1 < D`; `η` primitive; `ζ`,`ε` primitive roots; `p ∤ D`; `χ` primitive; `θ` the product.
- Uses from project: `mahlerTransform`, `twist`, `DirichletCharacter.toContinuousMapZp`, `muEtaCleared`, `toFieldChar`, `gaussSum`, `genBernoulli`, `X_mul_twist_subst_eq`, `coe_gaussSum_zmodChar`, `gaussSum_inv_ne_zero`
- Used by: `twist_muEtaCleared_moments`
- Visibility: public
- Lines: 1188-1257 (proof ~45 lines)
- Notes: long(30-50). `classical`.

### theorem twist_muEtaCleared_moments
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη …) {ζ} (hζ …) (hD …) {n} {χ} (hχ …) {ε} (hε …) {θ} (hθ …) (m : ℕ) : ((twist p K χ.toContinuousMapZp (muEtaCleared …) (powCM p K m) : integerRing K) : K) = ((gaussSum η⁻¹ …) : K) * LvalNeg (toFieldChar θ) m`
- What: RJW Lem 5.12 moments — `∫χ̃(x)x^m dμ̃_η = G(η⁻¹)·L(θ,−m)` (cleared).
- How: Moment as `m!·[t^m]` of the substituted twist transform (`apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`); `(m+1)`-st coefficient of `X_mul_twist_muEtaCleared_subst`; identify `LvalNeg`, clear factorials by `field_simp`.
- Hypotheses: `1 < D`; `η` primitive; `ζ` primitive `D`-th root; `p ∤ D`; `χ` primitive mod `p^n`; `ε` primitive `p^n`-th root; `θ` the product; `m : ℕ`.
- Uses from project: `twist`, `DirichletCharacter.toContinuousMapZp`, `muEtaCleared`, `powCM`, `gaussSum`, `LvalNeg`, `toFieldChar`, `mahlerTransform`, `X_mul_twist_muEtaCleared_subst`, `apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`, `del`, `coe_gaussSum_zmodChar`
- Used by: `zetaEta_twisted_moments`
- Visibility: public
- Lines: 1259-1306 (proof ~31 lines)
- Notes: long(30-50).

### theorem zetaEta_twisted_moments
- Type: `{D} [NeZero D] (hD1 : 1 < D) {η} (hη …) {ζ} (hζ …) (hD …) {n} {χ} (hχ …) {ε} (hε …) {θ} (hθ …) {k} (_hk : 0 < k) : ((twist p K χ.toContinuousMapZp (res p K (isClopen_units p) (muEtaCleared …)) (powCM p K (k-1)) : integerRing K) : K) = ((gaussSum η⁻¹ …) : K) * (1 − θ(p)·p^{k−1}) * LvalNeg (toFieldChar θ) (k-1)`
- What: RJW Def + final display — the χ-twisted moments of `ζ_η := x⁻¹·Res_{ℤ_p^×}(μ_η)`: `∫χ(x)x^k dζ_η = (1 − χη(p)p^{k−1})·L(χη,1−k)` (cleared; the `x⁻¹`-shift realised as `k ↦ k−1`). This is the existence half of RJW Thm 5.7.
- How: `res_units_eq` gives `Res = 1 − φ∘ψ`; `psi_muEtaCleared` for ψ; compute the φ-term Euler factor `χ(p)·η(p)·p^m` (composition with `mulCM p`, `toContinuousMapZp_mul`); coerce `algebraMap` of `p^m`; insert `twist_muEtaCleared_moments` and `toFieldChar_prod_natCast` to fold `θ(p) = η(p)χ(p)`; finish with `ring`.
- Hypotheses: `1 < D`; `η` primitive; `ζ` primitive `D`-th root; `p ∤ D`; `χ` primitive mod `p^n`; `ε` primitive `p^n`-th root; `θ` the product; `0 < k`.
- Uses from project: `twist`, `DirichletCharacter.toContinuousMapZp`, `res`, `PadicMeasure.isClopen_units`, `muEtaCleared`, `powCM`, `gaussSum`, `LvalNeg`, `toFieldChar`, `res_units_eq`, `psi_muEtaCleared`, `phi`, `PadicMeasure.mulCM`, `DirichletCharacter.toContinuousMapZp_mul`, `DirichletCharacter.toContinuousMapZp_apply`, `twist_muEtaCleared_moments`, `toFieldChar_prod_natCast`
- Used by: unused in file
- Visibility: public
- Lines: 1308-1405 (proof ~74 lines)
- Notes: OVER-50 (needs /decompose-proof). `classical`. Three internal `have`s (`hfun`, `hphi`, `hcoe`) + large `show … from by … ; ring` cast.

### lemma hasEnoughRootsOfUnity_of_padic_roots
- Type: `(hroots : ∀ n, ∃ ζ : integerRing K, IsPrimitiveRoot ζ (p^n)) (n : ℕ) : HasEnoughRootsOfUnity (integerRing K) (Monoid.exponent (ZMod (p^n))ˣ)`
- What: Given primitive `p`-power roots, the coefficient ring has enough roots of unity for the full character dual of `(ℤ/p^n)ˣ` (the prime-to-`p` part is the Teichmüller lift of a generator mod `p`).
- How: `e := exponent (ZMod (p^n))ˣ` divides `P := p^n(p−1)` (via `Group.exponent_dvd_card`, `ZMod.card_units_eq_totient`, `Nat.totient_prime_pow`); build a primitive `P`-th root as the coprime product of a `p^n`-root and a Teichmüller `(p−1)`-root (`PadicInt.exists_primitiveRoot_card_sub_one`, `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`); take its `P/e`-th power for a primitive `e`-th root (`IsPrimitiveRoot.pow_of_dvd`).
- Hypotheses: `K` (via `integerRing K`) contains a primitive `p^n`-th root for every `n`.
- Uses from project: `integerRing`, `integerRing.isometry_algebraMap`
- Used by: `eq_zero_of_twisted_moments_eq_zero`
- Visibility: public
- Lines: 1407-1465 (proof ~49 lines)
- Notes: long(30-50). `classical`. `omit [CompleteSpace K] [CharZero K]`.

### theorem eq_zero_of_twisted_moments_eq_zero
- Type: `(hroots …) (μ : MeasureR K ℤ_[p]) (hsupp : res p K (isClopen_units p) μ = μ) (h : ∀ n χ, χ.IsPrimitive → ∀ k, 0 < k → twist p K χ.toContinuousMapZp μ (powCM p K k) = 0) : μ = 0`
- What: RJW Thm 5.7 determinacy half: a unit-supported measure on `ℤ_p` killing every `χ(x)x^k` (primitive `χ` of `p`-power conductor, `k > 0`) is zero.
- How: (B) extend vanishing to all `p`-power-level characters via the primitive core (`FactorsThrough`, `toContinuousMapZp_changeLevel`); (C) the `x`-weighted coset indicators vanish by character orthogonality (`DirichletCharacter.sum_char_inv_mul_char_eq`, `hasEnoughRootsOfUnity_of_padic_roots`); (D) extend to all locally constant `Φ` (`exists_eq_comp_toZModPow`); (E) reduce a general `f` to (D) by the unit-inverse trick (`extendByZero`, `invCM`) and density (`exists_locallyConstant_norm_sub_le'`, `norm_apply_le`).
- Hypotheses: primitive `p^n`-roots for all `n`; `μ` supported on units; `μ` kills all `χ(x)x^k`.
- Uses from project: `MeasureR`, `res`, `PadicMeasure.isClopen_units`, `twist`, `DirichletCharacter.toContinuousMapZp`, `powCM`, `charFnCM`, `DirichletCharacter.toContinuousMapZp_changeLevel`, `isClopen_toZModPow_fiber`, `hasEnoughRootsOfUnity_of_padic_roots`, `integerRing`, `integerRing.isometry_algebraMap`, `PadicMeasure.invCM`, `PadicMeasure.mulCM`(? no — `invCM` only), `extendByZero`, `extendByZero_coe_unit`, `PadicMeasure.exists_locallyConstant_norm_sub_le'`, `norm_apply_le`, `DirichletCharacter.toContinuousMapZp_apply`
- Used by: `eq_of_twisted_moments_eq`
- Visibility: public
- Lines: 1467-1683 (proof ~205 lines)
- Notes: OVER-50 (needs /decompose-proof). `classical`. Five labelled stages (B)–(E). `omit [CompleteSpace K]`.

### theorem eq_of_twisted_moments_eq
- Type: `(hroots …) (μ ν : MeasureR K ℤ_[p]) (hμ : res … μ = μ) (hν : res … ν = ν) (h : ∀ n χ, χ.IsPrimitive → ∀ k, 0 < k → twist … μ (powCM p K k) = twist … ν (powCM p K k)) : μ = ν`
- What: RJW Theorem 5.7 uniqueness: two unit-supported measures with the same χ-twisted moments agree. With `zetaEta_twisted_moments` this is the full theorem.
- How: Apply `eq_zero_of_twisted_moments_eq_zero` to `μ − ν`, discharging unit-support (linearity of `res`) and the vanishing hypothesis (`sub_eq_zero`); conclude by `sub_eq_zero.mp`.
- Hypotheses: primitive `p^n`-roots for all `n`; `μ`, `ν` unit-supported; equal χ-twisted moments.
- Uses from project: `MeasureR`, `res`, `PadicMeasure.isClopen_units`, `twist`, `DirichletCharacter.toContinuousMapZp`, `powCM`, `charFnCM`, `eq_zero_of_twisted_moments_eq_zero`
- Used by: unused in file
- Visibility: public
- Lines: 1685-1715 (proof ~16 lines)
- Notes: none. `omit [CompleteSpace K]`.

---

## File Summary

**Total declarations: 27** — 1 def (`muEtaCleared`); 26 lemmas+theorems; 0 instances; 0 structures/classes.

**Breakdown:** 12 public lemmas, 6 public theorems, 8 private lemmas, 1 public def. (15 lemmas + 11 theorems = 26 proof-carrying; the def is non-proof.)

**Key API (used by ≥3 decls in this file):**
- `muEtaCleared` (def) — the central object; used by ~12 decls.
- `isUnit_root_mul_one_add_X_sub_one` — used by 5 decls (unit denominators).
- `mahlerTransform_muEtaCleared` — used by 3.
- `subst_map_C_mul` — used by 3.
- `subst_map_sum` — used by 3.
- `rescale_exp_sub_one_mul_unit_denom` — used by 2 (borderline).
- `toFieldChar_prod_natCast` — used by 2.

**Unused within file (terminal/exported API):** `gaussSum_isUnit_of_coprime`, `muEta_term_exp_identity`, `res_units_muEtaCleared_moments`, `zetaEta_twisted_moments`, `eq_of_twisted_moments_eq`. (`gaussSum_isUnit_of_coprime` and `muEta_term_exp_identity` appear to be genuinely unused even downstream — candidate dead code; the others are the file's top-level deliverables, consumed elsewhere in the project.)

**Decls with `sorry`: NONE.**

**`set_option`: NONE.** (Several proofs open `classical`.)

**Proofs > 50 lines (OVER-50, need /decompose-proof) — 5:**
1. `eq_zero_of_twisted_moments_eq_zero` (~205 lines) — stages (B)–(E).
2. `psi_symm_inverse_denom` (~108 lines) — stages (i)–(iii).
3. `psi_muEtaCleared` (~105 lines).
4. `X_mul_muEtaCleared_subst` (~85 lines) — stages (1)–(3).
5. `zetaEta_twisted_moments` (~74 lines).

**Proofs 30–50 lines (long) — 11:**
`hasEnoughRootsOfUnity_of_padic_roots` (~49), `X_mul_twist_muEtaCleared_subst` (~45), `rescale_exp_sub_one_mul_twist_term` (~38), `twist_char_factor_sum` (~33), `twist_subst_gaussSum_smear` (~33), `rescale_exp_sub_one_mul_twist_smear` (~33), `mahlerTransform_charTwist_muEtaCleared` (~32), `muEtaCleared_moments` (~32), `X_mul_twist_subst_eq` (~31), `twist_muEtaCleared_moments` (~31), `toFieldChar_prod_natCast` (~30), `twist_smear_reindex` (~30).
