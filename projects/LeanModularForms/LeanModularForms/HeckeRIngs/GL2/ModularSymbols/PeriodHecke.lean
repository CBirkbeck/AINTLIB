/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodInvariant
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeFinite

/-!
# Hecke- and diamond-equivariance of the period map (ES-3c)

This file discharges the equivariance hypotheses `hT`/`hD` consumed by the faithfulness endgame
`HeckeRing.GL2.ModularSymbols.heckeAlgℤ_finite_of_period` of `HeckeFinite.lean`, for weight `k ≥ 2`.
Concretely it proves that the (unconditional, `k ≥ 2`) period map `periodMap'` intertwines:

* the cusp Hecke operators `heckeEnd N k n` with the integral modular-symbol Hecke operators
  `heckeSymb N k n` (`periodMap'_heckeEnd`);
* the cusp diamond operators `diamondOpCusp k d` with the integral diamond operators
  `diamondSymb N k d` (`periodMap'_diamond`),

both through the transpose `dualPrecomp`.

The analytic and symbol Hecke operators are built from the **same** Heilbronn coset representatives
(`T_p_upper` / `lowerDiamondMat`, ensured by ES-2), and the period map intertwines them via the
Möbius change of variables `z = M • w` in the contour integral.  The crux is the change-of-variables
identity, which we package as a general `SL(2, ℤ)` cusp-value covariance
(`cuspValue_symRep_sl`) and a
determinant-`p` Heilbronn covariance (`cuspValue_symAct`); both reuse the σ-conjugate-frame boundary
naturality engine of `PeriodInvariant.lean`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2, §3.5.
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise TensorProduct Interval OnePoint
open UpperHalfPlane Complex MeasureTheory Filter Asymptotics CongruenceSubgroup
  Matrix.SpecialLinearGroup MvPolynomial ConjAct

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## The general `SL(2, ℤ)` cusp-boundary naturality

The `PeriodInvariant.lean` naturality `cuspBoundary_mob_naturality` is stated for `γ ∈ Γ₁(N)`, where
the automorphy factor cancels (`⇑f ∣ γ = ⇑f`).  Here we record the version for an *arbitrary*
`g ∈ SL(2, ℤ)`, where the slash survives on the codomain: the Möbius pullback `G = F ∘ mob g` of a
primitive `F` of `periodForm f₁ Q` is a primitive of `periodForm f₂ (cast P)` for the cusp form `f₂`
with `⇑f₂ = ⇑f₁ ∣ g`.  The proof is identical to the `Γ₁(N)` case (using the general Möbius
covariance `hasDerivAt_primitive_mob_general`), since the σ-conjugate-frame boundary engine
(`tendsto_F_pole`/`tendsto_F_upper`) is already stated for general `SL(2, ℤ)`. -/

/-- **General-`SL(2, ℤ)` cusp-boundary naturality.**  For `g ∈ SL(2, ℤ)`, cusp forms `f₁`, `f₂` with
`⇑f₂ = ⇑f₁ ∣[k] g`, a primitive `F` of `periodForm f₁ (symRep g (cast P))` with vertical top value
`Finf`, and `Ginf` the top value of its Möbius pullback `G = F ∘ mob g`, the cusp boundary value of
`G` (for `f₂`) at any cusp `o` equals the cusp boundary value of `F` (for `f₁`) at the Möbius-moved
cusp `g • o`.  Generalises `cuspBoundary_mob_naturality` to all of `SL(2, ℤ)`. -/
theorem cuspBoundary_mob_naturality_sl
    (f₁ f₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g : SL(2, ℤ))
    (hf₂ : ⇑f₂ = ⇑f₁ ∣[k] g) (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (periodForm (⇑f₁) (symRep ℂ (k - 2).toNat g (castSymPow (k - 2).toNat P)) z) z)
    (Finf Ginf : ℂ)
    (hFinf : ∀ q : ℝ, Tendsto (fun Y : ℝ => F ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Finf))
    (hGinf : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => F (mob g ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf))
    (o : OnePoint ℚ) :
    (match o with
      | (s : ℚ) => botVal f₂ (castSymPow (k - 2).toNat P) (fun z => F (mob g z)) s
      | .infty => Ginf) =
    (match (Matrix.SpecialLinearGroup.mapGL ℚ g) • o with
      | (r : ℚ) => botVal f₁ (symRep ℂ (k - 2).toNat g (castSymPow (k - 2).toNat P)) F r
      | .infty => Finf) := by
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symRep ℂ (k - 2).toNat g cP with hQ
  set G : ℂ → ℂ := fun z => F (mob g z) with hG
  -- `G = F ∘ mob g` is a primitive of `periodForm f₂ cP` (general Möbius covariance + slash).
  have hGderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt G (periodForm (⇑f₂) cP z) z := by
    intro z hz
    have hd := hasDerivAt_primitive_mob_general (⇑f₁) g cP hk F hF hz
    rwa [← hf₂] at hd
  -- Entries of `mapGL ℚ g` are the integer entries of `g`, cast.
  have hent : ∀ i j : Fin 2, (Matrix.SpecialLinearGroup.mapGL ℚ g) i j = ((g i j : ℤ) : ℚ) := by
    intro i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  -- Bottom boundary value of `F` at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotF : ∀ r : ℚ, Tendsto (fun Y : ℝ => F ((r : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botVal f₁ Q F r)) := fun r => tendsto_primitive_vertical_nhdsGT_zero f₁ Q r F hF
  -- Bottom boundary value of `G` at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotG : ∀ s : ℚ, Tendsto (fun Y : ℝ => G ((s : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botVal f₂ cP G s)) := fun s => tendsto_primitive_vertical_nhdsGT_zero f₂ cP s G hGderiv
  -- `mob 1 = id`.
  have hmob1 : ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z := fun z => by simp [mob]
  cases o with
  | infty =>
    show Ginf = _
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 = 0
    · rw [if_pos hc]
      have hc0 : (g 1 0 : ℝ) = 0 := by
        have : ((g 1 0 : ℤ) : ℚ) = 0 := by rw [← hent 1 0]; exact hc
        exact_mod_cast this
      exact tendsto_nhds_unique (hGinf 0) (tendsto_F_upper f₁ Q F hF Finf hFinf g 0 hc0)
    · rw [if_neg hc]
      set r : ℚ := (Matrix.SpecialLinearGroup.mapGL ℚ g) 0 0 /
        (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 with hr
      show Ginf = botVal f₁ Q F r
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) • (r : OnePoint ℚ) = ∞ := by
        have hgr : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (∞ : OnePoint ℚ) = (r : OnePoint ℚ) := by
          rw [OnePoint.smul_infty_eq_ite, if_neg hc]
        rw [map_inv, ← hgr, ← mul_smul, inv_mul_cancel, one_smul]
      obtain ⟨hcinv, hpoleinv⟩ := pole_of_smul_infty g⁻¹ r hsmulr
      have hbotr := tendsto_F_pole f₁ hk Q F hF g Ginf hGinf 1 (r:ℝ)
        (by simpa using hcinv) (by simpa using hpoleinv)
      simp only [hmob1] at hbotr
      exact (tendsto_nhds_unique (hbotF r) hbotr).symm
  | coe s =>
    show botVal f₂ cP G s = _
    rw [OnePoint.smul_some_eq_ite]
    by_cases hc : (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 * (s:ℚ)
        + (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 1 = 0
    · rw [if_pos hc]
      have hsmuls : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (s : OnePoint ℚ) = ∞ := by
        rw [OnePoint.smul_some_eq_ite, if_pos hc]
      obtain ⟨hcs, hpoles⟩ := pole_of_smul_infty g s hsmuls
      have hbots := tendsto_F_pole f₁ hk Q F hF 1 Finf
        (by intro q; simpa only [hmob1] using hFinf q) g (s:ℝ)
        (by simpa using hcs) (by simpa using hpoles)
      have hbotGs : Tendsto (fun Y : ℝ => F (mob g ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botVal f₂ cP G s)) := hbotG s
      exact tendsto_nhds_unique hbotGs hbots
    · rw [if_neg hc]
      set r : ℚ := ((Matrix.SpecialLinearGroup.mapGL ℚ g) 0 0 * (s:ℚ)
          + (Matrix.SpecialLinearGroup.mapGL ℚ g) 0 1)
        / ((Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 * (s:ℚ)
          + (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 1) with hr
      show botVal f₂ cP G s = botVal f₁ Q F r
      have hgsr : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (s : OnePoint ℚ) = (r : OnePoint ℚ) := by
        rw [OnePoint.smul_some_eq_ite, if_neg hc]
      obtain ⟨σ, hσ⟩ := ((r : OnePoint ℚ)).exists_mem_SL2 ℤ
      haveI harith : (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ •
          ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
        have hmap : (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
            = ((mapGL ℚ σ)⁻¹).map (algebraMap ℚ ℝ) := by rw [map_inv, map_mapGL]
        rw [hmap]
        exact Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
      obtain ⟨Lσ, hLσ⟩ := exists_tendsto_primitive_vertical_atTop'
        (CuspForm.translate f₁ (Matrix.SpecialLinearGroup.mapGL ℝ σ))
        (symRep ℂ (k - 2).toNat σ⁻¹ Q) (fun z => F (mob σ z)) (by
          intro z hz
          have hsr : symRep ℂ (k - 2).toNat σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) = Q := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
          have hd := hasDerivAt_primitive_mob_general (⇑f₁) σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) hk F
            (by rwa [hsr]) hz
          have hcoe : ⇑(CuspForm.translate f₁ (Matrix.SpecialLinearGroup.mapGL ℝ σ))
              = ⇑f₁ ∣[k] σ := by rw [ModularForm.SL_slash]; rfl
          rw [hcoe]; exact hd)
      have hLσ' : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop
          (𝓝 Lσ) := hLσ
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) • (r : OnePoint ℚ) = ∞ := by
        rw [map_inv, ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
      have hsmulσγs : (Matrix.SpecialLinearGroup.mapGL ℚ (σ⁻¹ * g)) • (s : OnePoint ℚ) = ∞ := by
        rw [map_mul, mul_smul, hgsr, map_inv, ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
      obtain ⟨hcD, hpoleD⟩ := pole_of_smul_infty (σ⁻¹ * g) s hsmulσγs
      have hLHS := tendsto_F_pole f₁ hk Q F hF σ Lσ hLσ' g (s:ℝ) hcD hpoleD
      have hbotGs : Tendsto (fun Y : ℝ => F (mob g ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botVal f₂ cP G s)) := hbotG s
      obtain ⟨hcR, hpoleR⟩ := pole_of_smul_infty σ⁻¹ r hsmulr
      have hRHS := tendsto_F_pole f₁ hk Q F hF σ Lσ hLσ' 1 (r:ℝ)
        (by simpa using hcR) (by simpa using hpoleR)
      simp only [hmob1] at hRHS
      rw [tendsto_nhds_unique hbotGs hLHS, tendsto_nhds_unique (hbotF r) hRHS]

/-! ## The general `SL(2, ℤ)` cusp-value covariance

Assembling the boundary naturality with the primitive / FTC machinery of `PeriodInvariant.lean`, we
obtain the change-of-variables for the cusp value under an arbitrary `g ∈ SL(2, ℤ)`: there is a
`c`-independent constant `T` with
`cuspValue f₁ (symRep g (cast P)) (g • c) = cuspValue f₂ (cast P) c + T`,
where `⇑f₂ = ⇑f₁ ∣ g`.  (For `g = γ ∈ Γ₁(N)`, `f₂ = f₁` and this is `cuspValue_symRep_gamma`.) -/

/-- **The general `SL(2, ℤ)` cusp-value covariance (`k ≥ 2`).**  For `g ∈ SL(2, ℤ)` and cusp forms
`f₁`, `f₂` with `⇑f₂ = ⇑f₁ ∣[k] g`, the cusp value of `f₁` against `symRep g (cast P)` at the
Möbius-moved cusp `g • c` equals the cusp value of `f₂` against `cast P` at `c`, up to a
`c`-independent constant.  Mirrors `cuspValue_symRep_gamma` for arbitrary `g`. -/
theorem cuspValue_symRep_sl (f₁ f₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g : SL(2, ℤ))
    (hf₂ : ⇑f₂ = ⇑f₁ ∣[k] g) (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k) :
    ∃ T : ℂ, ∀ c : Projectivization ℚ (Fin 2 → ℚ),
      cuspValue f₁ (symRep ℂ (k - 2).toNat g (castSymPow (k - 2).toNat P))
          ((Matrix.SpecialLinearGroup.mapGL ℚ g) • c) =
        cuspValue f₂ (castSymPow (k - 2).toNat P) c + T := by
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symRep ℂ (k - 2).toNat g cP with hQ
  -- A primitive `F` of `periodForm f₁ Q` on the upper half-plane.
  obtain ⟨F, hF⟩ := Complex.isExactOn_upperHalf (differentiableOn_periodForm f₁ Q)
  have hFz : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f₁) Q z) z := hF
  -- `G := F ∘ mob g` is a primitive of `periodForm f₂ cP`.
  have hG : ∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun w => F (mob g w)) (periodForm (⇑f₂) cP z) z := by
    intro z hz
    have hd := hasDerivAt_primitive_mob_general (⇑f₁) g cP hk F hFz hz
    rwa [← hf₂] at hd
  -- Top boundary values.
  obtain ⟨Finf, hFinf⟩ := exists_tendsto_primitive_vertical_atTop f₁ Q F hFz
  obtain ⟨Ginf, hGinf⟩ := exists_tendsto_primitive_vertical_atTop f₂ cP
    (fun w => F (mob g w)) hG
  have hGinf' : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => F (mob g ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf) := hGinf
  refine ⟨Finf - Ginf, fun c => ?_⟩
  -- Cusp-value formulas for both sides.
  have hcvQ := cuspValue_eq_top_sub_botVal f₁ Q F hFz Finf hFinf
    ((Matrix.SpecialLinearGroup.mapGL ℚ g) • c)
  have hcvP := cuspValue_eq_top_sub_botVal f₂ cP (fun w => F (mob g w)) hG Ginf hGinf c
  rw [hcvQ, hcvP]
  -- The cusp dictionary: the `OnePoint` representative of `(mapGL ℚ g) • c` is
  -- `(mapGL ℚ g) • (rep c)`.
  have hdict : (OnePoint.equivProjectivization ℚ).symm ((Matrix.SpecialLinearGroup.mapGL ℚ g) • c)
      = (Matrix.SpecialLinearGroup.mapGL ℚ g) • (OnePoint.equivProjectivization ℚ).symm c := by
    rw [Equiv.symm_apply_eq, OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  rw [hdict]
  -- Reduce to the boundary naturality.
  have hnat := cuspBoundary_mob_naturality_sl f₁ f₂ g hf₂ P hk F hFz Finf Ginf hFinf hGinf'
    ((OnePoint.equivProjectivization ℚ).symm c)
  rw [hQ, hcP]
  linear_combination hnat

/-! ## The determinant-`1` change of variables at the level of `rawPairing`

Summing the cusp-value covariance against a degree-`0` divisor, the `c`-independent tail period
cancels (its weight is `Σ_c D(c) = 0`), giving the clean change of variables
`rawPairing f₂ z = rawPairing f₁ (fullModSymRep g z)` for `g ∈ SL(2, ℤ)` and `⇑f₂ = ⇑f₁ ∣ g`. -/

/-- **The `SL(2, ℤ)` change of variables for `rawPairing` (`k ≥ 2`).**  For `g ∈ SL(2, ℤ)` and cusp
forms `f₁`, `f₂` with `⇑f₂ = ⇑f₁ ∣[k] g`, the raw period pairing satisfies
`rawPairing f₂ x = rawPairing f₁ (fullModSymRep g x)`.  The `c`-independent tail of
`cuspValue_symRep_sl` cancels because the divisor has degree `0`. -/
theorem rawPairing_fullModSymRep_sl (f₁ f₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g : SL(2, ℤ))
    (hf₂ : ⇑f₂ = ⇑f₁ ∣[k] g) (hk : 2 ≤ k) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    rawPairing f₂ x = rawPairing f₁ (fullModSymRep ℤ (k - 2).toNat g x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul D P =>
    -- Expand both sides as `Finsupp.sum` against `cuspValue`.
    obtain ⟨T, hT⟩ := cuspValue_symRep_sl f₁ f₂ g hf₂ P hk
    -- The RHS `rawPairing f₁ (fullModSymRep g (D ⊗ P))` is *definitionally* the `rawBilin` of the
    -- `g`-moved divisor and `symRep`-acted polynomial (`fullModSymRep_apply` and `rawPairing_tmul`
    -- are `rfl`); `show` bridges the `Module ℤ` instance diamond on the tensor type.
    show rawBilin f₂ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff P =
      rawBilin f₁ ((div0Rep ℤ g D : Div0 ℤ) :
          MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff
        (symRep ℤ (k - 2).toNat g P)
    -- Expand `rawBilin` as a `Finsupp.sum`.
    have hrb : ∀ (D' : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P' : SymPow ℤ (k - 2).toNat),
        rawBilin f₁ D' P' =
          D'.sum (fun c n => (n : ℂ) * cuspValue f₁ (castSymPow (k - 2).toNat P') c) := by
      intro D' P'
      simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
    have hrb₂ : ∀ (D' : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P' : SymPow ℤ (k - 2).toNat),
        rawBilin f₂ D' P' =
          D'.sum (fun c n => (n : ℂ) * cuspValue f₂ (castSymPow (k - 2).toNat P') c) := by
      intro D' P'
      simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
    rw [hrb, hrb₂, castSymPow_symRep]
    -- Reindex the `g`-image divisor sum injectively.
    have hdiv : ((div0Rep ℤ g D) : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff =
        Finsupp.mapDomain ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • ·)
          (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff := by
      rw [div0Rep_apply]
    have hinj : Function.Injective
        (fun c : Projectivization ℚ (Fin 2 → ℚ) =>
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • c) :=
      MulAction.injective _
    rw [hdiv, Finsupp.sum_mapDomain_index_inj hinj]
    -- Combine into a single degree-0 sum of the (constant) cusp-value difference.
    rw [← sub_eq_zero, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    -- Each summand:
    -- `n · cuspValue f₂ (cast P) c − n · cuspValue f₁ (symRep g (cast P)) (g•c) = n · (−T)`.
    have hsummand : ∀ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) *
            cuspValue f₂ (castSymPow (k - 2).toNat P) c -
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) *
            cuspValue f₁ (symRep ℂ (k - 2).toNat g (castSymPow (k - 2).toNat P))
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • c) =
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) * (-T) := by
      intro c _
      have hmapeq : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • c =
          (Matrix.SpecialLinearGroup.mapGL ℚ g) • c := by
        rw [Projectivization.matrixSpecialLinearGroup_smul_def]; rfl
      rw [hmapeq, hT c]; ring
    rw [Finset.sum_congr rfl hsummand, ← Finset.sum_mul]
    -- The total weight `Σ_c D(c) = 0`.
    have hsum0 : (∑ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ)) = 0 := by
      rw [← Int.cast_sum]
      have := Div0.sum_coeff_eq_zero D
      rw [Finsupp.sum] at this
      rw [this, Int.cast_zero]
    rw [hsum0, zero_mul]
  | add x y hx hy =>
    rw [map_add, hx, hy]
    exact (map_add (rawPairing f₁) _ _).symm.trans
      (congrArg (rawPairing f₁) (map_add (fullModSymRep ℤ (k - 2).toNat g) x y).symm)

/-! ## The diamond equivariance `hD`

`diamondOpCusp k d` is the slash by a chosen `Γ₀(N)` representative `γ_d`, and
`diamondSymb N k d` is
the descent of `fullModSymRep γ_d` to `Γ₁(N)`-coinvariants — using the *same* representative
`γ_d = (Gamma0MapUnits_surjective d).choose`.  Hence the diamond equivariance is the
det-`1` change of
variables `rawPairing_fullModSymRep_sl` for `g = γ_d`. -/

/-- **Diamond equivariance of the period map (`k ≥ 2`).**  The period map intertwines the cusp
diamond operator `diamondOpCusp k d` with the integral modular-symbol diamond operator
`diamondSymb N k d` (through the transpose `dualPrecomp`).  This is the hypothesis `hD` of the
endgame. -/
theorem periodMap'_diamond (hk : 2 ≤ k) (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    periodMap' N k hk (diamondOpCusp k d f) =
      dualPrecomp (diamondSymb N k d) (periodMap' N k hk f) := by
  -- The shared `Γ₀(N)` representative `γ_d`.
  set γd := (Gamma0MapUnits_surjective d).choose with hγd
  -- The slash relation: `⇑(diamondOpCusp k d f) = ⇑f ∣[k] (γ_d : SL(2, ℤ))`.
  have hslash : ⇑(diamondOpCusp k d f) = ⇑f ∣[k] ((γd : ↥(Gamma0 N)) : SL(2, ℤ)) := by
    rw [ModularForm.SL_slash]; rfl
  -- Reduce to `𝕄.mk` generators.
  refine LinearMap.ext fun μ => ?_
  obtain ⟨z, rfl⟩ := 𝕄.mk_surjective N k μ
  rw [periodMap'_apply_mk, dualPrecomp_apply]
  -- The symbol diamond on a generator is `𝕄.mk (fullModSymRep γ_d z)`.
  have hdsym : diamondSymb N k d (𝕄.mk N k z)
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat ((γd : ↥(Gamma0 N)) : SL(2, ℤ)) z) := by
    rw [diamondSymb, hγd, diamondSymbAux_mk]
  rw [hdsym, periodMap'_apply_mk]
  -- Apply the det-`1` change of variables.
  exact rawPairing_fullModSymRep_sl f (diamondOpCusp k d f)
    ((γd : ↥(Gamma0 N)) : SL(2, ℤ)) hslash hk z

/-! ## The determinant-`p` Heilbronn change of variables (the analogue of the det-`1` engine)

We now mirror the entire det-`1` `SL(2, ℤ)` covariance engine (`mob`, `periodForm_mob_general`,
`cuspBoundary_mob_naturality_sl`, `cuspValue_symRep_sl`, `rawPairing_fullModSymRep_sl`)
for a general
integer matrix `M` of positive determinant — in particular the Heilbronn coset matrices `upperMat`,
`lowerDiamondMat` of determinant `p`.  The Möbius map `mobM M w = (M₀₀w+M₀₁)/(M₁₀w+M₁₁)` now has
derivative `det(M)/(M₁₀w+M₁₁)²`, and the project's slash carries the determinant factor
`|det M|^{k-1}`, so the integrand-level change of variables again cancels exactly:
`periodForm h₀ (symAct M R)(mobM M w) · (det M · D⁻²) = periodForm (h₀ ∣ heilbronnGL M) R w`. -/

/-- The Möbius transformation `w ↦ (M₀₀w + M₀₁)/(M₁₀w + M₁₁)` of an integer matrix `M`, as a map
`ℂ → ℂ`.  Generalises `mob` (which is the `SL(2, ℤ)` case, `det = 1`) to determinant `p`. -/
def mobM (M : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * w + (M 0 1 : ℂ)) / ((M 1 0 : ℂ) * w + (M 1 1 : ℂ))

omit [NeZero N] in
/-- The denominator `M₁₀ w + M₁₁` is nonzero for `w` in the open upper half-plane, when `det M ≠ 0`.
-/
theorem denom_mobM_ne (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {w : ℂ} (hw : 0 < w.im) :
    ((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ≠ 0 := by
  have hd := UpperHalfPlane.denom_ne_zero_of_im (glMap (heilbronnGL M hM)) hw.ne'
  rw [UpperHalfPlane.denom] at hd
  intro hc
  apply hd
  show ((glMap (heilbronnGL M hM) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * w +
      ((glMap (heilbronnGL M hM) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = 0
  have h10 : ((glMap (heilbronnGL M hM) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = (M 1 0 : ℂ) := by
    simp [glMap, heilbronnGL, qMat, Matrix.GeneralLinearGroup.map, Units.map]
  have h11 : ((glMap (heilbronnGL M hM) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) = (M 1 1 : ℂ) := by
    simp [glMap, heilbronnGL, qMat, Matrix.GeneralLinearGroup.map, Units.map]
  rw [h10, h11]; exact hc

omit [NeZero N] in
/-- On the upper half-plane, `mobM M` is the (positive-determinant) Möbius action of
`heilbronnGL M`.
-/
theorem mobM_eq_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (z : ℍ) :
    mobM M (z : ℂ) = ((glMap (heilbronnGL M hM.ne') • z : ℍ) : ℂ) := by
  have hdpos : 0 < (glMap (heilbronnGL M hM.ne')).det.val :=
    glMap_det_pos_of_rat_det_pos (heilbronnGL M hM.ne') (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, heilbronnGL_coe]
      show 0 < (qMat M).det
      rw [qMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom]
      exact Int.cast_pos.mpr hM)
  rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, UpperHalfPlane.num, UpperHalfPlane.denom, mobM]
  have hcast : ∀ i j : Fin 2,
      ((glMap (heilbronnGL M hM.ne') : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ) = (M i j : ℂ) := by
    intro i j
    simp [glMap, heilbronnGL, qMat, Matrix.GeneralLinearGroup.map, Units.map]
  rw [hcast, hcast, hcast, hcast]

omit [NeZero N] in
/-- **The Möbius derivative (determinant `p`).**
`d/dw[(M₀₀w+M₀₁)/(M₁₀w+M₁₁)] = det(M)/(M₁₀w+M₁₁)²`.
Generalises `hasDerivAt_mob` (which has `det = 1`). -/
theorem hasDerivAt_mobM (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (mobM M)
      ((M.det : ℂ) * (((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ^ (2 : ℤ))⁻¹) w := by
  have hne := denom_mobM_ne M hM hw
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = (M.det : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hnum : HasDerivAt (fun w : ℂ => (M 0 0 : ℂ) * w + (M 0 1 : ℂ)) (M 0 0 : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (M 0 0 : ℂ)).add_const (M 0 1 : ℂ)
  have hden : HasDerivAt (fun w : ℂ => (M 1 0 : ℂ) * w + (M 1 1 : ℂ)) (M 1 0 : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (M 1 0 : ℂ)).add_const (M 1 1 : ℂ)
  have hdiv := hnum.div hden hne
  have hfun : mobM M = (fun w : ℂ => (M 0 0 : ℂ) * w + (M 0 1 : ℂ)) /
      (fun w : ℂ => (M 1 0 : ℂ) * w + (M 1 1 : ℂ)) := rfl
  rw [hfun]
  have hval : (M.det : ℂ) * (((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ^ (2 : ℤ))⁻¹ =
      ((M 0 0 : ℂ) * ((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) -
        ((M 0 0 : ℂ) * w + (M 0 1 : ℂ)) * (M 1 0 : ℂ)) /
        ((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ^ 2 := by
    rw [zpow_two, sq, ← hdet]; ring
  rw [hval]
  exact hdiv

/-- The complex `Sym^m` substitution attached to the adjugate of an integer matrix `M`: the
`ℂ`-linear endomorphism `P ↦ substAlgHom (adjugate M) P` of `SymPow ℂ m`.  The complex analogue of
the integral `symAct M m`. -/
noncomputable def symActC (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) : SymPow ℂ m →ₗ[ℂ] SymPow ℂ m :=
  LinearMap.restrict (substAlgHom (Matrix.adjugate M |>.map (Int.castRingHom ℂ))).toLinearMap <| by
    intro x hx
    exact substAlgHom_isHomogeneous (Matrix.adjugate M |>.map (Int.castRingHom ℂ)) hx

theorem symActC_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (P : SymPow ℂ m) :
    ((symActC M m P : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ)
      = substAlgHom ((Matrix.adjugate M).map (Int.castRingHom ℂ)) (P : MvPolynomial (Fin 2) ℂ) :=
  rfl

/-- The integral cast `castSymPow` intertwines `symAct` (over `ℤ`) and `symActC` (over `ℂ`):
`castSymPow (symAct M P) = symActC M (castSymPow P)`.  Analogue of `castSymPow_symRep`. -/
theorem castSymPow_symActC {m : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (P : SymPow ℤ m) :
    castSymPow m (symAct M m P) = symActC M m (castSymPow m P) := by
  apply Subtype.ext
  show MvPolynomial.map (Int.castRingHom ℂ) ((symAct M m P : SymPow ℤ m) : MvPolynomial (Fin 2) ℤ)
    = ((symActC M m (castSymPow m P) : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ)
  rw [symAct_coe, symActC_coe]
  show MvPolynomial.map (Int.castRingHom ℂ) (substAlgHom (Matrix.adjugate M)
      (P : MvPolynomial (Fin 2) ℤ))
    = substAlgHom ((Matrix.adjugate M).map (Int.castRingHom ℂ))
        (MvPolynomial.map (Int.castRingHom ℂ) (P : MvPolynomial (Fin 2) ℤ))
  induction (P : MvPolynomial (Fin 2) ℤ) using MvPolynomial.induction_on with
  | C a => simp [substAlgHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, substAlgHom_X, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    simp [Matrix.map_apply]

omit [NeZero N] in
/-- **The `evalSym1` covariance for determinant `p`.**  For an integer matrix `M` (det `≠ 0`),
writing `D = M₁₀z + M₁₁`, the adjugate substitution satisfies
`evalSym1 m (symActC M P) (mobM M z) = (det M)^m · (D^m)⁻¹ · evalSym1 m P z`.  Generalises
`evalSym1_symRep_smul`: the extra `(det M)^m` is the new determinant scaling. -/
theorem evalSym1_symActC_mobM {m : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0)
    (P : SymPow ℂ m) {z : ℂ} (hz : 0 < z.im) :
    evalSym1 m (symActC M m P) (mobM M z) =
      ((M.det : ℂ) ^ m) * (((M 1 0 : ℂ) * z + (M 1 1 : ℂ)) ^ m)⁻¹ * evalSym1 m P z := by
  have hD : ((M 1 0 : ℂ) * z + (M 1 1 : ℂ)) ≠ 0 := denom_mobM_ne M hM hz
  set D : ℂ := (M 1 0 : ℂ) * z + (M 1 1 : ℂ) with hDdef
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = (M.det : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  -- Entries of `(adjugate M).map (cast)`.
  have hadj : (Matrix.adjugate M).map (Int.castRingHom ℂ) =
      !![(M 1 1 : ℂ), -(M 0 1 : ℂ); -(M 1 0 : ℂ), (M 0 0 : ℂ)] := by
    rw [Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  -- Apply `evalSym1_substAlgHom` with the adjugate matrix.
  rw [show symActC M m P = ⟨substAlgHom ((Matrix.adjugate M).map (Int.castRingHom ℂ))
        (P : MvPolynomial (Fin 2) ℂ),
      substAlgHom_isHomogeneous _ P.2⟩ from Subtype.ext (symActC_coe M m P),
    evalSym1_substAlgHom, hadj]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  -- `M₁₁·(mobM M z) - M₀₁ = (det M)·z / D` and `-M₁₀·(mobM M z) + M₀₀ = (det M) / D`.
  have hmob : mobM M z = ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) / D := rfl
  have hdetC : (M.det : ℂ) ≠ 0 := by exact_mod_cast hM
  have hc0 : (M 1 1 : ℂ) * (mobM M z) + -(M 0 1 : ℂ)
      = (M.det : ℂ) * z / D := by
    rw [hmob, eq_div_iff hD]; field_simp; linear_combination (z : ℂ) * hdet
  have hc1 : -(M 1 0 : ℂ) * (mobM M z) + (M 0 0 : ℂ) = (M.det : ℂ) / D := by
    rw [hmob, eq_div_iff hD]; field_simp; linear_combination hdet
  rw [show ((M 1 1 : ℂ) * mobM M z + -(M 0 1 : ℂ)) = (M.det : ℂ) * z / D from hc0,
    show (-(M 1 0 : ℂ) * mobM M z + (M 0 0 : ℂ)) = (M.det : ℂ) / D from hc1]
  -- Pull out the homogeneous degree-`m` scaling: eval at `(det·z/D, det/D) = (det/D)·(z,1)`.
  have hE : D / (M.det : ℂ) ≠ 0 := div_ne_zero hD hdetC
  have hdiv := evalSym1_div m P z (D / (M.det : ℂ)) hE
  have he0 : (M.det : ℂ) * z / D = z / (D / (M.det : ℂ)) := by
    rw [div_div_eq_mul_div, mul_comm]
  have he1 : (M.det : ℂ) / D = 1 / (D / (M.det : ℂ)) := by rw [one_div, inv_div]
  have hscale : MvPolynomial.eval ![(M.det : ℂ) * z / D, (M.det : ℂ) / D]
        (P : MvPolynomial (Fin 2) ℂ)
      = ((D / (M.det : ℂ)) ^ m)⁻¹ * evalSym1 m P z := by rw [← hdiv, he0, he1]
  rw [hscale, div_pow]
  -- `(D/det)^{-m} · evalSym1 P z = det^m · D^{-m} · evalSym1 P z`.
  have hDm : (D ^ m : ℂ) ≠ 0 := pow_ne_zero _ hD
  have hdetm : ((M.det : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hdetC
  field_simp

omit [NeZero N] in
/-- **Möbius change of variables for a determinant-`p` integer matrix `M` (slash form).**  For any
`h0 : ℍ → ℂ`, weight `k ≥ 2`, `w` in the upper half-plane and `R : Sym^{k-2}`, the period integrand
of `symActC M R` evaluated at `mobM M w`, times the Möbius derivative `det(M)·D⁻²`,
equals the period
integrand of the slashed function `h0 ∣ heilbronnGL M` at `w`.  The determinant factors
`det(M)^{1-k}·det(M)^{k-2}·det(M) = 1` and the automorphy factors `D^{k-(k-2)-2} = 1`
cancel exactly.
The determinant-`p` analogue of `periodForm_mob_general`. -/
theorem periodForm_mobM_general (h0 : ℍ → ℂ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
    (R : SymPow ℂ (k - 2).toNat) (hk : 2 ≤ k) {w : ℂ} (hw : 0 < w.im) :
    periodForm h0 (symActC M (k - 2).toNat R) (mobM M w) *
          ((M.det : ℂ) * (((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ^ (2 : ℤ))⁻¹)
      = periodForm (h0 ∣[k] (heilbronnGL M hM.ne')) R w := by
  have hne : (M 1 0 : ℂ) * w + (M 1 1 : ℂ) ≠ 0 := denom_mobM_ne M hM.ne' hw
  have hdetC : (M.det : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set D : ℂ := (M 1 0 : ℂ) * w + (M 1 1 : ℂ) with hDdef
  set wH : ℍ := ⟨w, hw⟩ with hwH
  have hofw : UpperHalfPlane.ofComplex w = wH := by
    rw [show w = (wH : ℂ) from rfl, UpperHalfPlane.ofComplex_apply wH]
  have hmobcoe : mobM M w = ((glMap (heilbronnGL M hM.ne') • wH : ℍ) : ℂ) := mobM_eq_smul M hM wH
  have hmobpos : 0 < (mobM M w).im := by
    rw [hmobcoe]; exact ((glMap (heilbronnGL M hM.ne') • (⟨w, hw⟩ : ℍ) : ℍ)).im_pos
  rw [periodForm_apply_of_im_pos h0 _ hmobpos, periodForm_apply_of_im_pos (h0 ∣[k] _) R hw]
  -- The evaluation factor via the `symActC` Möbius covariance (`det^m`-scaled).
  have hev : evalSym1 (k - 2).toNat (symActC M (k - 2).toNat R) (mobM M w)
      = ((M.det : ℂ) ^ (k - 2).toNat) * (D ^ (k - 2).toNat)⁻¹ * evalSym1 (k - 2).toNat R w :=
    evalSym1_symActC_mobM M hM.ne' R hw
  -- The automorphy factor via the project slash.
  have hdpos : 0 < (glMap (heilbronnGL M hM.ne')).det.val :=
    glMap_det_pos_of_rat_det_pos (heilbronnGL M hM.ne') (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, heilbronnGL_coe]
      show 0 < (qMat M).det
      rw [qMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom]
      exact Int.cast_pos.mpr hM)
  have hdeneq : UpperHalfPlane.denom (glMap (heilbronnGL M hM.ne')) (wH : ℂ) = D := by
    rw [UpperHalfPlane.denom, hDdef]
    have h10 : ((glMap (heilbronnGL M hM.ne') : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
        (M 1 0 : ℂ) := by
      simp [glMap, heilbronnGL, qMat, Matrix.GeneralLinearGroup.map, Units.map]
    have h11 : ((glMap (heilbronnGL M hM.ne') : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
        (M 1 1 : ℂ) := by
      simp [glMap, heilbronnGL, qMat, Matrix.GeneralLinearGroup.map, Units.map]
    rw [h10, h11]
  have hv : (glMap (heilbronnGL M hM.ne')).det.val = (M.det : ℝ) := by
    rw [show (glMap (heilbronnGL M hM.ne')).det.val
        = algebraMap ℚ ℝ (heilbronnGL M hM.ne').det.val from
      congr_arg Units.val (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ)
        (heilbronnGL M hM.ne'))]
    show ((((heilbronnGL M hM.ne') : Matrix (Fin 2) (Fin 2) ℚ).det : ℚ) : ℝ) = (M.det : ℝ)
    rw [heilbronnGL_coe, qMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom]
    norm_cast
  have hdetval : ((|(glMap (heilbronnGL M hM.ne')).det.val| : ℝ) : ℂ) = (M.det : ℂ) := by
    rw [hv, abs_of_pos (by rw [hv] at hdpos; exact_mod_cast hM)]; norm_cast
  have haut : h0 ⟨mobM M w, hmobpos⟩
      = ((M.det : ℂ) ^ (1 - k)) * (D ^ k) * (h0 ∣[k] (heilbronnGL M hM.ne')) wH := by
    have hpt : (⟨mobM M w, hmobpos⟩ : ℍ) = (glMap (heilbronnGL M hM.ne')) • wH := by
      apply UpperHalfPlane.ext; exact hmobcoe
    rw [hpt]
    have happ : (h0 ∣[k] (heilbronnGL M hM.ne')) wH =
        (UpperHalfPlane.σ (glMap (heilbronnGL M hM.ne')))
          (h0 ((glMap (heilbronnGL M hM.ne')) • wH)) *
          ((|(glMap (heilbronnGL M hM.ne')).det.val| : ℝ) : ℂ) ^ (k - 1) *
          UpperHalfPlane.denom (glMap (heilbronnGL M hM.ne')) wH ^ (-k) := by
      show (h0 ∣[k] (glMap (heilbronnGL M hM.ne'))) wH = _
      rw [ModularForm.slash_apply]
    rw [hdeneq, hdetval] at happ
    have hσ : (UpperHalfPlane.σ (glMap (heilbronnGL M hM.ne')))
        (h0 ((glMap (heilbronnGL M hM.ne')) • wH)) = h0 ((glMap (heilbronnGL M hM.ne')) • wH) := by
      rw [UpperHalfPlane.σ, if_pos hdpos]; rfl
    rw [hσ] at happ
    -- `happ : (h0∣M) wH = h0(M•wH) · det^{k-1} · D^{-k}`.  Solve for `h0(M•wH)`.
    have hDk : (D ^ k : ℂ) ≠ 0 := zpow_ne_zero _ hne
    have hdetk : ((M.det : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ hdetC
    rw [happ, zpow_neg]
    rw [show (1 - k : ℤ) = -(k - 1) by ring, zpow_neg]
    field_simp
  -- Combine: `[det^{1-k}·D^k·(h0∣M)wH] · [det^m·(D^m)⁻¹·evalSym1 R w] · [det·(D^2)⁻¹]`.
  -- det exponent: `(1-k)+m+1 = 0`; D exponent: `k-m-2 = 0` (with `m = k-2`).
  have hDk : D ^ k = D ^ (k - 2).toNat * D ^ (2 : ℤ) := by
    rw [← zpow_natCast D (k - 2).toNat, ← zpow_add₀ hne,
      show ((k - 2).toNat : ℤ) + 2 = k by omega]
  have hdetk : (M.det : ℂ) ^ (1 - k) = ((M.det : ℂ) ^ (k - 2).toNat)⁻¹ * ((M.det : ℂ))⁻¹ := by
    rw [show (1 - k : ℤ) = -(((k - 2).toNat : ℤ) + 1) by omega, zpow_neg, zpow_add₀ hdetC,
      mul_inv, zpow_natCast, zpow_one]
  have hD2 : (D ^ (2 : ℤ) : ℂ) ≠ 0 := zpow_ne_zero _ hne
  have hDmn : (D ^ (k - 2).toNat : ℂ) ≠ 0 := pow_ne_zero _ hne
  have hdetmn : ((M.det : ℂ) ^ (k - 2).toNat) ≠ 0 := pow_ne_zero _ hdetC
  rw [hDk, hdetk] at haut
  rw [hev]
  field_simp at haut ⊢
  linear_combination (evalSym1 (k - 2).toNat R w) * haut

omit [NeZero N] in
/-- **The `M`-pullback primitive (determinant `p`).**  If `Fp` is a primitive of
`periodForm h0 (symActC M R)` on the upper half-plane, then `Fp ∘ mobM M` is a primitive of
`periodForm (h0 ∣ heilbronnGL M) R`: its derivative at `w` is the Möbius change of variables of
`Fp`'s, which by `periodForm_mobM_general` equals `periodForm (h0 ∣ heilbronnGL M) R w`.  The
determinant-`p` analogue of `hasDerivAt_primitive_mob_general`. -/
theorem hasDerivAt_primitive_mobM_general (h0 : ℍ → ℂ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0 < M.det) (R : SymPow ℂ (k - 2).toNat) (hk : 2 ≤ k) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im →
      HasDerivAt Fp (periodForm h0 (symActC M (k - 2).toNat R) z) z)
    {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun z => Fp (mobM M z))
      (periodForm (h0 ∣[k] (heilbronnGL M hM.ne')) R w) w := by
  have hmobpos : 0 < (mobM M w).im := by
    rw [mobM_eq_smul M hM ⟨w, hw⟩]
    exact ((glMap (heilbronnGL M hM.ne') • (⟨w, hw⟩ : ℍ) : ℍ)).im_pos
  have hF' : HasDerivAt Fp (periodForm h0 (symActC M (k - 2).toNat R) (mobM M w)) (mobM M w) :=
    hFp (mobM M w) hmobpos
  have hmob' : HasDerivAt (mobM M)
      ((M.det : ℂ) * (((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ^ (2 : ℤ))⁻¹) w := hasDerivAt_mobM M hM.ne' hw
  have hcomp := hF'.comp w hmob'
  have hcov := periodForm_mobM_general h0 M hM R hk hw
  rw [← hcov]
  exact hcomp

/-! ### The σ-conjugate-frame boundary engine for determinant `p`

To prove the determinant-`p` boundary naturality (`cuspBoundary_mobM_naturality`) we reuse the
abstract σ-frame top-value engine `tendsto_F_curve` of `PeriodInvariant.lean`, which takes an
*arbitrary* curve and an `SL(2, ℤ)` frame `σ`.  The det-`p` map `mobM M` enters only as the curve
`Y ↦ mobM M (q₀ + iY)`, whose `σ⁻¹`-image is the Möbius composition `mob σ⁻¹ (mobM M (q₀ + iY)) =
mobM ((σ⁻¹ : ℤ-mat) · M)(q₀ + iY)`, again of determinant `p`.  We therefore need the Möbius
composition law and the pole/upper geometry of `mobM` for a general nonzero-determinant matrix. -/

omit [NeZero N] in
/-- **Möbius composition.**  For `g ∈ SL(2, ℤ)` and an integer matrix `M` of positive determinant,
`mob g ∘ mobM M` is the Möbius map of the matrix product `(g : ℤ-mat) · M`:
`mob g (mobM M w) = mobM ((g : ℤ-mat) * M) w` (for `w` in the upper half-plane).  Möbius
maps compose
by matrix multiplication. -/
theorem mob_mobM_comp (g : SL(2, ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) {w : ℂ}
    (hw : 0 < w.im) :
    mob g (mobM M w) = mobM ((g : Matrix (Fin 2) (Fin 2) ℤ) * M) w := by
  have hD : ((M 1 0 : ℂ) * w + (M 1 1 : ℂ)) ≠ 0 := denom_mobM_ne M hM.ne' hw
  set D : ℂ := (M 1 0 : ℂ) * w + (M 1 1 : ℂ) with hDdef
  -- The inner Möbius image stays in the upper half-plane, so `mob g`'s denominator is nonzero.
  have hmw : 0 < (mobM M w).im := by
    rw [mobM_eq_smul M hM ⟨w, hw⟩]
    exact ((glMap (heilbronnGL M hM.ne') • (⟨w, hw⟩ : ℍ) : ℍ)).im_pos
  have hg : ((g 1 0 : ℂ) * (mobM M w) + (g 1 1 : ℂ)) ≠ 0 := denom_mob_ne g hmw
  -- The denominator of `mobM (gM) w`: `(g10 M00 + g11 M10) w + (g10 M01 + g11 M11) ≠ 0`.
  have hRHSden : ((g 1 0 : ℂ) * (M 0 0 : ℂ) + (g 1 1 : ℂ) * (M 1 0 : ℂ)) * w +
      ((g 1 0 : ℂ) * (M 0 1 : ℂ) + (g 1 1 : ℂ) * (M 1 1 : ℂ)) ≠ 0 := by
    have heq : ((g 1 0 : ℂ) * (M 0 0 : ℂ) + (g 1 1 : ℂ) * (M 1 0 : ℂ)) * w +
        ((g 1 0 : ℂ) * (M 0 1 : ℂ) + (g 1 1 : ℂ) * (M 1 1 : ℂ))
        = ((g 1 0 : ℂ) * (mobM M w) + (g 1 1 : ℂ)) * D := by
      rw [mobM, ← hDdef]; field_simp; ring
    rw [heq]; exact mul_ne_zero hg hD
  -- Entries of the product matrix.
  have he : ∀ i j : Fin 2, (((g : Matrix (Fin 2) (Fin 2) ℤ) * M) i j : ℂ) =
      (g i 0 : ℂ) * (M 0 j : ℂ) + (g i 1 : ℂ) * (M 1 j : ℂ) := by
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]; push_cast; ring
  show ((g 0 0 : ℂ) * (mobM M w) + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * (mobM M w) + (g 1 1 : ℂ)) =
    (((g : Matrix (Fin 2) (Fin 2) ℤ) * M) 0 0 * w + ((g : Matrix (Fin 2) (Fin 2) ℤ) * M) 0 1) /
      (((g : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 * w + ((g : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 1)
  rw [he, he, he, he, div_eq_div_iff hg hRHSden, mobM, ← hDdef]
  field_simp
  ring

omit [NeZero N] in
/-- **Closed form of the Möbius image of the vertical ray at a pole (determinant `p`).**  If the
integer matrix `M` has `M₁₀ ≠ 0` and `M₁₀·q + M₁₁ = 0` (so `M • q = ∞`), then for `Y > 0`,
`mobM M (q + iY) = M₀₀/M₁₀ + i·(det M)/(M₁₀²·Y)`.  The determinant-`p` analogue of `mob_pole_eq`. -/
theorem mobM_pole_eq (M : Matrix (Fin 2) (Fin 2) ℤ) {q Y : ℝ} (hc : (M 1 0 : ℝ) ≠ 0)
    (hpole : (M 1 0 : ℝ) * q + (M 1 1 : ℝ) = 0) (hY : 0 < Y) :
    mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)
      = (((M 0 0 : ℝ) / (M 1 0 : ℝ) : ℝ) : ℂ)
        + (((M.det : ℝ) / ((M 1 0 : ℝ) ^ 2 * Y) : ℝ) : ℂ) * Complex.I := by
  have hcC : (M 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpoleC : (M 1 0 : ℂ) * (q : ℂ) + (M 1 1 : ℂ) = 0 := by exact_mod_cast hpole
  have hdet : (M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ) = (M.det : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  simp only [mobM]
  have hden : (M 1 0 : ℂ) * ((q : ℂ) + (Y : ℂ) * Complex.I) + (M 1 1 : ℂ)
      = (M 1 0 : ℂ) * (Y : ℂ) * Complex.I := by linear_combination hpoleC
  rw [hden]
  have hdenne : (M 1 0 : ℂ) * (Y : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcC hYC) Complex.I_ne_zero
  rw [div_eq_iff hdenne]
  have hII : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [Matrix.det_fin_two]
  push_cast
  field_simp
  linear_combination (M 0 0 : ℂ) * hpoleC
    - ((M 0 0 : ℂ) * (M 1 1 : ℂ) - (M 0 1 : ℂ) * (M 1 0 : ℂ)) * hII

omit [NeZero N] in
/-- The real part of the Möbius image of the vertical ray at a pole is the constant `M₀₀/M₁₀`. -/
theorem re_mobM_pole (M : Matrix (Fin 2) (Fin 2) ℤ) {q Y : ℝ} (hc : (M 1 0 : ℝ) ≠ 0)
    (hpole : (M 1 0 : ℝ) * q + (M 1 1 : ℝ) = 0) (hY : 0 < Y) :
    (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).re = (M 0 0 : ℝ) / (M 1 0 : ℝ) := by
  rw [mobM_pole_eq M hc hpole hY, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

omit [NeZero N] in
/-- The imaginary part of the Möbius image of the vertical ray at a pole tends to `+∞` as `Y → 0⁺`
(for `det M > 0`): the perpendicular approach to the finite cusp `q` is sent to a curve
running off to
`i∞`.  The determinant-`p` analogue of `tendsto_im_mob_pole`. -/
theorem tendsto_im_mobM_pole (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) {q : ℝ}
    (hc : (M 1 0 : ℝ) ≠ 0) (hpole : (M 1 0 : ℝ) * q + (M 1 1 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).im) (𝓝[>] 0) atTop := by
  have hY0 : ∀ Y : ℝ, 0 < Y → (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).im
      = ((M.det : ℝ) / (M 1 0 : ℝ) ^ 2) * Y⁻¹ := by
    intro Y hY
    rw [mobM_pole_eq M hc hpole hY, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [mul_one, zero_mul, add_zero, zero_add, div_mul_eq_div_div, div_eq_mul_inv]
  have heq : (fun Y : ℝ => (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).im) =ᶠ[𝓝[>] 0]
      (fun Y : ℝ => ((M.det : ℝ) / (M 1 0 : ℝ) ^ 2) * Y⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with Y hY
    exact hY0 Y (Set.mem_Ioi.mp hY)
  rw [tendsto_congr' heq]
  refine Tendsto.const_mul_atTop ?_ tendsto_inv_nhdsGT_zero
  have hdetR : (0 : ℝ) < (M.det : ℝ) := by exact_mod_cast hM
  positivity

omit [NeZero N] in
/-- For an upper-triangular integer matrix `M` (`M₁₀ = 0`), `M₀₀ · M₁₁ = det M`. -/
theorem M00_mul_M11_of_upper (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hc : (M 1 0 : ℝ) = 0) : (M 0 0 : ℝ) * (M 1 1 : ℝ) = (M.det : ℝ) := by
  have hc0 : (M 1 0 : ℤ) = 0 := by exact_mod_cast hc
  rw [Matrix.det_fin_two, hc0]; push_cast; ring

omit [NeZero N] in
/-- **Closed form of the Möbius image of the vertical ray for an upper-triangular `M`
(determinant `p`).**  If `M₁₀ = 0` (so `M • ∞ = ∞`), then
`mobM M (q + iY) = (M₀₀ q + M₀₁)/M₁₁ + i·(M₀₀/M₁₁)·Y`.  The determinant-`p` analogue of
`mob_upper_eq`. -/
theorem mobM_upper_eq (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) {q Y : ℝ}
    (hc : (M 1 0 : ℝ) = 0) :
    mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)
      = ((((M 0 0 : ℝ) * q + (M 0 1 : ℝ)) / (M 1 1 : ℝ) : ℝ) : ℂ)
        + (((M 0 0 : ℝ) / (M 1 1 : ℝ) * Y : ℝ) : ℂ) * Complex.I := by
  have hdetR : (0 : ℝ) < (M.det : ℝ) := by exact_mod_cast hM
  have hc11 := M00_mul_M11_of_upper M hc
  have hg11 : (M 1 1 : ℝ) ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hc11; linarith
  have hcC : (M 1 0 : ℂ) = 0 := by exact_mod_cast hc
  have hg11C : (M 1 1 : ℂ) ≠ 0 := by exact_mod_cast hg11
  simp only [mobM]
  rw [hcC, zero_mul, zero_add, div_eq_iff hg11C]
  push_cast
  field_simp
  ring

omit [NeZero N] in
/-- The real part of the upper-triangular Möbius image of the vertical ray is the constant
`(M₀₀ q + M₀₁)/M₁₁`. -/
theorem re_mobM_upper (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) {q Y : ℝ}
    (hc : (M 1 0 : ℝ) = 0) :
    (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).re =
      ((M 0 0 : ℝ) * q + (M 0 1 : ℝ)) / (M 1 1 : ℝ) := by
  rw [mobM_upper_eq M hM hc, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

omit [NeZero N] in
/-- The imaginary part of the upper-triangular Möbius image of the vertical ray tends to `+∞` as
`Y → +∞` (the vertical ray is sent to a curve `→ i∞`).  Needs `det M > 0` (so `M₀₀/M₁₁ > 0`). -/
theorem tendsto_im_mobM_upper (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) {q : ℝ}
    (hc : (M 1 0 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).im) atTop atTop := by
  have hdetR : (0 : ℝ) < (M.det : ℝ) := by exact_mod_cast hM
  have hc11 := M00_mul_M11_of_upper M hc
  have hg11 : (M 1 1 : ℝ) ≠ 0 := by rintro h0; rw [h0, mul_zero] at hc11; linarith
  have heq : (fun Y : ℝ => (mobM M ((q : ℂ) + (Y : ℂ) * Complex.I)).im)
      = (fun Y : ℝ => (M 0 0 : ℝ) / (M 1 1 : ℝ) * Y) := by
    ext Y
    rw [mobM_upper_eq M hM hc, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [heq]
  refine Tendsto.const_mul_atTop ?_ tendsto_id
  -- `M₀₀/M₁₁ > 0`: `M₀₀·M₁₁ = det > 0`, so they have the same sign.
  rw [div_pos_iff]
  rcases lt_or_gt_of_ne hg11 with h | h
  · right; constructor
    · nlinarith [hc11, hdetR]
    · exact h
  · left; constructor
    · nlinarith [hc11, hdetR]
    · exact h

/-- **Boundary value of `F` along a Möbius-pole geodesic (determinant `p`).**  The det-`p` analogue
of `tendsto_F_pole`: for `F` a primitive of `periodForm f (symActC M R)` (`M` of positive
determinant) with σ-frame top value `L`, if `σ⁻¹ · M` sends `q₀` to `∞` (its lower row annihilates
`q₀`), the curve `Y ↦ mobM M (q₀ + iY)`'s `σ⁻¹`-image is the pole geodesic
`mobM (σ⁻¹ · M)(q₀ + iY)`, which runs off to `i∞` (`tendsto_im_mobM_pole`, `re_mobM_pole`), so
`F(mobM M (q₀ + iY)) → L`. -/
theorem tendsto_FM_pole (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (R : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) (symActC M (k - 2).toNat R) z) z)
    (σ : SL(2, ℤ)) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop (𝓝 L))
    (q₀ : ℝ)
    (hc : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 ≠ 0)
    (hpole : ((((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 : ℝ) * q₀ +
      ((((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 1 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => F (mobM M ((q₀ : ℂ) + Y * Complex.I))) (𝓝[>] 0) (𝓝 L) := by
  set M' := ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M with hM'
  have hM'det : 0 < M'.det := by
    rw [hM', Matrix.det_mul]
    have : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := (σ⁻¹).prop
    rw [this, one_mul]; exact hM
  have hcR : (M' 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmobpos : ∀ Y : ℝ, 0 < Y → 0 < (mobM M ((q₀ : ℂ) + Y * Complex.I)).im := by
    intro Y hY
    rw [mobM_eq_smul M hM ⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩]
    exact (glMap (heilbronnGL M hM.ne') • (⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩ : ℍ)).im_pos
  -- The `σ⁻¹`-image of the curve is the pole geodesic `mobM (σ⁻¹ M)(q₀ + iY)`.
  have hcomp : ∀ Y : ℝ, 0 < Y →
      mob σ⁻¹ (mobM M ((q₀:ℂ) + Y * Complex.I)) = mobM M' ((q₀:ℂ) + Y * Complex.I) := by
    intro Y hY
    rw [mob_mobM_comp σ⁻¹ M hM (by simp [hY]), hM']
  refine tendsto_F_curve f hk (symActC M (k - 2).toNat R) F hF σ L hL
    (|(M' 0 0 : ℝ) / (M' 1 0 : ℝ)|) (abs_nonneg _)
    (fun Y : ℝ => mobM M ((q₀:ℂ) + (Y:ℂ) * Complex.I)) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with Y hY; exact hmobpos Y (Set.mem_Ioi.mp hY)
  · filter_upwards [self_mem_nhdsWithin] with Y hY
    rw [hcomp Y (Set.mem_Ioi.mp hY), re_mobM_pole M' hcR hpole (Set.mem_Ioi.mp hY)]
  · have heq : (fun Y : ℝ => (mob σ⁻¹ (mobM M ((q₀:ℂ) + Y * Complex.I))).im) =ᶠ[𝓝[>] 0]
        (fun Y : ℝ => (mobM M' ((q₀:ℂ) + Y * Complex.I)).im) := by
      filter_upwards [self_mem_nhdsWithin] with Y hY
      rw [hcomp Y (Set.mem_Ioi.mp hY)]
    rw [tendsto_congr' heq]
    exact tendsto_im_mobM_pole M' hM'det hcR hpole

/-- **Boundary value of `F` along an upper-triangular geodesic to `i∞` (determinant `p`).**  The
det-`p` analogue of `tendsto_F_upper`: for `F` a primitive of `periodForm f (symActC M R)` with
identity-frame top value `Finf`, if `M` is upper-triangular (`M₁₀ = 0`, so `M • ∞ = ∞`),
the vertical
ray's image `mobM M (q₀ + iY)` runs off to `i∞` as `Y → ∞`, so `F(mobM M (q₀ + iY)) → Finf`. -/
theorem tendsto_FM_upper (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (R : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) (symActC M (k - 2).toNat R) z) z)
    (Finf : ℂ)
    (hFinf : ∀ q : ℝ, Tendsto (fun Y : ℝ => F ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Finf))
    (q₀ : ℝ) (hc : (M 1 0 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => F (mobM M ((q₀ : ℂ) + (Y:ℂ) * Complex.I))) atTop (𝓝 Finf) := by
  -- Use the identity σ-frame (`σ = 1`, `mob 1 = id`).
  have hmob1 : ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z := fun z => by simp [mob]
  refine tendsto_F_curve f hk (symActC M (k - 2).toNat R) F hF 1 Finf
    (by intro q; simpa only [hmob1] using hFinf q)
    (|((M 0 0 : ℝ) * q₀ + (M 0 1 : ℝ)) / (M 1 1 : ℝ)|) (abs_nonneg _)
    (fun Y : ℝ => mobM M ((q₀:ℂ) + (Y:ℂ) * Complex.I)) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with Y hY
    rw [mobM_eq_smul M hM ⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩]
    exact (glMap (heilbronnGL M hM.ne') • (⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩ : ℍ)).im_pos
  · filter_upwards with Y
    rw [inv_one, hmob1, re_mobM_upper M hM hc]
  · simp only [inv_one, hmob1]
    exact tendsto_im_mobM_upper M hM hc

/-- **Boundary value of `F` along a Möbius geodesic running to a finite cusp `M • ∞` (determinant
`p`).**  The det-`p` σ-frame companion to `tendsto_FM_upper`, handling a *general* matrix `M` (not
necessarily upper-triangular).  For `F` a primitive of `periodForm f (symActC M R)` with σ-frame top
value `L`, if `σ⁻¹ · M` is upper-triangular (`(σ⁻¹·M)₁₀ = 0`, equivalently
`σ⁻¹ · (M • ∞) = ∞`), then
the curve `Y ↦ mobM M (q₀ + iY)`'s `σ⁻¹`-image is the upper geodesic `mobM (σ⁻¹·M)(q₀ + iY)`, which
runs off to `i∞` as `Y → ∞` (`tendsto_im_mobM_upper`, `re_mobM_upper`), so
`F(mobM M (q₀ + iY)) → L`.  Used for the `o = ∞` finite-image cases of the boundary
naturality, where
`Ginf` is the top value of `F ∘ mobM M` along a curve approaching the finite cusp `M • ∞`. -/
theorem tendsto_FM_upper_gen (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (R : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) (symActC M (k - 2).toNat R) z) z)
    (σ : SL(2, ℤ)) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop (𝓝 L))
    (q₀ : ℝ)
    (hc : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 = 0) :
    Tendsto (fun Y : ℝ => F (mobM M ((q₀ : ℂ) + Y * Complex.I))) atTop (𝓝 L) := by
  set M' := ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M with hM'
  have hM'det : 0 < M'.det := by
    rw [hM', Matrix.det_mul,
      show ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from (σ⁻¹).prop, one_mul]
    exact hM
  have hcR : (M' 1 0 : ℝ) = 0 := by exact_mod_cast hc
  have hmobpos : ∀ Y : ℝ, 0 < Y → 0 < (mobM M ((q₀ : ℂ) + Y * Complex.I)).im := by
    intro Y hY
    rw [mobM_eq_smul M hM ⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩]
    exact (glMap (heilbronnGL M hM.ne') • (⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩ : ℍ)).im_pos
  have hcomp : ∀ Y : ℝ, 0 < Y →
      mob σ⁻¹ (mobM M ((q₀:ℂ) + Y * Complex.I)) = mobM M' ((q₀:ℂ) + Y * Complex.I) := by
    intro Y hY
    rw [mob_mobM_comp σ⁻¹ M hM (by simp [hY]), hM']
  refine tendsto_F_curve f hk (symActC M (k - 2).toNat R) F hF σ L hL
    (|((M' 0 0 : ℝ) * q₀ + (M' 0 1 : ℝ)) / (M' 1 1 : ℝ)|) (abs_nonneg _)
    (fun Y : ℝ => mobM M ((q₀:ℂ) + (Y:ℂ) * Complex.I)) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with Y hY; exact hmobpos Y hY
  · filter_upwards [eventually_gt_atTop 0] with Y hY
    rw [hcomp Y hY, re_mobM_upper M' hM'det hcR]
  · have heq : (fun Y : ℝ => (mob σ⁻¹ (mobM M ((q₀:ℂ) + Y * Complex.I))).im) =ᶠ[atTop]
        (fun Y : ℝ => (mobM M' ((q₀:ℂ) + Y * Complex.I)).im) := by
      filter_upwards [eventually_gt_atTop 0] with Y hY
      rw [hcomp Y hY]
    rw [tendsto_congr' heq]
    exact tendsto_im_mobM_upper M' hM'det hcR

/-! ## The generic (arbitrary arithmetic cusp form) cusp-value pairing

The cusp-value/`rawPairing` machinery of `PeriodMap.lean`/`PeriodInvariant.lean` is typed for
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k`.  To run the determinant-`p` boundary naturality for the
*conjugate* cusp forms `f ∣ heilbronnGL M` — which are cusp forms for a conjugate arithmetic group,
not `Γ₁(N)` — we need the same constructions for an *arbitrary* arithmetic cusp form.  The
underlying period integral `genPeriodIntegral` is already polymorphic, so the generic versions are a
thin re-packaging; we only repeat the convergence-dependent cusp-value formula. -/

variable {F : Type*} [FunLike F ℍ ℂ]

open scoped MatrixGroups in
/-- The cusp-to-`i∞` integral for an arbitrary arithmetic cusp form `f0` (generic
`cuspToInftyIntegral`). -/
noncomputable def cuspToInftyIntegralGen {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k]
    [Γ.IsArithmetic] (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) : ℂ :=
  haveI : (ConjAct.toConjAct (transMat q)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_transMat q
  genPeriodIntegral (CuspForm.translate f0 (transMat q)) (shiftPoly q P)

open scoped LinearAlgebra.Projectivization in
/-- The cusp value of an arbitrary arithmetic cusp form `f0` at a projective cusp `c` (generic
`cuspValue`). -/
noncomputable def cuspValueGen {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] [Γ.IsArithmetic]
    (f0 : F) {m : ℕ} (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) : ℂ :=
  match (OnePoint.equivProjectivization ℚ).symm c with
  | (q : ℚ) => cuspToInftyIntegralGen f0 P q
  | .infty => 0

/-- The generic bottom (finite-cusp) boundary value of a primitive `Fp` of `periodForm f0 P`. -/
noncomputable def botValGen (f0 : F) {m : ℕ} (P : SymPow ℂ m) (Fp : ℂ → ℂ) (r : ℚ) : ℂ :=
  Fp ((r : ℂ) + Complex.I) -
    ∫ t in (0 : ℝ)..1, periodForm (⇑f0) P ((r : ℂ) + t * Complex.I) * Complex.I

omit [NeZero N] in
/-- `shiftPoly` is additive in the polynomial slot. -/
theorem shiftPoly_add (q : ℚ) {m : ℕ} (P Q : SymPow ℂ m) :
    shiftPoly q (P + Q) = shiftPoly q P + shiftPoly q Q := by
  apply Subtype.ext
  show substAlgHom (shiftMat q) ((P + Q : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ) = _
  rw [show ((P + Q : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ) = (P : MvPolynomial (Fin 2) ℂ) +
    (Q : MvPolynomial (Fin 2) ℂ) from rfl, map_add]; rfl

omit [NeZero N] in
/-- `shiftPoly` is `ℂ`-homogeneous in the polynomial slot. -/
theorem shiftPoly_smul (c : ℂ) (q : ℚ) {m : ℕ} (P : SymPow ℂ m) :
    shiftPoly q (c • P) = c • shiftPoly q P := by
  apply Subtype.ext
  show substAlgHom (shiftMat q) ((c • P : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ) = _
  rw [show ((c • P : SymPow ℂ m) : MvPolynomial (Fin 2) ℂ) =
    c • (P : MvPolynomial (Fin 2) ℂ) from rfl, map_smul]; rfl

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [hcf : CuspFormClass F Γ k] [har : Γ.IsArithmetic]

/-- Local arithmeticity instance for the `transMat q`-conjugate, so the polymorphic period-integral
machinery applies to `CuspForm.translate f0 (transMat q)` without naming the ambient `Γ`. -/
instance instArithmetic_conj_transMat (q : ℚ) :
    (ConjAct.toConjAct (transMat q)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_transMat q

include hcf har

/-- `cuspValueGen` is additive in the polynomial slot. -/
theorem cuspValueGen_add_right (f0 : F) {m : ℕ} (P Q : SymPow ℂ m)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen f0 (P + Q) c = cuspValueGen f0 P c + cuspValueGen f0 Q c := by
  rw [cuspValueGen, cuspValueGen, cuspValueGen]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q =>
    haveI : (ConjAct.toConjAct (transMat q)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_transMat q
    simp only [cuspToInftyIntegralGen, shiftPoly_add]
    exact genPeriodIntegral_add_right _ _ _

/-- `cuspValueGen` is `ℂ`-homogeneous in the polynomial slot. -/
theorem cuspValueGen_smul_right (a : ℂ) (f0 : F) {m : ℕ} (P : SymPow ℂ m)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen f0 (a • P) c = a • cuspValueGen f0 P c := by
  rw [cuspValueGen, cuspValueGen]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q =>
    haveI : (ConjAct.toConjAct (transMat q)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_transMat q
    simp only [cuspToInftyIntegralGen, shiftPoly_smul]
    exact genPeriodIntegral_smul_right _ _ _

/-- The generic `ℤ`-linear functional `P ↦ cuspValueGen f0 (P : Sym ℂ) c` at a fixed cusp `c`. -/
noncomputable def cuspFunctionalGen (f0 : F) {m : ℕ} (c : Projectivization ℚ (Fin 2 → ℚ)) :
    SymPow ℤ m →ₗ[ℤ] ℂ where
  toFun P := cuspValueGen f0 (castSymPow m P) c
  map_add' P Q := by rw [map_add, cuspValueGen_add_right]
  map_smul' a P := by
    rw [map_smul, RingHom.id_apply,
      ← Int.cast_smul_eq_zsmul ℂ a (castSymPow m P), cuspValueGen_smul_right,
      Int.cast_smul_eq_zsmul ℂ a (cuspValueGen f0 (castSymPow m P) c)]

/-- The generic `ℤ`-bilinear period pairing in the divisor slot. -/
noncomputable def rawBilinGen (f0 : F) {m : ℕ} :
    (Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) →ₗ[ℤ] SymPow ℤ m →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ (fun c => cuspFunctionalGen f0 c)

/-- The generic raw period pairing on `Div⁰ ⊗ Sym^m` for an arbitrary arithmetic cusp form. -/
noncomputable def rawPairingGen (f0 : F) {m : ℕ} : (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] ℂ :=
  TensorProduct.lift ((rawBilinGen f0).comp
    ((MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap ∘ₗ (Div0 ℤ).subtype))

/-- The generic `rawPairingGen` against a single tensor is the `rawBilinGen` of the divisor and
polynomial. -/
theorem rawPairingGen_tmul (f0 : F) {m : ℕ} (D : Div0 ℤ) (P : SymPow ℤ m) :
    rawPairingGen f0 (D ⊗ₜ P) =
      rawBilinGen f0 (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff P :=
  rfl

/-! ### The generic cusp-value formula `cuspValueGen = top − bottom`

We mirror the typed `cuspValue_eq_top_sub_botVal`.  The integrability and FTC engine of
`PeriodInvariant.lean` is already polymorphic in the cusp-form type (`genIntegrableOn`,
`hasDerivAt_periodForm_primitive_vertical`), so the chain transfers verbatim with the generic
`cuspToInftyIntegralGen`. -/

/-- Generic `cuspToInftyIntegral_integrand`: the period integrand of the translate is `f0` evaluated
at the shifted point. -/
theorem cuspToInftyIntegralGen_integrand (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) {t : ℝ}
    (ht : 0 < t) :
    genIntegrand (⇑(CuspForm.translate f0 (transMat q))) (shiftPoly q P) t =
      f0 (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) *
        evalSym1 m P (Complex.I * t + (q : ℂ)) * Complex.I := by
  rw [genIntegrand_apply_of_pos _ _ ht, coe_cuspForm_translate_transMat,
    slash_transMat_apply (⇑f0) q ⟨Complex.I * t, by simp [ht]⟩, evalSym1_shiftPoly]

/-- Generic `genIntegrand_transMat_eq_periodForm`. -/
theorem genIntegrand_transMat_eq_periodFormGen (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) {t : ℝ}
    (ht : 0 < t) :
    genIntegrand (⇑(CuspForm.translate f0 (transMat q))) (shiftPoly q P) t =
      periodForm (⇑f0) P ((q : ℂ) + t * Complex.I) * Complex.I := by
  rw [cuspToInftyIntegralGen_integrand f0 P q ht,
    show (Complex.I * (t : ℂ) + (q : ℂ)) = (q : ℂ) + (t : ℂ) * Complex.I by ring]
  rfl

/-- Generic integrability of the vertical period integrand. -/
theorem integrableOn_periodFormGen_vertical (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) :
    IntegrableOn (fun t : ℝ => periodForm (⇑f0) P ((q : ℂ) + t * Complex.I) * Complex.I)
      (Set.Ioi 0) := by
  refine (genIntegrableOn (CuspForm.translate f0 (transMat q)) (shiftPoly q P)).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at ht
  exact genIntegrand_transMat_eq_periodFormGen f0 P q ht

/-- Generic `cuspToInftyIntegralGen` as the improper vertical integral of the period form. -/
theorem cuspToInftyIntegralGen_eq_periodForm (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegralGen f0 P q =
      ∫ t in Set.Ioi (0 : ℝ), periodForm (⇑f0) P ((q : ℂ) + t * Complex.I) * Complex.I := by
  rw [cuspToInftyIntegralGen, genPeriodIntegral]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  exact genIntegrand_transMat_eq_periodFormGen f0 P q ht

/-- Generic `tendsto_primitive_vertical_nhdsGT_zero`: the `Y → 0⁺` boundary value of a primitive is
`botValGen`. -/
theorem tendsto_primitive_vertical_nhdsGT_zeroGen (f0 : F) {m : ℕ} (P : SymPow ℂ m) (q : ℚ)
    (Fp : ℂ → ℂ) (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f0) P z) z) :
    Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0) (𝓝 (botValGen f0 P Fp q)) := by
  set g : ℝ → ℂ := fun t => periodForm (⇑f0) P ((q : ℂ) + t * Complex.I) * Complex.I with hg
  have hint : IntegrableOn g (Set.Ioi 0) := integrableOn_periodFormGen_vertical f0 P q
  have hFTC : ∀ Y : ℝ, 0 < Y →
      (∫ t in Y..1, g t) = Fp ((q : ℂ) + Complex.I) - Fp ((q : ℂ) + Y * Complex.I) := by
    intro Y hY
    have hsub : Set.uIcc Y 1 ⊆ {t : ℝ | 0 < t} := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rw [Set.mem_setOf_eq]
      rcases ht with h | h
      · linarith [h.1]
      · linarith [h.1]
    have hderiv : ∀ t ∈ Set.uIcc Y 1,
        HasDerivAt (fun s : ℝ => Fp ((q : ℂ) + s * Complex.I)) (g t) t := fun t ht =>
      hasDerivAt_periodForm_primitive_vertical f0 P Fp hFp q (hsub ht)
    have hii : IntervalIntegrable g MeasureTheory.volume Y 1 :=
      (hint.mono_set (fun t ht => hsub ht)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    push_cast; ring_nf
  have hii01 : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  have hcont : ContinuousWithinAt (fun b : ℝ => ∫ t in (1 : ℝ)..b, g t) (Set.Icc 0 1) 0 :=
    intervalIntegral.continuousWithinAt_primitive (by simp) (by simpa using hii01)
  have hcont' : Tendsto (fun Y : ℝ => ∫ t in (1 : ℝ)..Y, g t) (𝓝[>] 0)
      (𝓝 (∫ t in (1 : ℝ)..(0 : ℝ), g t)) := by
    refine hcont.tendsto.mono_left (nhdsWithin_le_iff.mpr ?_)
    have h0 : Set.Ici (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      Filter.mem_of_superset self_mem_nhdsWithin Set.Ioi_subset_Ici_self
    have h1 : Set.Iic (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
    rw [show Set.Icc (0 : ℝ) 1 = Set.Ici 0 ∩ Set.Iic 1 from rfl]
    exact Filter.inter_mem h0 h1
  have hkey : Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..(0 : ℝ), g t)) := by
    have h1 : (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) =ᶠ[𝓝[>] 0]
        (fun Y : ℝ => Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..Y, g t) := by
      filter_upwards [self_mem_nhdsWithin] with Y hY
      rw [Set.mem_Ioi] at hY
      have hh := hFTC Y hY
      rw [intervalIntegral.integral_symm Y 1]
      linear_combination hh
    rw [tendsto_congr' h1]
    exact tendsto_const_nhds.add hcont'
  have hval : Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..(0 : ℝ), g t = botValGen f0 P Fp q := by
    rw [botValGen, intervalIntegral.integral_symm 1 0]; ring
  rwa [hval] at hkey

/-- **Generic cusp value as top-minus-bottom boundary values.**  Determinant-`p`-ready analogue of
`cuspValue_eq_top_sub_botVal` for an arbitrary arithmetic cusp form. -/
theorem cuspValueGen_eq_top_sub_botValGen (f0 : F) {m : ℕ} (P : SymPow ℂ m) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f0) P z) z) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L))
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen f0 P c =
      L - (match (OnePoint.equivProjectivization ℚ).symm c with
            | (r : ℚ) => botValGen f0 P Fp r
            | .infty => L) := by
  rw [cuspValueGen]
  cases ho : (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe r =>
    simp only []
    rw [cuspToInftyIntegralGen_eq_periodForm]
    -- The improper integral equals `L − botValGen` by the FTC bridge.
    set g : ℝ → ℂ := fun t => periodForm (⇑f0) P ((r : ℂ) + t * Complex.I) * Complex.I with hg
    have hint : IntegrableOn g (Set.Ioi 0) := integrableOn_periodFormGen_vertical f0 P r
    have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop
        (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    have hBbot := tendsto_primitive_vertical_nhdsGT_zeroGen f0 P r Fp hFp
    have hFTC : ∀ Y₁ : ℝ, 0 < Y₁ →
        (∫ t in (0 : ℝ)..Y₁, g t) = Fp ((r : ℂ) + Y₁ * Complex.I) - botValGen f0 P Fp r := by
      intro Y₁ hY₁
      have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) Y₁,
          HasDerivAt (fun s : ℝ => Fp ((r : ℂ) + s * Complex.I)) (g t) t := fun t ht =>
        hasDerivAt_periodForm_primitive_vertical f0 P Fp hFp r ht.1
      have hii : IntervalIntegrable g MeasureTheory.volume 0 Y₁ := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY₁.le]
        exact hint.mono_set Set.Ioc_subset_Ioi_self
      have htop : Tendsto (fun Y : ℝ => Fp ((r : ℂ) + Y * Complex.I)) (𝓝[<] Y₁)
          (𝓝 (Fp ((r : ℂ) + Y₁ * Complex.I))) :=
        ((hasDerivAt_periodForm_primitive_vertical f0 P Fp hFp r
          hY₁).continuousAt).tendsto.mono_left
          nhdsWithin_le_nhds
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hY₁ hderiv hii hBbot htop]
    have hTrunc2 : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop
        (𝓝 (L - botValGen f0 P Fp r)) := by
      have heq : (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) =ᶠ[atTop]
          (fun Y₁ : ℝ => Fp ((r : ℂ) + Y₁ * Complex.I) - botValGen f0 P Fp r) := by
        filter_upwards [eventually_gt_atTop 0] with Y₁ hY₁
        exact hFTC Y₁ hY₁
      rw [tendsto_congr' heq]
      exact (hL r).sub_const _
    exact tendsto_nhds_unique hTrunc hTrunc2

omit hcf har

/-- For a genuine `Γ₁(N)` cusp form the generic cusp value coincides with the typed `cuspValue`. -/
theorem cuspValueGen_eq_cuspValue (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen f P c = cuspValue f P c :=
  rfl

/-- For a genuine `Γ₁(N)` cusp form the generic raw pairing coincides with the typed
`rawPairing`. -/
theorem rawPairingGen_eq_rawPairing (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    rawPairingGen f x = rawPairing f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul D P =>
    rw [rawPairingGen_tmul, rawPairing_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The determinant-`p` per-coset change of variables

We now establish, for each Heilbronn coset matrix `M` (determinant `p`), the determinant-`p`
analogue of the det-`1` change of variables `rawPairing_fullModSymRep_sl`:
`rawPairingGen (f ∣ heilbronnGL M) x = rawPairing f (actMat M x)`.  The `c`-independent tail of the
cusp-value covariance cancels because the divisor has degree `0`.  The deep analytic input — the
cusp-value covariance itself — is the determinant-`p` boundary naturality
(`cuspValueGen_symActC_heilbronn`). -/

/-- The `glMap g`-conjugate of an arithmetic group is arithmetic (`g : GL(2, ℚ)`).  Supplies the
arithmeticity instance for the conjugate cusp form `f ∣ glMap g`. -/
instance isArithmetic_conj_glMap (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] (g : GL (Fin 2) ℚ) :
    (ConjAct.toConjAct (glMap g)⁻¹ • Γ).IsArithmetic := by
  have h : (glMap g)⁻¹ = (g⁻¹).map (Rat.castHom ℝ) := by
    rw [glMap, ← map_inv]; rfl
  rw [h]
  exact Subgroup.IsArithmetic.conj Γ g⁻¹

omit [NeZero N] in
/-- The matrix entries of `heilbronnGL M` are the integer entries of `M`, cast to `ℚ`:
`(heilbronnGL M) i j = M i j`.  The det-`p` analogue of the `SL(2, ℤ)` entry identity used by the
det-`1` cusp geometry. -/
theorem heilbronnGL_entry (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (i j : Fin 2) :
    (heilbronnGL M hM) i j = ((M i j : ℤ) : ℚ) := by
  simp [heilbronnGL_coe, qMat]

omit [NeZero N] in
/-- On `SL(2, ℤ)`, the Heilbronn `GL(2, ℚ)` element of the integer matrix coincides with `mapGL ℚ`:
`heilbronnGL (g : ℤ-mat) = mapGL ℚ g`.  Bridges the det-`p` Heilbronn frame to the det-`1`
`SL(2, ℤ)` frame used by the σ-conjugate boundary engine. -/
theorem heilbronnGL_sl (g : SL(2, ℤ)) :
    heilbronnGL (g : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero g)
      = Matrix.SpecialLinearGroup.mapGL ℚ g := by
  apply Units.ext
  show qMat (g : Matrix (Fin 2) (Fin 2) ℤ) =
    (Matrix.SpecialLinearGroup.mapGL ℚ g : Matrix (Fin 2) (Fin 2) ℚ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j; simp [qMat, Matrix.SpecialLinearGroup.map_apply_coe]

omit [NeZero N] in
/-- **Pole data from a det-`p` cusp mapping to `∞`.**  If the Heilbronn element
`heilbronnGL M` of an
integer matrix `M` (det `≠ 0`) sends the rational cusp `c` to `∞`, then its lower row `(M₁₀, M₁₁)`
annihilates `c` and `M₁₀ ≠ 0` (over `ℝ`).  The det-`p` analogue of `pole_of_smul_infty`:
`M₁₀ = 0` would force `M₁₁ = 0` (from the pole), hence `det M = 0`, a contradiction. -/
theorem pole_of_smul_infty_M (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (c : ℚ)
    (hsmul : (heilbronnGL M hM) • (c : OnePoint ℚ) = ∞) :
    (M 1 0 : ℝ) ≠ 0 ∧ (M 1 0 : ℝ) * (c : ℝ) + (M 1 1 : ℝ) = 0 := by
  rw [OnePoint.smul_some_eq_ite] at hsmul
  have hpoleQ : (heilbronnGL M hM) 1 0 * c + (heilbronnGL M hM) 1 1 = 0 := by
    by_contra hne; rw [if_neg hne] at hsmul; exact absurd hsmul (by simp)
  rw [heilbronnGL_entry M hM 1 0, heilbronnGL_entry M hM 1 1] at hpoleQ
  have hpoleR : (M 1 0 : ℝ) * (c : ℝ) + (M 1 1 : ℝ) = 0 := by exact_mod_cast hpoleQ
  refine ⟨?_, hpoleR⟩
  intro hz
  rw [hz, zero_mul, zero_add] at hpoleR
  have hdet : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = (M.det : ℝ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  rw [hpoleR] at hdet
  have hz' : (M 1 0 : ℝ) = 0 := by exact_mod_cast hz
  rw [hz'] at hdet; simp only [Fin.isValue, mul_zero, sub_self] at hdet
  exact hM (by exact_mod_cast hdet.symm)

/-- **Determinant-`p` boundary naturality (the isolated geodesic-period crux, `μ ≡ 0`).**  The
det-`p` analogue of `cuspBoundary_mob_naturality_sl`.  For an integer matrix `M` of positive
determinant, a typed `Γ₁(N)` cusp form `f₁`, a generic arithmetic cusp form `f₂` with
`⇑f₂ = ⇑f₁ ∣[k] heilbronnGL M`, a primitive `F` of `periodForm f₁ (symActC M (cast P))`
with vertical
top value `Finf`, and `Ginf` the top value of its det-`p` Möbius pullback `G = F ∘ mobM M` (a
primitive of `periodForm f₂ (cast P)`), the cusp boundary value of `G` (for `f₂`) at any cusp `o`
equals the cusp boundary value of `F` (for `f₁`) at the Möbius-moved cusp `heilbronnGL M • o`.

The four cases mirror `cuspBoundary_mob_naturality_sl`, with `mob g` replaced by the det-`p` Möbius
`mobM M`, the σ-conjugate-frame boundary limits `tendsto_F_pole`/`tendsto_F_upper` replaced by their
det-`p` analogues `tendsto_FM_pole`/`tendsto_FM_upper`, and the pole geometry `pole_of_smul_infty`
replaced by `pole_of_smul_infty_M`.  The σ-frame matrix products are the integer products
`(σ⁻¹ : ℤ-mat) · M`, whose Heilbronn elements factor through `heilbronnGL_mul`/`heilbronnGL_sl`. -/
theorem cuspBoundary_mobM_naturality {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [CuspFormClass F Γ k] [Γ.IsArithmetic]
    (f₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (f₂ : F) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0 < M.det) (hf₂ : ⇑f₂ = ⇑f₁ ∣[k] (heilbronnGL M hM.ne'))
    (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k) (Fp : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt Fp (periodForm (⇑f₁) (symActC M (k - 2).toNat (castSymPow (k - 2).toNat P)) z) z)
    (Finf Ginf : ℂ)
    (hFinf : ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Finf))
    (hGinf : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => Fp (mobM M ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf))
    (o : OnePoint ℚ) :
    (match o with
      | (s : ℚ) => botValGen f₂ (castSymPow (k - 2).toNat P) (fun z => Fp (mobM M z)) s
      | .infty => Ginf) =
    (match (heilbronnGL M hM.ne') • o with
      | (r : ℚ) =>
        botVal f₁ (symActC M (k - 2).toNat (castSymPow (k - 2).toNat P)) Fp r
      | .infty => Finf) := by
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symActC M (k - 2).toNat cP with hQ
  set G : ℂ → ℂ := fun z => Fp (mobM M z) with hG
  -- `G = Fp ∘ mobM M` is a primitive of `periodForm f₂ cP` (det-`p` Möbius covariance + slash).
  have hGderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt G (periodForm (⇑f₂) cP z) z := by
    intro z hz
    have hd := hasDerivAt_primitive_mobM_general (⇑f₁) M hM cP hk Fp hF hz
    rwa [show (⇑f₁ ∣[k] (heilbronnGL M hM.ne')) = ⇑f₂ from hf₂.symm] at hd
  -- Bottom boundary value of `Fp` (typed `f₁`) at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotF : ∀ r : ℚ, Tendsto (fun Y : ℝ => Fp ((r : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botVal f₁ Q Fp r)) := fun r => tendsto_primitive_vertical_nhdsGT_zero f₁ Q r Fp hF
  -- Bottom boundary value of `G` (generic `f₂`) at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotG : ∀ s : ℚ, Tendsto (fun Y : ℝ => G ((s : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botValGen f₂ cP G s)) := fun s =>
    tendsto_primitive_vertical_nhdsGT_zeroGen f₂ cP s G hGderiv
  -- `mob 1 = id`.
  have hmob1 : ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z := fun z => by simp [mob]
  -- The integer-matrix product `(σ⁻¹ : ℤ-mat) · M` has positive determinant.
  have hMprod_det : ∀ σ : SL(2, ℤ),
      0 < (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M).det := by
    intro σ
    rw [Matrix.det_mul, show ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from (σ⁻¹).prop,
      one_mul]; exact hM
  -- The Heilbronn element of `(σ⁻¹ : ℤ-mat) · M` factors as `mapGL ℚ σ⁻¹ * heilbronnGL M`.
  have hHfac : ∀ (σ : SL(2, ℤ)) (o' : OnePoint ℚ),
      (heilbronnGL (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) (hMprod_det σ).ne') • o'
        = (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) • ((heilbronnGL M hM.ne') • o') := by
    intro σ o'
    rw [heilbronnGL_mul ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) M (sl_det_ne_zero σ⁻¹)
      hM.ne' (hMprod_det σ).ne', heilbronnGL_sl, mul_smul]
  -- A σ-frame top value of `Fp` (the top value of `Fp ∘ mob σ`), for any `σ ∈ SL(2, ℤ)`.
  have hframe : ∀ σ : SL(2, ℤ), ∃ Lσ : ℂ,
      ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp (mob σ ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Lσ) := by
    intro σ
    haveI harith : (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ •
        ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
      have hmap : (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
          = ((mapGL ℚ σ)⁻¹).map (algebraMap ℚ ℝ) := by rw [map_inv, map_mapGL]
      rw [hmap]
      exact Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
    obtain ⟨Lσ, hLσ⟩ := exists_tendsto_primitive_vertical_atTop'
      (CuspForm.translate f₁ (Matrix.SpecialLinearGroup.mapGL ℝ σ))
      (symRep ℂ (k - 2).toNat σ⁻¹ Q) (fun z => Fp (mob σ z)) (by
        intro z hz
        have hsr : symRep ℂ (k - 2).toNat σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) = Q := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
        have hd := hasDerivAt_primitive_mob_general (⇑f₁) σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) hk Fp
          (by rwa [hsr]) hz
        have hcoe : ⇑(CuspForm.translate f₁ (Matrix.SpecialLinearGroup.mapGL ℝ σ))
            = ⇑f₁ ∣[k] σ := by rw [ModularForm.SL_slash]; rfl
        rw [hcoe]; exact hd)
    exact ⟨Lσ, hLσ⟩
  cases o with
  | infty =>
    -- LHS = `Ginf`.  Split on whether `heilbronnGL M • ∞ = ∞`.
    show Ginf = _
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : (heilbronnGL M hM.ne') 1 0 = 0
    · -- `M` upper-triangular: `M • ∞ = ∞`, RHS = `Finf`; show `Ginf = Finf` (case A).
      rw [if_pos hc]
      have hc0 : (M 1 0 : ℝ) = 0 := by
        have : ((M 1 0 : ℤ) : ℚ) = 0 := by rw [← heilbronnGL_entry M hM.ne' 1 0]; exact hc
        exact_mod_cast this
      exact tendsto_nhds_unique (hGinf 0) (tendsto_FM_upper f₁ hk M hM cP Fp hF Finf hFinf 0 hc0)
    · -- `M • ∞ = M₀₀/M₁₀` finite, RHS = `botVal f₁ Q Fp r`; show
      -- `Ginf = botVal f₁ Q Fp r` (case B).
      rw [if_neg hc]
      set r : ℚ := (heilbronnGL M hM.ne') 0 0 / (heilbronnGL M hM.ne') 1 0 with hr
      show Ginf = botVal f₁ Q Fp r
      have hMr : (heilbronnGL M hM.ne') • (∞ : OnePoint ℚ) = (r : OnePoint ℚ) := by
        rw [OnePoint.smul_infty_eq_ite, if_neg hc]
      -- Pick `σ` with `σ • ∞ = r`, and its frame top value `Lσ`.
      obtain ⟨σ, hσ⟩ := ((r : OnePoint ℚ)).exists_mem_SL2 ℤ
      obtain ⟨Lσ, hLσ⟩ := hframe σ
      have hσr : (Matrix.SpecialLinearGroup.mapGL ℚ σ) • (∞ : OnePoint ℚ) = (r : OnePoint ℚ) := hσ
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) • (r : OnePoint ℚ) = ∞ := by
        rw [map_inv, ← hσr, ← mul_smul, inv_mul_cancel, one_smul]
      -- `Ginf = Lσ`: `(σ⁻¹ · M)` is upper-triangular (`σ⁻¹ • (M•∞) = σ⁻¹•r = ∞`).
      have hupinfty : (heilbronnGL (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M)
          (hMprod_det σ).ne') • (∞ : OnePoint ℚ) = ∞ := by
        rw [hHfac σ ∞, hMr, hsmulr]
      have hupzero : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 = 0 := by
        have h10 := (OnePoint.smul_infty_eq_self_iff
          (g := heilbronnGL (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M)
            (hMprod_det σ).ne')).mp hupinfty
        rw [heilbronnGL_entry _ (hMprod_det σ).ne' 1 0] at h10
        exact_mod_cast h10
      have hGinf_eq : Ginf = Lσ :=
        tendsto_nhds_unique (hGinf 0)
          (tendsto_FM_upper_gen f₁ hk M hM cP Fp hF σ Lσ hLσ 0 hupzero)
      -- `botVal f₁ Q Fp r = Lσ`: vertical ray at `r`, pole `σ⁻¹` (`σ⁻¹•r = ∞`).
      obtain ⟨hcR, hpoleR⟩ := pole_of_smul_infty σ⁻¹ r hsmulr
      have hbotr := tendsto_F_pole f₁ hk Q Fp hF σ Lσ hLσ 1 (r:ℝ)
        (by simpa using hcR) (by simpa using hpoleR)
      simp only [hmob1] at hbotr
      rw [hGinf_eq, tendsto_nhds_unique (hbotF r) hbotr]
  | coe s =>
    -- LHS = `botValGen f₂ cP G s`.  Split on whether `heilbronnGL M • s = ∞`.
    show botValGen f₂ cP G s = _
    rw [OnePoint.smul_some_eq_ite]
    by_cases hc : (heilbronnGL M hM.ne') 1 0 * (s:ℚ) + (heilbronnGL M hM.ne') 1 1 = 0
    · -- `M • s = ∞`, RHS = `Finf`; show `botValGen f₂ cP G s = Finf` (case C).
      rw [if_pos hc]
      have hsmuls : (heilbronnGL M hM.ne') • (s : OnePoint ℚ) = ∞ := by
        rw [OnePoint.smul_some_eq_ite, if_pos hc]
      obtain ⟨hcs, hpoles⟩ := pole_of_smul_infty_M M hM.ne' s hsmuls
      -- Identity-frame `σ = 1`: pole matrix `(1⁻¹ · M) = M`; need its entries.
      have hcs1 : (((1⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 ≠ 0 := by
        simpa using hcs
      have hpoles1 : ((((1⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 : ℝ) * (s:ℝ) +
          ((((1⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 1 : ℝ) = 0 := by
        simpa using hpoles
      have hbots := tendsto_FM_pole f₁ hk M hM cP Fp hF 1 Finf
        (by intro q; simpa only [hmob1] using hFinf q) (s:ℝ) hcs1 hpoles1
      have hbotGs : Tendsto (fun Y : ℝ => Fp (mobM M ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botValGen f₂ cP G s)) := hbotG s
      exact tendsto_nhds_unique hbotGs hbots
    · -- `M • s = r` finite, RHS = `botVal f₁ Q Fp r`; show LHS = RHS (case D).
      rw [if_neg hc]
      set r : ℚ := ((heilbronnGL M hM.ne') 0 0 * (s:ℚ) + (heilbronnGL M hM.ne') 0 1)
        / ((heilbronnGL M hM.ne') 1 0 * (s:ℚ) + (heilbronnGL M hM.ne') 1 1) with hr
      show botValGen f₂ cP G s = botVal f₁ Q Fp r
      have hMsr : (heilbronnGL M hM.ne') • (s : OnePoint ℚ) = (r : OnePoint ℚ) := by
        rw [OnePoint.smul_some_eq_ite, if_neg hc]
      obtain ⟨σ, hσ⟩ := ((r : OnePoint ℚ)).exists_mem_SL2 ℤ
      obtain ⟨Lσ, hLσ⟩ := hframe σ
      have hσr : (Matrix.SpecialLinearGroup.mapGL ℚ σ) • (∞ : OnePoint ℚ) = (r : OnePoint ℚ) := hσ
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) • (r : OnePoint ℚ) = ∞ := by
        rw [map_inv, ← hσr, ← mul_smul, inv_mul_cancel, one_smul]
      -- LHS = `Lσ`: arc curve `mobM M`, pole `(σ⁻¹ · M)` at `s` (`(σ⁻¹·M)•s = σ⁻¹•r = ∞`).
      have hsmulσMs : (heilbronnGL (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M)
          (hMprod_det σ).ne') • (s : OnePoint ℚ) = ∞ := by
        rw [hHfac σ s, hMsr, hsmulr]
      obtain ⟨hcD, hpoleD⟩ := pole_of_smul_infty_M
        (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) (hMprod_det σ).ne' s hsmulσMs
      have hcD' : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) 1 0 ≠ 0 := by
        exact_mod_cast hcD
      have hLHS := tendsto_FM_pole f₁ hk M hM cP Fp hF σ Lσ hLσ (s:ℝ) hcD' hpoleD
      have hbotGs : Tendsto (fun Y : ℝ => Fp (mobM M ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botValGen f₂ cP G s)) := hbotG s
      -- RHS = `Lσ`: vertical ray at `r`, pole `σ⁻¹` (`σ⁻¹•r = ∞`).
      obtain ⟨hcR, hpoleR⟩ := pole_of_smul_infty σ⁻¹ r hsmulr
      have hRHS := tendsto_F_pole f₁ hk Q Fp hF σ Lσ hLσ 1 (r:ℝ)
        (by simpa using hcR) (by simpa using hpoleR)
      simp only [hmob1] at hRHS
      rw [tendsto_nhds_unique hbotGs hLHS, tendsto_nhds_unique (hbotF r) hRHS]

/-- **The determinant-`p` cusp-value covariance.**  For an integer matrix `M` with `0 < M.det`, the
conjugate cusp form `f ∣ heilbronnGL M`, and any `P : Sym^{k-2}(ℤ)`, the cusp value of `f` against
the adjugate-substituted `symActC M (cast P)` at the Möbius-moved cusp
`heilbronnGL M • c` equals the
generic cusp value of the conjugate `f ∣ heilbronnGL M` against `cast P` at `c`, up to a
`c`-independent constant.  Determinant-`p` analogue of `cuspValue_symRep_sl`. -/
theorem cuspValueGen_symActC_heilbronn (hk : 2 ≤ k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
    (P : SymPow ℤ (k - 2).toNat) :
    ∃ T : ℂ, ∀ c : Projectivization ℚ (Fin 2 → ℚ),
      cuspValue f (symActC M (k - 2).toNat (castSymPow (k - 2).toNat P))
          ((heilbronnGL M hM.ne') • c) =
        cuspValueGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne')))
          (castSymPow (k - 2).toNat P) c + T := by
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symActC M (k - 2).toNat cP with hQ
  set f₂ := CuspForm.translate f (glMap (heilbronnGL M hM.ne')) with hf₂def
  have hf₂ : (⇑f₂ : ℍ → ℂ) = ⇑f ∣[k] (heilbronnGL M hM.ne') := rfl
  -- A primitive `Fp` of `periodForm f Q` on the upper half-plane.
  obtain ⟨Fp, hFp⟩ := Complex.isExactOn_upperHalf (differentiableOn_periodForm f Q)
  have hFz : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f) Q z) z := hFp
  -- `G := Fp ∘ mobM M` is a primitive of `periodForm f₂ cP`.
  have hG : ∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun w => Fp (mobM M w)) (periodForm (⇑f₂) cP z) z := by
    intro z hz
    have hd := hasDerivAt_primitive_mobM_general (⇑f) M hM cP hk Fp hFz hz
    rwa [show (⇑f ∣[k] (heilbronnGL M hM.ne')) = ⇑f₂ from hf₂.symm] at hd
  -- Top boundary values.
  obtain ⟨Finf, hFinf⟩ := exists_tendsto_primitive_vertical_atTop f Q Fp hFz
  obtain ⟨Ginf, hGinf⟩ := exists_tendsto_primitive_vertical_atTop' f₂ cP
    (fun w => Fp (mobM M w)) hG
  have hGinf' : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => Fp (mobM M ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf) := hGinf
  refine ⟨Finf - Ginf, fun c => ?_⟩
  -- Cusp-value formulas for both sides.
  have hcvQ := cuspValue_eq_top_sub_botVal f Q Fp hFz Finf hFinf ((heilbronnGL M hM.ne') • c)
  have hcvP := cuspValueGen_eq_top_sub_botValGen f₂ cP (fun w => Fp (mobM M w)) hG Ginf hGinf c
  rw [hcvQ, hcvP]
  -- The cusp dictionary: the `OnePoint` representative of `(heilbronnGL M) • c` is
  -- `(heilbronnGL M) • (rep c)`.
  have hdict : (OnePoint.equivProjectivization ℚ).symm ((heilbronnGL M hM.ne') • c)
      = (heilbronnGL M hM.ne') • (OnePoint.equivProjectivization ℚ).symm c := by
    rw [Equiv.symm_apply_eq, OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  rw [hdict]
  -- Reduce to the determinant-`p` boundary naturality.
  have hnat := cuspBoundary_mobM_naturality f f₂ M hM hf₂ P hk Fp hFz Finf Ginf hFinf hGinf'
    ((OnePoint.equivProjectivization ℚ).symm c)
  rw [hQ, hcP]
  linear_combination hnat

/-- **The determinant-`p` change of variables for `rawPairing`.**  For an integer matrix `M` with
`0 < M.det`, the generic raw pairing of the conjugate cusp form `f ∣ heilbronnGL M` against `x`
equals the typed raw pairing of `f` against the Heilbronn-acted `actMat M x`.  The `c`-independent
tail of `cuspValueGen_symActC_heilbronn` cancels because the divisor has degree `0`.
Determinant-`p`
analogue of `rawPairing_fullModSymRep_sl`. -/
theorem rawPairingGen_actMat (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    rawPairingGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne'))) x =
      rawPairing f (actMat M hM.ne' (k - 2).toNat x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul D P =>
    obtain ⟨T, hT⟩ := cuspValueGen_symActC_heilbronn hk f M hM P
    -- The RHS `rawPairing f (actMat M (D ⊗ P))` expands as the `rawBilin` of the `M`-moved divisor
    -- and the `symAct`-acted polynomial.
    show rawBilinGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne')))
        (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff P =
      rawBilin f ((divAct M hM.ne' D : Div0 ℤ) :
          MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff
        (symAct M (k - 2).toNat P)
    -- Expand both `rawBilin`/`rawBilinGen` as `Finsupp.sum` against cusp values.
    have hrb : ∀ (D' : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P' : SymPow ℤ (k - 2).toNat),
        rawBilin f D' P' =
          D'.sum (fun c n => (n : ℂ) * cuspValue f (castSymPow (k - 2).toNat P') c) := by
      intro D' P'
      simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
    have hrbG : ∀ (D' : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P' : SymPow ℤ (k - 2).toNat),
        rawBilinGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne'))) D' P' =
          D'.sum (fun c n => (n : ℂ) *
            cuspValueGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne')))
              (castSymPow (k - 2).toNat P') c) := by
      intro D' P'
      simp only [rawBilinGen, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctionalGen, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
    rw [hrb, hrbG, castSymPow_symActC]
    -- Reindex the `M`-image divisor sum injectively.
    have hdiv : ((divAct M hM.ne' D) : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff =
        Finsupp.mapDomain ((heilbronnGL M hM.ne') • ·)
          (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff := by
      rw [divAct_coe]
    have hinj : Function.Injective
        (fun c : Projectivization ℚ (Fin 2 → ℚ) => (heilbronnGL M hM.ne') • c) :=
      MulAction.injective _
    rw [hdiv, Finsupp.sum_mapDomain_index_inj hinj]
    -- Combine into a single degree-0 sum of the (constant) cusp-value difference.
    rw [← sub_eq_zero, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    have hsummand : ∀ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) *
            cuspValueGen (CuspForm.translate f (glMap (heilbronnGL M hM.ne')))
              (castSymPow (k - 2).toNat P) c -
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) *
            cuspValue f (symActC M (k - 2).toNat (castSymPow (k - 2).toNat P))
              ((heilbronnGL M hM.ne') • c) =
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) * (-T) := by
      intro c _
      rw [hT c]; ring
    rw [Finset.sum_congr rfl hsummand, ← Finset.sum_mul]
    have hsum0 : (∑ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ)) = 0 := by
      rw [← Int.cast_sum]
      have := Div0.sum_coeff_eq_zero D
      rw [Finsupp.sum] at this
      rw [this, Int.cast_zero]
    rw [hsum0, zero_mul]
  | add x y hx hy =>
    rw [map_add, hx, hy]
    exact (map_add (rawPairing f) _ _).symm.trans
      (congrArg (rawPairing f) (map_add (actMat M hM.ne' (k - 2).toNat) x y).symm)

/-! ### The slash decomposition: assembling the per-coset change of variables

The analytic Hecke operator `heckeEnd N k p = T_p` (`U_p` at bad primes) is the *sum* over the
Heilbronn cosets `M` of the slash `⇑f ∣ heilbronnGL M`.  Since the cusp value (hence `rawPairing`)
depends on the cusp form only through its underlying function and is additive over a pointwise
function-sum (the period integrand is linear in the function), `rawPairing (heckeEnd f)` is the sum
of the `rawPairingGen` of the conjugate cusp forms `f ∣ heilbronnGL M`.  Combined with
`rawPairingGen_actMat`, this expresses `rawPairing (heckeEnd f) x` as
`Σ_M rawPairing f (actMat M x)`
— matching the symbol-side `tpOp`/`upperOp` exactly. -/

/-- **Cusp-value additivity over a coset sum.**  If the underlying function of a `Γ₁(N)` cusp form
`g` is the finite sum `∑ i ∈ s, ⇑f ∣[k] glMap (heilbronnGL (Mfun i))`, then the cusp value of `g` is
the sum of the generic cusp values of the conjugate cusp forms `f ∣ glMap (heilbronnGL (Mfun i))`.
This is the function-additivity of the period integral (linear in the integrand). -/
theorem cuspValue_eq_sum_of_coe {ι : Type*} (s : Finset ι)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (Mfun : ι → Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : ∀ i ∈ s, (Mfun i).det ≠ 0) {m : ℕ} (P : SymPow ℂ m)
    (hcoe : (⇑g : ℍ → ℂ) =
      fun z => ∑ i ∈ s, (fun i => if h : (Mfun i).det ≠ 0 then
        (⇑f ∣[k] glMap (heilbronnGL (Mfun i) h)) z else 0) i)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue g P c =
      ∑ i ∈ s, if h : (Mfun i).det ≠ 0 then
        cuspValueGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h))) P c else 0 := by
  rw [← cuspValueGen_eq_cuspValue]
  simp only [cuspValueGen]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q =>
    show cuspToInftyIntegralGen g P q =
      ∑ i ∈ s, if h : (Mfun i).det ≠ 0 then
        cuspToInftyIntegralGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h))) P q else 0
    rw [cuspToInftyIntegralGen_eq_periodForm]
    -- The period integrand of `g` is the (pointwise) finite sum of those of the conjugates.
    have hsum_eq : ∀ t : ℝ, 0 < t →
        periodForm (⇑g) P ((q : ℂ) + t * Complex.I) * Complex.I =
          ∑ i ∈ s, (if h : (Mfun i).det ≠ 0 then
            periodForm (⇑(CuspForm.translate f (glMap (heilbronnGL (Mfun i) h)))) P
              ((q : ℂ) + t * Complex.I) * Complex.I
            else 0) := by
      intro t ht
      have him : 0 < ((q : ℂ) + (t : ℂ) * Complex.I).im := by simp [ht]
      have hgval : periodForm (⇑g) P ((q : ℂ) + t * Complex.I) =
          ∑ i ∈ s, (if h : (Mfun i).det ≠ 0 then
            periodForm (⇑(CuspForm.translate f (glMap (heilbronnGL (Mfun i) h)))) P
              ((q : ℂ) + t * Complex.I)
            else 0) := by
        simp only [periodForm]
        rw [hcoe]
        show (∑ x ∈ s, if h : (Mfun x).det ≠ 0 then
            (⇑f ∣[k] glMap (heilbronnGL (Mfun x) h))
              (UpperHalfPlane.ofComplex ((q : ℂ) + t * Complex.I)) else 0) *
            evalSym1 m P ((q : ℂ) + t * Complex.I) = _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [dif_pos (hdet i hi), dif_pos (hdet i hi)]
        rfl
      rw [hgval, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [dif_pos (hdet i hi), dif_pos (hdet i hi)]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => hsum_eq t (Set.mem_Ioi.mp ht))]
    rw [MeasureTheory.integral_finsetSum s (f := fun i (t : ℝ) =>
      if h : (Mfun i).det ≠ 0 then
        periodForm (⇑(CuspForm.translate f (glMap (heilbronnGL (Mfun i) h)))) P
          ((q : ℂ) + t * Complex.I) * Complex.I
      else 0) (fun i hi => by
        by_cases h : (Mfun i).det ≠ 0
        · simp only [dif_pos h]
          exact integrableOn_periodFormGen_vertical _ P q
        · simp only [dif_neg h]
          exact MeasureTheory.integrableOn_zero)]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [dif_pos (hdet i hi)]
    rw [cuspToInftyIntegralGen_eq_periodForm]

/-- **Raw-pairing additivity over a coset sum.**  Lifts `cuspValue_eq_sum_of_coe` from
cusp values to
the raw period pairing: if `⇑g = ∑ i ∈ s, ⇑f ∣[k] glMap (heilbronnGL (Mfun i))`, then
`rawPairing g x = ∑ i ∈ s, rawPairingGen (f ∣ glMap (heilbronnGL (Mfun i))) x`. -/
theorem rawPairing_eq_sum_of_coe {ι : Type*} (s : Finset ι)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (Mfun : ι → Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : ∀ i ∈ s, (Mfun i).det ≠ 0)
    (hcoe : (⇑g : ℍ → ℂ) =
      fun z => ∑ i ∈ s, (fun i => if h : (Mfun i).det ≠ 0 then
        (⇑f ∣[k] glMap (heilbronnGL (Mfun i) h)) z else 0) i)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    rawPairing g x =
      ∑ i ∈ s, if h : (Mfun i).det ≠ 0 then
        rawPairingGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h))) x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul D P =>
    rw [rawPairing_tmul]
    -- Expand each `rawBilin`/`rawPairingGen` as a `Finsupp.sum` of cusp values, using
    -- the cusp-value
    -- coset decomposition `cuspValue_eq_sum_of_coe`.
    have hrb : rawBilin g (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff P =
        (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.sum
          (fun c n => (n : ℂ) *
            ∑ i ∈ s, if h : (Mfun i).det ≠ 0 then
              cuspValueGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h)))
                (castSymPow (k - 2).toNat P) c else 0) := by
      simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [cuspValue_eq_sum_of_coe s f g Mfun hdet _ hcoe c]
    have hrbG : ∀ (i : ι), i ∈ s → ∀ (h : (Mfun i).det ≠ 0),
        rawPairingGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h))) (D ⊗ₜ P) =
          (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.sum
            (fun c n => (n : ℂ) *
              cuspValueGen (CuspForm.translate f (glMap (heilbronnGL (Mfun i) h)))
                (castSymPow (k - 2).toNat P) c) := by
      intro i hi h
      rw [rawPairingGen_tmul]
      simp only [rawBilinGen, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, cuspFunctionalGen, LinearMap.coe_mk, AddHom.coe_mk,
        zsmul_eq_mul]
    rw [hrb, Finsupp.sum]
    -- `Σ_c n_c · (Σ_i dite) = Σ_i dite (Σ_c n_c · cuspValueGen)`.
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : (Mfun i).det ≠ 0
    · rw [dif_pos h, hrbG i hi h, Finsupp.sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [dif_pos h]
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [dif_neg h, mul_zero]
  | add x y hx hy =>
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : (Mfun i).det ≠ 0
    · rw [dif_pos h, dif_pos h, dif_pos h, map_add]
    · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

/-! ## The Hecke `T_n` equivariance `hT`

We package the equivariance of a single operator as a relation `PeriodEquiv A B`, which is closed
under the ring operations used by the prime-power recurrence (sum, `ℤ`-scalar, product — the last in
reversed order, harmless once the symbol-side operators commute).  Matching the *identical*
recursions `heckeT_ppow`/`heckeSymbPpow` and `heckeT_n_aux`/`heckeSymb_aux` reduces the general-`n`
equivariance to the prime base case `heckeT_p_all`/`heckeSymb_p_all`, the genuine analytic input. -/

/-- The period-equivariance relation between a cusp-form endomorphism `A` and a modular-symbol
endomorphism `B`: `periodMap' (A f) = dualPrecomp B (periodMap' f)` for every cusp form
`f`.  Carries
the weight hypothesis `2 ≤ k` of the period map `periodMap'`. -/
def PeriodEquiv (hk : 2 ≤ k) (A : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (B : Module.End ℤ (𝕄 N k)) : Prop :=
  ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    periodMap' N k hk (A f) = dualPrecomp B (periodMap' N k hk f)

theorem PeriodEquiv.one (hk : 2 ≤ k) :
    PeriodEquiv hk (1 : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (1 : Module.End ℤ (𝕄 N k)) := by
  intro f; rw [Module.End.one_apply, dualPrecomp_one, Module.End.one_apply]

theorem PeriodEquiv.add {hk : 2 ≤ k} {A₁ A₂ : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    {B₁ B₂ : Module.End ℤ (𝕄 N k)} (h₁ : PeriodEquiv hk A₁ B₁) (h₂ : PeriodEquiv hk A₂ B₂) :
    PeriodEquiv hk (A₁ + A₂) (B₁ + B₂) := by
  intro f
  rw [LinearMap.add_apply, map_add, h₁ f, h₂ f, dualPrecomp_add, LinearMap.add_apply]

theorem PeriodEquiv.zsmul {hk : 2 ≤ k} {A : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    {B : Module.End ℤ (𝕄 N k)} (c : ℤ) (h : PeriodEquiv hk A B) :
    PeriodEquiv hk ((c : ℂ) • A) (c • B) := by
  intro f
  rw [LinearMap.smul_apply, map_smul, h f, dualPrecomp_zsmul, LinearMap.smul_apply,
    ← Int.cast_smul_eq_zsmul ℂ]

/-- Products: `PeriodEquiv` of two operators gives `PeriodEquiv` of the products *in reversed order*
on the symbol side (because `dualPrecomp` is an anti-homomorphism). -/
theorem PeriodEquiv.mul {hk : 2 ≤ k} {A₁ A₂ : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    {B₁ B₂ : Module.End ℤ (𝕄 N k)} (h₁ : PeriodEquiv hk A₁ B₁) (h₂ : PeriodEquiv hk A₂ B₂) :
    PeriodEquiv hk (A₁ * A₂) (B₂ * B₁) := by
  intro f
  rw [Module.End.mul_apply, h₁ (A₂ f), h₂ f, dualPrecomp_mul]
  rfl

theorem PeriodEquiv.sub {hk : 2 ≤ k} {A₁ A₂ : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    {B₁ B₂ : Module.End ℤ (𝕄 N k)} (h₁ : PeriodEquiv hk A₁ B₁) (h₂ : PeriodEquiv hk A₂ B₂) :
    PeriodEquiv hk (A₁ - A₂) (B₁ - B₂) := by
  intro f
  have hsub : dualPrecomp (B₁ - B₂) = dualPrecomp B₁ - dualPrecomp B₂ := by ext φ x; simp
  rw [LinearMap.sub_apply, map_sub, h₁ f, h₂ f, hsub, LinearMap.sub_apply]

theorem PeriodEquiv.zero (hk : 2 ≤ k) :
    PeriodEquiv hk (0 : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (0 : Module.End ℤ (𝕄 N k)) := by
  intro f; rw [LinearMap.zero_apply, map_zero, dualPrecomp_zero, LinearMap.zero_apply]

/-- `PeriodEquiv` respects products in the *same* order when the symbol-side factors commute (the
order-reversal of `dualPrecomp` is undone by the commutation).  Used for the prime-power recurrence,
where the symbol-side operators commute by `HeckeCommute`. -/
theorem PeriodEquiv.mul_commute {hk : 2 ≤ k}
    {A₁ A₂ : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    {B₁ B₂ : Module.End ℤ (𝕄 N k)} (h₁ : PeriodEquiv hk A₁ B₁) (h₂ : PeriodEquiv hk A₂ B₂)
    (hcomm : Commute B₁ B₂) :
    PeriodEquiv hk (A₁ * A₂) (B₁ * B₂) := by
  have := (h₁.mul h₂)
  rwa [← hcomm.eq] at this

/-! ### The diamond `PeriodEquiv` and its `n`-extension

`periodMap'_diamond` is `PeriodEquiv (diamondOpCusp k d) (diamondSymb N k d)`.  We extend it to the
`n`-indexed diamond operators `diamondOp_n`/`diamondSymb_n` (used in the prime-power recurrence). -/

/-- The `n`-indexed cusp diamond operator `⟨n⟩` on cusp forms: `diamondOpCusp (n mod N)` when
`(n, N) = 1`, zero otherwise.  The cusp-form analogue of `diamondSymb_n`. -/
noncomputable def diamondEnd_n (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  if h : Nat.Coprime n N then diamondOpCusp k (ZMod.unitOfCoprime n h) else 0

/-- The diamond equivariance, repackaged as a `PeriodEquiv`. -/
theorem periodEquiv_diamond (hk : 2 ≤ k) (d : (ZMod N)ˣ) :
    PeriodEquiv hk (diamondOpCusp k d) (diamondSymb N k d) :=
  fun f => periodMap'_diamond hk d f

/-- The `n`-indexed diamond equivariance, as a `PeriodEquiv`. -/
theorem periodEquiv_diamond_n (hk : 2 ≤ k) (n : ℕ) :
    PeriodEquiv hk (diamondEnd_n N k n) (diamondSymb_n N k n) := by
  by_cases h : Nat.Coprime n N
  · simp only [diamondEnd_n, diamondSymb_n, dif_pos h]
    exact periodEquiv_diamond hk _
  · simp only [diamondEnd_n, diamondSymb_n, dif_neg h]
    exact PeriodEquiv.zero hk

/-! ### The pure-algebra mirror reconciliation (leaf 2)

The genuine cusp Hecke operator `heckeEnd N k n` is built by the *forward* analytic recursion
`heckeT_n` (prime-power block on the left, in `heckeT_n_aux`), while the period-side mirror
`heckeEnd_aux` writes the prime-power block on the right (reversed, so `dualPrecomp`'s
order-reversal
matches the symbol recursion).  The two agree because all the prime-power Hecke blocks
commute, a fact
we lift from the *unrestricted* (all-prime, bad primes included) operator-level
commutativity already
available on `M_k(Γ₁(N))`:

* `heckeT_p_all_comm_distinct` — `T_p T_q = T_q T_p` for distinct primes (all four good/bad cases);
* `heckeT_p_all_comm_diamondOp` — `T_p ⟨d⟩ = ⟨d⟩ T_p` (all primes);
* `Unified.heckeT_n_comm_diamondOp_all` — `⟨d⟩ T_n = T_n ⟨d⟩` for all `n`.

These feed a generic `Commute`-against-`heckeT_ppow` engine (`commute_heckeT_ppow_mf`), then the
distinct-prime block commutation `commute_heckeT_ppow_heckeT_n_mf`, and finally the bridges from the
cusp-restricted operators (`heckeEnd`, `diamondEnd_n`, `heckeEndPpow`, `heckeEnd_aux`) to the
underlying `M_k`-operators via `toModularForm'`. -/

/-- Bridge: the cusp diamond operator `⟨d⟩` and the modular-form diamond operator agree under
`toModularForm'` (both act by the same slash `f ∣ mapGL ℝ g` on a shared representative). -/
theorem diamondOpCusp_toModularForm' (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (HeckeRing.GL2.diamondOpCusp k d f).toModularForm' =
      HeckeRing.GL2.diamondOp k d f.toModularForm' :=
  rfl

/-- Bridge: the prime cusp Hecke operator `heckeEnd N k ⟨p, _⟩` agrees, under `toModularForm'`, with
the modular-form prime operator `heckeT_p_all`. -/
theorem heckeEnd_prime_toModularForm' {p : ℕ} (hp : Nat.Prime p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (heckeEnd N k ⟨p, hp.pos⟩ f).toModularForm' =
      HeckeRing.GL2.heckeT_p_all k p hp f.toModularForm' := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [show (heckeEnd N k ⟨p, hp.pos⟩ f).toModularForm'
      = HeckeRing.GL2.heckeT_n k p f.toModularForm' from rfl, HeckeRing.GL2.heckeT_n_prime k hp]

/-- Bridge: the extended cusp diamond `diamondEnd_n` agrees, under `toModularForm'`, with the
modular-form extended diamond `diamondOp_n`. -/
theorem diamondEnd_n_toModularForm' (p : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (diamondEnd_n N k p f).toModularForm' = HeckeRing.GL2.diamondOp_n k p f.toModularForm' := by
  by_cases h : Nat.Coprime p N
  · rw [diamondEnd_n, dif_pos h, HeckeRing.GL2.diamondOp_n_coprime k h]; rfl
  · rw [diamondEnd_n, dif_neg h, HeckeRing.GL2.diamondOp_n_not_coprime k h]; rfl

open HeckeRing.GL2 in
/-- The extended diamond `⟨p⟩` commutes with the prime operator `T_p` (all primes, bad included). -/
theorem commute_diamondOp_n_heckeT_p_all {p : ℕ} (hp : Nat.Prime p) :
    Commute (diamondOp_n (N := N) k p) (heckeT_p_all k p hp) := by
  by_cases h : Nat.Coprime p N
  · show diamondOp_n k p * heckeT_p_all k p hp = heckeT_p_all k p hp * diamondOp_n k p
    rw [diamondOp_n_coprime k h, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact heckeT_p_all_comm_diamondOp k p hp (ZMod.unitOfCoprime p h)
  · simp [diamondOp_n_not_coprime k h, Commute, SemiconjBy]

open HeckeRing.GL2 in
/-- **Generic `heckeT_ppow` commutation engine.**  Any modular-form operator `T` that commutes with
both the prime operator `T_p` and the extended diamond `⟨p⟩` commutes with every power `T_{p^r}`.
(`heckeT_ppow` is assembled from exactly these two operators by the Hecke recurrence.) -/
theorem commute_heckeT_ppow_mf {p : ℕ} (hp : Nat.Prime p)
    (T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hTp : Commute T (heckeT_p_all k p hp)) (hTd : Commute T (diamondOp_n k p)) (r : ℕ) :
    Commute T (heckeT_ppow k p hp r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hTp
  | more r ih1 ih2 =>
    rw [heckeT_ppow_succ_succ]
    exact (hTp.mul_right ih2).sub_right ((hTd.mul_right ih1).smul_right _)

open HeckeRing.GL2 in
/-- `T_p` commutes with `T_{p^r}` (same prime, all `r`). -/
theorem commute_heckeT_p_all_heckeT_ppow {p : ℕ} (hp : Nat.Prime p) (r : ℕ) :
    Commute (heckeT_p_all (N := N) k p hp) (heckeT_ppow k p hp r) :=
  commute_heckeT_ppow_mf hp _ (Commute.refl _) (commute_diamondOp_n_heckeT_p_all hp).symm r

open HeckeRing.GL2 in
/-- `T_p` commutes with `T_{q^s}` for distinct primes `p ≠ q` (all four good/bad cases). -/
theorem commute_heckeT_p_all_heckeT_ppow_distinct {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (s : ℕ) :
    Commute (heckeT_p_all (N := N) k p hp) (heckeT_ppow k q hq s) := by
  refine commute_heckeT_ppow_mf hq _ ?_ ?_ s
  · exact heckeT_p_all_comm_distinct k hp hq hpq
  · by_cases h : Nat.Coprime q N
    · show heckeT_p_all k p hp * diamondOp_n k q = diamondOp_n k q * heckeT_p_all k p hp
      rw [diamondOp_n_coprime k h, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
      exact (heckeT_p_all_comm_diamondOp k p hp (ZMod.unitOfCoprime q h)).symm
    · simp [diamondOp_n_not_coprime k h, Commute, SemiconjBy]

open HeckeRing.GL2 in
/-- `T_p` commutes with `T_m` whenever `p ∤ m` (distinct-prime block commutation, all primes). -/
theorem commute_heckeT_p_all_heckeT_n {p : ℕ} (hp : Nat.Prime p) (m : ℕ) [NeZero m]
    (hpm : ¬ p ∣ m) :
    Commute (heckeT_p_all (N := N) k p hp) (heckeT_n k m) := by
  suffices H : ∀ j : ℕ, (hj0 : NeZero j) → ¬ p ∣ j →
      Commute (heckeT_p_all (N := N) k p hp) (heckeT_n k j) from H m ‹_› hpm
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj0 hpj
    haveI := hj0
    rcases eq_or_ne j 1 with rfl | hj1
    · simp
    · have hj : 1 < j := by have := NeZero.ne j; omega
      rw [heckeT_n_unfold k j hj]
      set q := j.minFac with hq_def
      have hq : Nat.Prime q := Nat.minFac_prime (by omega)
      set v := j.factorization q with hv_def
      have hv_pos : 0 < v := hq.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd j)
      have hdiv_pos : 0 < j / q ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j q)) (pow_pos hq.pos v)
      haveI : NeZero (j / q ^ v) := ⟨hdiv_pos.ne'⟩
      have hdiv_lt : j / q ^ v < j :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hq.one_lt)
      have hpq : p ≠ q := by
        rintro rfl
        exact hpj (hq_def ▸ Nat.minFac_dvd j)
      have hp_quot : ¬ p ∣ j / q ^ v :=
        fun h ↦ hpj (h.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd j q)))
      exact (commute_heckeT_p_all_heckeT_ppow_distinct hp hq hpq v).mul_right
        (ih _ hdiv_lt ⟨hdiv_pos.ne'⟩ hp_quot)

open HeckeRing.GL2 in
/-- `T_{p^w}` commutes with `T_m` whenever `p ∤ m` (distinct-prime block commutation,
all primes). -/
theorem commute_heckeT_ppow_heckeT_n {p : ℕ} (hp : Nat.Prime p) (w m : ℕ) [NeZero m]
    (hpm : ¬ p ∣ m) :
    Commute (heckeT_ppow (N := N) k p hp w) (heckeT_n k m) := by
  refine (commute_heckeT_ppow_mf hp (heckeT_n k m) ?_ ?_ w).symm
  · exact (commute_heckeT_p_all_heckeT_n hp m hpm).symm
  · exact (Unified.heckeT_n_comm_diamondOp_all k m p).symm

/-- **The determinant-`p` per-coset change of variables (the isolated analytic input).**  For each
prime `p` the period map intertwines the prime cusp Hecke operator `heckeEnd N k p` (= `T_p` at good
primes, `U_p` at bad primes) with the integral modular-symbol operator `heckeSymb_p_all N k p hp`.

This is the determinant-`p` analogue of the diamond-case equivariance
`periodMap'_diamond` (which was
proven via the det-`1` change of variables `rawPairing_fullModSymRep_sl`).  Its proof is the
determinant-`p` boundary naturality — the geodesic-period (`μ ≡ 0`) fact for the conjugate cusp form
`f ∣ heilbronnGL M` at each Heilbronn coset representative `M` (`upperMat`/`lowerDiamondMat`,
determinant `p`), summed over the `p + 1` cosets.  All the *integrand-level* change-of-variables
infrastructure is proven, sorry-free, above:

* `evalSym1_symActC_mobM` — the determinant-`p` `evalSym1` covariance (the `(det M)^m`-scaled
  analogue of `evalSym1_symRep_smul`);
* `periodForm_mobM_general` — the integrand change of variables
  `periodForm h₀ (symActC M R)(mobM M w) · (det M · D⁻²) = periodForm (h₀ ∣ heilbronnGL M) R w`
  (all determinant and automorphy factors cancel, the determinant-`p` analogue of
  `periodForm_mob_general`);
* `hasDerivAt_primitive_mobM_general` — the corresponding primitive pullback;
* `tendsto_FM_pole` / `tendsto_FM_upper` — the σ-conjugate-frame boundary limits for the det-`p`
  Möbius pole/upper geodesics (via the Möbius composition `mob_mobM_comp` and the det-`p` pole/upper
  geometry `mobM_pole_eq` / `mobM_upper_eq`).

The generalisation of the `Γ₁(N)`-typed cusp-value machinery to an arbitrary arithmetic cusp form is
now **complete and sorry-free** (`cuspValueGen`/`botValGen`/`rawPairingGen` with the cusp-value
formula `cuspValueGen_eq_top_sub_botValGen`), as are the two assembly steps:

* `rawPairingGen_actMat` — the determinant-`p` per-coset change of variables
  `rawPairingGen (f ∣ heilbronnGL M) x = rawPairing f (actMat M x)` (modulo the single deep input
  `cuspValueGen_symActC_heilbronn`, the determinant-`p` cusp-value covariance / boundary
  naturality);
* `rawPairing_eq_sum_of_coe` — the function-additivity expressing `rawPairing (heckeEnd f) x` as the
  sum over the Heilbronn cosets `Σ_M rawPairingGen (f ∣ heilbronnGL M) x`.

Discharging this statement now reduces to (i) the deep boundary naturality
`cuspValueGen_symActC_heilbronn` (the lone genuine analytic input, isolated as its own lemma), and
(ii) the finite-combinatorial coset bookkeeping matching the analytic slash decomposition
`heckeT_p_all f = Σ_M f ∣ heilbronnGL M` to the symbol-side `tpOp`/`upperOp = Σ_M actMat M`. -/
theorem periodEquiv_heckeEnd_prime (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) :
    PeriodEquiv hk (heckeEnd N k ⟨p, hp.pos⟩) (heckeSymb_p_all N k p hp) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro f
  -- Reduce to generators `𝕄.mk z`.
  refine LinearMap.ext fun μ => ?_
  obtain ⟨z, rfl⟩ := 𝕄.mk_surjective N k μ
  rw [periodMap'_apply_mk, dualPrecomp_apply]
  -- The underlying function of `heckeEnd N k ⟨p,_⟩ f` is `heckeT_p_all k p hp f.toModularForm'`.
  have hcoeEnd : (⇑(heckeEnd N k ⟨p, hp.pos⟩ f) : ℍ → ℂ)
      = ⇑(HeckeRing.GL2.heckeT_p_all k p hp f.toModularForm') :=
    congrArg (fun g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k => (⇑g : ℍ → ℂ))
      (heckeEnd_prime_toModularForm' hp f)
  by_cases hpN : Nat.Coprime p N
  · -- Good prime: `heckeSymb_p_all = tpSymb`, `tpOp = upperOp + actMat lowerDiamondMat`.
    rw [show heckeSymb_p_all N k p hp = tpSymb hp hpN k from dif_pos hpN, tpSymb_mk,
      periodMap'_apply_mk]
    -- The `p+1` coset matrices: `upperMat p b` for `b < p`, and `lowerDiamondMat` at `b = p`.
    set Mfun : ℕ → Matrix (Fin 2) (Fin 2) ℤ :=
      fun b => if b < p then upperMat p b else lowerDiamondMat (N := N) hpN with hMfun
    -- Every coset matrix has determinant `p` (both branches), so `det ≠ 0` unconditionally.
    have hdetpos : ∀ b, 0 < (Mfun b).det := by
      intro b
      simp only [hMfun]
      by_cases hbp : b < p
      · rw [if_pos hbp, upperMat_det]; exact_mod_cast hp.pos
      · rw [if_neg hbp, lowerDiamondMat_det]; exact_mod_cast hp.pos
    have hdet : ∀ b ∈ Finset.range (p + 1), (Mfun b).det ≠ 0 :=
      fun b _ => (hdetpos b).ne'
    -- The lower-term coset identity:
    -- `⇑(⟨p⟩ f) ∣ T_p_lower = ⇑f ∣ glMap(heilbronnGL lowerDiamondMat)`.
    have hlower : (⇑(HeckeRing.GL2.diamondOp k (ZMod.unitOfCoprime p hpN) f.toModularForm')
          ∣[k] (HeckeRing.GL2.T_p_lower p hp.pos : GL (Fin 2) ℚ))
        = ⇑f ∣[k] glMap (heilbronnGL (lowerDiamondMat (N := N) hpN)
            (lowerDiamondMat_det_ne_zero hp.pos hpN)) := by
      have hdmdet : (diamondMat (N := N) hpN).det ≠ 0 := by
        rw [diamondMat]; exact sl_det_ne_zero _
      -- Factor the Heilbronn element of `lowerDiamondMat` as a `GL(2, ℚ)` product (no
      -- matrix rewrite).
      have hGLfac : heilbronnGL (lowerDiamondMat (N := N) hpN)
          (lowerDiamondMat_det_ne_zero hp.pos hpN)
          = heilbronnGL (diamondMat (N := N) hpN) hdmdet *
            heilbronnGL (lowerMat p) (lowerMat_det_ne_zero hp.pos) :=
        heilbronnGL_mul (diamondMat (N := N) hpN) (lowerMat p) hdmdet (lowerMat_det_ne_zero hp.pos)
          (lowerDiamondMat_det_ne_zero hp.pos hpN)
      -- `heilbronnGL diamondMat = heilbronnGL (diamondRep : ℤ-mat) = mapGL ℚ diamondRep`.
      have hdiamGL : heilbronnGL (diamondMat (N := N) hpN) hdmdet
          = Matrix.SpecialLinearGroup.mapGL ℚ (diamondRep (N := N) hpN : SL(2, ℤ)) :=
        heilbronnGL_sl (diamondRep (N := N) hpN : SL(2, ℤ))
      -- The diamond slash on `f`, via the chosen `Γ₀(N)` representative `diamondRep`.
      have hd2 : (⇑(HeckeRing.GL2.diamondOp k (ZMod.unitOfCoprime p hpN) f.toModularForm') : ℍ → ℂ)
          = ⇑f ∣[k] glMap (heilbronnGL (diamondMat (N := N) hpN) hdmdet) := by
        rw [hdiamGL, glMap_mapGL_eq,
          HeckeRing.GL2.diamondOp_eq_diamondOpAux k _ (diamondRep (N := N) hpN)
            (diamondRep_spec hpN)]
        rfl
      rw [hGLfac, heilbronnGL_lowerMat hp.pos, map_mul, SlashAction.slash_mul, hd2]
      rfl
    -- The analytic coset decomposition
    -- `⇑(heckeEnd f) = Σ_{b<p+1} dite(⇑f ∣ glMap(heilbronnGL (Mfun b)), 0)`.
    have hcoe : (⇑(heckeEnd N k ⟨p, hp.pos⟩ f) : ℍ → ℂ) =
        fun zz => ∑ b ∈ Finset.range (p + 1), (fun b => if h : (Mfun b).det ≠ 0 then
          (⇑f ∣[k] glMap (heilbronnGL (Mfun b) h)) zz else 0) b := by
      rw [hcoeEnd, HeckeRing.GL2.heckeT_p_all_coprime k hp hpN]
      -- `⇑(heckeT_p F) = heckeT_p_fun = heckeT_p_ut(⇑f) + ⇑(⟨p⟩f) ∣ T_p_lower`.
      have hfun : (⇑(HeckeRing.GL2.heckeT_p k p hp hpN f.toModularForm') : ℍ → ℂ)
          = HeckeRing.GL2.heckeT_p_ut k p hp.pos (⇑f) +
            ⇑(HeckeRing.GL2.diamondOp k (ZMod.unitOfCoprime p hpN) f.toModularForm')
              ∣[k] (HeckeRing.GL2.T_p_lower p hp.pos : GL (Fin 2) ℚ) := rfl
      rw [hfun, hlower]
      funext zz
      -- Split off the `b = p` lower term (every coset matrix has determinant `p ≠ 0`, so the
      -- `dite`s below collapse to their positive branch).
      rw [Finset.sum_range_succ]
      simp only [Pi.add_apply]
      congr 1
      · -- Upper sum: `Σ_{b<p} ⇑f ∣ glMap(T_p_upper) = Σ_{b<p} ⇑f ∣ glMap(heilbronnGL(upperMat))`.
        rw [HeckeRing.GL2.heckeT_p_ut, Finset.sum_apply]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_range] at hb
        rw [dif_pos ((hdetpos b).ne')]
        simp only [hMfun, if_pos hb]
        rw [← heilbronnGL_upperMat hp.pos b]
        rfl
      · -- Lower term: `b = p`, `Mfun p = lowerDiamondMat`.
        rw [dif_pos ((hdetpos p).ne')]
        simp only [hMfun, if_neg (lt_irrefl p)]
    -- The symbol coset decomposition `tpOp z = Σ_{b<p+1} actMat (Mfun b) z`.
    have hsymb : tpOp hp.pos hpN (k - 2).toNat z =
        ∑ b ∈ Finset.range (p + 1), actMat (Mfun b) (hdetpos b).ne' (k - 2).toNat z := by
      rw [tpOp, LinearMap.add_apply, upperOp_apply, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_range] at hb
        simp only [hMfun, if_pos hb]
      · simp only [hMfun, if_neg (lt_irrefl p)]
    -- Combine via `rawPairing_eq_sum_of_coe` + `rawPairingGen_actMat`.
    rw [rawPairing_eq_sum_of_coe (Finset.range (p + 1)) f (heckeEnd N k ⟨p, hp.pos⟩ f) Mfun hdet
      hcoe z, hsymb, map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [dif_pos (hdet b hb), rawPairingGen_actMat hk f (Mfun b) (hdetpos b) z]
  · -- Bad prime `p ∣ N`: `heckeSymb_p_all = upperSymb`, `U_p = upperOp` (upper sum only).
    rw [show heckeSymb_p_all N k p hp = upperSymb hp hpN k from dif_neg hpN, upperSymb_mk,
      periodMap'_apply_mk]
    -- The `p` upper coset matrices `upperMat p b` for `b < p`.
    have hdetpos : ∀ b, 0 < (upperMat p b).det := fun b => by
      rw [upperMat_det]; exact_mod_cast hp.pos
    have hdet : ∀ b ∈ Finset.range p, (upperMat p b).det ≠ 0 :=
      fun b _ => (hdetpos b).ne'
    -- The analytic coset decomposition
    -- `⇑(heckeEnd f) = Σ_{b<p} dite(⇑f ∣ glMap(heilbronnGL (upperMat p b)), 0)`.
    have hcoe : (⇑(heckeEnd N k ⟨p, hp.pos⟩ f) : ℍ → ℂ) =
        fun zz => ∑ b ∈ Finset.range p, (fun b => if h : (upperMat p b).det ≠ 0 then
          (⇑f ∣[k] glMap (heilbronnGL (upperMat p b) h)) zz else 0) b := by
      rw [hcoeEnd, show HeckeRing.GL2.heckeT_p_all k p hp = HeckeRing.GL2.heckeT_p_divN k p hp hpN
        from dif_neg hpN]
      -- `⇑(heckeT_p_divN F) = heckeT_p_ut(⇑f)`.
      have hfun : (⇑(HeckeRing.GL2.heckeT_p_divN k p hp hpN f.toModularForm') : ℍ → ℂ)
          = HeckeRing.GL2.heckeT_p_ut k p hp.pos (⇑f) := rfl
      rw [hfun]
      funext zz
      rw [HeckeRing.GL2.heckeT_p_ut, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      simp only [dif_pos ((hdetpos b).ne')]
      rw [← heilbronnGL_upperMat hp.pos b]
      rfl
    -- The symbol coset decomposition `upperOp z = Σ_{b<p} actMat (upperMat p b) z`.
    have hsymb : upperOp p hp.pos (k - 2).toNat z =
        ∑ b ∈ Finset.range p, actMat (upperMat p b) (hdetpos b).ne' (k - 2).toNat z :=
      upperOp_apply p hp.pos (k - 2).toNat z
    -- Combine via `rawPairing_eq_sum_of_coe` + `rawPairingGen_actMat`.
    rw [rawPairing_eq_sum_of_coe (Finset.range p) f (heckeEnd N k ⟨p, hp.pos⟩ f)
      (fun b => upperMat p b) hdet hcoe z, hsymb, map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [dif_pos (hdet b hb), rawPairingGen_actMat hk f (upperMat p b) (hdetpos b) z]

/-! ### The prime-power and general-`n` recurrence (pure algebra)

We mirror the symbol-side recursions `heckeSymbPpow` / `heckeSymb_aux` by CuspForm-`Module.End`
operators `heckeEndPpow` / `heckeEnd_aux`.  The mirror is written with the multiplicative factors in
the *reversed* order, so the order-reversal of `dualPrecomp` (`PeriodEquiv.mul`) lands
exactly on the
symbol-side recursions without needing any commutativity input.  We then reconcile the
mirror with the
genuine `heckeEnd` operator (where the analytic commutativity of Hecke operators is used). -/

/-- CuspForm-`Module.End` mirror of `heckeSymbPpow`: the `T_{p^r}` recurrence on cusp
forms, with the
*same* scalar `(p : ℤ)^{(k-1).toNat}` as the symbol side, and the products written in reversed order
(so `PeriodEquiv.mul`'s order-reversal matches the symbol recursion exactly). -/
noncomputable def heckeEndPpow (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    ℕ → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  | 0 => 1
  | 1 => heckeEnd N k ⟨p, hp.pos⟩
  | r + 2 =>
    heckeEndPpow N k p hp (r + 1) * heckeEnd N k ⟨p, hp.pos⟩ -
      (((p : ℤ) ^ (k - 1).toNat : ℤ) : ℂ) • (heckeEndPpow N k p hp r * diamondEnd_n N k p)

/-- `PeriodEquiv (heckeEndPpow p r) (heckeSymbPpow p r)`, by two-step induction.  The reversed-order
mirror means each multiplicative step is a direct `PeriodEquiv.mul` (no commutativity needed). -/
theorem periodEquiv_heckeEndPpow (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) (r : ℕ) :
    PeriodEquiv hk (heckeEndPpow N k p hp r) (heckeSymbPpow N k p hp r) := by
  induction r using Nat.twoStepInduction with
  | zero => exact PeriodEquiv.one hk
  | one => exact periodEquiv_heckeEnd_prime hk hp
  | more r ih₁ ih₂ =>
    rw [heckeSymbPpow_succ_succ]
    show PeriodEquiv hk (heckeEndPpow N k p hp (r + 1) * heckeEnd N k ⟨p, hp.pos⟩ -
        (((p : ℤ) ^ (k - 1).toNat : ℤ) : ℂ) • (heckeEndPpow N k p hp r * diamondEnd_n N k p)) _
    exact PeriodEquiv.sub
      (PeriodEquiv.mul ih₂ (periodEquiv_heckeEnd_prime hk hp))
      (PeriodEquiv.zsmul ((p : ℤ) ^ (k - 1).toNat)
        (PeriodEquiv.mul ih₁ (periodEquiv_diamond_n hk p)))

/-- CuspForm-`Module.End` mirror of `heckeSymb_aux`: peels off the smallest prime factor, with the
prime-power block written on the *right* (reversed order, matching `PeriodEquiv.mul`). -/
noncomputable def heckeEnd_aux (N : ℕ) [NeZero N] (k : ℤ) (m : ℕ) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  if h : m ≤ 1 then 1
  else
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    heckeEnd_aux N k (m / p ^ v) * heckeEndPpow N k p hp v
termination_by m
decreasing_by
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)).ne' hp.one_lt)

/-- `PeriodEquiv (heckeEnd_aux m) (heckeSymb_aux m)`, by strong induction matching the peel.  The
reversed-order mirror means the multiplicative step is a direct `PeriodEquiv.mul`. -/
theorem periodEquiv_heckeEnd_aux (hk : 2 ≤ k) (m : ℕ) :
    PeriodEquiv hk (heckeEnd_aux N k m) (heckeSymb_aux N k m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [heckeEnd_aux, heckeSymb_aux]
    by_cases hle : m ≤ 1
    · rw [dif_pos hle, dif_pos hle]; exact PeriodEquiv.one hk
    · rw [dif_neg hle, dif_neg hle]
      exact PeriodEquiv.mul (ih _ (heckeT_n_unfold_lt m (by omega)))
        (periodEquiv_heckeEndPpow hk _ _)

open HeckeRing.GL2 in
/-- Bridge: the reversed cusp prime-power mirror `heckeEndPpow` agrees, under `toModularForm'`, with
the forward modular-form prime-power operator `heckeT_ppow`.  The reversal is undone using the
same-prime commutations `commute_heckeT_p_all_heckeT_ppow` and the `heckeT_ppow`/`⟨p⟩` commutation;
the scalar mismatch `((p:ℤ)^(k-1).toNat : ℂ) = (p:ℂ)^(k-1)` holds because `k ≥ 2`. -/
theorem heckeEndPpow_toModularForm' (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) (r : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (heckeEndPpow N k p hp r f).toModularForm' = heckeT_ppow k p hp r f.toModularForm' := by
  -- The mirror scalar `((p:ℤ)^(k-1).toNat : ℂ)` equals the genuine `(p:ℂ)^(k-1)` for `k ≥ 2`.
  have hscal : (((p : ℤ) ^ (k - 1).toNat : ℤ) : ℂ) = ((p : ℂ) ^ (k - 1)) := by
    push_cast
    rw [← zpow_natCast (p : ℂ) (k - 1).toNat, show ((k - 1).toNat : ℤ) = k - 1 by omega]
  induction r using Nat.twoStepInduction generalizing f with
  | zero => rfl
  | one => exact heckeEnd_prime_toModularForm' hp f
  | more r ih1 ih2 =>
    -- Reversed cusp recursion applied to `f`; `toModularForm'` distributes over `-`/`•` by `rfl`.
    show ((heckeEndPpow N k p hp (r + 1) (heckeEnd N k ⟨p, hp.pos⟩ f)).toModularForm' -
        (((p : ℤ) ^ (k - 1).toNat : ℤ) : ℂ) •
          (heckeEndPpow N k p hp r (diamondEnd_n N k p f)).toModularForm') = _
    rw [ih2 (heckeEnd N k ⟨p, hp.pos⟩ f), heckeEnd_prime_toModularForm' hp f,
      ih1 (diamondEnd_n N k p f), diamondEnd_n_toModularForm' p f]
    -- The two same-prime commutations, applied pointwise to `f.toModularForm'`.
    have hc1 : heckeT_ppow k p hp (r + 1) (heckeT_p_all k p hp f.toModularForm') =
        heckeT_p_all k p hp (heckeT_ppow k p hp (r + 1) f.toModularForm') :=
      LinearMap.congr_fun (commute_heckeT_p_all_heckeT_ppow hp (r + 1)).symm f.toModularForm'
    have hc2 : heckeT_ppow k p hp r (diamondOp_n k p f.toModularForm') =
        diamondOp_n k p (heckeT_ppow k p hp r f.toModularForm') :=
      LinearMap.congr_fun (commute_heckeT_ppow_mf hp (diamondOp_n k p)
        (commute_diamondOp_n_heckeT_p_all hp) (Commute.refl _) r).symm f.toModularForm'
    -- Forward modular-form recursion.
    rw [heckeT_ppow_succ_succ]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [hscal, hc1, hc2]

open HeckeRing.GL2 in
/-- Bridge: the reversed cusp mirror `heckeEnd_aux` agrees, under `toModularForm'`, with the forward
modular-form operator `heckeT_n`.  The reversal of the peel is undone using the distinct-prime block
commutation `commute_heckeT_ppow_heckeT_n`. -/
theorem heckeEnd_aux_toModularForm' (hk : 2 ≤ k) (m : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hm0 : NeZero m) :
    (heckeEnd_aux N k m f).toModularForm' = heckeT_n k m f.toModularForm' := by
  suffices H : ∀ j : ℕ, (hj0 : NeZero j) →
      ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        (heckeEnd_aux N k j g).toModularForm' = heckeT_n k j g.toModularForm' from H m hm0 f
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj0 g
    haveI := hj0
    rcases eq_or_ne j 1 with rfl | hj1
    · rw [heckeEnd_aux, dif_pos le_rfl, heckeT_n_one]
      rfl
    · have hj : 1 < j := by have := NeZero.ne j; omega
      set p := j.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := j.factorization p with hv_def
      have hv_pos : 0 < v := hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd j)
      have hdiv_pos : 0 < j / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j p)) (pow_pos hp.pos v)
      haveI : NeZero (j / p ^ v) := ⟨hdiv_pos.ne'⟩
      have hdiv_lt : j / p ^ v < j :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
      have hp_quot : ¬ p ∣ j / p ^ v :=
        hv_def ▸ Nat.not_dvd_ordCompl hp (NeZero.ne j)
      -- Reversed cusp peel: `heckeEnd_aux j g = heckeEnd_aux (j/p^v) (heckeEndPpow v g)`.
      have hpeel : (heckeEnd_aux N k j g).toModularForm'
          = (heckeEnd_aux N k (j / p ^ v) (heckeEndPpow N k p hp v g)).toModularForm' := by
        rw [heckeEnd_aux, dif_neg (not_le.mpr hj)]; rfl
      rw [hpeel, ih _ hdiv_lt ⟨hdiv_pos.ne'⟩, heckeEndPpow_toModularForm' hk hp v g]
      -- Forward modular-form peel: `T_j = T_{p^v} * T_{j/p^v}`, then swap.
      rw [heckeT_n_unfold k j hj]
      simp only [Module.End.mul_apply]
      exact LinearMap.congr_fun
        (commute_heckeT_ppow_heckeT_n hp v (j / p ^ v) hp_quot).symm g.toModularForm'

/-- **Reconciliation of the genuine Hecke operator with the reversed-order mirror (pure algebra).**
The genuine cusp Hecke operator `heckeEnd N k n` (= `heckeT_n_cusp k n`, built by the *non-reversed*
analytic recursion `heckeT_n`) agrees, on every cusp form, with the reversed-order mirror
`heckeEnd_aux N k n.val`.  The two recursions differ only in the order of the (commuting) Hecke
factors, so this is the analytic commutativity of `T_n` (`heckeT_n_comm` / the Petersson
`heckeT_n_cusp_comm`) transported to the mirror; it contains no change-of-variables
content.  Isolated
here as the pure-algebra gap (it does not involve `periodMap'`). -/
theorem heckeEnd_apply_eq_heckeEnd_aux (hk : 2 ≤ k) (n : ℕ+)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeEnd N k n f = heckeEnd_aux N k n.val f := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  -- Two cusp forms are equal iff their underlying functions agree; both functions are the
  -- underlying `M_k`-operator `heckeT_n` applied to `f.toModularForm'` (`heckeEnd_aux` after the
  -- mirror reconciliation `heckeEnd_aux_toModularForm'`, `heckeEnd` by definition).
  refine CuspForm.ext fun z => ?_
  have h := heckeEnd_aux_toModularForm' (N := N) (k := k) hk n.val f ⟨n.pos.ne'⟩
  exact congrArg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k => m z) h.symm

/-- **Hecke equivariance of the period map (`k ≥ 2`).**  The period map intertwines the cusp Hecke
operator `heckeEnd N k n` with the integral modular-symbol Hecke operator `heckeSymb N k n`
(through the transpose `dualPrecomp`).  This is the hypothesis `hT` of the endgame.

The analytic `heckeEnd N k n` and the symbol `heckeSymb N k n` are assembled by the *same*
prime-power recurrence (`heckeT_ppow`/`heckeSymbPpow`) from the *same* Heilbronn coset
representatives, so — exactly as for the diamond operators (`periodMap'_diamond`, proven via the
det-`1` change of variables `rawPairing_fullModSymRep_sl`) — the equivariance reduces, through the
`PeriodEquiv` closure lemmas and the matched recursions (`periodEquiv_heckeEnd_aux`), to the
**per-coset determinant-`p` Heilbronn change of variables** `periodEquiv_heckeEnd_prime` (the lone
isolated analytic input), modulo the pure-algebra mirror reconciliation
`heckeEnd_apply_eq_heckeEnd_aux`. -/
theorem periodMap'_heckeEnd (hk : 2 ≤ k) (n : ℕ+)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    periodMap' N k hk (heckeEnd N k n f) =
      dualPrecomp (heckeSymb N k n.val) (periodMap' N k hk f) := by
  rw [heckeEnd_apply_eq_heckeEnd_aux hk n f]
  have := periodEquiv_heckeEnd_aux hk n.val f
  rwa [show heckeSymb N k n.val = heckeSymb_aux N k n.val from rfl]

end HeckeRing.GL2.ModularSymbols
