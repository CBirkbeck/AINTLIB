module

public import BernoulliRegular.LValueAtOne.Cosine

/-!
# Even-character `L(1, χ)` formulas

This file packages the even `L(1, χ)` evaluation from the cosine-side
boundary-value identities.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T022a**: For an even Dirichlet character `χ` modulo `p`, `L(1, χ)`
equals `(1/p) · ∑ a, χ(a) · hurwitzZetaEven (toAddCircle a) 1`. This is the
target statement that the subsequent T022b–T022e tickets will simplify to
the logarithmic cyclotomic-unit form. -/
theorem even_LFunction_one_eq_p_inv_mul_sum_hurwitzZetaEven
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) :
    DirichletCharacter.LFunction χ 1 =
      ((p : ℂ)⁻¹) *
        ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 := by
  rw [DirichletCharacter.LFunction, ZMod.LFunction_def_even hχ_even.to_fun]
  rw [show ((p : ℂ) ^ (-1 : ℂ)) = (p : ℂ)⁻¹ from Complex.cpow_neg_one _]

/-- **T022b**: rewrite the even-character special value as a sum over the
nonzero residues only. -/
theorem even_LFunction_one_sum_over_nonzero
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) :
    DirichletCharacter.LFunction χ 1 =
      ((p : ℂ)⁻¹) *
        (Finset.univ.erase (0 : ZMod p)).sum fun a =>
          χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχ_zero : χ 0 = 0 := χ.map_zero' hp_ne_one
  calc
    DirichletCharacter.LFunction χ 1
        = ((p : ℂ)⁻¹) *
            ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 :=
          even_LFunction_one_eq_p_inv_mul_sum_hurwitzZetaEven (p := p) hχ_even
    _ = ((p : ℂ)⁻¹) *
          (Finset.univ.erase (0 : ZMod p)).sum fun a =>
            χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 := by
          refine congrArg (fun z : ℂ => ((p : ℂ)⁻¹) * z) ?_
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
          simp [hχ_zero]

/-- **T022b**: subtracting an `a`-independent constant from each nonzero
summand does not change the even-character special-value formula for a
nontrivial character. -/
theorem even_LFunction_one_sub_const
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) (hχ_ne_one : χ ≠ 1) (C : ℂ) :
    DirichletCharacter.LFunction χ 1 =
      ((p : ℂ)⁻¹) *
        (Finset.univ.erase (0 : ZMod p)).sum fun a =>
          χ a * (HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 - C) := by
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχ_zero : χ 0 = 0 := χ.map_zero' hp_ne_one
  have hsum_zero : ∑ a : ZMod p, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ_ne_one
  have hsum_zero_erase : (Finset.univ.erase (0 : ZMod p)).sum χ = 0 := by
    rw [Finset.sum_erase _ hχ_zero]
    exact hsum_zero
  calc
    DirichletCharacter.LFunction χ 1
        = ((p : ℂ)⁻¹) *
            (Finset.univ.erase (0 : ZMod p)).sum fun a =>
              χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 :=
          even_LFunction_one_sum_over_nonzero (p := p) hχ_even
    _ = ((p : ℂ)⁻¹) *
          (Finset.univ.erase (0 : ZMod p)).sum fun a =>
            χ a * (HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 - C) := by
          refine congrArg (fun z : ℂ => ((p : ℂ)⁻¹) * z) ?_
          set s : Finset (ZMod p) := Finset.univ.erase (0 : ZMod p)
          set f : ZMod p → ℂ :=
            fun a => χ a * HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1
          set g : ZMod p → ℂ := fun a => χ a * C
          calc
            s.sum f = s.sum (fun a => f a - g a) := by
              have hconst : s.sum g = 0 := by
                calc
                  s.sum g = (s.sum χ) * C := by
                    simp [g, ← Finset.sum_mul]
                  _ = 0 := by
                    have hs : s.sum χ = 0 := by
                      simpa [s] using hsum_zero_erase
                    rw [hs, zero_mul]
              calc
                s.sum f = s.sum f - s.sum g := by rw [hconst, sub_zero]
                _ = s.sum (fun a => f a - g a) := by rw [Finset.sum_sub_distrib]
            _ = s.sum (fun a =>
                  χ a * (HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 - C)) := by
              refine Finset.sum_congr rfl fun a _ => by
                simp [f, g]
                ring
            _ = (Finset.univ.erase (0 : ZMod p)).sum fun a =>
                  χ a * (HurwitzZeta.hurwitzZetaEven (ZMod.toAddCircle a) 1 - C) := by
                    simp [s]

/-- **T022**: `L(1, χ)` for even primitive characters modulo `p`. -/
theorem even_LFunction_one_eq_evenLValueRhs
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_even : χ.Even)
    (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = evenLValueRhs p χ := by
  let _ := hχ_prim
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change ZMod.LFunction (fun a : ZMod p => χ a) 1 = evenLValueRhs p χ
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχinv_ne_one : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ_ne_one
    calc
      χ = χ⁻¹⁻¹ := (inv_inv χ).symm
      _ = 1 := by simp [h]
  have hχinv_even : (χ⁻¹).Even := by
    rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_even]
    simp
  have hχinv_prim : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    have hdiv : (χ⁻¹).conductor ∣ p := DirichletCharacter.conductor_dvd_level (χ⁻¹)
    rcases (Nat.dvd_prime hp.out).mp hdiv with hcond | hcond
    · exact (hχinv_ne_one <| (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hcond).elim
    · exact hcond
  have hχinv_zero : χ⁻¹ 0 = 0 := (χ⁻¹).map_zero' hp_ne_one
  let χinv : ZMod p → ℂ := fun a => χ⁻¹ a
  have hdft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := by
    simpa using
      (ZMod.LFunction_dft (Φ := χinv) (s := (1 : ℂ))
        (hs := Or.inl (by simpa [χinv] using hχinv_zero)))
  have hft :
      ZMod.dft χinv = fun a : ZMod p =>
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * χ a := by
    funext a
    simpa [χinv, hχ_even.to_fun a, mul_comm] using
      (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ⁻¹) hχinv_prim a)
  have hleft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1 := by
    rw [hft, ZMod.LFunction, ZMod.LFunction]
    calc
      (p : ℂ) ^ (-1 : ℂ) *
          ∑ a : ZMod p,
            (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * χ a) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1
          = (p : ℂ) ^ (-1 : ℂ) *
              (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) *
                ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1 := by
            rw [ZMod.LFunction]
            ring
  have hsum_sin_zero :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 = 0 := by
    refine (hχinv_even.to_fun.mul_odd fun a => ?_).sum_eq_zero
    simpa using HurwitzZeta.sinZeta_neg (ZMod.toAddCircle a) (1 : ℂ)
  have hsum_isin_zero :
      ∑ a : ZMod p, χ⁻¹ a *
          (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) = 0 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)
          = Complex.I *
              ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = 0 := by rw [hsum_sin_zero, mul_zero]
  have hsum_exp :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1
          = ∑ a : ZMod p,
              (χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
                χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  have hneg : ZMod.toAddCircle (-a) = -ZMod.toAddCircle a :=
                    map_neg ZMod.toAddCircle a
                  rw [hneg, HurwitzZeta.expZeta, HurwitzZeta.cosZeta_neg,
                    HurwitzZeta.sinZeta_neg]
                  ring
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
            ∑ a : ZMod p,
              χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
            rw [hsum_isin_zero, sub_zero]
  have hboundary :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
        -evenLValueLogSum p χ := by
    unfold evenLValueLogSum
    calc
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1
          = ∑ a : ZMod p,
              -(χ⁻¹ a *
                ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  rcases eq_or_ne a 0 with rfl | ha
                  · simp [hχinv_zero]
                  · rw [cosZeta_toAddCircle_one_eq_boundary (p := p) ha]
                    have hlog :
                        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
                          ((Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ) := by
                      congr 1
                      rw [norm_one_sub_stdAddChar (p := p) ha]
                    rw [hlog]
                    rw [show
                      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) =
                        -(((Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) by simp]
                    exact mul_neg (χ⁻¹ a)
                      (((Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ))
      _ = -∑ a : ZMod p,
            χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) :=
              Finset.sum_neg_distrib
                (s := Finset.univ)
                (f := fun a : ZMod p =>
                  χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ))
      _ = -evenLValueLogSum p χ := by rfl
  have hcard_ne : (Fintype.card (ZMod p) : ℂ) ≠ 0 := by
    simpa [ZMod.card] using (show (p : ℂ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  have hgauss_ne : gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard_ne hχinv_ne_one (ZMod.isPrimitive_stdAddChar p)
  apply (mul_left_cancel₀ hgauss_ne)
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1
        = ZMod.LFunction (ZMod.dft χinv) 1 := hleft.symm
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := hdft
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := hsum_exp
    _ = -evenLValueLogSum p χ := hboundary
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * evenLValueRhs p χ := by
          simp [evenLValueRhs, hgauss_ne, mul_left_comm, mul_comm]

end LValueAtOne

end BernoulliRegular
