/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.Presentation
import «Adic spaces».FarguesFontaine.ChartVObj

open TopologicalRing ValuationSpectrum WittVector NNReal

/-!
# T908(c): the coordinate realization of `B^I` — the `Bloc` layer

The `ℤ`-indexed Teichmüller coordinates of `Bloc = A_inf[1/(p[ϖ])]`
(Kedlaya Def 4.2's two-sided expansions, dense layer): `blocCoeffF` via a
chosen `mk'`-representation, the representation independence
(`blocCoeffF_mk'`), and the per-term Gauss bound
(`zpow_mul_valuation_blocCoeffF_le`). The completion layer (coordinates on
`B^r`/`B^I` by approximant limits) builds on this file.
-/


set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The inverted element `p·[ϖ]` is nonzero. -/
theorem p_teichPi_ne_zero : (p : Ainf p F) * teichPi p F ϖ ≠ 0 := by
  intro h0
  refine gaussValue_p_teichPi_ne_zero p F ϖ (ρ := 1 / 2) (by norm_num)
    (by norm_num) ?_
  rw [h0]
  exact map_zero (gaussVal p F (by norm_num) (by norm_num))

/-- Every element of `Bloc` has an `mk'`-representation with an explicit
`sPow`-denominator. -/
theorem exists_mk'_sPow (u : Bloc p F ϖ) :
    ∃ ak : (Ainf p F) × ℕ,
      u = IsLocalization.mk' (Bloc p F ϖ) ak.1 (sPow p F ϖ ak.2) := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) u
  obtain ⟨k, hk⟩ := s.2
  refine ⟨(a, k), ?_⟩
  have hseq : sPow p F ϖ k = s := Subtype.ext hk
  rw [hseq]
  exact (IsLocalization.eq_mk'_iff_mul_eq.mpr hs)

/-- The chosen `mk'`-representation of a `Bloc`-element. -/
noncomputable def blocRep (u : Bloc p F ϖ) : (Ainf p F) × ℕ :=
  (exists_mk'_sPow p F ϖ u).choose

theorem blocRep_spec (u : Bloc p F ϖ) :
    u = IsLocalization.mk' (Bloc p F ϖ) (blocRep p F ϖ u).1
      (sPow p F ϖ (blocRep p F ϖ u).2) :=
  (exists_mk'_sPow p F ϖ u).choose_spec

/-- The localization map into `Bloc` is injective (the base is a domain and
the inverted element is nonzero). -/
theorem algebraMap_Bloc_injective :
    Function.Injective (algebraMap (Ainf p F) (Bloc p F ϖ)) :=
  IsLocalization.injective (Bloc p F ϖ)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (p_teichPi_ne_zero p F ϖ))

/-- The `W(F)`-image of `p·[ϖ]` is `p` times the Teichmüller lift of the
uniformizer. -/
theorem map_p_teichPi :
    WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        ((p : Ainf p F) * teichPi p F ϖ)
      = (p : WittVector p F) * WittVector.teichmuller p
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
  rw [map_mul, map_natCast, teichPi, WittVector.map_teichmuller]
  rfl

/-- Iterated `p`-shift of `W(F)`-coordinates. -/
theorem teichCoeffF_p_pow_mul (x : WittVector p F) (k j : ℕ) :
    teichCoeffF p F ((p : WittVector p F) ^ k * x) (j + k)
      = teichCoeffF p F x j := by
  induction k generalizing x j with
  | zero => simp
  | succ m ih =>
    have hsplit : (p : WittVector p F) ^ (m + 1) * x
        = (p : WittVector p F) ^ m * ((p : WittVector p F) * x) := by ring
    rw [hsplit, show j + (m + 1) = (j + 1) + m by omega,
      ih ((p : WittVector p F) * x) (j + 1), teichCoeffF_p_mul]

/-- Below the shift, iterated `p`-multiples have vanishing coordinates. -/
theorem teichCoeffF_p_pow_mul_zero (x : WittVector p F) {k j : ℕ}
    (hj : j < k) : teichCoeffF p F ((p : WittVector p F) ^ k * x) j = 0 := by
  induction k generalizing x j with
  | zero => omega
  | succ m ih =>
    have hsplit : (p : WittVector p F) ^ (m + 1) * x
        = (p : WittVector p F) * ((p : WittVector p F) ^ m * x) := by ring
    rw [hsplit]
    match j with
    | 0 => exact teichCoeffF_p_mul_zero p F _
    | j' + 1 =>
      rw [teichCoeffF_p_mul]
      exact ih _ (by omega)

/-- **The combined shift-and-scale**: `W(F)`-coordinates of `(p[ϖ])^k·a` are
the `ϖ^k`-scaled, `k`-shifted coordinates of `a`. -/
theorem teichCoeffF_map_p_teichPi_pow_mul (a : Ainf p F) (k j : ℕ) :
    teichCoeffF p F (WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k * a)) (j + k)
      = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k
        * teichCoeffF p F (WittVector.map
            ((powerBoundedSubring.toSubring F).subtype) a) j := by
  rw [map_mul, map_pow, map_p_teichPi p F ϖ, mul_pow, mul_assoc,
    teichCoeffF_p_pow_mul,
    ← map_pow (WittVector.teichmuller p
      (R := F)) ((PseudoUniformizer.toOF F ϖ : OF F) : F) k,
    teichCoeffF_teichmuller_mul]

/-- Below the shift, the coordinates of `(p[ϖ])^k·a` vanish. -/
theorem teichCoeffF_map_p_teichPi_pow_mul_zero (a : Ainf p F) {k j : ℕ}
    (hj : j < k) :
    teichCoeffF p F (WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        (((p : Ainf p F) * teichPi p F ϖ) ^ k * a)) j = 0 := by
  rw [map_mul, map_pow, map_p_teichPi p F ϖ, mul_pow, mul_assoc]
  exact teichCoeffF_p_pow_mul_zero p F _ hj

/-- The representation-level coordinate formula. -/
noncomputable def repCoeff (a : Ainf p F) (k : ℕ) (n : ℤ) : F :=
  if 0 ≤ n + (k : ℤ) then
    (((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹ ^ k
      * teichCoeffF p F (WittVector.map
          ((powerBoundedSubring.toSubring F).subtype) a) (n + k).toNat
  else 0

/-- **The `ℤ`-indexed Teichmüller coordinates on `Bloc`** (T908(c1)): for
`u = a/(p[ϖ])^k` the `n`-th coordinate is `ϖ^{-k}·(the (n+k)-th coordinate
of a)`, vanishing for `n < -k`. Defined via the chosen representation; the
representation independence is `blocCoeffF_mk'`. -/
noncomputable def blocCoeffF (u : Bloc p F ϖ) (n : ℤ) : F :=
  repCoeff p F ϖ (blocRep p F ϖ u).1 (blocRep p F ϖ u).2 n

/-- The cross-representation coordinate comparison at the `Ainf` level. -/
theorem teichCoeffF_map_eq_of_cross {a a' : Ainf p F} {k k' : ℕ}
    (hcross : ((p : Ainf p F) * teichPi p F ϖ) ^ k' * a
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k * a') {j j' : ℕ}
    (hjj' : j + k' = j' + k) :
    ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k'
        * teichCoeffF p F (WittVector.map
            ((powerBoundedSubring.toSubring F).subtype) a) j
      = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k
        * teichCoeffF p F (WittVector.map
            ((powerBoundedSubring.toSubring F).subtype) a') j' := by
  have h1 := teichCoeffF_map_p_teichPi_pow_mul p F ϖ a k' j
  have h2 := teichCoeffF_map_p_teichPi_pow_mul p F ϖ a' k j'
  rw [← h1, ← h2, hcross, show j + k' = j' + k from hjj']

/-- The below-shift vanishing, cross-representation form. -/
theorem teichCoeffF_map_eq_zero_of_cross {a a' : Ainf p F} {k k' : ℕ}
    (hcross : ((p : Ainf p F) * teichPi p F ϖ) ^ k' * a
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k * a') {j : ℕ}
    (hjk : j + k' < k) :
    teichCoeffF p F (WittVector.map
        ((powerBoundedSubring.toSubring F).subtype) a) j = 0 := by
  have h1 := teichCoeffF_map_p_teichPi_pow_mul p F ϖ a k' j
  have h2 := teichCoeffF_map_p_teichPi_pow_mul_zero p F ϖ a'
    (k := k) (j := j + k') hjk
  rw [hcross] at h1
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have := h1.symm.trans h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (pow_ne_zero _ hϖne)
  · exact h

/-- **Cross-representation invariance of the coordinate formula** (small
context: pure Witt-vector computation). -/
theorem repCoeff_eq_of_cross {a a' : Ainf p F} {k k' : ℕ}
    (hcross : ((p : Ainf p F) * teichPi p F ϖ) ^ k' * a
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k * a') (n : ℤ) :
    repCoeff p F ϖ a k n = repCoeff p F ϖ a' k' n := by
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  rw [repCoeff, repCoeff]
  by_cases hnk : 0 ≤ n + (k : ℤ)
  · by_cases hnk' : 0 ≤ n + (k' : ℤ)
    · rw [if_pos hnk, if_pos hnk']
      have hjj' : (n + k).toNat + k' = (n + k').toNat + k := by omega
      have hc := teichCoeffF_map_eq_of_cross p F ϖ hcross
        (j := (n + k).toNat) (j' := (n + k').toNat) hjj'
      set Ca := teichCoeffF p F (WittVector.map
        ((powerBoundedSubring.toSubring F).subtype) a) (n + k).toNat with hCa
      set Ca' := teichCoeffF p F (WittVector.map
        ((powerBoundedSubring.toSubring F).subtype) a') (n + k').toNat with hCa'
      set w := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hw
      refine mul_left_cancel₀ (pow_ne_zero (k + k') hϖne) ?_
      have hl : w ^ (k + k') * (w⁻¹ ^ k * Ca) = w ^ k' * Ca := by
        calc w ^ (k + k') * (w⁻¹ ^ k * Ca)
            = (w ^ k * w⁻¹ ^ k) * (w ^ k' * Ca) := by rw [pow_add]; ring
          _ = w ^ k' * Ca := by
              rw [← mul_pow, mul_inv_cancel₀ hϖne, one_pow, one_mul]
      have hr : w ^ (k + k') * (w⁻¹ ^ k' * Ca') = w ^ k * Ca' := by
        calc w ^ (k + k') * (w⁻¹ ^ k' * Ca')
            = (w ^ k' * w⁻¹ ^ k') * (w ^ k * Ca') := by rw [pow_add]; ring
          _ = w ^ k * Ca' := by
              rw [← mul_pow, mul_inv_cancel₀ hϖne, one_pow, one_mul]
      exact hl.trans (hc.trans hr.symm)
    · rw [if_pos hnk, if_neg hnk']
      have hz := teichCoeffF_map_eq_zero_of_cross p F ϖ hcross
        (j := (n + k).toNat) (by omega)
      rw [hz, mul_zero]
  · by_cases hnk' : 0 ≤ n + (k' : ℤ)
    · rw [if_neg hnk, if_pos hnk']
      have hz := teichCoeffF_map_eq_zero_of_cross p F ϖ hcross.symm
        (j := (n + k').toNat) (by omega)
      rw [hz, mul_zero]
    · rw [if_neg hnk, if_neg hnk']

/-- The chosen representation of an explicit `mk'` clears against it. -/
theorem blocRep_cross (a : Ainf p F) (k : ℕ) :
    ((p : Ainf p F) * teichPi p F ϖ)
        ^ (blocRep p F ϖ (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k))).2
        * a
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k
        * (blocRep p F ϖ
            (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k))).1 := by
  have hmk : IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k)
      = IsLocalization.mk' (Bloc p F ϖ)
        (blocRep p F ϖ (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k))).1
        (sPow p F ϖ (blocRep p F ϖ
          (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k))).2) :=
    blocRep_spec p F ϖ _
  have halg := (IsLocalization.mk'_eq_iff_eq
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))).mp hmk
  exact algebraMap_Bloc_injective p F ϖ halg

/-- **Representation independence** (the T908(c1) workhorse): any
`mk'(a, (p[ϖ])^k)`-representation computes the coordinates. -/
theorem blocCoeffF_mk' (a : Ainf p F) (k : ℕ) (n : ℤ) :
    blocCoeffF p F ϖ (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k)) n
      = repCoeff p F ϖ a k n :=
  (repCoeff_eq_of_cross p F ϖ (blocRep_cross p F ϖ a k) n).symm

/-- The valuation of the uniformizer image, abbreviated. -/
theorem valuation_repCoeff (a : Ainf p F) (k : ℕ) (n : ℤ) (h : 0 ≤ n + (k : ℤ)) :
    perfectoidValuation p F (repCoeff p F ϖ a k n)
      = (perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹ ^ k
        * perfectoidValuation p F
            ((teichCoeff p F a (n + k).toNat : OF F) : F) := by
  rw [repCoeff, if_pos h, map_mul, map_pow, map_inv₀,
    teichCoeffF_map p F a (n + k).toNat]

/-- **The per-term Gauss bound on the `mk'`-layer** (T908(c2) core):
`ρ^n·|coeff_n| ≤ wLoc` for localization fractions. -/
theorem zpow_mul_valuation_repCoeff_le {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a : Ainf p F) (k : ℕ) (n : ℤ) :
    ρ ^ n * perfectoidValuation p F (repCoeff p F ϖ a k n)
      ≤ wLoc p F ϖ hρ0 hρ1
          (IsLocalization.mk' (Bloc p F ϖ) a (sPow p F ϖ k)) := by
  by_cases h : 0 ≤ n + (k : ℤ)
  · rw [valuation_repCoeff p F ϖ a k n h,
      wLoc_mk' p F ϖ hρ0 hρ1 a (sPow p F ϖ k)]
    set c : NNReal := perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hc
    have hsden : gaussValue p F ρ ((sPow p F ϖ k : Ainf p F)) = (ρ * c) ^ k := by
      have h1 : gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
          = (gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ)) ^ k :=
        map_pow (gaussVal p F hρ0 hρ1) _ k
      calc gaussValue p F ρ ((sPow p F ϖ k : Ainf p F))
          = gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ k) := rfl
        _ = (gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ)) ^ k := h1
        _ = (ρ * c) ^ k := by rw [gaussValue_p_teichPi p F ϖ hρ1]
    rw [hsden]
    have hρn : (ρ : NNReal) ^ n = ρ ^ ((n + k).toNat) * (ρ ^ k)⁻¹ := by
      have h1 : ρ ^ ((n + k).toNat) * (ρ ^ k)⁻¹
          = ρ ^ (((n + k).toNat : ℤ)) * (ρ ^ ((k : ℕ) : ℤ))⁻¹ := by
        rw [zpow_natCast, zpow_natCast]
      rw [h1, ← div_eq_mul_inv, ← zpow_sub₀ hρ0.ne']
      congr 1
      omega
    rw [hρn]
    calc ρ ^ ((n + k).toNat) * (ρ ^ k)⁻¹ * (c⁻¹ ^ k
          * perfectoidValuation p F ((teichCoeff p F a (n + k).toNat : OF F) : F))
        = (ρ ^ ((n + k).toNat)
            * perfectoidValuation p F
                ((teichCoeff p F a (n + k).toNat : OF F) : F))
          * ((ρ ^ k)⁻¹ * c⁻¹ ^ k) := by ring
      _ = gaussTerm p F ρ a (n + k).toNat * ((ρ * c) ^ k)⁻¹ := by
          rw [gaussTerm, mul_pow, mul_inv, inv_pow]
      _ ≤ gaussValue p F ρ a * ((ρ * c) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (gaussTerm_le_gaussValue p F hρ1.le a _) zero_le
  · rw [repCoeff, if_neg h, map_zero, mul_zero]
    exact zero_le

/-- **The per-term Gauss bound** (T908(c2)): every `ℤ`-indexed coordinate of
a `Bloc`-element obeys `ρ^n·|coeff_n(u)| ≤ wLoc ρ u`. -/
theorem zpow_mul_valuation_blocCoeffF_le {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (u : Bloc p F ϖ) (n : ℤ) :
    ρ ^ n * perfectoidValuation p F (blocCoeffF p F ϖ u n)
      ≤ wLoc p F ϖ hρ0 hρ1 u := by
  have hspec := blocRep_spec p F ϖ u
  calc ρ ^ n * perfectoidValuation p F (blocCoeffF p F ϖ u n)
      = ρ ^ n * perfectoidValuation p F
          (repCoeff p F ϖ (blocRep p F ϖ u).1 (blocRep p F ϖ u).2 n) := rfl
    _ ≤ wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ)
          (blocRep p F ϖ u).1 (sPow p F ϖ (blocRep p F ϖ u).2)) :=
        zpow_mul_valuation_repCoeff_le p F ϖ hρ0 hρ1 _ _ n
    _ = wLoc p F ϖ hρ0 hρ1 u := by rw [← hspec]

end FarguesFontaine

end
