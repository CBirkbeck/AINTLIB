/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import «Adic spaces».FarguesFontaine.RobbaPresentation

/-!
# The plus-ring correspondence: integrality over the image ball

Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, Lemma 4.9,
the "moreover" clause (ticket T910-M, step M2b-3): every unit-ball
`Bloc`-element is **integral over the image ball**
`evalBallSubring` — the head/tail split at a Teichmüller depth `N`,
the two per-monomial routes (power-lift for `i ≤ k`, radius-monotone
constant route for `i > k`), and the small tail via `W`-scaled
surjectivity.
-/


open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ σ₁ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1}
  {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}

/-- The interval norm of a `Bloc`-image is the max of the endpoint local
valuations. -/
theorem wI_blocToBI_eq (w : Bloc p F ϖ) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 w
          : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
          : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = max (wLoc p F ϖ hρ₁0 hρ₁1 w) (wLoc p F ϖ hρ₂0 hρ₂1 w) := by
  rw [show ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 w
      : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
    = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 w from rfl]
  rw [wI_BIProd p F, valued_BlocToHatK, valued_BlocToHatK]

/-- Assembly at abstract base: a sum-plus-tail decomposition with integral
heads and integral tail is integral. -/
private theorem isIntegral_split_assembly {A : Type*} [CommRing A]
    (S : Subring A) {α : Type*} (s : Finset α) (f : α → A)
    (t z : A) (hz : z = (∑ i ∈ s, f i) + t)
    (hf : ∀ i ∈ s, IsIntegral ↥S (f i)) (ht : t ∈ S) :
    IsIntegral ↥S z := by
  rw [hz]
  exact (IsIntegral.sum f hf).add (isIntegral_algebraMap (x := (⟨t, ht⟩ : ↥S)))

section Master

variable (φ : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
  →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
variable (hφ : ∀ z, wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1
    ((φ z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
      : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
variable (hφb : ∀ x : Bloc p F ϖ,
  ((φ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x)
    : ↥(BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1))
    : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1))
  = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1 x)

set_option maxSynthPendingDepth 1 in
include hφb in
/-- **Every unit-ball `Bloc`-element is integral over the image ball**
(T910-M M2b-3, the master): head/tail split, the two monomial routes, and
the small tail. -/
theorem isIntegral_blocToBI_of_wLoc_le_one
    (hρσ : ρ₁ ≤ σ₁) (hσρ : σ₁ ≤ ρ₂)
    (zb : OF F) (m : ℕ) (hm : 0 < m)
    (hgen : perfectoidValuation p F (zb : F) = σ₁ ^ m)
    {b : (hatK p F hσ₁0 hσ₁1) × (hatK p F hρ₂0 hρ₂1)}
    (hbmem : b ∈ BISub p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hσ₁0 hσ₁1 hρ₂0 hρ₂1 b ≤ 1)
    (hbg : b = BIProd p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (teichPowGen p F ϖ zb m))
    (x : Ainf p F) (k : ℕ)
    (hw1 : wLoc p F ϖ hσ₁0 hσ₁1
      (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)) ≤ 1)
    (hw2 : wLoc p F ϖ hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)) ≤ 1) :
    IsIntegral (↥(evalBallSubring p F ϖ φ hφ hbmem hb))
      (blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
        (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k))) := by
  classical
  set V : NNReal := perfectoidValuation p F
    ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hV
  have hV0 : 0 < V := vpi_pos p F ϖ
  set Kinv : NNReal := ρ₁ ^ m * ((σ₁ ^ m)⁻¹) with hKinv
  have hKinv0 : 0 < Kinv :=
    mul_pos (pow_pos hρ₁0 m) (inv_pos.mpr (pow_pos hσ₁0 m))
  have hD1 : (0 : NNReal) < Kinv * ((σ₁ * V) ^ k) :=
    mul_pos hKinv0 (pow_pos (mul_pos hσ₁0 hV0) k)
  have hD2 : (0 : NNReal) < Kinv * ((ρ₂ * V) ^ k) :=
    mul_pos hKinv0 (pow_pos (mul_pos hρ₂0 hV0) k)
  obtain ⟨N₁, hN₁⟩ := NNReal.exists_pow_lt_of_lt_one hD1 hσ₁1
  obtain ⟨N₂, hN₂⟩ := NNReal.exists_pow_lt_of_lt_one hD2 hρ₂1
  set N := max N₁ N₂ with hN
  obtain ⟨w', hwd⟩ :=
    WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  have hsplit := mk'_sPow_split p F ϖ x k N w' hwd
  -- the tail is Kinv-small at both σ-radii
  have htail1 : wLoc p F ϖ hσ₁0 hσ₁1 (IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)) ≤ Kinv := by
    refine le_trans (wLoc_mk'_tail_le p F ϖ hσ₁0 hσ₁1 k N w') ?_
    have hle : σ₁ ^ (N + 1) ≤ σ₁ ^ (N₁ + 1) :=
      pow_le_pow_of_le_one zero_le hσ₁1.le (by omega)
    have hlt : σ₁ ^ (N₁ + 1) ≤ Kinv * ((σ₁ * V) ^ k) :=
      le_trans (pow_le_pow_of_le_one zero_le hσ₁1.le
        (Nat.le_succ N₁)) hN₁.le
    calc σ₁ ^ (N + 1) * (((σ₁ * V) ^ k)⁻¹)
        ≤ Kinv * ((σ₁ * V) ^ k) * (((σ₁ * V) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_trans hle hlt) zero_le
      _ = Kinv := by
          rw [mul_assoc, mul_inv_cancel₀
            (pow_pos (mul_pos hσ₁0 hV0) k).ne', mul_one]
  have htail2 : wLoc p F ϖ hρ₂0 hρ₂1 (IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)) ≤ Kinv := by
    refine le_trans (wLoc_mk'_tail_le p F ϖ hρ₂0 hρ₂1 k N w') ?_
    have hle : ρ₂ ^ (N + 1) ≤ ρ₂ ^ (N₂ + 1) :=
      pow_le_pow_of_le_one zero_le hρ₂1.le (by omega)
    have hlt : ρ₂ ^ (N₂ + 1) ≤ Kinv * ((ρ₂ * V) ^ k) :=
      le_trans (pow_le_pow_of_le_one zero_le hρ₂1.le
        (Nat.le_succ N₂)) hN₂.le
    calc ρ₂ ^ (N + 1) * (((ρ₂ * V) ^ k)⁻¹)
        ≤ Kinv * ((ρ₂ * V) ^ k) * (((ρ₂ * V) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_trans hle hlt) zero_le
      _ = Kinv := by
          rw [mul_assoc, mul_inv_cancel₀
            (pow_pos (mul_pos hρ₂0 hV0) k).ne', mul_one]
  -- the tail lies in the image ball
  have htailmem : blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k))
      ∈ evalBallSubring p F ϖ φ hφ hbmem hb := by
    obtain ⟨U, hUeq, hUnorm⟩ := exists_evalBI_eq_of_le_inv p F ϖ φ hφ hφb
      hρσ hσρ zb m hm hgen hbmem hb hbg
      (BIProd_mem_BISub p F ϖ (IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)))
      (by
        rw [wI_BIProd p F, valued_BlocToHatK, valued_BlocToHatK]
        exact max_le htail1 htail2)
    exact ⟨U, hUnorm, Subtype.ext hUeq⟩
  -- per-head integrality
  have hhead : ∀ i ∈ Finset.Iic N,
      IsIntegral (↥(evalBallSubring p F ϖ φ hφ hbmem hb))
        (blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i
              * WittVector.teichmuller p (teichCoeff p F x i))
            (sPow p F ϖ k))) := by
    intro i _
    by_cases hik : i ≤ k
    · exact isIntegral_monomial_of_le_one p F ϖ φ hφ hφb zb m hm hgen
        hbmem hb hbg i k hik (teichCoeff p F x i)
        (wLoc_mk'_monomial_le_one p F ϖ hσ₁0 hσ₁1 x k hw1 i)
    · refine isIntegral_of_pow_mem _ _ 1 one_pos ?_
      rw [pow_one]
      refine blocToBI_mem_evalBallSubring_of_wI_le p F ϖ φ hφ hφb
        hbmem hb _ ?_
      rw [wI_blocToBI_eq p F ϖ]
      refine max_le ?_ ?_
      · refine le_trans (wLoc_mk'_monomial_mono_of_le p F ϖ hρ₁0 hρ₁1
          hσ₁0 hσ₁1 hρσ i k (by omega) (teichCoeff p F x i)) ?_
        exact wLoc_mk'_monomial_le_one p F ϖ hσ₁0 hσ₁1 x k hw1 i
      · exact wLoc_mk'_monomial_le_one p F ϖ hρ₂0 hρ₂1 x k hw2 i
  -- assemble through the split
  have himg : blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k))
      = (∑ i ∈ Finset.Iic N, blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i
              * WittVector.teichmuller p (teichCoeff p F x i))
            (sPow p F ϖ k)))
        + blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (IsLocalization.mk' (Bloc p F ϖ)
              ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)) :=
    (congrArg (blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1) hsplit).trans
      ((map_add (blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1) _ _).trans
        (congrArg (· + blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1
            (IsLocalization.mk' (Bloc p F ϖ)
              ((p : Ainf p F) ^ (N + 1) * w') (sPow p F ϖ k)))
          (map_sum (blocToBI p F ϖ hσ₁0 hσ₁1 hρ₂0 hρ₂1) _ _)))
  exact isIntegral_split_assembly _ (Finset.Iic N) _ _ _ himg hhead htailmem

end Master

end FarguesFontaine

end
