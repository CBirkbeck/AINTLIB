/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.GaussPoint

/-!
# The localized Robba-type ring `Bloc = A_inf[1/(p·[ϖ])]`

Kedlaya's rings `A_{L,E} = W(o_L)_E[[x] : x ∈ L]` and `B_{L,E} = A_{L,E}[1/ϖ_E]`
(*Noetherian properties of Fargues–Fontaine curves*, Definition 2.2) are, in the
campaign specialization `E = ℚ_p`, `L = F`, plain localizations of `A_inf = W(O_F)`:
every Teichmüller lift `[x]` with `x ∈ F` equals `[a]·([ϖ]^k)⁻¹` for `a = x·ϖ^k ∈ O_F`,
so `A_{L,E} = A_inf[1/[ϖ]]` and `B_{L,E} = A_inf[1/(p[ϖ])]` (architecture decision AD-1
of `decomposition-laneB.md`).

The Gauss-norm family `λ_t` of Kedlaya (2.2.1) — in the untwisted weight
parametrization `w_ρ`, `ρ = p^{-1/t}` — extends from `A_inf` to `Bloc` by
multiplicativity (`Valuation.extendToLocalization`, decision AD-2): this file
defines the extended family `wLoc ρ` and its evaluation lemmas.

## Main definitions

* `FarguesFontaine.Bloc` : the localization `A_inf[1/(p·[ϖ])]`.
* `FarguesFontaine.wLoc` : the extended Gauss valuation `w_ρ` on `Bloc`.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Definition 2.2, formula (2.2.1), Definition 2.4.
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **Kedlaya's `B_{L,E}`** in the campaign specialization: the localization
`A_inf[1/(p·[ϖ])]` (decision AD-1: adjoining `[x]` for all `x ∈ F` and inverting `ϖ_E = p`
is exactly inverting `p·[ϖ]`). -/
abbrev Bloc := Localization.Away ((p : Ainf p F) * teichPi p F ϖ)

/-- The powers of `p·[ϖ]` avoid the support of the Gauss valuation. -/
theorem gaussVal_powers_le_primeCompl {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)
      ≤ (gaussVal p F hρ0 hρ1).supp.primeCompl := by
  rintro x ⟨k, rfl⟩
  intro hx
  simp only [SetLike.mem_coe, Valuation.mem_supp_iff, map_pow] at hx
  exact absurd hx
    (pow_ne_zero k (gaussValue_p_teichPi_ne_zero p F ϖ hρ0 hρ1))

/-- **The extended Gauss valuation** `w_ρ` on `Bloc` (Kedlaya (2.2.1) on `B_{L,E}`,
via the unique multiplicative extension to the localization, decision AD-2). -/
def wLoc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (Bloc p F ϖ) NNReal :=
  (gaussVal p F hρ0 hρ1).extendToLocalization
    (gaussVal_powers_le_primeCompl p F ϖ hρ0 hρ1) _

/-- `w_ρ` restricts to the Gauss value on `A_inf`. -/
@[simp]
theorem wLoc_algebraMap {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) :
    wLoc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) x)
      = gaussValue p F ρ x :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

/-- Evaluation on localization fractions. -/
theorem wLoc_mk' {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F)
    (y : Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) :
    wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ) x y)
      = gaussValue p F ρ x * (gaussValue p F ρ (y : Ainf p F))⁻¹ :=
  Valuation.extendToLocalization_mk' (gaussVal p F hρ0 hρ1)
    (gaussVal_powers_le_primeCompl p F ϖ hρ0 hρ1) (Bloc p F ϖ) x y

/-- The Gauss value of `p·[ϖ]` (the inverted element): `ρ·|ϖ|`. -/
theorem gaussValue_p_teichPi {ρ : NNReal} (hρ1 : ρ < 1) :
    gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ)
      = ρ * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
  rw [gaussValue_p_mul p F hρ1.le, teichPi, gaussValue_teichmuller p F hρ1.le]

/-- The image of `p·[ϖ]` is a unit of `Bloc`. -/
theorem isUnit_p_teichPi_image :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F) * teichPi p F ϖ)) :=
  IsLocalization.map_units _ (⟨_, Submonoid.mem_powers _⟩ :
    Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))

/-- The image of `[ϖ]` is a unit of `Bloc` (it divides the inverted element). -/
theorem isUnit_teichPi_image :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)) := by
  refine isUnit_of_mul_isUnit_left (y := algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)) ?_
  rw [← map_mul]
  have h : teichPi p F ϖ * (p : Ainf p F) = (p : Ainf p F) * teichPi p F ϖ := mul_comm _ _
  rw [h]
  exact isUnit_p_teichPi_image p F ϖ

/-- The image of `p` is a unit of `Bloc`. -/
theorem isUnit_p_image :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)) := by
  refine isUnit_of_mul_isUnit_left (y := algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ)) ?_
  rw [← map_mul]
  exact isUnit_p_teichPi_image p F ϖ

/-- Values of `w_ρ` on inverses of units: `w(u⁻¹) = w(u)⁻¹`. -/
theorem wLoc_units_inv {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : (Bloc p F ϖ)ˣ) :
    wLoc p F ϖ hρ0 hρ1 ↑u⁻¹ = (wLoc p F ϖ hρ0 hρ1 u)⁻¹ := by
  have h : wLoc p F ϖ hρ0 hρ1 ↑u * wLoc p F ϖ hρ0 hρ1 ↑u⁻¹ = 1 := by
    rw [← Valuation.map_mul, Units.mul_inv, Valuation.map_one]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- `w_ρ` of the inverse of (the image of) `p`: `ρ⁻¹`. -/
theorem wLoc_p_inv {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    wLoc p F ϖ hρ0 hρ1 ↑(isUnit_p_image p F ϖ).unit⁻¹ = ρ⁻¹ := by
  rw [wLoc_units_inv, IsUnit.unit_spec, wLoc_algebraMap]
  congr 1
  have h1 : (p : Ainf p F) * 1 = (p : Ainf p F) := mul_one _
  calc gaussValue p F ρ (p : Ainf p F)
      = gaussValue p F ρ ((p : Ainf p F) * 1) := by rw [mul_one]
    _ = ρ * gaussValue p F ρ 1 := gaussValue_p_mul p F hρ1.le 1
    _ = ρ := by rw [gaussValue_one p F hρ1.le, mul_one]

/-- `w_ρ` of the inverse of (the image of) `[ϖ]`: `|ϖ|⁻¹`. -/
theorem wLoc_teichPi_inv {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    wLoc p F ϖ hρ0 hρ1 ↑(isUnit_teichPi_image p F ϖ).unit⁻¹
      = (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹ := by
  rw [wLoc_units_inv, IsUnit.unit_spec, wLoc_algebraMap, teichPi,
    gaussValue_teichmuller p F hρ1.le]

end FarguesFontaine

end
