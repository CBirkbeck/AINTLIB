import BernoulliRegular.TotallyRealSubfield.ZetaPrime
import BernoulliRegular.TotallyRealSubfield.FixedAssociate
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.RealKummerLemma
import Mathlib.FieldTheory.KummerExtension
import FltRegular.NumberTheory.KummersLemma.Field

/-!
# AK-1: σ-anti radical from case-I Stage 2 data

For a case-I FLT solution at prime `p` with the integers `(a, b, c)`,
the **σ-anti radical** is the element

  α₀ := (a + ζb) / (a + ζ⁻¹b) ∈ K^×

where `ζ` is a fixed primitive `p`-th root of unity and `σ` is complex
conjugation. By construction `σ(α₀) = α₀⁻¹`, which is the key property
that makes the Kummer extension `K(α₀^{1/p})/K⁺` abelian (rather than
dihedral, as it would be for a *real* radical — see Reviewer guidance
2026-05-22 (Q1)).

This file is the entry-point for the AK chain replacing the
mathematically-incorrect RK chain (which assumed σ̃-fixed-subfield is
Galois cyclic over K⁺, but for odd `p` it is non-Galois).

## References

* [Diekmann23] §4.4 (anti-radical formulation; precise reference TBD).
* Reviewer guidance 2026-05-22 (Q1, σ-anti mechanism).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

namespace AntiKummer

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **σ-anti radical** `α₀ := (a + ζb)/(σ(a + ζb))` for case-I FLT data. -/
def antiRadical (a b : ℤ) (ζ : 𝓞 K) (_hab : ¬ (a = 0 ∧ b = 0)) : K :=
  algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) /
    NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)))

/-- **σ-anti property**: `σ(α₀) = α₀⁻¹` for the σ-anti radical
constructed from case-I FLT data. -/
theorem antiRadical_sigma_inv
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (_h_denom_nz : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0) :
    NumberField.IsCMField.complexConj K (antiRadical K a b ζ hab) =
      (antiRadical K a b ζ hab)⁻¹ := by
  unfold antiRadical
  rw [map_div₀]
  rw [NumberField.IsCMField.complexConj_apply_apply K]
  rw [inv_div]

/-- **The σ-anti Kummer extension** `L := K(α₀^{1/p})` for a σ-anti
element `α₀ ∈ K^×`. -/
abbrev antiKummerLift (α₀ : K) (_hα₀ : α₀ ≠ 0) : Type :=
  Polynomial.SplittingField (Polynomial.X ^ p - Polynomial.C α₀)

omit [IsCMField K] in
/-- **antiKummerLift has degree p over K** when `X^p - α₀` is irreducible. -/
theorem antiKummerLift_finrank_of_irreducible
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    Module.finrank K (antiKummerLift (p := p) K α₀ hα₀) = p := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hζ_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_nonempty : (primitiveRoots p K).Nonempty :=
    ⟨_, (mem_primitiveRoots hp_pos).mpr hζ_prim⟩
  exact finrank_of_isSplittingField_X_pow_sub_C
    (L := antiKummerLift (p := p) K α₀ hα₀) hζ_nonempty h_irr

omit [IsCMField K] in
/-- **`antiKummerLift α₀` is Galois over K** when `X^p - α₀` is irreducible. -/
theorem antiKummerLift_isGalois_of_irreducible
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    IsGalois K (antiKummerLift (p := p) K α₀ hα₀) := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hζ_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_nonempty : (primitiveRoots p K).Nonempty :=
    ⟨_, (mem_primitiveRoots hp_pos).mpr hζ_prim⟩
  exact isGalois_of_isSplittingField_X_pow_sub_C
    (L := antiKummerLift (p := p) K α₀ hα₀) hζ_nonempty h_irr

omit [IsCMField K] in
/-- **`antiKummerLift α₀` has cyclic Galois group over K** when
`X^p - α₀` is irreducible. -/
theorem antiKummerLift_isCyclic_of_irreducible
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    IsCyclic (antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[K]
      antiKummerLift (p := p) K α₀ hα₀) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hζ_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_nonempty : (primitiveRoots p K).Nonempty :=
    ⟨_, (mem_primitiveRoots hp_pos).mpr hζ_prim⟩
  exact isCyclic_of_isSplittingField_X_pow_sub_C
    (L := antiKummerLift (p := p) K α₀ hα₀) hζ_nonempty h_irr

/-- **σ-anti Kummer extension package**: an `L = K(α₀^{1/p})` equipped
with the σ̃ extension of complex conjugation. -/
structure SigmaAntiKummerExtension
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    where
  /-- The σ̃ extension: a K⁺-algebra automorphism of L extending
  complex conjugation. -/
  sigmaTilde : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[
      NumberField.maximalRealSubfield K]
    antiKummerLift (p := p) K α₀ hα₀
  /-- σ̃ has order 2 (involution). -/
  sigmaTilde_sq : sigmaTilde.trans sigmaTilde = AlgEquiv.refl
  /-- σ̃ restricts to complex conjugation on K. -/
  sigmaTilde_restricts_K : ∀ k : K,
    sigmaTilde (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (NumberField.IsCMField.complexConj K k)

/-- **The σ̃ K⁺-algebra HOMOMORPHISM** on L extending complex
conjugation, when L/K⁺ is Normal. -/
noncomputable def sigmaTildeHom
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    [Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)] :
    antiKummerLift (p := p) K α₀ hα₀ →ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
  (NumberField.IsCMField.complexConj K).toAlgHom.liftNormal _

/-- **The σ̃ AlgEquiv**: promotes `sigmaTildeHom` to an equivalence
via injectivity of any algebra hom of fields + finite-dimensional
codomain. -/
noncomputable def sigmaTildeEquiv
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    [FiniteDimensional (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)]
    [Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)] :
    antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ := by
  refine AlgEquiv.ofBijective (sigmaTildeHom (p := p) K α₀ hα₀) ⟨?_, ?_⟩
  ·
    exact RingHom.injective _
  ·
    have h_inj : Function.Injective (sigmaTildeHom (p := p) K α₀ hα₀) :=
      RingHom.injective _
    set f : antiKummerLift (p := p) K α₀ hα₀ →ₗ[NumberField.maximalRealSubfield K]
        antiKummerLift (p := p) K α₀ hα₀ :=
      (sigmaTildeHom (p := p) K α₀ hα₀).toLinearMap
    exact (LinearMap.injective_iff_surjective (f := f)).mp h_inj

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **σ̃ restricts to complex conjugation on K**: direct corollary of
`AlgHom.liftNormal_commutes`. -/
theorem sigmaTildeHom_restricts_K
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    [Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)]
    (k : K) :
    sigmaTildeHom (p := p) K α₀ hα₀
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (NumberField.IsCMField.complexConj K k) := by
  unfold sigmaTildeHom
  exact AlgHom.liftNormal_commutes (NumberField.IsCMField.complexConj K).toAlgHom _ k

/-- **`SigmaAntiKummerExtension` constructor from a chosen involutive
σ̃ candidate.** -/
noncomputable def SigmaAntiKummerExtension.mk_of_chosen
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (sT : antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[
        NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀)
    (h_sq : sT.trans sT = AlgEquiv.refl)
    (h_restricts : ∀ k : K,
      sT (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k) =
        algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
          (NumberField.IsCMField.complexConj K k)) :
    SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr where
  sigmaTilde := sT
  sigmaTilde_sq := h_sq
  sigmaTilde_restricts_K := h_restricts

/-- **The σ̃-fixed subfield of L**, as an `IntermediateField K⁺ L`. -/
noncomputable def antiKummerRealSubfield
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    (pkg : SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr) :
    IntermediateField (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  IntermediateField.fixedField (Subgroup.zpowers pkg.sigmaTilde)

/-- **`α₀ + α₀⁻¹` is fixed by complex conjugation** when `α₀` is σ-anti. -/
theorem antiRadical_sum_inv_complexConj_fixed
    (α₀ : K) (_hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    NumberField.IsCMField.complexConj K (α₀ + α₀⁻¹) = α₀ + α₀⁻¹ := by
  rw [map_add, h_anti, map_inv₀, h_anti, inv_inv, add_comm]

/-- **`α₀ + α₀⁻¹ ∈ K⁺`** when `α₀` is σ-anti. -/
theorem antiRadical_sum_inv_mem_Kplus
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (α₀ + α₀⁻¹) ∈ (NumberField.maximalRealSubfield K) := by
  rw [← NumberField.IsCMField.complexConj_eq_self_iff (K := K)]
  exact antiRadical_sum_inv_complexConj_fixed K α₀ hα₀ h_anti

/-- **The lifted K⁺-element** `⟨α₀ + α₀⁻¹, _⟩ : ↥K⁺`. -/
noncomputable def antiRadical_sum_inv_kplus
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    NumberField.maximalRealSubfield K :=
  ⟨α₀ + α₀⁻¹, antiRadical_sum_inv_mem_Kplus K α₀ hα₀ h_anti⟩

/-- **The K⁺-polynomial** `g := X^(2p) - (α₀ + α₀⁻¹) * X^p + 1 ∈ K⁺[X]`. -/
noncomputable def antiKummerKplusPoly
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    Polynomial (NumberField.maximalRealSubfield K) :=
  Polynomial.X ^ (2 * p) -
    Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
      Polynomial.X ^ p +
    Polynomial.C 1

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` is monic** of degree `2p`. -/
theorem antiKummerKplusPoly_monic
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).Monic := by
  unfold antiKummerKplusPoly
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have h_p_lt : p < 2 * p := by omega
  set q : Polynomial (NumberField.maximalRealSubfield K) :=
    -Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) * Polynomial.X ^ p + Polynomial.C 1
  have h_eq : (Polynomial.X ^ (2 * p) -
      Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
        Polynomial.X ^ p + Polynomial.C 1 :
        Polynomial (NumberField.maximalRealSubfield K)) =
      Polynomial.X ^ (2 * p) + q := by
    simp only [q]
    ring
  rw [h_eq]
  refine Polynomial.monic_X_pow_add (n := 2 * p) (p := q) ?_
  show Polynomial.degree q < 2 * p
  simp only [q]
  refine lt_of_le_of_lt
    (Polynomial.degree_add_le
      (-Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
        (Polynomial.X ^ p : Polynomial (NumberField.maximalRealSubfield K))) (Polynomial.C 1)) ?_
  refine max_lt ?_ ?_
  · have h_neg :
        (-Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
          (Polynomial.X ^ p : Polynomial (NumberField.maximalRealSubfield K))).degree =
        (Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
          (Polynomial.X ^ p : Polynomial (NumberField.maximalRealSubfield K))).degree := by
      rw [neg_mul, Polynomial.degree_neg]
    rw [h_neg]
    by_cases hC : antiRadical_sum_inv_kplus K α₀ hα₀ h_anti = 0
    · rw [hC, map_zero, zero_mul, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_C_mul (a := antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) hC]
      rw [Polynomial.degree_X_pow]
      exact_mod_cast h_p_lt
  · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    exact_mod_cast Nat.mul_pos two_pos hp_pos

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Factorisation**: `g.map (algebraMap K⁺ K) = (X^p - α₀)(X^p - α₀⁻¹)` in K[X]. -/
theorem antiKummerKplusPoly_map_eq_factor_product
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).map
        (algebraMap (NumberField.maximalRealSubfield K) K) =
      (Polynomial.X ^ p - Polynomial.C α₀) *
        (Polynomial.X ^ p - Polynomial.C α₀⁻¹) := by
  unfold antiKummerKplusPoly antiRadical_sum_inv_kplus
  push_cast [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_one]
  have h_lift : algebraMap (NumberField.maximalRealSubfield K) K
      (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) = α₀ + α₀⁻¹ := rfl
  rw [show (algebraMap (NumberField.maximalRealSubfield K) K)
      ⟨α₀ + α₀⁻¹, antiRadical_sum_inv_mem_Kplus K α₀ hα₀ h_anti⟩ = α₀ + α₀⁻¹ from rfl]
  have h_inv : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
  ring_nf
  rw [Polynomial.C_add, ← Polynomial.C_mul, h_inv]
  ring

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **`g.map (algebraMap K⁺ L) = ((X^p - α₀)(X^p - α₀⁻¹)).map (algebraMap K L)`**. -/
theorem antiKummerKplusPoly_map_L_eq_factor_product
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).map
        (algebraMap (NumberField.maximalRealSubfield K)
          (antiKummerLift (p := p) K α₀ hα₀)) =
      ((Polynomial.X ^ p - Polynomial.C α₀) *
        (Polynomial.X ^ p - Polynomial.C α₀⁻¹)).map
          (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)) := by
  rw [← antiKummerKplusPoly_map_eq_factor_product (p := p) K α₀ hα₀ h_anti,
      Polynomial.map_map]
  rfl

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **`Normal K⁺ L` from a `Polynomial.IsSplittingField K⁺ L g` instance.** -/
theorem antiKummerLift_normal_of_isSplittingField
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    [Polynomial.IsSplittingField (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)
      (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)] :
    Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  Normal.of_isSplittingField (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **`X^p - α₀` splits in L** (the K-defining polynomial of L). -/
theorem antiKummerLift_X_pow_sub_C_splits
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    ((Polynomial.X ^ p - Polynomial.C α₀).map
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀))).Splits :=
  Polynomial.IsSplittingField.splits (antiKummerLift (p := p) K α₀ hα₀)
    (Polynomial.X ^ p - Polynomial.C α₀)

omit [IsCMField K] in
/-- **`X^p - α₀⁻¹` splits in L** (the σ-conjugate of the defining polynomial). -/
theorem antiKummerLift_X_pow_sub_C_inv_splits
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    ((Polynomial.X ^ p - Polynomial.C α₀⁻¹).map
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀))).Splits := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have h_splits := antiKummerLift_X_pow_sub_C_splits (p := p) K α₀ hα₀
  have h_deg : ((Polynomial.X ^ p - Polynomial.C α₀).map
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀))).degree ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.degree_X_pow_sub_C (Fact.out : Nat.Prime p).pos]
    have : 0 < p := (Fact.out : Nat.Prime p).pos
    exact_mod_cast this.ne'
  set ρ : antiKummerLift (p := p) K α₀ hα₀ :=
    Polynomial.rootOfSplits h_splits h_deg with hρ_def
  have h_ρ_root :
      Polynomial.eval ρ ((Polynomial.X ^ p - Polynomial.C α₀).map
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀))) = 0 :=
    Polynomial.eval_rootOfSplits h_splits h_deg
  have h_ρ_pow : ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at h_ρ_root
    exact h_ρ_root
  have h_ρ_ne : ρ ≠ 0 := by
    intro h_eq
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have h_pow_zero : ρ ^ p = 0 := by rw [h_eq, zero_pow hp_pos.ne']
    rw [h_ρ_pow] at h_pow_zero
    exact hα₀ ((map_eq_zero_iff _ (RingHom.injective _)).mp h_pow_zero)
  have hζ_K : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  set ζ_L := algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
    (IsCyclotomicExtension.zeta p ℚ K)
  have hζ_L_prim : IsPrimitiveRoot ζ_L p :=
    hζ_K.map_of_injective (RingHom.injective _)
  refine X_pow_sub_C_splits_of_isPrimitiveRoot hζ_L_prim (α := ρ⁻¹) ?_
  rw [inv_pow, h_ρ_pow, ← map_inv₀]

/-- **g.map (algMap K⁺ L) splits in L**: combine the two factor splits. -/
theorem antiKummerKplusPoly_map_L_splits
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).map
      (algebraMap (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀))).Splits := by
  rw [antiKummerKplusPoly_map_L_eq_factor_product (p := p) K α₀ hα₀ h_anti]
  rw [Polynomial.map_mul]
  exact (antiKummerLift_X_pow_sub_C_splits (p := p) K α₀ hα₀).mul
    (antiKummerLift_X_pow_sub_C_inv_splits (p := p) K α₀ hα₀)

/-- **`Normal K⁺ L` from σ-anti α₀** (conditional on the splitting-field
adjoin_rootSet hypothesis). -/
theorem antiKummerLift_normal_of_anti_and_adjoin
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_adjoin : Algebra.adjoin (NumberField.maximalRealSubfield K)
      ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
        (antiKummerLift (p := p) K α₀ hα₀) : Set _) = ⊤) :
    Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) := by
  haveI : Polynomial.IsSplittingField (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)
      (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti) :=
    ⟨antiKummerKplusPoly_map_L_splits (p := p) K α₀ hα₀ h_anti, h_adjoin⟩
  exact Normal.of_isSplittingField (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
private theorem antiKummerLift_X_pow_sub_C_map_degree_ne_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    ((Polynomial.X ^ p - Polynomial.C α₀).map
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀))).degree ≠ 0 := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.degree_X_pow_sub_C (Fact.out : Nat.Prime p).pos]
  exact_mod_cast (Fact.out : Nat.Prime p).pos.ne'

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **Existence of a K-defining root** `ρ ∈ L` with `ρ^p = α₀`. -/
theorem antiKummerLift_exists_root
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    ∃ ρ : antiKummerLift (p := p) K α₀ hα₀,
      ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
  obtain ⟨ρ, hρ⟩ := (antiKummerLift_X_pow_sub_C_splits (p := p) K α₀ hα₀).exists_eval_eq_zero
    (antiKummerLift_X_pow_sub_C_map_degree_ne_zero (p := p) K α₀ hα₀)
  refine ⟨ρ, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] at hρ
  exact hρ

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **A nonzero root** of `X^p - α₀` in L, with `ρ^p = α₀` and `ρ ≠ 0`. -/
theorem antiKummerLift_exists_root_ne_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    ∃ ρ : antiKummerLift (p := p) K α₀ hα₀,
      ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ ∧ ρ ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := antiKummerLift_exists_root (p := p) K α₀ hα₀
  refine ⟨ρ, hρ, ?_⟩
  intro h_eq
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have h_pow_zero : ρ ^ p = 0 := by rw [h_eq]; exact zero_pow hp_pos.ne'
  rw [hρ] at h_pow_zero
  exact hα₀ ((map_eq_zero_iff _ (RingHom.injective _)).mp h_pow_zero)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **ρ is in `g.rootSet L`** (since X^p - α₀ divides g in K[X]). -/
theorem antiKummerLift_root_mem_rootSet
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    {ρ : antiKummerLift (p := p) K α₀ hα₀}
    (hρ_pow : ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) :
    ρ ∈ (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
      (antiKummerLift (p := p) K α₀ hα₀) := by
  rw [Polynomial.mem_rootSet]
  refine ⟨?_, ?_⟩
  ·
    intro h_zero
    have h_map_zero := congrArg
      (Polynomial.map (algebraMap (NumberField.maximalRealSubfield K) K)) h_zero
    rw [antiKummerKplusPoly_map_eq_factor_product (p := p) K α₀ hα₀ h_anti,
        Polynomial.map_zero] at h_map_zero
    rcases mul_eq_zero.mp h_map_zero with h | h
    · exact (Polynomial.X_pow_sub_C_ne_zero (Fact.out : Nat.Prime p).pos α₀) h
    · exact (Polynomial.X_pow_sub_C_ne_zero (Fact.out : Nat.Prime p).pos α₀⁻¹) h
  ·
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [show (algebraMap (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) =
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)).comp
        (algebraMap (NumberField.maximalRealSubfield K) K) from rfl]
    rw [← Polynomial.map_map]
    rw [antiKummerKplusPoly_map_eq_factor_product (p := p) K α₀ hα₀ h_anti]
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        hρ_pow, sub_self, zero_mul]

omit [IsCMField K] in
/-- **`ζ_L · ρ`** is also a root of `X^p - α₀` in L: `(ζ_L · ρ)^p = algMap α₀`. -/
theorem antiKummerLift_zeta_mul_root_pow_eq
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    {ρ : antiKummerLift (p := p) K α₀ hα₀}
    (hρ_pow : ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) :
    (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K) * ρ) ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
  rw [mul_pow, ← map_pow, hρ_pow,
      (IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one, map_one, one_mul]

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **`ρ⁻¹` is a root of `X^p - α₀⁻¹` in L**: `(ρ⁻¹)^p = algMap α₀⁻¹`. -/
theorem antiKummerLift_root_inv_pow_eq
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    {ρ : antiKummerLift (p := p) K α₀ hα₀}
    (hρ_pow : ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) :
    ρ⁻¹ ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀⁻¹ := by
  rw [inv_pow, hρ_pow, ← map_inv₀]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`ρ⁻¹ ∈ g.rootSet L`** (via the X^p - α₀⁻¹ factor of g). -/
theorem antiKummerLift_root_inv_mem_rootSet
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    {ρ : antiKummerLift (p := p) K α₀ hα₀}
    (hρ_pow : ρ ^ p = algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀)
    (_hρ_ne : ρ ≠ 0) :
    ρ⁻¹ ∈ (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
      (antiKummerLift (p := p) K α₀ hα₀) := by
  rw [Polynomial.mem_rootSet]
  refine ⟨?_, ?_⟩
  ·
    intro h_zero
    have h_map_zero := congrArg
      (Polynomial.map (algebraMap (NumberField.maximalRealSubfield K) K)) h_zero
    rw [antiKummerKplusPoly_map_eq_factor_product (p := p) K α₀ hα₀ h_anti,
        Polynomial.map_zero] at h_map_zero
    rcases mul_eq_zero.mp h_map_zero with h | h
    · exact (Polynomial.X_pow_sub_C_ne_zero (Fact.out : Nat.Prime p).pos α₀) h
    · exact (Polynomial.X_pow_sub_C_ne_zero (Fact.out : Nat.Prime p).pos α₀⁻¹) h
  ·
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [show (algebraMap (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) =
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)).comp
        (algebraMap (NumberField.maximalRealSubfield K) K) from rfl]
    rw [← Polynomial.map_map]
    rw [antiKummerKplusPoly_map_eq_factor_product (p := p) K α₀ hα₀ h_anti]
    rw [Polynomial.map_mul, Polynomial.eval_mul]
    apply mul_eq_zero.mpr
    right
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        antiKummerLift_root_inv_pow_eq (p := p) K α₀ hα₀ hρ_pow, sub_self]

/-- **The image of ζ in L belongs to `Algebra.adjoin K⁺ (g.rootSet L)`**. -/
theorem antiKummerLift_zeta_mem_adjoin
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K) ∈
      Algebra.adjoin (NumberField.maximalRealSubfield K)
        ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
          (antiKummerLift (p := p) K α₀ hα₀) : Set _) := by
  obtain ⟨ρ, hρ_pow, hρ_ne⟩ := antiKummerLift_exists_root_ne_zero (p := p) K α₀ hα₀
  set ζ_L := algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
    (IsCyclotomicExtension.zeta p ℚ K)
  have h_eq : ζ_L = (ζ_L * ρ) * ρ⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hρ_ne, mul_one]
  rw [h_eq]
  apply Subalgebra.mul_mem
  ·
    apply Algebra.subset_adjoin
    exact antiKummerLift_root_mem_rootSet (p := p) K α₀ hα₀ h_anti
      (antiKummerLift_zeta_mul_root_pow_eq (p := p) K α₀ hα₀ hρ_pow)
  ·
    apply Algebra.subset_adjoin
    exact antiKummerLift_root_inv_mem_rootSet (p := p) K α₀ hα₀ h_anti hρ_pow hρ_ne

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(X^p - α₀).rootSet L ⊆ g.rootSet L`**. -/
theorem antiKummerLift_X_pow_sub_C_rootSet_subset
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (Polynomial.X ^ p - Polynomial.C α₀).rootSet
        (antiKummerLift (p := p) K α₀ hα₀) ⊆
      (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
        (antiKummerLift (p := p) K α₀ hα₀) := by
  intro r hr
  rw [Polynomial.mem_rootSet] at hr
  obtain ⟨_h_nz, hr_eval⟩ := hr
  have hr_pow : r ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hr_eval
    exact hr_eval
  exact antiKummerLift_root_mem_rootSet (p := p) K α₀ hα₀ h_anti hr_pow

/-- **`K ⊆ Algebra.adjoin K⁺ (g.rootSet L)`** — equivalently, the K-image
in L is in the K⁺-adjoin of g's roots. -/
theorem antiKummerLift_K_image_in_adjoin_of_K_gen
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_K_gen : ∀ k : K,
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k ∈
        Algebra.adjoin (NumberField.maximalRealSubfield K)
          {algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
            (IsCyclotomicExtension.zeta p ℚ K)}) :
    ∀ k : K, algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k ∈
      Algebra.adjoin (NumberField.maximalRealSubfield K)
        ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
          (antiKummerLift (p := p) K α₀ hα₀) : Set _) := by
  intro k
  have h_adjoin_zeta_sub : Algebra.adjoin (NumberField.maximalRealSubfield K)
      {algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K)} ≤
    Algebra.adjoin (NumberField.maximalRealSubfield K)
      ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
        (antiKummerLift (p := p) K α₀ hα₀) : Set _) := by
    rw [Algebra.adjoin_le_iff]
    rintro x rfl
    exact antiKummerLift_zeta_mem_adjoin (p := p) K α₀ hα₀ h_anti
  exact h_adjoin_zeta_sub (h_K_gen k)

/-- **IsScalarTower ℚ K⁺ L instance** — needed for h_K_gen but not auto-derived. -/
instance antiKummerLift_isScalarTower_Q_Kplus_L
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    IsScalarTower ℚ (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℚ K
      (antiKummerLift (p := p) K α₀ hα₀),
      IsScalarTower.algebraMap_apply ℚ (NumberField.maximalRealSubfield K) K]
    rw [← IsScalarTower.algebraMap_apply (NumberField.maximalRealSubfield K) K
      (antiKummerLift (p := p) K α₀ hα₀)]

omit [IsCMField K] in
/-- **`h_K_gen` discharge**: every K-element maps into K⁺-adjoin of {ζ_L}. -/
theorem antiKummerLift_h_K_gen
    (α₀ : K) (hα₀ : α₀ ≠ 0) (k : K) :
    algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k ∈
      Algebra.adjoin (NumberField.maximalRealSubfield K)
        {algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
          (IsCyclotomicExtension.zeta p ℚ K)} := by
  have h_k_in_Q : k ∈ Algebra.adjoin ℚ
      ({b : K | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} : Set K) :=
    IsCyclotomicExtension.adjoin_roots k
  have h_k_in_Kplus : k ∈ Algebra.adjoin (NumberField.maximalRealSubfield K)
      ({b : K | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} : Set K) := by
    have h_le : Algebra.adjoin ℚ
        ({b : K | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} : Set K) ≤
      (Algebra.adjoin (NumberField.maximalRealSubfield K)
        ({b : K | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} : Set K)).restrictScalars ℚ := by
      rw [Algebra.adjoin_le_iff]
      exact Algebra.subset_adjoin
    exact h_le h_k_in_Q
  have h_image_in : algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k ∈
      Algebra.adjoin (NumberField.maximalRealSubfield K)
        ((algebraMap K (antiKummerLift (p := p) K α₀ hα₀)) ''
          ({b : K | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}) : Set _) := by
    rw [Algebra.adjoin_algebraMap (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀)]
    exact ⟨k, h_k_in_Kplus, rfl⟩
  refine (Algebra.adjoin_le_iff (S := Algebra.adjoin (NumberField.maximalRealSubfield K)
      ({algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (IsCyclotomicExtension.zeta p ℚ K)} : Set _))).mpr ?_ h_image_in
  rintro x ⟨b, ⟨n, hn_eq, _hn_ne, hb_pow⟩, rfl⟩
  rw [Set.mem_singleton_iff] at hn_eq
  rw [hn_eq] at hb_pow
  have hζ_K : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨i, _, rfl⟩ := hζ_K.eq_pow_of_pow_eq_one hb_pow
  rw [map_pow]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i

set_option maxHeartbeats 800000 in
/-- **AK-2 adjoin = ⊤, conditional on the K = K⁺[ζ] generation fact.** -/
theorem antiKummerKplusPoly_adjoin_rootSet_eq_top_of_K_gen
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_K_gen : ∀ k : K,
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k ∈
        Algebra.adjoin (NumberField.maximalRealSubfield K)
          {algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
            (IsCyclotomicExtension.zeta p ℚ K)}) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
        ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
          (antiKummerLift (p := p) K α₀ hα₀) : Set _) = ⊤ := by
  rw [eq_top_iff]
  have h_SF : Algebra.adjoin K
      ((Polynomial.X ^ p - Polynomial.C α₀).rootSet
        (antiKummerLift (p := p) K α₀ hα₀) : Set _) = ⊤ :=
    Polynomial.IsSplittingField.adjoin_rootSet
      (antiKummerLift (p := p) K α₀ hα₀) (Polynomial.X ^ p - Polynomial.C α₀)
  calc (⊤ : Subalgebra (NumberField.maximalRealSubfield K)
              (antiKummerLift (p := p) K α₀ hα₀))
      = (⊤ : Subalgebra K (antiKummerLift (p := p) K α₀ hα₀)).restrictScalars
            (NumberField.maximalRealSubfield K) := by
        rw [Subalgebra.restrictScalars_top]
    _ = (Algebra.adjoin K
            ((Polynomial.X ^ p - Polynomial.C α₀).rootSet
              (antiKummerLift (p := p) K α₀ hα₀) : Set _)).restrictScalars
              (NumberField.maximalRealSubfield K) := by rw [h_SF]
    _ ≤ Algebra.adjoin (NumberField.maximalRealSubfield K)
            ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
              (antiKummerLift (p := p) K α₀ hα₀) : Set _) := by
        intro x hx
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
        ·
          intro r hr
          apply Algebra.subset_adjoin
          exact antiKummerLift_X_pow_sub_C_rootSet_subset (p := p) K α₀ hα₀ h_anti hr
        ·
          intro k
          exact antiKummerLift_K_image_in_adjoin_of_K_gen (p := p) K α₀ hα₀ h_anti h_K_gen k
        · intro a b _ _ ha hb
          exact Subalgebra.add_mem _ ha hb
        · intro a b _ _ ha hb
          exact Subalgebra.mul_mem _ ha hb

/-- **AK-2 adjoin = ⊤ (unconditional)** by composing
`antiKummerKplusPoly_adjoin_rootSet_eq_top_of_K_gen` with the shipped
`antiKummerLift_h_K_gen` discharge. -/
theorem antiKummerKplusPoly_adjoin_rootSet_eq_top
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
        ((antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).rootSet
          (antiKummerLift (p := p) K α₀ hα₀) : Set _) = ⊤ :=
  antiKummerKplusPoly_adjoin_rootSet_eq_top_of_K_gen (p := p) K α₀ hα₀ h_anti
    (antiKummerLift_h_K_gen (p := p) K α₀ hα₀)

/-- **AK-2 Normal K⁺ L (unconditional in the σ-anti FLT37 setting)** by composing
`antiKummerLift_normal_of_anti_and_adjoin` with the unconditional adjoin. -/
theorem antiKummerLift_normal_of_anti
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    Normal (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  antiKummerLift_normal_of_anti_and_adjoin (p := p) K α₀ hα₀ h_anti
    (antiKummerKplusPoly_adjoin_rootSet_eq_top (p := p) K α₀ hα₀ h_anti)

/-- **σ̃ K⁺-algebra HOM (unconditional in the σ-anti setting)** — composes
`sigmaTildeHom` with the σ-anti-derived Normal instance. -/
noncomputable def sigmaTildeHom_anti
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    antiKummerLift (p := p) K α₀ hα₀ →ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
  haveI := antiKummerLift_normal_of_anti (p := p) K α₀ hα₀ h_anti
  sigmaTildeHom (p := p) K α₀ hα₀

/-- **σ̃ K⁺-algebra EQUIV (unconditional in the σ-anti setting)**. -/
noncomputable def sigmaTildeEquiv_anti
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
  haveI := antiKummerLift_normal_of_anti (p := p) K α₀ hα₀ h_anti
  haveI : Module.Finite (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
    Module.Finite.trans K (antiKummerLift (p := p) K α₀ hα₀)
  sigmaTildeEquiv (p := p) K α₀ hα₀

/-- **`IsGalois K⁺ L`** under σ-anti α₀**. -/
theorem antiKummerLift_isGalois_of_anti
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    IsGalois (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) := by
  haveI := antiKummerLift_normal_of_anti (p := p) K α₀ hα₀ h_anti
  exact { }

/-- **Instance: IsScalarTower K⁺ K L** — needed for the FD chain. -/
instance antiKummerLift_isScalarTower_Kplus_K_L
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    IsScalarTower (NumberField.maximalRealSubfield K) K
      (antiKummerLift (p := p) K α₀ hα₀) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- **Instance: FiniteDimensional K⁺ L when σ-anti**. Bridges Module.Finite.trans
to FiniteDimensional via the abbrev identification. -/
instance antiKummerLift_finiteDimensional_Kplus
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    FiniteDimensional (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  Module.Finite.trans K (antiKummerLift (p := p) K α₀ hα₀)

/-- **`[L : K⁺] = 2p`** when X^p - α₀ is K-irreducible. -/
theorem antiKummerLift_finrank_Kplus_of_irreducible
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    Module.finrank (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) = 2 * p := by
  have h_Kplus_K : Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
    finrank_K_over_Kplus K
  have h_K_L : Module.finrank K (antiKummerLift (p := p) K α₀ hα₀) = p :=
    antiKummerLift_finrank_of_irreducible (p := p) K α₀ hα₀ h_irr
  rw [← Module.finrank_mul_finrank (NumberField.maximalRealSubfield K) K
    (antiKummerLift (p := p) K α₀ hα₀), h_Kplus_K, h_K_L]

/-- **Module.finrank K⁺ Gal(L/K⁺) = 2p**. Stated without IsGalois.card_aut_eq_finrank. -/
theorem antiKummerLift_finrank_eq_two_mul_p_of_anti
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (_h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    Module.finrank (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) = 2 * p :=
  antiKummerLift_finrank_Kplus_of_irreducible (p := p) K α₀ hα₀ h_irr

/-- **Canonical p-th root of α₀ in L** via `Polynomial.rootOfSplits`. -/
noncomputable def antiKummerLiftRoot
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    antiKummerLift (p := p) K α₀ hα₀ :=
  Polynomial.rootOfSplits
    (antiKummerLift_X_pow_sub_C_splits (p := p) K α₀ hα₀)
    (by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
          Polynomial.degree_X_pow_sub_C (Fact.out : Nat.Prime p).pos]
      exact_mod_cast (Fact.out : Nat.Prime p).pos.ne')

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **`(antiKummerLiftRoot α₀)^p = algMap α₀`**: the canonical root satisfies the defining
equation. -/
theorem antiKummerLiftRoot_pow_eq
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
  have h_root :=
    Polynomial.eval_rootOfSplits
      (antiKummerLift_X_pow_sub_C_splits (p := p) K α₀ hα₀)
      (by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
            Polynomial.degree_X_pow_sub_C (Fact.out : Nat.Prime p).pos]
        exact_mod_cast (Fact.out : Nat.Prime p).pos.ne')
  change Polynomial.eval (antiKummerLiftRoot (p := p) K α₀ hα₀) _ = 0 at h_root
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h_root
  exact h_root

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **`antiKummerLiftRoot α₀ ≠ 0`**: the canonical root is non-zero (since `α₀ ≠ 0`). -/
theorem antiKummerLiftRoot_ne_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0) :
    antiKummerLiftRoot (p := p) K α₀ hα₀ ≠ 0 := by
  intro h_eq
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have h_pow_zero : (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p = 0 := by
    rw [h_eq]; exact zero_pow hp_pos.ne'
  rw [antiKummerLiftRoot_pow_eq] at h_pow_zero
  exact hα₀ ((map_eq_zero_iff _ (RingHom.injective _)).mp h_pow_zero)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerLiftRoot α₀` is a root of `g = antiKummerKplusPoly` in L**. -/
theorem antiKummerLiftRoot_aeval_g_eq_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    Polynomial.aeval (antiKummerLiftRoot (p := p) K α₀ hα₀)
      (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti) = 0 := by
  have h_mem :=
    antiKummerLift_root_mem_rootSet (p := p) K α₀ hα₀ h_anti
      (ρ := antiKummerLiftRoot (p := p) K α₀ hα₀)
      (antiKummerLiftRoot_pow_eq (p := p) K α₀ hα₀)
  rw [Polynomial.mem_rootSet] at h_mem
  exact h_mem.2

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(antiKummerLiftRoot α₀)⁻¹` is a root of `g = antiKummerKplusPoly` in L**. -/
theorem antiKummerLiftRoot_inv_aeval_g_eq_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    Polynomial.aeval (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹
      (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti) = 0 := by
  have h_mem :=
    antiKummerLift_root_inv_mem_rootSet (p := p) K α₀ hα₀ h_anti
      (ρ := antiKummerLiftRoot (p := p) K α₀ hα₀)
      (antiKummerLiftRoot_pow_eq (p := p) K α₀ hα₀)
      (antiKummerLiftRoot_ne_zero (p := p) K α₀ hα₀)
  rw [Polynomial.mem_rootSet] at h_mem
  exact h_mem.2

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`minpoly K⁺ (antiKummerLiftRoot α₀) = antiKummerKplusPoly`** under irreducibility of g. -/
theorem antiKummerLiftRoot_minpoly_eq_g
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    minpoly (NumberField.maximalRealSubfield K)
      (antiKummerLiftRoot (p := p) K α₀ hα₀) =
      antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti :=
  (minpoly.eq_of_irreducible_of_monic h_irr_g
    (antiKummerLiftRoot_aeval_g_eq_zero (p := p) K α₀ hα₀ h_anti)
    (antiKummerKplusPoly_monic (p := p) K α₀ hα₀ h_anti)).symm

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`minpoly K⁺ (antiKummerLiftRoot α₀)⁻¹ = antiKummerKplusPoly`** under irreducibility of g. -/
theorem antiKummerLiftRoot_inv_minpoly_eq_g
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    minpoly (NumberField.maximalRealSubfield K)
      (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ =
      antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti :=
  (minpoly.eq_of_irreducible_of_monic h_irr_g
    (antiKummerLiftRoot_inv_aeval_g_eq_zero (p := p) K α₀ hα₀ h_anti)
    (antiKummerKplusPoly_monic (p := p) K α₀ hα₀ h_anti)).symm

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` has degree `2p`** as a natural number. -/
theorem antiKummerKplusPoly_natDegree
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).natDegree = 2 * p := by
  have h_monic := antiKummerKplusPoly_monic (p := p) K α₀ hα₀ h_anti
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have h_deg : (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti).degree = (2 * p : ℕ) := by
    unfold antiKummerKplusPoly
    rw [show (Polynomial.X ^ (2 * p) -
        Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
          Polynomial.X ^ p + Polynomial.C 1 :
          Polynomial (NumberField.maximalRealSubfield K)) =
        Polynomial.X ^ (2 * p) +
          (-Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) * Polynomial.X ^ p +
            Polynomial.C 1) by ring]
    have h_X_pow_deg :
        (Polynomial.X ^ (2 * p) : Polynomial (NumberField.maximalRealSubfield K)).degree =
        2 * p := Polynomial.degree_X_pow _
    have h_rest_lt :
        (-Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) * Polynomial.X ^ p +
          Polynomial.C 1 : Polynomial (NumberField.maximalRealSubfield K)).degree < 2 * p := by
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
      refine max_lt ?_ ?_
      · by_cases hC : antiRadical_sum_inv_kplus K α₀ hα₀ h_anti = 0
        · rw [hC, map_zero, neg_zero, zero_mul, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · have h_neg :
              ((-Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti)) *
                (Polynomial.X ^ p : Polynomial (NumberField.maximalRealSubfield K))).degree =
              (Polynomial.C (antiRadical_sum_inv_kplus K α₀ hα₀ h_anti) *
                (Polynomial.X ^ p : Polynomial (NumberField.maximalRealSubfield K))).degree := by
            rw [neg_mul, Polynomial.degree_neg]
          rw [h_neg, Polynomial.degree_C_mul hC, Polynomial.degree_X_pow]
          exact_mod_cast (by omega : p < 2 * p)
      · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        exact_mod_cast (by omega : (0 : ℕ) < 2 * p)
    rw [Polynomial.degree_add_eq_left_of_degree_lt (h_X_pow_deg ▸ h_rest_lt)]
    exact h_X_pow_deg
  exact Polynomial.natDegree_eq_of_degree_eq_some h_deg

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerLiftRoot α₀` is integral over K⁺**: it's a root of monic non-zero `g ∈ K⁺[X]`. -/
theorem antiKummerLiftRoot_isIntegral_Kplus
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    IsIntegral (NumberField.maximalRealSubfield K)
      (antiKummerLiftRoot (p := p) K α₀ hα₀) := by
  refine ⟨antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti,
    antiKummerKplusPoly_monic (p := p) K α₀ hα₀ h_anti, ?_⟩
  have h := antiKummerLiftRoot_aeval_g_eq_zero (p := p) K α₀ hα₀ h_anti
  rwa [Polynomial.aeval_def] at h

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`(antiKummerLiftRoot α₀)⁻¹ is integral over K⁺`**. -/
theorem antiKummerLiftRoot_inv_isIntegral_Kplus
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    IsIntegral (NumberField.maximalRealSubfield K)
      (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ := by
  refine ⟨antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti,
    antiKummerKplusPoly_monic (p := p) K α₀ hα₀ h_anti, ?_⟩
  have h := antiKummerLiftRoot_inv_aeval_g_eq_zero (p := p) K α₀ hα₀ h_anti
  rwa [Polynomial.aeval_def] at h

/-- **`K⁺[ρ] = ⊤`** as `Subalgebra`: the canonical root generates L over K⁺. -/
theorem antiKummerLiftRoot_adjoin_eq_top
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
        ({antiKummerLiftRoot (p := p) K α₀ hα₀} :
          Set (antiKummerLift (p := p) K α₀ hα₀)) = ⊤ := by
  have hρ_int := antiKummerLiftRoot_isIntegral_Kplus (p := p) K α₀ hα₀ h_anti
  set pb := Algebra.adjoin.powerBasis hρ_int with hpb_def
  have h_pb_dim : pb.dim = 2 * p := by
    rw [hpb_def, Algebra.adjoin.powerBasis_dim,
        antiKummerLiftRoot_minpoly_eq_g (p := p) K α₀ hα₀ h_anti h_irr_g,
        antiKummerKplusPoly_natDegree (p := p) K α₀ hα₀ h_anti]
  have h_pb_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (Algebra.adjoin (NumberField.maximalRealSubfield K)
        ({antiKummerLiftRoot (p := p) K α₀ hα₀} :
          Set (antiKummerLift (p := p) K α₀ hα₀))) = 2 * p := by
    rw [← h_pb_dim, ← PowerBasis.finrank pb]
  have h_top_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) = 2 * p := by
    rw [(Subalgebra.topEquiv (R := NumberField.maximalRealSubfield K)
      (A := antiKummerLift (p := p) K α₀ hα₀)).toLinearEquiv.finrank_eq]
    exact antiKummerLift_finrank_Kplus_of_irreducible (p := p) K α₀ hα₀ h_irr
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  haveI h_fd_top : FiniteDimensional (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) :=
    Module.finite_of_finrank_pos (by rw [h_top_finrank]; omega)
  exact Subalgebra.eq_of_le_of_finrank_eq le_top
    (h_pb_finrank.trans h_top_finrank.symm)

/-- **`K⁺[ρ⁻¹] = ⊤`**: the inverse root also generates L over K⁺. -/
theorem antiKummerLiftRoot_inv_adjoin_eq_top
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
        ({(antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹} :
          Set (antiKummerLift (p := p) K α₀ hα₀)) = ⊤ := by
  have hρ_int := antiKummerLiftRoot_inv_isIntegral_Kplus (p := p) K α₀ hα₀ h_anti
  set pb := Algebra.adjoin.powerBasis hρ_int with hpb_def
  have h_pb_dim : pb.dim = 2 * p := by
    rw [hpb_def, Algebra.adjoin.powerBasis_dim,
        antiKummerLiftRoot_inv_minpoly_eq_g (p := p) K α₀ hα₀ h_anti h_irr_g,
        antiKummerKplusPoly_natDegree (p := p) K α₀ hα₀ h_anti]
  have h_pb_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (Algebra.adjoin (NumberField.maximalRealSubfield K)
        ({(antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹} :
          Set (antiKummerLift (p := p) K α₀ hα₀))) = 2 * p := by
    rw [← h_pb_dim, ← PowerBasis.finrank pb]
  have h_top_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) = 2 * p := by
    rw [(Subalgebra.topEquiv (R := NumberField.maximalRealSubfield K)
      (A := antiKummerLift (p := p) K α₀ hα₀)).toLinearEquiv.finrank_eq]
    exact antiKummerLift_finrank_Kplus_of_irreducible (p := p) K α₀ hα₀ h_irr
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  haveI h_fd_top : FiniteDimensional (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K)
        (antiKummerLift (p := p) K α₀ hα₀)) :=
    Module.finite_of_finrank_pos (by rw [h_top_finrank]; omega)
  exact Subalgebra.eq_of_le_of_finrank_eq le_top
    (h_pb_finrank.trans h_top_finrank.symm)

/-- **`PowerBasis K⁺ L` from canonical root ρ**: a power basis with `gen = ρ`. -/
noncomputable def antiKummerLiftPowerBasis
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    PowerBasis (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  PowerBasis.ofAdjoinEqTop
    (antiKummerLiftRoot_isIntegral_Kplus (p := p) K α₀ hα₀ h_anti)
    (antiKummerLiftRoot_adjoin_eq_top (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)

/-- **`PowerBasis K⁺ L` from canonical root ρ⁻¹**: a power basis with `gen = ρ⁻¹`. -/
noncomputable def antiKummerLiftPowerBasisInv
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    PowerBasis (NumberField.maximalRealSubfield K)
      (antiKummerLift (p := p) K α₀ hα₀) :=
  PowerBasis.ofAdjoinEqTop
    (antiKummerLiftRoot_inv_isIntegral_Kplus (p := p) K α₀ hα₀ h_anti)
    (antiKummerLiftRoot_inv_adjoin_eq_top (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)

/-- **The σ̃ involutive lift via PowerBasis.equivOfMinpoly**: sends ρ ↦ ρ⁻¹. -/
noncomputable def antiKummerSigmaTildeInvolutive
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    antiKummerLift (p := p) K α₀ hα₀ ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
  (antiKummerLiftPowerBasis (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).equivOfMinpoly
    (antiKummerLiftPowerBasisInv (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
    (by
      rw [show (antiKummerLiftPowerBasis (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).gen =
        antiKummerLiftRoot (p := p) K α₀ hα₀ from
        PowerBasis.ofAdjoinEqTop_gen _ _]
      rw [show (antiKummerLiftPowerBasisInv (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).gen =
        (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ from
        PowerBasis.ofAdjoinEqTop_gen _ _]
      rw [antiKummerLiftRoot_minpoly_eq_g (p := p) K α₀ hα₀ h_anti h_irr_g,
          antiKummerLiftRoot_inv_minpoly_eq_g (p := p) K α₀ hα₀ h_anti h_irr_g])

/-- **σ̃ sends ρ to ρ⁻¹** by construction. -/
theorem antiKummerSigmaTildeInvolutive_apply_root
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      (antiKummerLiftRoot (p := p) K α₀ hα₀) =
      (antiKummerLiftRoot (p := p) K α₀ hα₀)⁻¹ := by
  unfold antiKummerSigmaTildeInvolutive
  rw [show antiKummerLiftRoot (p := p) K α₀ hα₀ =
    (antiKummerLiftPowerBasis (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).gen from
    (PowerBasis.ofAdjoinEqTop_gen _ _).symm]
  rw [PowerBasis.equivOfMinpoly_gen]
  exact PowerBasis.ofAdjoinEqTop_gen _ _

/-- **σ̃² = id on ρ**: the involution property at the canonical root. -/
theorem antiKummerSigmaTildeInvolutive_sq_apply_root
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
      ((antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (antiKummerLiftRoot (p := p) K α₀ hα₀)) =
      antiKummerLiftRoot (p := p) K α₀ hα₀ := by
  rw [antiKummerSigmaTildeInvolutive_apply_root (p := p) K α₀ hα₀ h_anti h_irr h_irr_g]
  rw [map_inv₀, antiKummerSigmaTildeInvolutive_apply_root
    (p := p) K α₀ hα₀ h_anti h_irr h_irr_g, inv_inv]

/-- **σ̃ ∘ σ̃ = AlgEquiv.refl**: the involution property as a Galois identity. -/
theorem antiKummerSigmaTildeInvolutive_sq_eq_refl
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).trans
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) =
      AlgEquiv.refl := by
  set pb := antiKummerLiftPowerBasis (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
  refine AlgEquiv.coe_algHom_injective ?_
  refine pb.algHom_ext ?_
  have h_gen : pb.gen = antiKummerLiftRoot (p := p) K α₀ hα₀ :=
    PowerBasis.ofAdjoinEqTop_gen _ _
  show ((antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).trans
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)) pb.gen =
    (AlgEquiv.refl (A₁ := antiKummerLift (p := p) K α₀ hα₀)).toAlgHom pb.gen
  rw [AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq]
  rw [AlgEquiv.trans_apply, h_gen]
  exact antiKummerSigmaTildeInvolutive_sq_apply_root (p := p) K α₀ hα₀ h_anti h_irr h_irr_g

/-- **σ̃ sends `algMap K L α₀` to `algMap K L α₀⁻¹`**: the K-element identification. -/
theorem antiKummerSigmaTildeInvolutive_apply_algebraMap_alpha
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti)) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀⁻¹ := by
  have h_ρ_pow : (antiKummerLiftRoot (p := p) K α₀ hα₀) ^ p =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ :=
    antiKummerLiftRoot_pow_eq (p := p) K α₀ hα₀
  rw [← h_ρ_pow, map_pow, antiKummerSigmaTildeInvolutive_apply_root]
  rw [inv_pow, h_ρ_pow, ← map_inv₀]

/-- **σ̃ is non-trivial**: σ̃ ≠ AlgEquiv.refl (because σ̃ swaps ρ with ρ⁻¹, and
ρ ≠ ρ⁻¹ since ρ ≠ 0 and α₀² ≠ 1 forces ρ² ≠ 1). -/
theorem antiKummerSigmaTildeInvolutive_ne_refl
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) ≠
      AlgEquiv.refl := by
  intro h_eq
  have h_eq_apply : (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀) α₀ := by
    rw [h_eq]
    rfl
  rw [antiKummerSigmaTildeInvolutive_apply_algebraMap_alpha
    (p := p) K α₀ hα₀ h_anti h_irr h_irr_g] at h_eq_apply
  have h_alg_inj : Function.Injective
      (algebraMap K (antiKummerLift (p := p) K α₀ hα₀)) := RingHom.injective _
  have h_inv_eq : α₀⁻¹ = α₀ := h_alg_inj h_eq_apply
  have h_sq : α₀ ^ 2 = 1 := by
    have h_mul : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
    rw [h_inv_eq] at h_mul
    rw [sq]
    exact h_mul
  exact h_alpha_sq_ne h_sq

/-- **K⁺[α₀] = ⊤ in K** under `α₀² ≠ 1`: α₀ generates K as a K⁺-algebra. -/
theorem K_adjoin_alpha_eq_top
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    Algebra.adjoin (NumberField.maximalRealSubfield K) ({α₀} : Set K) = ⊤ := by
  have h_α₀_not_in_Kplus :
      α₀ ∉ (NumberField.maximalRealSubfield K : Subfield K) := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff (K := K)]
    intro h_fixed
    have h_inv_eq : α₀⁻¹ = α₀ := h_anti ▸ h_fixed
    apply h_alpha_sq_ne
    have h_mul : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
    rw [h_inv_eq] at h_mul
    rw [sq]
    exact h_mul
  have h_int : IsIntegral (NumberField.maximalRealSubfield K) α₀ :=
    (Algebra.IsIntegral.of_finite (R := NumberField.maximalRealSubfield K) (B := K)).isIntegral α₀
  have h_minpoly_deg : 2 ≤ (minpoly (NumberField.maximalRealSubfield K) α₀).natDegree := by
    by_contra h_lt
    push Not at h_lt
    have h_eq_one : (minpoly (NumberField.maximalRealSubfield K) α₀).natDegree = 1 := by
      have h_pos : 0 < (minpoly (NumberField.maximalRealSubfield K) α₀).natDegree :=
        minpoly.natDegree_pos h_int
      omega
    have : α₀ ∈ (algebraMap (NumberField.maximalRealSubfield K) K).range :=
      (minpoly.mem_range_of_degree_eq_one (NumberField.maximalRealSubfield K) α₀
        (by rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero h_int), h_eq_one]
            exact_mod_cast rfl))
    obtain ⟨b, hb⟩ := this
    apply h_α₀_not_in_Kplus
    rw [← hb]
    have h_alg_apply : algebraMap (NumberField.maximalRealSubfield K) K b = (b : K) := rfl
    rw [h_alg_apply]
    exact b.2
  have h_pb_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (Algebra.adjoin (NumberField.maximalRealSubfield K) ({α₀} : Set K)) =
      (minpoly (NumberField.maximalRealSubfield K) α₀).natDegree :=
    (Algebra.adjoin.powerBasis h_int).finrank
  have h_K_finrank : Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
    finrank_K_over_Kplus K
  have h_pb_le : Module.finrank (NumberField.maximalRealSubfield K)
      (Algebra.adjoin (NumberField.maximalRealSubfield K) ({α₀} : Set K)) ≤ 2 := by
    rw [← h_K_finrank]
    exact Submodule.finrank_le
      (Subalgebra.toSubmodule
        (Algebra.adjoin (NumberField.maximalRealSubfield K) ({α₀} : Set K)))
  have h_pb_eq_two : Module.finrank (NumberField.maximalRealSubfield K)
      (Algebra.adjoin (NumberField.maximalRealSubfield K) ({α₀} : Set K)) = 2 := by
    rw [h_pb_finrank]
    omega
  have h_top_finrank : Module.finrank (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K) K) = 2 := by
    rw [(Subalgebra.topEquiv (R := NumberField.maximalRealSubfield K)
      (A := K)).toLinearEquiv.finrank_eq]
    exact h_K_finrank
  haveI : FiniteDimensional (NumberField.maximalRealSubfield K)
      (⊤ : Subalgebra (NumberField.maximalRealSubfield K) K) :=
    Module.finite_of_finrank_pos (by rw [h_top_finrank]; omega)
  exact Subalgebra.eq_of_le_of_finrank_eq le_top
    (h_pb_eq_two.trans h_top_finrank.symm)

/-- **σ̃ restricts to complex conjugation on K**: for any K-element k, σ̃ sends
algMap k to algMap (σ k). -/
theorem antiKummerSigmaTildeInvolutive_restricts_K
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) (k : K) :
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
        (algebraMap K (antiKummerLift (p := p) K α₀ hα₀) k) =
      algebraMap K (antiKummerLift (p := p) K α₀ hα₀)
        (NumberField.IsCMField.complexConj K k) := by
  set f₁ : K →ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
    (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).toAlgHom.comp
      (IsScalarTower.toAlgHom (NumberField.maximalRealSubfield K) K
        (antiKummerLift (p := p) K α₀ hα₀)) with hf₁
  set f₂ : K →ₐ[NumberField.maximalRealSubfield K]
      antiKummerLift (p := p) K α₀ hα₀ :=
    (IsScalarTower.toAlgHom (NumberField.maximalRealSubfield K) K
      (antiKummerLift (p := p) K α₀ hα₀)).comp
        (NumberField.IsCMField.complexConj K).toAlgHom with hf₂
  suffices h_eq : f₁ = f₂ by
    have h_apply : f₁ k = f₂ k := by rw [h_eq]
    simpa [f₁, f₂, hf₁, hf₂] using h_apply
  refine AlgHom.ext_of_adjoin_eq_top
    (K_adjoin_alpha_eq_top K α₀ hα₀ h_anti h_alpha_sq_ne) ?_
  rintro x ⟨rfl⟩
  show f₁ α₀ = f₂ α₀
  simp only [f₁, f₂, AlgHom.coe_comp, Function.comp_apply,
    IsScalarTower.coe_toAlgHom',
    AlgEquiv.coe_algHom]
  rw [antiKummerSigmaTildeInvolutive_apply_algebraMap_alpha
    (p := p) K α₀ hα₀ h_anti h_irr h_irr_g, h_anti]

/-- **`SigmaAntiKummerExtension` package from the involutive σ̃**: combines the
shipped pieces (σ̃² = id, σ̃ restricts to σ on K) into the structure used by
downstream AK-3/AK-4 reasoning. Requires α₀² ≠ 1 + g irreducible over K⁺. -/
noncomputable def antiKummerSigmaTildePkg
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr where
  sigmaTilde :=
    antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
  sigmaTilde_sq :=
    antiKummerSigmaTildeInvolutive_sq_eq_refl (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
  sigmaTilde_restricts_K k :=
    antiKummerSigmaTildeInvolutive_restricts_K (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      h_alpha_sq_ne k

/-- **Order of σ̃ in Gal(L/K⁺) is 2** under α₀² ≠ 1. -/
theorem antiKummerSigmaTildeInvolutive_orderOf
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    orderOf (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) = 2 := by
  have h_ne : antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g ≠ 1 := by
    intro h_eq
    exact antiKummerSigmaTildeInvolutive_ne_refl (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
      h_alpha_sq_ne h_eq
  have h_sq_eq_one :
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) ^ 2 = 1 := by
    rw [pow_two]
    ext x
    show ((antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) *
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)) x = x
    rw [show (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g *
        antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) =
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g).trans
        (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) from rfl]
    rw [antiKummerSigmaTildeInvolutive_sq_eq_refl (p := p) K α₀ hα₀ h_anti h_irr h_irr_g]
    rfl
  have h_dvd : orderOf (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)
      ∣ 2 := orderOf_dvd_of_pow_eq_one h_sq_eq_one
  have h_order_ne_one :
      orderOf (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g) ≠ 1 := by
    intro h_one
    apply h_ne
    rw [← pow_one (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g),
      ← h_one, pow_orderOf_eq_one]
  rcases (Nat.le_of_dvd (by omega) h_dvd).lt_or_eq with h_lt | h_eq
  ·
    interval_cases (orderOf
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g))
    ·
      simp at h_dvd
    · exact absurd rfl h_order_ne_one
  · exact h_eq

/-- **|⟨σ̃⟩| = 2** under α₀² ≠ 1. -/
theorem antiKummerSigmaTildeInvolutive_zpowers_natCard
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (antiKummerKplusPoly (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    Nat.card (Subgroup.zpowers
      (antiKummerSigmaTildeInvolutive (p := p) K α₀ hα₀ h_anti h_irr h_irr_g)) = 2 := by
  rw [Nat.card_zpowers]
  exact antiKummerSigmaTildeInvolutive_orderOf (p := p) K α₀ hα₀ h_anti h_irr h_irr_g
    h_alpha_sq_ne

/-- **Primarity hypothesis** for `α₀ ∈ (𝓞 K)ˣ`: `(ζ - 1)^p ∣ α₀ - 1` in `𝓞 K`. -/
def AntiRadicalPrimary (α₀ : (𝓞 K)ˣ) : Prop :=
  ∀ (hζ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta p ℚ K) p),
    ((hζ.toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit - 1 : 𝓞 K) ^ p ∣
      ((α₀ : 𝓞 K) - 1)

omit [IsCMField K] in
/-- **L/K is unramified, from primary α₀ in 𝓞 K — flt-regular Kummer's lemma input.** -/
theorem antiKummerLift_isUnramified_K_of_primary
    {α₀ : K} (hα₀ : α₀ ≠ 0) (hp_odd : p ≠ 2)
    (hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p)
    (α₀_unit : (𝓞 K)ˣ)
    (_h_α₀_alg : algebraMap (𝓞 K) K α₀_unit = α₀)
    (h_primary : ((hζ.toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit - 1 : 𝓞 K) ^ p ∣
      ((α₀_unit : 𝓞 K) - 1))
    (h_not_pth_pow : ∀ v : K, v ^ p ≠ α₀_unit)
    [Polynomial.IsSplittingField K (antiKummerLift (p := p) K α₀ hα₀)
      (Polynomial.X ^ p - Polynomial.C (α₀_unit : K))] :
    Algebra.Unramified (𝓞 K) (𝓞 (antiKummerLift (p := p) K α₀ hα₀)) := by
  have h_primary' : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ ((α₀_unit : 𝓞 K) - 1) := by
    rwa [IsUnit.unit_spec] at h_primary
  exact KummersLemma.isUnramified hp_odd hζ α₀_unit h_primary' h_not_pth_pow _

instance antiKummerLift_numberField
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    NumberField (antiKummerLift (p := p) K α₀ hα₀) := by
  unfold antiKummerLift
  exact NumberField.of_module_finite K (Polynomial.SplittingField
    (Polynomial.X ^ p - Polynomial.C α₀))

instance antiKummerRealSubfield_numberField
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    (pkg : SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr) :
    NumberField (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg) :=
  NumberField.of_intermediateField _

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **AK-3 packaged form**: L⁺/K⁺ is unramified at all finite places. -/
theorem antiKummerRealSubfield_isUnramified
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    (pkg : SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr)
    (h_isUnramified : Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
        (hα₀ := hα₀) (h_irr := h_irr) pkg))) :
    Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
        (hα₀ := hα₀) (h_irr := h_irr) pkg)) :=
  h_isUnramified

/-- **AK-3 packaged Galois structure for L⁺/K⁺**: combined hypothesis pack
that L⁺ = `antiKummerRealSubfield pkg` is a finite-dimensional cyclic-degree-p
Galois unramified extension of K⁺. These are the predicates required by
the Hilbert 94 engine `no_h94_extension_of_Kplus_under_VC`. -/
structure AntiKummerRealSubfieldH94Inputs
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    (pkg : SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr) where
  finiteDim : FiniteDimensional (NumberField.maximalRealSubfield K)
    (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg)
  isGalois : IsGalois (NumberField.maximalRealSubfield K)
    (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg)
  isUnramified : Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
    (𝓞 (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg))
  isCyclic : IsCyclic
    (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
        (hα₀ := hα₀) (h_irr := h_irr) pkg ≃ₐ[NumberField.maximalRealSubfield K]
      antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
        (hα₀ := hα₀) (h_irr := h_irr) pkg)
  finrank_eq_p : Module.finrank (NumberField.maximalRealSubfield K)
    (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg) = p

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **AK-4 substantive: case-I FLT data + VC + AK-3 inputs ⟹ False.** -/
theorem ak_caseI_false_under_VC_and_inputs
    (hp_odd : p ≠ 2)
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    (pkg : SigmaAntiKummerExtension (p := p) K α₀ hα₀ h_irr)
    (inputs : AntiKummerRealSubfieldH94Inputs (p := p) (K := K) pkg)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K) :
    False := by
  haveI := inputs.finiteDim
  haveI := inputs.isGalois
  haveI := inputs.isUnramified
  haveI := inputs.isCyclic
  exact no_h94_extension_of_Kplus_under_VC (p := p) (K := K) hp_odd h_VC
    (antiKummerRealSubfield (p := p) (K := K) (α₀ := α₀)
      (hα₀ := hα₀) (h_irr := h_irr) pkg)
    inputs.finrank_eq_p

/-- **`antiKummerLiftTwisted`**: same underlying type as `antiKummerLift α₀`,
but with K-algebra structure twisted by `IsCMField.complexConj`. -/
def antiKummerLiftTwisted (α₀ : K) (hα₀ : α₀ ≠ 0) : Type :=
  antiKummerLift (p := p) K α₀ hα₀

noncomputable instance antiKummerLiftTwisted_commRing
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    CommRing (antiKummerLiftTwisted (p := p) K α₀ hα₀) :=
  inferInstanceAs (CommRing (antiKummerLift (p := p) K α₀ hα₀))

noncomputable instance antiKummerLiftTwisted_field
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    Field (antiKummerLiftTwisted (p := p) K α₀ hα₀) :=
  inferInstanceAs (Field (antiKummerLift (p := p) K α₀ hα₀))

/-- **Twisted K-algebra structure** on `antiKummerLiftTwisted`: the
algebra map is `algMap K (antiKummerLift α₀) ∘ complexConj`. -/
noncomputable instance antiKummerLiftTwisted_algebra_K
    {α₀ : K} {hα₀ : α₀ ≠ 0} :
    Algebra K (antiKummerLiftTwisted (p := p) K α₀ hα₀) :=
  Algebra.compHom (antiKummerLift (p := p) K α₀ hα₀)
    (NumberField.IsCMField.complexConj K).toAlgHom.toRingHom

end AntiKummer

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
