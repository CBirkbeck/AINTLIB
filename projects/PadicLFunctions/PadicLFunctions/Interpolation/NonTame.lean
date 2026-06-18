/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import PadicLFunctions.Interpolation.Branches
import PadicLFunctions.Interpolation.TameConductor

/-!
# Non-trivial tame conductors (RJW §5.2, Thm 5.7)

For `η` primitive of conductor `D > 1` coprime to `p`: the measure `μ_η` with
Mahler transform `F_η = (−1/G(η⁻¹)) ∑_c η(c)⁻¹/((1+T)ε_D^c − 1)` (an honest
element of `R⟦T⟧` since the denominators are units, TeX 1793–1798), its
moments `∫x^k μ_η = L(η,−k)` (Lem 5.9), the ψ-invariance `ψ(μ_η) = η(p)μ_η`
(Lem 5.10 — proved by the recorded ξ-free route, decomposition L5.2.4), the
unit-restricted moments (Lem 5.11), the twists `μ_θ` and `ζ_η`, and
**RJW Theorem 5.7** (`thm:nontame`, TeX 1773–1776).
-/

open PowerSeries

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

noncomputable section

namespace MeasureR

variable {p K}

omit [CompleteSpace K] [CharZero K] in
/-- L5.2.1: for `ζ` a primitive `D`-th root of unity with `p ∤ D` and
`D ∤ c`, the power series `ζ^c·(1+X) − 1` is a unit of `R⟦X⟧` (constant
coefficient `ζ^c − 1` is a unit by W3; TeX 1798). -/
theorem isUnit_root_mul_one_add_X_sub_one {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    IsUnit ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_mul, map_add, map_one, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero, mul_one]
  refine integerRing.isUnit_of_norm_eq_one ?_
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  simpa using hζK.norm_pow_sub_one_eq_one (p := p) hD hc

omit [CompleteSpace K] [CharZero K] in
/-- The Gauss sum `G(η⁻¹)` of a primitive character of conductor `D` coprime
to `p` is a unit of the integer ring (TeX 1798: "the Gauss sum is a `p`-adic
unit (indeed, we have `G(η)G(η⁻¹) = η(−1)D` and `D` is coprime to `p`)"). -/
theorem gaussSum_isUnit_of_coprime {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    IsUnit (gaussSum η⁻¹ (AddChar.zmodChar D hζ.pow_eq_one)) := by
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  refine integerRing.isUnit_of_norm_eq_one ?_
  rw [coe_gaussSum_zmodChar η hζ hζK]
  have hηK : (toFieldChar η).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff η
      (fun _ _ h => Subtype.ext h)).mpr hη
  exact norm_gaussSum_eq_one K
    ((DirichletCharacter.conductor_inv _).trans hηK) hD hζK

variable (p K)

/-- L5.2.2: the measure `μ_η` of RJW §5.2 (TeX 1793–1798): the inverse Mahler
transform of `−G(η⁻¹)⁻¹-normalised ∑_c η(c)⁻¹·((ζ^c)(1+T) − 1)⁻¹`, stated
unnormalised (multiplied through by the unit `−G(η⁻¹)`) per R5-CLEAR; the
genuinely-used object is the *family* below, with the Gauss-normalisation
carried in the statements. -/
def muEtaCleared {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D)
    {ζ : integerRing K} (_hζ : IsPrimitiveRoot ζ D) (_hD : ¬ (p : ℕ) ∣ D) :
    MeasureR K ℤ_[p] :=
  (mahlerRingEquiv p K).symm
    (-(∑ c ∈ Finset.range D,
        PowerSeries.C (η⁻¹ (c : ZMod D)) *
          Ring.inverse ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1)))

variable {p K}

omit [CharZero K] in
/-- The Mahler transform of `muEtaCleared` is the defining series `−G(η⁻¹)F_η`
(EquationFeta, TeX 1793–1795, cleared of its Gauss-sum denominator). -/
@[simp]
lemma mahlerTransform_muEtaCleared {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    mahlerTransform p K (muEtaCleared p K η hζ hD)
      = -(∑ c ∈ Finset.range D,
          PowerSeries.C (η⁻¹ (c : ZMod D)) *
            Ring.inverse ((PowerSeries.C (ζ ^ c)) * (1 + PowerSeries.X) - 1)) :=
  (mahlerRingEquiv p K).apply_symm_apply _

omit [CompleteSpace K] [CharZero K] in
/-- L5.2.6 bookkeeping: for `ζ` a primitive `D`-th root (`p ∤ D`, `D ∤ c`)
and `w` with `‖w − 1‖ < 1` (e.g. any `p`-power-order root of unity), the
product denominator `ζ^c·w·(1+T) − 1` is a unit of `R⟦T⟧`: its constant
coefficient `ζ^c·w − 1 = (ζ^c − 1) + ζ^c(w − 1)` has norm one by the
ultrametric dominance of the prime-to-`p` part. -/
theorem isUnit_root_mul_pow_one_add_X_sub_one {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c)
    {w : integerRing K} (hw : ‖((w : K)) - 1‖ < 1) :
    IsUnit ((PowerSeries.C (ζ ^ c * w)) * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K)) := by
  have hD0 : D ≠ 0 := fun h => hD (h ▸ dvd_zero _)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_mul, map_add, map_one, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, add_zero, mul_one]
  refine integerRing.isUnit_of_norm_eq_one ?_
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  have h1 : ‖(ζ : K) ^ c - 1‖ = 1 := hζK.norm_pow_sub_one_eq_one (p := p) hD hc
  have hζ1 : ‖(ζ : K) ^ c‖ = 1 :=
    norm_eq_one_of_pow_eq_one (L := K)
      (by rw [← pow_mul, mul_comm c D, pow_mul, hζK.pow_eq_one, one_pow]) hD0
  have h2 : ‖(ζ : K) ^ c * ((w : K) - 1)‖ < 1 := by
    rw [norm_mul, hζ1, one_mul]
    exact hw
  have hsplit : ((ζ ^ c * w - 1 : integerRing K) : K)
      = ((ζ : K) ^ c - 1) + (ζ : K) ^ c * ((w : K) - 1) := by
    push_cast
    ring
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [h1]; exact ne_of_gt h2), h1, max_eq_left h2.le]

/-- Ring homomorphisms commute with `Ring.inverse` at units. -/
lemma map_ring_inverse_of_isUnit {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {u : R} (hu : IsUnit u) :
    f (Ring.inverse u) = Ring.inverse (f u) := by
  have h1 := congrArg f (Ring.mul_inverse_cancel u hu)
  rw [map_mul, map_one] at h1
  exact (hu.map f).mul_left_cancel
    (h1.trans (Ring.mul_inverse_cancel _ (hu.map f)).symm)

omit [CharZero K] in
/-- The `ε^b`-line twist of `μ̃_η` has the product-root denominators
(L5.2.6's CRT bookkeeping: the `ε_{p^n}`-twists multiply the `ε_D`-units
inside the `γ`s; the `c = 0` line is `0` on both sides since neither
`X` nor a norm-small denominator is invertible). -/
lemma mahlerTransform_charTwist_muEtaCleared {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {N : ℕ} {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ N)) (b : ℕ) :
    mahlerTransform p K (twist p K
        (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
        (muEtaCleared p K η hζ hD))
      = -(∑ c ∈ Finset.range D,
          PowerSeries.C (η⁻¹ (c : ZMod D)) *
            Ring.inverse (PowerSeries.C (ζ ^ c * ε ^ b)
              * (1 + PowerSeries.X) - 1)) := by
  rw [mahlerTransform_charTwist_eq_substAffine, mahlerTransform_muEtaCleared,
    map_neg, map_sum, neg_inj]
  refine Finset.sum_congr rfl fun c hcr => ?_
  rw [map_mul, substAffine_C]
  congr 1
  have himage : substAffine (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b)
      (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1)
      = PowerSeries.C (ζ ^ c * ε ^ b) * (1 + PowerSeries.X) - 1 := by
    rw [map_sub, map_mul, map_one, substAffine_C, substAffine_one_add_X,
      show (1 + (ε ^ b - 1) : integerRing K) = ε ^ b from by ring, map_mul]
    ring
  rcases eq_or_ne c 0 with rfl | hc0
  · -- both inverses vanish: `X` and the norm-small denominator are non-units
    rw [show Ring.inverse (PowerSeries.C ((ζ : integerRing K) ^ 0)
          * (1 + PowerSeries.X) - 1) = (0 : PowerSeries (integerRing K)) from by
        rw [pow_zero, map_one, one_mul]
        exact Ring.inverse_non_unit _ (by
          rw [PowerSeries.isUnit_iff_constantCoeff]
          simp only [map_sub, map_add, map_one, PowerSeries.constantCoeff_X,
            add_zero, sub_self]
          exact not_isUnit_zero),
      map_zero]
    refine (Ring.inverse_non_unit _ ?_).symm
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp only [map_sub, map_mul, map_add, map_one, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, add_zero, mul_one, pow_zero, one_mul]
    refine integerRing.not_isUnit_of_norm_lt_one ?_
    simpa using norm_pow_sub_one_lt_one hε b
  · have hcd : ¬ D ∣ c :=
      fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.mp hcr))
    rw [map_ring_inverse_of_isUnit _ (isUnit_root_mul_one_add_X_sub_one hζ hD hcd),
      himage]

omit [CompleteSpace K] in
/-- L5.2.3 step 1 (abstract denominator): the unit identity
`(w(1+T)−1)·(w(1+T)−1)⁻¹ = 1` transported to `K⟦t⟧` by the coefficient
inclusion and the substitution `T = e^t − 1`: `(w·e^t − 1)·G_w = 1`. -/
lemma unit_denom_exp_identity {w : integerRing K}
    (hw : IsUnit (PowerSeries.C w * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K))) :
    (PowerSeries.C ((w : K)) * PowerSeries.exp K - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C w * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = 1 := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hX : (PowerSeries.substAlgHom hg) (PowerSeries.X : PowerSeries K)
      = PowerSeries.exp K - 1 := by
    rw [show ⇑(PowerSeries.substAlgHom hg)
        = PowerSeries.subst (PowerSeries.exp K - 1) from
      PowerSeries.coe_substAlgHom hg]
    exact PowerSeries.subst_X hg
  have hC : ∀ x : K, (PowerSeries.substAlgHom hg) (PowerSeries.C x)
      = PowerSeries.C x := fun x => (PowerSeries.substAlgHom hg).commutes x
  have hK := congrArg (PowerSeries.map (integerRing K).subtype)
    (Ring.mul_inverse_cancel _ hw)
  simp only [map_mul, map_sub, map_add, map_one, PowerSeries.map_X,
    PowerSeries.map_C, Subring.coe_subtype] at hK
  have hsub := congrArg (PowerSeries.substAlgHom hg) hK
  simpa only [map_mul, map_sub, map_add, map_one, hX, hC,
    show (1 : PowerSeries K) + (PowerSeries.exp K - 1) = PowerSeries.exp K
      by ring,
    PowerSeries.coe_substAlgHom hg] using hsub

omit [CompleteSpace K] in
/-- L5.2.3 step 1, the `μ_η`-instance: `(ζ^c·e^t − 1)·G_c = 1`. -/
lemma muEta_term_exp_identity {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    (PowerSeries.C ((ζ : K) ^ c) * PowerSeries.exp K - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = 1 := by
  have h := unit_denom_exp_identity (isUnit_root_mul_one_add_X_sub_one hζ hD hc)
  simpa only [SubmonoidClass.coe_pow] using h

omit [CompleteSpace K] in
/-- L5.2.3 step 2 (abstract denominator): clearing `e^{Mt} − 1` against
`G_w` recovers the geometric numerator `Σ_{j<M} w^j·e^{jt}`, for any
`M`-torsion `w` with `w(1+T) − 1` a unit. -/
lemma rescale_exp_sub_one_mul_unit_denom {w : integerRing K} {M : ℕ}
    (hwM : w ^ M = 1)
    (hw : IsUnit (PowerSeries.C w * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K))) :
    (PowerSeries.rescale ((M : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C w * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = ∑ j ∈ Finset.range M,
          PowerSeries.C ((w : K) ^ j)
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have hwK : ((w : K)) ^ M = 1 := by
    rw [← SubmonoidClass.coe_pow, hwM, OneMemClass.coe_one]
  have hx : (PowerSeries.C ((w : K)) * PowerSeries.exp K) ^ M
      = PowerSeries.rescale ((M : ℕ) : K) (PowerSeries.exp K) := by
    rw [mul_pow, ← map_pow, hwK, map_one, one_mul,
      PowerSeries.exp_pow_eq_rescale_exp]
  have hgs := geom_sum_mul (PowerSeries.C ((w : K)) * PowerSeries.exp K) M
  calc (PowerSeries.rescale ((M : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C w * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = (∑ j ∈ Finset.range M,
            (PowerSeries.C ((w : K)) * PowerSeries.exp K) ^ j)
          * ((PowerSeries.C ((w : K)) * PowerSeries.exp K - 1)
            * (PowerSeries.map (integerRing K).subtype
                (Ring.inverse (PowerSeries.C w * (1 + PowerSeries.X) - 1))).subst
                (PowerSeries.exp K - 1)) := by
        rw [← hx, ← hgs]
        ring
    _ = ∑ j ∈ Finset.range M,
          (PowerSeries.C ((w : K)) * PowerSeries.exp K) ^ j := by
        rw [unit_denom_exp_identity hw, mul_one]
    _ = ∑ j ∈ Finset.range M,
          PowerSeries.C ((w : K) ^ j)
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow, ← map_pow, PowerSeries.exp_pow_eq_rescale_exp]

omit [CompleteSpace K] in
/-- L5.2.3 step 2, the `μ_η`-instance: clearing `e^{Dt} − 1` against `G_c`
recovers `Σ_{j<D} ζ^{cj}·e^{jt}` (the formal expansion of TeX 1797 with the
denominators multiplied out). -/
lemma rescale_exp_sub_one_mul_muEta_term {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D)
    (hD : ¬ (p : ℕ) ∣ D) {c : ℕ} (hc : ¬ D ∣ c) :
    (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))).subst
            (PowerSeries.exp K - 1)
      = ∑ j ∈ Finset.range D,
          PowerSeries.C ((ζ : K) ^ (c * j))
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have h := rescale_exp_sub_one_mul_unit_denom
    (w := ζ ^ c) (M := D) (by rw [← pow_mul, mul_comm c D, pow_mul,
      hζ.pow_eq_one, one_pow])
    (isUnit_root_mul_one_add_X_sub_one hζ hD hc)
  simpa only [SubmonoidClass.coe_pow, ← pow_mul] using h

omit [CompleteSpace K] in
/-- Distributing the coefficient inclusion and the exponential substitution
over a constant multiple. -/
lemma subst_map_C_mul (w : integerRing K) (F : PowerSeries (integerRing K)) :
    (PowerSeries.map (integerRing K).subtype
        (PowerSeries.C w * F)).subst (PowerSeries.exp K - 1)
      = PowerSeries.C ((w : K))
          * (PowerSeries.map (integerRing K).subtype F).subst
              (PowerSeries.exp K - 1) := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  rw [map_mul, PowerSeries.map_C, ← PowerSeries.coe_substAlgHom hg, map_mul,
    show (PowerSeries.substAlgHom hg)
        (PowerSeries.C ((integerRing K).subtype w))
      = PowerSeries.C ((integerRing K).subtype w) from
      (PowerSeries.substAlgHom hg).commutes _,
    PowerSeries.coe_substAlgHom hg]
  rfl

omit [CompleteSpace K] in
/-- Distributing the coefficient inclusion and the exponential substitution
over a finite sum. -/
lemma subst_map_sum {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries (integerRing K)) :
    (PowerSeries.map (integerRing K).subtype
        (∑ i ∈ s, F i)).subst (PowerSeries.exp K - 1)
      = ∑ i ∈ s, (PowerSeries.map (integerRing K).subtype (F i)).subst
          (PowerSeries.exp K - 1) := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  rw [map_sum, ← PowerSeries.coe_substAlgHom hg, map_sum]

omit [CompleteSpace K] in
/-- Distributing the coefficient inclusion and the exponential substitution
over a negation. -/
lemma subst_map_neg (F : PowerSeries (integerRing K)) :
    (PowerSeries.map (integerRing K).subtype (-F)).subst
        (PowerSeries.exp K - 1)
      = -(PowerSeries.map (integerRing K).subtype F).subst
          (PowerSeries.exp K - 1) := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  rw [map_neg, ← PowerSeries.coe_substAlgHom hg, map_neg,
    PowerSeries.coe_substAlgHom hg]

/-- L5.2.3 step 3, the master identity: `X·H_η = −G(η⁻¹)·genBPS_{η_K}` in
`K⟦t⟧`, with `H_η` the exp-substituted `K`-valued Mahler transform of
`muEtaCleared` — the η⁻¹-weighted geometric numerators collapse through the
Gauss sum (modulus-`D` instance of the T509 (v-a) collapse) and the
generating-function identity T504. -/
lemma X_mul_muEtaCleared_subst {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hD : ¬ (p : ℕ) ∣ D) :
    PowerSeries.X * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
          (PowerSeries.exp K - 1)
      = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar η).genBernoulli k * (k.factorial : K)⁻¹) := by
  classical
  haveI : Fact (1 < D) := ⟨hD1⟩
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hηK : (toFieldChar η).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff η
      (fun _ _ h => Subtype.ext h)).mpr hη
  -- (1) the substituted transform as the η̄⁻¹-weighted sum of the `G_c`
  have hHsum : (PowerSeries.map (integerRing K).subtype
        (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
        (PowerSeries.exp K - 1)
      = -∑ c ∈ Finset.range D,
          PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
            * (PowerSeries.map (integerRing K).subtype
                (Ring.inverse (PowerSeries.C (ζ ^ c)
                  * (1 + PowerSeries.X) - 1))).subst
                (PowerSeries.exp K - 1) := by
    simp only [mahlerTransform_muEtaCleared η hζ hD, subst_map_neg,
      subst_map_sum, subst_map_C_mul]
    rw [neg_inj]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show (toFieldChar η)⁻¹ = toFieldChar η⁻¹ from MulChar.ringHomComp_inv η _]
    rfl
  -- (2) clear `e^{Dt} − 1` and collapse the Gauss sums
  have hclear : (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
            (PowerSeries.exp K - 1)
      = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η) ((j : ℕ) : ZMod D))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)) := by
    rw [hHsum, mul_neg, Finset.mul_sum, neg_inj]
    have hper : ∀ c ∈ Finset.range D,
        (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
            * (PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
              * (PowerSeries.map (integerRing K).subtype
                  (Ring.inverse (PowerSeries.C (ζ ^ c)
                    * (1 + PowerSeries.X) - 1))).subst
                  (PowerSeries.exp K - 1))
          = ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
                  * (ζ : K) ^ (c * j))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
      intro c hcr
      rcases eq_or_ne c 0 with rfl | hc0
      · rw [show ((0 : ℕ) : ZMod D) = 0 from Nat.cast_zero,
          (toFieldChar η)⁻¹.map_nonunit not_isUnit_zero, map_zero]
        simp
      · have hdvd : ¬ D ∣ c :=
          fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.mp hcr))
        rw [mul_left_comm, rescale_exp_sub_one_mul_muEta_term hζ hD hdvd,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    rw [Finset.sum_congr rfl hper, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, sum_inv_char_zeta_pow hηK hζK j, map_mul]
    ring
  -- (3) multiply by `X`, insert T504, cancel the regular factor
  have h504 := X_mul_sum_char_rescale_exp (K := K) hD1 (toFieldChar η)
  have hreg : (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
      ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff 1) h0
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_one] at h1
    simp only [Nat.factorial_one, Nat.cast_one, map_one, div_one, pow_one,
      if_neg one_ne_zero, sub_zero, map_zero] at h1
    exact NeZero.ne D (by simpa using h1)
  refine mul_right_cancel₀ hreg ?_
  calc PowerSeries.X * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
          (PowerSeries.exp K - 1)
        * (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
      = PowerSeries.X
          * ((PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1)
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
                (PowerSeries.exp K - 1)) := by ring
    _ = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
            (AddChar.zmodChar D hζK.pow_eq_one))
          * (PowerSeries.X * ∑ j ∈ Finset.range D,
              PowerSeries.C ((toFieldChar η) ((j : ℕ) : ZMod D))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K))) := by
        rw [hclear]
        ring
    _ = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar η).genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((D : ℕ) : K) (PowerSeries.exp K) - 1) := by
        rw [h504]
        ring

/-- L5.2.3 (RJW Lem 5.9, TeX 1801–1804): the moments of `μ_η` are the
`L`-values: `G(η⁻¹) · ∫x^k dμ_η`-cleared form,
`∫ x^k d(muEtaCleared η) = G(η⁻¹) · L(η,−k)`. -/
theorem muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) (k : ℕ) :
    ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * LvalNeg (toFieldChar η) k := by
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  -- the moment as `k!·[t^k] H_η`
  have hmom : ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
      = (k.factorial : K) * PowerSeries.coeff k
          ((PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (muEtaCleared p K η hζ hD))).subst
            (PowerSeries.exp K - 1)) := by
    rw [apply_powCM,
      show ((PowerSeries.constantCoeff ((del K)^[k] (mahlerTransform p K
          (muEtaCleared p K η hζ hD))) : integerRing K) : K)
        = PowerSeries.constantCoeff (PowerSeries.map (integerRing K).subtype
            ((del K)^[k] (mahlerTransform p K (muEtaCleared p K η hζ hD)))) from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rfl,
      map_subtype_del_iterate, constantCoeff_iterate_delField]
  -- the `(k+1)`-st coefficient of the master identity
  have hmaster := congrArg (PowerSeries.coeff (k + 1))
    (X_mul_muEtaCleared_subst hD1 hη hζ hζK hD)
  rw [PowerSeries.coeff_succ_X_mul, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk] at hmaster
  rw [hmom, hmaster, coe_gaussSum_zmodChar η hζ hζK, LvalNeg]
  have hkf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  field_simp

omit [CharZero K] in
/-- The denominator series `w·(1+T) − 1` read back through the Mahler
isomorphism is the measure `w·δ_1 − δ_0`. -/
lemma symm_denom_eq (w : integerRing K) :
    (mahlerRingEquiv p K).symm
        (PowerSeries.C w * (1 + PowerSeries.X) - 1)
      = w • dirac K ℤ_[p] 1 - 1 := by
  apply (mahlerRingEquiv p K).injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_one,
    show (mahlerRingEquiv p K) (w • dirac K ℤ_[p] 1)
      = mahlerTransform p K (w • dirac K ℤ_[p] 1) from rfl,
    mahlerTransform_smul, mahlerTransform_dirac,
    show (1 : ℤ_[p]) = ((1 : ℕ) : ℤ_[p]) from (Nat.cast_one).symm,
    binomialSeries_nat, pow_one, map_add, map_one, PowerSeries.map_X]

omit [CharZero K] in
/-- ψ of the inverse-denominator measure: `ψ(γ_m) = γ_{pm}` (decomposition
L5.2.4 steps (i)–(iii): geometric telescope, then the projection formula
`psi_phi_mul`, then cancellation of the unit `ε^{pm}δ_1 − δ_0`). -/
lemma psi_symm_inverse_denom {ζ : integerRing K} {D : ℕ}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {m : ℕ} (hm : ¬ D ∣ m) :
    psi p K ((mahlerRingEquiv p K).symm
        (Ring.inverse (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1)))
      = (mahlerRingEquiv p K).symm
          (Ring.inverse (PowerSeries.C (ζ ^ (p * m))
            * (1 + PowerSeries.X) - 1)) := by
  have hcop : Nat.Coprime D p :=
    Nat.coprime_comm.mp ((hp.out.coprime_iff_not_dvd).mpr hD)
  have hpm : ¬ D ∣ p * m := fun h => hm (hcop.dvd_of_dvd_mul_left h)
  have humA : IsUnit (PowerSeries.C (ζ ^ (p * m)) * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K)) := isUnit_root_mul_one_add_X_sub_one hζ hD hpm
  have humγ : IsUnit (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1 :
      PowerSeries (integerRing K)) := isUnit_root_mul_one_add_X_sub_one hζ hD hm
  set A : MeasureR K ℤ_[p] := (ζ ^ (p * m)) • dirac K ℤ_[p] 1 - 1 with hA
  set γ : MeasureR K ℤ_[p] := (mahlerRingEquiv p K).symm
    (Ring.inverse (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1)) with hγ
  -- (i) the geometric telescope `φ(A)·γ = Σ_{j<p} ζ^{mj}·δ_j`
  have hphiA : phi p K A
      = (ζ ^ (p * m)) • dirac K ℤ_[p] ((p : ℕ) : ℤ_[p]) - 1 := by
    rw [hA, map_sub, map_smul,
      show (1 : MeasureR K ℤ_[p]) = dirac K ℤ_[p] 0 from rfl,
      show phi p K (dirac K ℤ_[p] 1)
        = dirac K ℤ_[p] ((p : ℤ_[p]) * 1) from rfl,
      show phi p K (dirac K ℤ_[p] 0)
        = dirac K ℤ_[p] ((p : ℤ_[p]) * 0) from rfl,
      mul_one, mul_zero]
  have htel : phi p K A * γ = ∑ j ∈ Finset.range p,
      (ζ ^ (m * j)) • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p]) := by
    apply mahlerTransform_injective
    have hγtr : mahlerTransform p K γ
        = Ring.inverse (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1) :=
      (mahlerRingEquiv p K).apply_symm_apply _
    rw [mahlerTransform_mul, hphiA, mahlerTransform_sub, mahlerTransform_smul,
      mahlerTransform_dirac, binomialSeries_nat, mahlerTransform_one, hγtr,
      show mahlerTransform p K (∑ j ∈ Finset.range p,
            (ζ ^ (m * j)) • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p]))
          = ∑ j ∈ Finset.range p, PowerSeries.C (ζ ^ (m * j))
              * PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
                  (binomialSeries ℤ_[p] ((j : ℕ) : ℤ_[p])) from by
        rw [show mahlerTransform p K (∑ j ∈ Finset.range p,
              (ζ ^ (m * j)) • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p]))
            = (mahlerTransformₗ p K) (∑ j ∈ Finset.range p,
              (ζ ^ (m * j)) • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p])) from rfl,
          map_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [show (mahlerTransformₗ p K) ((ζ ^ (m * j))
                • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p]))
              = mahlerTransform p K ((ζ ^ (m * j))
                • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p])) from rfl,
            mahlerTransform_smul, mahlerTransform_dirac],
      show PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
            ((1 + PowerSeries.X) ^ p)
          = (1 + PowerSeries.X) ^ p from by
        rw [map_pow, map_add, map_one, PowerSeries.map_X]]
    have hx : PowerSeries.C (ζ ^ (p * m)) * (1 + PowerSeries.X) ^ p
        = (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X)) ^ p := by
      rw [mul_pow, ← map_pow, ← pow_mul, mul_comm m p]
    have hgs := geom_sum_mul
      (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) :
        PowerSeries (integerRing K)) p
    calc (PowerSeries.C (ζ ^ (p * m)) * (1 + PowerSeries.X) ^ p - 1)
            * Ring.inverse (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1)
        = (∑ j ∈ Finset.range p,
            (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X)) ^ j)
            * ((PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X) - 1)
              * Ring.inverse (PowerSeries.C (ζ ^ m)
                * (1 + PowerSeries.X) - 1)) := by
          rw [hx, ← hgs]
          ring
      _ = ∑ j ∈ Finset.range p,
            (PowerSeries.C (ζ ^ m) * (1 + PowerSeries.X)) ^ j := by
          rw [Ring.mul_inverse_cancel _ humγ, mul_one]
      _ = ∑ j ∈ Finset.range p, PowerSeries.C (ζ ^ (m * j))
            * PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
                (binomialSeries ℤ_[p] ((j : ℕ) : ℤ_[p])) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [binomialSeries_nat,
            show PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
                ((1 + PowerSeries.X) ^ j)
              = (1 + PowerSeries.X) ^ j from by
              rw [map_pow, map_add, map_one, PowerSeries.map_X],
            mul_pow, ← map_pow, ← pow_mul]
  -- (ii) ψ of the telescope is `δ_0 = 1`
  have hψtel : psi p K (∑ j ∈ Finset.range p,
      (ζ ^ (m * j)) • dirac K ℤ_[p] ((j : ℕ) : ℤ_[p])) = 1 := by
    rw [psi_sum, Finset.sum_eq_single 0]
    · rw [Nat.cast_zero, psi_smul, psi_dirac_zero, mul_zero, pow_zero, one_smul]
      rfl
    · intro j hj hj0
      have hju : IsUnit ((j : ℕ) : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_def]
        push_cast
        rw [Padic.norm_natCast_eq_one_iff]
        exact (hp.out.coprime_iff_not_dvd).mpr fun hdvd =>
          hj0 (Nat.eq_zero_of_dvd_of_lt hdvd (Finset.mem_range.mp hj))
      rw [psi_smul, psi_dirac_of_isUnit hju, smul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr hp.out.pos) h0
  -- (iii) cancel the unit `A`
  have hkey := psi_phi_mul A γ
  rw [htel, hψtel] at hkey
  have hAd := symm_denom_eq (p := p) (K := K) (ζ ^ (p * m))
  have hAγ : A * (mahlerRingEquiv p K).symm
      (Ring.inverse (PowerSeries.C (ζ ^ (p * m))
        * (1 + PowerSeries.X) - 1)) = 1 := by
    rw [hA, ← hAd, ← map_mul, Ring.mul_inverse_cancel _ humA, map_one]
  have hAunit : IsUnit A := by
    rw [hA, ← hAd]
    exact humA.map (mahlerRingEquiv p K).symm
  exact hAunit.mul_left_cancel (hkey.symm.trans hAγ.symm)

omit [CharZero K] in
/-- L5.2.4 (RJW Lem 5.10, TeX 1812–1813): "We have `ψ(F_η) = η(p)F_η`."
Proved by the recorded ξ-free route (decomposition L5.2.4: γ-telescope +
projection formula + reindexing `c ↦ pc` on `(ℤ/D)^×`; primitivity of `η`
is not needed). -/
theorem psi_muEtaCleared {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D}
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) :
    psi p K (muEtaCleared p K η hζ hD)
      = η ((p : ℕ) : ZMod D) • muEtaCleared p K η hζ hD := by
  classical
  haveI : Fact (1 < D) := ⟨hD1⟩
  set g : ZMod D → MeasureR K ℤ_[p] := fun x =>
    (mahlerRingEquiv p K).symm
      (Ring.inverse (PowerSeries.C (ζ ^ x.val) * (1 + PowerSeries.X) - 1))
    with hgdef
  -- μ̃ as the ZMod-indexed weighted sum of the `γ`s
  have hmu : muEtaCleared p K η hζ hD = -∑ x : ZMod D, η⁻¹ x • g x := by
    rw [muEtaCleared, map_neg, map_sum, neg_inj]
    refine Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod D)) (fun x => x.val)
      ?_ ?_ ?_ ?_ ?_
    · intro c _
      exact Finset.mem_univ _
    · intro x _
      exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro c hc
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hc)
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro c hc
      rw [show g ((c : ℕ) : ZMod D) = (mahlerRingEquiv p K).symm
            (Ring.inverse (PowerSeries.C (ζ ^ (((c : ℕ) : ZMod D)).val)
              * (1 + PowerSeries.X) - 1)) from rfl,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hc),
        ← PowerSeries.smul_eq_C_mul,
        show (mahlerRingEquiv p K).symm ((η⁻¹ ((c : ℕ) : ZMod D)) •
            Ring.inverse (PowerSeries.C (ζ ^ c) * (1 + PowerSeries.X) - 1))
          = (η⁻¹ ((c : ℕ) : ZMod D)) • (mahlerRingEquiv p K).symm
              (Ring.inverse (PowerSeries.C (ζ ^ c)
                * (1 + PowerSeries.X) - 1)) from
          map_smul (mahlerLinearEquiv p K).symm _ _]
  -- ψ acts on the family by the index shift `x ↦ p·x`
  have hred : ∀ a : ℕ, ζ ^ a = ζ ^ (a % D) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a D]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hpsig : ∀ x : ZMod D, x ≠ 0 →
      psi p K (g x) = g (((p : ℕ) : ZMod D) * x) := by
    intro x hx
    have hm : ¬ D ∣ x.val := by
      intro h
      exact hx ((ZMod.val_eq_zero x).mp
        (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt x)))
    have hval : (((p : ℕ) : ZMod D) * x).val = (p * x.val) % D := by
      rw [show ((p : ℕ) : ZMod D) * x = ((p * x.val : ℕ) : ZMod D) from by
          push_cast [ZMod.natCast_val, ZMod.cast_id]
          rfl,
        ZMod.val_natCast]
    rw [show g x = (mahlerRingEquiv p K).symm
          (Ring.inverse (PowerSeries.C (ζ ^ x.val)
            * (1 + PowerSeries.X) - 1)) from rfl,
      psi_symm_inverse_denom hζ hD hm,
      show g (((p : ℕ) : ZMod D) * x) = (mahlerRingEquiv p K).symm
          (Ring.inverse (PowerSeries.C (ζ ^ ((((p : ℕ) : ZMod D) * x).val))
            * (1 + PowerSeries.X) - 1)) from rfl,
      show ζ ^ (p * x.val) = ζ ^ ((((p : ℕ) : ZMod D) * x).val) from by
        rw [hval, ← hred]]
  -- the unit `p` reindexes the sum, twisting the weight by `η(p)`
  obtain ⟨u, hpu⟩ : IsUnit ((p : ℕ) : ZMod D) :=
    (ZMod.isUnit_iff_coprime p D).mpr ((hp.out.coprime_iff_not_dvd).mpr hD)
  have hweight : ∀ y : ZMod D,
      η⁻¹ (((u⁻¹ : (ZMod D)ˣ) : ZMod D) * y)
        = η ((p : ℕ) : ZMod D) * η⁻¹ y := by
    intro y
    rw [map_mul]
    congr 1
    rw [MulChar.inv_apply, Ring.inverse_unit u⁻¹, inv_inv, hpu]
  -- assemble: push ψ through the (negated) sum and reindex
  have hψneg : ∀ ν : MeasureR K ℤ_[p], psi p K (-ν) = -psi p K ν := fun ν => by
    rw [← zero_sub, psi_sub, psi_zero, zero_sub]
  rw [hmu, hψneg, psi_sum,
    show ∑ x : ZMod D, psi p K (η⁻¹ x • g x)
        = ∑ x : ZMod D, η⁻¹ x • g (((p : ℕ) : ZMod D) * x) from
      Finset.sum_congr rfl fun x _ => by
        rcases eq_or_ne x 0 with rfl | hx
        · rw [η⁻¹.map_nonunit not_isUnit_zero, zero_smul, psi_zero, zero_smul]
        · rw [psi_smul, hpsig x hx],
    show ∑ x : ZMod D, η⁻¹ x • g (((p : ℕ) : ZMod D) * x)
        = ∑ y : ZMod D, (η ((p : ℕ) : ZMod D) * η⁻¹ y) • g y from by
      refine Finset.sum_nbij' (fun x => ((p : ℕ) : ZMod D) * x)
        (fun y => ((u⁻¹ : (ZMod D)ˣ) : ZMod D) * y) ?_ ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_univ _
      · intro y _
        exact Finset.mem_univ _
      · intro x _
        rw [← hpu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
      · intro y _
        rw [← hpu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, one_mul]
      · intro x _
        have h1 := hweight (((p : ℕ) : ZMod D) * x)
        rw [show ((u⁻¹ : (ZMod D)ˣ) : ZMod D) * (((p : ℕ) : ZMod D) * x)
            = x from by
          rw [← hpu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, one_mul]] at h1
        rw [← h1],
    show ∑ y : ZMod D, (η ((p : ℕ) : ZMod D) * η⁻¹ y) • g y
        = η ((p : ℕ) : ZMod D) • ∑ y : ZMod D, η⁻¹ y • g y from by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => mul_smul _ _ _,
    smul_neg]

/-- L5.2.5 (RJW Lem 5.11, TeX 1831–1834): the unit-restricted moments carry
the Euler factor: `∫_{ℤ_p^×} x^k dμ_η = (1−η(p)p^k)·L(η,−k)` (cleared). -/
theorem res_units_muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) (k : ℕ) :
    ((res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD)
        (powCM p K k) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * (1 - (η ((p : ℕ) : ZMod D) : K) * (p : K) ^ k)
          * LvalNeg (toFieldChar η) k := by
  rw [res_units_eq, LinearMap.sub_apply, psi_muEtaCleared hD1 hζ hD, map_smul,
    LinearMap.smul_apply, phi_apply_powCM]
  have hcoe : ((algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ k)
      : integerRing K) : K) = (p : K) ^ k := by
    change algebraMap ℚ_[p] K ((((p : ℤ_[p]) ^ k : ℤ_[p])) : ℚ_[p]) = (p : K) ^ k
    push_cast
    rfl
  rw [show ((muEtaCleared p K η hζ hD (powCM p K k)
        - η ((p : ℕ) : ZMod D) • (algebraMap ℤ_[p] (integerRing K)
            ((p : ℤ_[p]) ^ k) * muEtaCleared p K η hζ hD (powCM p K k))
        : integerRing K) : K)
      = ((muEtaCleared p K η hζ hD (powCM p K k) : integerRing K) : K)
        - (η ((p : ℕ) : ZMod D) : K)
          * (((algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ k)
              : integerRing K) : K)
            * ((muEtaCleared p K η hζ hD (powCM p K k)
              : integerRing K) : K)) from by push_cast [smul_eq_mul]; ring,
    hcoe, muEtaCleared_moments hD1 hη hζ hD k]
  ring

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [CompleteSpace K]
  [CharZero K] in
/-- The product character `θ = η·χ` (coprime moduli `D` and `p^n`) evaluates
at naturals as the product of the component values (both sides vanish
simultaneously off the units, by coprimality on each component). -/
lemma toFieldChar_prod_natCast {D : ℕ}
    {η : DirichletCharacter (integerRing K) D}
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)) (j : ℕ) :
    (toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n))
      = (toFieldChar η) ((j : ℕ) : ZMod D)
        * (toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)) := by
  have hsplitU : IsUnit ((j : ℕ) : ZMod (D * p ^ n))
      ↔ IsUnit ((j : ℕ) : ZMod D) ∧ IsUnit ((j : ℕ) : ZMod (p ^ n)) := by
    rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime,
      ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
  change ((θ ((j : ℕ) : ZMod (D * p ^ n)) : integerRing K) : K) = _
  by_cases hj : IsUnit ((j : ℕ) : ZMod (D * p ^ n))
  · obtain ⟨u, hu⟩ := hj
    rw [hθ, MulChar.mul_apply, ← hu,
      DirichletCharacter.changeLevel_eq_cast_of_dvd η _ u,
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ _ u, hu,
      ZMod.cast_natCast (Dvd.intro _ rfl),
      ZMod.cast_natCast (Dvd.intro_left _ rfl)]
    push_cast
    rfl
  · rw [θ.map_nonunit hj]
    rcases not_and_or.mp (fun hc => hj (hsplitU.mpr hc)) with h | h
    · simp [show (toFieldChar η) ((j : ℕ) : ZMod D)
          = ((η ((j : ℕ) : ZMod D) : integerRing K) : K) from rfl, η.map_nonunit h]
    · simp [show (toFieldChar χ) ((j : ℕ) : ZMod (p ^ n))
          = ((χ ((j : ℕ) : ZMod (p ^ n)) : integerRing K) : K) from rfl,
        χ.map_nonunit h]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- For `M ≠ 0`, the rescaled exponential `e^{Mt} − 1` is a nonzero power series
over `K` (its degree-`1` coefficient is `M ≠ 0`). -/
lemma rescale_exp_sub_one_ne_zero {M : ℕ} [NeZero M] :
    (PowerSeries.rescale ((M : ℕ) : K) (PowerSeries.exp K) - 1 : PowerSeries K)
      ≠ 0 := by
  intro h0
  have h1 := congrArg (PowerSeries.coeff 1) h0
  rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_one] at h1
  simp only [Nat.factorial_one, Nat.cast_one, map_one, div_one, pow_one,
    if_neg one_ne_zero, sub_zero, map_zero] at h1
  exact NeZero.ne M (by simpa using h1)

/-- The exp-substituted `ε^b`-line of the twist of `μ̃_η`: it is the
`η̄⁻¹`-weighted sum of the substituted product-root inverses (the `K`-valued
image of `mahlerTransform_charTwist_muEtaCleared`, with `(toFieldChar η)⁻¹`
in place of `η⁻¹` via `MulChar.ringHomComp_inv`). -/
private lemma twist_subst_S_eq {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ n)) (b : ℕ) :
    (PowerSeries.map (integerRing K).subtype
        (mahlerTransform p K (twist p K
          (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
          (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1)
      = -∑ c ∈ Finset.range D,
          PowerSeries.C ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
            * (PowerSeries.map (integerRing K).subtype
                (Ring.inverse (PowerSeries.C (ζ ^ c * ε ^ b)
                  * (1 + PowerSeries.X) - 1))).subst
                (PowerSeries.exp K - 1) := by
  simp only [mahlerTransform_charTwist_muEtaCleared η hζ hD hε b,
    subst_map_neg, subst_map_sum, subst_map_C_mul]
  rw [neg_inj]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show (toFieldChar η)⁻¹ = toFieldChar η⁻¹ from
    MulChar.ringHomComp_inv η _]
  rfl

omit [CompleteSpace K] in
/-- L5.2.6 per-`(b,c)` clearing (`D ∤ c` line): clearing `e^{D·p^n·t} − 1`
against the substituted product-root inverse `G_{ζ^c·ε^b}` recovers the
geometric numerator weighted by the two character coefficients (the root
`ζ^c·ε^b` is `D·p^n`-torsion and its denominator is a unit). -/
private lemma rescale_exp_sub_one_mul_twist_term {D : ℕ} [NeZero D]
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ n))
    {b c : ℕ} (hcd : ¬ D ∣ c) (a₁ a₂ : K) :
    (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.C a₁ * (PowerSeries.C a₂
          * (PowerSeries.map (integerRing K).subtype
              (Ring.inverse (PowerSeries.C (ζ ^ c * ε ^ b)
                * (1 + PowerSeries.X) - 1))).subst
              (PowerSeries.exp K - 1)))
      = PowerSeries.C (a₁ * a₂)
        * ∑ j ∈ Finset.range (D * p ^ n),
            PowerSeries.C (((ζ : K) ^ c * (ε : K) ^ b) ^ j)
              * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have hwM : (ζ ^ c * ε ^ b) ^ (D * p ^ n) = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul,
      show c * (D * p ^ n) = D * (c * p ^ n) from by ring,
      show b * (D * p ^ n) = p ^ n * (b * D) from by ring,
      pow_mul ζ D (c * p ^ n), pow_mul ε (p ^ n) (b * D),
      hζ.pow_eq_one, hε.pow_eq_one, one_pow, one_pow, one_mul]
  have hwu : IsUnit (PowerSeries.C (ζ ^ c * ε ^ b)
      * (1 + PowerSeries.X) - 1 : PowerSeries (integerRing K)) := by
    refine isUnit_root_mul_pow_one_add_X_sub_one hζ hD hcd ?_
    simpa using norm_pow_sub_one_lt_one hε b
  have hcl := rescale_exp_sub_one_mul_unit_denom hwM hwu
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at hcl
  rw [show (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.C a₁ * (PowerSeries.C a₂
          * (PowerSeries.map (integerRing K).subtype
              (Ring.inverse (PowerSeries.C (ζ ^ c * ε ^ b)
                * (1 + PowerSeries.X) - 1))).subst
              (PowerSeries.exp K - 1)))
      = (PowerSeries.C a₁ * PowerSeries.C a₂)
        * ((PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
          * (PowerSeries.map (integerRing K).subtype
              (Ring.inverse (PowerSeries.C (ζ ^ c * ε ^ b)
                * (1 + PowerSeries.X) - 1))).subst
              (PowerSeries.exp K - 1)) from by ring,
    hcl, ← map_mul]

omit hp [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- L5.2.6 per-`j` character factorisation: the inner `(b,c)`-double sum
factors as a product of the two `K`-valued Gauss collapses (T509 (v-a) at the
coprime moduli `p^n` and `D`) times the product character `θ̃(j)`. -/
private lemma twist_char_factor_sum {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D}
    (hηK : (toFieldChar η).IsPrimitive)
    {ζ : integerRing K} (hζK : IsPrimitiveRoot ((ζ : K)) D)
    {n : ℕ} [NeZero (p ^ n)]
    {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχK : (toFieldChar χ).IsPrimitive) {ε : integerRing K}
    (hε : IsPrimitiveRoot ε (p ^ n)) (hεK : IsPrimitiveRoot ((ε : K)) (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)) (j : ℕ) :
    ∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
        PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
            * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
            * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = PowerSeries.C (((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) :
              integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one)
            * (toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have hfac : ∀ b ∈ Finset.range (p ^ n), ∀ c ∈ Finset.range D,
      (toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
          * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
          * ((ζ : K) ^ c * (ε : K) ^ b) ^ j
        = ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n)) * (ε : K) ^ (b * j))
          * ((toFieldChar η)⁻¹ ((c : ℕ) : ZMod D) * (ζ : K) ^ (c * j)) := by
    intro b _ c _
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring
  calc ∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
        PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
            * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
            * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = PowerSeries.C ((∑ b ∈ Finset.range (p ^ n),
            (toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n)) * (ε : K) ^ (b * j))
          * ∑ c ∈ Finset.range D,
            (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D) * (ζ : K) ^ (c * j))
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
        rw [Finset.sum_mul_sum, map_sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hfac b hb c hc]
    _ = PowerSeries.C (((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) :
              integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one)
            * (toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
        rw [sum_inv_char_zeta_pow hχK hεK j, sum_inv_char_zeta_pow hηK hζK j,
          coe_gaussSum_zmodChar χ hε hεK, toFieldChar_prod_natCast hθ j]
        ring_nf

/-- L5.2.6 step (A), the `G(χ⁻¹)`-smearing (T508): the substituted `K`-valued
Mahler transform of the twist `μ_θ`, scaled by `G(χ⁻¹)`, is the
`χ̃⁻¹`-weighted sum of its `ε^b`-lines. -/
private lemma twist_subst_gaussSum_smear {D : ℕ} [NeZero D]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} [NeZero (p ^ n)]
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ n)) :
    PowerSeries.C (((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) :
            integerRing K) : K))
        * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (twist p K χ.toContinuousMapZp
            (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1)
      = ∑ b ∈ Finset.range (p ^ n),
          PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n)))
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (twist p K
                  (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
                  (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1) := by
  have h508 := mahler_twist_formula hχ hε (muEtaCleared p K η hζ hD)
  have htr : PowerSeries.C (gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one))
        * mahlerTransform p K
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))
      = ∑ b ∈ Finset.range (p ^ n),
          PowerSeries.C (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)))
            * mahlerTransform p K (twist p K
              (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
              (muEtaCleared p K η hζ hD)) := by
    rw [← mahlerTransform_smul, h508,
      show mahlerTransform p K (∑ b ∈ Finset.range (p ^ n),
            χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) • twist p K
              (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
              (muEtaCleared p K η hζ hD))
          = (mahlerTransformₗ p K) (∑ b ∈ Finset.range (p ^ n),
            χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) • twist p K
              (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
              (muEtaCleared p K η hζ hD)) from rfl,
      map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (mahlerTransformₗ p K) (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) • twist p K
          (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
          (muEtaCleared p K η hζ hD))
        = mahlerTransform p K (χ⁻¹ ((b : ℕ) : ZMod (p ^ n)) • twist p K
          (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
          (muEtaCleared p K η hζ hD)) from rfl,
      mahlerTransform_smul]
  have h1 := congrArg (fun F => (PowerSeries.map (integerRing K).subtype
      F).subst (PowerSeries.exp K - 1)) htr
  simp only [subst_map_C_mul, subst_map_sum] at h1
  refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [show (toFieldChar χ)⁻¹ = toFieldChar χ⁻¹ from MulChar.ringHomComp_inv χ _]
  rfl

/-- L5.2.6 step (B), per-`ε^b`-line: clearing `e^{D·p^n·t} − 1` against the
`a`-scaled substituted `ε^b`-line of the twist gives the `η̄⁻¹`-weighted sum of
the `(b,c)` geometric numerators (the `c = 0` term vanishes; the `D ∤ c`
terms come from `rescale_exp_sub_one_mul_twist_term`). -/
private lemma rescale_exp_sub_one_mul_twist_line {D : ℕ} [NeZero D] [Fact (1 < D)]
    {η : DirichletCharacter (integerRing K) D} {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ n))
    (b : ℕ) (a : K) :
    (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.C a
          * (PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K
                (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
                (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1))
      = -∑ c ∈ Finset.range D,
          PowerSeries.C (a * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
            * ∑ j ∈ Finset.range (D * p ^ n),
                PowerSeries.C (((ζ : K) ^ c * (ε : K) ^ b) ^ j)
                  * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  rw [twist_subst_S_eq hζ hD hε b, mul_neg, Finset.mul_sum, mul_neg,
    Finset.mul_sum, neg_inj]
  refine Finset.sum_congr rfl fun c hcr => ?_
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [show ((0 : ℕ) : ZMod D) = 0 from Nat.cast_zero,
      (toFieldChar η)⁻¹.map_nonunit not_isUnit_zero]
    simp
  · exact rescale_exp_sub_one_mul_twist_term hζ hD hε
      (fun h => hc0 (Nat.eq_zero_of_dvd_of_lt h (Finset.mem_range.mp hcr))) _ _

omit hp [NormedAlgebra ℚ_[p] K] [CompleteSpace K] in
/-- L5.2.6 step (B) bookkeeping: merge each `(b,c)` character coefficient into
its `j`-sum and reorder the triple sum to put `j` outermost. -/
private lemma twist_smear_reindex {D : ℕ}
    {η : DirichletCharacter (integerRing K) D}
    {ζ : integerRing K}
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    {ε : integerRing K} :
    ∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
        PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
            * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
          * ∑ j ∈ Finset.range (D * p ^ n),
              PowerSeries.C (((ζ : K) ^ c * (ε : K) ^ b) ^ j)
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = ∑ j ∈ Finset.range (D * p ^ n), ∑ b ∈ Finset.range (p ^ n),
          ∑ c ∈ Finset.range D,
            PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
                * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
              * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) := by
  have hbc : ∀ b ∈ Finset.range (p ^ n),
      ∑ c ∈ Finset.range D,
          PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
              * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
            * ∑ j ∈ Finset.range (D * p ^ n),
                PowerSeries.C (((ζ : K) ^ c * (ε : K) ^ b) ^ j)
                  * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
        = ∑ c ∈ Finset.range D, ∑ j ∈ Finset.range (D * p ^ n),
            PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
                * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
              * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) :=
    fun b _ => Finset.sum_congr rfl fun c _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl hbc,
    show ∑ b ∈ Finset.range (p ^ n), ∑ c ∈ Finset.range D,
          ∑ j ∈ Finset.range (D * p ^ n),
          PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
              * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
              * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
        = ∑ b ∈ Finset.range (p ^ n), ∑ j ∈ Finset.range (D * p ^ n),
          ∑ c ∈ Finset.range D,
          PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
              * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D)
              * ((ζ : K) ^ c * (ε : K) ^ b) ^ j)
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) from
      Finset.sum_congr rfl fun b _ => Finset.sum_comm,
    Finset.sum_comm]

/-- L5.2.6 step (B), the double collapse: clearing `e^{D·p^n·t} − 1` against the
`G(χ⁻¹)`-smeared twist (`twist_subst_gaussSum_smear`), collapsing the two
coprime Gauss sums (`twist_char_factor_sum`) line by line. -/
private lemma rescale_exp_sub_one_mul_twist_smear {D : ℕ} [NeZero D] [Fact (1 < D)]
    {η : DirichletCharacter (integerRing K) D}
    (hηK : (toFieldChar η).IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} [NeZero (p ^ n)]
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    (hχK : (toFieldChar χ).IsPrimitive) {ε : integerRing K}
    (hε : IsPrimitiveRoot ε (p ^ n)) (hεK : IsPrimitiveRoot ((ε : K)) (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)) :
    (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.C (((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) :
              integerRing K) : K))
          * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K χ.toContinuousMapZp
              (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1))
      = -(PowerSeries.C (((gaussSum χ⁻¹
              (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * ∑ j ∈ Finset.range (D * p ^ n),
              PowerSeries.C ((toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)) := by
  rw [twist_subst_gaussSum_smear hζ hD hχ hε, Finset.mul_sum]
  have hperb : ∀ b ∈ Finset.range (p ^ n),
      (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
          * (PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n)))
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (twist p K
                  (charCM (ε ^ b - 1) (tendsto_pow_pow_sub_one hε b))
                  (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1))
        = -∑ c ∈ Finset.range D,
            PowerSeries.C ((toFieldChar χ)⁻¹ ((b : ℕ) : ZMod (p ^ n))
                * (toFieldChar η)⁻¹ ((c : ℕ) : ZMod D))
              * ∑ j ∈ Finset.range (D * p ^ n),
                  PowerSeries.C (((ζ : K) ^ c * (ε : K) ^ b) ^ j)
                    * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) :=
    fun b _ => rescale_exp_sub_one_mul_twist_line hζ hD hε b _
  rw [Finset.sum_congr rfl hperb, Finset.sum_neg_distrib, twist_smear_reindex,
    neg_inj,
    show PowerSeries.C (((gaussSum χ⁻¹
            (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
          * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
        * ∑ j ∈ Finset.range (D * p ^ n),
            PowerSeries.C ((toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
              * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = ∑ j ∈ Finset.range (D * p ^ n),
          PowerSeries.C (((gaussSum χ⁻¹
              (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
              * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one)
              * (toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
            * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, ← map_mul]]
  exact Finset.sum_congr rfl fun j _ =>
    twist_char_factor_sum hηK hζK hχK hε hεK hθ j

/-- L5.2.6 step (C): multiply the smeared/cleared identity by `X`, insert T504
at level `D·p^n` (`X_mul_sum_char_rescale_exp`), and cancel the regular factor
`e^{D·p^n·t} − 1` (`rescale_exp_sub_one_ne_zero`). -/
private lemma X_mul_twist_subst_eq {D : ℕ} [NeZero D] [Fact (1 < D)]
    {η : DirichletCharacter (integerRing K) D}
    (hηK : (toFieldChar η).IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} [NeZero (p ^ n)] [NeZero (D * p ^ n)] (hM1 : 1 < D * p ^ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    (hχK : (toFieldChar χ).IsPrimitive) {ε : integerRing K}
    (hε : IsPrimitiveRoot ε (p ^ n)) (hεK : IsPrimitiveRoot ((ε : K)) (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)) :
    PowerSeries.X
        * (PowerSeries.C (((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) :
              integerRing K) : K))
          * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K χ.toContinuousMapZp
              (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1))
      = -(PowerSeries.C (((gaussSum χ⁻¹
              (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹) := by
  refine mul_right_cancel₀ (rescale_exp_sub_one_ne_zero (M := D * p ^ n)) ?_
  calc PowerSeries.X
          * (PowerSeries.C (((gaussSum χ⁻¹
                (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K))
            * (PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K χ.toContinuousMapZp
                (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1))
          * (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        = PowerSeries.X
            * ((PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
              * (PowerSeries.C (((gaussSum χ⁻¹
                  (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K))
                * (PowerSeries.map (integerRing K).subtype
                  (mahlerTransform p K (twist p K χ.toContinuousMapZp
                    (muEtaCleared p K η hζ hD)))).subst
                    (PowerSeries.exp K - 1))) := by ring
      _ = -(PowerSeries.C (((gaussSum χ⁻¹
              (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * (PowerSeries.X * ∑ j ∈ Finset.range (D * p ^ n),
              PowerSeries.C ((toFieldChar θ) ((j : ℕ) : ZMod (D * p ^ n)))
                * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K))) := by
        rw [rescale_exp_sub_one_mul_twist_smear hηK hζ hζK hD hχ hχK hε hεK hθ]
        ring
      _ = -(PowerSeries.C (((gaussSum χ⁻¹
              (AddChar.zmodChar (p ^ n) hε.pow_eq_one) : integerRing K) : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((D * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1) := by
        rw [X_mul_sum_char_rescale_exp (K := K) hM1 (toFieldChar θ)]
        ring

/-- L5.2.6, the twisted master identity (Lem 5.12 in cleared exp-substituted
form): `X·H_θ = −G(η⁻¹)·genBPS_{θ_K}` with `H_θ` the exp-substituted
`K`-valued Mahler transform of `μ_θ = (μ̃_η)_χ`. The `G(χ⁻¹)`-smearing of
the twist into `ε^b`-lines (T508), each line's product-root clearing, and
the double Gauss collapse at the two coprime moduli; both `e^{Dp^nt} − 1`
and `G(χ⁻¹)` cancel. The ambient roots `hζ`/`hε` mirror the source's
`ε_D`, `ε_{p^n}` (statement replan as in `twist_muA_moments`). -/
lemma X_mul_twist_muEtaCleared_subst {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D)
    (hζK : IsPrimitiveRoot ((ζ : K)) D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχ : χ.IsPrimitive) {ε : integerRing K}
    (hε : IsPrimitiveRoot ε (p ^ n)) (hεK : IsPrimitiveRoot ((ε : K)) (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ)) :
    PowerSeries.X * (PowerSeries.map (integerRing K).subtype
          (mahlerTransform p K (twist p K χ.toContinuousMapZp
            (muEtaCleared p K η hζ hD)))).subst
          (PowerSeries.exp K - 1)
      = -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
              (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹) := by
  classical
  haveI : Fact (1 < D) := ⟨hD1⟩
  haveI : NeZero (D * p ^ n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne D) (pow_ne_zero _ hp.out.ne_zero)⟩
  have hM1 : 1 < D * p ^ n :=
    lt_of_lt_of_le hD1 (Nat.le_mul_of_pos_right D (pow_pos hp.out.pos n))
  have hηK : (toFieldChar η).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff η
      (fun _ _ h => Subtype.ext h)).mpr hη
  have hχK : (toFieldChar χ).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff χ
      (fun _ _ h => Subtype.ext h)).mpr hχ
  -- abbreviations: the exp-substituted `K`-valued transform `H` and `G(χ⁻¹)`
  set H : PowerSeries K := (PowerSeries.map (integerRing K).subtype
      (mahlerTransform p K (twist p K χ.toContinuousMapZp
        (muEtaCleared p K η hζ hD)))).subst (PowerSeries.exp K - 1) with hHdef
  set GχR : integerRing K :=
    gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hε.pow_eq_one) with hGχR
  -- (A) smear `G(χ⁻¹)·H` into `ε^b`-lines, (B) clear `e^{Mt} − 1` and collapse
  -- the two Gauss sums, (C) multiply by `X`; then cancel the common `G(χ⁻¹)`.
  have hmain : PowerSeries.X * (PowerSeries.C ((GχR : K)) * H)
      = -(PowerSeries.C ((GχR : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹) :=
    X_mul_twist_subst_eq hηK hζ hζK hD hM1 hχ hχK hε hεK hθ
  have hGχne : ((GχR : K)) ≠ 0 := by
    rw [hGχR, coe_gaussSum_zmodChar χ hε hεK]
    exact gaussSum_inv_ne_zero hχK hεK
  have hCne : (PowerSeries.C ((GχR : K)) : PowerSeries K) ≠ 0 := fun h =>
    hGχne (by simpa using congrArg PowerSeries.constantCoeff h)
  refine mul_left_cancel₀ hCne ?_
  calc PowerSeries.C ((GχR : K)) * (PowerSeries.X * H)
      = PowerSeries.X * (PowerSeries.C ((GχR : K)) * H) := by ring
    _ = -(PowerSeries.C ((GχR : K)
            * gaussSum (toFieldChar η)⁻¹ (AddChar.zmodChar D hζK.pow_eq_one))
          * PowerSeries.mk fun k =>
              (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹) := hmain
    _ = PowerSeries.C ((GχR : K))
          * -(PowerSeries.C (gaussSum (toFieldChar η)⁻¹
                (AddChar.zmodChar D hζK.pow_eq_one))
              * PowerSeries.mk fun k =>
                  (toFieldChar θ).genBernoulli k * (k.factorial : K)⁻¹) := by
        rw [map_mul]
        ring

/-- L5.2.6, the moments of `μ_θ = (μ̃_η)_χ` (RJW TeX 1854–1856: "via a
calculation essentially identical to the cases already seen"):
`∫χ̃(x)x^m dμ̃_η = G(η⁻¹)·L(θ,−m)` (cleared). -/
theorem twist_muEtaCleared_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)}
    (hχ : χ.IsPrimitive) {ε : integerRing K}
    (hε : IsPrimitiveRoot ε (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    (m : ℕ) :
    ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)
        (powCM p K m) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * LvalNeg (toFieldChar θ) m := by
  have hζK : IsPrimitiveRoot ((ζ : K)) D :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  have hεK : IsPrimitiveRoot ((ε : K)) (p ^ n) :=
    hε.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  have hmom : ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)
        (powCM p K m) : integerRing K) : K)
      = (m.factorial : K) * PowerSeries.coeff m
          ((PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K χ.toContinuousMapZp
              (muEtaCleared p K η hζ hD)))).subst
            (PowerSeries.exp K - 1)) := by
    rw [apply_powCM,
      show ((PowerSeries.constantCoeff ((del K)^[m] (mahlerTransform p K
          (twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD))))
            : integerRing K) : K)
        = PowerSeries.constantCoeff (PowerSeries.map (integerRing K).subtype
            ((del K)^[m] (mahlerTransform p K (twist p K χ.toContinuousMapZp
              (muEtaCleared p K η hζ hD))))) from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rfl,
      map_subtype_del_iterate, constantCoeff_iterate_delField]
  have hmaster := congrArg (PowerSeries.coeff (m + 1))
    (X_mul_twist_muEtaCleared_subst hD1 hη hζ hζK hD hχ hε hεK hθ)
  rw [PowerSeries.coeff_succ_X_mul, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk] at hmaster
  rw [hmom, hmaster, coe_gaussSum_zmodChar η hζ hζK, LvalNeg]
  have hkf : ((m.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 m.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- L5.2.6/L5.2.7 (RJW Def TeX 1866–1868 + final display 1870–1873): the
χ-twisted moments of `ζ_η := x⁻¹·Res_{ℤ_p^×}(μ_η)`, in the moment form the
theorem quantifies (the `x⁻¹`-shift realised by the index shift `k ↦ k−1`):
for `χ` primitive mod `p^n` (`n ≥ 0`) and `k > 0`,
`∫ χ(x)x^k dζ_η = (1 − χη(p)p^{k−1})·L(χη, 1−k)` (cleared). The Euler factor
arises uniformly from `Res = 1 − φ∘ψ` (no case split on `n`: for `n ≥ 1` it
degenerates through `χ(p) = 0`). `hε` mirrors the source's ambient
`ε_{p^n}` (statement replan as in `twist_muA_moments`). -/
theorem zetaEta_twisted_moments {D : ℕ} [NeZero D] (hD1 : 1 < D)
    {η : DirichletCharacter (integerRing K) D} (hη : η.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ε : integerRing K} (hε : IsPrimitiveRoot ε (p ^ n))
    {θ : DirichletCharacter (integerRing K) (D * p ^ n)}
    (hθ : θ = (DirichletCharacter.changeLevel (Dvd.intro _ rfl) η)
        * (DirichletCharacter.changeLevel (Dvd.intro_left _ rfl) χ))
    {k : ℕ} (_hk : 0 < k) :
    ((twist p K χ.toContinuousMapZp
        (res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD))
        (powCM p K (k - 1)) : integerRing K) : K)
      = ((gaussSum η⁻¹ (AddChar.zmodChar D (hζ.pow_eq_one)) : integerRing K) : K)
          * (1 - (θ ((p : ℕ) : ZMod (D * p ^ n)) : K) * (p : K) ^ (k - 1))
          * LvalNeg (toFieldChar θ) (k - 1) := by
  classical
  set m : ℕ := k - 1 with hm
  -- `Res = 1 − φ∘ψ` on the applied values
  rw [show twist p K χ.toContinuousMapZp
        (res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD))
        (powCM p K m)
      = (res p K (PadicMeasure.isClopen_units p) (muEtaCleared p K η hζ hD))
          (χ.toContinuousMapZp * powCM p K m) from rfl,
    res_units_eq, LinearMap.sub_apply, psi_muEtaCleared hD1 hζ hD, map_smul,
    LinearMap.smul_apply]
  -- the φ-term picks up the Euler factor `χ(p)·η(p)·p^m`
  have hfun : (χ.toContinuousMapZp * powCM p K m).comp
        (PadicMeasure.mulCM p (p : ℤ_[p]))
      = (χ ((p : ℕ) : ZMod (p ^ n))
          * algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m))
          • (χ.toContinuousMapZp * powCM p K m) := by
    ext x
    refine congrArg Subtype.val ?_
    change χ.toContinuousMapZp ((p : ℤ_[p]) * x)
        * algebraMap ℤ_[p] (integerRing K) (((p : ℤ_[p]) * x) ^ m)
      = (χ ((p : ℕ) : ZMod (p ^ n))
          * algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m))
        * (χ.toContinuousMapZp x
          * algebraMap ℤ_[p] (integerRing K) (x ^ m))
    rw [DirichletCharacter.toContinuousMapZp_mul, mul_pow, map_mul,
      show χ.toContinuousMapZp ((p : ℤ_[p]))
        = χ ((p : ℕ) : ZMod (p ^ n)) from by
        rw [DirichletCharacter.toContinuousMapZp_apply]
        congr 1
        exact map_natCast _ p]
    ring
  have hphi : phi p K (muEtaCleared p K η hζ hD)
        (χ.toContinuousMapZp * powCM p K m)
      = (χ ((p : ℕ) : ZMod (p ^ n))
          * algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m))
        * (muEtaCleared p K η hζ hD)
            (χ.toContinuousMapZp * powCM p K m) := by
    change (muEtaCleared p K η hζ hD)
        ((χ.toContinuousMapZp * powCM p K m).comp
          (PadicMeasure.mulCM p (p : ℤ_[p]))) = _
    rw [hfun, map_smul, smul_eq_mul]
  rw [hphi]
  -- coerce and insert the twisted moments
  have hcoe : ((algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m)
      : integerRing K) : K) = (p : K) ^ m := by
    change algebraMap ℚ_[p] K ((((p : ℤ_[p]) ^ m : ℤ_[p])) : ℚ_[p]) = (p : K) ^ m
    push_cast
    rfl
  have hmoments := twist_muEtaCleared_moments hD1 hη hζ hD hχ hε hθ m
  rw [show twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)
        (powCM p K m)
      = (muEtaCleared p K η hζ hD) (χ.toContinuousMapZp * powCM p K m)
      from rfl] at hmoments
  rw [show ((((muEtaCleared p K η hζ hD)
          (χ.toContinuousMapZp * powCM p K m)
        - η ((p : ℕ) : ZMod D)
          • ((χ ((p : ℕ) : ZMod (p ^ n))
              * algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m))
            * (muEtaCleared p K η hζ hD)
                (χ.toContinuousMapZp * powCM p K m))) : integerRing K) : K)
      = (((muEtaCleared p K η hζ hD)
            (χ.toContinuousMapZp * powCM p K m) : integerRing K) : K)
        - ((η ((p : ℕ) : ZMod D) : integerRing K) : K)
          * (((χ ((p : ℕ) : ZMod (p ^ n)) : integerRing K) : K)
            * ((algebraMap ℤ_[p] (integerRing K) ((p : ℤ_[p]) ^ m)
                : integerRing K) : K)
            * (((muEtaCleared p K η hζ hD)
                (χ.toContinuousMapZp * powCM p K m) : integerRing K) : K))
      from by push_cast [smul_eq_mul]; ring,
    hcoe, hmoments,
    show (θ ((p : ℕ) : ZMod (D * p ^ n)) : K)
      = ((η ((p : ℕ) : ZMod D) : integerRing K) : K)
        * ((χ ((p : ℕ) : ZMod (p ^ n)) : integerRing K) : K) from
      toFieldChar_prod_natCast hθ p]
  ring

omit [CompleteSpace K] [CharZero K] in
/-- The coefficient ring has enough roots of unity for the full character
dual of `(ℤ/p^n)ˣ`, given primitive `p`-power roots: the prime-to-`p` part
is the Teichmüller lift of a generator mod `p`
(`PadicInt.exists_primitiveRoot_card_sub_one`). -/
lemma hasEnoughRootsOfUnity_of_padic_roots
    (hroots : ∀ n : ℕ, ∃ ζ : integerRing K, IsPrimitiveRoot ζ (p ^ n)) (n : ℕ) :
    HasEnoughRootsOfUnity (integerRing K)
      (Monoid.exponent (ZMod (p ^ n))ˣ) := by
  classical
  set e : ℕ := Monoid.exponent (ZMod (p ^ n))ˣ with he
  set P : ℕ := p ^ n * (p - 1) with hP
  have hP0 : P ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero)
      (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  -- `e` divides `P = p^n (p − 1)`
  have heP : e ∣ P := by
    refine dvd_trans Group.exponent_dvd_card ?_
    rw [ZMod.card_units_eq_totient]
    rcases n with _ | m
    · simp
    · rw [Nat.totient_prime_pow hp.out (Nat.succ_pos m), hP]
      exact Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) dvd_rfl
  have he0 : e ≠ 0 := Monoid.exponent_ne_zero_of_finite
  -- a primitive `e`-th root, dividing down a primitive `P`-th root built as
  -- the coprime product of the `p`-power part and the Teichmüller part
  have hprim : ∃ ξ : integerRing K, IsPrimitiveRoot ξ e := by
    obtain ⟨ζ₁, hζ₁⟩ := hroots n
    obtain ⟨ω₀, hω₀⟩ := PadicInt.exists_primitiveRoot_card_sub_one p
    have hω : IsPrimitiveRoot (algebraMap ℤ_[p] (integerRing K) ω₀) (p - 1) :=
      hω₀.map_of_injective (integerRing.isometry_algebraMap p K).injective
    have hco : Nat.Coprime (p ^ n) (p - 1) := by
      refine Nat.Coprime.pow_left _ ?_
      have h1 : p - (p - 1) = 1 := by
        have h2 := hp.out.one_lt
        omega
      have h3 : p.gcd (p - 1) ∣ p - (p - 1) := Nat.dvd_sub
        (Nat.gcd_dvd_left p (p - 1)) (Nat.gcd_dvd_right p (p - 1))
      rw [h1] at h3
      exact Nat.dvd_one.mp h3
    have hcomm : Commute (ζ₁ : integerRing K)
        (algebraMap ℤ_[p] (integerRing K) ω₀) := Commute.all _ _
    have hordmul : orderOf (ζ₁ * algebraMap ℤ_[p] (integerRing K) ω₀) = P := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [← hζ₁.eq_orderOf, ← hω.eq_orderOf]; exact hco),
        ← hζ₁.eq_orderOf, ← hω.eq_orderOf]
    have hξ : IsPrimitiveRoot
        (ζ₁ * algebraMap ℤ_[p] (integerRing K) ω₀) P := by
      have h := IsPrimitiveRoot.orderOf
        (ζ₁ * algebraMap ℤ_[p] (integerRing K) ω₀)
      rwa [hordmul] at h
    have hdvd : P / e ∣ P := Nat.div_dvd_of_dvd heP
    have hne : P / e ≠ 0 :=
      Nat.div_ne_zero_iff.mpr
        ⟨he0, Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) heP⟩
    have hprim' := hξ.pow_of_dvd hne hdvd
    rw [Nat.div_div_self heP hP0] at hprim'
    exact ⟨_, hprim'⟩
  exact ⟨hprim, inferInstance⟩

omit [CompleteSpace K] in
/-- L5.2.8 (determinacy, the uniqueness half of **RJW Thm 5.7**): a measure
on `ℤ_p` supported on the units and killing every `χ(x)·x^k` (all primitive
`χ` of `p`-power conductor valued in `R`, all `k > 0`) is zero — provided `K`
contains enough roots of unity (hypothesis quantified per level). Recorded
design note at decomposition L5.2.8. -/
theorem eq_zero_of_twisted_moments_eq_zero
    (hroots : ∀ n : ℕ, ∃ ζ : integerRing K, IsPrimitiveRoot ζ (p ^ n))
    (μ : MeasureR K ℤ_[p])
    (hsupp : res p K (PadicMeasure.isClopen_units p) μ = μ)
    (h : ∀ (n : ℕ) (χ : DirichletCharacter (integerRing K) (p ^ n)), χ.IsPrimitive →
      ∀ k, 0 < k → twist p K χ.toContinuousMapZp μ (powCM p K k) = 0) :
    μ = 0 := by
  classical
  haveI : IsDomain (integerRing K) := inferInstance
  haveI : CharZero (integerRing K) :=
    ⟨fun a b hab => Nat.cast_injective (R := K)
      (by exact_mod_cast congrArg (Subtype.val) hab)⟩
  -- restriction is invisible: `μ(1_{ℤ_p^×}·f) = μ(f)`
  have hsuppf : ∀ f : C(ℤ_[p], integerRing K),
      μ (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f) = μ f :=
    fun f => congrArg (fun ν : MeasureR K ℤ_[p] => ν f) hsupp
  -- (B) the moments vanish for ALL `p`-power-level characters, via the
  -- primitive core (they agree on the units, and `μ` lives there)
  have hall : ∀ (n : ℕ) (χ : DirichletCharacter (integerRing K) (p ^ n))
      (k : ℕ), 0 < k → μ (χ.toContinuousMapZp * powCM p K k) = 0 := by
    intro n χ k hk
    obtain ⟨m, hmle, hcond⟩ : ∃ m, m ≤ n ∧ χ.conductor = p ^ m := by
      obtain ⟨m, hm1, hm2⟩ := (Nat.dvd_prime_pow hp.out).mp χ.conductor_dvd_level
      exact ⟨m, (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp
        (hm2 ▸ χ.conductor_dvd_level), hm2⟩
    have hft : DirichletCharacter.FactorsThrough χ (p ^ m) :=
      hcond ▸ χ.factorsThrough_conductor
    obtain ⟨hdvd, χ₀, hχeq⟩ := hft
    have hχ₀prim : χ₀.IsPrimitive := by
      refine le_antisymm
        (Nat.le_of_dvd (pow_pos hp.out.pos m) χ₀.conductor_dvd_level) ?_
      have hmem : χ₀.conductor ∈ DirichletCharacter.conductorSet χ :=
        ⟨dvd_trans χ₀.conductor_dvd_level hdvd, χ₀.primitiveCharacter, by
          rw [hχeq, DirichletCharacter.changeLevel_trans
            χ₀.primitiveCharacter χ₀.conductor_dvd_level hdvd,
            DirichletCharacter.changeLevel_primitiveCharacter]⟩
      calc p ^ m = χ.conductor := hcond.symm
        _ ≤ χ₀.conductor := Nat.sInf_le hmem
    -- the two tilde-functions agree under the unit indicator
    have hfun : charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
          * (χ.toContinuousMapZp * powCM p K k)
        = charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
          * (χ₀.toContinuousMapZp * powCM p K k) := by
      ext x
      refine congrArg Subtype.val ?_
      change Set.indicator {y : ℤ_[p] | IsUnit y} 1 x
          * (χ.toContinuousMapZp x * powCM p K k x)
        = Set.indicator {y : ℤ_[p] | IsUnit y} 1 x
          * (χ₀.toContinuousMapZp x * powCM p K k x)
      by_cases hx : IsUnit x
      · rw [hχeq,
          DirichletCharacter.toContinuousMapZp_changeLevel hmle hdvd χ₀ hx]
      · rw [Set.indicator_of_notMem (by simpa using hx), zero_mul, zero_mul]
    have h0 := h m χ₀ hχ₀prim k hk
    rw [show twist p K χ₀.toContinuousMapZp μ (powCM p K k)
        = μ (χ₀.toContinuousMapZp * powCM p K k) from rfl] at h0
    rw [← hsuppf, hfun, hsuppf]
    exact h0
  -- (C) the `x`-weighted coset indicators vanish, by character orthogonality
  have hcoset : ∀ (n : ℕ), 1 ≤ n → ∀ a : ZMod (p ^ n),
      μ (powCM p K 1
        * charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n a)) = 0 := by
    intro n hn a
    by_cases ha : IsUnit a
    · haveI := hasEnoughRootsOfUnity_of_padic_roots hroots n
      -- the orthogonality identity at the level of test functions
      have hfn : ((((p ^ n).totient : ℕ) : integerRing K))
            • (powCM p K 1 * charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n a))
          = ∑ χ : DirichletCharacter (integerRing K) (p ^ n),
              χ a⁻¹ • (χ.toContinuousMapZp * powCM p K 1) := by
        ext x
        simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply,
          ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul,
          charFnCM_apply]
        rw [show ∑ χ : DirichletCharacter (integerRing K) (p ^ n),
              χ a⁻¹ * (χ.toContinuousMapZp x * powCM p K 1 x)
            = (∑ χ : DirichletCharacter (integerRing K) (p ^ n),
                χ a⁻¹ * χ (PadicInt.toZModPow n x)) * powCM p K 1 x from by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun χ _ => by
              rw [DirichletCharacter.toContinuousMapZp_apply]
              ring,
          DirichletCharacter.sum_char_inv_mul_char_eq (integerRing K) ha
            (PadicInt.toZModPow n x)]
        by_cases hxa : PadicInt.toZModPow n x = a
        · rw [if_pos hxa.symm,
            Set.indicator_of_mem (show x ∈ {z : ℤ_[p]
              | PadicInt.toZModPow n z = a} from hxa), Pi.one_apply]
          exact congrArg Subtype.val (by ring)
        · rw [if_neg (fun hax => hxa hax.symm),
            Set.indicator_of_notMem (show x ∉ {z : ℤ_[p]
              | PadicInt.toZModPow n z = a} from hxa), zero_mul,
            mul_zero, mul_zero]
      have hμfn := congrArg μ hfn
      rw [map_smul, map_sum, smul_eq_mul] at hμfn
      have hzero : ∑ χ : DirichletCharacter (integerRing K) (p ^ n),
          μ (χ a⁻¹ • (χ.toContinuousMapZp * powCM p K 1)) = 0 := by
        refine Finset.sum_eq_zero fun χ _ => ?_
        rw [map_smul, hall n χ 1 one_pos, smul_zero]
      rw [hzero] at hμfn
      have htot : ((((p ^ n).totient : ℕ) : integerRing K)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (pow_pos hp.out.pos n)).ne'
      exact (mul_eq_zero.mp hμfn).resolve_left htot
    · -- non-unit coset: invisible to the unit-supported `μ`
      rw [← hsuppf]
      rw [show charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
            * (powCM p K 1 * charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n a))
          = 0 from ?_, map_zero]
      ext x
      refine congrArg Subtype.val ?_
      change Set.indicator {y : ℤ_[p] | IsUnit y} 1 x
          * (powCM p K 1 x * Set.indicator
              {z : ℤ_[p] | PadicInt.toZModPow n z = a} 1 x) = 0
      by_cases hxa : PadicInt.toZModPow n x = a
      · have hxu : ¬ IsUnit x := fun hx => ha (hxa ▸ hx.map _)
        rw [Set.indicator_of_notMem (by simpa using hxu), zero_mul]
      · rw [Set.indicator_of_notMem (show x ∉ {z : ℤ_[p]
            | PadicInt.toZModPow n z = a} from hxa), mul_zero, mul_zero]
  -- (D) the `x`-multiplied measure kills every locally constant function
  have hloc : ∀ Φ : LocallyConstant ℤ_[p] (integerRing K),
      μ (powCM p K 1 * Φ.toContinuousMap) = 0 := by
    intro Φ
    obtain ⟨n₀, g, hg⟩ := Φ.exists_eq_comp_toZModPow
    set n : ℕ := max n₀ 1 with hndef
    set g' : ZMod (p ^ n) → integerRing K :=
      g ∘ ZMod.castHom (pow_dvd_pow p (le_max_left n₀ 1)) (ZMod (p ^ n₀))
      with hg'def
    have hg' : ∀ x : ℤ_[p], Φ x = g' (PadicInt.toZModPow n x) := by
      intro x
      rw [hg'def]
      simp only [Function.comp_apply, ZMod.castHom_apply]
      rw [PadicInt.cast_toZModPow n₀ n (le_max_left n₀ 1), ← Function.comp_apply
        (f := g) (g := PadicInt.toZModPow n₀), ← hg]
    have hdec : powCM p K 1 * Φ.toContinuousMap
        = ∑ a : ZMod (p ^ n), g' a
            • (powCM p K 1
              * charFnCM K ℤ_[p] (isClopen_toZModPow_fiber p n a)) := by
      ext x
      simp only [ContinuousMap.mul_apply, ContinuousMap.coe_sum,
        Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
        charFnCM_apply, LocallyConstant.coe_continuousMap]
      rw [Finset.sum_eq_single (PadicInt.toZModPow n x)]
      · rw [Set.indicator_of_mem (show x ∈ {z : ℤ_[p]
            | PadicInt.toZModPow n z = PadicInt.toZModPow n x} from rfl),
          Pi.one_apply, hg' x]
        exact congrArg Subtype.val (by ring)
      · intro a _ ha
        rw [Set.indicator_of_notMem (show x ∉ {z : ℤ_[p]
            | PadicInt.toZModPow n z = a} from fun hx => ha hx.symm),
          mul_zero, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hdec, map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_smul, hcoset n (le_max_right n₀ 1) a, smul_zero]
  -- (E) conclude: the unit-inverse trick reduces `μ f` to (D) by density
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  set invU : C(ℤ_[p]ˣ, integerRing K) :=
    ⟨fun u => algebraMap ℤ_[p] (integerRing K) (PadicMeasure.invCM p u),
      ((integerRing.isometry_algebraMap p K).continuous).comp
        (map_continuous (PadicMeasure.invCM p))⟩ with hinvU
  have hinv : charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f
      = powCM p K 1 * (extendByZero p K invU * f) := by
    ext x
    refine congrArg Subtype.val ?_
    change Set.indicator {y : ℤ_[p] | IsUnit y} 1 x * f x
      = powCM p K 1 x * ((extendByZero p K invU) x * f x)
    by_cases hx : IsUnit x
    · rw [Set.indicator_of_mem (show x ∈ {y : ℤ_[p] | IsUnit y} from hx),
        Pi.one_apply]
      conv_rhs => rw [← hx.unit_spec]
      rw [extendByZero_coe_unit]
      change (1 : integerRing K) * f x
        = algebraMap ℤ_[p] (integerRing K) (((hx.unit : ℤ_[p])) ^ 1)
          * (algebraMap ℤ_[p] (integerRing K)
              (((hx.unit⁻¹ : ℤ_[p]ˣ)) : ℤ_[p]) * f x)
      rw [pow_one, ← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
    · rw [Set.indicator_of_notMem (by simpa using hx), zero_mul,
        show (extendByZero p K invU) x = 0 from dif_neg hx, zero_mul, mul_zero]
  rw [← hsuppf f, hinv]
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨Φ, hΦ⟩ := PadicMeasure.exists_locallyConstant_norm_sub_le'
    (extendByZero p K invU * f) hε
  have hΦn : ‖(extendByZero p K invU * f) - Φ.toContinuousMap‖ ≤ ε :=
    (ContinuousMap.norm_le _ hε.le).2 fun x => by simpa using hΦ x
  have hsplit : μ (powCM p K 1 * (extendByZero p K invU * f))
      = μ (powCM p K 1 * Φ.toContinuousMap)
        + μ (powCM p K 1
          * ((extendByZero p K invU * f) - Φ.toContinuousMap)) := by
    rw [← map_add]
    congr 1
    ring
  rw [dist_zero_right, hsplit, hloc Φ, zero_add]
  refine (norm_apply_le μ _).trans (le_trans ?_ hΦn)
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  have hval : ‖(powCM p K 1
      * ((extendByZero p K invU * f) - Φ.toContinuousMap)) x‖
      = ‖powCM p K 1 x‖
        * ‖((extendByZero p K invU * f) - Φ.toContinuousMap) x‖ := by
    rw [show (powCM p K 1
        * ((extendByZero p K invU * f) - Φ.toContinuousMap)) x
      = powCM p K 1 x
        * ((extendByZero p K invU * f) - Φ.toContinuousMap) x from rfl,
      AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm,
      AddSubgroupClass.coe_norm, MulMemClass.coe_mul, norm_mul]
  rw [hval]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (powCM p K 1 x).2) ?_
  exact ((extendByZero p K invU * f)
    - Φ.toContinuousMap).norm_coe_le_norm x

omit [CompleteSpace K] in
/-- **RJW Theorem 5.7, uniqueness** (TeX 1773–1776 "There exists a unique
measure"): two unit-supported measures with the same χ-twisted moments
agree. With the existence half `zetaEta_twisted_moments` this is the full
statement of the theorem. -/
theorem eq_of_twisted_moments_eq
    (hroots : ∀ n : ℕ, ∃ ζ : integerRing K, IsPrimitiveRoot ζ (p ^ n))
    (μ ν : MeasureR K ℤ_[p])
    (hμ : res p K (PadicMeasure.isClopen_units p) μ = μ)
    (hν : res p K (PadicMeasure.isClopen_units p) ν = ν)
    (h : ∀ (n : ℕ) (χ : DirichletCharacter (integerRing K) (p ^ n)),
      χ.IsPrimitive → ∀ k, 0 < k →
      twist p K χ.toContinuousMapZp μ (powCM p K k)
        = twist p K χ.toContinuousMapZp ν (powCM p K k)) :
    μ = ν := by
  have hsub := eq_zero_of_twisted_moments_eq_zero hroots (μ - ν) ?_ ?_
  · exact sub_eq_zero.mp hsub
  · refine LinearMap.ext fun f => ?_
    have h1 := congrArg (fun ρ : MeasureR K ℤ_[p] => ρ f) hμ
    have h2 := congrArg (fun ρ : MeasureR K ℤ_[p] => ρ f) hν
    change (μ - ν) (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f)
      = (μ - ν) f
    rw [LinearMap.sub_apply, LinearMap.sub_apply,
      show μ (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f) = μ f
        from h1,
      show ν (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f) = ν f
        from h2]
  · intro n χ hχ k hk
    change (μ - ν) (χ.toContinuousMapZp * powCM p K k) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact h n χ hχ k hk

end MeasureR

end

end PadicLFunctions
