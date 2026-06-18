/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.Twist
import PadicLFunctions.Interpolation.GenBernoulli
import PadicLFunctions.KubotaLeopoldt.ZetaP

/-!
# Interpolation at characters of p-power conductor (RJW Thm 5.1)

The χ-twisted moments of the §4 measures, and **RJW Theorem 5.1**
(`thm:tame conductor`, TeX 1619–1622): for `χ` primitive of conductor `p^n`
(`n ≥ 1`) and `k > 0`, `∫_{ℤ_p^×} χ(x)x^k · ζ_p = L(χ, 1−k)`. The value is
the generalised-Bernoulli expression `LvalNeg` (the analytic comparison is
quarantined in `GenBernoulliComplex.lean`); the ζ_p-pairing follows the §4
witness encoding of `PadicMeasure.kubotaLeopoldt`, with the §4 measures
crossing into the `R`-layer through `baseChange ∘ iota`.
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

noncomputable section

namespace MeasureR

variable {p K}

/-- The `K`-valued character induced by an `integerRing K`-valued one. -/
def toFieldChar {N : ℕ} (χ : DirichletCharacter (integerRing K) N) :
    DirichletCharacter K N :=
  χ.ringHomComp (integerRing K).subtype

omit [CharZero K] in
/-- T509 step (iii), the per-`c` identity (†c): the `κ_{ζ^c−1}`-twisted base
change of `μ_a` has its Mahler transform characterised by the
`substAffine`-transport of §4's `F_a`-identity:
`(ζ^{ca}(1+T)^a − 1)·𝓐(κ_{ζ^c−1}·(μ_a)_K) = S_c(geomSum a) − a`. -/
lemma charTwist_muA_mahler_identity {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    (PowerSeries.C (ζ ^ (c * a)) * (1 + PowerSeries.X) ^ a - 1)
        * mahlerTransform p K (twist p K
            (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
            (baseChange p K (PadicMeasure.muA p a)))
      = substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)
          (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
            (PadicMeasure.geomSum p a))
        - (a : PowerSeries (integerRing K)) := by
  rw [mahlerTransform_charTwist_eq_substAffine, mahlerTransform_baseChange,
    PadicMeasure.mahlerTransform_muA]
  have h4 := congrArg (PowerSeries.map (algebraMap ℤ_[p] (integerRing K)))
    (PadicMeasure.one_add_X_pow_sub_one_mul_Fa p hpa)
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
    map_natCast] at h4
  have h5 := congrArg
    (substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)) h4
  simp only [map_mul, map_sub, map_pow, map_one, map_natCast,
    substAffine_one_add_X] at h5
  rwa [show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, mul_pow, ← map_pow,
    ← pow_mul] at h5

omit [CharZero K] in
/-- The `substAffine (ζ^c−1)`-image of the base-changed geometric sum:
`S_c(Σ_{i<a}(1+X)^i) = Σ_{i<a} ζ^{ci}·(1+X)^i`. -/
lemma substAffine_map_geomSum {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) (a : ℕ) :
    substAffine (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c)
        (PowerSeries.map (algebraMap ℤ_[p] (integerRing K))
          (PadicMeasure.geomSum p a))
      = ∑ i ∈ Finset.range a,
          PowerSeries.C (ζ ^ (c * i)) * (1 + PowerSeries.X) ^ i := by
  rw [PadicMeasure.geomSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, map_add, map_one, PowerSeries.map_X, map_pow, substAffine_one_add_X,
    show (1 + (ζ ^ c - 1) : integerRing K) = ζ ^ c by ring, mul_pow, ← map_pow,
    ← pow_mul]

/-- T509 step (iv), the t-side identity (‡c): substituting `T = e^t − 1` into
the `K`-valued (†c): `(ζ^{ca}·e^{at} − 1)·H_c = Σ_{i<a} ζ^{ci}·e^{it} − a`,
with `H_c` the exp-substituted `K`-valued transform of the twisted measure. -/
lemma charTwist_muA_exp_identity {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    (PowerSeries.C ((ζ : K) ^ (c * a)) * PowerSeries.rescale (a : K)
          (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K
              (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
              (baseChange p K (PadicMeasure.muA p a))))).subst
            (PowerSeries.exp K - 1)
      = (∑ i ∈ Finset.range a,
          PowerSeries.C ((ζ : K) ^ (c * i)) * PowerSeries.rescale (i : K)
            (PowerSeries.exp K))
        - (a : PowerSeries K) := by
  have hg : PowerSeries.HasSubst (PowerSeries.exp K - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hX : (PowerSeries.substAlgHom hg) (PowerSeries.X : PowerSeries K)
      = PowerSeries.exp K - 1 := by
    rw [PowerSeries.coe_substAlgHom hg]; exact PowerSeries.subst_X hg
  have hK := congrArg (PowerSeries.map (integerRing K).subtype)
    (charTwist_muA_mahler_identity hζ c hpa)
  rw [substAffine_map_geomSum hζ c a] at hK
  simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
    map_sum, map_natCast, PowerSeries.map_C, Subring.coe_subtype] at hK
  have hC : ∀ x : K, (PowerSeries.substAlgHom hg) (PowerSeries.C x)
      = PowerSeries.C x := fun x => (PowerSeries.substAlgHom hg).commutes x
  have hsub := congrArg (PowerSeries.substAlgHom hg) hK
  simp only [map_mul, map_sub, map_pow, map_add, map_one, map_sum, map_natCast,
    hX, hC, show (1 : PowerSeries K) + (PowerSeries.exp K - 1) = PowerSeries.exp K
      by ring,
    PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coe_substAlgHom hg] at hsub
  simpa only [map_pow] using hsub

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- T509 (v-c): powers of rescaled exponentials: `(E_b)^l = E_{l·b}`. -/
lemma rescale_exp_pow (b : K) (l : ℕ) :
    (PowerSeries.rescale b (PowerSeries.exp K)) ^ l
      = PowerSeries.rescale ((l : K) * b) (PowerSeries.exp K) := by
  induction l with
  | zero =>
    simp [PowerSeries.rescale_zero, PowerSeries.constantCoeff_exp]
  | succ l ih =>
    rw [pow_succ, ih, PowerSeries.exp_mul_exp_eq_exp_add,
      show ((l : K) * b + b) = ((l + 1 : ℕ) : K) * b by push_cast; ring]

/-- T509 (v-b): the division-algorithm reindex
`Σ_{i<a}Σ_{j<N} f(i + a·j) = Σ_{m<a·N} f m`. -/
lemma sum_range_mul_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {a : ℕ} (N : ℕ) (ha : 0 < a) :
    ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range N, f (i + a * j)
      = ∑ m ∈ Finset.range (a * N), f m := by
  rw [← Finset.sum_product (s := Finset.range a) (t := Finset.range N)
    (f := fun q => f (q.1 + a * q.2))]
  refine Finset.sum_nbij' (fun q => q.1 + a * q.2) (fun m => (m % a, m / a))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq
    refine Finset.mem_range.mpr ?_
    calc i + a * j < a + a * j := Nat.add_lt_add_right hq.1 _
      _ = a * (j + 1) := by ring
      _ ≤ a * N := Nat.mul_le_mul_left a hq.2
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.mod_lt m ha, Nat.div_lt_of_lt_mul hm⟩
  · rintro ⟨i, j⟩ hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq
    refine Prod.ext ?_ ?_
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq.1]
    · simp [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt hq.1]
  · intro m _
    exact Nat.mod_add_div m a
  · intro q _
    rfl

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] in
/-- T509 (v-d): the `j`-indexed form of the generating-function identity T504
over `K` (any modulus `N > 1`): `X·Σ_{j<N} χK(j)·E_j = genBPS_χK·(E_N − 1)`
(boundary terms `j = 0` and `j = N` vanish through `χK(0) = 0`). -/
lemma X_mul_sum_char_rescale_exp {N : ℕ} [NeZero N] (hN1 : 1 < N)
    (χK : DirichletCharacter K N) :
    PowerSeries.X * ∑ j ∈ Finset.range N,
        PowerSeries.C (χK ((j : ℕ) : ZMod N))
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = (PowerSeries.mk fun k => χK.genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((N : ℕ) : K) (PowerSeries.exp K)
              - 1) := by
  haveI : Fact (1 < N) := ⟨hN1⟩
  rw [genBernoulliPowerSeries_mul χK]
  set h : ℕ → PowerSeries K := fun j =>
    χK ((j : ℕ) : ZMod N) •
      (PowerSeries.X * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K))
    with hh
  have h0 : h 0 = 0 := by
    simp only [hh, Nat.cast_zero]
    rw [χK.map_nonunit not_isUnit_zero, zero_smul]
  have hpn : h N = 0 := by
    simp only [hh]
    rw [show ((N : ℕ) : ZMod N) = 0 from ZMod.natCast_self _,
      χK.map_nonunit not_isUnit_zero, zero_smul]
  have hshift : ∑ b ∈ Finset.range N, h (b + 1)
      = ∑ j ∈ Finset.range N, h j := by
    have hs := Finset.sum_range_succ' h N
    rw [Finset.sum_range_succ, h0, hpn, add_zero, add_zero] at hs
    exact hs.symm
  calc PowerSeries.X * ∑ j ∈ Finset.range N,
        PowerSeries.C (χK ((j : ℕ) : ZMod N))
          * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K)
      = ∑ j ∈ Finset.range N, h j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hh]
        rw [PowerSeries.smul_eq_C_mul]
        ring
    _ = ∑ b ∈ Finset.range N, h (b + 1) := hshift.symm
    _ = ∑ b ∈ Finset.range N, χK ((b + 1 : ℕ) : ZMod N) •
          (PowerSeries.X * PowerSeries.rescale ((b : K) + 1)
            (PowerSeries.exp K)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hh]
        norm_num

omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] in
/-- T509 (v-a), the `K`-valued Gauss collapse (any modulus): for `χK`
primitive mod `N` and `ζ'` a primitive `N`-th root of unity in `K`,
`Σ_{c<N} χK⁻¹(c)·ζ'^{cj} = χK(j)·G(χK⁻¹)` for every `j` (the non-unit `j`
case carried by the primitive-character vanishing inside
`gaussSum_mulShift_of_isPrimitive`). -/
lemma sum_inv_char_zeta_pow {N : ℕ} [NeZero N]
    {χK : DirichletCharacter K N} (hχK : χK.IsPrimitive)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' N) (j : ℕ) :
    ∑ c ∈ Finset.range N, χK⁻¹ ((c : ℕ) : ZMod N) * ζ' ^ (c * j)
      = χK ((j : ℕ) : ZMod N)
        * gaussSum χK⁻¹ (AddChar.zmodChar N hζ'.pow_eq_one) := by
  have hχinv : χK⁻¹.IsPrimitive :=
    (DirichletCharacter.conductor_inv χK).trans hχK
  have hsum : ∑ c ∈ Finset.range N,
        χK⁻¹ ((c : ℕ) : ZMod N) * ζ' ^ (c * j)
      = gaussSum χK⁻¹ ((AddChar.zmodChar N hζ'.pow_eq_one).mulShift
          ((j : ℕ) : ZMod N)) := by
    rw [gaussSum]
    refine Finset.sum_nbij' (fun c => ((c : ℕ) : ZMod N)) (fun a => a.val)
      ?_ ?_ ?_ ?_ ?_
    · intro c _
      exact Finset.mem_univ _
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro c hc
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hc)
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro c _
      rw [AddChar.mulShift_apply, ← Nat.cast_mul,
        AddChar.zmodChar_apply' hζ'.pow_eq_one, mul_comm j c]
  rw [hsum, gaussSum_mulShift_of_isPrimitive _ hχinv, inv_inv]

/-- T509 (v-e) step 1: the (‡c) identity with the `a`-side denominator
telescoped away: `(E_{a·p^N} − 1)·H_c = (Σ_{i<a} ζ'^{ci}E_i − a)·
Σ_{j<p^N} ζ'^{caj}·E_{aj}`. -/
lemma charTwist_muA_exp_identity_cleared {ζ : integerRing K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ N)) (c : ℕ) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    (PowerSeries.rescale ((a * p ^ N : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.map (integerRing K).subtype
            (mahlerTransform p K (twist p K
              (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
              (baseChange p K (PadicMeasure.muA p a))))).subst
            (PowerSeries.exp K - 1)
      = ((∑ i ∈ Finset.range a, PowerSeries.C ((ζ : K) ^ (c * i))
            * PowerSeries.rescale ((i : ℕ) : K) (PowerSeries.exp K))
          - (a : PowerSeries K))
        * ∑ j ∈ Finset.range (p ^ N),
            PowerSeries.C ((ζ : K) ^ (c * (a * j)))
              * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K) := by
  set B : PowerSeries K := PowerSeries.C ((ζ : K) ^ (c * a))
      * PowerSeries.rescale ((a : ℕ) : K) (PowerSeries.exp K) with hB
  have hζK : ((ζ : K)) ^ (p ^ N) = 1 := by
    rw [show ((ζ : K)) ^ (p ^ N) = ((ζ ^ (p ^ N) : integerRing K) : K) by push_cast; rfl,
      hζ.pow_eq_one, OneMemClass.coe_one]
  -- the `j`-th power of the cofactor base
  have hBj : ∀ j : ℕ, B ^ j = PowerSeries.C ((ζ : K) ^ (c * (a * j)))
      * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K) := by
    intro j
    rw [hB, mul_pow, ← map_pow, ← pow_mul, rescale_exp_pow,
      show ((j : K)) * ((a : ℕ) : K) = ((a * j : ℕ) : K) by push_cast; ring,
      show c * a * j = c * (a * j) by ring]
  -- the telescope `(B − 1)·Σ_j B^j = B^{p^N} − 1 = E_{ap^N} − 1`
  have htel : (B - 1) * ∑ j ∈ Finset.range (p ^ N), B ^ j
      = PowerSeries.rescale ((a * p ^ N : ℕ) : K) (PowerSeries.exp K) - 1 := by
    rw [mul_comm, geom_sum_mul, hBj (p ^ N),
      show c * (a * p ^ N) = p ^ N * (c * a) by ring, pow_mul, hζK, one_pow, map_one,
      one_mul]
  have h := congrArg
    (· * ∑ j ∈ Finset.range (p ^ N), B ^ j) (charTwist_muA_exp_identity hζ c hpa)
  rw [← hB, mul_right_comm, htel] at h
  simpa only [hBj] using h

/-- T509 (v-e) step 2: the `χ̄⁻¹`-weighted sum of the telescoped identities,
with the inner character sums collapsed by the Gauss identity:
`(E_{ap^n} − 1)·Σ_c χ̄⁻¹(c)·H_c = G'·(Σ_{m<ap^n} χ̄(m)E_m −
χ̄(a)·a·Σ_{j<p^n} χ̄(j)·E_{aj})`. -/
lemma sum_char_inv_mul_exp_identity {n : ℕ}
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hζK : IsPrimitiveRoot ((ζ : K)) (p ^ n)) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a)
    (ha : 0 < a) :
    (PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * ∑ c ∈ Finset.range (p ^ n),
            PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
              * (PowerSeries.map (integerRing K).subtype
                  (mahlerTransform p K (twist p K
                    (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
                    (baseChange p K (PadicMeasure.muA p a))))).subst
                  (PowerSeries.exp K - 1)
      = PowerSeries.C (gaussSum (toFieldChar χ)⁻¹
            (AddChar.zmodChar (p ^ n) hζK.pow_eq_one))
          * ((∑ m ∈ Finset.range (a * p ^ n),
                PowerSeries.C ((toFieldChar χ) ((m : ℕ) : ZMod (p ^ n)))
                  * PowerSeries.rescale ((m : ℕ) : K) (PowerSeries.exp K))
            - PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
                * (a : PowerSeries K)
                * ∑ j ∈ Finset.range (p ^ n),
                    PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
                      * PowerSeries.rescale ((a * j : ℕ) : K)
                          (PowerSeries.exp K)) := by
  rw [Finset.mul_sum]
  -- per `c`: insert the telescoped identity and expand the product
  have hper : ∀ c ∈ Finset.range (p ^ n),
      (PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
          * (PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (twist p K
                  (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
                  (baseChange p K (PadicMeasure.muA p a))))).subst
                (PowerSeries.exp K - 1))
        = ∑ m ∈ Finset.range (a * p ^ n),
            PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n))
                * (ζ : K) ^ (c * m))
              * PowerSeries.rescale ((m : ℕ) : K) (PowerSeries.exp K)
          - PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
              * (a : PowerSeries K)
              * ∑ j ∈ Finset.range (p ^ n),
                  PowerSeries.C ((ζ : K) ^ (c * (a * j)))
                    * PowerSeries.rescale ((a * j : ℕ) : K)
                        (PowerSeries.exp K) := by
    intro c _
    rw [mul_left_comm, charTwist_muA_exp_identity_cleared hζ c hpa, sub_mul,
      Finset.sum_mul]
    rw [mul_sub]
    congr 1
    · -- the (i,j)-double sum reindexed to `m < a·p^n`
      rw [Finset.mul_sum]
      have hdouble : ∀ i ∈ Finset.range a,
          PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
              * ((PowerSeries.C ((ζ : K) ^ (c * i))
                  * PowerSeries.rescale ((i : ℕ) : K) (PowerSeries.exp K))
                * ∑ j ∈ Finset.range (p ^ n),
                    PowerSeries.C ((ζ : K) ^ (c * (a * j)))
                      * PowerSeries.rescale ((a * j : ℕ) : K)
                          (PowerSeries.exp K))
            = ∑ j ∈ Finset.range (p ^ n),
                PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n))
                    * (ζ : K) ^ (c * (i + a * j)))
                  * PowerSeries.rescale ((i + a * j : ℕ) : K)
                      (PowerSeries.exp K) := by
        intro i _
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ((i + a * j : ℕ) : K) = ((i : ℕ) : K) + ((a * j : ℕ) : K)
            by push_cast; ring,
          ← PowerSeries.exp_mul_exp_eq_exp_add,
          show c * (i + a * j) = c * i + c * (a * j) by ring, pow_add, map_mul,
          map_mul]
        ring
      rw [Finset.sum_congr rfl hdouble,
        sum_range_mul_eq_sum_range
          (f := fun m => PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n))
            * (ζ : K) ^ (c * m))
            * PowerSeries.rescale ((m : ℕ) : K) (PowerSeries.exp K))
          (p ^ n) ha]
    · ring
  have hχK : (toFieldChar χ).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff χ
      (fun _ _ h => Subtype.ext h)).mpr hχ
  rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
  rw [mul_sub]
  congr 1
  · -- swap the `c`-sum inside the `m`-sum and collapse
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul, ← map_sum, sum_inv_char_zeta_pow hχK hζK m, map_mul]
    ring
  · -- the `a`-side sums collapse with `χ̄(a·j) = χ̄(a)·χ̄(j)`
    have hswap : ∀ c ∈ Finset.range (p ^ n),
        PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
            * (a : PowerSeries K)
            * ∑ j ∈ Finset.range (p ^ n),
                PowerSeries.C ((ζ : K) ^ (c * (a * j)))
                  * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K)
          = ∑ j ∈ Finset.range (p ^ n),
              PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n))
                  * (ζ : K) ^ (c * (a * j)))
                * ((a : PowerSeries K)
                  * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K)) := by
      intro c _
      rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl hswap, Finset.sum_comm, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, sum_inv_char_zeta_pow hχK hζK (a * j),
      show (((a * j : ℕ)) : ZMod (p ^ n)) = ((a : ℕ) : ZMod (p ^ n))
          * ((j : ℕ) : ZMod (p ^ n)) from by push_cast; ring,
      map_mul, map_mul, map_mul]
    ring

/-- T509 (v-e), FINAL-10b — the χ-analogue of §4's `X_mul_subst_exp_Fa`:
`X·Σ_c χ̄⁻¹(c)·H_c = G'·(genBPS_χ̄ − χ̄(a)·rescale a genBPS_χ̄)`. -/
lemma X_mul_sum_char_inv_subst {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hζK : IsPrimitiveRoot ((ζ : K)) (p ^ n)) {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) :
    PowerSeries.X * ∑ c ∈ Finset.range (p ^ n),
        PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
          * (PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K
                (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
                (baseChange p K (PadicMeasure.muA p a))))).subst
              (PowerSeries.exp K - 1)
      = PowerSeries.C (gaussSum (toFieldChar χ)⁻¹
            (AddChar.zmodChar (p ^ n) hζK.pow_eq_one))
          * ((PowerSeries.mk fun k =>
                (toFieldChar χ).genBernoulli k * (k.factorial : K)⁻¹)
            - PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
                * PowerSeries.rescale ((a : ℕ) : K)
                    (PowerSeries.mk fun k =>
                      (toFieldChar χ).genBernoulli k * (k.factorial : K)⁻¹)) := by
  have ha : 0 < a := Nat.pos_of_ne_zero fun h => hpa (h ▸ dvd_zero _)
  haveI : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  -- the regular factor `E_{ap^n} − 1 ≠ 0`
  have hreg : PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1
      ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_one] at h1
    have h2 : ((a * p ^ n : ℕ) : K) = 0 := by simpa [Nat.factorial] using h1
    rw [Nat.cast_eq_zero] at h2
    exact absurd h2 (Nat.mul_ne_zero ha.ne' (pow_ne_zero n hp.out.ne_zero))
  refine mul_left_cancel₀ hreg ?_
  rw [show (PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K) - 1)
        * (PowerSeries.X * ∑ c ∈ Finset.range (p ^ n), _)
      = PowerSeries.X * ((PowerSeries.rescale ((a * p ^ n : ℕ) : K)
          (PowerSeries.exp K) - 1) * _) from mul_left_comm _ _ _,
    sum_char_inv_mul_exp_identity hχ hζ hζK hpa ha]
  -- (A): `X·Σ_{m<ap^n} χ̄(m)E_m = genBPS·(E_{ap^n} − 1)` by block-splitting
  have hA : PowerSeries.X * ∑ m ∈ Finset.range (a * p ^ n),
        PowerSeries.C ((toFieldChar χ) ((m : ℕ) : ZMod (p ^ n)))
          * PowerSeries.rescale ((m : ℕ) : K) (PowerSeries.exp K)
      = (PowerSeries.mk fun k =>
            (toFieldChar χ).genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K)
            - 1) := by
    have hsplit : ∑ m ∈ Finset.range (a * p ^ n),
          PowerSeries.C ((toFieldChar χ) ((m : ℕ) : ZMod (p ^ n)))
            * PowerSeries.rescale ((m : ℕ) : K) (PowerSeries.exp K)
        = (∑ i ∈ Finset.range (p ^ n),
            PowerSeries.C ((toFieldChar χ) ((i : ℕ) : ZMod (p ^ n)))
              * PowerSeries.rescale ((i : ℕ) : K) (PowerSeries.exp K))
          * ∑ l ∈ Finset.range a,
              (PowerSeries.rescale (((p ^ n : ℕ)) : K) (PowerSeries.exp K)) ^ l := by
      rw [show a * p ^ n = p ^ n * a by ring,
        ← sum_range_mul_eq_sum_range _ a (pow_pos hp.out.pos n)]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      rw [rescale_exp_pow,
        show ((i + p ^ n * l : ℕ) : ZMod (p ^ n)) = ((i : ℕ) : ZMod (p ^ n)) from by
          push_cast
          rw [← Nat.cast_pow, ZMod.natCast_self]
          ring,
        show ((i + p ^ n * l : ℕ) : K) = ((i : ℕ) : K) + ((l : K)) * (((p ^ n : ℕ)) : K)
          from by push_cast; ring,
        ← PowerSeries.exp_mul_exp_eq_exp_add]
      ring
    rw [hsplit, ← mul_assoc,
      X_mul_sum_char_rescale_exp (Nat.one_lt_pow (by omega) hp.out.one_lt)
        (toFieldChar χ),
      mul_assoc, mul_comm (PowerSeries.rescale (((p : ℕ) ^ n : ℕ) : K)
        (PowerSeries.exp K) - 1), geom_sum_mul, rescale_exp_pow,
      show ((a : K)) * (((p ^ n : ℕ)) : K) = ((a * p ^ n : ℕ) : K)
        by push_cast; ring]
  -- (B): the `a`-side via the `rescale a`-image of (v-d)
  have hB : PowerSeries.X
        * (PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
          * (a : PowerSeries K)
          * ∑ j ∈ Finset.range (p ^ n),
              PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
                * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K))
      = PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
          * PowerSeries.rescale ((a : ℕ) : K)
              (PowerSeries.mk fun k =>
                (toFieldChar χ).genBernoulli k * (k.factorial : K)⁻¹)
          * (PowerSeries.rescale ((a * p ^ n : ℕ) : K) (PowerSeries.exp K)
            - 1) := by
    have hres := congrArg (PowerSeries.rescale ((a : ℕ) : K))
      (X_mul_sum_char_rescale_exp (Nat.one_lt_pow (by omega) hp.out.one_lt) (toFieldChar χ))
    rw [map_mul, map_mul, map_sub, map_one, map_sum, PowerSeries.rescale_X,
      PowerSeries.rescale_rescale,
      show (((p : ℕ) ^ n : ℕ) : K) * ((a : ℕ) : K) = ((a * p ^ n : ℕ) : K)
        by push_cast; ring] at hres
    have hterm : ∀ j ∈ Finset.range (p ^ n),
        PowerSeries.rescale ((a : ℕ) : K)
            (PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
              * PowerSeries.rescale ((j : ℕ) : K) (PowerSeries.exp K))
          = PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
              * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K) := by
      intro j _
      have hresC : PowerSeries.rescale ((a : ℕ) : K)
          (PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n))))
          = PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n))) := by
        ext m
        rcases eq_or_ne m 0 with rfl | hm
        · simp
        · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hm]
      rw [map_mul, hresC, PowerSeries.rescale_rescale,
        show ((j : ℕ) : K) * ((a : ℕ) : K) = ((a * j : ℕ) : K) by push_cast; ring]
    rw [Finset.sum_congr rfl hterm] at hres
    rw [show ((a : PowerSeries K)) = PowerSeries.C ((a : ℕ) : K) from
      (map_natCast (PowerSeries.C (R := K)) a).symm,
      show PowerSeries.X * (PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
          * PowerSeries.C ((a : ℕ) : K)
          * ∑ j ∈ Finset.range (p ^ n),
              PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
                * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K))
        = PowerSeries.C ((toFieldChar χ) ((a : ℕ) : ZMod (p ^ n)))
            * (PowerSeries.C ((a : ℕ) : K) * PowerSeries.X
              * ∑ j ∈ Finset.range (p ^ n),
                  PowerSeries.C ((toFieldChar χ) ((j : ℕ) : ZMod (p ^ n)))
                    * PowerSeries.rescale ((a * j : ℕ) : K) (PowerSeries.exp K))
        from by ring,
      hres]
    ring
  -- assemble: the goal is the `C(G')`-linear combination of hA and hB
  linear_combination (PowerSeries.C (gaussSum (toFieldChar χ)⁻¹
      (AddChar.zmodChar (p ^ n) hζK.pow_eq_one))) * hA
    - (PowerSeries.C (gaussSum (toFieldChar χ)⁻¹
      (AddChar.zmodChar (p ^ n) hζK.pow_eq_one))) * hB

section fieldBridge

open PowerSeries

/-- `∂ = (1+t)·d/dt` over the coefficient field `K` (the `delQ`-analogue;
to be merged with `MeasureR.del`/`PadicMeasure.delQ` at cleanup). -/
noncomputable def delField (G : PowerSeries K) : PowerSeries K :=
  (1 + X) * PowerSeries.derivativeFun G

omit [CompleteSpace K] [CharZero K] in
lemma map_subtype_derivativeFun (F : PowerSeries (integerRing K)) :
    PowerSeries.map (integerRing K).subtype (PowerSeries.derivativeFun F)
      = PowerSeries.derivativeFun (PowerSeries.map (integerRing K).subtype F) := by
  ext n
  simp [coeff_derivativeFun]

omit [CompleteSpace K] [CharZero K] in
lemma map_subtype_del (F : PowerSeries (integerRing K)) :
    PowerSeries.map (integerRing K).subtype (del K F)
      = delField (PowerSeries.map (integerRing K).subtype F) := by
  rw [del, delField, map_mul, map_add, map_one, PowerSeries.map_X,
    map_subtype_derivativeFun]

omit [CompleteSpace K] [CharZero K] in
lemma map_subtype_del_iterate (j : ℕ) (F : PowerSeries (integerRing K)) :
    PowerSeries.map (integerRing K).subtype ((del K)^[j] F)
      = delField^[j] (PowerSeries.map (integerRing K).subtype F) := by
  induction j generalizing F with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      map_subtype_del, ih]

omit [IsUltrametricDist K] [CompleteSpace K] in
lemma hasSubst_exp_sub_one_K : HasSubst (exp K - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Chain rule for the substitution `T = e^t − 1` over `K`. -/
lemma derivativeFun_subst_exp_K (F : PowerSeries K) :
    PowerSeries.derivativeFun (F.subst (exp K - 1))
      = (delField F).subst (exp K - 1) := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hone : (1 : PowerSeries K).subst (exp K - 1) = 1 := by
    rw [← coe_substAlgHom hg, map_one]
  have hder : d⁄dX K (exp K - 1) = exp K := by
    rw [map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero]
  calc PowerSeries.derivativeFun (F.subst (exp K - 1))
      = d⁄dX K (F.subst (exp K - 1)) := rfl
    _ = (d⁄dX K F).subst (exp K - 1) * d⁄dX K (exp K - 1) :=
        derivative_subst K hg
    _ = (delField F).subst (exp K - 1) := by
        rw [hder, delField, subst_mul hg, subst_add hg, subst_X hg, hone]
        ring_nf
        rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
lemma constantCoeff_subst_exp_K (F : PowerSeries K) :
    constantCoeff (F.subst (exp K - 1)) = constantCoeff F := by
  rw [show (constantCoeff (F.subst (exp K - 1)) : K)
      = MvPowerSeries.constantCoeff (F.subst (exp K - 1)) from rfl,
    constantCoeff_subst (hasSubst_exp_sub_one_K (K := K)),
    finsum_eq_single _ 0 fun d hd => by
      have h0 : MvPowerSeries.constantCoeff (exp K - 1) = (0 : K) := by
        have h1 : PowerSeries.constantCoeff (exp K - 1) = (0 : K) := by simp
        exact h1
      rw [map_pow, h0, zero_pow hd, smul_zero]]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
lemma constantCoeff_iterate_derivativeFun_K (k : ℕ) (G : PowerSeries K) :
    constantCoeff (PowerSeries.derivativeFun^[k] G)
      = (k.factorial : K) * coeff k G := by
  induction k generalizing G with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coeff_derivativeFun, Nat.factorial_succ]
    push_cast
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(∂^k F)(0) = k!·[t^k](F(e^t−1))` over `K`. -/
lemma constantCoeff_iterate_delField (k : ℕ) (F : PowerSeries K) :
    constantCoeff (delField^[k] F)
      = (k.factorial : K) * coeff k (F.subst (exp K - 1)) := by
  induction k generalizing F with
  | zero => simp [constantCoeff_subst_exp_K, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (delField F), ← derivativeFun_subst_exp_K,
      coeff_derivativeFun, Nat.factorial_succ]
    push_cast
    ring

end fieldBridge

omit [hp : Fact p.Prime] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] in
/-- The Gauss sum of a primitive character (against a primitive additive
character) is nonzero, by `G(χ)G(χ⁻¹) = N` (any modulus). -/
lemma gaussSum_inv_ne_zero {N : ℕ} [NeZero N]
    {χK : DirichletCharacter K N} (hχK : χK.IsPrimitive)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' N) :
    gaussSum χK⁻¹ (AddChar.zmodChar N hζ'.pow_eq_one) ≠ 0 := by
  have hprim_e : (AddChar.zmodChar N hζ'.pow_eq_one).IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root _ hζ'
  have hχinv : χK⁻¹.IsPrimitive :=
    (DirichletCharacter.conductor_inv _).trans hχK
  have hmul := gaussSum_mul_gaussSum_inv hχK hprim_e
  have hne2 : gaussSum χK⁻¹ ((AddChar.zmodChar N hζ'.pow_eq_one))⁻¹ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact (Nat.cast_ne_zero.2 (NeZero.ne N)) hmul.symm
  rw [AddChar.inv_mulShift, gaussSum_mulShift_of_isPrimitive _ hχinv,
    inv_inv] at hne2
  exact right_ne_zero_of_mul hne2

omit [CompleteSpace K] [CharZero K] [NormedAlgebra ℚ_[p] K] in
/-- The `K`-coercion of the integral Gauss sum is the `K`-valued Gauss sum of
the induced character (any modulus). -/
lemma coe_gaussSum_zmodChar {N : ℕ} [NeZero N]
    (χ : DirichletCharacter (integerRing K) N) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ N) (hζK : IsPrimitiveRoot ((ζ : K)) N) :
    ((gaussSum χ⁻¹ (AddChar.zmodChar N hζ.pow_eq_one) : integerRing K) : K)
      = gaussSum (toFieldChar χ)⁻¹
          (AddChar.zmodChar N hζK.pow_eq_one) := by
  rw [gaussSum, gaussSum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  push_cast
  rw [show (toFieldChar χ)⁻¹ = toFieldChar χ⁻¹ from MulChar.ringHomComp_inv χ _,
    AddChar.zmodChar_apply, AddChar.zmodChar_apply]
  rfl

/-- T509 (v-f) transport: the `χ̄⁻¹`-weighted sum of the `H_c` is the
`K`-coerced Gauss sum times `H_χ` (T508 carried through `𝓐`, the coefficient
inclusion, and the exponential substitution). -/
lemma sum_char_inv_H_eq {n : ℕ}
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n)) {a : ℕ} :
    ∑ c ∈ Finset.range (p ^ n),
        PowerSeries.C ((toFieldChar χ)⁻¹ ((c : ℕ) : ZMod (p ^ n)))
          * (PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K
                (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
                (baseChange p K (PadicMeasure.muA p a))))).subst
              (PowerSeries.exp K - 1)
      = PowerSeries.C
          ((gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hζ.pow_eq_one)
            : integerRing K) : K)
          * (PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K χ.toContinuousMapZp
                (baseChange p K (PadicMeasure.muA p a))))).subst
              (PowerSeries.exp K - 1) := by
  have hg := hasSubst_exp_sub_one_K (K := K)
  have hmapsmul : ∀ (r : integerRing K) (F : PowerSeries (integerRing K)),
      PowerSeries.map (integerRing K).subtype (r • F)
        = PowerSeries.C ((r : K))
          * PowerSeries.map (integerRing K).subtype F := by
    intro r F
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, smul_eq_mul]
    rfl
  have hsubC : ∀ (x : K) (F : PowerSeries K),
      (PowerSeries.C x * F).subst (PowerSeries.exp K - 1)
        = PowerSeries.C x * F.subst (PowerSeries.exp K - 1) := by
    intro x F
    rw [← PowerSeries.coe_substAlgHom hg, map_mul]
    simp only [show ∀ y : K, (PowerSeries.substAlgHom hg) (PowerSeries.C y)
        = PowerSeries.C y from fun y => (PowerSeries.substAlgHom hg).commutes y,
      PowerSeries.coe_substAlgHom hg]
  have h508 := mahler_twist_formula hχ hζ
    (baseChange p K (PadicMeasure.muA p a))
  -- mahlerTransform of smul/sum (it is `mahlerTransformₗ` as a linear map)
  have h𝓐' : gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hζ.pow_eq_one) •
        mahlerTransform p K (twist p K χ.toContinuousMapZp
          (baseChange p K (PadicMeasure.muA p a)))
      = ∑ c ∈ Finset.range (p ^ n),
          χ⁻¹ ((c : ℕ) : ZMod (p ^ n)) •
            mahlerTransform p K (twist p K
              (charCM (ζ ^ c - 1) (tendsto_pow_pow_sub_one hζ c))
              (baseChange p K (PadicMeasure.muA p a))) := by
    have h1 := congrArg (mahlerTransformₗ p K) h508
    simp only [map_smul, map_sum] at h1
    simpa only [show ∀ μ, mahlerTransformₗ p K μ = mahlerTransform p K μ
      from fun _ => rfl] using h1
  have hmap := congrArg (PowerSeries.map (integerRing K).subtype) h𝓐'
  rw [hmapsmul, map_sum,
    Finset.sum_congr rfl (fun c _ => hmapsmul (χ⁻¹ ((c : ℕ) : ZMod (p ^ n)))
      (mahlerTransform p K (twist p K (charCM (ζ ^ c - 1)
        (tendsto_pow_pow_sub_one hζ c))
        (baseChange p K (PadicMeasure.muA p a)))))] at hmap
  have hsub := congrArg (fun F => F.subst (PowerSeries.exp K - 1)) hmap
  rw [hsubC, show (∑ c ∈ Finset.range (p ^ n),
        PowerSeries.C (((χ⁻¹ ((c : ℕ) : ZMod (p ^ n)) : integerRing K)) : K)
          * PowerSeries.map (integerRing K).subtype
              (mahlerTransform p K (twist p K (charCM (ζ ^ c - 1)
                (tendsto_pow_pow_sub_one hζ c))
                (baseChange p K (PadicMeasure.muA p a))))).subst
        (PowerSeries.exp K - 1)
      = ∑ c ∈ Finset.range (p ^ n),
          PowerSeries.C (((χ⁻¹ ((c : ℕ) : ZMod (p ^ n)) : integerRing K)) : K)
            * (PowerSeries.map (integerRing K).subtype
                (mahlerTransform p K (twist p K (charCM (ζ ^ c - 1)
                  (tendsto_pow_pow_sub_one hζ c))
                  (baseChange p K (PadicMeasure.muA p a))))).subst
              (PowerSeries.exp K - 1) from by
      rw [← PowerSeries.coe_substAlgHom hg, map_sum]
      exact Finset.sum_congr rfl fun c _ => by
        rw [PowerSeries.coe_substAlgHom hg, hsubC]] at hsub
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hsub.symm
  congr 2
  rw [show (toFieldChar χ)⁻¹ = toFieldChar χ⁻¹ from MulChar.ringHomComp_inv χ _]
  rfl

/-- L5.1.10: the χ-twisted moments of the base-changed `μ_a` (RJW
eq:special value theorem 1, TeX 1727–1730, uniform `LvalNeg` form): for `χ`
primitive mod `p^n` (`n ≥ 1`), `a` coprime to `p`, `k : ℕ`,
`∫ χ(x)x^k dμ_a = −(1 − χ(a)·a^{k+1})·L(χ,−k)`.

The hypothesis `hζ` (a primitive `p^n`-th root of unity in the coefficient
ring) mirrors the source's ambient `ε_{p^n} ∈ Q̄_p` (TeX 1657–1660: the fixed
compatible system of `p`-power roots of unity) — recorded statement-replan:
the skeleton omitted it, but the proof route (Lem 5.4) and the source both
live over a field containing `μ_{p^n}`. -/
theorem twist_muA_moments {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) (k : ℕ) :
    ((twist p K χ.toContinuousMapZp
        (baseChange p K (PadicMeasure.muA p a)) (powCM p K k) : integerRing K) : K)
      = -(1 - (χ (a : ZMod (p ^ n)) : K) * (a : K) ^ (k + 1))
          * LvalNeg (toFieldChar χ) k := by
  have hζK : IsPrimitiveRoot ((ζ : K)) (p ^ n) :=
    hζ.map_of_injective (f := (integerRing K).subtype) fun _ _ h => Subtype.ext h
  have hχK : (toFieldChar χ).IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff χ
      (fun _ _ h => Subtype.ext h)).mpr hχ
  haveI : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  -- the Gauss sum is nonzero
  have hG'ne : gaussSum (toFieldChar χ)⁻¹
      (AddChar.zmodChar (p ^ n) hζK.pow_eq_one) ≠ 0 :=
    gaussSum_inv_ne_zero hχK hζK
  -- the moment as `k!·[t^k] H_χ`
  have hmom : ((twist p K χ.toContinuousMapZp
        (baseChange p K (PadicMeasure.muA p a)) (powCM p K k)
        : integerRing K) : K)
      = (k.factorial : K) * PowerSeries.coeff k
          ((PowerSeries.map (integerRing K).subtype (mahlerTransform p K
            (twist p K χ.toContinuousMapZp
              (baseChange p K (PadicMeasure.muA p a))))).subst
            (PowerSeries.exp K - 1)) := by
    rw [apply_powCM,
      show ((PowerSeries.constantCoeff ((del K)^[k] (mahlerTransform p K
          (twist p K χ.toContinuousMapZp (baseChange p K
            (PadicMeasure.muA p a))))) : integerRing K) : K)
        = PowerSeries.constantCoeff (PowerSeries.map (integerRing K).subtype
            ((del K)^[k] (mahlerTransform p K (twist p K χ.toContinuousMapZp
              (baseChange p K (PadicMeasure.muA p a)))))) from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rfl,
      map_subtype_del_iterate, constantCoeff_iterate_delField]
  -- the `(k+1)`-st coefficient of FINAL-10b
  have h10b := congrArg (PowerSeries.coeff (k + 1))
    (X_mul_sum_char_inv_subst hn hχ hζ hζK hpa)
  rw [PowerSeries.coeff_succ_X_mul, sum_char_inv_H_eq hχ hζ,
    coe_gaussSum_zmodChar χ hζ hζK, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
    at h10b
  have hkey := mul_left_cancel₀ hG'ne h10b
  rw [hmom, hkey, LvalNeg]
  have hk1 : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  have hkf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hfact : (((k + 1).factorial : ℕ) : K)
      = ((k + 1 : ℕ) : K) * (k.factorial : K) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [show (toFieldChar χ) ((a : ℕ) : ZMod (p ^ n))
      = ((χ ((a : ℕ) : ZMod (p ^ n)) : integerRing K) : K) from rfl] at *
  field_simp [hfact]
  rw [hfact]
  push_cast
  ring

/-- Multiplying `ι(ζ-numerator)` by `x` recovers the unit-restriction of
`μ_a` (the `x⁻¹`-shift, RJW eq. 4.11 transported through `ι`). -/
lemma cmul_powCM_one_iota_zetaNum (a : ℕ) :
    PadicMeasure.cmul p (PadicMeasure.powCM p 1)
        (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
      = PadicMeasure.res p (PadicMeasure.isClopen_units p)
          (PadicMeasure.muA p a) := by
  rw [← PadicMeasure.iota_muAUnits]
  refine LinearMap.ext fun f => ?_
  change PadicMeasure.muAUnits p a
      (PadicMeasure.invCM p
        * ((PadicMeasure.powCM p 1 * f).comp (PadicMeasure.unitsValCM p)))
    = PadicMeasure.muAUnits p a (f.comp (PadicMeasure.unitsValCM p))
  congr 1
  ext u
  change ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((u : ℤ_[p]) ^ 1 * f ((u : ℤ_[p])))
    = f ((u : ℤ_[p]))
  rw [pow_one, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- **RJW Theorem 5.1**, θ-form — the source's own engine (TeX 1757–1761:
"`∫_{ℤ_p^×}χ(x)x^k · x^{-1}μ_a = −(1−χ(a)a^k)L(χ,1−k)`"): the χ-twisted
`k`-th moment of the base change of the §4 unit-side measure
`zetaNum a = x⁻¹·Res_{ℤ_p^×}(μ_a)` is `−(1−χ(a)a^k)·L(χ,1−k)`.

`hζ` mirrors the source's ambient `ε_{p^n}` (statement replan, as in
`twist_muA_moments`). -/
theorem tame_conductor_theta {n : ℕ} (hn : 1 ≤ n)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {a : ℕ} (hpa : ¬ (p : ℕ) ∣ a) {k : ℕ} (hk : 0 < k) :
    ((baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
        (χ.toContinuousMapZp * powCM p K k) : integerRing K) : K)
      = -(1 - (χ (a : ZMod (p ^ n)) : K) * (a : K) ^ k)
          * LvalNeg (toFieldChar χ) (k - 1) := by
  -- split one power of `x` off the test function
  have hsplit : χ.toContinuousMapZp * powCM p K k
      = algCM K (PadicMeasure.powCM p 1)
        * (χ.toContinuousMapZp * powCM p K (k - 1)) := by
    ext x
    refine congrArg Subtype.val ?_
    change χ.toContinuousMapZp x * algebraMap ℤ_[p] (integerRing K) (x ^ k)
      = algebraMap ℤ_[p] (integerRing K) (x ^ 1)
        * (χ.toContinuousMapZp x * algebraMap ℤ_[p] (integerRing K) (x ^ (k - 1)))
    rw [pow_one,
      show x ^ k = x ^ (k - 1) * x from by rw [← pow_succ, Nat.sub_add_cancel hk],
      map_mul]
    ring
  -- shift through the base-changed measure and restore `μ_a`
  rw [hsplit,
    show baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
        (algCM K (PadicMeasure.powCM p 1)
          * (χ.toContinuousMapZp * powCM p K (k - 1)))
      = cmul p K (algCM K (PadicMeasure.powCM p 1))
          (baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a)))
          (χ.toContinuousMapZp * powCM p K (k - 1)) from rfl,
    ← baseChange_cmul, cmul_powCM_one_iota_zetaNum, baseChange_res]
  -- restriction is invisible to the χ-twist
  have hres : res p K (PadicMeasure.isClopen_units p)
        (baseChange p K (PadicMeasure.muA p a))
        (χ.toContinuousMapZp * powCM p K (k - 1))
      = twist p K χ.toContinuousMapZp
          (baseChange p K (PadicMeasure.muA p a)) (powCM p K (k - 1)) := by
    have hcomm : twist p K χ.toContinuousMapZp
        (res p K (PadicMeasure.isClopen_units p)
          (baseChange p K (PadicMeasure.muA p a)))
        = res p K (PadicMeasure.isClopen_units p)
            (twist p K χ.toContinuousMapZp
              (baseChange p K (PadicMeasure.muA p a))) := by
      refine LinearMap.ext fun h => ?_
      change baseChange p K (PadicMeasure.muA p a)
          (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p)
            * (χ.toContinuousMapZp * h))
        = baseChange p K (PadicMeasure.muA p a)
            (χ.toContinuousMapZp
              * (charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * h))
      congr 1
      ring
    calc res p K (PadicMeasure.isClopen_units p)
          (baseChange p K (PadicMeasure.muA p a))
          (χ.toContinuousMapZp * powCM p K (k - 1))
        = twist p K χ.toContinuousMapZp
            (res p K (PadicMeasure.isClopen_units p)
              (baseChange p K (PadicMeasure.muA p a))) (powCM p K (k - 1)) := rfl
      _ = res p K (PadicMeasure.isClopen_units p)
            (twist p K χ.toContinuousMapZp
              (baseChange p K (PadicMeasure.muA p a))) (powCM p K (k - 1)) := by
          rw [hcomm]
      _ = twist p K χ.toContinuousMapZp
            (baseChange p K (PadicMeasure.muA p a)) (powCM p K (k - 1)) := by
          rw [twist_res_units (p := p) (K := K) hn]
  rw [hres, twist_muA_moments hn hχ hζ hpa (k - 1), Nat.sub_add_cancel hk]

/-- Pushing a units-Dirac convolution through `ι` is the dilation `σ_w`. -/
lemma iota_dirac_mul (w : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure.iota p (PadicMeasure.dirac p w * μ)
      = PadicMeasure.sigma p w (PadicMeasure.iota p μ) := by
  refine LinearMap.ext fun f => ?_
  change (PadicMeasure.dirac p w * μ) (f.comp (PadicMeasure.unitsValCM p))
    = PadicMeasure.iota p μ (f.comp (PadicMeasure.mulCM p ((w : ℤ_[p]ˣ) : ℤ_[p])))
  rw [PadicMeasure.units_mul_apply, PadicMeasure.dirac_apply,
    PadicMeasure.innerInt_apply]
  rfl

omit [CharZero K] in
/-- Base change commutes with pushforward along `ℤ_p`-self-maps. -/
theorem baseChange_pushforward (h : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) :
    baseChange p K (PadicMeasure.pushforward p h μ)
      = pushforward K ℤ_[p] ℤ_[p] h (baseChange p K μ) := by
  refine ext_locallyConstant fun Φ => ?_
  rw [locallyConstant_eq_sum_smul_charFn (K := K) Φ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_smul]
  congr 1
  rw [← algCM_charFn (K := K) (Φ.isLocallyConstant.isClopen_fiber v),
    show pushforward K ℤ_[p] ℤ_[p] h (baseChange p K μ)
        (algCM K (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p])))
      = baseChange p K μ ((algCM K (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p]))).comp h)
      from rfl,
    show (algCM K (LocallyConstant.charFn ℤ_[p]
        (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p]))).comp h
      = algCM K ((LocallyConstant.charFn ℤ_[p]
        (Φ.isLocallyConstant.isClopen_fiber v) : C(ℤ_[p], ℤ_[p])).comp h) from rfl,
    baseChange_algCM, baseChange_algCM]
  rfl

omit [CompleteSpace K] [CharZero K] in
/-- The character-monomial is a `w`-dilation eigenfunction:
`(χ̃·x^k)(w·x) = χ̃(w)w^k·(χ̃·x^k)(x)`. -/
lemma char_pow_comp_mulCM {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n))
    (w : ℤ_[p]ˣ) (k : ℕ) :
    (χ.toContinuousMapZp * powCM p K k).comp
        (PadicMeasure.mulCM p ((w : ℤ_[p]ˣ) : ℤ_[p]))
      = (χ.toContinuousMapZp ((w : ℤ_[p]))
          * powCM p K k ((w : ℤ_[p])))
        • (χ.toContinuousMapZp * powCM p K k) := by
  ext x
  refine congrArg Subtype.val ?_
  change χ.toContinuousMapZp ((w : ℤ_[p]) * x)
      * algebraMap ℤ_[p] (integerRing K) (((w : ℤ_[p]) * x) ^ k)
    = (χ.toContinuousMapZp ((w : ℤ_[p]))
        * algebraMap ℤ_[p] (integerRing K) ((w : ℤ_[p]) ^ k))
      * (χ.toContinuousMapZp x * algebraMap ℤ_[p] (integerRing K) (x ^ k))
  rw [DirichletCharacter.toContinuousMapZp_apply,
    DirichletCharacter.toContinuousMapZp_apply,
    DirichletCharacter.toContinuousMapZp_apply, map_mul, map_mul, mul_pow, map_mul]
  ring

/-- **RJW Theorem 5.1** (`thm:tame conductor`, TeX 1619–1622), witness form
mirroring `PadicMeasure.kubotaLeopoldt`'s encoding: for every unit `b` and
every measure-witness `ν` of `([b]−[1])·ζ_p`, the χ-twisted `k`-th moment of
`ν` (base-changed) equals `(χ(b)·b^k − 1)·L(χ, 1−k)`.

"Let χ be a (primitive) Dirichlet character of conductor `p^n` ... Then, for
`k > 0`, we have `∫_{ℤ_p^×}χ(x)x^k · ζ_p = L(χ,1−k)`."

`hζ` mirrors the source's ambient `ε_{p^n}` (statement replan, as in
`twist_muA_moments`). -/
theorem tame_conductor {n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2)
    {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive)
    {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {k : ℕ} (hk : 0 < k) (b : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (PadicMeasure.QuotientField p) (PadicMeasure.dirac p b - 1)
        * PadicMeasure.padicZeta p hp2 = algebraMap _ _ ν) :
    ((baseChange p K (PadicMeasure.iota p ν)
        (χ.toContinuousMapZp * powCM p K k) : integerRing K) : K)
      = ((χ (PadicInt.toZModPow n (b : ℤ_[p])) : K)
            * algebraMap ℚ_[p] K (((b : ℤ_[p]) : ℚ_[p]) ^ k) - 1)
          * LvalNeg (toFieldChar χ) (k - 1) := by
  classical
  obtain ⟨hpm, huv, hgen⟩ :=
    (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (PadicMeasure.exists_nat_topological_generator p hp2).choose with hm
  set u := (PadicMeasure.exists_nat_topological_generator p hp2).choose_spec.choose
    with hu
  -- the defining relation `([u]−1)·ζ_p = zetaNum m`, pulled back to `Λ(ℤ_p^×)`
  have hspec : algebraMap _ (PadicMeasure.QuotientField p)
        (PadicMeasure.dirac p u - 1) * PadicMeasure.padicZeta p hp2
      = algebraMap _ _ (PadicMeasure.zetaNum p m) := by
    rw [PadicMeasure.padicZeta]
    exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField p) _ _
  have hkey : (PadicMeasure.dirac p u - 1) * ν
      = (PadicMeasure.dirac p b - 1) * PadicMeasure.zetaNum p m := by
    apply IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ)
      (PadicMeasure.QuotientField p)
    rw [map_mul, map_mul, ← hν, ← hspec]
    ring
  -- the χ-twisted moment functional
  set Θ : PadicMeasure p ℤ_[p]ˣ → K := fun μ =>
    ((baseChange p K (PadicMeasure.iota p μ)
      (χ.toContinuousMapZp * powCM p K k) : integerRing K) : K) with hΘ
  have hΘsub : ∀ μ₁ μ₂, Θ (μ₁ - μ₂) = Θ μ₁ - Θ μ₂ := by
    intro μ₁ μ₂
    rw [hΘ]
    simp only [map_sub, LinearMap.sub_apply]
    push_cast
    ring
  have heigen : ∀ (w : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]ˣ),
      Θ (PadicMeasure.dirac p w * μ)
        = ((χ.toContinuousMapZp ((w : ℤ_[p]))
            * powCM p K k ((w : ℤ_[p])) : integerRing K) : K) * Θ μ := by
    intro w μ
    rw [hΘ]
    simp only
    rw [iota_dirac_mul,
      show PadicMeasure.sigma p w (PadicMeasure.iota p μ)
        = PadicMeasure.pushforward p (PadicMeasure.mulCM p ((w : ℤ_[p]ˣ) : ℤ_[p]))
            (PadicMeasure.iota p μ) from rfl,
      baseChange_pushforward,
      show pushforward K ℤ_[p] ℤ_[p] (PadicMeasure.mulCM p ((w : ℤ_[p]ˣ) : ℤ_[p]))
          (baseChange p K (PadicMeasure.iota p μ))
          (χ.toContinuousMapZp * powCM p K k)
        = baseChange p K (PadicMeasure.iota p μ)
            ((χ.toContinuousMapZp * powCM p K k).comp
              (PadicMeasure.mulCM p ((w : ℤ_[p]ˣ) : ℤ_[p]))) from rfl,
      char_pow_comp_mulCM, map_smul]
    push_cast [smul_eq_mul]
    ring
  -- apply `Θ` to the key relation and distribute
  have hmom := congrArg Θ hkey
  rw [sub_mul, sub_mul, one_mul, one_mul, hΘsub, hΘsub, heigen, heigen] at hmom
  -- the `c_u`-factor equals the θ-side factor
  have hcu : ((χ.toContinuousMapZp ((u : ℤ_[p]))
        * powCM p K k ((u : ℤ_[p])) : integerRing K) : K)
      = (χ ((m : ℕ) : ZMod (p ^ n)) : K) * (m : K) ^ k := by
    rw [show ((χ.toContinuousMapZp ((u : ℤ_[p]))
          * powCM p K k ((u : ℤ_[p])) : integerRing K) : K)
        = ((χ.toContinuousMapZp ((u : ℤ_[p])) : integerRing K) : K)
          * ((powCM p K k ((u : ℤ_[p])) : integerRing K) : K) from by push_cast; rfl,
      DirichletCharacter.toContinuousMapZp_apply, huv, map_natCast]
    congr 1
    change algebraMap ℚ_[p] K (((((m : ℕ) : ℤ_[p]) ^ k : ℤ_[p])) : ℚ_[p])
      = ((m : ℕ) : K) ^ k
    push_cast
    rfl
  -- value of `Θ(zetaNum m)` by the θ-form of the theorem
  have hθval : Θ (PadicMeasure.zetaNum p m)
      = -(1 - (χ ((m : ℕ) : ZMod (p ^ n)) : K) * (m : K) ^ k)
          * LvalNeg (toFieldChar χ) (k - 1) := tame_conductor_theta hn hχ hζ hpm hk
  -- nonvanishing of `c_u − 1` via the finite order of the character value
  have hne : (χ ((m : ℕ) : ZMod (p ^ n)) : K) * (m : K) ^ k - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    set N := Nat.card (ZMod (p ^ n))ˣ with hN
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have hNpos : 0 < N := Nat.card_pos
    -- `χ(m̄)^N = 1` since `m̄` is the image of the unit `u`
    have hmbar : ((m : ℕ) : ZMod (p ^ n))
        = ((PadicMeasure.unitsToZModPow p n u : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) := by
      rw [PadicMeasure.unitsToZModPow_coe, huv, map_natCast]
    have hpow1 : (((m : ℕ) : ZMod (p ^ n))) ^ N = 1 := by
      rw [hmbar, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
    have hχN : (χ ((m : ℕ) : ZMod (p ^ n)) : K) ^ N = 1 := by
      rw [show ((χ ((m : ℕ) : ZMod (p ^ n)) : integerRing K) : K) ^ N
          = ((((χ ((m : ℕ) : ZMod (p ^ n))) ^ N : integerRing K)) : K) from by
        push_cast; rfl]
      rw [← map_pow, hpow1, map_one, OneMemClass.coe_one]
    -- hence `m^{kN} = 1` in `K`, descending to `ℤ_p`
    have hmK : ((m : K)) ^ (k * N) = 1 := by
      have h2 := congrArg (· ^ N) heq
      simp only [mul_pow, one_pow] at h2
      rw [hχN, one_mul, ← pow_mul] at h2
      exact h2
    have hmQp : (((m : ℕ) : ℚ_[p])) ^ (k * N) = 1 := by
      have hinj : Function.Injective (algebraMap ℚ_[p] K) :=
        (algebraMap ℚ_[p] K).injective
      apply hinj
      rw [map_pow, map_natCast, map_one]
      exact_mod_cast hmK
    have hmZp : (((m : ℕ) : ℤ_[p])) ^ (k * N) = 1 := by
      have hcoe : ((((m : ℕ) : ℤ_[p]) ^ (k * N) : ℤ_[p]) : ℚ_[p])
          = ((1 : ℤ_[p]) : ℚ_[p]) := by
        push_cast
        exact_mod_cast hmQp
      exact Subtype.coe_injective hcoe
    have hcontra := PadicMeasure.topGen_pow_ne_one p hgen (k * N)
      (Nat.mul_pos hk hNpos)
    rw [huv] at hcontra
    exact hcontra hmZp
  -- the `c_b`-factor in the target's normal form
  have hcb : ((χ.toContinuousMapZp ((b : ℤ_[p]))
        * powCM p K k ((b : ℤ_[p])) : integerRing K) : K)
      = (χ (PadicInt.toZModPow n (b : ℤ_[p])) : K)
          * algebraMap ℚ_[p] K (((b : ℤ_[p]) : ℚ_[p]) ^ k) := by
    push_cast
    rw [DirichletCharacter.toContinuousMapZp_apply]
    congr 1
    change algebraMap ℚ_[p] K ((((b : ℤ_[p]) ^ k : ℤ_[p])) : ℚ_[p]) = _
    push_cast
    rfl
  -- solve the linear relation
  rw [hcu, hθval, hcb] at hmom
  refine mul_left_cancel₀ hne ?_
  linear_combination hmom

end MeasureR

end

end PadicLFunctions
