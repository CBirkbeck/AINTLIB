module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArtinHasse
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkWitt
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingCongruence
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientExpansion
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Basic Dwork factorization algebra

Split from `DworkFactorization.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- The finite truncation `∑_{n ≤ N} λ_n T^n` of a Dwork theta series. -/
def dworkThetaTrunc {A : Type*} [CommSemiring A]
    (dworkCoeff : ℕ → A) (N : ℕ) (u : A) : A :=
  ∑ n ∈ Finset.range (N + 1), dworkCoeff n * u ^ n

/-- Precision-indexed theta truncation.  The outer index selects the target
precision, while the finite sum still truncates at that same index. -/
def dworkThetaTruncTo {A : Type*} [CommSemiring A]
    (dworkCoeff : ℕ → ℕ → A) (N : ℕ) (u : A) : A :=
  dworkThetaTrunc (dworkCoeff N) N u

/-- The product of finite theta truncations over Frobenius powers
`u, u^ℓ, ..., u^(ℓ^(f-1))`. -/
def dworkThetaFrobeniusProduct {A : Type*} [CommSemiring A]
    (ℓ f N : ℕ) (dworkCoeff : ℕ → A) (u : A) : A :=
  ∏ i : Fin f, dworkThetaTrunc dworkCoeff N (u ^ (ℓ ^ (i : ℕ)))

/-- Precision-indexed Frobenius product of theta truncations. -/
def dworkThetaFrobeniusProductTo {A : Type*} [CommSemiring A]
    (ℓ f N : ℕ) (dworkCoeff : ℕ → ℕ → A) (u : A) : A :=
  dworkThetaFrobeniusProduct ℓ f N (dworkCoeff N) u

/-- The multi-index term occurring in the Dwork product expansion. -/
def dworkMultiIndexTerm {A : Type*} [CommSemiring A]
    {f : ℕ} (ℓ : ℕ) (dworkCoeff : ℕ → A) (u : A) (m : Fin f → ℕ) : A :=
  (∏ i : Fin f, dworkCoeff (m i)) * u ^ multiIndexValue ℓ m

/-- Precision-indexed multi-index term. -/
def dworkMultiIndexTermTo {A : Type*} [CommSemiring A]
    {f : ℕ} (ℓ : ℕ) (dworkCoeff : ℕ → ℕ → A) (N : ℕ) (u : A)
    (m : Fin f → ℕ) : A :=
  dworkMultiIndexTerm ℓ (dworkCoeff N) u m

/-- Exact finite product expansion before discarding high-weight terms. -/
theorem dworkThetaFrobeniusProduct_eq_piFinset_sum
    {A : Type*} [CommSemiring A]
    (ℓ f N : ℕ) (dworkCoeff : ℕ → A) (u : A) :
    dworkThetaFrobeniusProduct ℓ f N dworkCoeff u =
      ∑ m ∈ Fintype.piFinset (fun _ : Fin f => Finset.range (N + 1)),
        dworkMultiIndexTerm ℓ dworkCoeff u m := by
  classical
  unfold dworkThetaFrobeniusProduct dworkThetaTrunc dworkMultiIndexTerm
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _hm => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  calc
    (∏ i : Fin f, (u ^ (ℓ ^ (i : ℕ))) ^ m i)
        = ∏ i : Fin f, u ^ (m i * ℓ ^ (i : ℕ)) := by
            refine Finset.prod_congr rfl fun i _hi => ?_
            calc
              (u ^ (ℓ ^ (i : ℕ))) ^ m i = u ^ (ℓ ^ (i : ℕ) * m i) := by
                rw [pow_mul]
              _ = u ^ (m i * ℓ ^ (i : ℕ)) := by
                rw [Nat.mul_comm]
    _ = u ^ (∑ i : Fin f, m i * ℓ ^ (i : ℕ)) := by
            rw [Finset.prod_pow_eq_pow_sum]
    _ = u ^ multiIndexValue ℓ m := rfl

/-- A multi-index Dwork term lies in the ideal power given by its total
weight, provided each coefficient `λ_n` lies in `I^n`. -/
theorem dworkMultiIndexTerm_mem_I_pow_weight
    {A : Type*} [CommRing A] (I : Ideal A)
    {f : ℕ} (ℓ : ℕ) (dworkCoeff : ℕ → A) (u : A)
    (hCoeff : ∀ n : ℕ, dworkCoeff n ∈ I ^ n) (m : Fin f → ℕ) :
    dworkMultiIndexTerm ℓ dworkCoeff u m ∈ I ^ multiIndexWeight m := by
  have hprod :
      (∏ i : Fin f, dworkCoeff (m i)) ∈
        I ^ (∑ i : Fin f, m i) :=
    prod_mem_pow_sum_of_mem I Finset.univ (fun i : Fin f => m i)
      (fun i : Fin f => dworkCoeff (m i))
      (fun i _hi => hCoeff (m i))
  simpa [dworkMultiIndexTerm, multiIndexWeight] using
    Ideal.mul_mem_right (u ^ multiIndexValue ℓ m) (I ^ multiIndexWeight m) hprod

/-- The high-weight part of the bounded multi-index Dwork expansion is
zero modulo `I^(N+1)`. -/
theorem dworkPiFinsetSum_sub_multiIndexLESum_mem_I_pow_succ
    {A : Type*} [CommRing A] (I : Ideal A)
    (ℓ f N : ℕ) (dworkCoeff : ℕ → A) (u : A)
    (hCoeff : ∀ n : ℕ, dworkCoeff n ∈ I ^ n) :
    (∑ m ∈ Fintype.piFinset (fun _ : Fin f => Finset.range (N + 1)),
        dworkMultiIndexTerm ℓ dworkCoeff u m) -
      (∑ m ∈ multiIndexLE f N, dworkMultiIndexTerm ℓ dworkCoeff u m) ∈
        I ^ (N + 1) := by
  classical
  let s : Finset (Fin f → ℕ) :=
    Fintype.piFinset (fun _ : Fin f => Finset.range (N + 1))
  let term : (Fin f → ℕ) → A := fun m => dworkMultiIndexTerm ℓ dworkCoeff u m
  change (∑ m ∈ s, term m) -
      (∑ m ∈ s.filter (fun m => multiIndexWeight m ≤ N), term m) ∈ I ^ (N + 1)
  have hhigh :
      (∑ m ∈ s.filter (fun m => ¬ multiIndexWeight m ≤ N), term m) ∈
        I ^ (N + 1) := by
    refine Ideal.sum_mem _ ?_
    intro m hm
    rw [Finset.mem_filter] at hm
    have hN : N + 1 ≤ multiIndexWeight m :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hm.2)
    exact Ideal.pow_le_pow_right hN
      (dworkMultiIndexTerm_mem_I_pow_weight I ℓ dworkCoeff u hCoeff m)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not s (fun m => multiIndexWeight m ≤ N) term
  have hdiff :
      (∑ m ∈ s, term m) -
          (∑ m ∈ s.filter (fun m => multiIndexWeight m ≤ N), term m) =
        ∑ m ∈ s.filter (fun m => ¬ multiIndexWeight m ≤ N), term m := by
    rw [← hsplit]
    abel
  simpa [hdiff] using hhigh

/-- The finite theta product and the `multiIndexLE` truncation differ only by
terms of ideal order at least `N+1`. -/
theorem dworkThetaFrobeniusProduct_sub_multiIndexLESum_mem_I_pow_succ
    {A : Type*} [CommRing A] (I : Ideal A)
    (ℓ f N : ℕ) (dworkCoeff : ℕ → A) (u : A)
    (hCoeff : ∀ n : ℕ, dworkCoeff n ∈ I ^ n) :
    dworkThetaFrobeniusProduct ℓ f N dworkCoeff u -
      (∑ m ∈ multiIndexLE f N, dworkMultiIndexTerm ℓ dworkCoeff u m) ∈
        I ^ (N + 1) := by
  rw [dworkThetaFrobeniusProduct_eq_piFinset_sum]
  exact dworkPiFinsetSum_sub_multiIndexLESum_mem_I_pow_succ
    I ℓ f N dworkCoeff u hCoeff

/-- Products preserve congruence modulo an ideal: if each selected factor
differs by an element of `I`, then the two products differ by an element of
`I`. -/
theorem finset_prod_sub_prod_mem_ideal
    {ι A : Type*} [CommRing A] (I : Ideal A) (s : Finset ι)
    (F G : ι → A) (hFG : ∀ i ∈ s, F i - G i ∈ I) :
    (∏ i ∈ s, F i) - (∏ i ∈ s, G i) ∈ I := by
  classical
  revert hFG
  refine Finset.induction_on s ?base ?step
  · intro hFG
    simp
  · intro a s ha ih hFG
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have htail : (∏ i ∈ s, F i) - (∏ i ∈ s, G i) ∈ I :=
      ih fun i hi => hFG i (Finset.mem_insert_of_mem hi)
    have hhead : F a - G a ∈ I := hFG a (Finset.mem_insert_self a s)
    have h₁ :
        F a * ((∏ i ∈ s, F i) - (∏ i ∈ s, G i)) ∈ I :=
      Ideal.mul_mem_left I (F a) htail
    have h₂ :
        (F a - G a) * (∏ i ∈ s, G i) ∈ I :=
      Ideal.mul_mem_right (∏ i ∈ s, G i) I hhead
    have hsplit :
        F a * (∏ i ∈ s, F i) - G a * (∏ i ∈ s, G i) =
          F a * ((∏ i ∈ s, F i) - (∏ i ∈ s, G i)) +
            (F a - G a) * (∏ i ∈ s, G i) := by
      ring
    rw [hsplit]
    exact I.add_mem h₁ h₂

/-- Product congruence modulo a fixed ideal power. -/
theorem finset_prod_sub_prod_mem_pow
    {ι A : Type*} [CommRing A] (I : Ideal A) (s : Finset ι)
    (F G : ι → A) (n : ℕ) (hFG : ∀ i ∈ s, F i - G i ∈ I ^ n) :
    (∏ i ∈ s, F i) - (∏ i ∈ s, G i) ∈ I ^ n :=
  finset_prod_sub_prod_mem_ideal (I := I ^ n) s F G hFG

/-- `Fin`-indexed product congruence modulo a fixed ideal power. -/
theorem fin_prod_sub_prod_mem_pow
    {A : Type*} [CommRing A] (I : Ideal A) {f : ℕ}
    (F G : Fin f → A) (n : ℕ) (hFG : ∀ i : Fin f, F i - G i ∈ I ^ n) :
    (∏ i : Fin f, F i) - (∏ i : Fin f, G i) ∈ I ^ n := by
  simpa using
    finset_prod_sub_prod_mem_pow (I := I) Finset.univ F G n
      (fun i _hi => hFG i)

/-- Modulo `I^2`, a product of factors `1 + π uᵢ` is `1 + π∑uᵢ` whenever
`π ∈ I`. -/
theorem finset_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
    {ι A : Type*} [CommRing A] (I : Ideal A) (s : Finset ι)
    {π : A} (hπ : π ∈ I) (u : ι → A) :
    (∏ i ∈ s, (1 + π * u i)) - (1 + π * ∑ i ∈ s, u i) ∈ I ^ 2 := by
  classical
  revert u
  refine Finset.induction_on s ?base ?step
  · intro u
    simp
  · intro a s ha ih u
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    let P : A := ∏ i ∈ s, (1 + π * u i)
    let T : A := ∑ i ∈ s, u i
    have htail : P - (1 + π * T) ∈ I ^ 2 := by
      simpa [P, T] using ih u
    have hlinear :
        (1 + π * u a) * (P - (1 + π * T)) ∈ I ^ 2 :=
      Ideal.mul_mem_left _ _ htail
    have hππ : π * π ∈ I ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hπ hπ
    have hcross : (π * u a) * (π * T) ∈ I ^ 2 := by
      rw [show (π * u a) * (π * T) = (π * π) * (u a * T) by ring]
      exact Ideal.mul_mem_right _ _ hππ
    have hsplit :
        (1 + π * u a) * P - (1 + π * (u a + T)) =
          (1 + π * u a) * (P - (1 + π * T)) + (π * u a) * (π * T) := by
      ring
    change (1 + π * u a) * P - (1 + π * (u a + T)) ∈ I ^ 2
    rw [hsplit]
    exact (I ^ 2).add_mem hlinear hcross

/-- `Fin`-indexed form of
`finset_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two`. -/
theorem fin_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
    {A : Type*} [CommRing A] (I : Ideal A) {f : ℕ}
    {π : A} (hπ : π ∈ I) (u : Fin f → A) :
    (∏ i : Fin f, (1 + π * u i)) - (1 + π * ∑ i : Fin f, u i) ∈ I ^ 2 := by
  simpa using
    finset_prod_one_add_mul_sub_one_add_mul_sum_mem_pow_two
      (I := I) Finset.univ hπ u

/-- First-order product truncation for arbitrary `I`-small factors. -/
theorem finset_prod_one_add_sub_one_add_sum_mem_pow_two
    {ι A : Type*} [CommRing A] (I : Ideal A) (s : Finset ι)
    (c : ι → A) (hc : ∀ i ∈ s, c i ∈ I) :
    (∏ i ∈ s, (1 + c i)) - (1 + ∑ i ∈ s, c i) ∈ I ^ 2 := by
  classical
  revert c
  refine Finset.induction_on s ?base ?step
  · intro c hc
    simp
  · intro a s ha ih c hc
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    let P : A := ∏ i ∈ s, (1 + c i)
    let T : A := ∑ i ∈ s, c i
    have htail : P - (1 + T) ∈ I ^ 2 := by
      simpa [P, T] using ih c (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    have hlinear :
        (1 + c a) * (P - (1 + T)) ∈ I ^ 2 :=
      Ideal.mul_mem_left _ _ htail
    have hT : T ∈ I := by
      refine Ideal.sum_mem _ ?_
      intro i hi
      exact hc i (Finset.mem_insert_of_mem hi)
    have hcross : c a * T ∈ I ^ 2 := by
      simpa [pow_two] using
        Ideal.mul_mem_mul (hc a (Finset.mem_insert_self a s)) hT
    have hsplit :
        (1 + c a) * P - (1 + (c a + T)) =
          (1 + c a) * (P - (1 + T)) + c a * T := by
      ring
    change (1 + c a) * P - (1 + (c a + T)) ∈ I ^ 2
    rw [hsplit]
    exact (I ^ 2).add_mem hlinear hcross

/-- Second-order product truncation for arbitrary `I`-small factors.  The
quadratic term is written with the order on the index set to avoid division by
two. -/
theorem finset_prod_one_add_sub_quadratic_mem_pow_three
    {ι A : Type*} [LinearOrder ι] [CommRing A] (I : Ideal A) (s : Finset ι)
    (c : ι → A) (hc : ∀ i ∈ s, c i ∈ I) :
    (∏ i ∈ s, (1 + c i)) -
        (1 + ∑ i ∈ s, c i +
          ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) ∈ I ^ 3 := by
  classical
  rw [Finset.prod_one_add_ordered]
  let tail : ι → A := fun i =>
    ∑ j ∈ s.filter (fun j => j < i), c j
  have hterm :
      ∀ i ∈ s,
        c i * (∏ j ∈ s with j < i, (1 + c j)) - (c i + c i * tail i) ∈ I ^ 3 := by
    intro i hi
    have htail :
        (∏ j ∈ s.filter (fun j => j < i), (1 + c j)) - (1 + tail i) ∈ I ^ 2 := by
      simpa [tail] using
        finset_prod_one_add_sub_one_add_sum_mem_pow_two (I := I)
          (s.filter (fun j => j < i)) c
          (fun j hj => hc j (Finset.mem_filter.mp hj).1)
    have hmul :
        c i * ((∏ j ∈ s.filter (fun j => j < i), (1 + c j)) - (1 + tail i)) ∈
          I ^ 3 := by
      have hmul' :
          c i * ((∏ j ∈ s.filter (fun j => j < i), (1 + c j)) - (1 + tail i)) ∈
            I ^ 1 * I ^ 2 :=
        Ideal.mul_mem_mul (by simpa using hc i hi) htail
      rw [← pow_add] at hmul'
      simpa using hmul'
    rw [show c i * (∏ j ∈ s with j < i, (1 + c j)) - (c i + c i * tail i) =
        c i * ((∏ j ∈ s.filter (fun j => j < i), (1 + c j)) - (1 + tail i)) by
          simp [tail]
          ring]
    exact hmul
  have hsum :
      (∑ i ∈ s, c i * (∏ j ∈ s with j < i, (1 + c j))) -
          (∑ i ∈ s, (c i + c i * tail i)) ∈ I ^ 3 := by
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ ?_
    intro i hi
    exact hterm i hi
  have hsum_rewrite :
      (∑ i ∈ s, (c i + c i * tail i)) =
        (∑ i ∈ s, c i) + ∑ i ∈ s, c i * tail i := by
    rw [Finset.sum_add_distrib]
  rw [show 1 + ∑ i ∈ s, c i * (∏ j ∈ s with j < i, (1 + c j)) -
        (1 + ∑ i ∈ s, c i +
          ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) =
      (∑ i ∈ s, c i * (∏ j ∈ s with j < i, (1 + c j))) -
        (∑ i ∈ s, (c i + c i * tail i)) by
        rw [hsum_rewrite]
        simp [tail]
        ring]
  exact hsum

/-- Second-order product truncation for factors already separated into linear
and quadratic parts. -/
theorem finset_prod_one_add_linear_quadratic_sub_mem_pow_three
    {ι A : Type*} [LinearOrder ι] [CommRing A] (I : Ideal A) (s : Finset ι)
    (a b : ι → A) (ha : ∀ i ∈ s, a i ∈ I) (hb : ∀ i ∈ s, b i ∈ I ^ 2) :
    (∏ i ∈ s, (1 + a i + b i)) -
        (1 + (∑ i ∈ s, a i) + (∑ i ∈ s, b i) +
          ∑ i ∈ s, a i * ∑ j ∈ s.filter (fun j => j < i), a j) ∈ I ^ 3 := by
  classical
  let c : ι → A := fun i => a i + b i
  have hc : ∀ i ∈ s, c i ∈ I := fun i hi =>
    I.add_mem (ha i hi) (Ideal.pow_le_self (by decide) (hb i hi))
  have hprod :
      (∏ i ∈ s, (1 + c i)) -
          (1 + ∑ i ∈ s, c i +
            ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) ∈ I ^ 3 :=
    finset_prod_one_add_sub_quadratic_mem_pow_three I s c hc
  have hlinear :
      (∑ i ∈ s, c i) = (∑ i ∈ s, a i) + (∑ i ∈ s, b i) := by
    simp [c, Finset.sum_add_distrib]
  have hquad :
      (∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) -
          (∑ i ∈ s, a i * ∑ j ∈ s.filter (fun j => j < i), a j) ∈ I ^ 3 := by
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ ?_
    intro i hi
    let T : A := ∑ j ∈ s.filter (fun j => j < i), a j
    let U : A := ∑ j ∈ s.filter (fun j => j < i), b j
    have hT : T ∈ I := by
      refine Ideal.sum_mem _ ?_
      intro j hj
      exact ha j (Finset.mem_filter.mp hj).1
    have hU : U ∈ I ^ 2 := by
      refine Ideal.sum_mem _ ?_
      intro j hj
      exact hb j (Finset.mem_filter.mp hj).1
    have h1 : a i * U ∈ I ^ 3 := by
      have hmul : a i * U ∈ I ^ 1 * I ^ 2 :=
        Ideal.mul_mem_mul (by simpa using ha i hi) hU
      rw [← pow_add] at hmul
      simpa using hmul
    have h2 : b i * T ∈ I ^ 3 := by
      have hmul : b i * T ∈ I ^ 2 * I ^ 1 :=
        Ideal.mul_mem_mul (hb i hi) (by simpa using hT)
      rw [← pow_add] at hmul
      simpa [Nat.add_comm] using hmul
    have h3 : b i * U ∈ I ^ 3 := by
      have hmul : b i * U ∈ I ^ 2 * I ^ 2 :=
        Ideal.mul_mem_mul (hb i hi) hU
      rw [← pow_add] at hmul
      exact Ideal.pow_le_pow_right (by decide : 3 ≤ 4) (by simpa using hmul)
    have hsum : a i * U + b i * T + b i * U ∈ I ^ 3 :=
      (I ^ 3).add_mem ((I ^ 3).add_mem h1 h2) h3
    convert hsum using 1
    · simp [c, T, U, Finset.sum_add_distrib]
      ring
  have hprod' :
      (∏ i ∈ s, (1 + a i + b i)) -
          (1 + ∑ i ∈ s, c i +
            ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) ∈ I ^ 3 := by
    simpa [c, add_assoc] using hprod
  have hbridge :
      (1 + ∑ i ∈ s, c i +
            ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) -
          (1 + (∑ i ∈ s, a i) + (∑ i ∈ s, b i) +
            ∑ i ∈ s, a i * ∑ j ∈ s.filter (fun j => j < i), a j) ∈ I ^ 3 := by
    convert hquad using 1
    rw [hlinear]
    ring
  rw [show (∏ i ∈ s, (1 + a i + b i)) -
        (1 + (∑ i ∈ s, a i) + (∑ i ∈ s, b i) +
          ∑ i ∈ s, a i * ∑ j ∈ s.filter (fun j => j < i), a j) =
      ((∏ i ∈ s, (1 + a i + b i)) -
        (1 + ∑ i ∈ s, c i +
          ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j)) +
      ((1 + ∑ i ∈ s, c i +
          ∑ i ∈ s, c i * ∑ j ∈ s.filter (fun j => j < i), c j) -
        (1 + (∑ i ∈ s, a i) + (∑ i ∈ s, b i) +
          ∑ i ∈ s, a i * ∑ j ∈ s.filter (fun j => j < i), a j)) by ring]
  exact (I ^ 3).add_mem hprod' hbridge

/-- Frobenius is additive modulo `I^2` when the prime exponent itself lies in
`I^2`. -/
theorem finset_sum_pow_prime_sub_sum_pow_mem_sq
    {ι A : Type*} [CommRing A] (I : Ideal A) (s : Finset ι)
    {r : ℕ} (hr : Nat.Prime r) (hrI : (r : A) ∈ I ^ 2) (f : ι → A) :
    (∑ i ∈ s, f i) ^ r - (∑ i ∈ s, f i ^ r) ∈ I ^ 2 := by
  classical
  revert f
  refine Finset.induction_on s ?base ?step
  · intro f
    simp [hr.ne_zero]
  · intro a s ha ih f
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have htail :
        (∑ i ∈ s, f i) ^ r - (∑ i ∈ s, f i ^ r) ∈ I ^ 2 :=
      ih f
    rcases exists_add_pow_prime_eq (R := A) hr (f a) (∑ i ∈ s, f i) with ⟨c, hc⟩
    have hcross : (r : A) * f a * (∑ i ∈ s, f i) * c ∈ I ^ 2 :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hrI))
    rw [hc]
    rw [show f a ^ r + (∑ i ∈ s, f i) ^ r +
          (r : A) * f a * (∑ i ∈ s, f i) * c -
          (f a ^ r + ∑ i ∈ s, f i ^ r) =
        ((∑ i ∈ s, f i) ^ r - ∑ i ∈ s, f i ^ r) +
          (r : A) * f a * (∑ i ∈ s, f i) * c by ring]
    exact (I ^ 2).add_mem htail hcross

/-- If two elements are congruent modulo `I`, and each is Frobenius-fixed
modulo `I^2`, then they are already congruent modulo `I^2`. -/
theorem sub_mem_sq_of_sub_mem_of_pow_prime_sub_self
    {A : Type*} [CommRing A] (I : Ideal A) {r : ℕ} (hr : Nat.Prime r)
    (hrI : (r : A) ∈ I ^ 2) {x y : A}
    (hxy : x - y ∈ I) (hx : x ^ r - x ∈ I ^ 2) (hy : y ^ r - y ∈ I ^ 2) :
    x - y ∈ I ^ 2 := by
  let d : A := x - y
  have hd : d ∈ I := hxy
  have hx_eq : x = d + y := by
    dsimp [d]
    ring
  have hpowdiff : x ^ r - y ^ r ∈ I ^ 2 := by
    rcases exists_add_pow_prime_eq (R := A) hr d y with ⟨c, hc⟩
    have hr_two : 2 ≤ r := hr.two_le
    have hd_pow : d ^ r ∈ I ^ 2 :=
      Ideal.pow_le_pow_right hr_two (Ideal.pow_mem_pow hd r)
    have hcross : (r : A) * d * y * c ∈ I ^ 2 :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hrI))
    rw [hx_eq, hc]
    rw [show d ^ r + y ^ r + (r : A) * d * y * c - y ^ r =
        d ^ r + (r : A) * d * y * c by ring]
    exact (I ^ 2).add_mem hd_pow hcross
  have hfrobdiff : (x ^ r - x) - (y ^ r - y) ∈ I ^ 2 :=
    (I ^ 2).sub_mem hx hy
  have hsub : (x ^ r - y ^ r) - (x - y) ∈ I ^ 2 := by
    convert hfrobdiff using 1
    ring
  have hneg : -(x - y) ∈ I ^ 2 := by
    have h := (I ^ 2).sub_mem hsub hpowdiff
    convert h using 1
    ring
  simpa using (I ^ 2).neg_mem hneg

/-- Cancels a factor modulo an ideal using an explicit approximate inverse. -/
theorem mem_of_mul_mem_of_mul_inv_sub_one_mem
    {A : Type*} [CommRing A] (I : Ideal A) {a v x : A}
    (hax : a * x ∈ I) (hav : a * v - 1 ∈ I) :
    x ∈ I := by
  have hleft : v * (a * x) ∈ I :=
    Ideal.mul_mem_left _ _ hax
  have hright : (a * v - 1) * x ∈ I :=
    Ideal.mul_mem_right _ _ hav
  have h : x = v * (a * x) - (a * v - 1) * x := by
    ring
  rw [h]
  exact I.sub_mem hleft hright

theorem mul_mem_ideal_pow_add
    {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ} {x y : A}
    (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) :
    x * y ∈ I ^ (m + n) := by
  have hmul : x * y ∈ I ^ m * I ^ n :=
    Ideal.mul_mem_mul hx hy
  simpa [pow_add] using hmul

/-- An element of `I` becomes nilpotent modulo `I^(N+1)`. -/
theorem quotient_mk_mem_pow_succ_eq_zero
    {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I) (N : ℕ) :
    (Ideal.Quotient.mk (I ^ (N + 1)) x) ^ (N + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hx (N + 1)

/-- Substitution of a nilpotent constant into a power series is the finite
polynomial evaluation at that constant. -/
theorem powerSeries_subst_C_eq_C_sum_range_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) :
    PowerSeries.subst (PowerSeries.C a) F =
      PowerSeries.C (∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n F * a ^ n) := by
  have hnil : IsNilpotent a := ⟨N + 1, ha⟩
  have hsubst : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    simpa using hnil
  ext m
  by_cases hm : m = 0
  · subst m
    rw [PowerSeries.coeff_subst' hsubst]
    rw [finsum_eq_sum_of_support_subset
      (fun d : ℕ => PowerSeries.coeff d F •
        PowerSeries.coeff 0 ((PowerSeries.C a : PowerSeries A) ^ d))
      (s := Finset.range (N + 1))]
    · simp [smul_eq_mul]
    · intro d hd
      by_contra hdmem
      have hle : N + 1 ≤ d := Nat.le_of_not_gt (by simpa using hdmem)
      have hpow : a ^ d = 0 := pow_eq_zero_of_le hle ha
      exact hd (by simp [hpow])
  · rw [PowerSeries.coeff_subst' hsubst]
    rw [finsum_eq_zero_of_forall_eq_zero]
    · exact (PowerSeries.coeff_C_of_ne_zero hm).symm
    · intro d
      have hcoeff :
          PowerSeries.coeff m ((PowerSeries.C a : PowerSeries A) ^ d) = 0 := by
        rw [← map_pow (PowerSeries.C : A →+* PowerSeries A) a d]
        exact PowerSeries.coeff_C_of_ne_zero hm
      simp [hcoeff]

/-- Substitution of a nilpotent constant into a power series is the constant
power series attached to the finite truncation evaluation. -/
theorem powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) :
    PowerSeries.subst (PowerSeries.C a) F =
      PowerSeries.C
        ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) := by
  rw [powerSeries_subst_C_eq_C_sum_range_of_pow_succ_eq_zero a N ha F]
  congr 1
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp

/-- Finite truncation evaluation at a nilpotent element is multiplicative. -/
theorem powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F G : PowerSeries A) :
    (PowerSeries.trunc (N + 1) (F * G)).eval₂ (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a *
        (PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  apply PowerSeries.C_injective
  calc
    PowerSeries.C ((PowerSeries.trunc (N + 1) (F * G)).eval₂ (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a) (F * G) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst (PowerSeries.C a) F *
          PowerSeries.subst (PowerSeries.C a) G := by
          rw [PowerSeries.subst_mul hCa]
    _ = PowerSeries.C ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) *
          PowerSeries.C ((PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha F,
            powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha G]
    _ = PowerSeries.C
          ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a *
            (PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) := by
          simp

/-- Finite truncation evaluation at a nilpotent element commutes with powers. -/
theorem powerSeries_trunc_eval₂_pow_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ) (ha : a ^ (N + 1) = 0)
    (F : PowerSeries A) (m : ℕ) :
    (PowerSeries.trunc (N + 1) (F ^ m)).eval₂ (RingHom.id A) a =
      ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  apply PowerSeries.C_injective
  calc
    PowerSeries.C ((PowerSeries.trunc (N + 1) (F ^ m)).eval₂ (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a) (F ^ m) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst (PowerSeries.C a) F ^ m := by
          rw [PowerSeries.subst_pow hCa]
    _ = PowerSeries.C ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha F]
    _ = PowerSeries.C
          (((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) ^ m) := by
          simp

/-- Evaluating a polynomial at a nilpotent element differs from its constant
term by a nilpotent element. -/
theorem polynomial_eval₂_sub_coeff_zero_isNilpotent
    {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (P : Polynomial R) {a : A} {e : ℕ} (ha : a ^ e = 0) :
    IsNilpotent (P.eval₂ φ a - φ (P.coeff 0)) := by
  rcases Polynomial.X_dvd_sub_C (p := P) with ⟨Q, hQ⟩
  have heq : P.eval₂ φ a - φ (P.coeff 0) = a * Q.eval₂ φ a := by
    have h := congrArg (fun P : Polynomial R => P.eval₂ φ a) hQ
    simpa [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X] using h
  refine ⟨e, ?_⟩
  rw [heq, mul_pow, ha, zero_mul]

/-- A polynomial with constant term evaluating to `1` evaluates to a unit at
every nilpotent element. -/
theorem polynomial_eval₂_isUnit_of_coeff_zero_eq_one_of_pow_eq_zero
    {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (P : Polynomial R) {a : A} {e : ℕ} (ha : a ^ e = 0)
    (h0 : φ (P.coeff 0) = 1) :
    IsUnit (P.eval₂ φ a) := by
  have hnil :
      IsNilpotent (P.eval₂ φ a - 1) := by
    simpa [h0] using polynomial_eval₂_sub_coeff_zero_isNilpotent φ P ha
  convert hnil.isUnit_one_add using 1
  ring

/-- A finite power-series truncation whose constant coefficient is `1`
evaluates to a unit at every nilpotent element. -/
theorem powerSeries_trunc_eval₂_isUnit_of_constantCoeff_eq_one_of_pow_eq_zero
    {A : Type*} [CommRing A] (F : PowerSeries A) (N : ℕ)
    {a : A} {e : ℕ} (ha : a ^ e = 0)
    (hF0 : PowerSeries.constantCoeff F = 1) :
    IsUnit ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) a) := by
  refine polynomial_eval₂_isUnit_of_coeff_zero_eq_one_of_pow_eq_zero
    (RingHom.id A) (PowerSeries.trunc (N + 1) F) ha ?_
  simp [PowerSeries.coeff_trunc, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF0]

/-- The finite Artin-Hasse exponential truncation evaluates to a unit at
every nilpotent element after mapping integral coefficients to any quotient
ring. -/
theorem artinHasseExp_mapTo_trunc_eval_isUnit_of_pow_eq_zero
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    {a : A} {e : ℕ} (ha : a ^ e = 0) :
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) from
        fun n => artinHasseExpSeries_coeff_isRIntegral r n).mapTo φ
    IsUnit ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) a) := by
  dsimp only
  let hE : DieudonneDwork.IsRIntegralPS r (artinHasseExpSeries r) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral r n
  let Eps : PowerSeries A := hE.mapTo φ
  have hE0 : PowerSeries.constantCoeff Eps = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply Eps]
    rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    have hcoeff0 :
        (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries r), hE 0⟩ :
          DieudonneDwork.rIntegralRatSubring r) = 1 := by
      ext
      simp [artinHasseExpSeries_constantCoeff]
    rw [hcoeff0]
    exact map_one φ
  exact powerSeries_trunc_eval₂_isUnit_of_constantCoeff_eq_one_of_pow_eq_zero
    Eps N ha hE0

/-- Evaluating `F(T^r)` at a nilpotent element is the same as evaluating `F`
at the corresponding power. -/
theorem powerSeries_trunc_eval₂_subst_X_pow_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N r : ℕ) (hr : r ≠ 0)
    (ha : a ^ (N + 1) = 0) (ha_pow : (a ^ r) ^ (N + 1) = 0)
    (F : PowerSeries A) :
    (PowerSeries.trunc (N + 1)
        (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F)).eval₂
        (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a ^ r) := by
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  have hXr : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries A) ^ r) :=
    PowerSeries.HasSubst.X_pow hr
  apply PowerSeries.C_injective
  calc
    PowerSeries.C
        ((PowerSeries.trunc (N + 1)
          (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F)).eval₂
          (RingHom.id A) a)
        = PowerSeries.subst (PowerSeries.C a)
            (PowerSeries.subst ((PowerSeries.X : PowerSeries A) ^ r) F) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero a N ha]
    _ = PowerSeries.subst
          (PowerSeries.subst (PowerSeries.C a) ((PowerSeries.X : PowerSeries A) ^ r)) F := by
          rw [PowerSeries.subst_comp_subst_apply hXr hCa]
    _ = PowerSeries.subst (PowerSeries.C (a ^ r)) F := by
          congr 1
          rw [PowerSeries.subst_pow hCa, PowerSeries.subst_X hCa]
          simp
    _ = PowerSeries.C
          ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a ^ r)) := by
          rw [powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero (a ^ r) N ha_pow F]

/-- Evaluating a rescaled finite truncation at `a` is the same as evaluating
the original finite truncation at `a * u`. -/
theorem powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul
    {A : Type*} [CommSemiring A] (F : PowerSeries A) (N : ℕ) (a u : A) :
    (PowerSeries.trunc (N + 1) (PowerSeries.rescale u F)).eval₂ (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) (a * u) := by
  rw [PowerSeries.eval₂_trunc_eq_sum_range, PowerSeries.eval₂_trunc_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  simp [PowerSeries.coeff_rescale, mul_pow, mul_assoc, mul_comm]

/-- Two truncated ordinary-exponential correction factors multiply by adding
their target arguments, after extracting the common nilpotent parameter. -/
theorem rescale_exp_trunc_eval₂_mul
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ x y : A) (hδ : δ ^ (N + 1) = 0) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * y) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (x + y)) := by
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  have hmul :=
    powerSeries_trunc_eval₂_mul_of_pow_succ_eq_zero
      (A := A) δ N hδ (PowerSeries.rescale x Rps) (PowerSeries.rescale y Rps)
  have hformal : PowerSeries.rescale x Rps * PowerSeries.rescale y Rps =
      PowerSeries.rescale (x + y) Rps := by
    simpa [Rps] using rescale_exp_mapTo_mul r φ x y
  calc
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * y)
        =
          (PowerSeries.trunc (N + 1) (PowerSeries.rescale x Rps)).eval₂
              (RingHom.id A) δ *
            (PowerSeries.trunc (N + 1) (PowerSeries.rescale y Rps)).eval₂
              (RingHom.id A) δ := by
          rw [powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul,
            powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul]
    _ = (PowerSeries.trunc (N + 1)
            (PowerSeries.rescale x Rps * PowerSeries.rescale y Rps)).eval₂
            (RingHom.id A) δ := by
          rw [hmul]
    _ = (PowerSeries.trunc (N + 1) (PowerSeries.rescale (x + y) Rps)).eval₂
            (RingHom.id A) δ := by
          rw [hformal]
    _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (x + y)) := by
          rw [powerSeries_trunc_rescale_eval₂_eq_trunc_eval₂_mul]

/-- Subtraction form of the localized addition law for the ordinary
correction series. -/
theorem rescale_exp_trunc_eval₂_mul_sub
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A]
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ x y : A) (hδ : δ ^ (N + 1) = 0) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * x) *
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (y - x)) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * y) := by
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  have h :=
    rescale_exp_trunc_eval₂_mul r φ N δ x (y - x) hδ
  have harg : δ * (x + (y - x)) = δ * y := by
    ring
  simpa [Rps, harg] using h

/-- Finite product form of `rescale_exp_trunc_eval₂_mul`: a product of
correction factors around any finite family collapses to one factor at the
sum of the family. -/
theorem rescale_exp_trunc_eval₂_finset_prod_eq_sum
    (r : ℕ) [Fact (Nat.Prime r)] {A : Type*} [CommRing A] {ι : Type*}
    (φ : DieudonneDwork.rIntegralRatSubring r →+* A) (N : ℕ)
    (δ : A) (hδ : δ ^ (N + 1) = 0) (s : Finset ι) (u : ι → A) :
    let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
    (∏ i ∈ s,
        (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i)) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
        (δ * ∑ i ∈ s, u i) := by
  classical
  dsimp only
  let Rps : PowerSeries A := (rescale_exp_isRIntegral r).mapTo φ
  refine Finset.induction_on s ?_ ?_
  · simp only [Polynomial.eval₂_id, Finset.prod_empty, Finset.sum_empty, mul_zero,
      Polynomial.eval₂_at_zero, RingHom.id_apply]
    rw [PowerSeries.coeff_trunc]
    simp only [Nat.lt_add_one_iff, zero_le, ↓reduceIte]
    rw [DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    have hone :
        (⟨(PowerSeries.coeff (R := ℚ) 0)
            (PowerSeries.rescale (r : ℚ) (PowerSeries.exp ℚ)),
          (rescale_exp_isRIntegral r) 0⟩ : DieudonneDwork.rIntegralRatSubring r) = 1 := by
      apply Subtype.ext
      simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    rw [hone, map_one]
  · intro a s ha ih
    have htwo :=
      rescale_exp_trunc_eval₂_mul r φ N δ (u a) (∑ i ∈ s, u i) hδ
    calc
      (∏ i ∈ insert a s,
          (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i))
          =
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u a) *
              ∏ i ∈ s,
                (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u i) := by
            rw [Finset.prod_insert ha]
      _ =
            (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * u a) *
              (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
                (δ * ∑ i ∈ s, u i) := by
            rw [ih]
      _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * (u a + ∑ i ∈ s, u i)) := by
            simpa [Rps] using htwo
      _ = (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
            (δ * ∑ i ∈ insert a s, u i) := by
            rw [Finset.sum_insert ha]

end Furtwaengler

end BernoulliRegular

end
