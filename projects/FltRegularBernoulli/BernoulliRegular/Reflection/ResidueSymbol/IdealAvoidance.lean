module

public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal avoidance for class representatives

This file starts the REF-17 ideal-avoidance API.  The first result is the
single-maximal-ideal case: every class has a nonzero integral ideal
representative coprime to a prescribed maximal ideal.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace ResidueSymbol
namespace IdealAvoidance

open scoped BigOperators nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- If `I` is nonzero and `P` is maximal, then `I` contains an element not in
`P * I`. -/
theorem exists_mem_notMem_mul_left (I P : Ideal R) (hI : I ≠ ⊥) [P.IsMaximal] :
    ∃ x : R, x ∈ I ∧ x ∉ P * I := by
  have hlt : P * I < I := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    refine ⟨hI, P, ?_, by rw [mul_comm]⟩
    exact mt Ideal.isUnit_iff.mp (Ideal.IsMaximal.ne_top (I := P) inferInstance)
  exact Set.not_subset.mp (not_le_of_gt hlt)

/-- Simultaneous finite-prime avoidance inside a nonzero ideal.

Given finitely many maximal ideals `S` and a nonzero ideal `I`, there is a
nonzero `x ∈ I` whose image in each `I / P I` is nonzero. -/
theorem exists_mem_notMem_mul_left_finset (I : Ideal R) (hI : I ≠ ⊥)
    (S : Finset (Ideal R)) (hSmax : ∀ P ∈ S, P.IsMaximal) :
    ∃ x : R, x ≠ 0 ∧ x ∈ I ∧ ∀ P ∈ S, x ∉ P * I := by
  classical
  by_cases hS_empty : S = ∅
  · obtain ⟨x, hxI, hx_ne⟩ := (Submodule.ne_bot_iff I).mp hI
    refine ⟨x, hx_ne, hxI, ?_⟩
    intro P hP
    simp [hS_empty] at hP
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hlocal : ∀ P : S, ∃ x : R, x ∈ I ∧ x ∉ (P : Ideal R) * I := by
      intro P
      letI : (P : Ideal R).IsMaximal := hSmax P P.property
      exact exists_mem_notMem_mul_left I P hI
    choose a ha using hlocal
    have haI : ∀ P : S, a P ∈ I := fun P => (ha P).1
    have haNot : ∀ P : S, a P ∉ (P : Ideal R) * I := fun P => (ha P).2
    have hpair : Pairwise fun P Q : S => IsCoprime (P : Ideal R) (Q : Ideal R) := by
      intro P Q hne
      rw [Ideal.isCoprime_iff_sup_eq]
      letI : (P : Ideal R).IsMaximal := hSmax P P.property
      letI : (Q : Ideal R).IsMaximal := hSmax Q Q.property
      exact Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance
        (Subtype.coe_injective.ne hne)
    have hidempotent :
        ∀ P : S, ∃ e : R, ∀ Q : S,
          e - (if Q = P then (1 : R) else 0) ∈ (Q : Ideal R) := fun P =>
      Ideal.exists_forall_sub_mem_ideal hpair
        (fun Q : S => if Q = P then (1 : R) else 0)
    choose e he using hidempotent
    let x : R := ∑ P : S, e P * a P
    have hxI : x ∈ I := by
      dsimp [x]
      exact I.sum_mem fun P _ => I.mul_mem_left _ (haI P)
    have hdiff : ∀ Q : S, x - a Q ∈ (Q : Ideal R) * I := by
      intro Q
      have hsum_mem :
          (∑ P : S, (e P - (if Q = P then (1 : R) else 0)) * a P) ∈
            (Q : Ideal R) * I := by
        refine ((Q : Ideal R) * I).sum_mem ?_
        intro P _
        exact Ideal.mul_mem_mul (he P Q) (haI P)
      have hdelta :
          (∑ P : S, (if Q = P then (1 : R) else 0) * a P) = a Q := by
        rw [Finset.sum_eq_single Q]
        · simp
        · intro P _ hPQ
          have hQP : Q ≠ P := fun h => hPQ h.symm
          simp [hQP]
        · intro hQ
          simp at hQ
      have hsum_eq :
          (∑ P : S, (e P - (if Q = P then (1 : R) else 0)) * a P) =
            x - a Q := by
        calc
          (∑ P : S, (e P - (if Q = P then (1 : R) else 0)) * a P)
              = (∑ P : S, e P * a P) -
                  (∑ P : S, (if Q = P then (1 : R) else 0) * a P) := by
                simp [sub_mul, Finset.sum_sub_distrib]
          _ = x - a Q := by
                rw [hdelta]
      exact hsum_eq ▸ hsum_mem
    have havoid : ∀ Q : S, x ∉ (Q : Ideal R) * I := by
      intro Q hxQI
      apply haNot Q
      have hx_sub_mem : x - (x - a Q) ∈ (Q : Ideal R) * I :=
        ((Q : Ideal R) * I).sub_mem hxQI (hdiff Q)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx_sub_mem
    have hx_ne : x ≠ 0 := by
      obtain ⟨P, hP⟩ := hS_nonempty
      intro hx0
      exact havoid ⟨P, hP⟩ (by rw [hx0]; simp)
    refine ⟨x, hx_ne, hxI, ?_⟩
    intro P hP
    exact havoid ⟨P, hP⟩

omit [IsDedekindDomain R] in
/-- If `I` is coprime to a prime `P`, then an element of `I` not lying in
`P * I` is not itself in `P`. -/
theorem notMem_prime_of_mem_notMem_mul_left_of_isCoprime
    {I P : Ideal R} {x : R} (hxI : x ∈ I) (hxPI : x ∉ P * I)
    (hcop : IsCoprime I P) : x ∉ P := by
  intro hxP
  apply hxPI
  have hx_inf : x ∈ I ⊓ P := ⟨hxI, hxP⟩
  have h_inf : I * P = I ⊓ P := Ideal.mul_eq_inf_of_isCoprime hcop
  simpa [mul_comm, h_inf] using hx_inf

/-- Finite-prime avoidance inside a nonzero ideal, upgraded to principal
coprimality when the ambient ideal is already coprime to the prescribed
maximal ideals. -/
theorem exists_mem_coprime_principal_finset (I : Ideal R) (hI : I ≠ ⊥)
    (S : Finset (Ideal R)) (hSmax : ∀ P ∈ S, P.IsMaximal)
    (hIcop : ∀ P ∈ S, IsCoprime I P) :
    ∃ x : R, x ≠ 0 ∧ x ∈ I ∧
      ∀ P ∈ S, IsCoprime (Ideal.span ({x} : Set R)) P := by
  classical
  obtain ⟨x, hx_ne, hxI, hx_not⟩ :=
    exists_mem_notMem_mul_left_finset I hI S hSmax
  refine ⟨x, hx_ne, hxI, ?_⟩
  intro P hP
  letI : P.IsMaximal := hSmax P hP
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  have hxP : x ∈ P := by
    have hspan_le : Ideal.span ({x} : Set R) ≤ P := by
      have h_eq : P = Ideal.span ({x} : Set R) ⊔ P :=
        Ideal.IsMaximal.eq_of_le (I := P) (J := Ideal.span ({x} : Set R) ⊔ P)
          inferInstance hsup le_sup_right
      exact le_sup_left.trans_eq h_eq.symm
    exact hspan_le (Ideal.mem_span_singleton_self x)
  exact notMem_prime_of_mem_notMem_mul_left_of_isCoprime
    hxI (hx_not P hP) (hIcop P hP) hxP

/-- Single-prime ideal avoidance for class representatives.

Every ideal class has a nonzero integral representative coprime to a prescribed
maximal ideal. -/
theorem exists_class_representative_coprime_singleton (c : ClassGroup R)
    (P : Ideal R) [IsDomain R] [P.IsMaximal] :
    ∃ J : (Ideal R)⁰, ClassGroup.mk0 J = c ∧ IsCoprime (J : Ideal R) P := by
  obtain ⟨I, hI_class⟩ := ClassGroup.mk0_surjective (R := R) (c⁻¹)
  obtain ⟨x, hxI, hx_not_mem⟩ := exists_mem_notMem_mul_left (I : Ideal R) P
    (mem_nonZeroDivisors_iff_ne_zero.mp I.prop)
  have hx_ne : x ≠ 0 := by
    rintro rfl
    exact hx_not_mem (by simp)
  obtain ⟨J, hJ_mul⟩ := (Ideal.dvd_span_singleton (I := (I : Ideal R)) (x := x)).mpr hxI
  have hJ_ne : J ≠ ⊥ := by
    rintro rfl
    exact hx_ne (Ideal.span_singleton_eq_bot.mp (by simpa using hJ_mul))
  refine ⟨⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩, ?_, ?_⟩
  · have h_inv :
        ClassGroup.mk0 I =
          (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩)⁻¹ := by
      rw [ClassGroup.mk0_eq_mk0_inv_iff]
      exact ⟨x, hx_ne, hJ_mul.symm⟩
    have h_inv_eq :
        (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩)⁻¹ = c⁻¹ := by
      rw [← h_inv, hI_class]
    exact inv_injective h_inv_eq
  · rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hsup
    have hJP : J ≤ P := by
      have h_eq : P = J ⊔ P :=
        Ideal.IsMaximal.eq_of_le (I := P) (J := J ⊔ P) inferInstance hsup le_sup_right
      exact le_sup_left.trans_eq h_eq.symm
    have hx_mem_mul : x ∈ P * I := by
      have hspan_le : Ideal.span ({x} : Set R) ≤ I * P := by
        rw [hJ_mul]
        exact Ideal.mul_mono_right hJP
      rw [mul_comm]
      exact hspan_le (Ideal.mem_span_singleton_self x)
    exact hx_not_mem hx_mem_mul

/-- Finite-prime ideal avoidance for class representatives.

Every ideal class has a nonzero integral representative coprime to each ideal
in a prescribed finite set of maximal ideals. -/
theorem exists_class_representative_coprime_finset (c : ClassGroup R)
    (S : Finset (Ideal R)) [IsDomain R] (hSmax : ∀ P ∈ S, P.IsMaximal) :
    ∃ J : (Ideal R)⁰,
      ClassGroup.mk0 J = c ∧ ∀ P ∈ S, IsCoprime (J : Ideal R) P := by
  obtain ⟨I, hI_class⟩ := ClassGroup.mk0_surjective (R := R) (c⁻¹)
  obtain ⟨x, hx_ne, hxI, hx_not_mem⟩ :=
    exists_mem_notMem_mul_left_finset (I : Ideal R)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.prop) S hSmax
  obtain ⟨J, hJ_mul⟩ := (Ideal.dvd_span_singleton (I := (I : Ideal R)) (x := x)).mpr hxI
  have hJ_ne : J ≠ ⊥ := by
    rintro rfl
    exact hx_ne (Ideal.span_singleton_eq_bot.mp (by simpa using hJ_mul))
  refine ⟨⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩, ?_, ?_⟩
  · have h_inv :
        ClassGroup.mk0 I =
          (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩)⁻¹ := by
      rw [ClassGroup.mk0_eq_mk0_inv_iff]
      exact ⟨x, hx_ne, hJ_mul.symm⟩
    have h_inv_eq :
        (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩)⁻¹ = c⁻¹ := by
      rw [← h_inv, hI_class]
    exact inv_injective h_inv_eq
  · intro P hP
    letI : P.IsMaximal := hSmax P hP
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hsup
    have hJP : J ≤ P := by
      have h_eq : P = J ⊔ P :=
        Ideal.IsMaximal.eq_of_le (I := P) (J := J ⊔ P) inferInstance hsup le_sup_right
      exact le_sup_left.trans_eq h_eq.symm
    have hx_mem_mul : x ∈ P * I := by
      have hspan_le : Ideal.span ({x} : Set R) ≤ I * P := by
        rw [hJ_mul]
        exact Ideal.mul_mono_right hJP
      rw [mul_comm]
      exact hspan_le (Ideal.mem_span_singleton_self x)
    exact hx_not_mem P hP hx_mem_mul

/-- Version of `exists_class_representative_coprime_finset` for nonzero prime
ideals in a Dedekind domain. -/
theorem exists_class_representative_coprime_prime_finset (c : ClassGroup R)
    (S : Finset (Ideal R)) [IsDomain R]
    (hSprime : ∀ P ∈ S, P.IsPrime) (hS_ne : ∀ P ∈ S, P ≠ ⊥) :
    ∃ J : (Ideal R)⁰,
      ClassGroup.mk0 J = c ∧ ∀ P ∈ S, IsCoprime (J : Ideal R) P :=
  exists_class_representative_coprime_finset c S fun P hP =>
    (hSprime P hP).isMaximal (hS_ne P hP)

end IdealAvoidance
end ResidueSymbol
end Reflection
end BernoulliRegular
