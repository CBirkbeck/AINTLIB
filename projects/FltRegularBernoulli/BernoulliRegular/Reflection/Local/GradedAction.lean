module

public import BernoulliRegular.Reflection.Local.DeltaAction
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjection

/-!
# Delta action on completed local graded pieces

This file starts REF-11c.  It packages the first completed graded quotient
`completed U_1 / completed U_2`, gives it the induced cyclotomic `Delta`
action, and records the Teichmuller action on the distinguished zeta class.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section AlgebraLemmas

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem pow_sub_natCast_mul_pow_mem_succ_of_sub_mem_sq
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) {A n : ℕ}
    (hxy : y - (A : R) * x ∈ I ^ 2) :
    y ^ n - (A ^ n : R) * x ^ n ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hleft : (y ^ n - (A ^ n : R) * x ^ n) * y ∈ I ^ (n + 2) := by
        have hmul : (y ^ n - (A ^ n : R) * x ^ n) * y ∈ I ^ (n + 1) * I :=
          Ideal.mul_mem_mul ih hy
        simpa [pow_succ, Nat.add_assoc] using hmul
      have hxpow : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      have hright : ((A ^ n : R) * x ^ n) * (y - (A : R) * x) ∈ I ^ (n + 2) := by
        have hmul : x ^ n * (y - (A : R) * x) ∈ I ^ n * I ^ 2 :=
          Ideal.mul_mem_mul hxpow hxy
        have hmul' : x ^ n * (y - (A : R) * x) ∈ I ^ (n + 2) := by
          simpa [pow_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
        simpa [mul_assoc] using Ideal.mul_mem_left (I ^ (n + 2)) (A ^ n : R) hmul'
      have hsum :
          (y ^ n - (A ^ n : R) * x ^ n) * y +
              ((A ^ n : R) * x ^ n) * (y - (A : R) * x) ∈ I ^ (n + 2) :=
        Ideal.add_mem _ hleft hright
      convert hsum using 1
      simp only [pow_succ]
      ring

private theorem one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ
    {n : ℕ} (hn : 1 ≤ n) {x : R} (hx : x ∈ I ^ n) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : R) * x ∈ I ^ (n + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hleft :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_right (1 + x) (I ^ (n + 1)) ih
      have hxx : x * x ∈ I ^ (n + 1) := by
        have hx2 : x * x ∈ I ^ n * I ^ n := Ideal.mul_mem_mul hx hx
        have hx2' : x * x ∈ I ^ (n + n) := by
          simpa [pow_add] using hx2
        exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) hx2'
      have hright : (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.mul_mem_left (I ^ (n + 1)) (k : R) hxx
      have hsum :
          ((1 + x) ^ k - 1 - (k : R) * x) * (1 + x) +
              (k : R) * (x * x) ∈ I ^ (n + 1) :=
        Ideal.add_mem _ hleft hright
      convert hsum using 1
      rw [pow_succ, Nat.cast_succ]
      ring

end AlgebraLemmas

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The local cyclotomic action sends the distinguished root of unity to its
Teichmuller power. -/
@[simp]
theorem localCyclotomicUnitEquiv_zetaUnit
    (a : CyclotomicUnitDelta p) :
    localCyclotomicUnitEquiv (p := p) K a (localCyclotomicZetaUnit p K) =
      localCyclotomicZetaUnit p K ^ (a : ZMod p).val := by
  apply Units.ext
  change localCyclotomicRingEquiv (p := p) K a
      ((localCyclotomicZetaUnit p K : localCyclotomicUnitGroup p K) :
        localCyclotomicRing p K) =
    ((localCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      localCyclotomicUnitGroup p K) : localCyclotomicRing p K)
  rw [localCyclotomicZetaUnit_coe, localCyclotomicRingEquiv_algebraMap]
  simp only [Units.val_pow_eq_pow_val, localCyclotomicZetaUnit_coe]
  rw [← map_pow]
  congr 1
  change cyclotomicSigmaOfUnit (p := p) K a • (zeta_spec p ℚ K).toInteger =
    (zeta_spec p ℚ K).toInteger ^ (a : ZMod p).val
  exact cyclotomicSigmaOfUnit_smul_zetaInteger (p := p) (K := K) a

@[simp]
theorem completedLocalCyclotomicRingEquiv_algebraMap
    (a : CyclotomicUnitDelta p) (x : localCyclotomicRing p K) :
    completedLocalCyclotomicRingEquiv (p := p) K a
        (algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K) x) =
      algebraMap (localCyclotomicRing p K) (completedLocalCyclotomicRing p K)
        (localCyclotomicRingEquiv (p := p) K a x) := by
  let M := localCyclotomicMaximalIdeal p K
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_completedLocalCyclotomicRingEquiv]
  change Ideal.quotientMap (M ^ n)
      (localCyclotomicRingEquiv (p := p) K a :
        localCyclotomicRing p K →+* localCyclotomicRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
        (localCyclotomicRingEquiv (p := p) K a)
        (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
          (p := p) (K := K) a)
        n)
      (AdicCompletion.evalₐ M n
        (algebraMap (localCyclotomicRing p K) (AdicCompletion M (localCyclotomicRing p K))
          x)) =
    AdicCompletion.evalₐ M n
      (algebraMap (localCyclotomicRing p K) (AdicCompletion M (localCyclotomicRing p K))
        (localCyclotomicRingEquiv (p := p) K a x))
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  simp

/-- The completed cyclotomic action sends the distinguished root of unity to
its Teichmuller power. -/
@[simp]
theorem completedLocalCyclotomicUnitEquiv_zetaUnit
    (a : CyclotomicUnitDelta p) :
    completedLocalCyclotomicUnitEquiv (p := p) K a
        (completedLocalCyclotomicZetaUnit p K) =
      completedLocalCyclotomicZetaUnit p K ^ (a : ZMod p).val := by
  apply Units.ext
  change completedLocalCyclotomicRingEquiv (p := p) K a
      ((completedLocalCyclotomicZetaUnit p K :
        completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K) =
    ((completedLocalCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K)
  rw [completedLocalCyclotomicZetaUnit_coe, completedLocalCyclotomicRingEquiv_algebraMap]
  have hlocal := congrArg
    (fun u : localCyclotomicUnitGroup p K ↦ (u : localCyclotomicRing p K))
    (localCyclotomicUnitEquiv_zetaUnit (p := p) (K := K) a)
  change localCyclotomicRingEquiv (p := p) K a
      (localCyclotomicZetaUnit p K : localCyclotomicRing p K) =
    ((localCyclotomicZetaUnit p K ^ (a : ZMod p).val :
      localCyclotomicUnitGroup p K) : localCyclotomicRing p K) at hlocal
  rw [hlocal]
  simp [completedLocalCyclotomicZetaUnit_coe, map_pow]

theorem localCyclotomicResidue_quotientMap_localCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) :
    Ideal.quotientMap (localCyclotomicMaximalIdeal p K)
        (localCyclotomicRingEquiv (p := p) K a :
          localCyclotomicRing p K →+* localCyclotomicRing p K)
        (by
          rw [← Ideal.map_le_iff_le_comap]
          exact (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
            (p := p) (K := K) a).le) =
      RingHom.id (localCyclotomicRing p K ⧸ localCyclotomicMaximalIdeal p K) := by
  let R := localCyclotomicRing p K
  let M := localCyclotomicMaximalIdeal p K
  let φ : R ⧸ M →+* R ⧸ M :=
    Ideal.quotientMap M (localCyclotomicRingEquiv (p := p) K a : R →+* R)
      (by
        rw [← Ideal.map_le_iff_le_comap]
        exact (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
          (p := p) (K := K) a).le)
  change φ = RingHom.id (R ⧸ M)
  have hnat : Nat.card (R ⧸ M) = p :=
    localCyclotomicResidueCard (p := p) (K := K)
  haveI : Finite (R ⧸ M) := Nat.finite_of_card_ne_zero (by
    rw [hnat]
    exact (Fact.out : Nat.Prime p).ne_zero)
  letI : Fintype (R ⧸ M) := Fintype.ofFinite (R ⧸ M)
  have hcard : Fintype.card (R ⧸ M) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hnat
  apply RingHom.ext
  intro x
  let e : ZMod p ≃+* R ⧸ M :=
    ZMod.ringEquivOfPrime (R ⧸ M) (Fact.out : Nat.Prime p) hcard
  rcases e.surjective x with ⟨z, hz⟩
  rw [← hz]
  have hhom : φ.comp e.toRingHom = e.toRingHom := Subsingleton.elim _ _
  exact RingHom.congr_fun hhom z

theorem completedLocalCyclotomicRingEquiv_sub_self_mem_maximalIdeal
    (a : CyclotomicUnitDelta p) (x : completedLocalCyclotomicRing p K) :
    completedLocalCyclotomicRingEquiv (p := p) K a x - x ∈
      completedLocalCyclotomicMaximalIdeal p K := by
  let M := localCyclotomicMaximalIdeal p K
  let Mhat := completedLocalCyclotomicMaximalIdeal p K
  change completedLocalCyclotomicRingEquiv (p := p) K a x - x ∈ Mhat
  rw [← pow_one Mhat,
    completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) 1]
  rw [RingHom.mem_ker, map_sub]
  change AdicCompletion.evalₐ M 1 (completedLocalCyclotomicRingEquiv (p := p) K a x) -
      AdicCompletion.evalₐ M 1 x = 0
  rw [evalₐ_completedLocalCyclotomicRingEquiv]
  change
    Ideal.quotientMap (M ^ 1)
        (localCyclotomicRingEquiv (p := p) K a :
          localCyclotomicRing p K →+* localCyclotomicRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
          (localCyclotomicRingEquiv (p := p) K a)
          (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
            (p := p) (K := K) a)
          1)
        (AdicCompletion.evalₐ M 1 x) -
      AdicCompletion.evalₐ M 1 x = 0
  have hquot1 :
      Ideal.quotientMap (M ^ 1)
          (localCyclotomicRingEquiv (p := p) K a :
            localCyclotomicRing p K →+* localCyclotomicRing p K)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
            (localCyclotomicRingEquiv (p := p) K a)
            (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
              (p := p) (K := K) a)
            1) =
        RingHom.id (localCyclotomicRing p K ⧸ M ^ 1) := by
    let R := localCyclotomicRing p K
    let φ : R ⧸ M ^ 1 →+* R ⧸ M ^ 1 :=
      Ideal.quotientMap (M ^ 1) (localCyclotomicRingEquiv (p := p) K a : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
          (localCyclotomicRingEquiv (p := p) K a)
          (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
            (p := p) (K := K) a)
          1)
    change φ = RingHom.id (R ⧸ M ^ 1)
    have hnat : Nat.card (R ⧸ M ^ 1) = p := by
      simpa [R, M, pow_one] using localCyclotomicResidueCard (p := p) (K := K)
    haveI : Finite (R ⧸ M ^ 1) := Nat.finite_of_card_ne_zero (by
      rw [hnat]
      exact (Fact.out : Nat.Prime p).ne_zero)
    letI : Fintype (R ⧸ M ^ 1) := Fintype.ofFinite (R ⧸ M ^ 1)
    have hcard : Fintype.card (R ⧸ M ^ 1) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact hnat
    apply RingHom.ext
    intro q
    let e : ZMod p ≃+* R ⧸ M ^ 1 :=
      ZMod.ringEquivOfPrime (R ⧸ M ^ 1) (Fact.out : Nat.Prime p) hcard
    rcases e.surjective q with ⟨z, hz⟩
    rw [← hz]
    have hhom : φ.comp e.toRingHom = e.toRingHom := Subsingleton.elim _ _
    exact RingHom.congr_fun hhom z
  have happ := congrArg
    (fun f : localCyclotomicRing p K ⧸ M ^ 1 →+* localCyclotomicRing p K ⧸ M ^ 1 ↦
      f (AdicCompletion.evalₐ M 1 x)) hquot1
  simpa [M, pow_one, sub_eq_zero] using happ

@[simp]
theorem completedLocalCyclotomicZetaUnit_coe_eq_one_add_uniformizer :
    ((completedLocalCyclotomicZetaUnit p K : completedLocalCyclotomicUnitGroup p K) :
        completedLocalCyclotomicRing p K) =
      1 + completedLocalCyclotomicUniformizer p K := by
  rw [completedLocalCyclotomicZetaUnit_coe, completedLocalCyclotomicUniformizer,
    localCyclotomicUniformizer]
  simp [map_sub, map_one]

theorem completedLocalCyclotomicRingEquiv_uniformizer_sub_natCast_mul_mem_sq
    (a : CyclotomicUnitDelta p) :
    completedLocalCyclotomicRingEquiv (p := p) K a
        (completedLocalCyclotomicUniformizer p K) -
      ((a : ZMod p).val : completedLocalCyclotomicRing p K) *
        completedLocalCyclotomicUniformizer p K ∈
      completedLocalCyclotomicMaximalIdeal p K ^ 2 := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let π : S := completedLocalCyclotomicUniformizer p K
  let A : ℕ := (a : ZMod p).val
  have hπM : π ∈ M := by
    change completedLocalCyclotomicUniformizer p K ∈ completedLocalCyclotomicMaximalIdeal p K
    rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self π
  have hbinom :
      (1 + π) ^ A - 1 - (A : S) * π ∈ M ^ (1 + 1) :=
    one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ M (by decide : 1 ≤ 1)
      (by simpa [pow_one, S, M, π] using hπM) A
  have hπ_eq :
      π = ((completedLocalCyclotomicZetaUnit p K : completedLocalCyclotomicUnitGroup p K) :
          S) - 1 := by
    rw [completedLocalCyclotomicZetaUnit_coe_eq_one_add_uniformizer (p := p) (K := K)]
    ring
  have hzeta :
      completedLocalCyclotomicRingEquiv (p := p) K a
          (((completedLocalCyclotomicZetaUnit p K : completedLocalCyclotomicUnitGroup p K) :
            S)) =
        ((completedLocalCyclotomicZetaUnit p K ^ A :
          completedLocalCyclotomicUnitGroup p K) : S) := by
    have h := congrArg
      (fun u : completedLocalCyclotomicUnitGroup p K ↦ (u : S))
      (completedLocalCyclotomicUnitEquiv_zetaUnit (p := p) (K := K) a)
    change ((completedLocalCyclotomicUnitEquiv (p := p) K a
        (completedLocalCyclotomicZetaUnit p K) : completedLocalCyclotomicUnitGroup p K) :
          S) =
      ((completedLocalCyclotomicZetaUnit p K ^ (a : ZMod p).val :
          completedLocalCyclotomicUnitGroup p K) : S)
    exact h
  have hσπ :
      completedLocalCyclotomicRingEquiv (p := p) K a π = (1 + π) ^ A - 1 := by
    rw [hπ_eq, map_sub, map_one, hzeta]
    simp [S, A, Units.val_pow_eq_pow_val]
  simpa [S, M, π, A, hσπ] using hbinom

theorem natCast_delta_val_pow_sub_zmod_pow_val_mem_completedMaximalIdeal
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    (((a : ZMod p).val : completedLocalCyclotomicRing p K) ^ n) -
      (((a : ZMod p) ^ n).val : completedLocalCyclotomicRing p K) ∈
      completedLocalCyclotomicMaximalIdeal p K := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let A : ℕ := (a : ZMod p).val
  let c : ℕ := ((a : ZMod p) ^ n).val
  have hpM : (p : S) ∈ M := by
    simpa [S, M] using natCast_prime_mem_completedLocalCyclotomicMaximalIdeal
      (p := p) (K := K)
  have hcast : ((A ^ n : ℕ) : ZMod p) = (a : ZMod p) ^ n := by
    have hA : (A : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val (a : ZMod p)
    rw [Nat.cast_pow, hA]
  have hmod : A ^ n % p = c := by
    have hleft : ((A ^ n : ℕ) : ZMod p).val = A ^ n % p :=
      ZMod.val_natCast p (A ^ n)
    have hright : ((A ^ n : ℕ) : ZMod p).val = c := by
      simpa [c] using congrArg ZMod.val hcast
    exact hleft.symm.trans hright
  have hdecomp : A ^ n = c + p * (A ^ n / p) := by
    have h := Nat.mod_add_div (A ^ n) p
    rw [hmod] at h
    exact h.symm
  have hdiff : (A : S) ^ n - (c : S) = (p : S) * (A ^ n / p : S) := by
    have hcastdecomp : ((A ^ n : ℕ) : S) =
        ((c + p * (A ^ n / p) : ℕ) : S) :=
      congrArg (fun m : ℕ ↦ (m : S)) hdecomp
    calc
      (A : S) ^ n - (c : S) = ((A ^ n : ℕ) : S) - (c : S) := by
        rw [Nat.cast_pow]
      _ = ((c + p * (A ^ n / p) : ℕ) : S) - (c : S) := by rw [hcastdecomp]
      _ = (p : S) * (A ^ n / p : S) := by
        rw [Nat.cast_add, Nat.cast_mul]
        ring
  have hmem : (A : S) ^ n - (c : S) ∈ M := by
    rw [hdiff]
    exact Ideal.mul_mem_right (A ^ n / p : S) M hpM
  simpa [S, M, A, c] using hmem

set_option maxHeartbeats 800000 in
-- The completed local ring typeclass and quotient coercions make this congruence
-- substantially heavier than the surrounding formal subgroup lemmas.
theorem completedLocalCyclotomicRingEquiv_uniformizer_pow_sub_zmodPowVal_mul_mem_succ
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    completedLocalCyclotomicRingEquiv (p := p) K a
        (completedLocalCyclotomicUniformizer p K ^ n) -
      (((a : ZMod p) ^ n).val : completedLocalCyclotomicRing p K) *
        completedLocalCyclotomicUniformizer p K ^ n ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (n + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let π : S := completedLocalCyclotomicUniformizer p K
  let A : ℕ := (a : ZMod p).val
  let c : ℕ := ((a : ZMod p) ^ n).val
  have hπM : π ∈ M := by
    change completedLocalCyclotomicUniformizer p K ∈ completedLocalCyclotomicMaximalIdeal p K
    rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer (p := p) (K := K)]
    exact Ideal.mem_span_singleton_self π
  have hσπM : completedLocalCyclotomicRingEquiv (p := p) K a π ∈ M := by
    have hsub := completedLocalCyclotomicRingEquiv_sub_self_mem_maximalIdeal
      (p := p) (K := K) a π
    have hsum : completedLocalCyclotomicRingEquiv (p := p) K a π - π + π ∈ M :=
      Ideal.add_mem M hsub hπM
    simpa [sub_eq_add_neg, add_assoc] using hsum
  have hσπ_sq :
      completedLocalCyclotomicRingEquiv (p := p) K a π - (A : S) * π ∈ M ^ 2 := by
    simpa [S, M, π, A] using
      completedLocalCyclotomicRingEquiv_uniformizer_sub_natCast_mul_mem_sq
        (p := p) (K := K) a
  have hpowA :
      (completedLocalCyclotomicRingEquiv (p := p) K a π) ^ n -
          (A : S) ^ n * π ^ n ∈ M ^ (n + 1) := by
    simpa [Nat.cast_pow] using
      pow_sub_natCast_mul_pow_mem_succ_of_sub_mem_sq M hπM hσπM hσπ_sq
  have hcoeff :
      (A : S) ^ n - (c : S) ∈ M := by
    simpa [S, M, A, c, Nat.cast_pow] using
      natCast_delta_val_pow_sub_zmod_pow_val_mem_completedMaximalIdeal
        (p := p) (K := K) a n
  have hπpow : π ^ n ∈ M ^ n := Ideal.pow_mem_pow hπM n
  have hcoeffTerm : ((A : S) ^ n - (c : S)) * π ^ n ∈ M ^ (n + 1) := by
    have hmul : ((A : S) ^ n - (c : S)) * π ^ n ∈ M * M ^ n :=
      Ideal.mul_mem_mul hcoeff hπpow
    have hmul' : ((A : S) ^ n - (c : S)) * π ^ n ∈ M ^ (1 + n) := by
      rw [pow_add, pow_one]
      exact hmul
    rw [show n + 1 = 1 + n by omega]
    exact hmul'
  have hsum :
      ((completedLocalCyclotomicRingEquiv (p := p) K a π) ^ n -
          (A : S) ^ n * π ^ n) + ((A : S) ^ n - (c : S)) * π ^ n ∈
        M ^ (n + 1) :=
    Ideal.add_mem _ hpowA hcoeffTerm
  rw [map_pow]
  convert hsum using 1
  ring

set_option maxHeartbeats 800000 in
-- This packages the principal-uniformizer calculation for arbitrary elements of `m^n`;
-- the proof repeatedly coerces through the completed local ring and its ideal powers.
theorem completedLocalCyclotomicRingEquiv_sub_zmodPowVal_mul_mem_succ
    (a : CyclotomicUnitDelta p) {n : ℕ}
    {x : completedLocalCyclotomicRing p K}
    (hx : x ∈ completedLocalCyclotomicMaximalIdeal p K ^ n) :
    completedLocalCyclotomicRingEquiv (p := p) K a x -
      (((a : ZMod p) ^ n).val : completedLocalCyclotomicRing p K) * x ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (n + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let π : S := completedLocalCyclotomicUniformizer p K
  let c : ℕ := ((a : ZMod p) ^ n).val
  obtain ⟨y, hy⟩ :=
    exists_uniformizer_pow_mul_eq_of_mem_completedLocalCyclotomicMaximalIdeal_pow
      (p := p) (K := K) (n := n) hx
  have hpow :
      completedLocalCyclotomicRingEquiv (p := p) K a (π ^ n) -
        (c : S) * π ^ n ∈ M ^ (n + 1) := by
    simpa [S, M, π, c] using
      completedLocalCyclotomicRingEquiv_uniformizer_pow_sub_zmodPowVal_mul_mem_succ
        (p := p) (K := K) a n
  have hy_res :
      completedLocalCyclotomicRingEquiv (p := p) K a y - y ∈ M :=
    completedLocalCyclotomicRingEquiv_sub_self_mem_maximalIdeal (p := p) (K := K) a y
  have hterm₁ :
      (completedLocalCyclotomicRingEquiv (p := p) K a (π ^ n) -
          (c : S) * π ^ n) *
        completedLocalCyclotomicRingEquiv (p := p) K a y ∈ M ^ (n + 1) :=
    Ideal.mul_mem_right _ (M ^ (n + 1)) hpow
  have hπpow : π ^ n ∈ M ^ n := by
    have hπM : π ∈ M := by
      change completedLocalCyclotomicUniformizer p K ∈ completedLocalCyclotomicMaximalIdeal p K
      rw [completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer (p := p) (K := K)]
      exact Ideal.mem_span_singleton_self π
    exact Ideal.pow_mem_pow hπM n
  have hraw : π ^ n * (completedLocalCyclotomicRingEquiv (p := p) K a y - y) ∈
      M ^ (n + 1) := by
    have hmul : π ^ n * (completedLocalCyclotomicRingEquiv (p := p) K a y - y) ∈
        M ^ n * M :=
      Ideal.mul_mem_mul hπpow hy_res
    rw [pow_succ]
    exact hmul
  have hterm₂ :
      (c : S) * π ^ n *
          (completedLocalCyclotomicRingEquiv (p := p) K a y - y) ∈ M ^ (n + 1) := by
    simpa [mul_assoc] using Ideal.mul_mem_left (M ^ (n + 1)) (c : S) hraw
  have hsum :
      (completedLocalCyclotomicRingEquiv (p := p) K a (π ^ n) -
          (c : S) * π ^ n) *
        completedLocalCyclotomicRingEquiv (p := p) K a y +
          (c : S) * π ^ n *
            (completedLocalCyclotomicRingEquiv (p := p) K a y - y) ∈ M ^ (n + 1) :=
    Ideal.add_mem _ hterm₁ hterm₂
  rw [← hy, map_mul]
  convert hsum using 1
  ring

/-- The subgroup `completed U_2`, viewed inside `completed U_1`. -/
abbrev completedPrincipalUnitFirstGradedSubgroup :
    Subgroup (completedPrincipalUnitSubgroup p K 1) :=
  (completedPrincipalUnitSubgroup p K 2).subgroupOf
    (completedPrincipalUnitSubgroup p K 1)

@[simp]
theorem mem_completedPrincipalUnitFirstGradedSubgroup_iff
    {u : completedPrincipalUnitSubgroup p K 1} :
    u ∈ completedPrincipalUnitFirstGradedSubgroup p K ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈
        completedPrincipalUnitSubgroup p K 2 :=
  Iff.rfl

/-- The first completed graded quotient `completed U_1 / completed U_2`. -/
abbrev completedPrincipalUnitFirstGradedQuotient : Type _ :=
  completedPrincipalUnitSubgroup p K 1 ⧸
    completedPrincipalUnitFirstGradedSubgroup p K

/-- The quotient map `completed U_1 -> completed U_1 / completed U_2`. -/
def completedPrincipalUnitFirstGradedClass :
    completedPrincipalUnitSubgroup p K 1 →*
      completedPrincipalUnitFirstGradedQuotient p K :=
  QuotientGroup.mk' (completedPrincipalUnitFirstGradedSubgroup p K)

@[simp]
theorem completedPrincipalUnitFirstGradedClass_apply
    (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitFirstGradedClass p K u = QuotientGroup.mk u :=
  rfl

theorem completedPrincipalUnitFirstGradedSubgroup_map
    (a : CyclotomicUnitDelta p) :
    (completedPrincipalUnitFirstGradedSubgroup p K).map
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1).toMonoidHom =
      completedPrincipalUnitFirstGradedSubgroup p K := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v ∈ completedPrincipalUnitFirstGradedSubgroup p K at hv
    change completedPrincipalUnitSubgroupEquiv (p := p) K a 1 v ∈
      completedPrincipalUnitFirstGradedSubgroup p K
    rw [mem_completedPrincipalUnitFirstGradedSubgroup_iff] at hv ⊢
    exact completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitSubgroup
      (p := p) (K := K) a hv
  · intro hu
    refine ⟨(completedPrincipalUnitSubgroupEquiv (p := p) K a 1).symm u, ?_, ?_⟩
    · change u ∈ completedPrincipalUnitFirstGradedSubgroup p K at hu
      rw [mem_completedPrincipalUnitFirstGradedSubgroup_iff] at hu
      change ((completedPrincipalUnitSubgroupEquiv (p := p) K a 1).symm u :
          completedPrincipalUnitSubgroup p K 1) ∈
        completedPrincipalUnitFirstGradedSubgroup p K
      rw [mem_completedPrincipalUnitFirstGradedSubgroup_iff]
      exact completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitSubgroup
        (p := p) (K := K) a hu
    · exact (completedPrincipalUnitSubgroupEquiv (p := p) K a 1).right_inv u

/-- The induced cyclotomic action on `completed U_1 / completed U_2`. -/
noncomputable def completedPrincipalUnitFirstGradedQuotientEquiv
    (a : CyclotomicUnitDelta p) :
    completedPrincipalUnitFirstGradedQuotient p K ≃*
      completedPrincipalUnitFirstGradedQuotient p K :=
  QuotientGroup.congr
    (completedPrincipalUnitFirstGradedSubgroup p K)
    (completedPrincipalUnitFirstGradedSubgroup p K)
    (completedPrincipalUnitSubgroupEquiv (p := p) K a 1)
    (completedPrincipalUnitFirstGradedSubgroup_map (p := p) (K := K) a)

@[simp]
theorem completedPrincipalUnitFirstGradedQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K a
        (completedPrincipalUnitFirstGradedClass p K u) =
      completedPrincipalUnitFirstGradedClass p K
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1 u) :=
  rfl

/-- The actual `Delta` action on `completed U_1 / completed U_2`. -/
noncomputable def completedPrincipalUnitFirstGradedDeltaAction :
    CyclotomicUnitDelta p →*
      MulAut (completedPrincipalUnitFirstGradedQuotient p K) where
  toFun a := completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K a
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K 1
        (completedPrincipalUnitFirstGradedClass p K u) =
      completedPrincipalUnitFirstGradedClass p K u
    rw [completedPrincipalUnitFirstGradedQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_one]
    rfl
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K (a * b)
        (completedPrincipalUnitFirstGradedClass p K u) =
      completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K a
        (completedPrincipalUnitFirstGradedQuotientEquiv (p := p) K b
          (completedPrincipalUnitFirstGradedClass p K u))
    rw [completedPrincipalUnitFirstGradedQuotientEquiv_mk,
      completedPrincipalUnitFirstGradedQuotientEquiv_mk,
      completedPrincipalUnitFirstGradedQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_mul]
    rfl

@[simp]
theorem completedPrincipalUnitFirstGradedDeltaAction_apply_class
    (a : CyclotomicUnitDelta p) (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitFirstGradedDeltaAction (p := p) K a
        (completedPrincipalUnitFirstGradedClass p K u) =
      completedPrincipalUnitFirstGradedClass p K
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1 u) :=
  completedPrincipalUnitFirstGradedQuotientEquiv_mk (p := p) (K := K) a u

@[simp]
theorem completedPrincipalUnitSubgroupEquiv_zetaPrincipalUnit
    (a : CyclotomicUnitDelta p) :
    completedPrincipalUnitSubgroupEquiv (p := p) K a 1
        (completedLocalCyclotomicZetaPrincipalUnit p K) =
      completedLocalCyclotomicZetaPrincipalUnit p K ^ (a : ZMod p).val :=
  Subtype.ext <| completedLocalCyclotomicUnitEquiv_zetaUnit (p := p) (K := K) a

/-- The distinguished zeta class in the first completed graded quotient. -/
noncomputable def completedLocalCyclotomicZetaFirstGradedClass :
    completedPrincipalUnitFirstGradedQuotient p K :=
  completedPrincipalUnitFirstGradedClass p K
    (completedLocalCyclotomicZetaPrincipalUnit p K)

/-- On the first completed graded quotient, the distinguished zeta class
transforms by the Teichmuller character. -/
@[simp]
theorem completedPrincipalUnitFirstGradedDeltaAction_apply_zetaClass
    (a : CyclotomicUnitDelta p) :
    completedPrincipalUnitFirstGradedDeltaAction (p := p) K a
        (completedLocalCyclotomicZetaFirstGradedClass p K) =
      completedLocalCyclotomicZetaFirstGradedClass p K ^ (a : ZMod p).val := by
  change completedPrincipalUnitFirstGradedDeltaAction (p := p) K a
      (completedPrincipalUnitFirstGradedClass p K
        (completedLocalCyclotomicZetaPrincipalUnit p K)) =
    completedPrincipalUnitFirstGradedClass p K
        (completedLocalCyclotomicZetaPrincipalUnit p K) ^ (a : ZMod p).val
  rw [completedPrincipalUnitFirstGradedDeltaAction_apply_class,
    completedPrincipalUnitSubgroupEquiv_zetaPrincipalUnit, map_pow]

/-- The subgroup `completed U_{n+1}`, viewed inside `completed U_n`. -/
abbrev completedPrincipalUnitGradedSubgroup (n : ℕ) :
    Subgroup (completedPrincipalUnitSubgroup p K n) :=
  (completedPrincipalUnitSubgroup p K (n + 1)).subgroupOf
    (completedPrincipalUnitSubgroup p K n)

@[simp]
theorem mem_completedPrincipalUnitGradedSubgroup_iff
    {n : ℕ} {u : completedPrincipalUnitSubgroup p K n} :
    u ∈ completedPrincipalUnitGradedSubgroup p K n ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈
        completedPrincipalUnitSubgroup p K (n + 1) :=
  Iff.rfl

/-- The completed graded quotient `completed U_n / completed U_{n+1}`. -/
abbrev completedPrincipalUnitGradedQuotient (n : ℕ) : Type _ :=
  completedPrincipalUnitSubgroup p K n ⧸ completedPrincipalUnitGradedSubgroup p K n

/-- The quotient map `completed U_n -> completed U_n / completed U_{n+1}`. -/
def completedPrincipalUnitGradedClass (n : ℕ) :
    completedPrincipalUnitSubgroup p K n →*
      completedPrincipalUnitGradedQuotient p K n :=
  QuotientGroup.mk' (completedPrincipalUnitGradedSubgroup p K n)

@[simp]
theorem completedPrincipalUnitGradedClass_apply
    (n : ℕ) (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitGradedClass p K n u = QuotientGroup.mk u :=
  rfl

theorem completedPrincipalUnitGradedSubgroup_map
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    (completedPrincipalUnitGradedSubgroup p K n).map
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n).toMonoidHom =
      completedPrincipalUnitGradedSubgroup p K n := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v ∈ completedPrincipalUnitGradedSubgroup p K n at hv
    change completedPrincipalUnitSubgroupEquiv (p := p) K a n v ∈
      completedPrincipalUnitGradedSubgroup p K n
    rw [mem_completedPrincipalUnitGradedSubgroup_iff] at hv ⊢
    exact completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitSubgroup
      (p := p) (K := K) a hv
  · intro hu
    refine ⟨(completedPrincipalUnitSubgroupEquiv (p := p) K a n).symm u, ?_, ?_⟩
    · change u ∈ completedPrincipalUnitGradedSubgroup p K n at hu
      rw [mem_completedPrincipalUnitGradedSubgroup_iff] at hu
      change ((completedPrincipalUnitSubgroupEquiv (p := p) K a n).symm u :
          completedPrincipalUnitSubgroup p K n) ∈
        completedPrincipalUnitGradedSubgroup p K n
      rw [mem_completedPrincipalUnitGradedSubgroup_iff]
      exact completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitSubgroup
        (p := p) (K := K) a hu
    · exact (completedPrincipalUnitSubgroupEquiv (p := p) K a n).right_inv u

/-- The induced cyclotomic action on `completed U_n / completed U_{n+1}`. -/
noncomputable def completedPrincipalUnitGradedQuotientEquiv
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    completedPrincipalUnitGradedQuotient p K n ≃*
      completedPrincipalUnitGradedQuotient p K n :=
  QuotientGroup.congr
    (completedPrincipalUnitGradedSubgroup p K n)
    (completedPrincipalUnitGradedSubgroup p K n)
    (completedPrincipalUnitSubgroupEquiv (p := p) K a n)
    (completedPrincipalUnitGradedSubgroup_map (p := p) (K := K) a n)

@[simp]
theorem completedPrincipalUnitGradedQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (n : ℕ)
    (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitGradedQuotientEquiv (p := p) K a n
        (completedPrincipalUnitGradedClass p K n u) =
      completedPrincipalUnitGradedClass p K n
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) :=
  rfl

/-- The actual `Delta` action on `completed U_n / completed U_{n+1}`. -/
noncomputable def completedPrincipalUnitGradedDeltaAction (n : ℕ) :
    CyclotomicUnitDelta p →*
      MulAut (completedPrincipalUnitGradedQuotient p K n) where
  toFun a := completedPrincipalUnitGradedQuotientEquiv (p := p) K a n
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitGradedQuotientEquiv (p := p) K 1 n
        (completedPrincipalUnitGradedClass p K n u) =
      completedPrincipalUnitGradedClass p K n u
    rw [completedPrincipalUnitGradedQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_one]
    rfl
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitGradedQuotientEquiv (p := p) K (a * b) n
        (completedPrincipalUnitGradedClass p K n u) =
      completedPrincipalUnitGradedQuotientEquiv (p := p) K a n
        (completedPrincipalUnitGradedQuotientEquiv (p := p) K b n
          (completedPrincipalUnitGradedClass p K n u))
    rw [completedPrincipalUnitGradedQuotientEquiv_mk,
      completedPrincipalUnitGradedQuotientEquiv_mk,
      completedPrincipalUnitGradedQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_mul]
    rfl

@[simp]
theorem completedPrincipalUnitGradedDeltaAction_apply_class
    (a : CyclotomicUnitDelta p) (n : ℕ)
    (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitGradedDeltaAction (p := p) K n a
        (completedPrincipalUnitGradedClass p K n u) =
      completedPrincipalUnitGradedClass p K n
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n u) :=
  completedPrincipalUnitGradedQuotientEquiv_mk (p := p) (K := K) a n u

set_option maxHeartbeats 800000 in
-- Moving from the additive congruence on `m^n` to units expands several
-- completed-ring coercions and a binomial congruence for `(1 + x)^k`.
theorem completedPrincipalUnitSubgroupEquiv_sub_pow_zmodPowVal_mem_succ
    {n : ℕ} (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    (u : completedPrincipalUnitSubgroup p K n) :
    (((completedPrincipalUnitSubgroupEquiv (p := p) K a n u :
        completedPrincipalUnitSubgroup p K n) :
        completedLocalCyclotomicUnitGroup p K) :
        completedLocalCyclotomicRing p K) -
      ((((u : completedPrincipalUnitSubgroup p K n) ^
            (((a : ZMod p) ^ n).val) :
            completedPrincipalUnitSubgroup p K n) :
            completedLocalCyclotomicUnitGroup p K) :
            completedLocalCyclotomicRing p K) ∈
      completedLocalCyclotomicMaximalIdeal p K ^ (n + 1) := by
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let c : ℕ := ((a : ZMod p) ^ n).val
  let x : S := ((u : completedPrincipalUnitSubgroup p K n) :
      completedLocalCyclotomicUnitGroup p K) - 1
  have hx : x ∈ M ^ n := by
    simpa [S, M, x] using
      (mem_completedPrincipalUnitSubgroup_iff (p := p) (K := K) (n := n)
        (u := (u : completedLocalCyclotomicUnitGroup p K))).mp u.2
  have hσx :
      completedLocalCyclotomicRingEquiv (p := p) K a x - (c : S) * x ∈ M ^ (n + 1) := by
    simpa [S, M, c] using
      completedLocalCyclotomicRingEquiv_sub_zmodPowVal_mul_mem_succ
        (p := p) (K := K) a hx
  have hpow :
      (1 + x) ^ c - 1 - (c : S) * x ∈ M ^ (n + 1) :=
    one_add_pow_sub_one_sub_natCast_mul_mem_pow_succ M hn hx c
  have hu_eq :
      (((u : completedPrincipalUnitSubgroup p K n) :
        completedLocalCyclotomicUnitGroup p K) : S) = 1 + x := by
    dsimp [x]
    ring
  have hσu :
      (((completedPrincipalUnitSubgroupEquiv (p := p) K a n u :
          completedPrincipalUnitSubgroup p K n) :
          completedLocalCyclotomicUnitGroup p K) : S) =
        1 + completedLocalCyclotomicRingEquiv (p := p) K a x := by
    change completedLocalCyclotomicRingEquiv (p := p) K a
        (((u : completedPrincipalUnitSubgroup p K n) :
          completedLocalCyclotomicUnitGroup p K) : S) =
      1 + completedLocalCyclotomicRingEquiv (p := p) K a x
    rw [hu_eq, map_add, map_one]
  have hupow :
      (((((u : completedPrincipalUnitSubgroup p K n) ^ c :
          completedPrincipalUnitSubgroup p K n) :
          completedLocalCyclotomicUnitGroup p K) : S)) =
        (1 + x) ^ c := by
    change ((((u : completedPrincipalUnitSubgroup p K n) :
        completedLocalCyclotomicUnitGroup p K) ^ c :
        completedLocalCyclotomicUnitGroup p K) : S) = (1 + x) ^ c
    rw [Units.val_pow_eq_pow_val, hu_eq]
  rw [hσu, hupow]
  have hsub :
      (completedLocalCyclotomicRingEquiv (p := p) K a x - (c : S) * x) -
        ((1 + x) ^ c - 1 - (c : S) * x) ∈ M ^ (n + 1) :=
    Ideal.sub_mem _ hσx hpow
  convert hsub using 1
  ring

theorem completedPrincipalUnitGradedDeltaAction_apply_class_eq_pow
    {n : ℕ} (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    (u : completedPrincipalUnitSubgroup p K n) :
    completedPrincipalUnitGradedDeltaAction (p := p) K n a
        (completedPrincipalUnitGradedClass p K n u) =
      completedPrincipalUnitGradedClass p K n u ^
        ((a : ZMod p) ^ n).val := by
  rw [completedPrincipalUnitGradedDeltaAction_apply_class, ← map_pow]
  apply (QuotientGroup.eq).2
  rw [mem_completedPrincipalUnitGradedSubgroup_iff]
  let S := completedLocalCyclotomicRing p K
  let M := completedLocalCyclotomicMaximalIdeal p K
  let c : ℕ := ((a : ZMod p) ^ n).val
  let su : completedLocalCyclotomicUnitGroup p K :=
    (completedPrincipalUnitSubgroupEquiv (p := p) K a n u :
      completedPrincipalUnitSubgroup p K n)
  let upow : completedLocalCyclotomicUnitGroup p K :=
    ((u : completedPrincipalUnitSubgroup p K n) ^ c :
      completedPrincipalUnitSubgroup p K n)
  have hdiff : (su : S) - (upow : S) ∈ M ^ (n + 1) := by
    simpa [S, M, c, su, upow] using
      completedPrincipalUnitSubgroupEquiv_sub_pow_zmodPowVal_mem_succ
        (p := p) (K := K) hn a u
  rw [mem_completedPrincipalUnitSubgroup_iff]
  change ((su⁻¹ * upow : completedLocalCyclotomicUnitGroup p K) : S) - 1 ∈
    M ^ (n + 1)
  have hneg : (upow : S) - (su : S) ∈ M ^ (n + 1) := by
    simpa [sub_eq_add_neg, add_comm] using (M ^ (n + 1)).neg_mem hdiff
  have hunit :
      ((su⁻¹ * upow : completedLocalCyclotomicUnitGroup p K) : S) - 1 =
        ((su⁻¹ : completedLocalCyclotomicUnitGroup p K) : S) *
          ((upow : S) - (su : S)) := by
    calc
      ((su⁻¹ * upow : completedLocalCyclotomicUnitGroup p K) : S) - 1 =
          ((su⁻¹ : completedLocalCyclotomicUnitGroup p K) : S) * (upow : S) -
            ((su⁻¹ : completedLocalCyclotomicUnitGroup p K) : S) * (su : S) := by
            simp
      _ = ((su⁻¹ : completedLocalCyclotomicUnitGroup p K) : S) *
          ((upow : S) - (su : S)) := by ring
  rw [hunit]
  exact Ideal.mul_mem_left (M ^ (n + 1))
    ((su⁻¹ : completedLocalCyclotomicUnitGroup p K) : S) hneg

theorem completedPrincipalUnitGradedDeltaAction_apply_eq_pow
    {n : ℕ} (hn : 1 ≤ n) (a : CyclotomicUnitDelta p)
    (x : completedPrincipalUnitGradedQuotient p K n) :
    completedPrincipalUnitGradedDeltaAction (p := p) K n a x =
      x ^ ((a : ZMod p) ^ n).val := by
  refine QuotientGroup.induction_on x ?_
  intro u
  exact completedPrincipalUnitGradedDeltaAction_apply_class_eq_pow
    (p := p) (K := K) hn a u

theorem completedPrincipalUnitGradedQuotient_pow_eq_one
    {n : ℕ} (hn : 1 ≤ n)
    (x : completedPrincipalUnitGradedQuotient p K n) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro u
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff
    (N := completedPrincipalUnitGradedSubgroup p K n) (u ^ p)).2 (by
      rw [mem_completedPrincipalUnitGradedSubgroup_iff]
      change ((u : completedLocalCyclotomicUnitGroup p K) ^ p) ∈
        completedPrincipalUnitSubgroup p K (n + 1)
      exact pow_mem_completedPrincipalUnitSubgroup_succ_of_pos
        (p := p) (K := K) hn u.2)

/-- Positive completed graded quotients are additive `ZMod p`-modules. -/
instance completedPrincipalUnitGradedQuotientModuleZMod
    (n : ℕ) [Fact (1 ≤ n)] :
    Module (ZMod p) (Additive (completedPrincipalUnitGradedQuotient p K n)) :=
  AddCommGroup.zmodModule (n := p) fun x ↦ by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    simpa using completedPrincipalUnitGradedQuotient_pow_eq_one
      (p := p) (K := K) (n := n) (Fact.out : 1 ≤ n) x.toMul

/-- The completed graded quotient action as a `ZMod p`-linear equivalence. -/
noncomputable def completedPrincipalUnitGradedLinearEquivZMod
    (n : ℕ) [Fact (1 ≤ n)] (a : CyclotomicUnitDelta p) :
    Additive (completedPrincipalUnitGradedQuotient p K n) ≃ₗ[ZMod p]
      Additive (completedPrincipalUnitGradedQuotient p K n) where
  __ := MulEquiv.toAdditive ((completedPrincipalUnitGradedDeltaAction (p := p) K n) a)
  map_smul' c x :=
    ZMod.map_smul
      ((MulEquiv.toAdditive
        ((completedPrincipalUnitGradedDeltaAction (p := p) K n) a)).toAddMonoidHom) c x

@[simp]
theorem completedPrincipalUnitGradedLinearEquivZMod_apply
    (n : ℕ) [Fact (1 ≤ n)] (a : CyclotomicUnitDelta p)
    (x : Additive (completedPrincipalUnitGradedQuotient p K n)) :
    completedPrincipalUnitGradedLinearEquivZMod (p := p) K n a x =
      Additive.ofMul ((completedPrincipalUnitGradedDeltaAction (p := p) K n) a x.toMul) :=
  rfl

/-- The actual `Delta` action on a positive completed graded quotient as a
`ZMod p`-linear action. -/
noncomputable def completedPrincipalUnitGradedDeltaActionZMod
    (n : ℕ) [Fact (1 ≤ n)] :
    CyclotomicUnitDelta p →*
      (Additive (completedPrincipalUnitGradedQuotient p K n) ≃ₗ[ZMod p]
        Additive (completedPrincipalUnitGradedQuotient p K n)) where
  toFun := completedPrincipalUnitGradedLinearEquivZMod (p := p) K n
  map_one' := by
    ext x
    apply Additive.ext
    change completedPrincipalUnitGradedDeltaAction (p := p) K n 1 x.toMul = x.toMul
    simp
  map_mul' a b := by
    ext x
    apply Additive.ext
    change completedPrincipalUnitGradedDeltaAction (p := p) K n (a * b) x.toMul =
      completedPrincipalUnitGradedDeltaAction (p := p) K n a
        (completedPrincipalUnitGradedDeltaAction (p := p) K n b x.toMul)
    rw [map_mul]
    rfl

@[simp]
theorem completedPrincipalUnitGradedDeltaActionZMod_apply
    (n : ℕ) [Fact (1 ≤ n)] (a : CyclotomicUnitDelta p)
    (x : Additive (completedPrincipalUnitGradedQuotient p K n)) :
    completedPrincipalUnitGradedDeltaActionZMod (p := p) K n a x =
      Additive.ofMul ((completedPrincipalUnitGradedDeltaAction (p := p) K n) a x.toMul) :=
  rfl

set_option synthInstance.maxHeartbeats 80000 in
-- The `ZMod p` module instance is built from the quotient's `p`-torsion proof,
-- and synthesizing it for this displayed scalar action needs a larger budget.
theorem completedPrincipalUnitGradedDeltaActionZMod_apply_eq_smul
    (n : ℕ) [Fact (1 ≤ n)] (a : CyclotomicUnitDelta p)
    (x : Additive (completedPrincipalUnitGradedQuotient p K n)) :
    completedPrincipalUnitGradedDeltaActionZMod (p := p) K n a x =
      ((a : ZMod p) ^ n) • x := by
  let c : ZMod p := (a : ZMod p) ^ n
  apply Additive.ext
  change completedPrincipalUnitGradedDeltaAction (p := p) K n a x.toMul =
    (c • x).toMul
  have hsmul_toMul : (c • x).toMul = x.toMul ^ c.val := by
    haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, toMul_nsmul]
  rw [hsmul_toMul]
  exact completedPrincipalUnitGradedDeltaAction_apply_eq_pow
    (p := p) (K := K) (n := n) (Fact.out : 1 ≤ n) a x.toMul

/-- The `i`-th character projection on the positive completed graded quotient
`completed U_n / completed U_{n+1}`. -/
noncomputable def completedPrincipalUnitGradedCharacterProjection
    (n : ℕ) [Fact (1 ≤ n)] (i : ℕ) :
    Additive (completedPrincipalUnitGradedQuotient p K n) →ₗ[ZMod p]
      Additive (completedPrincipalUnitGradedQuotient p K n) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact SingularKummer.CharacterProjection.characterProjection (p := p) i
    (completedPrincipalUnitGradedDeltaActionZMod (p := p) K n)

/-- The range of the `i`-th character projection on the positive completed
graded quotient `completed U_n / completed U_{n+1}`. -/
noncomputable def completedPrincipalUnitGradedCharacterProjectionRange
    (n : ℕ) [Fact (1 ≤ n)] (i : ℕ) :
    Submodule (ZMod p) (Additive (completedPrincipalUnitGradedQuotient p K n)) :=
  LinearMap.range (completedPrincipalUnitGradedCharacterProjection (p := p) K n i)

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular

end
