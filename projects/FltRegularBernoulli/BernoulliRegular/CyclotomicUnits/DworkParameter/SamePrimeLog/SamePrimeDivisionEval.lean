module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.CompletedRing.IntegralCoefficientMap

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

/-- Same-prime quotient value of `z / n`, where the `p`-power part of `n` is
cancelled by lambda-adic order and the prime-to-`p` part is inverted in the
finite quotient. -/
noncomputable def samePrimeNatDivEval (N n s : ℕ) (hn : n ≠ 0)
    (z : ValuedIntegerRing p K)
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
      (samePrimeNatDivNumerator (p := p) (K := K) n s z hz) *
    quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
      (samePrimeFiniteLog_ordCompl_coprime (p := p) hn)

theorem samePrimeNatDivEval_mem_map_lambdaIdeal_pow {N n s : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz ∈
      Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
        ((lambdaIdeal p K) ^ s) :=
  (Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      ((lambdaIdeal p K) ^ s)).mul_mem_right
        (quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
          (samePrimeFiniteLog_ordCompl_coprime (p := p) hn))
        (Ideal.mem_map_of_mem (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
          (samePrimeNatDivNumerator_mem_lambdaIdeal_pow (p := p) (K := K) hz))

theorem samePrimeNatDivEval_eq_zero_of_succ_le {N n s : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hs : N + 1 ≤ s) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz = 0 := by
  rcases (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      Ideal.Quotient.mk_surjective).1
      (samePrimeNatDivEval_mem_map_lambdaIdeal_pow
        (p := p) (K := K) hn hz) with
    ⟨y, hy, hyq⟩
  rw [← hyq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_le_pow_right hs hy

theorem samePrimeNatDivEval_natCast_mul_eq_mk {N n s : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (n : ValuedIntegerRing p K) *
      samePrimeNatDivEval (p := p) (K := K) N n s hn z hz =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) z := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  let v : ℕ := n.factorization p
  let c : ℕ := ordCompl[p] n
  let y : R := samePrimeNatDivNumerator (p := p) (K := K) n s z hz
  have hc : Nat.Coprime c p := samePrimeFiniteLog_ordCompl_coprime (p := p) hn
  have hn_decomp_nat : p ^ v * c = n := by
    simpa [v, c] using Nat.ordProj_mul_ordCompl_eq_self n p
  have hn_cast : (n : R) = (p : R) ^ v * (c : R) := by
    rw [← hn_decomp_nat, Nat.cast_mul, Nat.cast_pow]
  have hnum : (p : R) ^ v * y = z := by
    simpa [v, y] using
      samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz
  have hinv :
      q (c : R) * quotientNatCastInv (p := p) (K := K) N c hc = 1 :=
    quotientNatCastInv_spec_right (p := p) (K := K) N c hc
  change q (n : R) *
      (q y * quotientNatCastInv (p := p) (K := K) N c hc) =
    q z
  rw [hn_cast, map_mul]
  calc
    q ((p : R) ^ v) * q (c : R) *
        (q y * quotientNatCastInv (p := p) (K := K) N c hc)
        = (q (c : R) * quotientNatCastInv (p := p) (K := K) N c hc) *
            (q ((p : R) ^ v) * q y) := by ring
    _ = q ((p : R) ^ v * y) := by
          rw [hinv, one_mul, ← map_mul]
    _ = q z := by rw [hnum]

theorem samePrimeNatDivEval_zero {N n s : ℕ} (hn : n ≠ 0)
    (hzero : (0 : ValuedIntegerRing p K) ∈
      (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn 0 hzero = 0 := by
  have hnum_mul :=
    samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hzero
  have hp_pow_ne :
      (p : ValuedIntegerRing p K) ^ n.factorization p ≠ 0 :=
    pow_ne_zero _ (natCast_prime_ne_zero_valuedInteger (p := p) (K := K))
  have hnum_zero :
      samePrimeNatDivNumerator (p := p) (K := K) n s 0 hzero = 0 :=
    (mul_eq_zero.mp hnum_mul).resolve_left hp_pow_ne
  simp [samePrimeNatDivEval, hnum_zero]

theorem samePrimeNatDivNumerator_eq_of_spec {n s : ℕ}
    {z y : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hy : (p : ValuedIntegerRing p K) ^ n.factorization p * y = z) :
    samePrimeNatDivNumerator (p := p) (K := K) n s z hz = y := by
  have hchosen :
      (p : ValuedIntegerRing p K) ^ n.factorization p *
          samePrimeNatDivNumerator (p := p) (K := K) n s z hz = z :=
    samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz
  exact mul_left_cancel₀
    (pow_ne_zero _ (natCast_prime_ne_zero_valuedInteger (p := p) (K := K)))
    (by rw [hchosen, hy])

theorem samePrimeNatDivEval_eq_of_spec {N n s : ℕ} (hn : n ≠ 0)
    {z y : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hy : (p : ValuedIntegerRing p K) ^ n.factorization p * y = z) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) y *
        quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
          (samePrimeFiniteLog_ordCompl_coprime (p := p) hn) := by
  rw [samePrimeNatDivEval,
    samePrimeNatDivNumerator_eq_of_spec (p := p) (K := K) hz hy]

theorem samePrimeNatDivEval_eq_of_mem {N n s t : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K}
    (hzs : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hzt : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + t)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hzs =
      samePrimeNatDivEval (p := p) (K := K) N n t hn z hzt := by
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hn hzt
    (samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hzs)]
  rfl

theorem samePrimeNatDivEval_eq_of_eq {N n s : ℕ} (hn : n ≠ 0)
    {z w : ValuedIntegerRing p K} (hzw : z = w)
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hw : w ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz =
      samePrimeNatDivEval (p := p) (K := K) N n s hn w hw := by
  subst w
  exact samePrimeNatDivEval_eq_of_mem (p := p) (K := K) hn hz hw

theorem samePrimeNatDivEval_add {N n s : ℕ} (hn : n ≠ 0)
    {z₁ z₂ : ValuedIntegerRing p K}
    (hz₁ : z₁ ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hz₂ : z₂ ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hz₁₂ : z₁ + z₂ ∈
      (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn (z₁ + z₂) hz₁₂ =
      samePrimeNatDivEval (p := p) (K := K) N n s hn z₁ hz₁ +
        samePrimeNatDivEval (p := p) (K := K) N n s hn z₂ hz₂ := by
  let y₁ : ValuedIntegerRing p K :=
    samePrimeNatDivNumerator (p := p) (K := K) n s z₁ hz₁
  let y₂ : ValuedIntegerRing p K :=
    samePrimeNatDivNumerator (p := p) (K := K) n s z₂ hz₂
  have hrepr :
      (p : ValuedIntegerRing p K) ^ n.factorization p * (y₁ + y₂) =
        z₁ + z₂ := by
    rw [mul_add, samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz₁,
      samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz₂]
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hn hz₁₂ hrepr,
    samePrimeNatDivEval, samePrimeNatDivEval]
  rw [map_add]
  ring

theorem samePrimeNatDivEval_neg {N n s : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hneg : -z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn (-z) hneg =
      -samePrimeNatDivEval (p := p) (K := K) N n s hn z hz := by
  let y : ValuedIntegerRing p K :=
    samePrimeNatDivNumerator (p := p) (K := K) n s z hz
  have hrepr :
      (p : ValuedIntegerRing p K) ^ n.factorization p * (-y) = -z := by
    rw [mul_neg, samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz]
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hn hneg hrepr,
    samePrimeNatDivEval]
  rw [map_neg]
  ring

theorem samePrimeNatDivEval_mul_left {N n s : ℕ} (hn : n ≠ 0)
    (r : ValuedIntegerRing p K) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hrz : r * z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn (r * z) hrz =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) r *
        samePrimeNatDivEval (p := p) (K := K) N n s hn z hz := by
  let y : ValuedIntegerRing p K :=
    samePrimeNatDivNumerator (p := p) (K := K) n s z hz
  have hrepr :
      (p : ValuedIntegerRing p K) ^ n.factorization p * (r * y) = r * z := by
    calc
      (p : ValuedIntegerRing p K) ^ n.factorization p * (r * y)
          = r * ((p : ValuedIntegerRing p K) ^ n.factorization p * y) := by ring
      _ = r * z := by
          rw [samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz]
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hn hrz hrepr,
    samePrimeNatDivEval]
  rw [map_mul]
  ring

theorem samePrimeNatDivEval_sum {ι : Type*} {N n s : ℕ}
    (hn : n ≠ 0) (t : Finset ι) (z : ι → ValuedIntegerRing p K)
    (hz : ∀ i, z i ∈
      (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hsum : (∑ i ∈ t, z i) ∈
      (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn (∑ i ∈ t, z i) hsum =
      ∑ i ∈ t,
        samePrimeNatDivEval (p := p) (K := K) N n s hn (z i) (hz i) := by
  classical
  revert hsum
  refine Finset.induction_on t ?empty ?insert
  · intro hsum
    simp [samePrimeNatDivEval_zero (p := p) (K := K) hn]
  · intro a t hat ih hsum
    have htail : (∑ i ∈ t, z i) ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) :=
      Ideal.sum_mem _ fun i _hi ↦ hz i
    have hadd : z a + ∑ i ∈ t, z i ∈
        (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
      simpa [Finset.sum_insert, hat] using hsum
    calc
      samePrimeNatDivEval (p := p) (K := K) N n s hn (∑ i ∈ insert a t, z i) hsum
          =
        samePrimeNatDivEval (p := p) (K := K) N n s hn
          (z a + ∑ i ∈ t, z i) hadd := by
          congr 1
          simp [Finset.sum_insert, hat]
      _ =
        samePrimeNatDivEval (p := p) (K := K) N n s hn (z a) (hz a) +
          samePrimeNatDivEval (p := p) (K := K) N n s hn
            (∑ i ∈ t, z i) htail := by
          rw [samePrimeNatDivEval_add (p := p) (K := K) hn (hz a) htail hadd]
      _ =
        samePrimeNatDivEval (p := p) (K := K) N n s hn (z a) (hz a) +
          ∑ i ∈ t,
            samePrimeNatDivEval (p := p) (K := K) N n s hn (z i) (hz i) := by
          rw [ih htail]
      _ =
        ∑ i ∈ insert a t,
          samePrimeNatDivEval (p := p) (K := K) N n s hn (z i) (hz i) := by
          simp [Finset.sum_insert, hat]

theorem samePrimeNatDivEval_mul_denominator_right {N n m s : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hmz : (m : ValuedIntegerRing p K) * z ∈
      (lambdaIdeal p K) ^ ((n * m).factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N (n * m) s
        (Nat.mul_ne_zero hn hm) ((m : ValuedIntegerRing p K) * z) hmz =
      samePrimeNatDivEval (p := p) (K := K) N n s hn z hz := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn hm
  let vn : ℕ := n.factorization p
  let vm : ℕ := m.factorization p
  let y : R := samePrimeNatDivNumerator (p := p) (K := K) n s z hz
  let cn : ℕ := ordCompl[p] n
  let cm : ℕ := ordCompl[p] m
  have hfac : (n * m).factorization p = vn + vm := by
    simpa [vn, vm] using
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_mul hn hm)
  have hspec : ((p : R) ^ vn) * y = z := by
    simpa [R, vn, y] using
      samePrimeNatDivNumerator_mul_spec (p := p) (K := K) hz
  have hm_decomp_nat : p ^ vm * ordCompl[p] m = m := by
    simpa [vm] using Nat.ordProj_mul_ordCompl_eq_self m p
  have hm_cast : (m : R) = ((p : R) ^ vm) * (cm : R) := by
    rw [← hm_decomp_nat]
    simp [R, vm, cm, Nat.cast_mul, Nat.cast_pow]
  have hrepr :
      (p : R) ^ (n * m).factorization p * (y * (cm : R)) =
        (m : R) * z := by
    calc
      (p : R) ^ (n * m).factorization p * (y * (cm : R))
          = (((p : R) ^ vn) * y) * (((p : R) ^ vm) * (cm : R)) := by
              rw [hfac, pow_add]
              ring
      _ = z * (m : R) := by
              rw [hspec, ← hm_cast]
      _ = (m : R) * z := by
              ring
  have hcn : Nat.Coprime cn p := samePrimeFiniteLog_ordCompl_coprime (p := p) hn
  have hcm : Nat.Coprime cm p := samePrimeFiniteLog_ordCompl_coprime (p := p) hm
  have hprod_inv :
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] (n * m))
          (samePrimeFiniteLog_ordCompl_coprime (p := p) hnm) =
        quotientNatCastInv (p := p) (K := K) N cm hcm *
          quotientNatCastInv (p := p) (K := K) N cn hcn := by
    refine quotientNatCastInv_eq_of_mul_right_eq_one
      (p := p) (K := K) (N := N) (m := ordCompl[p] (n * m))
      (samePrimeFiniteLog_ordCompl_coprime (p := p) hnm) ?_
    have hord : ordCompl[p] (n * m) = cn * cm := by
      simp [cn, cm, Nat.ordCompl_mul]
    rw [hord, Nat.cast_mul, map_mul]
    calc
      q (cn : R) * q (cm : R) *
          (quotientNatCastInv (p := p) (K := K) N cm hcm *
            quotientNatCastInv (p := p) (K := K) N cn hcn)
          =
        (q (cm : R) * quotientNatCastInv (p := p) (K := K) N cm hcm) *
          (q (cn : R) * quotientNatCastInv (p := p) (K := K) N cn hcn) := by
            ring
      _ = 1 := by
            rw [quotientNatCastInv_spec_right (p := p) (K := K) N cm hcm,
              quotientNatCastInv_spec_right (p := p) (K := K) N cn hcn]
            simp
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hnm hmz hrepr,
    samePrimeNatDivEval]
  change q (y * (cm : R)) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] (n * m))
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hnm) =
    q y * quotientNatCastInv (p := p) (K := K) N cn hcn
  rw [hprod_inv, map_mul]
  calc
    q y * q (cm : R) *
        (quotientNatCastInv (p := p) (K := K) N cm hcm *
          quotientNatCastInv (p := p) (K := K) N cn hcn)
        =
      q y *
        ((q (cm : R) * quotientNatCastInv (p := p) (K := K) N cm hcm) *
          quotientNatCastInv (p := p) (K := K) N cn hcn) := by
        ring
    _ = q y * quotientNatCastInv (p := p) (K := K) N cn hcn := by
        rw [quotientNatCastInv_spec_right (p := p) (K := K) N cm hcm]
        ring

theorem samePrimeNatDivEval_add_common_denominator {N n m s : ℕ} (hn : n ≠ 0)
    (hm : m ≠ 0) {z w : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hw : w ∈ (lambdaIdeal p K) ^ (m.factorization p * (p - 1) + s))
    (hzw : (m : ValuedIntegerRing p K) * z + (n : ValuedIntegerRing p K) * w ∈
      (lambdaIdeal p K) ^ ((n * m).factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz +
        samePrimeNatDivEval (p := p) (K := K) N m s hm w hw =
      samePrimeNatDivEval (p := p) (K := K) N (n * m) s
        (Nat.mul_ne_zero hn hm)
        ((m : ValuedIntegerRing p K) * z + (n : ValuedIntegerRing p K) * w) hzw := by
  have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn hm
  have hfac : (n * m).factorization p =
      n.factorization p + m.factorization p := by
    simpa using
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_mul hn hm)
  have hmz : (m : ValuedIntegerRing p K) * z ∈
      (lambdaIdeal p K) ^ ((n * m).factorization p * (p - 1) + s) := by
    have h := natCast_mul_mem_lambdaIdeal_pow_factorization_mul_pred_add
      (p := p) (K := K) (c := m) hz
    simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h
  have hnw : (n : ValuedIntegerRing p K) * w ∈
      (lambdaIdeal p K) ^ ((n * m).factorization p * (p - 1) + s) := by
    have h := natCast_mul_mem_lambdaIdeal_pow_factorization_mul_pred_add
      (p := p) (K := K) (c := n) hw
    simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h
  have hchange_z :
      samePrimeNatDivEval (p := p) (K := K) N (n * m) s hnm
          ((m : ValuedIntegerRing p K) * z) hmz =
        samePrimeNatDivEval (p := p) (K := K) N n s hn z hz :=
    samePrimeNatDivEval_mul_denominator_right (p := p) (K := K)
      (N := N) hn hm hz hmz
  have hchange_w :
      samePrimeNatDivEval (p := p) (K := K) N (n * m) s hnm
          ((n : ValuedIntegerRing p K) * w) hnw =
        samePrimeNatDivEval (p := p) (K := K) N m s hm w hw := by
    have hnw_mn :
        (n : ValuedIntegerRing p K) * w ∈
          (lambdaIdeal p K) ^ ((m * n).factorization p * (p - 1) + s) := by
      simpa [Nat.mul_comm] using hnw
    have h := samePrimeNatDivEval_mul_denominator_right (p := p) (K := K)
      (N := N) hm hn hw hnw_mn
    simpa [Nat.mul_comm] using h
  calc
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz +
        samePrimeNatDivEval (p := p) (K := K) N m s hm w hw
        =
      samePrimeNatDivEval (p := p) (K := K) N (n * m) s hnm
          ((m : ValuedIntegerRing p K) * z) hmz +
        samePrimeNatDivEval (p := p) (K := K) N (n * m) s hnm
          ((n : ValuedIntegerRing p K) * w) hnw := by
        rw [← hchange_z, ← hchange_w]
    _ =
      samePrimeNatDivEval (p := p) (K := K) N (n * m) s hnm
        ((m : ValuedIntegerRing p K) * z + (n : ValuedIntegerRing p K) * w) hzw := by
        rw [← samePrimeNatDivEval_add (p := p) (K := K) hnm hmz hnw hzw]

theorem samePrimeNatDivEval_factorial_weighted_mem {d n s : ℕ} (hn : n ≠ 0)
    (hnd : n ≤ d) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s) := by
  have hdiv : n ∣ d.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hm : d.factorial / n ≠ 0 := by
    intro hm0
    have hfac0 : d.factorial = 0 := by
      simpa [hm0] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hfac :
      d.factorial.factorization p =
        (d.factorial / n).factorization p + n.factorization p := by
    have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_mul hm hn)
    simpa [hmul_div] using h
  have h := natCast_mul_mem_lambdaIdeal_pow_factorization_mul_pred_add
    (p := p) (K := K) (c := d.factorial / n) hz
  simpa [hfac, Nat.add_mul, add_assoc, add_comm, add_left_comm] using h

theorem samePrimeNatDivEval_eq_factorial_denominator {N d n s : ℕ} (hn : n ≠ 0)
    (hnd : n ≤ d) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hDz : (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s)) :
    samePrimeNatDivEval (p := p) (K := K) N n s hn z hz =
      samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d)
        (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z) hDz := by
  have hdiv : n ∣ d.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) hnd
  have hmul_div : d.factorial / n * n = d.factorial := Nat.div_mul_cancel hdiv
  have hm : d.factorial / n ≠ 0 := by
    intro hm0
    have hfac0 : d.factorial = 0 := by
      simpa [hm0] using hmul_div.symm
    exact Nat.factorial_ne_zero d hfac0
  have hmul : n * (d.factorial / n) = d.factorial := by
    simpa [Nat.mul_comm] using hmul_div
  have hmz_nm :
      (((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z) ∈
        (lambdaIdeal p K) ^
          ((n * (d.factorial / n)).factorization p * (p - 1) + s) := by
    simpa [hmul] using hDz
  have h := samePrimeNatDivEval_mul_denominator_right (p := p) (K := K)
    (N := N) hn hm hz hmz_nm
  simpa [hmul] using h.symm

theorem samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_eq_zero
    {N d s : ℕ} (z : ℕ → ValuedIntegerRing p K)
    (hz : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hclear : (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n) = 0) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2)) = 0 := by
  classical
  let t : Finset {n // n ∈ Finset.Icc 1 d} := (Finset.Icc 1 d).attach
  let w : {n // n ∈ Finset.Icc 1 d} → ValuedIntegerRing p K :=
    fun a ↦ ((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1
  have hw : ∀ a, w a ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s) := by
    intro a
    have ha := Finset.mem_Icc.mp a.2
    exact samePrimeNatDivEval_factorial_weighted_mem
      (p := p) (K := K) (Nat.ne_zero_of_lt ha.1) ha.2 (hz a.1 a.2)
  have hsum_zero : (∑ a ∈ t, w a) = 0 := by
    rw [show (∑ a ∈ t, w a) =
        ∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n by
      simpa [t, w] using
        (Finset.sum_attach (Finset.Icc 1 d)
          (fun n ↦ ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n))]
    exact hclear
  have hsum_mem : (∑ a ∈ t, w a) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s) := by
    rw [hsum_zero]
    exact zero_mem _
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2))
        =
      ∑ a ∈ t, samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d) (w a) (hw a) := by
        refine Finset.sum_congr ?_ ?_
        · simp [t]
        · intro a _ha
          dsimp [w]
          have haI : a.1 ∈ Finset.Icc 1 d := a.2
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp haI).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp haI).2
          exact samePrimeNatDivEval_eq_factorial_denominator (p := p) (K := K)
            (N := N) (Nat.ne_zero_of_lt ha1) had (hz a.1 a.2) (hw a)
    _ =
      samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d) (∑ a ∈ t, w a) hsum_mem := by
        rw [← samePrimeNatDivEval_sum (p := p) (K := K) (N := N)
          (n := d.factorial) (s := s) (Nat.factorial_ne_zero d) t w hw hsum_mem]
    _ =
      samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d) 0 (zero_mem _) := by
        congr 1
    _ = 0 :=
        samePrimeNatDivEval_zero (p := p) (K := K) (N := N)
          (n := d.factorial) (s := s) (Nat.factorial_ne_zero d) (zero_mem _)

theorem samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_lambdaIdeal_pow
    {N d s t : ℕ} (z : ℕ → ValuedIntegerRing p K)
    (hz : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s))
    (hclear : (∑ n ∈ Finset.Icc 1 d,
      ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n) ∈
        (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + t))
    (ht : N + 1 ≤ t) :
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2)) = 0 := by
  classical
  let T : Finset {n // n ∈ Finset.Icc 1 d} := (Finset.Icc 1 d).attach
  let w : {n // n ∈ Finset.Icc 1 d} → ValuedIntegerRing p K :=
    fun a ↦ ((d.factorial / a.1 : ℕ) : ValuedIntegerRing p K) * z a.1
  have hw : ∀ a, w a ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s) := by
    intro a
    have ha := Finset.mem_Icc.mp a.2
    exact samePrimeNatDivEval_factorial_weighted_mem
      (p := p) (K := K) (Nat.ne_zero_of_lt ha.1) ha.2 (hz a.1 a.2)
  have hsum_s : (∑ a ∈ T, w a) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + s) :=
    Ideal.sum_mem _ fun a _ha ↦ hw a
  have hsum_t : (∑ a ∈ T, w a) ∈
      (lambdaIdeal p K) ^ (d.factorial.factorization p * (p - 1) + t) := by
    rw [show (∑ a ∈ T, w a) =
        ∑ n ∈ Finset.Icc 1 d,
          ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n by
      simpa [T, w] using
        (Finset.sum_attach (Finset.Icc 1 d)
          (fun n ↦ ((d.factorial / n : ℕ) : ValuedIntegerRing p K) * z n))]
    exact hclear
  calc
    (∑ a ∈ (Finset.Icc 1 d).attach,
      samePrimeNatDivEval (p := p) (K := K) N a.1 s
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (z a.1) (hz a.1 a.2))
        =
      ∑ a ∈ T, samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d) (w a) (hw a) := by
        refine Finset.sum_congr ?_ ?_
        · simp [T]
        · intro a _ha
          dsimp [w]
          have haI : a.1 ∈ Finset.Icc 1 d := a.2
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp haI).1
          have had : a.1 ≤ d := (Finset.mem_Icc.mp haI).2
          exact samePrimeNatDivEval_eq_factorial_denominator (p := p) (K := K)
            (N := N) (Nat.ne_zero_of_lt ha1) had (hz a.1 a.2) (hw a)
    _ =
      samePrimeNatDivEval (p := p) (K := K) N d.factorial s
        (Nat.factorial_ne_zero d) (∑ a ∈ T, w a) hsum_s := by
        rw [← samePrimeNatDivEval_sum (p := p) (K := K) (N := N)
          (n := d.factorial) (s := s) (Nat.factorial_ne_zero d) T w hw hsum_s]
    _ =
      samePrimeNatDivEval (p := p) (K := K) N d.factorial t
        (Nat.factorial_ne_zero d) (∑ a ∈ T, w a) hsum_t :=
        samePrimeNatDivEval_eq_of_mem (p := p) (K := K) (N := N)
          (n := d.factorial) (s := s) (t := t)
          (Nat.factorial_ne_zero d) hsum_s hsum_t
    _ = 0 :=
        samePrimeNatDivEval_eq_zero_of_succ_le
          (p := p) (K := K) (N := N) (n := d.factorial) (s := t)
          (Nat.factorial_ne_zero d) hsum_t ht

/-- Degree-indexed same-prime localized evaluator for a homogeneous numerator
of total lambda-order `d`. -/
noncomputable def samePrimeNatDivEvalAtDegree (N n d : ℕ) (hn : n ≠ 0)
    (z : ValuedIntegerRing p K) (hz : z ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeNatDivEval (p := p) (K := K) N n
    (d - n.factorization p * (p - 1)) hn z (by
      simpa [Nat.add_sub_of_le hden] using hz)

theorem samePrimeNatDivEvalAtDegree_eq_zero_of_cutoff_le {N n d : ℕ}
    (hn : n ≠ 0) (hnd : n ≤ d)
    (hcut : samePrimeFiniteLogCutoff (p := p) N ≤ d)
    {z : ValuedIntegerRing p K} (hz : z ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn z hz hden = 0 := by
  rw [samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K) hn _
    (by
      simpa [samePrimeFiniteLogCutoff] using
        Nat.succ_le_sub_factorization_mul_pred_of_mul_succ_le_of_le
          (ell := p) (N := N) (n := n) (d := d)
          (Fact.out : Nat.Prime p) hcut hnd)

theorem samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval {N n d s : ℕ}
    (hn : n ≠ 0) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d)
    (hzs : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s)) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn z hz hden =
      samePrimeNatDivEval (p := p) (K := K) N n s hn z hzs := by
  rw [samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_eq_of_mem (p := p) (K := K) hn _ hzs

theorem samePrimeNatDivEvalAtDegree_zero {N n d : ℕ} (hn : n ≠ 0)
    (hzero : (0 : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn 0 hzero hden = 0 := by
  rw [samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_zero (p := p) (K := K) hn _

theorem samePrimeNatDivEvalAtDegree_add {N n d : ℕ} (hn : n ≠ 0)
    {z w : ValuedIntegerRing p K} (hz : z ∈ (lambdaIdeal p K) ^ d)
    (hw : w ∈ (lambdaIdeal p K) ^ d) (hzw : z + w ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn (z + w) hzw hden =
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn z hz hden +
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn w hw hden := by
  rw [samePrimeNatDivEvalAtDegree, samePrimeNatDivEvalAtDegree,
    samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_add (p := p) (K := K) hn _ _ _

theorem samePrimeNatDivEvalAtDegree_neg {N n d : ℕ} (hn : n ≠ 0)
    {z : ValuedIntegerRing p K} (hz : z ∈ (lambdaIdeal p K) ^ d)
    (hneg : -z ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn (-z) hneg hden =
      -samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn z hz hden := by
  rw [samePrimeNatDivEvalAtDegree, samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_neg (p := p) (K := K) hn _ _

theorem samePrimeNatDivEvalAtDegree_mul_left {N n d : ℕ} (hn : n ≠ 0)
    (r : ValuedIntegerRing p K) {z : ValuedIntegerRing p K}
    (hz : z ∈ (lambdaIdeal p K) ^ d) (hrz : r * z ∈ (lambdaIdeal p K) ^ d)
    (hden : n.factorization p * (p - 1) ≤ d) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn (r * z) hrz hden =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) r *
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn z hz hden := by
  rw [samePrimeNatDivEvalAtDegree, samePrimeNatDivEvalAtDegree]
  exact samePrimeNatDivEval_mul_left (p := p) (K := K) hn r _ _

/-- Unsigned ordinary finite-logarithm term `x^n / n` in
`R / lambda^(N+1)`. -/
noncomputable def samePrimeFiniteLogTermCore (N n : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  if hn : n = 0 then 0 else
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx) *
      quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
        (samePrimeFiniteLog_ordCompl_coprime (p := p) hn)

/-- Signed ordinary finite-logarithm term `(-1)^(n+1) x^n / n`. -/
noncomputable def samePrimeFiniteLogTerm (N n : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
    samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx

@[simp]
theorem samePrimeFiniteLogTermCore_zero (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N 0 x hx = 0 := by
  simp [samePrimeFiniteLogTermCore]

@[simp]
theorem samePrimeFiniteLogTerm_zero (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N 0 x hx = 0 := by
  simp [samePrimeFiniteLogTerm]

theorem samePrimeFiniteLogTermCore_arg_zero (N n : ℕ) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n 0
        (zero_mem (lambdaIdeal p K)) = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnum_mul :=
    samePrimeFiniteLogTermNumerator_mul_spec (p := p) (K := K) hn
      (x := 0) (zero_mem (lambdaIdeal p K))
  rw [zero_pow hn] at hnum_mul
  have hp_pow_ne :
      (p : ValuedIntegerRing p K) ^ n.factorization p ≠ 0 :=
    pow_ne_zero _ (natCast_prime_ne_zero_valuedInteger (p := p) (K := K))
  have hnum_zero :
      samePrimeFiniteLogTermNumerator (p := p) (K := K) n 0
        (zero_mem (lambdaIdeal p K)) = 0 :=
    (mul_eq_zero.mp hnum_mul).resolve_left hp_pow_ne
  simp [samePrimeFiniteLogTermCore, hn, hnum_zero]

theorem samePrimeFiniteLogTerm_arg_zero (N n : ℕ) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n 0
        (zero_mem (lambdaIdeal p K)) = 0 := by
  simp [samePrimeFiniteLogTerm, samePrimeFiniteLogTermCore_arg_zero]

theorem samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval {N n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx =
      samePrimeNatDivEval (p := p) (K := K) N n
        (samePrimeFiniteLogTermOrder (p := p) n) hn (x ^ n)
        (by
          simpa [factorization_mul_pred_add_samePrimeFiniteLogTermOrder
              (p := p) hn] using
            Ideal.pow_mem_pow hx n) := by
  have hz :
      x ^ n ∈
        (lambdaIdeal p K) ^
          (n.factorization p * (p - 1) + samePrimeFiniteLogTermOrder (p := p) n) := by
    simpa [factorization_mul_pred_add_samePrimeFiniteLogTermOrder
        (p := p) hn] using
      Ideal.pow_mem_pow hx n
  rw [samePrimeFiniteLogTermCore, dif_neg hn]
  rw [samePrimeNatDivEval_eq_of_spec (p := p) (K := K) hn hz
    (samePrimeFiniteLogTermNumerator_mul_spec (p := p) (K := K) hn hx)]

theorem samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree {N n : ℕ}
    (hn : n ≠ 0) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx =
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        (x ^ n) (Ideal.pow_mem_pow hx n)
        (by
          have h := Nat.factorization_mul_pred_le_pred
            (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
          omega) := by
  rw [samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval (p := p) (K := K) hn hx]
  symm
  exact samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
    (p := p) (K := K) hn (Ideal.pow_mem_pow hx n)
    (by
      have h := Nat.factorization_mul_pred_le_pred
        (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
      omega)
    (by
      simpa [factorization_mul_pred_add_samePrimeFiniteLogTermOrder
          (p := p) hn] using
        Ideal.pow_mem_pow hx n)

theorem samePrimeFiniteLogTermCore_natCast_mul_eq_mk {N n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (n : ValuedIntegerRing p K) *
      samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ n) := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let q : R →+* R ⧸ I ^ (N + 1) := Ideal.Quotient.mk (I ^ (N + 1))
  let v : ℕ := n.factorization p
  let c : ℕ := ordCompl[p] n
  let y : R := samePrimeFiniteLogTermNumerator (p := p) (K := K) n x hx
  have hc : Nat.Coprime c p := samePrimeFiniteLog_ordCompl_coprime (p := p) hn
  have hn_decomp_nat : p ^ v * c = n := by
    simpa [v, c] using Nat.ordProj_mul_ordCompl_eq_self n p
  have hn_cast : (n : R) = (p : R) ^ v * (c : R) := by
    rw [← hn_decomp_nat, Nat.cast_mul, Nat.cast_pow]
  have hnum : (p : R) ^ v * y = x ^ n := by
    simpa [v, y] using
      samePrimeFiniteLogTermNumerator_mul_spec (p := p) (K := K) hn hx
  have hinv :
      q (c : R) * quotientNatCastInv (p := p) (K := K) N c hc = 1 :=
    quotientNatCastInv_spec_right (p := p) (K := K) N c hc
  rw [samePrimeFiniteLogTermCore, dif_neg hn]
  change q (n : R) *
      (q y * quotientNatCastInv (p := p) (K := K) N c hc) =
    q (x ^ n)
  rw [hn_cast, map_mul]
  calc
    q ((p : R) ^ v) * q (c : R) *
        (q y * quotientNatCastInv (p := p) (K := K) N c hc)
        = (q (c : R) * quotientNatCastInv (p := p) (K := K) N c hc) *
            (q ((p : R) ^ v) * q y) := by ring
    _ = q ((p : R) ^ v * y) := by
          rw [hinv, one_mul, ← map_mul]
    _ = q (x ^ n) := by rw [hnum]

theorem samePrimeFiniteLogTerm_natCast_mul_eq_mk {N n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (n : ValuedIntegerRing p K) *
      samePrimeFiniteLogTerm (p := p) (K := K) N n x hx =
    ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ n) := by
  rw [samePrimeFiniteLogTerm]
  calc
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (n : ValuedIntegerRing p K) *
      (((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx)
        =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (n : ValuedIntegerRing p K) *
          samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx) := by
            ring
    _ =
      ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) (x ^ n) := by
            rw [samePrimeFiniteLogTermCore_natCast_mul_eq_mk
              (p := p) (K := K) hn hx]

theorem samePrimeFiniteLogTermCore_mem_map_lambdaIdeal_pow {N n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTermCore (p := p) (K := K) N n x hx ∈
      Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
        ((lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n) := by
  rw [samePrimeFiniteLogTermCore, dif_neg hn]
  exact
    (Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      ((lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n)).mul_mem_right
        (quotientNatCastInv (p := p) (K := K) N (ordCompl[p] n)
          (samePrimeFiniteLog_ordCompl_coprime (p := p) hn))
        (Ideal.mem_map_of_mem (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
          (samePrimeFiniteLogTermNumerator_mem_lambdaIdeal_pow
            (p := p) (K := K) hn hx))

theorem samePrimeFiniteLogTerm_mem_map_lambdaIdeal_pow {N n : ℕ} (hn : n ≠ 0)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n x hx ∈
      Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
        ((lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n) :=
  (Ideal.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)))
      ((lambdaIdeal p K) ^ samePrimeFiniteLogTermOrder (p := p) n)).mul_mem_left
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1))
        (samePrimeFiniteLogTermCore_mem_map_lambdaIdeal_pow
          (p := p) (K := K) hn hx)


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
