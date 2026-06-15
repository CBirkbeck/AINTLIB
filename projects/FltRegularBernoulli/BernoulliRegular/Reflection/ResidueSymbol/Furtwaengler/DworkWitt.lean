module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Witt-vector bridge for Dwork splitting

This file contains the Witt-vector uniqueness bridge needed by the all-order
Artin-Hasse/Dwork splitting proof. The key point is that in every quotient
`𝓞 R' / Q^(N+1)`, the residue characteristic `ℓ` is nilpotent, so mathlib's
Teichmüller-series uniqueness theorem for Witt vectors applies.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

theorem wittGhostComponent_mem_ideal_pow_succ_of_coeff_mem
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    {x : WittVector r A} {n : ℕ}
    (hx : ∀ i : ℕ, i ≤ n → x.coeff i ∈ I) :
    WittVector.ghostComponent n x ∈ I ^ (n + 1) := by
  rw [WittVector.ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  refine Ideal.sum_mem _ ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi_le : i ≤ n := Nat.le_of_lt_succ hi
  have hterm :
      (MvPolynomial.aeval x.coeff)
          ((MvPolynomial.monomial (R := ℤ) (Finsupp.single i (r ^ (n - i))))
            (r ^ i)) =
        ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) := by
    simp [MvPolynomial.aeval_monomial, map_pow]
  rw [hterm]
  have hrpow : (r : A) ^ i ∈ I ^ i := Ideal.pow_mem_pow hrI i
  have hxpow : (x.coeff i) ^ (r ^ (n - i)) ∈ I ^ (r ^ (n - i)) :=
    Ideal.pow_mem_pow (hx i hi_le) (r ^ (n - i))
  have hmul :
      ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) ∈
        I ^ (i + r ^ (n - i)) := by
    have hmul' :
        ((r : A) ^ i) * (x.coeff i) ^ (r ^ (n - i)) ∈
          I ^ i * I ^ (r ^ (n - i)) :=
      Ideal.mul_mem_mul hrpow hxpow
    simpa [pow_add] using hmul'
  exact Ideal.pow_le_pow_right
    (by
      have htwo : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
      have hpow :
          n - i + 1 ≤ r ^ (n - i) :=
        ((n - i).lt_two_pow_self).succ_le.trans
          (pow_left_mono (n - i) htwo)
      omega)
    hmul

theorem witt_ker_map_le_ker_mk_comp_ghostComponent
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I) (n : ℕ) :
    RingHom.ker (WittVector.map (Ideal.Quotient.mk I)) ≤
      RingHom.ker
        ((Ideal.Quotient.mk (I ^ (n + 1))).comp (WittVector.ghostComponent (p := r) n)) := by
  intro x hx
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  refine wittGhostComponent_mem_ideal_pow_succ_of_coeff_mem I hrI ?_
  rw [RingHom.mem_ker, WittVector.map_eq_zero_iff] at hx
  intro i _hi
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hx i)

/-- The `n`-th Witt ghost component descends from `W(A/I)` to
`A/I^(n+1)` whenever the Witt prime lies in `I`. -/
noncomputable def wittGhostComponentModIdealPow
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I) (n : ℕ) :
    WittVector r (A ⧸ I) →+* A ⧸ I ^ (n + 1) :=
  RingHom.liftOfSurjective (WittVector.map (Ideal.Quotient.mk I))
    (WittVector.map_surjective _ Ideal.Quotient.mk_surjective)
    ⟨(Ideal.Quotient.mk (I ^ (n + 1))).comp (WittVector.ghostComponent (p := r) n),
      witt_ker_map_le_ker_mk_comp_ghostComponent I hrI n⟩

@[simp]
theorem wittGhostComponentModIdealPow_map_mk
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    (n : ℕ) (x : WittVector r A) :
    wittGhostComponentModIdealPow I hrI n
        (WittVector.map (Ideal.Quotient.mk I) x) =
      Ideal.Quotient.mk (I ^ (n + 1)) (WittVector.ghostComponent n x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

@[simp]
theorem wittGhostComponentModIdealPow_teichmuller_mk
    {r : ℕ} [Fact (Nat.Prime r)]
    {A : Type*} [CommRing A] (I : Ideal A) (hrI : (r : A) ∈ I)
    (n : ℕ) (a : A) :
    wittGhostComponentModIdealPow I hrI n
        (WittVector.teichmuller r (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ^ (n + 1)) (a ^ r ^ n) := by
  rw [← WittVector.map_teichmuller r (Ideal.Quotient.mk I) a,
    wittGhostComponentModIdealPow_map_mk, WittVector.ghostComponent_teichmuller]

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

omit [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [Fintype k] [Algebra (ZMod ℓ) k]
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [Field R']
    [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R'] in
/-- Taking an `ℓ`-th power shifts one inverse Frobenius step off the
coordinates used in the Witt Teichmüller expansion. -/
theorem frobeniusEquiv_symm_pow_succ_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (r : ℕ) (x : k) :
    (((_root_.frobeniusEquiv k ℓ).symm ^ (r + 1)) x) ^ ℓ =
      (((_root_.frobeniusEquiv k ℓ).symm ^ r) x) := by
  let φ : k ≃+* k := _root_.frobeniusEquiv k ℓ
  change ((φ.symm ^ (r + 1)) x) ^ ℓ = (φ.symm ^ r) x
  rw [pow_succ', RingAut.mul_apply]
  exact _root_.frobeniusEquiv_symm_pow_p (R := k) (p := ℓ) ((φ.symm ^ r) x)

omit [Fintype k] in
/-- Witt Frobenius sends Teichmüller representatives to Teichmüller
representatives of Frobenius powers. -/
theorem witt_frobenius_teichmuller (x : k) :
    WittVector.frobenius (WittVector.teichmuller ℓ x) =
      WittVector.teichmuller ℓ (x ^ ℓ) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller]
  rfl

omit [Fintype k] in
/-- Iterated Witt Frobenius on a Teichmüller representative. -/
theorem witt_iterate_frobenius_teichmuller (i : ℕ) (x : k) :
    (WittVector.frobenius^[i]) (WittVector.teichmuller ℓ x) =
      WittVector.teichmuller ℓ (x ^ (ℓ ^ i)) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, witt_frobenius_teichmuller]
      congr 1
      rw [← pow_mul, Nat.pow_succ]

/-- The finite Witt-Frobenius trace. -/
noncomputable def wittFrobeniusTrace (f : ℕ) (x : WittVector ℓ k) :
    WittVector ℓ k :=
  ∑ i : Fin f, (WittVector.frobenius^[i.1]) x

omit [Fintype k] in
/-- The finite Witt-Frobenius trace of a Teichmüller representative is the
sum of the Teichmüller representatives of its finite-field Frobenius powers. -/
theorem wittFrobeniusTrace_teichmuller (f : ℕ) (x : k) :
    wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x) =
      ∑ i : Fin f, WittVector.teichmuller ℓ (x ^ (ℓ ^ (i : ℕ))) := by
  classical
  simp [wittFrobeniusTrace, witt_iterate_frobenius_teichmuller]

omit [Fintype k] in
/-- The zeroth Witt coefficient of the finite Frobenius trace is the usual
finite Frobenius trace sum. -/
theorem wittFrobeniusTrace_teichmuller_coeff_zero (f : ℕ) (x : k) :
    (wittFrobeniusTrace (ℓ := ℓ) (k := k) f
        (WittVector.teichmuller ℓ x)).coeff 0 =
      ∑ i : Fin f, x ^ (ℓ ^ (i : ℕ)) := by
  classical
  rw [wittFrobeniusTrace_teichmuller]
  change WittVector.constantCoeff
      (∑ i : Fin f, WittVector.teichmuller ℓ (x ^ (ℓ ^ (i : ℕ)))) =
    ∑ i : Fin f, x ^ (ℓ ^ (i : ℕ))
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact WittVector.teichmuller_coeff_zero (p := ℓ) (x ^ (ℓ ^ (i : ℕ)))

omit [Fintype k] in
/-- Every Witt vector is congruent modulo `ℓ` to the Teichmüller lift of its
zeroth coefficient. -/
theorem wittVector_sub_teichmuller_coeff_zero_dvd_prime
    [PerfectRing k ℓ] (x : WittVector ℓ k) :
    (ℓ : WittVector ℓ k) ∣ x - WittVector.teichmuller ℓ (x.coeff 0) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  have h :=
    (WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := ℓ) x 0)
  have hsum :
      (∑ i ∈ Finset.Iic 0,
          WittVector.teichmuller ℓ (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
            (ℓ : WittVector ℓ k) ^ i) =
        WittVector.teichmuller ℓ (x.coeff 0) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hne
      exact (hne (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hi))).elim
    · intro hnot
      exact (hnot (Finset.mem_Iic.mpr le_rfl)).elim
  rw [hsum] at h
  simpa using h

omit [Fintype k] in
/-- The finite Witt-Frobenius trace differs from the Teichmüller lift of its
zeroth finite-field trace coefficient by an `ℓ`-multiple. -/
theorem wittFrobeniusTrace_teichmuller_sub_teichmuller_coeff_zero_dvd_prime
    [PerfectRing k ℓ] (f : ℕ) (x : k) :
    (ℓ : WittVector ℓ k) ∣
      wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x) -
        WittVector.teichmuller ℓ (∑ i : Fin f, x ^ (ℓ ^ (i : ℕ))) := by
  simpa [wittFrobeniusTrace_teichmuller_coeff_zero] using
    wittVector_sub_teichmuller_coeff_zero_dvd_prime
      (ℓ := ℓ)
      (x := wittFrobeniusTrace (ℓ := ℓ) (k := k) f (WittVector.teichmuller ℓ x))

omit [Fintype k] in
/-- A natural representative of an element of `ZMod ℓ`, viewed as a Witt
vector over `k`, differs from the Teichmüller lift of that residue class by
an `ℓ`-multiple. -/
theorem natCast_zmod_val_sub_teichmuller_dvd_prime
    [PerfectRing k ℓ] (a : ZMod ℓ) :
    (ℓ : WittVector ℓ k) ∣
      ((a.val : ℕ) : WittVector ℓ k) -
        WittVector.teichmuller ℓ (algebraMap (ZMod ℓ) k a) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  have hcoeff :
      (((a.val : ℕ) : WittVector ℓ k).coeff 0) =
        algebraMap (ZMod ℓ) k a := by
    change WittVector.constantCoeff (((a.val : ℕ) : WittVector ℓ k)) =
      algebraMap (ZMod ℓ) k a
    rw [map_natCast]
    have h := congrArg (algebraMap (ZMod ℓ) k) (ZMod.natCast_zmod_val a)
    rw [map_natCast] at h
    exact h
  have h :=
    wittVector_sub_teichmuller_coeff_zero_dvd_prime
      (ℓ := ℓ) (k := k) (x := ((a.val : ℕ) : WittVector ℓ k))
  rw [hcoeff] at h
  exact h

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Fontaine-style `Q`-adic ghost map from Witt vectors over the concrete
residue-field model to the quotient `𝓞 R' / Q^(N+1)`.

The inverse Frobenius twist is the standard one: on Teichmüller inputs it
lets the `N`-th ghost component recover the selected Teichmüller lift at
precision `N`. -/
noncomputable def wittThetaModQPow (N : ℕ) :
    WittVector ℓ k →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  exact
    (wittGhostComponentModIdealPow S.Q S.hQ N).comp
      ((WittVector.map S.residueQuotientEquiv.symm.toRingHom).comp
        (WittVector.map ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom)))

/-- Witt-vector uniqueness in the `Q^(N+1)` quotient.

This is the entry point for the all-order Dwork splitting proof: once two
ring maps out of `WittVector ℓ k` agree on Teichmüller representatives,
nilpotence of `ℓ` in the target quotient forces them to agree everywhere. -/
theorem wittVector_eq_of_apply_teichmuller_eq_quotient
    (N : ℕ)
    (φ ψ : WittVector ℓ k →+* (𝓞 R' ⧸ S.Q ^ (N + 1)))
    (h : ∀ x : k, φ (WittVector.teichmuller ℓ x) =
        ψ (WittVector.teichmuller ℓ x)) :
    φ = ψ := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  have hnil : IsNilpotent (ℓ : 𝓞 R' ⧸ S.Q ^ (N + 1)) := by
    change IsNilpotent (Ideal.Quotient.mk (S.Q ^ (N + 1)) (ℓ : 𝓞 R'))
    exact S.quotient_natCast_ell_isNilpotent N
  exact WittVector.eq_of_apply_teichmuller_eq φ ψ hnil h

/-- The concrete quotient Witt map is computed by the finite Teichmüller
series through precision `N`: the omitted tail is divisible by `ℓ^(N+1)`,
which maps to zero modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_eq_sum_teichmuller_series
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (x : WittVector ℓ k) :
    let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A := S.wittThetaModQPow N
    θ x =
      ∑ i ∈ Finset.Iic N,
        (ℓ : A) ^ i *
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i))) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ S.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A := S.wittThetaModQPow N
  let approx : WittVector ℓ k :=
    ∑ i ∈ Finset.Iic N,
      WittVector.teichmuller ℓ
        (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
        (ℓ : WittVector ℓ k) ^ i
  obtain ⟨c, hc⟩ :=
    WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff
      (p := ℓ) x N
  have htail :
      θ (x - approx) = 0 := by
    calc
      θ (x - approx)
          = θ ((ℓ : WittVector ℓ k) ^ (N + 1) * c) := by
              rw [show x - approx =
                x - ∑ i ∈ Finset.Iic N,
                  WittVector.teichmuller ℓ
                    (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
                    (ℓ : WittVector ℓ k) ^ i by
                  rfl, hc]
      _ = 0 := by
              rw [map_mul, map_pow, map_natCast,
                show ((ℓ : A) ^ (N + 1)) = 0 from
                  S.quotient_natCast_ell_pow_succ_eq_zero N, zero_mul]
  have hxapprox : θ x = θ approx := by
    have hsub : θ x - θ approx = 0 := by
      simpa [θ, approx, map_sub] using htail
    exact sub_eq_zero.mp hsub
  calc
    θ x = θ approx := hxapprox
    _ =
        θ (∑ i ∈ Finset.Iic N,
          WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
            (ℓ : WittVector ℓ k) ^ i) := by
          rfl
    _ =
        ∑ i ∈ Finset.Iic N,
          θ (WittVector.teichmuller ℓ
            (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i)) *
            (ℓ : WittVector ℓ k) ^ i) := by
          rw [map_sum]
    _ =
        ∑ i ∈ Finset.Iic N,
          (ℓ : A) ^ i *
            θ (WittVector.teichmuller ℓ
              (((_root_.frobeniusEquiv k ℓ).symm ^ i) (x.coeff i))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [map_mul, map_pow, map_natCast]
          ring

end ConcreteStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- On a Teichmüller unit, the concrete Fontaine-style Witt map recovers the
chosen integral Teichmüller lift modulo `Q^(N+1)`, provided `xN` is the
inverse-Frobenius preimage used by the map. -/
theorem wittThetaModQPow_teichmuller_unit_of_pow
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (x xN : kˣ)
    (hxN :
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k)) = (xN : k))
    (hxNpow : xN ^ (ℓ ^ N) = x) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  have hquot :
      F.toConcreteStickelbergerSetup.residueQuotientEquiv.symm (xN : k) =
        Ideal.Quotient.mk F.Q (F.teichUnitFullVal xN) := by
    apply F.toConcreteStickelbergerSetup.residueQuotientEquiv.injective
    simp [F.residueMap_teichUnitFullVal xN]
  have hquot' :
      F.toConcreteStickelbergerSetup.residueQuotientEquiv.symm.toRingHom (xN : k) =
        Ideal.Quotient.mk F.Q (F.teichUnitFullVal xN) := hquot
  have hxN' :
      (_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom (x : k) = (xN : k) := hxN
  rw [ConcreteStickelbergerSetup.wittThetaModQPow]
  simp only [RingHom.comp_apply]
  rw [WittVector.map_teichmuller, hxN', WittVector.map_teichmuller, hquot',
    wittGhostComponentModIdealPow_teichmuller_mk, ← F.teichUnitFullVal_pow, hxNpow]

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
/-- The inverse iterated Frobenius preimage of a residue-field unit. -/
noncomputable def frobeniusUnitPreimage
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) : kˣ :=
  Units.mapEquiv ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toMulEquiv) x

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
@[simp]
theorem frobeniusUnitPreimage_val
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    (frobeniusUnitPreimage (ℓ := ℓ) N x : k) =
      (_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k) := by
  rfl

omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
theorem frobeniusUnitPreimage_pow
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    frobeniusUnitPreimage (ℓ := ℓ) N x ^ (ℓ ^ N) = x := by
  ext
  rw [Units.val_pow_eq_pow_val, frobeniusUnitPreimage_val]
  change ((_root_.iterateFrobeniusEquiv k ℓ N)
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k))) = (x : k)
  rw [RingEquiv.apply_symm_apply]

/-- The concrete Teichmüller lift extended from units to all residue-field
elements by sending `0` to `0`. -/
noncomputable def teichFullVal
    (F : FullTeichStickelbergerSetup ℓ p k K R') (x : k) : 𝓞 R' := by
  classical
  exact if hx : x = 0 then 0 else F.teichUnitFullVal (Units.mk0 x hx)

@[simp]
theorem teichFullVal_zero :
    F.teichFullVal (0 : k) = 0 := by
  classical
  simp [teichFullVal]

theorem teichFullVal_of_ne {x : k} (hx : x ≠ 0) :
    F.teichFullVal x = F.teichUnitFullVal (Units.mk0 x hx) := by
  classical
  simp [teichFullVal, hx]

theorem residueMap_teichFullVal (x : k) :
    F.residueMap (F.teichFullVal x) = x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  · simpa [F.teichFullVal_of_ne hx] using
      F.residueMap_teichUnitFullVal (Units.mk0 x hx)

/-- The extended Teichmüller lift is compatible with powers. -/
@[simp]
theorem teichFullVal_pow (x : k) (n : ℕ) :
    F.teichFullVal (x ^ n) = F.teichFullVal x ^ n := by
  classical
  by_cases hx : x = 0
  · subst x
    cases n with
    | zero =>
        rw [pow_zero, pow_zero, F.teichFullVal_of_ne one_ne_zero]
        simp
    | succ n => simp
  · have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
    let xu : kˣ := Units.mk0 x hx
    have hxunit : Units.mk0 (x ^ n) hxn = xu ^ n := by
      ext
      simp [xu, Units.val_pow_eq_pow_val]
    calc
      F.teichFullVal (x ^ n)
          = F.teichUnitFullVal (Units.mk0 (x ^ n) hxn) := by
            rw [F.teichFullVal_of_ne hxn]
      _ = F.teichUnitFullVal (xu ^ n) := by
            rw [hxunit]
      _ = F.teichUnitFullVal xu ^ n := by
            rw [F.teichUnitFullVal_pow]
      _ = F.teichFullVal x ^ n := by
            rw [F.teichFullVal_of_ne hx]

/-- On a Teichmüller unit, the concrete Fontaine-style Witt map recovers the
chosen integral Teichmüller lift modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  refine F.wittThetaModQPow_teichmuller_unit_of_pow
    N x (frobeniusUnitPreimage (ℓ := ℓ) N x) ?_ ?_
  · exact (frobeniusUnitPreimage_val (ℓ := ℓ) N x).symm
  · exact frobeniusUnitPreimage_pow (ℓ := ℓ) N x

/-- On any residue-field element, the concrete Fontaine-style Witt map
recovers the extended Teichmüller lift modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_teichmuller
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : k) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ x) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal x) := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [WittVector.teichmuller_zero]
  · let xu : kˣ := Units.mk0 x hx
    have hunit := F.wittThetaModQPow_teichmuller_unit N xu
    simpa [teichFullVal, hx, xu] using hunit

/-- The concrete quotient Witt map on a Teichmüller representative is
compatible with the `ℓ`-power Frobenius in the quotient. -/
theorem wittThetaModQPow_teichmuller_pow_prime
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : k) :
    (F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ x)) ^ ℓ =
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x ^ ℓ)) := by
  calc
    (F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ x)) ^ ℓ
        = (Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal x)) ^ ℓ := by
          rw [F.wittThetaModQPow_teichmuller N x]
    _ = Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal (x ^ ℓ)) := by
          rw [← map_pow, F.teichFullVal_pow]
    _ =
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x ^ ℓ)) := by
          rw [F.wittThetaModQPow_teichmuller N (x ^ ℓ)]

/-- The concrete quotient Witt map sends the Witt-Frobenius trace of a
Teichmüller unit to the corresponding concrete Teichmüller Frobenius sum. -/
theorem wittThetaModQPow_wittFrobeniusTrace_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ] (N f : ℕ) (x : kˣ) :
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k) f
          (WittVector.teichmuller ℓ (x : k))) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        (∑ i : Fin f, (F.teichUnitFullVal x) ^ (ℓ ^ (i : ℕ))) := by
  classical
  calc
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k) f
          (WittVector.teichmuller ℓ (x : k)))
        = ∑ i : Fin f,
            F.toConcreteStickelbergerSetup.wittThetaModQPow N
              (WittVector.teichmuller ℓ ((x : k) ^ (ℓ ^ (i : ℕ)))) := by
            rw [ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller]
            simp
    _ = ∑ i : Fin f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            (F.teichUnitFullVal (x ^ (ℓ ^ (i : ℕ)))) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Units.val_pow_eq_pow_val] using
              F.wittThetaModQPow_teichmuller_unit N (x ^ (ℓ ^ (i : ℕ)))
    _ = Ideal.Quotient.mk (F.Q ^ (N + 1))
          (∑ i : Fin f, (F.teichUnitFullVal x) ^ (ℓ ^ (i : ℕ))) := by
            simp [map_sum]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
