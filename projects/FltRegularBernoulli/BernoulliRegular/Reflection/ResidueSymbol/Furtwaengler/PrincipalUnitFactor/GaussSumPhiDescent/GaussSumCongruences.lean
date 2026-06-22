module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Principal divisibility descent from an integral cyclotomic extension -/

/-- Principal divisibility by a square descends from `𝓞 R'` to `𝓞 K`.

This is the contraction step needed for U4 in the special principal situation
at `(ζ_p - 1)^2`.  If the image of `x` is divisible by the image of
`ε^2`, then `x / ε^2` is integral because its image in `R'` is an algebraic
integer; hence `x` was already divisible by `ε^2` in `𝓞 K`. -/
theorem mem_span_singleton_pow_two_of_algebraMap_mem_span_singleton_pow_two
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {ε x : 𝓞 K} (hε : ε ≠ 0)
    (hx :
      algebraMap (𝓞 K) (𝓞 R') x ∈
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') (ε ^ 2)} : Set (𝓞 R'))) :
    x ∈ Ideal.span ({ε ^ 2} : Set (𝓞 K)) := by
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨w, hw⟩ := hx
  let y : K := (x : K) / ((ε : K) ^ 2)
  have hεK : (ε : K) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr hε
  have hεKR' : algebraMap K R' ((ε : K) ^ 2) ≠ 0 :=
    (map_ne_zero (algebraMap K R')).mpr (pow_ne_zero 2 hεK)
  have hwR' :
      algebraMap K R' (x : K) =
        algebraMap K R' ((ε : K) ^ 2) * algebraMap (𝓞 R') R' w := by
    have hw' := congrArg (algebraMap (𝓞 R') R') hw
    simpa [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 R') R',
      ← IsScalarTower.algebraMap_apply (𝓞 K) K R', map_pow] using hw'
  have hy_alg : algebraMap K R' y = algebraMap (𝓞 R') R' w := by
    calc
      algebraMap K R' y =
          algebraMap K R' (x : K) / algebraMap K R' ((ε : K) ^ 2) := by
            simp [y]
      _ = (algebraMap K R' ((ε : K) ^ 2) * algebraMap (𝓞 R') R' w) /
            algebraMap K R' ((ε : K) ^ 2) := by
            rw [hwR']
      _ = algebraMap (𝓞 R') R' w := by
            field_simp [hεKR']
  have hy_int_R' : IsIntegral ℤ (algebraMap K R' y) := by
    rw [hy_alg]
    exact NumberField.RingOfIntegers.isIntegral_coe w
  have hy_int : IsIntegral ℤ y :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K R')).mp hy_int_R'
  refine ⟨⟨y, hy_int⟩, ?_⟩
  apply RingOfIntegers.ext
  change (x : K) = ((ε : K) ^ 2) * y
  rw [show y = (x : K) / ((ε : K) ^ 2) from rfl]
  field_simp [pow_ne_zero 2 hεK]

/-! ### First-order Gauss-sum congruence at the `p`-cyclotomic prime -/

/-- Over a finite field, the Gauss sum of the trivial multiplicative
character against a non-trivial additive character is `-1`.  This is the
normalization behind the classical congruence `g(χ) ≡ -1 (mod ζ_p - 1)`
when the values of `χ` are reduced modulo the `p`-cyclotomic augmentation
prime. -/
theorem gaussSum_one_eq_neg_one_of_addChar_ne_one
    {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]
    (ψ : AddChar F R) (hψ : ψ ≠ 1) :
    _root_.gaussSum (1 : MulChar F R) ψ = -1 := by
  classical
  have hsum : ∑ x : F, ψ x = 0 :=
    AddChar.sum_eq_zero_of_ne_one hψ
  have hsum_erase :
      (Finset.univ.erase (0 : F)).sum (fun x => ψ x) = -1 := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset F) ψ
        (Finset.mem_univ (0 : F))] at hsum
    simpa [add_eq_zero_iff_eq_neg] using hsum
  calc
    _root_.gaussSum (1 : MulChar F R) ψ =
        (Finset.univ.erase (0 : F)).sum (fun x => ψ x) := by
      unfold _root_.gaussSum
      rw [← Finset.sum_erase_add (Finset.univ : Finset F)
        (fun x => (1 : MulChar F R) x * ψ x) (Finset.mem_univ (0 : F))]
      simp only [MulChar.map_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx_ne
      rw [show (1 : MulChar F R) x = 1 by
        simpa using (MulChar.one_apply_coe (R := F) (R' := R) hx_unit.unit)]
      simp
    _ = -1 := hsum_erase

/-- If a multiplicative character is congruent to `1` on all units modulo an
ideal and the additive character is non-trivial, then its Gauss sum is
congruent to `-1` modulo that ideal.  This is the abstract λ-linear part of
the U4 Gauss-sum argument. -/
theorem gaussSum_add_one_mem_ideal_of_mulChar_sub_one_mem
    {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]
    (χ : MulChar F R) (ψ : AddChar F R) (hψ : ψ ≠ 1)
    {I : Ideal R} (hχ : ∀ x : F, x ≠ 0 → χ x - 1 ∈ I) :
    _root_.gaussSum χ ψ + 1 ∈ I := by
  classical
  have hdiff :
      _root_.gaussSum χ ψ - _root_.gaussSum (1 : MulChar F R) ψ ∈ I := by
    unfold _root_.gaussSum
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun x _ => ?_
    by_cases hx : x = 0
    · subst x
      rw [MulChar.map_zero, MulChar.map_zero]
      simp
    · rw [show χ x * ψ x - (1 : MulChar F R) x * ψ x =
          (χ x - (1 : MulChar F R) x) * ψ x by ring]
      have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx
      rw [show (1 : MulChar F R) x = 1 by
        simpa using (MulChar.one_apply_coe (R := F) (R' := R) hx_unit.unit)]
      exact Ideal.mul_mem_right _ _ (hχ x hx)
  have h_one :
      _root_.gaussSum (1 : MulChar F R) ψ = -1 :=
    gaussSum_one_eq_neg_one_of_addChar_ne_one ψ hψ
  convert hdiff using 1
  rw [h_one]
  ring

/-- If a ring endomorphism sends the multiplicative character to its inverse
and the additive character to its inverse, then it sends the Gauss sum to the
inverse-character/inverse-additive Gauss sum.

This is the precise abstract conjugation calculation needed for the remaining
U4 Gauss-sum norm identity. -/
theorem gaussSum_map_eq_inv_inv_of_ringHomComp
    {F R : Type*} [Field F] [Fintype F] [CommRing R]
    (χ : MulChar F R) (ψ : AddChar F R) (σ : R →+* R)
    (hχ : χ.ringHomComp σ = χ⁻¹)
    (hψ : σ.toMonoidHom.compAddChar ψ = ψ⁻¹) :
    σ (_root_.gaussSum χ ψ) = _root_.gaussSum χ⁻¹ ψ⁻¹ := by
  rw [gaussSum_ringHomComp, hχ, hψ]

/-- If `x ≡ -1 (mod I)` and `p ∈ I²`, then `x^p ≡ -1 (mod I²)` for odd
`p`. This is the algebraic square-lift used after the first-order Gauss-sum
congruence `g ≡ -1 (mod ζ_p - 1)`. -/
theorem pow_add_one_mem_ideal_sq_of_add_one_mem_of_natCast_mem_sq
    {R : Type*} [CommRing R] {I : Ideal R} {x : R} {p : ℕ}
    (hp_odd : Odd p) (hx : x + 1 ∈ I) (hp_mem : (p : R) ∈ I ^ 2) :
    x ^ p + 1 ∈ I ^ 2 := by
  have hpI : (p : R) ∈ I :=
    (I.pow_le_self (by norm_num : 2 ≠ 0)) hp_mem
  have hnegx_smod : -x ≡ 1 [SMOD I] := by
    rw [SModEq.sub_mem]
    have hxneg : -(x + 1) ∈ I := I.neg_mem hx
    convert hxneg using 1
    ring
  have hnegx_smod_one : -x ≡ 1 [SMOD I ^ 1] := by
    simpa using hnegx_smod
  have hpow :
      (-x) ^ p ≡ (1 : R) ^ p [SMOD I ^ (1 + 1)] :=
    SModEq.pow_add_one (I := I) (p := p) hpI (m := 1) (by norm_num)
      hnegx_smod_one
  rw [SModEq.sub_mem] at hpow
  have hpow_mem : (-x) ^ p - (1 : R) ^ p ∈ I ^ 2 := by
    simpa using hpow
  have hneg_mem : -(x ^ p + 1) ∈ I ^ 2 := by
    convert hpow_mem using 1
    rw [hp_odd.neg_pow, one_pow]
    ring
  simpa using (I ^ 2).neg_mem hneg_mem

namespace ConcreteStickelbergerSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The integral additive character attached to a concrete setup is
non-trivial. -/
theorem psiInt_ne_one
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    S.psiInt ≠ 1 := by
  intro h_eq
  have h_psi_eq : S.psi = 1 := by
    ext x
    rw [AddChar.one_apply]
    have h_alg := S.algebraMap_psiInt x
    have h_one : S.psiInt x = (1 : 𝓞 R') := by
      have := DFunLike.congr_fun h_eq x
      simpa [AddChar.one_apply] using this
    rw [h_one, map_one] at h_alg
    exact h_alg.symm
  have h_shift := S.hpsi (show (1 : k) ≠ 0 from one_ne_zero)
  apply h_shift
  ext y
  simp [h_psi_eq, AddChar.one_apply]

/-- The integral residue character takes values congruent to `1` modulo
`ζ_p - 1` on finite-field units. -/
theorem residueCharInt_pow_apply_sub_one_mem_zeta_p_sub_one
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    {x : k} (hx : x ≠ 0) :
    (S.residueCharInt ^ a) x - 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let u : kˣ := Units.mk0 x hx
  change (S.residueCharInt ^ a) (u : k) - 1 ∈
    Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))
  rw [MulChar.pow_apply_coe]
  rw [ConcreteStickelbergerSetup.residueCharInt, residueMulChar_apply_unit]
  rw [← pow_mul]
  exact Ideal.mem_span_singleton.mpr <| by
    simpa [ConcreteStickelbergerSetup.zeta_p_int_unit_coe] using
      sub_one_dvd_pow_sub_one S.zeta_p_int
        ((Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
          S.zeta_k S.hzeta_k S.hdiv u).val * a)

/-- The actual integral Gauss sum is `-1` modulo the `p`-cyclotomic
augmentation prime in the target ring. This is the concrete first-order
Gauss-sum congruence used by U4 before the descent/contraction step. -/
theorem gaussSumInt_add_one_mem_zeta_p_sub_one
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hψ : S.psiInt ≠ 1) :
    S.gaussSumInt a + 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) := by
  unfold ConcreteStickelbergerSetup.gaussSumInt
  exact gaussSum_add_one_mem_ideal_of_mulChar_sub_one_mem
    (S.residueCharInt ^ a) S.psiInt hψ
    (fun x hx => S.residueCharInt_pow_apply_sub_one_mem_zeta_p_sub_one a hx)

/-- The actual integral Gauss sum is `-1` modulo `ζ_p - 1`; version using
the setup's primitive additive character, with no extra non-triviality
hypothesis. -/
theorem gaussSumInt_add_one_mem_zeta_p_sub_one'
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ) :
    S.gaussSumInt a + 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) :=
  S.gaussSumInt_add_one_mem_zeta_p_sub_one a S.psiInt_ne_one

/-- The standard cyclotomic ramification input for the setup's chosen
primitive `p`-th root: for `p ≥ 3`, the rational prime `p` lies in
`(ζ_p - 1)^2`. -/
theorem natCast_p_mem_zeta_p_sub_one_sq
    (S : ConcreteStickelbergerSetup ℓ p k K R') (hp_three : 3 ≤ p) :
    (p : 𝓞 R') ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 := by
  let I : Ideal (𝓞 R') :=
    Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))
  have hassoc :
      Associated (p : 𝓞 R') ((S.zeta_p_int - 1) ^ (p - 1)) := by
    simpa using
      (associated_ell_zeta_sub_one_pow
        (ℓ := p) (R := 𝓞 R') S.zeta_p_int_isPrimitiveRoot)
  have hbase : S.zeta_p_int - 1 ∈ I :=
    Ideal.mem_span_singleton.mpr dvd_rfl
  have hpow : (S.zeta_p_int - 1) ^ (p - 1) ∈ I ^ (p - 1) :=
    Ideal.pow_mem_pow hbase (p - 1)
  have hle : I ^ (p - 1) ≤ I ^ 2 :=
    Ideal.pow_le_pow_right (by omega)
  exact (associated_mem_ideal_iff (I := I ^ 2) hassoc).2 (hle hpow)

/-- The concrete square congruence `g(χ)^p ≡ -1 (mod (ζ_p - 1)^2)`, assuming
the standard cyclotomic ramification input `p ∈ (ζ_p - 1)^2` for the setup's
chosen primitive `p`-th root. This is the ambient-ring form of the
semi-primary Φ-prime fact before descent back to `𝓞 K`. -/
theorem gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hp_odd : Odd p) (hψ : S.psiInt ≠ 1)
    (hp_mem : (p : 𝓞 R') ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2) :
    S.gaussSumInt a ^ p + 1 ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 :=
  pow_add_one_mem_ideal_sq_of_add_one_mem_of_natCast_mem_sq hp_odd
    (S.gaussSumInt_add_one_mem_zeta_p_sub_one a hψ) hp_mem

/-- The concrete square congruence `g(χ)^p ≡ -1 (mod (ζ_p - 1)^2)` for the
actual integral setup. This is the ambient-ring Gauss-sum congruence needed
to prove that descended prime Φ-elements are semi-primary. -/
theorem gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq'
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hp_three : 3 ≤ p) :
    S.gaussSumInt a ^ p + 1 ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 := by
  have hp_odd : Odd p :=
    (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  exact S.gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq
    a hp_odd S.psiInt_ne_one (S.natCast_p_mem_zeta_p_sub_one_sq hp_three)

/-- If an upstairs endomorphism sends the chosen integral `p`-th root to
the inverse power `ζ_p^(p-1)`, then it sends the integral residue character
to its inverse. -/
theorem residueCharInt_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
    (S : ConcreteStickelbergerSetup ℓ p k K R') (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_p_int = S.zeta_p_int ^ (p - 1)) :
    S.residueCharInt.ringHomComp σ = S.residueCharInt⁻¹ := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hσ_unit :
      σ ((S.zeta_p_int_unit : (𝓞 R')ˣ) : 𝓞 R') =
        ((S.zeta_p_int_unit : (𝓞 R')ˣ) : 𝓞 R') ^ (p - 1) := by
    simpa [ConcreteStickelbergerSetup.zeta_p_int_unit_coe] using hσζ
  have hcomp :
      S.residueCharInt.ringHomComp σ = S.residueCharInt ^ (p - 1) := by
    simpa [ConcreteStickelbergerSetup.residueCharInt] using
      (residueMulChar_ringHomComp_pow_eq
        S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
        S.zeta_p_int_unit_isPrimitiveRoot σ (p - 1) hσ_unit)
  have hχp : S.residueCharInt ^ p = 1 :=
    S.residueCharInt_pow_eq_one
  have hmul : S.residueCharInt ^ (p - 1) * S.residueCharInt = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le, hχp]
  exact hcomp.trans (eq_inv_of_mul_eq_one_left hmul)

/-- Power version of
`residueCharInt_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one`. -/
theorem residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
    (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_p_int = S.zeta_p_int ^ (p - 1)) :
    (S.residueCharInt ^ a).ringHomComp σ = (S.residueCharInt ^ a)⁻¹ := by
  rw [← MulChar.ringHomComp_pow,
    S.residueCharInt_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one σ hσζ]
  simp

/-- In an upstairs CM field, complex conjugation sends the chosen integral
`ℓ`-root to the inverse power `ζ_ℓ^(ℓ-1)`. -/
theorem zeta_ell_int_complexConj_eq_pow_sub_one
    [IsCMField R']
    (S : ConcreteStickelbergerSetup ℓ p k K R') :
    ringOfIntegersComplexConj R' S.zeta_ell_int =
      S.zeta_ell_int ^ (ℓ - 1) := by
  letI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  let u : (𝓞 R')ˣ :=
    (S.zeta_ell_int_isPrimitiveRoot.isUnit
      (Fact.out : Nat.Prime ℓ).ne_zero).unit
  have hu : (u : 𝓞 R') = S.zeta_ell_int := by
    simp [u]
  have hu_pow : u ^ ℓ = 1 := by
    apply Units.ext
    simpa [hu] using S.zeta_ell_int_isPrimitiveRoot.pow_eq_one
  have hu_torsion : u ∈ NumberField.Units.torsion R' :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2
        ⟨ℓ, (Fact.out : Nat.Prime ℓ).pos, by
          exact hu_pow⟩)
  have hconj_units :
      unitsComplexConj R' u = (u⁻¹ : (𝓞 R')ˣ) := by
    simpa using
      (unitsComplexConj_torsion (K := R') ⟨u, hu_torsion⟩)
  have h_inv_pow : (u⁻¹ : (𝓞 R')ˣ) = u ^ (ℓ - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one (Fact.out : Nat.Prime ℓ).ne_zero, hu_pow]
  calc
    ringOfIntegersComplexConj R' S.zeta_ell_int
        = ringOfIntegersComplexConj R' (u : 𝓞 R') := by rw [hu]
    _ = ((unitsComplexConj R' u : (𝓞 R')ˣ) : 𝓞 R') := rfl
    _ = ((u⁻¹ : (𝓞 R')ˣ) : 𝓞 R') := by rw [hconj_units]
    _ = ((u ^ (ℓ - 1) : (𝓞 R')ˣ) : 𝓞 R') := by rw [h_inv_pow]
    _ = S.zeta_ell_int ^ (ℓ - 1) := by
          rw [Units.val_pow_eq_pow_val, hu]

end ConcreteStickelbergerSetup

namespace TraceFormStickelbergerSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- Trace-form exponent compatibility with negation: multiplying the
trace exponent by `ℓ - 1` gives the exponent of the inverse additive
character. -/
theorem zeta_ell_int_pow_sub_one_mul_psiExponent_eq_neg
    (S : TraceFormStickelbergerSetup ℓ p k K R') (x : k) :
    S.zeta_ell_int ^ ((ℓ - 1) * S.psiExponent x) =
      S.zeta_ell_int ^ S.psiExponent (-x) := by
  let t : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)
  have ht_neg :
      Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * (-x)) = -t := by
    simp [t, mul_neg]
  rw [S.psiExponent_trace x, S.psiExponent_trace (-x), ht_neg]
  have hcast :
      (((ℓ - 1) * t.val : ℕ) : ZMod ℓ) = (((-t).val : ℕ) : ZMod ℓ) := by
    calc
      (((ℓ - 1) * t.val : ℕ) : ZMod ℓ)
          = ((ℓ - 1 : ℕ) : ZMod ℓ) * (t.val : ZMod ℓ) := by
              rw [Nat.cast_mul]
      _ = (-1 : ZMod ℓ) * t := by
              rw [Nat.cast_sub (Fact.out : Nat.Prime ℓ).one_le,
                ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]
              norm_num
      _ = -t := by simp
      _ = (((-t).val : ℕ) : ZMod ℓ) := by
              rw [ZMod.natCast_zmod_val]
  exact pow_eq_pow_of_modEq
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast)
    S.zeta_ell_int_isPrimitiveRoot.pow_eq_one

/-- If an upstairs endomorphism sends the chosen integral `ℓ`-th root to
the inverse power `ζ_ℓ^(ℓ-1)`, then it sends the trace-form integral
additive character to its inverse. -/
theorem psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
    (S : TraceFormStickelbergerSetup ℓ p k K R') (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_ell_int = S.zeta_ell_int ^ (ℓ - 1)) :
    σ.toMonoidHom.compAddChar S.psiInt = S.psiInt⁻¹ := by
  apply DFunLike.ext
  intro x
  change σ (S.zeta_ell_int ^ S.psiExponent x) =
    S.zeta_ell_int ^ S.psiExponent (-x)
  rw [map_pow, hσζ, ← pow_mul]
  exact S.zeta_ell_int_pow_sub_one_mul_psiExponent_eq_neg x

end TraceFormStickelbergerSetup

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

/-- The conductor-flexible integral additive character is non-trivial. -/
theorem psiInt_ne_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') :
    S.psiInt ≠ 1 := by
  intro h_eq
  have h_psi_eq : S.psi = 1 := by
    ext x
    rw [AddChar.one_apply]
    have h_alg := S.algebraMap_psiInt x
    have h_one : S.psiInt x = (1 : 𝓞 R') := by
      have := DFunLike.congr_fun h_eq x
      simpa [AddChar.one_apply] using this
    rw [h_one, map_one] at h_alg
    exact h_alg.symm
  have h_shift := S.hpsi (show (1 : k) ≠ 0 from one_ne_zero)
  apply h_shift
  ext y
  simp [h_psi_eq, AddChar.one_apply]

/-- The conductor-flexible integral residue character has order dividing
`p`. -/
theorem residueCharInt_pow_eq_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') :
    S.residueCharInt ^ p = 1 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  unfold ConductorFlexibleConcreteStickelbergerSetup.residueCharInt
  exact residueMulChar_pow_eq_one_mulChar
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- The conductor-flexible integral residue character takes values congruent
to `1` modulo `ζ_p - 1` on finite-field units. -/
theorem residueCharInt_pow_apply_sub_one_mem_zeta_p_sub_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    {x : k} (hx : x ≠ 0) :
    (S.residueCharInt ^ a) x - 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) := by
  classical
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let u : kˣ := Units.mk0 x hx
  change (S.residueCharInt ^ a) (u : k) - 1 ∈
    Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))
  rw [MulChar.pow_apply_coe]
  rw [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt,
    residueMulChar_apply_unit]
  rw [← pow_mul]
  exact Ideal.mem_span_singleton.mpr <| by
    simpa [ConductorFlexibleConcreteStickelbergerSetup.zeta_p_int_unit_coe] using
      sub_one_dvd_pow_sub_one S.zeta_p_int
        ((Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
          S.zeta_k S.hzeta_k S.hdiv u).val * a)

/-- The conductor-flexible integral Gauss sum is `-1` modulo the
`p`-cyclotomic augmentation prime in the target ring. -/
theorem gaussSumInt_add_one_mem_zeta_p_sub_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hψ : S.psiInt ≠ 1) :
    S.gaussSumInt a + 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) := by
  unfold ConductorFlexibleConcreteStickelbergerSetup.gaussSumInt
  exact gaussSum_add_one_mem_ideal_of_mulChar_sub_one_mem
    (S.residueCharInt ^ a) S.psiInt hψ
    (fun x hx => S.residueCharInt_pow_apply_sub_one_mem_zeta_p_sub_one a hx)

/-- The conductor-flexible integral Gauss sum is `-1` modulo `ζ_p - 1`;
version using the setup's primitive additive character. -/
theorem gaussSumInt_add_one_mem_zeta_p_sub_one'
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ) :
    S.gaussSumInt a + 1 ∈
      Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R')) :=
  S.gaussSumInt_add_one_mem_zeta_p_sub_one a S.psiInt_ne_one

/-- For `p ≥ 3`, the rational prime `p` lies in `(ζ_p - 1)^2` for the
conductor-flexible chosen primitive `p`-th root. -/
theorem natCast_p_mem_zeta_p_sub_one_sq
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (hp_three : 3 ≤ p) :
    (p : 𝓞 R') ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 := by
  let I : Ideal (𝓞 R') :=
    Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))
  have hassoc :
      Associated (p : 𝓞 R') ((S.zeta_p_int - 1) ^ (p - 1)) := by
    simpa using
      (associated_ell_zeta_sub_one_pow
        (ℓ := p) (R := 𝓞 R') S.zeta_p_int_isPrimitiveRoot)
  have hbase : S.zeta_p_int - 1 ∈ I :=
    Ideal.mem_span_singleton.mpr dvd_rfl
  have hpow : (S.zeta_p_int - 1) ^ (p - 1) ∈ I ^ (p - 1) :=
    Ideal.pow_mem_pow hbase (p - 1)
  have hle : I ^ (p - 1) ≤ I ^ 2 :=
    Ideal.pow_le_pow_right (by omega)
  exact (associated_mem_ideal_iff (I := I ^ 2) hassoc).2 (hle hpow)

/-- The conductor-flexible square congruence
`g(χ)^p ≡ -1 (mod (ζ_p - 1)^2)`. -/
theorem gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hp_odd : Odd p) (hψ : S.psiInt ≠ 1)
    (hp_mem : (p : 𝓞 R') ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2) :
    S.gaussSumInt a ^ p + 1 ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 :=
  pow_add_one_mem_ideal_sq_of_add_one_mem_of_natCast_mem_sq hp_odd
    (S.gaussSumInt_add_one_mem_zeta_p_sub_one a hψ) hp_mem

/-- The conductor-flexible ambient square congruence needed for
semi-primarity of descended Φ-prime elements. -/
theorem gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq'
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (hp_three : 3 ≤ p) :
    S.gaussSumInt a ^ p + 1 ∈
      (Ideal.span ({S.zeta_p_int - 1} : Set (𝓞 R'))) ^ 2 := by
  have hp_odd : Odd p :=
    (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  exact S.gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq
    a hp_odd S.psiInt_ne_one (S.natCast_p_mem_zeta_p_sub_one_sq hp_three)

/-- If an upstairs endomorphism sends the conductor-flexible chosen integral
`p`-th root to `ζ_p^(p-1)`, it sends the integral residue character to its
inverse. -/
theorem residueCharInt_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_p_int = S.zeta_p_int ^ (p - 1)) :
    S.residueCharInt.ringHomComp σ = S.residueCharInt⁻¹ := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hσ_unit :
      σ ((S.zeta_p_int_unit : (𝓞 R')ˣ) : 𝓞 R') =
        ((S.zeta_p_int_unit : (𝓞 R')ˣ) : 𝓞 R') ^ (p - 1) := by
    simpa [ConductorFlexibleConcreteStickelbergerSetup.zeta_p_int_unit_coe] using hσζ
  have hcomp :
      S.residueCharInt.ringHomComp σ = S.residueCharInt ^ (p - 1) := by
    simpa [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt] using
      (residueMulChar_ringHomComp_pow_eq
        S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
        S.zeta_p_int_unit_isPrimitiveRoot σ (p - 1) hσ_unit)
  have hχp : S.residueCharInt ^ p = 1 :=
    S.residueCharInt_pow_eq_one
  have hmul : S.residueCharInt ^ (p - 1) * S.residueCharInt = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le, hχp]
  exact hcomp.trans (eq_inv_of_mul_eq_one_left hmul)

/-- Power version of the conductor-flexible residue-character inverse
compatibility. -/
theorem residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (a : ℕ)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_p_int = S.zeta_p_int ^ (p - 1)) :
    (S.residueCharInt ^ a).ringHomComp σ = (S.residueCharInt ^ a)⁻¹ := by
  rw [← MulChar.ringHomComp_pow,
    S.residueCharInt_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one σ hσζ]
  simp

/-- In an upstairs CM field, complex conjugation sends the conductor-flexible
chosen integral `ℓ`-root to its inverse power. -/
theorem zeta_ell_int_complexConj_eq_pow_sub_one
    [IsCMField R']
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') :
    ringOfIntegersComplexConj R' S.zeta_ell_int =
      S.zeta_ell_int ^ (ℓ - 1) :=
  ringOfIntegersComplexConj_primitiveRoot
    (n := ℓ) (F := R') (Fact.out : Nat.Prime ℓ).pos S.zeta_ell_int_isPrimitiveRoot

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

/-- Trace-form exponent compatibility with negation in the
conductor-flexible setup. -/
theorem zeta_ell_int_pow_sub_one_mul_psiExponent_eq_neg
    (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R') (x : k) :
    S.zeta_ell_int ^ ((ℓ - 1) * S.psiExponent x) =
      S.zeta_ell_int ^ S.psiExponent (-x) := by
  let t : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)
  have ht_neg :
      Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * (-x)) = -t := by
    simp [t, mul_neg]
  rw [S.psiExponent_trace x, S.psiExponent_trace (-x), ht_neg]
  have hcast :
      (((ℓ - 1) * t.val : ℕ) : ZMod ℓ) = (((-t).val : ℕ) : ZMod ℓ) := by
    calc
      (((ℓ - 1) * t.val : ℕ) : ZMod ℓ)
          = ((ℓ - 1 : ℕ) : ZMod ℓ) * (t.val : ZMod ℓ) := by
              rw [Nat.cast_mul]
      _ = (-1 : ZMod ℓ) * t := by
              rw [Nat.cast_sub (Fact.out : Nat.Prime ℓ).one_le,
                ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]
              norm_num
      _ = -t := by simp
      _ = (((-t).val : ℕ) : ZMod ℓ) := by
              rw [ZMod.natCast_zmod_val]
  exact pow_eq_pow_of_modEq
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast)
    S.zeta_ell_int_isPrimitiveRoot.pow_eq_one

/-- If an upstairs endomorphism sends the conductor-flexible chosen integral
`ℓ`-th root to `ζ_ℓ^(ℓ-1)`, it sends the trace-form integral additive
character to its inverse. -/
theorem psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
    (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R') (σ : 𝓞 R' →+* 𝓞 R')
    (hσζ : σ S.zeta_ell_int = S.zeta_ell_int ^ (ℓ - 1)) :
    σ.toMonoidHom.compAddChar S.psiInt = S.psiInt⁻¹ := by
  apply DFunLike.ext
  intro x
  change σ (S.zeta_ell_int ^ S.psiExponent x) =
    S.zeta_ell_int ^ S.psiExponent (-x)
  rw [map_pow, hσζ, ← pow_mul]
  exact S.zeta_ell_int_pow_sub_one_mul_psiExponent_eq_neg x

end ConductorFlexibleTraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
