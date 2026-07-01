module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Concrete Stickelberger setup (Layer 3, REF-18c2c4)

This file packages the arithmetic data needed to turn the abstract
`StickelbergerSetup` API into the concrete cyclotomic situation used by the
digit-sum Stickelberger congruence.

The bundle intentionally keeps the difficult arithmetic assertions as fields:
the prime `Q` above `ℓ`, the integral element `π = ζ_ℓ - 1`, and the residue
map from `𝓞 R'` to the finite field. Later Layer 3 tickets can strengthen this
data by proving the canonical identification of `Q` and constructing
Teichmüller lifts.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Concrete arithmetic data for the Stickelberger congruence over a
cyclotomic field.

The finite field `k` is the residue-field model used in the Gauss-sum layer.
The number field `K` is the `p`-th cyclotomic field, and `R'` is a larger
cyclotomic field containing the `p`- and `ℓ`-power roots needed for the
residue and additive characters. -/
structure ConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] where
  /-- The residue characteristic is different from the Kummer exponent. -/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`. -/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`. -/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`. -/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`. -/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`. -/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`, chosen compatibly with the
  residue-field root `zeta_k`. -/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character. -/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`. -/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`. -/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`. -/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers. -/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`. -/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`. -/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`. -/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`. -/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model. -/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`. -/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root. This pins down the Teichmüller convention used
  by `residueCharInt`. -/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`. -/
  psi : AddChar k R'
  /-- Primitivity of the additive character. -/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`. -/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form. -/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Accessor for the primality of the residue characteristic. -/
theorem ell_prime : Nat.Prime ℓ :=
  Fact.out

/-- Accessor for the primality of the Kummer exponent. -/
theorem p_prime : Nat.Prime p :=
  Fact.out

/-- The residue characteristic and Kummer exponent are distinct. -/
theorem ell_ne_p (S : ConcreteStickelbergerSetup ℓ p k K R') : ℓ ≠ p :=
  S.hℓ_ne_p

/-- The residue-field root is primitive of order `p`. -/
theorem zeta_k_isPrimitiveRoot : IsPrimitiveRoot S.zeta_k p :=
  S.hzeta_k

/-- The target-field `p`-th root is primitive. -/
theorem zeta_p_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p p :=
  S.hzeta_p

/-- The integral lift of `ζ_p` maps to the selected root in `R'`. -/
@[simp]
theorem algebraMap_zeta_p_int :
    algebraMap (𝓞 R') R' S.zeta_p_int = (S.zeta_p : R'ˣ) :=
  S.zeta_p_int_spec

/-- The integral lift of `ζ_p` is still primitive. -/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.algebraMap_zeta_p_int] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)

/-- The target-field `ℓ`-th root is primitive. -/
theorem zeta_ell_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell ℓ :=
  S.hzeta_ell

/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`. -/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell

/-- The cardinality divisibility required to define the residue character. -/
theorem p_dvd_card_sub_one (S : ConcreteStickelbergerSetup ℓ p k K R') :
    p ∣ Fintype.card k - 1 :=
  S.hdiv

/-- The prime ideal `Q` is available as an instance when working from the
bundle. -/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime

/-- The rational prime `ℓ` lies in the selected prime ideal. -/
theorem ell_mem_Q : (ℓ : 𝓞 R') ∈ S.Q :=
  S.hQ

/-- Powers of the residue characteristic land in the corresponding powers of
the selected prime. This is the elementary nilpotence input used when passing
to `Q`-adic quotients. -/
theorem natCast_ell_pow_mem_Q_pow (N : ℕ) :
    (ℓ : 𝓞 R') ^ N ∈ S.Q ^ N :=
  Ideal.pow_mem_pow S.hQ N

/-- In the quotient modulo `Q^(N+1)`, the residue characteristic is nilpotent. -/
theorem quotient_natCast_ell_pow_succ_eq_zero (N : ℕ) :
    (Ideal.Quotient.mk (S.Q ^ (N + 1)) (ℓ : 𝓞 R')) ^ (N + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact S.natCast_ell_pow_mem_Q_pow (N + 1)

/-- Nilpotence form of `quotient_natCast_ell_pow_succ_eq_zero`. -/
theorem quotient_natCast_ell_isNilpotent (N : ℕ) :
    IsNilpotent (Ideal.Quotient.mk (S.Q ^ (N + 1)) (ℓ : 𝓞 R')) :=
  ⟨N + 1, S.quotient_natCast_ell_pow_succ_eq_zero N⟩

/-- The residue map has kernel `Q`. -/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map. -/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]

/-- The integral lift of `ζ_p` reduces to the selected finite-field root. -/
@[simp]
theorem residueMap_zeta_p_int : S.residueMap S.zeta_p_int = (S.zeta_k : k) :=
  S.zeta_p_int_residue

/-- The residue map is surjective. -/
theorem residueMap_surjective' : Function.Surjective S.residueMap :=
  S.residueMap_surjective

/-- The residue map identifies the quotient `𝓞 R' / Q` with the chosen
finite-field model `k`. -/
def residueQuotientEquiv : 𝓞 R' ⧸ S.Q ≃+* k :=
  (Ideal.quotientEquiv S.Q (RingHom.ker S.residueMap) (RingEquiv.refl (𝓞 R')) (by
    simpa using S.residueMap_ker)).trans
    (RingHom.quotientKerEquivOfSurjective S.residueMap_surjective)

@[simp]
theorem residueQuotientEquiv_mk (x : 𝓞 R') :
    S.residueQuotientEquiv (Ideal.Quotient.mk S.Q x) = S.residueMap x := by
  simp [residueQuotientEquiv]

/-- Elements outside `Q` become units modulo every positive power of `Q`. -/
theorem quotient_mk_isUnit_of_not_mem_Q (N : ℕ) {s : 𝓞 R'} (hs : s ∉ S.Q) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) s) := by
  haveI : S.Q.IsMaximal := by
    rw [← S.residueMap_ker_eq]
    exact RingHom.ker_isMaximal_of_surjective S.residueMap S.residueMap_surjective
  exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := S.Q)
    (n := N + 1) (Nat.succ_ne_zero N)).2 hs

/-- The canonical unit in `𝓞 R' / Q^(N+1)` attached to an element outside
`Q`. -/
def quotientUnitOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit

@[simp]
theorem quotientUnitOfNotMemQ_coe (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    (S.quotientUnitOfNotMemQ N s hs : 𝓞 R' ⧸ S.Q ^ (N + 1)) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) s :=
  (S.quotient_mk_isUnit_of_not_mem_Q N hs).unit_spec

/-- The chosen inverse of an element outside `Q` in the quotient by
`Q^(N+1)`. -/
def quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) : 𝓞 R' ⧸ S.Q ^ (N + 1) :=
  ((S.quotientUnitOfNotMemQ N s hs)⁻¹ : (𝓞 R' ⧸ S.Q ^ (N + 1))ˣ)

@[simp]
theorem quotient_mk_mul_quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientInvOfNotMemQ N s hs = 1 := by
  simp [quotientInvOfNotMemQ]

@[simp]
theorem quotientInvOfNotMemQ_mul_quotient_mk
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) s = 1 := by
  simp [quotientInvOfNotMemQ]

@[simp]
theorem quotient_mk_mul_denominator_inv_of_not_mem_Q
    (N : ℕ) (x : 𝓞 R') {s : 𝓞 R'} (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (x * s) *
        S.quotientInvOfNotMemQ N s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  rw [map_mul, mul_assoc, S.quotient_mk_mul_quotientInvOfNotMemQ N s hs, mul_one]

@[simp]
theorem denominator_inv_mul_quotient_mk_mul_of_not_mem_Q
    (N : ℕ) (x : 𝓞 R') {s : 𝓞 R'} (hs : s ∉ S.Q) :
    S.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (s * x) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  rw [map_mul, ← mul_assoc, S.quotientInvOfNotMemQ_mul_quotient_mk N s hs,
    one_mul]

/-- The quotient map sends every local denominator away from `Q` to a unit. -/
theorem quotient_mk_isUnit_primeCompl
    (N : ℕ) (s : S.Q.primeCompl) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R')) :=
  S.quotient_mk_isUnit_of_not_mem_Q N s.property

/-- The canonical map from the localization of `𝓞 R'` away from `Q` to the
finite quotient `𝓞 R' / Q^(N+1)`. This keeps local finite-log fractions inside
the same global quotient used by the Dwork endpoint. -/
def quotientLocalizationAwayQMap (N : ℕ) :
    Localization S.Q.primeCompl →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) :=
  IsLocalization.lift
    (M := S.Q.primeCompl)
    (S := Localization S.Q.primeCompl)
    (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
    (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
    (S.quotient_mk_isUnit_primeCompl N)

@[simp]
theorem quotientLocalizationAwayQMap_algebraMap
    (N : ℕ) (x : 𝓞 R') :
    S.quotientLocalizationAwayQMap N
        (algebraMap (𝓞 R') (Localization S.Q.primeCompl) x) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simp [quotientLocalizationAwayQMap,
    (IsLocalization.lift_eq
      (M := S.Q.primeCompl)
      (S := Localization S.Q.primeCompl)
      (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
      (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
      (S.quotient_mk_isUnit_primeCompl N)
      x)]

/-- Evaluate a local fraction with denominator away from `Q` in the finite
quotient.  The denominator is given as an element of the prime complement so
that algebraic identities have canonical denominator proofs. -/
def quotientFractionEvalPrimeCompl
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientLocalizationAwayQMap N
    (IsLocalization.mk' (Localization S.Q.primeCompl) x s)

/-- Evaluate a local fraction with an explicit proof that the denominator is
outside `Q`. -/
def quotientFractionEval
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientFractionEvalPrimeCompl N x ⟨s, hs⟩

@[simp]
theorem quotientFractionEvalPrimeCompl_one
    (N : ℕ) (x : 𝓞 R') :
    S.quotientFractionEvalPrimeCompl N x 1 =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEvalPrimeCompl] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_one
        (S := Localization S.Q.primeCompl)
        x)

theorem quotientFractionEvalPrimeCompl_den_mul
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
        S.quotientFractionEvalPrimeCompl N x s =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  have h :
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x =
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
          S.quotientFractionEvalPrimeCompl N x s :=
    (IsLocalization.lift_mk'_spec
        (M := S.Q.primeCompl)
        (S := Localization S.Q.primeCompl)
        (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
        (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
        (hg := S.quotient_mk_isUnit_primeCompl N)
        x
        (S.quotientFractionEvalPrimeCompl N x s)
        s).1 (by
          simp [quotientFractionEvalPrimeCompl, quotientLocalizationAwayQMap])
  exact h.symm

theorem quotientFractionEval_den_mul
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_den_mul N x ⟨s, hs⟩

theorem quotientFractionEval_eq_mk_mul_inv
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x *
        S.quotientInvOfNotMemQ N s hs := by
  apply (S.quotient_mk_isUnit_of_not_mem_Q N hs).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEval N x s hs),
    S.quotientFractionEval_den_mul N x s hs, mul_assoc,
    S.quotientInvOfNotMemQ_mul_quotient_mk N s hs, mul_one]

theorem quotientFractionEvalPrimeCompl_add
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') + x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ +
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_add] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_add
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_mul
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (x₁ * x₂) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ *
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_mul] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_mul
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_neg
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (-x) s =
      -S.quotientFractionEvalPrimeCompl N x s := by
  simpa [quotientFractionEvalPrimeCompl, map_neg] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_neg
        (S := Localization S.Q.primeCompl)
        x s)

theorem quotientFractionEvalPrimeCompl_sub
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') - x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ -
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_sub] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_sub
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_pow
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) (m : ℕ) :
    S.quotientFractionEvalPrimeCompl N (x ^ m) (s ^ m) =
      S.quotientFractionEvalPrimeCompl N x s ^ m := by
  simpa [quotientFractionEvalPrimeCompl, map_pow] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_pow
        (S := Localization S.Q.primeCompl)
        x s m)

theorem quotientFractionEvalPrimeCompl_eq_zero_of_mem
    (N : ℕ) {x : 𝓞 R'} (s : S.Q.primeCompl)
    (hx : x ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s = 0 := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [zero_mul, mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

theorem quotientFractionEval_eq_zero_of_mem
    (N : ℕ) {x s : 𝓞 R'} (hs : s ∉ S.Q)
    (hx : x ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEval N x s hs = 0 := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_eq_zero_of_mem N ⟨s, hs⟩ hx

theorem quotientFractionEvalPrimeCompl_eq_of_sub_mem
    (N : ℕ) {x y : 𝓞 R'} (s : S.Q.primeCompl)
    (hxy : x - y ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s =
      S.quotientFractionEvalPrimeCompl N y s := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s,
    mul_comm (S.quotientFractionEvalPrimeCompl N y s),
    S.quotientFractionEvalPrimeCompl_den_mul N y s]
  exact Ideal.Quotient.eq.mpr hxy

theorem quotientFractionEval_eq_of_sub_mem
    (N : ℕ) {x y s : 𝓞 R'} (hs : s ∉ S.Q)
    (hxy : x - y ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEval N x s hs =
      S.quotientFractionEval N y s hs := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_eq_of_sub_mem N ⟨s, hs⟩ hxy

/-- Unit-group form of the residue-field identification. -/
def residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ :=
  Units.mapEquiv S.residueQuotientEquiv.toMulEquiv

@[simp]
theorem residueUnitEquiv_val (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.residueUnitEquiv u : kˣ) : k) =
      S.residueQuotientEquiv (u : 𝓞 R' ⧸ S.Q) := by
  simp [residueUnitEquiv]

/-- The chosen finite field has cardinality `ℓ ^ f`. -/
theorem card_k_eq : Fintype.card k = ℓ ^ S.f :=
  S.card_k

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`. -/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`. -/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ

/-- The image of `π` in `R'` is `ζ_ℓ - 1`. -/
theorem algebraMap_π : algebraMap (𝓞 R') R' S.π = S.zeta_ell - 1 := by
  simp [S.hπ, S.zeta_ell_int_spec]

/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`. This is the
ramification containment available in the mixed cyclotomic field
`ℚ(ζ_p, ζ_ℓ)`. -/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.hπ]
  exact zeta_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot S.hQ

/-- Ideal form of `π_mem_Q`: the principal ideal `(π)` lies below `Q`. -/
theorem span_π_le_Q : Ideal.span {S.π} ≤ S.Q := by
  rw [Ideal.span_singleton_le_iff_mem]
  exact S.π_mem_Q

/-- If a later concrete setup supplies the reverse containment, the selected
prime above `ℓ` is exactly `(π)`. This isolates the equality step from the
general ramification containment, which is all that follows from `ℓ ∈ Q` in a
mixed cyclotomic field. -/
theorem Q_eq_span_π_of_le (hQ_le : S.Q ≤ Ideal.span {S.π}) :
    S.Q = Ideal.span {S.π} :=
  le_antisymm hQ_le S.span_π_le_Q

/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root. -/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API. -/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p
  psi_q := S.psi
  hpsi := S.hpsi

/-- The residue character specialised to the concrete bundle. -/
def residueChar : MulChar k R' :=
  S.abstractSetup.residueChar

/-- The order-`p` Teichmüller representative on the residue ring
`𝓞 R' / Q`, transported through the concrete residue-field model `k`. -/
def teichmuller : (𝓞 R' ⧸ S.Q)ˣ →* R'ˣ :=
  S.residueChar.toUnitHom.comp S.residueUnitEquiv.toMonoidHom

@[simp]
theorem teichmuller_apply_coe (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.teichmuller u : R'ˣ) : R') =
      S.residueChar (S.residueQuotientEquiv (u : 𝓞 R' ⧸ S.Q)) := by
  simp [teichmuller]

@[simp]
theorem teichmuller_apply_mk_unit (u : (𝓞 R')ˣ) :
    ((S.teichmuller (Units.map (Ideal.Quotient.mk S.Q) u) : R'ˣ) : R') =
      S.residueChar (S.residueMap (u : 𝓞 R')) := by
  simp [teichmuller_apply_coe]

/-- Concrete power form of the Teichmüller representative. -/
theorem teichmuller_apply_eq_zeta_p_pow (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.teichmuller u : R'ˣ) : R') =
      ((S.zeta_p : R'ˣ) : R') ^
        (Reflection.ResidueSymbol.PowerResidue.finiteFieldExponent
          S.zeta_k S.hzeta_k S.hdiv (S.residueUnitEquiv u)).val := by
  rw [teichmuller_apply_coe, ← residueUnitEquiv_val, residueChar,
    StickelbergerSetup.residueChar, residueMulChar_apply_unit]
  simp [abstractSetup]

/-- The transported Teichmüller representative has order dividing `p`. -/
theorem teichmuller_pow_eq_one (u : (𝓞 R' ⧸ S.Q)ˣ) :
    S.teichmuller u ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, teichmuller_apply_eq_zeta_p_pow, ← pow_mul, mul_comm, pow_mul]
  have hpow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
  rw [hpow, one_pow, Units.val_one]

/-- The residue Gauss sum specialised to the concrete bundle. -/
def gaussSum : R' :=
  S.abstractSetup.gaussSum

/-- Accessor: `χ_q^p = 1` for the concrete residue character. -/
theorem residueChar_pow_eq_one : S.residueChar ^ p = 1 :=
  S.abstractSetup.residueChar_pow_eq_one

/-- Accessor: the concrete residue character is non-trivial. -/
theorem residueChar_ne_one : S.residueChar ≠ 1 :=
  S.abstractSetup.residueChar_ne_one

/-- Accessor: the concrete Gauss sum satisfies the abstract norm relation. -/
theorem gaussSum_mul_inv_eq_card :
    S.gaussSum * _root_.gaussSum S.residueChar⁻¹ S.psi⁻¹ = Fintype.card k :=
  S.abstractSetup.gaussSum_mul_inv_eq_card

/-- Accessor: concrete q-adic containment from a congruence of `psi` modulo
an ideal. -/
theorem gaussSum_mem_ideal {I : Ideal R'} (h : ∀ x : k, S.psi x - 1 ∈ I) :
    S.gaussSum ∈ I :=
  S.abstractSetup.gaussSum_mem_ideal h

/-- In the pure `ℓ`-cyclotomic field, every prime above `ℓ` is the prime
generated by `ζ_ℓ - 1`. This is the exact mathlib ramification theorem in the
form needed by the mixed setup's local `ℓ`-cyclotomic part. -/
theorem prime_over_ell_eq_span_zeta_sub_one
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {ℓ} ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ ℓ)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(ℓ : ℤ)})] :
    P = Ideal.span {hζ.toInteger - 1} := by
  haveI : IsCyclotomicExtension {ℓ ^ (0 + 1)} ℚ L := by
    simpa only [zero_add, pow_one] using (inferInstance : IsCyclotomicExtension {ℓ} ℚ L)
  have hζ' : IsPrimitiveRoot ζ (ℓ ^ (0 + 1)) := by
    simpa only [zero_add, pow_one] using hζ
  simpa only [zero_add, pow_one] using
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
      (p := ℓ) (k := 0) (K := L) hζ' P)

end ConcreteStickelbergerSetup

/-- Conductor-flexible concrete arithmetic data for the Stickelberger
congruence.

This is the same explicit arithmetic payload as `ConcreteStickelbergerSetup`,
but without the exact pair-cyclotomic typeclass
`[IsCyclotomicExtension {p, ℓ} ℚ R']`.  It is intended for enlarged
cyclotomic fields whose conductor contains the required roots while not being
definitionally the pair conductor. -/
structure ConductorFlexibleConcreteStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] where
  /-- The residue characteristic is different from the Kummer exponent. -/
  hℓ_ne_p : ℓ ≠ p
  /-- Residue degree, with `#k = ℓ ^ f`. -/
  f : ℕ
  /-- The chosen finite field has cardinality `ℓ ^ f`. -/
  card_k : Fintype.card k = ℓ ^ f
  /-- A primitive `p`-th root of unity in the residue field. -/
  zeta_k : kˣ
  /-- Primitivity of `zeta_k`. -/
  hzeta_k : IsPrimitiveRoot zeta_k p
  /-- The cardinality compatibility needed for the residue character. -/
  hdiv : p ∣ Fintype.card k - 1
  /-- A primitive `p`-th root of unity in `R'`. -/
  zeta_p : R'ˣ
  /-- Primitivity of `zeta_p`. -/
  hzeta_p : IsPrimitiveRoot zeta_p p
  /-- An integral lift of `zeta_p` to `𝓞 R'`. -/
  zeta_p_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ)
  /-- A primitive `ℓ`-th root of unity in `R'`, used for the additive character. -/
  zeta_ell : R'
  /-- Primitivity of `zeta_ell`. -/
  hzeta_ell : IsPrimitiveRoot zeta_ell ℓ
  /-- An integral lift of `zeta_ell` to `𝓞 R'`. -/
  zeta_ell_int : 𝓞 R'
  /-- The integral lift maps to the chosen root in `R'`. -/
  zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell
  /-- The uniformizer candidate `π = ζ_ℓ - 1`. -/
  π : 𝓞 R'
  /-- Defining equation for `π` in the ring of integers. -/
  hπ : π = zeta_ell_int - 1
  /-- A prime ideal of `𝓞 R'` above `ℓ`. -/
  Q : Ideal (𝓞 R')
  /-- Primality of `Q`. -/
  hQ_prime : Q.IsPrime
  /-- The rational prime `ℓ` lies in `Q`. -/
  hQ : (ℓ : 𝓞 R') ∈ Q
  /-- A concrete residue map onto the finite-field model `k`. -/
  residueMap : 𝓞 R' →+* k
  /-- The residue map is onto the chosen finite field model. -/
  residueMap_surjective : Function.Surjective residueMap
  /-- The kernel of the residue map is `Q`. -/
  residueMap_ker : RingHom.ker residueMap = Q
  /-- Compatibility between the target primitive `p`-th root and the
  residue-field primitive root. -/
  zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k)
  /-- The primitive additive character on `k`. -/
  psi : AddChar k R'
  /-- Primitivity of the additive character. -/
  hpsi : psi.IsPrimitive
  /-- Exponent function expressing `psi` in powers of `ζ_ℓ`. -/
  psiExponent : k → ℕ
  /-- The additive character has the expected `ζ_ℓ`-power form. -/
  psi_eq_zeta_ell_pow : ∀ x : k, psi x = zeta_ell ^ psiExponent x

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-- The selected over-prime is prime. -/
protected instance Q_isPrime : S.Q.IsPrime :=
  S.hQ_prime

/-- The residue map has kernel `Q`. -/
theorem residueMap_ker_eq : RingHom.ker S.residueMap = S.Q :=
  S.residueMap_ker

/-- Membership in the selected prime is equivalent to vanishing under the
residue map. -/
theorem mem_Q_iff_residueMap_eq_zero (x : 𝓞 R') :
    x ∈ S.Q ↔ S.residueMap x = 0 := by
  rw [← S.residueMap_ker_eq, RingHom.mem_ker]

/-- The residue map identifies the quotient `𝓞 R' / Q` with the chosen
finite-field model `k`. -/
def residueQuotientEquiv : 𝓞 R' ⧸ S.Q ≃+* k :=
  (Ideal.quotientEquiv S.Q (RingHom.ker S.residueMap) (RingEquiv.refl (𝓞 R')) (by
    simpa using S.residueMap_ker)).trans
    (RingHom.quotientKerEquivOfSurjective S.residueMap_surjective)

@[simp]
theorem residueQuotientEquiv_mk (x : 𝓞 R') :
    S.residueQuotientEquiv (Ideal.Quotient.mk S.Q x) = S.residueMap x := by
  simp [residueQuotientEquiv]

/-- Unit-group form of the residue-field identification. -/
def residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ :=
  Units.mapEquiv S.residueQuotientEquiv.toMulEquiv

/-- Forget the concrete arithmetic data and recover the abstract
`StickelbergerSetup` used by the algebraic Gauss-sum API. -/
def abstractSetup : StickelbergerSetup p k R' where
  zeta_q := S.zeta_k
  hzeta_q := S.hzeta_k
  hdiv := S.hdiv
  zeta_R := S.zeta_p
  hzeta_R := S.hzeta_p
  psi_q := S.psi
  hpsi := S.hpsi

/-- The residue character specialised to the conductor-flexible bundle. -/
def residueChar : MulChar k R' :=
  S.abstractSetup.residueChar

/-- The integral lift of `ζ_p` is primitive in `𝓞 R'`. -/
theorem zeta_p_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int p := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_p_int_spec] using (IsPrimitiveRoot.coe_units_iff.mpr S.hzeta_p)

/-- Unit form of the integral `p`-th root. -/
def zeta_p_int_unit : (𝓞 R')ˣ :=
  (S.zeta_p_int_isPrimitiveRoot.isUnit (Fact.out : Nat.Prime p).ne_zero).unit

@[simp]
theorem zeta_p_int_unit_coe : (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int := by
  simp [zeta_p_int_unit]

/-- The unit lift of `ζ_p` reduces to the selected finite-field root. -/
@[simp]
theorem residueMap_zeta_p_int_unit :
    S.residueMap (S.zeta_p_int_unit : 𝓞 R') = (S.zeta_k : k) := by
  rw [S.zeta_p_int_unit_coe]
  exact S.zeta_p_int_residue

/-- The unit lift of `ζ_p` remains primitive. -/
theorem zeta_p_int_unit_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int_unit p := by
  simpa [zeta_p_int_unit] using
    S.zeta_p_int_isPrimitiveRoot.isUnit_unit (Fact.out : Nat.Prime p).ne_zero

/-- The residue character with values in the ring of integers. -/
def residueCharInt : MulChar k (𝓞 R') :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueMulChar S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- The integral lift of `ζ_ℓ` maps to the selected root in `R'`. -/
theorem algebraMap_zeta_ell_int : algebraMap (𝓞 R') R' S.zeta_ell_int = S.zeta_ell :=
  S.zeta_ell_int_spec

/-- The defining equation for `π` in `𝓞 R'`. -/
theorem π_def : S.π = S.zeta_ell_int - 1 :=
  S.hπ

/-- The image of `π` in `R'` is `ζ_ℓ - 1`. -/
theorem algebraMap_π : algebraMap (𝓞 R') R' S.π = S.zeta_ell - 1 := by
  simp [S.hπ, S.zeta_ell_int_spec]

/-- The integral lift of `ζ_ℓ` is primitive in `𝓞 R'`. -/
theorem zeta_ell_int_isPrimitiveRoot : IsPrimitiveRoot S.zeta_ell_int ℓ := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ NumberField.RingOfIntegers.coe_injective
  simpa [S.zeta_ell_int_spec] using S.hzeta_ell

/-- The selected prime above `ℓ` contains `π = ζ_ℓ - 1`. -/
theorem π_mem_Q : S.π ∈ S.Q := by
  rw [S.π_def]
  exact zeta_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot S.hQ

/-- Ideal form of `π_mem_Q`: the principal ideal `(π)` lies below `Q`. -/
theorem span_pi_le_Q : Ideal.span ({S.π} : Set (𝓞 R')) ≤ S.Q :=
  (Ideal.span_singleton_le_iff_mem _).mpr S.π_mem_Q

/-- The additive character is expressed in powers of the chosen primitive
`ℓ`-th root. -/
theorem psi_pow_form (x : k) : S.psi x = S.zeta_ell ^ S.psiExponent x :=
  S.psi_eq_zeta_ell_pow x

/-- The integral additive character defined by the exponent form
`ψ(x) = ζ_ℓ ^ psiExponent x`. -/
def psiInt : AddChar k (𝓞 R') where
  toFun x := S.zeta_ell_int ^ S.psiExponent x
  map_zero_eq_one' := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent 0) =
      algebraMap (𝓞 R') R' (1 : 𝓞 R')
    rw [map_pow, map_one, S.algebraMap_zeta_ell_int]
    simpa [S.psi_pow_form] using (AddChar.map_zero_eq_one S.psi)
  map_add_eq_mul' x y := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent (x + y)) =
      algebraMap (𝓞 R') R'
        (S.zeta_ell_int ^ S.psiExponent x * S.zeta_ell_int ^ S.psiExponent y)
    rw [map_mul, map_pow, map_pow, map_pow, S.algebraMap_zeta_ell_int]
    calc
      S.zeta_ell ^ S.psiExponent (x + y) = S.psi (x + y) := (S.psi_pow_form (x + y)).symm
      _ = S.psi x * S.psi y := AddChar.map_add_eq_mul S.psi x y
      _ = S.zeta_ell ^ S.psiExponent x * S.zeta_ell ^ S.psiExponent y := by
        rw [S.psi_pow_form x, S.psi_pow_form y]

/-- The concrete Gauss sum as an algebraic integer. -/
def gaussSumInt (a : ℕ) : 𝓞 R' :=
  _root_.gaussSum (S.residueCharInt ^ a) S.psiInt

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

/-- The old exact pair-cyclotomic concrete setup is a special case of the
conductor-flexible concrete API. -/
def toConductorFlexible (S : ConcreteStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  hℓ_ne_p := S.hℓ_ne_p
  f := S.f
  card_k := S.card_k
  zeta_k := S.zeta_k
  hzeta_k := S.hzeta_k
  hdiv := S.hdiv
  zeta_p := S.zeta_p
  hzeta_p := S.hzeta_p
  zeta_p_int := S.zeta_p_int
  zeta_p_int_spec := S.zeta_p_int_spec
  zeta_ell := S.zeta_ell
  hzeta_ell := S.hzeta_ell
  zeta_ell_int := S.zeta_ell_int
  zeta_ell_int_spec := S.zeta_ell_int_spec
  π := S.π
  hπ := S.hπ
  Q := S.Q
  hQ_prime := S.hQ_prime
  hQ := S.hQ
  residueMap := S.residueMap
  residueMap_surjective := S.residueMap_surjective
  residueMap_ker := S.residueMap_ker
  zeta_p_int_residue := S.zeta_p_int_residue
  psi := S.psi
  hpsi := S.hpsi
  psiExponent := S.psiExponent
  psi_eq_zeta_ell_pow := S.psi_eq_zeta_ell_pow

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
