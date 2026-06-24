module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.GaloisCovarianceAndK21CrossRing

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/

/-- **K2-1 on embedded descent generator**: applying K2-1 to the
embedded `phiPrimeGenDescent` reduced mod `𝔭` (which equals
`(Quotient.mk 𝔭 gaussSumInt)^p`). -/
theorem residueFieldEmbedding_phiPrimeGenDescent_pow_div_apply_smul_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f) (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0) :
    ((S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭)) unit_a *
        (residueFieldEmbedding h_over
          ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) :
            𝓞 K ⧸ P')) ^ ((ℓ' ^ f - 1) / p) = 1 := by
  rw [residueFieldEmbedding_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero h_over,
      map_pow]
  exact ideal_quotient_mk_gaussSumInt_pow_pow_div_apply_smul_eq_one S a hp h_χp_eq_one
    hf hN_mod_p unit_a h_unit hg_ne

/-! ### `phiPrimeGenDescent` as a Stickelberger ideal generator

When the constructive descent generator `phiPrimeGenDescent S a` lies in
the Stickelberger ideal at `P` and generates it (as a principal ideal),
we can package it into a `StickelbergerIdealEquality P` structure for use
with the K2-2 conditional theorem. -/

/-- **Constructive Stickelberger equality from descent**: given that
`phiPrimeGenDescent S a` generates the Stickelberger ideal at `P`, package
into a `StickelbergerIdealEquality P` structure. -/
theorem StickelbergerIdealEquality.of_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P) :
    StickelbergerIdealEquality (p := p) (K := K) P :=
  ⟨phiPrimeGenDescent S ha₁ ha₂ h_ne_zero,
   phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero, h_span⟩

/-! ### Descent atom (parametric form)

The descent atom — the substantive K2-2 statement — says

`(Quotient.mk P' phiPrimeGenDescent)^((NP'-1)/p) =
  (canonicalResidueZetaP P')^((-s).val)`

where `s = pthSymbolAtPrime_canonical NP' P`. We package the cross-ring
chain (K2-1 + K2-2c + SetupZetaCompatible) into a parametric form: given
the lifted ring identity in `𝓞 R' / 𝔭`, we deduce the descent atom in
`𝓞 K / P'`. -/

/-- **Descent atom from cross-ring identity**: given the lifted descent
identity in `𝓞 R' / 𝔭` (where the K2-1 + K2-2c + compat chain delivers
it), pull back to `𝓞 K / P'` via residue field embedding injectivity. -/
theorem descent_atom_of_cross_ring
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    [hP'_max : P'.IsMaximal]
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    -- The cross-ring lifted identity (the substantive content):
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) :
        𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
      ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^
        (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val := by
  -- Apply embedding e and use injectivity to lift.
  apply residueFieldEmbedding_injective h_over
  -- e (LHS) = e ((Quotient.mk P' phi)^((NP'-1)/p))
  --        = (e (Quotient.mk P' phi))^((NP'-1)/p)  [map_pow]
  --        = (Quotient.mk 𝔭 (algebraMap phi))^((NP'-1)/p)  [residueFieldEmbedding_mk]
  --        = (Quotient.mk 𝔭 (gaussSumInt^p))^((NP'-1)/p)  [algebraMap_phiPrimeGenDescent]
  --        = ((Quotient.mk 𝔭 gaussSumInt)^p)^((NP'-1)/p)  [map_pow]
  rw [map_pow, residueFieldEmbedding_mk h_over,
      algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero, map_pow]
  -- e (RHS) = e ((canonicalResidueZetaP P')^((-s).val))
  --        = (e (canonicalResidueZetaP P'))^((-s).val)  [map_pow]
  --        = (Quotient.mk 𝔭 (algebraMap cyclotomicZetaInteger K))^((-s).val)
  --        = (Quotient.mk 𝔭 zeta_p_int)^((-s).val)  [SetupZetaCompatible]
  rw [map_pow,
      ← canonicalResidueZetaP_image_val h_over,
      ← ideal_quotient_mk_zeta_p_int_eq_canonicalResidueZetaP_image S h_over h_compat]
  exact h_cross_ring

/-- **Descent atom (units form)**: the unit-level form of the descent
identity expected by `K2_2_of_descent_pow_eq_general`. Lifts the
ring-level `descent_atom_of_cross_ring` via `Units.ext`. -/
theorem descent_atom_unit_of_cross_ring
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    [hP'_max : P'.IsMaximal]
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) :
    letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
    Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
        (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
          P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) h_phi_notin_P') =
      canonicalResidueZetaP (p := p) (K := K) P' ^
        (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  apply Units.ext
  -- LHS .val = (Quotient.mk P' phi)^((NP'-1)/p)
  -- RHS .val = (canonicalResidueZetaP P' : 𝓞 K ⧸ P')^((-s).val)
  change ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) :
      𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
    ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^
      (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val
  exact descent_atom_of_cross_ring S ha₁ ha₂ h_ne_zero h_over h_compat h_cross_ring

/-! ### Cross-ring identity: assembly from K2-1 + character-value hypothesis

The cross-ring identity for `descent_atom_of_cross_ring` follows from
the K2-1 cross-ring cancellation plus a character-value hypothesis
(captured in `h_χ_value` below: the value of the residue character at
`unit_a`, which is the substantive K2-2c-with-index claim). -/

/-- **Cross-ring identity from K2-1 + character value**: under the K2-1
cross-ring cancellation hypothesis (LHS · `χ' unit_a` = 1) and a
character-value identification (`χ' unit_a = (Quotient.mk 𝔭 zeta_p_int)^s.val`),
deduce the cross-ring descent identity.

Critical algebraic fact: in a `CommGroupWithZero` of exponent dividing `p`
(specifically `(𝓞 R' / 𝔭)ˣ` for the unit forms), `x^(s.val)⁻¹ = x^((-s).val)`
when `x` has order dividing `p`. We sidestep this by stating the hypothesis
as already in the `(-s).val` form. -/
theorem cross_ring_identity_from_K2_1_K2_2c
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {P P' : Ideal (𝓞 K)} [P'.IsMaximal]
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0)
    -- Substantive hypothesis: the character at unit_a equals (zeta_p_int mod 𝔭)^((-s).val).
    -- Captures the K2-2c-with-index-a content in negated form for direct chaining.
    (h_χ_value :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val = 1) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
        𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
      ((Ideal.Quotient.mk 𝔭
          (S.zeta_p_int)) :
        𝓞 R' ⧸ 𝔭) ^
        (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val := by
  -- K2-1 cross-ring: χ' unit_a · (gaussSumInt mod 𝔭)^p^((N𝔭-1)/p) = 1.
  have h_K21 := ideal_quotient_mk_gaussSumInt_pow_pow_div_apply_smul_eq_one S a hp h_χp_eq_one
    hf hN_mod_p unit_a h_unit hg_ne
  -- Substitute (ℓ' ^ f - 1)/p = (NP' - 1)/p via hN_eq.
  rw [← hN_eq,
      ← mul_one ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)),
      ← h_χ_value,
      show ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)) *
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) =
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)) *
      (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^
          (- BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val by ring,
      h_K21, one_mul, hN_eq]

/-! ### K2-2c with character pow

When `residueCharInt = residueMulChar` (typical setup), then
`(residueCharInt^a).ringHomComp σ` evaluated at a quotient class equals
`σ(zeta_R)` raised to `a · pthSymbol.val`. -/

/-- **K2-2c with pow**: applying `(residueMulChar^a).ringHomComp σ` to
`Quotient.mk P α` gives `σ(zeta_R)` raised to `a * (pthSymbol α P).val`. -/
theorem residueMulChar_pow_ringHomComp_apply_quotient_canonical
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    (P : Ideal (𝓞 K)) (hbot : P ≠ ⊥) [hmax : P.IsMaximal]
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (hp_in : (p : 𝓞 K) ∉ P)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'') {a : ℕ} (ha : a ≠ 0)
    {α : 𝓞 K} (hα : α ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    (((residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
        hdiv zeta_R hzeta_R) ^ a).ringHomComp σ)
        ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      σ ((zeta_R : R')) ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply' _ ha,
      residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol
        P hbot hdiv hp_in zeta_R hzeta_R hα,
      ← pow_mul, map_pow, mul_comm]

/-! ### h_χ_value derivation: the per-index K2-2c content (negated form)

To use `cross_ring_identity_from_K2_1_K2_2c`, we need `h_χ_value`:

`χ' unit_a · (Quotient.mk 𝔭 zeta_p_int)^((-s).val) = 1`

Equivalently, `χ' unit_a = (Quotient.mk 𝔭 zeta_p_int)^(-((-s).val))`. From
`residueMulChar_pow_ringHomComp_apply_quotient_canonical` we get
`χ' unit_a = σ(zeta_R)^(a · s.val)`. Combining yields the constraint

`σ(zeta_R)^(a · s.val + (-s).val) = 1`

which holds when `a · s.val + (-s).val ≡ 0 (mod p)`, i.e., when
`(a - 1) · s.val ≡ 0 (mod p)` (using zeta of order p). -/

/-- **Order-p exponent congruence**: in a monoid where `x^p = 1`, if
`m + n ≡ 0 (mod p)` then `x^m · x^n = 1`. -/
theorem pow_add_eq_one_of_order_dvd_p
    {G : Type*} [Monoid G]
    {x : G} {p : ℕ} (_hp : 0 < p) (hx : x ^ p = 1)
    (m n : ℕ) (h_sum : (m + n) % p = 0) :
    x ^ m * x ^ n = 1 := by
  rw [← pow_add,
      show m + n = p * ((m + n) / p) + (m + n) % p from (Nat.div_add_mod _ _).symm,
      h_sum, add_zero, pow_mul, hx, one_pow]

/-- **Sum of `n.val` and `(-n).val` is `0 mod p`** for `n : ZMod p`. -/
theorem ZMod.val_add_neg_val {p : ℕ} [NeZero p] (n : ZMod p) :
    (n.val + (-n).val) % p = 0 := by
  have h : ((n.val + (-n).val : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.natCast_val, ZMod.cast_id']
    simp
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- **`h_χ_value` from "single-power" form**: if `χ' unit_a = x^(s.val)`
and `x` has order dividing `p`, then `χ' unit_a · x^((-s).val) = 1`. -/
theorem h_chi_value_of_single_power
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {G : Type*} [Monoid G]
    {x χ_u : G} {s : ZMod p}
    (h_eval : χ_u = x ^ s.val)
    (h_x_order : x ^ p = 1) :
    χ_u * x ^ (-s).val = 1 := by
  rw [h_eval]
  exact pow_add_eq_one_of_order_dvd_p (Fact.out : p.Prime).pos h_x_order s.val (-s).val
    (ZMod.val_add_neg_val s)

/-! ### General descent atom (parametric exponent t)

Generalizing `descent_atom_of_cross_ring` and `descent_atom_unit_of_cross_ring`
to take an arbitrary target exponent `t : ZMod p`, with conclusion
`...^t.val`. -/

/-- **General descent atom (ring level)**: parametric in `t : ZMod p`. -/
theorem descent_atom_of_cross_ring_general
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} [hP'_max : P'.IsMaximal]
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    (t : ZMod p)
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) :
        𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
      ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^ t.val := by
  apply residueFieldEmbedding_injective h_over
  rw [map_pow, residueFieldEmbedding_mk h_over,
      algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero, map_pow]
  rw [map_pow,
      ← canonicalResidueZetaP_image_val h_over,
      ← ideal_quotient_mk_zeta_p_int_eq_canonicalResidueZetaP_image S h_over h_compat]
  exact h_cross_ring

/-- **General descent atom (units level)**: parametric in `t : ZMod p`. -/
theorem descent_atom_unit_of_cross_ring_general
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    [hP'_max : P'.IsMaximal]
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    (t : ZMod p)
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val) :
    letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
    Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
        (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
          P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) h_phi_notin_P') =
      canonicalResidueZetaP (p := p) (K := K) P' ^ t.val := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  apply Units.ext
  change ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) :
      𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
    ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^ t.val
  exact descent_atom_of_cross_ring_general S ha₁ ha₂ h_ne_zero h_over h_compat t h_cross_ring

/-- **Cross-ring identity (general)**: parametric in `t : ZMod p`.
Given the K2-1 cancellation (LHS · χ' u = 1) and a character-value
hypothesis (χ' u · X^t.val = 1), conclude LHS = X^t.val. -/
theorem cross_ring_identity_from_K2_1_K2_2c_general
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (t : ZMod p)
    (h_χ_value :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val = 1) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
        𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
      ((Ideal.Quotient.mk 𝔭
          (S.zeta_p_int)) :
        𝓞 R' ⧸ 𝔭) ^ t.val := by
  have h_K21 := ideal_quotient_mk_gaussSumInt_pow_pow_div_apply_smul_eq_one S a hp h_χp_eq_one
    hf hN_mod_p unit_a h_unit hg_ne
  rw [← hN_eq,
      ← mul_one ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)),
      ← h_χ_value,
      show ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)) *
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^ t.val) =
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p)) *
      (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^ t.val by ring,
      h_K21, one_mul]

/-! ### Full K2-2 path (a) per-index theorem

Combining the chain — `cross_ring_identity_from_K2_1_K2_2c_general` →
`descent_atom_unit_of_cross_ring_general` →
`pthSymbolAtPrime_canonical_eq_of_descent_pow_eq` — gives the per-index
K2-2 conclusion. -/

/-- **K2-2 per-index symbol identity (path a)**: under the full chain of
hypotheses (K2-1 cross-ring inputs, SetupZetaCompatible, character-value
hypothesis at unit_a), the canonical p-th symbol of `phiPrimeGenDescent S a`
at `P'` equals the prescribed target `t : ZMod p`. -/
theorem K2_2_path_a_pthSymbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (t : ZMod p)
    (h_χ_value :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val = 1) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' = t := by
  -- Step 1: cross-ring identity from K2-1 + h_χ_value.
  have h_cross_ring := cross_ring_identity_from_K2_1_K2_2c_general
    S a hp h_χp_eq_one hf hN_eq hN_mod_p unit_a h_unit hg_ne t h_χ_value
  -- Step 2: descent atom (units form) from cross-ring identity.
  have h_descent := descent_atom_unit_of_cross_ring_general
    S ha₁ ha₂ h_ne_zero hdiv_P' h_phi_notin_P' h_over h_compat t h_cross_ring
  -- Step 3: pthSymbol = t from descent atom (discrete log uniqueness).
  exact pthSymbolAtPrime_canonical_eq_of_descent_pow_eq
    hP'_bot hp_in_P' hdiv_P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)
    h_phi_notin_P' t h_descent

/-! ### Specialized to single-power character form

When the character value at unit_a is a "single-power" `X^(s'.val)` for
some `s' : ZMod p`, with `X = (Quotient.mk 𝔭 zeta_p_int)` of order
dividing `p`, the descent atom yields `pthSymbol (phi_a) P' = -s'`. -/

/-- **K2-2 path (a) per-index, specialized to single-power χ value**:
under the K2-1 hypotheses, SetupZetaCompatible, and a "single-power" form
`χ' unit_a = X^(s'.val)` with `X^p = 1`, conclude
`pthSymbol (phiPrimeGenDescent S a) P' = -s'`. -/
theorem K2_2_path_a_pthSymbol_of_single_power
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (h_zeta_pow_p :
      ((Ideal.Quotient.mk 𝔭
        (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ p = 1)
    (s' : ZMod p)
    (h_χ_eval :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ s'.val) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' = -s' := by
  -- Derive h_χ_value from h_χ_eval + h_zeta_pow_p via h_chi_value_of_single_power.
  have h_χ_value := h_chi_value_of_single_power (s := s') h_χ_eval h_zeta_pow_p
  -- Set t = -s' and apply K2_2_path_a_pthSymbol.
  exact K2_2_path_a_pthSymbol S ha₁ ha₂ h_ne_zero hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp h_χp_eq_one hf hN_eq hN_mod_p unit_a h_unit hg_ne (-s') h_χ_value

/-! ### Pow mod p for order-p elements

Bridge lemmas for converting between natural-number powers and
ZMod p val powers when the base has order dividing p. -/

/-- **Pow mod p**: in a monoid, if `x^p = 1`, then `x^n = x^(n % p)`. -/
theorem pow_eq_pow_mod_p_of_order_dvd
    {G : Type*} [Monoid G] {x : G} {p : ℕ}
    (hx : x ^ p = 1) (n : ℕ) :
    x ^ n = x ^ (n % p) := by
  rcases Nat.eq_zero_or_pos p with h_p_zero | h_p_pos
  · subst h_p_zero
    simp
  · conv_lhs => rw [show n = p * (n / p) + n % p from (Nat.div_add_mod _ _).symm]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- **`(n.val · m).val · p arithmetic**: for `n m : ZMod p`, the natural
val of `n * m` equals `(n.val * m.val) % p`. -/
theorem ZMod.val_mul_eq_mod {p : ℕ} [NeZero p] (n m : ZMod p) :
    (n * m).val = (n.val * m.val) % p := ZMod.val_mul n m

/-- **`x^(n.val * m)` for `n : ZMod p` and `m : ℕ`**: equals
`x^((n * m_zmod).val)` where `m_zmod = (m : ZMod p)`. Useful for
converting per-index `a * s.val` to `(a * s).val`. -/
theorem pow_natVal_mul_eq_pow_zmod_mul
    {G : Type*} [Monoid G] {x : G} {p : ℕ} [NeZero p]
    (hx : x ^ p = 1) (n : ZMod p) (m : ℕ) :
    x ^ (m * n.val) = x ^ ((m : ZMod p) * n).val := by
  rw [pow_eq_pow_mod_p_of_order_dvd hx (m * n.val)]
  congr 1
  rw [ZMod.val_mul_eq_mod, ZMod.val_natCast]
  -- Goal: m * n.val % p = m % p * n.val % p
  conv_lhs => rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt n)]

/-! ### Specialized to per-index K2-2c form

When the K2-2c-with-pow form gives `χ' unit_a = X^(a * s.val)` (Nat
times Nat-val), we bridge to single-power via `pow_natVal_mul_eq_pow_zmod_mul`
and apply the single-power apex. -/

/-- **K2-2 path (a) per-index, specialized to K2-2c-with-pow form**: under
the K2-1 hypotheses, SetupZetaCompatible, and the per-index K2-2c form
`χ' unit_a = X^(a * s.val)` with `X^p = 1`, conclude
`pthSymbol (phiPrimeGenDescent S a) P' = -((a : ZMod p) * s)`. -/
theorem K2_2_path_a_pthSymbol_of_K2_2c_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (h_zeta_pow_p :
      ((Ideal.Quotient.mk 𝔭
        (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ p = 1)
    (s : ZMod p)
    (h_χ_eval_pow :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ (a * s.val)) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) * s) := by
  -- Convert h_χ_eval_pow from "Nat × Nat-val" form to single-power form via
  -- pow_natVal_mul_eq_pow_zmod_mul.
  have h_χ_eval_single : ((S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭)) unit_a =
      ((Ideal.Quotient.mk 𝔭
          (S.zeta_p_int)) :
        𝓞 R' ⧸ 𝔭) ^ (((a : ZMod p) * s).val) := by
    rw [h_χ_eval_pow, pow_natVal_mul_eq_pow_zmod_mul h_zeta_pow_p s a]
  -- Apply single-power apex.
  exact K2_2_path_a_pthSymbol_of_single_power S ha₁ ha₂ h_ne_zero hP'_bot hp_in_P'
    hdiv_P' h_phi_notin_P' h_over h_compat hp h_χp_eq_one hf hN_eq hN_mod_p unit_a h_unit hg_ne
    h_zeta_pow_p ((a : ZMod p) * s) h_χ_eval_single

/-- **`zeta_p_int` reduces to a `p`-th-power-`= 1` element in `𝓞 R'/𝔭`**.
Direct from `zeta_p_int_unit_isPrimitiveRoot` + ring hom map_pow. -/
theorem ideal_quotient_mk_zeta_p_int_pow_p_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')} :
    ((Ideal.Quotient.mk 𝔭
      (S.zeta_p_int)) :
        𝓞 R' ⧸ 𝔭) ^ p = 1 := by
  rw [← map_pow]
  -- zeta_p_int^p = 1 in 𝓞 R' (since zeta_p_int_unit is primitive p-th root).
  have h := S.zeta_p_int_unit_isPrimitiveRoot.pow_eq_one
  -- h : zeta_p_int_unit ^ p = 1 (in (𝓞 R')ˣ)
  have h_val : ((S.zeta_p_int_unit ^ p : (𝓞 R')ˣ) : 𝓞 R') = 1 := by
    rw [h]; rfl
  rw [Units.val_pow_eq_pow_val,
      show (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int from S.zeta_p_int_unit_coe] at h_val
  rw [h_val, map_one]

/-! ### Discharging h_χ_eval_pow from residueCharInt = residueMulChar

Abstract bridge: given an arbitrary character `χ` on `𝓞 K / P` identified
with `residueMulChar (canonicalResidueZetaP P) ... zeta_R ...`, the
per-index K2-2c form holds. -/

/-- **h_χ_eval_pow from character identification**: under the abstract
identification `χ = residueMulChar (canonicalResidueZetaP P) ... zeta_R ...`,
the per-index K2-2c form holds. Abstracted over the setup so callers can
specialize to whatever k they need. -/
theorem chi_pow_apply_quotient_eq_pow_pthSymbol
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'')
    {a : ℕ} (ha : a ≠ 0)
    {α : 𝓞 K} (hα : α ∉ P)
    (χ : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      MulChar (𝓞 K ⧸ P) R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      χ = residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        hdiv zeta_R hzeta_R) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((χ ^ a).ringHomComp σ) ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      σ (zeta_R : R') ^
        (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [h_residue_char_eq]
  exact residueMulChar_pow_ringHomComp_apply_quotient_canonical
    P hP_bot hdiv hp_in_P zeta_R hzeta_R σ ha hα

end Furtwaengler

end BernoulliRegular

end
