module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.CanonicalResidueCharK22Path

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

/-- **Concrete K2-2 path (a) for the canonical residue-field setup**.  This
specializes `K2_2_path_a_pthSymbol_of_residueCharInt_K2_2c_pow` to
`k = 𝓞 K / P` and discharges the final character-value hypothesis from the
explicit compatibility
`residueCharInt = residueMulChar (canonicalResidueZetaP P) ...`.

The remaining inputs are the arithmetic side conditions needed by the path:
the prime above `P'`, zeta compatibility in the extension residue field,
nonvanishing of the reduced Gauss sum, and the fact that the norm
`#(𝓞 K / P') = ℓ' ^ f` is nonzero in `𝓞 K / P`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (hn_notin_P : (((ℓ' ^ f : ℕ) : 𝓞 K)) ∉ P)
    (hg_ne : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let unit_a : (𝓞 K ⧸ P)ˣ :=
    unitOfNatCast_notMem (K := K) (P := P) (ℓ' ^ f) hn_notin_P
  have h_unit :
      (unit_a : 𝓞 K ⧸ P) = ((ℓ' ^ f : ℕ) : 𝓞 K ⧸ P) :=
    unitOfNatCast_notMem_eq_natCast (K := K) (P := P) (ℓ' ^ f) hn_notin_P
  have h_eval_nat := residueCharInt_pow_apply_unitOfNatCast_eq_pow_pthSymbol
    hP_bot hp_in_P hdiv_P S h_residue_char_eq (𝔭 := 𝔭) ha₁ hn_notin_P
  have hcast :
      (((ℓ' ^ f : ℕ) : 𝓞 K)) =
        (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) := by
    rw [hN_eq]
    norm_num
  have h_eval :
      ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^
          (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) := by
    simpa [unit_a, hcast] using h_eval_nat
  exact K2_2_path_a_pthSymbol_of_residueCharInt_K2_2c_pow
    (S := S) ha₁ ha₂ h_ne_zero hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp hf hN_eq hN_mod_p unit_a h_unit hg_ne
    (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)
    h_eval

/-- **Canonical K2-2 path with arithmetic side conditions discharged from
prime/norm data**.  Compared to
`K2_2_path_a_pthSymbol_of_canonical_residueCharInt`, callers no longer need
to provide `1 ≤ ℓ' ^ f`, `(ℓ' ^ f) % p = 1`, or `ℓ' ^ f ∉ P`; these follow from
`ℓ'` prime, `#(𝓞 K / P') = ℓ' ^ f`, `p ∣ #(𝓞 K / P') - 1`, and
`ℓ' ∉ P`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_norm_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    {f : ℕ}
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hℓ'_notin_P : (((ℓ' : ℕ) : 𝓞 K)) ∉ P)
    (hg_ne : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hf : 1 ≤ ℓ' ^ f := one_le_pow_of_natPrime
  have hN_pos : 0 < ℓ' ^ f :=
    Nat.pow_pos (Fact.out : ℓ'.Prime).pos
  have hN_mod_p : (ℓ' ^ f) % p = 1 :=
    Nat.mod_eq_one_of_dvd_sub_one hp hN_pos (by
      rw [hN_eq]
      exact hdiv_P')
  have hn_notin_P : (((ℓ' ^ f : ℕ) : 𝓞 K)) ∉ P := by
    haveI : P.IsPrime := hP_max.isPrime
    exact natCast_pow_notMem_of_natCast_notMem (K := K) (P := P) hℓ'_notin_P
  exact K2_2_path_a_pthSymbol_of_canonical_residueCharInt
    hP_bot hp_in_P hdiv_P S h_residue_char_eq ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp hf hN_eq hN_mod_p hn_notin_P hg_ne

/-- **Canonical K2-2 path with rational-prime separation discharging
`ℓ' ∉ P`**.  This is the norm-power wrapper plus the standard fact that a
prime different from the residue characteristic is nonzero in the residue
field. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_norm_pow_ne_char
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    {f : ℕ}
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hℓ_ne_ℓ' : ℓ ≠ ℓ')
    (hg_ne : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (𝓞 K ⧸ P) ℓ :=
    charP_quotient_of_natPrime_mem P (Fact.out : ℓ.Prime) hℓ_in_P
  have hℓ'_notin_P : (((ℓ' : ℕ) : 𝓞 K)) ∉ P :=
    natPrime_notMem_of_charP_quotient_ne
      (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (Fact.out : ℓ'.Prime) hℓ_ne_ℓ'
  exact K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_norm_pow
    hP_bot hp_in_P hdiv_P S h_residue_char_eq ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp hN_eq hℓ'_notin_P hg_ne

/-- **Canonical K2-2 path with the residue norm power extracted from finite
field theory**.  This wrapper removes the explicit `f` and
`ℓ' ^ f = #(𝓞 K/P')` inputs: they are obtained from the characteristic of
`𝓞 K/P'`, itself pulled back from the residue-field embedding into
`𝓞 R'/𝔭`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (hℓ_ne_ℓ' : ℓ ≠ ℓ')
    (hg_ne : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  haveI : CharP (𝓞 K ⧸ P') ℓ' := charP_baseResidue_of_liesOver h_over
  obtain ⟨f, _hℓ'_prime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P') ℓ'
  exact K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_norm_pow_ne_char
    hP_bot hℓ_in_P hp_in_P hdiv_P S h_residue_char_eq ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp (f := (f : ℕ)) hcard.symm hℓ_ne_ℓ' hg_ne

/-- **Top canonical K2-2 path with reduced Gauss-sum nonvanishing derived**.
This is the current most caller-facing path-a specialization: arithmetic norm
data, rational-prime separation, and reduced Gauss-sum nonvanishing are all
derived from structural inputs. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0 :=
    gaussSum_ringHomComp_ne_zero_of_phiPrimeGenDescent_notMem
      S ha₁ ha₂ h_ne_zero h_phi_notin_P' h_over
  exact K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char
    hP_bot hℓ_in_P hp_in_P hdiv_P S h_residue_char_eq ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp hℓ_ne_ℓ' hg_ne

/-- **Top canonical K2-2 path with residue-field divisibilities derived from
canonical residue roots**.  This wrapper removes the explicit assumptions
`p ∣ #(𝓞 K/P)-1` and `p ∣ #(𝓞 K/P')-1`; both follow from the canonical
primitive `p`-th roots in the two residue fields, using `p ∉ P` and
`p ∉ P'`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zetaDiv
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          (canonicalResidueZetaP_card_sub_one_dvd
            (p := p) (K := K) (q := P) hP_bot hp_in_P)
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1 :=
    canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P) hP_bot hp_in_P
  have hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1 :=
    canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P') hP'_bot hp_in_P'
  exact K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem
    hP_bot hℓ_in_P hp_in_P hdiv_P S
    (by simpa [hdiv_P] using h_residue_char_eq)
    ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over h_compat hp hℓ_ne_ℓ'

/-- **Top canonical K2-2 path from setup root compatibility**.  This is the
same caller-facing path-a theorem as
`K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zetaDiv`,
but replaces the full character equality by the simpler concrete root-choice
compatibility `S.zeta_k = canonicalResidueZetaP P`, and derives `1 < p`
from `[Fact (Nat.Prime p)]`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_k
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      SetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact
    K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zetaDiv
      hP_bot hℓ_in_P hp_in_P S
      (FullTeichDworkSetup.residueCharInt_eq_canonical_of_zeta_k_eq
        (p := p) (K := K) (P := P) hP_bot hp_in_P S h_zeta_k_eq)
      ha₁ ha₂ h_ne_zero
      hP'_bot hp_in_P' h_phi_notin_P'
      h_over h_compat (Fact.out : Nat.Prime p).one_lt hℓ_ne_ℓ'

/-- **Top canonical K2-2 path from source and target root choices**.  This
wrapper replaces both compatibility predicates by concrete equalities of the
chosen roots: `S.zeta_k` is the canonical source residue root at `P`, and
`S.zeta_p_int` is the image of the canonical cyclotomic integer from `K`. -/
theorem K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_choices
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact
    K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_k
      hP_bot hℓ_in_P hp_in_P S h_zeta_k_eq
      ha₁ ha₂ h_ne_zero
      hP'_bot hp_in_P' h_phi_notin_P'
      h_over (setupZetaCompatible_of_zeta_p_int_eq S h_zeta_p_int_eq) hℓ_ne_ℓ'

/-! ### Conductor-flexible K2-2 path

The following lemmas are the conductor-flexible analogue of the K2-2 path
above.  They deliberately consume `ConductorFlexibleFullTeichDworkSetup`
directly, together with the `h_psi` descent-compatibility witness, instead of
promoting the setup back to the old pair-cyclotomic interface. -/

/-- Flexible setup-zeta compatibility: in the target residue ring, the
setup's chosen integral `p`-th root reduces to the canonical cyclotomic
integer from `K`. -/
def ConductorFlexibleSetupZetaCompatible
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')} : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  Ideal.Quotient.mk 𝔭 S.zeta_p_int =
    Ideal.Quotient.mk 𝔭
      ((algebraMap (𝓞 K) (𝓞 R'))
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K))

/-- Literal equality of integral root choices implies flexible zeta
compatibility at every target prime. -/
theorem conductorFlexibleSetupZetaCompatible_of_zeta_p_int_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')}
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K)) :
    ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭) := by
  unfold ConductorFlexibleSetupZetaCompatible
  rw [h_zeta_p_int_eq]

/-- Under flexible zeta compatibility, the setup's `zeta_p_int` reduction is
the embedded canonical residue `p`-th root at the target prime. -/
theorem ConductorFlexibleFullTeichDworkSetup.ideal_quotient_mk_zeta_p_int_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Ideal.Quotient.mk 𝔭 S.zeta_p_int =
      ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
        h_over) : 𝓞 R' ⧸ 𝔭) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [h_compat, canonicalResidueZetaP_image_val h_over,
    canonicalResidueZetaP_val P', residueFieldEmbedding_mk h_over]

/-- The conductor-flexible integral residue character has order dividing
`p`, exposed in the cross-ring namespace to avoid importing the principal-unit
consumer layer. -/
theorem ConductorFlexibleConcreteStickelbergerSetup.residueCharInt_pow_eq_one_crossRing
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') :
    S.residueCharInt ^ p = 1 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  unfold ConductorFlexibleConcreteStickelbergerSetup.residueCharInt
  exact residueMulChar_pow_eq_one_mulChar
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- Flexible K2-1 character-order input from the setup. -/
theorem ConductorFlexibleFullTeichDworkSetup.residueCharInt_ringHomComp_pow_p_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (a : ℕ) (𝔭 : Ideal (𝓞 R')) :
    (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1 :=
  mulChar_pow_ringHomComp_pow_p_eq_one
    S.residueCharInt
    (S.concrete.residueCharInt_pow_eq_one_crossRing)
    a (Ideal.Quotient.mk 𝔭)

/-- Flexible `zeta_p_int` reduces to an element whose `p`-th power is `1`. -/
theorem ConductorFlexibleFullTeichDworkSetup.ideal_quotient_mk_zeta_p_int_pow_p_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')} :
    ((Ideal.Quotient.mk 𝔭 S.zeta_p_int) : 𝓞 R' ⧸ 𝔭) ^ p = 1 := by
  rw [← map_pow]
  have h := S.zeta_p_int_unit_isPrimitiveRoot.pow_eq_one
  have h_val : ((S.zeta_p_int_unit ^ p : (𝓞 R')ˣ) : 𝓞 R') = 1 := by
    rw [h]
    rfl
  rw [Units.val_pow_eq_pow_val] at h_val
  rw [show (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int from
    S.zeta_p_int_unit_coe] at h_val
  rw [h_val, map_one]

/-- Flexible `gaussSumInt` reduced mod `𝔭` is the Gauss sum of the
post-composed characters. -/
theorem ConductorFlexibleFullTeichDworkSetup.ideal_quotient_mk_gaussSumInt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (a : ℕ) (𝔭 : Ideal (𝓞 R')) :
    Ideal.Quotient.mk 𝔭 (S.gaussSumInt a) =
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) := by
  unfold ConductorFlexibleConcreteStickelbergerSetup.gaussSumInt
  exact gaussSum_ringHomComp _ _ (Ideal.Quotient.mk 𝔭)

/-- Flexible K2-1 cancellation in the cross-ring residue field. -/
theorem ConductorFlexibleFullTeichDworkSetup.ideal_quotient_mk_gaussSumInt_pow_pow_div
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
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
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p) =
      1 := by
  rw [S.ideal_quotient_mk_gaussSumInt]
  exact gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP_field hp _ h_χp_eq_one _
    hf hN_mod_p unit_a h_unit hg_ne

/-- Flexible embedding sends the descended generator to `gaussSumInt^p` mod
the chosen over-prime. -/
theorem ConductorFlexibleFullTeichDworkSetup.residueFieldEmbedding_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    residueFieldEmbedding h_over
      ((Ideal.Quotient.mk P' (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)) :
        𝓞 K ⧸ P') =
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p)) : 𝓞 R' ⧸ 𝔭) := by
  rw [residueFieldEmbedding_mk h_over]
  rw [S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero]

/-- Flexible reduced Gauss-sum nonvanishing from descended generator
nonmembership at the target prime. -/
theorem ConductorFlexibleFullTeichDworkSetup.gaussSum_ringHomComp_ne_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    gaussSum
      ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
      ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0 := by
  let x : 𝓞 K ⧸ P' := Ideal.Quotient.mk P'
    (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)
  have hx_ne : x ≠ 0 := fun hx =>
    h_phi_notin_P' (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have h_image_ne : residueFieldEmbedding h_over x ≠ 0 := by
    intro hx0
    have hx_eq : residueFieldEmbedding h_over x = residueFieldEmbedding h_over 0 := by
      simpa using hx0
    exact hx_ne ((residueFieldEmbedding_injective h_over) hx_eq)
  have h_embed := S.residueFieldEmbedding_phiPrimeGenDescent
    h_psi ha₁ ha₂ h_ne_zero h_over
  have h_embed_x :
      residueFieldEmbedding h_over x =
        (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) := by
    simpa [x] using h_embed
  have h_pow_ne :
      (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) ≠ 0 := fun hzero =>
    h_image_ne (by rw [h_embed_x]; exact hzero)
  intro hg
  have h_mk_zero : Ideal.Quotient.mk 𝔭 (S.gaussSumInt a) = 0 := by
    rw [S.ideal_quotient_mk_gaussSumInt]
    exact hg
  have h_pow_zero :
      (Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p) : 𝓞 R' ⧸ 𝔭) = 0 := by
    rw [map_pow, h_mk_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  exact h_pow_ne h_pow_zero

/-- Flexible source-root compatibility identifies the setup residue character
with the canonical residue character at `P`. -/
theorem ConductorFlexibleFullTeichDworkSetup.residueCharInt_eq_canonical_of_zeta_k_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.residueCharInt =
      residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
        (canonicalResidueZetaP_card_sub_one_dvd
          (p := p) (K := K) (q := P) hP_bot hp_in_P)
        S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt]
  exact residueMulChar_eq_of_zeta_eq h_zeta_k_eq
    S.hzeta_k S.hdiv
    (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
    (canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P) hP_bot hp_in_P)
    S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot

/-- Flexible K2-2c character evaluation at the natural norm unit. -/
theorem ConductorFlexibleFullTeichDworkSetup.residueCharInt_pow_apply_unitOfNatCast
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_residue_char_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P
          S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot)
    {𝔭 : Ideal (𝓞 R')}
    {a n : ℕ} (ha₁ : 1 ≤ a)
    (hn : ((n : ℕ) : 𝓞 K) ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        (unitOfNatCast_notMem (K := K) (P := P) n hn) =
      ((Ideal.Quotient.mk 𝔭
          S.zeta_p_int) :
        𝓞 R' ⧸ 𝔭) ^
        (a * (pthSymbolAtPrime_canonical (p := p) (K := K)
          (((n : ℕ) : 𝓞 K)) P).val) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha₁
  have h_eval := chi_pow_apply_unit_eq_pow_pthSymbol
    (p := p) (K := K) (R' := 𝓞 R') (R'' := 𝓞 R' ⧸ 𝔭)
    hP_bot hp_in_P hdiv_P
    S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot
    (Ideal.Quotient.mk 𝔭) ha_ne
    S.residueCharInt
    h_residue_char_eq hn
    (unitOfNatCast_notMem (K := K) (P := P) n hn)
    (unitOfNatCast_notMem_val (K := K) (P := P) n hn)
  simpa [ConductorFlexibleConcreteStickelbergerSetup.zeta_p_int_unit_coe] using h_eval

/-- Flexible cross-ring identity from K2-1 plus character evaluation. -/
theorem ConductorFlexibleFullTeichDworkSetup.cross_ring_identity_from_K2_1_K2_2c
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
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
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h_K21 := S.ideal_quotient_mk_gaussSumInt_pow_pow_div
    a hp h_χp_eq_one hf hN_mod_p unit_a h_unit hg_ne
  rw [← hN_eq]
  have h := h_K21
  rw [← mul_one ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^
    ((ℓ' ^ f - 1) / p))]
  rw [← h_χ_value]
  rw [show ((((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^
        ((ℓ' ^ f - 1) / p)) *
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^ t.val) =
      (((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^
          ((ℓ' ^ f - 1) / p)) *
      (((Ideal.Quotient.mk 𝔭) S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^ t.val by ring]
  rw [h, one_mul]

/-- Flexible descent atom at ring level. -/
theorem ConductorFlexibleFullTeichDworkSetup.descent_atom_of_cross_ring
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} [hP'_max : P'.IsMaximal]
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    (t : ZMod p)
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((Ideal.Quotient.mk P' (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) :
        𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
      ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^ t.val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply (residueFieldEmbedding_injective h_over)
  rw [map_pow, residueFieldEmbedding_mk h_over,
    S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero, map_pow]
  rw [map_pow, ← canonicalResidueZetaP_image_val h_over,
    ← S.ideal_quotient_mk_zeta_p_int_eq h_over h_compat]
  exact h_cross_ring

end Furtwaengler

end BernoulliRegular

end
