module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.PrimeFamily
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleConstruction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup.Part1
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteDworkProduct
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.EisensteinReciprocityInteger
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois

/-!
# Ireland--Rosen Proposition 14.5.4 and Theorem 1

This file closes the remaining Ireland--Rosen source-construction gap for
the ideal-norm Proposition 14.5.4 and Theorem 1.  The proof route uses the
enlarged conductor-flexible local setup for each prime factor of `(α)`, not the
earlier pair-cyclotomic split/order-one route and not any stronger reciprocity
theorem.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace IrelandRosen

/-- The order of `ℓ` modulo `ℓ ^ f - 1` is exactly `f`.

This is the elementary arithmetic behind the Ireland--Rosen conductor choice
`ℓ · (#k - 1)`: adjoining roots of order `#k - 1 = ℓ ^ f - 1` makes the
upstairs absolute residue degree over `ℓ` equal to the downstairs residue
degree `f`. -/
theorem orderOf_natCast_zmod_pow_sub_one
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (hf : 0 < f) :
    orderOf (ℓ : ZMod (ℓ ^ f - 1)) = f := by
  have hℓ_one : 1 < ℓ := by omega
  have hpow_one : 1 < ℓ ^ f :=
    one_lt_pow' hℓ_one hf.ne'
  have hpow_f :
      (ℓ : ZMod (ℓ ^ f - 1)) ^ f = 1 := by
    rw [← Nat.cast_pow]
    have hmod : ℓ ^ f ≡ 1 [MOD ℓ ^ f - 1] := by
      rw [Nat.ModEq]
      nth_rewrite 1 [show ℓ ^ f = (ℓ ^ f - 1) + 1 by omega]
      simp
    simpa using
      ((ZMod.natCast_eq_natCast_iff (ℓ ^ f) 1 (ℓ ^ f - 1)).mpr hmod)
  rw [orderOf_eq_iff hf]
  refine ⟨hpow_f, ?_⟩
  intro r hr rpos hpow_r
  have hmod_r : ℓ ^ r ≡ 1 [MOD ℓ ^ f - 1] := by
    rw [← Nat.cast_pow] at hpow_r
    exact (ZMod.natCast_eq_natCast_iff (ℓ ^ r) 1 (ℓ ^ f - 1)).mp (by
      simpa using hpow_r)
  have hpow_r_one : 1 ≤ ℓ ^ r :=
    one_le_pow₀ (by omega : 1 ≤ ℓ)
  have hsub_mod : ℓ ^ r - 1 ≡ 0 [MOD ℓ ^ f - 1] := by
    simpa using
      (Nat.ModEq.sub hpow_r_one (le_refl 1) hmod_r (Nat.ModEq.rfl : 1 ≡ 1 [MOD ℓ ^ f - 1]))
  have hdiv : ℓ ^ f - 1 ∣ ℓ ^ r - 1 :=
    Nat.modEq_zero_iff_dvd.mp hsub_mod
  have hpow_lt : ℓ ^ r < ℓ ^ f :=
    pow_lt_pow_right₀ hℓ_one hr
  have hlt : ℓ ^ r - 1 < ℓ ^ f - 1 := by omega
  have hzero : ℓ ^ r - 1 = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdiv hlt
  have hpow_r_gt_one : 1 < ℓ ^ r :=
    one_lt_pow' hℓ_one rpos.ne'
  omega

/-- If a finite residue field has size `ℓ ^ f`, then its unit-group order
`ℓ ^ f - 1` is coprime to `ℓ`. -/
theorem prime_coprime_card_sub_one_of_card_eq_pow
    {ℓ q f : ℕ} (hℓ_prime : ℓ.Prime) (hf : 0 < f) (hq : q = ℓ ^ f) :
    ℓ.Coprime (q - 1) := by
  rw [hq]
  rw [← Nat.coprime_pow_left_iff hf]
  have hpow_one : 1 ≤ ℓ ^ f :=
    Nat.succ_le_of_lt (pow_pos hℓ_prime.pos f)
  exact (Nat.coprime_self_sub_right hpow_one).mpr (Nat.coprime_one_right _)

/-- Local uniformizer criterion from the actual ramification index.  This is
the conductor-flexible form of `pi_not_mem_Q_sq_of_ramification`: once the
chosen upstairs prime has absolute ramification index `ℓ - 1` over `(ℓ)`,
the standard cyclotomic identity `ℓ ~ (ζ_ℓ - 1)^(ℓ-1)` forces
`ζ_ℓ - 1 ∉ Q^2`. -/
theorem pi_not_mem_Q_sq_of_ramificationIdx_eq
    {ℓ : ℕ} [Fact ℓ.Prime]
    {R' : Type v} [Field R'] [NumberField R']
    (zeta_ell_int : 𝓞 R')
    (hzeta_int : IsPrimitiveRoot zeta_ell_int ℓ)
    (Q : Ideal (𝓞 R')) [Q.IsPrime] (hQ_ne : Q ≠ ⊥)
    (h_ram :
      Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) Q = ℓ - 1) :
    zeta_ell_int - 1 ∉ Q ^ 2 := by
  classical
  obtain ⟨u, hu⟩ := (associated_ell_zeta_sub_one_pow hzeta_int).symm
  intro h_in_Q_sq
  have h_pi_pow : (zeta_ell_int - 1) ^ (ℓ - 1) ∈ (Q ^ 2) ^ (ℓ - 1) :=
    Ideal.pow_mem_pow h_in_Q_sq (ℓ - 1)
  rw [← pow_mul] at h_pi_pow
  have h_ell_in : (ℓ : 𝓞 R') ∈ Q ^ (2 * (ℓ - 1)) := by
    rw [← hu]
    exact Ideal.mul_mem_right _ _ h_pi_pow
  have hℓ_ge_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_le : ℓ ≤ 2 * (ℓ - 1) := by omega
  have h_ell_in_Q_ell : (ℓ : 𝓞 R') ∈ Q ^ ℓ :=
    Ideal.pow_le_pow_right h_le h_ell_in
  have h_map_ne_bot :
      Ideal.map (algebraMap ℤ (𝓞 R')) (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, eq_intCast]
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero
  have h_ram_count :
      Ideal.ramificationIdx (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) Q =
        Multiset.count Q (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap ℤ (𝓞 R')) (Ideal.span ({(ℓ : ℤ)} : Set ℤ)))) :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      h_map_ne_bot (by infer_instance) hQ_ne
  rw [h_ram] at h_ram_count
  have h_map_eq :
      Ideal.map (algebraMap ℤ (𝓞 R')) (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) =
        Ideal.span ({(ℓ : 𝓞 R')} : Set (𝓞 R')) := by
    rw [Ideal.map_span]
    simp
  rw [h_map_eq] at h_ram_count
  have h_span_le : Ideal.span ({(ℓ : 𝓞 R')} : Set (𝓞 R')) ≤ Q ^ ℓ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact h_ell_in_Q_ell
  have h_span_ne_bot : Ideal.span ({(ℓ : 𝓞 R')} : Set (𝓞 R')) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero
  have hcount := Ideal.count_le_of_ideal_ge h_span_le h_span_ne_bot Q
  have hQ_irr : Irreducible Q :=
    (Ideal.prime_of_isPrime hQ_ne (by infer_instance)).irreducible
  have h_count_Qpow : ℓ ≤ Multiset.count Q
      (UniqueFactorizationMonoid.normalizedFactors (Q ^ ℓ)) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
    have h1 : 1 ≤ Multiset.count Q
        (UniqueFactorizationMonoid.normalizedFactors Q) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
        normalize_eq, Multiset.count_singleton_self]
    nlinarith
  rw [← h_ram_count] at hcount
  omega

end IrelandRosen

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

/-- Flexible constructor from the non-`psi` data, using the canonical
trace-form additive character.  This is the conductor-flexible analogue of
`ConcreteStickelbergerSetup.mkFromTrace`. -/
noncomputable def mkFromTrace
    (hℓ_ne_p : ℓ ≠ p)
    (f : ℕ) (card_k : Fintype.card k = ℓ ^ f)
    (zeta_k : kˣ) (hzeta_k : IsPrimitiveRoot zeta_k p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_p : R'ˣ) (hzeta_p : IsPrimitiveRoot zeta_p p)
    (zeta_p_int : 𝓞 R')
    (zeta_p_int_spec : algebraMap (𝓞 R') R' zeta_p_int = (zeta_p : R'ˣ))
    (zeta_ell : R') (hzeta_ell : IsPrimitiveRoot zeta_ell ℓ)
    (zeta_ell_int : 𝓞 R')
    (zeta_ell_int_spec : algebraMap (𝓞 R') R' zeta_ell_int = zeta_ell)
    (π : 𝓞 R') (hπ : π = zeta_ell_int - 1)
    (Q : Ideal (𝓞 R')) (hQ_prime : Q.IsPrime) (hQ : (ℓ : 𝓞 R') ∈ Q)
    (residueMap : 𝓞 R' →+* k)
    (residueMap_surjective : Function.Surjective residueMap)
    (residueMap_ker : RingHom.ker residueMap = Q)
    (zeta_p_int_residue : residueMap zeta_p_int = (zeta_k : k))
    (h_ringChar : ringChar k = ℓ) :
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  hℓ_ne_p := hℓ_ne_p
  f := f
  card_k := card_k
  zeta_k := zeta_k
  hzeta_k := hzeta_k
  hdiv := hdiv
  zeta_p := zeta_p
  hzeta_p := hzeta_p
  zeta_p_int := zeta_p_int
  zeta_p_int_spec := zeta_p_int_spec
  zeta_ell := zeta_ell
  hzeta_ell := hzeta_ell
  zeta_ell_int := zeta_ell_int
  zeta_ell_int_spec := zeta_ell_int_spec
  π := π
  hπ := hπ
  Q := Q
  hQ_prime := hQ_prime
  hQ := hQ
  residueMap := residueMap
  residueMap_surjective := residueMap_surjective
  residueMap_ker := residueMap_ker
  zeta_p_int_residue := zeta_p_int_residue
  psi := BundleConstruction.psiTraceForm ℓ k R' hzeta_ell
  hpsi := BundleConstruction.psiTraceForm_isPrimitive ℓ k R' hzeta_ell h_ringChar
  psiExponent := BundleConstruction.psiTraceFormExponent ℓ k
  psi_eq_zeta_ell_pow :=
    BundleConstruction.psiTraceForm_eq_zeta_ell_pow ℓ k R' hzeta_ell

omit [Algebra (ZMod ℓ) k] in
/-- Unit-valued form of the integral residue character, for the
conductor-flexible concrete setup. -/
noncomputable def residueCharIntUnitHom
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') :
    kˣ →* (𝓞 R')ˣ :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueUnitHom S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

omit [Algebra (ZMod ℓ) k] in
@[simp]
theorem residueCharInt_apply_unit
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (x : kˣ) :
    S.residueCharInt (x : k) = (S.residueCharIntUnitHom x : 𝓞 R') := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  simp [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt,
    residueCharIntUnitHom, residueMulChar]

omit [Algebra (ZMod ℓ) k] in
/-- The unit-valued integral residue character has exponent dividing `p`. -/
theorem residueCharIntUnitHom_pow_p
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (x : kˣ) :
    S.residueCharIntUnitHom x ^ p = 1 := by
  apply Units.ext
  change ((S.residueCharIntUnitHom x : (𝓞 R')ˣ) : 𝓞 R') ^ p = (1 : 𝓞 R')
  rw [← S.residueCharInt_apply_unit x]
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  unfold ConductorFlexibleConcreteStickelbergerSetup.residueCharInt
  exact residueMulChar_pow_eq_one S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot x

omit [Algebra (ZMod ℓ) k] in
/-- Modulo `Q`, the integral residue character is the order-`p`
Teichmüller projection `x ↦ x^((#k - 1) / p)` on residue-field units. -/
theorem residueCharInt_residueMap_eq_pow_d
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R') (x : kˣ) :
    S.residueMap (S.residueCharInt (x : k)) =
      (x : k) ^ ((Fintype.card k - 1) / p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [ConductorFlexibleConcreteStickelbergerSetup.residueCharInt,
    residueMulChar_apply_unit, map_pow, S.residueMap_zeta_p_int_unit]
  have h := congrArg (fun u : kˣ => (u : k))
    (Reflection.ResidueSymbol.PowerResidue.zeta_pow_finiteFieldExponent_val
      S.hzeta_k S.hdiv x)
  simpa [Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit] using h

omit [Algebra (ZMod ℓ) k] in
/-- Unit-group residue equivalence on underlying values. -/
theorem residueUnitEquiv_val
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')
    (u : (𝓞 R' ⧸ S.Q)ˣ) :
    ((S.residueUnitEquiv u : kˣ) : k) =
      S.residueQuotientEquiv (u : 𝓞 R' ⧸ S.Q) := by
  simp [ConductorFlexibleConcreteStickelbergerSetup.residueUnitEquiv]

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- Flexible residue-character compatibility in residue-map form. -/
theorem residueCharInt_residueMap_eq_pow_d (x : kˣ) :
    S.residueMap (S.residueCharInt (x : k)) =
      (x : k) ^ ((Fintype.card k - 1) / p) :=
  S.concrete.residueCharInt_residueMap_eq_pow_d x

/-- The roots-of-unity reduction map as a multiplicative equivalence, once
bijectivity has been proved for the selected prime. -/
noncomputable def rootsOfUnityReductionEquiv
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))) :
    rootsOfUnity (Fintype.card k - 1) (𝓞 R') ≃*
      (𝓞 R' ⧸ S.Q)ˣ :=
  MulEquiv.ofBijective
    (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)) hbij

/-- Teichmüller section obtained by inverting the roots-of-unity reduction
map. -/
noncomputable def teichUnitFullOfRootsOfUnityBijective
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))) :
    kˣ →* (𝓞 R')ˣ :=
  (rootsOfUnity (Fintype.card k - 1) (𝓞 R')).subtype.comp
    ((S.rootsOfUnityReductionEquiv hbij).symm.toMonoidHom.comp
      S.concrete.residueUnitEquiv.symm.toMonoidHom)

/-- The Teichmüller section constructed from a bijective roots-of-unity
reduction map reduces to the original residue-field unit. -/
theorem teichUnitFullOfRootsOfUnityBijective_residue
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)))
    (x : kˣ) :
    S.residueMap (S.teichUnitFullOfRootsOfUnityBijective hbij x : 𝓞 R') =
      (x : k) := by
  classical
  let e := S.rootsOfUnityReductionEquiv hbij
  let xQ : (𝓞 R' ⧸ S.Q)ˣ := S.residueUnitEquiv.symm x
  let t : rootsOfUnity (Fintype.card k - 1) (𝓞 R') := e.symm xQ
  have ht : e t = xQ := e.apply_symm_apply xQ
  have ht_val :
      (Ideal.Quotient.mk S.Q ((t : (𝓞 R')ˣ) : 𝓞 R') : 𝓞 R' ⧸ S.Q) =
        (xQ : 𝓞 R' ⧸ S.Q) := by
    have h :=
      congrArg (fun u : (𝓞 R' ⧸ S.Q)ˣ => (u : 𝓞 R' ⧸ S.Q)) ht
    simp only [e, rootsOfUnityReductionEquiv, MulEquiv.ofBijective_apply] at h
    exact h
  have hxQ :
      S.residueQuotientEquiv (xQ : 𝓞 R' ⧸ S.Q) = (x : k) := by
    rw [← ConductorFlexibleConcreteStickelbergerSetup.residueUnitEquiv_val
      (S := S.toConductorFlexibleConcreteStickelbergerSetup) xQ]
    dsimp [xQ]
    exact congrArg (fun u : kˣ => (u : k))
      (S.residueUnitEquiv.apply_symm_apply x)
  rw [← ConductorFlexibleConcreteStickelbergerSetup.residueQuotientEquiv_mk
    (S := S.toConductorFlexibleConcreteStickelbergerSetup)]
  change
    S.residueQuotientEquiv
        (Ideal.Quotient.mk S.Q ((t : (𝓞 R')ˣ) : 𝓞 R')) =
      (x : k)
  rw [ht_val, hxQ]

/-- The same Teichmüller section satisfies the power convention used by
`ConductorFlexibleFullTeichStickelbergerSetup`. -/
theorem residueCharInt_eq_teichUnitFullOfRootsOfUnityBijective_pow_d
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)))
    (x : kˣ) :
    S.residueCharInt (x : k) =
      ((S.teichUnitFullOfRootsOfUnityBijective hbij x : 𝓞 R') ^
        ((Fintype.card k - 1) / p) : 𝓞 R') := by
  classical
  let n := Fintype.card k - 1
  let d := (Fintype.card k - 1) / p
  let e := S.rootsOfUnityReductionEquiv hbij
  let xQ : (𝓞 R' ⧸ S.Q)ˣ := S.residueUnitEquiv.symm x
  let t : rootsOfUnity n (𝓞 R') := e.symm xQ
  have ht_map : e t = xQ := e.apply_symm_apply xQ
  have ht_val :
      (Ideal.Quotient.mk S.Q ((t : (𝓞 R')ˣ) : 𝓞 R') : 𝓞 R' ⧸ S.Q) =
        (xQ : 𝓞 R' ⧸ S.Q) := by
    have h :=
      congrArg (fun u : (𝓞 R' ⧸ S.Q)ˣ => (u : 𝓞 R' ⧸ S.Q)) ht_map
    simp only [e, n, rootsOfUnityReductionEquiv, MulEquiv.ofBijective_apply] at h
    exact h
  have ht_residue :
      S.residueMap ((t : (𝓞 R')ˣ) : 𝓞 R') = (x : k) := by
    have hxQ :
        S.residueQuotientEquiv (xQ : 𝓞 R' ⧸ S.Q) = (x : k) := by
      rw [← ConductorFlexibleConcreteStickelbergerSetup.residueUnitEquiv_val
        (S := S.toConductorFlexibleConcreteStickelbergerSetup) xQ]
      dsimp [xQ]
      exact congrArg (fun u : kˣ => (u : k))
        (S.residueUnitEquiv.apply_symm_apply x)
    have h := congrArg S.residueQuotientEquiv ht_val
    simpa [ConductorFlexibleConcreteStickelbergerSetup.residueQuotientEquiv_mk,
      hxQ] using h
  have hχ_n :
      (S.residueCharIntUnitHom x) ^ n = 1 := by
    obtain ⟨m, hm⟩ := S.hdiv
    change (S.residueCharIntUnitHom x) ^ (Fintype.card k - 1) = 1
    rw [hm, pow_mul, S.residueCharIntUnitHom_pow_p x, one_pow]
  let χroot : rootsOfUnity n (𝓞 R') := ⟨S.residueCharIntUnitHom x, hχ_n⟩
  let τroot : rootsOfUnity n (𝓞 R') := t ^ d
  have hχ_residue :
      S.residueMap ((χroot : (𝓞 R')ˣ) : 𝓞 R') = (x : k) ^ d := by
    change S.residueMap (S.residueCharIntUnitHom x : 𝓞 R') =
      (x : k) ^ ((Fintype.card k - 1) / p)
    rw [← S.residueCharInt_apply_unit x]
    exact S.residueCharInt_residueMap_eq_pow_d x
  have hτ_residue :
      S.residueMap ((τroot : (𝓞 R')ˣ) : 𝓞 R') = (x : k) ^ d := by
    change S.residueMap (((t : (𝓞 R')ˣ) ^ d : (𝓞 R')ˣ) : 𝓞 R') =
      (x : k) ^ d
    rw [Units.val_pow_eq_pow_val, map_pow, ht_residue]
  have hquot :
      (Ideal.rootsOfUnityMapQuot S.Q n χroot : 𝓞 R' ⧸ S.Q) =
        (Ideal.rootsOfUnityMapQuot S.Q n τroot : 𝓞 R' ⧸ S.Q) := by
    apply S.residueQuotientEquiv.injective
    rw [Ideal.rootsOfUnityMapQuot_apply, Ideal.rootsOfUnityMapQuot_apply,
      ConductorFlexibleConcreteStickelbergerSetup.residueQuotientEquiv_mk,
      ConductorFlexibleConcreteStickelbergerSetup.residueQuotientEquiv_mk,
      hχ_residue, hτ_residue]
  have hmap :
      Ideal.rootsOfUnityMapQuot S.Q n χroot =
        Ideal.rootsOfUnityMapQuot S.Q n τroot := by
    ext
    exact hquot
  have hroot : χroot = τroot := hbij.1 hmap
  have hunit :
      S.residueCharIntUnitHom x = (t : (𝓞 R')ˣ) ^ d := by
    simpa [χroot, τroot] using
      congrArg (fun y : rootsOfUnity n (𝓞 R') => (y : (𝓞 R')ˣ)) hroot
  change S.residueCharInt (x : k) =
    (((S.teichUnitFullOfRootsOfUnityBijective hbij x : (𝓞 R')ˣ) : 𝓞 R') ^ d)
  rw [S.residueCharInt_apply_unit x]
  rw [← Units.val_pow_eq_pow_val, hunit]
  rfl

/-- The quotient unit group has cardinality `#k - 1`. -/
theorem natCard_quotientUnits_eq_card_sub_one :
    Nat.card (𝓞 R' ⧸ S.Q)ˣ = Fintype.card k - 1 := by
  classical
  letI : DecidableEq k := Classical.decEq k
  letI : Fintype (𝓞 R' ⧸ S.Q)ˣ :=
    Fintype.ofEquiv kˣ
      ((S.residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ).symm.toEquiv)
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr
    ((S.residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ).toEquiv)).trans
    (Fintype.card_units (α := k))

/-- The absolute norm of the chosen prime is the cardinality of the selected
residue field. -/
theorem absNorm_Q_eq_card_k :
    Ideal.absNorm S.Q = Fintype.card k := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr S.residueQuotientEquiv.toEquiv).trans
    (Nat.card_eq_fintype_card (α := k))

/-- The selected prime has nontrivial absolute norm. -/
theorem absNorm_Q_ne_one :
    Ideal.absNorm S.Q ≠ 1 := by
  rw [S.absNorm_Q_eq_card_k]
  have h_card : 2 ≤ Fintype.card k := Fintype.one_lt_card
  omega

/-- The selected prime norm is coprime to the order of the residue-field unit
group. -/
theorem absNorm_Q_coprime_card_sub_one :
    (Ideal.absNorm S.Q).Coprime (Fintype.card k - 1) := by
  rw [S.absNorm_Q_eq_card_k]
  have h_card_pos : 1 ≤ Fintype.card k := Fintype.card_pos
  exact (Nat.coprime_self_sub_right h_card_pos).mpr (Nat.coprime_one_right _)

/-- A primitive `(q - 1)`-st root of unity gives bijectivity of the
roots-of-unity reduction map. -/
theorem rootsOfUnityMapQuot_bijective_of_isPrimitiveRoot
    {ζ : 𝓞 R'} (hζ : IsPrimitiveRoot ζ (Fintype.card k - 1)) :
    Function.Bijective
      (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)) := by
  have hn_ne : Fintype.card k - 1 ≠ 0 := by
    have h_card : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  letI : NeZero (Fintype.card k - 1) := ⟨hn_ne⟩
  letI : Fintype (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) :=
    inferInstance
  have hroots' :
      Fintype.card (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) =
        Fintype.card k - 1 := hζ.card_rootsOfUnity
  letI : DecidableEq k := Classical.decEq k
  letI : Fintype (𝓞 R' ⧸ S.Q)ˣ :=
    Fintype.ofEquiv kˣ
      ((S.concrete.residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ).symm.toEquiv)
  have hquot' :
      Fintype.card (𝓞 R' ⧸ S.Q)ˣ = Fintype.card k - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.natCard_quotientUnits_eq_card_sub_one
  refine (Fintype.bijective_iff_injective_and_card
    (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))).mpr ?_
  exact ⟨Ideal.rootsOfUnityMapQuot_injective (I := S.Q)
      (K := R') (Fintype.card k - 1) S.absNorm_Q_ne_one
      S.absNorm_Q_coprime_card_sub_one,
    hroots'.trans hquot'.symm⟩

/-- Construct a conductor-flexible full-Teich setup from bijectivity of the
roots-of-unity reduction map. -/
noncomputable def mkFullTeich_of_rootsOfUnityMap_bijective
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))) :
    ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R' where
  toConductorFlexibleTraceFormStickelbergerSetup := S
  teichUnitFull := S.teichUnitFullOfRootsOfUnityBijective hbij
  teichUnitFull_residue :=
    S.teichUnitFullOfRootsOfUnityBijective_residue hbij
  residueCharInt_eq_teichUnitFull_pow_d :=
    S.residueCharInt_eq_teichUnitFullOfRootsOfUnityBijective_pow_d hbij

/-- Construct a conductor-flexible full-Teich setup from a primitive
`(#k - 1)`-st root of unity. -/
noncomputable def mkFullTeich_of_isPrimitiveRoot
    {ζ : 𝓞 R'} (hζ : IsPrimitiveRoot ζ (Fintype.card k - 1)) :
    ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R' :=
  S.mkFullTeich_of_rootsOfUnityMap_bijective
    (S.rootsOfUnityMapQuot_bijective_of_isPrimitiveRoot hζ)

end ConductorFlexibleTraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
