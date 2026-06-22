module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitVectors
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Full-Teichmüller Stickelberger setup (REF-18c2c4-L2c3d-0)

The route-D proof of the digit-sum Stickelberger congruence requires a
multiplicative section
`teichUnitFull : kˣ →* (𝓞 R')ˣ` whose values reduce modulo `Q` to the
identity on `kˣ`. Such a section has order exactly `q − 1` (with
`q = #k`), and exists in the integral closure as soon as `R'` contains
primitive `(q − 1)`-th roots of unity.

The base `TraceFormStickelbergerSetup` only requires
`[IsCyclotomicExtension {p, ℓ} ℚ R']`, which gives `lcm(p, ℓ)`-th roots
only — generally insufficient. The reviewer's recommended fix is an
extension layer that takes the order-`(q−1)` Teichmüller as an explicit
bundle hypothesis. Concrete instances are constructed over the auxiliary
field `R' = ℚ(ζ_{ℓ(q−1)})` (which contains both `ζ_p` and `ζ_{q−1}`,
since `p ∣ q−1`).

## Main definition

* `FullTeichStickelbergerSetup`: extends `TraceFormStickelbergerSetup`
  with `teichUnitFull` plus the residue compatibility identity and the
  bridge to `residueCharInt`.

## Downstream usage

The Wave-2 Stickelberger lemmas
(`teichUnitFull_sum_pow_units`,
`residueCharInt_rec_eq_teichUnitFull_pow`,
`digit_expansion_inner_sum_eval`,
`leadingCoeff_not_mem_Q`)
are stated against this richer setup; the existing arithmetic /
digit-vector layer (Wave-1) remains stated against the base
`TraceFormStickelbergerSetup` and is reused unchanged through the
inheritance. The actual digit-sum Stickelberger statements
(`gaussSumIntRec_mem_Q_pow_stickOrd_dwork`,
`gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork`, and assemblies)
live on the further refinement `FullTeichDworkSetup` in
`DworkAssembly.lean`, which carries the Dwork splitting expansion that
correctly replaces the originally-planned (false) denominator-cleared
digit-bounded expansion.

## Constructibility note

A concrete `FullTeichStickelbergerSetup` is **not** constructed in this
file. The instance over `R' = ℚ(ζ_{ℓ(q−1)})` (with the canonical
Teichmüller given by Hensel-lifted `(q−1)`-th roots) is tracked
separately. The uniformizer fact `pi_not_mem_Q_sq` is inherited from
the base setup and remains valid at the enlarged conductor `ℓ(q−1)`
because the ramification index at `ℓ` is still `ℓ − 1`
(`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ^1·(q−1)`,
`ℓ ∤ (q−1)`).
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Full-Teichmüller refinement of `TraceFormStickelbergerSetup`. Adds
an order-`(q − 1)` multiplicative section `teichUnitFull : kˣ →* (𝓞 R')ˣ`
of the residue map, together with the bridge identity
`residueCharInt(x) = teichUnitFull(x)^d` where `d = (q − 1)/p`.

A concrete instance requires `R'` to contain primitive `(q − 1)`-th
roots of unity (e.g., as supplied by
`[IsCyclotomicExtension {ℓ * (#k − 1)} ℚ R']`). At the structure level,
this is encoded as a hypothesis (`teichUnitFull` is supplied by the
user). -/
structure FullTeichStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] extends
    TraceFormStickelbergerSetup ℓ p k K R' where
  /-- Multiplicative section `kˣ →* (𝓞 R')ˣ` of the residue map. Its
  values reduce modulo `Q` to the identity on `kˣ` and have order
  dividing `q − 1` (= `#k − 1`). -/
  teichUnitFull : kˣ →* (𝓞 R')ˣ
  /-- Residue compatibility: `teichUnitFull` is a section of the
  composed map `(𝓞 R')ˣ →* (𝓞 R'/Q)ˣ ≃* kˣ`. -/
  teichUnitFull_residue :
    ∀ x : kˣ,
      toConcreteStickelbergerSetup.residueQuotientEquiv
          (Ideal.Quotient.mk toConcreteStickelbergerSetup.Q
            (teichUnitFull x : 𝓞 R')) =
        (x : k)
  /-- The integral residue character is the `d`-th power of the full
  Teichmüller, where `d = (#k − 1) / p`. -/
  residueCharInt_eq_teichUnitFull_pow_d :
    ∀ x : kˣ,
      toConcreteStickelbergerSetup.residueCharInt (x : k) =
        ((teichUnitFull x : 𝓞 R') ^ ((Fintype.card k - 1) / p) : 𝓞 R')

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

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
map. This is the constructive core of the full Teichmüller input: the
remaining arithmetic work is proving that the reduction map is bijective in
the chosen cyclotomic extension. -/
noncomputable def teichUnitFullOfRootsOfUnityBijective
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))) :
    kˣ →* (𝓞 R')ˣ :=
  (rootsOfUnity (Fintype.card k - 1) (𝓞 R')).subtype.comp
    ((S.rootsOfUnityReductionEquiv hbij).symm.toMonoidHom.comp
      S.residueUnitEquiv.symm.toMonoidHom)

/-- The Teichmüller section constructed from a bijective roots-of-unity
reduction map really reduces to the original residue-field unit. -/
theorem teichUnitFullOfRootsOfUnityBijective_residue
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)))
    (x : kˣ) :
    S.residueQuotientEquiv
        (Ideal.Quotient.mk S.Q
          (S.teichUnitFullOfRootsOfUnityBijective hbij x : 𝓞 R')) =
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
    exact h
  have hxQ :
      S.residueQuotientEquiv (xQ : 𝓞 R' ⧸ S.Q) = (x : k) := by
    rw [← ConcreteStickelbergerSetup.residueUnitEquiv_val
      (S := S.toConcreteStickelbergerSetup) xQ]
    dsimp [xQ]
    exact congrArg (fun u : kˣ => (u : k)) (S.residueUnitEquiv.apply_symm_apply x)
  change
    S.residueQuotientEquiv
        (Ideal.Quotient.mk S.Q ((t : (𝓞 R')ˣ) : 𝓞 R')) =
      (x : k)
  rw [ht_val, hxQ]

/-- The same Teichmüller section also satisfies the power convention used by
`FullTeichStickelbergerSetup`: the integral residue character is its
`(#k - 1) / p` power. -/
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
    exact h
  have ht_residue :
      S.residueMap ((t : (𝓞 R')ˣ) : 𝓞 R') = (x : k) := by
    have hxQ :
        S.residueQuotientEquiv (xQ : 𝓞 R' ⧸ S.Q) = (x : k) := by
      rw [← ConcreteStickelbergerSetup.residueUnitEquiv_val
        (S := S.toConcreteStickelbergerSetup) xQ]
      dsimp [xQ]
      exact congrArg (fun u : kˣ => (u : k)) (S.residueUnitEquiv.apply_symm_apply x)
    have h := congrArg S.residueQuotientEquiv ht_val
    simpa [ConcreteStickelbergerSetup.residueQuotientEquiv_mk, hxQ] using h
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
      ConcreteStickelbergerSetup.residueQuotientEquiv_mk,
      ConcreteStickelbergerSetup.residueQuotientEquiv_mk,
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
  rw [S.residueCharInt_apply_unit x]
  change ((S.residueCharIntUnitHom x : (𝓞 R')ˣ) : 𝓞 R') =
    (((S.teichUnitFullOfRootsOfUnityBijective hbij x : (𝓞 R')ˣ) : 𝓞 R') ^ d)
  rw [← Units.val_pow_eq_pow_val, hunit]
  rfl

/-- The quotient unit group has the same cardinality as the chosen finite-field
unit group, hence `#k - 1`. This is stated with `Nat.card` so callers do not
need a global `Fintype` instance for the quotient unit group. -/
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

/-- If the reduction map on `(q - 1)`-st roots of unity is injective and the
source has the expected cardinality `q - 1`, then the map is bijective. The
injectivity hypotheses are exactly mathlib's `rootsOfUnityMapQuot_injective`
inputs. -/
theorem rootsOfUnityMapQuot_bijective_of_card_roots
    (hQnorm : Ideal.absNorm S.Q ≠ 1)
    (hcop : (Ideal.absNorm S.Q).Coprime (Fintype.card k - 1))
    (hroots :
      Nat.card (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) =
        Fintype.card k - 1) :
    Function.Bijective
      (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1)) := by
  have hn_ne : Fintype.card k - 1 ≠ 0 := by
    have h_card : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  letI : NeZero (Fintype.card k - 1) := ⟨hn_ne⟩
  letI : DecidableEq k := Classical.decEq k
  letI : Fintype (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) :=
    inferInstance
  letI : Fintype (𝓞 R' ⧸ S.Q)ˣ :=
    Fintype.ofEquiv kˣ
      ((S.residueUnitEquiv : (𝓞 R' ⧸ S.Q)ˣ ≃* kˣ).symm.toEquiv)
  have hroots' :
      Fintype.card (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) =
        Fintype.card k - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hroots
  have hquot' :
      Fintype.card (𝓞 R' ⧸ S.Q)ˣ = Fintype.card k - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.natCard_quotientUnits_eq_card_sub_one
  refine (Fintype.bijective_iff_injective_and_card
    (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))).mpr ?_
  exact ⟨Ideal.rootsOfUnityMapQuot_injective (I := S.Q)
      (K := R') (Fintype.card k - 1) hQnorm hcop,
    hroots'.trans hquot'.symm⟩

/-- A primitive `(q - 1)`-st root of unity in `𝓞 R'` supplies the cardinality
input needed for bijectivity of the reduction map. The norm and coprimality
inputs for injectivity are derived from the residue quotient equivalence. -/
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
  have hroots :
      Nat.card (rootsOfUnity (Fintype.card k - 1) (𝓞 R')) =
        Fintype.card k - 1 := by
    rw [Nat.card_eq_fintype_card]
    exact hζ.card_rootsOfUnity
  exact S.rootsOfUnityMapQuot_bijective_of_card_roots
    S.absNorm_Q_ne_one S.absNorm_Q_coprime_card_sub_one hroots

/-- Construct a `FullTeichStickelbergerSetup` from bijectivity of the
roots-of-unity reduction map. -/
noncomputable def mkFullTeich_of_rootsOfUnityMap_bijective
    (hbij :
      Function.Bijective
        (Ideal.rootsOfUnityMapQuot S.Q (Fintype.card k - 1))) :
    FullTeichStickelbergerSetup ℓ p k K R' where
  toTraceFormStickelbergerSetup := S
  teichUnitFull := S.teichUnitFullOfRootsOfUnityBijective hbij
  teichUnitFull_residue :=
    S.teichUnitFullOfRootsOfUnityBijective_residue hbij
  residueCharInt_eq_teichUnitFull_pow_d :=
    S.residueCharInt_eq_teichUnitFullOfRootsOfUnityBijective_pow_d hbij

/-- Construct a `FullTeichStickelbergerSetup` from a primitive `(q - 1)`-st
root of unity. -/
noncomputable def mkFullTeich_of_isPrimitiveRoot
    {ζ : 𝓞 R'} (hζ : IsPrimitiveRoot ζ (Fintype.card k - 1)) :
    FullTeichStickelbergerSetup ℓ p k K R' :=
  S.mkFullTeich_of_rootsOfUnityMap_bijective
    (S.rootsOfUnityMapQuot_bijective_of_isPrimitiveRoot hζ)

/-- If the selected upstairs field is also cyclotomic of conductor `#k - 1`,
then it contains an integral primitive `(q - 1)`-st root of unity. -/
theorem exists_integer_isPrimitiveRoot_cardSubOne
    [IsCyclotomicExtension {Fintype.card k - 1} ℚ R'] :
    ∃ ζ : 𝓞 R', IsPrimitiveRoot ζ (Fintype.card k - 1) := by
  have hn_ne : Fintype.card k - 1 ≠ 0 := by
    have h_card : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  letI : NeZero (Fintype.card k - 1) := ⟨hn_ne⟩
  exact ⟨(IsCyclotomicExtension.zeta_spec (Fintype.card k - 1) ℚ R').toInteger,
    (IsCyclotomicExtension.zeta_spec
      (Fintype.card k - 1) ℚ R').toInteger_isPrimitiveRoot⟩

/-- **Integral primitive `m`-th root from a richer cyclotomic typeclass.**

If `R'` is a cyclotomic extension of `ℚ` of conductor `N`, and `m ∣ N` with
`m ≠ 0`, then `𝓞 R'` contains an integral primitive `m`-th root of unity:
specifically, `ζ_N^(N / m)` where `ζ_N` is the canonical primitive `N`-th
root.

This is the structural building block for REF-18tf3a2: the user enlarges
the upstairs field to a single cyclotomic of conductor `N` divisible by
all needed `(#k_P - 1)` values, and then uses this lemma to produce the
primitive `(#k_P - 1)`-st root in `𝓞 R'` for each source factor `P`. -/
theorem exists_integer_isPrimitiveRoot_dvd_of_isCyclotomicExtension
    {N m : ℕ} [hN : NeZero N] (hm : m ≠ 0) (hd : m ∣ N)
    {R' : Type*} [Field R'] [NumberField R'] [Algebra ℚ R']
    [IsCyclotomicExtension {N} ℚ R'] :
    ∃ ζ : 𝓞 R', IsPrimitiveRoot ζ m := by
  have hN_ne : N ≠ 0 := hN.out
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_ne
  let ζ : 𝓞 R' := (IsCyclotomicExtension.zeta_spec N ℚ R').toInteger
  have hζ : IsPrimitiveRoot ζ N :=
    (IsCyclotomicExtension.zeta_spec N ℚ R').toInteger_isPrimitiveRoot
  refine ⟨ζ ^ (N / m), ?_⟩
  have hd_div : N / m ∣ N := Nat.div_dvd_of_dvd hd
  have hd_div_ne : N / m ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hm, Nat.le_of_dvd hN_pos hd⟩
  have h := hζ.pow_of_dvd hd_div_ne hd_div
  rwa [Nat.div_div_self hd hN_ne] at h

/-- Construct a `FullTeichStickelbergerSetup` when the selected upstairs field
is cyclotomic of conductor `#k - 1`, so that the required Teichmüller root can
be chosen from the cyclotomic API. -/
noncomputable def mkFullTeich_of_cardSubOneCyclotomic
    [IsCyclotomicExtension {Fintype.card k - 1} ℚ R'] :
    FullTeichStickelbergerSetup ℓ p k K R' :=
  S.mkFullTeich_of_isPrimitiveRoot
    ((exists_integer_isPrimitiveRoot_cardSubOne
      (k := k) (R' := R')).choose_spec)

omit [Algebra (ZMod ℓ) k] in
/-- Obstruction for the current exact pair-cyclotomic source field: if
`R' = ℚ(ζ_p, ζ_ℓ)` contains the primitive root needed for a full Teichmüller
section, then `#k - 1` must divide `2 * p * ℓ`. For general source residue
fields this divisibility is not available, which is why the remaining source
field work has to enlarge or generalize the upstairs cyclotomic layer. -/
theorem cardSubOne_dvd_two_mul_pair_of_isPrimitiveRoot
    (hpℓ : p ≠ ℓ) {ζ : 𝓞 R'}
    (hζ : IsPrimitiveRoot ζ (Fintype.card k - 1)) :
    Fintype.card k - 1 ∣ 2 * (p * ℓ) := by
  haveI : IsCyclotomicExtension {p * ℓ} ℚ R' :=
    isCyclotomicExtension_singleton_mul_of_pair (p := p) (ℓ := ℓ) hpℓ
  have hn_ne : Fintype.card k - 1 ≠ 0 := by
    have h_card : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  have hζ_field :
      IsPrimitiveRoot (algebraMap (𝓞 R') R' ζ) (Fintype.card k - 1) :=
    hζ.map_of_injective (NumberField.RingOfIntegers.coe_injective (K := R'))
  simpa [mul_assoc] using
    hζ_field.dvd_of_isCyclotomicExtension (p * ℓ) hn_ne

end TraceFormStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichStickelbergerSetup ℓ p k K R')

/-- The underlying integral element of a Teichmüller value. -/
def teichUnitFullVal (x : kˣ) : 𝓞 R' := (S.teichUnitFull x : 𝓞 R')

/-- Multiplicativity of the integral Teichmüller value. -/
@[simp]
theorem teichUnitFullVal_mul (x y : kˣ) :
    S.teichUnitFullVal (x * y) =
      S.teichUnitFullVal x * S.teichUnitFullVal y := by
  unfold teichUnitFullVal
  rw [map_mul]
  rfl

/-- The Teichmüller value at `1` is `1`. -/
@[simp]
theorem teichUnitFullVal_one : S.teichUnitFullVal 1 = 1 := by
  unfold teichUnitFullVal
  rw [map_one]
  rfl

/-- Compatibility of the integral Teichmüller value with powers in `kˣ`. -/
@[simp]
theorem teichUnitFullVal_pow (x : kˣ) (n : ℕ) :
    S.teichUnitFullVal (x ^ n) = S.teichUnitFullVal x ^ n := by
  unfold teichUnitFullVal
  rw [map_pow]
  rfl

/-- The integral Teichmüller value is a unit in `𝓞 R'`, hence not in
the prime ideal `Q`. -/
theorem teichUnitFullVal_not_mem_Q (x : kˣ) :
    S.teichUnitFullVal x ∉ S.Q := by
  classical
  intro hmem
  -- (teichUnitFull x : 𝓞 R')ˣ has an inverse, so its underlying value
  -- is a unit; units of 𝓞 R' aren't in any proper prime ideal.
  have hunit : IsUnit (S.teichUnitFullVal x) := ⟨S.teichUnitFull x, rfl⟩
  have hQ_prime : S.Q.IsPrime := inferInstance
  exact hQ_prime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- The Teichmüller residue identity in residue-map form: applying
`residueMap` to `teichUnitFullVal x` yields `x` (as an element of `k`). -/
theorem residueMap_teichUnitFullVal (x : kˣ) :
    S.residueMap (S.teichUnitFullVal x) = (x : k) := by
  unfold teichUnitFullVal
  -- residueMap factors as `Quotient.mk` then `residueQuotientEquiv`.
  have h := S.teichUnitFull_residue x
  rw [← S.toConcreteStickelbergerSetup.residueQuotientEquiv_mk]
  exact h

/-- Residue compatibility for Frobenius powers of Teichmüller values. -/
theorem residueMap_teichUnitFullVal_pow (x : kˣ) (n : ℕ) :
    S.residueMap (S.teichUnitFullVal x ^ n) = (x : k) ^ n := by
  rw [map_pow, S.residueMap_teichUnitFullVal]

section TeichOrthogonality

variable [DecidableEq k]

omit [DecidableEq k] in
/-- The integral Teichmüller value has order dividing `q - 1` (= `#k - 1`).
This follows from `teichUnitFull` being a `MonoidHom` from `kˣ` and
`x^(#kˣ) = 1`. -/
theorem teichUnitFullVal_pow_card_sub_one (x : kˣ) :
    S.teichUnitFullVal x ^ (Fintype.card k - 1) = 1 := by
  haveI : DecidableEq k := Classical.decEq _
  unfold teichUnitFullVal
  -- Reduce via Units.val_pow and map_pow.
  rw [show (Fintype.card k - 1) = Fintype.card kˣ from
    (Fintype.card_units (α := k)).symm]
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one]
  rfl

omit [DecidableEq k] in
/-- A full Teichmüller section forces an integral primitive
`(#k - 1)`-st root of unity upstairs.

This is the converse obstruction to treating `teichUnitFull` as harmless
structure: because the section reduces identically on `kˣ`, the lift of a
generator of the cyclic group `kˣ` has exact order `#k - 1`. -/
theorem exists_isPrimitiveRoot_teichUnitFullVal_cardSubOne
    (S : FullTeichStickelbergerSetup ℓ p k K R') :
    ∃ ζ : 𝓞 R', IsPrimitiveRoot ζ (Fintype.card k - 1) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : kˣ, ∀ z : kˣ, z ∈ Subgroup.zpowers y :=
    IsCyclic.exists_generator
  refine ⟨S.teichUnitFullVal y, ?_⟩
  refine ⟨S.teichUnitFullVal_pow_card_sub_one y, ?_⟩
  intro n hn
  have hres : ((y : k) ^ n) = 1 := by
    have h := congrArg S.residueMap hn
    simpa [S.residueMap_teichUnitFullVal_pow] using h
  have hy_pow : y ^ n = 1 := by
    ext
    simpa using hres
  have h_order : orderOf y = Fintype.card kˣ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hy, Nat.card_eq_fintype_card]
  have hdvd : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one hy_pow
  rwa [h_order, Fintype.card_units] at hdvd

/-- **L2c3d-1: full Teichmüller power-sum orthogonality.** -/
theorem teichUnitFull_sum_pow_units (r : ℕ) :
    (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
      if (Fintype.card k - 1) ∣ r
      then (Fintype.card k - 1 : 𝓞 R')
      else 0 := by
  classical
  rcases Decidable.em ((Fintype.card k - 1) ∣ r) with hdvd | hndvd
  · -- (q-1) ∣ r: every term is 1, sum is (number of units) = q - 1.
    rw [if_pos hdvd]
    obtain ⟨c, hc⟩ := hdvd
    have h_term : ∀ x : kˣ, S.teichUnitFullVal x ^ r = 1 := by
      intro x
      rw [hc, pow_mul, S.teichUnitFullVal_pow_card_sub_one, one_pow]
    rw [Finset.sum_congr rfl fun x _ => h_term x]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_units]
    -- `(card k - 1) • (1 : 𝓞 R') = ↑(card k - 1) = ↑(card k) - 1`.
    rw [nsmul_eq_mul, mul_one]
    have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
    rw [Nat.cast_sub hpos, Nat.cast_one]
  · -- (q-1) ∤ r: sum is 0.
    rw [if_neg hndvd]
    -- Choose generator y of kˣ.
    obtain ⟨y, hy⟩ : ∃ y : kˣ, ∀ z : kˣ, z ∈ Subgroup.zpowers y :=
      IsCyclic.exists_generator
    -- t := teichUnitFullVal y. Show (t^r) * sum = sum.
    set t := S.teichUnitFullVal y with ht_def
    have h_t_mul_sum :
        t ^ r * (∑ x : kˣ, S.teichUnitFullVal x ^ r) =
          ∑ x : kˣ, S.teichUnitFullVal x ^ r := by
      rw [Finset.mul_sum]
      -- Term-wise: t^r * (teichUnitFullVal x)^r = teichUnitFullVal(y*x)^r.
      have h_term_mul : ∀ x : kˣ,
          t ^ r * S.teichUnitFullVal x ^ r =
            S.teichUnitFullVal (y * x) ^ r := by
        intro x
        rw [ht_def, ← mul_pow, ← S.teichUnitFullVal_mul]
      rw [Finset.sum_congr rfl fun x _ => h_term_mul x]
      -- Reindex via the bijection `x ↦ y * x` on `kˣ`.
      let e : kˣ ≃ kˣ := Equiv.mulLeft y
      have : (∑ x : kˣ, S.teichUnitFullVal (y * x) ^ r) =
              ∑ x : kˣ, S.teichUnitFullVal (e x) ^ r := rfl
      rw [this]
      exact Finset.sum_equiv e (by simp) (by intros; rfl)
    -- (t^r - 1) * sum = 0.
    have h_factor :
        (t ^ r - 1) * (∑ x : kˣ, S.teichUnitFullVal x ^ r) = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero, h_t_mul_sum]
    -- t^r ≠ 1 because residueMap(t^r) = y^r ≠ 1 in k.
    have h_t_ne : t ^ r ≠ 1 := by
      intro hcontra
      have hres : S.residueMap (t ^ r) = 1 := by
        rw [hcontra]; exact map_one _
      rw [ht_def, map_pow, S.residueMap_teichUnitFullVal] at hres
      -- y^r = 1 in k means (q-1) ∣ r since y has order q-1.
      have h_y_unit_pow : ((y : k) ^ r) = 1 := hres
      -- Lift to kˣ.
      have h_y_pow_unit : (y : kˣ) ^ r = 1 := by
        ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h_y_unit_pow
      -- Order of y divides r ⇒ (#kˣ) ∣ r ⇒ (q-1) ∣ r.
      have h_ord_dvd : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one h_y_pow_unit
      have h_y_gen : orderOf y = Fintype.card kˣ := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hy, Nat.card_eq_fintype_card]
      rw [h_y_gen, Fintype.card_units] at h_ord_dvd
      exact hndvd h_ord_dvd
    -- (t^r - 1) ≠ 0.
    have h_t_sub_ne : t ^ r - 1 ≠ 0 := sub_ne_zero.mpr h_t_ne
    -- Integral domain: (a - 1) * b = 0 and (a - 1) ≠ 0 ⇒ b = 0.
    rcases mul_eq_zero.mp h_factor with h | h
    · exact absurd h h_t_sub_ne
    · exact h

/-- **L2c3d-5: inner Teichmüller sum evaluation.** The inner sum in the
denominator-cleared digit expansion factors via multiplicativity and
evaluates by Teichmüller power-sum orthogonality. -/
theorem teichUnitFull_innerSum_eval (A M : ℕ) (c : kˣ) :
    (∑ x : kˣ,
        S.teichUnitFullVal x ^ A *
          S.teichUnitFullVal (c * x) ^ M) =
      if (Fintype.card k - 1) ∣ (A + M)
      then (Fintype.card k - 1 : 𝓞 R') *
            S.teichUnitFullVal c ^ M
      else 0 := by
  classical
  -- ω(c·x)^M = ω(c)^M · ω(x)^M.
  have h_term : ∀ x : kˣ,
      S.teichUnitFullVal x ^ A * S.teichUnitFullVal (c * x) ^ M =
        S.teichUnitFullVal c ^ M * S.teichUnitFullVal x ^ (A + M) := by
    intro x
    rw [S.teichUnitFullVal_mul, mul_pow, pow_add]
    ring
  rw [Finset.sum_congr rfl fun x _ => h_term x]
  rw [← Finset.mul_sum]
  rw [S.teichUnitFull_sum_pow_units (A + M)]
  -- Distribute the if/then.
  by_cases hdvd : (Fintype.card k - 1) ∣ (A + M)
  · rw [if_pos hdvd, if_pos hdvd]; ring
  · rw [if_neg hdvd, if_neg hdvd]; ring

end TeichOrthogonality

/-- Obstruction for the exact pair-cyclotomic upstairs API. Any full
Teichmüller setup over a field satisfying the current `{p, ℓ}` cyclotomic
typeclass already implies `#k - 1 ∣ 2 * (p * ℓ)`.

For arbitrary residue degree one only knows `p ∣ #k - 1`; the stronger
divisibility is generally false. This theorem records why the current
pair-cyclotomic `FullTeichDworkSetup`/`Ref18SourceUpstairsData` interface
cannot be the closed general-residue-degree REF-18h route without enlarging
or generalizing the upstairs field API. -/
theorem cardSubOne_dvd_two_mul_pair
    (S : FullTeichStickelbergerSetup ℓ p k K R') (hpℓ : p ≠ ℓ) :
    Fintype.card k - 1 ∣ 2 * (p * ℓ) := by
  obtain ⟨ζ, hζ⟩ := S.exists_isPrimitiveRoot_teichUnitFullVal_cardSubOne
  exact
    TraceFormStickelbergerSetup.cardSubOne_dvd_two_mul_pair_of_isPrimitiveRoot
      (ℓ := ℓ) (p := p) (k := k) (R' := R') hpℓ hζ

/-- **L2c3d-2 (raw form): the reciprocal residue character is a power
of the full Teichmüller.** Stated using the raw cofactor
`(#k - 1) / p`; the `stickD`-form wrapper lives in `LeadingTerm.lean`. -/
theorem residueCharInt_rec_eq_teichUnitFull_pow
    (a : ℕ) (_ha₁ : 1 ≤ a) (_ha₂ : a ≤ p - 1) (x : kˣ) :
    S.residueCharInt (x : k) ^ (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * ((Fintype.card k - 1) / p)) := by
  rw [S.residueCharInt_eq_teichUnitFull_pow_d x, ← pow_mul, mul_comm]

end FullTeichStickelbergerSetup

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- A natural number not divisible by `ℓ` is a `Q`-unit. -/
theorem natCast_not_mem_Q_of_not_dvd {n : ℕ} (hn : ¬ ℓ ∣ n) :
    (n : 𝓞 R') ∉ S.Q := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  intro hmem
  rw [S.toConcreteStickelbergerSetup.mem_Q_iff_residueMap_eq_zero] at hmem
  rw [map_natCast] at hmem
  exact hn ((CharP.cast_eq_zero_iff k ℓ n).1 hmem)

/-- The cardinality of the residue field has positive `f`-exponent. -/
theorem f_pos : 0 < S.f := by
  have h_card_ge : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hcard_eq : Fintype.card k = ℓ ^ S.f := S.card_k
  by_contra h
  push Not at h
  have hf : S.f = 0 := Nat.le_zero.mp h
  rw [hf, pow_zero] at hcard_eq
  omega

/-- `ℓ` does not divide `Fintype.card k - 1`. -/
theorem ell_not_dvd_card_k_sub_one (S : TraceFormStickelbergerSetup ℓ p k K R') :
    ¬ ℓ ∣ (Fintype.card k - 1) := by
  intro hdvd
  have hcard_eq : Fintype.card k = ℓ ^ S.f := S.card_k
  have hf_pos : 0 < S.f := S.f_pos
  have hℓ_dvd_card : ℓ ∣ Fintype.card k := by
    rw [hcard_eq]
    exact dvd_pow_self ℓ hf_pos.ne'
  have hcard_pos : 1 ≤ Fintype.card k := Fintype.card_pos
  -- ℓ ∣ card k and ℓ ∣ (card k - 1) ⇒ ℓ ∣ 1.
  have hone : ℓ ∣ 1 := by
    have h := Nat.dvd_sub hℓ_dvd_card hdvd
    rwa [Nat.sub_sub_self hcard_pos] at h
  exact (Fact.out : Nat.Prime ℓ).one_lt.ne' (Nat.dvd_one.mp hone)

/-- The integer `Fintype.card k - 1` is a `Q`-unit. -/
theorem natCast_card_k_sub_one_not_mem_Q :
    ((Fintype.card k - 1 : ℕ) : 𝓞 R') ∉ S.Q :=
  S.natCast_not_mem_Q_of_not_dvd S.ell_not_dvd_card_k_sub_one

/-- The uniformizer `π = ζ_ℓ - 1` is non-zero in `𝓞 R'`. Follows from
`zeta_ell_int` being a primitive `ℓ`-th root of unity with `ℓ ≥ 2`. -/
theorem pi_ne_zero : S.π ≠ 0 := by
  rw [S.toConcreteStickelbergerSetup.π_def]
  intro hc
  have h1 : S.zeta_ell_int = 1 := by linear_combination hc
  have h_prim := S.toConcreteStickelbergerSetup.zeta_ell_int_isPrimitiveRoot
  have hℓ_two_le : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_ord_one : S.zeta_ell_int ^ 1 = 1 := by rw [pow_one]; exact h1
  have h_ord_dvd : ℓ ∣ 1 := h_prim.dvd_of_pow_eq_one 1 h_ord_one
  have : ℓ ≤ 1 := Nat.le_of_dvd (by omega) h_ord_dvd
  omega

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
