module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import BernoulliRegular.Reflection.Local.Basic
public import BernoulliRegular.Reflection.SingularKummer.SingularZMod

/-!
# Singular Kummer: localization at a height-one prime

This file provides the REF-12 localization target.  For a height-one prime
`v`, the local units are represented inside `Kˣ` as the elements with
`v`-adic valuation one.  After choosing a uniformizer, every global field
class in `Kˣ / Kˣ^p` has a normalized representative in this local-unit
subgroup, giving a homomorphism

```text
  Kˣ / Kˣ^p -> U_v / U_v^p.
```

Composing this with the singular-pair generator gives the localization map
from the singular group `S` to the local-unit quotient.
-/

@[expose] public section

noncomputable section

open WithZero Multiplicative IsDedekindDomain
open scoped NumberField nonZeroDivisors WithZero

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The global field quotient `Kˣ / Kˣ^p`. -/
abbrev fieldPowerQuotient (p : ℕ) : Type _ :=
  Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range

/-- The quotient map `Kˣ -> Kˣ / Kˣ^p`. -/
def fieldPowerClass (p : ℕ) : Kˣ →* fieldPowerQuotient K p :=
  QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range

@[simp]
theorem fieldPowerClass_apply (p : ℕ) (x : Kˣ) :
    fieldPowerClass K p x = QuotientGroup.mk x :=
  rfl

@[simp]
theorem fieldPowerClass_pow_eq_one (p : ℕ) (x : Kˣ) :
    fieldPowerClass K p (x ^ p) = 1 :=
  (QuotientGroup.eq_one_iff
    (N := (powMonoidHom p : Kˣ →* Kˣ).range) (x ^ p)).2 ⟨x, rfl⟩

/-- Every element of `Kˣ / Kˣ^p` is killed by `p`. -/
theorem fieldPowerQuotient_pow_eq_one (p : ℕ)
    (x : fieldPowerQuotient K p) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x fun y => ?_
  rw [← QuotientGroup.mk_pow]
  exact fieldPowerClass_pow_eq_one K p y

/-- Additive `ZMod p`-module structure on `Kˣ / Kˣ^p`. -/
instance fieldPowerQuotientModuleZMod (p : ℕ) :
    Module (ZMod p) (Additive (fieldPowerQuotient K p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact fieldPowerQuotient_pow_eq_one K p x.toMul

variable (v : HeightOneSpectrum R)

/-- The local units at `v`, represented as global field units with
`v`-adic valuation one. -/
abbrev localUnitSubgroupAt : Subgroup Kˣ :=
  ({w : HeightOneSpectrum R | w ≠ v} : Set (HeightOneSpectrum R)).unit K

theorem mem_localUnitSubgroupAt_iff {x : Kˣ} :
    x ∈ localUnitSubgroupAt (R := R) (K := K) v ↔
      v.valuation K (x : K) = 1 := by
  change x ∈ ({w : HeightOneSpectrum R | w ≠ v} : Set (HeightOneSpectrum R)).unit K ↔
    v.valuation K (x : K) = 1
  constructor
  · intro hx
    exact hx v (by simp)
  · intro hx w hw
    have hwv : w = v := by
      by_contra hne
      exact hw hne
    simpa [hwv] using hx

/-- The quotient `U_v / U_v^p` of local units by local `p`-th powers. -/
abbrev localUnitPowerQuotientAt (p : ℕ) : Type _ :=
  localUnitSubgroupAt (R := R) (K := K) v ⧸
    (powMonoidHom p : localUnitSubgroupAt (R := R) (K := K) v →*
      localUnitSubgroupAt (R := R) (K := K) v).range

/-- The quotient map `U_v -> U_v / U_v^p`. -/
def localUnitPowerClassAt (p : ℕ) :
    localUnitSubgroupAt (R := R) (K := K) v →*
      localUnitPowerQuotientAt (R := R) (K := K) v p :=
  QuotientGroup.mk'
    (powMonoidHom p : localUnitSubgroupAt (R := R) (K := K) v →*
      localUnitSubgroupAt (R := R) (K := K) v).range

@[simp]
theorem localUnitPowerClassAt_apply (p : ℕ)
    (u : localUnitSubgroupAt (R := R) (K := K) v) :
    localUnitPowerClassAt (R := R) (K := K) v p u = QuotientGroup.mk u :=
  rfl

@[simp]
theorem localUnitPowerClassAt_pow_eq_one (p : ℕ)
    (u : localUnitSubgroupAt (R := R) (K := K) v) :
    localUnitPowerClassAt (R := R) (K := K) v p (u ^ p) = 1 :=
  (QuotientGroup.eq_one_iff
    (N := (powMonoidHom p : localUnitSubgroupAt (R := R) (K := K) v →*
      localUnitSubgroupAt (R := R) (K := K) v).range) (u ^ p)).2 ⟨u, rfl⟩

theorem localUnitPowerQuotientAt_pow_eq_one (p : ℕ)
    (x : localUnitPowerQuotientAt (R := R) (K := K) v p) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [← QuotientGroup.mk_pow]
  exact localUnitPowerClassAt_pow_eq_one (R := R) (K := K) v p u

/-- Additive `ZMod p`-module structure on `U_v / U_v^p`. -/
instance localUnitPowerQuotientAtModuleZMod (p : ℕ) :
    Module (ZMod p)
      (Additive (localUnitPowerQuotientAt (R := R) (K := K) v p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact localUnitPowerQuotientAt_pow_eq_one (R := R) (K := K) v p x.toMul

/-- A chosen local uniformizer at `v`, as a global field unit. -/
def localUniformizerUnit : Kˣ :=
  Units.mk0 (Classical.choose (v.valuation_exists_uniformizer K))
    (v.valuation_uniformizer_ne_zero K)

@[simp]
theorem localUniformizerUnit_valuation :
    v.valuation K ((localUniformizerUnit (R := R) (K := K) v : Kˣ) : K) =
      WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (v.valuation_exists_uniformizer K)

/-- The exponent of the chosen uniformizer needed to give a field unit
valuation one at `v`. -/
def localUniformizerExponent (x : Kˣ) : ℤ :=
  -((v.valuation K (x : K)).log)

@[simp]
theorem localUniformizerExponent_one :
    localUniformizerExponent (R := R) (K := K) v 1 = 0 := by
  unfold localUniformizerExponent
  rw [Units.val_one, map_one, WithZero.log_one]
  norm_num

theorem localUniformizerExponent_mul (x y : Kˣ) :
    localUniformizerExponent (R := R) (K := K) v (x * y) =
      localUniformizerExponent (R := R) (K := K) v x +
        localUniformizerExponent (R := R) (K := K) v y := by
  unfold localUniformizerExponent
  rw [Units.val_mul, map_mul]
  rw [WithZero.log_mul]
  · ring
  · exact (Valuation.ne_zero_iff (v.valuation K)).2 x.ne_zero
  · exact (Valuation.ne_zero_iff (v.valuation K)).2 y.ne_zero

theorem localUniformizerExponent_eq_neg_valuationOfNeZero (x : Kˣ) :
    localUniformizerExponent (R := R) (K := K) v x =
      -((v.valuationOfNeZero x).toAdd) := by
  unfold localUniformizerExponent
  rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq (K := K) v x]
  cases h : v.valuationOfNeZero x
  change -((WithZero.exp _).log) = -_
  rw [WithZero.log_exp]
  simp

theorem localUniformizerExponent_eq_count_toPrincipalIdeal (x : Kˣ) :
    localUniformizerExponent (R := R) (K := K) v x =
      FractionalIdeal.count K v
        ((toPrincipalIdeal R K x : (FractionalIdeal R⁰ K)ˣ) :
          FractionalIdeal R⁰ K) := by
  rw [localUniformizerExponent_eq_neg_valuationOfNeZero]
  let n : R := (IsLocalization.sec R⁰ (x : K)).1
  let d : R⁰ := (IsLocalization.sec R⁰ (x : K)).2
  have hd_ne : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have hsec : (x : K) * (algebraMap R K) (d : R) = (algebraMap R K) n := by
    simpa [n, d] using IsLocalization.sec_spec R⁰ (x : K)
  have hI :
      ((toPrincipalIdeal R K x : (FractionalIdeal R⁰ K)ˣ) :
          FractionalIdeal R⁰ K) =
        FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
          ↑(Ideal.span ({n} : Set R)) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg (FractionalIdeal.spanSingleton R⁰)
    calc
      (x : K) =
          ((algebraMap R K) (d : R))⁻¹ * ((x : K) * (algebraMap R K) (d : R)) := by
        field_simp [hd_ne]
      _ = ((algebraMap R K) (d : R))⁻¹ * (algebraMap R K) n := by
        rw [hsec]
  have hIne :
      ((toPrincipalIdeal R K x : (FractionalIdeal R⁰ K)ˣ) :
          FractionalIdeal R⁰ K) ≠ 0 :=
    Units.ne_zero (toPrincipalIdeal R K x)
  rw [FractionalIdeal.count_well_defined K v hIne hI]
  change -((v.valuationOfNeZero x).toAdd) = _
  simp only [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero]
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun
  simp [n, d]
  ring

theorem localUniformizerExponent_generator_dvd (p : ℕ) (s : SingularPair R K p) :
    (p : ℤ) ∣ localUniformizerExponent (R := R) (K := K) v (generator s) := by
  refine ⟨FractionalIdeal.count K v
    ((ideal s : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K), ?_⟩
  rw [localUniformizerExponent_eq_count_toPrincipalIdeal]
  have hprincipal :
      ((toPrincipalIdeal R K (generator s) : (FractionalIdeal R⁰ K)ˣ) :
          FractionalIdeal R⁰ K) =
        (((ideal s : (FractionalIdeal R⁰ K)ˣ) ^ p : (FractionalIdeal R⁰ K)ˣ) :
          FractionalIdeal R⁰ K) :=
    congrArg (fun I : (FractionalIdeal R⁰ K)ˣ => (I : FractionalIdeal R⁰ K))
      (principal_eq_ideal_pow (R := R) (K := K) s)
  rw [hprincipal]
  rw [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow]

theorem localUniformizerUnit_zpow_valuation_eq (x : Kˣ) :
    v.valuation K
        (((localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v x : Kˣ) : K) =
      v.valuation K (x : K) := by
  have hxv : v.valuation K (x : K) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation K)).2 x.ne_zero
  have hden_ne :
      v.valuation K
          (((localUniformizerUnit (R := R) (K := K) v) ^
            localUniformizerExponent (R := R) (K := K) v x : Kˣ) : K) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation K)).2
      (Units.ne_zero
        ((localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v x))
  rw [← WithZero.exp_log hden_ne, ← WithZero.exp_log hxv]
  apply congrArg WithZero.exp
  rw [Units.val_zpow_eq_zpow_val]
  rw [map_zpow₀]
  rw [localUniformizerUnit_valuation]
  rw [WithZero.log_zpow, WithZero.log_exp]
  unfold localUniformizerExponent
  ring

theorem localUnitNormalization_mem (x : Kˣ) :
    v.valuation K
        ((x / (localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v x : Kˣ) : K) = 1 := by
  have hxv : v.valuation K (x : K) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation K)).2 x.ne_zero
  rw [Units.val_div_eq_div_val, map_div₀,
    localUniformizerUnit_zpow_valuation_eq (R := R) (K := K) v]
  exact div_self hxv

/-- Normalize a global field unit to a local unit by dividing by the chosen
uniformizer to the appropriate valuation exponent. -/
def localUnitNormalization (x : Kˣ) :
    localUnitSubgroupAt (R := R) (K := K) v :=
  ⟨x / (localUniformizerUnit (R := R) (K := K) v) ^
      localUniformizerExponent (R := R) (K := K) v x, by
    rw [mem_localUnitSubgroupAt_iff]
    exact localUnitNormalization_mem (R := R) (K := K) v x⟩

theorem localUniformizerExponent_eq_zero_of_mem {x : Kˣ}
    (hx : x ∈ localUnitSubgroupAt (R := R) (K := K) v) :
    localUniformizerExponent (R := R) (K := K) v x = 0 := by
  unfold localUniformizerExponent
  rw [(mem_localUnitSubgroupAt_iff (R := R) (K := K) v).mp hx]
  rw [WithZero.log_one]
  norm_num

theorem localUnitNormalization_of_mem {x : Kˣ}
    (hx : x ∈ localUnitSubgroupAt (R := R) (K := K) v) :
    localUnitNormalization (R := R) (K := K) v x = ⟨x, hx⟩ := by
  apply Subtype.ext
  change x / (localUniformizerUnit (R := R) (K := K) v) ^
      localUniformizerExponent (R := R) (K := K) v x = x
  rw [localUniformizerExponent_eq_zero_of_mem (R := R) (K := K) v hx]
  simp

/-- Normalization is multiplicative. -/
def localUnitNormalizationHom :
    Kˣ →* localUnitSubgroupAt (R := R) (K := K) v where
  toFun := localUnitNormalization (R := R) (K := K) v
  map_one' := by
    apply Subtype.ext
    change (1 : Kˣ) /
        (localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v (1 : Kˣ) = 1
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    change x * y /
        (localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v (x * y) =
      x / (localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v x *
        (y / (localUniformizerUnit (R := R) (K := K) v) ^
          localUniformizerExponent (R := R) (K := K) v y)
    rw [localUniformizerExponent_mul]
    rw [div_mul_div_comm]
    rw [← zpow_add]

@[simp]
theorem localUnitNormalizationHom_apply (x : Kˣ) :
    localUnitNormalizationHom (R := R) (K := K) v x =
      localUnitNormalization (R := R) (K := K) v x :=
  rfl

/-- The map `Kˣ -> U_v / U_v^p` obtained by local-unit normalization. -/
def fieldUnitToLocalUnitPowerQuotient (p : ℕ) :
    Kˣ →* localUnitPowerQuotientAt (R := R) (K := K) v p :=
  (localUnitPowerClassAt (R := R) (K := K) v p).comp
    (localUnitNormalizationHom (R := R) (K := K) v)

@[simp]
theorem fieldUnitToLocalUnitPowerQuotient_apply (p : ℕ) (x : Kˣ) :
    fieldUnitToLocalUnitPowerQuotient (R := R) (K := K) v p x =
      localUnitPowerClassAt (R := R) (K := K) v p
        (localUnitNormalization (R := R) (K := K) v x) :=
  rfl

@[simp]
theorem fieldUnitToLocalUnitPowerQuotient_pow_eq_one (p : ℕ) (x : Kˣ) :
    fieldUnitToLocalUnitPowerQuotient (R := R) (K := K) v p (x ^ p) = 1 := by
  change localUnitPowerClassAt (R := R) (K := K) v p
      (localUnitNormalizationHom (R := R) (K := K) v (x ^ p)) = 1
  rw [map_pow]
  exact localUnitPowerClassAt_pow_eq_one (R := R) (K := K) v p
    (localUnitNormalizationHom (R := R) (K := K) v x)

/-- The induced map `Kˣ / Kˣ^p -> U_v / U_v^p`. -/
def fieldPowerQuotientToLocalUnitPowerQuotient (p : ℕ) :
    fieldPowerQuotient K p →*
      localUnitPowerQuotientAt (R := R) (K := K) v p :=
  QuotientGroup.lift (powMonoidHom p : Kˣ →* Kˣ).range
    (fieldUnitToLocalUnitPowerQuotient (R := R) (K := K) v p)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact fieldUnitToLocalUnitPowerQuotient_pow_eq_one (R := R) (K := K) v p y)

@[simp]
theorem fieldPowerQuotientToLocalUnitPowerQuotient_mk (p : ℕ) (x : Kˣ) :
    fieldPowerQuotientToLocalUnitPowerQuotient (R := R) (K := K) v p
        (fieldPowerClass K p x) =
      fieldUnitToLocalUnitPowerQuotient (R := R) (K := K) v p x :=
  rfl

/-- The generator homomorphism from singular pairs to `Kˣ`. -/
def generatorHom (p : ℕ) : SingularPair R K p →* Kˣ where
  toFun := generator
  map_one' := rfl
  map_mul' := fun _ _ => rfl

@[simp]
theorem generatorHom_apply (p : ℕ) (s : SingularPair R K p) :
    generatorHom (R := R) (K := K) p s = generator s :=
  rfl

/-- The singular-pair generator as a class in `Kˣ / Kˣ^p`. -/
def singularPairToFieldPowerQuotient (p : ℕ) :
    SingularPair R K p →* fieldPowerQuotient K p :=
  (fieldPowerClass K p).comp (generatorHom (R := R) (K := K) p)

@[simp]
theorem singularPairToFieldPowerQuotient_apply (p : ℕ) (s : SingularPair R K p) :
    singularPairToFieldPowerQuotient (R := R) (K := K) p s =
      fieldPowerClass K p (generator s) :=
  rfl

@[simp]
theorem singularPairToFieldPowerQuotient_principalPair (p : ℕ) (gamma : Kˣ) :
    singularPairToFieldPowerQuotient (R := R) (K := K) p
        (principalPair (R := R) (K := K) p gamma) = 1 := by
  change fieldPowerClass K p (gamma ^ p) = 1
  exact fieldPowerClass_pow_eq_one K p gamma

/-- Localization of the singular group to the global quotient `Kˣ / Kˣ^p`. -/
def singularGroupToFieldPowerQuotient (p : ℕ) :
    SingularGroup (R := R) (K := K) p →* fieldPowerQuotient K p :=
  QuotientGroup.lift
    (principalPairSubgroup (R := R) (K := K) p)
    (singularPairToFieldPowerQuotient (R := R) (K := K) p)
    (by
      intro s hs
      obtain ⟨gamma, rfl⟩ := hs
      exact singularPairToFieldPowerQuotient_principalPair (R := R) (K := K) p gamma)

@[simp]
theorem singularGroupToFieldPowerQuotient_mk (p : ℕ) (s : SingularPair R K p) :
    singularGroupToFieldPowerQuotient (R := R) (K := K) p
        (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) =
      fieldPowerClass K p (generator s) :=
  rfl

/-- REF-12 localization: singular classes mapped to the local-unit quotient
`U_v / U_v^p`. -/
def singularGroupLocalizationToLocalUnits (p : ℕ) :
    SingularGroup (R := R) (K := K) p →*
      localUnitPowerQuotientAt (R := R) (K := K) v p :=
  (fieldPowerQuotientToLocalUnitPowerQuotient (R := R) (K := K) v p).comp
    (singularGroupToFieldPowerQuotient (R := R) (K := K) p)

@[simp]
theorem singularGroupLocalizationToLocalUnits_mk (p : ℕ)
    (s : SingularPair R K p) :
    singularGroupLocalizationToLocalUnits (R := R) (K := K) v p
        (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) =
      fieldUnitToLocalUnitPowerQuotient (R := R) (K := K) v p (generator s) :=
  rfl

/-- The REF-12 localization map as a `ZMod p`-linear map after passing to
additive notation. -/
def singularGroupLocalizationToLocalUnitsLinear (p : ℕ) :
    Additive (SingularGroup (R := R) (K := K) p) →ₗ[ZMod p]
      Additive (localUnitPowerQuotientAt (R := R) (K := K) v p) :=
  (singularGroupLocalizationToLocalUnits (R := R) (K := K) v p).toAdditive.toZModLinearMap p

@[simp]
theorem singularGroupLocalizationToLocalUnitsLinear_apply_toMul (p : ℕ)
    (x : Additive (SingularGroup (R := R) (K := K) p)) :
    (singularGroupLocalizationToLocalUnitsLinear (R := R) (K := K) v p x).toMul =
      singularGroupLocalizationToLocalUnits (R := R) (K := K) v p x.toMul :=
  rfl

section Cyclotomic

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]

/-- The distinguished cyclotomic lambda prime as a height-one prime. -/
def cyclotomicLambdaHeightOne : HeightOneSpectrum (𝓞 F) where
  asIdeal := Local.cyclotomicLambda p F
  isPrime := zetaPrime_isPrime p F
  ne_bot := zetaPrime_ne_bot p F

/-- Local units at the cyclotomic lambda prime, represented inside `Kˣ`. -/
abbrev cyclotomicLocalUnitSubgroup : Subgroup Fˣ :=
  localUnitSubgroupAt (R := 𝓞 F) (K := F)
    (cyclotomicLambdaHeightOne (p := p) F)

/-- The cyclotomic local-unit quotient `U_lambda / U_lambda^p`. -/
abbrev cyclotomicLocalUnitPowerQuotient : Type _ :=
  localUnitPowerQuotientAt (R := 𝓞 F) (K := F)
    (cyclotomicLambdaHeightOne (p := p) F) p

/-- REF-12 localization at the cyclotomic lambda prime. -/
def singularGroupLocalizationToCyclotomicLocalUnits :
    SingularGroup (R := 𝓞 F) (K := F) p →*
      cyclotomicLocalUnitPowerQuotient (p := p) F :=
  singularGroupLocalizationToLocalUnits (R := 𝓞 F) (K := F)
    (cyclotomicLambdaHeightOne (p := p) F) p

/-- Linear form of the REF-12 cyclotomic localization map. -/
def singularGroupLocalizationToCyclotomicLocalUnitsLinear :
    Additive (SingularGroup (R := 𝓞 F) (K := F) p) →ₗ[ZMod p]
      Additive (cyclotomicLocalUnitPowerQuotient (p := p) F) :=
  singularGroupLocalizationToLocalUnitsLinear (R := 𝓞 F) (K := F)
    (cyclotomicLambdaHeightOne (p := p) F) p

end Cyclotomic

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end
