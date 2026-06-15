module

public import BernoulliRegular.Reflection.SingularKummer.SingularPair
public import BernoulliRegular.UnitQuotient.Components

/-!
# Singular Kummer: global units in the kernel

The pair-form singular exact sequence in `SingularPair` identifies the kernel
of `S → A[p]` with the image of the *fractional* units of `K`.  For the
reflection argument this kernel must be written in terms of the actual global
units `E = (𝓞 K)ˣ`, and then in terms of the quotient `E / E^p`.

This file specializes the fractional-unit statement to rings of integers and
records the global-unit form of the same kernel identity.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable {p : ℕ}

/-- A global unit of `𝓞 K` is a fractional unit in `K`. -/
def globalUnitToFractionalUnit :
    CyclotomicUnitGroup K →*
      fractionalUnitSubgroup (R := 𝓞 K) (K := K) where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K) u, by
    change toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) = 1
    rw [toPrincipalIdeal_eq_iff]
    simpa using
      (FractionalIdeal.spanSingleton_eq_spanSingleton (S := (𝓞 K)⁰)
        (x := ((Units.map (algebraMap (𝓞 K) K) u : Kˣ) : K))
        (y := (1 : K))).2 ⟨u⁻¹, by
        change algebraMap (𝓞 K) K ((u⁻¹ : CyclotomicUnitGroup K) : 𝓞 K) *
            algebraMap (𝓞 K) K (u : 𝓞 K) = 1
        rw [← map_mul]
        simp⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro u v
    apply Subtype.ext
    simp [map_mul]

@[simp]
theorem globalUnitToFractionalUnit_apply_val (u : CyclotomicUnitGroup K) :
    ((globalUnitToFractionalUnit K u).1 : Kˣ) =
      Units.map (algebraMap (𝓞 K) K) u :=
  by
  change (Units.map (algebraMap (𝓞 K) K) u : Kˣ) =
    Units.map (algebraMap (𝓞 K) K) u
  rfl

theorem globalUnitToFractionalUnit_apply_coe (u : CyclotomicUnitGroup K) :
    (((globalUnitToFractionalUnit K u).1 : Kˣ) : K) =
      algebraMap (𝓞 K) K (u : 𝓞 K) :=
  by
  change ((Units.map (algebraMap (𝓞 K) K) u : Kˣ) : K) =
    algebraMap (𝓞 K) K (u : 𝓞 K)
  rfl

theorem globalUnitToFractionalUnit_injective :
    Function.Injective (globalUnitToFractionalUnit K) := by
  intro u v huv
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h :=
    congrArg (fun w : fractionalUnitSubgroup (R := 𝓞 K) (K := K) =>
      ((w.1 : Kˣ) : K)) huv
  simpa [globalUnitToFractionalUnit_apply_coe] using h

theorem globalUnitToFractionalUnit_surjective :
    Function.Surjective (globalUnitToFractionalUnit K) := by
  intro u
  let x : Kˣ := u.1
  have hxPrincipal : toPrincipalIdeal (𝓞 K) K x = 1 := u.2
  have hxSpan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
        (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa using
      (toPrincipalIdeal_eq_iff (R := 𝓞 K) (K := K)
        (I := (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) (x := x)).1 hxPrincipal
  have hxMem : (x : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hxSpan]
    exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ (x : K)
  obtain ⟨r, hr⟩ :=
    (FractionalIdeal.mem_one_iff ((𝓞 K)⁰) (P := K)).1 hxMem
  have hxInvPrincipal : toPrincipalIdeal (𝓞 K) K x⁻¹ = 1 := by
    rw [map_inv, hxPrincipal, inv_one]
  have hxInvSpan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x⁻¹ : Kˣ) : K) =
        (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa using
      (toPrincipalIdeal_eq_iff (R := 𝓞 K) (K := K)
        (I := (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) (x := x⁻¹)).1 hxInvPrincipal
  have hxInvMem : ((x⁻¹ : Kˣ) : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hxInvSpan]
    exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ ((x⁻¹ : Kˣ) : K)
  obtain ⟨s, hs⟩ :=
    (FractionalIdeal.mem_one_iff ((𝓞 K)⁰) (P := K)).1 hxInvMem
  let v : CyclotomicUnitGroup K :=
    { val := r
      inv := s
      val_inv := by
        apply FaithfulSMul.algebraMap_injective (𝓞 K) K
        rw [map_mul, hr, hs]
        simp [x]
      inv_val := by
        apply FaithfulSMul.algebraMap_injective (𝓞 K) K
        rw [map_mul, hs, hr]
        simp [x] }
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change algebraMap (𝓞 K) K (v : 𝓞 K) = (x : K)
  simpa [v] using hr

/-- The global unit group of the ring of integers is the same as the
fractional-unit subgroup of `Kˣ`. -/
def globalUnitEquivFractionalUnit :
    CyclotomicUnitGroup K ≃*
      fractionalUnitSubgroup (R := 𝓞 K) (K := K) where
  toFun := globalUnitToFractionalUnit K
  invFun u := Classical.choose (globalUnitToFractionalUnit_surjective K u)
  left_inv u :=
    globalUnitToFractionalUnit_injective K <| Classical.choose_spec
      (globalUnitToFractionalUnit_surjective K (globalUnitToFractionalUnit K u))
  right_inv u :=
    Classical.choose_spec (globalUnitToFractionalUnit_surjective K u)
  map_mul' := fun u v =>
    map_mul (globalUnitToFractionalUnit K) u v

/-- The map from global units to the singular group. -/
def globalUnitToSingularGroup (p : ℕ) :
    CyclotomicUnitGroup K →*
      SingularGroup (R := 𝓞 K) (K := K) p :=
  (unitToSingularGroup (R := 𝓞 K) (K := K) p).comp
    (globalUnitToFractionalUnit K)

@[simp]
theorem globalUnitToSingularGroup_apply (p : ℕ) (u : CyclotomicUnitGroup K) :
    globalUnitToSingularGroup K p u =
      unitToSingularGroup (R := 𝓞 K) (K := K) p
        (globalUnitToFractionalUnit K u) :=
  rfl

theorem globalUnitToSingularGroup_range (p : ℕ) :
    (globalUnitToSingularGroup K p).range =
      (unitToSingularGroup (R := 𝓞 K) (K := K) p).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := hx
    exact ⟨globalUnitToFractionalUnit K u, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, hv⟩ := globalUnitToFractionalUnit_surjective K u
    refine ⟨v, ?_⟩
    simp [globalUnitToSingularGroup, hv]

/-- In the ring-of-integers case, the kernel of `S → A[p]` is the image of
global units. -/
theorem singularGroupClassMapToPTorsion_ker_eq_globalUnitToSingularGroup_range
    (p : ℕ) :
    (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p).ker =
      (globalUnitToSingularGroup K p).range := by
  rw [globalUnitToSingularGroup_range]
  exact singularGroupClassMapToPTorsion_ker_eq_unitToSingularGroup_range
    (R := 𝓞 K) (K := K) p

/-- Exactness of the singular sequence at `S`, with actual global units as the
left term. -/
theorem globalUnitToSingularGroup_exact_singularGroupClassMapToPTorsion (p : ℕ) :
    Function.MulExact
      (globalUnitToSingularGroup K p)
      (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) := by
  rw [MonoidHom.mulExact_iff]
  exact singularGroupClassMapToPTorsion_ker_eq_globalUnitToSingularGroup_range K p

/-- The global-unit form of the pair singular exact sequence. -/
theorem singularGroup_globalUnit_exact_and_surjective (p : ℕ) :
    Function.MulExact
        (globalUnitToSingularGroup K p)
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) ∧
      Function.Surjective
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) :=
  ⟨globalUnitToSingularGroup_exact_singularGroupClassMapToPTorsion K p,
    singularGroupClassMapToPTorsion_surjective (R := 𝓞 K) (K := K) p⟩

@[simp]
theorem globalUnitToSingularGroup_pow_eq_one (p : ℕ)
    (u : CyclotomicUnitGroup K) :
    globalUnitToSingularGroup K p (u ^ p) = 1 := by
  let gamma : Kˣ := Units.map (algebraMap (𝓞 K) K) u
  change
    (QuotientGroup.mk
      (unitPair (R := 𝓞 K) (K := K) p
        (globalUnitToFractionalUnit K (u ^ p))) :
        SingularGroup (R := 𝓞 K) (K := K) p) = 1
  exact
    (QuotientGroup.eq_one_iff
      (N := principalPairSubgroup (R := 𝓞 K) (K := K) p)
      (unitPair (R := 𝓞 K) (K := K) p
        (globalUnitToFractionalUnit K (u ^ p)))).2
      ⟨gamma, by
        apply Subtype.ext
        apply Prod.ext
        · change toPrincipalIdeal (𝓞 K) K gamma =
            (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
          exact (globalUnitToFractionalUnit K u).2
        · change gamma ^ p = (globalUnitToFractionalUnit K (u ^ p)).1
          rw [map_pow]
          rfl⟩

/-- The map `E/E^p → S` induced by global units. -/
def globalUnitPowerQuotientToSingularGroup (p : ℕ) [Fact p.Prime] :
    CyclotomicUnitPowerQuotient (p := p) (N := 1) K →*
      SingularGroup (R := 𝓞 K) (K := K) p :=
  QuotientGroup.lift
    (CyclotomicUnitPowerSubgroup (p := p) (N := 1) K)
    (globalUnitToSingularGroup K p)
    (by
      intro u hu
      obtain ⟨v, rfl⟩ := hu
      simpa using globalUnitToSingularGroup_pow_eq_one K p v)

@[simp]
theorem globalUnitPowerQuotientToSingularGroup_mk (p : ℕ) [Fact p.Prime]
    (u : CyclotomicUnitGroup K) :
    globalUnitPowerQuotientToSingularGroup K p
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u) =
      globalUnitToSingularGroup K p u :=
  rfl

theorem globalUnitPowerQuotientToSingularGroup_range (p : ℕ) [Fact p.Prime] :
    (globalUnitPowerQuotientToSingularGroup K p).range =
      (globalUnitToSingularGroup K p).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, rfl⟩ := hx
    refine QuotientGroup.induction_on q ?_
    intro u
    exact ⟨u, rfl⟩
  · intro hx
    obtain ⟨u, rfl⟩ := hx
    exact ⟨cyclotomicUnitPowerClass (p := p) (N := 1) K u, rfl⟩

/-- The kernel of `S → A[p]` is also the image of the actual quotient
`E/E^p`. -/
theorem singularGroupClassMapToPTorsion_ker_eq_globalUnitPowerQuotientToSingularGroup_range
    (p : ℕ) [Fact p.Prime] :
    (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p).ker =
      (globalUnitPowerQuotientToSingularGroup K p).range := by
  rw [globalUnitPowerQuotientToSingularGroup_range]
  exact singularGroupClassMapToPTorsion_ker_eq_globalUnitToSingularGroup_range K p

/-- Exactness at `S` for the singular sequence written with `E/E^p`. -/
theorem globalUnitPowerQuotientToSingularGroup_exact_singularGroupClassMapToPTorsion
    (p : ℕ) [Fact p.Prime] :
    Function.MulExact
      (globalUnitPowerQuotientToSingularGroup K p)
      (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) := by
  rw [MonoidHom.mulExact_iff]
  exact
    singularGroupClassMapToPTorsion_ker_eq_globalUnitPowerQuotientToSingularGroup_range
      K p

theorem exists_globalUnit_pow_eq_of_globalUnitToSingularGroup_eq_one (p : ℕ)
    (u : CyclotomicUnitGroup K) (hu : globalUnitToSingularGroup K p u = 1) :
    ∃ v : CyclotomicUnitGroup K, u = v ^ p := by
  have hquot :
      (QuotientGroup.mk
        (unitPair (R := 𝓞 K) (K := K) p
          (globalUnitToFractionalUnit K u)) :
          SingularGroup (R := 𝓞 K) (K := K) p) = 1 := by
    simpa [globalUnitToSingularGroup] using hu
  obtain ⟨gamma, hgammaPair⟩ :=
    (QuotientGroup.eq_one_iff
      (N := principalPairSubgroup (R := 𝓞 K) (K := K) p)
      (unitPair (R := 𝓞 K) (K := K) p
        (globalUnitToFractionalUnit K u))).1 hquot
  have hgammaIdeal : toPrincipalIdeal (𝓞 K) K gamma = 1 := by
    have h :=
      congrArg (fun s : SingularPair (𝓞 K) K p => ideal s) hgammaPair
    simpa [ideal, unitPair, principalPair] using h
  let gammaUnit : fractionalUnitSubgroup (R := 𝓞 K) (K := K) :=
    ⟨gamma, hgammaIdeal⟩
  obtain ⟨v, hv⟩ := globalUnitToFractionalUnit_surjective K gammaUnit
  have hgammaGenerator : gamma ^ p = (globalUnitToFractionalUnit K u).1 := by
    have h :=
      congrArg (fun s : SingularPair (𝓞 K) K p => generator s) hgammaPair
    simpa [generator, unitPair, principalPair] using h
  refine ⟨v, globalUnitToFractionalUnit_injective K ?_⟩
  apply Subtype.ext
  change (globalUnitToFractionalUnit K u).1 =
    (globalUnitToFractionalUnit K (v ^ p)).1
  rw [map_pow, hv]
  exact hgammaGenerator.symm

/-- The map `E/E^p → S` is injective. -/
theorem globalUnitPowerQuotientToSingularGroup_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (globalUnitPowerQuotientToSingularGroup K p) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext q
  constructor
  · intro hq
    change q = 1
    revert hq
    refine QuotientGroup.induction_on q ?_
    intro u hu
    have hu' : globalUnitToSingularGroup K p u = 1 := by
      rw [← globalUnitPowerQuotientToSingularGroup_mk (K := K) p u]
      exact hu
    obtain ⟨v, hv⟩ :=
      exists_globalUnit_pow_eq_of_globalUnitToSingularGroup_eq_one K p u hu'
    exact
      (QuotientGroup.eq_one_iff
        (N := CyclotomicUnitPowerSubgroup (p := p) (N := 1) K) u).2
        ⟨v, by
          simpa [pow_one] using hv.symm⟩
  · intro hq
    change globalUnitPowerQuotientToSingularGroup K p q = 1
    have hq' : q = 1 := by
      simpa using hq
    simp [hq']

/-- The short-exact-sequence data needed from Lemma 2.2 of the draft:
`0 → E/E^p → S → A[p] → 0`. -/
theorem singularGroup_globalUnitPowerQuotient_shortExact (p : ℕ) [Fact p.Prime] :
    Function.Injective (globalUnitPowerQuotientToSingularGroup K p) ∧
      Function.MulExact
        (globalUnitPowerQuotientToSingularGroup K p)
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) ∧
      Function.Surjective
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p) :=
  ⟨globalUnitPowerQuotientToSingularGroup_injective K p,
    globalUnitPowerQuotientToSingularGroup_exact_singularGroupClassMapToPTorsion K p,
    singularGroupClassMapToPTorsion_surjective (R := 𝓞 K) (K := K) p⟩

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
