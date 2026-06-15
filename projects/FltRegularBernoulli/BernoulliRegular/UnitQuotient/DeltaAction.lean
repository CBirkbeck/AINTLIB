module

public import BernoulliRegular.UnitQuotient.Components
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Unit quotients: the actual cyclotomic `Delta` action

The files `UnitQuotient.Components` and `UnitQuotient.Structure` allow a
declared action of `Delta = (ZMod p)ˣ` on `E/E^(p^N)`.  This file supplies the
actual action when `K` is the `p`-th cyclotomic field.

The construction uses the standard cyclotomic Galois equivalence

```text
Gal(K / Q) ≃ (ZMod p)ˣ
```

and the induced action of field automorphisms on the ring of integers.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The standard cyclotomic Galois equivalence
`Gal(K / Q) ≃ (ZMod p)^*`. -/
noncomputable abbrev cyclotomicGalEquivZMod :
    Gal(K / ℚ) ≃* CyclotomicUnitDelta p :=
  IsCyclotomicExtension.Rat.galEquivZMod p K

/-- The Galois automorphism indexed by `a : (ZMod p)^*`. -/
noncomputable def cyclotomicSigmaOfUnit (a : CyclotomicUnitDelta p) :
    Gal(K / ℚ) :=
  (cyclotomicGalEquivZMod (p := p) K).symm a

@[simp]
theorem cyclotomicGalEquivZMod_sigmaOfUnit (a : CyclotomicUnitDelta p) :
    cyclotomicGalEquivZMod (p := p) K (cyclotomicSigmaOfUnit (p := p) K a) = a :=
  (cyclotomicGalEquivZMod (p := p) K).apply_symm_apply a

@[simp]
theorem cyclotomicSigmaOfUnit_one :
    cyclotomicSigmaOfUnit (p := p) K 1 = 1 :=
  map_one (cyclotomicGalEquivZMod (p := p) K).symm

@[simp]
theorem cyclotomicSigmaOfUnit_mul (a b : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K (a * b) =
      cyclotomicSigmaOfUnit (p := p) K a * cyclotomicSigmaOfUnit (p := p) K b :=
  map_mul (cyclotomicGalEquivZMod (p := p) K).symm a b

/-- The distinguished primitive `p`-th root of unity in `O_K`. -/
noncomputable abbrev cyclotomicZetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

theorem cyclotomicZetaInteger_isPrimitiveRoot :
    IsPrimitiveRoot (cyclotomicZetaInteger (p := p) K) p := by
  simpa [cyclotomicZetaInteger] using
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot

@[simp]
theorem cyclotomicSigmaOfUnit_apply_zeta (a : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K a (IsCyclotomicExtension.zeta p ℚ K) =
      (IsCyclotomicExtension.zeta p ℚ K) ^ (a : ZMod p).val := by
  let σ := cyclotomicSigmaOfUnit (p := p) K a
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (n := p) (K := K) (σ := σ)
      (x := IsCyclotomicExtension.zeta p ℚ K)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one)
  rw [show IsCyclotomicExtension.Rat.galEquivZMod p K σ = a by
      exact cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) a] at h
  exact h

@[simp]
theorem cyclotomicSigmaOfUnit_smul_zetaInteger (a : CyclotomicUnitDelta p) :
    cyclotomicSigmaOfUnit (p := p) K a • cyclotomicZetaInteger (p := p) K =
      cyclotomicZetaInteger (p := p) K ^ (a : ZMod p).val := by
  let σ := cyclotomicSigmaOfUnit (p := p) K a
  have h :=
    IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
      (n := p) (K := K) (σ := σ)
      (x := cyclotomicZetaInteger (p := p) K)
      ((cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).pow_eq_one)
  rw [show IsCyclotomicExtension.Rat.galEquivZMod p K σ = a by
      exact cyclotomicGalEquivZMod_sigmaOfUnit (p := p) (K := K) a] at h
  exact h

/-- The ring-of-integers automorphism induced by the cyclotomic Galois
automorphism indexed by `a`. -/
noncomputable def cyclotomicRingOfIntegersEquiv (a : CyclotomicUnitDelta p) :
    𝓞 K ≃+* 𝓞 K :=
  MulSemiringAction.toRingEquiv (Gal(K / ℚ)) (𝓞 K)
    (cyclotomicSigmaOfUnit (p := p) K a)

@[simp]
theorem cyclotomicRingOfIntegersEquiv_one_apply (x : 𝓞 K) :
    cyclotomicRingOfIntegersEquiv (p := p) K 1 x = x := by
  change cyclotomicSigmaOfUnit (p := p) K 1 • x = x
  simp

theorem cyclotomicRingOfIntegersEquiv_mul_apply
    (a b : CyclotomicUnitDelta p) (x : 𝓞 K) :
    cyclotomicRingOfIntegersEquiv (p := p) K (a * b) x =
      cyclotomicRingOfIntegersEquiv (p := p) K a
        (cyclotomicRingOfIntegersEquiv (p := p) K b x) := by
  change cyclotomicSigmaOfUnit (p := p) K (a * b) • x =
    cyclotomicSigmaOfUnit (p := p) K a •
      cyclotomicSigmaOfUnit (p := p) K b • x
  rw [cyclotomicSigmaOfUnit_mul]
  exact smul_smul
    (cyclotomicSigmaOfUnit (p := p) K a)
    (cyclotomicSigmaOfUnit (p := p) K b) x

/-- The induced automorphism of the global unit group `E = O_K^*`. -/
noncomputable def cyclotomicUnitEquiv (a : CyclotomicUnitDelta p) :
    CyclotomicUnitGroup K ≃* CyclotomicUnitGroup K :=
  Units.mapEquiv ((cyclotomicRingOfIntegersEquiv (p := p) K a).toMulEquiv)

@[simp]
theorem cyclotomicUnitEquiv_one_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitEquiv (p := p) K 1 u = u :=
  Units.ext <| cyclotomicRingOfIntegersEquiv_one_apply (p := p) (K := K) (u : 𝓞 K)

theorem cyclotomicUnitEquiv_mul_apply
    (a b : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitEquiv (p := p) K (a * b) u =
      cyclotomicUnitEquiv (p := p) K a
        (cyclotomicUnitEquiv (p := p) K b u) :=
  Units.ext <| cyclotomicRingOfIntegersEquiv_mul_apply (p := p) (K := K) a b (u : 𝓞 K)

/-- The subgroup of `p^N`-th powers is stable under the actual cyclotomic
action on units. -/
theorem cyclotomicUnitPowerSubgroup_map (a : CyclotomicUnitDelta p) :
    (CyclotomicUnitPowerSubgroup (p := p) (N := N) K).map
        (cyclotomicUnitEquiv (p := p) K a).toMonoidHom =
      CyclotomicUnitPowerSubgroup (p := p) (N := N) K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨cyclotomicUnitEquiv (p := p) K a z, by simp [map_pow]⟩
  · intro hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(cyclotomicUnitEquiv (p := p) K a).symm z ^ (p ^ N), ?_, ?_⟩
    · exact ⟨(cyclotomicUnitEquiv (p := p) K a).symm z, rfl⟩
    · rw [map_pow]
      change cyclotomicUnitEquiv (p := p) K a
          ((cyclotomicUnitEquiv (p := p) K a).symm z) ^ (p ^ N) =
        z ^ (p ^ N)
      rw [MulEquiv.apply_symm_apply]

/-- The actual cyclotomic action on the quotient `E/E^(p^N)`. -/
noncomputable def cyclotomicUnitPowerQuotientEquiv (a : CyclotomicUnitDelta p) :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K ≃*
      CyclotomicUnitPowerQuotient (p := p) (N := N) K :=
  QuotientGroup.congr
    (CyclotomicUnitPowerSubgroup (p := p) (N := N) K)
    (CyclotomicUnitPowerSubgroup (p := p) (N := N) K)
    (cyclotomicUnitEquiv (p := p) K a)
    (cyclotomicUnitPowerSubgroup_map (p := p) (N := N) (K := K) a)

@[simp]
theorem cyclotomicUnitPowerQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K a
        (cyclotomicUnitPowerClass (p := p) (N := N) K u) =
      cyclotomicUnitPowerClass (p := p) (N := N) K
        (cyclotomicUnitEquiv (p := p) K a u) :=
  rfl

/-- The actual `Delta` action on `E/E^(p^N)`. -/
noncomputable def cyclotomicUnitPowerQuotientDeltaAction :
    CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K where
  toMulAut :=
    { toFun := cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K
      map_one' := by
        ext x
        refine QuotientGroup.induction_on x ?_
        intro u
        change cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K 1
            (cyclotomicUnitPowerClass (p := p) (N := N) K u) =
          cyclotomicUnitPowerClass (p := p) (N := N) K u
        rw [cyclotomicUnitPowerQuotientEquiv_mk, cyclotomicUnitEquiv_one_apply]
      map_mul' := by
        intro a b
        ext x
        refine QuotientGroup.induction_on x ?_
        intro u
        change cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K (a * b)
            (cyclotomicUnitPowerClass (p := p) (N := N) K u) =
          cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K a
            (cyclotomicUnitPowerQuotientEquiv (p := p) (N := N) K b
              (cyclotomicUnitPowerClass (p := p) (N := N) K u))
        rw [cyclotomicUnitPowerQuotientEquiv_mk, cyclotomicUnitPowerQuotientEquiv_mk,
          cyclotomicUnitPowerQuotientEquiv_mk, cyclotomicUnitEquiv_mul_apply] }

/-- The actual `Delta` action on `E/E^p`. -/
noncomputable abbrev cyclotomicUnitModPDeltaAction :
    CyclotomicUnitQuotientDeltaAction (p := p) (N := 1) K :=
  cyclotomicUnitPowerQuotientDeltaAction (p := p) (N := 1) K

@[simp]
theorem cyclotomicUnitPowerQuotientDeltaAction_act_mk
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    (cyclotomicUnitPowerQuotientDeltaAction (p := p) (N := N) K).act a
        (cyclotomicUnitPowerClass (p := p) (N := N) K u) =
      cyclotomicUnitPowerClass (p := p) (N := N) K
        (cyclotomicUnitEquiv (p := p) K a u) :=
  rfl

end BernoulliRegular

end
