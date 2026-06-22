import BernoulliRegular.Thaine.PollaczekUnitPlusGaloisAction.GaloisActionDecompositionAndEigenspace
import BernoulliRegular.Thaine.UnitsComplexConjBridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CharacterIdentification
import BernoulliRegular.UnitQuotient.ModPReduction
import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ModPRepresentation
import BernoulliRegular.UnitQuotient.FreeLatticeComparison.Eigenspaces
import BernoulliRegular.UnitQuotient.GlobalUnitDimension
import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37Closure
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.PthPowerLift
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.CertificateAudit

/-!
# T-EIG-B1: Structural decomposition of σ_a • pollaczekUnitPlus

For the σ-symmetric `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`,
the Galois action by `σ_a := cyclotomicSigmaOfUnit p K a` decomposes:

   `σ_a • pollaczekUnitPlus = (σ_a • pollaczekUnit) · (σ_{-a} • pollaczekUnit)`

Combined with the existing `cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue`
(in `KummerLift/CharacterIdentification.lean`), this provides the σ_a-eigenvalue
chain for pollaczekUnitPlus needed for the rank-one Pollaczek specialisation.

## Sources

* T-EIG-B0 bridge `unitsComplexConj_val_eq_cyclotomicSigmaOfUnit_neg_one_smul`.
* Project's `cyclotomicSigmaOfUnit_mul` (composition law).
* Project's `pollaczekUnitPlus` definition.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]


/-- **PUP image in mod-p free part is non-zero (multiplicative form)**:
the image of `[PUP]_{E/E^37}` under the canonical map to mod-p free part
is not the identity. -/
theorem flt37_pollaczekUnitPlus_class_in_powerQuotient_freepart_ne_one
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitPowerQuotientToFreePartModP (p := 37) (CyclotomicField 37 ℚ)
        (cyclotomicUnitPowerClass (p := 37) (N := 1) (CyclotomicField 37 ℚ)
          (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) ≠ 1 := by
  intro h_eq
  apply flt37_pollaczekUnitPlus_class_not_mem_torsion_powerClassSubgroup
  rw [← cyclotomicUnitPowerQuotientToFreePartModP_ker (p := 37) (K := CyclotomicField 37 ℚ)]
  exact h_eq

/-- **PUP image in mod-p free part is non-zero (additive form)**: the
class of `pollaczekUnitPlus` in `CyclotomicUnitFreePartModP` is non-zero. -/
theorem flt37_pollaczekUnitPlus_class_in_modp_freepart_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) ≠ 0 := by
  intro h_eq
  apply flt37_pollaczekUnitPlus_class_in_powerQuotient_freepart_ne_one
  -- The composite `cyclotomicUnitPowerQuotientToFreePartModP ∘ cyclotomicUnitPowerClass`
  -- equals `cyclotomicUnitToFreePartModPMul`, which is
  -- `Multiplicative.ofAdd ∘ cyclotomicUnitToFreePartModPAdd ∘ Additive.ofMul`.
  rw [cyclotomicUnitPowerQuotientToFreePartModP_apply_class]
  -- Goal: Multiplicative.ofAdd
  --   (cyclotomicUnitFreePartModPClass K (Additive.ofMul (cyclotomicUnitFreeClass K PUP))) = 1.
  -- That's `Multiplicative.ofAdd 0 = 1`, which holds when the inner = 0.
  -- The inner is `cyclotomicUnitToFreePartModPAdd K (Additive.ofMul PUP)` by definition.
  change Multiplicative.ofAdd
      (cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32))) = 1
  rw [h_eq]
  rfl

/-- **PUP additive class in mod-p free part equals `2 • PU` class**.

`pollaczekUnitPlus = pollaczekUnit · unitsComplexConj K (pollaczekUnit)`.
Mapping to `CyclotomicUnitFreePartModP`, both factors give the same class
(σ_{-1} acts trivially on the free part). Hence `[PUP] = 2 · [PU]` additively. -/
theorem pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K]
    [hp37 : Fact (Nat.Prime 37)]
    [NumberField.IsCMField K] :
    cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnitPlus 37 K 32)) =
      (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K 32)) := by
  unfold pollaczekUnitPlus
  rw [ofMul_mul]
  rw [map_add]
  -- Goal: ... K (ofMul PU) + ... K (ofMul (unitsComplexConj K PU)) = 2 • ... K (ofMul PU).
  -- Show that ... K (ofMul (unitsComplexConj K PU)) = ... K (ofMul PU) via free-class invariance.
  rw [show cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (NumberField.IsCMField.unitsComplexConj K (pollaczekUnit 37 K 32))) =
      cyclotomicUnitToFreePartModPAdd (p := 37) K
        (Additive.ofMul (pollaczekUnit 37 K 32)) from ?_]
  · rw [two_smul]
  · -- Use cyclotomicUnitFreePart_unitsComplexConj_eq, which gives equality of
    -- the free classes after complex conjugation. Then mod-p reduction gives equality.
    rw [cyclotomicUnitToFreePartModPAdd_apply, cyclotomicUnitToFreePartModPAdd_apply]
    have hp_two : (2 : ℕ) < 37 := by omega
    -- cyclotomicUnitFreePart_unitsComplexConj_eq says:
    -- ofMul (cyclotomicUnitFreeClass K (cyclotomicUnitsComplexConj K hp_two u)) =
    -- ofMul (cyclotomicUnitFreeClass K u).
    -- and `cyclotomicUnitsComplexConj K hp_two = unitsComplexConj K` definitionally.
    rw [show Additive.ofMul (cyclotomicUnitFreeClass K
            (NumberField.IsCMField.unitsComplexConj K (pollaczekUnit 37 K 32))) =
        Additive.ofMul (cyclotomicUnitFreeClass K (pollaczekUnit 37 K 32)) from
      cyclotomicUnitFreePart_unitsComplexConj_eq (p := 37) (K := K) hp_two _]

/-- **PU additive class in mod-p free part is non-zero (FLT37)**.

From `[PUP]_modp ≠ 0` (cert + realness) and `[PUP]_modp = 2 · [PU]_modp`,
the non-zero claim transfers to `[PU]_modp` via the invertibility of `2` in
`ZMod 37`. -/
theorem flt37_pollaczekUnit_class_in_modp_freepart_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) ≠ 0 := by
  intro h_pu
  -- If [PU]_modp = 0, then [PUP]_modp = 2 · [PU]_modp = 2 · 0 = 0, contradiction.
  apply flt37_pollaczekUnitPlus_class_in_modp_freepart_ne_zero
  rw [pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart]
  rw [h_pu]
  simp

/-- **Cert IFF [PU] non-zero in mod-p free part (FLT37)**.

Forward: if cert holds, [PU] ≠ 0 (shipped via the realness argument).
Reverse: if PUP = α^p in K, then [PUP] = p·[α] = 0 in mod-p free part,
hence [PU] = (1/2)·[PUP] = 0 (since 2 invertible in `ZMod 37`). -/
theorem flt37_pollaczekUnit_class_in_modp_freepart_ne_zero_iff_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) ≠ 0 ↔
      ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ≠
          ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
            𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
  refine ⟨?_, ?_⟩
  · -- [PU] ≠ 0 ⟹ cert: contrapositive — if PUP = α^p, then [PUP] = 0, hence [PU] = 0.
    intro h_PU_ne α h_eq
    apply h_PU_ne
    -- From PUP = α^p (in 𝓞 K), get [PUP]_modp = 0.
    have h_PUP_unit : pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 = α ^ 37 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact h_eq
    have h_PUP_zero :
        cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32)) = 0 := by
      rw [h_PUP_unit]
      -- ofMul (α^p) = p · ofMul α, and the map kills p-th powers.
      have := cyclotomicUnitToFreePartModPMul_pow_eq_one (p := 37)
        (K := CyclotomicField 37 ℚ) α
      exact Multiplicative.ext <| this
    -- [PUP] = 2·[PU], so [PUP] = 0 ⟹ 2·[PU] = 0 ⟹ [PU] = 0 (2 invertible).
    have h_two_PU :
        (2 : ℕ) • cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) = 0 := by
      rw [← pollaczekUnitPlus_class_eq_two_smul_pollaczekUnit_class_in_modp_freepart]
      exact h_PUP_zero
    -- 2 invertible in ZMod 37 ⟹ [PU] = 0.
    set y : CyclotomicUnitFreePartModP (p := 37) (CyclotomicField 37 ℚ) :=
      cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))
    -- Use the existing project pattern: 2 invertible in ZMod 37 via twoInvertibleZModOfPrimeGtTwo.
    letI : Invertible ((2 : ZMod 37)) :=
      twoInvertibleZModOfPrimeGtTwo (p := 37) (by omega)
    have h_two_smul_zmod : ((2 : ZMod 37)) • y = 0 := by
      have h_cast : (((2 : ℕ) : ZMod 37)) • y = ((2 : ℕ) : ℕ) • y :=
        Nat.cast_smul_eq_nsmul (R := ZMod 37) 2 y
      have h_eq : ((2 : ZMod 37)) • y = ((2 : ℕ) : ZMod 37) • y := by norm_cast
      rw [h_eq, h_cast]
      exact h_two_PU
    -- Multiply both sides by ⅟(2 : ZMod 37).
    calc y
        = (1 : ZMod 37) • y := (one_smul _ _).symm
      _ = (⅟(2 : ZMod 37) * (2 : ZMod 37)) • y := by rw [invOf_mul_self]
      _ = ⅟(2 : ZMod 37) • ((2 : ZMod 37) • y) := by rw [mul_smul]
      _ = ⅟(2 : ZMod 37) • (0 : _) := by rw [h_two_smul_zmod]
      _ = 0 := smul_zero _
  · -- cert ⟹ [PU] ≠ 0: shipped.
    intro _
    exact flt37_pollaczekUnit_class_in_modp_freepart_ne_zero

/-- **PU image in ω^32-eigenspace of mod-p free part is non-zero (FLT37)**.

The eigenspace element `⟨[PU]_modp, eigenspace-membership⟩` in
`cyclotomicUnitFreePartModPDeltaCharacterEigenspace K (ω^32)` is non-zero.
The non-zeroness follows from `[PU]_modp ≠ 0` (the underlying element). -/
theorem flt37_pollaczekUnit_image_in_omegaChar32_eigenspace_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (⟨cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
          (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
            (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))),
        pollaczekUnit_image_in_omegaChar32_eigenspace_FLT37⟩ :
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) ≠ 0 := by
  intro h_eq
  apply flt37_pollaczekUnit_class_in_modp_freepart_ne_zero
  -- The Subtype.ext gives the underlying value equality.
  have h_val : cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
        (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) = 0 := by
    have := congrArg Subtype.val h_eq
    exact this
  -- This is the same as `cyclotomicUnitToFreePartModPAdd K (Additive.ofMul PU) = 0`.
  change cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) = 0
  rw [cyclotomicUnitToFreePartModPAdd_apply]
  exact h_val

/-- **ω^32 character is even (FLT37)** — packaged for downstream
eigenspace lemmas requiring `IsEvenDeltaCharacter`. Since `32` is even,
`(-1)^32 = 1`, and the character `ω^32` sends `-1 ↦ 1`. -/
theorem cyclotomicOmegaChar_even_of_even (k : ℕ) (hk : Even k) :
    IsEvenDeltaCharacter (p := p) (cyclotomicOmegaChar (p := p) k) := by
  unfold IsEvenDeltaCharacter
  rw [cyclotomicOmegaChar_apply]
  -- Goal: ((-1 : CyclotomicUnitDelta p) : ZMod p)^k = 1.
  -- (-1 : CyclotomicUnitDelta p) corresponds to (-1 : ZMod p), and (-1)^k = 1 for k even.
  rw [show ((-1 : CyclotomicUnitDelta p) : ZMod p) = -1 from rfl]
  exact hk.neg_one_pow

/-- **ω^32 is non-trivial**: the character `ω^32 : Δ_37 → ZMod 37` differs
from the identity character. Evaluating at the unit `2 ∈ (ZMod 37)ˣ` gives
`2^32 ≠ 1` in `ZMod 37`. -/
theorem cyclotomicOmegaChar_32_ne_one_FLT37 [Fact (Nat.Prime 37)] :
    (cyclotomicOmegaChar (p := 37) 32) ≠
      (1 : MulChar (CyclotomicUnitDelta 37) (ZMod 37)) := by
  intro h
  have h2 : Nat.Coprime 2 37 := by decide
  have h_apply :
      cyclotomicOmegaChar (p := 37) 32
        (ZMod.unitOfCoprime 2 h2 : CyclotomicUnitDelta 37) = (1 : ZMod 37) := by
    rw [h]
    exact MulChar.one_apply (Group.isUnit (ZMod.unitOfCoprime 2 h2))
  rw [cyclotomicOmegaChar_apply, ZMod.coe_unitOfCoprime] at h_apply
  -- h_apply : ((2 : ℕ) : ZMod 37)^32 = 1.  Compute via Nat.cast.
  have h_kernel : ((2 : ℕ) : ZMod 37) ^ 32 = (7 : ZMod 37) := by
    norm_num
    rfl
  rw [h_kernel] at h_apply
  -- h_apply : (7 : ZMod 37) = 1, contradiction via ZMod.val.
  have h_val_eq := congrArg (ZMod.val (n := 37)) h_apply
  -- ZMod.val 7 = 7, ZMod.val 1 = 1, so 7 = 1 in ℕ, contradiction.
  rw [show ZMod.val (7 : ZMod 37) = 7 from rfl,
      show ZMod.val (1 : ZMod 37) = 1 from rfl] at h_val_eq
  exact absurd h_val_eq (by omega)

/-- **PU's image generates the ω^32-eigenspace of mod-p free part (FLT37)**.

The mod-p free part eigenspace at `ω^32` is 1-dimensional (over `ZMod 37`).
PU's image lies in it and is non-zero. Hence it generates the eigenspace.

This is the "non-zero rank-one generator" packaged form. -/
theorem flt37_pollaczekUnit_image_spans_omegaChar32_eigenspace
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    Submodule.span (ZMod 37)
        ({⟨cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
              (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
                (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))),
            pollaczekUnit_image_in_omegaChar32_eigenspace_FLT37⟩} :
          Set (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
            (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32))) = ⊤ := by
  letI : Fintype {w : InfinitePlace (CyclotomicField 37 ℚ) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Fintype.ofFinite _
  letI : DiscreteTopology (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) :=
    NumberField.Units.instDiscrete_unitLattice (CyclotomicField 37 ℚ)
  letI : IsZLattice ℝ (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top (CyclotomicField 37 ℚ)
  have h_finrank :
      Module.finrank (ZMod 37)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaChar (p := 37) 32)) = 1 :=
    cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
      (p := 37) (K := CyclotomicField 37 ℚ) (by omega)
      (cyclotomicOmegaChar_even_of_even (p := 37) 32 (by decide))
      cyclotomicOmegaChar_32_ne_one_FLT37
  exact (finrank_eq_one_iff_of_nonzero _
    flt37_pollaczekUnit_image_in_omegaChar32_eigenspace_ne_zero).mp h_finrank

end FLT37

end BernoulliRegular

end

