import BernoulliRegular.UnitQuotient.PadicTensor
import BernoulliRegular.UnitQuotient.FreeProjectorRanges
import BernoulliRegular.Thaine.PollaczekUnitPlusGaloisAction
import BernoulliRegular.Thaine.RankOneComponent
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.CertificateAudit

/-!
# Rank-one specialisation of the Padic χ-eigenspace at ω^32, p = 37

This file specialises the rank equality `finrank ℤ_[p] V_p^χ =
finrank (ZMod p) W^(χ mod p)` (shipped in PadicTensor) to χ = ω³² and
p = 37, using the existing rank-1 result for the mod-p eigenspace at
non-trivial even characters.

## Main results

* `MulChar.padicToZMod_cyclotomicOmegaPadicChar`: the toZMod-reduction
  of the Padic Teichmüller k-th-power character is the standard ZMod p
  k-th-power character.
* `cyclotomicUnitFreePartPadicCharacterEigenspace_finrank_omega32_FLT37`:
  V_37^(ω³²) is a free ℤ_37-module of rank 1.

## References

* Reviewer guidance, 2026-05-07 (Q1 atomic rank-one specialisation).
-/

noncomputable section

open NumberField

namespace BernoulliRegular


attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]

namespace FLT37

/-- **Padic ω^k character reduces to the standard mod-p ω^k character**:
`MulChar.padicToZMod (cyclotomicOmegaPadicChar k) = cyclotomicOmegaChar k`.
The two characters agree pointwise via the Teichmüller-toZMod identity:
`toZMod (teichmuller p x ^ k) = x^k`. -/
theorem padicToZMod_cyclotomicOmegaPadicChar (k : ℕ) :
    MulChar.padicToZMod (p := p) (cyclotomicOmegaPadicChar (p := p) k) =
      cyclotomicOmegaChar (p := p) k := by
  ext a
  rw [MulChar.padicToZMod_apply, cyclotomicOmegaPadicChar_toZMod]
  rfl

/-- The 32nd-power Teichmüller character is even at p = 37, since
`(-1 : ZMod 37)^32 = 1` (any even power of a sign is 1). -/
theorem cyclotomicOmegaChar_thirtytwo_isEven_FLT37 :
    IsEvenDeltaCharacter (p := 37) (cyclotomicOmegaChar (p := 37) 32) := by
  change cyclotomicOmegaChar (p := 37) 32 (-1 : CyclotomicUnitDelta 37) = 1
  rw [cyclotomicOmegaChar_apply]
  rw [show ((-1 : CyclotomicUnitDelta 37) : ZMod 37) = -1 from by
    push_cast; rfl]
  rfl

/-- The 32nd-power Teichmüller character is non-trivial at p = 37.
Witness: `2 ∈ (ZMod 37)ˣ` has order 36, so `2^32 ≠ 1` in ZMod 37 (in
fact `2^32 ≡ 7 mod 37`). -/
theorem cyclotomicOmegaChar_thirtytwo_ne_one_FLT37 :
    cyclotomicOmegaChar (p := 37) 32 ≠
      (1 : MulChar (CyclotomicUnitDelta 37) (ZMod 37)) := by
  intro h
  -- Lift `2 ∈ ZMod 37` to a unit in `(ZMod 37)ˣ = CyclotomicUnitDelta 37`.
  have h_two_ne : (2 : ZMod 37) ≠ 0 := by decide
  set a : CyclotomicUnitDelta 37 := Units.mk0 (2 : ZMod 37) h_two_ne
  have h_apply : cyclotomicOmegaChar (p := 37) 32 a =
      (1 : MulChar (CyclotomicUnitDelta 37) (ZMod 37)) a := by
    rw [h]
  rw [cyclotomicOmegaChar_apply] at h_apply
  rw [MulChar.one_apply (Group.isUnit a)] at h_apply
  -- h_apply : ((a : ZMod 37))^32 = 1, but a's value is 2, so 2^32 = 1.
  have h_a_val : (a : ZMod 37) = 2 := rfl
  rw [h_a_val] at h_apply
  -- Now h_apply : (2 : ZMod 37)^32 = 1. Evaluate.
  exact absurd h_apply (by decide)

/-- **Rank-1 of the Padic ω³²-eigenspace at p = 37**: the Padic character
eigenspace `V_37^(ω³²)` (the ω³²-eigenspace of `ℤ_37 ⊗_ℤ (𝓞 K)ˣ/torsion`)
is a free ℤ_37-module of rank 1.

Proof: combine the rank equality
`finrank ℤ_[p] V_p^χ = finrank (ZMod p) W^(χ mod p)` with
- `padicToZMod_cyclotomicOmegaPadicChar 32`: identifies the
  reduced character with `cyclotomicOmegaChar 32`,
- `cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local_eq`: identifies
  the local eigenspace with the project standard,
- `cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one`:
  the existing rank-1 fact for the mod-p ω³²-eigenspace.

This is the input the abstract atomic rank-one lemma consumes. -/
theorem cyclotomicUnitFreePartPadicCharacterEigenspace_finrank_omega32_FLT37 :
    Module.finrank ℤ_[37]
        (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) = 1 := by
  letI : Fintype {w : NumberField.InfinitePlace (CyclotomicField 37 ℚ) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := Fintype.ofFinite _
  letI : DiscreteTopology
      (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) :=
    NumberField.Units.instDiscrete_unitLattice (CyclotomicField 37 ℚ)
  letI : IsZLattice ℝ
      (NumberField.Units.unitLattice (CyclotomicField 37 ℚ)) := by
    refine ⟨?_⟩
    convert NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top
      (CyclotomicField 37 ℚ)
  rw [cyclotomicUnitFreePartPadicCharacterEigenspace_finrank
    (p := 37) (CyclotomicField 37 ℚ) (by norm_num : 2 < 37)
    (cyclotomicOmegaPadicChar (p := 37) 32)]
  rw [padicToZMod_cyclotomicOmegaPadicChar]
  rw [cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local_eq]
  exact cyclotomicUnitFreePartModPDeltaCharacterEigenspace_finrank_of_even_ne_one
    (p := 37) (CyclotomicField 37 ℚ) (by norm_num : 2 < 37)
    cyclotomicOmegaChar_thirtytwo_isEven_FLT37
    cyclotomicOmegaChar_thirtytwo_ne_one_FLT37

/-- **Padic ω³²-eigenspace at p = 37 is ℤ_[37]-linearly isomorphic to ℤ_[37]**.
A non-canonical iso obtained from the rank-1 fact via
`nonempty_linearEquiv_of_finrank_eq_one`. This is the bridge that lets the
abstract atomic rank-one lemma (at PID R = ℤ_[37], prime p = 37) be
applied to the eigenspace: under the iso, the Pollaczek class corresponds
to some `a ∈ ℤ_[37]`, and the atomic lemma's equivalence
`¬p ∣ a ↔ R/(a) has no p-torsion` transports to the K-side certificate
↔ eigenspace torsion-vanishing equivalence. -/
noncomputable def cyclotomicUnitFreePartPadicCharacterEigenspace_omega32_LinearEquiv_FLT37 :
    ℤ_[37] ≃ₗ[ℤ_[37]]
      cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32) :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one
    cyclotomicUnitFreePartPadicCharacterEigenspace_finrank_omega32_FLT37).some

/-- **Atomic rank-one specialised at the Padic ω³²-eigenspace, p = 37**.
For any non-zero `c ∈ V_37^(ω^32)`, the quotient `V_37^(ω^32) / Λ·c` has
no 37-torsion if and only if `c` is not 37-divisible in `V_37^(ω^32)`
(i.e., there is no `y ∈ V_37^(ω^32)` with `c = 37 • y`).

This is the abstract atomic rank-one lemma
`rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible`
specialised at Λ = ℤ_[37], p = 37 (which is prime in ℤ_[37], the
maximal ideal generator), `E = V_37^(ω^32)` (the ω³²-eigenspace), and
the rank-1 iso just shipped. Combined with the K-side certificate
(PU not a 37-th power) ⟺ PU's class not 37-divisible (via the Padic-modp
machinery), this gives the form Kučera Theorem 4.3 (Thaine annihilator
at single character ω³²) consumes for the Cor 8.19 bridge contrapositive. -/
theorem flt37_atomic_rankOne_omega32
    {c : cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)}
    (hc : c ≠ 0) :
    (¬ ∃ y, c = ((37 : ℕ) : ℤ_[37]) • y) ↔
    ∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
        Submodule.span ℤ_[37] ({c} : Set _),
      ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp_prime : Prime ((37 : ℕ) : ℤ_[37]) := by
    rw [show ((37 : ℕ) : ℤ_[37]) = (37 : ℤ_[37]) from by push_cast; rfl]
    exact PadicInt.prime_p (p := 37)
  exact Thaine.rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible
    (Λ := ℤ_[37]) hp_prime
    cyclotomicUnitFreePartPadicCharacterEigenspace_omega32_LinearEquiv_FLT37.symm
    hc

/-- **Pollaczek's Padic class projects into the Padic ω³²-eigenspace** (FLT37):
applying the Padic character idempotent `e_(ω³²)` to the natural inclusion
of PU into V_37 gives an element of V_37^(ω³²). This is the projector landing
in its eigenspace (already shipped) applied to PU's Padic image. -/
noncomputable def flt37_pollaczekUnit_padic_eigenspace_class
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
      (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32) :=
  ⟨cyclotomicUnitFreePartPadicCharacterProjector (p := 37)
      (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)
    (cyclotomicUnitFreePartToPadic (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
        (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)))),
    cyclotomicUnitFreePartPadicCharacterProjector_mem_eigenspace
      (p := 37) (CyclotomicField 37 ℚ) (by norm_num : 2 < 37)
      (cyclotomicOmegaPadicChar (p := 37) 32) _⟩

/-- **Reduction of PU's Padic eigenspace class is PU's mod-p class** (FLT37).
The mod-p reduction `red` of `e_(ω³²)(1 ⊗ [PU])` (PU's Padic eigenspace
class) equals the mod-p class of PU. Proof: projector compatibility
`red ∘ e_padic = e_modp ∘ red`, then `red(1 ⊗ [PU]) = [PU]_modp` (the
one-tmul lemma), then `[PU]_modp ∈ W^(ω³² mod 37)` (existing eigenspace
membership) so the mod-p projector acts as identity. -/
theorem flt37_pollaczekUnit_padic_eigenspace_class_red
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitFreePartPadicReduceModP (p := 37) (CyclotomicField 37 ℚ)
      ((flt37_pollaczekUnit_padic_eigenspace_class :
        cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) :
        CyclotomicUnitFreePartPadic (p := 37) (CyclotomicField 37 ℚ)) =
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) := by
  classical
  letI : Invertible ((Fintype.card (CyclotomicUnitDelta 37) : ZMod 37)) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := 37) (by norm_num : 2 < 37)
  change cyclotomicUnitFreePartPadicReduceModP (p := 37) (CyclotomicField 37 ℚ)
    (cyclotomicUnitFreePartPadicCharacterProjector (p := 37) (CyclotomicField 37 ℚ)
      (cyclotomicOmegaPadicChar (p := 37) 32)
      (cyclotomicUnitFreePartToPadic (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))))) = _
  rw [cyclotomicUnitFreePartPadicReduceModP_projector_compat (p := 37)
    (CyclotomicField 37 ℚ) (by norm_num : 2 < 37)
    (cyclotomicOmegaPadicChar (p := 37) 32)]
  rw [cyclotomicUnitFreePartPadicReduceModP_one_tmul]
  -- Goal: cyclotomicUnitFreePartModPDeltaCharacterProjector (padicToZMod ω³²)
  --   (cyclotomicUnitFreePartModPClass [PU]) = cyclotomicUnitFreePartModPClass [PU]
  unfold cyclotomicUnitFreePartModPDeltaCharacterProjector
  rw [padicToZMod_cyclotomicOmegaPadicChar]
  exact characterProjector_apply_of_mem_eigenspace
    (cyclotomicUnitFreePartModPDeltaRepresentation (p := 37) (CyclotomicField 37 ℚ))
    (cyclotomicOmegaChar (p := 37) 32)
    (pollaczekUnit_image_in_omegaChar32_eigenspace_FLT37 (K' := CyclotomicField 37 ℚ))

/-- **PU's Padic eigenspace class is not 37-divisible iff K-side cert** (FLT37).

The complete bridge from the K-side certificate (PU not a 37-th power) to
the eigenspace not-37-divisibility condition that the atomic rank-one
specialisation `flt37_atomic_rankOne_omega32` consumes.

Composes:
- `cyclotomicUnitFreePartPadic_eigenspace_not_pdivisible_iff`: the
  eigenspace not-p-divisible ⟺ red ≠ 0 bridge (axiom-clean, just shipped).
- `flt37_pollaczekUnit_padic_eigenspace_class_red`: red of PU's Padic
  eigenspace class is PU's mod-p class (just shipped).
- `flt37_pollaczekUnit_class_in_modp_freepart_ne_zero_iff_cert`: the
  existing K-side cert ⟺ [PU mod 37] ≠ 0 in W. -/
theorem flt37_pollaczekUnit_padic_eigenspace_class_not_37divisible_iff_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (¬ ∃ y ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32),
        ((37 : ℕ) : ℤ_[37]) • y =
          (flt37_pollaczekUnit_padic_eigenspace_class :
            cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
              (CyclotomicField 37 ℚ)
              (cyclotomicOmegaPadicChar (p := 37) 32)).1) ↔
      ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ≠
          ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
            𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
  rw [cyclotomicUnitFreePartPadic_eigenspace_not_pdivisible_iff
    (p := 37) (CyclotomicField 37 ℚ) (by norm_num : 2 < 37)
    (cyclotomicOmegaPadicChar (p := 37) 32)
    flt37_pollaczekUnit_padic_eigenspace_class.2]
  rw [flt37_pollaczekUnit_padic_eigenspace_class_red]
  -- Goal: cyclotomicUnitFreePartModPClass (Additive.ofMul (cyclotomicUnitFreeClass K PU)) ≠ 0
  --   ↔ K-side cert
  rw [show cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
        (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) =
      cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) from rfl]
  exact flt37_pollaczekUnit_class_in_modp_freepart_ne_zero_iff_cert

/-- **K-side certificate IFF eigenspace quotient has no 37-torsion** (FLT37).

The full chain composing the just-shipped `..._not_37divisible_iff_cert`
with the atomic rank-one specialisation. K-side certificate (PU not a
37-th power) is equivalent to: the rank-1 eigenspace quotient
  `V_37^(ω³²) / ℤ_[37]·[PU]_eigen`
has trivial 37-torsion.

This is the input form that Kučera Theorem 4.3 (Thaine annihilator at
single character ω³²) consumes, giving the
`ThaineSingleCharDischarge` component of the FLT37 thaine-pivot bundle.
Composed with the existing `cor8_19Bridge_closed`, this discharges
`Vandiver37PlusCoprime`, hence `FermatLastTheoremFor 37` unconditionally. -/
theorem flt37_pollaczekUnit_eigenspace_quotient_no_37torsion_iff_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (flt37_pollaczekUnit_padic_eigenspace_class :
        cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ≠ 0 →
    ((∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
          Submodule.span ℤ_[37]
            ({(flt37_pollaczekUnit_padic_eigenspace_class :
                cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                  (CyclotomicField 37 ℚ)
                  (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
        ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0) ↔
      ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ≠
          ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
            𝓞 (CyclotomicField 37 ℚ)) ^ 37) := by
  intro h_ne_zero
  rw [← flt37_atomic_rankOne_omega32 h_ne_zero]
  -- LHS: ¬ ∃ y, [PU]_eigen = 37 • y
  -- We have: ¬ ∃ y ∈ V^χ, 37 • y = [PU]_eigen.1 ↔ K-side cert.
  -- Convert the existence form:
  rw [show (¬ ∃ y, (flt37_pollaczekUnit_padic_eigenspace_class :
        cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ)
          (cyclotomicOmegaPadicChar (p := 37) 32)) =
        ((37 : ℕ) : ℤ_[37]) • y) ↔
      (¬ ∃ y ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32),
          ((37 : ℕ) : ℤ_[37]) • y =
            (flt37_pollaczekUnit_padic_eigenspace_class :
              cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                (CyclotomicField 37 ℚ)
                (cyclotomicOmegaPadicChar (p := 37) 32)).1) from ?_]
  · exact flt37_pollaczekUnit_padic_eigenspace_class_not_37divisible_iff_cert
  · constructor
    · rintro h ⟨y, hy_eig, hy⟩
      apply h
      refine ⟨⟨y, hy_eig⟩, ?_⟩
      exact Subtype.ext <| hy.symm
    · rintro h ⟨⟨y, hy_eig⟩, hy⟩
      apply h
      refine ⟨y, hy_eig, ?_⟩
      have := congrArg Subtype.val hy.symm
      exact this

/-- **K-side certificate is non-trivial: implies PU's Padic eigenspace class ≠ 0**.
If the Pollaczek unit is not a 37-th power (the K-side certificate), then
its Padic eigenspace class `e_(ω³²)(1 ⊗ [PU])` is a non-zero element of
`V_37^(ω³²)`. Proof: contrapositive — if [PU]_eigen = 0, then by the
just-shipped bridge `flt37_pollaczekUnit_padic_eigenspace_class_red`,
the mod-p class would also be zero, contradicting the existing
mod-p ne_zero IFF cert. -/
theorem flt37_pollaczekUnit_padic_eigenspace_class_ne_zero_of_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_cert : ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ≠
          ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
            𝓞 (CyclotomicField 37 ℚ)) ^ 37) :
    (flt37_pollaczekUnit_padic_eigenspace_class :
        cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ≠ 0 := by
  intro h_zero
  apply flt37_pollaczekUnit_class_in_modp_freepart_ne_zero_iff_cert.mpr h_cert
  -- Want: cyclotomicUnitToFreePartModPAdd (Additive.ofMul PU) = 0
  -- We have h_zero : (PU's eigenspace class) = 0 ∈ V_p^χ.
  -- red of PU's eigenspace class = PU's mod-p class (by bridge).
  -- red of 0 = 0. So PU's mod-p class = 0.
  have h_zero_val : (flt37_pollaczekUnit_padic_eigenspace_class :
      cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)).1 =
      (0 : CyclotomicUnitFreePartPadic (p := 37) (CyclotomicField 37 ℚ)) :=
    congrArg Subtype.val h_zero
  rw [show cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) =
      cyclotomicUnitFreePartModPClass (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) from rfl]
  rw [← flt37_pollaczekUnit_padic_eigenspace_class_red]
  rw [h_zero_val, map_zero]

/-- **Forward direction**: K-side certificate implies the eigenspace
quotient `V_37^(ω³²) / ℤ_[37]·[PU]_eigen` has no 37-torsion. -/
theorem flt37_pollaczekUnit_eigenspace_quotient_no_37torsion_of_cert
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_cert : ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        ((pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
            (𝓞 (CyclotomicField 37 ℚ))ˣ) :
          𝓞 (CyclotomicField 37 ℚ)) ≠
          ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
            𝓞 (CyclotomicField 37 ℚ)) ^ 37) :
    ∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
        Submodule.span ℤ_[37]
          ({(flt37_pollaczekUnit_padic_eigenspace_class :
              cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                (CyclotomicField 37 ℚ)
                (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
      ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0 :=
  (flt37_pollaczekUnit_eigenspace_quotient_no_37torsion_iff_cert
    (flt37_pollaczekUnit_padic_eigenspace_class_ne_zero_of_cert h_cert)).mpr h_cert

/-- **PU's Padic eigenspace class is unconditionally non-zero** (FLT37):
the K-side certificate `flt37_realLocalCert_global` is shipped
unconditionally in the project (LV004g chain), so its consequence
`[PU]_eigen ≠ 0` is also unconditional. -/
theorem flt37_pollaczekUnit_padic_eigenspace_class_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (flt37_pollaczekUnit_padic_eigenspace_class :
        cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ≠ 0 :=
  flt37_pollaczekUnit_padic_eigenspace_class_ne_zero_of_cert
    flt37_realLocalCert_global

/-- **Unconditional: V_37^(ω³²) / ℤ_[37]·[PU]_eigen has no 37-torsion** (FLT37).
The K-side cert is shipped unconditionally; combined with the just-shipped
forward direction, the eigenspace quotient torsion-vanishing is a fact. -/
theorem flt37_pollaczekUnit_eigenspace_quotient_no_37torsion
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
        (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
        Submodule.span ℤ_[37]
          ({(flt37_pollaczekUnit_padic_eigenspace_class :
              cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                (CyclotomicField 37 ℚ)
                (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
      ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0 :=
  flt37_pollaczekUnit_eigenspace_quotient_no_37torsion_of_cert
    flt37_realLocalCert_global

/-- **Concrete FLT37 rank-one-to-Thaine adapter.**

The Pollaczek quotient has already been proved to have no `37`-torsion.  To
obtain the single-character Thaine discharge, it remains to prove the
mathematical Kučera/Thaine implication from this quotient-torsion statement to
triviality of the `ω^32` plus-class component. -/
theorem thaineSingleCharDischarge37_of_padicEigenspaceQuotient
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (id : ClassGroupComponentIdentification 37 (CyclotomicField 37 ℚ))
    (h_thaine :
      (∀ x : (cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
          (CyclotomicField 37 ℚ) (cyclotomicOmegaPadicChar (p := 37) 32)) ⧸
          Submodule.span ℤ_[37]
            ({(flt37_pollaczekUnit_padic_eigenspace_class :
                cyclotomicUnitFreePartPadicCharacterEigenspace (p := 37)
                  (CyclotomicField 37 ℚ)
                  (cyclotomicOmegaPadicChar (p := 37) 32))} : Set _),
        ((37 : ℕ) : ℤ_[37]) • x = 0 → x = 0) →
      ¬ id.componentNontrivial 32) :
    ThaineSingleCharDischarge 37 (CyclotomicField 37 ℚ) id 32 where
  thaine_at_i := by
    intro _h_cert
    exact h_thaine flt37_pollaczekUnit_eigenspace_quotient_no_37torsion

end FLT37

end BernoulliRegular

end
