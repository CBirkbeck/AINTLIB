module

public import BernoulliRegular.Reflection.ClassGroupModP.AtomC
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace

/-!
# Plus-side fixed-point chain: σ_{-1} fixes the K⁺-image (Atom C, irregular case)

This file constructs the substantive plus-side fixed-point chain for
Atom C in the irregular prime case. The key identification:

* `σ_{-1}` (the cyclotomic Galois action at `-1 ∈ (ZMod p)ˣ`) acts as
  complex conjugation on `K = ℚ(ζ_p)`.
* Complex conjugation fixes elements of `(NumberField.maximalRealSubfield K)`.
* Hence `σ_{-1}` fixes the image of
  `algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)`.

This is the substantive ingredient saying that the plus part of `Cl(K)/p`
(= image of `Cl((NumberField.maximalRealSubfield K))`) lies in the +1
eigenspace of `σ_{-1}` acting on `Additive (ClassGroupModP K p)`.

## The chain (each level proved here)

1. K-level: `cyclotomicSigmaOfUnit_neg_one_apply_algebraMap_K`
2. 𝓞 K-level (smul form): `cyclotomicSigmaOfUnit_neg_one_smul_algebraMap`
3. 𝓞 K-level (RingEquiv form): `cyclotomicRingOfIntegersEquiv_neg_one_apply_algebraMap`
4. Ideal level: `cyclotomicGaloisConjugate_neg_one_extended_ideal`
5. Class level (mk0): `cyclotomicGaloisShiftedClass_neg_one_extended_class`
6. ClassGroup level: `cyclotomicGalActionMonoidHom_neg_one_classGroupMap`
7. ClassGroupModP level: `cyclotomicGalActionMonoidHomModP_neg_one_classGroupMap`
8. Additive(ClassGroupModP) level: `cyclotomicGalActionInstance_neg_one_classGroupMap`

## Remaining work for `PlusMinusIdentification`

The full `PlusMinusIdentification p K` structure additionally requires:

* **Plus-side non-triviality**: `(p ∣ hPlus K) ⟹ ∃ even i, eigenspace V_i ≠ 0`.
  Beyond what is proved here, this needs the eigenspace decomposition via
  characters of `(ZMod p)ˣ` (not just complex conjugation). The naive map
  `Cl(K⁺) → ClassGroupModP K p` can be zero even when both groups are
  non-trivial; the Spiegelungssatz argument uses the FULL `(ZMod p)ˣ`-eigenspace
  decomposition + REF-25.

* **Minus-side identification**: `(∃ odd j, V_j ≠ 0) ⟹ (p ∣ hMinus K)`.
  Requires the analogous chain for the minus part of `Cl(K)`.

* **Reflection identity** (`eigenspace_reflection`): the REF-25 statement
  bridging eigenspaces V_i ↔ V_{p-i} via the residue-symbol pairing.

The infrastructure here is the substantive +1-fixed-point content of the
plus-side argument; it isolates exactly what σ_{-1} = complex conjugation
contributes to the reflection chain.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BernoulliRegular

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

variable (hp_odd : p ≠ 2)

include hp_odd in
omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- `2 < p` follows from `p` prime and `p ≠ 2`. -/
private theorem hp_gt_two_of_ne_two : 2 < p := by
  rcases (Fact.out : p.Prime).two_le.lt_or_eq with h | h
  · exact h
  · exact (hp_odd h.symm).elim

include hp_odd in
/-- **σ_{-1} fixes elements of `K⁺` in `K`**: complex conjugation fixes
`(NumberField.maximalRealSubfield K) ⊂ K`. This is the K-level statement. -/
theorem cyclotomicSigmaOfUnit_neg_one_apply_algebraMap_K
    (z : NumberField.maximalRealSubfield K) :
    cyclotomicSigmaOfUnit (p := p) K (-1)
        ((algebraMap (NumberField.maximalRealSubfield K) K) z) =
      (algebraMap (NumberField.maximalRealSubfield K) K) z := by
  have hp_gt_two : 2 < p := hp_gt_two_of_ne_two hp_odd
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]
  -- Reduce to applying complex conjugation as a ring equiv.
  change ((cyclotomicComplexConjGal (p := p) K hp_gt_two).toRingHom)
      ((algebraMap (NumberField.maximalRealSubfield K) K) z) =
    (algebraMap (NumberField.maximalRealSubfield K) K) z
  -- cyclotomicComplexConjGal has the same underlying ring map as complexConj K.
  have hsame : (cyclotomicComplexConjGal (p := p) K hp_gt_two).toRingHom
      ((algebraMap (NumberField.maximalRealSubfield K) K) z) =
      NumberField.IsCMField.complexConj K
        ((algebraMap (NumberField.maximalRealSubfield K) K) z) := rfl
  rw [hsame]
  -- complexConj K (algebraMap K⁺ K z) = algebraMap K⁺ K z by commutes'.
  exact NumberField.IsCMField.complexConj_apply_eq_self (K := K) z

include hp_odd in
/-- **σ_{-1} fixes algebraMap-image at the ring-of-integers level**. -/
theorem cyclotomicSigmaOfUnit_neg_one_smul_algebraMap
    (y : 𝓞 (NumberField.maximalRealSubfield K)) :
    cyclotomicSigmaOfUnit (p := p) K (-1) •
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y := by
  apply Subtype.ext
  -- The action on 𝓞 K via Gal(K/ℚ) at the K-coercion level.
  change ((cyclotomicSigmaOfUnit (p := p) K (-1) : K → K)
      ((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y : 𝓞 K) : K)) =
    (((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y : 𝓞 K) : K))
  -- Lift the algebraMap through the IsScalarTower.
  have h_tower :
      (((algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y : 𝓞 K) : K)) =
      (algebraMap (NumberField.maximalRealSubfield K) K)
        ((algebraMap (𝓞 (NumberField.maximalRealSubfield K))
          (NumberField.maximalRealSubfield K) y)) := by
    rw [← IsScalarTower.algebraMap_apply
      (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K]
    rw [IsScalarTower.algebraMap_apply
      (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) K]
  rw [h_tower]
  exact cyclotomicSigmaOfUnit_neg_one_apply_algebraMap_K hp_odd _

include hp_odd in
/-- **σ_{-1} fixes algebraMap-image** for `cyclotomicRingOfIntegersEquiv`. -/
theorem cyclotomicRingOfIntegersEquiv_neg_one_apply_algebraMap
    (y : 𝓞 (NumberField.maximalRealSubfield K)) :
    cyclotomicRingOfIntegersEquiv (p := p) K (-1)
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y) =
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y := by
  change cyclotomicSigmaOfUnit (p := p) K (-1) •
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y) =
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y
  exact cyclotomicSigmaOfUnit_neg_one_smul_algebraMap hp_odd y

/-! ### Lift to the ideal level -/

include hp_odd in
/-- **σ_{-1} fixes K⁺-extension ideals**: the σ_{-1} Galois conjugate of an
ideal extended from the totally real subfield's ring of integers is the
same ideal. -/
theorem cyclotomicGaloisConjugate_neg_one_extended_ideal
    (qPlus : Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) (-1)
        (Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) qPlus) =
      Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) qPlus := by
  unfold Furtwaengler.cyclotomicGaloisConjugate
  -- Cast both maps to RingHom for `Ideal.map_map`.
  rw [← Ideal.map_coe (cyclotomicRingOfIntegersEquiv (p := p) K (-1))
        (qPlus.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))),
    Ideal.map_map]
  -- The composite ring hom equals the algebraMap on values.
  congr 1
  apply RingHom.ext
  intro y
  exact cyclotomicRingOfIntegersEquiv_neg_one_apply_algebraMap hp_odd y

/-! ### Lift to the class group level -/

include hp_odd in
/-- **σ_{-1} fixes K⁺-extension classes (mk0)**: the cyclotomic Galois shifted
class of an extension ideal equals the original class. -/
theorem cyclotomicGaloisShiftedClass_neg_one_extended_class
    (qPlus : (Ideal (𝓞 (NumberField.maximalRealSubfield K)))⁰) :
    cyclotomicGaloisShiftedClass (p := p) (K := K) (-1)
      ⟨Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) qPlus.val,
       by
         rw [mem_nonZeroDivisors_iff_ne_zero]
         intro h
         exact (mem_nonZeroDivisors_iff_ne_zero.mp qPlus.2) <| (Ideal.map_eq_bot_iff_of_injective
            (FaithfulSMul.algebraMap_injective
              (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).mp h⟩ =
      ClassGroup.mk0
        ⟨Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) qPlus.val,
         by
           rw [mem_nonZeroDivisors_iff_ne_zero]
           intro h
           exact (mem_nonZeroDivisors_iff_ne_zero.mp qPlus.2) <| (Ideal.map_eq_bot_iff_of_injective
              (FaithfulSMul.algebraMap_injective
                (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).mp h⟩ := by
  change ClassGroup.mk0
        ⟨Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) (-1) _, _⟩ =
      ClassGroup.mk0 ⟨_, _⟩
  congr 1
  exact Subtype.ext <| cyclotomicGaloisConjugate_neg_one_extended_ideal hp_odd qPlus.val

/-! ### Lift to the ClassGroup-level (image of classGroupMap) -/

include hp_odd in
/-- **σ_{-1} fixes the image of `classGroupMap`** in `ClassGroup (𝓞 K)`.
This is the substantive translation between the plus part of `Cl(K)`
(= image of `Cl((NumberField.maximalRealSubfield K))`) and the +1
eigenspace of σ_{-1}. -/
theorem cyclotomicGalActionMonoidHom_neg_one_classGroupMap
    (cPlus : ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :
    cyclotomicGalActionMonoidHom (p := p) (K := K) (-1)
        (classGroupMap K cPlus) = classGroupMap K cPlus := by
  -- Pick a representative ideal I⁺ for c⁺.
  obtain ⟨IPlus, hIPlus⟩ := ClassGroup.mk0_surjective cPlus
  rw [← hIPlus]
  -- Use `extensionMap_mk0` to push through the integer ideal form.
  rw [show (classGroupMap K (ClassGroup.mk0 IPlus)) =
      ClassGroup.mk0
        ⟨IPlus.1.map (algebraMap _ (𝓞 K)),
         mem_nonZeroDivisors_iff_ne_zero.mpr <|
           (Ideal.map_eq_bot_iff_of_injective
             (FaithfulSMul.algebraMap_injective
               (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).not.mpr
           (mem_nonZeroDivisors_iff_ne_zero.mp IPlus.2)⟩ from
      ClassGroup.extensionMap_mk0 (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) IPlus]
  -- Apply the action via `cyclotomicGalActionMonoidHom`'s coercion.
  change cyclotomicGalActionOnClassGroup (p := p) (K := K) (-1)
        (ClassGroup.mk0 _) = ClassGroup.mk0 _
  rw [cyclotomicGalActionOnClassGroup_mk0]
  exact cyclotomicGaloisShiftedClass_neg_one_extended_class hp_odd IPlus

/-! ### Lift to ClassGroupModP -/

include hp_odd in
/-- **σ_{-1} fixes `QuotientGroup.mk` of classGroupMap-image** in `ClassGroupModP K p`. -/
theorem cyclotomicGalActionMonoidHomModP_neg_one_classGroupMap
    (cPlus : ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :
    cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1)
        (QuotientGroup.mk (classGroupMap K cPlus)) =
      QuotientGroup.mk (classGroupMap K cPlus) := by
  unfold cyclotomicGalActionMonoidHomModP
  rw [QuotientGroup.map_mk]
  rw [cyclotomicGalActionMonoidHom_neg_one_classGroupMap hp_odd cPlus]

include hp_odd in
/-- **σ_{-1} fixes `Additive.ofMul` of mk-classGroupMap-image** in
`Additive (ClassGroupModP K p)`. -/
theorem cyclotomicGalActionInstance_neg_one_classGroupMap
    (cPlus : ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :
    cyclotomicGalActionInstance (p := p) (K := K) (-1)
        (Additive.ofMul (QuotientGroup.mk (classGroupMap K cPlus) :
            ClassGroupModP K p)) =
      Additive.ofMul (QuotientGroup.mk (classGroupMap K cPlus) : ClassGroupModP K p) := by
  change Additive.ofMul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) (-1)
    (QuotientGroup.mk (classGroupMap K cPlus))) =
    Additive.ofMul (QuotientGroup.mk (classGroupMap K cPlus) : ClassGroupModP K p)
  rw [cyclotomicGalActionMonoidHomModP_neg_one_classGroupMap hp_odd cPlus]

/-! ### Plus-side eigenspace membership (Diekmann Lemma 4.1 connection)

The image of `classGroupMap` in `Additive (ClassGroupModP K p)` is fixed by
`σ_{-1}`. Equivalently, it lies in the kernel of `σ_{-1} - id`, which is
the +1 eigenspace of `σ_{-1}` and decomposes as the sum of all
even-character eigenspaces (`⊕_{i even} V_i`).

This lemma packages the proven content as a fixed-point statement at the
linearised level, ready for downstream consumption by REF-25 and the
plus-side argument. -/

include hp_odd in
/-- **σ_{-1} - id annihilates the classGroupMap image**: the linearised
form of the fixed-point statement. -/
theorem cyclotomicGalActionInstance_sub_one_classGroupMap_eq_zero
    (cPlus : ClassGroup (𝓞 (NumberField.maximalRealSubfield K))) :
    (cyclotomicGalActionInstance (p := p) (K := K) (-1) -
        (1 : Module.End (ZMod p) (Additive (ClassGroupModP K p))))
      (Additive.ofMul (QuotientGroup.mk (classGroupMap K cPlus) :
          ClassGroupModP K p)) = 0 := by
  rw [LinearMap.sub_apply]
  rw [cyclotomicGalActionInstance_neg_one_classGroupMap hp_odd cPlus]
  simp

end BernoulliRegular

end
