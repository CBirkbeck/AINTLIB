module

public import BernoulliRegular.Reflection.ClassGroupModP.PhiResidueChar
public import BernoulliRegular.Reflection.ClassGroupModP.GalAction
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolIdealGaloisAction

/-!
# Phi-Galois compatibility (Atom D bridge for σ-fixed η)

This file builds the bridge from `pthSymbolAtIdeal_canonical_galoisAction_of_fixed`
to the `phi (galAction a v) = (a : ZMod p) * phi v` formula required by Atom D,
specialised to the case where `η` is σ_a-fixed.

## Main theorems

* `phiOnClassGroup_galois_of_fixed`: integer-ideal-rep form on `ClassGroup`.

* `phiOnClassGroupModPLinear_galois_of_fixed_at_mk0`: linearised form on
  `Additive (ClassGroupModP K p)` — the precise shape consumable by
  `EndToEndComposer.EndToEndReflectionAtoms.phi_galois`.

## Atom D status (σ-fixed η case)

* **Galois weight `k = 1`** is the value of `k` produced when `η` is fully
  σ_a-fixed. (More general η — with non-trivial Δ-character — would
  produce different `k`, requiring an additional character-twist argument
  on `pthSymbolAtIdeal_canonical (σ_a^{-1} η) I` vs `... η I`.)

* **Hypothesis-shape**: the substantive theorem requires hypotheses on each
  prime factor of `I` (η ∉ Q, p ∉ Q, Q maximal, p ∣ Nat.card (𝓞 K / Q) − 1).
  These are the standard "good ideal" conditions for the residue symbol.

* **Class-level upgrade**: lifting from "for some good rep `I`" to "for
  all classes `c`" requires a representative-finding argument (avoidance
  + density of primes ℓ ≡ 1 mod p). Project policy precludes Chebotarev,
  so this lift is a separate piece of work using explicit constructive
  avoidance via the per-γ supplier `Ref19PerGammaSupplier`.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Phi-Galois weight 1, integer-rep form** (Atom D for σ_a-fixed η).

For an integer ideal `I` whose prime factors all satisfy the residue
conditions (η ∉ Q, p ∉ Q, Q maximal, p ∣ #(𝓞 K / Q) - 1), and assuming
`σ_a η = η`:

```
phiOnClassGroup h_ref19 (mk0 (σ_a · I)) = (a : ZMod p) * phiOnClassGroup h_ref19 (mk0 I)
```
-/
theorem phiOnClassGroup_galois_of_fixed
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (I : (Ideal (𝓞 K))⁰)
    (hη_in : ∀ Q ∈ normalizedFactors I.val, η ∉ Q)
    (hp_in : ∀ Q ∈ normalizedFactors I.val, (p : 𝓞 K) ∉ Q)
    (hmax : ∀ Q ∈ normalizedFactors I.val, Q.IsMaximal)
    (hdiv : ∀ Q ∈ normalizedFactors I.val,
      p ∣ Nat.card (𝓞 K ⧸ Q) - 1) :
    phiOnClassGroup h_ref19
        (cyclotomicGalActionOnClassGroup (p := p) (K := K) a
          (ClassGroup.mk0 I)) =
      (a : ZMod p) * phiOnClassGroup h_ref19 (ClassGroup.mk0 I) := by
  -- Step 1: galAction a (mk0 I) = mk0 (σ_a · I) (via cyclotomicGaloisShiftedClass).
  rw [cyclotomicGalActionOnClassGroup_mk0]
  -- The shifted class is ClassGroup.mk0 of the σ_a-conjugated ideal.
  have hI_ne : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hσI_ne : cyclotomicGaloisConjugate (p := p) (K := K) a I.val ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hI_ne
  have h_shifted_eq :
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I =
        ClassGroup.mk0
          ⟨cyclotomicGaloisConjugate (p := p) (K := K) a I.val,
           mem_nonZeroDivisors_iff_ne_zero.mpr hσI_ne⟩ := rfl
  rw [h_shifted_eq, phiOnClassGroup_mk0 h_ref19, phiOnClassGroup_mk0 h_ref19]
  -- Goal: pthSymbolAtIdeal η (σ_a I.val) = a · pthSymbolAtIdeal η I.val
  exact pthSymbolAtIdeal_canonical_galoisAction_of_fixed
    a η hη_fixed hI_ne hη_in hp_in hmax hdiv

/-! ### ClassGroupModP / linear-map level -/

/-- **Phi-Galois weight 1 at the ClassGroupModP level**: descended through
the `Additive` and `ZMod p`-linear structure.

For any element `v ∈ Additive (ClassGroupModP K p)` of the form
`Additive.ofMul (QuotientGroup.mk (mk0 I))` where `I` satisfies the
residue conditions and `σ_a η = η`:

```
phiOnClassGroupModPLinear h_ref19 (cyclotomicGalActionInstance a v)
  = (a : ZMod p) * phiOnClassGroupModPLinear h_ref19 v
```
-/
theorem phiOnClassGroupModPLinear_galois_of_fixed_at_mk0
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (I : (Ideal (𝓞 K))⁰)
    (hη_in : ∀ Q ∈ normalizedFactors I.val, η ∉ Q)
    (hp_in : ∀ Q ∈ normalizedFactors I.val, (p : 𝓞 K) ∉ Q)
    (hmax : ∀ Q ∈ normalizedFactors I.val, Q.IsMaximal)
    (hdiv : ∀ Q ∈ normalizedFactors I.val,
      p ∣ Nat.card (𝓞 K ⧸ Q) - 1) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a
          (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
            ClassGroupModP K p))) =
      (a : ZMod p) *
        phiOnClassGroupModPLinear h_ref19
          (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
            ClassGroupModP K p)) := by
  -- Compute both sides by unfolding through the linearisation chain.
  -- Both `phiOnClassGroupModPLinear h_ref19 (Additive.ofMul x)` reduce to
  -- `phiOnClassGroup h_ref19 c` for `x = QuotientGroup.mk c`.
  have h_phi : ∀ J : (Ideal (𝓞 K))⁰,
      phiOnClassGroupModPLinear h_ref19
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 J) :
          ClassGroupModP K p)) =
      phiOnClassGroup h_ref19 (ClassGroup.mk0 J) := fun J => rfl
  rw [h_phi I]
  have h_galAction :
      cyclotomicGalActionInstance (p := p) (K := K) a
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) :
          ClassGroupModP K p)) =
      Additive.ofMul (QuotientGroup.mk
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a
          (ClassGroup.mk0 I)) : ClassGroupModP K p) := by
    change Additive.ofMul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk (ClassGroup.mk0 I))) = _
    unfold cyclotomicGalActionMonoidHomModP
    rw [QuotientGroup.map_mk]
  rw [h_galAction]
  -- Express `cyclotomicGalActionMonoidHom a (mk0 I)` as `mk0 (σ_a I')` for
  -- some I' = nonZeroDivisors-extended σ_a I.
  change phiOnClassGroupModPLinear h_ref19
      (Additive.ofMul (QuotientGroup.mk (cyclotomicGalActionOnClassGroup
        (p := p) (K := K) a (ClassGroup.mk0 I)))) =
    (a : ZMod p) * phiOnClassGroup h_ref19 (ClassGroup.mk0 I)
  rw [cyclotomicGalActionOnClassGroup_mk0]
  -- Convert `cyclotomicGaloisShiftedClass` into `mk0` of σ_a-conjugate ideal.
  have hI_ne : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hσI_ne : cyclotomicGaloisConjugate (p := p) (K := K) a I.val ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hI_ne
  have h_shifted_eq :
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I =
        ClassGroup.mk0
          ⟨cyclotomicGaloisConjugate (p := p) (K := K) a I.val,
           mem_nonZeroDivisors_iff_ne_zero.mpr hσI_ne⟩ := rfl
  rw [h_shifted_eq, h_phi]
  -- Now: phi (mk0 ⟨σ_a I, _⟩) = a * phi (mk0 I).
  rw [phiOnClassGroup_mk0 h_ref19, phiOnClassGroup_mk0 h_ref19]
  exact pthSymbolAtIdeal_canonical_galoisAction_of_fixed
    a η hη_fixed hI_ne hη_in hp_in hmax hdiv

/-! ### Unconditional phi-Galois weight 1 (no prime hypotheses)

The unconditional version of `pthSymbolAtIdeal_canonical_galoisAction`
(which handles all "bad" prime cases via vanishing) lets us prove the
phi-Galois formula for σ-fixed η at ALL classes — without prime
hypotheses on representative ideals. -/

/-- **Unconditional phi-Galois weight 1 on the integer-rep level** for
σ_a-fixed η. -/
theorem phiOnClassGroup_galois_of_fixed_unconditional
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (I : (Ideal (𝓞 K))⁰) :
    phiOnClassGroup h_ref19
        (cyclotomicGalActionOnClassGroup (p := p) (K := K) a
          (ClassGroup.mk0 I)) =
      (a : ZMod p) * phiOnClassGroup h_ref19 (ClassGroup.mk0 I) := by
  rw [cyclotomicGalActionOnClassGroup_mk0]
  have hI_ne : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hσI_ne : cyclotomicGaloisConjugate (p := p) (K := K) a I.val ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a hI_ne
  have h_shifted_eq :
      cyclotomicGaloisShiftedClass (p := p) (K := K) a I =
        ClassGroup.mk0
          ⟨cyclotomicGaloisConjugate (p := p) (K := K) a I.val,
           mem_nonZeroDivisors_iff_ne_zero.mpr hσI_ne⟩ := rfl
  rw [h_shifted_eq, phiOnClassGroup_mk0 h_ref19, phiOnClassGroup_mk0 h_ref19]
  exact pthSymbolAtIdeal_canonical_galoisAction_of_fixed_unconditional
    a η hη_fixed hI_ne

/-- **Unconditional phi-Galois weight 1 on `ClassGroup`**: extending to
arbitrary classes via `mk0_surjective`. -/
theorem phiOnClassGroup_galois_of_fixed_class
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (c : ClassGroup (𝓞 K)) :
    phiOnClassGroup h_ref19
        (cyclotomicGalActionOnClassGroup (p := p) (K := K) a c) =
      (a : ZMod p) * phiOnClassGroup h_ref19 c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  exact phiOnClassGroup_galois_of_fixed_unconditional h_ref19 a hη_fixed I

/-- **Unconditional phi-Galois weight 1 at the linearised level** for
σ_a-fixed η — no prime hypotheses on the representative. -/
theorem phiOnClassGroupModPLinear_galois_of_fixed
    {η : 𝓞 K} (h_ref19 : Ref19UniversalHypothesis (p := p) (K := K) η)
    (a : CyclotomicUnitDelta p)
    (hη_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a η = η)
    (v : Additive (ClassGroupModP K p)) :
    phiOnClassGroupModPLinear h_ref19
        (cyclotomicGalActionInstance (p := p) (K := K) a v) =
      (a : ZMod p) * phiOnClassGroupModPLinear h_ref19 v := by
  -- v = Additive.ofMul (mk c) for some c ∈ ClassGroup K.
  -- mk : ClassGroup K → ClassGroupModP K p is surjective (via QuotientGroup.mk).
  obtain ⟨w, hw⟩ : ∃ w : ClassGroupModP K p, Additive.ofMul w = v := ⟨v.toMul, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ClassGroup (𝓞 K), QuotientGroup.mk c = w :=
    QuotientGroup.mk_surjective _
  subst hw
  subst hc
  -- Compute both sides via the linearisation chain.
  have h_phi : ∀ d : ClassGroup (𝓞 K),
      phiOnClassGroupModPLinear h_ref19
        (Additive.ofMul (QuotientGroup.mk d : ClassGroupModP K p)) =
      phiOnClassGroup h_ref19 d := fun _ => rfl
  rw [h_phi c]
  have h_galAction :
      cyclotomicGalActionInstance (p := p) (K := K) a
        (Additive.ofMul (QuotientGroup.mk c : ClassGroupModP K p)) =
      Additive.ofMul (QuotientGroup.mk
        (cyclotomicGalActionMonoidHom (p := p) (K := K) a c) :
          ClassGroupModP K p) := by
    change Additive.ofMul (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a
        (QuotientGroup.mk c)) = _
    unfold cyclotomicGalActionMonoidHomModP
    rw [QuotientGroup.map_mk]
  rw [h_galAction, h_phi]
  -- cyclotomicGalActionMonoidHom a c = cyclotomicGalActionOnClassGroup a c.
  change phiOnClassGroup h_ref19
      (cyclotomicGalActionOnClassGroup (p := p) (K := K) a c) =
    (a : ZMod p) * phiOnClassGroup h_ref19 c
  exact phiOnClassGroup_galois_of_fixed_class h_ref19 a hη_fixed c

end Furtwaengler

end BernoulliRegular

end
