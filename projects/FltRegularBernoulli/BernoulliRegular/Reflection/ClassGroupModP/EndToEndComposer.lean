module

public import BernoulliRegular.Reflection.ClassGroupModP.PhiResidueChar
public import BernoulliRegular.Reflection.ClassGroupModP.GalAction
public import BernoulliRegular.Reflection.ClassGroupModP.PhiGaloisEigenspace
public import BernoulliRegular.Reflection.ComponentReflection.SpiegelungssatzFromPhi
public import BernoulliRegular.Reflection.ComponentReflection.EigenspaceReflection
public import BernoulliRegular.Reflection.SubstantiveAtoms

/-!
# End-to-end composer: Atoms A + B + C + D ⟹ ReflectionMinusNontrivialityBridge

This file packages the **end-to-end composer** for the reflection chain
that combines all four atoms into a single
`ReflectionMinusNontrivialityBridge p K`:

* **Atom A** (`Ref19UniversalHypothesis η`): canonical residue symbol
  vanishes on principal ideals. Used to construct
  `phiOnClassGroupModPLinear h_ref19` (Atom A constructive).

* **Atom B** (`CyclotomicGalAction p K`): the `(ZMod p)ˣ`-action on
  `Additive (ClassGroupModP K p)`. Hypothesis-supplied.

* **Atom C** (`ClassGroupComponentIdentification p K`):
  the class-group identifications (Δ-decomposition + plus/minus sides).
  Hypothesis-supplied.

* **Atom D** (Galois weight `k` of phi): the property
  `phiOnClassGroupModPLinear (galAction a v) = a^k * phi v`.
  Hypothesis-supplied.

The composer takes all four atoms and produces a
`ReflectionMinusNontrivialityBridge p K` ready for `T044b`'s
`(p ∣ hPlus K) → (p ∣ h K)`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **End-to-end atomic input bundle**: combines all four substantive
atoms into a single structure ready for the chain composer. -/
structure EndToEndReflectionAtoms where
  /-- The hyperprimary singular η. -/
  η : 𝓞 K
  /-- Atom A: universal REF-19 for η. -/
  ref19 : Furtwaengler.Ref19UniversalHypothesis (p := p) (K := K) η
  /-- Atom B: the `(ZMod p)ˣ`-action on Additive (ClassGroupModP K p). -/
  galAction : CyclotomicGalAction p K
  /-- Atom D: Galois weight k of phi. -/
  k : ℕ
  /-- Atom D continued: phi has Galois weight k. -/
  phi_galois :
    ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
      Furtwaengler.phiOnClassGroupModPLinear ref19 (galAction a v) =
        ((a : ZMod p) ^ k) * Furtwaengler.phiOnClassGroupModPLinear ref19 v
  /-- Atom A residual: phi nontrivial witness (existence of v with phi v ≠ 0). -/
  phi_nontrivial :
    ∃ v : Additive (ClassGroupModP K p),
      Furtwaengler.phiOnClassGroupModPLinear ref19 v ≠ 0
  /-- Card unit hypothesis: `(p - 1) = #(ZMod p)ˣ` is invertible in `ZMod p`. -/
  card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p))
  /-- Atom C: class-group component identifications. -/
  componentIdentification : ClassGroupComponentIdentification p K
  /-- Atom C+D bridge: `componentNontrivial k` exhibits a non-trivial
  `k`-th eigenspace via the eigenspace projection from phi. -/
  componentNontrivial_of_eigenspace :
    (∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p)) galAction k, w ≠ 0) →
      componentIdentification.componentNontrivial k
  /-- The weight-`k` index is a valid component index. -/
  k_isIndex : IsReflectionComponentIndex p k

namespace EndToEndReflectionAtoms

variable {p K}

/-- **Eigenspace nontriviality** from the bundled atoms.

Combines `phi_nontrivial` + `phi_galois` + `card_unit` via
`exists_eigenspace_phi_nontrivial_of_projectionData` (the substantive
REF-25 theorem) to conclude the `k`-th eigenspace contains a non-zero
element. -/
theorem eigenspace_k_nontrivial
    (E : EndToEndReflectionAtoms p K) :
    ∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p))
        E.galAction E.k, w ≠ 0 :=
  eigenspace_nontrivial_of_phi_nontrivial
    (standardEigenspaceProjectionData E.galAction
      (Furtwaengler.phiOnClassGroupModPLinear E.ref19) E.k
      E.phi_galois E.card_unit)
    E.phi_nontrivial

/-- **Atom C's `componentNontrivial k` from the bundled atoms.** -/
theorem componentNontrivial_k
    (E : EndToEndReflectionAtoms p K) :
    E.componentIdentification.componentNontrivial E.k :=
  E.componentNontrivial_of_eigenspace E.eigenspace_k_nontrivial

/-- **Bridge production** from the bundled atoms. -/
def toReflectionMinusNontrivialityBridge (hp_odd : Odd p)
    (E : EndToEndReflectionAtoms p K) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd E.componentIdentification.toSpiegelungssatzData

end EndToEndReflectionAtoms

/-- **Top-level T044b consumer from the bundled four atoms**. -/
theorem dvd_h_of_dvd_hPlus_of_endToEndReflectionAtoms
    (hp_odd_nat : Odd p) (hp_ne_two : p ≠ 2)
    (E : EndToEndReflectionAtoms p K)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_ne_two K
    (E.toReflectionMinusNontrivialityBridge hp_odd_nat)
    h_plus

/-- **Concrete factory** producing an `EndToEndReflectionAtoms` from
the substantively remaining inputs (Atoms C, D + Atom A's `η` and
`Ref19UniversalHypothesis`). -/
noncomputable def EndToEndReflectionAtoms.mk_with_A_B_constructed
    (η : 𝓞 K)
    (h_ref19 : Furtwaengler.Ref19UniversalHypothesis (p := p) (K := K) η)
    (k : ℕ)
    (phi_galois :
      ∀ (a : (ZMod p)ˣ) (v : Additive (ClassGroupModP K p)),
        Furtwaengler.phiOnClassGroupModPLinear h_ref19
            (cyclotomicGalActionInstance (p := p) (K := K) a v) =
          ((a : ZMod p) ^ k) *
            Furtwaengler.phiOnClassGroupModPLinear h_ref19 v)
    (phi_nontrivial :
      ∃ v : Additive (ClassGroupModP K p),
        Furtwaengler.phiOnClassGroupModPLinear h_ref19 v ≠ 0)
    (card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)))
    (componentIdentification : ClassGroupComponentIdentification p K)
    (componentNontrivial_of_eigenspace :
      (∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p))
          (cyclotomicGalActionInstance (p := p) (K := K)) k, w ≠ 0) →
        componentIdentification.componentNontrivial k)
    (k_isIndex : IsReflectionComponentIndex p k) :
    EndToEndReflectionAtoms p K where
  η := η
  ref19 := h_ref19
  galAction := cyclotomicGalActionInstance (p := p) (K := K)
  k := k
  phi_galois := phi_galois
  phi_nontrivial := phi_nontrivial
  card_unit := card_unit
  componentIdentification := componentIdentification
  componentNontrivial_of_eigenspace := componentNontrivial_of_eigenspace
  k_isIndex := k_isIndex

/-- **EndToEndReflectionAtoms factory from substantive REF-24 inputs**:
under StrongEigenspaceCondition i with universal u-unit witness +
Ref19 + remaining EndToEnd ingredients, produces the bundle with weight
`k = p - i`.

The substantive REF-24 content (numerator transform + ideal-level shift)
is encapsulated in `phi_galois_universal_eigenspace_unit`. The remaining
inputs (phi_nontrivial, componentIdentification, etc.) are the substantive
non-Atom-D inputs. -/
noncomputable def EndToEndReflectionAtoms.mk_with_strong_eigenspace_unit
    (η : 𝓞 K)
    (h_ref19 : Furtwaengler.Ref19UniversalHypothesis (p := p) (K := K) η)
    (i : ℕ) (hi : i ≤ p)
    (h_strong : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (phi_nontrivial : ∃ v : Additive (ClassGroupModP K p),
      Furtwaengler.phiOnClassGroupModPLinear h_ref19 v ≠ 0)
    (card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)))
    (componentIdentification : ClassGroupComponentIdentification p K)
    (componentNontrivial_of_eigenspace :
      (∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p))
          (cyclotomicGalActionInstance (p := p) (K := K)) (p - i), w ≠ 0) →
        componentIdentification.componentNontrivial (p - i))
    (k_isIndex : IsReflectionComponentIndex p (p - i)) :
    EndToEndReflectionAtoms p K :=
  EndToEndReflectionAtoms.mk_with_A_B_constructed p K η h_ref19 (p - i)
    (Furtwaengler.phi_galois_universal_eigenspace_unit h_ref19 i hi h_strong)
    phi_nontrivial card_unit componentIdentification
    componentNontrivial_of_eigenspace k_isIndex

/-- **ReflectionMinusNontrivialityBridge from the StrongEigenspaceCondition factory**:
the substantive structural reduction. -/
def reflectionMinusBridge_of_strong_eigenspace_unit
    (hp_odd_nat : Odd p)
    (η : 𝓞 K)
    (h_ref19 : Furtwaengler.Ref19UniversalHypothesis (p := p) (K := K) η)
    (i : ℕ) (hi : i ≤ p)
    (h_strong : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (phi_nontrivial : ∃ v : Additive (ClassGroupModP K p),
      Furtwaengler.phiOnClassGroupModPLinear h_ref19 v ≠ 0)
    (card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)))
    (componentIdentification : ClassGroupComponentIdentification p K)
    (componentNontrivial_of_eigenspace :
      (∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p))
          (cyclotomicGalActionInstance (p := p) (K := K)) (p - i), w ≠ 0) →
        componentIdentification.componentNontrivial (p - i))
    (k_isIndex : IsReflectionComponentIndex p (p - i)) :
    ReflectionMinusNontrivialityBridge p K :=
  (EndToEndReflectionAtoms.mk_with_strong_eigenspace_unit p K η h_ref19 i hi
    h_strong phi_nontrivial card_unit componentIdentification
    componentNontrivial_of_eigenspace k_isIndex).toReflectionMinusNontrivialityBridge
      hp_odd_nat

/-- **T044b end-to-end via the StrongEigenspaceCondition factory**:
the bridge `p ∣ hPlus K → p ∣ h K` derived from the new substantive
REF-24 factory. -/
theorem dvd_h_of_dvd_hPlus_of_strong_eigenspace_unit
    (hp_odd_nat : Odd p) (hp_ne_two : p ≠ 2)
    (η : 𝓞 K)
    (h_ref19 : Furtwaengler.Ref19UniversalHypothesis (p := p) (K := K) η)
    (i : ℕ) (hi : i ≤ p)
    (h_strong : ∀ a : CyclotomicUnitDelta p, ∃ u : 𝓞 K, IsUnit u ∧
      cyclotomicRingOfIntegersEquiv (p := p) K a η =
        η ^ ((a : ZMod p).val ^ i : ℕ) * u ^ p)
    (phi_nontrivial : ∃ v : Additive (ClassGroupModP K p),
      Furtwaengler.phiOnClassGroupModPLinear h_ref19 v ≠ 0)
    (card_unit : IsUnit ((Fintype.card (ZMod p)ˣ : ZMod p)))
    (componentIdentification : ClassGroupComponentIdentification p K)
    (componentNontrivial_of_eigenspace :
      (∃ w ∈ eigenspace (V := Additive (ClassGroupModP K p))
          (cyclotomicGalActionInstance (p := p) (K := K)) (p - i), w ≠ 0) →
        componentIdentification.componentNontrivial (p - i))
    (k_isIndex : IsReflectionComponentIndex p (p - i))
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  dvd_h_of_dvd_hPlus_of_endToEndReflectionAtoms p K hp_odd_nat hp_ne_two
    (EndToEndReflectionAtoms.mk_with_strong_eigenspace_unit p K η h_ref19 i hi
      h_strong phi_nontrivial card_unit componentIdentification
      componentNontrivial_of_eigenspace k_isIndex) h_plus

end BernoulliRegular

end
