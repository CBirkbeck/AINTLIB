module

public import BernoulliRegular.Reflection.ClassGroupModP.Module
public import BernoulliRegular.Reflection.ClassGroupModP.GalAction
public import BernoulliRegular.Reflection.SubstantiveAtoms
public import BernoulliRegular.Reflection.FinalRegularPrime
public import BernoulliRegular.Reflection.ComponentReflection.EigenspaceReflection


/-!
# Atom C: ClassGroupComponentIdentification — concrete construction

This file provides the **concrete construction** of Atom C
(`ClassGroupComponentIdentification p K`) of the reflection chain.

## Strategy

We define the `componentNontrivial` predicate as the natural
"Δ-character idempotent component is nontrivial" via the eigenspace
of `cyclotomicGalActionInstance`:

  `componentNontrivial i := ∃ v ∈ eigenspace galAction i, v ≠ 0`

This makes:
* `reflection_componentNontrivial` an *abstract reflection identity*
  on eigenspaces.
* `even_componentNontrivial_of_dvd_hPlus` and
  `dvd_hMinus_of_odd_componentNontrivial` the substantive plus/minus
  identifications.

## Concrete instance

We construct `ClassGroupComponentIdentification p K` for the
**regular prime case** (`Subsingleton (ClassGroup (𝓞 K))`):

* `componentNontrivial i := False` for all i (since `Cl(K)/p` is
  trivial, every eigenspace is the zero subgroup).
* All four fields discharge vacuously (premises are false under
  regularity).

This gives a concrete, sorry-free `ClassGroupComponentIdentification`
instance for regular primes, completing Atom C in this case.

## Irregular prime case

For the irregular case, we expose a structural API that takes the
substantive eigenspace+reflection content as input and produces the
bundle. The substantive open content is the per-character
identification with `hPlus K`/`hMinus K`, which is downstream class-
group-theoretic work.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Atom C, regular-prime construction**: under
`Subsingleton (ClassGroup (𝓞 K))` (the regular-prime hypothesis), the
class group is trivial, all components vanish, and all four atom
fields are vacuously satisfied.

This concretely instantiates `ClassGroupComponentIdentification p K`
for regular primes. -/
def ClassGroupComponentIdentification.ofSubsingleton
    [Subsingleton (ClassGroup (𝓞 K))] :
    ClassGroupComponentIdentification p K where
  componentNontrivial _ := False
  even_componentNontrivial_of_dvd_hPlus h_plus := by
    -- Premise `p ∣ hPlus K` is false under regularity (hPlus K = 1, p ≥ 2).
    exfalso
    have hone : hPlus K = 1 := hPlus_eq_one_of_subsingleton p hp_odd K
    rw [hone] at h_plus
    exact (Nat.Prime.one_lt hp.out).ne' (Nat.dvd_one.mp h_plus)
  dvd_hMinus_of_odd_componentNontrivial h_odd := by
    -- Premise asserts ∃ j with `componentNontrivial j = False`,
    -- which is impossible.
    exfalso
    obtain ⟨_, _, _, h_false⟩ := h_odd
    exact h_false
  reflection_componentNontrivial _ h_false := h_false

include hp_odd in
/-- **The regular-prime Atom C bundle is non-empty**. -/
theorem ClassGroupComponentIdentification.nonempty_of_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] :
    Nonempty (ClassGroupComponentIdentification p K) :=
  ⟨ClassGroupComponentIdentification.ofSubsingleton p hp_odd K⟩

/-! ### Irregular-prime structural composer

For the irregular case, expose a structural composer taking the
substantive eigenspace + reflection + class-group identifications
as input. -/

/-- **Atom C from substantive eigenspace identifications.**

Takes:
* a function `comp : ℕ → Prop` representing the per-index component
  nontriviality predicate (typically `eigenspace ... i ≠ ⊥`),
* the abstract reflection `comp i ⟹ comp (p - i)`,
* the plus-side identification `(p ∣ hPlus K) ⟹ ∃ even i, comp i`,
* the minus-side identification `(∃ odd j, comp j) ⟹ p ∣ hMinus K`,

and produces a `ClassGroupComponentIdentification p K`. -/
def ClassGroupComponentIdentification.ofStructural
    (comp : ℕ → Prop)
    (h_reflect : ∀ {i : ℕ}, IsReflectionComponentIndex p i →
      comp i → comp (reflectedComponentIndex p i))
    (h_plus : (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧ comp i)
    (h_minus : (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧ comp j) →
      (p : ℕ) ∣ hMinus K) :
    ClassGroupComponentIdentification p K where
  componentNontrivial := comp
  even_componentNontrivial_of_dvd_hPlus := h_plus
  dvd_hMinus_of_odd_componentNontrivial := h_minus
  reflection_componentNontrivial := h_reflect

/-! ### Eigenspace-based componentNontrivial

The natural definition of `componentNontrivial i` for the cyclotomic
setup uses the eigenspace of `cyclotomicGalActionInstance` at index `i`:
the i-th Δ-character idempotent component is non-trivial iff the
i-th eigenspace contains a non-zero element. -/

/-- **Eigenspace-based component non-triviality predicate**: the
`i`-th Δ-character eigenspace of `Additive (ClassGroupModP K p)`
under `cyclotomicGalActionInstance` is non-trivial. -/
def eigenspaceComponentNontrivial (i : ℕ) : Prop :=
  ∃ v ∈ eigenspace (V := Additive (ClassGroupModP K p))
      (cyclotomicGalActionInstance (p := p) (K := K)) i, v ≠ 0

omit [IsCMField K] in
/-- Under `Subsingleton (ClassGroup (𝓞 K))` (regular prime), every
eigenspace component is trivially trivial (since `Cl(K)/p` is trivial). -/
theorem eigenspaceComponentNontrivial_iff_false_of_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] (i : ℕ) :
    eigenspaceComponentNontrivial p K i ↔ False := by
  refine ⟨?_, fun h ↦ h.elim⟩
  rintro ⟨v, _, hv_ne⟩
  apply hv_ne
  -- Cl(K)/p is a subsingleton because Cl(K) is.
  haveI : Subsingleton (ClassGroupModP K p) :=
    Quotient.instSubsingletonQuotient _
  exact Subsingleton.elim _ _

/-- **Atom C with eigenspace-based componentNontrivial**.

The natural Δ-character idempotent decomposition of `Cl(K)/p` defines
`componentNontrivial i := i-th eigenspace is non-trivial`. With this
definition, the structural composer takes:

* the abstract reflection identity on eigenspaces,
* the plus-side identification `(p ∣ hPlus K) ⟹ ∃ even i, eigenspace i ≠ ⊥`,
* the minus-side identification `(∃ odd j, eigenspace j ≠ ⊥) ⟹ p ∣ hMinus K`,

and produces the concrete bundle. -/
def ClassGroupComponentIdentification.ofEigenspace
    (h_reflect : ∀ {i : ℕ}, IsReflectionComponentIndex p i →
      eigenspaceComponentNontrivial p K i →
      eigenspaceComponentNontrivial p K (reflectedComponentIndex p i))
    (h_plus : (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
        eigenspaceComponentNontrivial p K i)
    (h_minus : (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
        eigenspaceComponentNontrivial p K j) →
      (p : ℕ) ∣ hMinus K) :
    ClassGroupComponentIdentification p K :=
  ClassGroupComponentIdentification.ofStructural p K
    (eigenspaceComponentNontrivial p K) h_reflect h_plus h_minus

/-- **Regular-prime constructor for `ClassGroupComponentIdentification`**:
when `Cl(K)` is `Subsingleton`, the eigenspace component predicate is
identically False, all hypotheses are vacuous, and `(p ∣ hPlus K)` is
itself impossible (hPlus | h | 1, so p ∤ hPlus). -/
def ClassGroupComponentIdentification.ofRegular_subsingleton
    (hp_odd : p ≠ 2)
    [Subsingleton (ClassGroup (𝓞 K))] :
    ClassGroupComponentIdentification p K :=
  ClassGroupComponentIdentification.ofEigenspace p K
    (h_reflect := fun _ h_comp ↦ absurd h_comp
      ((eigenspaceComponentNontrivial_iff_false_of_subsingleton p K _).mp))
    (h_plus := fun h_dvd ↦ by
      -- (p ∣ hPlus K) is false since hPlus K | h K = 1.
      exfalso
      have hp_prime : p.Prime := Fact.out
      have hp_ge_2 : 2 ≤ p := hp_prime.two_le
      have h_hPlus_eq_one : hPlus K = 1 := by
        have hh := hPlus_dvd_h p hp_odd K
        unfold BernoulliRegular.h at hh
        have h_card : Fintype.card (ClassGroup (𝓞 K)) = 1 :=
          Fintype.card_eq_one_iff.mpr ⟨default, fun _ ↦ Subsingleton.elim _ _⟩
        rw [h_card] at hh
        exact Nat.eq_one_of_dvd_one hh
      rw [h_hPlus_eq_one] at h_dvd
      exact absurd h_dvd (by
        intro h
        have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h
        omega))
    (h_minus := fun ⟨j, _, _, h_comp⟩ ↦ absurd h_comp
      ((eigenspaceComponentNontrivial_iff_false_of_subsingleton p K j).mp))

/-- **Regular-prime SpiegelungssatzData**: extract from the regular-prime
ClassGroupComponentIdentification. -/
def spiegelungssatzData_ofRegular_subsingleton
    (hp_odd : p ≠ 2)
    [Subsingleton (ClassGroup (𝓞 K))] :
    SpiegelungssatzData p K :=
  (ClassGroupComponentIdentification.ofRegular_subsingleton p K hp_odd).toSpiegelungssatzData

/-- **Regular-prime ReflectionMinusNontrivialityBridge via Atom C path**:
composes the regular-prime SpiegelungssatzData with
`reflectionMinusNontrivialityBridge_of_spiegelungssatzData`. Demonstrates
the Atom C → Bridge chain for regular primes. -/
def reflectionMinusBridge_ofRegular_subsingleton_via_AtomC
    (hp_odd : p ≠ 2) (hp_odd_nat : Odd p)
    [Subsingleton (ClassGroup (𝓞 K))] :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd_nat
    (spiegelungssatzData_ofRegular_subsingleton p K hp_odd)

omit hp [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **`ClassGroupModP K p` is Subsingleton when p ∤ |Cl(K)|**: under
regularity at K, the p-th-power map on Cl(K) is a bijection (via mathlib's
`powCoprime`), so its range is all of Cl(K), making the quotient trivial. -/
theorem subsingleton_classGroupModP_of_coprime [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) :
    Subsingleton (ClassGroupModP K p) := by
  have h_card_coprime : (Nat.card (ClassGroup (𝓞 K))).Coprime p := by
    rw [Nat.card_eq_fintype_card]; exact hreg.symm
  -- powCoprime gives a bijection, hence the p-th-power map is surjective.
  have h_surj : Function.Surjective
      (powMonoidHom p : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)) := by
    intro y
    refine ⟨(powCoprime h_card_coprime).symm y, ?_⟩
    change (powCoprime h_card_coprime).symm y ^ p = y
    have := (powCoprime h_card_coprime).right_inv y
    simpa [powCoprime] using this
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  refine QuotientGroup.eq.mpr ?_
  exact h_surj (a⁻¹ * b)

omit [IsCMField K] in
/-- **`eigenspaceComponentNontrivial` is False under regularity**: from
`p.Coprime |Cl K|`, the ClassGroupModP is Subsingleton, so any
eigenspace contains only the zero element, so the predicate is False. -/
theorem eigenspaceComponentNontrivial_iff_false_of_coprime
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) (i : ℕ) :
    eigenspaceComponentNontrivial p K i ↔ False := by
  refine ⟨?_, fun h ↦ h.elim⟩
  rintro ⟨v, _, hv_ne⟩
  apply hv_ne
  haveI : Subsingleton (ClassGroupModP K p) :=
    subsingleton_classGroupModP_of_coprime p K hreg
  exact Subsingleton.elim _ _

/-- **Atom C from regularity (`p.Coprime |Cl K|`)**: under regularity,
all eigenspace components are trivially trivial; combined with the
Subsingleton-of-coprime fact, build the regular-prime
ClassGroupComponentIdentification without requiring the stronger
`Subsingleton ClassGroup` hypothesis. -/
def ClassGroupComponentIdentification.ofRegular
    (hp_odd : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) :
    ClassGroupComponentIdentification p K :=
  ClassGroupComponentIdentification.ofEigenspace p K
    (h_reflect := fun _ h_comp ↦ absurd h_comp
      ((eigenspaceComponentNontrivial_iff_false_of_coprime p K hreg _).mp))
    (h_plus := fun h_dvd ↦ by
      exfalso
      have hp_prime : p.Prime := Fact.out
      have h_not_dvd_h : ¬ (p : ℕ) ∣ Fintype.card (ClassGroup (𝓞 K)) :=
        hp_prime.coprime_iff_not_dvd.mp hreg
      have hdvd : hPlus K ∣ Fintype.card (ClassGroup (𝓞 K)) := by
        have hh := hPlus_dvd_h p hp_odd K
        unfold BernoulliRegular.h at hh
        convert hh
      exact h_not_dvd_h (h_dvd.trans hdvd))
    (h_minus := fun ⟨j, _, _, h_comp⟩ ↦ absurd h_comp
      ((eigenspaceComponentNontrivial_iff_false_of_coprime p K hreg j).mp))

/-- **T044b for regular primes via Atom C**: composes the bridge with
the existing `dvd_h_of_dvd_hPlus_of_bridge` to get `p ∣ h K` from
`p ∣ hPlus K` for regular primes. (Note: under Subsingleton ClassGroup,
this implication is itself vacuous since p ∤ hPlus K = 1.) -/
theorem dvd_h_of_dvd_hPlus_of_regular_subsingleton_via_AtomC
    (hp_odd : p ≠ 2) (hp_odd_nat : Odd p)
    [Subsingleton (ClassGroup (𝓞 K))]
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_odd K
    (reflectionMinusBridge_ofRegular_subsingleton_via_AtomC p K hp_odd hp_odd_nat)
    h_plus

/-- **Regular-prime SpiegelungssatzData via coprimality** (general regular case). -/
def spiegelungssatzData_ofRegular_coprime
    (hp_odd : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) :
    SpiegelungssatzData p K :=
  (ClassGroupComponentIdentification.ofRegular p K hp_odd hreg).toSpiegelungssatzData

/-- **Regular-prime ReflectionMinusNontrivialityBridge via Atom C path
(coprimality form)**: full regular-case constructor without
`Subsingleton` hypothesis. -/
def reflectionMinusBridge_ofRegular_coprime_via_AtomC
    (hp_odd : p ≠ 2) (hp_odd_nat : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K)))) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd_nat
    (spiegelungssatzData_ofRegular_coprime p K hp_odd hreg)

/-- **T044b end-to-end for regular primes via Atom C path** (coprimality form):
the full chain `p ∣ hPlus K → p ∣ h K` for any regular K. -/
theorem dvd_h_of_dvd_hPlus_of_regular_via_AtomC
    (hp_odd : p ≠ 2) (hp_odd_nat : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_odd K
    (reflectionMinusBridge_ofRegular_coprime_via_AtomC p K hp_odd hp_odd_nat hreg)
    h_plus


include hp_odd in
/-- **Atom C, eigenspace form, regular-prime case**: under
`Subsingleton (ClassGroup (𝓞 K))`, the eigenspace-based bundle exists
trivially since every component is empty. -/
def ClassGroupComponentIdentification.ofEigenspace_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] :
    ClassGroupComponentIdentification p K :=
  ClassGroupComponentIdentification.ofEigenspace p K
    (h_reflect := fun _ h ↦
      ((eigenspaceComponentNontrivial_iff_false_of_subsingleton p K _).mp h).elim)
    (h_plus := fun h_plus ↦ by
      exfalso
      have hone : hPlus K = 1 := hPlus_eq_one_of_subsingleton p hp_odd K
      rw [hone] at h_plus
      exact (Nat.Prime.one_lt hp.out).ne' (Nat.dvd_one.mp h_plus))
    (h_minus := fun h_odd ↦ by
      exfalso
      obtain ⟨_, _, _, h⟩ := h_odd
      exact (eigenspaceComponentNontrivial_iff_false_of_subsingleton p K _).mp h)

/-! ### Eigenspace nontriviality from `ClassGroupModP` nontriviality

Under the eigenspace decomposition completeness hypothesis (the natural
fact that `V = ⊕_k V_k` for V a ZMod p-module with `(ZMod p)ˣ`-action
and `(p-1)` invertible — Maschke for the group algebra `ZMod p[Δ]`),
nontriviality of `V` propagates to nontriviality of some eigenspace `V_k`.

This gives the `componentNontrivial`-existence content of Atom C
modulo the eigenspace decomposition. -/

omit [IsCMField K] in
/-- **Eigenspace decomposition completeness for the cyclotomic action**.

Under the standard hypothesis that `((p - 1 : ℕ) : ZMod p)` is
invertible (true for `p` prime), the cyclotomic Galois action's
eigenspace projections sum to the identity. This is
`standardEigenspaceDecompositionComplete_proof` applied to
`cyclotomicGalActionInstance`. -/
theorem cyclotomicGalActionInstance_eigenspaceDecompositionComplete (h_pminus1_unit :
      IsUnit (((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p))) :
    StandardEigenspaceDecompositionComplete
      (V := Additive (ClassGroupModP K p))
      (cyclotomicGalActionInstance (p := p) (K := K)) :=
  standardEigenspaceDecompositionComplete_proof
    (cyclotomicGalActionInstance (p := p) (K := K)) h_pminus1_unit

omit [IsCMField K] in
/-- **Eigenspace nontriviality from V nontriviality**: under the eigenspace
decomposition completeness hypothesis, if `V = Additive (ClassGroupModP K p)`
contains a non-zero element, then some eigenspace `V_k` is non-trivial. -/
theorem exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial
    (h_decomp : StandardEigenspaceDecompositionComplete
        (V := Additive (ClassGroupModP K p))
        (cyclotomicGalActionInstance (p := p) (K := K)))
    (h_nontrivial : ∃ v : Additive (ClassGroupModP K p), v ≠ 0) :
    ∃ k : ℕ, k < p - 1 ∧ eigenspaceComponentNontrivial p K k := by
  classical
  obtain ⟨v, hv⟩ := h_nontrivial
  -- v = ∑_k π_k(v). If all π_k(v) = 0, then v = 0, contradiction.
  -- So ∃ k with π_k(v) ≠ 0. Then π_k(v) ∈ V_k, witnessing
  -- eigenspaceComponentNontrivial k.
  have h_sum := h_decomp v
  -- If every standardEigenspaceProjection (cyclotomicGalActionInstance) k v = 0,
  -- then the sum = 0, but the sum = v ≠ 0. So some projection ≠ 0.
  by_contra h_all_trivial
  push Not at h_all_trivial
  apply hv
  rw [← h_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_lt : k < p - 1 := by
    simpa using hk
  -- π_k(v) ∈ V_k by `standardEigenspaceProjection_mem_eigenspace`.
  -- If V_k is trivial (no non-zero element), then π_k(v) must be 0.
  have h_mem :
      standardEigenspaceProjection
          (cyclotomicGalActionInstance (p := p) (K := K)) k v ∈
        eigenspace (V := Additive (ClassGroupModP K p))
          (cyclotomicGalActionInstance (p := p) (K := K)) k :=
    standardEigenspaceProjection_mem_eigenspace _ k v
  by_contra h_proj_ne
  exact h_all_trivial k hk_lt <| ⟨_, h_mem, h_proj_ne⟩

/-! ### End-to-end Atom C composition for the regular-prime case

Under `Subsingleton (ClassGroup (𝓞 K))`, the regular-prime Atom C
`ClassGroupComponentIdentification.ofSubsingleton` plugs directly into
the chain composer to produce `ReflectionMinusNontrivialityBridge p K`,
then `T044b`'s `(p ∣ hPlus K) → (p ∣ h K)`. -/

include hp_odd in
/-- **Bridge production for regular primes**: under
`Subsingleton (ClassGroup (𝓞 K))`, the Atom C bundle produces a
`ReflectionMinusNontrivialityBridge p K`. -/
def reflectionMinusNontrivialityBridge_of_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] (hp_odd_nat : Odd p) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd_nat
    (ClassGroupComponentIdentification.ofSubsingleton p hp_odd K).toSpiegelungssatzData

include hp_odd in
/-- **Top-level T044b consumer** under regularity, via Atom C. -/
theorem dvd_h_of_dvd_hPlus_via_atomC_subsingleton
    [Subsingleton (ClassGroup (𝓞 K))] (hp_odd_nat : Odd p)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_odd K
    (reflectionMinusNontrivialityBridge_of_subsingleton p hp_odd K hp_odd_nat)
    h_plus

omit [IsCMField K] in
/-- **Unconditional eigenspace nontriviality from `Cl(K)/p` nontriviality**:
this combines the substantively-proven decomposition completeness with
the eigenspace existence argument. -/
theorem exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial_unconditional
    (h_pminus1_unit :
      IsUnit (((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p)))
    (h_nontrivial : ∃ v : Additive (ClassGroupModP K p), v ≠ 0) :
    ∃ k : ℕ, k < p - 1 ∧ eigenspaceComponentNontrivial p K k :=
  exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial p K
    (cyclotomicGalActionInstance_eigenspaceDecompositionComplete p K h_pminus1_unit)
    h_nontrivial

/-! ### Plus/minus identification structure

The remaining substantive content for Atom C in the irregular case is
the **plus/minus identification**: which eigenspace components
correspond to the plus part `Cl(K⁺)/p` (giving `hPlus K`) and which to
the minus part (giving `hMinus K`).

The standard mathematical fact: under complex conjugation `c` (acting
on `K = ℚ(ζ_p)` as `ζ ↦ ζ^{-1}`, corresponding to `-1 ∈ (ZMod p)ˣ`):

* The plus part of `Cl(K)` is `Cl(K)^c = {x | c x = x}`.
* The minus part of `Cl(K)` is the kernel of `c + 1` (= image of `c - 1`).
* On `Cl(K)/p`, the plus part decomposes as `⊕_{k even} V_k`.
* The minus part decomposes as `⊕_{k odd} V_k`.

We expose the substantive content as a `PlusMinusIdentification`
structure carrying the relevant translations. -/

/-- **Plus-minus identification structure** for the cyclotomic class
group's elementary `p`-quotient. Carries the substantive content of
the identification of plus/minus parts with even/odd character
eigenspace components. -/
structure PlusMinusIdentification where
  /-- `(p ∣ hPlus K)` exhibits a non-trivial even-index eigenspace. -/
  even_eigenspace_of_dvd_hPlus :
    (p : ℕ) ∣ hPlus K →
      ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
        eigenspaceComponentNontrivial p K i
  /-- A non-trivial odd-index eigenspace exhibits `(p ∣ hMinus K)`. -/
  dvd_hMinus_of_odd_eigenspace :
    (∃ j : ℕ, IsReflectionComponentIndex p j ∧ Odd j ∧
        eigenspaceComponentNontrivial p K j) →
      (p : ℕ) ∣ hMinus K
  /-- Reflection identity on eigenspaces (i.e., REF-25): if the i-th
  eigenspace is non-trivial (for valid i), so is the (p-i)-th. -/
  eigenspace_reflection :
    ∀ {i : ℕ}, IsReflectionComponentIndex p i →
      eigenspaceComponentNontrivial p K i →
      eigenspaceComponentNontrivial p K (reflectedComponentIndex p i)

/-- **Atom C from `PlusMinusIdentification`**: produces the
`ClassGroupComponentIdentification` bundle from the substantive
plus/minus identification structure. -/
def ClassGroupComponentIdentification.ofPlusMinus
    (PMI : PlusMinusIdentification p K) :
    ClassGroupComponentIdentification p K :=
  ClassGroupComponentIdentification.ofEigenspace p K
    (h_reflect := PMI.eigenspace_reflection)
    (h_plus := PMI.even_eigenspace_of_dvd_hPlus)
    (h_minus := PMI.dvd_hMinus_of_odd_eigenspace)

include hp_odd in
/-- **End-to-end Atom C bridge from `PlusMinusIdentification`**:
produces the `ReflectionMinusNontrivialityBridge` from the
plus/minus identification. -/
def reflectionMinusNontrivialityBridge_of_plusMinus
    (PMI : PlusMinusIdentification p K) (hp_odd_nat : Odd p) :
    ReflectionMinusNontrivialityBridge p K :=
  reflectionMinusNontrivialityBridge_of_spiegelungssatzData
    (p := p) (K := K) hp_odd_nat
    (ClassGroupComponentIdentification.ofPlusMinus p K PMI).toSpiegelungssatzData

include hp_odd in
/-- **Top-level T044b consumer** via `PlusMinusIdentification`. -/
theorem dvd_h_of_dvd_hPlus_via_plusMinus
    (PMI : PlusMinusIdentification p K) (hp_odd_nat : Odd p)
    (h_plus : (p : ℕ) ∣ hPlus K) :
    (p : ℕ) ∣ h K :=
  ReflectionMinusNontrivialityBridge.dvd_h_of_dvd_hPlus
    p hp_odd K
    (reflectionMinusNontrivialityBridge_of_plusMinus p K PMI hp_odd_nat) h_plus

/-! ### Summary: Atom C status

* **Regular prime case** (`Subsingleton (ClassGroup (𝓞 K))`):
  CONCRETELY CONSTRUCTED via `ClassGroupComponentIdentification.ofSubsingleton`.
  All four bundle fields discharged vacuously. End-to-end T044b consumer
  works.

* **Irregular prime case**: STRUCTURALLY REDUCED to a single substantive
  input `PlusMinusIdentification p K`, which captures:
  - The plus-side identification `(p ∣ hPlus K) ⟹ ∃ even eigenspace ≠ 0`.
  - The minus-side identification `∃ odd eigenspace ≠ 0 ⟹ (p ∣ hMinus K)`.
  - The reflection identity (REF-25 content).

  These three pieces are the substantive open content for Atom C in
  the irregular case. The reduction itself is fully constructed
  (`ClassGroupComponentIdentification.ofPlusMinus`).

* **Supporting lemmas substantively PROVED**:
  - `geom_sum_zmod_units` (character orthogonality).
  - `geom_sum_zmod_units_inv` (inverse-power form).
  - `standardEigenspaceDecompositionComplete_proof` (Maschke-type
    decomposition theorem).
  - `cyclotomicGalActionInstance_eigenspaceDecompositionComplete`
    (decomposition for the cyclotomic action).
  - `exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial`
    (non-trivial V ⟹ non-trivial eigenspace).
-/

/-- **SP-1 (Δ-character decomposition of Cl(K)/p)**: the whole module
`Additive (ClassGroupModP K p)` is the direct sum of its `(p-1)`
character eigenspaces under the cyclotomic Galois action.

This is the direct instantiation of `eigenspaceSubmodule_top_eq_iSup`
at `V = Additive (ClassGroupModP K p)` and the cyclotomic action,
under the standard hypothesis `((p-1) : ZMod p)` invertible. -/
theorem classGroupModP_eq_directSum_eigenspaces
    (h_pminus1_unit : IsUnit (((Fintype.card (ZMod p)ˣ : ℕ) : ZMod p))) :
    (⊤ : Submodule (ZMod p) (Additive (ClassGroupModP K p))) =
      ⨆ i ∈ Finset.range (p - 1),
        eigenspaceSubmodule (cyclotomicGalActionInstance (p := p) (K := K)) i :=
  eigenspaceSubmodule_top_eq_iSup
    (cyclotomicGalActionInstance (p := p) (K := K)) h_pminus1_unit

omit [IsCMField K] in
/-- **Eigenspace nontriviality from σ-fixed nontriviality (Even-direction refinement)**:
if `v ∈ V := Additive (ClassGroupModP K p)` is nonzero AND σ-fixed
(`cyclotomicGalActionInstance (-1) v = v`), then some EVEN k yields a
nontrivial eigenspace `V_k`.

This refines `exists_eigenspaceComponentNontrivial_of_classGroupModP_nontrivial`
by extracting the parity constraint that comes from σ-fixedness. -/
theorem exists_even_eigenspaceComponentNontrivial_of_sigma_fixed_nontrivial
    (hp_odd : p ≠ 2)
    (h_decomp : StandardEigenspaceDecompositionComplete
        (V := Additive (ClassGroupModP K p))
        (cyclotomicGalActionInstance (p := p) (K := K)))
    {v : Additive (ClassGroupModP K p)}
    (h_fixed : cyclotomicGalActionInstance (p := p) (K := K) (-1) v = v)
    (hv_ne : v ≠ 0) :
    ∃ k : ℕ, k < p - 1 ∧ Even k ∧ eigenspaceComponentNontrivial p K k := by
  classical
  -- v = ∑_k π_k v. If all even π_k v = 0, then by odd-vanishing (h_fixed) v = 0.
  have h_sum := h_decomp v
  by_contra h_all_trivial
  push Not at h_all_trivial
  apply hv_ne
  rw [← h_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_lt : k < p - 1 := by simpa using hk
  by_cases hk_even : Even k
  · -- For even k: V_k must be trivial (else h_all_trivial), so π_k v = 0.
    have h_proj_mem :
        standardEigenspaceProjection
            (cyclotomicGalActionInstance (p := p) (K := K)) k v ∈
          eigenspace (V := Additive (ClassGroupModP K p))
            (cyclotomicGalActionInstance (p := p) (K := K)) k :=
      standardEigenspaceProjection_mem_eigenspace _ k v
    by_contra h_proj_ne
    apply h_all_trivial k hk_lt hk_even
    exact ⟨_, h_proj_mem, h_proj_ne⟩
  · -- For odd k: π_k v = 0 by the shipped odd-vanishing lemma.
    have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_even
    exact standardEigenspaceProjection_odd_eq_zero_of_fixed_neg_one
      hp_odd _ h_fixed hk_odd

end BernoulliRegular

end
