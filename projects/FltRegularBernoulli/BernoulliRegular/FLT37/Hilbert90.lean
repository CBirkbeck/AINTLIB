module

public import BernoulliRegular.FLT37.PrimaryDescent
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import FltRegular.CaseII.AuxLemmas

/-!
# Hilbert 90 setup for `K/K⁺` (ticket FLT37b2b2-b)

For a CM cyclotomic field `K = ℚ(ζ_p)`, `Gal(K/K⁺) = {1, σ}` where `σ` is
complex conjugation. This file packages:

* `algebraMap_norm_eq_self_mul_complexConj`: for `x : K`,
  `algebraMap K⁺ K (Algebra.norm K⁺ x) = x * complexConj K x`. The
  degree-2 specialisation of `Algebra.norm_eq_prod_automorphisms`.
* `norm_complexConj_div_self_eq_one`: for non-zero `α : K`,
  `Algebra.norm K⁺ (σα/α) = 1` — the input to Hilbert 90.

Future companions in this file (b-hilbert90, b-coprime, b-kummer) will
build the chain leading to `σα/α = u·v^p` (FLT37b2b2-b).

## References

* Washington, *Introduction to Cyclotomic Fields*, Theorem 6.16.
* `groupCohomology.exists_div_of_norm_eq_one` (Hilbert 90 cyclic).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section NormComplexConj

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The Galois group `Gal(K/K⁺)` viewed as a `Finset` is `{1, complexConj K}`. -/
private theorem finset_univ_galois_eq [IsCMField K] :
    haveI : DecidableEq (K ≃ₐ[K⁺] K) := Classical.decEq _
    (Insert.insert (1 : K ≃ₐ[K⁺] K) {complexConj K}) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [(complexConj_ne_one K).symm]),
    Finset.card_singleton]
  have : Fintype.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
  omega

/-- For `K/K⁺` Galois of degree 2 with `Gal = {1, complexConj}`, the
algebraMap of the relative norm is `x · complexConj K x`. -/
theorem algebraMap_norm_eq_self_mul_complexConj [IsCMField K] (x : K) :
    algebraMap (K⁺) K (Algebra.norm (K⁺) x) = x * complexConj K x := by
  rw [Algebra.norm_eq_prod_automorphisms]
  classical
  rw [← finset_univ_galois_eq (K := K),
    Finset.prod_insert (by simp [(complexConj_ne_one K).symm])]
  simp

/-- For non-zero `α : K`, the element `σα/α` has Galois norm `1` over `K⁺`.
This is the standard Hilbert-90-input identity for the antisymmetry of σ. -/
theorem norm_complexConj_div_self_eq_one [IsCMField K]
    {α : K} (hα : α ≠ 0) :
    Algebra.norm (K⁺) (complexConj K α / α) = 1 := by
  apply FaithfulSMul.algebraMap_injective (K⁺) K
  rw [algebraMap_norm_eq_self_mul_complexConj (K := K), map_one,
    map_div₀, complexConj_apply_apply]
  have hcc : complexConj K α ≠ 0 := fun h => hα <| by
    have := congrArg (complexConj K) h
    rwa [complexConj_apply_apply, map_zero] at this
  field_simp

end NormComplexConj

/-! ## Hilbert 90: `σα/α = γ/σγ` (FLT37b2b2-b-hilbert90)

The cyclic Hilbert 90 in mathlib (`groupCohomology.exists_div_of_norm_eq_one`)
is stated for `K, L : Type` at universe 0. We therefore restrict our K to
universe 0 in this section. (This is no loss for concrete cyclotomic fields
like `CyclotomicField 37 ℚ`.) -/

section Hilbert90

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Every element of `Gal(K/K⁺)` is a power of `complexConj K`, since the
group has order 2. -/
private theorem mem_zpowers_complexConj [IsCMField K] (σ : K ≃ₐ[K⁺] K) :
    σ ∈ Subgroup.zpowers (complexConj K) := by
  rcases algEquiv_eq_one_or_complexConj σ with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

instance [IsCMField K] : IsCyclic (K ≃ₐ[K⁺] K) :=
  ⟨⟨complexConj K, mem_zpowers_complexConj K⟩⟩

/-- **Hilbert 90 specialisation for K/K⁺.** For non-zero `α : K`, there
exists `γ : Kˣ` such that `σα/α = γ / complexConj K γ`. -/
theorem exists_div_complexConj_eq_complexConj_div_self [IsCMField K]
    {α : K} (hα : α ≠ 0) :
    ∃ γ : Kˣ, (γ : K) / complexConj K (γ : K) = complexConj K α / α :=
  groupCohomology.exists_div_of_norm_eq_one
    (g := complexConj K) (mem_zpowers_complexConj K)
    (norm_complexConj_div_self_eq_one (K := K) hα)

end Hilbert90

/-! ## Coprime descent: `α · γ ∈ K⁺` (FLT37b2b2-b-coprime) -/

section CoprimeDescent

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- From the Hilbert-90 conclusion `γ/σγ = σα/α`, derive that `γ · α` is
σ-fixed. -/
theorem complexConj_mul_eq_self_of_div_eq [IsCMField K]
    {α : K} (hα : α ≠ 0) {γ : Kˣ}
    (h : (γ : K) / complexConj K (γ : K) = complexConj K α / α) :
    complexConj K ((γ : K) * α) = (γ : K) * α := by
  have hcγ : complexConj K (γ : K) ≠ 0 := fun heq => γ.ne_zero <| by
    have := congrArg (complexConj K) heq
    rwa [complexConj_apply_apply, map_zero] at this
  rw [div_eq_div_iff hcγ hα] at h
  rw [map_mul, mul_comm]
  exact h.symm

/-- Stronger version: there exists `δ : K⁺` with `algebraMap K⁺ K δ = γ · α`. -/
theorem exists_mem_Kplus_eq_mul_of_div_eq [IsCMField K]
    {α : K} (hα : α ≠ 0) {γ : Kˣ}
    (h : (γ : K) / complexConj K (γ : K) = complexConj K α / α) :
    ∃ δ : K⁺, (algebraMap K⁺ K δ : K) = (γ : K) * α := by
  have h_fix : complexConj K ((γ : K) * α) = (γ : K) * α :=
    complexConj_mul_eq_self_of_div_eq (K := K) hα h
  have h_mem : (γ : K) * α ∈ (K⁺ : Subfield K) :=
    (complexConj_eq_self_iff K ((γ : K) * α)).mp h_fix
  exact ⟨⟨(γ : K) * α, h_mem⟩, rfl⟩

end CoprimeDescent

/-! ## Norm formula for principal ideals (FLT37b2b2-d-norm-singleton)

For `K/K⁺` Galois of degree 2, the relative norm of a principal ideal
satisfies `(relNorm (a)).map = (a) · (σa)`. This is the singleton case
of the general formula `(relNorm 𝔞).map = 𝔞 · σ𝔞`, which underlies the
class-group descent of `[𝔞·σ𝔞]`. -/

section NormSingleton

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The integer norm `intNorm (𝓞 K⁺) (𝓞 K) a` mapped back to `𝓞 K`
equals `a · σa` (where `σ = ringOfIntegersComplexConj K`). -/
theorem algebraMap_intNorm_eq_self_mul_complexConj [IsCMField K] (a : 𝓞 K) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a) =
      a * ringOfIntegersComplexConj K a := by
  apply RingOfIntegers.ext
  rw [show ((algebraMap (𝓞 K⁺) (𝓞 K) (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a) : 𝓞 K) : K) =
      algebraMap (K⁺) K (algebraMap (𝓞 K⁺) (K⁺)
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K) a)) from
    (IsScalarTower.algebraMap_apply (𝓞 K⁺) K⁺ K _).symm]
  rw [Algebra.algebraMap_intNorm (K := K⁺) (L := K)]
  rw [algebraMap_norm_eq_self_mul_complexConj (K := K)]
  push_cast
  rfl

/-- **K⁺-relative integer norm of `ζ` is `1`** (cyclotomic CM case).
Since `σ(ζ) = ζ^{p-1}` and `ζ · ζ^{p-1} = ζ^p = 1`, the relative norm
`ζ · σ(ζ) = 1`. By injectivity of `algebraMap`, the norm is `1` in
`𝓞 K⁺`. -/
theorem zeta_intNorm_eq_one [IsCMField K] :
    Algebra.intNorm (𝓞 K⁺) (𝓞 K)
        (((zeta_spec p ℚ K).toInteger : 𝓞 K)) = 1 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K⁺) (𝓞 K)
  rw [algebraMap_intNorm_eq_self_mul_complexConj (K := K), map_one]
  -- σ(ζ) = ζ^(p-1), so ζ · σ(ζ) = ζ^p = 1.
  have h_conj_zeta : ringOfIntegersComplexConj K
      (((zeta_spec p ℚ K).toInteger : 𝓞 K)) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) :=
    complexConj_apply_zeta (p := p) (K := K)
  rw [h_conj_zeta]
  have hp_pos : 0 < p := hp.1.pos
  have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    zeta_toInteger_pow_eq_one p K
  rw [← pow_succ', Nat.sub_add_cancel hp_pos, h_zeta_p]

/-- **K⁺-relative integer norm of `ζ^m` is `1`** for any `m`. Follows
from `zeta_intNorm_eq_one` and multiplicativity of `intNorm`. -/
theorem zeta_pow_intNorm_eq_one [IsCMField K] (m : ℕ) :
    Algebra.intNorm (𝓞 K⁺) (𝓞 K)
        ((((((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit :
          (𝓞 K)ˣ) ^ m : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
  rw [Units.val_pow_eq_pow_val,
    show ((((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit :
        (𝓞 K)ˣ) : 𝓞 K) = ((zeta_spec p ℚ K).toInteger : 𝓞 K) from
      IsUnit.unit_spec _, map_pow,
    zeta_intNorm_eq_one (p := p) (K := K), one_pow]

/-- **`relNorm`-via-`map` formula for principal ideals (singleton case).**
`(relNorm (𝓞 K⁺) (Ideal.span {a})).map = Ideal.span {a} · Ideal.span {σa}`. -/
theorem map_relNorm_span_singleton_eq_mul_complexConj [IsCMField K] (a : 𝓞 K) :
    (Ideal.relNorm (𝓞 K⁺) (Ideal.span ({a} : Set (𝓞 K)))).map
        (algebraMap (𝓞 K⁺) (𝓞 K)) =
      Ideal.span ({a} : Set (𝓞 K)) *
        Ideal.span ({ringOfIntegersComplexConj K a} : Set (𝓞 K)) := by
  rw [Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton]
  rw [algebraMap_intNorm_eq_self_mul_complexConj (K := K)]
  rw [← Ideal.span_singleton_mul_span_singleton]

end NormSingleton

/-! ## Class descent of `[𝔞·σ𝔞]` for primary `(α) = 𝔞^p` (FLT37b2b2-d-class)

Combining the singleton norm formula with `pow_dvd_pow_iff_dvd` (Dedekind
domain UFM) yields the descent for the specific 𝔞 used in Vandiver Lemma 1:
when `(α) = 𝔞^p`, the class `[𝔞·σ𝔞] = [𝔞]²` lifts to `Cl(𝓞 K⁺)` via
`relNorm 𝔞`. -/

section ClassDescentFromSingleton

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Norm formula on `𝔞` from the equation `(α) = 𝔞^p`.** Using only the
singleton case of the relNorm formula and `pow_left_inj` (via `Ideal`'s
`UniqueFactorizationMonoid` structure), we derive the general formula
for our specific 𝔞. -/
theorem map_relNorm_eq_mul_complexConj_of_pow [IsCMField K]
    {α : 𝓞 K} (_hα : α ≠ 0) {𝔞 : Ideal (𝓞 K)}
    (hp_pos : 0 < p)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p) :
    (Ideal.relNorm (𝓞 K⁺) 𝔞).map (algebraMap (𝓞 K⁺) (𝓞 K)) =
      𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  have h_singleton :
      (Ideal.relNorm (𝓞 K⁺) (Ideal.span ({α} : Set (𝓞 K)))).map
          (algebraMap (𝓞 K⁺) (𝓞 K)) =
        Ideal.span ({α} : Set (𝓞 K)) *
          Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) :=
    map_relNorm_span_singleton_eq_mul_complexConj (K := K) α
  rw [h] at h_singleton
  -- h_singleton: (relNorm (𝔞^p)).map = 𝔞^p · (σ_ideal_α^p as singleton)
  -- σ_ideal_α^p as singleton = (σα) as ideal = σ(𝔞^p) = (σ𝔞)^p
  have h_conj : (Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) :
      Ideal (𝓞 K)) =
      (𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p :=
    complexConj_ideal_pow_eq (K := K) h
  rw [h_conj, ← mul_pow, map_pow, Ideal.map_pow] at h_singleton
  -- Now h_singleton: ((Ideal.map _ (relNorm 𝔞)))^p = (𝔞 · σ𝔞)^p
  -- Apply pow_dvd_pow_iff_dvd (UFM property of Ideal A for A Dedekind)
  have hp_ne : p ≠ 0 := hp_pos.ne'
  -- From `X^p = Y^p` derive `X = Y` via antisymmetry
  -- For ideals: `A ∣ B ↔ B ≤ A`
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hp_ne]
    exact h_singleton.symm.dvd
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hp_ne]
    exact h_singleton.dvd

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **No-primary intermediate: `[𝔞·σ𝔞] = 1` from `(α) = 𝔞^p` + VC.**
This follows directly from the d-class result + Vandiver's conjecture
applied to the relNorm-witness in `Cl(𝓞 K⁺)`, *without* requiring
primarity of `α`. The classical Vandiver proof's primary hypothesis is
needed only to bridge from this to `[𝔞] = 1` (i.e., for `[σ𝔞] = [𝔞]`). -/
theorem classGroup_mul_complexConj_eq_one_of_pow_of_VC
    [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {α : 𝓞 K} (hα : α ≠ 0) {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p) :
    have h𝔞m_nz : 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ :=
      (map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞_nz
    have h_mul_nz :
        𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨h𝔞_nz, h𝔞m_nz⟩
    ClassGroup.mk0
        (⟨𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr h_mul_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) = 1 := by
  intro h𝔞m_nz h_mul_nz
  have hp_pos : 0 < p := hp.1.pos
  have h_norm := map_relNorm_eq_mul_complexConj_of_pow (p := p) (K := K) hα hp_pos h
  have h_relNorm_nz : Ideal.relNorm (𝓞 K⁺) 𝔞 ≠ ⊥ :=
    (Ideal.relNorm_eq_bot_iff (R := 𝓞 K⁺) (S := 𝓞 K) (I := 𝔞)).not.mpr h𝔞_nz
  -- [𝔞·σ𝔞] = classGroupMap [relNorm 𝔞]
  have h_image : ClassGroup.mk0
      (⟨𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr h_mul_nz⟩
        : nonZeroDivisors (Ideal (𝓞 K))) =
      classGroupMap K (ClassGroup.mk0 ⟨Ideal.relNorm (𝓞 K⁺) 𝔞,
        mem_nonZeroDivisors_iff_ne_zero.mpr h_relNorm_nz⟩) := by
    rw [ClassGroup.extensionMap_mk0]
    congr 1
    exact Subtype.ext h_norm.symm
  -- Show [relNorm 𝔞] = 1 in Cl(𝓞 K⁺) under VC.
  have h_𝔠_pow_principal : (Ideal.relNorm (𝓞 K⁺) 𝔞 ^ p).IsPrincipal := by
    rw [show (Ideal.relNorm (𝓞 K⁺) 𝔞 ^ p : Ideal (𝓞 (K⁺))) =
        Ideal.relNorm (𝓞 K⁺) (𝔞 ^ p) from (map_pow (Ideal.relNorm (𝓞 K⁺)) 𝔞 p).symm,
      ← h]
    rw [Ideal.relNorm_singleton]
    exact ⟨_, rfl⟩
  -- [relNorm 𝔞] has order dividing p in Cl(𝓞 K⁺).
  have h_order_p : ClassGroup.mk0
      (⟨Ideal.relNorm (𝓞 K⁺) 𝔞,
        mem_nonZeroDivisors_iff_ne_zero.mpr h_relNorm_nz⟩
        : nonZeroDivisors (Ideal (𝓞 K⁺))) ^ p = 1 := by
    have hpow_mem : Ideal.relNorm (𝓞 K⁺) 𝔞 ^ p ∈ nonZeroDivisors (Ideal (𝓞 K⁺)) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero p h_relNorm_nz)
    rw [show ClassGroup.mk0
        (⟨Ideal.relNorm (𝓞 K⁺) 𝔞, _⟩ : nonZeroDivisors (Ideal (𝓞 K⁺))) ^ p =
        ClassGroup.mk0 (⟨Ideal.relNorm (𝓞 K⁺) 𝔞 ^ p, hpow_mem⟩
          : nonZeroDivisors (Ideal (𝓞 K⁺))) from by rw [← map_pow]; rfl]
    exact (ClassGroup.mk0_eq_one_iff hpow_mem).mpr h_𝔠_pow_principal
  -- Under VC, [relNorm 𝔞] = 1.
  have h_𝔠_one : ClassGroup.mk0
      (⟨Ideal.relNorm (𝓞 K⁺) 𝔞,
        mem_nonZeroDivisors_iff_ne_zero.mpr h_relNorm_nz⟩
        : nonZeroDivisors (Ideal (𝓞 K⁺))) = 1 := by
    have h_order_dvd_gcd :
        orderOf (ClassGroup.mk0 (⟨Ideal.relNorm (𝓞 K⁺) 𝔞,
          mem_nonZeroDivisors_iff_ne_zero.mpr h_relNorm_nz⟩
            : nonZeroDivisors (Ideal (𝓞 K⁺)))) ∣
          Nat.gcd p (Fintype.card (ClassGroup (𝓞 K⁺))) := by
      rw [Nat.dvd_gcd_iff]
      exact ⟨orderOf_dvd_of_pow_eq_one h_order_p, orderOf_dvd_card⟩
    rw [h_VC] at h_order_dvd_gcd
    rw [← orderOf_eq_one_iff, Nat.dvd_one.mp h_order_dvd_gcd]
  rw [h_image, h_𝔠_one, map_one]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Element-level form of the no-primary intermediate.** Under VC
and `(α) = 𝔞^p`, the ideal `𝔞 · σ𝔞` is principal in `𝓞 K`. -/
theorem isPrincipal_mul_complexConj_of_pow_of_VC
    [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {α : 𝓞 K} (hα : α ≠ 0) {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p) :
    (𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrincipal := by
  have h𝔞m_nz : 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ :=
    (map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞_nz
  have h_mul_nz :
      𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨h𝔞_nz, h𝔞m_nz⟩
  exact (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr h_mul_nz)).mp
    (classGroup_mul_complexConj_eq_one_of_pow_of_VC (p := p) (K := K) h_VC hα h𝔞_nz h)

/-- **Vandiver Lemma 1, conditional on `[σ𝔞] = [𝔞]`.** Given
`(α) = 𝔞^p`, Vandiver's conjecture, and the class equality
`[σ𝔞] = [𝔞]` (the FLT37b2b2-c output), `𝔞` is principal in `𝓞 K`.

This composes `d-class` (the relNorm formula on 𝔞) with the
`(p+1)/2` trick + Vandiver's conjecture to discharge the descent
hypothesis of `isPrincipal_of_class_eq_complexConj_of_VC` automatically. -/
theorem isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC
    (hp_odd : p ≠ 2)
    [IsCMField K]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (K⁺)))))
    {α : 𝓞 K} (hα : α ≠ 0) {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p)
    (h_class_eq :
      ClassGroup.mk0
          (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              ((map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) =
        ClassGroup.mk0
          (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ : nonZeroDivisors (Ideal (𝓞 K)))) :
    𝔞.IsPrincipal := by
  -- Derive [𝔞]^p = 1 from (α) = 𝔞^p
  have h_pow_principal : (𝔞 ^ p).IsPrincipal := by
    rw [← h]; exact ⟨α, rfl⟩
  have h_pow_classOne : ClassGroup.mk0
      (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ : nonZeroDivisors (Ideal (𝓞 K))) ^ p = 1 := by
    rw [show ClassGroup.mk0
        (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ : nonZeroDivisors (Ideal (𝓞 K))) ^ p =
        ClassGroup.mk0
          (⟨𝔞 ^ p,
              mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero p h𝔞_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) from by rw [← map_pow]; rfl]
    exact (ClassGroup.mk0_eq_one_iff _).mpr h_pow_principal
  -- Construct h_sq_in_image: [𝔞]² ∈ image classGroupMap
  -- Use d-class result + h_class_eq to derive
  have h_sq_in_image : ∃ 𝔠₀ : ClassGroup (𝓞 (K⁺)),
      classGroupMap K 𝔠₀ =
        ClassGroup.mk0 (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) ^ 2 := by
    have hp_pos : 0 < p := hp.1.pos
    have h_norm := map_relNorm_eq_mul_complexConj_of_pow (p := p) (K := K) hα hp_pos h
    have h_relNorm_nz : Ideal.relNorm (𝓞 K⁺) 𝔞 ≠ ⊥ :=
      (Ideal.relNorm_eq_bot_iff (R := 𝓞 K⁺) (S := 𝓞 K) (I := 𝔞)).not.mpr h𝔞_nz
    have h𝔞m_nz :
        𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ :=
      (map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞_nz
    have h_mul_nz :
        𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨h𝔞_nz, h𝔞m_nz⟩
    refine ⟨ClassGroup.mk0
        ⟨Ideal.relNorm (𝓞 K⁺) 𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h_relNorm_nz⟩, ?_⟩
    -- classGroupMap [relNorm 𝔞] = mk0 ⟨(relNorm 𝔞).map, _⟩ = mk0 ⟨𝔞·σ𝔞, _⟩
    -- = mk0 ⟨𝔞, _⟩ · mk0 ⟨σ𝔞, _⟩ = mk0 ⟨𝔞, _⟩ · mk0 ⟨𝔞, _⟩ (using h_class_eq) = (mk0 ⟨𝔞, _⟩)²
    rw [ClassGroup.extensionMap_mk0]
    have h_eq1 : ClassGroup.mk0
        (⟨(Ideal.relNorm (𝓞 K⁺) 𝔞).map (algebraMap (𝓞 K⁺) (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr (h_norm ▸ h_mul_nz)⟩
          : nonZeroDivisors (Ideal (𝓞 K))) =
        ClassGroup.mk0
        (⟨𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr h_mul_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) := by
      congr 1
      exact Subtype.ext h_norm
    convert h_eq1 using 1
    have h_prod : (⟨𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr h_mul_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) =
        (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) *
        (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞m_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) := rfl
    rw [h_prod, map_mul, h_class_eq, sq]
  -- Apply the isPrincipal_of_class_eq_complexConj_of_VC theorem
  exact isPrincipal_of_class_eq_complexConj_of_VC
    (p := p) (hp_odd := hp_odd) (K := K) h_VC h𝔞_nz h_pow_classOne h_sq_in_image

end ClassDescentFromSingleton

/-! ## b-kummer-local-prime: σα/α has high `(ζ-1)`-valuation (FLT37b2b2-b-kummer-1)

For primary α, the difference `σα - α` is divisible by `(ζ-1)^{2p}` in
`𝓞 K`. We package this as the existence of an explicit witness `η`. -/

section KummerLocalPrime

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- For primary α, `σα - α = (ζ - 1)^{2p} · η` for some `η ∈ 𝓞 K`. -/
theorem exists_eq_zetaSubOne_pow_mul_of_isPrimary [IsCMField K]
    {α : 𝓞 K} (hα_primary : IsPrimary p α) :
    ∃ η : 𝓞 K, ringOfIntegersComplexConj K α - α =
      zetaSubOne p K ^ (2 * p) * η := by
  obtain ⟨η, hη⟩ := zetaSubOne_pow_dvd_sub_complexConj hα_primary
  refine ⟨-η, ?_⟩
  have : (α - ringOfIntegersComplexConj K α : 𝓞 K) =
      zetaSubOne p K ^ (2 * p) * η := hη
  linear_combination -this

/-- The dual form: `α - σα = (ζ - 1)^{2p} · η` for some `η ∈ 𝓞 K`. -/
theorem exists_self_sub_complexConj_eq_zetaSubOne_pow_mul_of_isPrimary [IsCMField K]
    {α : 𝓞 K} (hα_primary : IsPrimary p α) :
    ∃ η : 𝓞 K, α - ringOfIntegersComplexConj K α =
      zetaSubOne p K ^ (2 * p) * η :=
  zetaSubOne_pow_dvd_sub_complexConj hα_primary

/-- Direct divisibility form for the σα - α additive identity. -/
theorem zetaSubOne_pow_dvd_complexConj_sub_self_of_isPrimary [IsCMField K]
    {α : 𝓞 K} (hα_primary : IsPrimary p α) :
    zetaSubOne p K ^ (2 * p) ∣ ringOfIntegersComplexConj K α - α :=
  exists_eq_zetaSubOne_pow_mul_of_isPrimary p K hα_primary

/-- **Multiplicative form for primary units.** For a primary unit
`u : (𝓞 K)ˣ` (i.e., `IsPrimary p u`), we have
`σu · u⁻¹ - 1 = (ζ - 1)^{2p} · η` for some `η ∈ 𝓞 K`. -/
theorem exists_complexConj_mul_inv_sub_one_of_isPrimary [IsCMField K]
    {u : (𝓞 K)ˣ} (hu_primary : IsPrimary p (u : 𝓞 K)) :
    ∃ η : 𝓞 K,
      ringOfIntegersComplexConj K (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 =
      zetaSubOne p K ^ (2 * p) * η := by
  obtain ⟨η, hη⟩ := exists_eq_zetaSubOne_pow_mul_of_isPrimary p K hu_primary
  refine ⟨η * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K), ?_⟩
  have huinv : ((u : 𝓞 K)) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := Units.mul_inv u
  have hrw : (ringOfIntegersComplexConj K (u : 𝓞 K) - (u : 𝓞 K)) *
      ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
      zetaSubOne p K ^ (2 * p) * η * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [hη]
  rw [sub_mul, huinv] at hrw
  linear_combination hrw

/-- Divisibility form of the multiplicative Kummer-local identity:
`(ζ - 1)^{2p}` divides `σu · u⁻¹ - 1` for any primary unit `u`. -/
theorem zetaSubOne_pow_dvd_complexConj_mul_inv_sub_one_of_isPrimary [IsCMField K]
    {u : (𝓞 K)ˣ} (hu_primary : IsPrimary p (u : 𝓞 K)) :
    zetaSubOne p K ^ (2 * p) ∣
      ringOfIntegersComplexConj K (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 :=
  exists_complexConj_mul_inv_sub_one_of_isPrimary p K hu_primary

/-- **Inverse-direction multiplicative form for primary units.**
For a primary unit `u : (𝓞 K)ˣ`, also `u · σu⁻¹ - 1 ∈ ((ζ-1))^{2p}`,
by applying complex conjugation to the σu·u⁻¹ form (using that
complex conjugation is an involution and (ζ-1) is its own associate
under σ). -/
theorem zetaSubOne_pow_dvd_self_mul_complexConj_inv_sub_one_of_isPrimary
    [IsCMField K] {u : (𝓞 K)ˣ} (hu_primary : IsPrimary p (u : 𝓞 K)) :
    zetaSubOne p K ^ (2 * p) ∣
      (u : 𝓞 K) * ringOfIntegersComplexConj K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
  -- Apply σ to the σu·u⁻¹ - 1 ≡ 0 statement
  have h := zetaSubOne_pow_dvd_complexConj_mul_inv_sub_one_of_isPrimary
    p K hu_primary
  have h_apply : ringOfIntegersComplexConj K (zetaSubOne p K ^ (2 * p)) ∣
      ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K (u : 𝓞 K) *
          ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1) :=
    map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h
  rw [map_sub, map_mul, map_one] at h_apply
  -- σ(σu) = u
  have h_sigma_sq : ringOfIntegersComplexConj K
      (ringOfIntegersComplexConj K (u : 𝓞 K)) = (u : 𝓞 K) := by
    apply RingOfIntegers.ext
    simp
  rw [h_sigma_sq] at h_apply
  exact (associated_complexConj_zetaSubOne_pow p K (2 * p)).dvd.trans h_apply

/-- **Existence form of the inverse-direction multiplicative identity.** -/
theorem exists_self_mul_complexConj_inv_sub_one_eq_of_isPrimary [IsCMField K]
    {u : (𝓞 K)ˣ} (hu_primary : IsPrimary p (u : 𝓞 K)) :
    ∃ η : 𝓞 K,
      (u : 𝓞 K) * ringOfIntegersComplexConj K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 =
      zetaSubOne p K ^ (2 * p) * η :=
  zetaSubOne_pow_dvd_self_mul_complexConj_inv_sub_one_of_isPrimary p K hu_primary

end KummerLocalPrime

end FLT37

end BernoulliRegular

end
