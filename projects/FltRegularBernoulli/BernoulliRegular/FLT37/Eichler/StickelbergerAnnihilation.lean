module

public import BernoulliRegular.FLT37.Eichler.StickelbergerAction

/-!
# Stickelberger annihilation: the canonical-action dictionary (foundational leaf)

This file is a foundational leaf of the **L-ann** theorem — that the integral
Stickelberger element annihilates `ClassGroupModP K p` (the deep core of the
easy-direction Herbrand bound, Washington GTM 83 §6.2 / Stickelberger's
theorem). The strategy of L-ann is:

* The Gauss-sum prime factorisation (Washington Thm 6.10) shows that, for each
  prime `𝔮` of `𝓞 K` above some `ℓ ≠ p`, the ideal `𝔮 ^ θ_int` is principal,
  where the group-ring exponent acts on `𝔮` by Galois conjugation.
* Hence the class of `𝔮 ^ θ_int` is trivial in `ClassGroupModP K p`.
* Prime classes generate, so `θ_int` annihilates all of `ClassGroupModP K p`.

The bridge between the **ideal-theoretic** statement ("`θ_int` acts on `𝔮` by
Galois conjugation and the result is principal") and the **module-theoretic**
group-ring action `classGroupModPGroupRingAction` (built in
`StickelbergerAction.lean`, the language in which the Stickelberger eigenvalue
`= B_{1,χ⁻¹}` is read off) is exactly the content of this file: the canonical
cyclotomic group-ring action of a basis element `single a 1` on a class is the
Galois conjugate of that class.

## Main results

* `classGroupModPGroupRingAction_instance_single_apply`: the canonical
  group-ring action of `single a 1` on a module element `v` is the additive
  image of the multiplicative Galois action `cyclotomicGalActionMonoidHomModP a`
  on `v.toMul`.
* `classGroupModPGroupRingAction_instance_single_mk`: the canonical group-ring
  action of `single a 1` on the additive class of `QuotientGroup.mk c` is the
  additive class of `QuotientGroup.mk (cyclotomicGalActionMonoidHom a c)`.
* `classGroupModPGroupRingAction_instance_single_mk0`: the canonical group-ring
  action of `single a 1` on the additive class of the class of `mk0 I`
  (`I : (Ideal (𝓞 K))⁰`) is the additive class of the class of the Galois
  conjugate `mk0 (cyclotomicGaloisConjugate a I)`. This is the dictionary that
  turns ideal-theoretic Galois conjugation (what the Gauss-sum factorisation
  produces) into the group-ring module action (what L-ann annihilates).

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.2 (Stickelberger's
  theorem, Thm 6.10).
* Diekmann, *FLT for regular primes*, §4 (Stickelberger / Herbrand).
-/

@[expose] public section

noncomputable section

open NumberField MonoidAlgebra
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace Eichler

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Canonical group-ring action on a basis element.** The canonical cyclotomic
group-ring action (via `cyclotomicGalActionInstance`) of `single a 1` on a
module element `v : Additive (ClassGroupModP K p)` equals the additive image of
the multiplicative Galois action `cyclotomicGalActionMonoidHomModP a` on
`v.toMul`. -/
theorem classGroupModPGroupRingAction_instance_single_apply
    (a : CyclotomicUnitDelta p) (v : ClassGroupModPMod p K) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1) v =
      Additive.ofMul
        (cyclotomicGalActionMonoidHomModP (p := p) (K := K) a v.toMul) := by
  rw [classGroupModPGroupRingAction_instance_single]
  rfl

/-- **Canonical group-ring action on a quotient class.** The canonical
group-ring action of `single a 1` on the additive class of `QuotientGroup.mk c`
(for `c : ClassGroup (𝓞 K)`) is the additive class of
`QuotientGroup.mk (cyclotomicGalActionMonoidHom a c)`. -/
theorem classGroupModPGroupRingAction_instance_single_mk
    (a : CyclotomicUnitDelta p) (c : ClassGroup (𝓞 K)) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1)
        (Additive.ofMul (QuotientGroup.mk c : ClassGroupModP K p)) =
      Additive.ofMul
        (QuotientGroup.mk
          (cyclotomicGalActionMonoidHom (p := p) (K := K) a c) :
          ClassGroupModP K p) := by
  rw [classGroupModPGroupRingAction_instance_single_apply]
  congr 1

/-- **The canonical-action dictionary on integer-ideal classes.** The canonical
group-ring action of `single a 1` on the additive class of the class of an
integer ideal `mk0 I` is the additive class of the class of the Galois conjugate
`mk0 (cyclotomicGaloisConjugate a I)`. -/
theorem classGroupModPGroupRingAction_instance_single_mk0
    (a : CyclotomicUnitDelta p) (I : (Ideal (𝓞 K))⁰) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1)
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      Additive.ofMul
        (QuotientGroup.mk
          (ClassGroup.mk0
            (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I)) :
          ClassGroupModP K p) := by
  rw [classGroupModPGroupRingAction_instance_single_mk]
  congr 2
  change cyclotomicGalActionOnClassGroup (p := p) (K := K) a (ClassGroup.mk0 I) = _
  rw [cyclotomicGalActionOnClassGroup_mk0]
  rfl

/-- **Per-conjugate annihilation.** If the Galois conjugate `σ_a I` of an integer
ideal `I` is principal, then the canonical group-ring action of `single a 1`
sends the additive class of `mk0 I` to `0` in `Additive (ClassGroupModP K p)`. -/
theorem classGroupModPGroupRingAction_instance_single_mk0_eq_zero_of_isPrincipal
    (a : CyclotomicUnitDelta p) (I : (Ideal (𝓞 K))⁰)
    (hI : (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I).1.IsPrincipal) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1)
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      0 := by
  rw [classGroupModPGroupRingAction_instance_single_mk0]
  have hone : ClassGroup.mk0
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) =
      (1 : ClassGroup (𝓞 K)) :=
    (ClassGroup.mk0_eq_one_iff
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I).2).mpr hI
  rw [hone, QuotientGroup.mk_one, ofMul_one]

/-- **Leaf 3.** For the canonical cyclotomic group-ring action and a nonzero
integer ideal `I`, an arbitrary group-ring element `x` acts on the class
`[mk0 I]` as the sum over its support of the coefficient times the Galois
conjugate class:

  `ρ x [mk0 I] = ∑_{a ∈ supp x} x(a) • [mk0 (σ_a I)]`. -/
theorem classGroupModPGroupRingAction_instance_apply_mk0
    (x : MonoidAlgebra (ZMod p) (CyclotomicUnitDelta p)) (I : (Ideal (𝓞 K))⁰) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K)) x
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      x.sum fun a e ↦
        e • Additive.ofMul
          (QuotientGroup.mk
            (ClassGroup.mk0
              (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I)) :
            ClassGroupModP K p) := by
  rw [classGroupModPGroupRingAction, MonoidAlgebra.lift_apply,
    LinearMap.finsupp_sum_apply]
  refine Finsupp.sum_congr fun a _ ↦ ?_
  rw [LinearMap.smul_apply]
  congr 1
  rw [← classGroupModPGroupRingAction_single (p := p) (K := K)
    (cyclotomicGalActionInstance (p := p) (K := K)) a]
  exact classGroupModPGroupRingAction_instance_single_mk0 (p := p) (K := K) a I

/-- The set of **prime ideal classes** in `Additive (ClassGroupModP K p)`: the
additive classes `[mk0 𝔮]` for nonzero prime ideals `𝔮 ⊆ 𝓞 K`. This is the
candidate generating set of `ClassGroupModP K p`. -/
def primeClassSet : Set (ClassGroupModPMod p K) :=
  {v | ∃ (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ∈ (Ideal (𝓞 K))⁰), 𝔮.IsPrime ∧
    v = Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 ⟨𝔮, h𝔮⟩) : ClassGroupModP K p)}

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Generation core.** Every integer-ideal class `[mk0 I]` lies in the
`ZMod p`-submodule generated by the prime ideal classes. -/
theorem mem_span_primeClassSet (I : (Ideal (𝓞 K))⁰) :
    Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) ∈
      Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) := by
  suffices h : ∀ (J : Ideal (𝓞 K)) (hJ : J ∈ (Ideal (𝓞 K))⁰),
      Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 ⟨J, hJ⟩) : ClassGroupModP K p) ∈
        Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) by
    simpa using h I.1 I.2
  intro J
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro hJ
    exact absurd (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (by simp)
  | h₂ J hJunit =>
    intro hJ
    have hone : ClassGroup.mk0 (⟨J, hJ⟩ : (Ideal (𝓞 K))⁰) = (1 : ClassGroup (𝓞 K)) :=
      (ClassGroup.mk0_eq_one_iff hJ).mpr (by
        show J.IsPrincipal
        rw [Ideal.isUnit_iff.mp hJunit]
        infer_instance)
    have hzero : Additive.ofMul
        (QuotientGroup.mk (ClassGroup.mk0 (⟨J, hJ⟩ : (Ideal (𝓞 K))⁰)) :
          ClassGroupModP K p) = 0 := by
      rw [hone, QuotientGroup.mk_one, ofMul_one]
    rw [hzero]
    exact Submodule.zero_mem _
  | h₃ a 𝔭 ha_ne h𝔭_prime IH =>
    intro hJ
    have h𝔭_ne : 𝔭 ≠ 0 := h𝔭_prime.ne_zero
    have h𝔭_mem : 𝔭 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔭_ne
    have ha_mem : a ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr ha_ne
    have hsplit : ClassGroup.mk0 (⟨𝔭 * a, hJ⟩ : (Ideal (𝓞 K))⁰) =
        ClassGroup.mk0 (⟨𝔭, h𝔭_mem⟩ : (Ideal (𝓞 K))⁰) *
          ClassGroup.mk0 (⟨a, ha_mem⟩ : (Ideal (𝓞 K))⁰) := by
      rw [← map_mul]
      rfl
    have hsum : Additive.ofMul
        (QuotientGroup.mk (ClassGroup.mk0 (⟨𝔭 * a, hJ⟩ : (Ideal (𝓞 K))⁰)) :
          ClassGroupModP K p) =
        Additive.ofMul
          (QuotientGroup.mk (ClassGroup.mk0 (⟨𝔭, h𝔭_mem⟩ : (Ideal (𝓞 K))⁰)) :
            ClassGroupModP K p) +
        Additive.ofMul
          (QuotientGroup.mk (ClassGroup.mk0 (⟨a, ha_mem⟩ : (Ideal (𝓞 K))⁰)) :
            ClassGroupModP K p) := by
      rw [hsplit, QuotientGroup.mk_mul, ofMul_mul]
    rw [hsum]
    refine Submodule.add_mem _ ?_ (IH ha_mem)
    apply Submodule.subset_span
    exact ⟨𝔭, h𝔭_mem, (Ideal.prime_iff_isPrime h𝔭_ne).mp h𝔭_prime, rfl⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Leaf 5.** The prime ideal classes generate all of
`Additive (ClassGroupModP K p)`: their `ZMod p`-span is `⊤`. -/
theorem span_primeClassSet_eq_top :
    Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom p :
    ClassGroup (𝓞 K) →* _).range) v.toMul
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hv : v = Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) :=
    Additive.toMul.injective hc.symm
  rw [hv]
  exact mem_span_primeClassSet (p := p) (K := K) I

/-- **Leaf 6 (assembly).** If a fixed group-ring element `x` annihilates the
class `[mk0 𝔮]` of every nonzero prime ideal `𝔮`, then the canonical group-ring
action of `x` is the zero endomorphism on all of
`Additive (ClassGroupModP K p)`. -/
theorem classGroupModPGroupRingAction_eq_zero_of_annihilates_primes
    (x : MonoidAlgebra (ZMod p) (CyclotomicUnitDelta p))
    (H : ∀ (𝔮 : Ideal (𝓞 K)) (_ : 𝔮.IsPrime) (h𝔮ne : 𝔮 ≠ ⊥),
      classGroupModPGroupRingAction (p := p) (K := K)
          (cyclotomicGalActionInstance (p := p) (K := K)) x
          (Additive.ofMul
            (QuotientGroup.mk
              (ClassGroup.mk0 ⟨𝔮, mem_nonZeroDivisors_iff_ne_zero.mpr
                (by rwa [Ideal.zero_eq_bot])⟩) :
              ClassGroupModP K p)) = 0) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K)) x = 0 := by
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← span_primeClassSet_eq_top (p := p) (K := K),
    Submodule.span_le]
  rintro v ⟨𝔮, h𝔮mem, h𝔮prime, rfl⟩
  have h𝔮ne : 𝔮 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp h𝔮mem
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  exact H 𝔮 h𝔮prime h𝔮ne

end Eichler

end FLT37

end BernoulliRegular

end
