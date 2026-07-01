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

open NumberField
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
`v.toMul`.

This is the concrete instance form of `classGroupModPGroupRingAction_single`,
unfolded through the `ZMod p`-linear / `Additive` packaging
(`cyclotomicGalActionLinearModP`). -/
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
`QuotientGroup.mk (cyclotomicGalActionMonoidHom a c)`.

This unfolds `cyclotomicGalActionMonoidHomModP` through `QuotientGroup.map`. -/
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
  -- `cyclotomicGalActionMonoidHomModP a (mk c) = mk (cyclotomicGalActionMonoidHom a c)`
  -- since the ModP action is `QuotientGroup.map _ _ (cyclotomicGalActionMonoidHom a) _`,
  -- so this holds by `congr` on the (definitionally equal) `Additive.ofMul` arguments.
  congr 1

/-- **The canonical-action dictionary on integer-ideal classes.** The canonical
group-ring action of `single a 1` on the additive class of the class of an
integer ideal `mk0 I` is the additive class of the class of the Galois conjugate
`mk0 (cyclotomicGaloisConjugate a I)`.

This is the precise bridge that L-ann uses: the Gauss-sum prime factorisation
produces an ideal identity in which the group-ring exponent acts on a prime by
Galois conjugation; this lemma states that the same Galois conjugation is the
group-ring module action `classGroupModPGroupRingAction (single a 1)`. -/
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
  -- `cyclotomicGalActionMonoidHom a (mk0 I) = mk0 (σ_a I)`.
  congr 2
  change cyclotomicGalActionOnClassGroup (p := p) (K := K) a (ClassGroup.mk0 I) = _
  rw [cyclotomicGalActionOnClassGroup_mk0]
  rfl

/-- **Per-conjugate annihilation.** If the Galois conjugate `σ_a I` of an integer
ideal `I` is principal, then the canonical group-ring action of `single a 1`
sends the additive class of `mk0 I` to `0` in `Additive (ClassGroupModP K p)`.

This is the atomic annihilation step underlying L-ann: the Gauss-sum
factorisation makes the relevant Galois-conjugate ideals principal (their class
trivial), so each contributes `0` to the group-ring action. -/
theorem classGroupModPGroupRingAction_instance_single_mk0_eq_zero_of_isPrincipal
    (a : CyclotomicUnitDelta p) (I : (Ideal (𝓞 K))⁰)
    (hI : (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I).1.IsPrincipal) :
    classGroupModPGroupRingAction (p := p) (K := K)
        (cyclotomicGalActionInstance (p := p) (K := K))
        (MonoidAlgebra.single a 1)
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      0 := by
  rw [classGroupModPGroupRingAction_instance_single_mk0]
  -- The conjugate class `mk0 (σ_a I)` is trivial in `ClassGroup`, hence its
  -- image in `ClassGroupModP` is `1`, and `Additive.ofMul 1 = 0`.
  have hone : ClassGroup.mk0
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I) =
      (1 : ClassGroup (𝓞 K)) :=
    (ClassGroup.mk0_eq_one_iff
      (cyclotomicGaloisConjugateNonZeroDivisors (p := p) (K := K) a I).2).mpr hI
  rw [hone, QuotientGroup.mk_one, ofMul_one]

/-! ### Leaf 3: a group-ring element acts on a prime class as a sum over conjugates

The group-ring action of an arbitrary element
`x : MonoidAlgebra (ZMod p) (CyclotomicUnitDelta p)` on an integer-ideal class
`[mk0 I]` is the (finite, `ZMod p`-linear) sum over the support of `x` of the
coefficient `e` scaling the Galois-conjugate class `[mk0 (σ_a I)]`. This is the
linearity expansion of the dictionary
`classGroupModPGroupRingAction_instance_single_mk0`, exactly mirroring the
`map_sum` / `Finsupp.sum` / `smul_apply` pattern in
`stickelbergerCorrectedInt_action_eigenvector`. -/

/-- **Leaf 3.** For the canonical cyclotomic group-ring action and a nonzero
integer ideal `I`, an arbitrary group-ring element `x` acts on the class
`[mk0 I]` as the sum over its support of the coefficient times the Galois
conjugate class:

  `ρ x [mk0 I] = ∑_{a ∈ supp x} x(a) • [mk0 (σ_a I)]`.

This expands the action into the per-basis-element dictionary
(`classGroupModPGroupRingAction_instance_single_mk0`) via `lift_apply` +
`Finsupp.sum` linearity. -/
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
  -- Expand the action via `lift_apply` into a `Finsupp.sum` of `e • ρ a`, evaluate
  -- termwise (`finsupp_sum_apply` + `smul_apply`), then rewrite each `ρ a [mk0 I]`
  -- by the canonical-action dictionary.
  rw [classGroupModPGroupRingAction, MonoidAlgebra.lift_apply,
    LinearMap.finsupp_sum_apply]
  refine Finsupp.sum_congr fun a _ ↦ ?_
  rw [LinearMap.smul_apply]
  -- `cyclotomicGalActionInstance a [mk0 I] = [mk0 (σ_a I)]` is the dictionary,
  -- since `classGroupModPGroupRingAction ρ (single a 1) = ρ a`.
  congr 1
  rw [← classGroupModPGroupRingAction_single (p := p) (K := K)
    (cyclotomicGalActionInstance (p := p) (K := K)) a]
  exact classGroupModPGroupRingAction_instance_single_mk0 (p := p) (K := K) a I

/-! ### Leaf 5: prime ideal classes generate `ClassGroupModP K p`

In the Dedekind domain `𝓞 K`, every nonzero ideal factors into prime ideals
(`UniqueFactorizationMonoid`), and `ClassGroup.mk0` is multiplicative, so every
ideal class is a product (additively, a `ZMod p`-linear combination) of prime
ideal classes. Hence the prime ideal classes generate
`Additive (ClassGroupModP K p)`. -/

/-- The set of **prime ideal classes** in `Additive (ClassGroupModP K p)`: the
additive classes `[mk0 𝔮]` for nonzero prime ideals `𝔮 ⊆ 𝓞 K`. This is the
candidate generating set of `ClassGroupModP K p`. -/
def primeClassSet : Set (ClassGroupModPMod p K) :=
  {v | ∃ (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ∈ (Ideal (𝓞 K))⁰), 𝔮.IsPrime ∧
    v = Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 ⟨𝔮, h𝔮⟩) : ClassGroupModP K p)}

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Generation core.** Every integer-ideal class `[mk0 I]` lies in the
`ZMod p`-submodule generated by the prime ideal classes. Proved by induction on
the underlying ideal `I.val` via `UniqueFactorizationMonoid.induction_on_prime`:
the unit (`⊤`) case is the trivial class `0`, and the prime-times-rest case uses
`mk0`-multiplicativity `[mk0 (𝔭 * a)] = [mk0 𝔭] + [mk0 a]` together with the fact
that `[mk0 𝔭]` is a generator (`𝔭` prime) and `[mk0 a]` lies in the span by the
induction hypothesis. -/
theorem mem_span_primeClassSet (I : (Ideal (𝓞 K))⁰) :
    Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) ∈
      Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) := by
  -- Reduce to a statement about the underlying ideal `I.val` with an arbitrary
  -- nonzero-divisor witness, then induct on the ideal.
  suffices h : ∀ (J : Ideal (𝓞 K)) (hJ : J ∈ (Ideal (𝓞 K))⁰),
      Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 ⟨J, hJ⟩) : ClassGroupModP K p) ∈
        Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) by
    simpa using h I.1 I.2
  intro J
  -- Induct on the ideal `J`. The predicate carries the nonzero-divisor witness so
  -- that `mk0` is applicable.
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    -- `0` is a zero-divisor, so the nonzero-divisor witness is contradictory.
    intro hJ
    exact absurd (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (by simp)
  | h₂ J hJunit =>
    -- Unit ideal: `J = ⊤` is principal, so `mk0 ⟨J⟩ = 1` and its class is `0 ∈ span`.
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
    -- Prime times rest: split the class and use generator + IH.
    intro hJ
    -- `𝔭` and `a` are nonzero, hence nonzero divisors.
    have h𝔭_ne : 𝔭 ≠ 0 := h𝔭_prime.ne_zero
    have h𝔭_mem : 𝔭 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔭_ne
    have ha_mem : a ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr ha_ne
    -- `mk0 ⟨𝔭 * a⟩ = mk0 ⟨𝔭⟩ * mk0 ⟨a⟩` (codomain `ClassGroup`, no dependent motive).
    have hsplit : ClassGroup.mk0 (⟨𝔭 * a, hJ⟩ : (Ideal (𝓞 K))⁰) =
        ClassGroup.mk0 (⟨𝔭, h𝔭_mem⟩ : (Ideal (𝓞 K))⁰) *
          ClassGroup.mk0 (⟨a, ha_mem⟩ : (Ideal (𝓞 K))⁰) := by
      rw [← map_mul]
      rfl
    -- Convert the split membership goal into a sum of two memberships.
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
    -- `[mk0 ⟨𝔭⟩]` is a generator, since `𝔭` is a nonzero prime.
    apply Submodule.subset_span
    exact ⟨𝔭, h𝔭_mem, (Ideal.prime_iff_isPrime h𝔭_ne).mp h𝔭_prime, rfl⟩

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Leaf 5.** The prime ideal classes generate all of
`Additive (ClassGroupModP K p)`: their `ZMod p`-span is `⊤`. -/
theorem span_primeClassSet_eq_top :
    Submodule.span (ZMod p) (primeClassSet (p := p) (K := K)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  -- Every `v = ofMul w` with `w : ClassGroupModP K p`; `w = mk c` for some class
  -- `c`, and `c = mk0 I` for some integer ideal `I`, so `v` is in the span by the
  -- core lemma.
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom p :
    ClassGroup (𝓞 K) →* _).range) v.toMul
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hv : v = Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) :=
    Additive.toMul.injective hc.symm
  rw [hv]
  exact mem_span_primeClassSet (p := p) (K := K) I

/-! ### Leaf 6: assembly — annihilation reduces to the per-prime relation

The canonical group-ring action `classGroupModPGroupRingAction ρ x` is a
`ZMod p`-linear endomorphism of `Additive (ClassGroupModP K p)`. By Leaf 5 the
prime ideal classes generate the module, and a linear endomorphism that vanishes
on a generating set vanishes everywhere. Hence to show that a fixed `x`
annihilates the whole class group it suffices to check that it annihilates each
prime ideal class — which is the per-prime Stickelberger relation (Leaf 4). -/

/-- **Leaf 6 (assembly).** If a fixed group-ring element `x` annihilates the
class `[mk0 𝔮]` of every nonzero prime ideal `𝔮`, then the canonical group-ring
action of `x` is the zero endomorphism on all of
`Additive (ClassGroupModP K p)`.

This isolates the open content of **L-ann** to the per-prime relation
(the hypothesis): once the Gauss-sum prime factorisation shows that `x` kills
each prime ideal class, this lemma propagates the vanishing to the whole class
group by `ZMod p`-linearity and the prime-class generation of Leaf 5. -/
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
  -- It suffices that the kernel is everything; by Leaf 5 the prime classes span,
  -- so it suffices that each prime class lies in the kernel.
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← span_primeClassSet_eq_top (p := p) (K := K),
    Submodule.span_le]
  rintro v ⟨𝔮, h𝔮mem, h𝔮prime, rfl⟩
  -- `𝔮 ≠ ⊥` since `𝔮 ∈ (Ideal R)⁰`.
  have h𝔮ne : 𝔮 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp h𝔮mem
  -- The generator lies in the kernel: this is exactly the per-prime hypothesis
  -- (the nonzero-divisor witnesses agree by proof irrelevance).
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  exact H 𝔮 h𝔮prime h𝔮ne

end Eichler

end FLT37

end BernoulliRegular

end
