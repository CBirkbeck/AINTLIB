module

public import BernoulliRegular.FLT37.Eichler.StickelbergerAnnihilation

/-!
# Leaf 4: the per-prime Stickelberger relation — Galois-orbit reduction (foundational leaf)

This file is the **leaf-4** foundational layer of the **L-ann** theorem (that the
integral Stickelberger element annihilates `ClassGroupModP K p`, for
`K = ℚ(ζ_p)`). Leaf 4 is the per-prime Stickelberger relation:

> for a nonzero prime ideal `𝔮` of `𝓞 K`, the group-ring element `x`
> (the integral Stickelberger element) annihilates the class `[𝔮]` in
> `ClassGroupModP K p`.

The companion file `StickelbergerAnnihilation.lean` reduces the full annihilation
to this per-prime statement (`classGroupModPGroupRingAction_eq_zero_of_annihilates_primes`,
leaf 6) and provides the linearity expansion of the action on a prime class
(`classGroupModPGroupRingAction_instance_apply_mk0`, leaf 3): the action of `x`
on `[mk0 𝔮]` is the `ZMod p`-linear combination

  `ρ x [mk0 𝔮] = ∑_{a ∈ supp x} x(a) • [mk0 (σ_a 𝔮)]`,

where `σ_a 𝔮 = cyclotomicGaloisConjugate a 𝔮` is the cyclotomic Galois conjugate.

## What this file proves (the foundational reduction)

The remaining mathematical content of leaf 4 is the **Gauss-sum / Stickelberger
factorisation** (Washington Thm 6.10): the integral group-ring exponent vector,
applied to a prime `𝔮` above a rational prime `ℓ ≠ p` by Galois conjugation,
produces a **principal** ideal. That is genuinely a fresh build for `K = ℚ(ζ_p)`
and a prime above `ℓ ≠ p` — it is *not* the repo's existing
`GaussSum/PrimeFactorization/` package, which factorises the Gauss sum of a
*Dirichlet character mod `p`* over `L = ℚ(ζ_{p(p-1)})` and whose prime factors
are exclusively primes **above `p`** (`normalizedFactors_gaussSumIdeal_subset_primesAboveP`).

This file supplies the **Galois-orbit reduction** of that factorisation: it
suffices to prove the per-prime relation for **one** prime per rational prime
`ℓ`, because the cyclotomic Galois group `Gal(K/ℚ) ≅ (ZMod p)ˣ` is **abelian**
and acts transitively on the primes above each `ℓ`
(`exists_mem_cyclotomicConjugates_of_under_eq`). Concretely:

* `cyclotomicGaloisConjugate_comm`: the cyclotomic Galois conjugates commute,
  `σ_a (σ_b 𝔮) = σ_b (σ_a 𝔮)`, since `(ZMod p)ˣ` is commutative. This is the
  arithmetic heart of the orbit reduction.
* `stickelbergerOrbitIdeal`: the ideal `∏_a (σ_a 𝔮)^{e_a}` for a nonnegative
  exponent vector `e`.
* `stickelbergerOrbitIdeal_galAction`: `σ_b (∏_a (σ_a 𝔮)^{e_a}) = ∏_a (σ_a (σ_b 𝔮))^{e_a}`,
  i.e. the orbit ideal of the conjugate prime is the Galois conjugate of the
  orbit ideal. (Uses commutativity + multiplicativity of `σ`.)
* `stickelbergerOrbitIdeal_isPrincipal_of_conj`: **the foundational reduction.**
  If the orbit ideal of `𝔮₀` is principal, then the orbit ideal of any Galois
  conjugate `σ_b 𝔮₀` is principal, because the Galois conjugate of a principal
  ideal is principal.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.2 (Stickelberger's
  theorem, Thm 6.10), §6.1 (Galois action on primes).
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

/-- **Commutativity of the cyclotomic Galois conjugates.** For any two indices
`a b : (ZMod p)ˣ` and any ideal `q`,

  `σ_a (σ_b q) = σ_b (σ_a q)`. -/
theorem cyclotomicGaloisConjugate_comm (a b : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b q) =
      Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q) := by
  rw [← Furtwaengler.cyclotomicGaloisConjugate_mul,
    ← Furtwaengler.cyclotomicGaloisConjugate_mul, mul_comm]

open scoped Classical in
/-- The **Stickelberger orbit ideal** of a prime `q` for a nonnegative exponent
vector `e : (ZMod p)ˣ → ℕ`:

  `∏_a (σ_a q)^{e a}`,

the product over the Galois orbit of `q` of the conjugate primes raised to the
Stickelberger exponents. This is the ideal whose principality is the content of
the per-prime Stickelberger relation (leaf 4). -/
noncomputable def stickelbergerOrbitIdeal (e : CyclotomicUnitDelta p → ℕ)
    (q : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ a : CyclotomicUnitDelta p,
    Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q ^ e a

open scoped Classical in
/-- The Galois conjugate of the Stickelberger orbit ideal of `q` is the
Stickelberger orbit ideal of the Galois conjugate of `q`:

  `σ_b (∏_a (σ_a q)^{e a}) = ∏_a (σ_a (σ_b q))^{e a}`. -/
theorem stickelbergerOrbitIdeal_galAction (e : CyclotomicUnitDelta p → ℕ)
    (b : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) :
    Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b
        (stickelbergerOrbitIdeal (p := p) (K := K) e q) =
      stickelbergerOrbitIdeal (p := p) (K := K) e
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b q) := by
  classical
  unfold stickelbergerOrbitIdeal
  -- Push `σ_b` through the finite product (via the bundled ring hom
  -- `Ideal.mapHom` on the underlying `Ideal.map`).
  rw [show Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b
        (∏ a : CyclotomicUnitDelta p,
          Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q ^ e a) =
      Ideal.mapHom (cyclotomicRingOfIntegersEquiv (p := p) K b)
        (∏ a : CyclotomicUnitDelta p,
          Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q ^ e a) from rfl,
    map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  -- Termwise: `σ_b ((σ_a q)^{e a}) = (σ_a (σ_b q))^{e a}`. Refold the bundled hom
  -- application to `σ_b`, distribute over the power, then apply commutativity.
  rw [show (Ideal.mapHom (cyclotomicRingOfIntegersEquiv (p := p) K b))
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q ^ e a) =
      Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) a q ^ e a) from rfl,
    Furtwaengler.cyclotomicGaloisConjugate_pow_ideal, cyclotomicGaloisConjugate_comm]

open scoped Classical in
/-- **Foundational reduction (Galois-orbit reduction of leaf 4).** If the
Stickelberger orbit ideal of a prime `q₀` is principal, then the Stickelberger
orbit ideal of any Galois conjugate `σ_b q₀` is principal.

This is the precise statement that reduces the per-prime Stickelberger relation
to a single representative per rational prime `ℓ`: since the cyclotomic Galois
group acts transitively on the primes above `ℓ`, every such prime is `σ_b q₀`
for some `b`, and this lemma propagates principality of the orbit ideal across
the orbit. -/
theorem stickelbergerOrbitIdeal_isPrincipal_of_conj (e : CyclotomicUnitDelta p → ℕ)
    (b : CyclotomicUnitDelta p) (q₀ : Ideal (𝓞 K))
    (h : (stickelbergerOrbitIdeal (p := p) (K := K) e q₀).IsPrincipal) :
    (stickelbergerOrbitIdeal (p := p) (K := K) e
        (Furtwaengler.cyclotomicGaloisConjugate (p := p) (K := K) b q₀)).IsPrincipal := by
  classical
  rw [← stickelbergerOrbitIdeal_galAction]
  obtain ⟨γ, hγ⟩ := h
  refine ⟨⟨cyclotomicRingOfIntegersEquiv (p := p) K b γ, ?_⟩⟩
  rw [hγ, Ideal.submodule_span_eq, Ideal.submodule_span_eq,
    Furtwaengler.cyclotomicGaloisConjugate, Ideal.map_span, Set.image_singleton]

/-- **One representative per rational prime suffices.** If the Stickelberger
orbit ideal of a prime `q₀` of `𝓞 K` is principal, then the Stickelberger orbit
ideal of *every* prime `q` of `𝓞 K` lying above the same rational prime
(`q.under ℤ = q₀.under ℤ`) is principal.

This is the full Galois-orbit reduction of leaf 4: combined with the
transitivity of the cyclotomic Galois action on primes above a fixed rational
prime (`exists_mem_cyclotomicConjugates_of_under_eq`), it reduces the per-prime
Stickelberger relation — needed for the assembly lemma
`classGroupModPGroupRingAction_eq_zero_of_annihilates_primes` — to a single
chosen prime above each rational prime `ℓ`. The remaining (genuinely fresh, not
transportable from the repo's mod-`p`/above-`p` Gauss-sum package) content is the
Gauss-sum factorisation showing the orbit ideal of one prime above `ℓ ≠ p` is
principal. -/
theorem stickelbergerOrbitIdeal_isPrincipal_of_under_eq (e : CyclotomicUnitDelta p → ℕ)
    {q₀ q : Ideal (𝓞 K)} [hq₀ : q₀.IsPrime] [hq : q.IsPrime]
    (hunder : q.under ℤ = q₀.under ℤ)
    (h : (stickelbergerOrbitIdeal (p := p) (K := K) e q₀).IsPrincipal) :
    (stickelbergerOrbitIdeal (p := p) (K := K) e q).IsPrincipal := by
  obtain ⟨b, hb⟩ :=
    (Furtwaengler.mem_cyclotomicConjugates_iff (p := p) (K := K) q₀ q).mp
      (Furtwaengler.exists_mem_cyclotomicConjugates_of_under_eq (p := p) (K := K)
        hunder.symm)
  rw [← hb]
  exact stickelbergerOrbitIdeal_isPrincipal_of_conj (p := p) (K := K) e b q₀ h

end Eichler

end FLT37

end BernoulliRegular

end
