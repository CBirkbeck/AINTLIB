module

public import BernoulliRegular.Reflection.WeakSplitting.SplitsCompletely
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Local-factor identity at a prime that splits completely

For a nonzero prime `p` of `R = 𝓞 K` that splits completely in a finite
extension `M / K` (with `S = 𝓞 M`), the finite product of local Euler
factors over the primes of `S` lying above `p` collapses to a power of the
single local factor at `p`. Concretely,
$$
\prod_{Q \mid p}\bigl(1 - N(Q)^{-s}\bigr) =
  \bigl(1 - N(p)^{-s}\bigr)^{[M : K]},
$$
because each `Q` above `p` has residue degree one (so `N(Q) = N(p)`) and
there are exactly `[M : K]` such primes (REF-21b).

This is the single-prime building block (REF-21c1) for the global Euler-
product identity REF-21c2 between the partial Dedekind zeta functions of
`M` and `K`.

## Main results

* `BernoulliRegular.Ideal.SplitsCompletely.absNorm_eq_of_mem`: under
  `SplitsCompletely`, every prime `Q` of `S` above `p` satisfies
  `absNorm Q = absNorm p`.
* `BernoulliRegular.Ideal.SplitsCompletely.prod_localFactor_eq_pow`: the
  finite product `∏ Q above p, (1 - N(Q)^{-s})` equals
  `(1 - N(p)^{-s}) ^ [M : K]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable (K L : Type*) [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
variable [Module.Finite R S] [Module.IsTorsionFree R S]
variable [Module.Free ℤ R] [Module.Free ℤ S]

/--
Under `SplitsCompletely`, every prime `Q` of `S` lying above `p` has the
same absolute norm as `p`. Indeed, by `absNorm_eq_pow_inertiaDeg_of_liesOver`,
`absNorm Q = absNorm p ^ inertiaDeg p Q`, and the splits-completely
hypothesis forces `inertiaDeg p Q = 1`.
-/
theorem SplitsCompletely.absNorm_eq_of_mem
    {p : Ideal R} [hp_max : p.IsMaximal] (hp0 : p ≠ ⊥) (h : SplitsCompletely S p)
    {Q : Ideal S} (hQ : Q ∈ IsDedekindDomain.primesOverFinset p S) :
    Ideal.absNorm Q = Ideal.absNorm p := by
  obtain ⟨_he, hf⟩ := h Q hQ
  haveI : Q.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).1
  haveI : Q.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hQ).2
  rw [_root_.Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver Q p hp_max.isPrime hp0, hf, pow_one]

/--
The local-factor identity at a prime `p` that splits completely in `M / K`:
the product of the local Euler factors over the primes `Q` of `𝓞 M` above
`p` equals the single local factor at `p` raised to the extension degree
`[M : K]`.
-/
theorem SplitsCompletely.prod_localFactor_eq_pow
    {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) (h : SplitsCompletely S p) (s : ℂ) :
    ∏ Q ∈ IsDedekindDomain.primesOverFinset p S, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      ((1 : ℂ) - (Ideal.absNorm p : ℂ) ^ (-s)) ^ Module.finrank K L := by
  rw [Finset.prod_congr rfl fun _ hQ => by
        rw [SplitsCompletely.absNorm_eq_of_mem S hp0 h hQ],
      Finset.prod_const,
      SplitsCompletely.card_primesOverFinset_eq_finrank S K L hp0 h]

end Ideal

end BernoulliRegular
