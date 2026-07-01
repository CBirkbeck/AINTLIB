import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main
import FltRegular.CaseII.InductionStep

/-!
# LV010-CTOR-a: case II auxiliary ideal `𝔠 η = (x+yη)/((ζ-1)·𝔪)` is a p-th power

Wraps flt-regular's `exists_ideal_pow_eq_c` for the LV-route. Under FLT
case II's Kummer-form decomposition `x^p + y^p = ε · ((ζ-1)^{m+1} · z)^p`
(with `p ∤ y`, `p ∤ z`), each cyclotomic factor `(x + y·η)` (for `η` a
`p`-th root of unity) decomposes as

  `(x + y·η) · 𝓞 K = 𝔪 · 𝔠 η · 𝔭`

where `𝔪 = gcd((x), (y))`, `𝔭 = (ζ-1)`, and `𝔠 η` is the auxiliary
ideal (Washington's `B_a`). The key fact (`exists_ideal_pow_eq_c`):

  **Each `𝔠 η` is a p-th power as an ideal**: `∃ 𝔞 η, (𝔞 η)^p = 𝔠 η`.

Proof: `∏_η 𝔠 η = (𝔷' · 𝔭^m)^p` (a p-th power) plus pairwise coprimality
of the `𝔠 η`'s, by Dedekind UFD.

This is the foundational ideal-theoretic input for Washington Theorem 9.4.
The next step (LV-Washington-9.1) uses Kummer's lemma to convert
"`(x + yη) = (𝔞 η)^p · (real-or-class-trivial)`" into a unit-form
factorization.

## References

* flt-regular's `FltRegular.CaseII.InductionStep.exists_ideal_pow_eq_c`.
* Washington, *Introduction to Cyclotomic Fields*, §9.1, Eq. 9.1.0 + Lemma 9.6.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Ideal Polynomial

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

set_option backward.isDefEq.respectTransparency false in
/-- **Case II auxiliary ideal is a p-th power** (wrapper of
flt-regular's `exists_ideal_pow_eq_c`). Under the Kummer-form case II
decomposition `x^p + y^p = ε · ((ζ-1)^{m+1} · z)^p` with `p ∤ y` and
`p ∤ z`, the auxiliary ideal `𝔠 η = (x+yη)/((ζ-1)·𝔪)` is a `p`-th
power for each `p`-th root of unity `η`. -/
theorem caseII_auxiliary_ideal_isPthPower
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type} [NeZero p] [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y) (_hz : ¬ hζ.toInteger - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 K)) :
    ∃ I : Ideal (𝓞 K),
      divZetaSubOneDvdGcd hp_odd hζ e hy η = I ^ p :=
  exists_ideal_pow_eq_c hp_odd hζ e hy η

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
