import BernoulliRegular.Thaine.PollaczekUnitPlusGaloisAction.GaloisActionDecompositionAndEigenspace
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula
import Mathlib.NumberTheory.Bernoulli

/-!
# Washington §8.3 route to `¬ 37 ∣ h⁺` (Vandiver for 37)

This file records the **unit-side** route to `¬ 37 ∣ h⁺(ℚ(ζ₃₇))` following
Washington, *Introduction to Cyclotomic Fields* (GTM 83), **§8.3 "Units of
ℚ(ζ_p) and Vandiver's Conjecture"** (Theorems 8.14 and 8.16, pp. 153–157).

Its advantage over the live class-group route (`flt37_componentIdentification`
+ Kučera Thm 4.3 at ω³² + the Herbrand reflection bridge) is that it **avoids
Kučera's theorem entirely** (whose source is not in `docs/`): for the irregular
index `i = 32`, Theorem 8.14 reduces "the ω³² summand of `(E⁺/C⁺)_p` is
nontrivial" to "`pollaczekUnitPlus 37 K 32` is a 37-th power", and the latter is
**already disproved** in the repo by the axiom-clean
`FLT37.flt37_pollaczekUnitPlus_unit_ne_pow_37`. The other (regular) even indices
are killed by Theorem 8.16 (`E_i` a p-th power ⟹ `37 ∣ B_i`) together with the
finite Bernoulli table (`37 ∤ B_i` for even `i ≠ 32`, `2 ≤ i ≤ 34`).

The hardest analytic input — Sinnott's regulator-determinant identity (PF-1) —
is already proven in the repo (`kummerDirichletDeterminant_of_deletedFourier`,
axiom-clean). So the only genuinely new content here is:

* `Washington814Forward37` — Theorem 8.14, forward direction (unit side):
  `37 ∣ h⁺` produces some even `i ∈ [2,34]` with `pollaczekUnitPlus 37 K i` a
  37-th power. (The structural eigenspace-decomposition half;
  `even_eigenspace_nontrivial_of_dvd_hPlus` is the shipped class-group analogue.)
* `Washington816_37` — Theorem 8.16: if `pollaczekUnitPlus 37 K i` is a 37-th
  power then `37 ∣ (bernoulli i).num`. Source proof (Wash p. 157): from
  `log_p E_i^{(N)} = p · log_p η`, Proposition 8.12 gives
  `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1, ω^i))`, hence
  `v_p(L_p(1, ω^i)) > 0`; Corollary 5.13 gives `L_p(1, ω^i) ≡ -B_i/i (mod p)`,
  so `p ∣ B_i`. The repo has Cor 5.13's algebraic core
  (`Stickelberger.stickelbergerEigenvalue_eq_BernoulliGen`) and log-embedding
  machinery (`Sinnott/LogEmbedding.lean`, `Sinnott/LDerivative/`); the new
  piece is the single-unit log valuation (Prop 8.12), the repo's log infra
  being currently regulator-determinant-shaped.

`Washington814Forward37` and `Washington816_37` are stated here as named
`Prop`s — **not** axioms or `sorry`s — and `not_dvd_hPlus_of_washington83`
discharges `¬ 37 ∣ h⁺` from them (plus the computational Bernoulli table) using
the proven certificate. This keeps the development axiom- and sorry-clean while
pinning the exact remaining mathematical gaps.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §8.3, Thm 8.14
  (p. 157), Thm 8.16 (p. 157), Prop 8.10–8.13 (pp. 154–156), Cor 5.13.
* `.mathlib-quality/decomposition.md` (full source-grounded decomposition).
-/

@[expose] public section

open NumberField

namespace BernoulliRegular.FLT37.Sinnott

variable [Fact (Nat.Prime 37)] [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **Washington Theorem 8.14, forward direction (unit side, p = 37).**

If `37 ∣ h⁺(ℚ(ζ₃₇))` then for some even index `i` with `2 ≤ i ≤ 34` the
symmetrised Pollaczek unit `pollaczekUnitPlus 37 K i` (Washington's `E_i`, up to
the tracked `2^{(p-3)/2}` square factor) is a 37-th power in `(𝓞 K)ˣ`.

Source: Washington §8.3, Theorem 8.14 (p. 157), forward direction. Proof uses
the eigenspace decomposition `(E⁺/C⁺)_p ≅ ⊕_{i even} ε_i E⁺/⟨E_i⟩`
(Prop 8.10/8.11) with each summand cyclic of p-power order (Prop 8.13), so a
nonzero summand forces the corresponding `E_i` to be a p-th power. The shipped
`even_eigenspace_nontrivial_of_dvd_hPlus` is the class-group-side analogue of
the same forward step. -/
def Washington814Forward37 : Prop :=
  (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) →
    ∃ i : ℕ, Even i ∧ 2 ≤ i ∧ i ≤ 34 ∧
      ∃ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
        FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) i = α ^ 37

/-- **Washington Theorem 8.16 (unit side, p = 37).**

If `pollaczekUnitPlus 37 K i` is a 37-th power (even `i`, `2 ≤ i ≤ 34`) then
`37 ∣ (bernoulli i).num`.

Source: Washington §8.3, Theorem 8.16 (p. 157). Proof: write the unit as
`η^p`; then `log_p E_i^{(N)} = p log_p η`, so `v_p(log_p E_i^{(N)}) ≥ 1`. By
Proposition 8.12, `v_p(log_p E_i^{(N)}) = i/(p-1) + v_p(L_p(1, ω^i))`, whence
`v_p(L_p(1, ω^i)) > 0`. Corollary 5.13 gives `L_p(1, ω^i) ≡ -B_i/i (mod p)`, so
`p ∣ B_i`. -/
def Washington816_37 : Prop :=
  ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 →
    (∃ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) i = α ^ 37) →
    (37 : ℤ) ∣ (bernoulli i).num

/-- **`¬ 37 ∣ h⁺` via Washington §8.3** (axiom- and sorry-clean).

Composes the two §8.3 source boundaries (`Washington814Forward37`,
`Washington816_37`) and the finite Bernoulli table (`37 ∤ B_i` for even
`i ≠ 32`) with the **proven** certificate
`FLT37.flt37_pollaczekUnitPlus_unit_ne_pow_37` (`pollaczekUnitPlus 37 K 32` is
not a 37-th power).

Argument (Washington §8.3): assume `37 ∣ h⁺`. By Theorem 8.14 some even
`i ∈ [2,34]` has `pollaczekUnitPlus 37 K i` a 37-th power. If `i = 32`, this
contradicts the certificate. If `i ≠ 32`, Theorem 8.16 gives `37 ∣ B_i`,
contradicting the Bernoulli table. ∎

This avoids Kučera Theorem 4.3 (the single-character Thaine annihilator used by
the live class-group route at ω³²), whose source is not available locally. -/
theorem not_dvd_hPlus_of_washington83
    (h_8_14 : Washington814Forward37)
    (h_8_16 : Washington816_37)
    (h_table : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 34 → i ≠ 32 →
      ¬ (37 : ℤ) ∣ (bernoulli i).num) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) := by
  intro h_dvd
  obtain ⟨i, hi_even, hi2, hi34, α, hα⟩ := h_8_14 h_dvd
  by_cases hi32 : i = 32
  · subst hi32; exact FLT37.flt37_pollaczekUnitPlus_unit_ne_pow_37 α hα
  · exact h_table i hi_even hi2 hi34 hi32 (h_8_16 i hi_even hi2 hi34 ⟨α, hα⟩)

end BernoulliRegular.FLT37.Sinnott

end
