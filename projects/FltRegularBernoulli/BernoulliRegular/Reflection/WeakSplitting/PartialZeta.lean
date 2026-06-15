module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Partial Dedekind zeta function

This file defines a partial form of the Dedekind zeta function obtained by
removing finitely many Euler factors. For a number field `K` and a finite set
`F` of nonzero prime ideals of `𝓞 K`, set
$$
\zeta_{K, F}(s) = \zeta_K(s) \cdot \prod_{\mathfrak{p} \in F}
  \bigl(1 - N(\mathfrak{p})^{-s}\bigr).
$$
Equivalently, this is the function obtained from `dedekindZeta K` by deleting
the Euler factor at each prime in `F`. Each removed factor is entire in `s`
and nonzero at `s = 1`, so the partial zeta inherits the simple pole at
`s = 1` from the full Dedekind zeta function.

This is the basic local input needed for the polar-density / weak-splitting
argument of `BernoulliRegular/Reflection/kummer_reflection.tex`, Section 5
(REF-21).

## Main definitions

* `NumberField.dedekindZetaPartial`: the partial Dedekind zeta function with
  Euler factors at the primes of `F` removed.
* `NumberField.dedekindZetaPartialResidue`: the residue of
  `dedekindZetaPartial` at `s = 1`.

## Main results

* `NumberField.dedekindZetaPartial_empty`: empty removal recovers the full
  Dedekind zeta function.
* `NumberField.tendsto_sub_one_mul_dedekindZetaPartial_nhdsGT`: the partial
  Dedekind zeta has a simple pole at `s = 1`, with residue
  `dedekindZeta_residue K * ∏ p ∈ F, (1 - N(p)⁻¹)`.
-/

@[expose] public section

noncomputable section

namespace NumberField

open Filter Ideal IsDedekindDomain Topology

variable (K : Type*) [Field K] [NumberField K]

/--
The partial Dedekind zeta function: the full Dedekind zeta function with the
Euler factors at the primes in the finite set `F` removed. Concretely,
`dedekindZetaPartial K F s = dedekindZeta K s * ∏ p ∈ F, (1 - N(p)^(-s))`,
so multiplying back the inverses of the removed factors recovers the full
zeta function on the half-plane where the Euler product converges.
-/
def dedekindZetaPartial (F : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  dedekindZeta K s * ∏ p ∈ F, (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))

@[simp]
theorem dedekindZetaPartial_empty (s : ℂ) :
    dedekindZetaPartial K ∅ s = dedekindZeta K s := by
  simp [dedekindZetaPartial]

/--
The residue at `s = 1` of the partial Dedekind zeta function with Euler
factors at the primes in `F` removed. Equal to `dedekindZeta_residue K`
multiplied by the finite product `∏ p ∈ F, (1 - N(p)⁻¹)` of the removed
local factors evaluated at `s = 1`.
-/
def dedekindZetaPartialResidue (F : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  (dedekindZeta_residue K : ℂ) * ∏ p ∈ F, (1 - (Ideal.absNorm p.asIdeal : ℂ)⁻¹)

@[simp]
theorem dedekindZetaPartialResidue_empty :
    dedekindZetaPartialResidue K ∅ = (dedekindZeta_residue K : ℂ) := by
  simp [dedekindZetaPartialResidue]

/--
The partial Dedekind zeta function `dedekindZetaPartial K F` has a simple
pole at `s = 1` with residue `dedekindZetaPartialResidue K F`. This follows
from the corresponding fact for the full Dedekind zeta function together with
continuity at `s = 1` of each removed local factor.
-/
theorem tendsto_sub_one_mul_dedekindZetaPartial_nhdsGT
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun s : ℝ => (s - 1) * dedekindZetaPartial K F s) (𝓝[>] 1)
      (𝓝 (dedekindZetaPartialResidue K F)) := by
  have h₁ := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have h₂ : Tendsto
      (fun s : ℝ => ∏ p ∈ F, ((1 : ℂ) - (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s : ℂ))))
      (𝓝[>] 1)
      (𝓝 (∏ p ∈ F, ((1 : ℂ) - (Ideal.absNorm p.asIdeal : ℂ)⁻¹))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine tendsto_finsetProd F fun p _ => ?_
    have hp : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
      have h := HeightOneSpectrum.one_lt_absNorm p
      have hne : Ideal.absNorm p.asIdeal ≠ 0 := by omega
      exact_mod_cast hne
    have h_sub : Continuous
        (fun s : ℝ => (1 : ℂ) - ((Ideal.absNorm p.asIdeal : ℂ)) ^ (-(s : ℂ))) :=
      continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (Or.inl hp))
    convert h_sub.tendsto 1 using 2
    push_cast
    rw [Complex.cpow_neg, Complex.cpow_one]
  have heq : (fun s : ℝ => (s - 1) * dedekindZetaPartial K F s) =
      fun s : ℝ => ((s - 1) * dedekindZeta K s) *
        ∏ p ∈ F, ((1 : ℂ) - (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s : ℂ))) := by
    funext s
    simp [dedekindZetaPartial, mul_assoc]
  rw [heq]
  exact h₁.mul h₂

end NumberField
