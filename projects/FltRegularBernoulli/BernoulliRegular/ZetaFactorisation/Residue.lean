module

public import BernoulliRegular.ZetaFactorisation.EulerProduct

/-!
# Residue statements for cyclotomic zeta factorisation

This module packages the `s = 1` residue consequences of the Euler-product
factorisation used downstream in `HMinus`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology

namespace BernoulliRegular

section ZetaFactorisation

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Residues at `s = 1` -/

/-- Residue of `(s - 1) · ζ(s) · nontrivialLProduct p s` at `s = 1`: equals
`nontrivialLProduct p 1`, since `lim (s - 1)ζ(s) = 1` (residue of Riemann zeta)
and the nontrivial L-product is continuous at `s = 1`. -/
theorem tendsto_sub_one_mul_riemannZeta_mul_nontrivialLProduct :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * (riemannZeta (s : ℂ) * nontrivialLProduct p (s : ℂ)))
      (𝓝[>] 1)
      (𝓝 (nontrivialLProduct p (1 : ℂ))) := by
  -- `Finset.mem_erase` below needs `DecidableEq (DirichletCharacter ℂ p)`.
  classical
  have h_cont : Continuous (nontrivialLProduct p) :=
    continuous_finsetProd _ fun χ hχ ↦
      (DirichletCharacter.differentiable_LFunction (Finset.mem_erase.mp hχ).1).continuous
  have h_embed : Filter.Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with s hs h
           exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod : Filter.Tendsto (fun s : ℝ ↦ nontrivialLProduct p (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (nontrivialLProduct p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod := h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring

/-- Using the Washington identity `ζ_K = ζ · nontrivialLProduct`, the
residue of `ζ_K` at `s = 1` equals `nontrivialLProduct p 1`. -/
theorem tendsto_sub_one_mul_dedekindZeta_via_LProducts :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * dedekindZeta K (s : ℂ))
      (𝓝[>] 1)
      (𝓝 (nontrivialLProduct p (1 : ℂ))) := by
  refine (Filter.tendsto_congr' ?_).mp (tendsto_sub_one_mul_riemannZeta_mul_nontrivialLProduct p)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dedekindZeta_eq_riemannZeta_mul_nontrivialLProduct_of_one_lt_re p K (mod_cast hs)]

/-- The factorisation used by the class number formula: the Dedekind zeta residue of
`K = ℚ(ζ_p)` is the real part of `nontrivialLProduct p 1 = ∏_{χ≠1} L(1, χ)`. -/
theorem dedekindZeta_residue_eq_re_nontrivialLProduct :
    dedekindZeta_residue K = (nontrivialLProduct p (1 : ℂ)).re := by
  have heq : ((dedekindZeta_residue K : ℝ) : ℂ) = nontrivialLProduct p (1 : ℂ) :=
    tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
      (tendsto_sub_one_mul_dedekindZeta_via_LProducts p K)
  rw [← heq, Complex.ofReal_re]

/-- The same factorisation split by parity: the Dedekind zeta residue of `K = ℚ(ζ_p)` is the real
part of `evenLProduct p 1 * oddLProduct p 1`, the product of the even and odd nontrivial
`L`-values at `s = 1`. -/
theorem dedekindZeta_residue_eq_re_evenLProduct_mul_oddLProduct :
    dedekindZeta_residue K = (evenLProduct p (1 : ℂ) * oddLProduct p (1 : ℂ)).re := by
  rw [dedekindZeta_residue_eq_re_nontrivialLProduct (p := p) (K := K),
    nontrivialLProduct_eq_even_mul_odd]

end ZetaFactorisation

end BernoulliRegular
