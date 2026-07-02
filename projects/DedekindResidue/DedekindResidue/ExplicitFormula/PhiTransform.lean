module

public import Mathlib
public import DedekindResidue.ExplicitFormula.TestFunction
public import DedekindResidue.CompletedZeta.Normalisation

/-!
# The two-sided transform Φ of the explicit formula  (SP2-Φ)

Poitou's proof of Weil's explicit formula works with the two-sided Laplace/Mellin
transform (his eq. (2), p. 6-01):

* `Φ(s) := ∫_ℝ F(x)·e^{(s−1/2)x} dx`,

integrable in the closed band `-ε ≤ Re s ≤ 1+ε` for an admissible test function `F`
(the admissibility field `bv_integrable_exp` provides exactly the required decay).
On the critical line it recovers the paper's Fourier transform (B–F eq. (2)):
`Φ(1/2 + iγ) = F̂(γ)`, and for even `F` it satisfies the reflection `Φ(1−s) = Φ(s)`,
which folds the left contour edge onto the right one in the explicit-formula rectangle
(Poitou's `{Φ(s) + Φ(1−s)}` is `2Φ(s)` for even `F`).

## Main declarations

* `paperPhi` — the transform;
* `integrableOn_Iio_comp_neg_iff`, `integral_comp_neg_real` — reflection helpers;
* `integrableOn_Ici_mul_cexp` — the half-line domination workhorse;
* `integrable_paperPhi_kernel` — kernel integrability in the closed band;
* `paperPhi_half_add_mul_I` — `Φ(1/2+iγ) = F̂(γ)`;
* `paperPhi_one_sub` — `Φ(1−s) = Φ(s)` for even `F`.

Source: Poitou pp. 6-01/6-02 (`refs/DedekindResidue/poitou-petits-discriminants.pdf`);
B–F p. 3. Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-Φ.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex

/-- **Poitou's transform** (his eq. (2)): `Φ(s) = ∫_ℝ F(x)·e^{(s−1/2)x} dx`. -/
noncomputable def paperPhi (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp ((s - 1/2) * x)

/-- Reflection of half-line integrability through `x ↦ -x`. -/
theorem integrableOn_Iio_comp_neg_iff (G : ℝ → ℂ) :
    IntegrableOn G (Set.Iio (0:ℝ)) ↔ IntegrableOn (fun x => G (-x)) (Set.Ioi (0:ℝ)) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : volume.restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) (volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [IntegrableOn, hmap, A.integrable_map_iff]
  rfl

/-- **Half-line domination workhorse**: if `G·e^{(1/2+ε)x}` is integrable on `[0,∞)`
and `Re c ≤ 1/2 + ε`, then `G·e^{cx}` is integrable on `[0,∞)`. -/
theorem integrableOn_Ici_mul_cexp {G : ℝ → ℂ} {ε : ℝ}
    (hG : IntegrableOn (fun x : ℝ => G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
      (Set.Ici 0))
    {c : ℂ} (hc : c.re ≤ 1/2 + ε) :
    IntegrableOn (fun x : ℝ => G x * Complex.exp (c * x)) (Set.Ici 0) := by
  have hpt : ∀ x : ℝ, G x * Complex.exp (c * x)
      = (Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ))
        * (G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ)) := by
    intro x
    rw [mul_mul_mul_comm]
    rw [show ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ) * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ)
        = 1 by rw [← Complex.ofReal_mul, ← Real.exp_add]; norm_num]
    ring
  have hbd : ∀ x ∈ Set.Ici (0:ℝ),
      ‖Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ)‖ ≤ 1 := by
    intro x hx
    rw [Set.mem_Ici] at hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, ← Real.exp_add]
    rw [show (c * (x:ℂ)).re = c.re * x by simp [Complex.mul_re]]
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have hprod : IntegrableOn (fun x : ℝ =>
      (Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ))
        * (G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))) (Set.Ici 0) :=
    hG.bdd_mul ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      ((ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall hbd))
  exact hprod.congr_fun (fun x _ => (hpt x).symm) measurableSet_Ici

/-- **Φ-a: kernel integrability** in the closed band `-ε ≤ Re s ≤ 1 + ε` for an
admissible test function (with the admissibility witness `ε` made explicit). -/
theorem integrable_paperPhi_kernel {F : ℝ → ℂ} (hF : IsAdmissibleTestFn F)
    {ε : ℝ}
    (hint : IntegrableOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0))
    {s : ℂ} (hs1 : -ε ≤ s.re) (hs2 : s.re ≤ 1 + ε) :
    Integrable (fun x : ℝ => F x * Complex.exp ((s - 1/2) * x)) := by
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · -- left half-line: reflect and use evenness
    rw [integrableOn_Iio_comp_neg_iff]
    have hpt : ∀ x : ℝ, F (-x) * Complex.exp ((s - 1/2) * ((-x : ℝ) : ℂ))
        = F x * Complex.exp ((1/2 - s) * x) := by
      intro x
      rw [hF.even x]
      congr 1
      push_cast
      ring
    have h1 : IntegrableOn (fun x : ℝ => F x * Complex.exp ((1/2 - s) * x))
        (Set.Ici 0) := by
      refine integrableOn_Ici_mul_cexp hint ?_
      have hre : ((1:ℂ)/2 - s).re = 1/2 - s.re := by
        rw [Complex.sub_re]
        norm_num
      rw [hre]
      linarith
    refine (h1.mono_set Set.Ioi_subset_Ici_self).congr_fun (fun x _ => ?_)
      measurableSet_Ioi
    exact (hpt x).symm
  · -- right half-line
    refine integrableOn_Ici_mul_cexp hint ?_
    have hre : (s - (1:ℂ)/2).re = s.re - 1/2 := by
      rw [Complex.sub_re]
      norm_num
    rw [hre]
    linarith

/-- **Φ-b**: on the critical line, `Φ` is the paper's Fourier transform (B–F eq. (2)):
`Φ(1/2 + iγ) = F̂(γ)`. -/
theorem paperPhi_half_add_mul_I (F : ℝ → ℂ) (γ : ℝ) :
    paperPhi F (1/2 + (γ : ℂ) * Complex.I) = paperFourierIntegral F γ := by
  rw [paperPhi, paperFourierIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have : ((1:ℂ)/2 + (γ:ℂ) * Complex.I - 1/2) * x = Complex.I * x * γ := by ring
  simp only [this]

/-- Full-line integrals are invariant under `x ↦ -x`. -/
theorem integral_comp_neg_real (f : ℝ → ℂ) : ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  calc ∫ x : ℝ, f (-x) = ∫ x, f x ∂(Measure.map (fun x : ℝ => -x) volume) :=
        (A.integral_map f).symm
    _ = ∫ x : ℝ, f x := by rw [Measure.map_neg_eq_self (volume : Measure ℝ)]

/-- **Φ-c: the reflection** `Φ(1−s) = Φ(s)` for an even test function — this folds the
left edge of Poitou's rectangle onto the right edge (his `{Φ(s) + Φ(1−s)}` is `2Φ(s)`
for even `F`). -/
theorem paperPhi_one_sub {F : ℝ → ℂ} (heven : ∀ x : ℝ, F (-x) = F x) (s : ℂ) :
    paperPhi F (1 - s) = paperPhi F s := by
  rw [paperPhi, paperPhi]
  rw [← integral_comp_neg_real (fun x : ℝ => F x * Complex.exp ((1 - s - 1/2) * x))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [heven x]
  congr 1
  push_cast
  ring

end DedekindResidue

end
