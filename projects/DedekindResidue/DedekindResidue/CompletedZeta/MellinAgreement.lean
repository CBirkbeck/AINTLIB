module

public import Mathlib
public import DedekindResidue.CompletedZeta.FEPair

/-!
# The Mellin agreement computation  (SP1-AGE-4, brick 5)

The final arithmetic identity behind Hecke's theorem: on `Re s > 1`,

  `mellin (heckeF − heckeFConst) (s/2) = κ·2^{-r₂}·completedZetaPrefactor K s·ζ_K(s)`

with `κ` the (s-independent) Jacobian constant of the `(t,u) ↦ y` change of variables.
The route (fully derived in the SP1-AGE ticket): per class, Mellin-scaling by
`s_C = N(I)⁻²·β` (`mellin_comp_mul_left`), the box-unfolding of the zero-removed theta
along the fundamental cone (`fundamentalCone.idealSet` — the cone is a fundamental domain
for the unit action mod torsion, and `idealSetEquivNorm`'s `× torsion` factor cancels
`heckeG`'s `w⁻¹`), the per-orbit factorisation into `Γ`-integrals, and the ideal-counting
sum. Agreement for real `s > 1` extends to the half-plane by the identity theorem.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]


open scoped Classical in
/-- The deviation of `g_I` from its constant term is the box integral of the zero-removed
theta (valid for every `t > 0`). -/
theorem heckeG_sub_const_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {t : ℝ} (ht : 0 < t) :
    heckeG K I t - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K
      = (torsionOrder K : ℝ)⁻¹ * ∫ u in ZSpan.fundamentalDomain
          ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ),
          (heckeTheta K I (heckeWeights K t u) - 1) := by
  obtain ⟨R, hR, hbox⟩ := exists_box_coord_bound K
  set B := ZSpan.fundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) with hBdef
  have hBmeas : MeasurableSet B := ZSpan.fundamentalDomain_measurableSet _
  have hBfin : volume B < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  set m : ℝ := Real.exp (-(2 * (Fintype.card (InfinitePlace K)) * R)) with hm_def
  have hm : 0 < m := Real.exp_pos _
  set a' : ℝ := m * t ^ ((1 : ℝ) / (Module.finrank ℚ K)) with ha'_def
  have ha' : 0 < a' := by
    have := Real.rpow_pos_of_pos ht ((1 : ℝ) / (Module.finrank ℚ K))
    positivity
  have hcontu : Continuous (fun u : logSpace K => heckeTheta K I (heckeWeights K t u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hj := continuousAt_heckeTheta_heckeWeights K I (p := ((t : ℝ), u)) ht
    have hin : ContinuousAt (fun u' : logSpace K => ((t : ℝ), u')) u :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hcompeq : (fun u' : logSpace K => heckeTheta K I (heckeWeights K t u'))
        = (fun q : ℝ × logSpace K => heckeTheta K I (heckeWeights K q.1 q.2))
          ∘ (fun u' : logSpace K => ((t : ℝ), u')) := rfl
    rw [hcompeq]
    exact ContinuousAt.comp (x := u) hj hin
  have hint : IntegrableOn (fun u : logSpace K =>
      heckeTheta K I (heckeWeights K t u)) B := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (ne_top_of_lt hBfin)
        (C := ∑' v : idealZLattice K I,
          Real.exp (-π * ∑ i : index K, a' * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)))
      hcontu.aestronglyMeasurable.restrict ?_
    refine (MeasureTheory.ae_restrict_iff' hBmeas).mpr (Filter.Eventually.of_forall
      (fun u hu => ?_))
    have hca : ∀ w, a' ≤ heckeWeights K t u w := by
      intro w
      exact heckeWeights_ge_of_bounded K hR (hbox u hu) ht.le w
    rw [Real.norm_eq_abs, abs_of_pos]
    · exact heckeTheta_le_iso K I ha' hca
    · have hsplit := heckeTheta_eq_one_add K I ha' hca
      have htail : 0 ≤ ∑' v : idealZLattice K I, (if v = 0 then 0
          else Real.exp (-π * ∑ i : index K,
            placeWeights K (heckeWeights K t u) i
              * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)) := by
        refine tsum_nonneg (fun v => ?_)
        split_ifs
        · exact le_refl 0
        · exact (Real.exp_pos _).le
      rw [hsplit]
      linarith
  have hsplit : ∫ u in B, heckeTheta K I (heckeWeights K t u)
      = unitBoxVol K + ∫ u in B, (heckeTheta K I (heckeWeights K t u) - 1) := by
    rw [MeasureTheory.integral_sub hint (MeasureTheory.integrableOn_const
      (ne_top_of_lt hBfin))]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    have hvol : volume.real B = unitBoxVol K := by
      rw [unitBoxVol, hBdef]
      rfl
    rw [hvol]
    ring
  rw [heckeG, ← hBdef, hsplit]
  ring

end

end DedekindResidue
