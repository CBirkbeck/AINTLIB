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
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped nonZeroDivisors Real ENNReal NNReal

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

open scoped Classical in
/-- Unit-scaling preserves membership in the ideal lattice of an integral ideal. -/
theorem unit_smul_mem_idealLattice (J : (Ideal (𝓞 K))⁰) (u : (𝓞 K)ˣ) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
    u • x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) := by
  rw [mem_idealLattice] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * y, ?_, ?_⟩
  · rw [SetLike.mem_coe, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy ⊢
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨(u : 𝓞 K) * b, Ideal.mul_mem_left _ _ hb, by rw [map_mul]⟩
  · rw [map_mul]
    rfl

omit [NumberField K] in
open scoped Classical in
theorem unit_smul_ne_zero (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ≠ 0) : u • x ≠ 0 := by
  intro h0
  apply hx
  have h2 : u⁻¹ • (u • x) = u⁻¹ • (0 : mixedSpace K) := congrArg _ h0
  rw [inv_smul_smul] at h2
  rw [h2]
  show mixedEmbedding K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * 0 = 0
  exact mul_zero _

open scoped Classical in
/-- **The cone unfolding**: every nonzero point of the ideal lattice of an integral ideal
`J` is uniquely a fundamental-system power times a fundamental-cone point of `J`. -/
noncomputable def coneUnfoldEquiv (J : (Ideal (𝓞 K))⁰) :
    (idealSet K J) × (Fin (rank K) → ℤ)
      ≃ {x : mixedSpace K // x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)
          ∧ x ≠ 0} := by
  have hlat : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (∏ i, fundSystem K i ^ (p.2 i : ℤ)) • (p.1 : mixedSpace K)
        ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) :=
    fun p => unit_smul_mem_idealLattice K J _ p.1.2.2
  have hcone_mem : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      ((p.1 : mixedSpace K) ∈ fundamentalCone K) := fun p => p.1.2.1
  have hne : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (∏ i, fundSystem K i ^ (p.2 i : ℤ)) • (p.1 : mixedSpace K) ≠ 0 := by
    intro p
    refine unit_smul_ne_zero K _ ?_
    intro h0
    have hmem := hcone_mem p
    rw [h0] at hmem
    exact hmem.2 (map_zero (mixedEmbedding.norm (K := K)))
  refine Equiv.ofBijective (fun p =>
    ⟨(∏ i, fundSystem K i ^ (p.2 i : ℤ)) • (p.1 : mixedSpace K), hlat p, hne p⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, n⟩ ⟨⟨b, hb⟩, m⟩ hab
    simp only [Subtype.mk_eq_mk] at hab
    -- (u_m⁻¹ * u_n) • a = b
    have hmove : ((∏ i, fundSystem K i ^ (m i : ℤ))⁻¹
        * ∏ i, fundSystem K i ^ (n i : ℤ)) • a = b := by
      rw [mul_smul]
      rw [hab, inv_smul_smul]
    have hμtor : ((∏ i, fundSystem K i ^ (m i : ℤ))⁻¹
        * ∏ i, fundSystem K i ^ (n i : ℤ)) ∈ torsion K := by
      rw [← unit_smul_mem_iff_mem_torsion ha.1]
      rw [hmove]
      exact hb.1
    -- rewrite μ as a pure fundSystem power with exponents n - m
    have hμpow : ((∏ i, fundSystem K i ^ (m i : ℤ))⁻¹
        * ∏ i, fundSystem K i ^ (n i : ℤ))
        = ∏ i, fundSystem K i ^ ((n - m) i : ℤ) := by
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← zpow_neg, ← zpow_add]
      congr 1
      simp [sub_eq_add_neg, add_comm]
    have huniq := exist_unique_eq_mul_prod K (∏ i, fundSystem K i ^ ((n - m) i : ℤ))
    obtain ⟨ζe, hζe, huni⟩ := huniq
    have h1 : ((1 : torsion K), (n - m)) = ζe := by
      refine huni _ ?_
      show (∏ i, fundSystem K i ^ ((n - m) i : ℤ))
        = ((1 : torsion K) : (𝓞 K)ˣ) * ∏ i, fundSystem K i ^ ((n - m) i : ℤ)
      rw [OneMemClass.coe_one, one_mul]
    have h2 : ((⟨_, hμtor⟩ : torsion K), (0 : Fin (rank K) → ℤ)) = ζe := by
      refine huni _ ?_
      show (∏ i, fundSystem K i ^ ((n - m) i : ℤ))
        = ((∏ i, fundSystem K i ^ (m i : ℤ))⁻¹ * ∏ i, fundSystem K i ^ (n i : ℤ))
          * ∏ i, fundSystem K i ^ ((0 : Fin (rank K) → ℤ) i)
      rw [hμpow]
      simp
    rw [← h2] at h1
    have hnm : n - m = 0 := by
      have := congrArg Prod.snd h1
      simpa using this
    have hμ1 : ((∏ i, fundSystem K i ^ (m i : ℤ))⁻¹
        * ∏ i, fundSystem K i ^ (n i : ℤ)) = 1 := by
      rw [hμpow, show n - m = 0 from hnm]
      simp
    have hn : n = m := by
      have := sub_eq_zero.mp hnm
      exact this
    have hab' : a = b := by
      rw [hμ1, one_smul] at hmove
      exact hmove
    simp [hn, hab']
  · rintro ⟨v, hvlat, hvne⟩
    have hvnorm : mixedEmbedding.norm v ≠ 0 := by
      rw [mem_idealLattice] at hvlat
      obtain ⟨y, hy, rfl⟩ := hvlat
      rw [norm_eq_norm]
      have hy0 : y ≠ 0 := fun h => hvne (by rw [h, map_zero])
      have hN : Algebra.norm ℚ y ≠ 0 := by exact Algebra.norm_ne_zero_iff.mpr hy0
      simpa using hN
    obtain ⟨u, hu⟩ := exists_unit_smul_mem hvnorm
    obtain ⟨⟨ζtor, nexp⟩, hdecomp, -⟩ := exist_unique_eq_mul_prod K u
    have hζinv : ((ζtor : (𝓞 K)ˣ))⁻¹ ∈ torsion K := inv_mem ζtor.2
    have hwv_cone : (∏ i, fundSystem K i ^ (nexp i)) • v ∈ fundamentalCone K := by
      have h1 : ((ζtor : (𝓞 K)ˣ))⁻¹ • (u • v) ∈ fundamentalCone K :=
        torsion_smul_mem_of_mem hu hζinv
      rw [smul_smul] at h1
      have heq : ((ζtor : (𝓞 K)ˣ))⁻¹ * u = ∏ i, fundSystem K i ^ (nexp i) := by
        rw [hdecomp, ← mul_assoc, inv_mul_cancel, one_mul]
      rwa [heq] at h1
    have hwv_lat : (∏ i, fundSystem K i ^ (nexp i)) • v
        ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) :=
      unit_smul_mem_idealLattice K J _ hvlat
    refine ⟨⟨⟨(∏ i, fundSystem K i ^ (nexp i)) • v,
      Set.mem_inter hwv_cone (SetLike.mem_coe.mpr hwv_lat)⟩, fun i => -(nexp i)⟩, ?_⟩
    rw [Subtype.ext_iff]
    show (∏ i, fundSystem K i ^ ((fun i => -(nexp i)) i))
        • ((∏ i, fundSystem K i ^ (nexp i)) • v) = v
    have hprodinv : (∏ i, fundSystem K i ^ ((fun i => -(nexp i)) i))
        = (∏ i, fundSystem K i ^ (nexp i))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [zpow_neg]
    rw [hprodinv, inv_smul_smul]

open scoped Classical in
/-- The box integral of a `unitLattice`-periodic function does not depend on the choice of
ℤ-basis of the unit lattice: any two `ZSpan` boxes are fundamental domains of the same
lattice. -/
theorem setIntegral_box_swap (f : logSpace K → ℝ)
    (hf : ∀ l ∈ unitLattice K, ∀ x, f (l + x) = f x) :
    ∫ u in ZSpan.fundamentalDomain
      ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ), f u
      = ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ), f u := by
  have h1 := ZSpan.isAddFundamentalDomain
    ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ) volume
  have h2 := ZSpan.isAddFundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ) volume
  rw [(Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ] at h1
  rw [(basisUnitLattice K).ofZLatticeBasis_span ℝ] at h2
  haveI : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  refine h1.setIntegral_eq h2 (f := f) (fun l x => ?_)
  rw [Submodule.vadd_def, vadd_eq_add]
  exact hf (l : logSpace K) l.2 x

open scoped Classical in
/-- `heckeG` computed over the canonical `basisUnitLattice` box — the box whose translates
are indexed by `logEmbedding_fundSystem`. -/
theorem heckeG_eq_basisUnitLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    heckeG K I t = (torsionOrder K : ℝ)⁻¹ *
      ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        heckeTheta K I (heckeWeights K t u) := by
  rw [heckeG]
  congr 1
  refine setIntegral_box_swap K _ (fun l hl x => ?_)
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hl
  rw [add_comm, ← ha]
  exact heckeTheta_heckeWeights_periodic K I _ x (Additive.toMul a)

open scoped Classical in
/-- The composite coordinate identification `EuclideanSpace ≃ mixedSpace` through which
`idealZLattice` is the comap of `idealLattice`. -/
noncomputable def euclidMixedEquiv : EuclideanSpace ℝ (index K) ≃ₗ[ℝ] mixedSpace K :=
  ((euclidean.stdOrthonormalBasis K).repr.symm.toLinearEquiv).trans
    (euclidean.toMixed K).toLinearEquiv

open scoped Classical in
theorem mem_idealZLattice_iff_euclidMixed (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : EuclideanSpace ℝ (index K)) :
    v ∈ idealZLattice K I ↔ euclidMixedEquiv K v ∈ mixedEmbedding.idealLattice K I := by
  rw [idealZLattice, euclideanIdealLattice, ← SetLike.mem_coe, ZLattice.coe_comap,
    Set.mem_preimage, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe]
  rfl

open scoped Classical in
/-- **The Euclidean cone unfolding**: nonzero points of the Euclidean ideal lattice of an
integral ideal are indexed by cone points × fundamental-unit exponents. -/
noncomputable def euclidConeEquiv (J : (Ideal (𝓞 K))⁰) :
    {v : EuclideanSpace ℝ (index K) //
        v ∈ idealZLattice K (FractionalIdeal.mk0 K J) ∧ v ≠ 0}
      ≃ (idealSet K J) × (Fin (rank K) → ℤ) := by
  refine (Equiv.subtypeEquiv (euclidMixedEquiv K).toEquiv (fun v => ?_)).trans
    (coneUnfoldEquiv K J).symm
  constructor
  · rintro ⟨hmem, hne⟩
    exact ⟨(mem_idealZLattice_iff_euclidMixed K _ v).mp hmem, by
      simp only [LinearEquiv.coe_toEquiv]
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact hne⟩
  · rintro ⟨hmem, hne⟩
    refine ⟨(mem_idealZLattice_iff_euclidMixed K _ v).mpr ?_, fun h0 => hne (by
      simp only [LinearEquiv.coe_toEquiv, h0, map_zero])⟩
    simpa using hmem

open scoped Classical in
theorem euclidMixedEquiv_symm_mixedEmbedding (x : K) :
    (euclidMixedEquiv K).symm (mixedEmbedding K x) = embeddingCoords K x := by
  rw [euclidMixedEquiv, embeddingCoords]
  rfl

open scoped Classical in
/-- The image of `logEmbedding` of a fundamental-system power is the corresponding
ℤ-combination of the `basisUnitLattice` box basis. -/
theorem logEmbedding_prod_fundSystem (n : Fin (rank K) → ℤ) :
    logEmbedding K (Additive.ofMul (∏ i, fundSystem K i ^ (n i)))
      = ∑ i, n i • (((basisUnitLattice K).ofZLatticeBasis ℝ) i : logSpace K) := by
  have h1 : Additive.ofMul (∏ i, fundSystem K i ^ (n i))
      = ∑ i, n i • Additive.ofMul (fundSystem K i) := by
    induction (Finset.univ : Finset (Fin (rank K))) using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
        rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, logEmbedding_fundSystem]
  congr 1
  rw [Module.Basis.ofZLatticeBasis_apply]

open scoped Classical in
/-- **Per-point unit shift**: the Gaussian argument of a unit-scaled point at
log-coordinates `u` is that of the original point at translated coordinates. -/
theorem sum_placeWeights_unit_smul (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) (y : K) :
    ∑ i : index K, placeWeights K (heckeWeights K t u) i
        * (((euclidMixedEquiv K).symm (ε • mixedEmbedding K y)) i) ^ 2
      = ∑ i : index K, placeWeights K (heckeWeights K t
          (u + logEmbedding K (Additive.ofMul ε))) i * ((embeddingCoords K y) i) ^ 2 := by
  have hsmul : (ε • mixedEmbedding K y : mixedSpace K)
      = mixedEmbedding K (algebraMap (𝓞 K) K (ε : 𝓞 K) * y) := by
    rw [unitSMul_smul, ← map_mul]
  rw [hsmul, euclidMixedEquiv_symm_mixedEmbedding,
    sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq,
    heckeWeights_add_logEmbedding]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, mul_pow]
  ring

open scoped Classical in
/-- **Reindex a zero-removed lattice sum along the Euclidean cone unfolding**: the sum
over nonzero points of the ideal lattice becomes a sum over cone points × unit exponents. -/
theorem tsum_ite_eq_tsum_coneUnfold (J : (Ideal (𝓞 K))⁰)
    (g : EuclideanSpace ℝ (index K) → ℝ) :
    (∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        if v = 0 then 0 else g (v : EuclideanSpace ℝ (index K)))
      = ∑' p : (idealSet K J) × (Fin (rank K) → ℤ),
          g ((euclidMixedEquiv K).symm
            ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K)))) := by
  have hmem : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (euclidMixedEquiv K).symm ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K)))
        ∈ idealZLattice K (FractionalIdeal.mk0 K J) := by
    intro p
    rw [mem_idealZLattice_iff_euclidMixed, LinearEquiv.apply_symm_apply]
    exact unit_smul_mem_idealLattice K J _ (p.1.2.2)
  have hne : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (⟨(euclidMixedEquiv K).symm ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K))),
        hmem p⟩ : idealZLattice K (FractionalIdeal.mk0 K J)) ≠ 0 := by
    intro p h0
    have h1 : (euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K))) = 0 := by
      have := congrArg (fun z : idealZLattice K (FractionalIdeal.mk0 K J) =>
        (z : EuclideanSpace ℝ (index K))) h0
      simpa using this
    rw [LinearEquiv.map_eq_zero_iff] at h1
    have hp1ne : ((p.1 : mixedSpace K)) ≠ 0 := by
      intro hz
      have hc := p.1.2.1
      rw [hz] at hc
      exact hc.2 (map_zero (mixedEmbedding.norm (K := K)))
    exact (unit_smul_ne_zero K _ hp1ne) h1
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun p => ⟨(euclidMixedEquiv K).symm
      ((∏ i, fundSystem K i ^ ((p : (idealSet K J) × (Fin (rank K) → ℤ)).2 i))
        • (((p : (idealSet K J) × (Fin (rank K) → ℤ)).1 : mixedSpace K))), hmem p⟩)
    ?_ ?_ ?_
  · -- injectivity
    rintro p q hpq
    have hval := congrArg (fun z : idealZLattice K (FractionalIdeal.mk0 K J) =>
      (z : EuclideanSpace ℝ (index K))) hpq
    simp only at hval
    have hmix := (euclidMixedEquiv K).symm.injective hval
    have hcu : coneUnfoldEquiv K J (p : (idealSet K J) × (Fin (rank K) → ℤ))
        = coneUnfoldEquiv K J (q : (idealSet K J) × (Fin (rank K) → ℤ)) :=
      Subtype.ext hmix
    exact Subtype.ext ((coneUnfoldEquiv K J).injective hcu)
  · -- support inclusion
    rintro v hv
    rw [Function.mem_support] at hv
    have hvne : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hvne' : (v : EuclideanSpace ℝ (index K)) ≠ 0 := by
      intro h0
      exact hvne (Subtype.ext h0)
    set w : {x : EuclideanSpace ℝ (index K) //
        x ∈ idealZLattice K (FractionalIdeal.mk0 K J) ∧ x ≠ 0} :=
      ⟨(v : EuclideanSpace ℝ (index K)), v.2, hvne'⟩ with hw
    set pr := euclidConeEquiv K J w with hpr
    have hback : (euclidConeEquiv K J).symm pr = w := Equiv.symm_apply_apply _ _
    -- compute the value of the inverse
    have hvalsymm : ((euclidConeEquiv K J).symm pr : EuclideanSpace ℝ (index K))
        = (euclidMixedEquiv K).symm
            ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K))) := by
      rw [euclidConeEquiv]
      rfl
    have hvw : (euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K)))
        = (v : EuclideanSpace ℝ (index K)) := by
      rw [← hvalsymm, hback]
    have hgpr : g ((euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K)))) ≠ 0 := by
      rw [hvw]
      rwa [if_neg hvne] at hv
    refine ⟨⟨pr, hgpr⟩, ?_⟩
    exact Subtype.ext hvw
  · -- pointwise agreement
    rintro ⟨p, hp⟩
    rw [if_neg (hne p)]

open scoped Classical in
/-- **The theta tail as a cone sum with shifted log-coordinates**: reindex + per-point
unit shift combined. Each cone point contributes through its canonical algebraic
preimage, and the fundamental-unit exponents move into a translation of `u`. -/
theorem heckeTheta_tail_cone (J : (Ideal (𝓞 K))⁰) (t : ℝ) (u : logSpace K) :
    (∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        if v = 0 then 0 else Real.exp (-π * ∑ i : index K,
          placeWeights K (heckeWeights K t u) i
            * ((v : EuclideanSpace ℝ (index K)) i) ^ 2))
      = ∑' p : (idealSet K J) × (Fin (rank K) → ℤ),
          Real.exp (-π * ∑ i : index K, placeWeights K (heckeWeights K t
            (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (p.2 j))))) i
              * ((embeddingCoords K (algebraMap (𝓞 K) K
                  ((preimageOfMemIntegerSet (idealSetMap K J p.1)) : 𝓞 K))) i) ^ 2) := by
  rw [tsum_ite_eq_tsum_coneUnfold K J (g := fun x => Real.exp (-π * ∑ i : index K,
    placeWeights K (heckeWeights K t u) i * (x i) ^ 2))]
  refine tsum_congr (fun p => ?_)
  congr 1
  have hcoe : ((p.1 : mixedSpace K))
      = mixedEmbedding K (algebraMap (𝓞 K) K
          ((preimageOfMemIntegerSet (idealSetMap K J p.1)) : 𝓞 K)) := by
    rw [show (algebraMap (𝓞 K) K
        ((preimageOfMemIntegerSet (idealSetMap K J p.1)) : 𝓞 K))
      = ((preimageOfMemIntegerSet (idealSetMap K J p.1) : 𝓞 K) : K) from rfl]
    rw [mixedEmbedding_preimageOfMemIntegerSet]
    rw [idealSetMap_apply]
  rw [hcoe]
  exact congrArg (fun r => -π * r)
    (sum_placeWeights_unit_smul K t u (∏ j, fundSystem K j ^ (p.2 j)) _)

open scoped Classical in
/-- **Tiling the log-space by unit-box translates**: the integral of an integrable
function over `logSpace` is the sum over fundamental-unit exponents of box integrals at
translated arguments. -/
theorem integral_eq_tsum_box_shift (f : logSpace K → ℝ) (hf : Integrable f) :
    ∫ u, f u = ∑' n : Fin (rank K) → ℤ,
      ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        f (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (n j)))) := by
  classical
  set B := (basisUnitLattice K).ofZLatticeBasis ℝ with hB
  have hFD := ZSpan.isAddFundamentalDomain B volume
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑B)) (logSpace K) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑B)).toAddSubgroup
        (logSpace K) volume)
  rw [hFD.integral_eq_tsum' f hf]
  have hpre : ∀ g : Submodule.span ℤ (Set.range ⇑B),
      ∫ x in ZSpan.fundamentalDomain B, f (-g +ᵥ x)
        = ∫ x in ZSpan.fundamentalDomain B, f (-(g : logSpace K) + x) := by
    intro g
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun x _ => ?_)
    rw [Submodule.vadd_def, vadd_eq_add]
    norm_cast
  rw [tsum_congr hpre]
  -- reindex the span by exponent vectors
  set eB := ((Module.Basis.restrictScalars ℤ B).equivFun).toEquiv with heB
  rw [← Equiv.tsum_eq eB.symm (fun g => ∫ u in ZSpan.fundamentalDomain B,
    f (-(g : logSpace K) + u))]
  · -- now both sides are sums over exponent vectors; match term-by-term after n ↦ -n
    rw [← Equiv.tsum_eq (Equiv.neg (Fin (rank K) → ℤ)) (fun n =>
      ∫ u in ZSpan.fundamentalDomain B,
        f (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (n j)))))]
    refine tsum_congr (fun n => ?_)
    have hval : ((eB.symm n : Submodule.span ℤ (Set.range ⇑B)) : logSpace K)
        = ∑ i, n i • (B i) := by
      rw [heB]
      show (((Module.Basis.restrictScalars ℤ B).equivFun.symm n :
        Submodule.span ℤ (Set.range ⇑B)) : logSpace K) = _
      rw [(Module.Basis.restrictScalars ℤ B).equivFun_symm_apply]
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Module.Basis.restrictScalars_apply]
    have hshift : logEmbedding K (Additive.ofMul (∏ j, fundSystem K j
          ^ ((Equiv.neg (Fin (rank K) → ℤ)) n j)))
        = -((eB.symm n : Submodule.span ℤ (Set.range ⇑B)) : logSpace K) := by
      rw [logEmbedding_prod_fundSystem, hval, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Equiv.neg_apply, Pi.neg_apply, neg_smul, ← hB]
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun u _ => ?_)
    rw [hshift]
    congr 1
    abel

open scoped Classical in
/-- Cone points of an integral ideal form a countable family (they sit inside the ideal
lattice, which is a discrete subgroup). -/
instance instCountableIdealSet (J : (Ideal (𝓞 K))⁰) : Countable (idealSet K J) := by
  have hinj : Function.Injective (fun a : idealSet K J =>
      (⟨(a : mixedSpace K), a.2.2⟩ :
        mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))) := by
    intro a b hab
    have := congrArg (fun z : mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) =>
      (z : mixedSpace K)) hab
    exact Subtype.ext this
  exact Function.Injective.countable hinj

open scoped Classical in
/-- **Tiling the log-space by unit-box translates, `lintegral` version** — no
integrability hypothesis needed. -/
theorem lintegral_eq_tsum_box_shift (f : logSpace K → ℝ≥0∞) :
    ∫⁻ u, f u = ∑' n : Fin (rank K) → ℤ,
      ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        f (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (n j)))) := by
  classical
  set B := (basisUnitLattice K).ofZLatticeBasis ℝ with hB
  have hFD := ZSpan.isAddFundamentalDomain B volume
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑B)) (logSpace K) volume :=
    inferInstanceAs
      (VAddInvariantMeasure (Submodule.span ℤ (Set.range ⇑B)).toAddSubgroup
        (logSpace K) volume)
  rw [hFD.lintegral_eq_tsum' f]
  have hpre : ∀ g : Submodule.span ℤ (Set.range ⇑B),
      ∫⁻ x in ZSpan.fundamentalDomain B, f (-g +ᵥ x)
        = ∫⁻ x in ZSpan.fundamentalDomain B, f (-(g : logSpace K) + x) := by
    intro g
    refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
      (fun x _ => ?_)
    rw [Submodule.vadd_def, vadd_eq_add]
    norm_cast
  rw [tsum_congr hpre]
  set eB := ((Module.Basis.restrictScalars ℤ B).equivFun).toEquiv with heB
  rw [← Equiv.tsum_eq eB.symm (fun g => ∫⁻ u in ZSpan.fundamentalDomain B,
    f (-(g : logSpace K) + u))]
  rw [← Equiv.tsum_eq (Equiv.neg (Fin (rank K) → ℤ)) (fun n =>
    ∫⁻ u in ZSpan.fundamentalDomain B,
      f (u + logEmbedding K (Additive.ofMul (∏ j, fundSystem K j ^ (n j)))))]
  refine tsum_congr (fun n => ?_)
  have hval : ((eB.symm n : Submodule.span ℤ (Set.range ⇑B)) : logSpace K)
      = ∑ i, n i • (B i) := by
    rw [heB]
    show (((Module.Basis.restrictScalars ℤ B).equivFun.symm n :
      Submodule.span ℤ (Set.range ⇑B)) : logSpace K) = _
    rw [(Module.Basis.restrictScalars ℤ B).equivFun_symm_apply]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Module.Basis.restrictScalars_apply]
  have hshift : logEmbedding K (Additive.ofMul (∏ j, fundSystem K j
        ^ ((Equiv.neg (Fin (rank K) → ℤ)) n j)))
      = -((eB.symm n : Submodule.span ℤ (Set.range ⇑B)) : logSpace K) := by
    rw [logEmbedding_prod_fundSystem, hval, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Equiv.neg_apply, Pi.neg_apply, neg_smul, ← hB]
  refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun u _ => ?_)
  rw [hshift]
  congr 1
  abel

open scoped Classical in
/-- `ℝ≥0∞`-valued version of `tsum_ite_eq_tsum_coneUnfold` (same unfolding, for
lintegral-valued families). -/
theorem tsum_ite_eq_tsum_coneUnfold_ennreal (J : (Ideal (𝓞 K))⁰)
    (g : EuclideanSpace ℝ (index K) → ℝ≥0∞) :
    (∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
        if v = 0 then 0 else g (v : EuclideanSpace ℝ (index K)))
      = ∑' p : (idealSet K J) × (Fin (rank K) → ℤ),
          g ((euclidMixedEquiv K).symm
            ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K)))) := by
  have hmem : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (euclidMixedEquiv K).symm ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K)))
        ∈ idealZLattice K (FractionalIdeal.mk0 K J) := by
    intro p
    rw [mem_idealZLattice_iff_euclidMixed, LinearEquiv.apply_symm_apply]
    exact unit_smul_mem_idealLattice K J _ (p.1.2.2)
  have hne : ∀ p : (idealSet K J) × (Fin (rank K) → ℤ),
      (⟨(euclidMixedEquiv K).symm ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K))),
        hmem p⟩ : idealZLattice K (FractionalIdeal.mk0 K J)) ≠ 0 := by
    intro p h0
    have h1 : (euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (p.2 i)) • ((p.1 : mixedSpace K))) = 0 := by
      have := congrArg (fun z : idealZLattice K (FractionalIdeal.mk0 K J) =>
        (z : EuclideanSpace ℝ (index K))) h0
      simpa using this
    rw [LinearEquiv.map_eq_zero_iff] at h1
    have hp1ne : ((p.1 : mixedSpace K)) ≠ 0 := by
      intro hz
      have hc := p.1.2.1
      rw [hz] at hc
      exact hc.2 (map_zero (mixedEmbedding.norm (K := K)))
    exact (unit_smul_ne_zero K _ hp1ne) h1
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun p => ⟨(euclidMixedEquiv K).symm
      ((∏ i, fundSystem K i ^ ((p : (idealSet K J) × (Fin (rank K) → ℤ)).2 i))
        • (((p : (idealSet K J) × (Fin (rank K) → ℤ)).1 : mixedSpace K))), hmem p⟩)
    ?_ ?_ ?_
  · rintro p q hpq
    have hval := congrArg (fun z : idealZLattice K (FractionalIdeal.mk0 K J) =>
      (z : EuclideanSpace ℝ (index K))) hpq
    simp only at hval
    have hmix := (euclidMixedEquiv K).symm.injective hval
    have hcu : coneUnfoldEquiv K J (p : (idealSet K J) × (Fin (rank K) → ℤ))
        = coneUnfoldEquiv K J (q : (idealSet K J) × (Fin (rank K) → ℤ)) :=
      Subtype.ext hmix
    exact Subtype.ext ((coneUnfoldEquiv K J).injective hcu)
  · rintro v hv
    rw [Function.mem_support] at hv
    have hvne : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hvne' : (v : EuclideanSpace ℝ (index K)) ≠ 0 := by
      intro h0
      exact hvne (Subtype.ext h0)
    set w : {x : EuclideanSpace ℝ (index K) //
        x ∈ idealZLattice K (FractionalIdeal.mk0 K J) ∧ x ≠ 0} :=
      ⟨(v : EuclideanSpace ℝ (index K)), v.2, hvne'⟩ with hw
    set pr := euclidConeEquiv K J w with hpr
    have hback : (euclidConeEquiv K J).symm pr = w := Equiv.symm_apply_apply _ _
    have hvalsymm : ((euclidConeEquiv K J).symm pr : EuclideanSpace ℝ (index K))
        = (euclidMixedEquiv K).symm
            ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K))) := by
      rw [euclidConeEquiv]
      rfl
    have hvw : (euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K)))
        = (v : EuclideanSpace ℝ (index K)) := by
      rw [← hvalsymm, hback]
    have hgpr : g ((euclidMixedEquiv K).symm
        ((∏ i, fundSystem K i ^ (pr.2 i)) • ((pr.1 : mixedSpace K)))) ≠ 0 := by
      rw [hvw]
      rwa [if_neg hvne] at hv
    refine ⟨⟨pr, hgpr⟩, ?_⟩
    exact Subtype.ext hvw
  · rintro ⟨p, hp⟩
    rw [if_neg (hne p)]

open scoped Classical in
/-- The canonical algebraic preimage of a cone point. -/
noncomputable def conePreimage (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) : K :=
  algebraMap (𝓞 K) K ((preimageOfMemIntegerSet (idealSetMap K J a)) : 𝓞 K)

open scoped Classical in
theorem mixedEmbedding_conePreimage (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    mixedEmbedding K (conePreimage K J a) = (a : mixedSpace K) := by
  rw [conePreimage, show (algebraMap (𝓞 K) K
      ((preimageOfMemIntegerSet (idealSetMap K J a)) : 𝓞 K))
    = ((preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : K) from rfl,
    mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]

open scoped Classical in
/-- A single Gaussian term of the Hecke theta, as a function of the log-coordinate. -/
noncomputable def gaussTerm (t : ℝ) (u : logSpace K)
    (x : EuclideanSpace ℝ (index K)) : ℝ :=
  Real.exp (-π * ∑ i : index K, placeWeights K (heckeWeights K t u) i * (x i) ^ 2)

open scoped Classical in
theorem gaussTerm_pos (t : ℝ) (u : logSpace K) (x : EuclideanSpace ℝ (index K)) :
    0 < gaussTerm K t u x := Real.exp_pos _

open scoped Classical in
theorem continuous_gaussTerm (t : ℝ) (c : EuclideanSpace ℝ (index K)) :
    Continuous (fun u : logSpace K => gaussTerm K t u c) := by
  refine Real.continuous_exp.comp ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ (fun i _ => Continuous.mul ?_ continuous_const)
  have hw : ∀ w : InfinitePlace K,
      Continuous (fun u : logSpace K => heckeWeights K t u w) := by
    intro w
    show Continuous (fun u : logSpace K =>
      t ^ ((1 : ℝ) / (Module.finrank ℚ K)) * Real.exp (2 * fullLog K u w / mult w))
    refine Continuous.mul continuous_const ?_
    refine Real.continuous_exp.comp ?_
    refine Continuous.div_const ?_ _
    refine Continuous.mul continuous_const ?_
    have hfl : Continuous (fun u : logSpace K => fullLog K u w) := by
      rw [show (fun u : logSpace K => fullLog K u w)
        = fun u : logSpace K => if h : w = (w₀ : InfinitePlace K) then
            -∑ w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}, u w'
          else u ⟨w, h⟩ from rfl]
      split_ifs with h
      · exact (continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)).neg
      · exact continuous_apply _
    exact hfl
  rcases i with (w | ⟨w, j⟩) <;>
    · show Continuous (fun u : logSpace K => heckeWeights K t u _)
      exact hw _

open scoped Classical in
/-- The unit shift of a Gaussian term, in `gaussTerm` form. -/
theorem gaussTerm_unit_smul (t : ℝ) (u : logSpace K) (ε : (𝓞 K)ˣ) (y : K) :
    gaussTerm K t u ((euclidMixedEquiv K).symm (ε • mixedEmbedding K y))
      = gaussTerm K t (u + logEmbedding K (Additive.ofMul ε)) (embeddingCoords K y) := by
  rw [gaussTerm, gaussTerm]
  exact congrArg (fun r => Real.exp (-π * r))
    (sum_placeWeights_unit_smul K t u ε y)

open scoped Classical in
/-- **The box lintegral of the theta tail, fully unfolded** along the fundamental cone. -/
theorem lintegral_box_theta_tail (J : (Ideal (𝓞 K))⁰) {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      ENNReal.ofReal
        (heckeTheta K (FractionalIdeal.mk0 K J) (heckeWeights K t u) - 1)
      = ∑' a : idealSet K J, ∫⁻ u : logSpace K,
          ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a))) := by
  have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  set G : EuclideanSpace ℝ (index K) → ℝ≥0∞ := fun x =>
    ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      ENNReal.ofReal (gaussTerm K t u x) with hG
  -- Step 1: pointwise ENNReal tail expansion
  have hstep1 : ∀ u : logSpace K,
      ENNReal.ofReal (heckeTheta K (FractionalIdeal.mk0 K J) (heckeWeights K t u) - 1)
        = ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
            if v = 0 then 0
            else ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K))) := by
    intro u
    have ha : 0 < Finset.univ.inf' hne (heckeWeights K t u) :=
      (Finset.lt_inf'_iff hne).mpr (fun w _ => heckeWeights_pos K ht u w)
    have hca : ∀ w, Finset.univ.inf' hne (heckeWeights K t u) ≤ heckeWeights K t u w :=
      fun w => Finset.inf'_le _ (Finset.mem_univ w)
    have hplaceW : ∀ i, Finset.univ.inf' hne (heckeWeights K t u)
        ≤ placeWeights K (heckeWeights K t u) i := by
      rintro (w | ⟨w, j⟩) <;> exact hca _
    have hsummable : Summable fun v : idealZLattice K (FractionalIdeal.mk0 K J) =>
        (if v = 0 then 0
          else gaussTerm K t u (v : EuclideanSpace ℝ (index K))) := by
      refine (summable_real_weightedGaussian _ ha hplaceW).of_nonneg_of_le
        (fun v => ?_) (fun v => ?_)
      · split_ifs
        · exact le_refl 0
        · exact (gaussTerm_pos K t u _).le
      · split_ifs
        · exact (Real.exp_pos _).le
        · exact le_refl _
    rw [heckeTheta_eq_one_add K _ ha hca, add_sub_cancel_left]
    rw [show (∑' v : idealZLattice K (FractionalIdeal.mk0 K J), (if v = 0 then 0
        else Real.exp (-π * ∑ i : index K,
          placeWeights K (heckeWeights K t u) i
            * ((v : EuclideanSpace ℝ (index K)) i) ^ 2)))
      = (∑' v : idealZLattice K (FractionalIdeal.mk0 K J), (if v = 0 then 0
        else gaussTerm K t u (v : EuclideanSpace ℝ (index K)))) from rfl]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun v => by
      split_ifs
      · exact le_refl 0
      · exact (gaussTerm_pos K t u _).le) hsummable]
    refine tsum_congr (fun v => ?_)
    split_ifs
    · exact ENNReal.ofReal_zero
    · rfl
  rw [setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
    (fun u _ => hstep1 u)]
  -- Step 2: swap lintegral and tsum
  rw [lintegral_tsum (fun v => ?_)]
  swap
  · by_cases hv : v = 0
    · simp only [if_pos hv]
      exact aemeasurable_const
    · simp only [if_neg hv]
      exact (ENNReal.continuous_ofReal.comp (continuous_gaussTerm K t _)).aemeasurable
  -- Step 3: the per-v box integral is `ite (v = 0) 0 (G ↑v)`
  have hstep3 : ∀ v : idealZLattice K (FractionalIdeal.mk0 K J),
      (∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        if v = 0 then 0
        else ENNReal.ofReal (gaussTerm K t u (v : EuclideanSpace ℝ (index K))))
        = if v = 0 then 0 else G (v : EuclideanSpace ℝ (index K)) := by
    intro v
    by_cases hv : v = 0
    · rw [if_pos hv]
      rw [setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
        (fun u _ => if_pos hv), lintegral_zero]
    · rw [if_neg hv, hG]
      exact setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
        (fun u _ => if_neg hv)
  rw [tsum_congr hstep3]
  -- Step 4: cone reindex (on the G-valued family)
  rw [tsum_ite_eq_tsum_coneUnfold_ennreal K J G]
  -- Step 5+6: per-point shift, then split the product sum
  rw [ENNReal.tsum_prod']
  refine tsum_congr (fun a => ?_)
  have hstep5 : ∀ n : Fin (rank K) → ℤ,
      G ((euclidMixedEquiv K).symm
        ((∏ j, fundSystem K j ^ (n j)) • ((a : mixedSpace K))))
        = ∫⁻ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
            ENNReal.ofReal (gaussTerm K t (u + logEmbedding K
              (Additive.ofMul (∏ j, fundSystem K j ^ (n j))))
              (embeddingCoords K (conePreimage K J a))) := by
    intro n
    rw [hG]
    refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
      (fun u _ => ?_)
    refine congrArg ENNReal.ofReal ?_
    rw [← mixedEmbedding_conePreimage K J a]
    exact gaussTerm_unit_smul K t u (∏ j, fundSystem K j ^ (n j)) (conePreimage K J a)
  rw [tsum_congr hstep5]
  -- Step 7: re-tile to the whole log-space
  rw [lintegral_eq_tsum_box_shift K (fun u =>
    ENNReal.ofReal (gaussTerm K t u (embeddingCoords K (conePreimage K J a))))]

open scoped Classical in
/-- The log-coordinates map of the Hecke substitution: `(τ, u) ↦ (τ/n + 2·fullLog(u)_w/m_w)_w`.
Its bijectivity is the change of variables underlying the per-orbit Γ-factorisation. -/
noncomputable def heckeLogMap : (ℝ × logSpace K) →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun p := fun w => p.1 / (Module.finrank ℚ K) + 2 * fullLog K p.2 w / mult w
  map_add' p q := by
    funext w
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [fullLog_add, Pi.add_apply]
    ring
  map_smul' c p := by
    funext w
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    have hsmul : fullLog K (c • p.2) w = c * fullLog K p.2 w := by
      rw [show c • p.2 = fun w' : {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)} =>
        c * p.2 w' from rfl]
      rw [fullLog, fullLog]
      split_ifs with h
      · rw [← Finset.mul_sum]
        ring
      · rfl
    rw [hsmul]
    ring

open scoped Classical in
theorem heckeLogMap_injective : Function.Injective (heckeLogMap K) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨τ, u⟩ hp
  rw [LinearMap.mem_ker] at hp
  have hw : ∀ w : InfinitePlace K,
      τ / (Module.finrank ℚ K) + 2 * fullLog K u w / mult w = 0 :=
    fun w => congrFun hp w
  have hn : (0:ℝ) < (Module.finrank ℚ K : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  -- weighted row sum: multiply by mult w / 2 and sum
  have hsum : ∑ w : InfinitePlace K,
      (mult w : ℝ) / 2 * (τ / (Module.finrank ℚ K) + 2 * fullLog K u w / mult w)
      = τ / 2 := by
    have hterm : ∀ w : InfinitePlace K,
        (mult w : ℝ) / 2 * (τ / (Module.finrank ℚ K) + 2 * fullLog K u w / mult w)
        = (mult w : ℝ) * τ / (2 * Module.finrank ℚ K) + fullLog K u w := by
      intro w
      have hm : (mult w : ℝ) ≠ 0 := by
        have := mult_pos (w := w)
        positivity
      field_simp
    rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_add_distrib,
      sum_fullLog, add_zero, ← Finset.sum_div, ← Finset.sum_mul,
      show (∑ w : InfinitePlace K, (mult w : ℝ)) = (Module.finrank ℚ K : ℝ) by
        exact_mod_cast congrArg Nat.cast (sum_mult_eq (K := K))]
    field_simp
  have hτ : τ = 0 := by
    have h0 : ∑ w : InfinitePlace K,
        (mult w : ℝ) / 2 * (τ / (Module.finrank ℚ K) + 2 * fullLog K u w / mult w)
        = 0 := by
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [hw w, mul_zero]
    rw [hsum] at h0
    linarith
  have hu : u = 0 := by
    funext w'
    have := hw w'
    rw [hτ, zero_div, zero_add] at this
    have hm : (mult (w' : InfinitePlace K) : ℝ) ≠ 0 := by
      have := mult_pos (w := (w' : InfinitePlace K))
      positivity
    have hfl : fullLog K u (w' : InfinitePlace K) = 0 := by
      field_simp at this
      linarith
    rw [fullLog] at hfl
    rw [dif_neg w'.2] at hfl
    simpa using hfl
  rw [hτ, hu]
  rfl

open scoped Classical in
theorem heckeLogMap_bijective : Function.Bijective (heckeLogMap K) := by
  have hdim : Module.finrank ℝ (ℝ × logSpace K)
      = Module.finrank ℝ (InfinitePlace K → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_pi, Module.finrank_pi]
    have hcard : Fintype.card {w : InfinitePlace K // w ≠ (w₀ : InfinitePlace K)}
        = Fintype.card (InfinitePlace K) - 1 := by
      rw [Fintype.card_subtype_compl (p := fun w : InfinitePlace K =>
        w = (w₀ : InfinitePlace K))]
      congr 1
    rw [hcard]
    have hpos : 1 ≤ Fintype.card (InfinitePlace K) :=
      Fintype.card_pos_iff.mpr inferInstance
    omega

  exact ⟨heckeLogMap_injective K,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (heckeLogMap_injective K)⟩

open scoped Classical in
/-- The Hecke substitution as a linear equivalence — the change of variables of the
per-orbit Mellin factorisation. -/
noncomputable def heckeLogEquiv : (ℝ × logSpace K) ≃ₗ[ℝ] (InfinitePlace K → ℝ) :=
  LinearEquiv.ofBijective (heckeLogMap K) (heckeLogMap_bijective K)

open scoped Classical in
/-- **The point-dependence of the Gaussian factors through the norm**: the whole-space
lintegral of a Gaussian term at the point `ζ(y)` is that at `ζ(1)` with the ray parameter
scaled by `|N(y)|²` — via the proven `x`-absorption (`sq_mul_heckeWeights`) and
translation invariance. No Jacobian needed. -/
theorem lintegral_gaussTerm_eq_norm_scaled {y : K} (hy : y ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ u : logSpace K, ENNReal.ofReal (gaussTerm K t u (embeddingCoords K y))
      = ∫⁻ u : logSpace K, ENNReal.ofReal
          (gaussTerm K (((|Algebra.norm ℚ y| : ℚ) : ℝ) ^ 2 * t) u
            (embeddingCoords K 1)) := by
  have hpt : ∀ u : logSpace K, gaussTerm K t u (embeddingCoords K y)
      = gaussTerm K (((|Algebra.norm ℚ y| : ℚ) : ℝ) ^ 2 * t) (u + xShift K y)
          (embeddingCoords K 1) := by
    intro u
    rw [gaussTerm, gaussTerm]
    refine congrArg (fun r => Real.exp (-π * r)) ?_
    rw [sum_placeWeights_embeddingCoords_sq, sum_placeWeights_embeddingCoords_sq]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [map_one, one_pow, mul_one]
    rw [← sq_mul_heckeWeights K hy ht u w]
    ring
  simp_rw [hpt]
  exact lintegral_add_right_eq_self
    (fun u => ENNReal.ofReal (gaussTerm K (((|Algebra.norm ℚ y| : ℚ) : ℝ) ^ 2 * t) u
      (embeddingCoords K 1))) (xShift K y)

open scoped Classical in
/-- 1-D Mellin scaling for lower integrals over the positive ray. -/
theorem lintegral_Ioi_mellin_scale {c : ℝ} (hc : 0 < c) (σ : ℝ) (H : ℝ → ℝ≥0∞)
    (hH : AEMeasurable H (volume.restrict (Set.Ioi (0:ℝ)))) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (σ - 1)) * H (c * t)
      = ENNReal.ofReal (c ^ (-σ))
        * ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (σ - 1)) * H t := by
  have hstep1 : ∀ t ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (t ^ (σ - 1)) * H (c * t)
        = ENNReal.ofReal (c ^ (1 - σ))
          * (ENNReal.ofReal ((c * t) ^ (σ - 1)) * H (c * t)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.mul_rpow hc.le ht0.le, ← mul_assoc, ← Real.rpow_add hc]
    norm_num
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpre : (fun t : ℝ => c * t) ⁻¹' (Set.Ioi (0:ℝ)) = Set.Ioi (0:ℝ) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      by_contra hle
      push Not at hle
      nlinarith
    · intro h
      positivity
  have hmap : (Measure.map (fun t : ℝ => c * t) (volume.restrict (Set.Ioi (0:ℝ))))
      = ENNReal.ofReal c⁻¹ • (volume.restrict (Set.Ioi (0:ℝ))) := by
    conv_lhs => rw [show volume.restrict (Set.Ioi (0:ℝ))
        = volume.restrict ((fun t : ℝ => c * t) ⁻¹' (Set.Ioi (0:ℝ))) by rw [hpre]]
    rw [← Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi]
    rw [show (fun t : ℝ => c * t) = (c * ·) from rfl, Real.map_volume_mul_left hc.ne']
    rw [Measure.restrict_smul]
    congr 1
    rw [abs_of_pos (by positivity : (0:ℝ) < c⁻¹)]
  have hFmeas : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ (σ - 1)) * H s)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine AEMeasurable.mul ?_ hH
    have hcont : ContinuousOn (fun s : ℝ => s ^ (σ - 1)) (Set.Ioi (0:ℝ)) :=
      fun x hx => (Real.continuousAt_rpow_const x _
        (Or.inl (ne_of_gt hx))).continuousWithinAt
    exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable
      measurableSet_Ioi
  have hsub : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal ((c * t) ^ (σ - 1)) * H (c * t)
      = ENNReal.ofReal c⁻¹
        * ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s ^ (σ - 1)) * H s := by
    have hlm := lintegral_map' (f := fun s : ℝ => ENNReal.ofReal (s ^ (σ - 1)) * H s)
      (g := fun t : ℝ => c * t)
      (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (by rw [hmap]; exact hFmeas.smul_measure _)
      (measurable_const_mul c).aemeasurable
    rw [← hlm, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show c⁻¹ = c ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add hc]
  rw [show (1 : ℝ) - σ + -1 = -σ by ring]

open scoped Classical in
/-- The norm of the canonical preimage of a cone point is its integer norm. -/
theorem abs_norm_conePreimage (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    ((|Algebra.norm ℚ (conePreimage K J a)| : ℚ) : ℝ)
      = (intNorm (idealSetMap K J a) : ℝ) := by
  rw [intNorm_coe, ← norm_eq_norm, mixedEmbedding_conePreimage]
  rw [show ((idealSetMap K J a : integerSet K) : mixedSpace K) = (a : mixedSpace K)
    from idealSetMap_apply K J a]

open scoped Classical in
/-- **The counting step (δ)**: the cone-point norm sum is `torsionOrder` times the sum
over nonzero principal ideals divisible by `J`. -/
theorem tsum_idealSet_norm_rpow (J : (Ideal (𝓞 K))⁰) (σ : ℝ) :
    ∑' a : idealSet K J,
      ENNReal.ofReal (((((|Algebra.norm ℚ (conePreimage K J a)| : ℚ) : ℝ)) ^ 2) ^ (-σ))
      = (torsionOrder K)
        * ∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
            ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
            ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
              ^ (-σ)) := by
  have hsummand : ∀ a : idealSet K J,
      ENNReal.ofReal (((((|Algebra.norm ℚ (conePreimage K J a)| : ℚ) : ℝ)) ^ 2) ^ (-σ))
        = ENNReal.ofReal ((((intNorm (idealSetMap K J a) : ℝ)) ^ 2) ^ (-σ)) := by
    intro a
    rw [abs_norm_conePreimage]
  rw [tsum_congr hsummand]
  -- fiber the cone side over the integer norm
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun a : idealSet K J =>
    intNorm (idealSetMap K J a))) (fun a =>
      ENNReal.ofReal ((((intNorm (idealSetMap K J a) : ℝ)) ^ 2) ^ (-σ))),
    ENNReal.tsum_sigma']
  -- fiber the ideal side over the norm
  have hidealfiber : (∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
        ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
          ^ (-σ)))
      = ∑' n : ℕ, ∑' _I : {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} //
            Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n},
          ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)) := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
      (fun I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} =>
          Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))))
      (fun I => ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)))]
    rw [ENNReal.tsum_sigma']
    refine tsum_congr (fun n => tsum_congr (fun I => ?_))
    show ENNReal.ofReal ((((Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) :
      Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)) = _
    rw [I.2]
  rw [hidealfiber]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  -- reduce the cone fiber to a constant sum
  have hconst : (∑' b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
      ENNReal.ofReal ((((intNorm (idealSetMap K J ((Equiv.sigmaFiberEquiv
        (fun a : idealSet K J => intNorm (idealSetMap K J a))) ⟨n, b⟩)) : ℝ)) ^ 2) ^ (-σ)))
      = ∑' _b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
          ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)) := by
    refine tsum_congr (fun b => ?_)
    show ENNReal.ofReal ((((intNorm (idealSetMap K J b.val) : ℝ)) ^ 2) ^ (-σ)) = _
    rw [b.2]
  rw [hconst]
  -- reindex the cone fiber to the mathlib norm-fiber, then to ideals × torsion
  have hfib1 : {a : idealSet K J // intNorm (idealSetMap K J a) = n}
      ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)} := by
    refine Equiv.subtypeEquivRight (fun a => ?_)
    constructor
    · intro h
      rw [← h, intNorm_coe,
        show ((idealSetMap K J a : integerSet K) : mixedSpace K) = (a : mixedSpace K)
          from idealSetMap_apply K J a]
    · intro h
      have h2 : (intNorm (idealSetMap K J a) : ℝ) = (n : ℝ) := by
        rw [intNorm_coe, show ((idealSetMap K J a : integerSet K) : mixedSpace K)
          = (a : mixedSpace K) from idealSetMap_apply K J a]
        exact h
      exact_mod_cast h2
  rw [show (∑' _b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
      ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))
    = ∑' _b : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)},
        ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)) from
    (Equiv.tsum_eq hfib1.symm (fun _ => ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))).symm]
  rw [show (∑' _b : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)},
      ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))
    = ∑' _p : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n} × (torsion K),
        ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)) from
    (Equiv.tsum_eq (idealSetEquivNorm K J n).symm
      (fun _ => ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))).symm]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
      ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n},
      (∑' _ζ : torsion K, ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))
        = (torsionOrder K) * ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)) := by
    intro I
    rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    norm_cast
  rw [tsum_congr hinner, ENNReal.tsum_mul_left]
  congr 1
  have hfibeq : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
      ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n}
      ≃ {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} //
            Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n} := by
    refine (Equiv.subtypeEquivRight (fun I => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
        (fun I => Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n)).symm
    rw [and_assoc]
  exact (Equiv.tsum_eq hfibeq.symm
    (fun _ => ENNReal.ofReal ((((n : ℝ)) ^ 2) ^ (-σ)))).symm

open scoped Classical in
/-- The nonzero principal ideals divisible by `J` are exactly `𝔟·J` for `𝔟` in the class
`[J]⁻¹`. -/
noncomputable def principalDvdEquiv (J : (Ideal (𝓞 K))⁰) :
    {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = (ClassGroup.mk0 J)⁻¹}
      ≃ {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} := by
  refine Equiv.ofBijective (fun b => ⟨b * J, ⟨(b : (Ideal (𝓞 K))⁰) , by
    rw [Submonoid.coe_mul]
    exact mul_comm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) (J : Ideal (𝓞 K))⟩, ?_⟩) ⟨?_, ?_⟩
  · -- principality
    have h1 : ClassGroup.mk0 (b * J : (Ideal (𝓞 K))⁰) = 1 := by
      rw [map_mul, b.2, inv_mul_cancel]
    have h2 := (ClassGroup.mk0_eq_one_iff
      (SetLike.coe_mem ((b * J : (Ideal (𝓞 K))⁰)))).mp
    exact h2 h1
  · -- injective
    rintro b c hbc
    have h1 : (b : (Ideal (𝓞 K))⁰) * J = (c : (Ideal (𝓞 K))⁰) * J := by
      have := congrArg (fun z : {I : (Ideal (𝓞 K))⁰ // _ ∧ _} =>
        (z : (Ideal (𝓞 K))⁰)) hbc
      simpa using this
    exact Subtype.ext (mul_right_cancel h1)
  · -- surjective
    rintro ⟨I, ⟨C, hC⟩, hP⟩
    have hCmem : C ∈ (Ideal (𝓞 K))⁰ := by
      refine mem_nonZeroDivisors_of_ne_zero (fun hC0 => ?_)
      have hI0 : (I : Ideal (𝓞 K)) = 0 := by
        rw [hC, hC0, mul_zero]
      exact nonZeroDivisors.coe_ne_zero I (by exact_mod_cast hI0)
    refine ⟨⟨⟨C, hCmem⟩, ?_⟩, ?_⟩
    · -- class of C is [J]⁻¹
      rw [eq_inv_iff_mul_eq_one, ← map_mul]
      have hprod : ((⟨C, hCmem⟩ : (Ideal (𝓞 K))⁰) * J) = I := by
        refine Subtype.ext ?_
        rw [show (((⟨C, hCmem⟩ : (Ideal (𝓞 K))⁰) * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
          = C * (J : Ideal (𝓞 K)) from rfl, hC]
        ring
      rw [hprod]
      exact (ClassGroup.mk0_eq_one_iff (SetLike.coe_mem I)).mpr hP
    · refine Subtype.ext ?_
      show (⟨C, hCmem⟩ * J : (Ideal (𝓞 K))⁰) = I
      refine Subtype.ext ?_
      rw [show ((⟨C, hCmem⟩ * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = C * (J : Ideal (𝓞 K)) from rfl, hC]
      ring

open scoped Classical in
/-- **The class fiber (δ-2)**: the sum over principal ideals divisible by `J` is the
`N(J)^{-2σ}`-scaled sum over the ideal class `[J]⁻¹`. -/
theorem tsum_principal_dvd_eq (J : (Ideal (𝓞 K))⁰) (σ : ℝ) :
    (∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
        ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
          ^ (-σ)))
      = ENNReal.ofReal ((((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ))
        * ∑' b : {b : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 b = (ClassGroup.mk0 J)⁻¹},
            ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
              ^ (-σ)) := by
  rw [← Equiv.tsum_eq (principalDvdEquiv K J) (fun I =>
    ENNReal.ofReal ((((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
      ^ (-σ))), ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun b => ?_)
  have hval : ((principalDvdEquiv K J b : {I : (Ideal (𝓞 K))⁰ // _ ∧ _}) :
      (Ideal (𝓞 K))⁰) = (b : (Ideal (𝓞 K))⁰) * J := rfl
  rw [show ENNReal.ofReal ((((Ideal.absNorm (((principalDvdEquiv K J b :
      {I : (Ideal (𝓞 K))⁰ // _ ∧ _}) : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ))
    = ENNReal.ofReal ((((Ideal.absNorm ((((b : (Ideal (𝓞 K))⁰) * J : (Ideal (𝓞 K))⁰)) :
        Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)) by rw [hval]]
  rw [show ((((b : (Ideal (𝓞 K))⁰) * J : (Ideal (𝓞 K))⁰)) : Ideal (𝓞 K))
    = ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) from rfl]
  rw [map_mul]
  rw [Nat.cast_mul, mul_pow, Real.mul_rpow (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal _)]

/-- **The per-place Gamma integral in exponential coordinates**:
`∫ e^{aλ − π e^λ} dλ = π^{-a}·Γ(a)`. -/
theorem lintegral_exp_mul_sub_pi_exp {a : ℝ} (ha : 0 < a) :
    ∫⁻ l : ℝ, ENNReal.ofReal (Real.exp (a * l - π * Real.exp l))
      = ENNReal.ofReal (π ^ (-a) * Real.Gamma a) := by
  have himg := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ)
    MeasurableSet.univ
    (f := Real.exp) (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn)
    (fun z => ENNReal.ofReal (z ^ (a - 1) * Real.exp (-π * z)))
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at himg
  have hpt : ∀ l : ℝ, ENNReal.ofReal (|Real.exp l|)
        * ENNReal.ofReal ((Real.exp l) ^ (a - 1) * Real.exp (-π * Real.exp l))
      = ENNReal.ofReal (Real.exp (a * l - π * Real.exp l)) := by
    intro l
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos l)]
    congr 1
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hLHS : ∫⁻ l : ℝ, ENNReal.ofReal (Real.exp (a * l - π * Real.exp l))
      = ∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (a - 1) * Real.exp (-π * z)) := by
    rw [himg]
    exact (lintegral_congr (fun l => hpt l)).symm
  rw [hLHS]
  have hsplit : ∀ z ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (z ^ (a - 1) * Real.exp (-π * z))
        = ENNReal.ofReal (z ^ (a - 1)) * ENNReal.ofReal (Real.exp (-(π * z))) := by
    intro z hz
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hz) _), neg_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hsplit]
  have hscale := lintegral_Ioi_mellin_scale Real.pi_pos a
    (fun z => ENNReal.ofReal (Real.exp (-z)))
    ((ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).aemeasurable)
  rw [hscale]
  have hGamma : (∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (z ^ (a - 1))
        * ENNReal.ofReal (Real.exp (-z)))
      = ENNReal.ofReal (Real.Gamma a) := by
    rw [Real.Gamma_eq_integral ha,
      ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent ha)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hx) _))))]
    refine (setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)).symm
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hz) _)]
    congr 1
    ring
  rw [hGamma, ← ENNReal.ofReal_mul (by positivity)]

open scoped Classical in
/-- The Hecke substitution as a continuous linear equivalence. -/
noncomputable def heckeLogCLE : (ℝ × logSpace K) ≃L[ℝ] (InfinitePlace K → ℝ) :=
  (heckeLogEquiv K).toContinuousLinearEquiv

open scoped Classical in
instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ × logSpace K)) := by
  rw [show (volume : Measure (ℝ × logSpace K))
    = (volume : Measure ℝ).prod (volume : Measure (logSpace K)) from rfl]
  infer_instance

open scoped Classical in
instance : Measure.IsAddHaarMeasure
    (Measure.map (heckeLogCLE K) (volume : Measure (ℝ × logSpace K))) :=
  (heckeLogCLE K).isAddHaarMeasure_map volume

open scoped Classical in
/-- **The Jacobian constant** of the Hecke substitution: the Haar-comparison factor of the
pushforward of the product volume. Its value is never needed — only positivity. -/
noncomputable def heckeJacobian : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (Measure.map (heckeLogCLE K) (volume : Measure (ℝ × logSpace K)))
    (volume : Measure (InfinitePlace K → ℝ))

open scoped Classical in
theorem map_heckeLogCLE_volume :
    Measure.map (heckeLogCLE K) (volume : Measure (ℝ × logSpace K))
      = heckeJacobian K • (volume : Measure (InfinitePlace K → ℝ)) :=
  Measure.isAddLeftInvariant_eq_smul _ _

open scoped Classical in
theorem heckeJacobian_pos : 0 < heckeJacobian K :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- Integrability of the exponential-coordinates Gamma integrand. -/
theorem integrable_exp_mul_sub_pi_exp {a : ℝ} (ha : 0 < a) :
    Integrable (fun l : ℝ => Real.exp (a * l - π * Real.exp l)) := by
  constructor
  · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun l => (Real.exp_pos _).le))]
    rw [lintegral_exp_mul_sub_pi_exp ha]
    exact ENNReal.ofReal_lt_top

/-- The Bochner form of the per-place Gamma integral. -/
theorem integral_exp_mul_sub_pi_exp {a : ℝ} (ha : 0 < a) :
    ∫ l : ℝ, Real.exp (a * l - π * Real.exp l) = π ^ (-a) * Real.Gamma a := by
  have h1 : ENNReal.ofReal (∫ l : ℝ, Real.exp (a * l - π * Real.exp l))
      = ENNReal.ofReal (π ^ (-a) * Real.Gamma a) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_sub_pi_exp ha)
      (Filter.Eventually.of_forall (fun l => (Real.exp_pos _).le)),
      lintegral_exp_mul_sub_pi_exp ha]
  have h2 : (0:ℝ) ≤ ∫ l : ℝ, Real.exp (a * l - π * Real.exp l) :=
    integral_nonneg (fun l => (Real.exp_pos _).le)
  have h3 : (0:ℝ) ≤ π ^ (-a) * Real.Gamma a := by
    have := Real.Gamma_pos_of_pos ha
    positivity
  exact (ENNReal.ofReal_eq_ofReal_iff h2 h3).mp h1

open scoped Classical in
/-- The weighted row-sum of the Hecke substitution recovers the ray coordinate. -/
theorem sum_mult_heckeLogCLE (p : ℝ × logSpace K) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (heckeLogCLE K p) w = p.1 := by
  have happ : ∀ w : InfinitePlace K, (heckeLogCLE K p) w
      = p.1 / (Module.finrank ℚ K) + 2 * fullLog K p.2 w / mult w := fun w => rfl
  rw [Finset.sum_congr rfl (fun w _ => by rw [happ w])]
  have hterm : ∀ w : InfinitePlace K,
      (mult w : ℝ) * (p.1 / (Module.finrank ℚ K) + 2 * fullLog K p.2 w / mult w)
      = (mult w : ℝ) * p.1 / (Module.finrank ℚ K) + 2 * fullLog K p.2 w := by
    intro w
    have hm : (mult w : ℝ) ≠ 0 := by
      have := mult_pos (w := w)
      positivity
    field_simp
  rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_add_distrib]
  have h2 : ∑ w : InfinitePlace K, 2 * fullLog K p.2 w = 0 := by
    rw [← Finset.mul_sum, sum_fullLog, mul_zero]
  rw [h2, add_zero]
  have hsum : ∑ w : InfinitePlace K, (mult w : ℝ) * p.1 / (Module.finrank ℚ K)
      = (∑ w : InfinitePlace K, (mult w : ℝ)) * p.1 / (Module.finrank ℚ K) := by
    rw [Finset.sum_mul, Finset.sum_div]
  rw [hsum, show (∑ w : InfinitePlace K, (mult w : ℝ)) = (Module.finrank ℚ K : ℝ) by
    exact_mod_cast congrArg Nat.cast (sum_mult_eq (K := K))]
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  field_simp

open scoped Classical in
/-- **The universal Mellin constant in closed form**: the change of variables along the
Hecke substitution factorises the master integral into per-place Gamma integrals. -/
theorem lintegral_exp_heckeLog (σ : ℝ) (hσ : 0 < σ) :
    ∫⁻ p : ℝ × logSpace K, ENNReal.ofReal (Real.exp (σ * p.1
        - π * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K p) w)))
      = (heckeJacobian K : ℝ≥0∞) * ENNReal.ofReal (∏ w : InfinitePlace K,
          π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)) := by
  set G : (InfinitePlace K → ℝ) → ℝ≥0∞ := fun l =>
    ENNReal.ofReal (∏ w : InfinitePlace K,
      Real.exp ((mult w : ℝ) * σ * l w - π * Real.exp (l w))) with hG
  have hpt : ∀ p : ℝ × logSpace K,
      ENNReal.ofReal (Real.exp (σ * p.1
        - π * ∑ w : InfinitePlace K, Real.exp ((heckeLogCLE K p) w)))
        = G (heckeLogCLE K p) := by
    intro p
    rw [hG]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_mult_heckeLogCLE K p,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  simp_rw [hpt]
  have hGmeas : Measurable G := by
    rw [hG]
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_prod _ (fun w _ => ?_)
    refine Real.measurable_exp.comp ?_
    refine Measurable.sub ?_ ?_
    · exact (measurable_pi_apply w).const_mul _
    · exact (Real.measurable_exp.comp (measurable_pi_apply w)).const_mul _
  have hmap : ∫⁻ p : ℝ × logSpace K, G (heckeLogCLE K p)
      = (heckeJacobian K : ℝ≥0∞) * ∫⁻ l, G l := by
    rw [← lintegral_map hGmeas (heckeLogCLE K).continuous.measurable,
      map_heckeLogCLE_volume, lintegral_smul_measure]
    rfl
  rw [hmap]
  congr 1
  -- evaluate the product integral
  have hint : ∀ w : InfinitePlace K,
      Integrable (fun l : ℝ => Real.exp ((mult w : ℝ) * σ * l - π * Real.exp l)) := by
    intro w
    refine integrable_exp_mul_sub_pi_exp ?_
    have := mult_pos (w := w)
    positivity
  have hprod_int : Integrable (fun l : InfinitePlace K → ℝ =>
      ∏ w : InfinitePlace K, Real.exp ((mult w : ℝ) * σ * l w - π * Real.exp (l w))) := by
    exact MeasureTheory.Integrable.fintype_prod (f := fun w x =>
      Real.exp ((mult w : ℝ) * σ * x - π * Real.exp x)) hint
  rw [hG]
  rw [← ofReal_integral_eq_lintegral_ofReal hprod_int
    (Filter.Eventually.of_forall (fun l => Finset.prod_nonneg
      (fun w _ => (Real.exp_pos _).le)))]
  congr 1
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (f := fun w x =>
    Real.exp ((mult w : ℝ) * σ * x - π * Real.exp x))]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  refine integral_exp_mul_sub_pi_exp ?_
  have := mult_pos (w := w)
  positivity

end

end DedekindResidue
