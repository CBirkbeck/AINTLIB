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

end

end DedekindResidue
