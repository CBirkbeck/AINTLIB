import LeanModularForms.Issues.Issue55

open ModularForm UpperHalfPlane MatrixGroups ComplexConjugate CongruenceSubgroup Pointwise Subgroup
  Matrix.SpecialLinearGroup HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace HeckeRing.GL2

namespace Newform

/-- The coefficient field `ℚ(a_n : n ≥ 1)` of a newform. -/
noncomputable def coefficientField (f : Newform N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun n : ℕ+ ↦ (qExpansion 1 f.toCuspForm).coeff n)

/-- The coefficient field of a newform is finite-dimensional over `ℚ`. -/
theorem coefficientField_finiteDimensional (f : Newform N k) :
    FiniteDimensional ℚ f.coefficientField := by
  sorry

/-- The coefficient field of a newform is a number field. -/
instance (f : Newform N k) : NumberField f.coefficientField :=
  {to_finiteDimensional := coefficientField_finiteDimensional f}

lemma coeff_mem_coefficientField (f : Newform N k) (n : ℕ+) :
    (qExpansion 1 f.toCuspForm).coeff n ∈ f.coefficientField :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self n)

lemma isSelfDual_iff_qExpansion_one_coeff_im_eq_zero (f : Newform N k) :
    ModularFormClass.isSelfDual f.toCuspForm ↔
      ∀ n : ℕ, ((qExpansion 1 f.toCuspForm).coeff n).im = 0 := by
  simpa [CongruenceSubgroup.strictWidthInfty_Gamma1 N] using
    ModularFormClass.isSelfDual_iff f.toCuspForm

lemma qExpansion_one_coeff_im_eq_zero_of_coefficientField_isTotallyReal (f : Newform N k)
    (hK : NumberField.IsTotallyReal f.coefficientField) :
    ∀ n : ℕ, ((qExpansion 1 f.toCuspForm).coeff n).im = 0 := by
  intro n
  cases n with
  | zero => simp [CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos (one_mem_strictPeriods_Gamma1_map N)]
  | succ n =>
      let npos : ℕ+ := ⟨n + 1, n.succ_pos⟩
      simpa [npos] using Complex.conj_eq_iff_im.mp (RingHom.congr_fun
        (NumberField.IsTotallyReal.complexEmbedding_isReal (algebraMap f.coefficientField ℂ))
        ⟨(qExpansion 1 f.toCuspForm).coeff npos, coeff_mem_coefficientField f npos⟩)

/--
For every embedding σ : K_f ↪ ℂ, the coefficientwise conjugate
f^σ(q) = ∑ n ≥ 1, σ(a_n(f)) q^n
is again a normalized newform. Its dual has coefficients
a_n((f^σ)ᵛ) = overline(σ(a_n(f))).
Galois conjugation commutes with duality:
(f^σ)ᵛ = (fᵛ)^σ.
-/
theorem exists_selfDual_galoisConjugate_newform_of_isSelfDual (f : Newform N k)
    (hself : ModularFormClass.isSelfDual f.toCuspForm) (σ : f.coefficientField →+* ℂ) :
    ∃ g : Newform N k, ModularFormClass.isSelfDual g.toCuspForm ∧
      ∀ n : ℕ+, (qExpansion 1 g.toCuspForm).coeff n =
        σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_coefficientField f n⟩ := by
  sorry

lemma complexEmbedding_coeff_im_eq_zero_of_isSelfDual (f : Newform N k)
    (hself : ModularFormClass.isSelfDual f.toCuspForm) (σ : f.coefficientField →+* ℂ) (n : ℕ+) :
    (σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_coefficientField f n⟩).im = 0 := by
  obtain ⟨g, hgself, hgcoeff⟩ := exists_selfDual_galoisConjugate_newform_of_isSelfDual f hself σ
  rw [← hgcoeff n]
  exact (isSelfDual_iff_qExpansion_one_coeff_im_eq_zero g).mp hgself n

lemma coefficientField_isTotallyReal_of_forall_complexEmbedding_coeff_im_eq_zero
    (f : Newform N k) (hσ : ∀ (σ : f.coefficientField →+* ℂ) (n : ℕ+),
      (σ ⟨(qExpansion 1 f.toCuspForm).coeff n, coeff_mem_coefficientField f n⟩).im = 0) :
    NumberField.IsTotallyReal f.coefficientField := by
  unfold coefficientField at hσ ⊢
  refine ⟨fun v ↦ ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff]
  let σ := NumberField.InfinitePlace.embedding v
  rw [NumberField.ComplexEmbedding.isReal_iff]
  apply RingHom.equivRatAlgHom.injective
  apply IntermediateField.algHom_ext_of_eq_adjoin (F := ℚ) rfl
  rintro x ⟨n, rfl⟩
  change star (σ ⟨_, _⟩) = σ ⟨_, _⟩
  exact Complex.conj_eq_iff_im.mpr (hσ σ n)

/-- A newform's coefficient field is totally real if and only if the newform is self-dual. -/
theorem coefficientField_isTotallyReal_iff_isSelfDual (f : Newform N k) :
    NumberField.IsTotallyReal f.coefficientField ↔ ModularFormClass.isSelfDual f.toCuspForm :=
  ⟨fun hK ↦ (isSelfDual_iff_qExpansion_one_coeff_im_eq_zero f).mpr
    (qExpansion_one_coeff_im_eq_zero_of_coefficientField_isTotallyReal f hK),
    fun hself ↦ coefficientField_isTotallyReal_of_forall_complexEmbedding_coeff_im_eq_zero f
      (complexEmbedding_coeff_im_eq_zero_of_isSelfDual f hself)⟩

/-- A newform's coefficient field is CM if and only if the newform is not self-dual. -/
theorem coefficientField_isCM_iff_not_isSelfDual (f : Newform N k) :
    NumberField.IsCMField f.coefficientField ↔ ¬ ModularFormClass.isSelfDual f.toCuspForm := by
  sorry

end Newform

end HeckeRing.GL2
