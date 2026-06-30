import LeanModularForms.Issues.SelfDual.Basic

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def ModularForm.isSelfDual [Γ.IsSelfDual] (f : ModularForm Γ k) : Prop :=
  (‹Γ.IsSelfDual›.self_dual ▸ ModularForm.dual f) = f

theorem ModularForm.isSelfDual_iff_coe_dual_eq [Γ.IsSelfDual] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔ ⇑(ModularForm.dual f) = ⇑f := by
  constructor
  · intro h
    calc
      ⇑(ModularForm.dual f) =
          ⇑(‹Γ.IsSelfDual›.self_dual ▸ ModularForm.dual f : ModularForm Γ k) := by
        rw [ModularForm.coe_cast_group]
      _ = ⇑f := by rw [h]
  · intro h
    apply ModularForm.ext
    intro z
    rw [ModularForm.coe_cast_group]
    exact congrFun h z

theorem ModularForm.isSelfDual_iff_apply [Γ.IsSelfDual] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔ ∀ z, ModularForm.dual f z = f z := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq]
  exact ⟨fun h z => congrFun h z, fun h => funext h⟩

@[simp]
theorem ModularForm.isSelfDual_zero [Γ.IsSelfDual] :
    ModularForm.isSelfDual (0 : ModularForm Γ k) := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq]
  ext z
  simp

theorem ModularForm.isSelfDual_add [Γ.IsSelfDual] {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) (hg : ModularForm.isSelfDual g) :
    ModularForm.isSelfDual (f + g) := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq] at hf hg ⊢
  ext z
  simpa [ModularForm.dual_apply] using congrArg₂ HAdd.hAdd (congrFun hf z) (congrFun hg z)

theorem ModularForm.isSelfDual_neg [Γ.IsSelfDual] {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) :
    ModularForm.isSelfDual (-f) := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq] at hf ⊢
  ext z
  simpa [ModularForm.dual_apply] using congrArg Neg.neg (congrFun hf z)

theorem ModularForm.isSelfDual_sub [Γ.IsSelfDual] {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) (hg : ModularForm.isSelfDual g) :
    ModularForm.isSelfDual (f - g) := by
  simpa [sub_eq_add_neg] using ModularForm.isSelfDual_add hf (ModularForm.isSelfDual_neg hg)

theorem ModularForm.isSelfDual_smul_real [Γ.IsSelfDual] (c : ℝ) {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) :
    ModularForm.isSelfDual (c • f) := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq] at hf ⊢
  ext z
  have hsigma : UpperHalfPlane.σ UpperHalfPlane.J (c : ℂ) = c :=
    UpperHalfPlane.σ_ofReal UpperHalfPlane.J c
  change (((c : ℂ) • ⇑f) ∣[k] UpperHalfPlane.J) z = (c : ℂ) * f z
  rw [smul_slash, hsigma]
  simpa [Pi.smul_apply, smul_eq_mul] using
    congrArg (fun x : ℂ => (c : ℂ) * x) (congrFun hf z)

theorem ModularForm.isSelfDual_iff [Γ.IsSelfDual] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔
      ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
  rw [ModularForm.isSelfDual_iff_coe_dual_eq]
  let h := Γ.strictWidthInfty
  have hh : 0 < h := by simpa [h] using Subgroup.strictWidthInfty_pos Γ
  have hΓ : h ∈ Γ.strictPeriods := by
    simpa [h] using Subgroup.strictWidthInfty_mem_strictPeriods Γ
  constructor
  · intro hfd n
    have hq : (UpperHalfPlane.qExpansion h (ModularForm.dual f)).coeff n =
        (UpperHalfPlane.qExpansion h f).coeff n := by
      rw [hfd]
    have hstar : (starRingEnd ℂ) ((UpperHalfPlane.qExpansion h f).coeff n) =
        (UpperHalfPlane.qExpansion h f).coeff n := by
      rw [← ModularForm.qExpansion_dual_coeff f n, hq]
    simpa [h] using (Complex.conj_eq_iff_im.mp hstar)
  · intro hcoeff
    let fd : ModularForm Γ k := (Subgroup.IsSelfDual.self_dual (Γ := Γ) ▸ ModularForm.dual f)
    have hfd_coe : ⇑fd = ⇑(ModularForm.dual f) := by
      dsimp [fd]
      rw [ModularForm.coe_cast_group]
    have hq : UpperHalfPlane.qExpansion h fd = UpperHalfPlane.qExpansion h f := by
      apply PowerSeries.ext
      intro n
      rw [show (UpperHalfPlane.qExpansion h fd).coeff n =
          (UpperHalfPlane.qExpansion h (ModularForm.dual f)).coeff n by rw [hfd_coe]]
      rw [ModularForm.qExpansion_dual_coeff f n]
      exact Complex.conj_eq_iff_im.mpr (by simpa [h] using hcoeff n)
    have hzero_q : UpperHalfPlane.qExpansion h (fd - f) = 0 := by
      rw [show UpperHalfPlane.qExpansion h (fd - f) =
          UpperHalfPlane.qExpansion h (⇑fd - ⇑f : UpperHalfPlane → ℂ) by rfl]
      rw [ModularForm.qExpansion_sub hh hΓ fd f]
      simp [hq]
    have hzero_form : fd - f = 0 :=
      (ModularForm.qExpansion_eq_zero_iff hh hΓ (fd - f)).mp hzero_q
    have hfd_eq : fd = f := sub_eq_zero.mp hzero_form
    calc
      ⇑(ModularForm.dual f) = ⇑fd := hfd_coe.symm
      _ = ⇑f := by rw [hfd_eq]
