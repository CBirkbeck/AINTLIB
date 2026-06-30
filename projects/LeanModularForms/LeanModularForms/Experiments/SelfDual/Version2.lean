import LeanModularForms.Experiments.SelfDual.Basic

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def ModularForm.isSelfDual' (f : ModularForm Γ k) : Prop :=
  ⇑(ModularForm.dual f) = ⇑f

theorem ModularForm.isSelfDual'_iff_apply (f : ModularForm Γ k) :
    ModularForm.isSelfDual' f ↔ ∀ z, ModularForm.dual f z = f z :=
  ⟨fun h z => congrFun h z, fun h => funext h⟩

@[simp]
theorem ModularForm.isSelfDual'_zero :
    ModularForm.isSelfDual' (0 : ModularForm Γ k) := by
  ext z
  simp

theorem ModularForm.isSelfDual'_add {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) (hg : ModularForm.isSelfDual' g) :
    ModularForm.isSelfDual' (f + g) := by
  ext z
  simpa [ModularForm.isSelfDual', ModularForm.dual_apply] using
    congrArg₂ HAdd.hAdd (congrFun hf z) (congrFun hg z)

theorem ModularForm.isSelfDual'_neg {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) :
    ModularForm.isSelfDual' (-f) := by
  ext z
  simpa [ModularForm.isSelfDual', ModularForm.dual_apply] using
    congrArg Neg.neg (congrFun hf z)

theorem ModularForm.isSelfDual'_sub {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) (hg : ModularForm.isSelfDual' g) :
    ModularForm.isSelfDual' (f - g) := by
  simpa [sub_eq_add_neg] using ModularForm.isSelfDual'_add hf (ModularForm.isSelfDual'_neg hg)

theorem ModularForm.isSelfDual'_smul_real (c : ℝ) {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) :
    ModularForm.isSelfDual' (c • f) := by
  ext z
  have hsigma : UpperHalfPlane.σ UpperHalfPlane.J (c : ℂ) = c :=
    UpperHalfPlane.σ_ofReal UpperHalfPlane.J c
  change (((c : ℂ) • ⇑f) ∣[k] UpperHalfPlane.J) z = (c : ℂ) * f z
  rw [smul_slash, hsigma]
  simpa [Pi.smul_apply, smul_eq_mul] using
    congrArg (fun x : ℂ => (c : ℂ) * x) (congrFun hf z)

theorem ModularForm.isSelfDual_iff' [Γ.IsSelfDual] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ModularForm.isSelfDual' f ↔
      ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
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
