/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Fricke

/-!
# The Fricke involution preserves the extended oldspace

This file proves Diamond–Shurman Prop 5.6.2 / Ex 5.6.3(e): the Fricke involution
`w_N` (`frickeOperatorCusp`) preserves the extended old subspace
`cuspFormsOldExtended N k` of `S_k(Γ₁(N))`.

The key geometric fact is that the Fricke involution **swaps the two degeneracy
directions** between a divisor `M ∣ N` and `N`.  Writing `d = N/M`, the matrix
identity `frickeGL N = frickeGL M * diag(d, 1)` (as `GL₂(ℚ)` elements) sends:

* a **level-raise** generator `levelRaise M d g'` (degeneracy `α_d = diag(d,1)`) to a
  scalar multiple of `levelInclude_cusp (w_M g')` (a **level-inclusion** generator);
* a **level-inclusion** generator `levelInclude_cusp g'` to a scalar multiple of
  `levelRaise M d (w_M g')` (a **level-raise** generator).

Both land in `cuspFormsOldExtended`, so the closure (`Submodule.span_induction`)
finishes the proof.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, Prop 5.6.2, Ex 5.6.3(e).
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

open Matrix

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The diagonal matrix `diag(d, 1) = [[d, 0], [0, 1]] ∈ GL₂(ℚ)` (determinant `d ≠ 0`).
This is the rational shadow of `levelRaiseMatrix d`. -/
private def diagQ (d : ℕ) [NeZero d] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, 1]
    (by rw [det_fin_two_of]; simpa using (Nat.cast_ne_zero (R := ℚ)).mpr (NeZero.ne d))

@[simp] private lemma diagQ_coe (d : ℕ) [NeZero d] :
    (↑(diagQ d) : Matrix (Fin 2) (Fin 2) ℚ) = !![(d : ℚ), 0; 0, 1] := rfl

/-- The scalar matrix `diag(d, d) = [[d, 0], [0, d]] ∈ GL₂(ℚ)` (determinant `d² ≠ 0`). -/
private def scalQ (d : ℕ) [NeZero d] : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(d : ℚ), 0; 0, (d : ℚ)]
    (by rw [det_fin_two_of]
        simpa using mul_ne_zero ((Nat.cast_ne_zero (R := ℚ)).mpr (NeZero.ne d))
          ((Nat.cast_ne_zero (R := ℚ)).mpr (NeZero.ne d)))

@[simp] private lemma scalQ_coe (d : ℕ) [NeZero d] :
    (↑(scalQ d) : Matrix (Fin 2) (Fin 2) ℚ) = !![(d : ℚ), 0; 0, (d : ℚ)] := rfl

/-- The determinant of `scalQ d` (over `ℚ`) is `d²`. -/
private lemma scalQ_det_val (d : ℕ) [NeZero d] : (scalQ d).det.val = (d : ℚ) ^ 2 := by
  rw [GeneralLinearGroup.val_det_apply, scalQ_coe, det_fin_two_of]; ring

/-- `glMap (diagQ d) = levelRaiseMatrix d`: the rational diagonal `diag(d,1)` maps to the
real level-raising matrix. -/
private lemma glMap_diagQ (d : ℕ) [NeZero d] :
    glMap (diagQ d) = levelRaiseMatrix d := by
  apply Units.ext
  ext i j
  rw [glMap_apply, diagQ_coe]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, GeneralLinearGroup.mkOfDetNeZero]

/-- **Include → raise matrix identity** (machine-verified): `frickeGL N = frickeGL M * diag(d, 1)`
as `GL₂(ℚ)` elements, for `d * M = N`.  Concretely
`[0,-1;M,0]·[d,0;0,1] = [0,-1;Md,0] = [0,-1;N,0]`. -/
private lemma frickeGL_eq_frickeGL_mul_diagQ {M : ℕ} [NeZero M] (d : ℕ) [NeZero d]
    (heq : d * M = N) :
    frickeGL N = frickeGL M * diagQ d := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_mul, frickeGL_coe, frickeGL_coe, diagQ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← heq, mul_comm]

/-- **Raise → include matrix identity** (machine-verified): `diag(d, 1) * frickeGL N =
frickeGL M * diag(d, d)` as `GL₂(ℚ)` elements, for `d * M = N`.  Concretely
`[d,0;0,1]·[0,-1;N,0] = [0,-d;N,0]` and `[0,-1;M,0]·[d,0;0,d] = [0,-d;Md,0] = [0,-d;N,0]`. -/
private lemma diagQ_mul_frickeGL {M : ℕ} [NeZero M] (d : ℕ) [NeZero d]
    (heq : d * M = N) :
    diagQ d * frickeGL N = frickeGL M * scalQ d := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, frickeGL_coe, frickeGL_coe,
    diagQ_coe, scalQ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← heq, mul_comm]

/-- `glMap (scalQ d)` has positive determinant `d² > 0`. -/
private lemma glMap_scalQ_det_pos (d : ℕ) [NeZero d] :
    0 < (glMap (scalQ d)).det.val :=
  glMap_det_pos_of_rat_det_pos _ (by
    rw [scalQ_det_val]
    have : (0 : ℚ) < (d : ℚ) := by exact_mod_cast NeZero.pos d
    positivity)

/-- **Scalar-matrix slash.** Slashing by the scalar matrix `diag(d, d)` is multiplication by
`d^{k-2}`: `h ∣[k] diag(d,d) = d^{k-2} • h`.  (From `|det| = d²`, `denom = d`, and `diag(d,d)`
acting trivially on `ℍ`.) -/
private lemma slash_scalQ (d : ℕ) [NeZero d] (h : UpperHalfPlane → ℂ) :
    h ∣[k] (scalQ d : GL (Fin 2) ℚ) = ((d : ℂ) ^ (k - 2)) • h := by
  ext z
  show (h ∣[k] glMap (scalQ d)) z = _
  rw [ModularForm.slash_apply, sigma_eq_id_of_pos_det (glMap_scalQ_det_pos d),
    ContinuousAlgEquiv.refl_apply]
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hsmul : (glMap (scalQ d)) • z = z := by
    refine (GL_smul_pos_eq hdpos (g := 1) (by simp) ?_ z).trans (one_smul _ z)
    rw [Units.val_one]
    ext i j
    rw [glMap_apply, scalQ_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply]
  have hdenom : UpperHalfPlane.denom (glMap (scalQ d)) z = (d : ℂ) := by
    show ((glMap (scalQ d)) 1 0 : ℂ) * (z : ℂ) + ((glMap (scalQ d)) 1 1 : ℂ) = _
    rw [glMap_apply (scalQ d) 1 0, glMap_apply (scalQ d) 1 1, scalQ_coe]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_natCast,
      map_zero, Matrix.of_apply]
    push_cast; ring
  have hdet : (↑|(glMap (scalQ d)).det.val| : ℂ) = (d : ℂ) ^ 2 := by
    have hdv : (glMap (scalQ d)).det.val = algebraMap ℚ ℝ (scalQ d : GL (Fin 2) ℚ).det.val :=
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _)
    rw [abs_of_pos (glMap_scalQ_det_pos d), hdv, scalQ_det_val]
    push_cast; ring
  rw [hsmul, hdenom, hdet, Pi.smul_apply, smul_eq_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [show ((d : ℂ) ^ 2) ^ (k - 1) = (d : ℂ) ^ (2 * (k - 1)) by
        rw [show ((d : ℂ) ^ 2) = (d : ℂ) ^ (2 : ℤ) by norm_cast, ← _root_.zpow_mul],
    mul_assoc, ← zpow_add₀ hd, mul_comm]
  congr 1
  ring

/-- **Fricke sends a level-RAISE generator to a level-INCLUSION generator (up to scalar).**
For `d * M = N`, `w_N (ι_d g') = d⁻¹ • (w_M g')` viewed at level `N` via `levelInclude_cusp`.
The Fricke factor `α_d = diag(d,1)` is swapped to the right of `frickeGL`, producing
`frickeGL M · diag(d,d)`; the scalar `diag(d,d)` slash contributes `d^{k-2}`, combining with the
`d^{1-k}` level-raise normalisation to `d⁻¹`. -/
private lemma frickeOperatorCusp_levelRaise {M : ℕ} [NeZero M] (d : ℕ) [NeZero d]
    (heq : d * M = N) (hMN : M ∣ N) (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    frickeOperatorCusp k (heq ▸ levelRaise M d k g') =
      ((d : ℂ)⁻¹) • levelInclude_cusp hMN k (frickeOperatorCusp (N := M) k g') := by
  subst heq
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdiag : (⇑g' : UpperHalfPlane → ℂ) ∣[k] levelRaiseMatrix d =
      ⇑g' ∣[k] (diagQ d : GL (Fin 2) ℚ) := by
    show ⇑g' ∣[k] levelRaiseMatrix d = ⇑g' ∣[k] glMap (diagQ d)
    rw [glMap_diagQ]
  have hscal : ((d : ℂ) ^ (1 - k)) * ((d : ℂ) ^ (k - 2)) = (d : ℂ)⁻¹ := by
    rw [← zpow_add₀ hd]; norm_num
  have key : (⇑(levelRaise M d k g') ∣[k] (frickeGL (d * M) : GL (Fin 2) ℚ)) =
      (d : ℂ)⁻¹ • (⇑g' ∣[k] (frickeGL M : GL (Fin 2) ℚ)) := by
    rw [coe_levelRaise, levelRaiseFun, smul_slash_pos_det k _ _ _ frickeGL_det_pos, hdiag,
      ← SlashAction.slash_mul, diagQ_mul_frickeGL d rfl, SlashAction.slash_mul, slash_scalQ,
      smul_smul, hscal]
  apply CuspForm.ext
  intro z
  rw [show (frickeOperatorCusp k ((rfl : d * M = d * M) ▸ (levelRaise M d k) g')) =
      frickeOperatorCusp k ((levelRaise M d k) g') from rfl]
  show (⇑(levelRaise M d k g') ∣[k] (frickeGL (d * M) : GL (Fin 2) ℚ)) z =
    ((d : ℂ)⁻¹ • levelInclude_cusp hMN k (frickeOperatorCusp (N := M) k g')) z
  rw [key]
  show ((d : ℂ)⁻¹ • (⇑g' ∣[k] (frickeGL M : GL (Fin 2) ℚ))) z =
    (d : ℂ)⁻¹ • ((levelInclude_cusp hMN k (frickeOperatorCusp (N := M) k g')) z)
  rfl

/-- **Fricke sends a level-INCLUSION generator to a level-RAISE generator (up to scalar).**
For `d * M = N`, `w_N (ι_M g') = d^{k-1} • ι_d (w_M g')` (a level-raise generator).  The Fricke
factor `α_d = diag(d,1)` appears to the right of `frickeGL M`, becoming the level-raise matrix;
the scalar `d^{k-1}` exactly cancels the `d^{1-k}` level-raise normalisation. -/
private lemma frickeOperatorCusp_levelInclude {M : ℕ} [NeZero M] (d : ℕ) [NeZero d]
    (heq : d * M = N) (hMN : M ∣ N) (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    frickeOperatorCusp k (levelInclude_cusp hMN k g') =
      ((d : ℂ) ^ (k - 1)) • (heq ▸ levelRaise M d k (frickeOperatorCusp (N := M) k g')) := by
  subst heq
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdiag : ∀ h : UpperHalfPlane → ℂ, h ∣[k] levelRaiseMatrix d =
      h ∣[k] (diagQ d : GL (Fin 2) ℚ) := fun h ↦ by
    show h ∣[k] levelRaiseMatrix d = h ∣[k] glMap (diagQ d)
    rw [glMap_diagQ]
  have hscal : ((d : ℂ) ^ (k - 1)) * ((d : ℂ) ^ (1 - k)) = 1 := by
    rw [← zpow_add₀ hd]; norm_num
  have hwM : (⇑(frickeOperatorCusp (N := M) k g') : UpperHalfPlane → ℂ) =
      ⇑g' ∣[k] (frickeGL M : GL (Fin 2) ℚ) := frickeOperatorCusp_coe k g'
  have key : (⇑(levelInclude_cusp hMN k g') ∣[k] (frickeGL (d * M) : GL (Fin 2) ℚ)) =
      ((d : ℂ) ^ (k - 1)) • ⇑((levelRaise M d k) (frickeOperatorCusp (N := M) k g')) := by
    rw [coe_levelRaise, levelRaiseFun, smul_smul, hscal, one_smul, hwM, hdiag,
      ← SlashAction.slash_mul, levelInclude_cusp_coe, ← frickeGL_eq_frickeGL_mul_diagQ d rfl]
  apply CuspForm.ext
  intro z
  show (⇑(levelInclude_cusp hMN k g') ∣[k] (frickeGL (d * M) : GL (Fin 2) ℚ)) z =
    (((d : ℂ) ^ (k - 1)) • ((rfl : d * M = d * M) ▸
      (levelRaise M d k) (frickeOperatorCusp (N := M) k g'))) z
  rw [key]
  show (((d : ℂ) ^ (k - 1)) • ⇑((levelRaise M d k) (frickeOperatorCusp (N := M) k g'))) z =
    ((d : ℂ) ^ (k - 1)) • (((levelRaise M d k) (frickeOperatorCusp (N := M) k g')) z)
  rfl

/-- **Diamond–Shurman Prop 5.6.2 / Ex 5.6.3(e).** The Fricke involution `w_N`
(`frickeOperatorCusp`) preserves the extended oldspace `cuspFormsOldExtended N k`.

Proved by `Submodule.span_induction`: the Fricke involution swaps the two kinds of generator
(level-raise ↔ level-inclusion), each landing back in the span up to a nonzero scalar
(`frickeOperatorCusp_levelRaise`, `frickeOperatorCusp_levelInclude`); closure under `+`, `•`,
`0` is `LinearMap.map_add` / `map_smul` / `map_zero`. -/
theorem frickeOperatorCusp_mem_cuspFormsOldExtended
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOldExtended N k) :
    frickeOperatorCusp k g ∈ cuspFormsOldExtended N k := by
  refine Submodule.span_induction
    (p := fun x _ ↦ frickeOperatorCusp k x ∈ cuspFormsOldExtended N k)
    ?_ ?_ ?_ ?_ hg
  · rintro f (⟨M, d, _, _, hd, heq, g', rfl⟩ | ⟨M, _, hMN, hMltN, g', rfl⟩)
    · -- level-RAISE generator → level-INCLUSION generator (up to scalar)
      have hMN : M ∣ N := ⟨d, by rw [← heq]; ring⟩
      have hMltN : M < N := by
        rw [← heq]; exact lt_mul_left (Nat.pos_of_neZero M) hd
      rw [frickeOperatorCusp_levelRaise d heq hMN g']
      exact Submodule.smul_mem _ _
        (levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _)
    · -- level-INCLUSION generator → level-RAISE generator (up to scalar)
      obtain ⟨d, hd⟩ := id hMN
      have hNpos : 0 < N := Nat.pos_of_neZero N
      haveI : NeZero d := ⟨by rintro rfl; simp [hd] at hNpos⟩
      have heq : d * M = N := by rw [hd]; ring
      have hd1 : 1 < d := by
        rcases Nat.lt_or_ge 1 d with h | h
        · exact h
        · rw [le_antisymm h (Nat.pos_of_neZero d), one_mul] at heq
          omega
      rw [frickeOperatorCusp_levelInclude d heq hMN g']
      refine Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ?_))
      exact ⟨M, d, inferInstance, inferInstance, hd1, heq, frickeOperatorCusp (N := M) k g', rfl⟩
  · rw [map_zero]; exact (cuspFormsOldExtended N k).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]; exact (cuspFormsOldExtended N k).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]; exact (cuspFormsOldExtended N k).smul_mem c hx

end HeckeRing.GL2
