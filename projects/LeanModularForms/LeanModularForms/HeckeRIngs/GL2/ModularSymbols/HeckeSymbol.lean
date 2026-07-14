/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleM
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n

/-!
# The integer Hecke and diamond operators on `𝕄 N k`

This file defines the Hecke operators `T_n` (and `U_p` for `p ∣ N`) and the diamond operators
`⟨d⟩` as `ℤ`-linear endomorphisms of the integral modular-symbol module `𝕄 N k`.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups TensorProduct
open Representation MvPolynomial Matrix.SpecialLinearGroup HeckeRing.GL2

/-! ## The single-matrix Heilbronn action on `Div0 ℤ ⊗ SymPow ℤ m` -/

/-- The cast of an integer matrix into `ℚ`. -/
noncomputable abbrev qMat (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℚ :=
  M.map (Int.castRingHom ℚ)

theorem qMat_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) :
    (qMat M).det ≠ 0 := by
  rw [qMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Int.coe_castRingHom,
    Ne, Int.cast_eq_zero]
  exact hM

theorem qMat_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) : qMat (M * M') = qMat M * qMat M' := by
  rw [qMat, qMat, qMat, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, map_mul]

/-- An integer matrix with nonzero determinant, viewed as an element of `GL(2, ℚ)`. -/
noncomputable def heilbronnGL (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (qMat M) (qMat_det_ne_zero hM)

@[simp]
theorem heilbronnGL_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    (heilbronnGL M hM : Matrix (Fin 2) (Fin 2) ℚ) = qMat M := rfl

/-- `heilbronnGL` is multiplicative on integer matrices with nonzero determinant. -/
theorem heilbronnGL_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hMM' : (M * M').det ≠ 0) :
    heilbronnGL (M * M') hMM' = heilbronnGL M hM * heilbronnGL M' hM' := by
  apply Units.ext
  show qMat (M * M') = qMat M * qMat M'
  exact qMat_mul M M'

/-- The Heilbronn action on the augmentation-kernel `Div0 ℤ`: the integer matrix `M` (with nonzero
determinant) acts on cusps `ℙ¹(ℚ)` via the `GL(2, ℚ)`-action, and this permutation preserves the
augmentation, hence `Div0 ℤ`. -/
noncomputable def divAct (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : Div0 ℤ →ₗ[ℤ] Div0 ℤ :=
  LinearMap.restrict
    (MonoidAlgebra.mapDomainLinearMap ℤ ℤ ((heilbronnGL M hM) • ·)) <| by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_mapDomainLinearMap,
      Finsupp.linearCombination_mapDomain] at hx ⊢
    rw [show ((fun _ => (1 : ℤ)) ∘ ((heilbronnGL M hM) • ·)) = (fun _ => (1 : ℤ)) from rfl]
    exact hx

@[simp]
theorem divAct_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (D : Div0 ℤ) :
    ((divAct M hM D : Div0 ℤ) : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff
      = Finsupp.mapDomain ((heilbronnGL M hM) • ·)
          (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff :=
  rfl

/-- The Heilbronn action on `SymPow ℤ m`: the integer matrix `M` acts by the linear substitution
attached to its adjugate, `Xᵢ ↦ ∑ⱼ (adj M)ᵢⱼ Xⱼ`.  Using the adjugate (rather than `M` itself)
makes `M ↦ symAct M` a *covariant* monoid action agreeing with `symRep` on `SL(2, ℤ)`. -/
noncomputable def symAct (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) : SymPow ℤ m →ₗ[ℤ] SymPow ℤ m :=
  LinearMap.restrict (substAlgHom (Matrix.adjugate M)).toLinearMap <| by
    intro x hx
    exact substAlgHom_isHomogeneous (Matrix.adjugate M) hx

@[simp]
theorem symAct_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (P : SymPow ℤ m) :
    ((symAct M m P : SymPow ℤ m) : MvPolynomial (Fin 2) ℤ)
      = substAlgHom (Matrix.adjugate M) (P : MvPolynomial (Fin 2) ℤ) :=
  rfl

/-- The combined Heilbronn action of an integer matrix `M` (nonzero determinant) on
`Div0 ℤ ⊗[ℤ] SymPow ℤ m`. -/
noncomputable def actMat (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (m : ℕ) :
    (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] (Div0 ℤ ⊗[ℤ] SymPow ℤ m) :=
  TensorProduct.map (divAct M hM) (symAct M m)

@[simp]
theorem actMat_tmul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (m : ℕ)
    (D : Div0 ℤ) (P : SymPow ℤ m) :
    actMat M hM m (D ⊗ₜ P) = (divAct M hM D) ⊗ₜ (symAct M m P) :=
  rfl

/-! ## Composition law: `actMat` is a covariant action -/

theorem det_mul_ne_zero {M M' : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) :
    (M * M').det ≠ 0 := by
  rw [Matrix.det_mul]; exact mul_ne_zero hM hM'

/-- `divAct` composes covariantly: `divAct (M * M') = divAct M ∘ divAct M'`. -/
theorem divAct_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) :
    divAct (M * M') (det_mul_ne_zero hM hM') = (divAct M hM).comp (divAct M' hM') := by
  refine LinearMap.ext fun D => Subtype.ext (MonoidAlgebra.coeff_injective ?_)
  rw [LinearMap.comp_apply, divAct_coe, divAct_coe, divAct_coe, ← Finsupp.mapDomain_comp]
  congr 1
  funext y
  rw [Function.comp_apply, ← mul_smul, ← heilbronnGL_mul M M' hM hM']

/-- `symAct` composes covariantly: `symAct (M * M') = symAct M ∘ symAct M'`. -/
theorem symAct_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) :
    symAct (M * M') m = (symAct M m).comp (symAct M' m) := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  rw [LinearMap.comp_apply, symAct_coe, symAct_coe, symAct_coe, Matrix.adjugate_mul_distrib,
    ← AlgHom.comp_apply, substAlgHom_comp]

/-- The combined Heilbronn action is a covariant monoid action:
`actMat (M * M') = actMat M ∘ actMat M'`. -/
theorem actMat_mul (M M' : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (m : ℕ) :
    actMat (M * M') (det_mul_ne_zero hM hM') m = (actMat M hM m).comp (actMat M' hM' m) := by
  rw [actMat, actMat, actMat, divAct_mul M M' hM hM', symAct_mul M M' m]
  exact TensorProduct.map_comp _ _ _ _

/-! ## Compatibility with `fullModSymRep` on `SL(2, ℤ)` -/

/-- The determinant of (the integer matrix of) an `SL(2, ℤ)` element is `1 ≠ 0`. -/
theorem sl_det_ne_zero (g : SL(2, ℤ)) : (g : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  rw [show (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 from g.prop]; exact one_ne_zero

/-- On `SL(2, ℤ)`, the symmetric-power Heilbronn action agrees with `symRep`: the adjugate of an
`SL(2, ℤ)` matrix is its inverse, which is exactly the matrix used by `symRep`. -/
theorem symAct_eq_symRep (g : SL(2, ℤ)) (m : ℕ) :
    symAct (g : Matrix (Fin 2) (Fin 2) ℤ) m = symRep ℤ m g := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  rw [symAct_coe]
  show substAlgHom (Matrix.adjugate (g : Matrix (Fin 2) (Fin 2) ℤ)) (P : MvPolynomial (Fin 2) ℤ)
    = substAlgHom (symMat ℤ g) (P : MvPolynomial (Fin 2) ℤ)
  congr 2

/-- On `SL(2, ℤ)`, the `GL(2, ℚ)`-action on cusps used by `divAct` agrees with the
`SL(2, ℚ)`-action used by `div0Rep`: both send `[v] ↦ [g · v]` for the same rational matrix. -/
theorem heilbronnGL_smul_eq_sl_smul (g : SL(2, ℤ)) (y : Projectivization ℚ (Fin 2 → ℚ)) :
    (heilbronnGL (g : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero g)) • y
      = (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • y :=
  rfl

/-- On `SL(2, ℤ)`, the divisor Heilbronn action agrees with `div0Rep`. -/
theorem divAct_eq_div0Rep (g : SL(2, ℤ)) :
    divAct (g : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero g) = div0Rep ℤ g := by
  refine LinearMap.ext fun D => Subtype.ext (MonoidAlgebra.coeff_injective ?_)
  rw [divAct_coe, div0Rep_apply]
  rfl

/-- **Key compatibility (i).** On `SL(2, ℤ)`, the combined Heilbronn action `actMat` agrees with
the diagonal tensor representation `fullModSymRep`. -/
theorem actMat_eq_fullModSymRep (g : SL(2, ℤ)) (m : ℕ) :
    actMat (g : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero g) m = fullModSymRep ℤ m g := by
  rw [actMat, divAct_eq_div0Rep, symAct_eq_symRep]
  rfl

open CongruenceSubgroup

variable {N : ℕ}

/-! ## Upper-triangular coset matrices and the integer coset identity -/

/-- The integer upper-triangular coset matrix `[[1, b], [0, p]]` (the integer version of
`T_p_upper`). -/
noncomputable def upperMat (p b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b : ℤ); 0, (p : ℤ)]

@[simp]
theorem upperMat_det (p b : ℕ) : (upperMat p b).det = p := by
  simp [upperMat, Matrix.det_fin_two_of]

theorem upperMat_det_ne_zero {p : ℕ} (hp : 0 < p) (b : ℕ) : (upperMat p b).det ≠ 0 := by
  rw [upperMat_det]; exact_mod_cast hp.ne'

/-- The Heilbronn `GL(2, ℚ)` element of `upperMat p b` is exactly `T_p_upper p hp b`. -/
theorem heilbronnGL_upperMat {p : ℕ} (hp : 0 < p) (b : ℕ) :
    heilbronnGL (upperMat p b) (upperMat_det_ne_zero hp b) = T_p_upper p hp b := by
  apply Units.ext
  show qMat (upperMat p b) = (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ)
  rw [T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat, upperMat]

/-- The **integer coset identity** (the matrix form of Shimura's well-definedness, derived from
`moebius_conj`).  For `σ ∈ SL(2, ℤ)` and `b : Fin p` with `σ₀₀ + b·σ₁₀ ≢ 0 (mod p)`, there is
`τ ∈ SL(2, ℤ)` with `upperMat p b · σ = τ · upperMat p j` (where `j = moebiusFin' p hp σ b`), and
explicit entries witnessing membership in `Γ₁(N)` / `Γ₀(N)`. -/
theorem upperMat_mul_sl {p : ℕ} [Fact p.Prime] (hp : Nat.Prime p) (σ : SL(2, ℤ)) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ∃ τ : SL(2, ℤ),
      upperMat p b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ)
        = (τ : Matrix (Fin 2) (Fin 2) ℤ)
          * upperMat p (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ↑p * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
          ↑(moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val := by
  obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := moebius_conj hp σ b hA
  refine ⟨τ, ?_, hτ00, hτ10, hτ11⟩
  -- transfer the GL(2, ℚ) identity to an integer matrix identity via injectivity of casting
  have hcast : qMat (upperMat p b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ))
      = qMat ((τ : Matrix (Fin 2) (Fin 2) ℤ)
          * upperMat p (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val) := by
    rw [qMat_mul, qMat_mul]
    have e1 : qMat (upperMat p b.val) = (T_p_upper p hp.pos b.val : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [← heilbronnGL_upperMat hp.pos b.val]; rfl
    have e2 : qMat (upperMat p (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val)
        = (T_p_upper p hp.pos (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val :
            Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [← heilbronnGL_upperMat hp.pos]; rfl
    have e3 : qMat (σ : Matrix (Fin 2) (Fin 2) ℤ) = (mapGL ℚ σ : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [mapGL_coe_matrix]; rfl
    have e4 : qMat (τ : Matrix (Fin 2) (Fin 2) ℤ) = (mapGL ℚ τ : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [mapGL_coe_matrix]; rfl
    rw [e1, e2, e3, e4]
    have := congr_arg (Units.val) hmat
    simpa only [Units.val_mul] using this
  have hinj : Function.Injective (qMat) := fun A B hAB => by
    ext i j
    have := congr_fun (congr_fun (congr_arg (fun M => M) hAB) i) j
    simpa [qMat, Matrix.map_apply] using this
  exact hinj hcast

/-- `actMat` depends only on the matrix, not on the proof of nonzero determinant. -/
theorem actMat_congr {M M' : Matrix (Fin 2) (Fin 2) ℤ} (h : M = M')
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (m : ℕ) :
    actMat M hM m = actMat M' hM' m := by
  subst h; rfl

/-- Algebraic core of the coset descent: if `upperMat p b · σ = τ · upperMat p b'` as integer
matrices, then `actMat (upperMat p b) ∘ fullModSymRep σ` applied to `x` equals
`fullModSymRep τ` applied to `actMat (upperMat p b') x`.  Pure consequence of the multiplicativity
of `actMat` and its agreement with `fullModSymRep` on `SL(2, ℤ)`. -/
theorem actMat_upperMat_comp_fullModSymRep {p : ℕ} (hp : 0 < p) (m : ℕ)
    (σ τ : SL(2, ℤ)) (b b' : ℕ)
    (hmat : upperMat p b * (σ : Matrix (Fin 2) (Fin 2) ℤ)
      = (τ : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p b')
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    actMat (upperMat p b) (upperMat_det_ne_zero hp b) m (fullModSymRep ℤ m σ x)
      = fullModSymRep ℤ m τ (actMat (upperMat p b') (upperMat_det_ne_zero hp b') m x) :=
  calc actMat (upperMat p b) (upperMat_det_ne_zero hp b) m (fullModSymRep ℤ m σ x)
      = actMat (upperMat p b) (upperMat_det_ne_zero hp b) m
          (actMat (σ : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero σ) m x) :=
        congr_arg (actMat (upperMat p b) (upperMat_det_ne_zero hp b) m)
          (LinearMap.congr_fun (actMat_eq_fullModSymRep σ m).symm x)
    _ = actMat (upperMat p b * (σ : Matrix (Fin 2) (Fin 2) ℤ))
          (det_mul_ne_zero (upperMat_det_ne_zero hp b) (sl_det_ne_zero σ)) m x :=
        (LinearMap.congr_fun (actMat_mul (upperMat p b) (σ : Matrix (Fin 2) (Fin 2) ℤ)
          (upperMat_det_ne_zero hp b) (sl_det_ne_zero σ) m) x).symm
    _ = actMat ((τ : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p b')
          (det_mul_ne_zero (sl_det_ne_zero τ) (upperMat_det_ne_zero hp b')) m x :=
        LinearMap.congr_fun (actMat_congr hmat _ _ m) x
    _ = actMat (τ : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero τ) m
          (actMat (upperMat p b') (upperMat_det_ne_zero hp b') m x) :=
        LinearMap.congr_fun (actMat_mul (τ : Matrix (Fin 2) (Fin 2) ℤ) (upperMat p b')
          (sl_det_ne_zero τ) (upperMat_det_ne_zero hp b') m) x
    _ = fullModSymRep ℤ m τ (actMat (upperMat p b') (upperMat_det_ne_zero hp b') m x) :=
        LinearMap.congr_fun (actMat_eq_fullModSymRep τ m)
          (actMat (upperMat p b') (upperMat_det_ne_zero hp b') m x)

/-- `𝕄.mk` absorbs the `fullModSymRep`-action of a `Γ₁(N)` element. -/
theorem mk_fullModSymRep_gamma1 [NeZero N] (k : ℤ) (τ : SL(2, ℤ)) (hτ : τ ∈ Gamma1 N)
    (y : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat τ y) = 𝕄.mk N k y :=
  Representation.Coinvariants.mk_self_apply (modSymRep N (k - 2).toNat) ⟨τ, hτ⟩ y

/-- The `𝕄.mk`-level coset descent for one upper-triangular representative: under the integer coset
identity with `τ ∈ Γ₁(N)`, the class is reindexed `b ↦ b'`. -/
theorem mk_actMat_upperMat_comp_fullModSymRep [NeZero N] {p : ℕ} (hp : 0 < p) (k : ℤ)
    (σ τ : SL(2, ℤ)) (hτ : τ ∈ Gamma1 N) (b b' : ℕ)
    (hmat : upperMat p b * (σ : Matrix (Fin 2) (Fin 2) ℤ)
      = (τ : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p b')
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (actMat (upperMat p b) (upperMat_det_ne_zero hp b) (k - 2).toNat
        (fullModSymRep ℤ (k - 2).toNat σ x))
      = 𝕄.mk N k (actMat (upperMat p b') (upperMat_det_ne_zero hp b') (k - 2).toNat x) := by
  rw [actMat_upperMat_comp_fullModSymRep hp (k - 2).toNat σ τ b b' hmat x]
  exact mk_fullModSymRep_gamma1 k τ hτ _

/-- Generic algebraic coset descent: if `A · σ = τ · B` with `det A, det B ≠ 0`, then
`actMat A ∘ fullModSymRep σ` and `fullModSymRep τ ∘ actMat B` agree on `x`. -/
theorem actMat_comp_fullModSymRep {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) (m : ℕ) (σ τ : SL(2, ℤ))
    (hmat : A * (σ : Matrix (Fin 2) (Fin 2) ℤ) = (τ : Matrix (Fin 2) (Fin 2) ℤ) * B)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    actMat A hA m (fullModSymRep ℤ m σ x) = fullModSymRep ℤ m τ (actMat B hB m x) :=
  calc actMat A hA m (fullModSymRep ℤ m σ x)
      = actMat A hA m (actMat (σ : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero σ) m x) :=
        congr_arg (actMat A hA m) (LinearMap.congr_fun (actMat_eq_fullModSymRep σ m).symm x)
    _ = actMat (A * (σ : Matrix (Fin 2) (Fin 2) ℤ))
          (det_mul_ne_zero hA (sl_det_ne_zero σ)) m x :=
        (LinearMap.congr_fun (actMat_mul A (σ : Matrix (Fin 2) (Fin 2) ℤ) hA
          (sl_det_ne_zero σ) m) x).symm
    _ = actMat ((τ : Matrix (Fin 2) (Fin 2) ℤ) * B)
          (det_mul_ne_zero (sl_det_ne_zero τ) hB) m x :=
        LinearMap.congr_fun (actMat_congr hmat _ _ m) x
    _ = actMat (τ : Matrix (Fin 2) (Fin 2) ℤ) (sl_det_ne_zero τ) m (actMat B hB m x) :=
        LinearMap.congr_fun (actMat_mul (τ : Matrix (Fin 2) (Fin 2) ℤ) B (sl_det_ne_zero τ) hB m) x
    _ = fullModSymRep ℤ m τ (actMat B hB m x) :=
        LinearMap.congr_fun (actMat_eq_fullModSymRep τ m) (actMat B hB m x)

/-- Generic `mk`-level coset descent: if `A · σ = τ · B` with `τ ∈ Γ₁(N)`, the coinvariant class
`mk (actMat A (ρ_σ x))` equals `mk (actMat B x)`. -/
theorem mk_actMat_coset [NeZero N] {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) (k : ℤ) (σ τ : SL(2, ℤ)) (hτ : τ ∈ Gamma1 N)
    (hmat : A * (σ : Matrix (Fin 2) (Fin 2) ℤ) = (τ : Matrix (Fin 2) (Fin 2) ℤ) * B)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (actMat A hA (k - 2).toNat (fullModSymRep ℤ (k - 2).toNat σ x))
      = 𝕄.mk N k (actMat B hB (k - 2).toNat x) := by
  rw [actMat_comp_fullModSymRep hA hB (k - 2).toNat σ τ hmat x]
  exact mk_fullModSymRep_gamma1 k τ hτ _

/-! ## The `U_p` operator at `p ∣ N` (upper-triangular sum) -/

/-- The upper-triangular sum operator `Σ_{b<p} actMat (upperMat p b)` on `Div0 ℤ ⊗ SymPow ℤ m`.
This is `U_p` when `p ∣ N` and the upper part of `T_p` when `p ∤ N`. -/
noncomputable def upperOp (p : ℕ) (hp : 0 < p) (m : ℕ) :
    (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] (Div0 ℤ ⊗[ℤ] SymPow ℤ m) :=
  ∑ b ∈ Finset.range p, actMat (upperMat p b) (upperMat_det_ne_zero hp b) m

theorem upperOp_apply (p : ℕ) (hp : 0 < p) (m : ℕ) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    upperOp p hp m x =
      ∑ b ∈ Finset.range p, actMat (upperMat p b) (upperMat_det_ne_zero hp b) m x := by
  rw [upperOp, LinearMap.coe_sum, Finset.sum_apply]

/-- For `σ ∈ Γ₁(N)` and `p ∣ N`, every value `σ₀₀ + b·σ₁₀` is coprime to `p` (`σ₀₀ ≡ 1`,
`σ₁₀ ≡ 0 mod p`). -/
theorem not_dvd_gamma1_divN {p : ℕ} (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) (b : ℕ) :
    ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑b * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd_N : (p : ℤ) ∣ (N : ℤ) := by
    rw [Int.natCast_dvd_natCast]; by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  have hp_dvd_σ10 : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    hp_dvd_N.trans <| by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hσ_g1.2.2
  have hσ00_mod_p : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod p) = 1 := by
    have hp_dvd : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1) := hp_dvd_N.trans <| by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hσ_g1.1]; ring
    rw [← sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1) p).mpr hp_dvd
    push_cast at this ⊢; exact this
  intro hdvd
  have : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑b * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) :
      ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have h10 : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
  rw [show (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑b * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) :
    ZMod p) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod p)
      + ((b : ℤ) : ZMod p) * (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p) by
    push_cast; ring, h10, mul_zero, add_zero, hσ00_mod_p] at this
  exact one_ne_zero this

/-- The conjugating element `τ` from `upperMat_mul_sl` lies in `Γ₁(N)` when `σ ∈ Γ₁(N)`. -/
theorem upperMat_mul_sl_tau_mem_gamma1 {p : ℕ}
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) {τ : SL(2, ℤ)} {j₀ j₁ : ℕ}
    (hτ00 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑j₀ * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hτ10 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ↑p * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hτ11 : (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * ↑j₁) :
    τ ∈ Gamma1 N := by
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · rw [hτ00]; push_cast; rw [hσ_g1.2.2, mul_zero, add_zero]; exact hσ_g1.1
  · rw [hτ11]; push_cast; rw [hσ_g1.2.2, zero_mul, sub_zero]; exact hσ_g1.2.1
  · rw [hτ10]; push_cast; rw [hσ_g1.2.2, mul_zero]

/-- The bijection on `Fin p` reindexing the coset representatives, from `moebiusFin'`. -/
theorem moebiusFin'_bijective_of_gamma1 {p : ℕ} (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) : Function.Bijective (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ)) :=
  Finite.injective_iff_bijective.mp
    (moebiusFin'_injective p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) (by exact_mod_cast σ.prop))

/-- **`U_p` descent (`p ∣ N`).** For `σ ∈ Γ₁(N)`, the upper-triangular sum operator commutes with
`𝕄.mk ∘ modSymRep σ`: the coset representatives are permuted (up to a left `Γ₁(N)`-factor) under
right multiplication by `σ`, so the coinvariant class of the sum is unchanged. -/
theorem mk_upperOp_comp_modSymRep_divN [NeZero N] {p : ℕ} (hp : Nat.Prime p)
    (hpN : ¬Nat.Coprime p N) (k : ℤ) (s : ↥(Gamma1 N)) :
    ((𝕄.mk N k).comp (upperOp p hp.pos (k - 2).toNat)).comp (modSymRep N (k - 2).toNat s)
      = (𝕄.mk N k).comp (upperOp p hp.pos (k - 2).toNat) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  show 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat
      (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x))
    = 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat x)
  rw [upperOp_apply, upperOp_apply, map_sum, map_sum, ← Fin.sum_univ_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_equiv (Equiv.ofBijective _ (moebiusFin'_bijective_of_gamma1 hp s))
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun b _ => ?_)
  rw [Equiv.ofBijective_apply]
  obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := upperMat_mul_sl hp (s : SL(2, ℤ)) b
    (not_dvd_gamma1_divN hp hpN (s : SL(2, ℤ)) s.property b.val)
  exact (mk_actMat_upperMat_comp_fullModSymRep hp.pos k (s : SL(2, ℤ)) τ
    (upperMat_mul_sl_tau_mem_gamma1 (s : SL(2, ℤ)) s.property hτ00 hτ10 hτ11)
    b.val (moebiusFin' p hp ((s : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b).val hmat x)

/-- **`U_p` at `p ∣ N`** on `𝕄 N k`: the descent of the upper-triangular sum operator to
`Γ₁(N)`-coinvariants. -/
noncomputable def upperSymb [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (k : ℤ) : 𝕄 N k →ₗ[ℤ] 𝕄 N k :=
  Representation.Coinvariants.lift (modSymRep N (k - 2).toNat)
    ((𝕄.mk N k).comp (upperOp p hp.pos (k - 2).toNat))
    (mk_upperOp_comp_modSymRep_divN hp hpN k)

@[simp]
theorem upperSymb_mk [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    upperSymb hp hpN k (𝕄.mk N k x) = 𝕄.mk N k (upperOp p hp.pos (k - 2).toNat x) :=
  rfl

/-! ## The lower-triangular coset matrix -/

/-- The integer lower/diagonal coset matrix `[[p, 0], [0, 1]]` (the integer version of
`T_p_lower`). -/
noncomputable def lowerMat (p : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), 0; 0, 1]

@[simp]
theorem lowerMat_det (p : ℕ) : (lowerMat p).det = p := by
  simp [lowerMat, Matrix.det_fin_two_of]

theorem lowerMat_det_ne_zero {p : ℕ} (hp : 0 < p) : (lowerMat p).det ≠ 0 := by
  rw [lowerMat_det]; exact_mod_cast hp.ne'

/-- The Heilbronn `GL(2, ℚ)` element of `lowerMat p` is exactly `T_p_lower p hp`. -/
theorem heilbronnGL_lowerMat {p : ℕ} (hp : 0 < p) :
    heilbronnGL (lowerMat p) (lowerMat_det_ne_zero hp) = T_p_lower p hp := by
  apply Units.ext
  show qMat (lowerMat p) = (T_p_lower p hp : Matrix (Fin 2) (Fin 2) ℚ)
  rw [T_p_lower_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat, lowerMat]

/-! ## The `T_p` operator at `p ∤ N` (upper sum + diamond-twisted lower term)

For `p ∤ N` the double coset `Γ₁(N) \ Γ₁(N) diag(1,p) Γ₁(N)` has `p + 1` representatives: the `p`
upper matrices `[[1,b],[0,p]]` and one "lower" representative which, reduced to `Γ₁(N)`-cosets,
acquires a diamond twist `⟨p⟩`.  We take the `(p+1)`-th Heilbronn matrix to be `γ_p · lowerMat`
where `γ_p ∈ Γ₀(N)` is the diamond representative for `⟨p⟩` (chosen as in `diamondSymb`). -/

/-- The chosen `Γ₀(N)` representative for the diamond `⟨p⟩` at `p ∤ N`. -/
noncomputable def diamondRep {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) : ↥(Gamma0 N) :=
  (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose

theorem diamondRep_spec {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) :
    Gamma0MapUnits (diamondRep (N := N) hpN) = ZMod.unitOfCoprime p hpN :=
  (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose_spec

/-- The integer matrix of the diamond representative `γ_p`. -/
noncomputable def diamondMat {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  ((diamondRep (N := N) hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

theorem diamondMat_det {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) :
    (diamondMat (N := N) hpN).det = 1 := by
  rw [diamondMat]; exact_mod_cast (diamondRep (N := N) hpN : SL(2, ℤ)).prop

/-- The `(p+1)`-th Heilbronn coset matrix at `p ∤ N`: the diamond representative times `lowerMat`,
of determinant `p`. -/
noncomputable def lowerDiamondMat {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  diamondMat (N := N) hpN * lowerMat p

theorem lowerDiamondMat_det {p : ℕ} [NeZero N] (hpN : Nat.Coprime p N) :
    (lowerDiamondMat (N := N) hpN).det = p := by
  rw [lowerDiamondMat, Matrix.det_mul, diamondMat_det, one_mul, lowerMat_det]

theorem lowerDiamondMat_det_ne_zero {p : ℕ} [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (lowerDiamondMat (N := N) hpN).det ≠ 0 := by
  rw [lowerDiamondMat_det]; exact_mod_cast hp.ne'

/-- The `T_p` operator on `Div0 ℤ ⊗ SymPow ℤ m` at `p ∤ N`: the upper-triangular sum plus the
diamond-twisted lower term. -/
noncomputable def tpOp {p : ℕ} [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (m : ℕ) :
    (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] (Div0 ℤ ⊗[ℤ] SymPow ℤ m) :=
  upperOp p hp m + actMat (lowerDiamondMat (N := N) hpN) (lowerDiamondMat_det_ne_zero hp hpN) m

/-! ### Arithmetic lemmas for the `p ∤ N` coset combinatorics (ported, no analytic content) -/

/-- If `p ∣ M₁₀` and `det M = 1`, then `M₀₀ + b·M₁₀` is never divisible by `p`. -/
theorem hb_not_dvd_topLeft_add_of_dvd_botLeft {p : ℕ} (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (h10 : (p : ℤ) ∣ M 1 0) (b : ℤ) : ¬(p : ℤ) ∣ (M 0 0 + b * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have h10' : ((M 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at this; rwa [h10', mul_zero, add_zero] at this
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  push_cast at hd; rw [h00, h10', zero_mul, mul_zero, sub_zero] at hd
  exact zero_ne_one hd

/-- Determinant-one witness for the upper→lower conjugating matrix. -/
theorem hb_upper_div_tau_det {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (a b : ℤ)
    (ha : M 0 0 + b * M 1 0 = a * ↑p) :
    (!![a, M 0 1 + b * M 1 1; M 1 0, ↑p * M 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]; linear_combination -M 1 1 * ha + hdet

/-- Determinant-one witness for the lower→upper conjugating matrix. -/
theorem hb_lower_tau_det {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (j' q : ℤ)
    (hq : M 1 1 - M 1 0 * j' = ↑p * q) :
    (!![↑p * M 0 0, M 0 1 - M 0 0 * j'; M 1 0, q] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]; linear_combination -M 0 0 * hq + hdet

/-- `p ∣ num - den · (num/den mod p)` when `den ≢ 0 mod p`. -/
theorem hb_dvd_sub_mul_inv_val {p : ℕ} [Fact p.Prime] [NeZero p]
    (num den : ℤ) (hden : (den : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (num - den * ↑((num : ZMod p) * (den : ZMod p)⁻¹).val) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero, mul_comm (num : ZMod p) _, ← mul_assoc,
    mul_inv_cancel₀ hden, one_mul]

/-- The canonical index `b₀` (when `M₁₀ ≢ 0 mod p`): the unique `b` with `p ∣ M₀₀ + b·M₁₀`. -/
theorem hb_dvd_topLeft_add_canonicalIndex {p : ℕ} (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (M 0 0 + ↑((-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val) * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  have : (-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹) * ((M 1 0 : ℤ) : ZMod p) =
      -(M 0 0 : ZMod p) := by
    rw [mul_assoc, inv_mul_cancel₀ h10_ne, mul_one]
  rw [this, add_neg_cancel]

/-- When `M₁₀ ≢ 0 mod p`, the divisibility `p ∣ M₀₀ + i·M₁₀` pins `i` to the canonical index. -/
theorem hb_dvd_topLeft_add_iff_eq_canonicalIndex {p : ℕ} (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (b₀ : Fin p)
    (hb₀ : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0)) (i : Fin p) :
    (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) ↔ i = b₀ := by
  refine ⟨fun hdvd => moebiusFin'_injective p hp M hdet ?_, fun h => h ▸ hb₀⟩
  simp only [moebiusFin',
    show ((M 0 0 + ↑i.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd,
    show ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, ↓reduceIte]

/-- Swap/permute lemma for summing the `p + 1` cosets: when exactly the index `b₀` is special, the
sum of `(if special then L else g (φ i))` plus `g (φ b₀)` equals `Σ g + L`. -/
theorem hb_sum_ite_swap_eq {p : ℕ} {V : Type*} [AddCommGroup V]
    (g : Fin p → V) (L : V) (φ : Fin p → Fin p) (hφ : Function.Bijective φ)
    (b₀ : Fin p) (P : Fin p → Prop) [DecidablePred P] (hP : ∀ i, P i ↔ i = b₀) :
    (∑ x, if P x then L else g (φ x)) + g (φ b₀) = (∑ x, g x) + L := by
  have h_ite_eq : ∀ i : Fin p, (if P i then L else g (φ i)) =
      g (φ i) + if i = b₀ then L - g (φ b₀) else 0 := by
    intro i; simp only [hP]; split_ifs with h1
    · subst h1; abel
    · rw [add_zero]
  simp_rw [h_ite_eq, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ => L - g (φ b₀)), if_pos (Finset.mem_univ _)]
  have h_bij_sum : ∑ x : Fin p, g (φ x) = ∑ x, g x :=
    Finset.sum_equiv (Equiv.ofBijective _ hφ)
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun _ _ => rfl)
  rw [h_bij_sum]; abel

/-- Membership in `Γ₁(N)` from triviality of `Gamma0MapUnits`. -/
theorem mem_gamma1_of_gamma0MapUnits_one (g : ↥(Gamma0 N)) (hg : Gamma0MapUnits g = 1) :
    (g : SL(2, ℤ)) ∈ Gamma1 N :=
  (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <| congr_arg Units.val hg

/-! ### `p ∤ N` coset identities: the `p + 1` Heilbronn matrices permute mod `Γ₁(N)` -/

/-- **Lower → upper (case `p ∤ σ₁₀`).** For `σ ∈ Γ₁(N)`, `p ∤ N`, the diamond-twisted lower
representative maps under right multiplication by `σ` to an upper representative `upper(j')`, up to
a left `Γ₁(N)`-factor. -/
theorem lowerDiamondMat_mul_sl {p : ℕ} [NeZero N] [Fact p.Prime] (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10 : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 N ∧
      lowerDiamondMat (N := N) hpN * (σ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p
            ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p)
              * (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p)⁻¹).val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := σ.prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_g0 : σ ∈ Gamma0 N := Gamma1_in_Gamma0 N hσ
  have hσ_mem0 := (Gamma0_mem (N := N)).mp hσ_g0
  have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 :=
    fun h => hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set j' := (((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val with hj'
  obtain ⟨q, hq⟩ := hb_dvd_sub_mul_inv_val (M 1 1) (M 1 0) h10_ne
  rw [← hj'] at hq
  -- τ_low (from orbit_lower_gamma0), in Γ₀(N)
  set τl : Matrix (Fin 2) (Fin 2) ℤ := !![↑p * M 0 0, M 0 1 - M 0 0 * ↑j'; M 1 0, q] with hτl
  set τ : SL(2, ℤ) := ⟨τl, hb_lower_tau_det hdet p (↑j') q hq⟩ with hτ
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ_mem0
  -- γ' := γ_p * τ ∈ Γ₁(N)
  refine ⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * τ, ?_, ?_⟩
  · -- Gamma0MapUnits (γ_p * τ) = 1
    have hprod_g0 : ((diamondRep (N := N) hpN : SL(2, ℤ)) * τ) ∈ Gamma0 N :=
      (Gamma0 N).mul_mem (diamondRep (N := N) hpN).property hτ_g0
    refine mem_gamma1_of_gamma0MapUnits_one ⟨_, hprod_g0⟩ ?_
    have hσ_g1 := (Gamma1_mem N σ).mp hσ
    have hτ_unit : Gamma0MapUnits ⟨τ, hτ_g0⟩ = (ZMod.unitOfCoprime p hpN)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]; ext
      simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
        ZMod.coe_unitOfCoprime, Units.val_mul, Units.val_one]
      show ((q : ℤ) : ZMod N) * ((p : ℕ) : ZMod N) = 1
      rw [mul_comm, ← Int.cast_natCast (R := ZMod N), ← Int.cast_mul, ← hq]
      push_cast; rw [hσ_mem0, zero_mul, sub_zero]; exact hσ_g1.2.1
    have : Gamma0MapUnits (⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * τ, hprod_g0⟩ : ↥(Gamma0 N))
        = Gamma0MapUnits (diamondRep (N := N) hpN) * Gamma0MapUnits ⟨τ, hτ_g0⟩ := by
      rw [← map_mul]; rfl
    rw [this, diamondRep_spec, hτ_unit, mul_inv_cancel]
  · -- the matrix identity lowerDiamondMat * M = (γ_p * τ) * upper(j')
    show lowerDiamondMat (N := N) hpN * M
      = (((diamondRep (N := N) hpN : SL(2, ℤ)) * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * upperMat p j'
    rw [lowerDiamondMat, Matrix.SpecialLinearGroup.coe_mul]
    rw [mul_assoc, mul_assoc]
    congr 1
    -- lowerMat * M = τl * upper(j')   (the core lower→upper identity)
    show lowerMat p * M = (τ : Matrix (Fin 2) (Fin 2) ℤ) * upperMat p j'
    rw [hτ]
    show lowerMat p * M = τl * upperMat p j'
    have hM11 : M 1 1 = M 1 0 * (j' : ℤ) + q * ↑p := by linarith [hq]
    have e00 : (lowerMat p * M) 0 0 = (τl * upperMat p j') 0 0 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e01 : (lowerMat p * M) 0 1 = (τl * upperMat p j') 0 1 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e10 : (lowerMat p * M) 1 0 = (τl * upperMat p j') 1 0 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]; ring
    have e11 : (lowerMat p * M) 1 1 = (τl * upperMat p j') 1 1 := by
      simp only [hτl, lowerMat, upperMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]
      rw [hM11]; ring
    ext i j; fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11

/-- **Upper → lower (case `p ∤ σ₁₀`, special index `b₀`).** For `σ ∈ Γ₁(N)`, `p ∤ N`, if
`p ∣ σ₀₀ + b₀·σ₁₀` then `upper(b₀)·σ` maps to the diamond-twisted lower representative, up to a
left `Γ₁(N)`-factor. -/
theorem upperMat_mul_sl_to_lower {p : ℕ} [NeZero N] [Fact p.Prime] (_hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) (b₀ : ℕ)
    (hb₀ : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀ * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 N ∧
      upperMat p b₀ * (σ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN := by
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := σ.prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_g0 : σ ∈ Gamma0 N := Gamma1_in_Gamma0 N hσ
  have hσ_mem0 := (Gamma0_mem (N := N)).mp hσ_g0
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  obtain ⟨a, ha⟩ := hb₀
  have ha' : M 0 0 + ↑b₀ * M 1 0 = a * ↑p := by rw [ha, mul_comm]
  -- τ_up (from slash_upper_div_eq_under_gamma1), in Γ₀(N)
  set τu : Matrix (Fin 2) (Fin 2) ℤ := !![a, M 0 1 + ↑b₀ * M 1 1; M 1 0, ↑p * M 1 1] with hτu
  set τ : SL(2, ℤ) := ⟨τu, hb_upper_div_tau_det hdet p a ↑b₀ ha'⟩ with hτ
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((M 1 0 : ℤ) : ZMod N) = 0; exact hσ_mem0
  -- γ' := τ * γ_p⁻¹ ∈ Γ₁(N)
  refine ⟨τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, ?_, ?_⟩
  · -- Gamma0MapUnits (τ * γ_p⁻¹) = 1
    have hinv_g0 : ((diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
      (Gamma0 N).inv_mem (diamondRep (N := N) hpN).property
    have hprod_g0 : (τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) ∈ Gamma0 N :=
      (Gamma0 N).mul_mem hτ_g0 hinv_g0
    refine mem_gamma1_of_gamma0MapUnits_one ⟨_, hprod_g0⟩ ?_
    have hτ_unit : Gamma0MapUnits ⟨τ, hτ_g0⟩ = ZMod.unitOfCoprime p hpN := by
      ext
      simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
        ZMod.coe_unitOfCoprime]
      show ((↑p * M 1 1 : ℤ) : ZMod N) = ((p : ℕ) : ZMod N)
      push_cast; rw [hσ_g1.2.1, mul_one]
    have hsplit : Gamma0MapUnits (⟨τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hprod_g0⟩ :
          ↥(Gamma0 N))
        = Gamma0MapUnits ⟨τ, hτ_g0⟩ * Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹,
            hinv_g0⟩ := by
      rw [← map_mul]; rfl
    have hinv_unit : Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hinv_g0⟩
        = (ZMod.unitOfCoprime p hpN)⁻¹ := by
      have : Gamma0MapUnits ⟨(diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, hinv_g0⟩
          = (Gamma0MapUnits (diamondRep (N := N) hpN))⁻¹ := by
        rw [← map_inv]; rfl
      rw [this, diamondRep_spec]
    rw [hsplit, hτ_unit, hinv_unit, mul_inv_cancel]
  · -- matrix identity: upper(b₀) * M = (τ * γ_p⁻¹) * lowerDiamondMat
    have hM00 : M 0 0 + ↑b₀ * M 1 0 = a * ↑p := ha'
    have htriv : (τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) *
        (diamondRep (N := N) hpN : SL(2, ℤ)) = τ := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hcoe : ((τ * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN
        = (τ : Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      rw [lowerDiamondMat, diamondMat, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, htriv]
    rw [hcoe]
    -- now: upper(b₀) * M = τ.coe * lowerMat = τu * lowerMat
    show upperMat p b₀ * M = τu * lowerMat p
    have e00 : (upperMat p b₀ * M) 0 0 = (τu * lowerMat p) 0 0 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
      linear_combination hM00
    have e01 : (upperMat p b₀ * M) 0 1 = (τu * lowerMat p) 0 1 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    have e10 : (upperMat p b₀ * M) 1 0 = (τu * lowerMat p) 1 0 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    have e11 : (upperMat p b₀ * M) 1 1 = (τu * lowerMat p) 1 1 := by
      simp only [hτu, upperMat, lowerMat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]; ring
    ext i j; fin_cases i <;> fin_cases j
    · exact e00
    · exact e01
    · exact e10
    · exact e11

/-- **Lower → lower (case `p ∣ σ₁₀`).** For `σ ∈ Γ₁(N)`, `p ∤ N`, if `p ∣ σ₁₀` then the
diamond-twisted lower representative is fixed (up to a left `Γ₁(N)`-factor) by right multiplication
by `σ`. -/
theorem lowerDiamondMat_mul_sl_fixed {p : ℕ} [NeZero N] (_hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10 : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 N ∧
      lowerDiamondMat (N := N) hpN * (σ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * lowerDiamondMat (N := N) hpN := by
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := σ.prop; rw [Matrix.det_fin_two] at this; exact this
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  obtain ⟨c, hc⟩ := hσ10  -- M 1 0 = p * c
  -- τ := !![M00, p·M01; c, M11], so lower·M = τ·lower; det = 1
  set τl : Matrix (Fin 2) (Fin 2) ℤ := !![M 0 0, ↑p * M 0 1; c, M 1 1] with hτl
  have hτl_det : τl.det = 1 := by
    rw [hτl, Matrix.det_fin_two_of]
    have hh : M 1 0 = ↑p * c := hc
    linear_combination hdet + M 0 1 * hh
  set τ : SL(2, ℤ) := ⟨τl, hτl_det⟩ with hτ
  -- τ ∈ Γ₁(N): need N ∣ c (= M10/p), from N ∣ M10, p ∤ N
  have hτ_g1 : τ ∈ Gamma1 N := by
    rw [Gamma1_mem]
    have hM10N : (N : ℤ) ∣ M 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hσ_g1.2.2
    have hcN : (N : ℤ) ∣ c := by
      have hpN' : IsCoprime (p : ℤ) (N : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hpN
      have : (N : ℤ) ∣ ↑p * c := hc ▸ hM10N
      exact (IsCoprime.dvd_of_dvd_mul_left hpN'.symm this)
    refine ⟨?_, ?_, ?_⟩
    · show ((τl 0 0 : ℤ) : ZMod N) = 1
      simp only [hτl, Matrix.cons_val_zero, Matrix.of_apply]; exact hσ_g1.1
    · show ((τl 1 1 : ℤ) : ZMod N) = 1
      simp only [hτl, Matrix.cons_val_one, Matrix.of_apply]
      exact hσ_g1.2.1
    · show ((τl 1 0 : ℤ) : ZMod N) = 0
      simp only [hτl, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcN
  -- γ' := γ_p * τ * γ_p⁻¹ ∈ Γ₁(N) by normality
  refine ⟨(diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
      * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹, ?_, ?_⟩
  · exact Gamma0_normalizes_Gamma1 (diamondRep (N := N) hpN) τ hτ_g1
  · -- lowerDiamond * M = γ' * lowerDiamond
    have hlowerτ : lowerMat p * M = (τ : Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      have e00 : (lowerMat p * M) 0 0 = (τl * lowerMat p) 0 0 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      have e01 : (lowerMat p * M) 0 1 = (τl * lowerMat p) 0 1 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      have e10 : (lowerMat p * M) 1 0 = (τl * lowerMat p) 1 0 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]
        rw [hc]; ring
      have e11 : (lowerMat p * M) 1 1 = (τl * lowerMat p) 1 1 := by
        simp only [hτl, lowerMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.of_apply]; ring
      ext i j; fin_cases i <;> fin_cases j
      · exact e00
      · exact e01
      · exact e10
      · exact e11
    -- assemble: γ_p·lower·M = γ_p·τ·lower = (γ_p·τ·γ_p⁻¹)·(γ_p·lower)
    have hcancel : ((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
          * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹) * (diamondRep (N := N) hpN : SL(2, ℤ))
        = (diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ)) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hrhs : (((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ))
          * (diamondRep (N := N) hpN : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * lowerDiamondMat (N := N) hpN
        = (((diamondRep (N := N) hpN : SL(2, ℤ)) * (τ : SL(2, ℤ)) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) * lowerMat p := by
      rw [lowerDiamondMat, diamondMat, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, hcancel]
    rw [show lowerDiamondMat (N := N) hpN * M
        = ((diamondRep (N := N) hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * (lowerMat p * M) by rw [lowerDiamondMat, diamondMat, mul_assoc], hlowerτ, hrhs,
      Matrix.SpecialLinearGroup.coe_mul, mul_assoc]

/-! ### Assembling the `T_p` (`p ∤ N`) descent -/

/-- Abbreviation for `mk (actMat (upper b) x)`, the `b`-th upper coinvariant class. -/
private noncomputable def upperClass [NeZero N] {p : ℕ} (hp : 0 < p) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) (b : Fin p) : 𝕄 N k :=
  𝕄.mk N k (actMat (upperMat p b.val) (upperMat_det_ne_zero hp b.val) (k - 2).toNat x)

/-- The `𝕄.mk` of `tpOp` expands as the sum of the upper classes plus the lower-diamond class. -/
theorem mk_tpOp_eq [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat x)
      = (∑ b : Fin p, upperClass hp.pos k x b)
        + 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
            (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat x) := by
  rw [tpOp, LinearMap.add_apply, map_add, upperOp_apply, map_sum, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- **`T_p` descent (`p ∤ N`).** For `σ ∈ Γ₁(N)`, the `T_p` operator (upper sum + diamond-twisted
lower) commutes with `𝕄.mk ∘ modSymRep σ`: the `p + 1` coset representatives are permuted (up to a
left `Γ₁(N)`-factor) under right multiplication by `σ`. -/
theorem mk_tpOp_comp_modSymRep [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (k : ℤ) (s : ↥(Gamma1 N)) :
    ((𝕄.mk N k).comp (tpOp hp.pos hpN (k - 2).toNat)).comp (modSymRep N (k - 2).toNat s)
      = (𝕄.mk N k).comp (tpOp hp.pos hpN (k - 2).toNat) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := ((s : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by exact_mod_cast (s : SL(2, ℤ)).prop
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  show 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat
      (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x))
    = 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat x)
  rw [mk_tpOp_eq hp hpN, mk_tpOp_eq hp hpN]
  -- the lower-diamond class on the left, after applying ρ_s
  set Lσ := 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
      (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
      (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x)) with hLσ
  set L := 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
      (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat x) with hL
  by_cases hσ10 : (p : ℤ) ∣ M 1 0
  · -- case 1: p ∣ σ₁₀ — uppers permute among themselves, lower fixed
    have hbij : Function.Bijective (moebiusFin' p hp M) := moebiusFin'_bijective_of_gamma1 hp _
    have hLeq : Lσ = L := by
      obtain ⟨γ', hγ', hmat⟩ := lowerDiamondMat_mul_sl_fixed hp hpN (s : SL(2, ℤ)) s.property hσ10
      rw [hLσ, hL]
      exact mk_actMat_coset _ _ k (s : SL(2, ℤ)) γ' hγ' hmat x
    rw [hLeq]
    congr 1
    -- the upper sum: Σ upperClass after ρ_s = Σ upperClass, via the moebius bijection
    refine Finset.sum_equiv (Equiv.ofBijective _ hbij)
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun b _ => ?_)
    rw [Equiv.ofBijective_apply]
    have hdet2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact hdet_M
    obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := upperMat_mul_sl hp (s : SL(2, ℤ)) b
      (hb_not_dvd_topLeft_add_of_dvd_botLeft hp M hdet2 hσ10 _)
    exact mk_actMat_upperMat_comp_fullModSymRep hp.pos k (s : SL(2, ℤ)) τ
      (upperMat_mul_sl_tau_mem_gamma1 (s : SL(2, ℤ)) s.property hτ00 hτ10 hτ11)
      b.val (moebiusFin' p hp M b).val hmat x
  · -- case 2: p ∤ σ₁₀ — the special index b₀ swaps with the lower term
    have hdet2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact hdet_M
    have h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0 :=
      fun h => hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val, ZMod.val_lt _⟩
      with hb₀_def
    have hb₀ : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) :=
      hb_dvd_topLeft_add_canonicalIndex hp M h10_ne
    have hbij : Function.Bijective (moebiusFin' p hp M) := moebiusFin'_bijective_of_gamma1 hp _
    -- lower → upper(moebius b₀) : Lσ = upperClass(moebius b₀)
    have hmoeb_b₀ : (moebiusFin' p hp M b₀).val
        = (((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val := by
      simp only [moebiusFin', if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀)]
    have hLσ_eq : Lσ = upperClass hp.pos k x (moebiusFin' p hp M b₀) := by
      obtain ⟨γL, hγL, hmatL⟩ := lowerDiamondMat_mul_sl hp hpN (s : SL(2, ℤ)) s.property hσ10
      rw [hLσ]
      show 𝕄.mk N k (actMat (lowerDiamondMat (N := N) hpN)
          (lowerDiamondMat_det_ne_zero hp.pos hpN) (k - 2).toNat
          (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x))
        = 𝕄.mk N k (actMat (upperMat p (moebiusFin' p hp M b₀).val)
            (upperMat_det_ne_zero hp.pos _) (k - 2).toNat x)
      rw [hmoeb_b₀]
      exact mk_actMat_coset _ _ k (s : SL(2, ℤ)) γL hγL hmatL x
    -- per-term: upperClass'(b) = if b = b₀ then L else upperClass(moebius b)
    have hper : ∀ b : Fin p,
        upperClass hp.pos k (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x) b
        = if b = b₀ then L else upperClass hp.pos k x (moebiusFin' p hp M b) := by
      intro b
      show 𝕄.mk N k (actMat (upperMat p b.val) (upperMat_det_ne_zero hp.pos b.val) (k - 2).toNat
          (fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ)) x)) = _
      split_ifs with hbb
      · -- b = b₀ : upper(b₀) → lowerDiamond
        rw [hbb, hL]
        obtain ⟨γ', hγ', hmat⟩ :=
          upperMat_mul_sl_to_lower hp hpN (s : SL(2, ℤ)) s.property b₀.val hb₀
        exact mk_actMat_coset _ _ k (s : SL(2, ℤ)) γ' hγ' hmat x
      · -- b ≠ b₀ : upper(b) → upper(moebius b)
        have hA : ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) := by
          rw [hb_dvd_topLeft_add_iff_eq_canonicalIndex hp M hdet_M b₀ hb₀]; exact hbb
        obtain ⟨τ, hmat, hτ00, hτ10, hτ11⟩ := upperMat_mul_sl hp (s : SL(2, ℤ)) b hA
        exact mk_actMat_upperMat_comp_fullModSymRep hp.pos k (s : SL(2, ℤ)) τ
          (upperMat_mul_sl_tau_mem_gamma1 (s : SL(2, ℤ)) s.property hτ00 hτ10 hτ11)
          b.val (moebiusFin' p hp M b).val hmat x
    -- assemble via sum_ite_swap_eq
    rw [hLσ_eq]
    simp_rw [hper]
    exact hb_sum_ite_swap_eq (upperClass hp.pos k x) L (moebiusFin' p hp M) hbij b₀
      (P := fun b => b = b₀) (fun _ => Iff.rfl)

/-- **`T_p` at `p ∤ N`** on `𝕄 N k`: the descent of the upper-sum-plus-diamond-lower operator to
`Γ₁(N)`-coinvariants. -/
noncomputable def tpSymb [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (k : ℤ) : 𝕄 N k →ₗ[ℤ] 𝕄 N k :=
  Representation.Coinvariants.lift (modSymRep N (k - 2).toNat)
    ((𝕄.mk N k).comp (tpOp hp.pos hpN (k - 2).toNat))
    (mk_tpOp_comp_modSymRep hp hpN k)

@[simp]
theorem tpSymb_mk [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (k : ℤ)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    tpSymb hp hpN k (𝕄.mk N k x) = 𝕄.mk N k (tpOp hp.pos hpN (k - 2).toNat x) :=
  rfl

/-! ## The diamond operator `⟨d⟩` -/

/-- Applying `𝕄.mk` after the `fullModSymRep`-action of a `Γ₀(N)` element kills the relations of
`Γ₁(N)`-coinvariants: for `s ∈ Γ₁(N)`, conjugating by the `Γ₀(N)` element lands back in `Γ₁(N)`
(normality), so the coinvariant class is unchanged.  This is the well-definedness of `⟨d⟩` on
`𝕄 N k`. -/
theorem mk_fullModSymRep_gamma0_comp_modSymRep [NeZero N] (k : ℤ) (γ : ↥(Gamma0 N))
    (s : ↥(Gamma1 N)) :
    ((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))).comp
        (modSymRep N (k - 2).toNat s)
      = (𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))) := by
  refine LinearMap.ext fun x => ?_
  have hconj : (γ : SL(2, ℤ)) * (s : SL(2, ℤ))
      = ((γ : SL(2, ℤ)) * (s : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹) * (γ : SL(2, ℤ)) :=
    (inv_mul_cancel_right ((γ : SL(2, ℤ)) * (s : SL(2, ℤ))) (γ : SL(2, ℤ))).symm
  show 𝕄.mk N k ((fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)))
      ((fullModSymRep ℤ (k - 2).toNat (s : SL(2, ℤ))) x))
    = 𝕄.mk N k ((fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))) x)
  rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
  exact Representation.Coinvariants.mk_self_apply (modSymRep N (k - 2).toNat)
    ⟨_, Gamma0_normalizes_Gamma1 γ (s : SL(2, ℤ)) s.property⟩ _

/-- The descent to `Γ₁(N)`-coinvariants of the `fullModSymRep`-action of a `Γ₀(N)` element. -/
noncomputable def diamondSymbAux [NeZero N] (k : ℤ) (γ : ↥(Gamma0 N)) : 𝕄 N k →ₗ[ℤ] 𝕄 N k :=
  Representation.Coinvariants.lift (modSymRep N (k - 2).toNat)
    ((𝕄.mk N k).comp (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ))))
    (mk_fullModSymRep_gamma0_comp_modSymRep k γ)

@[simp]
theorem diamondSymbAux_mk [NeZero N] (k : ℤ) (γ : ↥(Gamma0 N))
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    diamondSymbAux k γ (𝕄.mk N k x)
      = 𝕄.mk N k (fullModSymRep ℤ (k - 2).toNat (γ : SL(2, ℤ)) x) :=
  rfl

/-- The diamond operator `⟨d⟩` on `𝕄 N k` as a `ℤ`-linear endomorphism.  It is the descent to
`Γ₁(N)`-coinvariants of the `fullModSymRep`-action of a `Γ₀(N)` representative `γ_d` with
`Gamma0MapUnits γ_d = d` (the same representative chosen by `diamondOp`/`diamondOpCusp`,
namely `(Gamma0MapUnits_surjective d).choose`). -/
noncomputable def diamondSymb (N : ℕ) [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) : 𝕄 N k →ₗ[ℤ] 𝕄 N k :=
  diamondSymbAux k (Gamma0MapUnits_surjective d).choose

/-! ## Assembling `T_n` from the prime-power components -/

/-- `T_p` on `𝕄 N k` for **all** primes: `tpSymb` (= the upper sum + diamond-lower) when `(p,N)=1`,
and `upperSymb` (= `U_p`, the upper sum only) when `p ∣ N`.  Mirrors
`HeckeRing.GL2.heckeT_p_all`. -/
noncomputable def heckeSymb_p_all (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    Module.End ℤ (𝕄 N k) :=
  if hpN : Nat.Coprime p N then tpSymb hp hpN k else upperSymb hp hpN k

/-- Extended diamond operator `⟨n⟩` for general `n ∈ ℕ`: `diamondSymb (n mod N)` when `(n,N)=1`,
zero otherwise.  Mirrors `HeckeRing.GL2.diamondOp_n`. -/
noncomputable def diamondSymb_n (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) : Module.End ℤ (𝕄 N k) :=
  if h : Nat.Coprime n N then diamondSymb N k (ZMod.unitOfCoprime n h) else 0

/-- `T_{p^r}` on `𝕄 N k` via the Diamond–Shurman recurrence (over `ℤ`, weight `k ≥ 2`):
- `T_{p^0} = 1`, `T_{p^1} = T_p`,
- `T_{p^{r+2}} = T_p · T_{p^{r+1}} - p^{k-1} · ⟨p⟩ · T_{p^r}`.
The scalar `p^{k-1}` uses `(k-1).toNat` (`= k-1` for `k ≥ 2`).  Mirrors
`HeckeRing.GL2.heckeT_ppow`. -/
noncomputable def heckeSymbPpow (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    ℕ → Module.End ℤ (𝕄 N k)
  | 0 => 1
  | 1 => heckeSymb_p_all N k p hp
  | r + 2 =>
    heckeSymb_p_all N k p hp * heckeSymbPpow N k p hp (r + 1) -
      ((p : ℤ) ^ (k - 1).toNat) • (diamondSymb_n N k p * heckeSymbPpow N k p hp r)

@[simp]
theorem heckeSymbPpow_zero (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    heckeSymbPpow N k p hp 0 = 1 := rfl

@[simp]
theorem heckeSymbPpow_one (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    heckeSymbPpow N k p hp 1 = heckeSymb_p_all N k p hp := rfl

theorem heckeSymbPpow_succ_succ (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    heckeSymbPpow N k p hp (r + 2) =
      heckeSymb_p_all N k p hp * heckeSymbPpow N k p hp (r + 1) -
        ((p : ℤ) ^ (k - 1).toNat) • (diamondSymb_n N k p * heckeSymbPpow N k p hp r) := rfl

/-- Auxiliary for `heckeSymb`: peels off the smallest prime factor of `m`. -/
noncomputable def heckeSymb_aux (N : ℕ) [NeZero N] (k : ℤ) (m : ℕ) : Module.End ℤ (𝕄 N k) :=
  if h : m ≤ 1 then 1
  else
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    heckeSymbPpow N k p hp v * heckeSymb_aux N k (m / p ^ v)
termination_by m
decreasing_by
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)).ne' hp.one_lt)

/-- **The Hecke operator `T_n`** on `𝕄 N k` for general `n ∈ ℕ⁺`, as a `ℤ`-linear endomorphism.

Defined as the product of prime-power components `T_n = ∏_{p^v ‖ n} T_{p^v}` (with `U_p` at bad
primes `p ∣ N`), assembled by peeling off `minFac(n)`.  Mirrors `HeckeRing.GL2.heckeT_n`, using the
same double-coset representatives `T_p_upper` (and the diamond-twisted lower term at `p ∤ N`). -/
noncomputable def heckeSymb (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) [NeZero n] : 𝕄 N k →ₗ[ℤ] 𝕄 N k :=
  heckeSymb_aux N k n

@[simp]
theorem heckeSymb_one (N : ℕ) [NeZero N] (k : ℤ) :
    heckeSymb N k 1 = 1 := by
  simp [heckeSymb, heckeSymb_aux]

theorem heckeSymb_prime (N : ℕ) [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeSymb N k p = heckeSymb_p_all N k p hp := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  show heckeSymb_aux N k p = heckeSymb_p_all N k p hp
  rw [heckeSymb_aux, dif_neg (not_le.mpr hp.one_lt)]
  simp only [hp.minFac_eq, hp.factorization_self, pow_one, Nat.div_self hp.pos]
  rw [heckeSymb_aux, dif_pos le_rfl, mul_one]
  rfl

end HeckeRing.GL2.ModularSymbols
