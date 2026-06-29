import LeanModularForms.HeckeRIngs.GL2.Newforms.Newform
import Mathlib.Tactic

/-!
# LeanBridge issue #55: dual and self-dual cusp forms

This file defines the conjugate-coefficient dual of a cusp form in the
Nebentypus ambient space `S_k(N, χ)`, represented in this repository as the
`χ`-eigenspace inside cusp forms for `Γ₁(N)`.

The construction is the slash action by the reflection
`J = [-1, 0; 0, 1]`, which sends `τ` to `-conj τ`.  The form `dualForm f`
is a bundled cusp form, its `∞`-Fourier coefficients are the complex
conjugates of those of `f`, and it sends the `χ`-character subspace to the
pointwise conjugate character subspace.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex
open scoped ComplexConjugate MatrixGroups ModularForm Pointwise

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The canonical Fourier coefficient `aₙ(f)` of a cusp form at the cusp `∞`. -/
noncomputable def fourierCoeffAtInfinity (f : CuspForm Γ k) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n

@[simp]
lemma fourierCoeffAtInfinity_apply (f : CuspForm Γ k) (n : ℕ) :
    fourierCoeffAtInfinity f n =
      (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n :=
  rfl

/-- `g` has the `∞`-coefficients expected of the conjugate-coefficient dual of `f`. -/
def HasConjugateCoefficientsAtInfinity (f g : CuspForm Γ k) : Prop :=
  ∀ n : ℕ, fourierCoeffAtInfinity g n = conj (fourierCoeffAtInfinity f n)

@[symm]
lemma HasConjugateCoefficientsAtInfinity.symm {f g : CuspForm Γ k}
    (h : HasConjugateCoefficientsAtInfinity f g) :
    HasConjugateCoefficientsAtInfinity g f := by
  intro n
  have hn := congrArg conj (h n)
  simpa using hn.symm

lemma hasConjugateCoefficientsAtInfinity_comm (f g : CuspForm Γ k) :
    HasConjugateCoefficientsAtInfinity f g ↔ HasConjugateCoefficientsAtInfinity g f :=
  ⟨HasConjugateCoefficientsAtInfinity.symm, HasConjugateCoefficientsAtInfinity.symm⟩

/--
A cusp form is self-dual, for its L-function, when all canonical Fourier
coefficients at `∞` are real.
-/
def IsSelfDual (f : CuspForm Γ k) : Prop :=
  ∀ n : ℕ, (fourierCoeffAtInfinity f n).im = 0

lemma isSelfDual_iff_self_hasConjugateCoefficientsAtInfinity
    (f : CuspForm Γ k) :
    IsSelfDual f ↔ HasConjugateCoefficientsAtInfinity f f := by
  constructor
  · intro hf n
    exact ((Complex.conj_eq_iff_im).mpr (hf n)).symm
  · intro h n
    exact (Complex.conj_eq_iff_im).mp (h n).symm

namespace LFunction

/--
Self-duality of the L-function attached to a cusp form, expressed at the
coefficient-sequence level: the Dirichlet-series coefficients are real.
-/
def IsSelfDual (f : CuspForm Γ k) : Prop :=
  ∀ n : ℕ, (ModularForms.lCoeff f n).im = 0

end LFunction

lemma lCoeff_eq_fourierCoeffAtInfinity (f : CuspForm Γ k) (n : ℕ) :
    ModularForms.lCoeff f n = fourierCoeffAtInfinity f n := by
  rfl

lemma isSelfDual_iff_lFunction_selfDual
    (f : CuspForm Γ k) :
    IsSelfDual f ↔ LFunction.IsSelfDual f := by
  simp [IsSelfDual, LFunction.IsSelfDual]

variable {N : ℕ} [NeZero N]

section CongruenceSubgroup

/-- Reflection of an integral determinant-one matrix by `J`. -/
def reflectSL (A : SL(2, ℤ)) : SL(2, ℤ) where
  val := !![A 0 0, -A 0 1; -A 1 0, A 1 1]
  property := by
    rw [Matrix.det_fin_two]
    have hdet := A.property
    rw [Matrix.det_fin_two] at hdet
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet

lemma reflectSL_mem_Gamma1 {N : ℕ} (A : SL(2, ℤ)) (hA : A ∈ Gamma1 N) :
    reflectSL A ∈ Gamma1 N := by
  rw [Gamma1_mem] at hA ⊢
  simpa [reflectSL] using hA

lemma J_inv_eq_J : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
  rw [inv_eq_iff_mul_eq_one]
  simpa [sq] using UpperHalfPlane.J_sq

lemma reflectSL_mapGL_eq_J_mul (A : SL(2, ℤ)) :
    (mapGL ℝ (reflectSL A) : GL (Fin 2) ℝ) =
      UpperHalfPlane.J * (mapGL ℝ A : GL (Fin 2) ℝ) * UpperHalfPlane.J⁻¹ := by
  rw [J_inv_eq_J]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectSL, UpperHalfPlane.J, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

lemma Gamma1_map_conj_J_le (N : ℕ) :
    (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • ((Gamma1 N).map (mapGL ℝ)) ≤
      (Gamma1 N).map (mapGL ℝ) := by
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  rcases hx with ⟨A, hA, hAeq⟩
  refine ⟨reflectSL A, reflectSL_mem_Gamma1 A hA, ?_⟩
  have hJJ : UpperHalfPlane.J * UpperHalfPlane.J = 1 := by
    simpa [sq] using UpperHalfPlane.J_sq
  rw [reflectSL_mapGL_eq_J_mul, hAeq]
  simp [J_inv_eq_J, ConjAct.smul_def]
  calc
    UpperHalfPlane.J * (UpperHalfPlane.J * x * UpperHalfPlane.J) * UpperHalfPlane.J =
        (UpperHalfPlane.J * UpperHalfPlane.J) * x *
          (UpperHalfPlane.J * UpperHalfPlane.J) := by
      group
    _ = x := by simp [hJJ]

lemma Gamma1_map_le_conj_J (N : ℕ) :
    (Gamma1 N).map (mapGL ℝ) ≤
      (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • ((Gamma1 N).map (mapGL ℝ)) := by
  rw [Subgroup.subset_pointwise_smul_iff]
  rw [← ConjAct.toConjAct_inv]
  simpa [J_inv_eq_J] using Gamma1_map_conj_J_le N

/--
Conjugating the image of `Γ₁(N)` in `GL₂(ℝ)` by `J` gives back the same subgroup.
-/
lemma Gamma1_map_conj_J_eq (N : ℕ) :
    (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • ((Gamma1 N).map (mapGL ℝ)) =
      (Gamma1 N).map (mapGL ℝ) :=
  le_antisymm (Gamma1_map_conj_J_le N) (Gamma1_map_le_conj_J N)

end CongruenceSubgroup

/--
The conjugate-coefficient dual cusp form.

Concretely, this is the slash action by `J = [-1,0;0,1]`, bundled back as a
cusp form for `Γ₁(N)`.
-/
noncomputable def dualForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (Gamma1_map_conj_J_eq N) ▸ CuspForm.translate f UpperHalfPlane.J

/-
Previous inclusion-based definition:

noncomputable def dualForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  CuspForm.restrictSubgroup (Gamma1_map_le_conj_J N) (CuspForm.translate f UpperHalfPlane.J)
-/

lemma cuspForm_cast_coe {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ = Γ')
    (f : CuspForm Γ k) :
    ⇑(h ▸ f : CuspForm Γ' k) = ⇑f := by
  cases h
  rfl

omit [NeZero N] in
lemma dualForm_coe (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(dualForm f) = ⇑f ∣[k] UpperHalfPlane.J := by
  unfold dualForm
  rw [cuspForm_cast_coe]
  rfl

omit [NeZero N] in
lemma slash_J_apply (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    (⇑f ∣[k] UpperHalfPlane.J) τ = conj (f (UpperHalfPlane.J • τ)) := by
  simp [ModularForm.slash_apply]

/-- The `q`-parameter at `J • τ` is the complex conjugate of the `q`-parameter at `τ`. -/
lemma qParam_J_eq_conj (τ : UpperHalfPlane) :
    Function.Periodic.qParam (1 : ℝ) (↑(UpperHalfPlane.J • τ) : ℂ) =
      conj (Function.Periodic.qParam (1 : ℝ) (τ : ℂ)) := by
  have harg : 2 * ↑Real.pi * I * (↑(UpperHalfPlane.J • τ) : ℂ) / (↑(1 : ℝ) : ℂ) =
      conj (2 * ↑Real.pi * I * (τ : ℂ) / (↑(1 : ℝ) : ℂ)) := by
    simp only [UpperHalfPlane.coe_J_smul, div_eq_mul_inv, map_mul, map_inv₀, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Function.Periodic.qParam, Function.Periodic.qParam, harg, Complex.exp_conj]

lemma qParam_J_pow_conj (τ : UpperHalfPlane) (m : ℕ) :
    Function.Periodic.qParam (1 : ℝ) (↑(UpperHalfPlane.J • τ) : ℂ) ^ m =
      conj (Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) := by
  rw [qParam_J_eq_conj]
  simp

omit [NeZero N] in
lemma dualForm_hasSum_conj_coeff
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    HasSum
      (fun m : ℕ ↦ conj ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m) •
        Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      (dualForm f τ) := by
  have h_period := one_mem_strictPeriods_Gamma1_map N
  haveI : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨((Gamma1 N).map (mapGL ℝ)).isCusp_of_mem_strictPeriods one_pos h_period⟩
  have hf_sum : HasSum
      (fun m : ℕ ↦ (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m •
        Function.Periodic.qParam (1 : ℝ) (↑(UpperHalfPlane.J • τ) : ℂ) ^ m)
      (f (UpperHalfPlane.J • τ)) := by
    exact UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f h_period)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
      (UpperHalfPlane.J • τ)
  have hconj := (Complex.hasSum_conj').mpr hf_sum
  rw [dualForm_coe, slash_J_apply]
  simpa [smul_eq_mul, qParam_J_pow_conj τ, mul_comm, mul_left_comm, mul_assoc] using hconj

omit [NeZero N] in
/-- The `∞`-Fourier coefficients of `dualForm f` are the conjugates of those of `f`. -/
lemma dualForm_coeffAtInfinity_eq_conj
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    fourierCoeffAtInfinity (dualForm f) n = conj (fourierCoeffAtInfinity f n) := by
  have hcoeff := ModularFormClass.qExpansion_coeff_unique
    (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (Γ := ((Gamma1 N).map (mapGL ℝ))) (k := k)
    (c := fun m : ℕ ↦ conj ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m))
    one_pos (one_mem_strictPeriods_Gamma1_map N)
    (f := dualForm f) (dualForm_hasSum_conj_coeff f) n
  rw [fourierCoeffAtInfinity, fourierCoeffAtInfinity,
    ModularForms.strictWidthInfty_Gamma1_mapGL]
  exact hcoeff.symm

omit [NeZero N] in
lemma dualForm_hasConjugateCoefficientsAtInfinity
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    HasConjugateCoefficientsAtInfinity f (dualForm f) :=
  dualForm_coeffAtInfinity_eq_conj f

omit [NeZero N] in
lemma dualForm_lCoeff_eq_conj
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    ModularForms.lCoeff (dualForm f) n = conj (ModularForms.lCoeff f n) := by
  rw [lCoeff_eq_fourierCoeffAtInfinity, lCoeff_eq_fourierCoeffAtInfinity]
  exact dualForm_coeffAtInfinity_eq_conj f n

section Involution

omit [NeZero N] in
lemma cuspForm_Gamma1_ext_of_forall_fourierCoeffAtInfinity_eq
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (h : ∀ n : ℕ, fourierCoeffAtInfinity f n = fourierCoeffAtInfinity g n) :
    f = g := by
  refine DFunLike.coe_injective ?_
  show (⇑f : UpperHalfPlane → ℂ) = ⇑g
  have h_period := one_mem_strictPeriods_Gamma1_map N
  have h_qExp_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) f.toModularForm').coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g.toModularForm').coeff n := by
    intro n
    change (UpperHalfPlane.qExpansion (1 : ℝ) (⇑f : UpperHalfPlane → ℂ)).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ) (⇑g : UpperHalfPlane → ℂ)).coeff n
    simpa [fourierCoeffAtInfinity, ModularForms.strictWidthInfty_Gamma1_mapGL] using h n
  have h_diff_qExp_zero :
      UpperHalfPlane.qExpansion (1 : ℝ) (f.toModularForm' - g.toModularForm') = 0 := by
    rw [ModularForm.qExpansion_sub one_pos h_period f.toModularForm' g.toModularForm']
    ext n
    simp [h_qExp_eq n]
  have h_diff_zero : f.toModularForm' - g.toModularForm' = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos h_period
      (f := f.toModularForm' - g.toModularForm')).mp h_diff_qExp_zero
  funext z
  have hz := DFunLike.congr_fun h_diff_zero z
  exact sub_eq_zero.mp hz

omit [NeZero N] in
/-- The dualForm map is an involution. -/
lemma dualForm_dualForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    dualForm (dualForm f) = f := by
  apply cuspForm_Gamma1_ext_of_forall_fourierCoeffAtInfinity_eq
  intro n
  rw [dualForm_coeffAtInfinity_eq_conj, dualForm_coeffAtInfinity_eq_conj]
  simp

omit [NeZero N] in
lemma isSelfDual_of_dualForm_eq_self
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (h : dualForm f = f) :
    IsSelfDual f := by
  intro n
  have hcoeff := congrArg (fun g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k ↦
    fourierCoeffAtInfinity g n) h
  rw [dualForm_coeffAtInfinity_eq_conj] at hcoeff
  exact Complex.conj_eq_iff_im.mp hcoeff

omit [NeZero N] in
lemma dualForm_eq_self_of_isSelfDual
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : IsSelfDual f) :
    dualForm f = f := by
  apply cuspForm_Gamma1_ext_of_forall_fourierCoeffAtInfinity_eq
  intro n
  have hreal : conj (fourierCoeffAtInfinity f n) = fourierCoeffAtInfinity f n :=
    (Complex.conj_eq_iff_im).mpr (hf n)
  rw [dualForm_coeffAtInfinity_eq_conj, hreal]

omit [NeZero N] in
/-- A cusp form is fixed by `dualForm` if and only if all of its `∞`-coefficients are real. -/
lemma dualForm_eq_self_iff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    dualForm f = f ↔ IsSelfDual f :=
  ⟨isSelfDual_of_dualForm_eq_self, dualForm_eq_self_of_isSelfDual f⟩

end Involution

section Character

/-- Pointwise conjugation of a Nebentypus character. -/
def conjNebentypus (χ : (ZMod N)ˣ →* ℂˣ) : (ZMod N)ˣ →* ℂˣ where
  toFun d := star (χ d)
  map_one' := by simp
  map_mul' d e := by
    ext
    simp [map_mul]

omit [NeZero N] in
@[simp]
lemma conjNebentypus_apply_coe (χ : (ZMod N)ˣ →* ℂˣ) (d : (ZMod N)ˣ) :
    ((conjNebentypus χ d : ℂ)) = conj ((χ d : ℂ)) := by
  rfl

lemma reflectSL_mem_Gamma0 {N : ℕ} (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) :
    reflectSL A ∈ Gamma0 N := by
  rw [Gamma0_mem] at hA ⊢
  simpa [reflectSL] using hA

lemma J_mul_mapGL_eq_reflectSL_mul_J (A : SL(2, ℤ)) :
    UpperHalfPlane.J * (mapGL ℝ A : GL (Fin 2) ℝ) =
      (mapGL ℝ (reflectSL A) : GL (Fin 2) ℝ) * UpperHalfPlane.J := by
  rw [reflectSL_mapGL_eq_J_mul, J_inv_eq_J]
  rw [mul_assoc (UpperHalfPlane.J * (mapGL ℝ A : GL (Fin 2) ℝ))
    UpperHalfPlane.J UpperHalfPlane.J]
  simp [show UpperHalfPlane.J * UpperHalfPlane.J = 1 by
    simpa [sq] using UpperHalfPlane.J_sq]

omit [NeZero N] in
lemma Gamma0MapUnits_reflectSL (g : ↥(Gamma0 N)) :
    Gamma0MapUnits
        ⟨reflectSL (g : SL(2, ℤ)), reflectSL_mem_Gamma0 (g : SL(2, ℤ)) g.property⟩ =
      Gamma0MapUnits g := by
  ext
  simp [Gamma0MapUnits_val, Gamma0Map, reflectSL]

/--
The dual form sends the `χ`-Nebentypus subspace to the subspace for the pointwise
conjugate character.
-/
lemma dualForm_mem_conjNebentypus {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ) :
    dualForm f ∈ cuspFormCharSpace k (conjNebentypus χ) := by
  rw [cuspFormCharSpace_iff_nebentypus]
  intro g
  have hf_neb := (cuspFormCharSpace_iff_nebentypus k χ f).mp hfχ
  let gJ : ↥(Gamma0 N) :=
    ⟨reflectSL (g : SL(2, ℤ)), reflectSL_mem_Gamma0 (g : SL(2, ℤ)) g.property⟩
  have hunit : Gamma0MapUnits gJ = Gamma0MapUnits g := Gamma0MapUnits_reflectSL g
  calc
    (⇑(dualForm f) ∣[k] mapGL ℝ (g : SL(2, ℤ)))
        = ((⇑f ∣[k] UpperHalfPlane.J) ∣[k] mapGL ℝ (g : SL(2, ℤ))) := by
          rw [dualForm_coe]
    _ = ⇑f ∣[k] (UpperHalfPlane.J * mapGL ℝ (g : SL(2, ℤ))) := by
          rw [← SlashAction.slash_mul]
    _ = ⇑f ∣[k] (mapGL ℝ (reflectSL (g : SL(2, ℤ))) * UpperHalfPlane.J) := by
          rw [J_mul_mapGL_eq_reflectSL_mul_J]
    _ = (⇑f ∣[k] mapGL ℝ (reflectSL (g : SL(2, ℤ)))) ∣[k] UpperHalfPlane.J := by
          rw [SlashAction.slash_mul]
    _ = (((χ (Gamma0MapUnits g) : ℂ) • ⇑f) ∣[k] UpperHalfPlane.J) := by
          rw [← hunit]
          exact congrArg (fun F : UpperHalfPlane → ℂ => F ∣[k] UpperHalfPlane.J) (hf_neb gJ)
    _ = (↑(conjNebentypus χ (Gamma0MapUnits g)) : ℂ) • ⇑(dualForm f) := by
          rw [dualForm_coe]
          simp [ModularForm.smul_slash]

/-- A Nebentypus character is real-valued when all of its values have zero imaginary part. -/
def HasRealNebentypus (χ : (ZMod N)ˣ →* ℂˣ) : Prop :=
  ∀ d : (ZMod N)ˣ, ((χ d : ℂ).im = 0)

omit [NeZero N] in
/-- A real-valued Nebentypus character is unchanged by pointwise complex conjugation. -/
lemma conjNebentypus_eq_of_hasRealNebentypus {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : HasRealNebentypus χ) :
    conjNebentypus χ = χ := by
  ext d
  rw [conjNebentypus_apply_coe]
  exact (Complex.conj_eq_iff_im).mpr (hχ d)

omit [NeZero N] in
@[simp]
lemma hasRealNebentypus_one : HasRealNebentypus (N := N) 1 := by
  intro d
  simp

/-- A character is quadratic if all values are `±1`. -/
def IsQuadraticNebentypus (χ : (ZMod N)ˣ →* ℂˣ) : Prop :=
  ∀ d : (ZMod N)ˣ, χ d = 1 ∨ χ d = -1

omit [NeZero N] in
lemma IsQuadraticNebentypus.hasRealNebentypus {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : IsQuadraticNebentypus χ) : HasRealNebentypus χ := by
  intro d
  rcases hχ d with hd | hd <;> simp [hd]

lemma HasRealNebentypus.isQuadratic {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : HasRealNebentypus χ) : IsQuadraticNebentypus χ := by
  intro d
  let x : ℝ := (χ d : ℂ).re
  have hx_complex : (x : ℂ) = (χ d : ℂ) := by
    apply Complex.ext
    · simp [x]
    · simp [x, hχ d]
  have hpow_units : χ d ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one, map_one]
  have hpow_complex : (x : ℂ) ^ Fintype.card (ZMod N)ˣ = (1 : ℂ) := by
    rw [hx_complex]
    simpa using congrArg Units.val hpow_units
  have hpow_real : x ^ Fintype.card (ZMod N)ˣ = 1 := by
    exact Complex.ofReal_injective (by simpa using hpow_complex)
  have hx_fin : IsOfFinOrder x :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos_iff.mpr ⟨(1 : (ZMod N)ˣ)⟩, hpow_real⟩
  rcases le_total 0 x with hx_nonneg | hx_nonpos
  · left
    apply Units.ext
    change (χ d : ℂ) = (1 : ℂ)
    rw [← hx_complex, IsOfFinOrder.eq_one hx_nonneg hx_fin]
    norm_num
  · right
    apply Units.ext
    change (χ d : ℂ) = (-1 : ℂ)
    rw [← hx_complex, IsOfFinOrder.eq_neg_one hx_nonpos hx_fin]
    norm_num

/-- For Nebentypus characters, being real-valued is equivalent to being quadratic. -/
lemma hasRealNebentypus_iff_isQuadraticNebentypus (χ : (ZMod N)ˣ →* ℂˣ) :
    HasRealNebentypus χ ↔ IsQuadraticNebentypus χ :=
  ⟨HasRealNebentypus.isQuadratic, IsQuadraticNebentypus.hasRealNebentypus⟩

end Character

section TestCases

/-- Test case: a real Nebentypus space is preserved by the dual form. -/
lemma dualForm_mem_realNebentypus {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ) (hχ : HasRealNebentypus χ) :
    dualForm f ∈ cuspFormCharSpace k χ := by
  simpa [conjNebentypus_eq_of_hasRealNebentypus hχ] using
    dualForm_mem_conjNebentypus (χ := χ) (f := f) hfχ

/-- Test case: a newform with a non-real coefficient is not self-dual. -/
lemma newform_not_selfDual_of_nonreal_coeff (f : Newform N k) {n : ℕ}
    (hn : (fourierCoeffAtInfinity f.toCuspForm n).im ≠ 0) :
    ¬ IsSelfDual f.toCuspForm := by
  intro h
  exact hn (h n)

end TestCases

end HeckeRing.GL2
