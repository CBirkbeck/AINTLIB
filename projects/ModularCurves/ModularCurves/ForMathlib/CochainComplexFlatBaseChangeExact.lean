/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.BaseChangeKerCoker

/-!
# Universal exactness of bounded flat complexes under iterated base change

Positive-tail exactness of a bounded complex of flat modules after a base change `A`
transports to any further base change `C`: the `A`-side complex has flat terms and, by
the bounded splice, flat cokernels, so its exactness is preserved by every additive
base change. This is the forward (non-flat) companion of
`LinearMap.baseChange_exact_iff_of_faithfullyFlat`.
-/

universe u v

open TensorProduct

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- A tensor product with a subsingleton right factor is a subsingleton. -/
theorem TensorProduct.subsingleton_right (A : Type v) [CommRing A] [Algebra R A]
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] :
    Subsingleton (A ⊗[R] M) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  induction x with
  | zero => rfl
  | tmul a m => rw [Subsingleton.elim m 0, tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- Positive-tail exactness of a bounded complex of flat modules after a base change `A`
transports along any algebra tower `R → A → C`: the base-changed complex has flat terms
and flat cokernels, so its exactness is universal. -/
theorem LinearMap.baseChange_exact_of_bounded_flat_baseChange_exact
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [∀ n, Module.Flat R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1))
    (N : ℕ) [Subsingleton (M (N + 1))]
    (A : Type v) [CommRing A] [Algebra R A]
    (C : Type v) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (hexact : ∀ q, q < N →
      Function.Exact ((d q).baseChange A) ((d (q + 1)).baseChange A))
    (q : ℕ) (hq : q < N) :
    Function.Exact ((d q).baseChange C) ((d (q + 1)).baseChange C) := by
  -- the `A`-side complex
  set MA : ℕ → Type v := fun n ↦ A ⊗[R] M n with hMA
  letI : ∀ n, Module.Flat A (MA n) := fun n ↦ Module.Flat.baseChange R A (M n)
  letI : Subsingleton (MA (N + 1)) :=
    TensorProduct.subsingleton_right A (M (N + 1))
  set dA : ∀ n, MA n →ₗ[A] MA (n + 1) := fun n ↦ (d n).baseChange A with hdA
  -- the cokernel of the second `A`-side differential is flat, by the bounded splice
  letI : Module.Flat A (MA (q + 2) ⧸ LinearMap.range (dA (q + 1))) :=
    Module.Flat.quotient_range_of_bounded_exact MA dA N
      (fun n hn ↦ hexact n hn) (q + 1) hq
  -- transport the pair along `A → C`, then collapse the tower
  have hAC :
      Function.Exact ((dA q).baseChange C) ((dA (q + 1)).baseChange C) := by
    refine LinearMap.baseChange_exact_of_exact_of_flat_coker C (dA q) (dA (q + 1))
      (LinearMap.ext fun y ↦ (hexact q hq).apply_apply_eq_zero y) (hexact q hq)
  exact (LinearMap.baseChange_baseChange_exact_iff A C (d q) (d (q + 1))).mp hAC

/-- Bijectivity of the kernel base-change comparison composes along an algebra tower. -/
theorem kerBaseChangeComparison_bijective_of_tower
    {R : Type u} [CommRing R] {P Q : Type u} [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module R Q] (f : P →ₗ[R] Q)
    (A K : Type u) [CommRing A] [CommRing K] [Algebra R A] [Algebra R K]
    [Algebra A K] [IsScalarTower R A K]
    (hA : Function.Bijective (ModularCurves.kerBaseChangeComparison A f))
    (hK : Function.Bijective
      (ModularCurves.kerBaseChangeComparison K (f.baseChange A))) :
    Function.Bijective (ModularCurves.kerBaseChangeComparison K f) := by
  classical
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K
    (LinearMap.ker f)
  let eA : K ⊗[A] (A ⊗[R] LinearMap.ker f) ≃ₗ[K]
      K ⊗[A] LinearMap.ker (f.baseChange A) :=
    (LinearEquiv.ofBijective (ModularCurves.kerBaseChangeComparison A f)
      hA).baseChange A K _ _
  let eK : K ⊗[A] LinearMap.ker (f.baseChange A) ≃ₗ[K]
      LinearMap.ker ((f.baseChange A).baseChange K) :=
    LinearEquiv.ofBijective
      (ModularCurves.kerBaseChangeComparison K (f.baseChange A)) hK
  let eBB := ModularCurves.LinearMap.baseChangeBaseChangeKernelEquiv A K f
  have hfac : ∀ x, ModularCurves.kerBaseChangeComparison K f x =
      eBB (eK (eA (eCancel.symm x))) := by
    intro x
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k m =>
        apply Subtype.ext
        show k ⊗ₜ[R] (m : P) = _
        simp only [eCancel, eA, eK, eBB,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
          LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply,
          ModularCurves.LinearMap.baseChangeBaseChangeKernelEquiv,
          LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          ModularCurves.kerBaseChangeComparison_coe, LinearMap.baseChange_tmul,
          Submodule.coe_subtype,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
        simp
  constructor
  · intro x y hxy
    have := congrArg (fun q => eCancel (eA.symm (eK.symm (eBB.symm q))))
      ((hfac x).symm.trans ((hfac y).symm ▸ hxy))
    simpa using this
  · intro y
    refine ⟨eCancel (eA.symm (eK.symm (eBB.symm y))), ?_⟩
    rw [hfac]
    simp

end ModularCurves
