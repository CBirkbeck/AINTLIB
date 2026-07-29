/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's `CoherentCohomologyFinite.SegreDiagonalSurjectivity`.
-/
import ModularCurves.ForMathlib.SegreExponentMatrix
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Equal-bidegree surjectivity of the Segre coordinate map

Every pure tensor of homogeneous polynomials of the same degree lies in the
range of the Segre coordinate map.
-/

open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

lemma segreCoordinateHom_monomial
    (R : Type u) [CommRing R] (m n : ℕ)
    (e : Fin (m + 1) × Fin (n + 1) →₀ ℕ) (r : R) :
    segreCoordinateHom R m n (monomial e r) =
      monomial (segreRowSum e) r ⊗ₜ[R] monomial (segreColumnSum e) 1 := by
  rw [segreCoordinateHom, aeval_monomial]
  classical
  simp only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.algebraMap_apply]
  have hprod :
      e.prod (fun x exponent =>
          ((X x.1 : MvPolynomial (Fin (m + 1)) R) ^ exponent) ⊗ₜ[R]
            ((X x.2 : MvPolynomial (Fin (n + 1)) R) ^ exponent)) =
        (e.prod (fun x exponent =>
            (X x.1 : MvPolynomial (Fin (m + 1)) R) ^ exponent) ⊗ₜ[R]
          e.prod (fun x exponent =>
            (X x.2 : MvPolynomial (Fin (n + 1)) R) ^ exponent)) := by
    simp only [Finsupp.prod]
    induction e.support using Finset.induction_on with
    | empty => exact Algebra.TensorProduct.one_def
    | @insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
          Algebra.TensorProduct.tmul_mul_tmul]
  have hrow :
      (segreRowSum e).prod
          (fun i exponent => (X i : MvPolynomial (Fin (m + 1)) R) ^ exponent) =
        e.prod (fun x exponent =>
          (X x.1 : MvPolynomial (Fin (m + 1)) R) ^ exponent) :=
    Finsupp.prod_mapDomain_index
      (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  have hcolumn :
      (segreColumnSum e).prod
          (fun j exponent => (X j : MvPolynomial (Fin (n + 1)) R) ^ exponent) =
        e.prod (fun x exponent =>
          (X x.2 : MvPolynomial (Fin (n + 1)) R) ^ exponent) :=
    Finsupp.prod_mapDomain_index
      (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  rw [hprod, Algebra.TensorProduct.tmul_mul_tmul, monomial_eq, monomial_eq,
    hrow, hcolumn, C_1, one_mul, algebraMap_eq]

/-- Equal-degree pure tensors of monomials lie in the Segre coordinate range. -/
lemma pureTensor_monomial_mem_segreCoordinateRange
    (R : Type u) [CommRing R] (m n : ℕ)
    (a : Fin (m + 1) →₀ ℕ) (b : Fin (n + 1) →₀ ℕ) (r s : R)
    (hdegree : a.degree = b.degree) :
    monomial a r ⊗ₜ[R] monomial b s ∈
      LinearMap.range (segreCoordinateHom R m n).toLinearMap := by
  obtain ⟨e, he₁, he₂⟩ := exists_exponentMatrix a b hdegree
  refine ⟨monomial e (r * s), ?_⟩
  rw [AlgHom.toLinearMap_apply, segreCoordinateHom_monomial, he₁, he₂]
  calc
    monomial a (r * s) ⊗ₜ[R] monomial b 1 =
        ((r * s) • monomial a (1 : R)) ⊗ₜ[R] monomial b (1 : R) := by
      rw [smul_monomial]
      simp
    _ = (r • monomial a (1 : R)) ⊗ₜ[R] (s • monomial b (1 : R)) := by
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, mul_comm]
    _ = monomial a r ⊗ₜ[R] monomial b s := by
      rw [smul_monomial, smul_monomial]
      simp

/-- Equal-degree pure tensors of homogeneous polynomials lie in the coordinate range. -/
lemma pureTensor_homogeneous_mem_segreCoordinateRange
    (R : Type u) [CommRing R] (m n d : ℕ)
    (p : MvPolynomial (Fin (m + 1)) R)
    (q : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ homogeneousSubmodule (Fin (m + 1)) R d)
    (hq : q ∈ homogeneousSubmodule (Fin (n + 1)) R d) :
    p ⊗ₜ[R] q ∈ LinearMap.range (segreCoordinateHom R m n).toLinearMap := by
  have hp' : p.IsHomogeneous d := by
    rwa [mem_homogeneousSubmodule] at hp
  have hq' : q.IsHomogeneous d := by
    rwa [mem_homogeneousSubmodule] at hq
  rw [as_sum p, as_sum q, TensorProduct.sum_tmul]
  simp_rw [TensorProduct.tmul_sum]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro b hb
  exact pureTensor_monomial_mem_segreCoordinateRange R m n a b
    (coeff a p) (coeff b q)
    ((hp'.degree_eq_sum_deg_support ha).symm.trans
      (hq'.degree_eq_sum_deg_support hb))

end MvPolynomial
