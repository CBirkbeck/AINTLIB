module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Free-lattice determinant criteria

This file contains the basis-dependent determinant form of the mod-`p`
finite-index criterion. A full subgroup/index statement can be built on top of
this once the concrete lattices for cyclotomic units are fixed.
-/

@[expose] public section

namespace BernoulliRegular

/-- For an integral square matrix, nonvanishing of its determinant modulo `p`
is exactly nondivisibility of the integral determinant by `p`.

This is the matrix form of the finite-index/free-lattice criterion: in bases,
the subgroup inclusion is represented by an integral matrix `A`, the index is
`|det A|`, and the mod-`p` map is injective exactly when the determinant of
`A` over `ZMod p` is nonzero. -/
theorem intMatrix_index_not_dvd_iff_det_modP_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (p : ℕ) :
    (¬ (p : ℤ) ∣ A.det) ↔
      (A.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
  change (¬ (p : ℤ) ∣ A.det) ↔
    ((Int.castRingHom (ZMod p)).mapMatrix A).det ≠ 0
  rw [← RingHom.map_det (Int.castRingHom (ZMod p)) A]
  change (¬ (p : ℤ) ∣ A.det) ↔ ¬ ((A.det : ZMod p) = 0)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Reversed orientation of `intMatrix_index_not_dvd_iff_det_modP_ne_zero`. -/
theorem intMatrix_det_modP_ne_zero_iff_not_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (p : ℕ) :
    (A.map (Int.castRingHom (ZMod p))).det ≠ 0 ↔
      ¬ (p : ℤ) ∣ A.det :=
  (intMatrix_index_not_dvd_iff_det_modP_ne_zero A p).symm

end BernoulliRegular

end
