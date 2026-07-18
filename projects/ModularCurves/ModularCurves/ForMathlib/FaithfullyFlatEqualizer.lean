/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The Amitsur equalizer of a faithfully flat algebra

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-A1]`): the degree-≤-1 part of the
Amitsur/descent exact sequence (Stacks `descent-lemma-ff-exact`, used by the 03C8 descent
bootstrap). For a faithfully flat `R`-algebra `S`, the equalizer of the two inclusions
`S ⇉ S ⊗[R] S` is exactly the image of `R`:

* `mem_range_algebraMap_iff_tmul_eq` — `s ∈ range (algebraMap R S) ↔ s ⊗ 1 = 1 ⊗ s`;
* `equalizer_includeLeft_includeRight_eq_bot` — the `AlgHom.equalizer` form, mirroring the
  shape of `coinvariants` (`AlgHom.equalizer ρ includeLeft`).

The nontrivial inclusion is the classical cokernel trick: if `s ⊗ 1 = 1 ⊗ s`, push into
`S ⊗[R] (S ⧸ range (algebraMap R S))`, where `s ⊗ [1] = 0`; faithful flatness makes
`x ↦ 1 ⊗ x` injective (`Module.FaithfullyFlat.tensorProduct_mk_injective`), so the class of
`s` in the cokernel vanishes. In the Hopf-Galois application the faithfully flat map is the
co-action `ρ : B → B ⊗[R] A` (free of positive rank via the shear automorphism), and this
equalizer is the top row of the two-row comparison in the `[HG-B5]` bootstrap.
-/

open scoped TensorProduct

namespace Module.FaithfullyFlat

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

variable {S} in
/-- The nontrivial half of the Amitsur equalizer: an element of a faithfully flat algebra
whose two inclusions into `S ⊗[R] S` agree comes from `R`. Push the equation into the
cokernel of `R → S`: `s ⊗ [1] = [1 ⊗ s]` there, the left side is `0`, and `x ↦ 1 ⊗ x` into a
faithfully flat module is injective. -/
theorem mem_range_algebraMap_of_tmul_eq {s : S}
    (h : s ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] s) : s ∈ Set.range (algebraMap R S) := by
  set N : Submodule R S := LinearMap.range (Algebra.linearMap R S) with hN
  have h2 := congrArg (LinearMap.lTensor S N.mkQ) h
  rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul] at h2
  have hq1 : N.mkQ 1 = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by rw [Algebra.linearMap_apply, map_one]⟩
  rw [hq1, TensorProduct.tmul_zero] at h2
  have hqs : N.mkQ s = 0 :=
    tensorProduct_mk_injective (A := R) (B := S) (S ⧸ N)
      (show TensorProduct.mk R S (S ⧸ N) 1 (N.mkQ s) = TensorProduct.mk R S (S ⧸ N) 1 0 by
        rw [TensorProduct.mk_apply, TensorProduct.mk_apply, TensorProduct.tmul_zero]
        exact h2.symm)
  obtain ⟨r, hr⟩ := (Submodule.Quotient.mk_eq_zero N).mp (by rwa [Submodule.mkQ_apply] at hqs)
  exact ⟨r, hr⟩

variable {S} in
/-- **The Amitsur equalizer of a faithfully flat algebra** (Stacks `descent-lemma-ff-exact`,
degree ≤ 1): `s` comes from `R` if and only if `s ⊗ 1 = 1 ⊗ s` in `S ⊗[R] S`. -/
theorem mem_range_algebraMap_iff_tmul_eq (s : S) :
    s ∈ Set.range (algebraMap R S) ↔ s ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] s := by
  refine ⟨fun ⟨r, hr⟩ => ?_, mem_range_algebraMap_of_tmul_eq R⟩
  rw [← hr, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The `AlgHom.equalizer` form of the Amitsur equalizer: the subalgebra of `S` where the two
inclusions `S ⇉ S ⊗[R] S` agree is the bottom subalgebra. This is the shape consumed by the
`[HG-B5]` descent bootstrap (compare `coinvariants ρ = AlgHom.equalizer ρ includeLeft`). -/
theorem equalizer_includeLeft_includeRight_eq_bot :
    AlgHom.equalizer (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) = ⊥ := by
  ext s
  rw [AlgHom.mem_equalizer, Algebra.mem_bot, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  exact (mem_range_algebraMap_iff_tmul_eq R s).symm

end Module.FaithfullyFlat
