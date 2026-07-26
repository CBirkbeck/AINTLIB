/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The cotangent space at a rational point of a smooth algebra (T-SMOOTH-REG brick 4)

Let `A` be a formally smooth `k`-algebra with `Ω[A⁄k]` free of rank `≤ 1`, and let
`𝔪 = ker (A → k)` be the maximal ideal of a `k`-rational point. Then

> `𝔪/𝔪²` is at most one-dimensional over `k`, hence `𝔪 ≤ (x) + 𝔪²` for a single `x ∈ 𝔪`.

The injectivity of the cotangent comparison `𝔪/𝔪² → k ⊗_A Ω[A⁄k]` is mathlib's
`Algebra.FormallySmooth.kerCotangentToTensor_injective_iff` applied to the *split*
surjection `A ↠ k` (the splitting is the structure map `k → A`, which is why
`H¹_{k/k}` vanishes and the comparison is injective rather than merely surjective).

Combined with `ForMathlib/KrullDimQuotientSpan.lean` (the dimension lower bound) this gives
"smooth of relative dimension one over an algebraically closed field ⟹ the local rings are
regular, hence domains".
-/

universe u

open TensorProduct

namespace ModularCurves

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra A k]
  [IsScalarTower k A k]

/-- A `k`-algebra `A` with a `k`-algebra map to `k` has that map surjective — the structure
map `k → A` is a section. -/
theorem algebraMap_surjective_of_isScalarTower : Function.Surjective (algebraMap A k) :=
  fun c => ⟨algebraMap k A c, (IsScalarTower.algebraMap_apply k A k c).symm.trans (by simp)⟩

variable [Algebra.FormallySmooth k A]

/-- **(brick 4a)** At a `k`-rational point of a formally smooth `k`-algebra the cotangent
comparison `𝔪/𝔪² → k ⊗_A Ω[A⁄k]` is injective, because `H¹` of `k` over `k` vanishes. -/
theorem kerCotangentToTensor_injective :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k A k) :=
  (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    (algebraMap_surjective_of_isScalarTower k A)).mpr inferInstance

variable [Module.Free A (Ω[A⁄k])]

/-- **(brick 4b)** Hence `dim_k 𝔪/𝔪² ≤ rank_A Ω[A⁄k]`. -/
theorem rank_cotangent_le_rank_kaehler :
    Module.rank k (RingHom.ker (algebraMap A k) : Ideal A).Cotangent ≤
      Module.rank A (Ω[A⁄k]) := by
  haveI : Nontrivial A := (algebraMap A k).domain_nontrivial
  have hbc : Module.rank k (k ⊗[A] Ω[A⁄k]) = Module.rank A (Ω[A⁄k]) := by
    rw [Module.rank_baseChange]
    simp
  rw [← hbc]
  exact LinearMap.rank_le_of_injective
    ((KaehlerDifferential.kerCotangentToTensor k A k).restrictScalars k)
    (kerCotangentToTensor_injective k A)

/-- **(T-SMOOTH-REG brick 4 ★)** If moreover `Ω[A⁄k]` has rank at most one, the maximal
ideal of the rational point is *principal modulo its square*: there is a single `x ∈ 𝔪`
with `𝔪 ≤ (x) + 𝔪²`. -/
theorem exists_le_span_singleton_sup_sq (hrank : Module.rank A (Ω[A⁄k]) ≤ 1) :
    ∃ x ∈ RingHom.ker (algebraMap A k),
      (RingHom.ker (algebraMap A k) : Ideal A) ≤
        Ideal.span {x} ⊔ (RingHom.ker (algebraMap A k) : Ideal A) ^ 2 := by
  classical
  set 𝔪 : Ideal A := RingHom.ker (algebraMap A k) with h𝔪
  have hrk : Module.rank k 𝔪.Cotangent ≤ 1 :=
    le_trans (rank_cotangent_le_rank_kaehler k A) hrank
  obtain ⟨y, hy⟩ := rank_le_one_iff.mp hrk
  obtain ⟨⟨x, hx⟩, rfl⟩ := 𝔪.toCotangent_surjective y
  refine ⟨x, hx, fun z hz => ?_⟩
  obtain ⟨r, hr⟩ := hy (𝔪.toCotangent ⟨z, hz⟩)
  -- `r • (x mod 𝔪²) = z mod 𝔪²`, and the `k`-action is the `A`-action through `k → A`
  have hrA : (algebraMap k A r) • 𝔪.toCotangent ⟨x, hx⟩ = 𝔪.toCotangent ⟨z, hz⟩ := by
    rw [← hr, algebra_compatible_smul A r]
  rw [← map_smul] at hrA
  have hsub : z - r • x ∈ 𝔪 ^ 2 := by
    have h := (Ideal.toCotangent_eq (I := 𝔪)
      (x := ⟨z, hz⟩) (y := (algebraMap k A r) • (⟨x, hx⟩ : 𝔪))).mp hrA.symm
    simpa using h
  have hzeq : z = r • x + (z - r • x) := by abel
  rw [hzeq]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hsub)
  rw [Algebra.smul_def]
  exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩

end ModularCurves
