/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.ReducedConstantRankFree

/-!
# Constant kernel rank over a reduced ring (Mumford, *Abelian Varieties* §5)

Let `u : K₀ →ₗ[R] K₁` be a map of finite projective modules over a **reduced** Noetherian ring
`R`, and suppose the fibre kernels `ker (u ⊗ κ(p))` all have the same dimension `n`. Then

* the cokernel `K₁ ⧸ range u` is projective
  (`projective_quotient_range_of_constant_finrank_ker_baseChange`),
* the kernel `ker u` is projective (`projective_ker_of_constant_finrank_ker_baseChange`),
* the kernel `ker u` is finite (`finite_ker_of_constant_finrank_ker_baseChange`).

## Why this file exists

This is the step of Mumford's proof of the seesaw/cube theorems that **replaces
cohomology-and-base-change (Grauert)**, which mathlib does not have. In the intended application
`u` is the degree-`(0,1)` differential of a finite projective replacement of a Čech complex, so
`ker u` computes `H⁰` and `K₁ ⧸ range u` receives `H¹`; constancy of `dim H⁰` of the fibres is the
hypothesis one actually verifies on an elliptic surface, and local freeness of `H⁰` is the payload.

## The argument

Kernels do not commute with `⊗` — but **cokernels always do**, by right exactness. So the fibre
dimension of the cokernel is computable from the two rank–nullity identities

* `dim coker(u ⊗ κ) + dim range(u ⊗ κ) = dim (κ ⊗ K₁)`,
* `dim range(u ⊗ κ) + dim ker(u ⊗ κ) = dim (κ ⊗ K₀)`,

which give `dim coker(u ⊗ κ(p)) + rk_p K₀ = rk_p K₁ + n`. Both `p ↦ rk_p K₀` and `p ↦ rk_p K₁`
are locally constant (`Module.isLocallyConstant_rankAtStalk`, available because finite projective
modules are flat and finitely presented), hence so is `p ↦ dim coker(u ⊗ κ(p))`. Stacks [0FWG]
(`projective_of_isReduced_of_isLocallyConstant_finrank_fiber`) — the only place reducedness is
spent — then makes the cokernel projective.

Projectivity of the cokernel splits `0 → range u → K₁ → K₁ ⧸ range u → 0`, making `range u` a
direct summand of `K₁` and hence projective, which in turn splits
`0 → ker u → K₀ → range u → 0`; both splittings are packaged in
`Module.Projective.ker_of_projective_coker`.

Note that no *pointwise* inequality `rk_p K₀ ≤ rk_p K₁ + n` is asserted anywhere: the arithmetic
is done with the two additive identities and `omega`, never by rearranging `ℕ`-subtractions.
-/

universe u v

open Module
open scoped TensorProduct

namespace ModularCurves

section Cokernel

variable {R : Type u} [CommRing R] {K₀ K₁ : Type u}
  [AddCommGroup K₀] [Module R K₀] [AddCommGroup K₁] [Module R K₁]

/-- The range of `A ⊗ (range u ↪ K₁)` is the range of `u.baseChange A`: both are the image of
`A ⊗ K₀` in `A ⊗ K₁`, because `u` factors through its range by a surjection. This is
`LinearMap.lTensor_range` transported to the `A`-linear `AlgebraTensorModule` maps. -/
theorem range_lTensor_subtype_eq_range_baseChange (u : K₀ →ₗ[R] K₁) (A : Type v) [CommRing A]
    [Algebra R A] :
    LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor A A
        (((LinearMap.range u).subtype).restrictScalars R)) =
      LinearMap.range (u.baseChange A) := by
  apply SetLike.ext
  intro x
  change x ∈ LinearMap.range (LinearMap.lTensor A ((LinearMap.range u).subtype)) ↔
    x ∈ LinearMap.range (LinearMap.lTensor A u)
  rw [LinearMap.lTensor_range A (g := u)]

/-- **Cokernels commute with base change** (right exactness of `⊗`, no flatness needed): the
base change of `K₁ ⧸ range u` is the cokernel of `u.baseChange A`. -/
noncomputable def baseChangeQuotientRangeEquiv (u : K₀ →ₗ[R] K₁) (A : Type v) [CommRing A]
    [Algebra R A] :
    A ⊗[R] (K₁ ⧸ LinearMap.range u) ≃ₗ[A] (A ⊗[R] K₁) ⧸ LinearMap.range (u.baseChange A) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := R) A R A
      (LinearMap.range u)).trans
    (Submodule.quotEquivOfEq _ _ (range_lTensor_subtype_eq_range_baseChange u A))

/-- **Rank–nullity for a fibre**, in the `ℕ`-subtraction-free additive form: the cokernel
dimension is `dim (κ ⊗ K₁) + dim ker - dim (κ ⊗ K₀)`, written as an equality of sums so that no
`ℕ`-subtraction has to be justified. It is the sum of the two rank–nullity identities for
`u.baseChange κ`, the one for its range/kernel and the one for its range/cokernel. -/
theorem finrank_quotient_range_baseChange_add [Module.Finite R K₀] [Module.Finite R K₁]
    (u : K₀ →ₗ[R] K₁) (κ : Type u) [Field κ] [Algebra R κ] :
    finrank κ ((κ ⊗[R] K₁) ⧸ LinearMap.range (u.baseChange κ)) + finrank κ (κ ⊗[R] K₀) =
      finrank κ (κ ⊗[R] K₁) + finrank κ (LinearMap.ker (u.baseChange κ)) := by
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range (u.baseChange κ))
  have hker := LinearMap.finrank_range_add_finrank_ker (u.baseChange κ)
  omega

end Cokernel

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {K₀ K₁ : Type u}
  [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
  [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]

omit [IsNoetherianRing R] in
/-- `Module.rankAtStalk_eq` with the fibre spelled out as `κ(p) ⊗[R] M`, which is the form in
which `projective_of_isReduced_of_isLocallyConstant_finrank_fiber` takes its hypothesis. -/
theorem rankAtStalk_eq_finrank_residueField_tensor (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (p : PrimeSpectrum R) :
    rankAtStalk (R := R) M p =
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) :=
  Module.rankAtStalk_eq p

/-- With the fibre kernel dimension constant equal to `n`, the fibre dimension of the cokernel is
`rk_p K₁ + n - rk_p K₀`, hence locally constant. -/
theorem isLocallyConstant_finrank_fiber_quotient_range (u : K₀ →ₗ[R] K₁) (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, finrank p.asIdeal.ResidueField
      (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = n) :
    IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] (K₁ ⧸ LinearMap.range u)) := by
  haveI : Module.FinitePresentation R K₀ := Module.finitePresentation_of_finite R K₀
  haveI : Module.FinitePresentation R K₁ := Module.finitePresentation_of_finite R K₁
  have hfun : (fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (K₁ ⧸ LinearMap.range u))) =
      fun p : PrimeSpectrum R =>
        rankAtStalk (R := R) K₁ p + n - rankAtStalk (R := R) K₀ p := by
    funext p
    have hcoker := (baseChangeQuotientRangeEquiv u p.asIdeal.ResidueField).finrank_eq
    have hrank := finrank_quotient_range_baseChange_add u p.asIdeal.ResidueField
    rw [h p] at hrank
    rw [rankAtStalk_eq_finrank_residueField_tensor K₀ p,
      rankAtStalk_eq_finrank_residueField_tensor K₁ p]
    omega
  rw [hfun]
  exact (Module.isLocallyConstant_rankAtStalk (M := K₁)).comp₂
    (Module.isLocallyConstant_rankAtStalk (M := K₀)) fun a b => a + n - b

end Noetherian

section Reduced

variable {R : Type u} [CommRing R] [IsReduced R] [IsNoetherianRing R] {K₀ K₁ : Type u}
  [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
  [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]

/-- **(A)** Over a reduced Noetherian ring, a map of finite projective modules whose fibre kernels
all have dimension `n` has **projective cokernel**.

Cokernels commute with base change, so the fibre dimension of `K₁ ⧸ range u` is
`rk_p K₁ + n - rk_p K₀`, which is locally constant; Stacks [0FWG] applies. -/
theorem projective_quotient_range_of_constant_finrank_ker_baseChange (u : K₀ →ₗ[R] K₁) (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, finrank p.asIdeal.ResidueField
      (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = n) :
    Module.Projective R (K₁ ⧸ LinearMap.range u) :=
  projective_of_isReduced_of_isLocallyConstant_finrank_fiber
    (isLocallyConstant_finrank_fiber_quotient_range u n h)

/-- **(B)** Over a reduced Noetherian ring, a map of finite projective modules whose fibre kernels
all have dimension `n` has **projective kernel**.

The projective cokernel of (A) splits `K₁` as `range u ⊕ (K₁ ⧸ range u)`, so `range u` is
projective, which splits `K₀` as `ker u ⊕ range u`. -/
theorem projective_ker_of_constant_finrank_ker_baseChange (u : K₀ →ₗ[R] K₁) (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, finrank p.asIdeal.ResidueField
      (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = n) :
    Module.Projective R (LinearMap.ker u) := by
  haveI := projective_quotient_range_of_constant_finrank_ker_baseChange u n h
  exact Module.Projective.ker_of_projective_coker u

omit [IsReduced R] [Module.Projective R K₀] [Module.Finite R K₁] [Module.Projective R K₁] in
/-- **(C)** The kernel is finite. Together with (B) this says `ker u` is finite projective.

The fibre hypothesis is retained so that (B) and (C) share a signature; it is not consumed,
since a submodule of a finite module over a Noetherian ring is already finite. -/
theorem finite_ker_of_constant_finrank_ker_baseChange (u : K₀ →ₗ[R] K₁) (n : ℕ)
    (_h : ∀ p : PrimeSpectrum R, finrank p.asIdeal.ResidueField
      (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = n) :
    Module.Finite R (LinearMap.ker u) :=
  inferInstance

end Reduced

end ModularCurves
