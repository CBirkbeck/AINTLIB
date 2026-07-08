/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Base change of kernels and cokernels of linear maps

The module-theoretic core of cohomology-and-base-change for a relative curve
(AINTLIB ModularCurves COH-1 = GME Lemma 1.10.4 / Corollary 1.10.5, via the
Grothendieck-complex route of Mumford, *Abelian Varieties* §5, which is the source Hida
cites for the lemma — "[ALG] III.12.10"). For a relative curve the Grothendieck complex
has amplitude `[0,1]`, i.e. it is a single map `d : P →ₗ[R] Q` of finite projective
modules with `T⁰(M) = ker (d.lTensor M)` and `T¹(M) = coker (d.lTensor M)`; every
statement here is about such a map, in the maximal module-theoretic generality.

* `range_lTensor_range_subtype`: `T¹` commutes with base change, in the form
  identifying `range (d.lTensor M)` with the image of `(range d) ⊗ M`; combined with
  mathlib's `TensorProduct.tensorQuotientEquiv` this is Hida's "`T₁(𝓕) = T₁(O_S) ⊗ 𝓕`"
  (GME p. 82).
* `Module.subsingleton_of_forall_field_tensor_subsingleton`: a finitely generated
  module all of whose fibres at `R`-fields vanish is zero (GME p. 107, the step
  "`(R¹f_*𝓛) ⊗ k(s) = 0` for all geometric points `s` ⟹ `R¹f_*𝓛 = 0`"). The finiteness
  hypothesis is necessary: `ℚ/ℤ` over `ℤ` has vanishing fibres at every `ℤ`-field.
* `Module.Flat.lTensor_subtype_injective_of_flat_quotient` (purity): a submodule with
  flat quotient stays injected after any base change (Tor-free form of the mechanism in
  Mumford §5 Lemma 2 / Stacks 00HL).
* `Module.Flat.of_flat_quotient`: a submodule of a flat module with flat quotient is
  flat (Mumford p. 49, "it is easy to see that all the modules `Z^p` are flat too").
* `kerLTensorComparison_bijective`: kernels commute with base change when the cokernel
  is flat — Hida's "`T₁` exact ⟹ `T₀` is also exact" (GME p. 82) and Lemma 1.10.4(ii).
* `LinearMap.fg_ker_of_finite` / `Module.Projective.ker_of_flat_coker`: the kernel is
  finite projective (= locally free) — GME Corollary 1.10.5, "if `R¹f_*𝓛` is locally
  `O_S`-free, then `f_*𝓛` is also locally `O_S`-free".
* `kerBaseChangeComparison_bijective`: the `A`-linear fibre identification
  `A ⊗[R] ker d ≃ ker (d.baseChange A)` — the shape "(`f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))`"
  consumed at GME (2.15) and (2.17).

Decomposition, verbatim source quotes and adversarial attack logs:
`.mathlib-quality/decomposition-pic-coh.md` (stream v10.11, worker fable-PIC0).
Upstream candidates throughout.
-/

open TensorProduct

universe u v

namespace ModularCurves

variable {R : Type u} [CommRing R]
variable {P : Type*} {Q : Type*} [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module R Q]

section CokerBaseChange

variable (M : Type*) [AddCommGroup M] [Module R M] (f : P →ₗ[R] Q)

/-- **Cokernel base change** (GME p. 82: "`T₁(𝓕) = T₁(O_S) ⊗_{O_S} 𝓕`", top-degree
right-exactness; Mumford §5 p. 49). The range of `f.lTensor M` agrees with the image of
`(range f) ⊗ M`, so that `TensorProduct.tensorQuotientEquiv` identifies
`M ⊗ (Q ⧸ range f)` with `(M ⊗ Q) ⧸ range (f.lTensor M)`. -/
theorem range_lTensor_range_subtype :
    LinearMap.range (f.lTensor M) =
      LinearMap.range ((LinearMap.range f).subtype.lTensor M) := by
  sorry

end CokerBaseChange

/-- **Fibrewise vanishing detects vanishing** (GME p. 107: "Since
`(R¹f_*𝓛) ⊗ k(s) ≅ H¹(E_s, 𝓛(s)) = 0` for all geometric points `s ∈ S`, we know that
`R¹f_*𝓛 = 0`"). A finitely generated module whose base change to every `R`-field is
trivial is trivial. Finiteness is necessary: over `ℤ`, the module `ℚ/ℤ` is divisible
and torsion, so `K ⊗ ℚ/ℤ = 0` for every `ℤ`-field `K`, yet `ℚ/ℤ ≠ 0`. -/
theorem Module.subsingleton_of_forall_field_tensor_subsingleton
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Subsingleton (K ⊗[R] N)) :
    Subsingleton N := by
  sorry

section Purity

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Purity of a submodule with flat quotient** (the mechanism of Mumford §5 Lemma 2;
Stacks 00HL; `Tor₁(Q/N, M) = 0` in Tor-free form): if `Q ⧸ N` is flat, then
`N ⊗ M → Q ⊗ M` is injective for every `M`. -/
theorem Module.Flat.lTensor_subtype_injective_of_flat_quotient
    (N : Submodule R Q) [Module.Flat R (Q ⧸ N)] :
    Function.Injective (N.subtype.lTensor M) := by
  sorry

/-- **Two-out-of-three for flatness** (Mumford §5 p. 49: "it is easy to see that all
the modules `Z^p = Ker(L^p → L^{p+1})` are flat too"): a submodule of a flat module
with flat quotient is flat. -/
theorem Module.Flat.of_flat_quotient
    (N : Submodule R Q) [Module.Flat R Q] [Module.Flat R (Q ⧸ N)] :
    Module.Flat R N := by
  sorry

end Purity

section KerBaseChange

variable (M : Type*) [AddCommGroup M] [Module R M] (f : P →ₗ[R] Q)

/-- The canonical comparison map `M ⊗ ker f → ker (f.lTensor M)`, the length-one case
of Hida's `ι : T_i(O_S) ⊗ 𝓕 → T_i(𝓕)` (GME p. 79). It is bijective when `coker f` is
flat (`kerLTensorComparison_bijective`); it need not be otherwise. -/
noncomputable def kerLTensorComparison :
    M ⊗[R] (LinearMap.ker f) →ₗ[R] LinearMap.ker (f.lTensor M) :=
  LinearMap.codRestrict _ ((LinearMap.ker f).subtype.lTensor M) fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [LinearMap.mem_ker.mp k.2]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]

@[simp]
theorem kerLTensorComparison_apply_coe (x : M ⊗[R] (LinearMap.ker f)) :
    (kerLTensorComparison M f x).1 = (LinearMap.ker f).subtype.lTensor M x :=
  rfl

/-- **Kernel base change under flat cokernel** (GME p. 82: "`T₁` is an exact functor if
`R¹f_*𝓛 = T₁(O_S)` is locally-free. In this case, `T₀` is also exact."; GME Lemma
1.10.4(ii); Mumford §5 Cor. 2's mechanism). If `Q` is flat and `Q ⧸ range f` is flat,
the canonical map `M ⊗ ker f → ker (f.lTensor M)` is bijective for every `M`. -/
theorem kerLTensorComparison_bijective
    [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Function.Bijective (kerLTensorComparison M f) := by
  sorry

end KerBaseChange

section KerFiniteProjective

variable (f : P →ₗ[R] Q)

/-- Over a noetherian ring, the kernel of a map out of a finite module is finite
(GME Cor 1.10.5 bookkeeping; submodule of a noetherian module). -/
theorem LinearMap.fg_ker_of_finite [IsNoetherianRing R] [Module.Finite R P] :
    (LinearMap.ker f).FG := by
  sorry

/-- **The kernel is projective** (GME Corollary 1.10.5: "If `R¹f_*𝓛` is locally
`O_S`-free, then `f_*𝓛` is also locally `O_S`-free"; cf. Mumford p. 49: "`K⁰` is
`A`-projective, since it is `A`-flat and finitely generated over a noetherian `A`").
Over a noetherian ring, if `P` is projective, `Q` is finite flat and `Q ⧸ range f` is
flat, then `ker f` is a projective module. -/
theorem Module.Projective.ker_of_flat_coker [IsNoetherianRing R]
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Module.Projective R (LinearMap.ker f) := by
  sorry

end KerFiniteProjective

section BaseChangeAlgebra

variable (A : Type*) [CommRing A] [Algebra R A] (f : P →ₗ[R] Q)

/-- The `A`-linear comparison map `A ⊗[R] ker f → ker (f.baseChange A)`; the
algebra-base-change form of `kerLTensorComparison`, in the shape
"`(f_*𝓛) ⊗_{O_S} k(s) → f_*(𝓛(s))`" of GME (2.15) and (2.17). -/
noncomputable def kerBaseChangeComparison :
    A ⊗[R] (LinearMap.ker f) →ₗ[A] LinearMap.ker (f.baseChange A) :=
  LinearMap.codRestrict _ ((LinearMap.ker f).subtype.baseChange A) fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [LinearMap.mem_ker.mp k.2]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- **Fibre identification** (GME p. 107: "Again by Lemma 1.10.4, we know `f_*𝓛` is
locally free and `(f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))`"): for an `R`-algebra `A`, if `Q` and
`Q ⧸ range f` are flat then `A ⊗[R] ker f → ker (f.baseChange A)` is bijective. -/
theorem kerBaseChangeComparison_bijective
    [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Function.Bijective (kerBaseChangeComparison A f) := by
  sorry

end BaseChangeAlgebra

end ModularCurves
