/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
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
  have h : (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f :=
    LinearMap.subtype_comp_codRestrict _ _ _
  conv_lhs => rw [← h, LinearMap.lTensor_comp]
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr
    (LinearMap.lTensor_surjective M f.surjective_rangeRestrict), Submodule.map_top]

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
  rw [← Module.support_eq_empty_iff (R := R)]
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  exact not_subsingleton_iff_nontrivial.mpr hp (h p.asIdeal.ResidueField)

section Purity

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Purity of a submodule with flat quotient** (the mechanism of Mumford §5 Lemma 2;
Stacks 00HL; `Tor₁(Q/N, M) = 0` in Tor-free form): if `Q ⧸ N` is flat, then
`N ⊗ M → Q ⊗ M` is injective for every `M`. -/
theorem Module.Flat.lTensor_subtype_injective_of_flat_quotient
    (N : Submodule R Q) [Module.Flat R (Q ⧸ N)] :
    Function.Injective (N.subtype.lTensor M) :=
  LinearMap.lTensor_injective_of_exact_of_flat N.mkQ (Submodule.mkQ_surjective N)
    N.subtype N.injective_subtype (LinearMap.exact_subtype_mkQ N) M

/-- **Two-out-of-three for flatness** (Mumford §5 p. 49: "it is easy to see that all
the modules `Z^p = Ker(L^p → L^{p+1})` are flat too"): a submodule of a flat module
with flat quotient is flat. -/
theorem Module.Flat.of_flat_quotient
    (N : Submodule R Q) [Module.Flat R Q] [Module.Flat R (Q ⧸ N)] :
    Module.Flat R N := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hsquare : (N.subtype.rTensor R).comp (I.subtype.lTensor N)
      = (I.subtype.lTensor Q).comp (N.subtype.rTensor I) :=
    TensorProduct.ext' fun n i => rfl
  have h2 : Function.Injective (I.subtype.lTensor Q) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype
  have h1 : Function.Injective (N.subtype.rTensor I) := by
    have hA3 : Function.Injective (N.subtype.lTensor I) :=
      Module.Flat.lTensor_subtype_injective_of_flat_quotient I N
    have hconj : (TensorProduct.comm R I Q).toLinearMap.comp
        ((N.subtype.lTensor I).comp (TensorProduct.comm R N I).toLinearMap)
        = N.subtype.rTensor I :=
      TensorProduct.ext' fun n i => by simp
    rw [← hconj]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact (TensorProduct.comm R I Q).injective.comp
      (hA3.comp (TensorProduct.comm R N I).injective)
  have hcomp : Function.Injective ((N.subtype.rTensor R).comp (I.subtype.lTensor N)) := by
    rw [hsquare, LinearMap.coe_comp]
    exact h2.comp h1
  rw [LinearMap.coe_comp] at hcomp
  exact hcomp.of_comp

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
  haveI him : Module.Flat R (LinearMap.range f) := Module.Flat.of_flat_quotient _
  have hexact2 : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hkerinj : Function.Injective ((LinearMap.ker f).subtype.lTensor M) :=
    LinearMap.lTensor_injective_of_exact_of_flat f.rangeRestrict
      f.surjective_rangeRestrict _ (LinearMap.ker f).injective_subtype hexact2 M
  constructor
  · intro a b hab
    exact hkerinj (congrArg Subtype.val hab)
  · rintro ⟨z, hz⟩
    rw [LinearMap.mem_ker] at hz
    have hfact : f.lTensor M
        = ((LinearMap.range f).subtype.lTensor M).comp (f.rangeRestrict.lTensor M) := by
      rw [← LinearMap.lTensor_comp, LinearMap.subtype_comp_codRestrict]
    have hsubinj : Function.Injective ((LinearMap.range f).subtype.lTensor M) :=
      Module.Flat.lTensor_subtype_injective_of_flat_quotient M (LinearMap.range f)
    have h0 : (f.rangeRestrict.lTensor M) z = 0 := by
      apply hsubinj
      rw [map_zero, ← LinearMap.comp_apply, ← hfact]
      exact hz
    have hex : Function.Exact ((LinearMap.ker f).subtype.lTensor M)
        (f.rangeRestrict.lTensor M) :=
      lTensor_exact M hexact2 f.surjective_rangeRestrict
    obtain ⟨w, hw⟩ := (hex z).mp h0
    exact ⟨w, Subtype.ext hw⟩

end KerBaseChange

section KerFiniteProjective

variable (f : P →ₗ[R] Q)

/-- Over a noetherian ring, the kernel of a map out of a finite module is finite
(GME Cor 1.10.5 bookkeeping; submodule of a noetherian module). -/
theorem LinearMap.fg_ker_of_finite [IsNoetherianRing R] [Module.Finite R P] :
    (LinearMap.ker f).FG :=
  IsNoetherian.noetherian _

/-- **The kernel is projective** (GME Corollary 1.10.5: "If `R¹f_*𝓛` is locally
`O_S`-free, then `f_*𝓛` is also locally `O_S`-free"; cf. Mumford p. 49: "`K⁰` is
`A`-projective, since it is `A`-flat and finitely generated over a noetherian `A`").
Over a noetherian ring, if `P` is projective, `Q` is finite flat and `Q ⧸ range f` is
flat, then `ker f` is a projective module. -/
theorem Module.Projective.ker_of_flat_coker [IsNoetherianRing R]
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Module.Projective R (LinearMap.ker f) := by
  haveI him_flat : Module.Flat R (LinearMap.range f) := Module.Flat.of_flat_quotient _
  haveI him_fin : Module.Finite R (LinearMap.range f) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  haveI him_fp : Module.FinitePresentation R (LinearMap.range f) :=
    Module.finitePresentation_of_finite R _
  haveI him_proj : Module.Projective R (LinearMap.range f) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  have hfs : ∀ y : LinearMap.range f, f (s y) = y := fun y =>
    congrArg Subtype.val (LinearMap.ext_iff.mp hs y)
  refine Module.Projective.of_split (LinearMap.ker f).subtype
    (LinearMap.codRestrict _ (LinearMap.id - s.comp f.rangeRestrict) fun x => ?_) ?_
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
      LinearMap.comp_apply, hfs (f.rangeRestrict x)]
    exact sub_self _
  · ext x
    have hx0 : f.rangeRestrict (x : P) = 0 :=
      Subtype.ext (LinearMap.mem_ker.mp x.2)
    simp [LinearMap.codRestrict_apply, hx0]

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
  have hlt := kerLTensorComparison_bijective (M := A) f
  constructor
  · intro a b hab
    have h1 : ((LinearMap.ker f).subtype.baseChange A) a
        = ((LinearMap.ker f).subtype.baseChange A) b := congrArg Subtype.val hab
    rw [LinearMap.baseChange_eq_ltensor] at h1
    exact hlt.1 (Subtype.ext h1)
  · rintro ⟨z, hz⟩
    rw [LinearMap.mem_ker] at hz
    have hz' : (f.lTensor A) z = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      exact hz
    obtain ⟨w, hw⟩ := hlt.2 ⟨z, LinearMap.mem_ker.mpr hz'⟩
    refine ⟨w, Subtype.ext ?_⟩
    show ((LinearMap.ker f).subtype.baseChange A) w = z
    rw [LinearMap.baseChange_eq_ltensor]
    exact congrArg Subtype.val hw

end BaseChangeAlgebra

end ModularCurves
