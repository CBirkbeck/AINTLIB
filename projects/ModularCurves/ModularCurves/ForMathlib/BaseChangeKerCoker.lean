/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support

/-!
# Base change of kernels and cokernels of linear maps

The module-theoretic core of cohomology-and-base-change for a relative curve
(AINTLIB ModularCurves COH-1 = GME Lemma 1.10.4 / Corollary 1.10.5, via the
Grothendieck-complex route of Mumford, *Abelian Varieties* §5, which is the source Hida
cites for the lemma — "[ALG] III.12.10"). For a relative curve the Grothendieck complex
has amplitude `[0,1]`, i.e. it is a single map `d : P →ₗ[R] Q` of finite projective
modules with `T⁰(M) = ker (d.lTensor M)` and `T¹(M) = coker (d.lTensor M)`; every
statement here is about such a map, in the maximal module-theoretic generality.

* `T¹` commutes with base change — Hida's "`T₁(𝓕) = T₁(O_S) ⊗ 𝓕`" (GME p. 82) — is
  mathlib's `LinearMap.lTensor_range` combined with `TensorProduct.tensorQuotientEquiv`
  (no project declaration needed; recorded here for consumers of the COH-1 interface).
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
* `Module.Projective.ker_of_flat_coker`: the kernel is projective (with finiteness via
  `IsNoetherian.noetherian`, it is finite projective = locally free) — GME Corollary
  1.10.5, "if `R¹f_*𝓛` is locally `O_S`-free, then `f_*𝓛` is also locally `O_S`-free".
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

/-- **Fibrewise vanishing detects vanishing** (GME p. 107: "Since
`(R¹f_*𝓛) ⊗ k(s) ≅ H¹(E_s, 𝓛(s)) = 0` for all geometric points `s ∈ S`, we know that
`R¹f_*𝓛 = 0`"). A finitely generated module whose base change to every `R`-field is
trivial is trivial. Finiteness is necessary: over `ℤ`, the module `ℚ/ℤ` is divisible
and torsion, so `K ⊗ ℚ/ℤ = 0` for every `ℤ`-field `K`, yet `ℚ/ℤ ≠ 0`. -/
theorem Module.subsingleton_of_forall_field_tensor_subsingleton
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Subsingleton (K ⊗[R] N)) :
    Subsingleton N :=
  Module.support_eq_empty_iff.mp <| Set.eq_empty_of_forall_notMem fun p ↦
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).not.mpr <|
      not_nontrivial_iff_subsingleton.mpr (h p.asIdeal.ResidueField)

section Purity

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Purity of a submodule with flat quotient** (the mechanism of Mumford §5 Lemma 2;
Stacks 00HL; `Tor₁(Q/N, M) = 0` in Tor-free form): if `Q ⧸ N` is flat, then
`N ⊗ M → Q ⊗ M` is injective for every `M`. -/
theorem Module.Flat.lTensor_subtype_injective_of_flat_quotient
    (N : Submodule R Q) [Module.Flat R (Q ⧸ N)] :
    Function.Injective (N.subtype.lTensor M) :=
  N.mkQ.lTensor_injective_of_exact_of_flat N.mkQ_surjective N.subtype N.injective_subtype
    (LinearMap.exact_subtype_mkQ N) M

/-- **Two-out-of-three for flatness** (Mumford §5 p. 49: "it is easy to see that all
the modules `Z^p = Ker(L^p → L^{p+1})` are flat too"): a submodule of a flat module
with flat quotient is flat. -/
theorem Module.Flat.of_flat_quotient
    (N : Submodule R Q) [Module.Flat R Q] [Module.Flat R (Q ⧸ N)] :
    Module.Flat R N := by
  refine Module.Flat.iff_rTensor_injective'.mpr fun I ↦ .of_comp (f := ⇑(N.subtype.lTensor R)) ?_
  rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype).comp
    (Module.Flat.lTensor_subtype_injective_of_flat_quotient I N)

end Purity

section KerBaseChange

variable (M : Type*) [AddCommGroup M] [Module R M] (f : P →ₗ[R] Q)

/-- The canonical comparison map `M ⊗ ker f → ker (f.lTensor M)`, the length-one case
of Hida's `ι : T_i(O_S) ⊗ 𝓕 → T_i(𝓕)` (GME p. 79). It is bijective when `coker f` is
flat (`kerLTensorComparison_bijective`); it need not be otherwise. -/
noncomputable def kerLTensorComparison :
    M ⊗[R] (LinearMap.ker f) →ₗ[R] LinearMap.ker (f.lTensor M) :=
  LinearMap.codRestrict _ ((LinearMap.ker f).subtype.lTensor M) fun x ↦ by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.comp_ker_subtype, LinearMap.lTensor_zero, LinearMap.zero_apply]

@[simp]
theorem kerLTensorComparison_coe (x : M ⊗[R] (LinearMap.ker f)) :
    (kerLTensorComparison M f x : M ⊗[R] P) = (LinearMap.ker f).subtype.lTensor M x :=
  rfl

/-- **Kernel base change under flat cokernel** (GME p. 82: "`T₁` is an exact functor if
`R¹f_*𝓛 = T₁(O_S)` is locally-free. In this case, `T₀` is also exact."; GME Lemma
1.10.4(ii); Mumford §5 Cor. 2's mechanism). If `Q` is flat and `Q ⧸ range f` is flat,
the canonical map `M ⊗ ker f → ker (f.lTensor M)` is bijective for every `M`. -/
theorem kerLTensorComparison_bijective
    [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Function.Bijective (kerLTensorComparison M f) := by
  have : Module.Flat R (LinearMap.range f) := Module.Flat.of_flat_quotient _
  have hexact : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  refine ⟨fun a b hab ↦ LinearMap.lTensor_injective_of_exact_of_flat f.rangeRestrict
    f.surjective_rangeRestrict _ (LinearMap.ker f).injective_subtype hexact M
    (congrArg Subtype.val hab), fun ⟨z, hz⟩ ↦ ?_⟩
  have h0 : f.rangeRestrict.lTensor M z = 0 :=
    Module.Flat.lTensor_subtype_injective_of_flat_quotient M (LinearMap.range f) <| by
      rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        LinearMap.subtype_comp_codRestrict]
  exact ((lTensor_exact M hexact f.surjective_rangeRestrict z).mp h0).imp fun _ ↦ Subtype.ext

private noncomputable def sectionOfSurjective [Module.Projective R Q]
    (hf : Function.Surjective f) : Q →ₗ[R] P :=
  (Module.projective_lifting_property f .id hf).choose

private lemma comp_sectionOfSurjective [Module.Projective R Q]
    (hf : Function.Surjective f) :
    f ∘ₗ sectionOfSurjective f hf = .id :=
  (Module.projective_lifting_property f .id hf).choose_spec

private noncomputable def kerRetractionOfSurjective [Module.Projective R Q]
    (hf : Function.Surjective f) : P →ₗ[R] LinearMap.ker f :=
  LinearMap.codRestrict _ (.id - sectionOfSurjective f hf ∘ₗ f) fun x ↦ by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    have h := DFunLike.congr_fun (comp_sectionOfSurjective f hf) (f x)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr h.symm

private lemma kerRetractionOfSurjective_comp_subtype [Module.Projective R Q]
    (hf : Function.Surjective f) :
    kerRetractionOfSurjective f hf ∘ₗ (LinearMap.ker f).subtype = .id := by
  ext x
  simp [kerRetractionOfSurjective, LinearMap.mem_ker.mp x.property]

/-- The kernel of a surjection between projective modules is projective, over an arbitrary
base ring. -/
theorem Module.Projective.ker_of_surjective [Module.Projective R P]
    [Module.Projective R Q] (hf : Function.Surjective f) :
    Module.Projective R (LinearMap.ker f) :=
  .of_split (LinearMap.ker f).subtype (kerRetractionOfSurjective f hf)
    (kerRetractionOfSurjective_comp_subtype f hf)

/-- The kernel of a surjection from a finite module onto a projective module is finite. -/
theorem Module.Finite.ker_of_surjective_of_projective [Module.Finite R P]
    [Module.Projective R Q] (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) :=
  .of_surjective (kerRetractionOfSurjective f hf) fun x ↦
    ⟨x, DFunLike.congr_fun (kerRetractionOfSurjective_comp_subtype f hf) x⟩

end KerBaseChange

/-- **The kernel is projective** (GME Corollary 1.10.5: "If `R¹f_*𝓛` is locally
`O_S`-free, then `f_*𝓛` is also locally `O_S`-free"; cf. Mumford p. 49: "`K⁰` is
`A`-projective, since it is `A`-flat and finitely generated over a noetherian `A`").
Over a noetherian ring, if `P` is projective, `Q` is finite flat and `Q ⧸ range f` is
flat, then `ker f` is a projective module. -/
theorem Module.Projective.ker_of_flat_coker (f : P →ₗ[R] Q) [IsNoetherianRing R]
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Module.Projective R (LinearMap.ker f) := by
  have : Module.Flat R (LinearMap.range f) := Module.Flat.of_flat_quotient _
  have : Module.FinitePresentation R (LinearMap.range f) := Module.finitePresentation_of_finite R _
  have : Module.Projective R (LinearMap.range f) := Module.Flat.projective_of_finitePresentation
  rw [← LinearMap.ker_rangeRestrict]
  obtain ⟨l, hl⟩ := (((LinearMap.exact_subtype_ker_map f.rangeRestrict).split_tfae
    Subtype.val_injective f.surjective_rangeRestrict).out 0 1).mp
    (Module.projective_lifting_property _ _ f.surjective_rangeRestrict)
  exact .of_split _ _ hl

section BaseChangeAlgebra

variable (A : Type*) [CommRing A] [Algebra R A] (f : P →ₗ[R] Q)

/-- The `A`-linear comparison map `A ⊗[R] ker f → ker (f.baseChange A)`; the
algebra-base-change form of `kerLTensorComparison`, in the shape
"`(f_*𝓛) ⊗_{O_S} k(s) → f_*(𝓛(s))`" of GME (2.15) and (2.17). Mathlib's heterobasic
`LinearMap.tensorKer A A f` inhabits the same type; this `codRestrict` form is kept for
its `rfl` coe (`kerBaseChangeComparison_coe`) — when upstreaming, contribute
`kerBaseChangeComparison_bijective` as API for `tensorKer` instead. -/
noncomputable def kerBaseChangeComparison :
    A ⊗[R] (LinearMap.ker f) →ₗ[A] LinearMap.ker (f.baseChange A) :=
  LinearMap.codRestrict _ ((LinearMap.ker f).subtype.baseChange A) fun x ↦ by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]

@[simp]
theorem kerBaseChangeComparison_coe (x : A ⊗[R] (LinearMap.ker f)) :
    (kerBaseChangeComparison A f x : A ⊗[R] P) = (LinearMap.ker f).subtype.baseChange A x :=
  rfl

/-- **Fibre identification** (GME p. 107: "Again by Lemma 1.10.4, we know `f_*𝓛` is
locally free and `(f_*𝓛) ⊗ k(s) ≅ f_*(𝓛(s))`"): for an `R`-algebra `A`, if `Q` and
`Q ⧸ range f` are flat then `A ⊗[R] ker f → ker (f.baseChange A)` is bijective. -/
theorem kerBaseChangeComparison_bijective
    [Module.Flat R Q] [Module.Flat R (Q ⧸ LinearMap.range f)] :
    Function.Bijective (kerBaseChangeComparison A f) :=
  -- proof-by-defeq: `f.baseChange A ≡ f.lTensor A` (`LinearMap.baseChange_eq_ltensor` is
  -- `rfl`); if a mathlib bump breaks this, transport along that lemma with
  -- `congrArg Subtype.val` / `Subtype.ext` in each direction.
  kerLTensorComparison_bijective A f

/-- If the differential is surjective and its target is projective, its kernel commutes with
every algebra base change. This is the arbitrary-base endpoint used when a length-one
Grothendieck complex has vanishing degree-one cohomology. -/
theorem kerBaseChangeComparison_bijective_of_surjective [Module.Projective R Q]
    (hf : Function.Surjective f) :
    Function.Bijective (kerBaseChangeComparison A f) := by
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  haveI : Subsingleton (Q ⧸ LinearMap.range f) := by
    rw [hrange]
    infer_instance
  exact kerBaseChangeComparison_bijective A f

end BaseChangeAlgebra

end ModularCurves
