/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
* `LinearMap.exists_away_baseChange_surjective_of_residueField`: if a differential with
  finite target is surjective after tensoring with `κ(p)`, it is surjective after
  inverting one element outside `p`.
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
* `LinearMap.baseChange_exact_of_bounded_exact`: arbitrary algebra base change preserves a
  bounded exact complex of flat modules (the algebraic content of Mumford §5, Lemma 2).
* `LinearMap.exact_of_bounded_forall_field_baseChange_exact`: a bounded complex of
  finite projective modules that is exact over every field fibre is exact over the base.
* `LinearMap.exact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology`:
  the same conclusion for a bounded complex of flat modules whose explicit homology
  modules are finite.
* `kerBaseChangeComparison_bijective_of_bounded_forall_field_baseChange_exact`: its
  degree-zero kernel is finite projective and commutes with arbitrary algebra base change.
* `Module.rankAtStalk_ker_eq_of_bounded_forall_field_baseChange_exact`: if the degree-zero
  kernels on residue fibres all have dimension `r`, then the degree-zero kernel over the base
  has constant rank `r`.
* `LinearMap.exists_away_finiteProjective_ker_of_residueField_surjective`: the local
  finite-projective kernel and arbitrary further-base-change endpoint obtained by
  combining the preceding principal-neighbourhood theorem with a two-term complex.

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

/-- A binary product of flat modules is flat. -/
theorem Module.Flat.prod
    {M : Type v} {N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  apply Function.Injective.of_comp
    (f := TensorProduct.prodRight R R Q M N)
  change Function.Injective ⇑((TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ
    f.rTensor (M × N))
  have hcomp :
      (TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ f.rTensor (M × N) =
        (f.rTensor M).prodMap (f.rTensor N) ∘ₗ
          (TensorProduct.prodRight R R P M N).toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    rintro ⟨m, n⟩
    simp
  rw [hcomp, LinearMap.coe_comp]
  exact (Function.Injective.prodMap
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)).comp
      (TensorProduct.prodRight R R P M N).injective

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

section BoundedFlatComplex

variable (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (d : ∀ n, M n →ₗ[R] M (n + 1))

/-- In a bounded exact sequence of flat modules, every cokernel is flat. This is the
backwards induction used for a bounded flat Cech complex: the terminal cokernel is zero,
and exactness identifies each preceding cokernel with the range of the next differential. -/
theorem Module.Flat.quotient_range_of_bounded_exact [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1)))
    (n : ℕ) (hn : n ≤ N) :
    Module.Flat R (M (n + 1) ⧸ LinearMap.range (d n)) := by
  induction hn using Nat.decreasingInduction with
  | self => infer_instance
  | @of_succ k hk ih =>
      letI : Module.Flat R (M (k + 2) ⧸ LinearMap.range (d (k + 1))) := ih
      letI : Module.Flat R (LinearMap.range (d (k + 1))) :=
        Module.Flat.of_flat_quotient _
      exact Module.Flat.of_linearEquiv
        (Submodule.quotEquivOfEq (LinearMap.range (d k)) (LinearMap.ker (d (k + 1)))
            (LinearMap.exact_iff.mp (hexact k hk)).symm ≪≫ₗ
          LinearMap.quotKerEquivRange (d (k + 1)))

/-- Every cycle module in a bounded exact sequence of flat modules is flat. -/
theorem Module.Flat.ker_of_bounded_exact_at [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1)))
    (n : ℕ) (hn : n ≤ N) :
    Module.Flat R (LinearMap.ker (d n)) := by
  letI : Module.Flat R (M (n + 1) ⧸ LinearMap.range (d n)) :=
    Module.Flat.quotient_range_of_bounded_exact M d N hexact n hn
  letI : Module.Flat R (LinearMap.range (d n)) :=
    Module.Flat.of_flat_quotient _
  letI : Module.Flat R (M n ⧸ LinearMap.ker (d n)) :=
    Module.Flat.of_linearEquiv (LinearMap.quotKerEquivRange (d n))
  exact Module.Flat.of_flat_quotient _

/-- The degree-zero kernel of a bounded exact sequence of flat modules is flat. -/
theorem Module.Flat.ker_of_bounded_exact [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1))) :
    Module.Flat R (LinearMap.ker (d 0)) :=
  Module.Flat.ker_of_bounded_exact_at M d N hexact 0 (Nat.zero_le N)

/-- The cokernel in degree `k` is flat when a bounded complex of flat modules is exact
from degree `k` onward. No exactness in lower degrees is required. -/
theorem Module.Flat.quotient_range_of_bounded_exact_from [∀ n, Module.Flat R (M n)]
    (N k : ℕ) (hk : k ≤ N) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, k ≤ n → n < N → Function.Exact (d n) (d (n + 1))) :
    Module.Flat R (M (k + 1) ⧸ LinearMap.range (d k)) := by
  let M' : ℕ → Type v := fun n ↦ M (k + n)
  let d' : ∀ n, M' n →ₗ[R] M' (n + 1) := fun n ↦ d (k + n)
  have hterminal : Subsingleton (M' (N - k + 1)) := by
    dsimp only [M']
    have hindex : k + (N - k + 1) = N + 1 := by omega
    rw [hindex]
    infer_instance
  letI : Subsingleton (M' (N - k + 1)) := hterminal
  have hexact' : ∀ n, n < N - k → Function.Exact (d' n) (d' (n + 1)) := by
    intro n hn
    dsimp only [d']
    exact hexact (k + n) (by omega) (by omega)
  simpa only [M', d', Nat.add_zero] using
    Module.Flat.quotient_range_of_bounded_exact M' d' (N - k) hexact' 0
      (Nat.zero_le (N - k))

/-- The cycle module in degree `k` is flat when a bounded complex of flat modules is exact
from degree `k` onward. No exactness in lower degrees is required. -/
theorem Module.Flat.ker_of_bounded_exact_from [∀ n, Module.Flat R (M n)]
    (N k : ℕ) (hk : k ≤ N) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, k ≤ n → n < N → Function.Exact (d n) (d (n + 1))) :
    Module.Flat R (LinearMap.ker (d k)) := by
  letI : Module.Flat R (M (k + 1) ⧸ LinearMap.range (d k)) :=
    Module.Flat.quotient_range_of_bounded_exact_from M d N k hk hexact
  letI : Module.Flat R (LinearMap.range (d k)) :=
    Module.Flat.of_flat_quotient _
  letI : Module.Flat R (M k ⧸ LinearMap.ker (d k)) :=
    Module.Flat.of_linearEquiv (LinearMap.quotKerEquivRange (d k))
  exact Module.Flat.of_flat_quotient _

/-- A finite degree-zero cycle module in a bounded exact sequence of flat modules over a
Noetherian ring is projective. This is the finite-flat step in Mumford, *Abelian Varieties*,
§5, Lemma 1. -/
theorem Module.Projective.ker_of_bounded_exact_of_finite [IsNoetherianRing R]
    [∀ n, Module.Flat R (M n)] [Module.Finite R (LinearMap.ker (d 0))]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1))) :
    Module.Projective R (LinearMap.ker (d 0)) := by
  letI : Module.Flat R (LinearMap.ker (d 0)) :=
    Module.Flat.ker_of_bounded_exact M d N hexact
  letI : Module.FinitePresentation R (LinearMap.ker (d 0)) :=
    Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

/-- Kernels in degree zero commute with arbitrary tensor products for a bounded exact
sequence of flat modules. -/
theorem kerLTensorComparison_bijective_of_bounded_exact
    (A : Type*) [AddCommGroup A] [Module R A] [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1))) :
    Function.Bijective (kerLTensorComparison A (d 0)) := by
  letI : Module.Flat R (M 1 ⧸ LinearMap.range (d 0)) :=
    Module.Flat.quotient_range_of_bounded_exact M d N hexact 0 (Nat.zero_le N)
  exact kerLTensorComparison_bijective A (d 0)

end BoundedFlatComplex

private theorem baseChange_surjective_iff_subsingleton_coker
    (A : Type*) [CommRing A] [Algebra R A] (f : P →ₗ[R] Q) :
    Function.Surjective (f.baseChange A) ↔
      Subsingleton (A ⊗[R] (Q ⧸ LinearMap.range f)) := by
  have hexact : Function.Exact
      ((LinearMap.range f).subtype.baseChange A)
      ((LinearMap.range f).mkQ.baseChange A) :=
    lTensor_exact A (LinearMap.exact_subtype_mkQ (LinearMap.range f))
      (Submodule.mkQ_surjective (LinearMap.range f))
  have hquotSurj : Function.Surjective ((LinearMap.range f).mkQ.baseChange A) :=
    LinearMap.baseChange_surjective A (Submodule.mkQ_surjective (LinearMap.range f))
  have hquotKer :
      LinearMap.ker ((LinearMap.range f).mkQ.baseChange A) =
        (LinearMap.range f).baseChange A :=
    hexact.linearMap_ker_eq
  have hcoker :
      (LinearMap.range f).baseChange A = ⊤ ↔
        Subsingleton (A ⊗[R] (Q ⧸ LinearMap.range f)) := by
    rw [← hquotKer, ← Submodule.Quotient.subsingleton_iff]
    exact (((LinearMap.range f).mkQ.baseChange A).quotKerEquivOfSurjective
      hquotSurj).toEquiv.subsingleton_congr
  have hfac :
      f.baseChange A =
        ((LinearMap.range f).subtype.baseChange A) ∘ₗ
          (f.rangeRestrict.baseChange A) := by
    rw [← LinearMap.baseChange_comp]
    rfl
  have hrange :
      LinearMap.range (f.baseChange A) = (LinearMap.range f).baseChange A := by
    rw [hfac, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr
        (LinearMap.baseChange_surjective A (LinearMap.surjective_rangeRestrict f)),
      Submodule.map_top]
    rfl
  rw [← LinearMap.range_eq_top, hrange, hcoker]

/-- If a linear map with finite target is surjective on the residue fibre at a prime,
then it is surjective after restricting to a principal neighbourhood of that prime. -/
theorem LinearMap.exists_away_baseChange_surjective_of_residueField
    [Module.Finite R Q] (f : P →ₗ[R] Q) (p : Ideal R) [p.IsPrime]
    (h : Function.Surjective (f.baseChange p.ResidueField)) :
    ∃ r : R, r ∉ p ∧
      Function.Surjective (f.baseChange (Localization.Away r)) := by
  let C := Q ⧸ LinearMap.range f
  haveI : Module.Finite R C :=
    Module.Finite.of_surjective (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective (LinearMap.range f))
  have hκC : Subsingleton (p.ResidueField ⊗[R] C) :=
    (baseChange_surjective_iff_subsingleton_coker p.ResidueField f).mp h
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R C := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hκC
  haveI : Subsingleton (LocalizedModule p.primeCompl C) :=
    Module.notMem_support_iff.mp hp
  obtain ⟨r, hr, haway⟩ := LocalizedModule.exists_subsingleton_away (M := C) p
  have htensor : Subsingleton (Localization.Away r ⊗[R] C) :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers r) C).toEquiv.subsingleton_congr.mp
      haway
  exact ⟨r, hr, (baseChange_surjective_iff_subsingleton_coker
    (Localization.Away r) f).mpr htensor⟩

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

section Exactness

variable {T : Type*} [AddCommGroup T] [Module R T]

/-- The factorization of the first map of a complex through the kernel of the second. -/
def LinearMap.codRestrictToKer (f : P →ₗ[R] Q) (g : Q →ₗ[R] T)
    (h : g ∘ₗ f = 0) : P →ₗ[R] LinearMap.ker g :=
  LinearMap.codRestrict _ f fun x ↦ by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h, LinearMap.zero_apply]

@[simp]
theorem LinearMap.codRestrictToKer_coe (f : P →ₗ[R] Q) (g : Q →ₗ[R] T)
    (h : g ∘ₗ f = 0) (x : P) :
    (LinearMap.codRestrictToKer f g h x : Q) = f x :=
  rfl

/-- A complex is exact precisely when its first map surjects onto the kernel of its second. -/
theorem LinearMap.codRestrictToKer_surjective_iff_exact
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0) :
    Function.Surjective (LinearMap.codRestrictToKer f g h) ↔ Function.Exact f g := by
  rw [LinearMap.exact_iff]
  constructor
  · intro hsurj
    apply le_antisymm
    · intro q hq
      obtain ⟨p, hp⟩ := hsurj ⟨q, hq⟩
      exact ⟨p, congrArg Subtype.val hp⟩
    · intro q hq
      obtain ⟨p, rfl⟩ := hq
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h, LinearMap.zero_apply]
  · intro hexact q
    have hq : (q : Q) ∈ LinearMap.range f := by
      rw [← hexact]
      exact q.property
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

/-- If `A → B → C` is exact, `B` and `C` are flat, and the second map is
surjective, then the quotient of `A` by the kernel of the first map is flat. -/
theorem Module.Flat.quotient_ker_of_exact_surjective
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    [Module.Flat R B] [Module.Flat R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hexact : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Flat R (A ⧸ LinearMap.ker f) := by
  letI : Module.Flat R (B ⧸ LinearMap.ker g) :=
    Module.Flat.of_linearEquiv (g.quotKerEquivOfSurjective hg)
  letI : Module.Flat R (LinearMap.ker g) :=
    Module.Flat.of_flat_quotient (LinearMap.ker g)
  exact Module.Flat.of_linearEquiv
    ((LinearMap.quotKerEquivRange f).trans
      (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hexact).symm))

/-- Over a noetherian ring, the finite quotient supplied by an exact sequence ending in
a surjection of flat modules is projective. -/
theorem Module.Projective.quotient_ker_of_exact_surjective
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    [IsNoetherianRing R] [Module.Finite R A]
    [Module.Flat R B] [Module.Flat R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hexact : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective R (A ⧸ LinearMap.ker f) := by
  letI : Module.Flat R (A ⧸ LinearMap.ker f) :=
    Module.Flat.quotient_ker_of_exact_surjective f g hexact hg
  letI : Module.FinitePresentation R (A ⧸ LinearMap.ker f) :=
    Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

end Exactness

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

/-- The kernel after iterated algebra base change agrees with the kernel after direct base
change, via the canonical tensor-product cancellation equivalences. -/
noncomputable def LinearMap.baseChangeBaseChangeKernelEquiv
    (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (f : P →ₗ[R] Q) :
    LinearMap.ker ((f.baseChange A).baseChange B) ≃ₗ[B]
      LinearMap.ker (f.baseChange B) := by
  let eP := AlgebraTensorModule.cancelBaseChange R A B B P
  let eQ := AlgebraTensorModule.cancelBaseChange R A B B Q
  refine
    { toFun := fun x ↦ ⟨eP.toLinearMap x, ?_⟩
      invFun := fun x ↦ ⟨eP.symm.toLinearMap x, ?_⟩
      left_inv := fun x ↦ by
        ext
        exact eP.symm_apply_apply x
      right_inv := fun x ↦ by
        ext
        exact eP.apply_symm_apply x
      map_add' := fun x y ↦ by
        ext
        exact eP.map_add x y
      map_smul' := fun r x ↦ by
        ext
        exact eP.map_smul r x }
  · change (f.baseChange B) (eP.toLinearMap x) = 0
    have hx : eQ.symm.toLinearMap ((f.baseChange B) (eP.toLinearMap x)) = 0 := by
      calc
        _ = ((f.baseChange A).baseChange B) x := by
          simpa only [eP, eQ, LinearMap.comp_apply] using congrArg
            (fun g ↦ g x.1) (LinearMap.baseChange_baseChange (A := A) (B := B) f).symm
        _ = 0 := x.2
    calc
      _ = eQ.toLinearMap (eQ.symm.toLinearMap
          ((f.baseChange B) (eP.toLinearMap x))) :=
        (eQ.apply_symm_apply ((f.baseChange B) (eP.toLinearMap x))).symm
      _ = eQ.toLinearMap 0 := congrArg eQ.toLinearMap hx
      _ = 0 := eQ.toLinearMap.map_zero
  · change ((f.baseChange A).baseChange B) (eP.symm.toLinearMap x) = 0
    have hx : (f.baseChange B) x = 0 := x.2
    calc
      _ = eQ.symm.toLinearMap
          ((f.baseChange B) (eP.toLinearMap (eP.symm.toLinearMap x))) := by
        simpa only [eP, eQ, LinearMap.comp_apply] using congrArg
          (fun g ↦ g (eP.symm.toLinearMap x.1))
            (LinearMap.baseChange_baseChange (A := A) (B := B) f)
      _ = eQ.symm.toLinearMap ((f.baseChange B) x) := by
        exact congrArg eQ.symm.toLinearMap
          (congrArg (f.baseChange B) (eP.apply_symm_apply x.1))
      _ = 0 := by rw [hx, map_zero]

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

/-- If the scalar-extension algebra is flat, the canonical comparison from the
base change of a kernel to the kernel of the base-changed map is bijective. -/
theorem kerBaseChangeComparison_bijective_of_flat
    [Module.Flat R A] :
    Function.Bijective (kerBaseChangeComparison A f) := by
  have hComparison : kerBaseChangeComparison A f =
      LinearMap.tensorKer A A f := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [kerBaseChangeComparison_coe]
    change (LinearMap.ker f).subtype.baseChange A y =
      ((LinearMap.tensorKer A A f y :
        LinearMap.ker (AlgebraTensorModule.lTensor A A f)) : A ⊗[R] P)
    rw [LinearMap.tensorKer_coe]
    rfl
  rw [hComparison]
  exact (LinearMap.tensorKerEquiv A A f).bijective

/-- Extending scalars between fields preserves the dimension of the kernel of a
base-changed linear map. -/
theorem LinearMap.finrank_ker_baseChange_eq
    (A B : Type u) [Field A] [Field B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (f : P →ₗ[R] Q) :
    Module.finrank B (LinearMap.ker (f.baseChange B)) =
      Module.finrank A (LinearMap.ker (f.baseChange A)) := by
  letI : Module.Free A (LinearMap.ker (f.baseChange A)) :=
    Module.Free.of_divisionRing A (LinearMap.ker (f.baseChange A))
  let eIter : B ⊗[A] LinearMap.ker (f.baseChange A) ≃ₗ[B]
      LinearMap.ker ((f.baseChange A).baseChange B) :=
    LinearEquiv.ofBijective (kerBaseChangeComparison B (f.baseChange A))
      (kerBaseChangeComparison_bijective B (f.baseChange A))
  let e := eIter.trans (LinearMap.baseChangeBaseChangeKernelEquiv A B f)
  exact e.finrank_eq.symm.trans Module.finrank_baseChange

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

/-- The algebra-linear degree-zero kernel comparison for a bounded exact sequence of
flat modules. -/
theorem kerBaseChangeComparison_bijective_of_bounded_exact
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1))) :
    Function.Bijective (kerBaseChangeComparison A (d 0)) :=
  kerLTensorComparison_bijective_of_bounded_exact M d A N hexact

/-- Cycles in degree `k` commute with arbitrary algebra base change when a bounded complex
of flat modules is exact from degree `k` onward. -/
theorem kerBaseChangeComparison_bijective_of_bounded_exact_from
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1))
    (A : Type*) [CommRing A] [Algebra R A] [∀ n, Module.Flat R (M n)]
    (N k : ℕ) (hk : k ≤ N) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, k ≤ n → n < N → Function.Exact (d n) (d (n + 1))) :
    Function.Bijective (kerBaseChangeComparison A (d k)) := by
  letI : Module.Flat R (M (k + 1) ⧸ LinearMap.range (d k)) :=
    Module.Flat.quotient_range_of_bounded_exact_from M d N k hk hexact
  exact kerBaseChangeComparison_bijective A (d k)

section Exactness

variable {T : Type*} [AddCommGroup T] [Module R T]

/-- Base change preserves the relation that two consecutive linear maps compose to zero. -/
theorem LinearMap.baseChange_comp_eq_zero
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    (A : Type*) [CommRing A] [Algebra R A] :
    g.baseChange A ∘ₗ f.baseChange A = 0 := by
  rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero]

/-- Factoring a complex through its second kernel commutes with algebra base change. -/
theorem kerBaseChangeComparison_comp_codRestrictToKer_baseChange
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0) :
    kerBaseChangeComparison A g ∘ₗ
        (LinearMap.codRestrictToKer f g h).baseChange A =
      LinearMap.codRestrictToKer (f.baseChange A) (g.baseChange A) (by
        rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero]) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [LinearMap.comp_apply, kerBaseChangeComparison_coe,
    LinearMap.codRestrictToKer_coe]
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

/-- If formation of the second kernel commutes with base change, then the base-changed
map into cycles has the same kernel as the base change of the original first map. -/
theorem LinearMap.ker_baseChange_codRestrictToKer_eq
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    (A : Type*) [CommRing A] [Algebra R A]
    (hbij : Function.Bijective (kerBaseChangeComparison A g)) :
    LinearMap.ker ((LinearMap.codRestrictToKer f g h).baseChange A) =
      LinearMap.ker (f.baseChange A) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    have hxcomp := LinearMap.congr_fun
      (kerBaseChangeComparison_comp_codRestrictToKer_baseChange A f g h) x
    rw [LinearMap.comp_apply, hx, map_zero] at hxcomp
    exact (congrArg Subtype.val hxcomp).symm
  · intro hx
    apply hbij.injective
    rw [map_zero]
    have hxcomp := LinearMap.congr_fun
      (kerBaseChangeComparison_comp_codRestrictToKer_baseChange A f g h) x
    rw [LinearMap.comp_apply] at hxcomp
    rw [hxcomp]
    exact Subtype.ext hx

end Exactness

end BaseChangeAlgebra

section Exactness

variable {T : Type*} [AddCommGroup T] [Module R T]

/-- In an algebra tower, exactness after iterated base change is equivalent to exactness
after direct base change. -/
theorem LinearMap.baseChange_baseChange_exact_iff
    (A : Type*) (B : Type*)
    [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) :
    Function.Exact
        ((f.baseChange A).baseChange B)
        ((g.baseChange A).baseChange B) ↔
      Function.Exact (f.baseChange B) (g.baseChange B) := by
  let eP := AlgebraTensorModule.cancelBaseChange R A B B P
  let eQ := AlgebraTensorModule.cancelBaseChange R A B B Q
  let eT := AlgebraTensorModule.cancelBaseChange R A B B T
  have hf :
      f.baseChange B ∘ₗ eP.toLinearMap =
        eQ.toLinearMap ∘ₗ (f.baseChange A).baseChange B := by
    rw [LinearMap.baseChange_baseChange]
    ext x
    simp [eP, eQ]
  have hg :
      g.baseChange B ∘ₗ eQ.toLinearMap =
        eT.toLinearMap ∘ₗ (g.baseChange A).baseChange B := by
    rw [LinearMap.baseChange_baseChange]
    ext x
    simp [eQ, eT]
  exact (Function.Exact.iff_of_ladder_linearEquiv hf hg).symm

/-- Exactness after base change can be checked after a further faithfully flat
scalar extension. -/
theorem LinearMap.baseChange_exact_iff_of_faithfullyFlat
    (A : Type*) (B : Type*)
    [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [Module.FaithfullyFlat A B]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) :
    Function.Exact (f.baseChange A) (g.baseChange A) ↔
      Function.Exact (f.baseChange B) (g.baseChange B) := by
  rw [← LinearMap.baseChange_baseChange_exact_iff A B f g]
  simpa only [LinearMap.baseChange_eq_ltensor] using
    (Module.FaithfullyFlat.lTensor_exact_iff_exact A B
      (f.baseChange A) (g.baseChange A)).symm

/-- An exact pair remains exact after arbitrary algebra base change when the target and
the cokernel of the second map are flat. -/
theorem LinearMap.baseChange_exact_of_exact_of_flat_coker
    (A : Type*) [CommRing A] [Algebra R A]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    [Module.Flat R T] [Module.Flat R (T ⧸ LinearMap.range g)]
    (hexact : Function.Exact f g) :
    Function.Exact (f.baseChange A) (g.baseChange A) := by
  apply (LinearMap.codRestrictToKer_surjective_iff_exact
    (f.baseChange A) (g.baseChange A) _).mp
  rw [← kerBaseChangeComparison_comp_codRestrictToKer_baseChange A f g h]
  exact (kerBaseChangeComparison_bijective A g).2.comp
    (LinearMap.baseChange_surjective A
      ((LinearMap.codRestrictToKer_surjective_iff_exact f g h).mpr hexact))

/-- Exactness after base change to every prime residue field implies exactness after base
change to every field algebra. The algebra map to a field factors through the residue field
of its kernel prime, and the remaining field extension is flat. -/
theorem LinearMap.baseChange_exact_of_forall_residueField_baseChange_exact
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T)
    (hres : ∀ p : PrimeSpectrum R,
      Function.Exact (f.baseChange p.asIdeal.ResidueField)
        (g.baseChange p.asIdeal.ResidueField))
    (K : Type u) [Field K] [Algebra R K] :
    Function.Exact (f.baseChange K) (g.baseChange K) := by
  let p : Ideal R := RingHom.ker (algebraMap R K)
  letI hp : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  have hp_le : p ≤ RingHom.ker (algebraMap R K) := le_rfl
  have hp_unit : p.primeCompl ≤
      (IsUnit.submonoid K).comap (algebraMap R K) := by
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    intro hr_zero
    exact hr hr_zero
  let φ : p.ResidueField →+* K :=
    Ideal.ResidueField.lift p (algebraMap R K) hp_le hp_unit
  letI : Algebra p.ResidueField K := φ.toAlgebra
  letI : IsScalarTower R p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (Ideal.ResidueField.lift_algebraMap
        p (algebraMap R K) hp_le hp_unit r).symm
  have hκ : Function.Exact
      (f.baseChange p.ResidueField) (g.baseChange p.ResidueField) :=
    hres ⟨p, hp⟩
  have hiter : Function.Exact
      ((f.baseChange p.ResidueField).baseChange K)
      ((g.baseChange p.ResidueField).baseChange K) :=
    LinearMap.baseChange_exact_of_exact_of_flat_coker
      (R := p.ResidueField) K
      (f.baseChange p.ResidueField) (g.baseChange p.ResidueField)
      hκ.linearMap_comp_eq_zero hκ
  let eP := AlgebraTensorModule.cancelBaseChange R p.ResidueField K K P
  let eQ := AlgebraTensorModule.cancelBaseChange R p.ResidueField K K Q
  let eT := AlgebraTensorModule.cancelBaseChange R p.ResidueField K K T
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := eP) (e₂ := eQ) (e₃ := eT)
    (f₁₂ := (f.baseChange p.ResidueField).baseChange K)
    (f₂₃ := (g.baseChange p.ResidueField).baseChange K)
    (g₁₂ := f.baseChange K) (g₂₃ := g.baseChange K)
    (by
      ext
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
        curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        LinearMap.baseChange_tmul, eP, eQ])
    (by
      ext
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
        curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        LinearMap.baseChange_tmul, eQ, eT])).mpr hiter

/-- Exactness of a complex can be checked on every field fibre when its homology is finite
and formation of the second kernel commutes with base change. The flatness hypotheses are the
module-theoretic criterion ensuring that kernel comparison. -/
theorem LinearMap.exact_of_forall_field_baseChange_exact_of_finite
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    [Module.Flat R T] [Module.Flat R (T ⧸ LinearMap.range g)]
    [Module.Finite R
      (LinearMap.ker g ⧸ LinearMap.range (LinearMap.codRestrictToKer f g h))]
    (hfield : ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact (f.baseChange K) (g.baseChange K)) :
    Function.Exact f g := by
  apply (LinearMap.codRestrictToKer_surjective_iff_exact f g h).mp
  have hcoker : Subsingleton
      (LinearMap.ker g ⧸ LinearMap.range (LinearMap.codRestrictToKer f g h)) :=
    Module.subsingleton_of_forall_field_tensor_subsingleton _ fun K _ _ ↦ by
      apply (baseChange_surjective_iff_subsingleton_coker K
        (LinearMap.codRestrictToKer f g h)).mp
      have hcomparison := kerBaseChangeComparison_bijective K g
      have hcomposition : Function.Surjective
          (kerBaseChangeComparison K g ∘ₗ
            (LinearMap.codRestrictToKer f g h).baseChange K) := by
        rw [kerBaseChangeComparison_comp_codRestrictToKer_baseChange]
        exact (LinearMap.codRestrictToKer_surjective_iff_exact _ _ _).mpr (hfield K)
      intro y
      obtain ⟨x, hx⟩ := hcomposition (kerBaseChangeComparison K g y)
      refine ⟨x, hcomparison.injective ?_⟩
      simpa only [LinearMap.comp_apply] using hx
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact hcoker

/-- Over a local ring, exactness of a pair can be checked on the residue field when its
homology is finite and formation of the second kernel commutes with base change. -/
theorem LinearMap.exact_of_residueField_baseChange_exact_of_finite
    [IsLocalRing R]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    [Module.Flat R T] [Module.Flat R (T ⧸ LinearMap.range g)]
    [Module.Finite R
      (LinearMap.ker g ⧸ LinearMap.range (LinearMap.codRestrictToKer f g h))]
    (hresidue : Function.Exact
      (f.baseChange (IsLocalRing.ResidueField R))
      (g.baseChange (IsLocalRing.ResidueField R))) :
    Function.Exact f g := by
  apply (LinearMap.codRestrictToKer_surjective_iff_exact f g h).mp
  have hcoker : Subsingleton
      (LinearMap.ker g ⧸
        LinearMap.range (LinearMap.codRestrictToKer f g h)) := by
    apply (IsLocalRing.subsingleton_tensorProduct
      (R := R)
      (M := LinearMap.ker g ⧸
        LinearMap.range (LinearMap.codRestrictToKer f g h))).mp
    apply (baseChange_surjective_iff_subsingleton_coker
      (IsLocalRing.ResidueField R)
      (LinearMap.codRestrictToKer f g h)).mp
    have hcomparison :=
      kerBaseChangeComparison_bijective
        (IsLocalRing.ResidueField R) g
    have hcomposition : Function.Surjective
        (kerBaseChangeComparison (IsLocalRing.ResidueField R) g ∘ₗ
          (LinearMap.codRestrictToKer f g h).baseChange
            (IsLocalRing.ResidueField R)) := by
      rw [kerBaseChangeComparison_comp_codRestrictToKer_baseChange]
      exact
        (LinearMap.codRestrictToKer_surjective_iff_exact _ _ _).mpr
          hresidue
    intro y
    obtain ⟨x, hx⟩ :=
      hcomposition
        (kerBaseChangeComparison (IsLocalRing.ResidueField R) g y)
    refine ⟨x, hcomparison.injective ?_⟩
    simpa only [LinearMap.comp_apply] using hx
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  exact hcoker

/-- Over a Noetherian ring, the middle module of an exact pair is finite when the two
surrounding modules are finite. This is the module-theoretic sandwich used in long exact
cohomology sequences. -/
theorem Module.Finite.of_exact_of_finite [IsNoetherianRing R]
    {M : Type*} {N : Type*} {T : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
    [Module R M] [Module R N] [Module R T]
    (f : M →ₗ[R] N) (g : N →ₗ[R] T)
    [Module.Finite R M] [Module.Finite R T]
    (h : Function.Exact f g) : Module.Finite R N := by
  letI : IsNoetherian R N :=
    isNoetherian_of_range_eq_ker f g (LinearMap.exact_iff.mp h).symm
  infer_instance

private theorem boundedFlatCokerAndExactOfFiniteHomology
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfinite : ∀ n, n < N →
      Module.Finite R
        (LinearMap.ker (d (n + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d n) (d (n + 1)) (hcomp n))))
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n ≤ N) :
    Module.Flat R (M (n + 1) ⧸ LinearMap.range (d n)) ∧
      (n < N → Function.Exact (d n) (d (n + 1))) := by
  induction hn using Nat.decreasingInduction with
  | self =>
      exact ⟨inferInstance, fun hn => (Nat.lt_irrefl N hn).elim⟩
  | @of_succ k hk ih =>
      letI : Module.Flat R
          (M (k + 2) ⧸ LinearMap.range (d (k + 1))) := ih.1
      letI : Module.Finite R
          (LinearMap.ker (d (k + 1)) ⧸
            LinearMap.range
              (LinearMap.codRestrictToKer (d k) (d (k + 1)) (hcomp k))) :=
        hfinite k hk
      have hexact : Function.Exact (d k) (d (k + 1)) :=
        LinearMap.exact_of_forall_field_baseChange_exact_of_finite
          (d k) (d (k + 1)) (hcomp k) (hfield k hk)
      letI : Module.Flat R (LinearMap.range (d (k + 1))) :=
        Module.Flat.of_flat_quotient _
      let e : (M (k + 1) ⧸ LinearMap.range (d k)) ≃ₗ[R]
          LinearMap.range (d (k + 1)) :=
        Submodule.quotEquivOfEq
            (LinearMap.range (d k)) (LinearMap.ker (d (k + 1)))
            (LinearMap.exact_iff.mp hexact).symm ≪≫ₗ
          LinearMap.quotKerEquivRange (d (k + 1))
      exact ⟨Module.Flat.of_linearEquiv e, fun _ => hexact⟩

/-- A bounded complex of flat modules with finite explicit homology is exact when every
field base change is exact. Boundedness lets one descend from the terminal zero term: the
next cokernel is flat, finite homology detects exactness on field fibres, and exactness
identifies the preceding cokernel with a flat range. -/
theorem LinearMap.exact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfinite : ∀ n, n < N →
      Module.Finite R
        (LinearMap.ker (d (n + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d n) (d (n + 1)) (hcomp n))))
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n < N) :
    Function.Exact (d n) (d (n + 1)) :=
  (boundedFlatCokerAndExactOfFiniteHomology M d N hcomp hfinite hfield n hn.le).2 hn

private theorem boundedFlatCokerAndExactOfFiniteHomologyAtResidue
    [IsLocalRing R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfinite : ∀ n, n < N →
      Module.Finite R
        (LinearMap.ker (d (n + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d n) (d (n + 1)) (hcomp n))))
    (hresidue : ∀ n, n < N →
      Function.Exact
        ((d n).baseChange (IsLocalRing.ResidueField R))
        ((d (n + 1)).baseChange (IsLocalRing.ResidueField R)))
    (n : ℕ) (hn : n ≤ N) :
    Module.Flat R (M (n + 1) ⧸ LinearMap.range (d n)) ∧
      (n < N → Function.Exact (d n) (d (n + 1))) := by
  induction hn using Nat.decreasingInduction with
  | self =>
      exact ⟨inferInstance, fun hn ↦ (Nat.lt_irrefl N hn).elim⟩
  | @of_succ k hk ih =>
      letI : Module.Flat R
          (M (k + 2) ⧸ LinearMap.range (d (k + 1))) := ih.1
      letI : Module.Finite R
          (LinearMap.ker (d (k + 1)) ⧸
            LinearMap.range
              (LinearMap.codRestrictToKer
                (d k) (d (k + 1)) (hcomp k))) :=
        hfinite k hk
      have hexact : Function.Exact (d k) (d (k + 1)) :=
        LinearMap.exact_of_residueField_baseChange_exact_of_finite
          (d k) (d (k + 1)) (hcomp k) (hresidue k hk)
      letI : Module.Flat R (LinearMap.range (d (k + 1))) :=
        Module.Flat.of_flat_quotient _
      let e : (M (k + 1) ⧸ LinearMap.range (d k)) ≃ₗ[R]
          LinearMap.range (d (k + 1)) :=
        Submodule.quotEquivOfEq
            (LinearMap.range (d k)) (LinearMap.ker (d (k + 1)))
            (LinearMap.exact_iff.mp hexact).symm ≪≫ₗ
          LinearMap.quotKerEquivRange (d (k + 1))
      exact ⟨Module.Flat.of_linearEquiv e, fun _ ↦ hexact⟩

/-- A bounded complex of flat modules with finite explicit homology over a local ring is
exact when its residue-field base change is exact. -/
theorem LinearMap.exact_of_bounded_flat_residueField_baseChange_exact_of_finite_homology
    [IsLocalRing R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfinite : ∀ n, n < N →
      Module.Finite R
        (LinearMap.ker (d (n + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d n) (d (n + 1)) (hcomp n))))
    (hresidue : ∀ n, n < N →
      Function.Exact
        ((d n).baseChange (IsLocalRing.ResidueField R))
        ((d (n + 1)).baseChange (IsLocalRing.ResidueField R)))
    (n : ℕ) (hn : n < N) :
    Function.Exact (d n) (d (n + 1)) :=
  (boundedFlatCokerAndExactOfFiniteHomologyAtResidue
    M d N hcomp hfinite hresidue n hn.le).2 hn

end Exactness

section BoundedFlatBaseChange

variable (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (d : ∀ n, M n →ₗ[R] M (n + 1))

/-- Arbitrary algebra base change preserves every exact pair in a bounded exact complex
of flat modules. This is the tensor-stability statement in Mumford §5, Lemma 2. -/
theorem LinearMap.baseChange_exact_of_bounded_exact
    (A : Type*) [CommRing A] [Algebra R A] [∀ n, Module.Flat R (M n)]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, n < N → Function.Exact (d n) (d (n + 1)))
    (n : ℕ) (hn : n < N) :
    Function.Exact ((d n).baseChange A) ((d (n + 1)).baseChange A) := by
  letI : Module.Flat R (M ((n + 1) + 1) ⧸ LinearMap.range (d (n + 1))) :=
    Module.Flat.quotient_range_of_bounded_exact M d N hexact (n + 1)
      (Nat.succ_le_iff.mpr hn)
  exact LinearMap.baseChange_exact_of_exact_of_flat_coker
    A (d n) (d (n + 1)) (hexact n hn).linearMap_comp_eq_zero (hexact n hn)

end BoundedFlatBaseChange

private theorem projective_range_of_projective_coker
    (f : P →ₗ[R] Q) [Module.Projective R Q]
    [Module.Projective R (Q ⧸ LinearMap.range f)] :
    Module.Projective R (LinearMap.range f) := by
  letI : Module.Projective R (LinearMap.ker (LinearMap.range f).mkQ) :=
    Module.Projective.ker_of_surjective _
      (Submodule.mkQ_surjective (LinearMap.range f))
  rw [← Submodule.ker_mkQ (LinearMap.range f)]
  infer_instance

/-- Over an arbitrary ring, the kernel of a map between projective modules with projective
cokernel is projective. -/
theorem Module.Projective.ker_of_projective_coker
    (f : P →ₗ[R] Q) [Module.Projective R P] [Module.Projective R Q]
    [Module.Projective R (Q ⧸ LinearMap.range f)] :
    Module.Projective R (LinearMap.ker f) := by
  letI : Module.Projective R (LinearMap.range f) :=
    projective_range_of_projective_coker f
  letI : Module.Projective R (LinearMap.ker f.rangeRestrict) :=
    Module.Projective.ker_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  rw [← LinearMap.ker_rangeRestrict]
  infer_instance

/-- Over an arbitrary ring, the kernel of a map from a finite module to a projective module
with projective cokernel is finite. -/
theorem Module.Finite.ker_of_projective_coker
    (f : P →ₗ[R] Q) [Module.Finite R P] [Module.Projective R Q]
    [Module.Projective R (Q ⧸ LinearMap.range f)] :
    Module.Finite R (LinearMap.ker f) := by
  letI : Module.Projective R (LinearMap.range f) :=
    projective_range_of_projective_coker f
  letI : Module.Finite R (LinearMap.ker f.rangeRestrict) :=
    Module.Finite.ker_of_surjective_of_projective f.rangeRestrict
      f.surjective_rangeRestrict
  rw [← LinearMap.ker_rangeRestrict]
  infer_instance

section BoundedFiniteProjectiveComplex

variable (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (d : ∀ n, M n →ₗ[R] M (n + 1)) [∀ n, Module.Finite R (M n)]
  [∀ n, Module.Projective R (M n)]

private theorem boundedCokerFiniteProjectiveAndExact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n ≤ N) :
    (Module.Finite R (M (n + 1) ⧸ LinearMap.range (d n)) ∧
      Module.Projective R (M (n + 1) ⧸ LinearMap.range (d n))) ∧
      (n < N → Function.Exact (d n) (d (n + 1))) := by
  induction hn using Nat.decreasingInduction with
  | self =>
      exact ⟨⟨inferInstance, inferInstance⟩, fun hn ↦ (Nat.lt_irrefl N hn).elim⟩
  | @of_succ k hk ih =>
      letI : Module.Finite R (M (k + 2) ⧸ LinearMap.range (d (k + 1))) := ih.1.1
      letI : Module.Projective R (M (k + 2) ⧸ LinearMap.range (d (k + 1))) := ih.1.2
      letI : Module.Projective R (LinearMap.range (d (k + 1))) :=
        projective_range_of_projective_coker (d (k + 1))
      letI : Module.Finite R (LinearMap.range (d (k + 1))) :=
        Module.Finite.of_surjective (d (k + 1)).rangeRestrict
          (d (k + 1)).surjective_rangeRestrict
      letI : Module.Projective R (LinearMap.ker (d (k + 1))) :=
        Module.Projective.ker_of_projective_coker (d (k + 1))
      letI : Module.Finite R (LinearMap.ker (d (k + 1))) :=
        Module.Finite.ker_of_projective_coker (d (k + 1))
      letI : Module.Finite R
          (LinearMap.ker (d (k + 1)) ⧸
            LinearMap.range (LinearMap.codRestrictToKer (d k) (d (k + 1)) (hcomp k))) :=
        Module.Finite.of_surjective _
          (Submodule.mkQ_surjective (LinearMap.range
            (LinearMap.codRestrictToKer (d k) (d (k + 1)) (hcomp k))))
      have hexact : Function.Exact (d k) (d (k + 1)) :=
        LinearMap.exact_of_forall_field_baseChange_exact_of_finite
          (d k) (d (k + 1)) (hcomp k) (hfield k hk)
      let e : (M (k + 1) ⧸ LinearMap.range (d k)) ≃ₗ[R]
          LinearMap.range (d (k + 1)) :=
        Submodule.quotEquivOfEq (LinearMap.range (d k)) (LinearMap.ker (d (k + 1)))
            (LinearMap.exact_iff.mp hexact).symm ≪≫ₗ
          LinearMap.quotKerEquivRange (d (k + 1))
      exact ⟨⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩,
        fun _ ↦ hexact⟩

/-- Every cokernel in a bounded finite-projective complex is finite when the complex is
exact after base change to every field. -/
theorem Module.Finite.quotient_range_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n ≤ N) :
    Module.Finite R (M (n + 1) ⧸ LinearMap.range (d n)) :=
  (boundedCokerFiniteProjectiveAndExact M d N hcomp hfield n hn).1.1

/-- Every cokernel in a bounded finite-projective complex is projective when the complex is
exact after base change to every field. -/
theorem Module.Projective.quotient_range_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n ≤ N) :
    Module.Projective R (M (n + 1) ⧸ LinearMap.range (d n)) :=
  (boundedCokerFiniteProjectiveAndExact M d N hcomp hfield n hn).1.2

/-- A bounded complex of finite projective modules is exact when every field base change is
exact. -/
theorem LinearMap.exact_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (n : ℕ) (hn : n < N) :
    Function.Exact (d n) (d (n + 1)) :=
  (boundedCokerFiniteProjectiveAndExact M d N hcomp hfield n hn.le).2 hn

/-- The degree-zero kernel of a bounded finite-projective complex that is exact on every
field fibre is finite. -/
theorem Module.Finite.ker_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K)) :
    Module.Finite R (LinearMap.ker (d 0)) := by
  letI : Module.Projective R (M 1 ⧸ LinearMap.range (d 0)) :=
    Module.Projective.quotient_range_of_bounded_forall_field_baseChange_exact
      M d N hcomp hfield 0 (Nat.zero_le N)
  exact Module.Finite.ker_of_projective_coker (d 0)

/-- The degree-zero kernel of a bounded finite-projective complex that is exact on every
field fibre is projective. -/
theorem Module.Projective.ker_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K)) :
    Module.Projective R (LinearMap.ker (d 0)) := by
  letI : Module.Projective R (M 1 ⧸ LinearMap.range (d 0)) :=
    Module.Projective.quotient_range_of_bounded_forall_field_baseChange_exact
      M d N hcomp hfield 0 (Nat.zero_le N)
  exact Module.Projective.ker_of_projective_coker (d 0)

/-- The degree-zero kernel of a bounded finite-projective complex that is exact on every
field fibre commutes with arbitrary algebra base change. -/
theorem kerBaseChangeComparison_bijective_of_bounded_forall_field_baseChange_exact
    (A : Type*) [CommRing A] [Algebra R A]
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K)) :
    Function.Bijective (kerBaseChangeComparison A (d 0)) :=
  kerBaseChangeComparison_bijective_of_bounded_exact A M d N
    (LinearMap.exact_of_bounded_forall_field_baseChange_exact M d N hcomp hfield)

/-- The degree-zero kernel of a bounded finite-projective complex has constant rank `r`
when its base change to every residue field has kernel dimension `r`. -/
theorem Module.rankAtStalk_ker_eq_of_bounded_forall_field_baseChange_exact
    (N : ℕ) [Subsingleton (M (N + 1))]
    (hcomp : ∀ n, d (n + 1) ∘ₗ d n = 0)
    (hfield : ∀ n, n < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact ((d n).baseChange K) ((d (n + 1)).baseChange K))
    (r : ℕ)
    (hrank : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker ((d 0).baseChange p.asIdeal.ResidueField)) = r) :
    Module.rankAtStalk (R := R) (LinearMap.ker (d 0)) = fun _ ↦ r := by
  letI : Module.Finite R (LinearMap.ker (d 0)) :=
    Module.Finite.ker_of_bounded_forall_field_baseChange_exact M d N hcomp hfield
  letI : Module.Projective R (LinearMap.ker (d 0)) :=
    Module.Projective.ker_of_bounded_forall_field_baseChange_exact M d N hcomp hfield
  letI : Module.Flat R (LinearMap.ker (d 0)) := inferInstance
  funext p
  rw [Module.rankAtStalk_eq]
  let e : p.asIdeal.Fiber (LinearMap.ker (d 0)) ≃ₗ[p.asIdeal.ResidueField]
      LinearMap.ker ((d 0).baseChange p.asIdeal.ResidueField) :=
    LinearEquiv.ofBijective
      (kerBaseChangeComparison p.asIdeal.ResidueField (d 0))
      (kerBaseChangeComparison_bijective_of_bounded_forall_field_baseChange_exact
        M d p.asIdeal.ResidueField N hcomp hfield)
  exact e.finrank_eq.trans (hrank p)

end BoundedFiniteProjectiveComplex

/-- Near a prime where the residue-fibre differential is surjective, a differential
between finite projective modules has finite projective kernel, and that kernel commutes
with every further algebra base change. -/
theorem LinearMap.exists_away_finiteProjective_ker_of_residueField_surjective
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (p : Ideal R) [p.IsPrime]
    (h : Function.Surjective (f.baseChange p.ResidueField)) :
    ∃ r : R, r ∉ p ∧
      Function.Surjective (f.baseChange (Localization.Away r)) ∧
      Module.Finite (Localization.Away r)
        (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
      Module.Projective (Localization.Away r)
        (LinearMap.ker (f.baseChange (Localization.Away r))) ∧
      ∀ (A : Type*) [CommRing A] [Algebra (Localization.Away r) A],
        Function.Bijective
          (kerBaseChangeComparison A (f.baseChange (Localization.Away r))) := by
  obtain ⟨r, hr, hsurj⟩ :=
    ModularCurves.LinearMap.exists_away_baseChange_surjective_of_residueField f p h
  refine ⟨r, hr, hsurj, ?_, ?_, ?_⟩
  · exact Module.Finite.ker_of_surjective_of_projective _ hsurj
  · exact Module.Projective.ker_of_surjective _ hsurj
  · intro A _ _
    exact kerBaseChangeComparison_bijective_of_surjective A _ hsurj

end ModularCurves
