/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.CoactionShear
import ModularCurves.ForMathlib.HopfGalois
import ModularCurves.ForMathlib.CoactionCharpoly
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The Hopf–Galois bootstrap: from a shifted basis to the Galois property

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B5]`; Stacks
`groupoids-lemma-basis-marks-invariants`, tag 03C8, comodule form): given a co-action
`ρ : B →ₐ[R] B ⊗[R] A` of a finite free Hopf algebra and elements `x i : B` whose
co-action images `ρ (x i)` form a basis of `B ⊗[R] A` as a left `B`-module, we prove

* `coinvariantsBasis` — the `x i` themselves form a basis of `B` over the co-invariant
  subring `C = coinvariants ρ` (Stacks: `A = ⊕ᵢ C·xᵢ`), and
* `bijective_canonicalGaloisMap_of_basis` — the canonical Galois map
  `B ⊗[C] B → B ⊗[R] A` is bijective.

The Stacks two-row equalizer comparison is replaced by an elementwise coassociativity
computation (banked in the decomposition appendix): writing `ρ f = ∑ ι(cᵢ)·ρ(xᵢ)` in the
basis and comparing `δ̃` with `ρ ⊗ id` on both expansions forces every coordinate `cᵢ`
into the co-invariants. No faithful flatness, no Amitsur equalizer, and no twisted module
instances enter: the only `B`-module structure used on `B ⊗[R] A` is the canonical
left-factor one, and the `ρ`-side is handled by the shear automorphism.
-/

namespace ModularCurves

open TensorProduct

section Bootstrap

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable {ι' : Type*} [Fintype ι']

/-- The left-inclusion image of a left `B`-basis of `B ⊗[R] A` is a basis of
`(B ⊗[R] A) ⊗[R] A` over `B ⊗[R] A`: base-change the basis along
`includeLeft : B → B ⊗[R] A` and cancel the middle factor. -/
noncomputable def includeLeftBasis (hb : Module.Basis ι' B (B ⊗[R] A)) :
    Module.Basis ι' (B ⊗[R] A) ((B ⊗[R] A) ⊗[R] A) :=
  (hb.baseChange (B ⊗[R] A)).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B (B ⊗[R] A) (B ⊗[R] A) A)

/-- Cancelling the base change against the left inclusion, elementwise: the composite
`y ↦ cancelBaseChange (1 ⊗ y)` is `includeLeft ⊗ id`. -/
theorem cancelBaseChange_one_tmul (y : B ⊗[R] A) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R B (B ⊗[R] A) (B ⊗[R] A) A
      ((1 : B ⊗[R] A) ⊗ₜ[B] y)
      = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (S := R))
          (AlgHom.id R A)) y := by
  induction y with
  | zero => simp
  | tmul b a =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        Algebra.TensorProduct.map_tmul]
      congr 1
      rw [Algebra.smul_def, mul_one]
      rfl
  | add y z hy hz => rw [tmul_add, map_add, map_add, hy, hz]

omit [Fintype ι'] in
/-- The vectors of `includeLeftBasis` are the `includeLeft ⊗ id` images of the original
basis vectors. -/
theorem includeLeftBasis_apply (hb : Module.Basis ι' B (B ⊗[R] A)) (i : ι') :
    includeLeftBasis R A hb i
      = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (S := R))
          (AlgHom.id R A)) (hb i) := by
  rw [includeLeftBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    cancelBaseChange_one_tmul]

/-- **`w`-cancellation**: the `ρ ⊗ id` images of a left `B`-basis of `B ⊗[R] A` admit no
nontrivial `(B ⊗[R] A)`-linear relation. (They are the shear-automorphism twist of the
genuine basis `includeLeftBasis`, so linear relations transport across the twist.) -/
theorem eq_zero_of_sum_smul_map_coaction_eq_zero (ρ : B →ₐ[R] B ⊗[R] A)
    (hρ : IsCoaction ρ) (hb : Module.Basis ι' B (B ⊗[R] A)) (d : ι' → B ⊗[R] A)
    (h : ∑ i, d i • (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (hb i) = 0) :
    ∀ i, d i = 0 := by
  classical
  set Ξ := Algebra.TensorProduct.congr (coactionShearEquiv ρ hρ)
    (AlgEquiv.refl : A ≃ₐ[R] A)
    with hΞdef
  -- `ρ ⊗ id = Ξ ∘ (ι ⊗ id)` elementwise
  have hfactor : ∀ y : B ⊗[R] A,
      (Algebra.TensorProduct.map ρ (AlgHom.id R A)) y
        = Ξ ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (S := R))
            (AlgHom.id R A)) y) := by
    intro y
    induction y with
    | zero => simp
    | tmul b a =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hΞdef,
          Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        congr 1
        exact (AlgHom.congr_fun (coactionShear_comp_includeLeft ρ) b).symm
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  -- `Ξ` intertwines scalar multiplication through the shear
  have hsmul : ∀ (u : B ⊗[R] A) (z : (B ⊗[R] A) ⊗[R] A),
      Ξ (u • z) = coactionShearEquiv ρ hρ u • Ξ z := by
    intro u z
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
  -- transport the relation across `Ξ` and use independence of `includeLeftBasis`
  have hrel : ∑ i, (coactionShearEquiv ρ hρ).symm (d i) • includeLeftBasis R A hb i
      = 0 := by
    apply (map_eq_zero_iff Ξ Ξ.injective).mp
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [hsmul, AlgEquiv.apply_symm_apply, includeLeftBasis_apply, ← hfactor])]
    exact h
  intro i
  have := Fintype.linearIndependent_iff.mp
    (includeLeftBasis R A hb).linearIndependent
    (fun j => (coactionShearEquiv ρ hρ).symm (d j)) hrel i
  exact (map_eq_zero_iff _ (coactionShearEquiv ρ hρ).symm.injective).mp this

/-- **Every basis coordinate of a co-action value is co-invariant** (the heart of Stacks
03C8): expanding `ρ f = ∑ ι(cᵢ)·ρ(xᵢ)` and evaluating `δ̃` against `ρ ⊗ id` on both
expansions (coassociativity enters through `deltaTilde_comp_coaction`, at `f` and at each
`x i`) yields `∑ (ι(cᵢ) − ρ(cᵢ)) • wᵢ = 0`, which the `w`-cancellation kills. -/
theorem repr_coaction_mem_coinvariants [Module.Free R A] [Module.Finite R A]
    (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (hb : Module.Basis ι' B (B ⊗[R] A)) (x : ι' → B) (hx : ∀ i, hb i = ρ (x i))
    (f : B) (i : ι') : hb.repr (ρ f) i ∈ coinvariants ρ := by
  classical
  have hbr : ∀ g : B, deltaTilde R A (ρ g)
      = (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (ρ g) := fun g => by
    simpa [AlgHom.comp_apply] using
      AlgHom.congr_fun (deltaTilde_comp_coaction R A ρ hρ) g
  set c : ι' → B := fun j => hb.repr (ρ f) j with hcdef
  have hexp : ρ f = ∑ j, c j • hb j := by
    rw [hcdef]
    exact (hb.sum_repr (ρ f)).symm
  -- chain 1: δ̃ of the expansion
  have hchain1 : deltaTilde R A (ρ f)
      = ∑ j, ((c j ⊗ₜ[R] (1 : A)) : B ⊗[R] A)
          • (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (hb j) := by
    rw [hexp, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, map_mul,
      show (algebraMap B (B ⊗[R] A)) (c j) = c j ⊗ₜ[R] (1 : A) from rfl,
      deltaTilde_tmul_one, hx j, hbr (x j), ← hx j,
      Algebra.smul_def,
      show (algebraMap (B ⊗[R] A) ((B ⊗[R] A) ⊗[R] A)) (c j ⊗ₜ[R] (1 : A))
        = (c j ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) from rfl]
  -- chain 2: (ρ ⊗ id) of the expansion
  have hchain2 : deltaTilde R A (ρ f)
      = ∑ j, ρ (c j) • (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (hb j) := by
    rw [hbr f, hexp, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, map_mul,
      show (algebraMap B (B ⊗[R] A)) (c j) = c j ⊗ₜ[R] (1 : A) from rfl,
      Algebra.TensorProduct.map_tmul, map_one, Algebra.smul_def,
      show (algebraMap (B ⊗[R] A) ((B ⊗[R] A) ⊗[R] A)) (ρ (c j))
        = (ρ (c j)) ⊗ₜ[R] (1 : A) from rfl]
  -- subtract and cancel
  have hzero : ∑ j, ((c j ⊗ₜ[R] (1 : A)) - ρ (c j))
      • (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (hb j) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => sub_smul (c j ⊗ₜ[R] (1 : A)) (ρ (c j))
      ((Algebra.TensorProduct.map ρ (AlgHom.id R A)) (hb j))),
      Finset.sum_sub_distrib, ← hchain1, ← hchain2, sub_self]
  have := eq_zero_of_sum_smul_map_coaction_eq_zero R A ρ hρ hb _ hzero i
  rw [mem_coinvariants]
  rw [sub_eq_zero] at this
  exact this.symm

variable {R A} in
/-- **Stacks 03C8, first conclusion**: elements of `B` whose co-action images form a left
`B`-basis of `B ⊗[R] A` form a basis of `B` over the co-invariants.

Independence: push a relation through `ρ`, where co-invariance turns the coefficients
into left-inclusion scalars, and use independence of the given basis. Spanning: retract
the basis expansion of `ρ f` through the counit; the coordinates are co-invariant by
`repr_coaction_mem_coinvariants`. -/
noncomputable def coinvariantsBasis [Module.Free R A] [Module.Finite R A]
    (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (hb : Module.Basis ι' B (B ⊗[R] A)) (x : ι' → B) (hx : ∀ i, hb i = ρ (x i)) :
    Module.Basis ι' (coinvariants ρ) B :=
  Module.Basis.mk (v := x)
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have happ : ∑ i, ((g i : B)) • hb i = 0 := by
        have hρ0 : ∑ i, ρ (g i • x i) = 0 := by
          rw [← map_sum, hg, map_zero]
        rw [← hρ0]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Algebra.smul_def,
          show (algebraMap B (B ⊗[R] A)) ((g i : B)) = ((g i : B)) ⊗ₜ[R] (1 : A)
            from rfl,
          ← (mem_coinvariants).mp (g i).2, hx i,
          show (g i • x i : B) = (g i : B) * x i from rfl, map_mul]
      have := Fintype.linearIndependent_iff.mp hb.linearIndependent
        (fun i => ((g i : B))) happ j
      exact Subtype.ext this)
    (by
      intro f _
      have hσρ : ∀ g : B, counitRetraction R A (ρ g) = g := fun g => by
        simpa [AlgHom.comp_apply] using
          AlgHom.congr_fun (counitRetraction_comp_coaction R A ρ hρ) g
      have hσι : ∀ g : B, counitRetraction R A (g ⊗ₜ[R] (1 : A)) = g := fun g => by
        simpa [AlgHom.comp_apply] using
          AlgHom.congr_fun (counitRetraction_comp_includeLeft R A (B := B)) g
      have hexp : ρ f = ∑ j, hb.repr (ρ f) j • hb j := (hb.sum_repr (ρ f)).symm
      have hf : f = ∑ j, hb.repr (ρ f) j * x j := by
        conv_lhs => rw [← hσρ f, hexp, map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Algebra.smul_def, map_mul,
          show (algebraMap B (B ⊗[R] A)) (hb.repr (ρ f) j)
            = (hb.repr (ρ f) j) ⊗ₜ[R] (1 : A) from rfl,
          hσι (hb.repr (ρ f) j), hx j, hσρ (x j)]
      rw [hf]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have hmem : hb.repr (ρ f) j ∈ coinvariants ρ :=
        repr_coaction_mem_coinvariants R A ρ hρ hb x hx f j
      rw [show hb.repr (ρ f) j * x j
          = (⟨hb.repr (ρ f) j, hmem⟩ : coinvariants ρ) • x j from rfl]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))

variable {R A} in
@[simp]
theorem coinvariantsBasis_apply [Module.Free R A] [Module.Finite R A]
    (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (hb : Module.Basis ι' B (B ⊗[R] A)) (x : ι' → B) (hx : ∀ i, hb i = ρ (x i))
    (i : ι') : coinvariantsBasis ρ hρ hb x hx i = x i :=
  Module.Basis.mk_apply _ _ _

variable {R A} in
/-- The canonical Galois map as a left `B`-linear map. -/
noncomputable def galoisLinear (ρ : B →ₐ[R] B ⊗[R] A) :
    (B ⊗[coinvariants ρ] B) →ₗ[B] B ⊗[R] A where
  toFun := canonicalGaloisMap ρ
  map_add' := map_add _
  map_smul' := by
    intro b y
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact AlgHom.congr_fun (canonicalGaloisMap_comp_includeLeft ρ) b

/-- **Stacks 03C8, second conclusion**: the canonical Galois map is bijective — it is a
left `B`-linear map carrying the base-changed `coinvariantsBasis` to the given basis. -/
theorem bijective_canonicalGaloisMap_of_basis [Module.Free R A] [Module.Finite R A]
    (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (hb : Module.Basis ι' B (B ⊗[R] A)) (x : ι' → B) (hx : ∀ i, hb i = ρ (x i)) :
    Function.Bijective (canonicalGaloisMap ρ) := by
  classical
  set bT := (coinvariantsBasis ρ hρ hb x hx).baseChange B with hbT
  have hmap : galoisLinear ρ = (bT.equiv hb (Equiv.refl ι')).toLinearMap := by
    refine bT.ext (fun i => ?_)
    show galoisLinear ρ (bT i) = (bT.equiv hb (Equiv.refl ι')) (bT i)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply, hbT,
      Module.Basis.baseChange_apply, coinvariantsBasis_apply]
    show canonicalGaloisMap ρ ((1 : B) ⊗ₜ[coinvariants ρ] x i) = hb i
    rw [canonicalGaloisMap_tmul, hx i]
    rw [show ((1 : B) ⊗ₜ[R] (1 : A)) = (1 : B ⊗[R] A) from rfl, one_mul]
  have hbij : Function.Bijective (galoisLinear ρ) := by
    rw [hmap]
    exact (bT.equiv hb (Equiv.refl ι')).bijective
  exact hbij

end Bootstrap

end ModularCurves
