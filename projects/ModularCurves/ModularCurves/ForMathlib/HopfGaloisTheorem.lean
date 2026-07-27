/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.HopfGaloisBootstrap
import ModularCurves.ForMathlib.CoinvariantsPoints
import ModularCurves.ForMathlib.CoinvariantsBaseChange
import ModularCurves.ForMathlib.FlatLocalInfiniteResidue
import ModularCurves.ForMathlib.SemilocalBasis
import ModularCurves.ForMathlib.FaithfullyFlatEqualizer
import ModularCurves.ForMathlib.FaithfullyFlatFiniteDescent

/-!
# The Hopf–Galois theorem for co-actions of finite free Hopf algebras

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B6]`; Stacks 03BM =
SGA 3 Exp. V Théorème 4.1, affine case, comodule form): for a co-action
`ρ : B →ₐ[R] B ⊗[R] A` of a finite free commutative Hopf algebra such that the
product map `B ⊗[R] B → B ⊗[R] A`, `b ⊗ b' ↦ (b ⊗ 1)·ρ(b')` is surjective (the
action-pair is a closed immersion — e.g. a free translation action), `B` is a
Hopf–Galois extension of its co-invariants: the canonical Galois map is bijective
and `B` is faithfully flat over `coinvariants ρ`.

The proof is the per-prime bootstrap of the decomposition appendix `[HG-B6]`:
localize the co-invariants at a maximal ideal, pass to the flat local extension
with infinite residue field (`LocalPolynomialExtension`), base-change the
co-action, harvest the shifted basis via semi-locality + the semi-local basis
selection, conclude Galois upstairs by the bootstrap, and descend.
-/

namespace ModularCurves

open TensorProduct

section GeneralizedGalois

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (C₀ : Type*) [CommRing C₀] [Algebra C₀ B] [SMulCommClass R C₀ B]

/-- A co-action, re-based to scalars `C₀` mapping into the co-invariants (the `C₀`-algebra
structure on `B ⊗[R] A` is `Algebra.TensorProduct.leftAlgebra` through the left factor). -/
noncomputable def coactionOver (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    B →ₐ[C₀] B ⊗[R] A where
  toRingHom := ρ.toRingHom
  commutes' := fun c => by
    show ρ (algebraMap C₀ B c) = algebraMap C₀ (B ⊗[R] A) c
    rw [hcoinv c, Algebra.TensorProduct.algebraMap_apply]

@[simp]
theorem coactionOver_apply (ρ : B →ₐ[R] B ⊗[R] A) (hcoinv) (b : B) :
    coactionOver R A C₀ ρ hcoinv b = ρ b := rfl

/-- The generalized Galois product map over `C₀`: `b ⊗ b' ↦ (b ⊗ 1) · ρ(b')`. -/
noncomputable def galoisProductMap (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    (B ⊗[C₀] B) →ₐ[C₀] B ⊗[R] A :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.includeLeft (S := C₀))
    (coactionOver R A C₀ ρ hcoinv)

@[simp]
theorem galoisProductMap_tmul (ρ : B →ₐ[R] B ⊗[R] A) (hcoinv) (b b' : B) :
    galoisProductMap R A C₀ ρ hcoinv (b ⊗ₜ[C₀] b')
      = (b ⊗ₜ[R] (1 : A)) * ρ b' := by
  rw [galoisProductMap, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply, coactionOver_apply]

/-- The generalized Galois product map as a left `B`-linear map. -/
noncomputable def galoisProductLinear (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A)) :
    (B ⊗[C₀] B) →ₗ[B] B ⊗[R] A where
  toFun := galoisProductMap R A C₀ ρ hcoinv
  map_add' := map_add _
  map_smul' := by
    intro b y
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [show (algebraMap B (B ⊗[C₀] B)) b = b ⊗ₜ[C₀] (1 : B) from rfl,
      galoisProductMap_tmul, map_one, mul_one]
    rfl

/-- **Generalized bootstrap conclusion** (the `C₀`-form of Stacks 03C8's second half):
if `(x i)` is a `C₀`-basis of `B` and the `ρ (x i)` form a left `B`-basis of `B ⊗[R] A`,
the generalized Galois product map over `C₀` is bijective. -/
theorem bijective_galoisProductMap_of_basis
    {ι' : Type*} [Fintype ι'] (ρ : B →ₐ[R] B ⊗[R] A)
    (hcoinv : ∀ c : C₀, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ[R] (1 : A))
    (hb : Module.Basis ι' B (B ⊗[R] A)) (bx : Module.Basis ι' C₀ B)
    (hx : ∀ i, hb i = ρ (bx i)) :
    Function.Bijective (galoisProductMap R A C₀ ρ hcoinv) := by
  classical
  set bT := bx.baseChange B with hbT
  have hmap : galoisProductLinear R A C₀ ρ hcoinv
      = (bT.equiv hb (Equiv.refl ι')).toLinearMap := by
    refine bT.ext (fun i => ?_)
    show galoisProductMap R A C₀ ρ hcoinv (bT i) = (bT.equiv hb (Equiv.refl ι')) (bT i)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply, hbT, Module.Basis.baseChange_apply]
    rw [galoisProductMap_tmul, hx i,
      show ((1 : B) ⊗ₜ[R] (1 : A)) = (1 : B ⊗[R] A) from rfl, one_mul]
  have hbij : Function.Bijective (galoisProductLinear R A C₀ ρ hcoinv) := by
    rw [hmap]
    exact (bT.equiv hb (Equiv.refl ι')).bijective
  exact hbij

end GeneralizedGalois

section FlatCoverInjectivity

variable {C : Type*} [CommRing C]
variable {M : Type*} [AddCommGroup M] [Module C M]
variable {N : Type*} [AddCommGroup N] [Module C N]

/-- **Flat-cover injectivity**: a linear map over `C` is injective as soon as its base
change to every flat local extension `IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)`
(`P` maximal) is injective. The extensions are faithfully flat over each localization,
so the kernel vanishes locally, hence globally. -/
theorem injective_of_forall_lTensor_localPolynomialExtension (F : M →ₗ[C] N)
    (H : ∀ (P : Ideal C) [P.IsMaximal], Function.Injective
      (LinearMap.lTensor (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) F)) :
    Function.Injective F := by
  intro x y hxy
  haveI hloc : ∀ (P : Ideal C) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk C (Localization.AtPrime P) M 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) _).mpr
      (TensorProduct.isBaseChange C M (Localization.AtPrime P))
  refine Module.eq_of_localization_maximal
    (fun P _ => (Localization.AtPrime P) ⊗[C] M)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) M 1)
    x y (fun P hP => ?_)
  -- pass from the localization to the flat local extension, where `H` applies
  have hmkinj : Function.Injective (TensorProduct.mk (Localization.AtPrime P)
      (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
      ((Localization.AtPrime P) ⊗[C] M) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective _
  have hcancelinj := (TensorProduct.AlgebraTensorModule.cancelBaseChange C
    (Localization.AtPrime P) (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
    (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) M).injective
  apply hmkinj
  apply hcancelinj
  -- compute both composites down to `1 ⊗ₜ[C] _` in the extension
  have hval : ∀ m : M,
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C
        (Localization.AtPrime P) (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
        (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) M)
      (TensorProduct.mk (Localization.AtPrime P)
        (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
        ((Localization.AtPrime P) ⊗[C] M) 1
        (TensorProduct.mk C (Localization.AtPrime P) M 1 m))
      = (1 : IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) ⊗ₜ[C] m := by
    intro m
    rw [TensorProduct.mk_apply, TensorProduct.mk_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [hval x, hval y]
  exact H P (by
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hxy])

/-- **Flat-cover flatness, localized glue**: flatness over `C` follows from flatness of
the localizations at all maximal ideals. -/
theorem flat_of_forall_flat_localized
    (H : ∀ (P : Ideal C) [P.IsMaximal],
      Module.Flat C ((Localization.AtPrime P) ⊗[C] M)) :
    Module.Flat C M := by
  classical
  haveI hloc : ∀ (P : Ideal C) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk C (Localization.AtPrime P) M 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) _).mpr
      (TensorProduct.isBaseChange C M (Localization.AtPrime P))
  exact Module.flat_of_isLocalized_maximal (R := C) (S := C) (M := M)
    (fun P _ => (Localization.AtPrime P) ⊗[C] M)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) M 1)
    (fun P _ => H P)

/-- **Per-prime flatness descent**: flatness of the localized module descends from a
faithfully flat extension of the localization. The extension is abstract so consumers can
discharge the scalar structure per prime. -/
theorem flat_localized_of_flat_extension (P : Ideal C) [P.IsMaximal]
    (E : Type*) [CommRing E] [Algebra C E] [Algebra (Localization.AtPrime P) E]
    [IsScalarTower C (Localization.AtPrime P) E]
    [Module.FaithfullyFlat (Localization.AtPrime P) E]
    (hE : Module.Flat E (E ⊗[C] M)) :
    Module.Flat C ((Localization.AtPrime P) ⊗[C] M) := by
  haveI hflat2 : Module.Flat E
      (E ⊗[Localization.AtPrime P] ((Localization.AtPrime P) ⊗[C] M)) :=
    (Module.Flat.equiv_iff
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        C (Localization.AtPrime P) E E M)).mpr hE
  haveI hflatCp : Module.Flat (Localization.AtPrime P)
      ((Localization.AtPrime P) ⊗[C] M) :=
    Module.Flat.of_flat_tensorProduct (R := Localization.AtPrime P)
      (M := (Localization.AtPrime P) ⊗[C] M) (S := E)
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
    ((Localization.AtPrime P) ⊗[C] M)).mp hflatCp

/-- **Flat-cover injectivity**, abstract form: injectivity of a `C`-linear map may be
checked after base change to a family of faithfully flat extensions of the localizations
at maximal ideals. -/
theorem injective_of_forall_lTensor_extension
    (E : ∀ (P : Ideal C) [P.IsMaximal], Type*)
    [∀ (P : Ideal C) [P.IsMaximal], CommRing (E P)]
    [instEC : ∀ (P : Ideal C) [P.IsMaximal], Algebra C (E P)]
    [instECp : ∀ (P : Ideal C) [P.IsMaximal], Algebra (Localization.AtPrime P) (E P)]
    [instTower : ∀ (P : Ideal C) [P.IsMaximal],
      IsScalarTower C (Localization.AtPrime P) (E P)]
    [instFF : ∀ (P : Ideal C) [P.IsMaximal],
      Module.FaithfullyFlat (Localization.AtPrime P) (E P)]
    (F : M →ₗ[C] N)
    (H : ∀ (P : Ideal C) [P.IsMaximal], Function.Injective
      (LinearMap.lTensor (E P) F)) :
    Function.Injective F := by
  intro x y hxy
  haveI hloc : ∀ (P : Ideal C) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk C (Localization.AtPrime P) M 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) _).mpr
      (TensorProduct.isBaseChange C M (Localization.AtPrime P))
  refine Module.eq_of_localization_maximal
    (fun P _ => (Localization.AtPrime P) ⊗[C] M)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) M 1)
    x y (fun P hP => ?_)
  have hmkinj : Function.Injective (TensorProduct.mk (Localization.AtPrime P)
      (E P) ((Localization.AtPrime P) ⊗[C] M) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective _
  have hcancelinj := (TensorProduct.AlgebraTensorModule.cancelBaseChange C
    (Localization.AtPrime P) (E P) (E P) M).injective
  apply hmkinj
  apply hcancelinj
  have hval : ∀ m : M,
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C
        (Localization.AtPrime P) (E P) (E P) M)
      (TensorProduct.mk (Localization.AtPrime P) (E P)
        ((Localization.AtPrime P) ⊗[C] M) 1
        (TensorProduct.mk C (Localization.AtPrime P) M 1 m))
      = (1 : E P) ⊗ₜ[C] m := by
    intro m
    rw [TensorProduct.mk_apply, TensorProduct.mk_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [hval x, hval y]
  exact H P (by
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hxy])

end FlatCoverInjectivity

section PerPrime

open TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (ρ : B →ₐ[R] B ⊗[R] A)
variable (C' : Type*) [CommRing C'] [Algebra R C']
variable [Algebra (coinvariants ρ) C'] [IsScalarTower R (coinvariants ρ) C']

/-- The scalars of a base change land in the co-invariants of the base-changed
co-action. -/
theorem tmul_one_mem_coinvariants_coactionBaseChange (c' : C') :
    (c' ⊗ₜ[coinvariants ρ] (1 : B)) ∈ coinvariants (coactionBaseChange R A ρ C') := by
  rw [mem_coinvariants, coactionBaseChange_tmul, map_one]
  rw [show (c' ⊗ₜ[coinvariants ρ] (1 : B ⊗[R] A))
      = (baseChangeAssoc R A ρ C') ((c' ⊗ₜ[coinvariants ρ] (1 : B)) ⊗ₜ[R] (1 : A)) from by
    rw [baseChangeAssoc_tmul_one, Algebra.TensorProduct.map_tmul]
    rfl]
  rw [AlgEquiv.symm_apply_apply]

/-- The scalar map onto the co-invariants of the base-changed co-action. -/
noncomputable def baseChangeCoinvariantsMap :
    C' →+* coinvariants (coactionBaseChange R A ρ C') :=
  (Algebra.TensorProduct.includeLeftRingHom (R := coinvariants ρ) (A := C') (B := B)).codRestrict
    (coinvariants (coactionBaseChange R A ρ C')).toSubring
    (tmul_one_mem_coinvariants_coactionBaseChange R A ρ C')

@[simp]
theorem coe_baseChangeCoinvariantsMap (c' : C') :
    (baseChangeCoinvariantsMap R A ρ C' c' : C' ⊗[coinvariants ρ] B)
      = c' ⊗ₜ[coinvariants ρ] (1 : B) := rfl

/-- Over a flat base change, the scalar map onto the base-changed co-invariants is
surjective (Stacks 03BK(3)). -/
theorem surjective_baseChangeCoinvariantsMap [Module.Flat (coinvariants ρ) C'] :
    Function.Surjective (baseChangeCoinvariantsMap R A ρ C') := by
  rintro ⟨x, hx⟩
  obtain ⟨c', hc'⟩ := (mem_coinvariants_coactionBaseChange_iff R A ρ C' x).mp hx
  exact ⟨c', Subtype.ext hc'⟩

omit [Algebra R C'] [IsScalarTower R (coinvariants ρ) C'] in
/-- Over a flat base change, the scalar map into the base-changed algebra is injective
(tensor the inclusion `C ⊆ B` with the flat module `C'`). -/
theorem injective_tmul_one_of_flat [Module.Flat (coinvariants ρ) C'] :
    Function.Injective (fun c' : C' => c' ⊗ₜ[coinvariants ρ] (1 : B)) := by
  have hval : Function.Injective (Algebra.linearMap (coinvariants ρ) B) :=
    fun x y h => Subtype.ext h
  have hlt : Function.Injective
      ((Algebra.linearMap (coinvariants ρ) B).lTensor C') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hval
  have hcomp : (fun c' : C' => c' ⊗ₜ[coinvariants ρ] (1 : B))
      = ((Algebra.linearMap (coinvariants ρ) B).lTensor C')
        ∘ (TensorProduct.rid (coinvariants ρ) C').symm := by
    funext c'
    show c' ⊗ₜ[coinvariants ρ] (1 : B)
      = ((Algebra.linearMap (coinvariants ρ) B).lTensor C')
          ((TensorProduct.rid (coinvariants ρ) C').symm c')
    rw [TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul]
    rw [show (Algebra.linearMap (coinvariants ρ) B) (1 : coinvariants ρ) = (1 : B) from
      map_one (algebraMap (coinvariants ρ) B)]
  rw [hcomp]
  exact hlt.comp (TensorProduct.rid (coinvariants ρ) C').symm.injective

omit [Algebra R C'] [IsScalarTower R (coinvariants ρ) C'] in
/-- The base-changed algebra is nontrivial when the scalars are. -/
theorem nontrivial_baseChange_of_flat [Module.Flat (coinvariants ρ) C'] [Nontrivial C'] :
    Nontrivial (C' ⊗[coinvariants ρ] B) :=
  ⟨(1 : C') ⊗ₜ[coinvariants ρ] (1 : B), (0 : C') ⊗ₜ[coinvariants ρ] (1 : B),
    (injective_tmul_one_of_flat R A ρ C').ne one_ne_zero⟩

/-- The co-invariants of a flat local base change form a local ring (surjective image of
the local scalars). -/
theorem isLocalRing_coinvariants_coactionBaseChange
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C'] :
    IsLocalRing (coinvariants (coactionBaseChange R A ρ C')) := by
  haveI : Nontrivial (C' ⊗[coinvariants ρ] B) := nontrivial_baseChange_of_flat R A ρ C'
  haveI : Nontrivial (coinvariants (coactionBaseChange R A ρ C')) := by
    refine ⟨1, 0, fun h => ?_⟩
    have := congrArg (Subtype.val) h
    exact one_ne_zero this
  exact IsLocalRing.of_surjective' (baseChangeCoinvariantsMap R A ρ C')
    (surjective_baseChangeCoinvariantsMap R A ρ C')

/-- The residue field of the base-changed co-invariants is (up to isomorphism) the
residue field of the scalars, hence inherits infiniteness: the scalar map is a
surjective local homomorphism of local rings. -/
theorem infinite_residueField_coinvariants_coactionBaseChange
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C']
    [IsLocalRing (coinvariants (coactionBaseChange R A ρ C'))]
    [Infinite (IsLocalRing.ResidueField C')] :
    Infinite (IsLocalRing.ResidueField (coinvariants (coactionBaseChange R A ρ C'))) := by
  haveI hπloc : IsLocalHom (baseChangeCoinvariantsMap R A ρ C') :=
    .of_surjective _ (surjective_baseChangeCoinvariantsMap R A ρ C')
  set φ := (IsLocalRing.residue (coinvariants (coactionBaseChange R A ρ C'))).comp
    (baseChangeCoinvariantsMap R A ρ C') with hφdef
  have hφs : Function.Surjective φ :=
    IsLocalRing.residue_surjective.comp (surjective_baseChangeCoinvariantsMap R A ρ C')
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal C' := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · intro htop
      have h1 : φ 1 = 0 := by
        rw [← RingHom.mem_ker, htop]
        trivial
      rw [map_one] at h1
      exact one_ne_zero h1
    · intro x hx
      have hmem : baseChangeCoinvariantsMap R A ρ C' x
          ∈ IsLocalRing.maximalIdeal (coinvariants (coactionBaseChange R A ρ C')) := by
        by_contra hnot
        have hunit := IsLocalRing.notMem_maximalIdeal.mp hnot
        exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx)
          (IsUnit.of_map _ x hunit)
      rw [RingHom.mem_ker, hφdef, RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hequiv : IsLocalRing.ResidueField C'
      ≃+* IsLocalRing.ResidueField (coinvariants (coactionBaseChange R A ρ C')) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφs)
  exact Infinite.of_injective hequiv hequiv.injective

/-- The `R`-level Galois precursor `B ⊗[R] B → B ⊗[R] A`, `b ⊗ b' ↦ (b ⊗ 1)·ρ(b')`.
Its surjectivity (the action-pair being a closed immersion) is the geometric input of the
Hopf–Galois theorem. -/
noncomputable def galoisPrecursor : (B ⊗[R] B) →ₐ[R] B ⊗[R] A :=
  Algebra.TensorProduct.productMap Algebra.TensorProduct.includeLeft ρ

@[simp]
theorem galoisPrecursor_tmul (b b' : B) :
    galoisPrecursor R A ρ (b ⊗ₜ[R] b') = (b ⊗ₜ[R] (1 : A)) * ρ b' := by
  rw [galoisPrecursor, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply]

/-- The multiplicative heart of the span computation: a base-changed pure tensor acting on
a base-changed co-action value realizes the associated precursor term. -/
theorem smul_coactionBaseChange_one_tmul (c' : C') (b c : B) :
    ((c' ⊗ₜ[coinvariants ρ] b : C' ⊗[coinvariants ρ] B))
        • (coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] c))
      = (baseChangeAssoc R A ρ C').symm
          (c' ⊗ₜ[coinvariants ρ] ((b ⊗ₜ[R] (1 : A)) * ρ c)) := by
  rw [Algebra.smul_def, coactionBaseChange_tmul]
  rw [show (algebraMap (C' ⊗[coinvariants ρ] B) ((C' ⊗[coinvariants ρ] B) ⊗[R] A))
      (c' ⊗ₜ[coinvariants ρ] b) = (c' ⊗ₜ[coinvariants ρ] b) ⊗ₜ[R] (1 : A) from rfl]
  rw [show ((c' ⊗ₜ[coinvariants ρ] b) ⊗ₜ[R] (1 : A) :
      (C' ⊗[coinvariants ρ] B) ⊗[R] A)
      = (baseChangeAssoc R A ρ C').symm
          ((Algebra.TensorProduct.map (AlgHom.id C' C') (includeLeftOverCoinvariants ρ))
            (c' ⊗ₜ[coinvariants ρ] b)) from by
    rw [← baseChangeAssoc_tmul_one, AlgEquiv.symm_apply_apply]]
  rw [← map_mul, Algebra.TensorProduct.map_tmul]
  congr 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

/-- **The span condition** (feeding Stacks 03C1): when the Galois precursor is surjective,
the range of the base-changed co-action spans `(C' ⊗[C] B) ⊗[R] A` over `C' ⊗[C] B`. -/
theorem span_range_coactionBaseChange_eq_top
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Submodule.span (C' ⊗[coinvariants ρ] B)
      (LinearMap.range (coactionOverCoinvariants
        (coactionBaseChange R A ρ C')).toLinearMap :
          Set ((C' ⊗[coinvariants ρ] B) ⊗[R] A)) = ⊤ := by
  rw [eq_top_iff]
  rintro u -
  have hgen : ∀ w : C' ⊗[coinvariants ρ] (B ⊗[R] A),
      (baseChangeAssoc R A ρ C').symm w ∈ Submodule.span (C' ⊗[coinvariants ρ] B)
        (LinearMap.range (coactionOverCoinvariants
          (coactionBaseChange R A ρ C')).toLinearMap :
            Set ((C' ⊗[coinvariants ρ] B) ⊗[R] A)) := by
    intro w
    induction w with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add w₁ w₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | tmul c' v =>
        obtain ⟨t, ht⟩ := hsurj v
        rw [← ht]
        clear ht
        induction t with
        | zero =>
            rw [map_zero, TensorProduct.tmul_zero, map_zero]
            exact Submodule.zero_mem _
        | add t₁ t₂ h₁ h₂ =>
            rw [map_add, TensorProduct.tmul_add, map_add]
            exact Submodule.add_mem _ h₁ h₂
        | tmul b c =>
            rw [galoisPrecursor_tmul, ← smul_coactionBaseChange_one_tmul]
            refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
            exact ⟨(1 : C') ⊗ₜ[coinvariants ρ] c, rfl⟩
  have := hgen (baseChangeAssoc R A ρ C' u)
  rwa [AlgEquiv.symm_apply_apply] at this

/-- **The shifted basis, per prime** (Stacks 03C1 applied over the flat local base change
with infinite residue field): elements of the base-changed algebra whose co-action images
form a left basis of the base-changed comodule algebra. -/
theorem exists_shifted_basis_coactionBaseChange
    [Module.Free R A] [Module.Finite R A]
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (hρ : IsCoaction ρ) (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    ∃ x : Fin (Module.finrank (C' ⊗[coinvariants ρ] B)
        ((C' ⊗[coinvariants ρ] B) ⊗[R] A)) → C' ⊗[coinvariants ρ] B,
      ∃ hb : Module.Basis (Fin (Module.finrank (C' ⊗[coinvariants ρ] B)
        ((C' ⊗[coinvariants ρ] B) ⊗[R] A))) (C' ⊗[coinvariants ρ] B)
        ((C' ⊗[coinvariants ρ] B) ⊗[R] A),
      ∀ i, hb i = coactionBaseChange R A ρ C' (x i) := by
  classical
  haveI hCC : IsLocalRing (coinvariants (coactionBaseChange R A ρ C')) :=
    isLocalRing_coinvariants_coactionBaseChange R A ρ C'
  haveI := infinite_residueField_coinvariants_coactionBaseChange R A ρ C'
  haveI : Nontrivial (C' ⊗[coinvariants ρ] B) := nontrivial_baseChange_of_flat R A ρ C'
  have hfin := finite_setOf_isMaximal_of_isLocalRing R A
    (coactionBaseChange R A ρ C') (isCoaction_coactionBaseChange R A ρ C' hρ)
  obtain ⟨y, hyN, b, hb⟩ := Submodule.exists_basis_mem_of_span_eq_top
    (R := coinvariants (coactionBaseChange R A ρ C'))
    (n := fun j : Fin hfin.toFinset.card =>
      ((hfin.toFinset.equivFin.symm j : hfin.toFinset) : Ideal (C' ⊗[coinvariants ρ] B)))
    (fun j => hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm j).2)
    (fun P hP => ⟨hfin.toFinset.equivFin ⟨P, hfin.mem_toFinset.mpr hP⟩, by
      rw [Equiv.symm_apply_apply]⟩)
    (fun j => maximalIdeal_map_le_of_isMaximal R A _
      (isCoaction_coactionBaseChange R A ρ C' hρ) _
      (hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm j).2))
    (r := Module.finrank (C' ⊗[coinvariants ρ] B) ((C' ⊗[coinvariants ρ] B) ⊗[R] A))
    rfl
    (LinearMap.range (coactionOverCoinvariants (coactionBaseChange R A ρ C')).toLinearMap)
    (span_range_coactionBaseChange_eq_top R A ρ C' hsurj)
  choose xf hxf using fun i => LinearMap.mem_range.mp (hyN i)
  exact ⟨xf, b, fun i => by rw [hb i, ← hxf i]; rfl⟩

/-- A basis of the base-changed algebra over the base-changed co-invariants is already a
basis over the scalars `C'`: the scalar map onto the co-invariants is bijective and the
two scalar actions agree. -/
noncomputable def basisOverScalarsOfBasisOverCoinvariants
    [Module.Flat (coinvariants ρ) C'] {ι' : Type*} [Fintype ι']
    (bx : Module.Basis ι' (coinvariants (coactionBaseChange R A ρ C'))
      (C' ⊗[coinvariants ρ] B)) :
    Module.Basis ι' C' (C' ⊗[coinvariants ρ] B) :=
  Module.Basis.mk (v := bx)
    (by
      have hsmul : ∀ (c' : C') (v : C' ⊗[coinvariants ρ] B),
          c' • v = (baseChangeCoinvariantsMap R A ρ C' c') • v := by
        intro c' v
        rw [Algebra.smul_def, Algebra.smul_def]
        congr 1
      have hπinj : Function.Injective (baseChangeCoinvariantsMap R A ρ C') := by
        intro a b h
        have := congrArg Subtype.val h
        exact injective_tmul_one_of_flat R A ρ C' this
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h2 : ∑ j, (baseChangeCoinvariantsMap R A ρ C' (g j)) • bx j = 0 := by
        rw [← hg]
        exact Finset.sum_congr rfl (fun j _ => (hsmul (g j) (bx j)).symm)
      have := Fintype.linearIndependent_iff.mp bx.linearIndependent
        (fun j => baseChangeCoinvariantsMap R A ρ C' (g j)) h2 i
      exact hπinj (by rw [this, map_zero]))
    (by
      have hsmul : ∀ (c' : C') (v : C' ⊗[coinvariants ρ] B),
          c' • v = (baseChangeCoinvariantsMap R A ρ C' c') • v := by
        intro c' v
        rw [Algebra.smul_def, Algebra.smul_def]
        congr 1
      intro v _
      have hexp : v = ∑ j, bx.repr v j • bx j := (bx.sum_repr v).symm
      obtain ⟨g, hg⟩ := Classical.axiomOfChoice
        (fun j => surjective_baseChangeCoinvariantsMap R A ρ C' (bx.repr v j))
      rw [hexp]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [← hg j, ← hsmul (g j) (bx j)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))

@[simp]
theorem basisOverScalarsOfBasisOverCoinvariants_apply
    [Module.Flat (coinvariants ρ) C'] {ι' : Type*} [Fintype ι']
    (bx : Module.Basis ι' (coinvariants (coactionBaseChange R A ρ C'))
      (C' ⊗[coinvariants ρ] B)) (i : ι') :
    basisOverScalarsOfBasisOverCoinvariants R A ρ C' bx i = bx i :=
  Module.Basis.mk_apply _ _ _

/-- **The per-prime Galois bijectivity**: over a flat local base change with infinite
residue field, the generalized Galois product map of the base-changed co-action, with
scalars the base ring `C'` itself, is bijective. -/
theorem bijective_galoisProductMap_coactionBaseChange
    [Module.Free R A] [Module.Finite R A]
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (hρ : IsCoaction ρ) (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Function.Bijective (galoisProductMap R A C' (coactionBaseChange R A ρ C')
      (fun c' => (mem_coinvariants).mp
        (tmul_one_mem_coinvariants_coactionBaseChange R A ρ C' c'))) := by
  classical
  obtain ⟨x, hb, hx⟩ := exists_shifted_basis_coactionBaseChange R A ρ C' hρ hsurj
  have hρ' : IsCoaction (coactionBaseChange R A ρ C') :=
    isCoaction_coactionBaseChange R A ρ C' hρ
  refine bijective_galoisProductMap_of_basis R A C' _ _ hb
    (basisOverScalarsOfBasisOverCoinvariants R A ρ C'
      (coinvariantsBasis (coactionBaseChange R A ρ C') hρ' hb x hx)) (fun i => ?_)
  rw [basisOverScalarsOfBasisOverCoinvariants_apply, coinvariantsBasis_apply]
  exact hx i

section ModuleLeftErased

attribute [-instance] Subalgebra.moduleLeft

/-- The canonical Galois map as a `C`-linear map built in the module regime, with
`Subalgebra.moduleLeft` erased so that the tensor-product module structure on the source
is the standard one (the `AlgHom`-derived `toLinearMap` would carry the algebra-regime
instances, which do not match the module-level induction machinery). -/
noncomputable def canonicalGaloisLinear :
    (B ⊗[coinvariants ρ] B) →ₗ[coinvariants ρ] B ⊗[R] A where
  toFun := canonicalGaloisMap ρ
  map_add' := map_add _
  map_smul' := fun c y => map_smul (canonicalGaloisMap ρ) c y

@[simp]
theorem canonicalGaloisLinear_apply (u : B ⊗[coinvariants ρ] B) :
    canonicalGaloisLinear R A ρ u = canonicalGaloisMap ρ u := rfl

/-- The base-change embedding `B ⊗[R] A → (C' ⊗[C] B) ⊗[R] A`, `x ⊗ a ↦ (1 ⊗ x) ⊗ a`,
as an `R`-linear map in the module regime. -/
noncomputable def baseChangeEmbed : (B ⊗[R] A) →ₗ[R]
    ((C' ⊗[coinvariants ρ] B) ⊗[R] A) :=
  TensorProduct.map
    (LinearMap.restrictScalars R (TensorProduct.mk (coinvariants ρ) C' B 1))
    LinearMap.id

@[simp]
theorem baseChangeEmbed_tmul (x : B) (a : A) :
    baseChangeEmbed R A ρ C' (x ⊗ₜ[R] a)
      = ((1 : C') ⊗ₜ[coinvariants ρ] x) ⊗ₜ[R] a := rfl

/-- The base-changed co-action evaluated on `1 ⊗ c` is the embedded co-action value. -/
theorem coactionBaseChange_one_tmul_eq_embed (c : B) :
    coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] c)
      = baseChangeEmbed R A ρ C' (ρ c) := by
  rw [coactionBaseChange_tmul]
  induction ρ c with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | add w₁ w₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂]
  | tmul x a =>
      rw [baseChangeEmbed_tmul]
      refine ((baseChangeAssoc R A ρ C').symm_apply_eq).mpr ?_
      show (1 : C') ⊗ₜ[coinvariants ρ] (x ⊗ₜ[R] a)
        = (Algebra.TensorProduct.assoc R (coinvariants ρ) C' C' B A)
            (((1 : C') ⊗ₜ[coinvariants ρ] x) ⊗ₜ[R] a)
      rw [Algebra.TensorProduct.assoc_tmul]

/-- The heterobasic associator in the module regime. -/
noncomputable def assocT :
    ((C' ⊗[coinvariants ρ] B) ⊗[R] A) ≃ₗ[C']
      C' ⊗[coinvariants ρ] (B ⊗[R] A) :=
  TensorProduct.AlgebraTensorModule.assoc R (coinvariants ρ) C' C' B A

/-- The module-regime form of the multiplicative heart: a base-changed pure tensor acting
on a base-changed co-action value. -/
theorem smul_coactionBaseChange_one_tmul' (c' : C') (b c : B) :
    ((c' ⊗ₜ[coinvariants ρ] b : C' ⊗[coinvariants ρ] B))
        • (coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] c))
      = (assocT R A ρ C').symm
          (c' ⊗ₜ[coinvariants ρ] ((b ⊗ₜ[R] (1 : A)) * ρ c)) := by
  rw [coactionBaseChange_one_tmul_eq_embed]
  induction ρ c with
  | zero =>
      rw [map_zero, smul_zero, mul_zero, TensorProduct.tmul_zero,
        map_zero (assocT R A ρ C').symm]
  | add w₁ w₂ h₁ h₂ =>
      rw [map_add, smul_add, h₁, h₂, mul_add, TensorProduct.tmul_add,
        map_add (assocT R A ρ C').symm]
  | tmul x a =>
      rw [baseChangeEmbed_tmul]
      rw [show ((c' ⊗ₜ[coinvariants ρ] b : C' ⊗[coinvariants ρ] B))
          • ((((1 : C') ⊗ₜ[coinvariants ρ] x) ⊗ₜ[R] a) :
              (C' ⊗[coinvariants ρ] B) ⊗[R] A)
          = ((c' ⊗ₜ[coinvariants ρ] (b * x)) ⊗ₜ[R] a) from by
        rw [TensorProduct.smul_tmul', smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
      rw [show ((b ⊗ₜ[R] (1 : A)) * (x ⊗ₜ[R] a) : B ⊗[R] A)
          = (b * x) ⊗ₜ[R] a from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
      rw [assocT, TensorProduct.AlgebraTensorModule.assoc_symm_tmul]

/-- The comparison-square identity: composing the two associativity/base-change equivalences
with the generalized Galois product map of the base-changed co-action recovers
`lTensor C' (canonicalGaloisLinear …)`. The heart of `injective_lTensor_canonicalGaloisMap`,
proved by tensor induction. -/
theorem lTensor_canonicalGaloisMap_eq_galoisProductMap
    [Module.Free R A] [Module.Finite R A] [Module.Flat (coinvariants ρ) C'] :
    ∀ u : C' ⊗[coinvariants ρ] (B ⊗[coinvariants ρ] B),
      (assocT R A ρ C')
        (galoisProductMap R A C' (coactionBaseChange R A ρ C')
          (fun c' => (mem_coinvariants).mp
            (tmul_one_mem_coinvariants_coactionBaseChange R A ρ C' c'))
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange (coinvariants ρ) C'
              (C' ⊗[coinvariants ρ] B) (C' ⊗[coinvariants ρ] B) B).symm
            ((TensorProduct.AlgebraTensorModule.assoc (coinvariants ρ) (coinvariants ρ) C'
                C' B B).symm u)))
      = (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ)) u := by
  classical
  set S₁ := (TensorProduct.AlgebraTensorModule.assoc (coinvariants ρ) (coinvariants ρ) C'
    C' B B).symm with hS₁
  set S₂ := (TensorProduct.AlgebraTensorModule.cancelBaseChange (coinvariants ρ) C'
    (C' ⊗[coinvariants ρ] B) (C' ⊗[coinvariants ρ] B) B).symm with hS₂
  set G := galoisProductMap R A C' (coactionBaseChange R A ρ C')
    (fun c' => (mem_coinvariants).mp
      (tmul_one_mem_coinvariants_coactionBaseChange R A ρ C' c')) with hG
  intro u
  induction u with
  | zero =>
      rw [map_zero S₁, map_zero S₂, map_zero G, map_zero (assocT R A ρ C'),
        map_zero (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ))]
  | add u₁ u₂ h₁ h₂ =>
      rw [map_add S₁, map_add S₂, map_add G, map_add (assocT R A ρ C'), h₁, h₂,
        ← map_add (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ))]
  | tmul c' w =>
      induction w with
      | zero =>
          rw [TensorProduct.tmul_zero, map_zero S₁, map_zero S₂, map_zero G,
            map_zero (assocT R A ρ C'),
            map_zero (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ))]
      | add w₁ w₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, map_add S₁, map_add S₂, map_add G,
            map_add (assocT R A ρ C'), h₁, h₂,
            ← map_add (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ)),
            ← TensorProduct.tmul_add]
      | tmul b₁ b₂ =>
          rw [hS₁, TensorProduct.AlgebraTensorModule.assoc_symm_tmul, hS₂,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hG,
            galoisProductMap_tmul, LinearMap.lTensor_tmul]
          rw [show canonicalGaloisLinear R A ρ (b₁ ⊗ₜ[coinvariants ρ] b₂)
              = (b₁ ⊗ₜ[R] (1 : A)) * ρ b₂ from canonicalGaloisMap_tmul ρ b₁ b₂]
          rw [show ((c' ⊗ₜ[coinvariants ρ] b₁ : C' ⊗[coinvariants ρ] B) ⊗ₜ[R] (1 : A))
                * (coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] b₂))
              = ((c' ⊗ₜ[coinvariants ρ] b₁ : C' ⊗[coinvariants ρ] B))
                • (coactionBaseChange R A ρ C' ((1 : C') ⊗ₜ[coinvariants ρ] b₂)) from by
            rw [Algebra.smul_def]
            rfl]
          rw [smul_coactionBaseChange_one_tmul' R A ρ C' c' b₁ b₂,
            LinearEquiv.apply_symm_apply]

/-- **The comparison square**: base-changing the canonical Galois map along `C → C'`
realizes the generalized Galois product map of the base-changed co-action, so its
injectivity descends per prime. -/
theorem injective_lTensor_canonicalGaloisMap
    [Module.Free R A] [Module.Finite R A]
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (hρ : IsCoaction ρ) (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Function.Injective
      (LinearMap.lTensor C' (canonicalGaloisLinear R A ρ)) := by
  classical
  have hsq := lTensor_canonicalGaloisMap_eq_galoisProductMap R A ρ C'
  set S₁ := (TensorProduct.AlgebraTensorModule.assoc (coinvariants ρ) (coinvariants ρ) C'
    C' B B).symm with hS₁
  set S₂ := (TensorProduct.AlgebraTensorModule.cancelBaseChange (coinvariants ρ) C'
    (C' ⊗[coinvariants ρ] B) (C' ⊗[coinvariants ρ] B) B).symm with hS₂
  set G := galoisProductMap R A C' (coactionBaseChange R A ρ C')
    (fun c' => (mem_coinvariants).mp
      (tmul_one_mem_coinvariants_coactionBaseChange R A ρ C' c')) with hG
  intro u v huv
  have h2 : (assocT R A ρ C') (G (S₂ (S₁ u))) = (assocT R A ρ C') (G (S₂ (S₁ v))) := by
    rw [hsq u, hsq v, huv]
  have hGinj : Function.Injective G := by
    rw [hG]
    exact (bijective_galoisProductMap_coactionBaseChange R A ρ C' hρ hsurj).injective
  exact S₁.injective (S₂.injective (hGinj ((assocT R A ρ C').injective h2)))

end ModuleLeftErased

/-- Per prime, the base-changed algebra is free over the scalars: the shifted basis
exists and descends to `C'`. -/
theorem free_baseChange_of_surjective_galoisPrecursor
    [Module.Free R A] [Module.Finite R A]
    [Module.Flat (coinvariants ρ) C'] [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')]
    (hρ : IsCoaction ρ) (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Module.Free C' (C' ⊗[coinvariants ρ] B) := by
  obtain ⟨x, hb, hx⟩ := exists_shifted_basis_coactionBaseChange R A ρ C' hρ hsurj
  exact Module.Free.of_basis (basisOverScalarsOfBasisOverCoinvariants R A ρ C'
    (coinvariantsBasis (coactionBaseChange R A ρ C')
      (isCoaction_coactionBaseChange R A ρ C' hρ) hb x hx))

end PerPrime

section Globalize

open TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Free R A] [Module.Finite R A]
variable {B : Type*} [CommRing B] [Algebra R B]
variable (ρ : B →ₐ[R] B ⊗[R] A)

attribute [-instance] Subalgebra.instSMulSubtypeMem in
/-- **Flatness of `B` over the co-invariants**: per prime, the flat local extension turns
`B` free; descend along the faithfully flat extension and glue over the maximal ideals. -/
theorem flat_coinvariants (hρ : IsCoaction ρ)
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Module.Flat (coinvariants ρ) B := by
  classical
  refine flat_of_forall_flat_localized (fun P _ => ?_)
  haveI hflatCp : Module.Flat (coinvariants ρ) (Localization.AtPrime P) :=
    IsLocalization.flat _ P.primeCompl
  haveI hflatCx : Module.Flat (coinvariants ρ)
      (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) :=
    Module.Flat.trans (coinvariants ρ) (Localization.AtPrime P)
      (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
  haveI hfree := free_baseChange_of_surjective_galoisPrecursor R A ρ
    (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) hρ hsurj
  exact flat_localized_of_flat_extension P
    (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
    Module.Flat.of_free

/-- **Faithful flatness of `B` over the co-invariants**: flatness plus surjectivity on
prime spectra (lying-over along the integral extension). -/
theorem faithfullyFlat_coinvariants (hρ : IsCoaction ρ)
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Module.FaithfullyFlat (coinvariants ρ) B := by
  haveI := flat_coinvariants R A ρ hρ hsurj
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, hcomap⟩ := exists_prime_over_coinvariants R A ρ hρ p
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hcomap⟩

attribute [-instance] Subalgebra.instSMulSubtypeMem in
/-- **Global injectivity of the canonical Galois map**: check after base change to each
flat local extension, where the comparison square reduces it to the per-prime Galois
bijectivity. -/
theorem injective_canonicalGaloisLinear (hρ : IsCoaction ρ)
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Function.Injective (canonicalGaloisLinear R A ρ) := by
  classical
  refine injective_of_forall_lTensor_localPolynomialExtension
    (canonicalGaloisLinear R A ρ) (fun P _ => ?_)
  haveI hflatCp : Module.Flat (coinvariants ρ) (Localization.AtPrime P) :=
    IsLocalization.flat _ P.primeCompl
  haveI hflatCx : Module.Flat (coinvariants ρ)
      (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) :=
    Module.Flat.trans (coinvariants ρ) (Localization.AtPrime P)
      (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P))
  exact injective_lTensor_canonicalGaloisMap R A ρ
    (IsLocalRing.LocalPolynomialExtension (Localization.AtPrime P)) hρ hsurj

/-- The scalar-collapse map `B ⊗[R] B → B ⊗[C] B`. -/
noncomputable def collapseScalars :
    (B ⊗[R] B) →ₐ[R] (B ⊗[coinvariants ρ] B) :=
  Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeft
      (R := coinvariants ρ) (S := coinvariants ρ) (A := B) (B := B)).restrictScalars R)
    ((Algebra.TensorProduct.includeRight
      (R := coinvariants ρ) (A := B) (B := B)).restrictScalars R)

omit [Module.Free R A] [Module.Finite R A] in
@[simp]
theorem collapseScalars_tmul (b b' : B) :
    collapseScalars R A ρ (b ⊗ₜ[R] b') = b ⊗ₜ[coinvariants ρ] b' := by
  rw [collapseScalars, Algebra.TensorProduct.productMap_apply_tmul]
  show (b ⊗ₜ[coinvariants ρ] (1 : B)) * ((1 : B) ⊗ₜ[coinvariants ρ] b') = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [Module.Free R A] [Module.Finite R A] in
/-- **Surjectivity of the canonical Galois map**, directly from the precursor. -/
theorem surjective_canonicalGaloisMap
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    Function.Surjective (canonicalGaloisMap ρ) := by
  have hcomp : ∀ t : B ⊗[R] B,
      canonicalGaloisMap ρ (collapseScalars R A ρ t) = galoisPrecursor R A ρ t := by
    intro t
    induction t with
    | zero => rw [map_zero, map_zero, map_zero]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
    | tmul b b' =>
        rw [collapseScalars_tmul, galoisPrecursor_tmul, canonicalGaloisMap_tmul]
  intro y
  obtain ⟨t, ht⟩ := hsurj y
  exact ⟨collapseScalars R A ρ t, by rw [hcomp, ht]⟩

/-- **The Hopf–Galois theorem for co-actions of finite free Hopf algebras**
(Stacks 03BM = SGA 3 Exp. V Théorème 4.1, affine case, comodule form): a co-action
`ρ : B →ₐ[R] B ⊗[R] A` whose Galois precursor `B ⊗[R] B → B ⊗[R] A` is surjective is
Hopf–Galois: the canonical Galois map `B ⊗[C] B → B ⊗[R] A` is bijective and `B` is
faithfully flat over its co-invariants. -/
theorem isHopfGalois_of_surjective_galoisPrecursor (hρ : IsCoaction ρ)
    (hsurj : Function.Surjective (galoisPrecursor R A ρ)) :
    IsHopfGalois ρ where
  galois := ⟨injective_canonicalGaloisLinear R A ρ hρ hsurj,
    surjective_canonicalGaloisMap R A ρ hsurj⟩
  faithfullyFlat := faithfullyFlat_coinvariants R A ρ hρ hsurj

end Globalize

end ModularCurves
