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

end PerPrime

end ModularCurves
