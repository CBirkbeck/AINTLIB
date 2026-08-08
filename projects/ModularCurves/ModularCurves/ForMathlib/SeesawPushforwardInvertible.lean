/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.CochainComplexBoundedFlat
import ModularCurves.ForMathlib.ConstantKernelRankProjective
import ModularCurves.ForMathlib.InvertibleOfRankOne
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero
import ModularCurves.ForMathlib.SchemeModuleProperLowDegreeCechFinite

/-!
# The seesaw pushforward is invertible over a reduced base (`KM-SEESAW-2`)

`baseSections_invertible_of_kernel_finrank_of_isReduced`: for an invertible module `M` on a
proper flat family `π : X ⟶ S` of finite presentation over a **reduced** Noetherian affine
base, the base-linear global sections `π_* M = baseSections π M` form an **invertible module**
over `Γ(S, ⊤)`, provided

* `hhigh` — the ordered base-Čech complex `C` of `M` is exact in **positive** degrees
  (`1 ≤ q < #ι`); nothing is assumed at `q = 0`, and
* `hrank` — the degree-zero Čech kernel has dimension `1` after base change to every field
  over `Γ(S, ⊤)` (equivalently `h⁰(X_s, M_s) = 1` for every `s`).

## Why this is not `baseSections_invertible_of_hasDegreeOneFibreCohomology`

`EllipticCurve/DegreeOneFibreCohomology.lean` proves the same conclusion from the degree-one
package, which assumes exactness of `C` in **all** degrees `q < #ι`, including `q = 0`. That is
`H¹`-vanishing on the fibres and it is *false* for the seesaw input: on a genus-one fibre
`H¹(E_s, 𝒪) ≅ κ(s) ≠ 0` (see the module docstring of `ForMathlib/Seesaw.lean`). Exactness at
`q = 0` is exactly what buys projectivity of `ker d⁰` there, through
`Module.Projective.ker_of_bounded_exact_of_finite`.

Here that step is replaced by **reducedness of the base**: `hhigh` alone makes the cycle module
`ker d¹` flat and makes cycles commute with arbitrary base change
(`Module.Flat.ker_of_bounded_exact_from`,
`kerBaseChangeComparison_bijective_of_bounded_exact_from`, both applied in degree `k = 1`), which
is precisely what the finite-projective replacement of Mumford, *Abelian Varieties* §5 Lemma 1
(`ForMathlib/LowDegreeFiniteProjectiveReplacement.lean`) needs in order to compute `H⁰` after
every base change. The replacement turns `d⁰` into a map `u : KZero → KOne` of **finite
projective** modules with the same base-changed kernels, and then
`projective_ker_of_constant_finrank_ker_baseChange`
(`ForMathlib/ConstantKernelRankProjective.lean`, Stacks [0FWG]) — the only place reducedness is
spent — makes `ker u` finite projective. Its rank is `1` at every prime because for the
replacement, cokernels are projective and hence kernels *do* commute with base change; the
line-bundle criterion `Module.Invertible.of_finite_of_projective_of_rankAtStalk_eq_one` finishes,
after transport along `baseSectionsIsoKernelOrderedBaseCechDifferential`.

## Structure of the file

`baseSections_invertible_of_orderedBaseCechHomologyFinite` carries all of the mathematics and is
**sorry-free**: it takes finiteness of the ordered base-Čech homology as an explicit hypothesis.
Over an arbitrary Noetherian affine base that hypothesis is discharged by
`Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper_of_isAffine`
(`ForMathlib/SchemeModuleProperLowDegreeCechFinite.lean`), which transports the
`Spec (.of R)`-shaped Chow-comodel chain along `S.isoSpec` through
`Scheme.Modules.OrderedBaseCechHomologyFinite.of_comp`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- A pair of maps through a zero module is exact: everything is a value of the first map and
everything is killed by the second. -/
private theorem exact_of_subsingleton_middle {R : Type*} [CommRing R]
    {P Q T : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T] [Subsingleton Q] (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) :
    Function.Exact f g := by
  intro y
  refine ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ ?_⟩
  rw [Subsingleton.elim y 0, map_zero]

/-- Base change along the identity algebra does not change a kernel: `R` is flat over itself, so
the comparison `R ⊗[R] ker f → ker (f ⊗ R)` is bijective. -/
private noncomputable def kerBaseChangeSelfEquiv {R : Type u} [CommRing R]
    {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.baseChange R) :=
  (TensorProduct.lid R (LinearMap.ker f)).symm.trans
    (LinearEquiv.ofBijective (kerBaseChangeComparison R f)
      (kerBaseChangeComparison_bijective_of_flat R f))

/-! ### The degree-zero kernel commutes with base change

`baseSections_invertible_of_orderedBaseCechHomologyFinite` below produces, *inside its proof*, a
finite-projective replacement `u` whose cokernel is projective, hence whose kernel commutes with
every base change. The three lemmas here export that consequence for the **original** differential
`d⁰`, which is what a consumer wanting `π_* M ⊗ κ(s) ↪ H⁰(X_s, M_s)` actually needs. -/

open TensorProduct in
/-- On underlying elements, the replacement's degree-zero base-change equivalence is the base
change of the comparison map `kZeroToCZero`. Definitional, but recorded because
`LowDegreeFiniteReplacement.baseChangeKernelEquiv` is built from a `private` `codRestrict`. -/
theorem LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv_coe
    {R : Type u} [CommRing R] [IsNoetherianRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Flat R (LinearMap.ker S.g.hom)] [Module.Finite R (LinearMap.ker S.f.hom)]
    [Module.Finite R S.homology]
    [Module.Finite R (LowDegreeFiniteReplacement.HZero S.moduleCatToCycles)]
    [Module.Finite R (LowDegreeFiniteReplacement.HOne S.moduleCatToCycles)]
    (A : Type u) [CommRing A] [Algebra R A]
    (hbij : Function.Bijective (kerBaseChangeComparison A S.g.hom))
    (z : LinearMap.ker
      ((LowDegreeFiniteReplacement.kZeroToKOne S.moduleCatToCycles).baseChange A)) :
    ((LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S A hbij z :
        LinearMap.ker (S.f.hom.baseChange A)) : A ⊗[R] S.X₁) =
      (LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles).baseChange A
        (z : A ⊗[R] (LowDegreeFiniteReplacement.KZero S.moduleCatToCycles)) :=
  rfl

/-- The comparison `ker u → ker d⁰` carried by `kZeroToCZero`: the replacement is a map of
complexes (`comparison_commutes`), so `kZeroToCZero` sends the kernel of the replacement
differential into the kernel of the original one. -/
noncomputable def LowDegreeFiniteReplacement.kerReplacementToKer
    {R : Type u} [CommRing R] [IsNoetherianRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LowDegreeFiniteReplacement.HZero S.moduleCatToCycles)]
    [Module.Finite R (LowDegreeFiniteReplacement.HOne S.moduleCatToCycles)] :
    LinearMap.ker (LowDegreeFiniteReplacement.kZeroToKOne S.moduleCatToCycles) →ₗ[R]
      LinearMap.ker S.f.hom :=
  LinearMap.codRestrict _
    (LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles ∘ₗ
      (LinearMap.ker (LowDegreeFiniteReplacement.kZeroToKOne S.moduleCatToCycles)).subtype)
    fun x ↦ by
      have hx := LinearMap.congr_fun
        (LowDegreeFiniteReplacement.comparison_commutes S.moduleCatToCycles) (x : _)
      simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2, map_zero] at hx
      have h2 : S.moduleCatToCycles
          (LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles (x : _)) = 0 := hx.symm
      rw [LinearMap.mem_ker]
      exact congrArg Subtype.val h2

open TensorProduct in
/-- A map whose base change along the identity algebra is bijective is bijective. -/
private theorem bijective_of_baseChange_self {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (h : Function.Bijective (f.baseChange R)) : Function.Bijective f := by
  have hcomm : ∀ x : R ⊗[R] M,
      (TensorProduct.lid R N) (f.baseChange R x) = f ((TensorProduct.lid R M) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp [hx, hy]
  have hfac : ⇑f =
      ⇑(TensorProduct.lid R N) ∘ ⇑(f.baseChange R) ∘ ⇑(TensorProduct.lid R M).symm := by
    funext m
    rw [Function.comp_apply, Function.comp_apply, hcomm, LinearEquiv.apply_symm_apply]
  rw [hfac]
  exact ((TensorProduct.lid R N).bijective.comp h).comp (TensorProduct.lid R M).symm.bijective

open TensorProduct in
/-- Base change preserves bijectivity. -/
private theorem baseChange_bijective_of_bijective {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Type u) [CommRing A] [Algebra R A] (f : M →ₗ[R] N) (h : Function.Bijective f) :
    Function.Bijective (f.baseChange A) := by
  let e := LinearEquiv.ofBijective f h
  have h1 : f ∘ₗ e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x ↦ e.apply_symm_apply x
  have h2 : e.symm.toLinearMap ∘ₗ f = LinearMap.id :=
    LinearMap.ext fun x ↦ e.symm_apply_apply x
  have h1' : (f.baseChange A) ∘ₗ (e.symm.toLinearMap.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have h2' : (e.symm.toLinearMap.baseChange A) ∘ₗ (f.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  refine ⟨Function.LeftInverse.injective (g := e.symm.toLinearMap.baseChange A) fun x ↦ ?_,
    Function.RightInverse.surjective (g := e.symm.toLinearMap.baseChange A) fun x ↦ ?_⟩
  · exact LinearMap.congr_fun h2' x
  · exact LinearMap.congr_fun h1' x

open TensorProduct in
/-- **The degree-zero kernel commutes with base change** as soon as the finite-projective
replacement of `S` has projective cokernel and the cycles of `S` commute with base change.

This is the statement `π_* M ⊗_R A → H⁰(X_A, M_A)` that a fibrewise argument needs, exported for
the *original* differential `S.f` — inside
`baseSections_invertible_of_orderedBaseCechHomologyFinite` it is only available for the
replacement differential `u`. The transfer is the square

`(A ⊗ ker u) → ker (u ⊗ A) ≅ ker (S.f ⊗ A)` versus `(A ⊗ ker u) → (A ⊗ ker S.f) → ker (S.f ⊗ A)`,

which commutes because both composites are the base change of `kZeroToCZero ∘ subtype`. -/
theorem kerBaseChangeComparison_zero_bijective_of_projective_replacement_cokernel
    {R : Type u} [CommRing R] [IsNoetherianRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Flat R (LinearMap.ker S.g.hom)] [Module.Finite R (LinearMap.ker S.f.hom)]
    [Module.Finite R S.homology]
    [Module.Finite R (LowDegreeFiniteReplacement.HZero S.moduleCatToCycles)]
    [Module.Finite R (LowDegreeFiniteReplacement.HOne S.moduleCatToCycles)]
    [Module.Projective R (LowDegreeFiniteReplacement.KOne S.moduleCatToCycles ⧸
      LinearMap.range (LowDegreeFiniteReplacement.kZeroToKOne S.moduleCatToCycles))]
    (hbij : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (kerBaseChangeComparison A S.g.hom))
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective (kerBaseChangeComparison A S.f.hom) := by
  let u := LowDegreeFiniteReplacement.kZeroToKOne S.moduleCatToCycles
  let θ := LowDegreeFiniteReplacement.kerReplacementToKer S
  have hmaps : (LinearMap.ker S.f.hom).subtype ∘ₗ θ =
      LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles ∘ₗ
        (LinearMap.ker u).subtype := rfl
  have key : ∀ (B : Type u) [CommRing B] [Algebra R B],
      ⇑(kerBaseChangeComparison B S.f.hom) ∘ ⇑(θ.baseChange B) =
        ⇑(LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S B (hbij B)) ∘
          ⇑(kerBaseChangeComparison B u) := by
    intro B _ _
    have e1 : LinearMap.baseChange B ((LinearMap.ker S.f.hom).subtype ∘ₗ θ) =
        LinearMap.baseChange B (LinearMap.ker S.f.hom).subtype ∘ₗ LinearMap.baseChange B θ :=
      LinearMap.baseChange_comp θ (LinearMap.ker S.f.hom).subtype
    have e2 : LinearMap.baseChange B
          (LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles ∘ₗ
            (LinearMap.ker u).subtype) =
        LinearMap.baseChange B (LowDegreeFiniteReplacement.kZeroToCZero S.moduleCatToCycles) ∘ₗ
          LinearMap.baseChange B (LinearMap.ker u).subtype :=
      LinearMap.baseChange_comp (LinearMap.ker u).subtype _
    have hcomp := e1.symm.trans ((congrArg (LinearMap.baseChange B) hmaps).trans e2)
    funext x
    exact Subtype.ext ((LinearMap.congr_fun hcomp x).trans
      (LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv_coe S B (hbij B)
        (kerBaseChangeComparison B u x)).symm)
  have hu' : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (kerBaseChangeComparison B u) := fun B _ _ ↦
    kerBaseChangeComparison_bijective B u
  have hcompose : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (⇑(kerBaseChangeComparison B S.f.hom) ∘ ⇑(θ.baseChange B)) := by
    intro B _ _
    have h0 : Function.Bijective
        (⇑(LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S B (hbij B)) ∘
          ⇑(kerBaseChangeComparison B u)) :=
      ((LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S B
        (hbij B)).bijective).comp (hu' B)
    exact cast (congrArg Function.Bijective (key B).symm) h0
  have hθbij : Function.Bijective θ :=
    bijective_of_baseChange_self θ
      (((kerBaseChangeComparison_bijective_of_flat R S.f.hom).of_comp_iff' _).mp (hcompose R))
  have hAbij := hcompose A
  exact (Function.Bijective.of_comp_iff _
    (baseChange_bijective_of_bijective A θ hθbij)).mp hAbij

/-- **(`KM-SEESAW-2`, main content)** Constant residue rank one of the degree-zero Čech kernel
makes the pushforward's global sections invertible over a reduced Noetherian affine base, given
positive-degree exactness of the ordered base-Čech complex and finiteness of its homology.

Positive-degree exactness is used only through the cycle module `ker d¹`: it is flat and it
commutes with every algebra base change, which is what the finite-projective replacement of
Mumford §5 Lemma 1 consumes. Reducedness is used only in
`projective_ker_of_constant_finrank_ker_baseChange`. -/
theorem baseSections_invertible_of_orderedBaseCechHomologyFinite
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    {M : X.Modules} (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hhom : AlgebraicGeometry.Scheme.Modules.OrderedBaseCechHomologyFinite π U M)
    (hhigh : ∀ q, 1 ≤ q → q < Fintype.card ι →
      Function.Exact ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d q (q+1)).hom
        ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d (q+1) (q+2)).hom)
    (hrank : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      Module.finrank K (LinearMap.ker
        (((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.baseChange K))
        = 1) :
    Module.Invertible Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M) := by
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(S, (⊤ : S.Opens))
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  letI (q : ℕ) : Module.Flat B (C.X q) :=
    Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible π M hM U hUaff q
  letI (q : ℕ) : Module.Finite B (C.homology q) := hhom q
  letI : IsNoetherianRing B :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  letI : _root_.IsReduced B := inferInstance
  -- The complex is bounded by `#ι`, so it is exact from degree `1` to degree `#ι + 1`.
  letI : Subsingleton (C.X (Fintype.card ι + 1 + 1)) :=
    Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π M U
      (Fintype.card ι + 1 + 1) (by omega)
  have hexact : ∀ n, 1 ≤ n → n < Fintype.card ι + 1 →
      Function.Exact ((C.d n (n + 1)).hom) ((C.d (n + 1) (n + 2)).hom) := by
    intro n h1 _
    rcases Nat.lt_or_ge n (Fintype.card ι) with h | h
    · exact hhigh n h1 h
    · haveI : Subsingleton (C.X (n + 1)) :=
        Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π M U (n + 1) (by omega)
      exact exact_of_subsingleton_middle _ _
  -- Positive-degree exactness makes the cycle module `ker d¹` flat and base-change compatible.
  letI : Module.Flat B (LinearMap.ker (C.d 1 2).hom) :=
    Module.Flat.ker_of_bounded_exact_from (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom)
      (Fintype.card ι + 1) 1 (by omega) hexact
  have hbij : ∀ (A : Type u) [CommRing A] [Algebra B A],
      Function.Bijective (kerBaseChangeComparison A (C.d 1 2).hom) := by
    intro A _ _
    exact kerBaseChangeComparison_bijective_of_bounded_exact_from
      (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) A (Fintype.card ι + 1) 1 (by omega) hexact
  -- The two-term piece `C.X 0 → C.X 1 → C.X 2` of the complex, and its replacement.
  let S₀ : ShortComplex (ModuleCat.{u} B) := C.sc' 0 1 2
  letI : Module.Flat B S₀.X₁ := (inferInstance : Module.Flat B (C.X 0))
  letI : Module.Flat B (LinearMap.ker S₀.g.hom) :=
    (inferInstance : Module.Flat B (LinearMap.ker (C.d 1 2).hom))
  letI : Module.Finite B (LinearMap.ker S₀.f.hom) :=
    (HomologicalComplex.finite_kernel_zero_of_finite_homology C :
      Module.Finite B (LinearMap.ker (C.d 0 1).hom))
  letI : Module.Finite B S₀.homology :=
    Module.Finite.equiv (C.homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0)
      (by rw [CochainComplex.next]; rfl)).toLinearEquiv
  letI : Module.Finite B (LinearMap.ker S₀.moduleCatToCycles) :=
    Module.Finite.ker_moduleCatToCycles S₀
  letI : Module.Finite B (LinearMap.ker S₀.g.hom ⧸ LinearMap.range S₀.moduleCatToCycles) :=
    Module.Finite.quotient_range_moduleCatToCycles S₀
  letI : Module.Projective B (LowDegreeFiniteReplacement.KZero S₀.moduleCatToCycles) :=
    LowDegreeFiniteReplacement.kZero_projective S₀.moduleCatToCycles
  let u := LowDegreeFiniteReplacement.kZeroToKOne S₀.moduleCatToCycles
  -- The replacement has the same base-changed degree-zero kernels, so `hrank` transfers to it.
  have hkerrank : ∀ p : PrimeSpectrum B,
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = 1 := by
    intro p
    exact (LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S₀
      p.asIdeal.ResidueField (hbij p.asIdeal.ResidueField)).finrank_eq.trans
      (hrank p.asIdeal.ResidueField)
  -- Reducedness: constant fibre kernel dimension makes the kernel and the cokernel projective.
  letI : Module.Projective B (LinearMap.ker u) :=
    projective_ker_of_constant_finrank_ker_baseChange u 1 hkerrank
  letI : Module.Finite B (LinearMap.ker u) :=
    finite_ker_of_constant_finrank_ker_baseChange u 1 hkerrank
  letI : Module.Projective B (LowDegreeFiniteReplacement.KOne S₀.moduleCatToCycles ⧸
      LinearMap.range u) :=
    projective_quotient_range_of_constant_finrank_ker_baseChange u 1 hkerrank
  -- A projective cokernel makes `ker u` commute with base change, so its rank is `1` everywhere.
  have hbiju : ∀ (A : Type u) [CommRing A] [Algebra B A],
      Function.Bijective (kerBaseChangeComparison A u) := by
    intro A _ _
    exact kerBaseChangeComparison_bijective A u
  have hrankAtU : Module.rankAtStalk (R := B) (LinearMap.ker u) = fun _ ↦ 1 := by
    funext p
    rw [Module.rankAtStalk_eq]
    exact (LinearEquiv.ofBijective (kerBaseChangeComparison p.asIdeal.ResidueField u)
      (hbiju p.asIdeal.ResidueField)).finrank_eq.trans (hkerrank p)
  -- Transport back to `H⁰` of the Čech complex, i.e. to the pushforward's global sections.
  let eKer : LinearMap.ker u ≃ₗ[B] LinearMap.ker (C.d 0 1).hom :=
    (kerBaseChangeSelfEquiv u).trans
      ((LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S₀ B (hbij B)).trans
        (kerBaseChangeSelfEquiv (C.d 0 1).hom).symm)
  let eSec : (Scheme.Modules.baseSections π M : Type u) ≃ₗ[B] LinearMap.ker u :=
    (Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
      π M U hU).toLinearEquiv.trans eKer.symm
  letI : Module.Finite B (Scheme.Modules.baseSections π M) := Module.Finite.equiv eSec.symm
  letI : Module.Projective B (Scheme.Modules.baseSections π M) :=
    Module.Projective.of_equiv' eSec.symm
  exact Module.Invertible.of_finite_of_projective_of_rankAtStalk_eq_one
    ((Module.rankAtStalk_eq_of_equiv eSec).trans hrankAtU)

/-- **(`KM-SEESAW-2`, base-change form)** Under the hypotheses of
`baseSections_invertible_of_kernel_finrank_of_isReduced`, the degree-zero kernel of the ordered
base-Čech complex — that is, `π_* M` — commutes with *every* algebra base change:

`A ⊗_{Γ(S,⊤)} Γ(X, M) ≅ ker (d⁰ ⊗ A) = H⁰(X_A, M_A)`.

Taking `A = κ(s)` this is the injection `π_* M ⊗ κ(s) ↪ H⁰(X_s, M_s)` that a fibrewise
nowhere-vanishing argument consumes. Reducedness enters only through
`projective_quotient_range_of_constant_finrank_ker_baseChange`, exactly as in the invertibility
theorem below. -/
theorem kerBaseChangeComparison_orderedBaseCech_zero_bijective
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    {M : X.Modules} (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hhigh : ∀ q, 1 ≤ q → q < Fintype.card ι →
      Function.Exact ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d q (q+1)).hom
        ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d (q+1) (q+2)).hom)
    (hrank : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      Module.finrank K (LinearMap.ker
        (((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.baseChange K))
        = 1)
    (A : Type u) [CommRing A] [Algebra Γ(S, (⊤ : S.Opens)) A] :
    Function.Bijective (kerBaseChangeComparison A
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom) := by
  let C := Scheme.Modules.orderedBaseCechComplex π M U
  let B := Γ(S, (⊤ : S.Opens))
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  letI (q : ℕ) : Module.Flat B (C.X q) :=
    Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible π M hM U hUaff q
  letI : IsNoetherianRing B :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  letI (q : ℕ) : Module.Finite B (C.homology q) :=
    Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper_of_isAffine
      (xπ := π) U hU hUaff M q
  letI : _root_.IsReduced B := inferInstance
  letI : Subsingleton (C.X (Fintype.card ι + 1 + 1)) :=
    Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π M U
      (Fintype.card ι + 1 + 1) (by omega)
  have hexact : ∀ n, 1 ≤ n → n < Fintype.card ι + 1 →
      Function.Exact ((C.d n (n + 1)).hom) ((C.d (n + 1) (n + 2)).hom) := by
    intro n h1 _
    rcases Nat.lt_or_ge n (Fintype.card ι) with h | h
    · exact hhigh n h1 h
    · haveI : Subsingleton (C.X (n + 1)) :=
        Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π M U (n + 1) (by omega)
      exact exact_of_subsingleton_middle _ _
  letI : Module.Flat B (LinearMap.ker (C.d 1 2).hom) :=
    Module.Flat.ker_of_bounded_exact_from (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom)
      (Fintype.card ι + 1) 1 (by omega) hexact
  let S₀ : ShortComplex (ModuleCat.{u} B) := C.sc' 0 1 2
  have hbij : ∀ (A : Type u) [CommRing A] [Algebra B A],
      Function.Bijective (kerBaseChangeComparison A S₀.g.hom) := by
    intro A _ _
    exact kerBaseChangeComparison_bijective_of_bounded_exact_from
      (fun q ↦ C.X q) (fun q ↦ (C.d q (q + 1)).hom) A (Fintype.card ι + 1) 1 (by omega) hexact
  letI : Module.Flat B S₀.X₁ := (inferInstance : Module.Flat B (C.X 0))
  letI : Module.Flat B (LinearMap.ker S₀.g.hom) :=
    (inferInstance : Module.Flat B (LinearMap.ker (C.d 1 2).hom))
  letI : Module.Finite B (LinearMap.ker S₀.f.hom) :=
    (HomologicalComplex.finite_kernel_zero_of_finite_homology C :
      Module.Finite B (LinearMap.ker (C.d 0 1).hom))
  letI : Module.Finite B S₀.homology :=
    Module.Finite.equiv (C.homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0)
      (by rw [CochainComplex.next]; rfl)).toLinearEquiv
  letI : Module.Finite B (LinearMap.ker S₀.moduleCatToCycles) :=
    Module.Finite.ker_moduleCatToCycles S₀
  letI : Module.Finite B (LinearMap.ker S₀.g.hom ⧸ LinearMap.range S₀.moduleCatToCycles) :=
    Module.Finite.quotient_range_moduleCatToCycles S₀
  letI : Module.Projective B (LowDegreeFiniteReplacement.KZero S₀.moduleCatToCycles) :=
    LowDegreeFiniteReplacement.kZero_projective S₀.moduleCatToCycles
  let u := LowDegreeFiniteReplacement.kZeroToKOne S₀.moduleCatToCycles
  have hkerrank : ∀ p : PrimeSpectrum B,
      Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker (u.baseChange p.asIdeal.ResidueField)) = 1 := by
    intro p
    exact (LowDegreeFiniteReplacement.shortComplexBaseChangeKernelEquiv S₀
      p.asIdeal.ResidueField (hbij p.asIdeal.ResidueField)).finrank_eq.trans
      (hrank p.asIdeal.ResidueField)
  letI : Module.Projective B (LowDegreeFiniteReplacement.KOne S₀.moduleCatToCycles ⧸
      LinearMap.range u) :=
    projective_quotient_range_of_constant_finrank_ker_baseChange u 1 hkerrank
  exact kerBaseChangeComparison_zero_bijective_of_projective_replacement_cokernel S₀ hbij A

/-- **(`KM-SEESAW-2`)** For an invertible module on a proper flat family of finite presentation
over a reduced Noetherian affine base, positive-degree exactness of the ordered base-Čech complex
together with constant residue rank one of its degree-zero kernel makes the pushforward's global
sections `baseSections π M` an invertible `Γ(S, ⊤)`-module.

All the mathematics is in `baseSections_invertible_of_orderedBaseCechHomologyFinite`; the only
extra ingredient here is Čech homology finiteness, supplied by
`Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper_of_isAffine`. -/
theorem baseSections_invertible_of_kernel_finrank_of_isReduced
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    {M : X.Modules} (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hhigh : ∀ q, 1 ≤ q → q < Fintype.card ι →
      Function.Exact ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d q (q+1)).hom
        ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d (q+1) (q+2)).hom)
    (hrank : ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
      Module.finrank K (LinearMap.ker
        (((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.baseChange K))
        = 1) :
    Module.Invertible Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M) := by
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  letI : IsNoetherianRing Γ(S, (⊤ : S.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  exact baseSections_invertible_of_orderedBaseCechHomologyFinite hM U hU hUaff
    (Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper_of_isAffine
      (xπ := π) U hU hUaff M) hhigh hrank

end ModularCurves
