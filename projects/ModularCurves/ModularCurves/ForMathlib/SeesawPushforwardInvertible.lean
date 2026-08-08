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
Over `S = Spec (.of R)` that hypothesis is discharged by
`Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper`.

## Known gap

`orderedBaseCechHomologyFinite_of_isProper` is stated in this tree only for a base that is
*syntactically* `Spec (.of R)`, and the whole coherent-pushforward chain below it
(`SchemeModuleCanonicalSupportChowLowDegreeAssembly`) inherits that shape. Transporting it to a
general affine base `S` along `S.isoSpec` is a genuine (if routine) piece of work — the two Čech
complexes live over the two different rings `Γ(S, ⊤)` and `Γ(Spec Γ(S, ⊤), ⊤)` — and is left as
the single `sorry` of `orderedBaseCechHomologyFinite_of_isProper_of_isAffine` below.
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

/-- **Missing bridge.** Finiteness of the ordered base-Čech homology of a coherent module on a
proper Noetherian family over an arbitrary Noetherian **affine** base.

`Scheme.Modules.orderedBaseCechHomologyFinite_of_isProper`
(`ForMathlib/SchemeModuleProperLowDegreeCechFinite.lean:149`) is exactly this statement, but only
for a base of the syntactic shape `Spec (.of R)`; its whole supporting chain
(`exists_nonzero_homologyFiniteComodel`,
`CanonicalSupportThickening.exists_chowComodel_orderedBaseCechHomologyFinite`, and the relative
projective factorisation below them) is stated the same way, and the helpers are `private`.

Transporting it along `S.isoSpec : S ≅ Spec Γ(S, ⊤)` is routine but not short: the two ordered
base-Čech complexes live in `ModuleCat Γ(S, ⊤)` and `ModuleCat Γ(Spec Γ(S, ⊤), ⊤)`, and the terms
are *not* definitionally equal (the categorical products defining them use the two different
`HasLimits` instances). The route that does work runs through
`orderedBaseCechComplexBaseChangeIso π t M U hUaff` for `t := S.isoSpec.inv`, which identifies
`ModuleCat.extendScalars t.appTop.hom` applied to the complex with the ordered base-Čech complex
of `pullback.snd π t` over `Spec Γ(S, ⊤)`; `t.appTop.hom` is a ring isomorphism, hence flat, so
`kerBaseChangeComparison_bijective_of_flat` and right exactness of `⊗` turn the transported
statement back into finiteness over `Γ(S, ⊤)` by `Module.Finite.trans`. Its cost is the
instance bookkeeping for `pullback π t` (`IsNoetherian`, `IsSeparated`, affineness of the
preimage cover) plus a homology comparison; mathlib has no ready
`(F.mapHomologicalComplex c).obj C).homology n ≅ F.obj (C.homology n)`, and
`ModuleCat.restrictScalars` carries no `PreservesFiniteLimits`/`PreservesFiniteColimits`
instance, so that comparison has to be built by hand.

The cheaper fix is to generalise `orderedBaseCechHomologyFinite_of_isProper` from `Spec (.of R)`
to an arbitrary affine Noetherian base in its own file, which also unblocks
`InvertibleSheafProperCechResidueSpread` and the rest of the `Spec (.of R)`-shaped chain. -/
private theorem orderedBaseCechHomologyFinite_of_isProper_of_isAffine
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    AlgebraicGeometry.Scheme.Modules.OrderedBaseCechHomologyFinite π U M := by
  sorry

/-- **(`KM-SEESAW-2`)** For an invertible module on a proper flat family of finite presentation
over a reduced Noetherian affine base, positive-degree exactness of the ordered base-Čech complex
together with constant residue rank one of its degree-zero kernel makes the pushforward's global
sections `baseSections π M` an invertible `Γ(S, ⊤)`-module.

All the mathematics is in `baseSections_invertible_of_orderedBaseCechHomologyFinite`; the only
extra ingredient here is Čech homology finiteness, supplied by
`orderedBaseCechHomologyFinite_of_isProper_of_isAffine`. -/
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
  exact baseSections_invertible_of_orderedBaseCechHomologyFinite hM U hU hUaff
    (orderedBaseCechHomologyFinite_of_isProper_of_isAffine (π := π) U hU hUaff M) hhigh hrank

end ModularCurves
