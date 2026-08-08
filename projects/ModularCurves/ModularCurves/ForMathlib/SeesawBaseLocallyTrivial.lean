/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AbelEquivalence
import ModularCurves.ForMathlib.SeesawPushforwardInvertible
import ModularCurves.Picard.GlueTrivialization

/-!
# The seesaw sheaf is trivial over a Zariski cover of the base (`KM-SEESAW-3`)

Half **B.2** of the rank-one seesaw (Stacks [0EX7] at rank 1). Half B.1,
`baseSections_invertible_of_kernel_finrank_of_isReduced`
(`ForMathlib/SeesawPushforwardInvertible.lean`), makes `π_* M = baseSections π M` an **invertible**
`Γ(S, ⊤)`-module. This file turns that into the geometric statement KM p. 66 actually uses:

> "Because `f_*L` is invertible on `S`, Zariski locally on `S` we may pick an `O_S`-basis `ℓ` of
> `f_*L`."

`exists_baseCover_restrict_unitObj_iso_of_invertible_baseSections`: there is an open cover
`V : ι' → S.Opens` of the base with `M |_{π⁻¹ V i} ≅ 𝒪`.

## The cover, and why it is a *dual* partition of unity

`Module.Invertible R P` unfolds to bijectivity of the contraction `P^∨ ⊗_R P → R`, so `1` is a
finite sum `∑ φ_k(ℓ_k)` (`exists_finset_dual_apply_sum_eq_one`). Setting `f_k := φ_k(ℓ_k)`, the
basic opens `D(f_k) ⊆ S` cover `S` (`iSup_basicOpen_of_span_eq_top`), and on `D(f_k)` the *global*
section `ℓ_k ∈ Γ(X, M) = P` has nonzero image in `P ⊗ κ(s)` for every `s ∈ D(f_k)` — because
`φ_k ⊗ κ(s)` sends it to `f_k mod 𝔭_s ≠ 0`.

Working with this "trace-ideal" cover rather than with a free-locus cover
(`Module.free_of_flat_of_isLocalRing` plus a basic-open spread, or
`exists_finite_basicOpen_trivialization` / `exists_pow_smul_eq_restrict_of_isInvertible` of
`EllipticCurve/AbelEquivalence.lean`) avoids localizing `Γ(X, M)` altogether: the `ℓ_k` are honest
global sections of `M` on all of `X`, so no comparison `Γ(M, π⁻¹ D(f)) ≅ Γ(X, M)_f` — i.e. no
quasi-coherence of `π_* M` on a non-affine `X` — is ever needed.

## Route

Everything below the blocked step is proved here:

* `exists_finset_dual_apply_sum_eq_one` — the dual partition of unity (pure algebra).
* `bijective_smul_of_isUnit_evalSection` — if the evaluation of `ℓ` against a trivialization of
  `M` on `W` is a **unit** of `Γ(X, W)`, then `r ↦ r • ℓ` is bijective `Γ(X, W') → Γ(M, W')` for
  every `W' ≤ W`; through `sectionsLinearEquivOfTrivialization` this is multiplication by a unit.
* `nonempty_restrict_unitObj_iso_of_bijective_smul` — the local-to-global step: cover-local
  bijectivity of `r ↦ r • ℓ` trivializes `M` on `U`. The glued morphism is
  `Scheme.Modules.globalSectionHom` on `U.toScheme` and it is tested by
  `nonempty_unitObj_iso_of_globalSection` (`Picard/GlueTrivialization.lean`); the passage between
  `Γ(M.restrict U.ι, W'')` and `Γ(M, U.ι ''ᵁ W'')` is `restrictAppIso`, which is `Iso.refl`, so
  the only real content is the scalar twist by `U.ι.appIso`.
* `nonempty_restrict_unitObj_iso_of_isUnit_evalSection` — the two previous items combined over the
  trivializing cover supplied by `Scheme.Modules.IsInvertible`.
* `isUnit_evalSection_of_dual_baseSections` — "nowhere vanishing ⟹ unit", by
  `RingedSpace.isUnit_of_isUnit_germ` (valid on an arbitrary open, no affineness needed).

## What is left, and why (the one `sorry`)

`le_basicOpen_evalSection_of_dual_baseSections` — *the section `ℓ_k` is nowhere vanishing over
`D(f_k)`*. Its first three steps are now proved:

* step 1, `1 ⊗ ℓ_k ≠ 0` in `π_* M ⊗ κ(y)`, is `tmul_one_ne_zero_of_isUnit_dual_apply` here;
* step 2, the cohomology-and-base-change injection `π_* M ⊗ κ(y) ↪ H⁰(X_{κ(y)}, M_{κ(y)})`, is
  `kerBaseChangeComparison_orderedBaseCech_zero_bijective`
  (`ForMathlib/SeesawPushforwardInvertible.lean`), added for this file. It is the reason `hhigh`,
  `hrank` and `[IsReduced S]` — Half B.1's own hypotheses — now appear here.
* step 3, the *transport* of that nonzero class to a nonzero section of `M_T` on `X ×_S T`, is
  `baseChange_unit_ne_zero_of_isUnit_dual_apply` here, on top of the fibre-transport chain
  `orderedBaseCechKernelBaseChangeEquivBaseSections` and its `_apply` lemma
  (`ForMathlib/SeesawPushforwardInvertible.lean`) — the chain sends `1 ⊗ ℓ` to the pullback of `ℓ`
  along `pullback.fst π t`. Its element-level API is now in
  `ForMathlib/AffineModuleCechBaseChange.lean` and
  `ForMathlib/SchemeModuleOrderedBaseCechZero.lean`.

What remains is step 4 only: `hfib`/`hπ` make that nonzero section a **unit** on the fibre, and one
must read that unit off at the point `y`. This needs `evalSection` compatibility with the pullback
of modules along `pullback.fst π t` — a piece of `Picard/Evaluation.lean`-style API that does not
exist yet. See the lemma's own docstring for the precise list.

## Consumer

`ModularCurves.exists_pullback_twist_of_locally` (`WeilPairing/RelPicLocal.lean`), through
`exists_pullback_iso_of_kernel_finrank_of_fibre_trivial` (`ForMathlib/Seesaw.lean`), whose
`hglue`-shaped input is precisely the per-base-open trivialization produced here.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- **Dual partition of unity.** For an invertible module the contraction `P^∨ ⊗ P → R` is
surjective, so `1` is a finite sum of values `φ ℓ` of functionals on elements. Consequently the
`φ ℓ` occurring generate the unit ideal, which is how an invertible module produces a *cover*. -/
theorem exists_finset_dual_apply_sum_eq_one {R : Type u} [CommRing R] {P : Type u}
    [AddCommGroup P] [Module R P] (h : Module.Invertible R P) :
    ∃ T : Finset (Module.Dual R P × P), ∑ i ∈ T, i.1 i.2 = 1 := by
  obtain ⟨z, hz⟩ := h.bijective.surjective 1
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset z
  refine ⟨T, ?_⟩
  rw [hT, map_sum] at hz
  simpa using hz

open TensorProduct in
/-- **Step 1 of the nowhere-vanishing argument.** If some functional takes an invertible value on
`l`, then `l` survives every base change: `1 ⊗ l ≠ 0`.

Applied with `K = κ(s)` and `f_k = φ_k(ℓ_k)` this says that on `D(f_k)` the section `ℓ_k` has
nonzero image in `π_* M ⊗ κ(s)` — which is why the cover is built from a dual partition of
unity rather than from a free locus. -/
theorem tmul_one_ne_zero_of_isUnit_dual_apply {R : Type u} [CommRing R] {P : Type u}
    [AddCommGroup P] [Module R P] (φ : Module.Dual R P) (l : P)
    (K : Type u) [CommRing K] [Nontrivial K] [Algebra R K]
    (h : IsUnit (algebraMap R K (φ l))) :
    (1 : K) ⊗ₜ[R] l ≠ (0 : K ⊗[R] P) := by
  intro hzero
  have h1 : (Module.Dual.baseChange K φ) ((1 : K) ⊗ₜ[R] l) = algebraMap R K (φ l) := by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_one]
  rw [hzero, map_zero] at h1
  rw [← h1] at h
  exact not_isUnit_zero h

open TensorProduct in
/-- **Steps 1–3 of the nowhere-vanishing argument, assembled.** Over an affine base change
`t : T ⟶ S` on which the dual value `φ l` becomes invertible, the pullback of `l` along
`pullback.fst π t` is a **nonzero** section of `M` on the fibre product.

The three inputs are `tmul_one_ne_zero_of_isUnit_dual_apply` (step 1: `1 ⊗ l ≠ 0`),
`kerBaseChangeComparison_orderedBaseCech_zero_bijective` (step 2: the injection
`π_* M ⊗ Γ(T,⊤) ↪ ker (d⁰ ⊗ Γ(T,⊤))`) and
`orderedBaseCechKernelBaseChangeEquivBaseSections_apply` (step 3: the fibre-transport chain sends
`1 ⊗ l` to the pullback of `l`). Nothing here uses `hfib` or `hπ`: this is the "the section
survives" half, and it holds for an arbitrary invertible `M`. -/
private theorem baseChange_unit_ne_zero_of_isUnit_dual_apply
    {X S T : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated] [IsAffine T] [Nontrivial Γ(T, (⊤ : T.Opens))]
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
    (t : T ⟶ S)
    (φ : Module.Dual Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (l : AlgebraicGeometry.Scheme.Modules.baseSections π M)
    (hunit : IsUnit (t.appTop.hom (φ l))) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (Limits.pullback.fst π t)).unit.app M).val.app (Opposite.op (⊤ : X.Opens))) l ≠ 0 := by
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) := t.appTop.hom.toAlgebra
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  let e0 := (AlgebraicGeometry.Scheme.Modules.baseSectionsIsoKernelOrderedBaseCechDifferential
    π M U hU).toLinearEquiv
  have h1 : (1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] l ≠ 0 :=
    tmul_one_ne_zero_of_isUnit_dual_apply φ l Γ(T, (⊤ : T.Opens)) hunit
  have h2 : (1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] (e0 l) ≠ 0 := by
    intro hz
    refine h1 ((LinearEquiv.lTensor Γ(T, (⊤ : T.Opens)) e0).map_eq_zero_iff.mp ?_)
    exact (LinearEquiv.lTensor_tmul Γ(T, (⊤ : T.Opens)) e0 1 l).trans hz
  have h3 : kerBaseChangeComparison Γ(T, (⊤ : T.Opens))
      ((AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom
      ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] (e0 l)) ≠ 0 := by
    intro hz
    exact h2 ((kerBaseChangeComparison_orderedBaseCech_zero_bijective hM U hU hUaff hhigh hrank
      Γ(T, (⊤ : T.Opens))).injective (hz.trans (map_zero _).symm))
  intro hzero
  refine h3 ?_
  refine (orderedBaseCechKernelBaseChangeEquivBaseSections U hU hUaff t).map_eq_zero_iff.mp ?_
  exact (orderedBaseCechKernelBaseChangeEquivBaseSections_apply U hU hUaff t l).trans hzero

/-- **Local-to-global.** A global section `l` of `M` whose multiplication map `r ↦ r • l` is
bijective on every open inside a member of a family covering `U` trivializes `M` over `U`.

The glued morphism `𝒪 ⟶ M` is `Scheme.Modules.globalSectionHom` formed *on the open subscheme*
`U.toScheme` for the restricted module, and the test is
`Scheme.Modules.nonempty_unitObj_iso_of_globalSection`. Two bookkeeping facts carry the transfer
between `U.toScheme` and `X`: sections of `M.restrict U.ι` over `W''` are literally sections of `M`
over `U.ι ''ᵁ W''` (`restrictAppIso` is `Iso.refl`), and the `Γ(U.toScheme, W'')`-action is the
`Γ(X, U.ι ''ᵁ W'')`-action twisted by the ring isomorphism `U.ι.appIso W''`. -/
theorem nonempty_restrict_unitObj_iso_of_bijective_smul {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (l : Γ(M, ⊤)) {ι : Type u} (W : ι → X.Opens) (hcov : U ≤ ⨆ j, W j)
    (hbij : ∀ (j : ι) (W' : X.Opens), W' ≤ W j → W' ≤ U →
      Function.Bijective fun r : Γ(X, W') ↦
        r • M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l) :
    Nonempty (M.restrict U.ι ≅ AlgebraicGeometry.Scheme.Modules.unitObj U.toScheme) := by
  set m : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
    M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ (⊤ : X.Opens))).op l
    with hm
  have hcover : ⨆ j, U.ι ⁻¹ᵁ W j = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov x.2)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  have hres : ∀ Wpp : U.toScheme.Opens,
      (M.restrict U.ι).presheaf.map (homOfLE (le_top : Wpp ≤ (⊤ : U.toScheme.Opens))).op m =
        M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ Wpp ≤ (⊤ : X.Opens))).op l := by
    intro Wpp
    have h1 : (M.restrict U.ι).presheaf.map
          (homOfLE (le_top : Wpp ≤ (⊤ : U.toScheme.Opens))).op m =
        M.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
            (homOfLE (le_top : Wpp ≤ (⊤ : U.toScheme.Opens)))).op
          (M.presheaf.map
            (homOfLE (le_top : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ (⊤ : X.Opens))).op l) := rfl
    rw [h1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun q ↦ (ConcreteCategory.hom (M.presheaf.map q)) l)
      (Subsingleton.elim _ _)
  have hbij' : ∀ (j : ι) (Wpp : U.toScheme.Opens), Wpp ≤ U.ι ⁻¹ᵁ W j →
      Function.Bijective ((AlgebraicGeometry.Scheme.Modules.globalSectionHom
        (M.restrict U.ι) m).app Wpp) := by
    intro j Wpp hWpp
    have hW'U : U.ι ''ᵁ Wpp ≤ U :=
      (Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top)
    have hW'W : U.ι ''ᵁ Wpp ≤ W j :=
      (Scheme.Hom.image_mono U.ι hWpp).trans (U.ι.image_preimage_le (W j))
    have hcomp : ⇑((AlgebraicGeometry.Scheme.Modules.globalSectionHom
          (M.restrict U.ι) m).app Wpp) =
        (fun t : Γ(X, U.ι ''ᵁ Wpp) ↦
            t • M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ Wpp ≤ (⊤ : X.Opens))).op l) ∘
          ⇑(U.ι.appIso Wpp).inv := by
      funext r
      rw [AlgebraicGeometry.Scheme.Modules.globalSectionHom_app, hres Wpp]
      rfl
    rw [hcomp]
    exact (hbij j (U.ι ''ᵁ Wpp) hW'W hW'U).comp
      (ConcreteCategory.bijective_of_isIso (U.ι.appIso Wpp).inv)
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_unitObj_iso_of_globalSection
    (M.restrict U.ι) (fun j ↦ U.ι ⁻¹ᵁ W j) hcover m hbij'
  exact ⟨e.symm⟩

/-- **A unit value trivializes locally.** If, against some trivialization of `M` on `W`, the
global section `l` evaluates to a *unit* of `Γ(X, W)`, then multiplication by `l` is bijective
`Γ(X, W') → Γ(M, W')` for every `W' ≤ W`.

Through `sectionsLinearEquivOfTrivialization` the map `r ↦ r • l` becomes multiplication by the
restricted evaluation (`evalSection_restrictOverTrivialization` for the restriction step,
`evalSection_smul_right` for the linearity step), and a restriction of a unit is a unit. -/
theorem bijective_smul_of_isUnit_evalSection {X : Scheme.{u}} (M : X.Modules)
    (l : Γ(M, ⊤)) {W : X.Opens}
    (ψ : M.over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W))
    (hunit : IsUnit (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom
      (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l)))
    (W' : X.Opens) (hW' : W' ≤ W) :
    Function.Bijective fun r : Γ(X, W') ↦
      r • M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l := by
  set a := ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom
    (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l) with ha
  set ψ' := ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M W ψ
    (CategoryTheory.Over.mk (homOfLE hW')) with hψ'
  set τ := ModularCurves.sectionsLinearEquivOfTrivialization M W' ψ' with hτ
  have hlres : M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l =
      M.presheaf.map (homOfLE hW').op
        (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun q ↦ (ConcreteCategory.hom (M.presheaf.map q)) l)
      (Subsingleton.elim _ _)
  have hτl : τ (M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l) =
      X.presheaf.map (homOfLE hW').op a := by
    rw [hlres, hτ, hψ']
    exact ModularCurves.evalSection_restrictOverTrivialization M W ψ hW' _
  have hcomp : (fun r : Γ(X, W') ↦
        r • M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l) =
      ⇑τ.symm ∘ fun r : Γ(X, W') ↦ r * X.presheaf.map (homOfLE hW').op a := by
    funext r
    refine τ.injective ?_
    have hsmul : τ (r • M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l) =
        (show ↑(X.ringCatSheaf.obj.obj (Opposite.op W')) from r) *
          τ (M.presheaf.map (homOfLE (le_top : W' ≤ (⊤ : X.Opens))).op l) :=
      ModularCurves.SheafOfModules.evalSection_smul_right X.ringCatSheaf M W' ψ'.hom r _
    rw [Function.comp_apply, τ.apply_symm_apply, hsmul, hτl]
  rw [hcomp]
  refine τ.symm.bijective.comp ?_
  exact IsUnit.isUnit_iff_mulRight_bijective.mp
    (IsUnit.map (ConcreteCategory.hom (X.presheaf.map (homOfLE hW').op)) hunit)

/-- **Nowhere-unit-vanishing sections trivialize.** An invertible module with a global section
whose evaluation against *every* trivialization on *every* open inside `U` is a unit is trivial
over `U`.

The trivializing cover of `Scheme.Modules.IsInvertible` is intersected with `U` and its
trivializations are transported by `restrictTrivialization`, `restrictIsoOfPullbackIso` and
`overTrivializationOfRestrictIso`; then `bijective_smul_of_isUnit_evalSection` feeds
`nonempty_restrict_unitObj_iso_of_bijective_smul`. -/
theorem nonempty_restrict_unitObj_iso_of_isUnit_evalSection {X : Scheme.{u}} {M : X.Modules}
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) (l : Γ(M, ⊤)) (U : X.Opens)
    (h : ∀ (W : X.Opens), W ≤ U →
      ∀ ψ : M.over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W),
        IsUnit (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom
          (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l))) :
    Nonempty (M.restrict U.ι ≅ AlgebraicGeometry.Scheme.Modules.unitObj U.toScheme) := by
  obtain ⟨ι, V, hV, htriv⟩ := hM
  refine nonempty_restrict_unitObj_iso_of_bijective_smul M U l (fun j ↦ V j ⊓ U) ?_ ?_
  · intro x hx
    have hxV : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ⟨hj, hx⟩⟩
  · intro j W' hW'j _
    refine bijective_smul_of_isUnit_evalSection M l
      (AlgebraicGeometry.Scheme.Modules.overTrivializationOfRestrictIso M (V j ⊓ U)
        (AlgebraicGeometry.Scheme.Modules.restrictIsoOfPullbackIso M (V j ⊓ U)
          (AlgebraicGeometry.Scheme.Modules.restrictTrivialization inf_le_left
            (htriv j).some))) ?_ W' hW'j
    exact h (V j ⊓ U) inf_le_right _

/-- **THE ONE REMAINING STEP — transporting a fibre section back to a point.** *The global
section `l` of `M` is nowhere vanishing over the base-basic-open `D(φ l)`*: against any
trivialization `ψ` of `M` on an open `W ⊆ π⁻¹ D(φ l)`, the evaluation of `l` is invertible at
every point of `W`.

## The proof, and exactly where it now stands

Fix `y ∈ W`, let `k := κ(y)` be the residue field of `X` at `y` (a `Γ(S, ⊤)`-algebra through
`π`), write `P := π_* M = baseSections π M` and let `a := evalSection … ψ.hom l|_W` be the local
coordinate of `l`. Then, in order:

1. **`1 ⊗ l ≠ 0` in `k ⊗ P`.** ✅ PROVED — `tmul_one_ne_zero_of_isUnit_dual_apply` above. The
   functional `φ` sends `1 ⊗ l` to the image of `φ l` in `k`, which is invertible because
   `y ∈ π⁻¹ D(φ l)` and `κ(π y) → κ(y)` is a field map. (This is why the cover is built from a
   dual partition of unity.)
2. **`k ⊗ P ↪ ker (d⁰ ⊗ k) = H⁰(X_k, M_k)`.** ✅ PROVED — this was the blocking gap and it is now
   `kerBaseChangeComparison_orderedBaseCech_zero_bijective`
   (`ForMathlib/SeesawPushforwardInvertible.lean`), which extends the replacement's
   `kerBaseChangeComparison_bijective u` to the original differential `d⁰` along the square
   `(A ⊗ ker u) → ker (u ⊗ A) ≅ ker (d⁰ ⊗ A)` versus `(A ⊗ ker u) → (A ⊗ ker d⁰) → ker (d⁰ ⊗ A)`
   (both composites are the base change of `kZeroToCZero ∘ subtype`). It is exactly why `hhigh`,
   `hrank` and `[IsReduced S]` were added to this file.
   With 1 this gives: the image of `l` in `ker (d⁰ ⊗ k)` is nonzero.
3. **Transport the class to a nonzero section of `M_k` on `X_k`.** ✅ PROVED —
   `baseChange_unit_ne_zero_of_isUnit_dual_apply` above, which packages 1 and 2 with
   `orderedBaseCechKernelBaseChangeEquivBaseSections_apply`
   (`ForMathlib/SeesawPushforwardInvertible.lean`): the five-link fibre-transport chain sends
   `1 ⊗ l` to the *pullback of `l` along `pullback.fst π t`*, so that pullback is nonzero. The
   element-level API for the chain that this needed is now in place — see
   `orderedBaseCechXBaseChangeIso_one_tmul_of_projection_eq`
   (`ForMathlib/AffineModuleCechBaseChange.lean`) and
   `baseSectionsIsoKernelOrderedBaseCechDifferential_hom_π` /
   `orderedBaseCechObject_ext` (`ForMathlib/SchemeModuleOrderedBaseCechZero.lean`).
4. **`H⁰(X_k, M_k) ≅ k`, and descend to `y`.** ❌ REMAINING. `hfib` gives `M_k ≅ 𝒪_{X_k}` and `hπ`
   gives `Γ(X_k, 𝒪) ≅ k`, so the nonzero section of 3 becomes a nonzero constant `c ∈ k`, hence a
   **unit** of `Γ(X_k, 𝒪)`; and `X.fromSpecResidueField y` together with `𝟙` gives a section
   `σ : Spec k ⟶ X ×_S Spec k` over `y`, at which the value of `l` is `a(y)` up to a unit. Then
   `a(y) ≠ 0`, i.e. `y ∈ X.basicOpen a` (`Scheme.mem_basicOpen`).

## What still blocks 4, precisely

The transport is done; what is missing is **`evalSection` versus pullback of modules along a
scheme morphism**. Concretely, three ingredients, none of which exists in the tree:

* the **pulled-back trivialization**: from `ψ : M.over W ≅ 𝒪` produce a trivialization of
  `(Scheme.Modules.pullback g).obj M` over `g ⁻¹ᵁ W`, for `g := pullback.fst π t` — the existing
  `restrictTrivialization` / `restrictIsoOfPullbackIso` / `overTrivializationOfRestrictIso` family
  (`Picard/`) only covers *open immersions*, not a general `g`;
* the **naturality of `evalSection` along `g`**: the evaluation of `g^* l` against that
  trivialization is `g^# a`. (`evalSection_naturality` in `Picard/Evaluation.lean` is naturality in
  the *open*, not along a morphism of schemes; `evalSection_factor`
  (`Picard/PicComparison.lean`) then supplies the unit relating it to `hfib`'s own trivialization,
  on the same open, and is the piece that *does* exist.);
* the **germ comparison**: a point `z` of `X ×_S Spec k` over `y` (take `σ` above), plus the fact
  that the local homomorphism `𝒪_{X,y} → 𝒪_{X_k,z}` reflects units, so that unitness of `g^# a` at
  `z` gives unitness of `a` at `y` (`RingedSpace.isUnit_of_isUnit_germ` is then the packaging, as
  in `isUnit_evalSection_of_dual_baseSections` below).

Nothing about the *statement* is in doubt: with steps 1–3 in hand the mathematics of 4 is the
completely standard "`h⁰` of the fibre is `κ(s)`, so a nonzero section is a unit". -/
private theorem le_basicOpen_evalSection_of_dual_baseSections
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
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
    (hinv : Module.Invertible Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj M ≅
          AlgebraicGeometry.Scheme.Modules.unitObj (Limits.pullback π x)))
    (φ : Module.Dual Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (l : AlgebraicGeometry.Scheme.Modules.baseSections π M)
    (W : X.Opens) (hW : W ≤ π ⁻¹ᵁ S.basicOpen (φ l))
    (ψ : M.over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W)) :
    W ≤ X.basicOpen (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom
      (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l)) := by
  sorry

/-- Nowhere vanishing ⟹ unit. Only the packaging: `RingedSpace.isUnit_of_isUnit_germ` says a
section which is a unit in every stalk is a unit, and `Scheme.mem_basicOpen` says membership in the
basic open is exactly unitness of the germ. No affineness of `W` is needed. All the mathematics is
in `le_basicOpen_evalSection_of_dual_baseSections`. -/
private theorem isUnit_evalSection_of_dual_baseSections
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
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
    (hinv : Module.Invertible Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj M ≅
          AlgebraicGeometry.Scheme.Modules.unitObj (Limits.pullback π x)))
    (φ : Module.Dual Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (l : AlgebraicGeometry.Scheme.Modules.baseSections π M)
    (W : X.Opens) (hW : W ≤ π ⁻¹ᵁ S.basicOpen (φ l))
    (ψ : M.over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W)) :
    IsUnit (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom
      (M.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op l)) := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ W _ fun y hy ↦ ?_
  exact (X.mem_basicOpen _ y hy).mp
    (le_basicOpen_evalSection_of_dual_baseSections hπ hM U hU hUaff hhigh hrank hinv hfib
      φ l W hW ψ hy)

/-- **(`KM-SEESAW-3`, Half B.2 of Stacks [0EX7] at rank 1)** If the pushforward's global sections
`π_* M` form an invertible `Γ(S, ⊤)`-module and `M` is trivial on every field-valued fibre, then
`M` is trivial over a Zariski open cover **of the base**.

KM p. 66: *"Because `f_*L` is invertible on `S`, Zariski locally on `S` we may pick an `O_S`-basis
`ℓ` of `f_*L`."* The cover is the dual partition of unity of `hinv`: write `1 = ∑ φ_k(ℓ_k)` with
`φ_k ∈ (π_* M)^∨` and `ℓ_k ∈ Γ(X, M)`, and take `V_k := D(φ_k(ℓ_k)) ⊆ S`. On `π⁻¹ V_k` the section
`ℓ_k` is nowhere vanishing, hence trivializes `M` there.

`hfib` is not redundant. Dropping it and keeping only the rank makes the statement **false**: on an
elliptic curve `E/k`, `M = 𝒪_E(P)` for a rational `P ≠ 0` has `h⁰ = 1` stably under field
extension, so `π_* M` is invertible, but `𝒪_E → 𝒪_E(P)` is injective and *not* surjective — the
generator of `Γ(𝒪_E(P))` vanishes at `P`. Fibrewise triviality is what makes a nonzero fibre
section a *unit*; see step 3 of `le_basicOpen_evalSection_of_dual_baseSections`.

Everything except that one nowhere-vanishing step is proved here. -/
theorem exists_baseCover_restrict_unitObj_iso_of_invertible_baseSections
    {X S : Scheme.{u}} [IsAffine S] [IsReduced S] [IsNoetherian S]
    [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
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
    (hinv : Module.Invertible Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M))
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (Limits.pullback.fst π x)).obj M ≅
          AlgebraicGeometry.Scheme.Modules.unitObj (Limits.pullback π x))) :
    ∃ (ι' : Type u) (V : ι' → S.Opens), TopologicalSpace.IsOpenCover V ∧
      ∀ i, Nonempty ((M.restrict (π ⁻¹ᵁ V i).ι) ≅
        AlgebraicGeometry.Scheme.Modules.unitObj (π ⁻¹ᵁ V i).toScheme) := by
  obtain ⟨T, hT⟩ := exists_finset_dual_apply_sum_eq_one hinv
  have hspan : Ideal.span (Set.range fun i : {i // i ∈ T} ↦ i.1.1 i.1.2) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hT]
    exact Submodule.sum_mem _ fun i hi ↦ Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩
  refine ⟨{i : Module.Dual Γ(S, (⊤ : S.Opens))
      (AlgebraicGeometry.Scheme.Modules.baseSections π M) ×
      (AlgebraicGeometry.Scheme.Modules.baseSections π M) // i ∈ T},
    fun i ↦ S.basicOpen (i.1.1 i.1.2), ?_, ?_⟩
  · refine TopologicalSpace.IsOpenCover.mk ?_
    rw [← iSup_range (g := fun f ↦ S.basicOpen f)]
    exact AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (⊤ : S.Opens) _ hspan
  · intro i
    refine nonempty_restrict_unitObj_iso_of_isUnit_evalSection hM i.1.2 _ fun W hW ψ ↦ ?_
    exact isUnit_evalSection_of_dual_baseSections hπ hM U hU hUaff hhigh hrank hinv hfib
      i.1.1 i.1.2 W hW ψ

end ModularCurves
