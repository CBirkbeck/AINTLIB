import ModularCurves.ForMathlib.FiniteEtaleFundamentalGroup
import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.Coarse
import ModularCurves.Moduli.GammaHMaster
import ModularCurves.ModularCurve.YFullRoute
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The twisted modular curve Y(ρ̄_N) (Buzzard, *Formalizing Fermat* Lecture 8, p. 33)

The post-1980s target. Verbatim from the source slides:

> "We have `ρ̄_N : Gal(ℚ̄/ℚ) → Aut_{ℤ/Nℤ}(V)` equipped with an alternating
> `Gal(ℚ̄/ℚ)`-equivariant perfect pairing to `μ_N(ℚ̄)`. […] Now we can look at the functor
> on ℚ-schemes `S` parametrising elliptic curves `E/S` such that `E[N] ≅ ρ̄_N` as
> representations-with-pairing. This functor is representable by a smooth, geometrically
> irreducible curve `Y(ρ̄_N)` over ℚ. NB irreducibility is proved complex-analytically by
> uniformising the ℂ-points of the curve by the upper half plane."

Prerequisite (registered DS5): the dictionary between continuous `Gal(ℚ̄/ℚ)`-modules on
finite abelian groups and finite étale group schemes over `ℚ` (Grothendieck–Galois). The
scheme `V_ρ` attached to `ρ` is registered data with its characterising properties stated;
construction ticket chain `T-F1*` (Galois descent of the constant group scheme —
"a scary lemma (étale descent of morphisms)", Loeffler §3.6).

Statement policy: the *field-points* description (what Buzzard's application consumes:
`K`-points for `K` of characteristic zero "canonically" biject with pairs
`(E/K, E[N] ≅ ρ carrying the Weil pairing to p)`) is stated in full, with the canonicity
made precise as naturality in `K`; the full functor-on-`Sch/ℚ` representability is
`yRho_representable`. Geometric irreducibility is a black box (BB-IRR: 1980s,
complex-analytic uniformisation).
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- The absolute Galois group of `ℚ` (with its Krull topology, from mathlib): stated as
the automorphism group of the algebraic closure, definitionally
`Field.absoluteGaloisGroup ℚ` (kept as an `abbrev` of the unfolded form so the group and
Krull-topology instances apply). -/
abbrev GalQ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- **(T-F0)** `ℚ̄` contains exactly `N` `N`-th roots of unity (char. 0, algebraically
closed). Input hypothesis for mathlib's `modularCyclotomicCharacter`. -/
theorem card_rootsOfUnity_algClosureQ (N : ℕ) [NeZero N] :
    Fintype.card { x // x ∈ rootsOfUnity N (AlgebraicClosure ℚ) } = N := by
  haveI : NeZero ((N : AlgebraicClosure ℚ)) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  have hdeg : (Polynomial.cyclotomic N (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  exact hprim.card_rootsOfUnity

/-- A mod-`N` Galois representation datum for the twisted modular curve: a continuous
action of `Gal(ℚ̄/ℚ)` on `(ℤ/N)²` with cyclotomic determinant, together with the pairing
normalisation `p`. Buzzard p. 33: `ρ̄_N` "equipped with an alternating Gal-equivariant
perfect pairing to `μ_N(ℚ̄)`" — the pairing datum is an equivariant identification of
`Λ²(ρ) = det ρ` with `μ_N(ℚ̄)`, unique up to `(ℤ/N)ˣ`. -/
structure GaloisRepData (N : ℕ) [NeZero N] where
  /-- The representation. -/
  ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N)
  /-- Continuity: the kernel is open (equivalently, the action factors through a finite
  quotient — `ZMod N` is discrete). -/
  ker_open : IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ)
  /-- Cyclotomic determinant: `det ∘ ρ` is the mod-`N` cyclotomic character of `ℚ`. -/
  det_cyclo : ∀ σ : GalQ,
    Matrix.GeneralLinearGroup.det (ρ σ) =
      modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv
  /-- The pairing normalisation `p`: a group isomorphism from `ℤ/N` (the line `Λ²ρ`,
  carrying the Galois action through `det ∘ ρ`) to `μ_N(ℚ̄)`, Galois-equivariantly. -/
  p : Multiplicative (ZMod N) ≃* rootsOfUnity N (AlgebraicClosure ℚ)
  p_equivariant : ∀ (σ : GalQ) (x : Multiplicative (ZMod N)),
    σ ((p x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((p (x ^ ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv : (ZMod N)ˣ) : ZMod N).val) :
          (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)

/-! ### The Grothendieck–Galois construction of `V_ρ` (T-F1, discharging DS5)

The AG-GG development (`ForMathlib/FiniteEtaleGalois`, `FiniteEtaleFiberFunctor`,
`FiniteEtaleFundamentalGroup`) provides the equivalence
`(FiniteEtale ℚ)ᵒᵖ ≌ ContAction FintypeCat Gal(ℚ^sep/ℚ)`.  `V_ρ` is `Spec` of the
finite étale algebra corresponding to the `ρ`-twisted `(ℤ/N)²` under this equivalence.
`GalQ` is the automorphism group of the *algebraic* closure; in characteristic zero it
is canonically homeomorphically isomorphic to that of the separable closure. -/

section GaloisSepBridge

open ModularCurves.FiniteEtaleGalois in
/-- Concrete-field instance registration (see the AG-GG-3 protocol note): mathlib's
`separableClosure` instances do not unify against the `SeparableClosure` abbreviation at
concrete fields. -/
instance : CompactSpace (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  compactSpace_galSepClosure ℚ

open ModularCurves.FiniteEtaleGalois in
noncomputable instance : PreGaloisCategory.IsFundamentalGroup
    (CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ) :
      (CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ ⥤ FintypeCat.{0})
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  isFundamentalGroup_galSepClosure (k := ℚ)

/-- In characteristic zero the separable closure is the algebraic closure. -/
noncomputable def sepClosureQAlgEquiv : SeparableClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  (IntermediateField.equivOfEq
    ((separableClosure.eq_top_iff ℚ (AlgebraicClosure ℚ)).mpr inferInstance)).trans
    IntermediateField.topEquiv

/-- The multiplicative comparison between the two absolute Galois groups. -/
noncomputable def galSepMulEquivGalQ :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ≃* GalQ :=
  AlgEquiv.autCongr sepClosureQAlgEquiv

lemma continuous_galSepMulEquivGalQ : Continuous galSepMulEquivGalQ := by
  have h : Continuous (galSepMulEquivGalQ.toMonoidHom :
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) →* GalQ) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    rw [Filter.mem_map]
    obtain ⟨E, hfin, hE⟩ :=
      (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) s).mp hs
    haveI hfd : FiniteDimensional ℚ (E.map sepClosureQAlgEquiv.symm.toAlgHom) :=
      LinearEquiv.finiteDimensional
        (IntermediateField.intermediateFieldMap sepClosureQAlgEquiv.symm E).toLinearEquiv
    have hmem1 : (((E.map sepClosureQAlgEquiv.symm.toAlgHom).fixingSubgroup :
        Subgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
        Set (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) ∈ nhds 1 :=
      (krullTopology_mem_nhds_one_iff ℚ (SeparableClosure ℚ) _).mpr
        ⟨E.map sepClosureQAlgEquiv.symm.toAlgHom, hfd, subset_rfl⟩
    refine Filter.mem_of_superset hmem1 ?_
    intro σ hσ
    refine hE ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    show sepClosureQAlgEquiv (σ (sepClosureQAlgEquiv.symm x)) = x
    have hmem : sepClosureQAlgEquiv.symm x ∈ E.map sepClosureQAlgEquiv.symm.toAlgHom :=
      ⟨x, hx, rfl⟩
    rw [hσ _ hmem, AlgEquiv.apply_symm_apply]
  exact h

/-- The homeomorphic multiplicative comparison between the Galois groups of the
separable and the algebraic closure of `ℚ`. -/
noncomputable def galSepContinuousMulEquivGalQ :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ≃ₜ* GalQ :=
  { galSepMulEquivGalQ with
    continuous_toFun := continuous_galSepMulEquivGalQ
    continuous_invFun := by
      haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
        AlgebraicClosure.isAlgebraic ℚ
      haveI : T2Space GalQ := krullTopology_t2
      exact (Continuous.homeoOfEquivCompactToT2
        (f := galSepMulEquivGalQ.toEquiv)
        continuous_galSepMulEquivGalQ).symm.continuous }

end GaloisSepBridge

section RhoAction

open ModularCurves.FiniteEtaleGalois

open scoped FintypeCatDiscrete

variable {N : ℕ} [NeZero N]

/-- The `(ℤ/N)²`-fiber as a `Gal(ℚ^sep/ℚ)`-set via `ρ`.  An `abbrev` so that the
carrier projection reduces during instance search. -/
noncomputable abbrev rhoAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (Fin 2 → ZMod N)
  ρ :=
    { toFun := fun σ => FintypeCat.homMk (fun v => D.ρ (galSepMulEquivGalQ σ) • v)
      map_one' := FintypeCat.hom_ext _ _ fun v => by
        show D.ρ (galSepMulEquivGalQ 1) • v = v
        rw [map_one, map_one, one_smul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun v => by
        show D.ρ (galSepMulEquivGalQ (σ * τ)) • v = _
        rw [map_mul, map_mul, mul_smul]
        rfl }

/-- The kernel of the `ρ`-action on the separable-closure side is open. -/
lemma rhoAction_ker_open (D : GaloisRepData N) :
    IsOpen {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} := by
  have h : {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} =
      galSepMulEquivGalQ ⁻¹' (MonoidHom.ker D.ρ : Set GalQ) := rfl
  rw [h]
  exact D.ker_open.preimage continuous_galSepMulEquivGalQ

open scoped Pointwise in
/-- The `ρ`-action is continuous (the fiber is discrete and the kernel is open). -/
lemma rhoAction_isContinuous (D : GaloisRepData N) :
    (rhoAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj (rhoAction D) :
          Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (rhoAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (rhoAction D),
        {σ | σ • v = w} ×ˢ ({v} : Set _) := by
    ext ⟨σ, v⟩
    simp
  rw [hdecomp]
  refine isOpen_iUnion fun v => IsOpen.prod ?_ trivial
  refine isOpen_iff_mem_nhds.mpr fun σ₀ hσ₀ => ?_
  have hnb : σ₀ • {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} ∈ nhds σ₀ := by
    refine IsOpen.mem_nhds ((rhoAction_ker_open D).smul σ₀) ?_
    exact ⟨1, by simp only [Set.mem_setOf_eq, map_one], mul_one σ₀⟩
  refine Filter.mem_of_superset hnb ?_
  rintro σ ⟨τ, hτ, rfl⟩
  have hτ1 : D.ρ (galSepMulEquivGalQ τ) = 1 := hτ
  have hAct : (rhoAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun x => ?_
    show D.ρ (galSepMulEquivGalQ τ) • (x : Fin 2 → ZMod N) = x
    rw [hτ1, one_smul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((rhoAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The `ρ`-twisted `(ℤ/N)²` as a continuous Galois set. -/
noncomputable abbrev rhoContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoAction D, rhoAction_isContinuous D⟩

/-- The finite étale `ℚ`-algebra corresponding to the `ρ`-twisted `(ℤ/N)²` under the
Galois correspondence. -/
noncomputable def vRhoAlgebra (D : GaloisRepData N) : CommAlgCat.FiniteEtale.{0} ℚ :=
  ((finiteEtaleEquivContAction ℚ).inverse.obj (rhoContAction D)).unop

end RhoAction

/-- **(T-F1, was DS5)** The finite étale scheme `V_ρ` over `ℚ` attached to the Galois
module `(ℤ/N)²` via `ρ`: the spectrum of the finite étale algebra corresponding to the
`ρ`-twisted `(ℤ/N)²` under the Grothendieck–Galois correspondence
`(FiniteEtale ℚ)ᵒᵖ ≌ ContAction FintypeCat Gal(ℚ^sep/ℚ)`.
Specifications: `vRho_finite_etale`, `vRho_points` (T-F1a/b). -/
noncomputable def vRho {N : ℕ} [NeZero N] (D : GaloisRepData N) : Scheme.{0} :=
  Spec (.of (vRhoAlgebra D : Type 0))

/-- **(T-F1)** The structure morphism of `V_ρ`. -/
noncomputable def vRhoπ {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    vRho D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0)))

/-- **(T-F1a, specification of DS5)** `V_ρ ⟶ Spec ℚ` is finite étale. -/
theorem vRhoπ_finite_etale {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    IsFinite (vRhoπ D) ∧ Etale (vRhoπ D) := by
  constructor
  · show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · show Etale (Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0))))
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance

/-- **(DS5c / T-F1b, specification of DS5)** The canonical `ℚ̄`-points description of
`V_ρ`: points over `ℚ̄` biject with `(ℤ/N)²`. Registered as canonical data (it is part of
the Grothendieck–Galois construction of DS5); the `GalQ`-equivariance of this bijection
(the action on points being `ρ`) is the companion specification `vRhoPointsEquiv_equivariant`
in ticket `T-F1b`. -/
noncomputable def vRhoPointsEquiv {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ vRho D //
        h ≫ vRhoπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ (Fin 2 → ZMod N) :=
  ((specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)).trans
    (FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D))

/-- **(T-F1b, companion specification)** The points bijection is Galois-equivariant:
translating a `ℚ̄`-point of `V_ρ` by `σ : Gal(ℚ̄/ℚ)` corresponds to acting by `ρ σ`
on `(ℤ/N)²`. -/
theorem vRhoPointsEquiv_equivariant {N : ℕ} [NeZero N] (D : GaloisRepData N) (σ : GalQ)
    (h : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ vRho D //
        h ≫ vRhoπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    vRhoPointsEquiv D ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ h.1, by
        rw [Category.assoc, h.2, ← Spec.map_comp]
        congr 1
        ext r
        exact σ.commutes r⟩ =
      D.ρ σ • vRhoPointsEquiv D h := by
  set L1 := specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)
    with hL1
  set L2 := AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ) (A₁ := (vRhoAlgebra D : Type 0)))
    sepClosureQAlgEquiv.symm with hL2
  -- Layer 1: translation becomes post-composition with σ
  have hA : ∀ hp : (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ h.1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))),
      L1 ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ h.1, hp⟩ =
        σ.toAlgHom.comp (L1 h) := by
    intro hp
    have hpre : Spec.preimage (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ h.1) =
        Spec.preimage h.1 ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    refine AlgHom.ext fun a => ?_
    exact congrArg (fun q : CommRingCat.of (vRhoAlgebra D : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom a) hpre
  -- Layer 2: post-composition with σ becomes post-composition with the pulled-back σ
  have hB : ∀ φ : (vRhoAlgebra D : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ,
      L2 (σ.toAlgHom.comp φ) =
        (galSepMulEquivGalQ.symm σ).toAlgHom.comp (L2 φ) := by
    intro φ
    refine AlgHom.ext fun a => ?_
    show sepClosureQAlgEquiv.symm (σ (φ a)) =
      sepClosureQAlgEquiv.symm (σ (sepClosureQAlgEquiv (sepClosureQAlgEquiv.symm (φ a))))
    rw [AlgEquiv.apply_symm_apply]
  -- Layer 3: the counit is equivariant
  have hC : FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D)
      ((galSepMulEquivGalQ.symm σ).toAlgHom.comp (L2 (L1 h))) =
      D.ρ σ • FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D)
        (L2 (L1 h)) := by
    refine Eq.trans (FiniteEtaleGalois.pointsEquivOfContAction_smul (k := ℚ)
      (rhoContAction D) (galSepMulEquivGalQ.symm σ) (L2 (L1 h))) ?_
    show D.ρ (galSepMulEquivGalQ (galSepMulEquivGalQ.symm σ)) •
        FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D) (L2 (L1 h)) = _
    rw [MulEquiv.apply_symm_apply]
  refine Eq.trans (congrArg (fun y => FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (rhoContAction D) (L2 y)) (hA _)) ?_
  refine Eq.trans (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (rhoContAction D)) (hB (L1 h))) ?_
  exact hC

section FrameSubstrate

open ModularCurves.FiniteEtaleGalois

open scoped FintypeCatDiscrete

variable {N : ℕ} [NeZero N]

/-- **[T-YR-3a]** `GL₂(ℤ/N)` as a `Gal(ℚ^sep/ℚ)`-set via left `ρ`-multiplication: the
Galois set of *frames* — bare isomorphisms `(ℤ/N)²_{ℚ̄} ≅ V_ρ ×_ℚ ℚ̄` (a frame is the
image matrix of the standard basis; `σ` translates a frame to `ρ(σ)·A`). -/
noncomputable abbrev frameAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun A => D.ρ (galSepMulEquivGalQ σ) * A)
      map_one' := FintypeCat.hom_ext _ _ fun A => by
        show D.ρ (galSepMulEquivGalQ 1) * A = A
        rw [map_one, map_one, one_mul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun A => by
        show D.ρ (galSepMulEquivGalQ (σ * τ)) * A = _
        rw [map_mul, map_mul, mul_assoc]
        rfl }

open scoped Pointwise in
/-- The frame action is continuous (discrete fiber, kernel contains `ker ρ`, which is
open — the same kernel set as `rhoAction`). -/
lemma frameAction_isContinuous (D : GaloisRepData N) :
    (frameAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj (frameAction D) :
          Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (frameAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (frameAction D),
        {σ | σ • v = w} ×ˢ ({v} : Set _) := by
    ext ⟨σ, v⟩
    simp
  rw [hdecomp]
  refine isOpen_iUnion fun v => IsOpen.prod ?_ trivial
  refine isOpen_iff_mem_nhds.mpr fun σ₀ hσ₀ => ?_
  have hnb : σ₀ • {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} ∈ nhds σ₀ := by
    refine IsOpen.mem_nhds ((rhoAction_ker_open D).smul σ₀) ?_
    exact ⟨1, by simp only [Set.mem_setOf_eq, map_one], mul_one σ₀⟩
  refine Filter.mem_of_superset hnb ?_
  rintro σ ⟨τ, hτ, rfl⟩
  have hτ1 : D.ρ (galSepMulEquivGalQ τ) = 1 := hτ
  have hAct : (frameAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun A => ?_
    show D.ρ (galSepMulEquivGalQ τ) *
      (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = A
    rw [hτ1, one_mul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((frameAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The frames as a continuous Galois set. -/
noncomputable abbrev frameContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨frameAction D, frameAction_isContinuous D⟩

/-- The finite étale `ℚ`-algebra of the frame scheme. -/
noncomputable def wFramesAlgebra (D : GaloisRepData N) : CommAlgCat.FiniteEtale.{0} ℚ :=
  ((finiteEtaleEquivContAction ℚ).inverse.obj (frameContAction D)).unop

/-- **[T-YR-3a]** The finite étale `ℚ`-scheme of frames `Isom((ℤ/N)², V_ρ)`: the
`GL₂(ℤ/N)`-worth of bare isomorphisms from the constant group to `V_ρ`, as a scheme
via the Grothendieck–Galois correspondence (mirror of `vRho`). -/
noncomputable def wFrames (D : GaloisRepData N) : Scheme.{0} :=
  Spec (.of (wFramesAlgebra D : Type 0))

/-- The structure morphism of the frame scheme. -/
noncomputable def wFramesπ (D : GaloisRepData N) :
    wFrames D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0)))

/-- **[T-YR-3a]** `wFrames ⟶ Spec ℚ` is finite étale. -/
theorem wFramesπ_finite_etale (D : GaloisRepData N) :
    IsFinite (wFramesπ D) ∧ Etale (wFramesπ D) := by
  constructor
  · show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · show Etale (Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0))))
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance

/-- **[T-YR-3a]** The canonical `ℚ̄`-points description of the frame scheme: points over
`ℚ̄` biject with `GL₂(ℤ/N)`. -/
noncomputable def wFramesPointsEquiv (D : GaloisRepData N) :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ wFrames D //
        h ≫ wFramesπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ Matrix.GeneralLinearGroup (Fin 2) (ZMod N) :=
  ((specPointsEquivAlgHom ℚ (wFramesAlgebra D : Type 0) (AlgebraicClosure ℚ)).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)).trans
    (FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameContAction D))

/-- **[T-YR-3a]** Right `γ`-translation of frames as a morphism of continuous Galois
sets (right multiplication commutes with the left `ρ`-action). -/
noncomputable def frameRightMulMor (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameContAction D ⟶ frameContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun A => A * γ)
      comm := fun σ => FintypeCat.hom_ext _ _ fun A => by
        show (D.ρ (galSepMulEquivGalQ σ) * A) * γ =
          D.ρ (galSepMulEquivGalQ σ) * (A * γ)
        rw [mul_assoc] }

theorem frameRightMulMor_mul (D : GaloisRepData N)
    (γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameRightMulMor D (γ₁ * γ₂) =
      frameRightMulMor D γ₁ ≫ frameRightMulMor D γ₂ := by
  ext A i j
  exact congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) (ZMod N) =>
    (M : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) ((mul_assoc A γ₁ γ₂).symm)

theorem frameRightMulMor_one (D : GaloisRepData N) :
    frameRightMulMor D 1 = 𝟙 (frameContAction D) := by
  ext A i j
  exact congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) (ZMod N) =>
    (M : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) (mul_one A)

/-- The right translation at the algebra level, through the Galois correspondence
(contravariant: the composite flips). -/
noncomputable def wFramesRightMulAlg (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wFramesAlgebra D ⟶ wFramesAlgebra D :=
  ((finiteEtaleEquivContAction ℚ).inverse.map (frameRightMulMor D γ)).unop

/-- **[T-YR-3a]** The right `GL₂(ℤ/N)`-translation on the frame scheme. -/
noncomputable def wFramesRightMul (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) : wFrames D ⟶ wFrames D :=
  Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom)

/-- The right translation lies over `Spec ℚ`. -/
theorem wFramesRightMul_π (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wFramesRightMul D γ ≫ wFramesπ D = wFramesπ D := by
  show Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0)))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (wFramesRightMulAlg D γ).hom.hom.commutes r

/-- Functoriality of the right translation (double contravariance = covariance). -/
theorem wFramesRightMul_mul (D : GaloisRepData N)
    (γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wFramesRightMul D (γ₁ * γ₂) =
      wFramesRightMul D γ₁ ≫ wFramesRightMul D γ₂ := by
  have hAlg : wFramesRightMulAlg D (γ₁ * γ₂) =
      wFramesRightMulAlg D γ₂ ≫ wFramesRightMulAlg D γ₁ := by
    have h2 := congrArg
      (fun m => ((finiteEtaleEquivContAction ℚ).inverse.map m).unop)
      (frameRightMulMor_mul D γ₁ γ₂)
    exact h2.trans (congrArg Quiver.Hom.unop
      ((finiteEtaleEquivContAction ℚ).inverse.map_comp _ _))
  show Spec.map (CommRingCat.ofHom
      (wFramesRightMulAlg D (γ₁ * γ₂)).hom.hom.toRingHom) = _
  rw [hAlg,
    show CommRingCat.ofHom (wFramesRightMulAlg D γ₂ ≫
        wFramesRightMulAlg D γ₁).hom.hom.toRingHom =
      CommRingCat.ofHom (wFramesRightMulAlg D γ₂).hom.hom.toRingHom ≫
        CommRingCat.ofHom (wFramesRightMulAlg D γ₁).hom.hom.toRingHom from rfl,
    Spec.map_comp]
  rfl

theorem wFramesRightMul_one (D : GaloisRepData N) :
    wFramesRightMul D 1 = 𝟙 (wFrames D) := by
  have hAlg : wFramesRightMulAlg D 1 = 𝟙 (wFramesAlgebra D) := by
    have h2 := congrArg
      (fun m => ((finiteEtaleEquivContAction ℚ).inverse.map m).unop)
      (frameRightMulMor_one D)
    exact h2.trans (congrArg Quiver.Hom.unop
      ((finiteEtaleEquivContAction ℚ).inverse.map_id _))
  show Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D 1).hom.hom.toRingHom) = _
  rw [hAlg,
    show CommRingCat.ofHom (𝟙 (wFramesAlgebra D) :
        wFramesAlgebra D ⟶ wFramesAlgebra D).hom.hom.toRingHom =
      𝟙 (CommRingCat.of (wFramesAlgebra D : Type 0)) from rfl,
    Spec.map_id]
  rfl

/-- [T-YR-3b helper] Naturality of the Galois-points counit in the continuous Galois
set: the fiber functor applied to a correspondence-morphism matches the underlying
set-map (mirror of `pointsEquivOfContAction_smul`, with the counit's naturality square
in place of equivariance). -/
lemma pointsEquivOfContAction_map {X Y : ContAction FintypeCat.{0}
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)} (m : X ⟶ Y)
    (x : ((CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).obj
      ((finiteEtaleEquivContAction ℚ).inverse.obj X) : Type 0)) :
    FiniteEtaleGalois.pointsEquivOfContAction ℚ Y
        ((CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ)).map
          ((finiteEtaleEquivContAction ℚ).inverse.map m) x) =
      m.hom.hom (FiniteEtaleGalois.pointsEquivOfContAction ℚ X x) := by
  have hc := ((finiteEtaleEquivContAction ℚ).counitIso.hom.naturality m)
  have h2 := congrArg (fun q => q.hom.hom x) hc
  exact h2

/-- **[T-YR-3b]** The frame points-reading intertwines the right translation:
composing a `ℚ̄`-point with `wFramesRightMul γ` multiplies the frame by `γ`
(3-layer mirror of `vRhoPointsEquiv_equivariant`: `Spec.preimage`-extraction,
`arrowCongr`-transport, and the counit's naturality `pointsEquivOfContAction_map`). -/
theorem wFramesPointsEquiv_rightMul (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (h : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ wFrames D //
      h ≫ wFramesπ D =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    wFramesPointsEquiv D ⟨h.1 ≫ wFramesRightMul D γ, by
        rw [Category.assoc, wFramesRightMul_π, h.2]⟩ =
      wFramesPointsEquiv D h * γ := by
  set L1 := specPointsEquivAlgHom ℚ (wFramesAlgebra D : Type 0)
    (AlgebraicClosure ℚ) with hL1
  set L2 := AlgEquiv.arrowCongr
    (AlgEquiv.refl (R := ℚ) (A₁ := (wFramesAlgebra D : Type 0)))
    sepClosureQAlgEquiv.symm with hL2
  have hA : ∀ hp : (h.1 ≫ wFramesRightMul D γ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (wFramesAlgebra D : Type 0))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))),
      L1 ⟨h.1 ≫ wFramesRightMul D γ, hp⟩ =
        (L1 h).comp (wFramesRightMulAlg D γ).hom.hom := by
    intro hp
    have hpre : Spec.preimage (h.1 ≫ wFramesRightMul D γ) =
        CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom ≫
          Spec.preimage h.1 := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
      rfl
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun q : CommRingCat.of (wFramesAlgebra D : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hpre
  have hB : ∀ ψ : (wFramesAlgebra D : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ,
      L2 (ψ.comp (wFramesRightMulAlg D γ).hom.hom) =
        (L2 ψ).comp (wFramesRightMulAlg D γ).hom.hom := by
    intro ψ
    exact AlgHom.ext fun w => rfl
  have hC : FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameContAction D)
      ((L2 (L1 h)).comp (wFramesRightMulAlg D γ).hom.hom) =
      FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameContAction D)
        (L2 (L1 h)) * γ :=
    pointsEquivOfContAction_map (frameRightMulMor D γ) (L2 (L1 h))
  refine Eq.trans (congrArg (fun y => FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (frameContAction D) (L2 y)) (hA _)) ?_
  refine Eq.trans (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (frameContAction D)) (hB (L1 h))) ?_
  exact hC

/-- **[T-YR-3d-1c]** The trivial Galois action on `(ℤ/N)²` (the Galois set of the
constant scheme `(ℤ/N)²_ℚ`). -/
noncomputable abbrev constVecAction (N : ℕ) [NeZero N] :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (Fin 2 → ZMod N)
  ρ := { toFun := fun _ => FintypeCat.homMk id
         map_one' := rfl
         map_mul' := fun _ _ => rfl }

lemma constVecAction_isContinuous (N : ℕ) [NeZero N] :
    (constVecAction N).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (constVecAction N) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun y => ?_
  have huniv : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
      (CategoryTheory.forget₂ _ TopCat).obj (constVecAction N) => p.1 • p.2) ⁻¹'
      ({y} : Set _) = Set.univ ×ˢ ({y} : Set _) := by
    ext p
    constructor
    · intro hp
      exact ⟨trivial, hp⟩
    · intro hp
      exact hp.2
  rw [huniv]
  exact IsOpen.prod isOpen_univ trivial

/-- The constant `(ℤ/N)²` as a continuous Galois set. -/
noncomputable abbrev constVecContAction (N : ℕ) [NeZero N] :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨constVecAction N, constVecAction_isContinuous N⟩

/-- **[T-YR-3d-1c]** The mixed product Galois set `(ℤ/N)² × GL₂` (trivial action on
the vector factor, left `ρ`-multiplication on the frame factor) — the Galois set of
`(ℤ/N)²_ℚ ×_ℚ wFrames`. -/
noncomputable abbrev frameProdAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of ((Fin 2 → ZMod N) ×
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun vA => (vA.1, D.ρ (galSepMulEquivGalQ σ) * vA.2))
      map_one' := FintypeCat.hom_ext _ _ fun vA => by
        show (vA.1, D.ρ (galSepMulEquivGalQ 1) * vA.2) = vA
        rw [map_one, map_one, one_mul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun vA => by
        show (vA.1, D.ρ (galSepMulEquivGalQ (σ * τ)) * vA.2) = _
        rw [map_mul, map_mul, mul_assoc]
        rfl }

open scoped Pointwise in
lemma frameProdAction_isContinuous (D : GaloisRepData N) :
    (frameProdAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (frameProdAction D) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (frameProdAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (frameProdAction D),
        {σ | σ • v = w} ×ˢ ({v} : Set _) := by
    ext ⟨σ, v⟩
    simp
  rw [hdecomp]
  refine isOpen_iUnion fun v => IsOpen.prod ?_ trivial
  refine isOpen_iff_mem_nhds.mpr fun σ₀ hσ₀ => ?_
  have hnb : σ₀ • {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} ∈ nhds σ₀ := by
    refine IsOpen.mem_nhds ((rhoAction_ker_open D).smul σ₀) ?_
    exact ⟨1, by simp only [Set.mem_setOf_eq, map_one], mul_one σ₀⟩
  refine Filter.mem_of_superset hnb ?_
  rintro σ ⟨τ, hτ, rfl⟩
  have hτ1 : D.ρ (galSepMulEquivGalQ τ) = 1 := hτ
  have hAct : (frameProdAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun vA => ?_
    show ((vA : (Fin 2 → ZMod N) ×
      Matrix.GeneralLinearGroup (Fin 2) (ZMod N)).1,
      D.ρ (galSepMulEquivGalQ τ) * vA.2) = vA
    rw [hτ1, one_mul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((frameProdAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The mixed product as a continuous Galois set. -/
noncomputable abbrev frameProdContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨frameProdAction D, frameProdAction_isContinuous D⟩

/-- **[T-YR-3d-1c]** The universal-frame evaluation `(v, A) ↦ A·v` as a morphism of
continuous Galois sets (equivariant: the vector factor is trivial and
`σ·(A·v) = (ρσ·A)·v`). -/
noncomputable def frameEvalMor (D : GaloisRepData N) :
    frameProdContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vA => vA.2 • vA.1)
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => by
        show (D.ρ (galSepMulEquivGalQ σ) * vA.2) • vA.1 =
          D.ρ (galSepMulEquivGalQ σ) • (vA.2 • vA.1)
        rw [mul_smul] }

/-- First projection of the mixed product (to the trivial vector factor). -/
noncomputable def frameProdFst (D : GaloisRepData N) :
    frameProdContAction D ⟶ constVecContAction N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.fst
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => rfl }

/-- Second projection of the mixed product (to the frames). -/
noncomputable def frameProdSnd (D : GaloisRepData N) :
    frameProdContAction D ⟶ frameContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => rfl }

/-- **[T-YR-3d-1c]** The mixed product with its projections is the categorical binary
product of continuous Galois sets (mirror of `rhoSqIsProduct`). -/
noncomputable def frameProdIsProduct (D : GaloisRepData N) :
    Limits.IsLimit (Limits.BinaryFan.mk (frameProdFst D) (frameProdSnd D)) := by
  refine Limits.BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun x => (s.fst.hom.hom x, s.snd.hom.hom x))
        comm := fun σ => FintypeCat.hom_ext _ _ fun x => ?_ })
    (fun s => rfl) (fun s => rfl) (fun s m h₁ h₂ => ?_)
  · have h1 := congrArg (fun q => q x) (s.fst.hom.comm σ)
    have h2 := congrArg (fun q => q x) (s.snd.hom.comm σ)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
    exact Prod.ext h1 h2
  · ext x : 3
    refine Prod.ext ?_ ?_
    · exact congrArg (fun q : s.pt ⟶ constVecContAction N => q.hom.hom x) h₁
    · exact congrArg (fun q : s.pt ⟶ frameContAction D => q.hom.hom x) h₂

/-- **[asm-2b-i]** The `ρ`-mixed product Galois set: vectors-with-frames where *both*
factors carry the `ρ`-translation, `σ·(w, A) = (ρσ·w, ρσ·A)` — the target of the
shear `(v, A) ↦ (A·v, A)`. -/
noncomputable abbrev rhoFrameProdAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of ((Fin 2 → ZMod N) ×
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun wA => (D.ρ (galSepMulEquivGalQ σ) • wA.1,
          D.ρ (galSepMulEquivGalQ σ) * wA.2))
      map_one' := FintypeCat.hom_ext _ _ fun wA => by
        show (D.ρ (galSepMulEquivGalQ 1) • wA.1,
          D.ρ (galSepMulEquivGalQ 1) * wA.2) = wA
        rw [map_one, map_one, one_smul, one_mul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun wA => by
        show (D.ρ (galSepMulEquivGalQ (σ * τ)) • wA.1,
          D.ρ (galSepMulEquivGalQ (σ * τ)) * wA.2) = _
        rw [map_mul, map_mul, mul_smul, mul_assoc]
        rfl }

open scoped Pointwise in
lemma rhoFrameProdAction_isContinuous (D : GaloisRepData N) :
    (rhoFrameProdAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (rhoFrameProdAction D) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (rhoFrameProdAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (rhoFrameProdAction D),
        {σ | σ • v = w} ×ˢ ({v} : Set _) := by
    ext ⟨σ, v⟩
    simp
  rw [hdecomp]
  refine isOpen_iUnion fun v => IsOpen.prod ?_ trivial
  refine isOpen_iff_mem_nhds.mpr fun σ₀ hσ₀ => ?_
  have hnb : σ₀ • {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} ∈ nhds σ₀ := by
    refine IsOpen.mem_nhds ((rhoAction_ker_open D).smul σ₀) ?_
    exact ⟨1, by simp only [Set.mem_setOf_eq, map_one], mul_one σ₀⟩
  refine Filter.mem_of_superset hnb ?_
  rintro σ ⟨τ, hτ, rfl⟩
  have hτ1 : D.ρ (galSepMulEquivGalQ τ) = 1 := hτ
  have hAct : (rhoFrameProdAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun wA => ?_
    show (D.ρ (galSepMulEquivGalQ τ) • (wA : (Fin 2 → ZMod N) ×
      Matrix.GeneralLinearGroup (Fin 2) (ZMod N)).1,
      D.ρ (galSepMulEquivGalQ τ) * wA.2) = wA
    rw [hτ1, one_smul, one_mul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((rhoFrameProdAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The `ρ`-mixed product as a continuous Galois set. -/
noncomputable abbrev rhoFrameProdContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoFrameProdAction D, rhoFrameProdAction_isContinuous D⟩

/-- First projection of the `ρ`-mixed product (to the `ρ`-vectors). -/
noncomputable def rhoFrameProdFst (D : GaloisRepData N) :
    rhoFrameProdContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.fst
      comm := fun σ => FintypeCat.hom_ext _ _ fun wA => rfl }

/-- Second projection of the `ρ`-mixed product (to the frames). -/
noncomputable def rhoFrameProdSnd (D : GaloisRepData N) :
    rhoFrameProdContAction D ⟶ frameContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun σ => FintypeCat.hom_ext _ _ fun wA => rfl }

/-- **[asm-2b-i]** The `ρ`-mixed product with its projections is the categorical
binary product of continuous Galois sets. -/
noncomputable def rhoFrameProdIsProduct (D : GaloisRepData N) :
    Limits.IsLimit (Limits.BinaryFan.mk (rhoFrameProdFst D) (rhoFrameProdSnd D)) := by
  refine Limits.BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun x => (s.fst.hom.hom x, s.snd.hom.hom x))
        comm := fun σ => FintypeCat.hom_ext _ _ fun x => ?_ })
    (fun s => rfl) (fun s => rfl) (fun s m h₁ h₂ => ?_)
  · have h1 := congrArg (fun q => q x) (s.fst.hom.comm σ)
    have h2 := congrArg (fun q => q x) (s.snd.hom.comm σ)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
    exact Prod.ext h1 h2
  · ext x : 3
    refine Prod.ext ?_ ?_
    · exact congrArg (fun q : s.pt ⟶ rhoContAction D => q.hom.hom x) h₁
    · exact congrArg (fun q : s.pt ⟶ frameContAction D => q.hom.hom x) h₂

section PiAlgHom

/-- [asm-1 leaf] The coordinate idempotents of a finite split algebra map to
zero-or-one in a domain. -/
private theorem piAlgHom_single_zero_or_one {k : Type} [Field k] {ι : Type}
    [Fintype ι] [DecidableEq ι] {L : Type} [CommRing L] [NoZeroDivisors L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) (i : ι) :
    φ (Pi.single i 1) = 0 ∨ φ (Pi.single i 1) = 1 := by
  have hidem : φ (Pi.single i 1) * φ (Pi.single i 1) = φ (Pi.single i 1) := by
    rw [← map_mul]
    congr 1
    ext j
    by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  have h2 : φ (Pi.single i 1) * (φ (Pi.single i 1) - 1) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.mp h3)

/-- [asm-1 leaf] Distinct coordinate idempotents are orthogonal after `φ`. -/
private theorem piAlgHom_single_orth {k : Type} [Field k] {ι : Type}
    [Fintype ι] [DecidableEq ι] {L : Type} [CommRing L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) {i j : ι} (hij : i ≠ j) :
    φ (Pi.single i 1) * φ (Pi.single j 1) = 0 := by
  rw [← map_mul]
  have h0 : (Pi.single i 1 : ι → k) * Pi.single j 1 = 0 := by
    ext m
    by_cases hm : m = i
    · subst hm
      simp [Pi.single_apply, hij.symm]
    · simp [Pi.single_apply, hm]
  rw [h0, map_zero]

/-- [asm-1 leaf] The images of the coordinate idempotents sum to one. -/
private theorem piAlgHom_single_sum {k : Type} [Field k] {ι : Type}
    [Fintype ι] [DecidableEq ι] {L : Type} [CommRing L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) :
    ∑ i, φ (Pi.single i 1) = 1 := by
  rw [← map_sum]
  have h1 : (∑ i, Pi.single i (1 : k)) = (1 : ι → k) := by
    ext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  rw [h1, map_one]

/-- [asm-1 leaf] The index at which a split-algebra homomorphism into a domain
evaluates. -/
noncomputable def piAlgHomIndex {k : Type} [Field k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {L : Type} [CommRing L] [Nontrivial L] [NoZeroDivisors L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) : ι := by
  classical
  refine Finset.choose (fun i => φ (Pi.single i 1) = 1) Finset.univ ?_
  obtain ⟨i, hi⟩ : ∃ i, φ (Pi.single i 1) = 1 := by
    by_contra hnone
    push_neg at hnone
    have hall : ∀ i, φ (Pi.single i 1) = 0 := fun i =>
      (piAlgHom_single_zero_or_one φ i).resolve_right (hnone i)
    have hs := piAlgHom_single_sum φ
    rw [Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  refine ⟨i, ⟨Finset.mem_univ i, hi⟩, ?_⟩
  rintro j ⟨-, hj⟩
  by_contra hji
  have horth := piAlgHom_single_orth φ hji
  rw [hj, hi, one_mul] at horth
  exact one_ne_zero horth

theorem piAlgHomIndex_spec {k : Type} [Field k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {L : Type} [CommRing L] [Nontrivial L] [NoZeroDivisors L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) :
    φ (Pi.single (piAlgHomIndex φ) 1) = 1 := by
  classical
  exact Finset.choose_property (fun i => φ (Pi.single i 1) = 1) Finset.univ _

theorem piAlgHomIndex_unique {k : Type} [Field k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {L : Type} [CommRing L] [Nontrivial L] [NoZeroDivisors L]
    [Algebra k L] (φ : (ι → k) →ₐ[k] L) {j : ι}
    (hj : φ (Pi.single j 1) = 1) : j = piAlgHomIndex φ := by
  by_contra hji
  have horth := piAlgHom_single_orth φ hji
  rw [hj, piAlgHomIndex_spec, one_mul] at horth
  exact one_ne_zero horth

/-- [asm-1 leaf] The evaluation index is invariant under post-composition with an
algebra automorphism (`σ 1 = 1`). -/
theorem piAlgHomIndex_comp {k : Type} [Field k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {L : Type} [CommRing L] [Nontrivial L] [NoZeroDivisors L]
    [Algebra k L] (σ : L ≃ₐ[k] L) (φ : (ι → k) →ₐ[k] L) :
    piAlgHomIndex ((σ : L →ₐ[k] L).comp φ) = piAlgHomIndex φ := by
  refine (piAlgHomIndex_unique _ ?_).symm
  show σ (φ (Pi.single (piAlgHomIndex φ) 1)) = 1
  rw [piAlgHomIndex_spec, map_one]

/-- **[asm-1 leaf]** Algebra homomorphisms out of a finite split `k`-algebra into a
domain are coordinate evaluations. -/
noncomputable def piAlgHomEquiv (k : Type) [Field k] (ι : Type) [Fintype ι]
    [DecidableEq ι] (L : Type) [CommRing L] [Nontrivial L] [NoZeroDivisors L]
    [Algebra k L] :
    ((ι → k) →ₐ[k] L) ≃ ι where
  toFun := piAlgHomIndex
  invFun i := (Algebra.ofId k L).comp (Pi.evalAlgHom k (fun _ => k) i)
  left_inv φ := by
    classical
    refine (AlgHom.ext fun x => ?_).symm
    have hx : x = ∑ j, x j • Pi.single j (1 : k) := by
      ext m
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    calc φ x = ∑ j, x j • φ (Pi.single j (1 : k)) := by
          conv_lhs => rw [hx]
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => map_smul φ _ _
      _ = x (piAlgHomIndex φ) • φ (Pi.single (piAlgHomIndex φ) (1 : k)) := by
          refine Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) ?_
          intro j _ hj
          have h0 : φ (Pi.single j (1 : k)) = 0 :=
            (piAlgHom_single_zero_or_one φ j).resolve_right
              (fun h1 => hj (piAlgHomIndex_unique φ h1))
          rw [h0, smul_zero]
      _ = ((Algebra.ofId k L).comp
            (Pi.evalAlgHom k (fun _ => k) (piAlgHomIndex φ))) x := by
          rw [piAlgHomIndex_spec, Algebra.smul_def, mul_one]
          rfl
  right_inv i := by
    classical
    refine (piAlgHomIndex_unique _ ?_).symm
    show (Algebra.ofId k L) ((Pi.evalAlgHom k (fun _ => k) i) (Pi.single i 1)) = 1
    rw [show (Pi.evalAlgHom k (fun _ => k) i) (Pi.single i 1) = 1 from by
      simp [Pi.single_apply], map_one]

end PiAlgHom

/-- **[asm-1]** The correspondence-image of the split algebra is the trivial Galois
set: the fiber is the `AlgHom`-set, identified with `(ℤ/N)²` by `piAlgHomEquiv`; the
Galois action is post-composition, which fixes the evaluation index
(`piAlgHomIndex_comp`), matching the trivial action. -/
noncomputable def constVecCorrespondenceIso (N : ℕ) [NeZero N] :
    (finiteEtaleEquivContAction ℚ).functor.obj
        (Opposite.op (CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ))) ≅
      constVecContAction N where
  hom := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun φ => piAlgHomIndex φ)
      comm := fun σ => FintypeCat.hom_ext _ _ fun φ => piAlgHomIndex_comp σ φ }
  inv := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun i =>
        (Algebra.ofId ℚ (SeparableClosure ℚ)).comp
          (Pi.evalAlgHom ℚ (fun _ => ℚ) i))
      comm := fun σ => FintypeCat.hom_ext _ _ fun i => AlgHom.ext fun x =>
        (σ.commutes _).symm }
  hom_inv_id := by
    ext φ
    exact congrArg (fun ψ => ψ)
      ((piAlgHomEquiv ℚ (Fin 2 → ZMod N) (SeparableClosure ℚ)).left_inv φ)
  inv_hom_id := by
    ext i x
    exact congrFun
      ((piAlgHomEquiv ℚ (Fin 2 → ZMod N) (SeparableClosure ℚ)).right_inv i) x

/-- The finite étale `ℚ`-algebra of the constant `(ℤ/N)²`-scheme. -/
noncomputable def constVecAlgebra (N : ℕ) [NeZero N] : CommAlgCat.FiniteEtale.{0} ℚ :=
  ((finiteEtaleEquivContAction ℚ).inverse.obj (constVecContAction N)).unop

/-- **[asm-1]** The constant-scheme algebra is the split algebra: transport of
`constVecCorrespondenceIso` through the correspondence's inverse and unit. -/
noncomputable def constVecAlgebraIso (N : ℕ) [NeZero N] :
    constVecAlgebra N ≅ CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) :=
  (((finiteEtaleEquivContAction ℚ).inverse.mapIso
      (constVecCorrespondenceIso N).symm ≪≫
    ((finiteEtaleEquivContAction ℚ).unitIso.app
      (Opposite.op (CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)))).symm).unop).symm


/-- **[T-YR-3d-1c step-3]** Transport of the mixed product through the Galois
correspondence: the algebra of the product is the tensor product (mirror of
`vRhoSqAlgebraIso`). -/
noncomputable def frameProdAlgebraIso (D : GaloisRepData N) :
    (finiteEtaleEquivContAction ℚ).inverse.obj (frameProdContAction D) ≅
      Opposite.op (FiniteEtaleGalois.tensorObj (constVecAlgebra N)
        (wFramesAlgebra D)) := by
  have h1 : Limits.IsLimit ((finiteEtaleEquivContAction ℚ).inverse.mapCone
      (Limits.BinaryFan.mk (frameProdFst D) (frameProdSnd D))) :=
    Limits.isLimitOfPreserves _ (frameProdIsProduct D)
  have h1' := (Limits.IsLimit.postcomposeHomEquiv
    (Limits.pairComp (constVecContAction N) (frameContAction D)
      (finiteEtaleEquivContAction ℚ).inverse) _).symm h1
  exact h1'.conePointUniqueUpToIso
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (constVecAlgebra N)
      (wFramesAlgebra D))

/-- **[T-YR-3d-1c step-3]** The evaluation comultiplication: the finite étale algebra
map corresponding to the universal-frame evaluation (mirror of `vRhoComulHom`). -/
noncomputable def frameEvalAlgHom (D : GaloisRepData N) :
    vRhoAlgebra D ⟶ FiniteEtaleGalois.tensorObj (constVecAlgebra N)
      (wFramesAlgebra D) :=
  ((frameProdAlgebraIso D).inv ≫
    (finiteEtaleEquivContAction ℚ).inverse.map (frameEvalMor D)).unop

/-- **[asm-2b-ii]** Transport of the `ρ`-mixed product through the Galois
correspondence: the algebra of the `ρ`-mixed product is the tensor product
(mirror of `frameProdAlgebraIso`). -/
noncomputable def rhoFrameProdAlgebraIso (D : GaloisRepData N) :
    (finiteEtaleEquivContAction ℚ).inverse.obj (rhoFrameProdContAction D) ≅
      Opposite.op (FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
        (wFramesAlgebra D)) := by
  have h1 : Limits.IsLimit ((finiteEtaleEquivContAction ℚ).inverse.mapCone
      (Limits.BinaryFan.mk (rhoFrameProdFst D) (rhoFrameProdSnd D))) :=
    Limits.isLimitOfPreserves _ (rhoFrameProdIsProduct D)
  have h1' := (Limits.IsLimit.postcomposeHomEquiv
    (Limits.pairComp (rhoContAction D) (frameContAction D)
      (finiteEtaleEquivContAction ℚ).inverse) _).symm h1
  exact h1'.conePointUniqueUpToIso
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D)
      (wFramesAlgebra D))

/-- **[asm-2b-ii]** The `ρ`-mixed tensor-splitting bridge is compatible with the left
cofan-injection (mirror of `frameProdAlgebraIso_inv_left`). -/
theorem rhoFrameProdAlgebraIso_inv_left (D : GaloisRepData N) :
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (rhoFrameProdFst D)).unop ≫ (rhoFrameProdAlgebraIso D).inv.unop =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (vRhoAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (vRhoAlgebra D : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hcomp := Limits.IsLimit.conePointUniqueUpToIso_hom_comp
    ((Limits.IsLimit.postcomposeHomEquiv
        (Limits.pairComp (rhoContAction D) (frameContAction D)
          (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse) _).symm
      (Limits.isLimitOfPreserves _ (rhoFrameProdIsProduct D)))
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D)
      (wFramesAlgebra D))
    ⟨Limits.WalkingPair.left⟩
  have hop : ((FiniteEtaleGalois.tensorBinaryCofan (vRhoAlgebra D)
        (wFramesAlgebra D)).op).π.app ⟨Limits.WalkingPair.left⟩
      = (rhoFrameProdAlgebraIso D).inv
          ≫ (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
              (rhoFrameProdFst D) :=
    ((Iso.inv_hom_id_assoc (rhoFrameProdAlgebraIso D) _).symm.trans
      (congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·) hcomp)).trans
      (congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·) (Category.comp_id _))
  exact (congrArg Quiver.Hom.unop hop.symm).trans rfl

/-- **[asm-2b-ii]** The `ρ`-mixed tensor-splitting bridge is compatible with the right
cofan-injection (mirror of `frameProdAlgebraIso_inv_right`). -/
theorem rhoFrameProdAlgebraIso_inv_right (D : GaloisRepData N) :
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (rhoFrameProdSnd D)).unop ≫ (rhoFrameProdAlgebraIso D).inv.unop =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (vRhoAlgebra D : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hcomp := Limits.IsLimit.conePointUniqueUpToIso_hom_comp
    ((Limits.IsLimit.postcomposeHomEquiv
        (Limits.pairComp (rhoContAction D) (frameContAction D)
          (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse) _).symm
      (Limits.isLimitOfPreserves _ (rhoFrameProdIsProduct D)))
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D)
      (wFramesAlgebra D))
    ⟨Limits.WalkingPair.right⟩
  have hop : ((FiniteEtaleGalois.tensorBinaryCofan (vRhoAlgebra D)
        (wFramesAlgebra D)).op).π.app ⟨Limits.WalkingPair.right⟩
      = (rhoFrameProdAlgebraIso D).inv
          ≫ (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
              (rhoFrameProdSnd D) :=
    ((Iso.inv_hom_id_assoc (rhoFrameProdAlgebraIso D) _).symm.trans
      (congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·) hcomp)).trans
      (congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·) (Category.comp_id _))
  exact (congrArg Quiver.Hom.unop hop.symm).trans rfl

/-- **[asm-1]** `Spec` of the split-vs-constVec algebra identification. -/
noncomputable def constVecSpecIso (N : ℕ) [NeZero N] :
    Spec (CommRingCat.of ((Fin 2 → ZMod N) → ℚ)) ≅
      Spec (CommRingCat.of (constVecAlgebra N : Type 0)) where
  hom := Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).hom.hom.hom.toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).inv.hom.hom.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp,
      show CommRingCat.ofHom (constVecAlgebraIso N).inv.hom.hom.toRingHom ≫
          CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom =
        𝟙 (CommRingCat.of ((Fin 2 → ZMod N) → ℚ)) from ?_, Spec.map_id]
    have h := congrArg (fun (f : CommAlgCat.FiniteEtale.of ℚ
        ((Fin 2 → ZMod N) → ℚ) ⟶ CommAlgCat.FiniteEtale.of ℚ
        ((Fin 2 → ZMod N) → ℚ)) =>
      CommRingCat.ofHom f.hom.hom.toRingHom) ((constVecAlgebraIso N).inv_hom_id)
    exact h
  inv_hom_id := by
    rw [← Spec.map_comp,
      show CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
          CommRingCat.ofHom (constVecAlgebraIso N).inv.hom.hom.toRingHom =
        𝟙 (CommRingCat.of (constVecAlgebra N : Type 0)) from ?_, Spec.map_id]
    have h := congrArg (fun (f : constVecAlgebra N ⟶ constVecAlgebra N) =>
      CommRingCat.ofHom f.hom.hom.toRingHom) ((constVecAlgebraIso N).hom_inv_id)
    exact h

/-- **[asm-1 COMPLETE]** The constant scheme over `Spec ℚ` is the correspondence-built
constant-vector scheme: `constSchemeSpecIso` composed with `Spec` of the algebra
identification. -/
noncomputable def constVecSchemeIso (N : ℕ) [NeZero N] :
    constScheme (Spec (CommRingCat.of ℚ)) (Fin 2 → ZMod N) ≅
      Spec (CommRingCat.of (constVecAlgebra N : Type 0)) :=
  constSchemeSpecIso (CommRingCat.of ℚ) (Fin 2 → ZMod N) ≪≫ constVecSpecIso N

/-- The constant-`(ℤ/N)²` scheme via the correspondence, with its structure map. -/
noncomputable def constVecScheme (N : ℕ) [NeZero N] : Scheme.{0} :=
  Spec (.of (constVecAlgebra N : Type 0))

noncomputable def constVecSchemeπ (N : ℕ) [NeZero N] :
    constVecScheme N ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)))

/-- **[T-YR-3d-1c step-4]** The universal-frame evaluation at the scheme level:
`(ℤ/N)²_ℚ ×_ℚ Isom((ℤ/N)², V_ρ) ⟶ V_ρ` (mirror of `vRhoAdd`: the fibre-product/tensor
identification followed by `Spec` of the evaluation comultiplication). -/
noncomputable def frameEval (D : GaloisRepData N) :
    pullback (constVecSchemeπ N) (wFramesπ D) ⟶ vRho D :=
  (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
    (wFramesAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)

end FrameSubstrate

section FramedProblem

variable {N : ℕ} [NeZero N]

/-- [T-YR-3b helper] The pull of a globally `N`-killed section is raw-killed at any
point (the `weilPairingEval`-input form; `Point.pull_zsmul` + the T-YR-4 smul→raw
conversion). -/
theorem sectionPull_raw_kill {T T' : Scheme.{0}} {E : EllipticCurve T} (t : T' ⟶ T)
    {P : E.Section} (hP : (N : ℤ) • P = 0) :
    (EllipticCurve.Point.pull E t P).1 ≫ E.mulByHom N = t ≫ E.zero := by
  have h1 : (N : ℤ) • EllipticCurve.Point.pull E t P = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hP, EllipticCurve.Point.pull_zero]
  have hval := congrArg Subtype.val h1
  rw [E.point_smul_eq_comp_mulBy, E.point_zero_val] at hval
  exact hval

/-- **[T-YR-3b]** Symplectic compatibility of a full-level pair with a frame, at
geometric points: the Weil pairing of the pulled basis equals `p` of the frame's
determinant. Diagonal-`GL₂`-invariant (both sides twist by `det γ`; the invariance
lemma is the quotient-descent supply). -/
def FramedSymp (D : GaloisRepData N) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ))
    (E : EllipticCurve T) (P Q : E.Section)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) : Prop :=
  ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))),
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
        (E.weilPairingEval (EllipticCurve.Point.pull E t P)
          (EllipticCurve.Point.pull E t Q)
          (sectionPull_raw_kill t hP) (sectionPull_raw_kill t hQ)).1 =
      ((D.p (Multiplicative.ofAdd
        (((Matrix.GeneralLinearGroup.det
          (wFramesPointsEquiv D ⟨t ≫ h, by
            rw [Category.assoc, hover, ht]⟩) : (ZMod N)ˣ) : ZMod N))) :
        (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)

end FramedProblem

/-- The `(ℤ/N)²`-coordinate of a `ℚ̄`-valued raw `N`-torsion point of `E`, read through a
`ρ`-level isomorphism and the canonical points description of `V_ρ`. Real construction
(pullback plumbing) modulo the registered data it consumes. -/
noncomputable def coord {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) : Fin 2 → ZMod N :=
  vRhoPointsEquiv D
    ⟨E.pointToTorsion x hx ≫ torsionIso.hom ≫ pullback.fst _ _, by
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc torsionIso.hom, hOver, ← Category.assoc,
        E.pointToTorsion_torsionπ, ht]⟩

/-- The pairing-compatibility relation at a geometric point: `e_N(x,y) = p(a₁b₂ − a₂b₁)`
where `(a₁,a₂), (b₁,b₂)` are the coordinates of `x, y`. The two sides live in
`Γ(Spec ℚ̄, ⊤)ˣ`-roots and `μ_N(ℚ̄)` respectively and are compared through the canonical
`Γ`–`Spec` ring isomorphism; the definitional unfolding is ticket `T-F3` (this `Prop` is
`sorry`-defined *as a definition of the relation*, discharged by T-F3 — register DS5d). -/
def PairingCompatAt {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) : Prop :=
  (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
      (E.weilPairingEval x y hx hy).1 =
    ((D.p (Multiplicative.ofAdd
      (coord D sT torsionIso hOver t ht x hx 0 *
          coord D sT torsionIso hOver t ht y hy 1 -
        coord D sT torsionIso hOver t ht x hx 1 *
          coord D sT torsionIso hOver t ht y hy 0)) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)

/-- A **ρ-level structure** on an elliptic curve `E` over a `ℚ`-scheme `T`: an
isomorphism of group schemes over `T` between `E[N]` and the pullback of `V_ρ`, carrying
the Weil pairing `e_N` to the pairing `p` of the datum.

Skeleton form: the underlying scheme isomorphism over `T`, with group-compatibility and
pairing-compatibility recorded as `Prop` fields against the registered structures. The
pairing condition is stated on geometric points via `weilPairingEval`; strengthening to
the scheme-level identity is ticket `T-F3`. -/
structure RhoLevelStructure {N : ℕ} [NeZero N] (D : GaloisRepData N)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T) where
  /-- The isomorphism `E[N] ≅ V_ρ ×_ℚ T` of `T`-schemes. -/
  torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT
  over_T : torsionIso.hom ≫ pullback.snd _ _ = E.torsionπ N
  /-- Compatibility of the identification with the `(ℤ/N)²`-coordinates on geometric
  points: composing a `ℚ̄`-valued torsion point of `E` with the isomorphism and reading
  off coordinates via `vRhoPointsEquiv` is *additive* and carries the Weil pairing to the
  standard symplectic pairing transported through `p`. Stated on geometric points valued
  in `ℚ̄`; the scheme-level (group-object morphism) form is ticket `T-F3`. -/
  coords_additive : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hxy : (x + y).1 ≫ E.mulByHom N = t ≫ E.zero),
    coord D sT torsionIso over_T t ht (x + y) hxy =
      coord D sT torsionIso over_T t ht x hx + coord D sT torsionIso over_T t ht y hy
  /-- Pairing compatibility: the Weil pairing of two `ℚ̄`-valued torsion points equals
  `p` of the standard symplectic pairing `a₁b₂ − a₂b₁` of their coordinates.
  (`Γ(Spec ℚ̄, ⊤)`-valued roots of unity are compared with `μ_N(ℚ̄)` through the
  canonical `Γ`–`Spec` isomorphism; equation recorded through `pairingCompatStatement`
  to keep the field readable.) -/
  pairing_compat : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
    PairingCompatAt D sT torsionIso over_T t ht x y hx hy

section RhoProblem

open CategoryTheory

variable {N : ℕ} [NeZero N]

/-- **[T-YR-2b]** The `N`-torsion map along an `Ell/ℚ`-morphism (`[N]`-naturality
`EllHom.mulByHom_top` + the zero-section compatibility give the kernel-square lift). -/
noncomputable def torsionMapOfEllHom {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] : A.curve.torsion N ⟶ B.curve.torsion N :=
  pullback.lift (A.curve.torsionι N ≫ g.top) (A.curve.torsionπ N ≫ g.baseHom) (by
    rw [Category.assoc, ← ModularCurves.EllHom.mulByHom_top, ← Category.assoc]
    rw [show A.curve.torsionι N ≫ A.curve.mulByHom N =
      A.curve.torsionπ N ≫ A.curve.zero from pullback.condition]
    rw [Category.assoc, g.zero_w, ← Category.assoc])

@[reassoc (attr := simp)]
theorem torsionMapOfEllHom_ι {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    torsionMapOfEllHom g N ≫ B.curve.torsionι N = A.curve.torsionι N ≫ g.top :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem torsionMapOfEllHom_π {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    torsionMapOfEllHom g N ≫ B.curve.torsionπ N = A.curve.torsionπ N ≫ g.baseHom :=
  pullback.lift_snd _ _ _

/-- **[T-YR-2c]** The torsion square of an `Ell/ℚ`-morphism is cartesian (the
abstract-square version of `torsion_baseChange_isPullback`). -/
theorem isPullback_torsionMapOfEllHom {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    IsPullback (torsionMapOfEllHom g N) (A.curve.torsionπ N) (B.curve.torsionπ N)
      g.baseHom := by
  have hcond : ∀ {W : Scheme.{0}} (sfst : W ⟶ B.curve.torsion N)
      (ssnd : W ⟶ A.base), sfst ≫ B.curve.torsionπ N = ssnd ≫ g.baseHom →
      (sfst ≫ B.curve.torsionι N) ≫ B.curve.π = ssnd ≫ g.baseHom := by
    intro W sfst ssnd hs
    rw [Category.assoc, B.curve.torsionι_π N, hs]
  have hkill : ∀ {W : Scheme.{0}} (sfst : W ⟶ B.curve.torsion N)
      (ssnd : W ⟶ A.base) (hs : sfst ≫ B.curve.torsionπ N = ssnd ≫ g.baseHom),
      g.isPullback.lift (sfst ≫ B.curve.torsionι N) ssnd (hcond sfst ssnd hs) ≫
          A.curve.mulByHom N = ssnd ≫ A.curve.zero := by
    intro W sfst ssnd hs
    apply g.isPullback.hom_ext
    · rw [Category.assoc, ModularCurves.EllHom.mulByHom_top, ← Category.assoc,
        g.isPullback.lift_fst, Category.assoc,
        show B.curve.torsionι N ≫ B.curve.mulByHom N =
          B.curve.torsionπ N ≫ B.curve.zero from pullback.condition,
        ← Category.assoc, hs, Category.assoc, ← g.zero_w, ← Category.assoc]
    · rw [Category.assoc, EllipticCurve.mulByHom_π, g.isPullback.lift_snd,
        Category.assoc, A.curve.zero_π, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (torsionMapOfEllHom_π g N)
    (fun s => (pullback.lift
      (g.isPullback.lift (s.fst ≫ B.curve.torsionι N) s.snd
        (hcond s.fst s.snd s.condition))
      s.snd (hkill s.fst s.snd s.condition) : s.pt ⟶ A.curve.torsion N))
    (fun s => ?_) (fun s => pullback.lift_snd _ _ _) (fun s m hm1 hm2 => ?_))
  · apply pullback.hom_ext
    · show (_ ≫ torsionMapOfEllHom g N) ≫ B.curve.torsionι N =
        s.fst ≫ B.curve.torsionι N
      rw [Category.assoc, torsionMapOfEllHom_ι g N, ← Category.assoc]
      exact (congrArg (· ≫ g.top) (pullback.lift_fst _ _ _)).trans
        (g.isPullback.lift_fst _ _ _)
    · show (_ ≫ torsionMapOfEllHom g N) ≫ B.curve.torsionπ N =
        s.fst ≫ B.curve.torsionπ N
      rw [Category.assoc, torsionMapOfEllHom_π g N, ← Category.assoc]
      exact (congrArg (· ≫ g.baseHom) (pullback.lift_snd _ _ _)).trans
        s.condition.symm
  · apply pullback.hom_ext
    · show m ≫ A.curve.torsionι N = _ ≫ A.curve.torsionι N
      refine Eq.trans ?_ (pullback.lift_fst
        (g.isPullback.lift (s.fst ≫ B.curve.torsionι N) s.snd
          (hcond s.fst s.snd s.condition))
        s.snd (hkill s.fst s.snd s.condition)).symm
      apply g.isPullback.hom_ext
      · rw [g.isPullback.lift_fst, Category.assoc, ← torsionMapOfEllHom_ι g N,
          ← Category.assoc, hm1]
      · rw [g.isPullback.lift_snd, Category.assoc, A.curve.torsionι_π N, hm2]
    · show m ≫ A.curve.torsionπ N = _ ≫ A.curve.torsionπ N
      exact hm2.trans (pullback.lift_snd _ _ _).symm
/-- [T-YR-2 helper, SKELETON] Transport of `N`-torsion along an `Ell/ℚ`-morphism: the
cartesian curve square (`EllHom.isPullback`) pasted with
`torsion_baseChange_isPullback` (TorsionFibre.lean) identifies the source torsion with
the pullback of the target torsion along the base map. -/
noncomputable def ellHomTorsionIso {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    A.curve.torsion N ≅ pullback (B.curve.torsionπ N) g.baseHom :=
  (isPullback_torsionMapOfEllHom g N).isoPullback

/-- [T-YR-2 helper, SKELETON] The torsion transport lies over the base. -/
theorem ellHomTorsionIso_over {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    (ellHomTorsionIso g N).hom ≫ pullback.snd (B.curve.torsionπ N) g.baseHom =
      A.curve.torsionπ N :=
  (isPullback_torsionMapOfEllHom g N).isoPullback_hom_snd

/-- [T-YR-2e helper] Post-composition with a pointed monoid-object morphism of
elliptic-curve records over a fixed base is an *additive* map on `t`-points:
`IsMonHom.monoidHom` postcomposition transported through `pointEquivOverHom`. -/
noncomputable def EllipticCurve.pointMapOfMonHom {S : Scheme.{u}}
    {E F : EllipticCurve S} (φ : E.asOver ⟶ F.asOver) [IsMonHom φ]
    {T : Scheme.{u}} (t : T ⟶ S) : E.Point t →+ F.Point t :=
  letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk t ⟶ F.asOver) := Hom.commGroup
  AddMonoidHom.mk'
    (fun x => (F.pointEquivOverHom t).symm
      (IsMonHom.monoidHom φ (Over.mk t) ((E.pointEquivOverHom t) x)))
    (by
      intro x y
      apply (F.pointEquivOverHom t).injective
      rw [Equiv.apply_symm_apply, E.pointEquivOverHom_add t, map_mul,
        F.pointEquivOverHom_add t, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- [T-YR-2e helper] Additive pushforward of `t`-points along an `Ell/ℚ`-morphism:
through the `IsMonHom` K4-canonicity iso onto the base-changed curve
(`curveIsoPullbackOverIso`), then the additive base-change dictionary
(`Point.baseChangeEquiv`). -/
noncomputable def EllHom.mapPoint {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) :
    A.curve.Point t →+ B.curve.Point (t ≫ g.baseHom) :=
  haveI : IsMonHom (EllHom.curveIsoPullbackOverIso (CommRingCat.of ℚ) g).hom :=
    EllHom.isMonHom_curveIsoPullbackOverIso_hom (CommRingCat.of ℚ) g
  (EllipticCurve.Point.baseChangeEquiv B.curve g.baseHom t).toAddMonoidHom.comp
    (EllipticCurve.pointMapOfMonHom
      (EllHom.curveIsoPullbackOverIso (CommRingCat.of ℚ) g).hom t)

theorem EllHom.mapPoint_coe {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) (x : A.curve.Point t) :
    (EllHom.mapPoint g t x).1 = x.1 ≫ g.top := by
  have hleft : (EllHom.curveIsoPullbackOverIso (CommRingCat.of ℚ) g).hom.left ≫
      pullback.fst B.curve.π g.baseHom = g.top := g.isPullback.isoPullback_hom_fst
  show (x.1 ≫ (EllHom.curveIsoPullbackOverIso (CommRingCat.of ℚ) g).hom.left) ≫
      pullback.fst B.curve.π g.baseHom = x.1 ≫ g.top
  exact (Category.assoc _ _ _).trans (congrArg (x.1 ≫ ·) hleft)

/-- [T-YR-2e helper] The pushforward of a raw `N`-killed point is raw `N`-killed. -/
theorem EllHom.mapPoint_torsion {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} {t : T ⟶ A.base} (x : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    (EllHom.mapPoint g t x).1 ≫ B.curve.mulByHom N =
      (t ≫ g.baseHom) ≫ B.curve.zero := by
  rw [EllHom.mapPoint_coe, Category.assoc, ← ModularCurves.EllHom.mulByHom_top,
    ← Category.assoc, hx, Category.assoc, g.zero_w, ← Category.assoc]

/-- [T-YR-2e helper] `pointToTorsion` is natural in the curve: pushing the point
forward and lifting agrees with lifting and applying `torsionMapOfEllHom`. -/
theorem pointToTorsion_mapPoint {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} {t : T ⟶ A.base} (x : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    A.curve.pointToTorsion x hx ≫ torsionMapOfEllHom g N =
      B.curve.pointToTorsion (EllHom.mapPoint g t x)
        (EllHom.mapPoint_torsion g x hx) := by
  apply pullback.hom_ext
  · show (A.curve.pointToTorsion x hx ≫ torsionMapOfEllHom g N) ≫
        B.curve.torsionι N =
      B.curve.pointToTorsion (EllHom.mapPoint g t x)
          (EllHom.mapPoint_torsion g x hx) ≫ B.curve.torsionι N
    rw [Category.assoc, torsionMapOfEllHom_ι g N, ← Category.assoc,
      A.curve.pointToTorsion_torsionι, B.curve.pointToTorsion_torsionι,
      EllHom.mapPoint_coe]
  · show (A.curve.pointToTorsion x hx ≫ torsionMapOfEllHom g N) ≫
        B.curve.torsionπ N =
      B.curve.pointToTorsion (EllHom.mapPoint g t x)
          (EllHom.mapPoint_torsion g x hx) ≫ B.curve.torsionπ N
    rw [Category.assoc, torsionMapOfEllHom_π g N, ← Category.assoc,
      A.curve.pointToTorsion_torsionπ, B.curve.pointToTorsion_torsionπ]

/-- **[T-YR-2e-W, DS4-register]** Naturality of the Weil-pairing evaluation along an
`Ell/ℚ`-morphism: `e_N` of the pushed-forward points agrees with `e_N` upstairs (the
cartesian square identifies `A[N]` with the base change of `B[N]`, and `e_N` is
base-change compatible, KM 2.8.4.2). BLOCKED on DS4: `weilPairing` is
register-`sorry`-defined (WeilPairing/Basic.lean DS4) with no naturality spec, and the
two sides consume the two curves' *independent* registered pairings; discharged by
stream-C together with DS4's closure. -/
theorem weilPairingEval_mapPoint {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) (x y : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero)
    (hy : y.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    (B.curve.weilPairingEval (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
        (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy)).1 =
      (A.curve.weilPairingEval x y hx hy).1 := by sorry

/-- [T-YR-2e] The pulled-back ρ-torsion trivialization square: the cartesian torsion
square of `g` (T-YR-2c) pasted with `α`'s trivialization square is cartesian over
`A.structMap`. -/
theorem pullTorsionPB (D : GaloisRepData N) {A B : EllObj (CommRingCat.of ℚ)}
    (g : A ⟶ B) (α : RhoLevelStructure D B.structMap B.curve) :
    IsPullback
      (torsionMapOfEllHom g N ≫
        (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap))
      (A.curve.torsionπ N) (vRhoπ D) A.structMap := by
  have hB : IsPullback (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap)
      (B.curve.torsionπ N) (vRhoπ D) B.structMap := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ α.torsionIso rfl α.over_T
    rw [Category.assoc, pullback.condition, ← Category.assoc, α.over_T]
  have hpaste := (isPullback_torsionMapOfEllHom g N).paste_horiz hB
  rw [g.base_w] at hpaste
  exact hpaste

/-- [T-YR-2e] The pulled ρ-torsion trivialization. -/
noncomputable def pullTorsionIso (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (α : RhoLevelStructure D B.structMap B.curve) :
    A.curve.torsion N ≅ pullback (vRhoπ D) A.structMap :=
  (pullTorsionPB D g α).isoPullback

theorem pullTorsionIso_over (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (α : RhoLevelStructure D B.structMap B.curve) :
    (pullTorsionIso D g α).hom ≫ pullback.snd (vRhoπ D) A.structMap =
      A.curve.torsionπ N :=
  (pullTorsionPB D g α).isoPullback_hom_snd

theorem pullTorsionIso_fst (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (α : RhoLevelStructure D B.structMap B.curve) :
    (pullTorsionIso D g α).hom ≫ pullback.fst (vRhoπ D) A.structMap =
      torsionMapOfEllHom g N ≫
        (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap) :=
  (pullTorsionPB D g α).isoPullback_hom_fst

/-- [T-YR-2e] Coordinates read through the pulled trivialization are the coordinates
of the pushed-forward point read through `α`. -/
theorem coord_pull (D : GaloisRepData N) {A B : EllObj (CommRingCat.of ℚ)}
    (g : A ⟶ B) (α : RhoLevelStructure D B.structMap B.curve)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ A.base)
    (ht : t ≫ A.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    coord D A.structMap (pullTorsionIso D g α) (pullTorsionIso_over D g α) t ht x hx =
      coord D B.structMap α.torsionIso α.over_T (t ≫ g.baseHom)
        (by rw [Category.assoc, g.base_w, ht]) (EllHom.mapPoint g t x)
        (EllHom.mapPoint_torsion g x hx) := by
  refine congrArg (vRhoPointsEquiv D) (Subtype.ext ?_)
  show A.curve.pointToTorsion x hx ≫ (pullTorsionIso D g α).hom ≫
      pullback.fst (vRhoπ D) A.structMap =
    B.curve.pointToTorsion (EllHom.mapPoint g t x)
        (EllHom.mapPoint_torsion g x hx) ≫ α.torsionIso.hom ≫
      pullback.fst (vRhoπ D) B.structMap
  calc A.curve.pointToTorsion x hx ≫ (pullTorsionIso D g α).hom ≫
      pullback.fst (vRhoπ D) A.structMap
      = A.curve.pointToTorsion x hx ≫ torsionMapOfEllHom g N ≫
          (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap) :=
        congrArg (A.curve.pointToTorsion x hx ≫ ·) (pullTorsionIso_fst D g α)
    _ = (A.curve.pointToTorsion x hx ≫ torsionMapOfEllHom g N) ≫
          (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap) :=
        (Category.assoc _ _ _).symm
    _ = B.curve.pointToTorsion (EllHom.mapPoint g t x)
          (EllHom.mapPoint_torsion g x hx) ≫
          (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap) :=
        congrArg (· ≫ (α.torsionIso.hom ≫ pullback.fst (vRhoπ D) B.structMap))
          (pointToTorsion_mapPoint g x hx)

/-- [T-YR-2e helper] `coord` is congruent in the point (the raw-kill proof transports;
proofs are irrelevant). -/
theorem coord_congr (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    {x y : E.Point t} (h : x = y)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) :
    coord D sT torsionIso hOver t ht x hx =
      coord D sT torsionIso hOver t ht y (h ▸ hx) := by
  subst h; rfl

/-- [T-YR-2, SKELETON] Pull a ρ-level structure back along an `Ell/ℚ`-morphism. -/
noncomputable def RhoLevelStructure.pull (D : GaloisRepData N)
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (α : RhoLevelStructure D B.structMap B.curve) :
    RhoLevelStructure D A.structMap A.curve where
  torsionIso := pullTorsionIso D g α
  over_T := pullTorsionIso_over D g α
  coords_additive := by
    intro t ht x y hx hy hxy
    rw [coord_pull D g α t ht (x + y) hxy, coord_pull D g α t ht x hx,
      coord_pull D g α t ht y hy,
      coord_congr D B.structMap α.torsionIso α.over_T (t ≫ g.baseHom) _
        (map_add (EllHom.mapPoint g t) x y)
        (EllHom.mapPoint_torsion g (x + y) hxy)]
    exact α.coords_additive _ _ _ _ _ _ _
  pairing_compat := by
    intro t ht x y hx hy
    have hB := α.pairing_compat (t ≫ g.baseHom)
      (by rw [Category.assoc, g.base_w, ht])
      (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
      (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy)
    show (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
        (A.curve.weilPairingEval x y hx hy).1 = _
    rw [← weilPairingEval_mapPoint g t x y hx hy,
      coord_pull D g α t ht x hx, coord_pull D g α t ht y hy]
    exact hB

/-- [T-YR-2f helper] A ρ-level structure is determined by its torsion trivialization
(the other fields are `Prop`s). -/
theorem RhoLevelStructure.ext_torsionIso {D : GaloisRepData N} {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of ℚ)} {E : EllipticCurve T}
    {α β : RhoLevelStructure D sT E} (h : α.torsionIso = β.torsionIso) : α = β := by
  cases α; cases β; cases h; rfl

/-- [T-YR-2f helper] `torsionMapOfEllHom` respects identities. -/
theorem torsionMapOfEllHom_id {A : EllObj (CommRingCat.of ℚ)} (N : ℕ) [NeZero N] :
    torsionMapOfEllHom (𝟙 A) N = 𝟙 (A.curve.torsion N) := by
  apply pullback.hom_ext
  · show torsionMapOfEllHom (𝟙 A) N ≫ A.curve.torsionι N =
      𝟙 (A.curve.torsion N) ≫ A.curve.torsionι N
    rw [torsionMapOfEllHom_ι, Category.id_comp]
    exact Category.comp_id _
  · show torsionMapOfEllHom (𝟙 A) N ≫ A.curve.torsionπ N =
      𝟙 (A.curve.torsion N) ≫ A.curve.torsionπ N
    rw [torsionMapOfEllHom_π, Category.id_comp]
    exact Category.comp_id _

/-- [T-YR-2f helper] `torsionMapOfEllHom` respects composition. -/
theorem torsionMapOfEllHom_comp {A B C : EllObj (CommRingCat.of ℚ)} (g₁ : A ⟶ B)
    (g₂ : B ⟶ C) (N : ℕ) [NeZero N] :
    torsionMapOfEllHom (g₁ ≫ g₂) N =
      torsionMapOfEllHom g₁ N ≫ torsionMapOfEllHom g₂ N := by
  apply pullback.hom_ext
  · show torsionMapOfEllHom (g₁ ≫ g₂) N ≫ C.curve.torsionι N =
      (torsionMapOfEllHom g₁ N ≫ torsionMapOfEllHom g₂ N) ≫ C.curve.torsionι N
    rw [torsionMapOfEllHom_ι, Category.assoc, torsionMapOfEllHom_ι, ← Category.assoc,
      torsionMapOfEllHom_ι, Category.assoc]
    rfl
  · show torsionMapOfEllHom (g₁ ≫ g₂) N ≫ C.curve.torsionπ N =
      (torsionMapOfEllHom g₁ N ≫ torsionMapOfEllHom g₂ N) ≫ C.curve.torsionπ N
    rw [torsionMapOfEllHom_π, Category.assoc, torsionMapOfEllHom_π, ← Category.assoc,
      torsionMapOfEllHom_π, Category.assoc]
    rfl

/-- [T-YR-2f] Pulling back along the identity is the identity. -/
theorem RhoLevelStructure.pull_id (D : GaloisRepData N)
    {A : EllObj (CommRingCat.of ℚ)} (α : RhoLevelStructure D A.structMap A.curve) :
    RhoLevelStructure.pull D (𝟙 A) α = α := by
  refine RhoLevelStructure.ext_torsionIso (Iso.ext (pullback.hom_ext ?_ ?_))
  · rw [show (RhoLevelStructure.pull D (𝟙 A) α).torsionIso =
        pullTorsionIso D (𝟙 A) α from rfl,
      pullTorsionIso_fst, torsionMapOfEllHom_id, Category.id_comp]
  · rw [show (RhoLevelStructure.pull D (𝟙 A) α).torsionIso =
        pullTorsionIso D (𝟙 A) α from rfl,
      pullTorsionIso_over, α.over_T]

/-- [T-YR-2f] Pulling back along a composite is the composite of the pullbacks. -/
theorem RhoLevelStructure.pull_comp (D : GaloisRepData N)
    {A B C : EllObj (CommRingCat.of ℚ)} (g₁ : A ⟶ B) (g₂ : B ⟶ C)
    (α : RhoLevelStructure D C.structMap C.curve) :
    RhoLevelStructure.pull D (g₁ ≫ g₂) α =
      RhoLevelStructure.pull D g₁ (RhoLevelStructure.pull D g₂ α) := by
  refine RhoLevelStructure.ext_torsionIso (Iso.ext (pullback.hom_ext ?_ ?_))
  · rw [show (RhoLevelStructure.pull D (g₁ ≫ g₂) α).torsionIso =
        pullTorsionIso D (g₁ ≫ g₂) α from rfl,
      show (RhoLevelStructure.pull D g₁ (RhoLevelStructure.pull D g₂ α)).torsionIso =
        pullTorsionIso D g₁ (RhoLevelStructure.pull D g₂ α) from rfl,
      pullTorsionIso_fst, pullTorsionIso_fst, torsionMapOfEllHom_comp,
      show (RhoLevelStructure.pull D g₂ α).torsionIso = pullTorsionIso D g₂ α from rfl,
      pullTorsionIso_fst, Category.assoc]
  · rw [show (RhoLevelStructure.pull D (g₁ ≫ g₂) α).torsionIso =
        pullTorsionIso D (g₁ ≫ g₂) α from rfl,
      show (RhoLevelStructure.pull D g₁ (RhoLevelStructure.pull D g₂ α)).torsionIso =
        pullTorsionIso D g₁ (RhoLevelStructure.pull D g₂ α) from rfl,
      pullTorsionIso_over, pullTorsionIso_over]

/-- **[T-YR-2] The ρ-level moduli problem** (Buzzard p. 33 verbatim: "the functor on
ℚ-schemes S parametrising elliptic curves E/S such that E[N] ≅ ρ̄_N as
representations-with-pairing"), functorialized over `Ell/ℚ` (mirror of
`gammaFullNaiveProblem`'s functorialization). -/
noncomputable def rhoProblem (D : GaloisRepData N) :
    ModularCurves.ModuliProblem (CommRingCat.of ℚ) where
  obj X := RhoLevelStructure D X.unop.structMap X.unop.curve
  map f := ↾fun α => RhoLevelStructure.pull D f.unop α
  map_id := by
    intro X
    ext α
    exact RhoLevelStructure.pull_id D α
  map_comp := by
    intro X Y Z f g
    ext α
    exact RhoLevelStructure.pull_comp D g.unop f.unop α

section RhoRigidity

open MonoidalCategory

-- `open MonObj` is avoided (its scoped `γ`-notation, brought in by the engine's
-- `Mod.lean` import, shadows group-element binders); reproduce the unit locally,
-- exactly as `GammaHMaster` does.
local notation "η[" M "]" => CategoryTheory.MonObj.one (X := M)

/-- **[T-YR-4, k̄-core] (classical ρ-rigidity)** — no nontrivial base-identical
self-iso fixes a ρ-level structure over a field mapping to `Spec ℚ` (`N ≥ 3`): the fixed
trivialization forces `torsionMapOfEllHom e = 𝟙` (iso-cancel on the pasted rectangle),
hence every geometric `N`-torsion point is fixed, and the KVC keystone
(`pointedAuto_eq_id_of_fixes_torsion_kvc`, [KVC-drop-in D]) kills. -/
theorem rho_fix_absurd (D : GaloisRepData N) (hN : 3 ≤ (N : ℤ))
    (k : Type) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℚ))
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj (CommRingCat.of ℚ)) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj (CommRingCat.of ℚ)))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (aT : (rhoProblem D).obj (Opposite.op
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj (CommRingCat.of ℚ))))
    (hfix : (rhoProblem D).map e.hom.op aT = aT) : False := by
  classical
  -- 1. the fixed trivialization forces the torsion map to be the identity
  have htiso : pullTorsionIso D e.hom aT = aT.torsionIso :=
    congrArg RhoLevelStructure.torsionIso hfix
  have hhom : (pullTorsionIso D e.hom aT).hom = aT.torsionIso.hom :=
    congrArg Iso.hom htiso
  have h1 := pullTorsionIso_fst D e.hom aT
  rw [hhom] at h1
  have hτcomp : torsionMapOfEllHom e.hom N ≫ aT.torsionIso.hom =
      aT.torsionIso.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      exact h1.symm
    · rw [Category.assoc, aT.over_T, torsionMapOfEllHom_π, he, Category.comp_id]
  have hτ : torsionMapOfEllHom e.hom N = 𝟙 (E.torsion N) :=
    (cancel_mono aT.torsionIso.hom).mp (by
      rw [Category.id_comp]; exact hτcomp)
  -- 2. the induced pointed `Over`-automorphism
  have hcπ : e.hom.top ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  have hzc : E.zero ≫ e.hom.top = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ (Over.homMk e.hom.top hcπ : E.asOver ⟶ E.asOver) =
      η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ e.hom.top = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ e.hom.top
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ e.hom.top :=
      Category.assoc _ _ _
    have s2 : (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ e.hom.top
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero :=
      congrArg (fun m => (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ m) hzc
    exact s1.trans s2
  haveI hIsoεO : IsIso (Over.homMk e.hom.top hcπ : E.asOver ⟶ E.asOver) := by
    have hcπ' : e.inv.top ≫ E.π = E.π := by
      have h := e.inv.isPullback.w
      rw [EllObj.isoInv_baseHom e he, Category.comp_id] at h
      exact h
    refine ⟨Over.homMk e.inv.top hcπ', ?_, ?_⟩
    · exact Over.OverMorphism.ext (congrArg EllHom.top e.hom_inv_id)
    · exact Over.OverMorphism.ext (congrArg EllHom.top e.inv_hom_id)
  -- 3. numeric side conditions
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  have hNnat : 3 ≤ N := by exact_mod_cast hN
  have hNk : ((N : ℕ) : k) ≠ 0 := by
    intro h0
    have hφ : (Spec.preimage sm).hom ((N : ℚ)) = ((N : ℕ) : k) := map_natCast _ N
    have hinj : Function.Injective (Spec.preimage sm).hom := RingHom.injective _
    have hQ : ((N : ℕ) : ℚ) = 0 := hinj (by rw [hφ, h0, map_zero])
    exact absurd hQ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  -- 4. every geometric `N`-torsion point is fixed
  have hfixAll : ∀ x : E.Point (𝟙 (Spec (CommRingCat.of k))), (N : ℤ) • x = 0 →
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x ≫
        (Over.homMk e.hom.top hcπ : E.asOver ⟶ E.asOver) =
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x := by
    intro x hx
    have hval := congrArg Subtype.val hx
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val] at hval
    have hxc : x.1 ≫ e.hom.top = x.1 := by
      calc x.1 ≫ e.hom.top
          = (E.pointToTorsion x hval ≫ E.torsionι N) ≫ e.hom.top := by
            rw [E.pointToTorsion_torsionι]
        _ = E.pointToTorsion x hval ≫ torsionMapOfEllHom e.hom N ≫
              E.torsionι N :=
            (Category.assoc _ _ _).trans (congrArg
              (E.pointToTorsion x hval ≫ ·) (torsionMapOfEllHom_ι e.hom N).symm)
        _ = E.pointToTorsion x hval ≫ E.torsionι N := by
            rw [hτ, Category.id_comp]
        _ = x.1 := E.pointToTorsion_torsionι x hval
    refine Over.OverMorphism.ext ?_
    show x.1 ≫ e.hom.top = x.1
    exact hxc
  -- 5. the KVC keystone closes
  have hεid : (Over.homMk e.hom.top hcπ : E.asOver ⟶ E.asOver) = 𝟙 E.asOver :=
    EllipticCurve.pointedAuto_eq_id_of_fixes_torsion_kvc E
      (Over.homMk e.hom.top hcπ) hIsoεO hη N hNnat hNk hfixAll
  have hcid : e.hom.top = 𝟙 E.E := congrArg CommaMorphism.left hεid
  exact hne (Iso.ext (EllHom.ext he hcid))

/-- **[T-YR-4] The ρ-level problem is noetherian-locally rigid** (`N ≥ 3`): the PROVEN
detection (`exists_isoFibre_ne_refl`) finds a geometric fibre where a base-identical
iso stays nontrivial; the fixed ρ-structure transports along the fibre square; the
`ρ`-k̄-core (`rho_fix_absurd`) kills. -/
theorem rho_rigidNoeth (D : GaloisRepData N) (hN : 3 ≤ (N : ℤ)) :
    (rhoProblem D).RigidNoeth := by
  intro X hX e he hne a hfix
  haveI := hX
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  obtain ⟨k, _, _, t, hfib⟩ := EllObj.exists_isoFibre_ne_refl N hN
    (YFull.nIsInvertible_over_spec (CommRingCat.of ℚ) X.structMap hinvQ) e he hne
  set eT := EllObj.isoFibre e he t with heT
  have hcomp : eT.hom ≫ X.pullbackAlongπ t = X.pullbackAlongπ t ≫ e.hom :=
    EllHom.fibre_pullbackAlongπ e.hom he t
  set aT := (rhoProblem D).map (X.pullbackAlongπ t).op a with haT
  have hfixT : (rhoProblem D).map eT.hom.op aT = aT := by
    calc (rhoProblem D).map eT.hom.op aT
        = (rhoProblem D).map ((X.pullbackAlongπ t).op ≫ eT.hom.op) a := by
          rw [haT, ← Functor.map_comp_apply]
      _ = (rhoProblem D).map (e.hom.op ≫ (X.pullbackAlongπ t).op) a := by
          rw [← op_comp, ← op_comp, hcomp]
      _ = (rhoProblem D).map (X.pullbackAlongπ t).op
            ((rhoProblem D).map e.hom.op a) := by
          rw [Functor.map_comp_apply]
      _ = aT := by rw [hfix, haT]
  exact rho_fix_absurd D hN k (t ≫ X.structMap) (X.curve.baseChange t)
    eT rfl hfib aT hfixT

end RhoRigidity

end RhoProblem

section FramedProblemFunctor

variable {N : ℕ} [NeZero N]

/-- [T-YR-3b helper] `pullSection` preserves global `N`-killing (additivity). -/
theorem pullSection_kill {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {P : B.curve.Section} (hP : (N : ℤ) • P = 0) :
    (N : ℤ) • EllHom.pullSection (CommRingCat.of ℚ) g P = 0 := by
  calc (N : ℤ) • EllHom.pullSection (CommRingCat.of ℚ) g P
      = AddMonoidHom.mk' (EllHom.pullSection (CommRingCat.of ℚ) g)
          (EllHom.pullSection_add (CommRingCat.of ℚ) g) ((N : ℤ) • P) :=
        (map_zsmul (AddMonoidHom.mk' _
          (EllHom.pullSection_add (CommRingCat.of ℚ) g)) (N : ℤ) P).symm
    _ = 0 := by rw [hP, map_zero]

/-- [T-YR-3b helper] Pushing the pull of a pulled-back section forward recovers the
pull at the composed point (valuewise: `lift_fst`). -/
theorem mapPoint_pull_pullSection {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T' : Scheme.{0}} (t : T' ⟶ A.base) (P : B.curve.Section) :
    EllHom.mapPoint g t (EllipticCurve.Point.pull A.curve t
        (EllHom.pullSection (CommRingCat.of ℚ) g P)) =
      EllipticCurve.Point.pull B.curve (t ≫ g.baseHom) P := by
  refine Subtype.ext ?_
  rw [EllHom.mapPoint_coe]
  show (t ≫ (EllHom.pullSection (CommRingCat.of ℚ) g P).1) ≫ g.top =
    (t ≫ g.baseHom) ≫ P.1
  rw [Category.assoc,
    show (EllHom.pullSection (CommRingCat.of ℚ) g P).1 ≫ g.top =
      g.baseHom ≫ P.1 from g.isPullback.lift_fst _ _ _,
    ← Category.assoc]

/-- [T-YR-3b helper] `weilPairingEval` is congruent in the points (proof-irrelevant). -/
theorem weilPairingEval_congr {T T' : Scheme.{0}} {E : EllipticCurve T}
    {t : T' ⟶ T} {x x' y y' : E.Point t} (hx' : x = x') (hy' : y = y')
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    (E.weilPairingEval x y hx hy).1 =
      (E.weilPairingEval x' y' (hx' ▸ hx) (hy' ▸ hy)).1 := by
  subst hx'; subst hy'; rfl

/-- [T-YR-3b helper] The frame points-reading is congruent in the point. -/
theorem wFramesPointsEquiv_congr (D : GaloisRepData N)
    {a b : Spec (.of (AlgebraicClosure ℚ)) ⟶ wFrames D} (hab : a = b)
    (pa : a ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    wFramesPointsEquiv D ⟨a, pa⟩ = wFramesPointsEquiv D ⟨b, hab ▸ pa⟩ := by
  subst hab; rfl

/-- **[T-YR-3b]** `FramedSymp` pulls back along `Ell/ℚ`-morphisms (through the
registered Weil-naturality `weilPairingEval_mapPoint`, T-YR-2e-W). -/
theorem framedSymp_pull (D : GaloisRepData N) {A B : EllObj (CommRingCat.of ℚ)}
    (g : A ⟶ B) {P Q : B.curve.Section}
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    {h : B.base ⟶ wFrames D} {hover : h ≫ wFramesπ D = B.structMap}
    (hsymp : FramedSymp D B.structMap B.curve P Q hP hQ h hover) :
    FramedSymp D A.structMap A.curve
      (EllHom.pullSection (CommRingCat.of ℚ) g P)
      (EllHom.pullSection (CommRingCat.of ℚ) g Q)
      (pullSection_kill g hP) (pullSection_kill g hQ)
      (g.baseHom ≫ h) (by rw [Category.assoc, hover, g.base_w]) := by
  intro t ht
  have ht' : (t ≫ g.baseHom) ≫ B.structMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, g.base_w, ht]
  have hs := hsymp (t ≫ g.baseHom) ht'
  have hW := weilPairingEval_mapPoint g t
    (EllipticCurve.Point.pull A.curve t (EllHom.pullSection (CommRingCat.of ℚ) g P))
    (EllipticCurve.Point.pull A.curve t (EllHom.pullSection (CommRingCat.of ℚ) g Q))
    (sectionPull_raw_kill t (pullSection_kill g hP))
    (sectionPull_raw_kill t (pullSection_kill g hQ))
  refine Eq.trans ?_ (Eq.trans hs ?_)
  · exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
      (hW.symm.trans (weilPairingEval_congr
        (mapPoint_pull_pullSection g t P) (mapPoint_pull_pullSection g t Q) _ _))
  · exact congrArg (fun A' => ((D.p (Multiplicative.ofAdd
      (((Matrix.GeneralLinearGroup.det A' : (ZMod N)ˣ) : ZMod N))) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (wFramesPointsEquiv_congr D (Category.assoc t g.baseHom h) _)

/-- [T-YR-3b helper] Integer combinations of `N`-killed sections are `N`-killed. -/
theorem comb_kill {T : Scheme.{0}} {E : EllipticCurve T} {P Q : E.Section}
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) (a b : ℤ) :
    (N : ℤ) • (a • P + b • Q) = 0 := by
  rw [smul_add, smul_comm (N : ℤ) a, smul_comm (N : ℤ) b, hP, hQ,
    smul_zero, smul_zero, add_zero]

/-- [T-YR-3b helper] `p` of a product exponent is the `val`-power (the
`Multiplicative`/`ZMod` power dictionary). -/
theorem p_ofAdd_mul_val (D : GaloisRepData N) (z w : ZMod N) :
    (((D.p (Multiplicative.ofAdd (z * w))) : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) =
    (((D.p (Multiplicative.ofAdd z)) : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) ^ w.val := by
  have h1 : z * w = (w.val : ZMod N) * z := by
    rw [ZMod.natCast_val, ZMod.cast_id, mul_comm]
  rw [h1, ← nsmul_eq_mul, ofAdd_nsmul, map_pow]
  norm_cast

/-- **[T-YR-3b]** `FramedSymp` is invariant under the diagonal `GL₂`-twist: acting on
the full-level pair by the matrix columns and on the frame by right translation
preserves the pairing-match. The pairing side is the registered symplectic formula
(`weilPairingEval_symplectic`, T-C2c); the frame side is `wFramesPointsEquiv_rightMul`;
the exponents match by `ZMod.val_intCast` + `Matrix.det_fin_two`. -/
theorem framedSymp_glSmul (D : GaloisRepData N) {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of ℚ)} {E : EllipticCurve T} {P Q : E.Section}
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    {h : T ⟶ wFrames D} {hover : h ≫ wFramesπ D = sT}
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hsymp : FramedSymp D sT E P Q hP hQ h hover) :
    FramedSymp D sT E
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • P +
        (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • Q)
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • P +
        (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • Q)
      (comb_kill hP hQ _ _) (comb_kill hP hQ _ _)
      (h ≫ wFramesRightMul D γ)
      (by rw [Category.assoc, wFramesRightMul_π, hover]) := by
  intro t ht
  have hs := hsymp t ht
  -- notation
  set m : Matrix (Fin 2) (Fin 2) (ZMod N) := (γ : Matrix (Fin 2) (Fin 2) (ZMod N))
    with hm
  -- 1. pull-normalization of the twisted basis
  have hPP : EllipticCurve.Point.pull E t
      ((((m 0 0).val : ℤ) • P + ((m 1 0).val : ℤ) • Q)) =
      ((m 0 0).val : ℤ) • EllipticCurve.Point.pull E t P +
        ((m 1 0).val : ℤ) • EllipticCurve.Point.pull E t Q := by
    rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
      EllipticCurve.Point.pull_zsmul]
  have hQQ : EllipticCurve.Point.pull E t
      ((((m 0 1).val : ℤ) • P + ((m 1 1).val : ℤ) • Q)) =
      ((m 0 1).val : ℤ) • EllipticCurve.Point.pull E t P +
        ((m 1 1).val : ℤ) • EllipticCurve.Point.pull E t Q := by
    rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
      EllipticCurve.Point.pull_zsmul]
  -- 2. kill-conditions for the pulled basis
  have hppk : (EllipticCurve.Point.pull E t P).1 ≫ E.mulByHom N = t ≫ E.zero :=
    sectionPull_raw_kill t hP
  have hpqk : (EllipticCurve.Point.pull E t Q).1 ≫ E.mulByHom N = t ≫ E.zero :=
    sectionPull_raw_kill t hQ
  have hcomb1 : (((m 0 0).val : ℤ) • EllipticCurve.Point.pull E t P +
      ((m 1 0).val : ℤ) • EllipticCurve.Point.pull E t Q).1 ≫ E.mulByHom N =
      t ≫ E.zero := by
    have := sectionPull_raw_kill (E := E) t (comb_kill hP hQ ((m 0 0).val : ℤ)
      ((m 1 0).val : ℤ))
    rwa [hPP] at this
  have hcomb2 : (((m 0 1).val : ℤ) • EllipticCurve.Point.pull E t P +
      ((m 1 1).val : ℤ) • EllipticCurve.Point.pull E t Q).1 ≫ E.mulByHom N =
      t ≫ E.zero := by
    have := sectionPull_raw_kill (E := E) t (comb_kill hP hQ ((m 0 1).val : ℤ)
      ((m 1 1).val : ℤ))
    rwa [hQQ] at this
  -- 3. the registered symplectic formula
  have hW := E.weilPairingEval_symplectic
    (EllipticCurve.Point.pull E t P) (EllipticCurve.Point.pull E t Q)
    (((m 0 0).val : ℤ)) (((m 1 0).val : ℤ)) (((m 0 1).val : ℤ)) (((m 1 1).val : ℤ))
    hppk hpqk hcomb1 hcomb2
  -- 4. LHS-chain: twisted eval = original eval to the determinant power
  have hLHS : (E.weilPairingEval
      (EllipticCurve.Point.pull E t
        ((((m 0 0).val : ℤ) • P + ((m 1 0).val : ℤ) • Q)))
      (EllipticCurve.Point.pull E t
        ((((m 0 1).val : ℤ) • P + ((m 1 1).val : ℤ) • Q)))
      (sectionPull_raw_kill t (comb_kill hP hQ _ _))
      (sectionPull_raw_kill t (comb_kill hP hQ _ _))).1 =
      (E.weilPairingEval (EllipticCurve.Point.pull E t P)
        (EllipticCurve.Point.pull E t Q) hppk hpqk).1 ^
        (((((m 0 0).val : ℤ) * ((m 1 1).val : ℤ) -
          ((m 1 0).val : ℤ) * ((m 0 1).val : ℤ)) % (N : ℤ)).toNat) :=
    (weilPairingEval_congr hPP hQQ _ _).trans hW
  -- 5. the frame side: right translation multiplies the frame
  have hframe : wFramesPointsEquiv D ⟨t ≫ (h ≫ wFramesRightMul D γ), by
      rw [Category.assoc,
        show (h ≫ wFramesRightMul D γ) ≫ wFramesπ D = sT from by
          rw [Category.assoc, wFramesRightMul_π, hover], ht]⟩ =
      wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ * γ := by
    refine Eq.trans (wFramesPointsEquiv_congr D
      ((Category.assoc t h (wFramesRightMul D γ)).symm) _) ?_
    exact wFramesPointsEquiv_rightMul D γ ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩
  -- 6. assembly: exponent identification + the power dictionary
  have hdet2 : ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      Matrix.det m := rfl
  have hcoedet : ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      ((((m 0 0).val : ℤ) * ((m 1 1).val : ℤ) -
        ((m 1 0).val : ℤ) * ((m 0 1).val : ℤ) : ℤ) : ZMod N) := by
    rw [hdet2, Matrix.det_fin_two]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  have hk : ((((m 0 0).val : ℤ) * ((m 1 1).val : ℤ) -
      ((m 1 0).val : ℤ) * ((m 0 1).val : ℤ)) % (N : ℤ)).toNat =
      ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N).val := by
    rw [hcoedet]
    exact ((congrArg Int.toNat (ZMod.val_intCast _)).symm.trans
      (Int.toNat_natCast _))
  rw [hLHS, map_pow, hs, hk, hframe, map_mul, Units.val_mul, p_ofAdd_mul_val]

/-- **[T-YR-3b]** The framed-symplectic moduli problem: naive full level-`N` pairs
equipped with a symplectically matched frame of `V_ρ` (the contracted-product
presentation of the ρ-level problem, before the free `GL₂`-quotient). -/
noncomputable def framedProblem (D : GaloisRepData N) :
    ModularCurves.ModuliProblem (CommRingCat.of ℚ) where
  obj X := { Lh : ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).obj X) ×
      { h : X.unop.base ⟶ wFrames D // h ≫ wFramesπ D = X.unop.structMap } //
    FramedSymp D X.unop.structMap X.unop.curve Lh.1.val.1 Lh.1.val.2
      Lh.1.property.1.1 Lh.1.property.1.2 Lh.2.val Lh.2.property }
  map f := ↾fun Lh => ⟨⟨⟨⟨EllHom.pullSection (CommRingCat.of ℚ) f.unop
        Lh.val.1.val.1,
      EllHom.pullSection (CommRingCat.of ℚ) f.unop Lh.val.1.val.2⟩,
      EllHom.isNaiveFullLevel_pullSection (CommRingCat.of ℚ) f.unop
        Lh.val.1.property⟩,
    ⟨f.unop.baseHom ≫ Lh.val.2.val, by
      rw [Category.assoc, Lh.val.2.property, f.unop.base_w]⟩⟩,
    framedSymp_pull D f.unop Lh.val.1.property.1.1 Lh.val.1.property.1.2
      Lh.property⟩
  map_id := by
    intro X
    ext Lh
    · exact Subtype.ext (Prod.ext
        (EllHom.pullSection_id (CommRingCat.of ℚ) Lh.val.1.val.1)
        (EllHom.pullSection_id (CommRingCat.of ℚ) Lh.val.1.val.2))
    · exact Category.id_comp _
  map_comp := by
    intro X Y Z f g
    ext Lh
    · exact Subtype.ext (Prod.ext
        (EllHom.pullSection_comp (CommRingCat.of ℚ) g.unop f.unop Lh.val.1.val.1)
        (EllHom.pullSection_comp (CommRingCat.of ℚ) g.unop f.unop Lh.val.1.val.2))
    · exact Category.assoc _ _ _

/-- **[T-YR-3b-v]** The *bare* framed problem: full-level pairs with a frame, WITHOUT
the symplectic condition — the ambient problem whose free `GL₂`-quotient the landed
[GHB7] machinery computes; the symplectic locus is carved per-`X` on the relative
data (route-fork of record, board v10.353). -/
noncomputable def bareFramedProblem (D : GaloisRepData N) :
    ModularCurves.ModuliProblem (CommRingCat.of ℚ) where
  obj X := ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).obj X) ×
    { h : X.unop.base ⟶ wFrames D // h ≫ wFramesπ D = X.unop.structMap }
  map f := ↾fun Lh => ⟨⟨⟨EllHom.pullSection (CommRingCat.of ℚ) f.unop Lh.1.val.1,
      EllHom.pullSection (CommRingCat.of ℚ) f.unop Lh.1.val.2⟩,
      EllHom.isNaiveFullLevel_pullSection (CommRingCat.of ℚ) f.unop
        Lh.1.property⟩,
    ⟨f.unop.baseHom ≫ Lh.2.val, by
      rw [Category.assoc, Lh.2.property, f.unop.base_w]⟩⟩
  map_id := by
    intro X
    ext Lh
    · exact Subtype.ext (Prod.ext
        (EllHom.pullSection_id (CommRingCat.of ℚ) Lh.1.val.1)
        (EllHom.pullSection_id (CommRingCat.of ℚ) Lh.1.val.2))
    · exact Category.id_comp _
  map_comp := by
    intro X Y Z f g
    ext Lh
    · exact Subtype.ext (Prod.ext
        (EllHom.pullSection_comp (CommRingCat.of ℚ) g.unop f.unop Lh.1.val.1)
        (EllHom.pullSection_comp (CommRingCat.of ℚ) g.unop f.unop Lh.1.val.2))
    · exact Category.assoc _ _ _

/-- **[T-YR-3b-iv]** The diagonal `GL₂`-translation of the framed problem:
`glSmul γ` on the full-level pair, right `γ`-translation on the frame; the symplectic
match is preserved by `framedSymp_glSmul`. Natural by `pullSection_glSmul` and
associativity. -/
noncomputable def framedSmulNat (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    framedProblem D ⟶ framedProblem D where
  app X := ↾fun Lh => ⟨⟨X.unop.curve.glSmul γ Lh.val.1,
    ⟨Lh.val.2.val ≫ wFramesRightMul D γ, by
      rw [Category.assoc, wFramesRightMul_π, Lh.val.2.property]⟩⟩,
    framedSymp_glSmul D Lh.val.1.property.1.1 Lh.val.1.property.1.2 γ Lh.property⟩
  naturality X Y f := by
    ext Lh
    exact Subtype.ext (Prod.ext
      (EllHom.pullSection_glSmul (CommRingCat.of ℚ) f.unop γ Lh.val.1)
      (Subtype.ext (Category.assoc _ _ _)))

/-- **[T-YR-3b-v]** The diagonal translation of the bare framed problem. -/
noncomputable def bareFramedSmulNat (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    bareFramedProblem D ⟶ bareFramedProblem D where
  app X := ↾fun Lh => ⟨X.unop.curve.glSmul γ Lh.1,
    ⟨Lh.2.val ≫ wFramesRightMul D γ, by
      rw [Category.assoc, wFramesRightMul_π, Lh.2.property]⟩⟩
  naturality X Y f := by
    ext Lh
    exact Prod.ext
      (EllHom.pullSection_glSmul (CommRingCat.of ℚ) f.unop γ Lh.1)
      (Subtype.ext (Category.assoc _ _ _))

/-- **[T-YR-3b-v]** The `GL₂(ℤ/N)`-action on the bare framed problem. -/
noncomputable def bareFramedAut (D : GaloisRepData N) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N) →* Aut (bareFramedProblem D) where
  toFun γ :=
    { hom := bareFramedSmulNat D γ⁻¹
      inv := bareFramedSmulNat D γ
      hom_inv_id := by
        ext X Lh
        exact Prod.ext
          (by
            show X.unop.curve.glSmul γ (X.unop.curve.glSmul γ⁻¹ Lh.1) = Lh.1
            rw [← EllipticCurve.glSmul_mul, inv_mul_cancel,
              EllipticCurve.glSmul_one])
          (Subtype.ext (by
            show (Lh.2.val ≫ wFramesRightMul D γ⁻¹) ≫ wFramesRightMul D γ =
              Lh.2.val
            rw [Category.assoc, ← wFramesRightMul_mul, inv_mul_cancel,
              wFramesRightMul_one, Category.comp_id]))
      inv_hom_id := by
        ext X Lh
        exact Prod.ext
          (by
            show X.unop.curve.glSmul γ⁻¹ (X.unop.curve.glSmul γ Lh.1) = Lh.1
            rw [← EllipticCurve.glSmul_mul, mul_inv_cancel,
              EllipticCurve.glSmul_one])
          (Subtype.ext (by
            show (Lh.2.val ≫ wFramesRightMul D γ) ≫ wFramesRightMul D γ⁻¹ =
              Lh.2.val
            rw [Category.assoc, ← wFramesRightMul_mul, mul_inv_cancel,
              wFramesRightMul_one, Category.comp_id])) }
  map_one' := by
    ext X Lh
    exact Prod.ext
      (by
        show X.unop.curve.glSmul
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ Lh.1 = Lh.1
        rw [inv_one, EllipticCurve.glSmul_one])
      (Subtype.ext (by
        show Lh.2.val ≫ wFramesRightMul D
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ = Lh.2.val
        rw [inv_one, wFramesRightMul_one, Category.comp_id]))
  map_mul' γ δ := by
    ext X Lh
    exact Prod.ext
      (by
        show X.unop.curve.glSmul (γ * δ)⁻¹ Lh.1 =
          X.unop.curve.glSmul γ⁻¹ (X.unop.curve.glSmul δ⁻¹ Lh.1)
        rw [mul_inv_rev, EllipticCurve.glSmul_mul])
      (Subtype.ext (by
        show Lh.2.val ≫ wFramesRightMul D (γ * δ)⁻¹ =
          (Lh.2.val ≫ wFramesRightMul D δ⁻¹) ≫ wFramesRightMul D γ⁻¹
        rw [mul_inv_rev, wFramesRightMul_mul, Category.assoc]))

/-- **[T-YR-3b-v]** The bare diagonal action is free over nonempty bases. -/
theorem bareFramedAut_freeAction (D : GaloisRepData N) :
    ModuliProblem.FreeAction (bareFramedAut D) := by
  intro X hne γ hγ a hfix
  apply hγ
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hL : X.curve.glSmul γ⁻¹ a.1 = a.1 :=
    congrArg (fun z => z.1) hfix
  have hg1 : (γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 :=
    glSmul_eq_one_of_eq_self N hinvQ X hne γ⁻¹ a.1 hL
  rwa [inv_eq_one] at hg1

/-- **[T-YR-3b-iv]** The `GL₂(ℤ/N)`-action on the framed problem (the `γ⁻¹`-hom
convention of `gammaHAut`: the smul laws are right-action laws, `Aut`-homomorphisms
are left actions). -/
noncomputable def framedAut (D : GaloisRepData N) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N) →* Aut (framedProblem D) where
  toFun γ :=
    { hom := framedSmulNat D γ⁻¹
      inv := framedSmulNat D γ
      hom_inv_id := by
        ext X Lh
        exact Subtype.ext (Prod.ext
          (by
            show X.unop.curve.glSmul γ (X.unop.curve.glSmul γ⁻¹ Lh.val.1) =
              Lh.val.1
            rw [← EllipticCurve.glSmul_mul, inv_mul_cancel,
              EllipticCurve.glSmul_one])
          (Subtype.ext (by
            show (Lh.val.2.val ≫ wFramesRightMul D γ⁻¹) ≫ wFramesRightMul D γ =
              Lh.val.2.val
            rw [Category.assoc, ← wFramesRightMul_mul, inv_mul_cancel,
              wFramesRightMul_one, Category.comp_id])))
      inv_hom_id := by
        ext X Lh
        exact Subtype.ext (Prod.ext
          (by
            show X.unop.curve.glSmul γ⁻¹ (X.unop.curve.glSmul γ Lh.val.1) =
              Lh.val.1
            rw [← EllipticCurve.glSmul_mul, mul_inv_cancel,
              EllipticCurve.glSmul_one])
          (Subtype.ext (by
            show (Lh.val.2.val ≫ wFramesRightMul D γ) ≫ wFramesRightMul D γ⁻¹ =
              Lh.val.2.val
            rw [Category.assoc, ← wFramesRightMul_mul, mul_inv_cancel,
              wFramesRightMul_one, Category.comp_id]))) }
  map_one' := by
    ext X Lh
    exact Subtype.ext (Prod.ext
      (by
        show X.unop.curve.glSmul
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ Lh.val.1 = Lh.val.1
        rw [inv_one, EllipticCurve.glSmul_one])
      (Subtype.ext (by
        show Lh.val.2.val ≫ wFramesRightMul D
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ = Lh.val.2.val
        rw [inv_one, wFramesRightMul_one, Category.comp_id])))
  map_mul' γ δ := by
    ext X Lh
    exact Subtype.ext (Prod.ext
      (by
        show X.unop.curve.glSmul (γ * δ)⁻¹ Lh.val.1 =
          X.unop.curve.glSmul γ⁻¹ (X.unop.curve.glSmul δ⁻¹ Lh.val.1)
        rw [mul_inv_rev, EllipticCurve.glSmul_mul])
      (Subtype.ext (by
        show Lh.val.2.val ≫ wFramesRightMul D (γ * δ)⁻¹ =
          (Lh.val.2.val ≫ wFramesRightMul D δ⁻¹) ≫ wFramesRightMul D γ⁻¹
        rw [mul_inv_rev, wFramesRightMul_mul, Category.assoc])))

/-- **[T-YR-3b-iv]** The diagonal action is free over nonempty bases: the full-level
component already is (`glSmul_eq_one_of_eq_self`; `N` is invertible in `ℚ`). -/
theorem framedAut_freeAction (D : GaloisRepData N) :
    ModuliProblem.FreeAction (framedAut D) := by
  intro X hne γ hγ a hfix
  apply hγ
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hL : X.curve.glSmul γ⁻¹ a.val.1 = a.val.1 :=
    congrArg (fun z => z.val.1) hfix
  have hg1 : (γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 :=
    glSmul_eq_one_of_eq_self N hinvQ X hne γ⁻¹ a.val.1 hL
  rwa [inv_eq_one] at hg1

/-- **[asm-2]** The universal-frame evaluation lies over `Spec ℚ`. -/
theorem frameEval_π (D : GaloisRepData N) :
    frameEval D ≫ vRhoπ D =
      pullback.fst (constVecSchemeπ N) (wFramesπ D) ≫ constVecSchemeπ N := by
  have hcomp : CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0)) ≫
      CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap ℚ (FiniteEtaleGalois.tensorObj
        (constVecAlgebra N) (wFramesAlgebra D) : Type 0)) := by
    ext r
    exact (frameEvalAlgHom D).hom.hom.commutes r
  show ((AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
      (wFramesAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (frameEvalAlgHom D).hom.hom.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0))) = _
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (Spec.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun f => (AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map f) hcomp) ?_
  have hfactor : CommRingCat.ofHom (algebraMap ℚ (FiniteEtaleGalois.tensorObj
      (constVecAlgebra N) (wFramesAlgebra D) : Type 0)) =
      CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)) ≫
      CommRingCat.ofHom (algebraMap (constVecAlgebra N : Type 0)
        (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0))) := by
    ext r
    exact (IsScalarTower.algebraMap_apply ℚ (constVecAlgebra N : Type 0)
      (TensorProduct ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)) r)
  refine Eq.trans (congrArg (fun f => (AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map f) hfactor) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (Spec.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (constVecAlgebra N : Type 0))))
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0))

/-- **[asm-2a]** The canonical `ℚ̄`-points description of the constant-vector scheme:
points over `ℚ̄` biject with `(ℤ/N)²` (mirror of `wFramesPointsEquiv` at the trivial
Galois set). -/
noncomputable def constVecPointsEquiv (N : ℕ) [NeZero N] :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of (constVecAlgebra N : Type 0)) //
      h ≫ constVecSchemeπ N =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ (Fin 2 → ZMod N) :=
  ((specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
      (AlgebraicClosure ℚ)).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)).trans
    (FiniteEtaleGalois.pointsEquivOfContAction ℚ (constVecContAction N))

/-- [asm-2a helper] The bridge is compatible with the left cofan-injection: the
correspondence of the first projection composed with the bridge-inverse is the
tensor inclusion (the `conePointUniqueUpToIso` compatibility, extracted by
re-deriving the defining limit terms). -/
theorem frameProdAlgebraIso_inv_left (D : GaloisRepData N) :
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdFst D)).unop ≫ (frameProdAlgebraIso D).inv.unop =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (constVecAlgebra N : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hcomp := Limits.IsLimit.conePointUniqueUpToIso_hom_comp
    ((Limits.IsLimit.postcomposeHomEquiv
        (Limits.pairComp (constVecContAction N) (frameContAction D)
          (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse) _).symm
      (Limits.isLimitOfPreserves _ (frameProdIsProduct D)))
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (constVecAlgebra N)
      (wFramesAlgebra D))
    ⟨Limits.WalkingPair.left⟩
  have hop : ((FiniteEtaleGalois.tensorBinaryCofan (constVecAlgebra N)
        (wFramesAlgebra D)).op).π.app ⟨Limits.WalkingPair.left⟩
      = (frameProdAlgebraIso D).inv
          ≫ (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
              (frameProdFst D) :=
    ((Iso.inv_hom_id_assoc (frameProdAlgebraIso D) _).symm.trans
      (congrArg ((frameProdAlgebraIso D).inv ≫ ·) hcomp)).trans
      (congrArg ((frameProdAlgebraIso D).inv ≫ ·) (Category.comp_id _))
  exact (congrArg Quiver.Hom.unop hop.symm).trans rfl

/-- **[asm-2a]** The tensor-splitting bridge is compatible with the right
cofan-injection: precomposing the bridge with the correspondence image of the
second product-projection is `includeRight`. -/
theorem frameProdAlgebraIso_inv_right (D : GaloisRepData N) :
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdSnd D)).unop ≫ (frameProdAlgebraIso D).inv.unop =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hcomp := Limits.IsLimit.conePointUniqueUpToIso_hom_comp
    ((Limits.IsLimit.postcomposeHomEquiv
        (Limits.pairComp (constVecContAction N) (frameContAction D)
          (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse) _).symm
      (Limits.isLimitOfPreserves _ (frameProdIsProduct D)))
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (constVecAlgebra N)
      (wFramesAlgebra D))
    ⟨Limits.WalkingPair.right⟩
  have hop : ((FiniteEtaleGalois.tensorBinaryCofan (constVecAlgebra N)
        (wFramesAlgebra D)).op).π.app ⟨Limits.WalkingPair.right⟩
      = (frameProdAlgebraIso D).inv
          ≫ (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
              (frameProdSnd D) :=
    ((Iso.inv_hom_id_assoc (frameProdAlgebraIso D) _).symm.trans
      (congrArg ((frameProdAlgebraIso D).inv ≫ ·) hcomp)).trans
      (congrArg ((frameProdAlgebraIso D).inv ≫ ·) (Category.comp_id _))
  exact (congrArg Quiver.Hom.unop hop.symm).trans rfl

/-- **[asm-2a]** The universal-frame evaluation on `ℚ̄`-points: the `V_ρ`-reading of
the evaluated point is the classified frame acting on the vector (scaffold; the
proof is the counit-naturality assembly through the tensor pair-split). -/
theorem frameEval_points (D : GaloisRepData N)
    (p : Spec (.of (AlgebraicClosure ℚ)) ⟶
      pullback (constVecSchemeπ N) (wFramesπ D))
    (hp : p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    vRhoPointsEquiv D ⟨p ≫ frameEval D, by
        rw [Category.assoc, frameEval_π]
        exact hp⟩ =
      (wFramesPointsEquiv D ⟨p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), by
        rw [Category.assoc, ← pullback.condition]
        exact hp⟩) •
      (constVecPointsEquiv N ⟨p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D),
        by rw [Category.assoc]; exact hp⟩) := by
  -- the tensor-level point and its algebra reading
  set p' := p ≫ (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
    (wFramesAlgebra D : Type 0)).hom with hp'
  -- L1-extraction: the evaluation-composite reads as precomposition with the
  -- evaluation comultiplication
  have hL1 : Spec.preimage (p ≫ frameEval D) =
      CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom ≫
        Spec.preimage p' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hp', frameEval]
    exact (Category.assoc _ _ _).symm
  -- the pair-split: the tensor-point's components are the pullback projections
  have hfst : Spec.preimage (p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D)) =
      CommRingCat.ofHom (algebraMap (constVecAlgebra N : Type 0)
        (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0))) ≫ Spec.preimage p' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hp', Category.assoc]
    exact congrArg (p ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).symm
  have hsnd : Spec.preimage (p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D)) =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom ≫ Spec.preimage p' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hp', Category.assoc]
    exact congrArg (p ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_hom_snd ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).symm
  -- the tensor-point lies over ℚ
  have hover' : p' ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ
      (TensorProduct ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    have hfac : CommRingCat.ofHom (algebraMap ℚ
        (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0))) =
        CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)) ≫
        CommRingCat.ofHom (algebraMap (constVecAlgebra N : Type 0)
          (TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0))) := by
      ext r
      exact (IsScalarTower.algebraMap_apply ℚ (constVecAlgebra N : Type 0)
        (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)) r)
    rw [hfac, Spec.map_comp, ← Category.assoc]
    rw [show p' ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (constVecAlgebra N : Type 0)
          (TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)))) =
      p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) from by
      rw [hp', Category.assoc]
      exact congrArg (p ≫ ·)
        (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ
          (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0))]
    exact (Category.assoc _ _ _).trans hp
  -- the evaluated point lies over ℚ (hoisted for the subtype below)
  have hqv : (p ≫ frameEval D) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (vRhoAlgebra D : Type 0))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [show Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (vRhoAlgebra D : Type 0))) = vRhoπ D from rfl,
      Category.assoc, frameEval_π]
    exact hp
  -- the vRho-side reading of the evaluated point is the evaluation-precomposition
  have hA : specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)
      ⟨p ≫ frameEval D, hqv⟩ =
      (specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ)
        ⟨p', hover'⟩).comp (frameEvalAlgHom D).hom.hom := by
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun q : CommRingCat.of (vRhoAlgebra D : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hL1
  -- the evaluation comultiplication factors through the correspondence-bridge
  -- (definitional in `frameEvalAlgHom`): precomposition with it is the fiber-map
  -- of the evaluation morphism after the bridge-conjugation.
  have hSplit : (frameEvalAlgHom D).hom.hom =
      ((frameProdAlgebraIso D).inv.unop.hom.hom).comp
        (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameEvalMor D)).unop.hom.hom) := rfl
  -- the bridged product-reading of the tensor point
  set χ := (AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm
      (specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ)
        ⟨p', hover'⟩)).comp (frameProdAlgebraIso D).inv.unop.hom.hom with hχ
  -- the counit naturality computes the ρ-reading as the evaluation of the
  -- product-reading
  have hC : FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D)
      ((AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
        (specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)
          ⟨p ≫ frameEval D, hqv⟩)) =
      (frameEvalMor D).hom.hom
        (FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameProdContAction D) χ) := by
    have hx : (AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ))
        sepClosureQAlgEquiv.symm)
        (specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)
          ⟨p ≫ frameEval D, hqv⟩) =
        χ.comp (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameEvalMor D)).unop.hom.hom) := by
      rw [hA]
      exact AlgHom.ext fun w => rfl
    exact (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
        (rhoContAction D)) hx).trans
      (pointsEquivOfContAction_map (frameEvalMor D) χ)
  -- the goal is the counit-chain (definitional unfold of `vRhoPointsEquiv`),
  -- and the evaluation morphism acts by the frame-on-vector smul (definitional);
  -- the product-reading's components are the two factor-readings.
  refine Eq.trans (show vRhoPointsEquiv D ⟨p ≫ frameEval D, _⟩ =
    FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D)
      ((AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
        (specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)
          ⟨p ≫ frameEval D, hqv⟩)) from rfl) (hC.trans ?_)
  show (FiniteEtaleGalois.pointsEquivOfContAction ℚ
      (frameProdContAction D) χ).2 •
    (FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameProdContAction D) χ).1 = _
  -- the split points over ℚ (hoisted for the subtype elements)
  have hfp : (p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D)) ≫
      constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [Category.assoc]; exact hp
  have hsp : (p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D)) ≫ wFramesπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, ← pullback.condition]; exact hp
  -- left component-read: the vector-factor reading is the bridge after the
  -- left cofan-injection
  have hxf : (AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
      (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0) (AlgebraicClosure ℚ)
        ⟨p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), hfp⟩) =
      χ.comp (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdFst D)).unop.hom.hom) := by
    have hAfst : specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
        (AlgebraicClosure ℚ)
        ⟨p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), hfp⟩ =
        (specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ)
          ⟨p', hover'⟩).comp
          (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)) := by
      refine AlgHom.ext fun w => ?_
      exact congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
        CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hfst
    rw [hAfst]
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun t => sepClosureQAlgEquiv.symm
      ((specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ) ⟨p', hover'⟩) t))
      (congrArg (fun m => m.hom.hom w) (frameProdAlgebraIso_inv_left D)).symm
  -- right component-read: the frame-factor reading is the bridge after the
  -- right cofan-injection
  have hxs : (AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
      (specPointsEquivAlgHom ℚ (wFramesAlgebra D : Type 0) (AlgebraicClosure ℚ)
        ⟨p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), hsp⟩) =
      χ.comp (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdSnd D)).unop.hom.hom) := by
    have hAsnd : specPointsEquivAlgHom ℚ (wFramesAlgebra D : Type 0)
        (AlgebraicClosure ℚ)
        ⟨p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), hsp⟩ =
        (specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ)
          ⟨p', hover'⟩).comp
          (Algebra.TensorProduct.includeRight (R := ℚ)) := by
      refine AlgHom.ext fun w => ?_
      exact congrArg (fun q : CommRingCat.of (wFramesAlgebra D : Type 0) ⟶
        CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hsnd
    rw [hAsnd]
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun t => sepClosureQAlgEquiv.symm
      ((specPointsEquivAlgHom ℚ (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)) (AlgebraicClosure ℚ) ⟨p', hover'⟩) t))
      (congrArg (fun m => m.hom.hom w) (frameProdAlgebraIso_inv_right D)).symm
  -- the two factor-readings via counit-naturality at the projections
  have hread1 : constVecPointsEquiv N
      ⟨p ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), hfp⟩ =
      (FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameProdContAction D) χ).1 :=
    (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
      (constVecContAction N)) hxf).trans
      (pointsEquivOfContAction_map (frameProdFst D) χ)
  have hread2 : wFramesPointsEquiv D
      ⟨p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), hsp⟩ =
      (FiniteEtaleGalois.pointsEquivOfContAction ℚ (frameProdContAction D) χ).2 :=
    (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
      (frameContAction D)) hxs).trans
      (pointsEquivOfContAction_map (frameProdSnd D) χ)
  exact ((congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) (ZMod N) =>
      A • (FiniteEtaleGalois.pointsEquivOfContAction ℚ
        (frameProdContAction D) χ).1) hread2).symm.trans
    (congrArg (fun v => wFramesPointsEquiv D
      ⟨p ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), hsp⟩ • v) hread1.symm))

/-- **[asm-2]** The `h`-slice of the universal-frame evaluation: over a base `T`
carrying a frame-classifier `h`, the constant vector scheme maps to the
`V_ρ`-pullback (evaluation of the classified frame on the constant vectors). -/
noncomputable def frameEvalSlice (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    pullback sT (constVecSchemeπ N) ⟶ pullback (vRhoπ D) sT :=
  pullback.lift
    (pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) ≫ frameEval D)
    (pullback.fst sT (constVecSchemeπ N))
    (by rw [Category.assoc, frameEval_π, ← Category.assoc, pullback.lift_fst,
      ← pullback.condition])

/-- **[T-YR-3b-v]** The right `GL₂`-translations as a `SchemeAction` on the frame
scheme (covariant laws are `wFramesRightMul_one/_mul`). -/
noncomputable def wFramesAction (D : GaloisRepData N) :
    SchemeAction (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (wFrames D) where
  hom γ := wFramesRightMul D γ
  hom_one := wFramesRightMul_one D
  hom_mul γ₁ γ₂ := wFramesRightMul_mul D γ₁ γ₂

/-- **[T-YR-3b-v]** The frames-side representing bijection: maps to
`W_X := X.base ×_ℚ wFrames` over `g` are frames over the pulled-back base. -/
noncomputable def framesEqv (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    {T : Scheme.{0}} (g : T ⟶ X.base) :
    { h : T ⟶ pullback X.structMap (wFramesπ D) //
      h ≫ pullback.fst X.structMap (wFramesπ D) = g } ≃
    { h : T ⟶ wFrames D // h ≫ wFramesπ D = g ≫ X.structMap } where
  toFun h := ⟨h.1 ≫ pullback.snd X.structMap (wFramesπ D), by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, h.2]⟩
  invFun h := ⟨pullback.lift g h.1 h.2.symm, pullback.lift_fst _ _ _⟩
  left_inv h := Subtype.ext (by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, h.2]
    · rw [pullback.lift_snd])
  right_inv h := Subtype.ext (pullback.lift_snd _ _ _)

/-- Naturality of the frames-side bijection: restriction along `k` is composition. -/
theorem framesEqv_nat (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    {T T' : Scheme.{0}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (h : { h : T ⟶ pullback X.structMap (wFramesπ D) //
      h ≫ pullback.fst X.structMap (wFramesπ D) = g }) :
    (framesEqv D X (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩).1 =
      k ≫ (framesEqv D X g h).1 :=
  Category.assoc _ _ _

/-- [T-YR-3b-v helper] The universal-property split of maps into a fibre product,
subtype-form. -/
noncomputable def pullbackSplitEquiv {Z₁ Z₂ B T : Scheme.{0}} (f₁ : Z₁ ⟶ B)
    (f₂ : Z₂ ⟶ B) (g : T ⟶ B) :
    { u : T ⟶ pullback f₁ f₂ // u ≫ (pullback.fst f₁ f₂ ≫ f₁) = g } ≃
    ({ v : T ⟶ Z₁ // v ≫ f₁ = g } × { w : T ⟶ Z₂ // w ≫ f₂ = g }) where
  toFun u := ⟨⟨u.1 ≫ pullback.fst f₁ f₂, by rw [Category.assoc]; exact u.2⟩,
    ⟨u.1 ≫ pullback.snd f₁ f₂, by
      rw [Category.assoc, ← pullback.condition]
      exact u.2⟩⟩
  invFun vw := ⟨pullback.lift vw.1.1 vw.2.1 (vw.1.2.trans vw.2.2.symm), by
    rw [← Category.assoc, pullback.lift_fst]; exact vw.1.2⟩
  left_inv u := Subtype.ext (by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd])
  right_inv vw := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _

/-- [T-YR-3b-v helper] A relative datum's bijection is congruent in the classifying
map (proofs transport). -/
theorem relRep_eqv_congr {Q : ModularCurves.ModuliProblem (CommRingCat.of ℚ)}
    {X : EllObj (CommRingCat.of ℚ)} (d : ModuliProblem.RelRepData Q X)
    {T : Scheme.{0}} (g : T ⟶ X.base) {v w : T ⟶ d.Z} (hvw : v = w)
    (pv : v ≫ d.f = g) :
    d.eqv g ⟨v, pv⟩ = d.eqv g ⟨w, hvw ▸ pv⟩ := by
  subst hvw; rfl

/-- **[T-YR-3b-v(b)]** The product relative datum: given a full-level relative datum
`dL` at `X`, the fibre product `dL.Z ×_{X.base} (X.base ×_ℚ wFrames)` represents the
bare framed problem (`pullbackSplitEquiv` then `dL.eqv × framesEqv`). -/
noncomputable def bareFramedRelRepData (D : GaloisRepData N)
    {X : EllObj (CommRingCat.of ℚ)}
    (dL : ModuliProblem.RelRepData (gammaFullNaiveProblem (CommRingCat.of ℚ) N) X) :
    ModuliProblem.RelRepData (bareFramedProblem D) X where
  Z := pullback dL.f (pullback.fst X.structMap (wFramesπ D))
  f := pullback.fst dL.f (pullback.fst X.structMap (wFramesπ D)) ≫ dL.f
  eqv g := (pullbackSplitEquiv dL.f (pullback.fst X.structMap (wFramesπ D)) g).trans
    (Equiv.prodCongr (dL.eqv g) (framesEqv D X g))
  nat g k u := by
    refine Prod.ext ?_ ?_
    · refine Eq.trans (relRep_eqv_congr dL (k ≫ g)
        (Category.assoc k u.1
          (pullback.fst dL.f (pullback.fst X.structMap (wFramesπ D)))) _) ?_
      exact dL.nat g k ⟨u.1 ≫ pullback.fst _ _, by
        rw [Category.assoc]; exact u.2⟩
    · exact Subtype.ext (Category.assoc _ _ _)

/-- [T-YR-3b-v(c)] The frames-factor action on `W_X = X.base ×_ℚ wFrames`. -/
noncomputable def wxAction (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback X.structMap (wFramesπ D) ⟶ pullback X.structMap (wFramesπ D) :=
  pullback.map X.structMap (wFramesπ D) X.structMap (wFramesπ D)
    (𝟙 X.base) (wFramesRightMul D γ) (𝟙 (Spec (.of ℚ)))
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, wFramesRightMul_π])

theorem wxAction_fst (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wxAction D X γ ≫ pullback.fst X.structMap (wFramesπ D) =
      pullback.fst X.structMap (wFramesπ D) := by
  rw [wxAction, pullback.lift_fst, Category.comp_id]

theorem wxAction_snd (D : GaloisRepData N) (X : EllObj (CommRingCat.of ℚ))
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wxAction D X γ ≫ pullback.snd X.structMap (wFramesπ D) =
      pullback.snd X.structMap (wFramesπ D) ≫ wFramesRightMul D γ := by
  rw [wxAction, pullback.lift_snd]

/-- [T-YR-3b-v(c)] The diagonal action on the product relative scheme (raw-typed;
the `SchemeAction`-laws are proven on these spec lemmas). -/
noncomputable def zxAction (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶
      pullback dE.f (pullback.fst X.structMap (wFramesπ D)) :=
  pullback.map dE.f (pullback.fst X.structMap (wFramesπ D)) dE.f
    (pullback.fst X.structMap (wFramesπ D))
    (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (wxAction D X γ) (𝟙 X.base)
    (by rw [Category.comp_id, dE.over_base])
    (by rw [Category.comp_id, wxAction_fst])

theorem zxAction_fst (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxAction D dE γ ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.σZ.hom (Subgroup.topEquiv.symm γ) := by
  rw [zxAction, pullback.lift_fst]

theorem zxAction_snd (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxAction D dE γ ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D)) =
      pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        wxAction D X γ := by
  rw [zxAction, pullback.lift_snd]

theorem zxAction_one (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    zxAction D dE 1 = 𝟙 (pullback dE.f (pullback.fst X.structMap (wFramesπ D))) := by
  apply pullback.hom_ext
  · rw [zxAction_fst, Category.id_comp,
      show Subgroup.topEquiv.symm
        (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 from map_one _,
      dE.σZ.hom_one, Category.comp_id]
  · rw [zxAction_snd, Category.id_comp,
      show wxAction D X (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 𝟙 _ from by
        apply pullback.hom_ext
        · rw [wxAction_fst, Category.id_comp]
        · rw [wxAction_snd, wFramesRightMul_one, Category.comp_id,
            Category.id_comp],
      Category.comp_id]

theorem zxAction_mul (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxAction D dE (γ₁ * γ₂) = zxAction D dE γ₁ ≫ zxAction D dE γ₂ := by
  apply pullback.hom_ext
  · rw [zxAction_fst, Category.assoc, zxAction_fst, ← Category.assoc,
      zxAction_fst, Category.assoc,
      show Subgroup.topEquiv.symm (γ₁ * γ₂) =
        Subgroup.topEquiv.symm γ₁ * Subgroup.topEquiv.symm γ₂ from map_mul _ _ _,
      dE.σZ.hom_mul]
  · rw [zxAction_snd, Category.assoc, zxAction_snd, ← Category.assoc,
      zxAction_snd, Category.assoc,
      show wxAction D X (γ₁ * γ₂) = wxAction D X γ₁ ≫ wxAction D X γ₂ from by
        apply pullback.hom_ext
        · rw [wxAction_fst, Category.assoc, wxAction_fst, wxAction_fst]
        · rw [wxAction_snd, Category.assoc, wxAction_snd, ← Category.assoc,
            wxAction_snd, Category.assoc, wFramesRightMul_mul]]

/-- **[T-YR-3b-v(c)]** The bare framed problem has equivariant relative data at every
`X`: the full-level equivariant datum at `H = ⊤` ([GHA5]) fibre-multiplied with the
frames factor, carrying the diagonal action. -/
theorem bareFramed_equivariantRelRepData (D : GaloisRepData N)
    (X : EllObj (CommRingCat.of ℚ)) :
    Nonempty (ModuliProblem.EquivariantRelRepData (bareFramedAut D) X) := by
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  obtain ⟨dE⟩ := gammaFullNaive_equivariantRelRepData (CommRingCat.of ℚ) N ⊤ hinvQ X
  refine ⟨{ bareFramedRelRepData D dE.toRelRepData with
    σZ := ⟨fun γ => zxAction D dE γ, zxAction_one D dE, zxAction_mul D dE⟩
    over_base := ?_, equivariant := ?_, finite := ?_, etale := ?_ }⟩
  · intro γ
    show zxAction D dE γ ≫
      (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f) = _
    rw [← Category.assoc, zxAction_fst, Category.assoc, dE.over_base]
    rfl
  · intro T g u γ
    refine Prod.ext ?_ (Subtype.ext ?_)
    · have hLtrans : (u.1 ≫ zxAction D dE γ) ≫
          pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) =
          (u.1 ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            dE.σZ.hom (Subgroup.topEquiv.symm γ) :=
        (Category.assoc _ _ _).trans
          ((congrArg (u.1 ≫ ·) (zxAction_fst D dE γ)).trans
            (Category.assoc _ _ _).symm)
      have hL := dE.equivariant g ⟨u.1 ≫ pullback.fst _ _, by
          rw [Category.assoc]; exact u.2⟩ (Subgroup.topEquiv.symm γ)
      have helem : ((((Subgroup.topEquiv.symm γ)⁻¹)⁻¹ : (⊤ : Subgroup
          (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = (γ⁻¹)⁻¹ := by
        rw [inv_inv, inv_inv]
        rfl
      refine Eq.trans (relRep_eqv_congr dE.toRelRepData g hLtrans _) ?_
      refine Eq.trans hL ?_
      refine Eq.trans (gammaHAut_app_val (CommRingCat.of ℚ) N ⊤
        ((Subgroup.topEquiv.symm γ))⁻¹ (X.pullbackAlong g) _) ?_
      exact congrArg (fun m => (X.pullbackAlong g).curve.glSmul m
        (dE.eqv g ⟨u.1 ≫ pullback.fst _ _, by
          rw [Category.assoc]; exact u.2⟩)) helem
    · show ((u.1 ≫ zxAction D dE γ) ≫
          pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
          pullback.snd X.structMap (wFramesπ D) = _
      calc ((u.1 ≫ zxAction D dE γ) ≫
            pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            pullback.snd X.structMap (wFramesπ D)
          = ((u.1 ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
              wxAction D X γ) ≫ pullback.snd X.structMap (wFramesπ D) :=
            congrArg (· ≫ pullback.snd X.structMap (wFramesπ D))
              ((Category.assoc _ _ _).trans
                ((congrArg (u.1 ≫ ·) (zxAction_snd D dE γ)).trans
                  (Category.assoc _ _ _).symm))
        _ = (u.1 ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
              (pullback.snd X.structMap (wFramesπ D) ≫ wFramesRightMul D γ) :=
            (Category.assoc _ _ _).trans
              (congrArg ((u.1 ≫ pullback.snd dE.f
                (pullback.fst X.structMap (wFramesπ D))) ≫ ·) (wxAction_snd D X γ))
        _ = ((u.1 ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
              pullback.snd X.structMap (wFramesπ D)) ≫ wFramesRightMul D γ :=
            (Category.assoc _ _ _).symm
        _ = ((u.1 ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
              pullback.snd X.structMap (wFramesπ D)) ≫
              wFramesRightMul D ((γ⁻¹)⁻¹) :=
            congrArg (fun m => ((u.1 ≫ pullback.snd dE.f
              (pullback.fst X.structMap (wFramesπ D))) ≫
              pullback.snd X.structMap (wFramesπ D)) ≫ wFramesRightMul D m)
              (inv_inv γ).symm
  · haveI h1 : IsFinite (wFramesπ D) := (wFramesπ_finite_etale D).1
    haveI h2 : IsFinite (pullback.fst X.structMap (wFramesπ D)) :=
      MorphismProperty.pullback_fst _ _ h1
    haveI h3 : IsFinite (pullback.fst dE.f
        (pullback.fst X.structMap (wFramesπ D))) :=
      MorphismProperty.pullback_fst _ _ h2
    haveI h4 : IsFinite dE.f := dE.finite
    show IsFinite (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f)
    exact inferInstance
  · haveI h1 : Etale (wFramesπ D) := (wFramesπ_finite_etale D).2
    haveI h2 : Etale (pullback.fst X.structMap (wFramesπ D)) :=
      MorphismProperty.pullback_fst _ _ h1
    haveI h3 : Etale (pullback.fst dE.f
        (pullback.fst X.structMap (wFramesπ D))) :=
      MorphismProperty.pullback_fst _ _ h2
    haveI h4 : Etale dE.f := dE.etale
    show Etale (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f)
    exact inferInstance

/-- **[T-YR-3b CLOSURE] (KM 7.1.2/7.1.3 via [GHB7])** The free `GL₂`-quotient of the
bare framed problem exists as a quotient-problem package: relatively representable by
finite étale morphisms, with projection and couniversal property. This is the
contracted-product Isom-scheme substrate for `Y(ρ̄)`. -/
theorem bareFramed_quotientProblemData (D : GaloisRepData N) :
    Nonempty (ModuliProblem.QuotientProblemData (bareFramedAut D)) :=
  ModuliProblem.exists_quotientProblemData (bareFramedAut D)
    (bareFramedAut_freeAction D) (bareFramed_equivariantRelRepData D)

/-- **[T-YR-3b CLOSURE, GHC5-shape]** The quotient of the bare framed problem is
affine over `Ell/ℚ`. -/
theorem bareFramed_quotient_affineOverEll (D : GaloisRepData N)
    (pkg : ModuliProblem.QuotientProblemData (bareFramedAut D)) :
    pkg.prob.AffineOverEll :=
  pkg.affineOverEll

end FramedProblemFunctor


/-- **(T-F6 = expert review Q9: the symplectic Isom-scheme route)** Relative
representability of the ρ-level problem: for every elliptic curve `E` over a
`ℚ`-scheme `T`, the functor `T' ↦ {ρ-level structures on E ×_T T'}` is representable
by a finite étale `T`-scheme — the symplectic isomorphism scheme
`Isom^symp(E[N], V_ρ̄)`. `Y(ρ̄)` is then the Isom-scheme over a rigidified level base,
which *carries its moduli interpretation by construction*; the identification with the
Galois twist of `Y(N)_ℚ` is a separate later theorem (route note, plan §Y(ρ̄)). -/
theorem rhoLevel_relativelyRepresentable {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ))
    (E : EllipticCurve T) :
    ∃ (I : Scheme.{0}) (f : I ⟶ T), IsFinite f ∧ Etale f ∧
      ∀ {T' : Scheme.{0}} (k : T' ⟶ T),
        Nonempty ({ h : T' ⟶ I // h ≫ f = k } ≃
          RhoLevelStructure D (k ≫ sT) (E.baseChange k)) := by sorry

/-- The representing property for the twisted modular curve: `(Y, sY)` is a smooth
affine `ℚ`-curve whose `T`-points over `ℚ` are naturally the isomorphism classes of
pairs `(E, α)` — the quotient by pointed over-`T` isomorphisms carrying coordinates to
coordinates (DEF-4). Extracted as a predicate so that geometric irreducibility (T-F5)
can be asserted OF THE REPRESENTING CURVE, not of arbitrary smooth curves (DEF-6). -/
def RepresentsYRho {N : ℕ} [NeZero N] (D : GaloisRepData N) (Y : Scheme.{0})
    (sY : Y ⟶ Spec (.of ℚ)) : Prop :=
  SmoothOfRelativeDimension 1 sY ∧ IsAffineHom sY ∧
    ∀ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℚ)),
      Nonempty ({ h : T ⟶ Y // h ≫ sY = sT } ≃
        Quot (fun (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E) =>
          ∃ f : a.1 ≅ b.1,
            ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
              (ht : t ≫ sT =
                Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
              (x : a.1.Point t)
              (hx : x.1 ≫ a.1.mulByHom N = t ≫ a.1.zero)
              (hx' : (f.hom.mapPoint x).1 ≫ b.1.mulByHom N = t ≫ b.1.zero),
              coord D sT b.2.torsionIso b.2.over_T t ht (f.hom.mapPoint x) hx' =
                coord D sT a.2.torsionIso a.2.over_T t ht x hx))

/-- **(T-F4 = Buzzard p. 33, the main statement)** The twisted modular curve exists:
some `(Y, sY)` represents the ρ-level moduli problem in the sense of
`RepresentsYRho`. Requires `N ≥ 3` (rigidity — Loeffler Prop 3.8.3).
Route of record: the symplectic Isom-scheme over a rigidified base (T-F6, review Q9);
the Galois-twist identification is a separate later theorem (D8). -/
theorem yRho_representable {N : ℕ} [NeZero N] (hN : 3 ≤ N) (D : GaloisRepData N) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ)), RepresentsYRho D Y sY := by sorry

/-- **(T-F5, stream IRR)** Any curve representing the ρ-level problem is
geometrically irreducible over `ℚ`: its base change to `ℚ̄` is irreducible.
ADVERSARIAL FIX (2026-07-05, DEF-6): the previous statement quantified over ALL smooth
relative curves (with `D` unused) and was false (`ℙ¹ ⊔ ℙ¹` counterexample); geometric
irreducibility is a property of the REPRESENTING curve, so the representability
predicate is now the hypothesis. Source: Buzzard p. 33 ("NB irreducibility is proved
complex-analytically by uniformising the ℂ-points of the curve by the upper half
plane"; p. 34 "Proof: See 1980s") — routes in stream IRR (GME 2.9.3 / 2.5.3 algebraic
route, analytic uniformisation alternative). -/
theorem yRho_geometricallyIrreducible {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ))
    (hY : RepresentsYRho D Y sY) :
    IrreducibleSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := by sorry

end ModularCurves
