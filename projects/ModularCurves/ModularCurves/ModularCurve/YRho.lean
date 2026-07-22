import ModularCurves.ForMathlib.FiniteEtaleFundamentalGroup
import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.Coarse
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
