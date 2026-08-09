import ModularCurves.ForMathlib.FiniteEtaleFundamentalGroup
import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.Coarse
import ModularCurves.Moduli.GammaHMaster
import ModularCurves.ModularCurve.YFullRoute
import ModularCurves.GroupScheme.GLSchemeAction
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
`yRho_representable` (proved downstream, `ModularCurve/RhoPoints.lean`).
Geometric irreducibility is a black box (BB-IRR: 1980s,
complex-analytic uniformisation).
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

-- v4.33 bump: neither the `Scheme`/`CommAlgCat` category instances nor the semireducible
-- component types are transparent enough for the rewrites below at `implicit` transparency.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
    Nat.card { x // x ∈ rootsOfUnity N (AlgebraicClosure ℚ) } = N := by
  haveI : NeZero ((N : AlgebraicClosure ℚ)) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  have hdeg : (Polynomial.cyclotomic N (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  exact hprim.card_rootsOfUnity

/-- **(T-G1.L1)** `ℚ̄` contains a primitive `N`-th root of unity. -/
theorem exists_isPrimitiveRoot_algClosureQ (N : ℕ) [NeZero N] :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ N := by
  haveI : NeZero ((N : AlgebraicClosure ℚ)) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  have hdeg : (Polynomial.cyclotomic N (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/-- **(T-G1.L2)** A primitive `N`-th root of unity identifies `ℤ/N` (written
multiplicatively) with `μ_N(ℚ̄)`. This is the pairing normalisation `p`: no choice beyond
`ζ` is involved, and *any* choice is Galois-equivariant for the cyclotomic action — see
`pairingNormalisation_equivariant`. -/
noncomputable def pairingNormalisationOfPrimitiveRoot {N : ℕ} [NeZero N]
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ N) :
    Multiplicative (ZMod N) ≃* rootsOfUnity N (AlgebraicClosure ℚ) :=
  haveI hζu : IsPrimitiveRoot (hζ.isUnit (NeZero.ne N)).unit' N :=
    hζ.isUnit_unit' (NeZero.ne N)
  (AddEquiv.toMultiplicativeLeft hζu.zmodEquivZPowers).trans
    (MulEquiv.subgroupCongr hζu.zpowers_eq)

/-- **(T-G1.L3)** The normalisation is Galois-equivariant through the mod-`N` cyclotomic
character: `σ (p x) = p (x ^ χ(σ))`. This is mathlib's `modularCyclotomicCharacter.spec`
read through the identification. -/
theorem pairingNormalisation_equivariant {N : ℕ} [NeZero N]
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ N) (σ : GalQ)
    (x : Multiplicative (ZMod N)) :
    σ ((pairingNormalisationOfPrimitiveRoot hζ x : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) =
      ((pairingNormalisationOfPrimitiveRoot hζ
        (x ^ ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv : (ZMod N)ˣ) : ZMod N).val) :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  have hmem : ((pairingNormalisationOfPrimitiveRoot hζ x :
      rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) ∈
      rootsOfUnity N (AlgebraicClosure ℚ) :=
    (pairingNormalisationOfPrimitiveRoot hζ x).2
  have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv hmem
  refine hspec.trans ?_
  rw [map_pow]
  rfl

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
      modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_algClosureQ N)
        σ.toRingEquiv
  /-- The pairing normalisation `p`: a group isomorphism from `ℤ/N` (the line `Λ²ρ`,
  carrying the Galois action through `det ∘ ρ`) to `μ_N(ℚ̄)`, Galois-equivariantly. -/
  p : Multiplicative (ZMod N) ≃* rootsOfUnity N (AlgebraicClosure ℚ)
  p_equivariant : ∀ (σ : GalQ) (x : Multiplicative (ZMod N)),
    σ ((p x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((p (x ^ ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv : (ZMod N)ˣ) : ZMod N).val) :
          (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)

/-- **(T-G1 MAIN)** A mod-`N` Galois representation with cyclotomic determinant *is* a
`GaloisRepData`: the pairing normalisation `p` and its equivariance are derived, not
assumed. (`det ρ̄ = χ` is what makes the resulting `(ρ̄, p)` symplectically coherent
downstream; `p` itself exists for any choice of primitive root — see
`pairingNormalisation_equivariant`.) -/
noncomputable def GaloisRepData.ofDetCyclo {N : ℕ} [NeZero N]
    (ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (ker_open : IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ))
    (det_cyclo : ∀ σ : GalQ, Matrix.GeneralLinearGroup.det (ρ σ) =
      modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv) :
    GaloisRepData N :=
  { ρ := ρ
    ker_open := ker_open
    det_cyclo := det_cyclo
    p := pairingNormalisationOfPrimitiveRoot
      (exists_isPrimitiveRoot_algClosureQ N).choose_spec
    p_equivariant := pairingNormalisation_equivariant
      (exists_isPrimitiveRoot_algClosureQ N).choose_spec }

@[simp] theorem GaloisRepData.ofDetCyclo_ρ {N : ℕ} [NeZero N]
    (ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (h₁ h₂) :
    (GaloisRepData.ofDetCyclo ρ h₁ h₂).ρ = ρ := rfl

/-- **(T-G1 MAIN, `∃`-form)** Existence: the pairing datum never obstructs. -/
theorem exists_galoisRepData_of_detCyclo {N : ℕ} [NeZero N]
    (ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (ker_open : IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ))
    (det_cyclo : ∀ σ : GalQ, Matrix.GeneralLinearGroup.det (ρ σ) =
      modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv) :
    ∃ D : GaloisRepData N, D.ρ = ρ :=
  ⟨GaloisRepData.ofDetCyclo ρ ker_open det_cyclo, rfl⟩

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
/-- **Continuity criterion for a finite Galois set.** A finite `Γ`-set is continuous as soon as
some open `K ∋ 1` acts trivially on it: the stabiliser of every point then contains the open
neighbourhood `σ₀ • K` of each of its elements, so the action map into the discrete carrier is
locally constant. Every continuity proof in the `ρ`-tower (`rhoAction`, `rhoSqAction`,
`pointAction`) is this lemma at a different `K`. -/
lemma isContinuous_of_isOpen_of_trivial
    (A : Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (K : Set (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) (hK : IsOpen K) (hK1 : (1 : _) ∈ K)
    (hact : ∀ τ ∈ K, A.ρ τ = 𝟙 A.V) : A.IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj A : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj A => p.1 • p.2) ⁻¹' ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj A, {σ | σ • v = w} ×ˢ ({v} : Set _) := by
    ext ⟨σ, v⟩
    simp
  rw [hdecomp]
  refine isOpen_iUnion fun v => IsOpen.prod ?_ trivial
  refine isOpen_iff_mem_nhds.mpr fun σ₀ hσ₀ => ?_
  refine Filter.mem_of_superset (IsOpen.mem_nhds (hK.smul σ₀) ⟨1, hK1, mul_one σ₀⟩) ?_
  rintro σ ⟨τ, hτ, rfl⟩
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map (A.ρ τ)) v = v
        rw [hact τ hτ, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The `ρ`-action is continuous (the fiber is discrete and the kernel is open). -/
lemma rhoAction_isContinuous (D : GaloisRepData N) :
    (rhoAction D).IsContinuous :=
  isContinuous_of_isOpen_of_trivial _ _ (rhoAction_ker_open D)
    (by simp only [Set.mem_setOf_eq, map_one]) fun τ hτ =>
      FintypeCat.hom_ext _ _ fun x => by
        show D.ρ (galSepMulEquivGalQ τ) • (x : Fin 2 → ZMod N) = x
        rw [show D.ρ (galSepMulEquivGalQ τ) = 1 from hτ, one_smul]

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

set_option backward.isDefEq.respectTransparency false in
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

/-- **[T-EQ-2 b-1]** The `γ`-coordinate change on the constant vector Galois set
(trivially equivariant since the action is trivial). -/
noncomputable def constVecGLMor (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecContAction N ⟶ constVecContAction N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun v => γ • v)
      comm := fun σ => FintypeCat.hom_ext _ _ fun v => rfl }

/-- **[T-EQ-2 b-2]** The vector-side `γ`-twist of the mixed product. -/
noncomputable def frameProdVecTwist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdContAction D ⟶ frameProdContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vA => (γ • vA.1, vA.2))
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => rfl }

/-- **[T-EQ-2 b-2]** The frame-side right-`γ`-twist of the mixed product. -/
noncomputable def frameProdFrameTwist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdContAction D ⟶ frameProdContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vA => (vA.1, vA.2 * γ))
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => by
        show (vA.1, (D.ρ (galSepMulEquivGalQ σ) * vA.2) * γ) =
          (vA.1, D.ρ (galSepMulEquivGalQ σ) * (vA.2 * γ))
        rw [mul_assoc] }

/-- **[T-EQ-2 b-2]** The contracted-product relation at the Galois-set level:
evaluating the `γ`-changed coordinates equals evaluating along the right-translated
frame (`A·(γ·v) = (A·γ)·v`). -/
theorem frameProdTwist_eval (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdVecTwist D γ ≫ frameEvalMor D =
      frameProdFrameTwist D γ ≫ frameEvalMor D := by
  ext vA : 3
  show vA.2 • (γ • vA.1) = (vA.2 * γ) • vA.1
  exact smul_smul vA.2 γ vA.1

/-- **[T-EQ-2 b-2]** The vector twist over the first projection. -/
theorem frameProdVecTwist_fst (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdVecTwist D γ ≫ frameProdFst D =
      frameProdFst D ≫ constVecGLMor N γ := by
  ext vA
  rfl

/-- **[T-EQ-2 b-2]** The vector twist fixes the second projection. -/
theorem frameProdVecTwist_snd (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdVecTwist D γ ≫ frameProdSnd D = frameProdSnd D := by
  ext vA
  rfl

/-- **[T-EQ-2 b-2]** The frame twist fixes the first projection. -/
theorem frameProdFrameTwist_fst (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdFrameTwist D γ ≫ frameProdFst D = frameProdFst D := by
  ext vA
  rfl

/-- **[T-EQ-2 b-2]** The frame twist over the second projection. -/
theorem frameProdFrameTwist_snd (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameProdFrameTwist D γ ≫ frameProdSnd D =
      frameProdSnd D ≫ frameRightMulMor D γ := by
  ext vA
  rfl

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

/-- **[asm-2b-iii]** The shear `(v, A) ↦ (A·v, A)` as a morphism of continuous Galois
sets (equivariance: `(ρσ·A)·v = ρσ·(A·v)` in the first factor). -/
noncomputable def frameShearMor (D : GaloisRepData N) :
    frameProdContAction D ⟶ rhoFrameProdContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vA => (vA.2 • vA.1, vA.2))
      comm := fun σ => FintypeCat.hom_ext _ _ fun vA => by
        show ((D.ρ (galSepMulEquivGalQ σ) * vA.2) • vA.1,
            D.ρ (galSepMulEquivGalQ σ) * vA.2) =
          (D.ρ (galSepMulEquivGalQ σ) • vA.2 • vA.1,
            D.ρ (galSepMulEquivGalQ σ) * vA.2)
        rw [mul_smul] }

/-- **[asm-2b-iii]** The inverse shear `(w, A) ↦ (A⁻¹·w, A)` as a morphism of
continuous Galois sets (equivariance: `(ρσ·A)⁻¹·(ρσ·w) = A⁻¹·w`). -/
noncomputable def frameCoshearMor (D : GaloisRepData N) :
    rhoFrameProdContAction D ⟶ frameProdContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun wA => (wA.2⁻¹ • wA.1, wA.2))
      comm := fun σ => FintypeCat.hom_ext _ _ fun wA => by
        show ((D.ρ (galSepMulEquivGalQ σ) * wA.2)⁻¹ •
            (D.ρ (galSepMulEquivGalQ σ) • wA.1),
            D.ρ (galSepMulEquivGalQ σ) * wA.2) =
          (wA.2⁻¹ • wA.1, D.ρ (galSepMulEquivGalQ σ) * wA.2)
        rw [mul_inv_rev, mul_smul, inv_smul_smul] }

/-- **[asm-2b-iii]** The co-evaluation `(w, A) ↦ A⁻¹·w` as a morphism of continuous
Galois sets (lands in the trivial vector set — the Galois twist cancels). -/
noncomputable def frameCoevalMor (D : GaloisRepData N) :
    rhoFrameProdContAction D ⟶ constVecContAction N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun wA => wA.2⁻¹ • wA.1)
      comm := fun σ => FintypeCat.hom_ext _ _ fun wA => by
        show (D.ρ (galSepMulEquivGalQ σ) * wA.2)⁻¹ •
            (D.ρ (galSepMulEquivGalQ σ) • wA.1) = wA.2⁻¹ • wA.1
        rw [mul_inv_rev, mul_smul, inv_smul_smul] }

/-- Shear then `ρ`-first-projection is the evaluation. -/
theorem frameShearMor_fst (D : GaloisRepData N) :
    frameShearMor D ≫ rhoFrameProdFst D = frameEvalMor D := by
  ext x : 3
  rfl

/-- Shear then `ρ`-second-projection is the frame projection. -/
theorem frameShearMor_snd (D : GaloisRepData N) :
    frameShearMor D ≫ rhoFrameProdSnd D = frameProdSnd D := by
  ext x : 3
  rfl

/-- Shear then co-evaluation is the vector projection (`A⁻¹·(A·v) = v`). -/
theorem frameShearMor_coeval (D : GaloisRepData N) :
    frameShearMor D ≫ frameCoevalMor D = frameProdFst D := by
  ext x : 3
  exact inv_smul_smul _ _

/-- Co-shear then first projection is the co-evaluation. -/
theorem frameCoshearMor_fst (D : GaloisRepData N) :
    frameCoshearMor D ≫ frameProdFst D = frameCoevalMor D := by
  ext x : 3
  rfl

/-- Co-shear then second projection is the `ρ`-frame projection. -/
theorem frameCoshearMor_snd (D : GaloisRepData N) :
    frameCoshearMor D ≫ frameProdSnd D = rhoFrameProdSnd D := by
  ext x : 3
  rfl

/-- Co-shear then evaluation is the `ρ`-vector projection (`A·(A⁻¹·w) = w`). -/
theorem frameCoshearMor_eval (D : GaloisRepData N) :
    frameCoshearMor D ≫ frameEvalMor D = rhoFrameProdFst D := by
  ext x : 3
  exact smul_inv_smul _ _

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

/-- **[asm-3a]** The constant-scheme identification lies over `Spec ℚ`. -/
theorem constVecSchemeIso_π (N : ℕ) [NeZero N] :
    (constVecSchemeIso N).hom ≫ constVecSchemeπ N =
      constSchemeπ (Spec (CommRingCat.of ℚ)) (Fin 2 → ZMod N) := by
  refine Limits.Sigma.hom_ext _ _ fun v => ?_
  rw [← Category.assoc]
  rw [show (constVecSchemeIso N).hom =
    (constSchemeSpecIso (CommRingCat.of ℚ) (Fin 2 → ZMod N)).hom ≫
      (constVecSpecIso N).hom from rfl]
  rw [← Category.assoc, constSchemeSpecIso_ι_hom]
  rw [show (constVecSpecIso N).hom = Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).hom.hom.hom.toRingHom) from rfl]
  rw [show constVecSchemeπ N = Spec.map (CommRingCat.ofHom
    (algebraMap ℚ (constVecAlgebra N : Type 0))) from rfl]
  rw [Category.assoc, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  rw [show (CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)) ≫
      CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom) ≫
      CommRingCat.ofHom (Pi.evalRingHom
        (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) v) =
    𝟙 (CommRingCat.of ℚ) from by
    ext r
    show (Pi.evalRingHom _ v) ((constVecAlgebraIso N).hom.hom.hom
      (algebraMap ℚ (constVecAlgebra N : Type 0) r)) = r
    rw [AlgHom.commutes]
    rfl]
  rw [AlgebraicGeometry.Spec.map_id]
  exact (Limits.Sigma.ι_desc (f := fun _ : (Fin 2 → ZMod N) =>
    Spec (CommRingCat.of ℚ)) (fun _ => 𝟙 _) v).symm

/-- **[T-YR-3d-1c step-4]** The universal-frame evaluation at the scheme level:
`(ℤ/N)²_ℚ ×_ℚ Isom((ℤ/N)², V_ρ) ⟶ V_ρ` (mirror of `vRhoAdd`: the fibre-product/tensor
identification followed by `Spec` of the evaluation comultiplication). -/
noncomputable def frameEval (D : GaloisRepData N) :
    pullback (constVecSchemeπ N) (wFramesπ D) ⟶ vRho D :=
  (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
    (wFramesAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)

/-- **[T-EQ-2 b-3]** The `γ`-coordinate change at the algebra level. -/
noncomputable def constVecGLAlg (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecAlgebra N ⟶ constVecAlgebra N :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (constVecGLMor N γ)).unop

/-- **[T-EQ-2 b-3]** The `γ`-coordinate change on the constant vector scheme. -/
noncomputable def constVecGLScheme (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecScheme N ⟶ constVecScheme N :=
  Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom)

/-- **[T-EQ-2 b-3]** The coordinate change lies over the base. -/
theorem constVecGLScheme_π (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecGLScheme N γ ≫ constVecSchemeπ N = constVecSchemeπ N := by
  show Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (constVecGLAlg N γ).hom.hom.commutes r

/-- **[T-EQ-2 b-3]** The tensor-side vector twist (the correspondence-conjugate of
`frameProdVecTwist`). -/
noncomputable def tensorVecTwistAlg (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) ⟶
      FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) :=
  ((frameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (frameProdVecTwist D γ) ≫ (frameProdAlgebraIso D).hom).unop

/-- **[T-EQ-2 b-3]** The tensor-side frame twist (the correspondence-conjugate of
`frameProdFrameTwist`). -/
noncomputable def tensorFrameTwistAlg (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) ⟶
      FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) :=
  ((frameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (frameProdFrameTwist D γ) ≫ (frameProdAlgebraIso D).hom).unop

/-- **[T-EQ-2 b-3]** The evaluation comultiplication intertwines the two twists (the
`b-2` square transported functorially — no elementwise computation). -/
theorem frameEvalAlgHom_twist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameEvalAlgHom D ≫ tensorVecTwistAlg D γ =
      frameEvalAlgHom D ≫ tensorFrameTwistAlg D γ := by
  show ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameEvalMor D)).unop ≫
    ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdVecTwist D γ) ≫ (frameProdAlgebraIso D).hom).unop =
    ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameEvalMor D)).unop ≫
    ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdFrameTwist D γ) ≫ (frameProdAlgebraIso D).hom).unop
  rw [← CategoryTheory.unop_comp, ← CategoryTheory.unop_comp]
  congr 1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun m => (frameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m)
    (frameProdTwist_eval D γ)

end FrameSubstrate

section PairingLayer

variable {N : ℕ} [NeZero N]

/-- **[CARVE-1d-i]** The `μ_N`-roots Galois set (natural action on roots of unity in
`ℚ̄`, transported along `galSepMulEquivGalQ`). -/
noncomputable abbrev muNRootsAction (N : ℕ) [NeZero N] :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (rootsOfUnity N (AlgebraicClosure ℚ))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun ζ => ⟨Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom ζ.1, by
          rw [mem_rootsOfUnity]
          rw [← map_pow]
          rw [show (ζ.1 : (AlgebraicClosure ℚ)ˣ) ^ (N : ℕ) = 1 from
            (mem_rootsOfUnity _ _).mp ζ.2]
          exact map_one _⟩)
      map_one' := FintypeCat.hom_ext _ _ fun ζ => Subtype.ext (Units.ext (by
        show (galSepMulEquivGalQ 1) (ζ.1 : (AlgebraicClosure ℚ)ˣ).val = _
        rw [map_one]
        rfl))
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun ζ => Subtype.ext
        (Units.ext (by
          show (galSepMulEquivGalQ (σ * τ)) (ζ.1 : (AlgebraicClosure ℚ)ˣ).val = _
          rw [map_mul]
          rfl)) }

open scoped Pointwise FintypeCatDiscrete in
/-- **[CARVE-1d-i]** Continuity of the roots set: the kernel of `ρ` acts trivially
(its cyclotomic image is `1`, and the character's spec fixes every root). -/
lemma muNRootsAction_isContinuous (D : GaloisRepData N) [Fact (1 < N)] :
    (muNRootsAction N).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (muNRootsAction N) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (muNRootsAction N) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (muNRootsAction N),
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
  have hcy : modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (card_rootsOfUnity_algClosureQ N) (galSepMulEquivGalQ τ).toRingEquiv = 1 := by
    rw [show modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N)
        (galSepMulEquivGalQ τ).toRingEquiv =
      Matrix.GeneralLinearGroup.det (D.ρ (galSepMulEquivGalQ τ)) from
      (D.det_cyclo (galSepMulEquivGalQ τ)).symm]
    rw [hτ1, map_one]
  have hAct : (muNRootsAction N).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun ζ => Subtype.ext ?_
    have hspec := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (card_rootsOfUnity_algClosureQ N)
      (galSepMulEquivGalQ τ).toRingEquiv ζ.2
    rw [hcy] at hspec
    rw [show (((1 : (ZMod N)ˣ) : ZMod N)).val = 1 from by
      rw [Units.val_one, ZMod.val_one]] at hspec
    rw [pow_one] at hspec
    exact Units.ext hspec
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((muNRootsAction N).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

open scoped FintypeCatDiscrete in
/-- The roots set as a continuous Galois set. -/
noncomputable abbrev muNRootsContAction (D : GaloisRepData N) [Fact (1 < N)] :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨muNRootsAction N, muNRootsAction_isContinuous D⟩


/-- **[CARVE-1d-i]** The finite étale algebra and scheme of the roots set, with the
comparison comultiplication and its scheme map. -/
noncomputable def muNRootsAlgebra (D : GaloisRepData N) [Fact (1 < N)] :
    CommAlgCat.FiniteEtale.{0} ℚ :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.obj
    (muNRootsContAction D)).unop

noncomputable def muNRootsScheme (D : GaloisRepData N) [Fact (1 < N)] : Scheme.{0} :=
  Spec (.of (muNRootsAlgebra D : Type 0))

noncomputable def muNRootsSchemeπ (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsScheme D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (muNRootsAlgebra D : Type 0)))


/-- **[3d-i]** The standard symplectic form twists by the determinant under the
matrix action on coordinates. -/
theorem sympl_glSmul (A : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (u v : Fin 2 → ZMod N) :
    (A • u) 0 * (A • v) 1 - (A • u) 1 * (A • v) 0 =
      ((Matrix.GeneralLinearGroup.det A : (ZMod N)ˣ) : ZMod N) *
        (u 0 * v 1 - u 1 * v 0) := by
  show ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec u) 0 *
      ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) 1 -
    ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec u) 1 *
      ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).mulVec v) 0 =
    ((Matrix.GeneralLinearGroup.det A : (ZMod N)ˣ) : ZMod N) *
      (u 0 * v 1 - u 1 * v 0)
  rw [show ((Matrix.GeneralLinearGroup.det A : (ZMod N)ˣ) : ZMod N) =
    (A : Matrix (Fin 2) (Fin 2) (ZMod N)).det from rfl]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring


/-- **[T-CV-1b]** The root of the cyclotomic quotient is an `N`-th root of unity. -/
theorem cycloRoot_pow (N : ℕ) [NeZero N] :
    (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ N = 1 := by
  have h := AdjoinRoot.mk_self (f := (Polynomial.X : Polynomial ℚ) ^ N - 1)
  rw [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] at h
  exact h

/-- **[T-CV-1b]** The cyclotomic quotient `ℚ[X]/(Xᴺ − 1)` as a finite étale
`ℚ`-algebra. -/
noncomputable def cycloQuotAlgebra (N : ℕ) [NeZero N] :
    CommAlgCat.FiniteEtale.{0} ℚ :=
  haveI := muNModel_finite ℚ N
  haveI := muNModel_algebra_etale_of_isUnit ℚ N
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  CommAlgCat.FiniteEtale.of ℚ (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1))

/-- **[T-CV-1c]** Algebra maps out of the cyclotomic quotient into a field are the
`N`-th roots of unity (evaluation at the root). -/
noncomputable def cycloAlgHomEquivRoots (N : ℕ) [NeZero N] (L : Type) [Field L]
    [Algebra ℚ L] :
    ((AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ] L) ≃
      rootsOfUnity N L where
  toFun φ := rootsOfUnity.mkOfPowEq (φ (AdjoinRoot.root _)) (by
    rw [← map_pow, cycloRoot_pow, map_one])
  invFun ζ := AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ L) ((ζ : Lˣ) : L) (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    rw [show (((ζ : Lˣ) : L)) ^ N = 1 from (mem_rootsOfUnity' N _).mp ζ.2]
    exact sub_self 1)
  left_inv φ := AdjoinRoot.algHom_ext (by
    rw [AdjoinRoot.liftAlgHom_root]
    exact rootsOfUnity.coe_mkOfPowEq _)
  right_inv ζ := Subtype.ext (Units.ext (by
    rw [rootsOfUnity.coe_mkOfPowEq, AdjoinRoot.liftAlgHom_root]))

/-- **[T-CV-1c]** Roots of unity transport along the separable-vs-algebraic closure
identification. -/
noncomputable def rootsSepQbarEquiv (N : ℕ) [NeZero N] :
    rootsOfUnity N (SeparableClosure ℚ) ≃ rootsOfUnity N (AlgebraicClosure ℚ) where
  toFun ζ := rootsOfUnity.mkOfPowEq
    (sepClosureQAlgEquiv (((ζ : (SeparableClosure ℚ)ˣ) : SeparableClosure ℚ)))
    (by
      rw [← map_pow]
      rw [show (((ζ : (SeparableClosure ℚ)ˣ) : SeparableClosure ℚ)) ^ N = 1 from
        (mem_rootsOfUnity' N _).mp ζ.2]
      rw [map_one])
  invFun ζ := rootsOfUnity.mkOfPowEq
    (sepClosureQAlgEquiv.symm
      (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)))
    (by
      rw [← map_pow]
      rw [show (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ^ N = 1 from
        (mem_rootsOfUnity' N _).mp ζ.2]
      rw [map_one])
  left_inv ζ := Subtype.ext (Units.ext (by
    rw [rootsOfUnity.coe_mkOfPowEq, rootsOfUnity.coe_mkOfPowEq,
      AlgEquiv.symm_apply_apply]))
  right_inv ζ := Subtype.ext (Units.ext (by
    rw [rootsOfUnity.coe_mkOfPowEq, rootsOfUnity.coe_mkOfPowEq,
      AlgEquiv.apply_symm_apply]))

/-- **[T-CV-1c]** The Galois transport compatibility of the closure identification. -/
theorem galSep_sepQ_compat (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (x : SeparableClosure ℚ) :
    (galSepMulEquivGalQ σ) (sepClosureQAlgEquiv x) = sepClosureQAlgEquiv (σ x) := by
  show (AlgEquiv.autCongr sepClosureQAlgEquiv σ) (sepClosureQAlgEquiv x) = _
  simp [AlgEquiv.autCongr]

/-- **[T-CV-1d]** The forward read intertwines the Galois actions. -/
theorem cycloRead_comp (N : ℕ) [NeZero N]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (φ : (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ]
      SeparableClosure ℚ) :
    rootsSepQbarEquiv N (cycloAlgHomEquivRoots N (SeparableClosure ℚ)
        ((σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ).comp φ)) =
      ⟨Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom
        (rootsSepQbarEquiv N
          (cycloAlgHomEquivRoots N (SeparableClosure ℚ) φ)).1, by
        rw [mem_rootsOfUnity]
        rw [← map_pow]
        rw [show ((rootsSepQbarEquiv N
            (cycloAlgHomEquivRoots N (SeparableClosure ℚ) φ)).1 :
            (AlgebraicClosure ℚ)ˣ) ^ N = 1 from
          (mem_rootsOfUnity N _).mp (rootsSepQbarEquiv N
            (cycloAlgHomEquivRoots N (SeparableClosure ℚ) φ)).2]
        exact map_one _⟩ := by
  refine Subtype.ext (Units.ext ?_)
  show sepClosureQAlgEquiv (((σ : SeparableClosure ℚ →ₐ[ℚ]
      SeparableClosure ℚ).comp φ) (AdjoinRoot.root _)) =
    (galSepMulEquivGalQ σ) (sepClosureQAlgEquiv (φ (AdjoinRoot.root _)))
  rw [galSep_sepQ_compat]
  rfl

/-- **[T-CV-1d]** The inverse read intertwines the Galois actions. -/
theorem cycloReadInv_comp (N : ℕ) [NeZero N]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (ζ : rootsOfUnity N (AlgebraicClosure ℚ)) :
    (σ : SeparableClosure ℚ →ₐ[ℚ] SeparableClosure ℚ).comp
        ((cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
          ((rootsSepQbarEquiv N).symm ζ)) =
      (cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
        ((rootsSepQbarEquiv N).symm
          ⟨Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom ζ.1, by
            rw [mem_rootsOfUnity]
            rw [← map_pow]
            rw [show (ζ.1 : (AlgebraicClosure ℚ)ˣ) ^ N = 1 from
              (mem_rootsOfUnity N _).mp ζ.2]
            exact map_one _⟩) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply]
  show σ ((AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ (SeparableClosure ℚ))
      (sepClosureQAlgEquiv.symm
        (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))) _)
      (AdjoinRoot.root _)) = _
  rw [AdjoinRoot.liftAlgHom_root]
  rw [show ((cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
      ((rootsSepQbarEquiv N).symm
        (⟨Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom ζ.1, by
          rw [mem_rootsOfUnity]
          rw [← map_pow]
          rw [show (ζ.1 : (AlgebraicClosure ℚ)ˣ) ^ N = 1 from
            (mem_rootsOfUnity N _).mp ζ.2]
          exact map_one _⟩ : rootsOfUnity N (AlgebraicClosure ℚ))))
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) =
    sepClosureQAlgEquiv.symm ((galSepMulEquivGalQ σ)
      (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))) from
    AdjoinRoot.liftAlgHom_root _ _ _ _]
  have hc := galSep_sepQ_compat σ (sepClosureQAlgEquiv.symm
    (((ζ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)))
  rw [AlgEquiv.apply_symm_apply] at hc
  rw [hc, AlgEquiv.symm_apply_apply]

open scoped FintypeCatDiscrete in
/-- **[T-CV-1d]** The correspondence image of the cyclotomic quotient is the roots
Galois set. -/
noncomputable def muNRootsCorrespondenceIso (D : GaloisRepData N) [Fact (1 < N)] :
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.obj
        (Opposite.op (cycloQuotAlgebra N)) ≅ muNRootsContAction D where
  hom := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun φ => rootsSepQbarEquiv N
        (cycloAlgHomEquivRoots N (SeparableClosure ℚ) φ))
      comm := fun σ => FintypeCat.hom_ext _ _ fun φ => cycloRead_comp N σ φ }
  inv := ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun ζ =>
        (cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
          ((rootsSepQbarEquiv N).symm ζ))
      comm := fun σ => FintypeCat.hom_ext _ _ fun ζ =>
        (cycloReadInv_comp N σ ζ).symm }
  hom_inv_id := by
    ext φ
    show (cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
      ((rootsSepQbarEquiv N).symm (rootsSepQbarEquiv N
        (cycloAlgHomEquivRoots N (SeparableClosure ℚ) φ))) = φ
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  inv_hom_id := by
    ext ζ
    have h1 : rootsSepQbarEquiv N (cycloAlgHomEquivRoots N (SeparableClosure ℚ)
        ((cycloAlgHomEquivRoots N (SeparableClosure ℚ)).symm
          ((rootsSepQbarEquiv N).symm ζ))) = ζ := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact congrArg (fun w : rootsOfUnity N (AlgebraicClosure ℚ) =>
      ((w : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h1

open scoped FintypeCatDiscrete in
/-- **[T-CV-1e]** The roots algebra is the cyclotomic quotient (transport through the
correspondence's inverse and unit — mirror of `constVecAlgebraIso`). -/
noncomputable def muNRootsAlgebraIso (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsAlgebra D ≅ cycloQuotAlgebra N :=
  (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.mapIso
      (muNRootsCorrespondenceIso D).symm ≪≫
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.app
      (Opposite.op (cycloQuotAlgebra N))).symm).unop).symm

/-- **[T-CV-1e]** `Spec` of the roots-algebra identification (mirror of
`constVecSpecIso`). -/
noncomputable def muNRootsSpecIso (D : GaloisRepData N) [Fact (1 < N)] :
    Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1))) ≅
      Spec (CommRingCat.of (muNRootsAlgebra D : Type 0)) where
  hom := Spec.map (CommRingCat.ofHom
    (muNRootsAlgebraIso D).hom.hom.hom.toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (muNRootsAlgebraIso D).inv.hom.hom.toRingHom)
  hom_inv_id :=
    (Spec.map_comp _ _).symm.trans
      ((congrArg Spec.map
        (congrArg (fun (f : cycloQuotAlgebra N ⟶ cycloQuotAlgebra N) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          ((muNRootsAlgebraIso D).inv_hom_id))).trans
        (Spec.map_id _))
  inv_hom_id :=
    (Spec.map_comp _ _).symm.trans
      ((congrArg Spec.map
        (congrArg (fun (f : muNRootsAlgebra D ⟶ muNRootsAlgebra D) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          ((muNRootsAlgebraIso D).hom_inv_id))).trans
        (Spec.map_id _))

/-- **[T-CV-1 CLOSE]** The DS3 bridge: `μ_N` over `Spec ℚ` is the roots scheme. -/
noncomputable def muNSpecQIso (D : GaloisRepData N) [Fact (1 < N)] :
    muN (Spec (CommRingCat.of ℚ)) N ≅ muNRootsScheme D :=
  muNSpecFieldIso ℚ N ≪≫ muNRootsSpecIso D

/-- **[T-CV-1 CLOSE]** The bridge lies over the base. -/
theorem muNSpecQIso_π (D : GaloisRepData N) [Fact (1 < N)] :
    (muNSpecQIso D).hom ≫ muNRootsSchemeπ D =
      muNπ (Spec (CommRingCat.of ℚ)) N := by
  have hinner : (muNRootsSpecIso D).hom ≫ muNRootsSchemeπ D =
      Spec.map (CommRingCat.ofHom
        (AdjoinRoot.of ((Polynomial.X : Polynomial ℚ) ^ N - 1))) :=
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map (by
      ext r
      exact ((muNRootsAlgebraIso D).hom.hom.hom.commutes r)))
  exact (Category.assoc _ _ _).trans
    ((congrArg ((muNSpecFieldIso ℚ N).hom ≫ ·) hinner).trans
      (muNSpecFieldIso_struct ℚ N))


open scoped FintypeCatDiscrete in
/-- **[T-F3a-i]** The paired `ρ`-set: the diagonal Galois action on ordered pairs of
`(ℤ/N)²`-vectors. -/
noncomputable abbrev rhoPairAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk (fun uv =>
        (D.ρ (galSepMulEquivGalQ σ) • uv.1, D.ρ (galSepMulEquivGalQ σ) • uv.2))
      map_one' := FintypeCat.hom_ext _ _ fun uv => by
        show (D.ρ (galSepMulEquivGalQ 1) • uv.1,
          D.ρ (galSepMulEquivGalQ 1) • uv.2) = uv
        rw [map_one, map_one, one_smul, one_smul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun uv => by
        show (D.ρ (galSepMulEquivGalQ (σ * τ)) • uv.1,
          D.ρ (galSepMulEquivGalQ (σ * τ)) • uv.2) = _
        rw [map_mul, map_mul, mul_smul, mul_smul]
        rfl }

open scoped Pointwise FintypeCatDiscrete in
/-- **[T-F3a-i]** Continuity of the paired `ρ`-action (same open kernel). -/
lemma rhoPairAction_isContinuous (D : GaloisRepData N) :
    (rhoPairAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (rhoPairAction D) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (rhoPairAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (rhoPairAction D),
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
  have hAct : (rhoPairAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun uv => ?_
    show (D.ρ (galSepMulEquivGalQ τ) • uv.1,
      D.ρ (galSepMulEquivGalQ τ) • uv.2) = uv
    rw [hτ1, one_smul, one_smul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((rhoPairAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

open scoped FintypeCatDiscrete in
/-- The paired `ρ`-set as a continuous Galois set. -/
noncomputable abbrev rhoPairContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoPairAction D, rhoPairAction_isContinuous D⟩

open scoped FintypeCatDiscrete in
/-- **[T-F3a-ii]** The symplectic-pairing comparison: `(u,v) ↦ p(ofAdd (u∧v))` is
equivariant from the paired `ρ`-set into the roots (`sympl_glSmul` + `det_cyclo` +
`p_equivariant`). -/
noncomputable def rhoPairMor (D : GaloisRepData N) [Fact (1 < N)] :
    rhoPairContAction D ⟶ muNRootsContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk
        (fun uv => D.p (Multiplicative.ofAdd
          (uv.1 0 * uv.2 1 - uv.1 1 * uv.2 0)))
      comm := fun σ => FintypeCat.hom_ext _ _ fun uv => Subtype.ext (Units.ext (by
        show ((D.p (Multiplicative.ofAdd
            ((D.ρ (galSepMulEquivGalQ σ) • uv.1) 0 *
                (D.ρ (galSepMulEquivGalQ σ) • uv.2) 1 -
              (D.ρ (galSepMulEquivGalQ σ) • uv.1) 1 *
                (D.ρ (galSepMulEquivGalQ σ) • uv.2) 0)) :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          (galSepMulEquivGalQ σ)
            ((D.p (Multiplicative.ofAdd (uv.1 0 * uv.2 1 - uv.1 1 * uv.2 0)) :
              (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        rw [sympl_glSmul, D.det_cyclo (galSepMulEquivGalQ σ)]
        rw [D.p_equivariant (galSepMulEquivGalQ σ)
          (Multiplicative.ofAdd (uv.1 0 * uv.2 1 - uv.1 1 * uv.2 0))]
        congr 2
        rw [show (Multiplicative.ofAdd (uv.1 0 * uv.2 1 - uv.1 1 * uv.2 0)) ^
            ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
              (card_rootsOfUnity_algClosureQ N)
              (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val =
          Multiplicative.ofAdd
            (((modularCyclotomicCharacter (AlgebraicClosure ℚ)
              (card_rootsOfUnity_algClosureQ N)
              (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val •
            (uv.1 0 * uv.2 1 - uv.1 1 * uv.2 0)) from rfl]
        rw [nsmul_eq_mul]
        congr 1
        rw [show (((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val :
            ZMod N) =
          ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N) from by
          simp only [ZMod.natCast_val, ZMod.cast_id]])) }

/-- **[T-F3a-iii]** The finite étale algebra of the paired `ρ`-set. -/
noncomputable def vRhoPairAlgebra (D : GaloisRepData N) :
    CommAlgCat.FiniteEtale.{0} ℚ :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.obj
    (rhoPairContAction D)).unop

/-- **[T-F3a-iii]** Its spectrum. -/
noncomputable def vRhoPairScheme (D : GaloisRepData N) : Scheme.{0} :=
  Spec (.of (vRhoPairAlgebra D : Type 0))

/-- **[T-F3a-iii]** The structure morphism. -/
noncomputable def vRhoPairSchemeπ (D : GaloisRepData N) :
    vRhoPairScheme D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoPairAlgebra D : Type 0)))

/-- **[T-F3a-iii]** The pairing comparison, algebra side. -/
noncomputable def rhoPairAlgHom (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsAlgebra D ⟶ vRhoPairAlgebra D :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (rhoPairMor D)).unop

/-- **[T-F3a-iii]** The pairing comparison, scheme side. -/
noncomputable def rhoPairSchemeMap (D : GaloisRepData N) [Fact (1 < N)] :
    vRhoPairScheme D ⟶ muNRootsScheme D :=
  Spec.map (CommRingCat.ofHom (rhoPairAlgHom D).hom.hom.toRingHom)

/-- **[T-F3a-iii]** The pairing comparison lies over `ℚ`. -/
theorem rhoPairSchemeMap_π (D : GaloisRepData N) [Fact (1 < N)] :
    rhoPairSchemeMap D ≫ muNRootsSchemeπ D = vRhoPairSchemeπ D := by
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  exact congrArg AlgebraicGeometry.Spec.map (by
    ext r
    exact (rhoPairAlgHom D).hom.hom.commutes r)

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** The abstract fiber of `V_ρ`'s algebra is the `ρ`-set (the counit of
the Galois correspondence at the `ρ`-set; `op (unop _)` is definitionally the original).
-/
noncomputable def vRhoFiberIso (D : GaloisRepData N) :
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.obj
        (Opposite.op (vRhoAlgebra D)) ≅ rhoContAction D :=
  (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).counitIso.app (rhoContAction D)

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** First projection of the paired `ρ`-set. -/
noncomputable def rhoPairFst (D : GaloisRepData N) :
    rhoPairContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.fst
      comm := fun σ => FintypeCat.hom_ext _ _ fun uv => rfl }

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** Second projection of the paired `ρ`-set. -/
noncomputable def rhoPairSnd (D : GaloisRepData N) :
    rhoPairContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun σ => FintypeCat.hom_ext _ _ fun uv => rfl }

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** The paired `ρ`-set with its projections is a binary product fan. -/
noncomputable def rhoPairBinaryFan (D : GaloisRepData N) :
    Limits.BinaryFan (rhoContAction D) (rhoContAction D) :=
  Limits.BinaryFan.mk (rhoPairFst D) (rhoPairSnd D)

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** The paired `ρ`-set is the binary product of the `ρ`-set with
itself. -/
noncomputable def rhoPairBinaryFanIsLimit (D : GaloisRepData N) :
    Limits.IsLimit (rhoPairBinaryFan D) := by
  refine Limits.BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun x => (s.fst.hom.hom x, s.snd.hom.hom x))
        comm := fun σ => FintypeCat.hom_ext _ _ fun x => ?_ })
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · have hf := congrArg (fun (h : s.pt.obj.V ⟶ (rhoAction D).V) => h x)
      (s.fst.hom.comm σ)
    have hg := congrArg (fun (h : s.pt.obj.V ⟶ (rhoAction D).V) => h x)
      (s.snd.hom.comm σ)
    exact Prod.ext hf hg
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    exacts [congrFun (congrArg (fun (q : s.pt ⟶ rhoContAction D) =>
        q.hom.hom x) h₁) _,
      congrFun (congrArg (fun (q : s.pt ⟶ rhoContAction D) =>
        q.hom.hom x) h₂) _]

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** The correspondence image of the tensor square of `V_ρ`'s algebra is
the paired `ρ`-set: both are binary products (the op-tensor cofan through the
limit-preserving equivalence, and the explicit pair fan), matched leg-wise by the
counit. -/
noncomputable def pairCorrespondenceIso (D : GaloisRepData N) :
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.obj
        (Opposite.op (FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D))) ≅
      rhoPairContAction D :=
  Limits.IsLimit.conePointsIsoOfNatIso
    (Limits.isLimitOfPreserves
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor
      (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D) (vRhoAlgebra D)))
    (rhoPairBinaryFanIsLimit D)
    (Limits.pairComp _ _ _ ≪≫ Limits.mapPairIso (vRhoFiberIso D) (vRhoFiberIso D))

open scoped FintypeCatDiscrete in
/-- **[T-F3a-iv]** The abstract paired algebra is the tensor square (transport through
the correspondence's inverse and unit — `muNRootsAlgebraIso` mirror). -/
noncomputable def vRhoPairTensorIso (D : GaloisRepData N) :
    vRhoPairAlgebra D ≅
      FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D) :=
  (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.mapIso
      (pairCorrespondenceIso D).symm ≪≫
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.app
      (Opposite.op (FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
        (vRhoAlgebra D)))).symm).unop).symm

open scoped TensorProduct in
/-- **[T-F3a-iv]** `Spec` of the tensor identification (`muNRootsSpecIso` mirror). -/
noncomputable def vRhoPairSpecIso (D : GaloisRepData N) :
    Spec (CommRingCat.of ((vRhoAlgebra D : Type 0) ⊗[ℚ] (vRhoAlgebra D : Type 0))) ≅
      Spec (CommRingCat.of (vRhoPairAlgebra D : Type 0)) where
  hom := Spec.map (CommRingCat.ofHom
    (vRhoPairTensorIso D).hom.hom.hom.toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (vRhoPairTensorIso D).inv.hom.hom.toRingHom)
  hom_inv_id :=
    (Spec.map_comp _ _).symm.trans
      ((congrArg Spec.map
        (congrArg (fun (f : FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
            (vRhoAlgebra D) ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
            (vRhoAlgebra D)) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          ((vRhoPairTensorIso D).inv_hom_id))).trans
        (Spec.map_id _))
  inv_hom_id :=
    (Spec.map_comp _ _).symm.trans
      ((congrArg Spec.map
        (congrArg (fun (f : vRhoPairAlgebra D ⟶ vRhoPairAlgebra D) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          ((vRhoPairTensorIso D).hom_inv_id))).trans
        (Spec.map_id _))

open scoped TensorProduct in
/-- **[T-F3a-v]** The fibre square of `V_ρ` over `ℚ` is the paired scheme
(mathlib's `pullbackSpecIso` composed with the tensor identification). -/
noncomputable def pullbackVRhoIso (D : GaloisRepData N) :
    pullback (vRhoπ D) (vRhoπ D) ≅ vRhoPairScheme D :=
  AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
    (vRhoAlgebra D : Type 0) ≪≫ vRhoPairSpecIso D

/-- **[T-F3a-v]** The `V_ρ`-pairing map on the fibre square: transport to the paired
scheme and compare into the roots scheme. -/
noncomputable def vRhoPairingMap (D : GaloisRepData N) [Fact (1 < N)] :
    pullback (vRhoπ D) (vRhoπ D) ⟶ muNRootsScheme D :=
  (pullbackVRhoIso D).hom ≫ rhoPairSchemeMap D

open scoped TensorProduct in
/-- **[T-F3a-v]** The pairing map lies over the base. -/
theorem vRhoPairingMap_π (D : GaloisRepData N) [Fact (1 < N)] :
    vRhoPairingMap D ≫ muNRootsSchemeπ D =
      pullback.fst (vRhoπ D) (vRhoπ D) ≫ vRhoπ D := by
  have h1 : (vRhoPairSpecIso D).hom ≫ vRhoPairSchemeπ D =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ
        ((vRhoAlgebra D : Type 0) ⊗[ℚ] (vRhoAlgebra D : Type 0)))) :=
    (AlgebraicGeometry.Spec.map_comp _ _).symm.trans
      (congrArg AlgebraicGeometry.Spec.map (by
        ext r
        exact ((vRhoPairTensorIso D).hom.hom.hom.commutes r)))
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap ℚ
      ((vRhoAlgebra D : Type 0) ⊗[ℚ] (vRhoAlgebra D : Type 0)))) =
      Spec.map (CommRingCat.ofHom (algebraMap (vRhoAlgebra D : Type 0)
        ((vRhoAlgebra D : Type 0) ⊗[ℚ] (vRhoAlgebra D : Type 0)))) ≫ vRhoπ D := by
    refine Eq.trans ?_ (AlgebraicGeometry.Spec.map_comp _ _)
    exact congrArg AlgebraicGeometry.Spec.map (by
      ext r
      exact (IsScalarTower.algebraMap_apply ℚ (vRhoAlgebra D : Type 0)
        ((vRhoAlgebra D : Type 0) ⊗[ℚ] (vRhoAlgebra D : Type 0)) r))
  rw [vRhoPairingMap, pullbackVRhoIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [rhoPairSchemeMap_π]
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (vRhoAlgebra D : Type 0)).hom ≫ ·)
    (h1.trans h2)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ vRhoπ D)
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ _ _)


end PairingLayer

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

/-- **[T-F3b]** The coordinate-pair read of a pair of raw `N`-torsion points through a
`ρ`-level isomorphism, as a `W`-point of the fibre square of `V_ρ`. -/
noncomputable def coordPairLift {N : ℕ} [NeZero N] (D : GaloisRepData N)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    W ⟶ pullback (vRhoπ D) (vRhoπ D) :=
  pullback.lift
    (E.pointToTorsion x hx ≫ torsionIso.hom ≫ pullback.fst (vRhoπ D) sT)
    (E.pointToTorsion y hy ≫ torsionIso.hom ≫ pullback.fst (vRhoπ D) sT)
    (by
      have hside : ∀ (z : E.Point t) (hz : z.1 ≫ E.mulByHom N = t ≫ E.zero),
          (E.pointToTorsion z hz ≫ torsionIso.hom ≫ pullback.fst (vRhoπ D) sT) ≫
            vRhoπ D = t ≫ sT := fun z hz => by
        simp only [Category.assoc]
        rw [pullback.condition, reassoc_of% hOver,
          reassoc_of% (E.pointToTorsion_torsionπ z hz)]
      rw [hside x hx, hside y hy])

/-- **[T-F3b]** The Weil-pairing read of a pair of raw `N`-torsion points, as a
`W`-point of the roots scheme (through the `μ_N`-basechange and the DS3 bridge). -/
noncomputable def torsionPairEval {N : ℕ} [NeZero N] (D : GaloisRepData N)
    [Fact (1 < N)] {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    {W : Scheme.{0}} (t : W ⟶ T) (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    W ⟶ muNRootsScheme D :=
  pullback.lift (E.pointToTorsion x hx) (E.pointToTorsion y hy) (by simp) ≫
    E.weilPairing N ≫ muNMapAlong sT N ≫ (muNSpecQIso D).hom

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
  /-- **[T-F3b, board v3]** Morphism-level pairing compatibility: for every scheme
  `W` and every pair of raw `N`-torsion `W`-points, the Weil-pairing read in the
  roots scheme equals the coordinate-pair read through `torsionIso` composed with the
  `V_ρ`-pairing map. Quantified over scheme-valued points, so the condition has
  content over bases with no `ℚ̄`-points (where the pointwise fields are vacuous) and
  transports along base change through the registered naturalities. -/
  pairing_scheme : ∀ [Fact (1 < N)] {W : Scheme.{0}} (t : W ⟶ T)
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
    torsionPairEval D sT t x y hx hy =
      coordPairLift D sT torsionIso over_T t x y hx hy ≫ vRhoPairingMap D

section RhoProblem

open _root_.CategoryTheory

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

/-- **(T-C1c, DS4 REGISTER SPEC: compatibility with base change of the CURVE)** The
Weil pairing commutes with the cartesian torsion square of an `Ell/ℚ`-morphism: pushing a
pair of `A[N]`-points forward to `B[N]` and pairing there is the same as pairing in
`A[N]` and mapping the value along `μ_{N,A.base} ⟶ μ_{N,B.base}`.

This is the *curve*-direction companion of the registered base-change spec
`weilPairingEval_restrict` (which is the `T`-direction), and is the exact content of
KM 2.8.4.2 ("the pairing commutes with base change"). It is stated here as a DS4 register
entry — the pairings of `A.curve` and of `B.curve` are two independent register data, so
no relation between them is derivable; the point-level naturality
`weilPairingEval_mapPoint` below IS derived from it. -/
theorem weilPairing_torsionMapOfEllHom {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (N : ℕ) [NeZero N] :
    pullback.map (A.curve.torsionπ N) (A.curve.torsionπ N)
        (B.curve.torsionπ N) (B.curve.torsionπ N)
        (torsionMapOfEllHom g N) (torsionMapOfEllHom g N) g.baseHom
        (torsionMapOfEllHom_π g N).symm (torsionMapOfEllHom_π g N).symm ≫
      B.curve.weilPairing N =
        A.curve.weilPairing N ≫ muNMapAlong g.baseHom N := by sorry

/-- **[T-YR-2e-W]** Naturality of the Weil-pairing evaluation along an `Ell/ℚ`-morphism:
`e_N` of the pushed-forward points agrees with `e_N` upstairs. **PROVED** from the DS4
register spec `weilPairing_torsionMapOfEllHom` (curve base change) together with
`pointToTorsion_mapPoint` (the torsion lift is natural in the curve) and
`muNPointsEquiv_mapAlong` (the `μ_N`-points dictionary is natural in the base). -/
theorem weilPairingEval_mapPoint {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    {T : Scheme.{0}} (t : T ⟶ A.base) (x y : A.curve.Point t)
    (hx : x.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero)
    (hy : y.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero) :
    (B.curve.weilPairingEval (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
        (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy)).1 =
      (A.curve.weilPairingEval x y hx hy).1 := by
  -- the two torsion lifts are related by the cartesian torsion square
  have hlift : pullback.lift
        (B.curve.pointToTorsion (EllHom.mapPoint g t x) (EllHom.mapPoint_torsion g x hx))
        (B.curve.pointToTorsion (EllHom.mapPoint g t y) (EllHom.mapPoint_torsion g y hy))
        (by simp) =
      pullback.lift (A.curve.pointToTorsion x hx) (A.curve.pointToTorsion y hy) (by simp) ≫
        pullback.map (A.curve.torsionπ N) (A.curve.torsionπ N)
          (B.curve.torsionπ N) (B.curve.torsionπ N)
          (torsionMapOfEllHom g N) (torsionMapOfEllHom g N) g.baseHom
          (torsionMapOfEllHom_π g N).symm (torsionMapOfEllHom_π g N).symm := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst]
      exact (pointToTorsion_mapPoint g x hx).symm
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd]
      exact (pointToTorsion_mapPoint g y hy).symm
  have hover : (pullback.lift (A.curve.pointToTorsion x hx) (A.curve.pointToTorsion y hy)
        (by simp) ≫ A.curve.weilPairing N) ≫ muNπ A.base N = t := by
    rw [Category.assoc, A.curve.weilPairing_over N, ← Category.assoc,
      pullback.lift_fst, A.curve.pointToTorsion_torsionπ]
  refine Eq.trans ?_ (muNPointsEquiv_mapAlong g.baseHom N t
    ⟨pullback.lift (A.curve.pointToTorsion x hx) (A.curve.pointToTorsion y hy) (by simp) ≫
      A.curve.weilPairing N, hover⟩)
  refine congrArg Subtype.val (congrArg (muNPointsEquiv B.base N (t ≫ g.baseHom))
    (Subtype.ext ?_))
  show pullback.lift
      (B.curve.pointToTorsion (EllHom.mapPoint g t x) (EllHom.mapPoint_torsion g x hx))
      (B.curve.pointToTorsion (EllHom.mapPoint g t y) (EllHom.mapPoint_torsion g y hy))
      (by simp) ≫ B.curve.weilPairing N =
    (pullback.lift (A.curve.pointToTorsion x hx) (A.curve.pointToTorsion y hy)
      (by simp) ≫ A.curve.weilPairing N) ≫ muNMapAlong g.baseHom N
  rw [hlift, Category.assoc, weilPairing_torsionMapOfEllHom g N, Category.assoc]

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
  pairing_scheme := by
    intro _ W t x y hx hy
    have hB := α.pairing_scheme (t ≫ g.baseHom)
      (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
      (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy)
    have hoverA : (pullback.lift (A.curve.pointToTorsion x hx)
        (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N) ≫
        muNπ A.base N = t := by
      rw [Category.assoc, A.curve.weilPairing_over N, ← Category.assoc,
        pullback.lift_fst, A.curve.pointToTorsion_torsionπ]
    have h1 : ((muNPointsEquiv B.base N (t ≫ g.baseHom))
        ⟨(pullback.lift (A.curve.pointToTorsion x hx)
            (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N) ≫
          muNMapAlong g.baseHom N, by
            rw [Category.assoc, muNMapAlong_π, ← Category.assoc, hoverA]⟩ :
          Γ(W, ⊤)) =
        ((muNPointsEquiv B.base N (t ≫ g.baseHom))
          ⟨pullback.lift (B.curve.pointToTorsion (EllHom.mapPoint g t x)
                (EllHom.mapPoint_torsion g x hx))
              (B.curve.pointToTorsion (EllHom.mapPoint g t y)
                (EllHom.mapPoint_torsion g y hy)) (by simp) ≫
            B.curve.weilPairing N, by
              rw [Category.assoc, B.curve.weilPairing_over N, ← Category.assoc,
                pullback.lift_fst, B.curve.pointToTorsion_torsionπ]⟩ : Γ(W, ⊤)) := by
      rw [muNPointsEquiv_mapAlong g.baseHom N t
        ⟨pullback.lift (A.curve.pointToTorsion x hx)
            (A.curve.pointToTorsion y hy) (by simp) ≫ A.curve.weilPairing N,
          hoverA⟩]
      exact (weilPairingEval_mapPoint g t x y hx hy).symm
    have h3 := congrArg Subtype.val
      ((muNPointsEquiv B.base N (t ≫ g.baseHom)).injective (Subtype.ext h1))
    have hcoordleg : ∀ (z : A.curve.Point t)
        (hz : z.1 ≫ A.curve.mulByHom N = t ≫ A.curve.zero),
        A.curve.pointToTorsion z hz ≫ (pullTorsionIso D g α).hom ≫
            pullback.fst (vRhoπ D) A.structMap =
          B.curve.pointToTorsion (EllHom.mapPoint g t z)
              (EllHom.mapPoint_torsion g z hz) ≫ α.torsionIso.hom ≫
            pullback.fst (vRhoπ D) B.structMap := fun z hz => by
      rw [← Category.assoc, ← pointToTorsion_mapPoint g z hz, Category.assoc,
        pullTorsionIso_fst]
      simp only [Category.assoc]
    have hcoord : coordPairLift D A.structMap (pullTorsionIso D g α)
          (pullTorsionIso_over D g α) t x y hx hy =
        coordPairLift D B.structMap α.torsionIso α.over_T (t ≫ g.baseHom)
          (EllHom.mapPoint g t x) (EllHom.mapPoint g t y)
          (EllHom.mapPoint_torsion g x hx) (EllHom.mapPoint_torsion g y hy) := by
      apply pullback.hom_ext
      · show pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D) =
          pullback.lift _ _ _ ≫ pullback.fst (vRhoπ D) (vRhoπ D)
        rw [pullback.lift_fst, pullback.lift_fst]
        exact hcoordleg x hx
      · show pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D) =
          pullback.lift _ _ _ ≫ pullback.snd (vRhoπ D) (vRhoπ D)
        rw [pullback.lift_snd, pullback.lift_snd]
        exact hcoordleg y hy
    refine Eq.trans ?_ (Eq.trans hB (congrArg (· ≫ vRhoPairingMap D) hcoord.symm))
    show pullback.lift (A.curve.pointToTorsion x hx) (A.curve.pointToTorsion y hy)
        (by simp) ≫ A.curve.weilPairing N ≫ muNMapAlong A.structMap N ≫
        (muNSpecQIso D).hom =
      pullback.lift (B.curve.pointToTorsion (EllHom.mapPoint g t x)
          (EllHom.mapPoint_torsion g x hx))
        (B.curve.pointToTorsion (EllHom.mapPoint g t y)
          (EllHom.mapPoint_torsion g y hy)) (by simp) ≫
        B.curve.weilPairing N ≫ muNMapAlong B.structMap N ≫ (muNSpecQIso D).hom
    have hstruct : muNMapAlong A.structMap N =
        muNMapAlong g.baseHom N ≫ muNMapAlong B.structMap N :=
      (congrArg (fun m => muNMapAlong m N) g.base_w.symm).trans
        (muNMapAlong_comp g.baseHom B.structMap N)
    rw [hstruct]
    simp only [Category.assoc]
    rw [reassoc_of% h3]

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

/-- **[3c-A]** Precomposition with the split-algebra identification. -/
noncomputable def precompCvIsoEquiv (N : ℕ) [NeZero N] :
    ((constVecAlgebra N : Type 0) →ₐ[ℚ] SeparableClosure ℚ) ≃
      (((Fin 2 → ZMod N) → ℚ) →ₐ[ℚ] SeparableClosure ℚ) where
  toFun φ := φ.comp (constVecAlgebraIso N).inv.hom.hom
  invFun ψ := ψ.comp (constVecAlgebraIso N).hom.hom.hom
  left_inv φ := AlgHom.ext fun x => congrArg φ
    (congrArg (fun (m : constVecAlgebra N ⟶ constVecAlgebra N) => m.hom.hom x)
      (constVecAlgebraIso N).hom_inv_id)
  right_inv ψ := AlgHom.ext fun x => congrArg ψ
    (congrArg (fun (m : CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) => m.hom.hom x)
      (constVecAlgebraIso N).inv_hom_id)

/-- **[3c-A]** The concrete (counit-free) index-read of a `ℚ̄`-point of the constant
vector scheme: the evaluation index of its algebra reading through the split-algebra
identification. -/
noncomputable def constVecIndexRead (N : ℕ) [NeZero N] :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of (constVecAlgebra N : Type 0)) //
      h ≫ constVecSchemeπ N =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ (Fin 2 → ZMod N) :=
  (((specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
      (AlgebraicClosure ℚ)).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)).trans
    (precompCvIsoEquiv N)).trans
    (piAlgHomEquiv ℚ (Fin 2 → ZMod N) (SeparableClosure ℚ))

/-- **[3c-A]** The read-correction bijection: the abstract counit-read measured
against the concrete index-read. -/
noncomputable def readCorrection (N : ℕ) [NeZero N] :
    (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) :=
  (constVecIndexRead N).symm.trans (constVecPointsEquiv N)

/-- **[3c-A]** The inverse correction as an endomorphism of the trivial Galois set
(every function is equivariant for the trivial action). -/
noncomputable def corrMor (N : ℕ) [NeZero N] :
    constVecContAction N ⟶ constVecContAction N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (readCorrection N).symm
      comm := fun σ => FintypeCat.hom_ext _ _ fun v => rfl }

/-- The forward correction (the inverse morphism). -/
noncomputable def corrMorInv (N : ℕ) [NeZero N] :
    constVecContAction N ⟶ constVecContAction N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (readCorrection N)
      comm := fun σ => FintypeCat.hom_ext _ _ fun v => rfl }

theorem corrMor_corrMorInv (N : ℕ) [NeZero N] :
    corrMor N ≫ corrMorInv N = 𝟙 _ := by
  ext v : 3
  exact (readCorrection N).apply_symm_apply v

theorem corrMorInv_corrMor (N : ℕ) [NeZero N] :
    corrMorInv N ≫ corrMor N = 𝟙 _ := by
  ext v : 3
  exact (readCorrection N).symm_apply_apply v

/-- **[3c-A]** The correction transported to the constant-vector algebra. -/
noncomputable def corrAlgHom (N : ℕ) [NeZero N] :
    constVecAlgebra N ⟶ constVecAlgebra N :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (corrMor N)).unop

noncomputable def corrAlgHomInv (N : ℕ) [NeZero N] :
    constVecAlgebra N ⟶ constVecAlgebra N :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (corrMorInv N)).unop

theorem corrAlgHomInv_corrAlgHom (N : ℕ) [NeZero N] :
    corrAlgHomInv N ≫ corrAlgHom N = 𝟙 _ :=
  congrArg Quiver.Hom.unop
    ((((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
        _ _).symm).trans
      ((congrArg
        (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
        (corrMor_corrMorInv N)).trans
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_id _)))

theorem corrAlgHom_corrAlgHomInv (N : ℕ) [NeZero N] :
    corrAlgHom N ≫ corrAlgHomInv N = 𝟙 _ :=
  congrArg Quiver.Hom.unop
    ((((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
        _ _).symm).trans
      ((congrArg
        (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
        (corrMorInv_corrMor N)).trans
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_id _)))

/-- **[3c-A]** The correction as a scheme automorphism of the constant vector
scheme. -/
noncomputable def corrSchemeIso (N : ℕ) [NeZero N] :
    constVecScheme N ≅ constVecScheme N where
  hom := Spec.map (CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (corrAlgHomInv N).hom.hom.toRingHom)
  hom_inv_id :=
    (AlgebraicGeometry.Spec.map_comp _ _).symm.trans
      ((congrArg AlgebraicGeometry.Spec.map
        (congrArg (fun (f : constVecAlgebra N ⟶ constVecAlgebra N) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          (corrAlgHomInv_corrAlgHom N))).trans
        (AlgebraicGeometry.Spec.map_id _))
  inv_hom_id :=
    (AlgebraicGeometry.Spec.map_comp _ _).symm.trans
      ((congrArg AlgebraicGeometry.Spec.map
        (congrArg (fun (f : constVecAlgebra N ⟶ constVecAlgebra N) =>
          CommRingCat.ofHom f.hom.hom.toRingHom)
          (corrAlgHom_corrAlgHomInv N))).trans
        (AlgebraicGeometry.Spec.map_id _))

/-- **[3c-A]** The correction lies over `Spec ℚ`. -/
theorem corrSchemeIso_π (N : ℕ) [NeZero N] :
    (corrSchemeIso N).hom ≫ constVecSchemeπ N = constVecSchemeπ N := by
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  exact congrArg AlgebraicGeometry.Spec.map (by
    ext r
    exact (corrAlgHom N).hom.hom.commutes r)

/-- **[3c-A]** THE PIN: the abstract counit-read of a corrected point is the concrete
index-read of the point (counit-naturality at the transported correction plus the
correction's defining triangle). -/
theorem constVecPointsEquiv_corrScheme (N : ℕ) [NeZero N]
    (pt : Spec (.of (AlgebraicClosure ℚ)) ⟶
      Spec (CommRingCat.of (constVecAlgebra N : Type 0)))
    (hpt : pt ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    constVecPointsEquiv N ⟨pt ≫ (corrSchemeIso N).hom, Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (pt ≫ ·) (corrSchemeIso_π N)) hpt)⟩ =
      constVecIndexRead N ⟨pt, hpt⟩ := by
  have hL : Spec.preimage (pt ≫ (corrSchemeIso N).hom) =
      CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom ≫ Spec.preimage pt := by
    apply Spec.map_injective
    rw [AlgebraicGeometry.Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    rfl
  have hAcorr : specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
      (AlgebraicClosure ℚ)
      ⟨pt ≫ (corrSchemeIso N).hom, Eq.trans (Category.assoc _ _ _)
        (Eq.trans (congrArg (pt ≫ ·) (corrSchemeIso_π N)) hpt)⟩ =
      (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0) (AlgebraicClosure ℚ)
        ⟨pt, hpt⟩).comp (corrAlgHom N).hom.hom := by
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hL
  have hxcorr : (AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ))
      sepClosureQAlgEquiv.symm)
      (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0) (AlgebraicClosure ℚ)
        ⟨pt ≫ (corrSchemeIso N).hom, Eq.trans (Category.assoc _ _ _)
          (Eq.trans (congrArg (pt ≫ ·) (corrSchemeIso_π N)) hpt)⟩) =
      ((AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
        (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
          (AlgebraicClosure ℚ) ⟨pt, hpt⟩)).comp
        (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (corrMor N)).unop.hom.hom) := by
    rw [hAcorr]
    exact AlgHom.ext fun w => rfl
  refine Eq.trans (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (constVecContAction N)) hxcorr) ?_
  refine Eq.trans (pointsEquivOfContAction_map (corrMor N)
    ((AlgEquiv.arrowCongr (AlgEquiv.refl (R := ℚ)) sepClosureQAlgEquiv.symm)
      (specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
        (AlgebraicClosure ℚ) ⟨pt, hpt⟩))) ?_
  exact congrArg (constVecIndexRead N)
    (Equiv.symm_apply_apply (constVecPointsEquiv N) ⟨pt, hpt⟩)

/-- **[3c-B3]** The concrete index-read of a constant `ℚ̄`-point is its index. -/
theorem constVecIndexRead_const (N : ℕ) [NeZero N] (u : Fin 2 → ZMod N)
    (hov : (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
      (constVecSchemeIso N).hom) ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    constVecIndexRead N ⟨_, hov⟩ = u := by
  have hpre : Spec.preimage (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
      (constVecSchemeIso N).hom) =
      CommRingCat.ofHom (constVecAlgebraIso N).hom.hom.hom.toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom
          (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) u) ≫
        CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    apply Spec.map_injective
    rw [Spec.map_preimage]
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ·)
      (constSchemeSpecIso_ι_hom_assoc (CommRingCat.of ℚ) (Fin 2 → ZMod N) u
        (constVecSpecIso N).hom)) ?_
    refine Eq.trans (congrArg (fun t => Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom
          (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) u)) ≫ t)
      (show (constVecSpecIso N).hom = Spec.map (CommRingCat.ofHom
        (constVecAlgebraIso N).hom.hom.hom.toRingHom) from rfl)) ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ·)
      (AlgebraicGeometry.Spec.map_comp _ _).symm) ?_
    exact (AlgebraicGeometry.Spec.map_comp _ _).symm
  refine (piAlgHomIndex_unique _ ?_).symm
  refine Eq.trans (congrArg (fun z => sepClosureQAlgEquiv.symm z)
    (congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
        CommRingCat.of (AlgebraicClosure ℚ) =>
      q.hom ((constVecAlgebraIso N).inv.hom.hom (Pi.single u 1))) hpre)) ?_
  refine Eq.trans (congrArg (fun z => sepClosureQAlgEquiv.symm
      (algebraMap ℚ (AlgebraicClosure ℚ) ((Pi.evalRingHom
        (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) u) z)))
    (congrArg (fun (m : CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) =>
      m.hom.hom (Pi.single u (1 : ℚ))) (constVecAlgebraIso N).inv_hom_id)) ?_
  show sepClosureQAlgEquiv.symm ((algebraMap ℚ (AlgebraicClosure ℚ))
      ((Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) u)
        (Pi.single u 1))) = 1
  rw [show (Pi.evalRingHom (fun _ : (Fin 2 → ZMod N) => (ℚ : Type 0)) u)
      (Pi.single u (1 : ℚ)) = 1 from Pi.single_eq_same u 1]
  rw [map_one, map_one]

/-- **[T-EQ-2 P0]** The scheme-action equiv is the vector `smul`. -/
theorem glEquiv_eq_smul (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    EllipticCurve.glEquiv γ v = γ • v := rfl

/-- **[T-EQ-2 P1]** The `γ`-coordinate change on the split `Pi`-algebra:
precomposition with the `smul` (`f ↦ f ∘ (γ • ·)`). -/
noncomputable def piGLAlgHom (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ((Fin 2 → ZMod N) → ℚ) →ₐ[ℚ] ((Fin 2 → ZMod N) → ℚ) where
  toFun f := fun v => f (γ • v)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem piGLAlgHom_apply (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (f : (Fin 2 → ZMod N) → ℚ) (v : Fin 2 → ZMod N) :
    piGLAlgHom N γ f v = f (γ • v) := rfl

/-- **[T-EQ-2 P1]** The evaluation index of a `γ`-precomposed `AlgHom` is the
`γ`-translate of its index. -/
theorem piAlgHomIndex_piGL (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (φ : ((Fin 2 → ZMod N) → ℚ) →ₐ[ℚ] SeparableClosure ℚ) :
    piAlgHomIndex (φ.comp (piGLAlgHom N γ)) = γ • piAlgHomIndex φ := by
  classical
  refine (piAlgHomIndex_unique _ ?_).symm
  show φ (piGLAlgHom N γ (Pi.single (γ • piAlgHomIndex φ) 1)) = 1
  rw [show piGLAlgHom N γ (Pi.single (γ • piAlgHomIndex φ) 1) =
      Pi.single (piAlgHomIndex φ) 1 from funext fun v => by
    rw [piGLAlgHom_apply]
    by_cases hv : v = piAlgHomIndex φ
    · subst hv
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne
        (fun hc => hv (MulAction.injective γ hc))]]
  exact piAlgHomIndex_spec φ

/-- **[T-EQ-2 P1-a]** The correspondence square for the coordinate change: the
functor-image of the `Pi`-precomposition matches the set-level `γ`-action through
the split identification (`muNRootsCorrespondence_pow` technique). -/
theorem constVecCorrespondence_GL (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ))) ≫
        (constVecCorrespondenceIso N).hom =
      (constVecCorrespondenceIso N).hom ≫ constVecGLMor N γ := by
  ext φ : 3
  rw [show ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ))) ≫
        (constVecCorrespondenceIso N).hom).hom.hom =
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)))).hom.hom ≫
        (constVecCorrespondenceIso N).hom.hom.hom from rfl,
    show ((constVecCorrespondenceIso N).hom ≫ constVecGLMor N γ).hom.hom =
      (constVecCorrespondenceIso N).hom.hom.hom ≫
        (constVecGLMor N γ).hom.hom from rfl,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    FiniteEtaleGalois.finiteEtaleEquivContAction_functor_map_hom]
  exact piAlgHomIndex_piGL N γ
    (show ((Fin 2 → ZMod N) → ℚ) →ₐ[ℚ] SeparableClosure ℚ from φ)

section GeneralConjugate

/-- Conjugating an endomorphism square through the unit of an equivalence
(abstract, so the heavy instantiations stay out of the defeq paths). -/
theorem equivalence_unit_conjugate_square {C : Type*} [CategoryTheory.Category C]
    {E : Type*} [CategoryTheory.Category E] (e : CategoryTheory.Equivalence C E)
    {X : C} {A : E} (c : e.functor.obj X ≅ A) (f : X ⟶ X) (m : A ⟶ A)
    (hsq : e.functor.map f ≫ c.hom = c.hom ≫ m) :
    f ≫ (e.unitIso.hom.app X ≫ e.inverse.map c.hom) =
      (e.unitIso.hom.app X ≫ e.inverse.map c.hom) ≫ e.inverse.map m := by
  have hnat := e.unitIso.hom.naturality f
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hnat
  calc f ≫ (e.unitIso.hom.app X ≫ e.inverse.map c.hom)
      = (f ≫ e.unitIso.hom.app X) ≫ e.inverse.map c.hom :=
        (Category.assoc _ _ _).symm
    _ = (e.unitIso.hom.app X ≫ e.inverse.map (e.functor.map f)) ≫
          e.inverse.map c.hom := congrArg (· ≫ e.inverse.map c.hom) hnat
    _ = e.unitIso.hom.app X ≫ e.inverse.map (e.functor.map f ≫ c.hom) :=
        (Category.assoc _ _ _).trans
          (congrArg (e.unitIso.hom.app X ≫ ·) (e.inverse.map_comp _ _).symm)
    _ = e.unitIso.hom.app X ≫ e.inverse.map (c.hom ≫ m) :=
        congrArg (fun q => e.unitIso.hom.app X ≫ e.inverse.map q) hsq
    _ = (e.unitIso.hom.app X ≫ e.inverse.map c.hom) ≫ e.inverse.map m :=
        (congrArg (e.unitIso.hom.app X ≫ ·) (e.inverse.map_comp _ _)).trans
          (Category.assoc _ _ _).symm

end GeneralConjugate

/-- [T-EQ-2 b-5 helper] `Spec` of the ring image of a finite-étale-algebra composite
splits. -/
theorem specMap_finiteEtale_comp {A B C : CommAlgCat.FiniteEtale.{0} ℚ}
    (x : A ⟶ B) (y : B ⟶ C) :
    Spec.map (CommRingCat.ofHom ((x ≫ y).hom.hom.toRingHom)) =
      Spec.map (CommRingCat.ofHom y.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom x.hom.hom.toRingHom) := by
  rw [show (x ≫ y).hom.hom.toRingHom =
    (y.hom.hom.toRingHom).comp (x.hom.hom.toRingHom) from rfl,
    CommRingCat.ofHom_comp, Spec.map_comp]

/-- **[T-EQ-2 P1-b]** The transported split identification in composite form
(definitional). -/
theorem constVecAlgebraIso_hom_eq (N : ℕ) [NeZero N] :
    (constVecAlgebraIso N).hom =
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (constVecCorrespondenceIso N).hom).unop ≫
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
        (Opposite.op (CommAlgCat.FiniteEtale.of ℚ
          ((Fin 2 → ZMod N) → ℚ)))).unop := rfl

/-- **[T-EQ-2 P1-b]** The algebra-side coordinate-change square, composite form. -/
theorem constVecGLAlg_square' (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecGLAlg N γ ≫
        (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (constVecCorrespondenceIso N).hom).unop ≫
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
          (Opposite.op (CommAlgCat.FiniteEtale.of ℚ
            ((Fin 2 → ZMod N) → ℚ)))).unop) =
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (constVecCorrespondenceIso N).hom).unop ≫
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
          (Opposite.op (CommAlgCat.FiniteEtale.of ℚ
            ((Fin 2 → ZMod N) → ℚ)))).unop) ≫
        (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) := by
  have hop := equivalence_unit_conjugate_square
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ)
    (constVecCorrespondenceIso N)
    (Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
      CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)))
    (constVecGLMor N γ) (constVecCorrespondence_GL N γ)
  have h2 := congrArg Quiver.Hom.unop hop
  simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc] at h2
  simp only [Category.assoc]
  exact h2.symm

/-- **[T-EQ-2 P1-b]** The algebra-side coordinate-change square, iso form. -/
theorem constVecGLAlg_square (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecGLAlg N γ ≫ (constVecAlgebraIso N).hom =
      (constVecAlgebraIso N).hom ≫
        (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) := by
  rw [constVecAlgebraIso_hom_eq]
  exact constVecGLAlg_square' N γ

/-- **[T-EQ-2 P1-b]** The algebra-side coordinate-change square, inverse form. -/
theorem constVecGLAlg_square_inv (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (constVecAlgebraIso N).inv ≫ constVecGLAlg N γ =
      (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
          CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) ≫
        (constVecAlgebraIso N).inv := by
  rw [Iso.inv_comp_eq]
  calc constVecGLAlg N γ
      = (constVecGLAlg N γ ≫ (constVecAlgebraIso N).hom) ≫
          (constVecAlgebraIso N).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((constVecAlgebraIso N).hom ≫
          (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
              CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ))) ≫
          (constVecAlgebraIso N).inv :=
        congrArg (· ≫ (constVecAlgebraIso N).inv) (constVecGLAlg_square N γ)
    _ = (constVecAlgebraIso N).hom ≫
          (ObjectProperty.homMk (CommAlgCat.ofHom (piGLAlgHom N γ)) :
            CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ) ⟶
              CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) ≫
          (constVecAlgebraIso N).inv := Category.assoc _ _ _

/-- **[T-EQ-2 P1-c]** The Spec-side coordinate-change square against the split
identification. -/
theorem constVecGLScheme_specIso (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    Spec.map (CommRingCat.ofHom (piGLAlgHom N γ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (constVecAlgebraIso N).hom.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom
          (constVecAlgebraIso N).hom.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom
    ((congrArg (fun (m : constVecAlgebra N ⟶
        CommAlgCat.FiniteEtale.of ℚ ((Fin 2 → ZMod N) → ℚ)) =>
      m.hom.hom.toRingHom) (constVecGLAlg_square N γ)).symm))

/-- **[T-EQ-2 d2-core]** The Sigma-side coordinate change transports to the
constant-vector scheme through the split identification: `constGL` becomes
`constVecGLScheme`. -/
theorem constGL_constVecSchemeIso (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (EllipticCurve.constGL (S := Spec (CommRingCat.of ℚ)) γ).hom ≫
        (constVecSchemeIso N).hom =
      (constVecSchemeIso N).hom ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [show (constVecSchemeIso N).hom =
    (constSchemeSpecIso (CommRingCat.of ℚ) (Fin 2 → ZMod N)).hom ≫
      (constVecSpecIso N).hom from rfl]
  simp only [Category.assoc]
  rw [show (EllipticCurve.constGL (S := Spec (CommRingCat.of ℚ)) γ).hom =
    Limits.Sigma.desc (fun a => Limits.Sigma.ι
      (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ))
      (EllipticCurve.glEquiv γ a)) from rfl]
  rw [Limits.Sigma.ι_desc_assoc]
  rw [constSchemeSpecIso_ι_hom_assoc, constSchemeSpecIso_ι_hom_assoc]
  rw [show (constVecSpecIso N).hom = Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).hom.hom.hom.toRingHom) from rfl]
  rw [← constVecGLScheme_specIso N γ]
  rw [← AlgebraicGeometry.Spec.map_comp_assoc]
  refine congrArg (· ≫ Spec.map (CommRingCat.ofHom
    (constVecAlgebraIso N).hom.hom.hom.toRingHom)) ?_
  refine congrArg Spec.map ?_
  rw [← CommRingCat.ofHom_comp]
  rfl

/-- **[T-EQ-2 N-abs]** The abstract counit-read intertwines the coordinate change
(3-layer `wFramesPointsEquiv_rightMul` template). -/
theorem constVecPointsEquiv_GL (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (h : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of (constVecAlgebra N : Type 0)) //
      h ≫ constVecSchemeπ N =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    constVecPointsEquiv N ⟨h.1 ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom), by
      rw [Category.assoc]
      rw [show Spec.map (CommRingCat.ofHom
          (constVecGLAlg N γ).hom.hom.toRingHom) ≫ constVecSchemeπ N =
        constVecSchemeπ N from constVecGLScheme_π N γ]
      exact h.2⟩ =
      γ • constVecPointsEquiv N h := by
  set L1 := specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
    (AlgebraicClosure ℚ) with hL1
  set L2 := AlgEquiv.arrowCongr
    (AlgEquiv.refl (R := ℚ) (A₁ := (constVecAlgebra N : Type 0)))
    sepClosureQAlgEquiv.symm with hL2
  have hA : ∀ hp : (h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap ℚ (constVecAlgebra N : Type 0))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))),
      L1 ⟨h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom), hp⟩ =
        (L1 h).comp (constVecGLAlg N γ).hom.hom := by
    intro hp
    have hpre : Spec.preimage (h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom)) =
        CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
          Spec.preimage h.1 := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hpre
  have hB : ∀ ψ : (constVecAlgebra N : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ,
      L2 (ψ.comp (constVecGLAlg N γ).hom.hom) =
        (L2 ψ).comp (constVecGLAlg N γ).hom.hom := by
    intro ψ
    exact AlgHom.ext fun w => rfl
  have hC : FiniteEtaleGalois.pointsEquivOfContAction ℚ (constVecContAction N)
      ((L2 (L1 h)).comp (constVecGLAlg N γ).hom.hom) =
      γ • FiniteEtaleGalois.pointsEquivOfContAction ℚ (constVecContAction N)
        (L2 (L1 h)) :=
    pointsEquivOfContAction_map (constVecGLMor N γ) (L2 (L1 h))
  refine Eq.trans (congrArg (fun y => FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (constVecContAction N) (L2 y)) (hA _)) ?_
  refine Eq.trans (congrArg (FiniteEtaleGalois.pointsEquivOfContAction ℚ
    (constVecContAction N)) (hB (L1 h))) ?_
  exact hC

/-- **[T-EQ-2 N-idx]** The concrete index-read intertwines the coordinate change
(the `Pi`-side of the pin). -/
theorem constVecIndexRead_GL (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (h : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶
        Spec (CommRingCat.of (constVecAlgebra N : Type 0)) //
      h ≫ constVecSchemeπ N =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    constVecIndexRead N ⟨h.1 ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom), by
      rw [Category.assoc]
      rw [show Spec.map (CommRingCat.ofHom
          (constVecGLAlg N γ).hom.hom.toRingHom) ≫ constVecSchemeπ N =
        constVecSchemeπ N from constVecGLScheme_π N γ]
      exact h.2⟩ =
      γ • constVecIndexRead N h := by
  set L1 := specPointsEquivAlgHom ℚ (constVecAlgebra N : Type 0)
    (AlgebraicClosure ℚ) with hL1
  set L2 := AlgEquiv.arrowCongr
    (AlgEquiv.refl (R := ℚ) (A₁ := (constVecAlgebra N : Type 0)))
    sepClosureQAlgEquiv.symm with hL2
  have hA : ∀ hp : (h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap ℚ (constVecAlgebra N : Type 0))) =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))),
      L1 ⟨h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom), hp⟩ =
        (L1 h).comp (constVecGLAlg N γ).hom.hom := by
    intro hp
    have hpre : Spec.preimage (h.1 ≫ Spec.map (CommRingCat.ofHom
        (constVecGLAlg N γ).hom.hom.toRingHom)) =
        CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
          Spec.preimage h.1 := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    refine AlgHom.ext fun w => ?_
    exact congrArg (fun q : CommRingCat.of (constVecAlgebra N : Type 0) ⟶
      CommRingCat.of (AlgebraicClosure ℚ) => q.hom w) hpre
  have hB : ∀ ψ : (constVecAlgebra N : Type 0) →ₐ[ℚ] AlgebraicClosure ℚ,
      L2 (ψ.comp (constVecGLAlg N γ).hom.hom) =
        (L2 ψ).comp (constVecGLAlg N γ).hom.hom := by
    intro ψ
    exact AlgHom.ext fun w => rfl
  have hP : ∀ ψ : (constVecAlgebra N : Type 0) →ₐ[ℚ] SeparableClosure ℚ,
      precompCvIsoEquiv N (ψ.comp (constVecGLAlg N γ).hom.hom) =
        (precompCvIsoEquiv N ψ).comp (piGLAlgHom N γ) := by
    intro ψ
    refine AlgHom.ext fun w => ?_
    show ψ ((constVecGLAlg N γ).hom.hom ((constVecAlgebraIso N).inv.hom.hom w)) =
      ψ ((constVecAlgebraIso N).inv.hom.hom (piGLAlgHom N γ w))
    refine congrArg ψ ?_
    exact congrArg (fun (m : CommAlgCat.FiniteEtale.of ℚ
        ((Fin 2 → ZMod N) → ℚ) ⟶ constVecAlgebra N) => m.hom.hom w)
      (constVecGLAlg_square_inv N γ)
  refine Eq.trans (congrArg (fun y => piAlgHomEquiv ℚ (Fin 2 → ZMod N)
    (SeparableClosure ℚ) (precompCvIsoEquiv N (L2 y))) (hA _)) ?_
  refine Eq.trans (congrArg (fun y => piAlgHomEquiv ℚ (Fin 2 → ZMod N)
    (SeparableClosure ℚ) (precompCvIsoEquiv N y)) (hB (L1 h))) ?_
  refine Eq.trans (congrArg (piAlgHomEquiv ℚ (Fin 2 → ZMod N)
    (SeparableClosure ℚ)) (hP (L2 (L1 h)))) ?_
  exact piAlgHomIndex_piGL N γ (precompCvIsoEquiv N (L2 (L1 h)))

/-- **[T-EQ-2 rc-comm]** The read-correction commutes with the coordinate change
(both reads intertwine it). -/
theorem readCorrection_smul (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (v : Fin 2 → ZMod N) :
    readCorrection N (γ • v) = γ • readCorrection N v := by
  show constVecPointsEquiv N ((constVecIndexRead N).symm (γ • v)) =
    γ • constVecPointsEquiv N ((constVecIndexRead N).symm v)
  have hidx : (constVecIndexRead N).symm (γ • v) =
      ⟨((constVecIndexRead N).symm v).1 ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom), by
        rw [Category.assoc]
        rw [show Spec.map (CommRingCat.ofHom
            (constVecGLAlg N γ).hom.hom.toRingHom) ≫ constVecSchemeπ N =
          constVecSchemeπ N from constVecGLScheme_π N γ]
        exact ((constVecIndexRead N).symm v).2⟩ := by
    refine (constVecIndexRead N).injective ?_
    rw [Equiv.apply_symm_apply]
    exact ((constVecIndexRead_GL N γ ((constVecIndexRead N).symm v)).trans
      (congrArg (γ • ·) (Equiv.apply_symm_apply _ v))).symm
  rw [hidx]
  exact (constVecPointsEquiv_GL N γ ((constVecIndexRead N).symm v)).trans
    (congrArg (γ • ·) (by
      show constVecPointsEquiv N ((constVecIndexRead N).symm v) = _
      rfl))

/-- **[T-EQ-2 d3]** The correction morphism commutes with the coordinate change. -/
theorem corrMor_constVecGLMor (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    corrMor N ≫ constVecGLMor N γ = constVecGLMor N γ ≫ corrMor N := by
  ext v : 3
  show γ • (readCorrection N).symm v = (readCorrection N).symm (γ • v)
  refine ((readCorrection N).injective ?_).symm
  rw [Equiv.apply_symm_apply, readCorrection_smul, Equiv.apply_symm_apply]

/-- **[T-EQ-2 d3]** The algebra-level commutation. -/
theorem corrAlgHom_constVecGLAlg (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    constVecGLAlg N γ ≫ corrAlgHom N = corrAlgHom N ≫ constVecGLAlg N γ := by
  show ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (constVecGLMor N γ)).unop ≫
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (corrMor N)).unop =
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (corrMor N)).unop ≫
    ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
      (constVecGLMor N γ)).unop
  rw [← CategoryTheory.unop_comp, ← CategoryTheory.unop_comp]
  refine congrArg Quiver.Hom.unop ?_
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (corrMor_constVecGLMor N γ)

/-- **[T-EQ-2 d3]** The scheme-level commutation: the read-correction commutes with
the coordinate change on the constant-vector scheme. -/
theorem corrSchemeIso_constVecGL (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) ≫
        (corrSchemeIso N).hom =
      (corrSchemeIso N).hom ≫
        Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) := by
  show Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (corrAlgHom N).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  refine congrArg Spec.map ?_
  show CommRingCat.ofHom ((corrAlgHom N ≫ constVecGLAlg N γ).hom.hom.toRingHom) =
    CommRingCat.ofHom ((constVecGLAlg N γ ≫ corrAlgHom N).hom.hom.toRingHom)
  exact congrArg (fun (m : constVecAlgebra N ⟶ constVecAlgebra N) =>
    CommRingCat.ofHom m.hom.hom.toRingHom) (corrAlgHom_constVecGLAlg N γ).symm

/-- **[T-EQ-2 d1]** The coordinate change lies over the constant-scheme
projection. -/
theorem constGL_constSchemeπ (S : Scheme.{0}) (N : ℕ) [NeZero N]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (EllipticCurve.constGL (S := S) γ).hom ≫
        constSchemeπ S (Fin 2 → ZMod N) =
      constSchemeπ S (Fin 2 → ZMod N) := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [show (EllipticCurve.constGL (S := S) γ).hom = Limits.Sigma.desc (fun a =>
    Limits.Sigma.ι (fun _ : (Fin 2 → ZMod N) => S)
      (EllipticCurve.glEquiv γ a)) from rfl]
  rw [Limits.Sigma.ι_desc_assoc]
  show Limits.Sigma.ι (fun _ : (Fin 2 → ZMod N) => S)
      (EllipticCurve.glEquiv γ a) ≫ Limits.Sigma.desc (fun _ => 𝟙 S) =
    Limits.Sigma.ι (fun _ : (Fin 2 → ZMod N) => S) a ≫
      Limits.Sigma.desc (fun _ => 𝟙 S)
  rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]

/-- **[T-EQ-2 d1]** The coordinate change commutes with the base-change
comparison. -/
theorem constGL_mapAlong {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (N : ℕ) [NeZero N] (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (EllipticCurve.constGL (S := T) γ).hom ≫
        constSchemeMapAlong sT (Fin 2 → ZMod N) =
      constSchemeMapAlong sT (Fin 2 → ZMod N) ≫
        (EllipticCurve.constGL (S := Spec (CommRingCat.of ℚ)) γ).hom := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [show (EllipticCurve.constGL (S := T) γ).hom = Limits.Sigma.desc (fun a =>
    Limits.Sigma.ι (fun _ : (Fin 2 → ZMod N) => T)
      (EllipticCurve.glEquiv γ a)) from rfl]
  rw [Limits.Sigma.ι_desc_assoc, ι_constSchemeMapAlong,
    ι_constSchemeMapAlong_assoc]
  rw [show (EllipticCurve.constGL (S := Spec (CommRingCat.of ℚ)) γ).hom =
    Limits.Sigma.desc (fun a => Limits.Sigma.ι
      (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ))
      (EllipticCurve.glEquiv γ a)) from rfl]
  rw [Limits.Sigma.ι_desc]

/-- **[T-EQ-2 d1]** The C-leg square: the coordinate change transports through the
base-change comparison isomorphism into the frame of the pinned trivialization. -/
theorem constGL_isoPullback {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (N : ℕ) [NeZero N] (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (EllipticCurve.constGL (S := T) γ).hom ≫
        (isPullback_constSchemeMapAlong sT
          (Fin 2 → ZMod N)).flip.isoPullback.hom =
      (isPullback_constSchemeMapAlong sT
          (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
        pullback.map sT (constSchemeπ (Spec (CommRingCat.of ℚ))
            (Fin 2 → ZMod N)) sT
          (constSchemeπ (Spec (CommRingCat.of ℚ)) (Fin 2 → ZMod N))
          (𝟙 T) (EllipticCurve.constGL
            (S := Spec (CommRingCat.of ℚ)) γ).hom
          (𝟙 (Spec (CommRingCat.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id, constGL_constSchemeπ]) := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((EllipticCurve.constGL (S := T) γ).hom ≫ ·)
      ((isPullback_constSchemeMapAlong sT
        (Fin 2 → ZMod N)).flip.isoPullback_hom_fst)) ?_
    refine Eq.trans (constGL_constSchemeπ T N γ) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((isPullback_constSchemeMapAlong sT
        (Fin 2 → ZMod N)).flip.isoPullback.hom ≫ ·)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
    exact (isPullback_constSchemeMapAlong sT
      (Fin 2 → ZMod N)).flip.isoPullback_hom_fst
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((EllipticCurve.constGL (S := T) γ).hom ≫ ·)
      ((isPullback_constSchemeMapAlong sT
        (Fin 2 → ZMod N)).flip.isoPullback_hom_snd)) ?_
    refine Eq.trans (constGL_mapAlong sT N γ) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((isPullback_constSchemeMapAlong sT
        (Fin 2 → ZMod N)).flip.isoPullback.hom ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ (EllipticCurve.constGL
      (S := Spec (CommRingCat.of ℚ)) γ).hom)
      ((isPullback_constSchemeMapAlong sT
        (Fin 2 → ZMod N)).flip.isoPullback_hom_snd)

/-- **[T-EQ-2 d2]** A component square over `Spec ℚ` transports to the `T`-pullback
frames of the pinned trivialization (generic: both twists on the second factor). -/
theorem pullback_map_snd_square {T A B : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    {πA : A ⟶ Spec (CommRingCat.of ℚ)} {πB : B ⟶ Spec (CommRingCat.of ℚ)}
    (u : A ⟶ A) (v : A ⟶ B) (u' : B ⟶ B)
    (hu : u ≫ πA = πA) (hv : v ≫ πB = πA) (hu' : u' ≫ πB = πB)
    (hsq : u ≫ v = v ≫ u') :
    pullback.map sT πA sT πA (𝟙 T) u (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hu]) ≫
      pullback.map sT πA sT πB (𝟙 T) v (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hv]) =
      pullback.map sT πA sT πB (𝟙 T) v (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hv]) ≫
      pullback.map sT πB sT πB (𝟙 T) u' (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hu']) := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT πA sT πA (𝟙 T) u
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
    refine Eq.trans ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT πA sT πB (𝟙 T) v
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT πA sT πA (𝟙 T) u
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ v) (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.snd sT πA ≫ ·) hsq) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT πA sT πB (𝟙 T) v
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ u') (pullback.lift_snd _ _ _)) ?_
    exact Category.assoc _ _ _

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

/-- **[T-EQ-2 b-4]** The tensor vector twist under the left cofan injection is the
coordinate change. -/
theorem tensorVecTwistAlg_includeLeft (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (constVecAlgebra N : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) ≫ tensorVecTwistAlg D γ =
      constVecGLAlg N γ ≫ ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ))) := by
  have hE : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdVecTwist D γ) ≫ (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D)) =
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D)) ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (constVecGLMor N γ) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun m => (frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m)
      (frameProdVecTwist_fst D γ)
  refine Eq.trans (congrArg (· ≫ tensorVecTwistAlg D γ)
    (frameProdAlgebraIso_inv_left D).symm) ?_
  refine Eq.trans (congrArg Quiver.Hom.unop hE) ?_
  exact congrArg (constVecGLAlg N γ ≫ ·) (frameProdAlgebraIso_inv_left D)

/-- **[T-EQ-2 b-4]** The tensor vector twist fixes the right cofan injection. -/
theorem tensorVecTwistAlg_includeRight (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) ≫ tensorVecTwistAlg D γ =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ))) := by
  have hE : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdVecTwist D γ) ≫ (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D)) =
      (frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (fun m => (frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m)
      (frameProdVecTwist_snd D γ)
  refine Eq.trans (congrArg (· ≫ tensorVecTwistAlg D γ)
    (frameProdAlgebraIso_inv_right D).symm) ?_
  exact Eq.trans (congrArg Quiver.Hom.unop hE) (frameProdAlgebraIso_inv_right D)

/-- **[T-EQ-2 b-4]** The tensor frame twist fixes the left cofan injection. -/
theorem tensorFrameTwistAlg_includeLeft (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (constVecAlgebra N : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) ≫ tensorFrameTwistAlg D γ =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ))) := by
  have hE : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdFrameTwist D γ) ≫ (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D)) =
      (frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (fun m => (frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m)
      (frameProdFrameTwist_fst D γ)
  refine Eq.trans (congrArg (· ≫ tensorFrameTwistAlg D γ)
    (frameProdAlgebraIso_inv_left D).symm) ?_
  exact Eq.trans (congrArg Quiver.Hom.unop hE) (frameProdAlgebraIso_inv_left D)

/-- **[T-EQ-2 b-4]** The tensor frame twist under the right cofan injection is the
right translation. -/
theorem tensorFrameTwistAlg_includeRight (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) ≫ tensorFrameTwistAlg D γ =
      wFramesRightMulAlg D γ ≫ ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ))) := by
  have hE : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameProdFrameTwist D γ) ≫ (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D)) =
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D)) ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameRightMulMor D γ) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun m => (frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m)
      (frameProdFrameTwist_snd D γ)
  refine Eq.trans (congrArg (· ≫ tensorFrameTwistAlg D γ)
    (frameProdAlgebraIso_inv_right D).symm) ?_
  refine Eq.trans (congrArg Quiver.Hom.unop hE) ?_
  exact congrArg (wFramesRightMulAlg D γ ≫ ·) (frameProdAlgebraIso_inv_right D)



/-- **[T-EQ-2 b-5]** The vector twist through the `Spec`-tensor identification. -/
theorem pullbackSpecIso_vecTwist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).inv ≫
      pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (constVecGLScheme N γ) (𝟙 (wFrames D))
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, constVecGLScheme_π])
        (by rw [Category.comp_id, Category.id_comp]) =
      Spec.map (CommRingCat.ofHom (tensorVecTwistAlg D γ).hom.hom.toRingHom) ≫
        (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).inv := by
  have hRL : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        (constVecAlgebra N : Type 0) →+* TensorProduct ℚ
          (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)) ≫
      CommRingCat.ofHom (tensorVecTwistAlg D γ).hom.hom.toRingHom =
      CommRingCat.ofHom (constVecGLAlg N γ).hom.hom.toRingHom ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun m => CommRingCat.ofHom m.hom.hom.toRingHom)
      (tensorVecTwistAlg_includeLeft D γ)
  have hRR : CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ] TensorProduct ℚ
          (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).toRingHom) ≫
      CommRingCat.ofHom (tensorVecTwistAlg D γ).hom.hom.toRingHom =
      CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ] TensorProduct ℚ
            (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg (fun m => CommRingCat.ofHom m.hom.hom.toRingHom)
      (tensorVecTwistAlg_includeRight D γ)
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ?_).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst _ _)
        rfl)).symm
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ constVecGLScheme N γ)
      (AlgebraicGeometry.pullbackSpecIso_inv_fst ℚ _ _)) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
    refine Eq.trans (congrArg Spec.map hRL.symm) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _) ?_
    exact (congrArg (Spec.map (CommRingCat.ofHom
      (tensorVecTwistAlg D γ).hom.hom.toRingHom) ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_fst ℚ _ _)).symm.trans
      (Category.assoc _ _ _).symm
  · refine ((Category.assoc _ _ _).trans ?_)
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      ((pullback.lift_snd _ _ _).trans (Category.comp_id _))) ?_
    refine Eq.trans (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ _ _) ?_
    refine Eq.trans (congrArg Spec.map hRR.symm) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _) ?_
    exact ((congrArg (Spec.map (CommRingCat.ofHom
      (tensorVecTwistAlg D γ).hom.hom.toRingHom) ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ _ _)).symm).trans
      (Category.assoc _ _ _).symm

/-- **[T-EQ-2 b-5]** The frame twist through the `Spec`-tensor identification. -/
theorem pullbackSpecIso_frameTwist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).inv ≫
      pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (𝟙 (constVecScheme N)) (wFramesRightMul D γ)
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, wFramesRightMul_π]) =
      Spec.map (CommRingCat.ofHom (tensorFrameTwistAlg D γ).hom.hom.toRingHom) ≫
        (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).inv := by
  have hRL : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        (constVecAlgebra N : Type 0) →+* TensorProduct ℚ
          (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)) ≫
      CommRingCat.ofHom (tensorFrameTwistAlg D γ).hom.hom.toRingHom =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg (fun m => CommRingCat.ofHom m.hom.hom.toRingHom)
      (tensorFrameTwistAlg_includeLeft D γ)
  have hRR : CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ] TensorProduct ℚ
          (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).toRingHom) ≫
      CommRingCat.ofHom (tensorFrameTwistAlg D γ).hom.hom.toRingHom =
      CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight :
            (wFramesAlgebra D : Type 0) →ₐ[ℚ] TensorProduct ℚ
              (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0)).toRingHom) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun m => CommRingCat.ofHom m.hom.hom.toRingHom)
      (tensorFrameTwistAlg_includeRight D γ)
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ?_)
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
    refine Eq.trans (AlgebraicGeometry.pullbackSpecIso_inv_fst ℚ _ _) ?_
    refine Eq.trans (congrArg Spec.map hRL.symm) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _) ?_
    exact ((congrArg (Spec.map (CommRingCat.ofHom
      (tensorFrameTwistAlg D γ).hom.hom.toRingHom) ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_fst ℚ _ _)).symm).trans
      (Category.assoc _ _ _).symm
  · refine ((Category.assoc _ _ _).trans ?_)
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ wFramesRightMul D γ)
      (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ _ _)) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
    refine Eq.trans (congrArg Spec.map hRR.symm) ?_
    refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _) ?_
    exact ((congrArg (Spec.map (CommRingCat.ofHom
      (tensorFrameTwistAlg D γ).hom.hom.toRingHom) ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ _ _)).symm).trans
      (Category.assoc _ _ _).symm

/-- **[T-EQ-2 b-5]** The contracted-product relation for the universal-frame
evaluation: changing coordinates by `γ` equals right-translating the frame by `γ`. -/
theorem frameEval_twist (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (constVecGLScheme N γ) (𝟙 (wFrames D))
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, constVecGLScheme_π])
        (by rw [Category.comp_id, Category.id_comp]) ≫ frameEval D =
      pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (𝟙 (constVecScheme N)) (wFramesRightMul D γ)
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, wFramesRightMul_π]) ≫ frameEval D := by
  have hIso : ∀ (m : pullback (constVecSchemeπ N) (wFramesπ D) ⟶
        pullback (constVecSchemeπ N) (wFramesπ D))
      (a : CommRingCat.of (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)) ⟶
        CommRingCat.of (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0))),
      (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).inv ≫ m =
        Spec.map a ≫
          (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)).inv →
      m ≫ (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).hom =
        (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).hom ≫ Spec.map a := by
    intro m a h
    have hA : m = (AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
        (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0)).inv ≫ m :=
      (Iso.hom_inv_id_assoc _ _).symm
    have hB := congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·) h
    refine Eq.trans (congrArg (· ≫ (AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom)
      (hA.trans hB)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact (congrArg (Spec.map a ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _)
  have hV := hIso _
    (CommRingCat.ofHom (tensorVecTwistAlg D γ).hom.hom.toRingHom)
    (pullbackSpecIso_vecTwist D γ)
  have hF := hIso _
    (CommRingCat.ofHom (tensorFrameTwistAlg D γ).hom.hom.toRingHom)
    (pullbackSpecIso_frameTwist D γ)
  show _ ≫ ((AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
      (wFramesAlgebra D : Type 0)).hom ≫
      Spec.map (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)) =
    _ ≫ ((AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
      (wFramesAlgebra D : Type 0)).hom ≫
      Spec.map (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ Spec.map
    (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)) hV) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.symm ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ Spec.map
    (CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom)) hF) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
    (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·) ?_
  refine Eq.trans (specMap_finiteEtale_comp
    (frameEvalAlgHom D) (tensorFrameTwistAlg D γ)).symm ?_
  refine Eq.trans (congrArg (fun m => Spec.map
    (CommRingCat.ofHom m.hom.hom.toRingHom))
    (frameEvalAlgHom_twist D γ).symm) ?_
  exact specMap_finiteEtale_comp (frameEvalAlgHom D) (tensorVecTwistAlg D γ)

/-- **[asm-2b-iv]** The co-evaluation comultiplication: the finite étale algebra map
corresponding to the co-evaluation (mirror of `frameEvalAlgHom`). -/
noncomputable def frameCoevalAlgHom (D : GaloisRepData N) :
    constVecAlgebra N ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D)
      (wFramesAlgebra D) :=
  ((rhoFrameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (frameCoevalMor D)).unop

/-- **[asm-2b-iv]** The shear comultiplication: the algebra map of the transported
shear, from the `ρ`-mixed tensor algebra to the plain mixed tensor algebra. -/
noncomputable def frameShearAlgHom (D : GaloisRepData N) :
    FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (wFramesAlgebra D) ⟶
      FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) :=
  ((frameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (frameShearMor D) ≫
    (rhoFrameProdAlgebraIso D).hom).unop

/-- **[asm-2b-iv]** The co-shear comultiplication (mirror). -/
noncomputable def frameCoshearAlgHom (D : GaloisRepData N) :
    FiniteEtaleGalois.tensorObj (constVecAlgebra N) (wFramesAlgebra D) ⟶
      FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (wFramesAlgebra D) :=
  ((rhoFrameProdAlgebraIso D).inv ≫
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map (frameCoshearMor D) ≫
    (frameProdAlgebraIso D).hom).unop

/-- **[asm-2b-iv]** The co-evaluation at the scheme level:
`V_ρ ×_ℚ Isom((ℤ/N)², V_ρ) ⟶ (ℤ/N)²_ℚ`, `(w, A) ↦ A⁻¹·w` (mirror of `frameEval`). -/
noncomputable def frameCoeval (D : GaloisRepData N) :
    pullback (vRhoπ D) (wFramesπ D) ⟶ constVecScheme N :=
  (AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
    (wFramesAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (frameCoevalAlgHom D).hom.hom.toRingHom)

/-- **[asm-2b-iv]** The co-evaluation lies over the `ρ`-side projection (mirror of
`frameEval_π`). -/
theorem frameCoeval_π (D : GaloisRepData N) :
    frameCoeval D ≫ constVecSchemeπ N =
      pullback.fst (vRhoπ D) (wFramesπ D) ≫ vRhoπ D := by
  have hcomp : CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0)) ≫
      CommRingCat.ofHom (frameCoevalAlgHom D).hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap ℚ (FiniteEtaleGalois.tensorObj
        (vRhoAlgebra D) (wFramesAlgebra D) : Type 0)) := by
    ext r
    exact (frameCoevalAlgHom D).hom.hom.commutes r
  show ((AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (frameCoevalAlgHom D).hom.hom.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (constVecAlgebra N : Type 0))) = _
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (Spec.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun f => (AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map f) hcomp) ?_
  have hfactor : CommRingCat.ofHom (algebraMap ℚ (FiniteEtaleGalois.tensorObj
      (vRhoAlgebra D) (wFramesAlgebra D) : Type 0)) =
      CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0)) ≫
      CommRingCat.ofHom (algebraMap (vRhoAlgebra D : Type 0)
        (TensorProduct ℚ (vRhoAlgebra D : Type 0)
          (wFramesAlgebra D : Type 0))) := by
    ext r
    exact (IsScalarTower.algebraMap_apply ℚ (vRhoAlgebra D : Type 0)
      (TensorProduct ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)) r)
  refine Eq.trans (congrArg (fun f => (AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map f) hfactor) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (Spec.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (vRhoAlgebra D : Type 0))))
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0))

/-- **[asm-2b-iv]** The evaluation-with-frame pairing `(v, A) ↦ (A·v, A)` at the
scheme level. -/
noncomputable def framePairEval (D : GaloisRepData N) :
    pullback (constVecSchemeπ N) (wFramesπ D) ⟶ pullback (vRhoπ D) (wFramesπ D) :=
  pullback.lift (frameEval D) (pullback.snd _ _)
    (by rw [frameEval_π, pullback.condition])

/-- **[asm-2b-iv]** The co-evaluation-with-frame pairing `(w, A) ↦ (A⁻¹·w, A)` at the
scheme level. -/
noncomputable def framePairCoeval (D : GaloisRepData N) :
    pullback (vRhoπ D) (wFramesπ D) ⟶ pullback (constVecSchemeπ N) (wFramesπ D) :=
  pullback.lift (frameCoeval D) (pullback.snd _ _)
    (by rw [frameCoeval_π, pullback.condition])

@[reassoc]
theorem framePairEval_fst (D : GaloisRepData N) :
    framePairEval D ≫ pullback.fst (vRhoπ D) (wFramesπ D) = frameEval D :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem framePairEval_snd (D : GaloisRepData N) :
    framePairEval D ≫ pullback.snd (vRhoπ D) (wFramesπ D) =
      pullback.snd (constVecSchemeπ N) (wFramesπ D) :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem framePairCoeval_fst (D : GaloisRepData N) :
    framePairCoeval D ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) =
      frameCoeval D :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem framePairCoeval_snd (D : GaloisRepData N) :
    framePairCoeval D ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D) =
      pullback.snd (vRhoπ D) (wFramesπ D) :=
  pullback.lift_snd _ _ _

/-- **[asm-2b-v]** The shear comultiplication eats the left injection to the
evaluation comultiplication. -/
theorem frameShearAlgHom_inl (D : GaloisRepData N) :
    ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
        (vRhoAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (vRhoAlgebra D : Type 0)
            (wFramesAlgebra D : Type 0))) ≫ frameShearAlgHom D =
      frameEvalAlgHom D := by
  have hop : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameShearMor D) ≫
      (rhoFrameProdAlgebraIso D).hom) ≫
      ((rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (rhoFrameProdFst D)) =
      (frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameEvalMor D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((frameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameShearMor_fst D)))
  exact (congrArg (· ≫ frameShearAlgHom D)
    (rhoFrameProdAlgebraIso_inv_left D).symm).trans (congrArg Quiver.Hom.unop hop)

/-- **[asm-2b-v]** The shear comultiplication eats the right injection to the right
injection. -/
theorem frameShearAlgHom_inr (D : GaloisRepData N) :
    ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (vRhoAlgebra D : Type 0)
            (wFramesAlgebra D : Type 0))) ≫ frameShearAlgHom D =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hop : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameShearMor D) ≫
      (rhoFrameProdAlgebraIso D).hom) ≫
      ((rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (rhoFrameProdSnd D)) =
      (frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((frameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameShearMor_snd D)))
  exact (congrArg (· ≫ frameShearAlgHom D)
    (rhoFrameProdAlgebraIso_inv_right D).symm).trans
    ((congrArg Quiver.Hom.unop hop).trans (frameProdAlgebraIso_inv_right D))

/-- **[asm-2b-v]** The co-shear comultiplication eats the left injection to the
co-evaluation comultiplication. -/
theorem frameCoshearAlgHom_inl (D : GaloisRepData N) :
    ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
        (constVecAlgebra N : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0))) ≫ frameCoshearAlgHom D =
      frameCoevalAlgHom D := by
  have hop : ((rhoFrameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameCoshearMor D) ≫
      (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D)) =
      (rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameCoevalMor D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameCoshearMor_fst D)))
  exact (congrArg (· ≫ frameCoshearAlgHom D)
    (frameProdAlgebraIso_inv_left D).symm).trans (congrArg Quiver.Hom.unop hop)

/-- **[asm-2b-v]** The co-shear comultiplication eats the right injection to the
right injection. -/
theorem frameCoshearAlgHom_inr (D : GaloisRepData N) :
    ObjectProperty.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0))) ≫ frameCoshearAlgHom D =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ℚ) :
          (wFramesAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (vRhoAlgebra D : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hop : ((rhoFrameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameCoshearMor D) ≫
      (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdSnd D)) =
      (rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (rhoFrameProdSnd D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameCoshearMor_snd D)))
  exact (congrArg (· ≫ frameCoshearAlgHom D)
    (frameProdAlgebraIso_inv_right D).symm).trans
    ((congrArg Quiver.Hom.unop hop).trans (rhoFrameProdAlgebraIso_inv_right D))

/-- **[asm-2b-v]** The co-evaluation then the shear is the left injection
(`v = A⁻¹·(A·v)` transported through the correspondence). -/
theorem frameShearAlgHom_coeval (D : GaloisRepData N) :
    frameCoevalAlgHom D ≫ frameShearAlgHom D =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (constVecAlgebra N : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (constVecAlgebra N : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hop : ((frameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameShearMor D) ≫
      (rhoFrameProdAlgebraIso D).hom) ≫
      ((rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameCoevalMor D)) =
      (frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameProdFst D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((frameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameShearMor_coeval D)))
  exact (congrArg Quiver.Hom.unop hop).trans (frameProdAlgebraIso_inv_left D)

/-- **[asm-2b-v]** The evaluation then the co-shear is the left injection
(`w = A·(A⁻¹·w)` transported through the correspondence). -/
theorem frameCoshearAlgHom_eval (D : GaloisRepData N) :
    frameEvalAlgHom D ≫ frameCoshearAlgHom D =
      ObjectProperty.homMk (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) :
          (vRhoAlgebra D : Type 0) →ₐ[ℚ]
            TensorProduct ℚ (vRhoAlgebra D : Type 0)
              (wFramesAlgebra D : Type 0))) := by
  have hop : ((rhoFrameProdAlgebraIso D).inv ≫
      (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (frameCoshearMor D) ≫
      (frameProdAlgebraIso D).hom) ≫
      ((frameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (frameEvalMor D)) =
      (rhoFrameProdAlgebraIso D).inv ≫
        (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (rhoFrameProdFst D) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((rhoFrameProdAlgebraIso D).inv ≫ ·)
      (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp
          _ _).symm.trans
        (congrArg
          (fun t => (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map t)
          (frameCoshearMor_eval D)))
  exact (congrArg Quiver.Hom.unop hop).trans (rhoFrameProdAlgebraIso_inv_left D)

/-- **[asm-2b-v]** The Φ-conjugation: under the tensor identifications, the pairing
`(v, A) ↦ (A·v, A)` is `Spec` of the shear comultiplication. -/
theorem framePairEval_conj (D : GaloisRepData N) :
    (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).inv ≫ framePairEval D =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (frameShearAlgHom D).hom.hom.toRingHom) ≫
      (AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).inv := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (Iso.inv_hom_id_assoc _ _) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_fst' ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).symm)
    refine Eq.trans (congrArg AlgebraicGeometry.Spec.map ?_)
      (AlgebraicGeometry.Spec.map_comp _ _)
    show CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap (vRhoAlgebra D : Type 0)
        (TensorProduct ℚ (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0))) ≫
      CommRingCat.ofHom (frameShearAlgHom D).hom.hom.toRingHom
    ext x
    exact (congrArg (fun m => m.hom.hom x) (frameShearAlgHom_inl D)).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).symm)
    refine Eq.trans (congrArg AlgebraicGeometry.Spec.map ?_)
      (AlgebraicGeometry.Spec.map_comp _ _)
    show CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (vRhoAlgebra D : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom ≫
      CommRingCat.ofHom (frameShearAlgHom D).hom.hom.toRingHom
    ext x
    exact (congrArg (fun m => m.hom.hom x) (frameShearAlgHom_inr D)).symm

/-- **[asm-2b-v]** The Ψ-conjugation: the pairing `(w, A) ↦ (A⁻¹·w, A)` is `Spec` of
the co-shear comultiplication. -/
theorem framePairCoeval_conj (D : GaloisRepData N) :
    (AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).inv ≫ framePairCoeval D =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (frameCoshearAlgHom D).hom.hom.toRingHom) ≫
      (AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).inv := by
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (Iso.inv_hom_id_assoc _ _) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_fst' ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).symm)
    refine Eq.trans (congrArg AlgebraicGeometry.Spec.map ?_)
      (AlgebraicGeometry.Spec.map_comp _ _)
    show CommRingCat.ofHom (frameCoevalAlgHom D).hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap (constVecAlgebra N : Type 0)
        (TensorProduct ℚ (constVecAlgebra N : Type 0)
          (wFramesAlgebra D : Type 0))) ≫
      CommRingCat.ofHom (frameCoshearAlgHom D).hom.hom.toRingHom
    ext x
    exact (congrArg (fun m => m.hom.hom x) (frameCoshearAlgHom_inl D)).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
        (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).inv ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
      (AlgebraicGeometry.pullbackSpecIso_inv_snd ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).symm)
    refine Eq.trans (congrArg AlgebraicGeometry.Spec.map ?_)
      (AlgebraicGeometry.Spec.map_comp _ _)
    show CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (vRhoAlgebra D : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℚ) :
        (wFramesAlgebra D : Type 0) →ₐ[ℚ]
          TensorProduct ℚ (constVecAlgebra N : Type 0)
            (wFramesAlgebra D : Type 0)).toRingHom ≫
      CommRingCat.ofHom (frameCoshearAlgHom D).hom.hom.toRingHom
    ext x
    exact (congrArg (fun m => m.hom.hom x) (frameCoshearAlgHom_inr D)).symm

/-- **[asm-2b-v]** CORE-A: pairing with the frame then co-evaluating recovers the
vector. -/
theorem framePairEval_coeval (D : GaloisRepData N) :
    framePairEval D ≫ frameCoeval D =
      pullback.fst (constVecSchemeπ N) (wFramesπ D) := by
  refine Eq.trans (congrArg (· ≫ frameCoeval D)
    ((Iso.hom_inv_id_assoc (AlgebraicGeometry.pullbackSpecIso ℚ
        (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0))
      (framePairEval D)).symm.trans
    (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ (constVecAlgebra N : Type 0)
        (wFramesAlgebra D : Type 0)).hom ≫ ·) (framePairEval_conj D)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    ((Category.assoc _ _ _).trans
      (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
        (Iso.inv_hom_id_assoc _ _)))) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (AlgebraicGeometry.Spec.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun t => (AlgebraicGeometry.pullbackSpecIso ℚ
      (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map t) ?_)
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ (constVecAlgebra N : Type 0)
      (wFramesAlgebra D : Type 0))
  show CommRingCat.ofHom (frameCoevalAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (frameShearAlgHom D).hom.hom.toRingHom =
    CommRingCat.ofHom (algebraMap (constVecAlgebra N : Type 0)
      (TensorProduct ℚ (constVecAlgebra N : Type 0) (wFramesAlgebra D : Type 0)))
  ext x
  exact congrArg (fun m => m.hom.hom x) (frameShearAlgHom_coeval D)

/-- **[asm-2b-v]** CORE-B: pairing with the frame then evaluating recovers the
`ρ`-vector. -/
theorem framePairCoeval_eval (D : GaloisRepData N) :
    framePairCoeval D ≫ frameEval D =
      pullback.fst (vRhoπ D) (wFramesπ D) := by
  refine Eq.trans (congrArg (· ≫ frameEval D)
    ((Iso.hom_inv_id_assoc (AlgebraicGeometry.pullbackSpecIso ℚ
        (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0))
      (framePairCoeval D)).symm.trans
    (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
        (wFramesAlgebra D : Type 0)).hom ≫ ·) (framePairCoeval_conj D)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    ((Category.assoc _ _ _).trans
      (congrArg (AlgebraicGeometry.Spec.map _ ≫ ·)
        (Iso.inv_hom_id_assoc _ _)))) ?_
  refine Eq.trans (congrArg ((AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫ ·)
    (AlgebraicGeometry.Spec.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (fun t => (AlgebraicGeometry.pullbackSpecIso ℚ
      (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)).hom ≫
      AlgebraicGeometry.Spec.map t) ?_)
    (AlgebraicGeometry.pullbackSpecIso_hom_fst' ℚ (vRhoAlgebra D : Type 0)
      (wFramesAlgebra D : Type 0))
  show CommRingCat.ofHom (frameEvalAlgHom D).hom.hom.toRingHom ≫
      CommRingCat.ofHom (frameCoshearAlgHom D).hom.hom.toRingHom =
    CommRingCat.ofHom (algebraMap (vRhoAlgebra D : Type 0)
      (TensorProduct ℚ (vRhoAlgebra D : Type 0) (wFramesAlgebra D : Type 0)))
  ext x
  exact congrArg (fun m => m.hom.hom x) (frameCoshearAlgHom_eval D)


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

/-- **[asm-2b-vi]** The inverse of the evaluation slice: pair the `ρ`-point with the
`h`-frame and co-evaluate. -/
noncomputable def frameEvalSliceInv (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    pullback (vRhoπ D) sT ⟶ pullback sT (constVecSchemeπ N) :=
  pullback.lift (pullback.snd (vRhoπ D) sT)
    (pullback.lift (pullback.fst (vRhoπ D) sT)
        (pullback.snd (vRhoπ D) sT ≫ h)
        (by rw [Category.assoc, hover, pullback.condition]) ≫ frameCoeval D)
    (by rw [Category.assoc, frameCoeval_π, ← Category.assoc, pullback.lift_fst,
      pullback.condition])

@[reassoc]
theorem frameEvalSlice_fst (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    frameEvalSlice D sT h hover ≫ pullback.fst (vRhoπ D) sT =
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) ≫ frameEval D :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem frameEvalSlice_snd (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    frameEvalSlice D sT h hover ≫ pullback.snd (vRhoπ D) sT =
      pullback.fst sT (constVecSchemeπ N) :=
  pullback.lift_snd _ _ _

/-- **[T-EQ-2 c]** The slice-level contracted-product relation: twisting the constant
coordinates by `γ` equals slicing along the right-`γ`-translated frame. -/
theorem frameEvalSlice_rightMul (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (constVecGLScheme N γ) (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, constVecGLScheme_π]) ≫
      frameEvalSlice D sT h hover =
      frameEvalSlice D sT (h ≫ wFramesRightMul D γ)
        (by rw [Category.assoc, wFramesRightMul_π, hover]) := by
  have hTL : pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
      (constVecGLScheme N γ) (𝟙 (Spec (CommRingCat.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, constVecGLScheme_π]) ≫
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) =
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) ≫
      pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (constVecGLScheme N γ) (𝟙 (wFrames D))
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, constVecGLScheme_π])
        (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
        (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
          (constVecGLScheme N γ) (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
        (pullback.lift_fst _ _ _)) ?_)
      refine Eq.trans (pullback.lift_snd _ _ _) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (pullback.lift _ _ _ ≫ ·)
        (pullback.lift_fst _ _ _)) ?_
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ constVecGLScheme N γ) (pullback.lift_fst _ _ _))
    · refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg
        (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
          (constVecGLScheme N γ) (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
        (pullback.lift_snd _ _ _)) ?_)
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ h) (pullback.lift_fst _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (pullback.fst sT (constVecSchemeπ N) ≫ ·)
        (Category.id_comp h)) ?_
      refine Eq.symm ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (pullback.lift _ _ _ ≫ ·)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))) ?_
      exact pullback.lift_snd _ _ _
  have hLF : pullback.lift (pullback.snd sT (constVecSchemeπ N))
      (pullback.fst sT (constVecSchemeπ N) ≫ h)
      (by rw [Category.assoc, hover, ← pullback.condition]) ≫
      pullback.map (constVecSchemeπ N) (wFramesπ D) (constVecSchemeπ N)
        (wFramesπ D) (𝟙 (constVecScheme N)) (wFramesRightMul D γ)
        (𝟙 (Spec (CommRingCat.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, wFramesRightMul_π]) =
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ (h ≫ wFramesRightMul D γ))
        (by rw [Category.assoc, Category.assoc, wFramesRightMul_π, hover,
          ← pullback.condition]) := by
    apply pullback.hom_ext
    · refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (pullback.lift _ _ _ ≫ ·)
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
      exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (pullback.lift _ _ _ ≫ ·)
        (pullback.lift_snd _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ wFramesRightMul D γ)
        (pullback.lift_snd _ _ _)) ?_
      exact (Category.assoc _ _ _).trans (pullback.lift_snd _ _ _).symm
  apply pullback.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT (constVecSchemeπ N) sT
        (constVecSchemeπ N) (𝟙 T) (constVecGLScheme N γ)
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ frameEval D) hTL) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.lift _ _ _ ≫ ·)
      (frameEval_twist D γ)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ frameEval D) hLF) ?_
    exact (pullback.lift_fst _ _ _).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (pullback.map sT (constVecSchemeπ N) sT
        (constVecSchemeπ N) (𝟙 T) (constVecGLScheme N γ)
        (𝟙 (Spec (CommRingCat.of ℚ))) _ _ ≫ ·)
      (pullback.lift_snd _ _ _)) ?_
    refine Eq.trans ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) ?_
    exact (pullback.lift_snd _ _ _).symm

@[reassoc]
theorem frameEvalSliceInv_fst (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    frameEvalSliceInv D sT h hover ≫ pullback.fst sT (constVecSchemeπ N) =
      pullback.snd (vRhoπ D) sT :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem frameEvalSliceInv_snd (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    frameEvalSliceInv D sT h hover ≫ pullback.snd sT (constVecSchemeπ N) =
      pullback.lift (pullback.fst (vRhoπ D) sT) (pullback.snd (vRhoπ D) sT ≫ h)
        (by rw [Category.assoc, hover, pullback.condition]) ≫ frameCoeval D :=
  pullback.lift_snd _ _ _

/-- **[asm-2b]** The evaluation slice along a frame is an isomorphism: a
trivialization `h` of the frames over `T` identifies the constant vector scheme
over `T` with the pulled-back `V_ρ` (the moduli heart of the contracted-product
route — CORE-A/B transported along the `h`-graph). -/
theorem frameEvalSlice_isIso (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (h : T ⟶ wFrames D)
    (hover : h ≫ wFramesπ D = sT) :
    IsIso (frameEvalSlice D sT h hover) := by
  have hsub1 : frameEvalSlice D sT h hover ≫
      pullback.lift (pullback.fst (vRhoπ D) sT) (pullback.snd (vRhoπ D) sT ≫ h)
        (by rw [Category.assoc, hover, pullback.condition]) =
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) ≫
        framePairEval D := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, frameEvalSlice_fst,
        frameEvalSlice_snd, frameEvalSlice_fst_assoc, frameEvalSlice_snd_assoc,
        framePairEval_fst, framePairEval_snd, framePairEval_fst_assoc,
        framePairEval_snd_assoc]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, frameEvalSlice_fst,
        frameEvalSlice_snd, frameEvalSlice_fst_assoc, frameEvalSlice_snd_assoc,
        framePairEval_fst, framePairEval_snd, framePairEval_fst_assoc,
        framePairEval_snd_assoc]
  have hsub2 : frameEvalSliceInv D sT h hover ≫
      pullback.lift (pullback.snd sT (constVecSchemeπ N))
        (pullback.fst sT (constVecSchemeπ N) ≫ h)
        (by rw [Category.assoc, hover, ← pullback.condition]) =
      pullback.lift (pullback.fst (vRhoπ D) sT) (pullback.snd (vRhoπ D) sT ≫ h)
        (by rw [Category.assoc, hover, pullback.condition]) ≫
        framePairCoeval D := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, frameEvalSliceInv_fst,
        frameEvalSliceInv_snd, frameEvalSliceInv_fst_assoc,
        frameEvalSliceInv_snd_assoc, framePairCoeval_fst, framePairCoeval_snd,
        framePairCoeval_fst_assoc, framePairCoeval_snd_assoc]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, frameEvalSliceInv_fst,
        frameEvalSliceInv_snd, frameEvalSliceInv_fst_assoc,
        frameEvalSliceInv_snd_assoc, framePairCoeval_fst, framePairCoeval_snd,
        framePairCoeval_fst_assoc, framePairCoeval_snd_assoc]
  refine ⟨frameEvalSliceInv D sT h hover, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, frameEvalSliceInv_fst,
        frameEvalSlice_snd, frameEvalSlice_snd_assoc]
    · rw [Category.assoc, Category.id_comp, frameEvalSliceInv_snd,
        ← Category.assoc, hsub1, Category.assoc, framePairEval_coeval,
        pullback.lift_fst]
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp, frameEvalSlice_fst,
        ← Category.assoc, hsub2, Category.assoc, framePairCoeval_eval,
        pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp, frameEvalSlice_snd,
        frameEvalSliceInv_fst, frameEvalSliceInv_fst_assoc]

/-- **[asm-3b]** The framed torsion trivialization: a full level structure `L` and a
frame `h` over `T` identify `E[N]` with the pulled-back `V_ρ` — the ρ-dictionary's
torsion isomorphism (`fullLevelIso` to the constant scheme, base-change comparison,
the constant-vector identification, then the evaluation slice along `h`). -/
noncomputable def framedTorsionIso (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) :
    E.torsion N ≅ pullback (vRhoπ D) sT :=
  letI := frameEvalSlice_isIso D sT h hover
  (E.fullLevelIso hinv L).symm ≪≫
    (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
    asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
      (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
    asIso (frameEvalSlice D sT h hover)

/-- **[asm-3b]** The framed torsion trivialization lies over `T`. -/
theorem framedTorsionIso_π (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) :
    (framedTorsionIso D sT E hinv L h hover).hom ≫ pullback.snd (vRhoπ D) sT =
      E.torsionπ N := by
  haveI := frameEvalSlice_isIso D sT h hover
  rw [show framedTorsionIso D sT E hinv L h hover =
    (E.fullLevelIso hinv L).symm ≪≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
      asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
      asIso (frameEvalSlice D sT h hover) from rfl]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_hom]
  simp only [Category.assoc]
  rw [frameEvalSlice_snd, pullback.lift_fst, Category.comp_id,
    IsPullback.isoPullback_hom_fst, ← E.fullLevelHom_torsionπ L]
  exact Iso.inv_hom_id_assoc _ _

/-- **[3c-A]** The PINNED framed torsion trivialization: the read-correction is
inserted before the evaluation slice, so the induced coordinate reads compute to the
concrete index-read (`constVecPointsEquiv_corrScheme`). -/
noncomputable def framedTorsionIsoPinned (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) :
    E.torsion N ≅ pullback (vRhoπ D) sT :=
  letI := frameEvalSlice_isIso D sT h hover
  (E.fullLevelIso hinv L).symm ≪≫
    (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
    asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
      (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
    asIso (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
      (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≪≫
    asIso (frameEvalSlice D sT h hover)

/-- **[T-EQ-2 e]** The pinned framed trivialization descends the diagonal action:
the `γ`-translated framed pair pins to the SAME trivialization (the coordinate
change through every leg cancels against the frame translation — KM 4.7's
well-definedness on `GL₂`-orbits, morphism-level). -/
theorem framedTorsionIsoPinned_glSmul (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    framedTorsionIsoPinned D sT E hinv (E.glSmul γ L)
        (h ≫ wFramesRightMul D γ)
        (by rw [Category.assoc, wFramesRightMul_π, hover]) =
      framedTorsionIsoPinned D sT E hinv L h hover := by
  haveI := frameEvalSlice_isIso D sT h hover
  have hoverRm : (h ≫ wFramesRightMul D γ) ≫ wFramesπ D = sT := by
    rw [Category.assoc, wFramesRightMul_π, hover]
  haveI := frameEvalSlice_isIso D sT (h ≫ wFramesRightMul D γ) hoverRm
  have hcore : (EllipticCurve.constGL (S := T) γ).hom ≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
      pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
      frameEvalSlice D sT h hover =
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
      pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
      frameEvalSlice D sT (h ≫ wFramesRightMul D γ) hoverRm := by
    refine Eq.trans ((Category.assoc _ _ _).symm.trans (Eq.trans
      (congrArg (· ≫ (pullback.map sT (constSchemeπ (Spec (.of ℚ))
          (Fin 2 → ZMod N)) sT (constVecSchemeπ N) (𝟙 T)
          (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
        pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
          (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
        frameEvalSlice D sT h hover))
        (constGL_isoPullback sT N γ)) (Category.assoc _ _ _))) ?_
    refine congrArg ((isPullback_constSchemeMapAlong sT
      (Fin 2 → ZMod N)).flip.isoPullback.hom ≫ ·) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm.trans (Eq.trans
      (congrArg (· ≫ (pullback.map sT (constVecSchemeπ N) sT
          (constVecSchemeπ N) (𝟙 T) (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫
        frameEvalSlice D sT h hover))
        (pullback_map_snd_square sT
          (EllipticCurve.constGL (S := Spec (CommRingCat.of ℚ)) γ).hom
          (constVecSchemeIso N).hom
          (Spec.map (CommRingCat.ofHom
            (constVecGLAlg N γ).hom.hom.toRingHom))
          (constGL_constSchemeπ (Spec (CommRingCat.of ℚ)) N γ)
          (constVecSchemeIso_π N) (constVecGLScheme_π N γ)
          (constGL_constVecSchemeIso N γ)))
      (Category.assoc _ _ _))) ?_
    refine congrArg ((pullback.map sT (constSchemeπ (Spec (.of ℚ))
        (Fin 2 → ZMod N)) sT (constVecSchemeπ N) (𝟙 T)
        (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≫ ·) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm.trans (Eq.trans
      (congrArg (· ≫ frameEvalSlice D sT h hover)
        (pullback_map_snd_square sT
          (Spec.map (CommRingCat.ofHom
            (constVecGLAlg N γ).hom.hom.toRingHom))
          (corrSchemeIso N).hom
          (Spec.map (CommRingCat.ofHom
            (constVecGLAlg N γ).hom.hom.toRingHom))
          (constVecGLScheme_π N γ) (corrSchemeIso_π N)
          (constVecGLScheme_π N γ) (corrSchemeIso_constVecGL N γ)))
      (Category.assoc _ _ _))) ?_
    refine congrArg ((pullback.map sT (constVecSchemeπ N) sT
        (constVecSchemeπ N) (𝟙 T) (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≫ ·) ?_
    exact frameEvalSlice_rightMul D sT h hover γ
  ext1
  rw [show framedTorsionIsoPinned D sT E hinv (E.glSmul γ L)
      (h ≫ wFramesRightMul D γ)
      (by rw [Category.assoc, wFramesRightMul_π, hover]) =
    (E.fullLevelIso hinv (E.glSmul γ L)).symm ≪≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
      asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
      asIso (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≪≫
      asIso (frameEvalSlice D sT (h ≫ wFramesRightMul D γ) hoverRm) from rfl]
  rw [show framedTorsionIsoPinned D sT E hinv L h hover =
    (E.fullLevelIso hinv L).symm ≪≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
      asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
      asIso (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≪≫
      asIso (frameEvalSlice D sT h hover) from rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [E.fullLevelIso_glSmul hinv γ L]
  simp only [Iso.trans_inv, Category.assoc]
  refine congrArg ((E.fullLevelIso hinv L).inv ≫ ·) ?_
  refine Eq.trans (congrArg ((EllipticCurve.constGL (S := T) γ).inv ≫ ·)
    hcore.symm) ?_
  exact Iso.inv_hom_id_assoc _ _

/-- **[3c-A]** The pinned framed torsion trivialization lies over `T`. -/
theorem framedTorsionIsoPinned_π (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT) :
    (framedTorsionIsoPinned D sT E hinv L h hover).hom ≫
      pullback.snd (vRhoπ D) sT = E.torsionπ N := by
  haveI := frameEvalSlice_isIso D sT h hover
  rw [show framedTorsionIsoPinned D sT E hinv L h hover =
    (E.fullLevelIso hinv L).symm ≪≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback ≪≫
      asIso (pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm)) ≪≫
      asIso (pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm)) ≪≫
      asIso (frameEvalSlice D sT h hover) from rfl]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_hom, asIso_hom]
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun t => (E.fullLevelIso hinv L).inv ≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫
      pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
        (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) ≫ t)
    (frameEvalSlice_snd D sT h hover)) ?_
  refine Eq.trans (congrArg (fun t => (E.fullLevelIso hinv L).inv ≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫
      pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
        (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) ≫ t)
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
  refine Eq.trans (congrArg (fun t => (E.fullLevelIso hinv L).inv ≫
      (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom ≫ t)
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))) ?_
  refine Eq.trans (congrArg (fun t => (E.fullLevelIso hinv L).inv ≫ t)
    (IsPullback.isoPullback_hom_fst _)) ?_
  refine Eq.trans (congrArg ((E.fullLevelIso hinv L).inv ≫ ·)
    (E.fullLevelHom_torsionπ L).symm) ?_
  exact Iso.inv_hom_id_assoc _ _

/-- **[3c-B4]** Every `ℚ̄`-point of a constant scheme lying over a `ℚ̄`-point of the
base factors through the inclusion at a constant index (the `ℚ̄`-spectrum is a
single point, so the locally constant read is constant). -/
noncomputable instance : Unique ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))) :=
  inferInstanceAs (Unique (PrimeSpectrum (AlgebraicClosure ℚ)))

theorem constScheme_qbar_factor {T : Scheme.{0}}
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (w : Spec (.of (AlgebraicClosure ℚ)) ⟶ constScheme T (Fin 2 → ZMod N))
    (hw : w ≫ constSchemeπ T (Fin 2 → ZMod N) = t) :
    ∃ u : Fin 2 → ZMod N,
      w = t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u := by
  refine ⟨constSchemePointsEquiv T (Fin 2 → ZMod N) (t ≫ 𝟙 T)
    ⟨w, hw.trans (Category.comp_id t).symm⟩ default, ?_⟩
  set c := constSchemePointsEquiv T (Fin 2 → ZMod N) (t ≫ 𝟙 T)
    ⟨w, hw.trans (Category.comp_id t).symm⟩ with hc
  have hnat := constSchemePointsEquiv_natural T (Fin 2 → ZMod N) (𝟙 T) t
    ⟨Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (c default),
      Limits.Sigma.ι_desc _ _⟩
  rw [constSchemePointsEquiv_sigmaι] at hnat
  have hread2 : constSchemePointsEquiv T (Fin 2 → ZMod N) (t ≫ 𝟙 T)
      ⟨t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (c default), by
        rw [Category.assoc, Limits.Sigma.ι_desc]⟩ = c := by
    refine Eq.trans hnat ?_
    refine LocallyConstant.ext fun p => ?_
    refine Eq.trans ?_ (congrArg c (Subsingleton.elim default p))
    rfl
  have hinj := (constSchemePointsEquiv T (Fin 2 → ZMod N) (t ≫ 𝟙 T)).injective
    hread2
  exact (congrArg Subtype.val hinj).symm

/-- **[3c-B4]** The factorization index over a `ℚ̄`-point is unique. -/
theorem sigmaι_qbar_index_injective {T : Scheme.{0}}
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T) {u v : Fin 2 → ZMod N}
    (h : t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v) : u = v := by
  have h1 := constSchemePointsEquiv_natural T (Fin 2 → ZMod N) (𝟙 T) t
    ⟨Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u, Limits.Sigma.ι_desc _ _⟩
  have h2 := constSchemePointsEquiv_natural T (Fin 2 → ZMod N) (𝟙 T) t
    ⟨Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v, Limits.Sigma.ι_desc _ _⟩
  rw [constSchemePointsEquiv_sigmaι] at h1 h2
  have hsub : (⟨t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u, by
      rw [Category.assoc, Limits.Sigma.ι_desc]⟩ :
      { m : Spec (.of (AlgebraicClosure ℚ)) ⟶ constScheme T (Fin 2 → ZMod N) //
        m ≫ constSchemeπ T (Fin 2 → ZMod N) = t ≫ 𝟙 T }) =
      ⟨t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) v, by
      rw [Category.assoc, Limits.Sigma.ι_desc]⟩ :=
    Subtype.ext h
  have hcc := (h1.symm.trans (congrArg
    (constSchemePointsEquiv T (Fin 2 → ZMod N) (t ≫ 𝟙 T)) hsub)).trans h2
  exact congrArg (fun (f : LocallyConstant
    ↥(Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Fin 2 → ZMod N)) => f default)
    hcc

/-- **[3c-B5]** A `ℚ̄`-torsion point factors through the full-level trivialization at
an index. -/
theorem torsion_qbar_factor {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (z : Spec (.of (AlgebraicClosure ℚ)) ⟶ E.torsion N)
    (hz : z ≫ E.torsionπ N = t) :
    ∃ u : Fin 2 → ZMod N,
      z ≫ (E.fullLevelIso hinv L).inv =
        t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u :=
  constScheme_qbar_factor t (z ≫ (E.fullLevelIso hinv L).inv) (by
    rw [Category.assoc]
    rw [show (E.fullLevelIso hinv L).inv ≫ constSchemeπ T (Fin 2 → ZMod N) =
      E.torsionπ N from (congrArg ((E.fullLevelIso hinv L).inv ≫ ·)
        (E.fullLevelHom_torsionπ L).symm).trans (Iso.inv_hom_id_assoc _ _)]
    exact hz)

/-- **[3c-B5]** A factored torsion point is the inclusion-composite at its index. -/
theorem torsion_qbar_factor_eq {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (z : Spec (.of (AlgebraicClosure ℚ)) ⟶ E.torsion N)
    {u : Fin 2 → ZMod N}
    (hfac : z ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u) :
    z = t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ E.fullLevelHom L := by
  have h1 : z = (z ≫ (E.fullLevelIso hinv L).inv) ≫
      (E.fullLevelIso hinv L).hom := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h1, hfac, Category.assoc]
  rfl

/-- **[3c-B5]** The inclusion-composite is the pulled standard combination. -/
theorem sigmaι_fullLevelHom {T : Scheme.{0}} {E : EllipticCurve T}
    (L : E.FullLevelPt N) (u : Fin 2 → ZMod N) :
    Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ E.fullLevelHom L =
      E.pointToTorsion (((u 0).val : ℤ) • L.1.1 + ((u 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
          rw [smul_add, smul_comm (N : ℤ) ((u 0).val : ℤ),
            smul_comm (N : ℤ) ((u 1).val : ℤ), L.2.1.1, L.2.1.2, smul_zero,
            smul_zero, add_zero])) :=
  Limits.Sigma.ι_desc _ _

/-- **[3c-C]** The pinned coordinate formula: the coordinate of a `ℚ̄`-torsion point
through the pinned dictionary is the frame matrix acting on the full-level index. -/
theorem coord_framedPinned (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    {u : Fin 2 → ZMod N}
    (hfac : E.pointToTorsion x hx ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u) :
    coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
      (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht x hx =
    wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ • u := by
  haveI := frameEvalSlice_isIso D sT h hover
  set R1 := (isPullback_constSchemeMapAlong sT (Fin 2 → ZMod N)).flip.isoPullback.hom
    with hR1
  set R2 := pullback.map sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) sT
      (constVecSchemeπ N) (𝟙 T) (constVecSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (constVecSchemeIso_π N).symm) with hR2
  set R3 := pullback.map sT (constVecSchemeπ N) sT (constVecSchemeπ N) (𝟙 T)
      (corrSchemeIso N).hom (𝟙 (Spec (.of ℚ)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (corrSchemeIso_π N).symm) with hR3
  set SL := frameEvalSlice D sT h hover with hSL
  set IN := pullback.lift (pullback.snd sT (constVecSchemeπ N))
      (pullback.fst sT (constVecSchemeπ N) ≫ h)
      (by rw [Category.assoc, hover, ← pullback.condition]) with hIN
  -- atomic projection facts
  have hR1fst : R1 ≫ pullback.fst sT (constSchemeπ (Spec (.of ℚ))
      (Fin 2 → ZMod N)) = constSchemeπ T (Fin 2 → ZMod N) :=
    IsPullback.isoPullback_hom_fst _
  have hR1snd : R1 ≫ pullback.snd sT (constSchemeπ (Spec (.of ℚ))
      (Fin 2 → ZMod N)) = constSchemeMapAlong sT (Fin 2 → ZMod N) :=
    IsPullback.isoPullback_hom_snd _
  have hR2fst : R2 ≫ pullback.fst sT (constVecSchemeπ N) =
      pullback.fst sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hR2snd : R2 ≫ pullback.snd sT (constVecSchemeπ N) =
      pullback.snd sT (constSchemeπ (Spec (.of ℚ)) (Fin 2 → ZMod N)) ≫
        (constVecSchemeIso N).hom :=
    pullback.lift_snd _ _ _
  have hR3fst : R3 ≫ pullback.fst sT (constVecSchemeπ N) =
      pullback.fst sT (constVecSchemeπ N) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hR3snd : R3 ≫ pullback.snd sT (constVecSchemeπ N) =
      pullback.snd sT (constVecSchemeπ N) ≫ (corrSchemeIso N).hom :=
    pullback.lift_snd _ _ _
  have hSLfst : SL ≫ pullback.fst (vRhoπ D) sT = IN ≫ frameEval D :=
    frameEvalSlice_fst D sT h hover
  have hINfst : IN ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) =
      pullback.snd sT (constVecSchemeπ N) :=
    pullback.lift_fst _ _ _
  have hINsnd : IN ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D) =
      pullback.fst sT (constVecSchemeπ N) ≫ h :=
    pullback.lift_snd _ _ _
  have hhom : (framedTorsionIsoPinned D sT E hinv L h hover).hom =
      (E.fullLevelIso hinv L).inv ≫ R1 ≫ R2 ≫ R3 ≫ SL := rfl
  -- the sliced value of the coordinate point
  set q : Spec (.of (AlgebraicClosure ℚ)) ⟶ pullback sT (constVecSchemeπ N) :=
    t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ R1 ≫ R2 ≫ R3 with hq
  have hval : E.pointToTorsion x hx ≫
      (framedTorsionIsoPinned D sT E hinv L h hover).hom ≫
      pullback.fst (vRhoπ D) sT = (q ≫ IN) ≫ frameEval D := by
    rw [hhom]
    simp only [Category.assoc]
    rw [← Category.assoc (E.pointToTorsion x hx) (E.fullLevelIso hinv L).inv,
      hfac, hSLfst, hq]
    simp only [Category.assoc]
  -- projections of the composite point
  have hqfst : q ≫ pullback.fst sT (constVecSchemeπ N) = t := by
    rw [hq]
    simp only [Category.assoc]
    rw [hR3fst, hR2fst, hR1fst]
    rw [show Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫
        constSchemeπ T (Fin 2 → ZMod N) = 𝟙 T from Limits.Sigma.ι_desc _ _,
      Category.comp_id]
  have hqsnd : q ≫ pullback.snd sT (constVecSchemeπ N) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
        (constVecSchemeIso N).hom) ≫ (corrSchemeIso N).hom := by
    rw [hq]
    simp only [Category.assoc]
    refine Eq.trans (congrArg (fun v => t ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ R1 ≫ R2 ≫ v) hR3snd) ?_
    refine Eq.trans (congrArg (fun v => t ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ R1 ≫ v)
      ((Category.assoc R2 _ _).symm.trans
        (congrArg (· ≫ (corrSchemeIso N).hom) hR2snd))) ?_
    refine Eq.trans (congrArg (fun v => t ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u ≫ v)
      ((congrArg (R1 ≫ ·) (Category.assoc _ _ _)).trans
        ((Category.assoc R1 _ _).symm.trans
          (congrArg (· ≫ ((constVecSchemeIso N).hom ≫ (corrSchemeIso N).hom))
            hR1snd)))) ?_
    refine Eq.trans (congrArg (t ≫ ·)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ ((constVecSchemeIso N).hom ≫ (corrSchemeIso N).hom))
          (ι_constSchemeMapAlong sT (Fin 2 → ZMod N) u)))) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ((constVecSchemeIso N).hom ≫ (corrSchemeIso N).hom))
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫
          Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u)
          ht))))) ?_
    simp only [Category.assoc]
  -- the over-ℚ̄ base fact for the constant point
  have hPTov : (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
      Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
      (constVecSchemeIso N).hom) ≫ constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ·) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun v => Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫ v)
      (constVecSchemeIso_π N)) ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ ·)
      (Limits.Sigma.ι_desc (f := fun _ : (Fin 2 → ZMod N) =>
        Spec (CommRingCat.of ℚ)) (fun _ => 𝟙 _) u)) ?_
    exact Category.comp_id _
  -- projections of the sliced point
  have hfst2 : (q ≫ IN) ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
        (constVecSchemeIso N).hom) ≫ (corrSchemeIso N).hom := by
    rw [Category.assoc, hINfst]
    exact hqsnd
  have hsnd2 : (q ≫ IN) ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D) =
      t ≫ h := by
    rw [Category.assoc, hINsnd, ← Category.assoc, hqfst]
  have hp : (q ≫ IN) ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D) ≫
      constVecSchemeπ N =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ constVecSchemeπ N) hfst2).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((Spec.map (CommRingCat.ofHom
              (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
            Sigma.ι (fun _ : (Fin 2 → ZMod N) => Spec (CommRingCat.of ℚ)) u ≫
            (constVecSchemeIso N).hom) ≫ ·) (corrSchemeIso_π N)).trans hPTov)))
  have hfe := frameEval_points D (q ≫ IN) hp
  have hwr : wFramesPointsEquiv D
      ⟨(q ≫ IN) ≫ pullback.snd (constVecSchemeπ N) (wFramesπ D), by
        rw [Category.assoc, ← pullback.condition]; exact hp⟩ =
      wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ :=
    congrArg (wFramesPointsEquiv D) (Subtype.ext hsnd2)
  have hcv : constVecPointsEquiv N
      ⟨(q ≫ IN) ≫ pullback.fst (constVecSchemeπ N) (wFramesπ D), by
        rw [Category.assoc]; exact hp⟩ = u :=
    (congrArg (constVecPointsEquiv N) (Subtype.ext hfst2)).trans
      ((constVecPointsEquiv_corrScheme N _ hPTov).trans
        (constVecIndexRead_const N u hPTov))
  refine Eq.trans (congrArg (vRhoPointsEquiv D) (Subtype.ext hval)) (hfe.trans ?_)
  refine Eq.trans (congrArg
    (fun A : Matrix.GeneralLinearGroup (Fin 2) (ZMod N) =>
      A • constVecPointsEquiv N ⟨(q ≫ IN) ≫ pullback.fst (constVecSchemeπ N)
        (wFramesπ D), by rw [Category.assoc]; exact hp⟩) hwr) ?_
  exact congrArg (fun v => wFramesPointsEquiv D ⟨t ≫ h, by
    rw [Category.assoc, hover, ht]⟩ • v) hcv

/-- **[3c-D]** Integer-lift arithmetic on `N`-killed points: the `ZMod`-value of a sum
scales as the sum of values. -/
theorem zmodVal_add_smul {A : Type} [AddCommGroup A] {P : A}
    (hP : (N : ℤ) • P = 0) (a b : ZMod N) :
    (((a + b : ZMod N)).val : ℤ) • P = ((a.val : ℤ)) • P + ((b.val : ℤ)) • P := by
  rw [← add_smul]
  have hmod2 : (((a + b : ZMod N)).val : ℤ) =
      ((a.val : ℤ) + (b.val : ℤ)) % (N : ℤ) := by
    rw [ZMod.val_add]
    push_cast
    rfl
  refine Eq.symm ?_
  calc ((a.val : ℤ) + (b.val : ℤ)) • P
      = (((a.val : ℤ) + (b.val : ℤ)) % (N : ℤ) +
          (N : ℤ) * (((a.val : ℤ) + (b.val : ℤ)) / (N : ℤ))) • P := by
        congr 1
        rw [Int.emod_def]
        ring
    _ = (((a.val : ℤ) + (b.val : ℤ)) % (N : ℤ)) • P +
          ((N : ℤ) * (((a.val : ℤ) + (b.val : ℤ)) / (N : ℤ))) • P :=
        add_smul _ _ _
    _ = (((a + b : ZMod N)).val : ℤ) • P + 0 := by
        rw [← hmod2, mul_comm, mul_smul, hP, smul_zero]
    _ = (((a + b : ZMod N)).val : ℤ) • P := add_zero _

/-- **[3c-D]** The standard combinations are additive in the index. -/
theorem comb_add {T : Scheme.{0}} {E : EllipticCurve T} (L : E.FullLevelPt N)
    (u v : Fin 2 → ZMod N) :
    ((((u 0).val : ℤ) • L.1.1 + ((u 1).val : ℤ) • L.1.2) +
      (((v 0).val : ℤ) • L.1.1 + ((v 1).val : ℤ) • L.1.2)) =
    ((((u + v) 0).val : ℤ) • L.1.1 + (((u + v) 1).val : ℤ) • L.1.2) := by
  rw [add_add_add_comm]
  rw [show ((u + v) 0) = u 0 + v 0 from rfl, show ((u + v) 1) = u 1 + v 1 from rfl]
  rw [zmodVal_add_smul L.2.1.1 (u 0) (v 0), zmodVal_add_smul L.2.1.2 (u 1) (v 1)]

/-- **[3c-D]** The full-level factorization index is additive. -/
theorem torsion_factor_index_add {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hxy : (x + y).1 ≫ E.mulByHom N = t ≫ E.zero)
    {ux uy w : Fin 2 → ZMod N}
    (hfx : E.pointToTorsion x hx ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) ux)
    (hfy : E.pointToTorsion y hy ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) uy)
    (hfw : E.pointToTorsion (x + y) hxy ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) w) :
    w = ux + uy := by
  -- point-level characterizations from the factorizations
  have hxc : x = EllipticCurve.Point.pull E t
      (((ux 0).val : ℤ) • L.1.1 + ((ux 1).val : ℤ) • L.1.2) := by
    refine Subtype.ext ?_
    have h1 := congrArg (· ≫ E.torsionι N)
      ((torsion_qbar_factor_eq hinv L t (E.pointToTorsion x hx) hfx).trans
        (congrArg (t ≫ ·) (sigmaι_fullLevelHom L ux)))
    simp only [Category.assoc] at h1
    rw [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι] at h1
    exact h1
  have hyc : y = EllipticCurve.Point.pull E t
      (((uy 0).val : ℤ) • L.1.1 + ((uy 1).val : ℤ) • L.1.2) := by
    refine Subtype.ext ?_
    have h1 := congrArg (· ≫ E.torsionι N)
      ((torsion_qbar_factor_eq hinv L t (E.pointToTorsion y hy) hfy).trans
        (congrArg (t ≫ ·) (sigmaι_fullLevelHom L uy)))
    simp only [Category.assoc] at h1
    rw [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι] at h1
    exact h1
  -- the sum is the pulled combination at the sum index
  have hsum : x + y = EllipticCurve.Point.pull E t
      ((((ux + uy) 0).val : ℤ) • L.1.1 + (((ux + uy) 1).val : ℤ) • L.1.2) := by
    rw [hxc, hyc, ← EllipticCurve.Point.pull_add]
    exact congrArg (EllipticCurve.Point.pull E t) (comb_add L ux uy)
  -- hence its torsion point is the inclusion-composite at the sum index
  have hzw : E.pointToTorsion (x + y) hxy =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) ≫
        E.fullLevelHom L := by
    apply pullback.hom_ext
    · show E.pointToTorsion (x + y) hxy ≫ E.torsionι N =
        (t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) ≫
          E.fullLevelHom L) ≫ E.torsionι N
      rw [E.pointToTorsion_torsionι]
      rw [show Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) ≫
          E.fullLevelHom L = E.pointToTorsion
            ((((ux + uy) 0).val : ℤ) • L.1.1 + (((ux + uy) 1).val : ℤ) • L.1.2)
            ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
              rw [smul_add, smul_comm (N : ℤ) (((ux + uy) 0).val : ℤ),
                smul_comm (N : ℤ) (((ux + uy) 1).val : ℤ), L.2.1.1, L.2.1.2,
                smul_zero, smul_zero, add_zero])) from sigmaι_fullLevelHom L _]
      rw [Category.assoc, E.pointToTorsion_torsionι]
      exact congrArg Subtype.val hsum
    · show E.pointToTorsion (x + y) hxy ≫ E.torsionπ N =
        (t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) ≫
          E.fullLevelHom L) ≫ E.torsionπ N
      rw [E.pointToTorsion_torsionπ]
      rw [show Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) ≫
          E.fullLevelHom L = E.pointToTorsion
            ((((ux + uy) 0).val : ℤ) • L.1.1 + (((ux + uy) 1).val : ℤ) • L.1.2)
            ((E.smul_eq_zero_iff_comp_mulByHom _ N _).mp (by
              rw [smul_add, smul_comm (N : ℤ) (((ux + uy) 0).val : ℤ),
                smul_comm (N : ℤ) (((ux + uy) 1).val : ℤ), L.2.1.1, L.2.1.2,
                smul_zero, smul_zero, add_zero])) from sigmaι_fullLevelHom L _]
      rw [Category.assoc, E.pointToTorsion_torsionπ]
      exact (Category.comp_id t).symm
  -- compare the two factorizations of the sum
  have hcomp : t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) w =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) (ux + uy) := by
    rw [← hfw, hzw]
    simp only [Category.assoc]
    rw [show E.fullLevelHom L ≫ (E.fullLevelIso hinv L).inv =
      𝟙 (constScheme T (Fin 2 → ZMod N)) from
      (E.fullLevelIso hinv L).hom_inv_id, Category.comp_id]
  exact sigmaι_qbar_index_injective t hcomp

/-- **[3c-D]** The pinned-dictionary coordinate is additive — the `coords_additive`
field of `RhoLevelStructure` for the framed construction. -/
theorem coord_framedPinned_additive (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hxy : (x + y).1 ≫ E.mulByHom N = t ≫ E.zero) :
    coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
      (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht (x + y) hxy =
    coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
      (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht x hx +
    coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
      (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht y hy := by
  obtain ⟨ux, hfx⟩ := torsion_qbar_factor hinv L t (E.pointToTorsion x hx)
    (E.pointToTorsion_torsionπ x hx)
  obtain ⟨uy, hfy⟩ := torsion_qbar_factor hinv L t (E.pointToTorsion y hy)
    (E.pointToTorsion_torsionπ y hy)
  obtain ⟨w, hfw⟩ := torsion_qbar_factor hinv L t (E.pointToTorsion (x + y) hxy)
    (E.pointToTorsion_torsionπ (x + y) hxy)
  rw [coord_framedPinned D sT E hinv L h hover t ht x hx hfx,
    coord_framedPinned D sT E hinv L h hover t ht y hy hfy,
    coord_framedPinned D sT E hinv L h hover t ht (x + y) hxy hfw,
    torsion_factor_index_add hinv L t x y hx hy hxy hfx hfy hfw, smul_add]

/-- **[3d-ii]** The point-level characterization of a factored torsion point: it is
the pulled standard combination at its index. -/
theorem torsion_factor_point_eq {T : Scheme.{0}} {E : EllipticCurve T}
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    {u : Fin 2 → ZMod N}
    (hfac : E.pointToTorsion x hx ≫ (E.fullLevelIso hinv L).inv =
      t ≫ Sigma.ι (fun _ : (Fin 2 → ZMod N) => T) u) :
    x = EllipticCurve.Point.pull E t
      (((u 0).val : ℤ) • L.1.1 + ((u 1).val : ℤ) • L.1.2) := by
  refine Subtype.ext ?_
  have h1 := congrArg (· ≫ E.torsionι N)
    ((torsion_qbar_factor_eq hinv L t (E.pointToTorsion x hx) hfac).trans
      (congrArg (t ≫ ·) (sigmaι_fullLevelHom L u)))
  simp only [Category.assoc] at h1
  rw [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι] at h1
  exact h1

/-- **[3d]** Pairing compatibility of the pinned dictionary: given the symplectic
compatibility of the full-level pair with the frame, the Weil pairing of two
`ℚ̄`-torsion points is `p` of the standard symplectic pairing of their pinned
coordinates. -/
theorem pairingCompat_framedPinned (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hsymp : FramedSymp D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 h hover)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) :
    PairingCompatAt D sT (framedTorsionIsoPinned D sT E hinv L h hover)
      (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht x y hx hy := by
  obtain ⟨ux, hfx⟩ := torsion_qbar_factor hinv L t (E.pointToTorsion x hx)
    (E.pointToTorsion_torsionπ x hx)
  obtain ⟨uy, hfy⟩ := torsion_qbar_factor hinv L t (E.pointToTorsion y hy)
    (E.pointToTorsion_torsionπ y hy)
  have hxc2 : x = ((ux 0).val : ℤ) • EllipticCurve.Point.pull E t L.1.1 +
      ((ux 1).val : ℤ) • EllipticCurve.Point.pull E t L.1.2 :=
    (torsion_factor_point_eq hinv L t x hx hfx).trans (by
      rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
        EllipticCurve.Point.pull_zsmul])
  have hyc2 : y = ((uy 0).val : ℤ) • EllipticCurve.Point.pull E t L.1.1 +
      ((uy 1).val : ℤ) • EllipticCurve.Point.pull E t L.1.2 :=
    (torsion_factor_point_eq hinv L t y hy hfy).trans (by
      rw [EllipticCurve.Point.pull_add, EllipticCurve.Point.pull_zsmul,
        EllipticCurve.Point.pull_zsmul])
  show (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
      (E.weilPairingEval x y hx hy).1 =
    ((D.p (Multiplicative.ofAdd
      (coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht x hx 0 *
        coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht y hy 1 -
        coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht x hx 1 *
        coord D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t ht y hy 0)) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  rw [coord_framedPinned D sT E hinv L h hover t ht x hx hfx,
    coord_framedPinned D sT E hinv L h hover t ht y hy hfy]
  rw [show (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ • ux)
        0 *
      (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ • uy) 1 -
      (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ • ux) 1 *
      (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩ • uy) 0 =
      ((Matrix.GeneralLinearGroup.det
        (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩) :
        (ZMod N)ˣ) : ZMod N) * (ux 0 * uy 1 - ux 1 * uy 0) from
    sympl_glSmul _ ux uy]
  clear hfx hfy
  revert hx hy
  rw [hxc2, hyc2]
  intro hx hy
  rw [show (E.weilPairingEval
      (((ux 0).val : ℤ) • EllipticCurve.Point.pull E t L.1.1 +
        ((ux 1).val : ℤ) • EllipticCurve.Point.pull E t L.1.2)
      (((uy 0).val : ℤ) • EllipticCurve.Point.pull E t L.1.1 +
        ((uy 1).val : ℤ) • EllipticCurve.Point.pull E t L.1.2) hx hy :
      Γ(Spec (.of (AlgebraicClosure ℚ)), ⊤)) =
    (E.weilPairingEval (EllipticCurve.Point.pull E t L.1.1)
      (EllipticCurve.Point.pull E t L.1.2)
      (sectionPull_raw_kill t L.2.1.1) (sectionPull_raw_kill t L.2.1.2) :
      Γ(Spec (.of (AlgebraicClosure ℚ)), ⊤)) ^
      ((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
        ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat from
    E.weilPairingEval_symplectic _ _ _ _ _ _ _ _ hx hy]
  rw [map_pow, hsymp t ht]
  -- the exponent arithmetic: (p z)^K = p (z^K), and the cast of K is the pairing
  rw [← Units.val_pow_eq_pow_val, ← SubmonoidClass.coe_pow, ← map_pow]
  congr 2
  rw [show (Multiplicative.ofAdd ((Matrix.GeneralLinearGroup.det
      (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩) :
      (ZMod N)ˣ) : ZMod N)) ^
      ((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
        ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat =
    Multiplicative.ofAdd
      (((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
        ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat •
      ((Matrix.GeneralLinearGroup.det
        (wFramesPointsEquiv D ⟨t ≫ h, by rw [Category.assoc, hover, ht]⟩) :
        (ZMod N)ˣ) : ZMod N)) from rfl]
  congr 1
  rw [nsmul_eq_mul, mul_comm]
  congr 1
  have hnneg : (0 : ℤ) ≤ (((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
      ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne N))
  have h3 : (((((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
      ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat : ℕ)) : ZMod N) =
      (((((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
      ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat : ℤ)) : ZMod N) := by
    push_cast
    rfl
  have h2 : (((((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
      ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) % (N : ℤ)).toNat : ℤ)) : ZMod N) =
      (((((ux 0).val : ℤ) * ((uy 1).val : ℤ) -
      ((ux 1).val : ℤ) * ((uy 0).val : ℤ)) : ℤ) : ZMod N) := by
    rw [Int.toNat_of_nonneg hnneg, Int.emod_def]
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [h3, h2]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id]

/-- **[asm-3 COMPLETE]** The ρ-dictionary: a full level structure together with a
symplectically compatible frame yields a ρ-level structure — all four fields carried
by the pinned framed construction. -/
noncomputable def rhoLevelStructureOfFramed (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (hsymp : FramedSymp D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 h hover)
    (hsymp_scheme : ∀ [Fact (1 < N)] {W : Scheme.{0}} (t : W ⟶ T)
      (x y : E.Point t)
      (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
      (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      torsionPairEval D sT t x y hx hy =
        coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t x y hx hy ≫
          vRhoPairingMap D) :
    RhoLevelStructure D sT E where
  torsionIso := framedTorsionIsoPinned D sT E hinv L h hover
  over_T := framedTorsionIsoPinned_π D sT E hinv L h hover
  coords_additive := fun t ht x y hx hy hxy =>
    coord_framedPinned_additive D sT E hinv L h hover t ht x y hx hy hxy
  pairing_compat := fun t ht x y hx hy =>
    pairingCompat_framedPinned D sT E hinv L h hover hsymp t ht x y hx hy
  pairing_scheme := hsymp_scheme

/-- **[T-EQ-2 COMPLETE]** The dictionary descends the diagonal `GL₂`-action: the
`γ`-translated framed pair (`glSmul` on the level, right translation on the frame)
yields the SAME `ρ`-level structure — KM 4.7's well-definedness on orbits, at the
morphism level (no geometric points). This is the descent-hypothesis feeding the
quotient couniversal property in T-EQ-3. -/
theorem rhoLevelStructureOfFramed_glSmul (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T)
    (hinv : NIsInvertible T N) (L : E.FullLevelPt N)
    (h : T ⟶ wFrames D) (hover : h ≫ wFramesπ D = sT)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hoverRm : (h ≫ wFramesRightMul D γ) ≫ wFramesπ D = sT)
    (hsymp' : FramedSymp D sT E (E.glSmul γ L).1.1 (E.glSmul γ L).1.2
      (E.glSmul γ L).2.1.1 (E.glSmul γ L).2.1.2
      (h ≫ wFramesRightMul D γ) hoverRm)
    (hsymp_scheme' : ∀ [Fact (1 < N)] {W : Scheme.{0}} (t : W ⟶ T)
      (x y : E.Point t)
      (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
      (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      torsionPairEval D sT t x y hx hy =
        coordPairLift D sT (framedTorsionIsoPinned D sT E hinv (E.glSmul γ L)
            (h ≫ wFramesRightMul D γ) hoverRm)
          (framedTorsionIsoPinned_π D sT E hinv (E.glSmul γ L)
            (h ≫ wFramesRightMul D γ) hoverRm) t x y hx hy ≫
          vRhoPairingMap D)
    (hsymp : FramedSymp D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 h hover)
    (hsymp_scheme : ∀ [Fact (1 < N)] {W : Scheme.{0}} (t : W ⟶ T)
      (x y : E.Point t)
      (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
      (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      torsionPairEval D sT t x y hx hy =
        coordPairLift D sT (framedTorsionIsoPinned D sT E hinv L h hover)
          (framedTorsionIsoPinned_π D sT E hinv L h hover) t x y hx hy ≫
          vRhoPairingMap D) :
    rhoLevelStructureOfFramed D sT E hinv (E.glSmul γ L)
        (h ≫ wFramesRightMul D γ) hoverRm hsymp' hsymp_scheme' =
      rhoLevelStructureOfFramed D sT E hinv L h hover hsymp hsymp_scheme :=
  RhoLevelStructure.ext_torsionIso
    (framedTorsionIsoPinned_glSmul D sT E hinv L h hover γ)

/-- **[CARVE-1a]** The cyclotomically twisted units set: `(ℤ/N)ˣ` with `σ` acting by
multiplication by the mod-`N` cyclotomic character. -/
noncomputable abbrev cycloUnitsAction (N : ℕ) [NeZero N] :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (ZMod N)ˣ
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun u => modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N) (galSepMulEquivGalQ σ).toRingEquiv * u)
      map_one' := FintypeCat.hom_ext _ _ fun u => by
        show modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N)
          (galSepMulEquivGalQ 1).toRingEquiv * u = u
        rw [map_one]
        show modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N) (1 : GalQ).toRingEquiv * u = u
        rw [show ((1 : GalQ)).toRingEquiv = RingEquiv.refl _ from rfl]
        rw [show modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N) (RingEquiv.refl _) = 1 from map_one _]
        rw [one_mul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun u => by
        show modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (card_rootsOfUnity_algClosureQ N)
          (galSepMulEquivGalQ (σ * τ)).toRingEquiv * u = _
        rw [map_mul]
        rw [show ((galSepMulEquivGalQ σ * galSepMulEquivGalQ τ)).toRingEquiv =
          (galSepMulEquivGalQ σ).toRingEquiv *
            (galSepMulEquivGalQ τ).toRingEquiv from rfl]
        rw [map_mul]
        rw [mul_assoc]
        rfl }

open scoped Pointwise FintypeCatDiscrete in
/-- **[CARVE-1a]** Continuity of the twisted units set: the cyclotomic character
kills the (open) kernel of `ρ` since it is `det ∘ ρ`. -/
lemma cycloUnitsAction_isContinuous (D : GaloisRepData N) :
    (cycloUnitsAction N).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj
          (cycloUnitsAction N) : Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (cycloUnitsAction N) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (cycloUnitsAction N),
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
  have hcy : modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (card_rootsOfUnity_algClosureQ N) (galSepMulEquivGalQ τ).toRingEquiv = 1 := by
    rw [show modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N)
        (galSepMulEquivGalQ τ).toRingEquiv =
      Matrix.GeneralLinearGroup.det (D.ρ (galSepMulEquivGalQ τ)) from
      (D.det_cyclo (galSepMulEquivGalQ τ)).symm]
    rw [hτ1, map_one]
  have hAct : (cycloUnitsAction N).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun u => ?_
    show modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (card_rootsOfUnity_algClosureQ N)
      (galSepMulEquivGalQ τ).toRingEquiv * u = u
    rw [hcy, one_mul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((cycloUnitsAction N).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

open scoped FintypeCatDiscrete in
/-- The twisted units set as a continuous Galois set. -/
noncomputable abbrev cycloUnitsContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨cycloUnitsAction N, cycloUnitsAction_isContinuous D⟩

open scoped FintypeCatDiscrete in
/-- **[CARVE-1b]** The determinant reading of frames: equivariant into the twisted
units set by `det_cyclo`. -/
noncomputable def detFrameMor (D : GaloisRepData N) :
    frameContAction D ⟶ cycloUnitsContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun A => Matrix.GeneralLinearGroup.det A)
      comm := fun σ => FintypeCat.hom_ext _ _ fun A => by
        show Matrix.GeneralLinearGroup.det (D.ρ (galSepMulEquivGalQ σ) * A) =
          modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv *
            Matrix.GeneralLinearGroup.det A
        rw [map_mul, D.det_cyclo] }

/-- **[CARVE-1c]** The finite étale algebra of the twisted units set. -/
noncomputable def cycloUnitsAlgebra (D : GaloisRepData N) :
    CommAlgCat.FiniteEtale.{0} ℚ :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.obj
    (cycloUnitsContAction D)).unop

/-- The twisted units scheme. -/
noncomputable def cycloUnitsScheme (D : GaloisRepData N) : Scheme.{0} :=
  Spec (.of (cycloUnitsAlgebra D : Type 0))

noncomputable def cycloUnitsSchemeπ (D : GaloisRepData N) :
    cycloUnitsScheme D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (cycloUnitsAlgebra D : Type 0)))

/-- **[CARVE-1c]** The determinant comultiplication and its scheme map. -/
noncomputable def detFrameAlgHom (D : GaloisRepData N) :
    cycloUnitsAlgebra D ⟶ wFramesAlgebra D :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (detFrameMor D)).unop

noncomputable def detFrameScheme (D : GaloisRepData N) :
    wFrames D ⟶ cycloUnitsScheme D :=
  Spec.map (CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom)

/-- **[CARVE-1c]** The determinant scheme map lies over `ℚ`. -/
theorem detFrameScheme_π (D : GaloisRepData N) :
    detFrameScheme D ≫ cycloUnitsSchemeπ D = wFramesπ D := by
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  exact congrArg AlgebraicGeometry.Spec.map (by
    ext r
    exact (detFrameAlgHom D).hom.hom.commutes r)

open scoped FintypeCatDiscrete in
/-- **[CARVE-1d-i]** The pairing-normalisation comparison: `u ↦ p(ofAdd u)` is
equivariant from the twisted units into the roots (by `p_equivariant`). -/
noncomputable def detCompMor (D : GaloisRepData N) [Fact (1 < N)] :
    cycloUnitsContAction D ⟶ muNRootsContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk
        (fun u => D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)))
      comm := fun σ => FintypeCat.hom_ext _ _ fun u => Subtype.ext (Units.ext (by
        show ((D.p (Multiplicative.ofAdd
            (((modularCyclotomicCharacter (AlgebraicClosure ℚ)
              (card_rootsOfUnity_algClosureQ N)
              (galSepMulEquivGalQ σ).toRingEquiv * u : (ZMod N)ˣ) :
              ZMod N))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          (galSepMulEquivGalQ σ)
            ((D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) :
              (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        rw [D.p_equivariant (galSepMulEquivGalQ σ)
          (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N))]
        congr 2
        rw [show (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^
            ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
              (card_rootsOfUnity_algClosureQ N)
              (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val =
          Multiplicative.ofAdd
            (((modularCyclotomicCharacter (AlgebraicClosure ℚ)
              (card_rootsOfUnity_algClosureQ N)
              (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val •
            ((u : (ZMod N)ˣ) : ZMod N)) from rfl]
        rw [Units.val_mul, nsmul_eq_mul]
        congr 1
        rw [show (((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N).val :
            ZMod N) =
          ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv : (ZMod N)ˣ) : ZMod N) from by
          simp only [ZMod.natCast_val, ZMod.cast_id]])) }

noncomputable def detCompAlgHom (D : GaloisRepData N) [Fact (1 < N)] :
    muNRootsAlgebra D ⟶ cycloUnitsAlgebra D :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (detCompMor D)).unop

noncomputable def detCompScheme (D : GaloisRepData N) [Fact (1 < N)] :
    cycloUnitsScheme D ⟶ muNRootsScheme D :=
  Spec.map (CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom)

theorem detCompScheme_π (D : GaloisRepData N) [Fact (1 < N)] :
    detCompScheme D ≫ muNRootsSchemeπ D = cycloUnitsSchemeπ D := by
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  exact congrArg AlgebraicGeometry.Spec.map (by
    ext r
    exact (detCompAlgHom D).hom.hom.commutes r)

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

/-- **[T-CV-2b]** The universal naive full-level structure carried by the relative
representing scheme: the image of the tautological section under the representing
bijection (the problem value over `dE.Z` itself). -/
noncomputable def univLevel {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    (gammaFullNaiveProblem (CommRingCat.of ℚ) N).obj
      (Opposite.op (X.pullbackAlong dE.f)) :=
  dE.eqv dE.f ⟨𝟙 dE.Z, Category.id_comp dE.f⟩

/-- **[T-CV-2b]** The first universal point, typed at `𝟙 dE.Z` (uniform spelling —
the `Section` carrier's `pullbackAlong`-typing is definitionally the same). -/
noncomputable def univP {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    (X.curve.baseChange dE.f).Point (𝟙 dE.Z) := (univLevel dE).1.1

/-- **[T-CV-2b]** The second universal point, typed at `𝟙 dE.Z`. -/
noncomputable def univQ {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    (X.curve.baseChange dE.f).Point (𝟙 dE.Z) := (univLevel dE).1.2

/-- **[T-CV-2b]** The first universal point is raw-killed by `N`. -/
theorem univLevel_fst_killed {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    (univP dE).1 ≫ (X.curve.baseChange dE.f).mulByHom N =
      𝟙 dE.Z ≫ (X.curve.baseChange dE.f).zero :=
  ((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
    (univP dE)).mp (univLevel dE).2.1.1

/-- **[T-CV-2b]** The second universal point is raw-killed by `N`. -/
theorem univLevel_snd_killed {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    (univQ dE).1 ≫ (X.curve.baseChange dE.f).mulByHom N =
      𝟙 dE.Z ≫ (X.curve.baseChange dE.f).zero :=
  ((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
    (univQ dE)).mp (univLevel dE).2.1.2

/-- **[T-CV-2b]** The pairing-side comparison map on the framed test space
`Z = dE.Z ×_{X.base} (X.base ×_ℚ wFrames)`: evaluate the Weil pairing on the
universal full-level pair and read the value in the roots scheme. -/
noncomputable def eZMap (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶ muNRootsScheme D :=
  pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
    pullback.lift
      ((X.curve.baseChange dE.f).pointToTorsion (univP dE)
        (univLevel_fst_killed dE))
      ((X.curve.baseChange dE.f).pointToTorsion (univQ dE)
        (univLevel_snd_killed dE))
      (((X.curve.baseChange dE.f).pointToTorsion_torsionπ _ _).trans
        ((X.curve.baseChange dE.f).pointToTorsion_torsionπ _ _).symm) ≫
    (X.curve.baseChange dE.f).weilPairing N ≫
    muNMapAlong (dE.f ≫ X.structMap) N ≫ (muNSpecQIso D).hom

/-- **[T-CV-2b]** The pairing-side comparison lies over the base. -/
theorem eZMap_π (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    eZMap D dE ≫ muNRootsSchemeπ D =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.f ≫ X.structMap := by
  rw [eZMap]
  simp only [Category.assoc]
  rw [muNSpecQIso_π, muNMapAlong_π,
    reassoc_of% ((X.curve.baseChange dE.f).weilPairing_over N),
    pullback.lift_fst_assoc]
  have htail : (X.curve.baseChange dE.f).pointToTorsion (univP dE)
      (univLevel_fst_killed dE) ≫ (X.curve.baseChange dE.f).torsionπ N ≫
      dE.f ≫ X.structMap = dE.f ≫ X.structMap :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ dE.f ≫ X.structMap)
        ((X.curve.baseChange dE.f).pointToTorsion_torsionπ _ _)).trans
        (Category.id_comp _))
  exact congrArg
    (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ ·) htail

/-- **[T-CV-2a]** The determinant-side comparison map on the framed test space:
read the frame, take its cyclotomically twisted determinant, and land in the
roots scheme. -/
noncomputable def dZMap (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶ muNRootsScheme D :=
  pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
    pullback.snd X.structMap (wFramesπ D) ≫ detFrameScheme D ≫ detCompScheme D

/-- **[T-CV-2a]** The determinant-side comparison lies over the base. -/
theorem dZMap_π (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    dZMap D dE ≫ muNRootsSchemeπ D =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.f ≫ X.structMap := by
  rw [dZMap]
  simp only [Category.assoc]
  rw [detCompScheme_π, detFrameScheme_π, ← pullback.condition,
    ← Category.assoc, ← pullback.condition, Category.assoc]

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-i]** Multiplication by a fixed unit on the cyclo-twisted units set
(equivariant since the group is abelian). -/
noncomputable def cycloUnitsMulMor (D : GaloisRepData N) (u₀ : (ZMod N)ˣ) :
    cycloUnitsContAction D ⟶ cycloUnitsContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun u => u * u₀)
      comm := fun σ => FintypeCat.hom_ext _ _ fun u => by
        show (modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv * u) * u₀ =
          modularCyclotomicCharacter (AlgebraicClosure ℚ)
            (card_rootsOfUnity_algClosureQ N)
            (galSepMulEquivGalQ σ).toRingEquiv * (u * u₀)
        rw [mul_assoc] }

/-- **[T-CV-3b-i]** Its algebra avatar. -/
noncomputable def cycloUnitsMulAlg (D : GaloisRepData N) (u₀ : (ZMod N)ˣ) :
    cycloUnitsAlgebra D ⟶ cycloUnitsAlgebra D :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (cycloUnitsMulMor D u₀)).unop

/-- **[T-CV-3b-i]** Its scheme avatar. -/
noncomputable def cycloUnitsMulScheme (D : GaloisRepData N) (u₀ : (ZMod N)ˣ) :
    cycloUnitsScheme D ⟶ cycloUnitsScheme D :=
  Spec.map (CommRingCat.ofHom (cycloUnitsMulAlg D u₀).hom.hom.toRingHom)

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-i]** The determinant intertwines right translation with unit
multiplication (`det (A·γ) = det A · det γ`), continuous-set level. -/
theorem detFrameMor_rightMul (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameRightMulMor D γ ≫ detFrameMor D =
      detFrameMor D ≫ cycloUnitsMulMor D (Matrix.GeneralLinearGroup.det γ) := by
  ext A
  exact congrArg (fun w : (ZMod N)ˣ => ((w : ZMod N)))
    (map_mul Matrix.GeneralLinearGroup.det A γ)

/-- **[T-CV-3b-i]** The scheme-level square (double contravariance = covariance;
`wFramesRightMul_mul` transport pattern). -/
theorem detFrameScheme_rightMul (D : GaloisRepData N)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    wFramesRightMul D γ ≫ detFrameScheme D =
      detFrameScheme D ≫ cycloUnitsMulScheme D (Matrix.GeneralLinearGroup.det γ) := by
  have hAlg : detFrameAlgHom D ≫ wFramesRightMulAlg D γ =
      cycloUnitsMulAlg D (Matrix.GeneralLinearGroup.det γ) ≫ detFrameAlgHom D := by
    have h2 := congrArg
      (fun m => ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m).unop)
      (detFrameMor_rightMul D γ)
    exact ((congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp _ _)).symm.trans
      h2).trans (congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp _ _))
  show Spec.map (CommRingCat.ofHom (wFramesRightMulAlg D γ).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (detFrameAlgHom D).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (cycloUnitsMulAlg D (Matrix.GeneralLinearGroup.det γ)).hom.hom.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg
    (fun (m : cycloUnitsAlgebra D ⟶ wFramesAlgebra D) =>
      CommRingCat.ofHom m.hom.hom.toRingHom) hAlg)

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-ii]** The `k`-th power endo of the roots set — equivariant for EVERY
`k` (Galois commutes with powers), unlike constant multiplication. -/
noncomputable def muNRootsPowMor (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsContAction D ⟶ muNRootsContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun ζ => ζ ^ k)
      comm := fun σ => FintypeCat.hom_ext _ _ fun ζ => Subtype.ext (Units.ext (by
        show ((Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom ζ.1 ^ k :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          ((Units.map (galSepMulEquivGalQ σ).toAlgHom.toMonoidHom (ζ ^ k).1 :
            (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        rw [← map_pow]
        rfl)) }

/-- **[T-CV-3b-ii]** Its algebra avatar. -/
noncomputable def muNRootsPowAlg (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsAlgebra D ⟶ muNRootsAlgebra D :=
  ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
    (muNRootsPowMor D k)).unop

/-- **[T-CV-3b-ii]** Its scheme avatar. -/
noncomputable def muNRootsPowScheme (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsScheme D ⟶ muNRootsScheme D :=
  Spec.map (CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom)

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-ii]** The pairing normalisation intertwines unit multiplication with
the power endo (`p(ofAdd (u·u₀)) = p(ofAdd u)^{u₀.val}`). -/
theorem detCompMor_mul (D : GaloisRepData N) [Fact (1 < N)] (u₀ : (ZMod N)ˣ) :
    cycloUnitsMulMor D u₀ ≫ detCompMor D =
      detCompMor D ≫ muNRootsPowMor D ((u₀ : ZMod N)).val := by
  ext u
  show ((D.p (Multiplicative.ofAdd (((u * u₀ : (ZMod N)ˣ) : ZMod N))) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    (((D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^
        ((u₀ : ZMod N)).val : rootsOfUnity N (AlgebraicClosure ℚ)) :
      (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  rw [show ((D.p (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^
      ((u₀ : ZMod N)).val : rootsOfUnity N (AlgebraicClosure ℚ)) :
      (AlgebraicClosure ℚ)ˣ) =
    ((D.p ((Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^
      ((u₀ : ZMod N)).val)) : (AlgebraicClosure ℚ)ˣ) from by
    rw [map_pow]]
  congr 2
  rw [show (Multiplicative.ofAdd ((u : (ZMod N)ˣ) : ZMod N)) ^
      ((u₀ : ZMod N)).val =
    Multiplicative.ofAdd (((u₀ : ZMod N)).val •
      ((u : (ZMod N)ˣ) : ZMod N)) from rfl]
  rw [Units.val_mul, nsmul_eq_mul]
  rw [show ((((u₀ : ZMod N)).val : ZMod N)) = ((u₀ : ZMod N)) from by
    simp only [ZMod.natCast_val, ZMod.cast_id]]
  rw [mul_comm]

/-- **[T-CV-3b-ii]** The scheme-level square. -/
theorem detCompScheme_mul (D : GaloisRepData N) [Fact (1 < N)] (u₀ : (ZMod N)ˣ) :
    cycloUnitsMulScheme D u₀ ≫ detCompScheme D =
      detCompScheme D ≫ muNRootsPowScheme D ((u₀ : ZMod N)).val := by
  have hAlg : detCompAlgHom D ≫ cycloUnitsMulAlg D u₀ =
      muNRootsPowAlg D ((u₀ : ZMod N)).val ≫ detCompAlgHom D := by
    have h2 := congrArg
      (fun m => ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map m).unop)
      (detCompMor_mul D u₀)
    exact ((congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp _ _)).symm.trans
      h2).trans (congrArg Quiver.Hom.unop
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map_comp _ _))
  show Spec.map (CommRingCat.ofHom (cycloUnitsMulAlg D u₀).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (detCompAlgHom D).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (muNRootsPowAlg D ((u₀ : ZMod N)).val).hom.hom.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg
    (fun (m : muNRootsAlgebra D ⟶ cycloUnitsAlgebra D) =>
      CommRingCat.ofHom m.hom.hom.toRingHom) hAlg)

/-- **[T-CV-3b]** The determinant-side comparison twists by the power endo under the
diagonal action. -/
theorem dZMap_zxAction (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxAction D dE γ ≫ dZMap D dE =
      dZMap D dE ≫ muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  rw [dZMap]
  rw [← Category.assoc, zxAction_snd]
  simp only [Category.assoc]
  rw [reassoc_of% (wxAction_snd D X γ),
    reassoc_of% (detFrameScheme_rightMul D γ),
    detCompScheme_mul D (Matrix.GeneralLinearGroup.det γ)]

/-- **[T-CV-3b-iii-i]** The inverse of the DS3 bridge lies over the base. -/
theorem muNSpecQIso_π_inv (D : GaloisRepData N) [Fact (1 < N)] :
    (muNSpecQIso D).inv ≫ muNπ (Spec (CommRingCat.of ℚ)) N =
      muNRootsSchemeπ D := by
  rw [Iso.inv_comp_eq, muNSpecQIso_π]

/-- **[T-CV-3b-iii-i]** The `Γ`-read of a map into the roots scheme, through the DS3
bridge and the `μ_N`-points dictionary. -/
noncomputable def muNRootsRead (D : GaloisRepData N) [Fact (1 < N)] {W : Scheme.{0}}
    (b : W ⟶ Spec (CommRingCat.of ℚ)) (φ : W ⟶ muNRootsScheme D)
    (hφ : φ ≫ muNRootsSchemeπ D = b) : Γ(W, ⊤) :=
  (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N b
    ⟨φ ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, hφ]⟩ : Γ(W, ⊤))

/-- **[T-CV-3b-iii-i]** Maps into the roots scheme over a common base are determined
by their `Γ`-reads. -/
theorem muNRoots_hom_ext (D : GaloisRepData N) [Fact (1 < N)] {W : Scheme.{0}}
    {b : W ⟶ Spec (CommRingCat.of ℚ)} {φ ψ : W ⟶ muNRootsScheme D}
    (hφ : φ ≫ muNRootsSchemeπ D = b) (hψ : ψ ≫ muNRootsSchemeπ D = b)
    (h : muNRootsRead D b φ hφ = muNRootsRead D b ψ hψ) : φ = ψ := by
  have h3 := congrArg Subtype.val
    ((muNPointsEquiv (Spec (CommRingCat.of ℚ)) N b).injective (Subtype.ext h))
  have h4 : φ ≫ (muNSpecQIso D).inv = ψ ≫ (muNSpecQIso D).inv := h3
  calc φ = (φ ≫ (muNSpecQIso D).inv) ≫ (muNSpecQIso D).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (ψ ≫ (muNSpecQIso D).inv) ≫ (muNSpecQIso D).hom :=
        congrArg (· ≫ (muNSpecQIso D).hom) h4
    _ = ψ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **[T-CV-3b-iii-v-b]** The model-side power endomorphism of the cyclotomic
quotient (`root ↦ root^k`). -/
noncomputable def cycloQuotPowAlgHom (N : ℕ) [NeZero N] (k : ℕ) :
    (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ]
      (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ _)
    ((AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ k) (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, ← pow_mul, mul_comm k N, pow_mul, cycloRoot_pow,
        one_pow]
      exact sub_self 1)

theorem cycloQuotPowAlgHom_root (N : ℕ) [NeZero N] (k : ℕ) :
    cycloQuotPowAlgHom N k (AdjoinRoot.root _) =
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)) ^ k :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **[T-CV-3b-iii-v-b]** As a finite étale hom. -/
noncomputable def cycloQuotPow (N : ℕ) [NeZero N] (k : ℕ) :
    cycloQuotAlgebra N ⟶ cycloQuotAlgebra N :=
  ObjectProperty.homMk (CommAlgCat.ofHom (cycloQuotPowAlgHom N k))

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-b]** The correspondence intertwines the model power with the
roots power (elementwise: `mkOfPowEq`-reads raise to the `k`-th power; the functor
acts by the fiber via `finiteEtaleEquivContAction_functor_map_hom`). -/
theorem muNRootsCorrespondence_pow (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (cycloQuotPow N k)) ≫ (muNRootsCorrespondenceIso D).hom =
      (muNRootsCorrespondenceIso D).hom ≫ muNRootsPowMor D k := by
  ext φ
  have h1 : rootsSepQbarEquiv N (cycloAlgHomEquivRoots N (SeparableClosure ℚ)
      ((show (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ]
          SeparableClosure ℚ from φ).comp (cycloQuotPowAlgHom N k))) =
      (rootsSepQbarEquiv N (cycloAlgHomEquivRoots N (SeparableClosure ℚ)
        (show (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ]
          SeparableClosure ℚ from φ))) ^ k := by
    refine Subtype.ext (Units.ext ?_)
    show sepClosureQAlgEquiv (((show (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^
        N - 1)) →ₐ[ℚ] SeparableClosure ℚ from φ).comp (cycloQuotPowAlgHom N k))
        (AdjoinRoot.root _)) = _
    rw [AlgHom.comp_apply]
    refine Eq.trans (congrArg (fun z => sepClosureQAlgEquiv
        ((show (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ N - 1)) →ₐ[ℚ]
          SeparableClosure ℚ from φ) z))
      (cycloQuotPowAlgHom_root N k)) ?_
    rw [map_pow, map_pow]
    rfl
  rw [show ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (cycloQuotPow N k)) ≫
        (muNRootsCorrespondenceIso D).hom).hom.hom =
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).functor.map
        (Quiver.Hom.op (cycloQuotPow N k))).hom.hom ≫
        (muNRootsCorrespondenceIso D).hom.hom.hom from rfl,
    show ((muNRootsCorrespondenceIso D).hom ≫ muNRootsPowMor D k).hom.hom =
      (muNRootsCorrespondenceIso D).hom.hom.hom ≫
        (muNRootsPowMor D k).hom.hom from rfl,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    FiniteEtaleGalois.finiteEtaleEquivContAction_functor_map_hom]
  exact congrArg (fun w : rootsOfUnity N (AlgebraicClosure ℚ) =>
    ((w : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h1

section GeneralConjugateMoved
end GeneralConjugateMoved

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-c]** The algebra-side power square, in the composite form of the
transported identification (`unit ≫ inverse.map corr`, unopped). -/
theorem muNRootsPowAlg_square' (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsPowAlg D k ≫
        (((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (muNRootsCorrespondenceIso D).hom).unop ≫
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
          (Opposite.op (cycloQuotAlgebra N))).unop) =
      ((((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
          (muNRootsCorrespondenceIso D).hom).unop ≫
        ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
          (Opposite.op (cycloQuotAlgebra N))).unop)) ≫ cycloQuotPow N k := by
  have hop := equivalence_unit_conjugate_square
    (FiniteEtaleGalois.finiteEtaleEquivContAction ℚ)
    (muNRootsCorrespondenceIso D) (Quiver.Hom.op (cycloQuotPow N k))
    (muNRootsPowMor D k) (muNRootsCorrespondence_pow D k)
  have h2 := congrArg Quiver.Hom.unop hop
  simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc] at h2
  simp only [Category.assoc]
  exact h2.symm

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-d]** The transported identification in composite form
(definitional: every layer is a record projection). -/
theorem muNRootsAlgebraIso_hom_eq (D : GaloisRepData N) [Fact (1 < N)] :
    (muNRootsAlgebraIso D).hom =
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.map
        (muNRootsCorrespondenceIso D).hom).unop ≫
      ((FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).unitIso.hom.app
        (Opposite.op (cycloQuotAlgebra N))).unop := rfl

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-d]** The algebra-side pow square, iso form. -/
theorem muNRootsPowAlg_square (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsPowAlg D k ≫ (muNRootsAlgebraIso D).hom =
      (muNRootsAlgebraIso D).hom ≫ cycloQuotPow N k := by
  rw [muNRootsAlgebraIso_hom_eq]
  exact muNRootsPowAlg_square' D k

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-d]** The algebra-side pow square, inverse form. -/
theorem muNRootsPowAlg_square_inv (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    (muNRootsAlgebraIso D).inv ≫ muNRootsPowAlg D k =
      cycloQuotPow N k ≫ (muNRootsAlgebraIso D).inv := by
  rw [Iso.inv_comp_eq]
  calc muNRootsPowAlg D k
      = (muNRootsPowAlg D k ≫ (muNRootsAlgebraIso D).hom) ≫
          (muNRootsAlgebraIso D).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((muNRootsAlgebraIso D).hom ≫ cycloQuotPow N k) ≫
          (muNRootsAlgebraIso D).inv :=
        congrArg (· ≫ (muNRootsAlgebraIso D).inv) (muNRootsPowAlg_square D k)
    _ = (muNRootsAlgebraIso D).hom ≫ cycloQuotPow N k ≫
          (muNRootsAlgebraIso D).inv := Category.assoc _ _ _

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-e]** The Spec-side pow intertwine against the roots
identification. -/
theorem muNRootsPowScheme_specIso (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsPowScheme D k ≫ (muNRootsSpecIso D).inv =
      (muNRootsSpecIso D).inv ≫
        Spec.map (CommRingCat.ofHom (cycloQuotPowAlgHom N k).toRingHom) := by
  show Spec.map (CommRingCat.ofHom (muNRootsPowAlg D k).hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (muNRootsAlgebraIso D).inv.hom.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (muNRootsAlgebraIso D).inv.hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (cycloQuotPowAlgHom N k).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg
    (fun (m : cycloQuotAlgebra N ⟶ muNRootsAlgebra D) =>
      CommRingCat.ofHom m.hom.hom.toRingHom) (muNRootsPowAlg_square_inv D k))

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-e]** The roots power lies over the base. -/
theorem muNRootsPowScheme_π (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsPowScheme D k ≫ muNRootsSchemeπ D = muNRootsSchemeπ D := by
  refine Eq.trans (AlgebraicGeometry.Spec.map_comp _ _).symm ?_
  exact congrArg AlgebraicGeometry.Spec.map (by
    ext r
    exact (muNRootsPowAlg D k).hom.hom.commutes r)

/-- **[T-CV-3b-iii-v-e]** The two model pows agree. -/
theorem cycloQuotPow_eq_model (N : ℕ) [NeZero N] (k : ℕ) :
    cycloQuotPowAlgHom N k = muNModelPowAlgHom ℚ N k :=
  AdjoinRoot.algHom_ext (by
    rw [cycloQuotPowAlgHom_root, muNModelPowAlgHom_root])

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-e]** The power endo through the DS3 bridge is `muNPow`. -/
theorem muNRootsPowScheme_QIso (D : GaloisRepData N) [Fact (1 < N)] (k : ℕ) :
    muNRootsPowScheme D k ≫ (muNSpecQIso D).inv =
      (muNSpecQIso D).inv ≫ muNPow (Spec (CommRingCat.of ℚ)) N k := by
  rw [show (muNSpecQIso D).inv =
    (muNRootsSpecIso D).inv ≫ (muNSpecFieldIso ℚ N).inv from rfl]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ (muNSpecFieldIso ℚ N).inv)
    (muNRootsPowScheme_specIso D k)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((muNRootsSpecIso D).inv ≫ ·) ?_)
    (Category.assoc _ _ _).symm
  rw [show (cycloQuotPowAlgHom N k) = muNModelPowAlgHom ℚ N k from
    cycloQuotPow_eq_model N k]
  exact muNSpecFieldIso_pow ℚ N k

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-v-e]** The `Γ`-read of the power endo is the power of the read. -/
theorem muNRootsRead_pow (D : GaloisRepData N) [Fact (1 < N)] {W : Scheme.{0}}
    (b : W ⟶ Spec (CommRingCat.of ℚ)) (φ : W ⟶ muNRootsScheme D)
    (hφ : φ ≫ muNRootsSchemeπ D = b) (k : ℕ) :
    muNRootsRead D b (φ ≫ muNRootsPowScheme D k) (by
        rw [Category.assoc, muNRootsPowScheme_π, hφ]) =
      muNRootsRead D b φ hφ ^ k := by
  have hkey : (φ ≫ muNRootsPowScheme D k) ≫ (muNSpecQIso D).inv =
      (φ ≫ (muNSpecQIso D).inv) ≫ muNPow (Spec (CommRingCat.of ℚ)) N k :=
    (Category.assoc _ _ _).trans
      ((congrArg (φ ≫ ·) (muNRootsPowScheme_QIso D k)).trans
        (Category.assoc _ _ _).symm)
  have hsub : (⟨(φ ≫ muNRootsPowScheme D k) ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, Category.assoc,
        muNRootsPowScheme_π, hφ]⟩ :
      { h : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        h ≫ muNπ (Spec (CommRingCat.of ℚ)) N = b }) =
    ⟨(φ ≫ (muNSpecQIso D).inv) ≫ muNPow (Spec (CommRingCat.of ℚ)) N k, by
      rw [Category.assoc, muNPow_π, Category.assoc, muNSpecQIso_π_inv, hφ]⟩ :=
    Subtype.ext hkey
  refine Eq.trans (congrArg
    (fun v : { h : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        h ≫ muNπ (Spec (CommRingCat.of ℚ)) N = b } =>
      (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N b v : Γ(W, ⊤))) hsub) ?_
  exact muNPointsEquiv_pow (Spec (CommRingCat.of ℚ)) N b
    ⟨φ ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, hφ]⟩ k

/-- **[T-CV-3a]** The roots-scheme structure map is finite étale
(`vRhoπ_finite_etale` mirror). -/
theorem muNRootsSchemeπ_finite_etale (D : GaloisRepData N) [Fact (1 < N)] :
    IsFinite (muNRootsSchemeπ D) ∧ Etale (muNRootsSchemeπ D) := by
  constructor
  · show IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (muNRootsAlgebra D : Type 0))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · show Etale (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (muNRootsAlgebra D : Type 0))))
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance

/-- **[T-CV-3a]** The paired comparison into the fibre square of the roots scheme. -/
noncomputable def sympPair (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶
      pullback (muNRootsSchemeπ D) (muNRootsSchemeπ D) :=
  pullback.lift (eZMap D dE) (dZMap D dE)
    ((eZMap_π D dE).trans (dZMap_π D dE).symm)

/-- **[T-CV-3a]** The symplectic locus: the agreement locus of the pairing-side and
determinant-side comparisons, as the pullback of the diagonal of the roots scheme. -/
noncomputable def sympLocus (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) : Scheme.{0} :=
  pullback (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE)

/-- **[T-CV-3a]** Its inclusion into the framed test space. -/
noncomputable def sympLocusι (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    sympLocus D dE ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D)) :=
  pullback.snd _ _

/-- **[T-CV-3a]** The inclusion is an open immersion (unramified + finite-type
diagonal). -/
theorem sympLocusι_isOpenImmersion (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    IsOpenImmersion (sympLocusι D dE) := by
  haveI : Etale (muNRootsSchemeπ D) := (muNRootsSchemeπ_finite_etale D).2
  haveI : IsFinite (muNRootsSchemeπ D) := (muNRootsSchemeπ_finite_etale D).1
  show IsOpenImmersion
    (pullback.snd (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE))
  infer_instance

/-- **[T-CV-3a]** The inclusion is a closed immersion (separated diagonal). -/
theorem sympLocusι_isClosedImmersion (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    IsClosedImmersion (sympLocusι D dE) := by
  haveI : IsSeparated (muNRootsSchemeπ D) :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (muNRootsAlgebra D : Type 0)))))
  show IsClosedImmersion
    (pullback.snd (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE))
  exact MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance

/-- **[T-CV-3(c-i), map-level core]** Factoring through the symplectic locus is
exactly the agreement of the two comparison maps. -/
theorem sympLocus_factor_iff (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}}
    (h : T ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D))) :
    (∃ w : T ⟶ sympLocus D dE, w ≫ sympLocusι D dE = h) ↔
      h ≫ eZMap D dE = h ≫ dZMap D dE := by
  have hcond : sympLocusι D dE ≫ sympPair D dE =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE) ≫
        pullback.diagonal (muNRootsSchemeπ D) :=
    pullback.condition.symm
  have hιe : sympLocusι D dE ≫ eZMap D dE =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE) :=
    (congrArg (sympLocusι D dE ≫ ·) (pullback.lift_fst _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst (muNRootsSchemeπ D) (muNRootsSchemeπ D))
            hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
                (sympPair D dE) ≫ ·) (pullback.diagonal_fst _)).trans
              (Category.comp_id _)))))
  have hιd : sympLocusι D dE ≫ dZMap D dE =
      pullback.fst (pullback.diagonal (muNRootsSchemeπ D)) (sympPair D dE) :=
    (congrArg (sympLocusι D dE ≫ ·) (pullback.lift_snd _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd (muNRootsSchemeπ D) (muNRootsSchemeπ D))
            hcond).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (pullback.fst (pullback.diagonal (muNRootsSchemeπ D))
                (sympPair D dE) ≫ ·) (pullback.diagonal_snd _)).trans
              (Category.comp_id _)))))
  constructor
  · rintro ⟨w, rfl⟩
    rw [Category.assoc, Category.assoc, hιe, hιd]
  · intro he
    refine ⟨pullback.lift (h ≫ eZMap D dE) h ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id,
        sympPair, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id,
        sympPair, Category.assoc, pullback.lift_snd]
      exact he

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b-iii-ii]** The `Γ`-read of the pairing-side comparison at a test map is
the Weil-pairing evaluation of the universal pair, restricted along the test
(all identity-morphisms spelled at `(X.pullbackAlong dE.f).base`, the typing forced
by the `Section` carrier). -/
theorem eZMap_read (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}}
    (h : T ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D))) :
    muNRootsRead D
        ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
          (dE.f ≫ X.structMap))
        (h ≫ eZMap D dE) (by
          rw [Category.assoc, eZMap_π]
          simp only [Category.assoc]) =
      (Scheme.Γ.map (h ≫ pullback.fst dE.f
          (pullback.fst X.structMap (wFramesπ D))).op).hom
        ((X.curve.baseChange dE.f).weilPairingEval (univP dE)
          (univQ dE) (univLevel_fst_killed dE)
          (univLevel_snd_killed dE)).1 := by
  have hw : (X.curve.baseChange dE.f).pointToTorsion (univP dE)
      (univLevel_fst_killed dE) ≫ (X.curve.baseChange dE.f).torsionπ N =
    (X.curve.baseChange dE.f).pointToTorsion (univQ dE)
      (univLevel_snd_killed dE) ≫ (X.curve.baseChange dE.f).torsionπ N := by simp
  have hover : pullback.lift ((X.curve.baseChange dE.f).pointToTorsion
        (univP dE) (univLevel_fst_killed dE))
      ((X.curve.baseChange dE.f).pointToTorsion
        (univQ dE) (univLevel_snd_killed dE)) hw ≫
      (X.curve.baseChange dE.f).weilPairing N ≫ muNπ dE.Z N =
      𝟙 dE.Z := by
    rw [(X.curve.baseChange dE.f).weilPairing_over N, ← Category.assoc,
      pullback.lift_fst, (X.curve.baseChange dE.f).pointToTorsion_torsionπ]
  have hcancel : (h ≫ eZMap D dE) ≫ (muNSpecQIso D).inv =
      (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        ((pullback.lift ((X.curve.baseChange dE.f).pointToTorsion
              (univLevel dE).1.1 (univLevel_fst_killed dE))
            ((X.curve.baseChange dE.f).pointToTorsion
              (univLevel dE).1.2 (univLevel_snd_killed dE)) hw ≫
          (X.curve.baseChange dE.f).weilPairing N) ≫
          muNMapAlong (dE.f ≫ X.structMap) N) := by
    rw [eZMap]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id, Category.comp_id]
    try simp only [Category.assoc]
    try rfl
  have hsub1 : (⟨(h ≫ eZMap D dE) ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, Category.assoc, eZMap_π]
      simp only [Category.assoc]⟩ :
      { m : T ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N =
          (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            (dE.f ≫ X.structMap) }) =
    ⟨((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        (pullback.lift ((X.curve.baseChange dE.f).pointToTorsion
            (univP dE) (univLevel_fst_killed dE))
          ((X.curve.baseChange dE.f).pointToTorsion
            (univQ dE) (univLevel_snd_killed dE)) hw ≫
        (X.curve.baseChange dE.f).weilPairing N)) ≫
        muNMapAlong (dE.f ≫ X.structMap) N, by
      try simp only [Category.assoc]
      rw [muNMapAlong_π]
      try simp only [Category.assoc]
      rw [reassoc_of% hover]
      try simp only [Category.id_comp]⟩ :=
    Subtype.ext (hcancel.trans (Category.assoc _ _ _).symm)
  refine Eq.trans (congrArg
    (fun v : { m : T ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N =
          (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            (dE.f ≫ X.structMap) } =>
      (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N _ v : Γ(T, ⊤))) hsub1) ?_
  refine Eq.trans (muNPointsEquiv_mapAlong (dE.f ≫ X.structMap) N
    (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)))
    ⟨(h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        (pullback.lift ((X.curve.baseChange dE.f).pointToTorsion
            (univP dE) (univLevel_fst_killed dE))
          ((X.curve.baseChange dE.f).pointToTorsion
            (univQ dE) (univLevel_snd_killed dE)) hw ≫
        (X.curve.baseChange dE.f).weilPairing N), by
      try simp only [Category.assoc]
      rw [hover]
      exact congrArg (h ≫ ·) (Category.comp_id _)⟩) ?_
  have hnat := muNPointsEquiv_natural dE.Z N
    (𝟙 dE.Z)
    (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)))
    ⟨pullback.lift ((X.curve.baseChange dE.f).pointToTorsion
        (univP dE) (univLevel_fst_killed dE))
      ((X.curve.baseChange dE.f).pointToTorsion
        (univQ dE) (univLevel_snd_killed dE)) hw ≫
      (X.curve.baseChange dE.f).weilPairing N, hover⟩
  refine Eq.trans ?_ hnat
  refine congrArg
    (fun v : { m : T ⟶ muN dE.Z N //
        m ≫ muNπ dE.Z N =
          (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            𝟙 dE.Z } =>
      (muNPointsEquiv dE.Z N _ v : Γ(T, ⊤))) ?_
  exact Subtype.ext rfl

/-- **[T-CV-3b-iii-iii]** The `γ`-translated tautological section classifies the
`glSmul`-acted universal level structure (the equivariance of the relative datum at
the tautological section, with the `gammaHAut` double inverse collapsed). -/
theorem univLevel_zx {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    dE.eqv dE.f ⟨dE.σZ.hom (Subgroup.topEquiv.symm γ), dE.over_base _⟩ =
      (X.pullbackAlong dE.f).curve.glSmul γ (univLevel dE) := by
  have h := dE.equivariant dE.f ⟨𝟙 dE.Z, Category.id_comp dE.f⟩
    (Subgroup.topEquiv.symm γ)
  refine Eq.trans (congrArg (dE.eqv dE.f)
    (Subtype.ext (Category.id_comp _).symm)) (h.trans ?_)
  show ((X.pullbackAlong dE.f).curve.glSmul
    ((((Subgroup.topEquiv.symm γ)⁻¹ : (⊤ : Subgroup
        (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))))⁻¹ :
      (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) :
      Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (univLevel dE)) = _
  rw [inv_inv]
  rfl

/-- **[T-CV-3b-iii-iv]** The Weil pairing of the `glSmul`-combined universal pair is
the `det`-power of the universal pairing (the registered symplectic formula at the
universal level — no geometric points needed). -/
theorem univLevel_glSmul_eval {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ((X.curve.baseChange dE.f).weilPairingEval
        ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • univP dE +
          (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • univQ dE)
        ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • univP dE +
          (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • univQ dE)
        (((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
            _).mp (comb_kill (univLevel dE).2.1.1 (univLevel dE).2.1.2 _ _))
        (((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
            _).mp (comb_kill (univLevel dE).2.1.1 (univLevel dE).2.1.2 _ _))).1 =
      ((X.curve.baseChange dE.f).weilPairingEval (univP dE) (univQ dE)
        (univLevel_fst_killed dE) (univLevel_snd_killed dE)).1 ^
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  set m : Matrix (Fin 2) (Fin 2) (ZMod N) := (γ : Matrix (Fin 2) (Fin 2) (ZMod N))
    with hm
  have hW := (X.curve.baseChange dE.f).weilPairingEval_symplectic
    (univP dE) (univQ dE)
    (((m 0 0).val : ℤ)) (((m 1 0).val : ℤ)) (((m 0 1).val : ℤ))
    (((m 1 1).val : ℤ))
    (univLevel_fst_killed dE) (univLevel_snd_killed dE)
    (((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
        _).mp (comb_kill (univLevel dE).2.1.1 (univLevel dE).2.1.2 _ _))
    (((X.curve.baseChange dE.f).smul_eq_zero_iff_comp_mulByHom (𝟙 dE.Z) N
        _).mp (comb_kill (univLevel dE).2.1.1 (univLevel dE).2.1.2 _ _))
  refine hW.trans ?_
  congr 1
  have hcoedet : ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      ((((m 0 0).val : ℤ) * ((m 1 1).val : ℤ) -
        ((m 1 0).val : ℤ) * ((m 0 1).val : ℤ) : ℤ) : ZMod N) := by
    rw [show ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) (ZMod N)).det from rfl, Matrix.det_fin_two]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [hcoedet]
  exact ((congrArg Int.toNat (ZMod.val_intCast _)).symm.trans
    (Int.toNat_natCast _))

/-- [T-CV-3b-iii helper] The pairing evaluation is congruent along a base-map equality
and raw component equalities (crosses `Point` types over propositionally equal
classifying maps). -/
theorem weilPairingEval_congr_raw {T T' : Scheme.{0}} {E : EllipticCurve T}
    {t t' : T' ⟶ T} (htt : t = t') {x y : E.Point t} {x' y' : E.Point t'}
    (hx : x.1 = x'.1) (hy : y.1 = y'.1)
    (kx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (ky : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (kx' : x'.1 ≫ E.mulByHom N = t' ≫ E.zero)
    (ky' : y'.1 ≫ E.mulByHom N = t' ≫ E.zero) :
    (E.weilPairingEval x y kx ky).1 = (E.weilPairingEval x' y' kx' ky').1 := by
  subst htt
  have hxx : x = x' := Subtype.ext hx
  have hyy : y = y' := Subtype.ext hy
  subst hxx; subst hyy
  rfl

/-- [T-CV-3b-iii helper] The pairing evaluation of a full-level structure is invariant
under the `eqToHom`-transport along an equality of classifying maps (the transport is
the identity after `subst`; stated in the composite form `RelRepData.eqv_congr`
produces, with every point `show`-ascribed to the uniform `𝟙 T` spelling). -/
theorem fullLevel_eval_eqToHom {X : EllObj (CommRingCat.of ℚ)} {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ X.base} (hg : g₁ = g₂)
    (v : (gammaFullNaiveProblem (CommRingCat.of ℚ) N).obj
      (Opposite.op (X.pullbackAlong g₁))) :
    ((X.curve.baseChange g₂).weilPairingEval
        (show (X.curve.baseChange g₂).Point (𝟙 T) from
          ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
            (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg))
            v).1.1)
        (show (X.curve.baseChange g₂).Point (𝟙 T) from
          ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
            (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg))
            v).1.2)
        (((X.curve.baseChange g₂).smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
            (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg))
            v).2.1.1)
        (((X.curve.baseChange g₂).smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
            (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hg))
            v).2.1.2)).1 =
      ((X.curve.baseChange g₁).weilPairingEval
        (show (X.curve.baseChange g₁).Point (𝟙 T) from v.1.1)
        (show (X.curve.baseChange g₁).Point (𝟙 T) from v.1.2)
        (((X.curve.baseChange g₁).smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          v.2.1.1)
        (((X.curve.baseChange g₁).smul_eq_zero_iff_comp_mulByHom (𝟙 T) N _).mp
          v.2.1.2)).1 := by
  subst hg
  have hEQ : (gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
      (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t))
        (rfl : g₁ = g₁))) v = v :=
    FunctorToTypes.map_id_apply _ v
  exact weilPairingEval_congr_raw rfl (congrArg (fun w => w.1.1.1) hEQ)
    (congrArg (fun w => w.1.2.1) hEQ) _ _ _ _

/-- [T-CV-3b-iii-v] The `γ`-transported first universal point (the functorial pull of
`univP` along the `σZ γ`-translation), typed uniformly at `𝟙 dE.Z`. -/
noncomputable def univPzx {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (X.curve.baseChange (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).Point
      (𝟙 dE.Z) :=
  ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
      (univLevel dE)).1.1

/-- [T-CV-3b-iii-v] The `γ`-transported second universal point, typed uniformly at
`𝟙 dE.Z`. -/
noncomputable def univQzx {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (X.curve.baseChange (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).Point
      (𝟙 dE.Z) :=
  ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
      (univLevel dE)).1.2

/-- [T-CV-3b-iii-v] The transported first universal point is raw-killed by `N`. -/
theorem univPzx_killed {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (univPzx dE γ).1 ≫
        (X.curve.baseChange
          (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).mulByHom N =
      𝟙 dE.Z ≫
        (X.curve.baseChange (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).zero :=
  ((X.curve.baseChange
      (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).smul_eq_zero_iff_comp_mulByHom
    (𝟙 dE.Z) N (univPzx dE γ)).mp
    ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
      (univLevel dE)).2.1.1

/-- [T-CV-3b-iii-v] The transported second universal point is raw-killed by `N`. -/
theorem univQzx_killed {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (univQzx dE γ).1 ≫
        (X.curve.baseChange
          (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).mulByHom N =
      𝟙 dE.Z ≫
        (X.curve.baseChange (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).zero :=
  ((X.curve.baseChange
      (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f)).smul_eq_zero_iff_comp_mulByHom
    (𝟙 dE.Z) N (univQzx dE γ)).mp
    ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
      (univLevel dE)).2.1.2

/-- **[T-CV-3b-iii-v(H3)]** Restriction of the universal pairing value along the
`γ`-translation of the representing scheme is the `det γ`-power: the Γ-read of the
`σZ γ`-pullback of `e_N(univP, univQ)` (the value-chain through the equivariance of
the relative datum, crossed to the pairing side by the DS4 registers). -/
theorem univLevel_eval_restrict {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (Scheme.Γ.map (dE.σZ.hom (Subgroup.topEquiv.symm γ)).op).hom
      ((X.curve.baseChange dE.f).weilPairingEval (univP dE) (univQ dE)
        (univLevel_fst_killed dE) (univLevel_snd_killed dE)).1 =
      ((X.curve.baseChange dE.f).weilPairingEval (univP dE) (univQ dE)
        (univLevel_fst_killed dE) (univLevel_snd_killed dE)).1 ^
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  have hover : dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f = dE.f := dE.over_base _
  -- the value chain: the transported universal structure is the `glSmul`-acted one
  have h1 := dE.nat dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))
    ⟨𝟙 dE.Z, Category.id_comp dE.f⟩
  have h2 := ModuliProblem.RelRepData.eqv_congr dE.toRelRepData hover
    (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ 𝟙 dE.Z) (by rw [Category.comp_id])
  have h3 := relRep_eqv_congr dE.toRelRepData dE.f
    (Category.comp_id (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
    ((by rw [Category.comp_id] :
      (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ 𝟙 dE.Z) ≫ dE.f =
        dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ dE.f).trans hover)
  have h4 := univLevel_zx dE γ
  have hVAL : (X.pullbackAlong dE.f).curve.glSmul γ (univLevel dE) =
      (gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
        (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hover))
        ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
          (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
          (univLevel dE)) :=
    h4.symm.trans (h3.symm.trans (h2.trans (congrArg
      (fun z => (gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
        (eqToHom (congrArg (fun t => Opposite.op (X.pullbackAlong t)) hover)) z)
      h1)))
  -- the restricted points' kill facts
  have kres₁ : (EllipticCurve.Point.restrict (X.curve.baseChange dE.f)
        (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (univP dE)).1 ≫
        (X.curve.baseChange dE.f).mulByHom N =
      (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ 𝟙 dE.Z) ≫
        (X.curve.baseChange dE.f).zero := by
    show (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ (univP dE).1) ≫ _ = _
    rw [Category.assoc, univLevel_fst_killed dE, ← Category.assoc]
  have kres₂ : (EllipticCurve.Point.restrict (X.curve.baseChange dE.f)
        (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (univQ dE)).1 ≫
        (X.curve.baseChange dE.f).mulByHom N =
      (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ 𝟙 dE.Z) ≫
        (X.curve.baseChange dE.f).zero := by
    show (dE.σZ.hom (Subgroup.topEquiv.symm γ) ≫ (univQ dE).1) ≫ _ = _
    rw [Category.assoc, univLevel_snd_killed dE, ← Category.assoc]
  -- raw identification: restricting = pushing the transported point forward
  have hlift₁ : (EllHom.pullSection (CommRingCat.of ℚ)
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
        (univP dE)).1 ≫
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).top =
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).baseHom ≫
        (univP dE).1 :=
    (X.pullbackAlongMap dE.f
      (dE.σZ.hom (Subgroup.topEquiv.symm γ))).isPullback.lift_fst _ _ _
  have hlift₂ : (EllHom.pullSection (CommRingCat.of ℚ)
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
        (univQ dE)).1 ≫
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).top =
      (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ))).baseHom ≫
        (univQ dE).1 :=
    (X.pullbackAlongMap dE.f
      (dE.σZ.hom (Subgroup.topEquiv.symm γ))).isPullback.lift_fst _ _ _
  have hraw₁ : (EllipticCurve.Point.restrict (X.curve.baseChange dE.f)
        (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (univP dE)).1 =
      (EllHom.mapPoint
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
        (𝟙 dE.Z) (univPzx dE γ)).1 :=
    hlift₁.symm.trans (EllHom.mapPoint_coe _ _ _).symm
  have hraw₂ : (EllipticCurve.Point.restrict (X.curve.baseChange dE.f)
        (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (univQ dE)).1 =
      (EllHom.mapPoint
        (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
        (𝟙 dE.Z) (univQzx dE γ)).1 :=
    hlift₂.symm.trans (EllHom.mapPoint_coe _ _ _).symm
  exact ((X.curve.baseChange dE.f).weilPairingEval_restrict
      (dE.σZ.hom (Subgroup.topEquiv.symm γ)) (univP dE) (univQ dE)
      (univLevel_fst_killed dE) (univLevel_snd_killed dE)
      kres₁ kres₂).symm.trans
    ((weilPairingEval_congr_raw
        ((Category.comp_id _).trans (Category.id_comp _).symm) hraw₁ hraw₂
        kres₁ kres₂
        (EllHom.mapPoint_torsion
          (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
          (univPzx dE γ) (univPzx_killed dE γ))
        (EllHom.mapPoint_torsion
          (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
          (univQzx dE γ) (univQzx_killed dE γ))).trans
      ((weilPairingEval_mapPoint
          (X.pullbackAlongMap dE.f (dE.σZ.hom (Subgroup.topEquiv.symm γ)))
          (𝟙 dE.Z) (univPzx dE γ) (univQzx dE γ)
          (univPzx_killed dE γ) (univQzx_killed dE γ)).trans
        ((fullLevel_eval_eqToHom hover
            ((gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
              (X.pullbackAlongMap dE.f
                (dE.σZ.hom (Subgroup.topEquiv.symm γ))).op
              (univLevel dE))).symm.trans
          ((weilPairingEval_congr_raw rfl
              (congrArg (fun z => z.1.1.1) hVAL.symm)
              (congrArg (fun z => z.1.2.1) hVAL.symm) _ _ _ _).trans
            (univLevel_glSmul_eval dE γ)))))

open scoped FintypeCatDiscrete in
/-- [T-CV-3b-iii] `muNRootsRead` is congruent in the map and the base point
(proofs transport). -/
theorem muNRootsRead_congr (D : GaloisRepData N) [Fact (1 < N)] {W : Scheme.{0}}
    {b b' : W ⟶ Spec (CommRingCat.of ℚ)} (hb : b = b')
    {φ φ' : W ⟶ muNRootsScheme D} (hf : φ = φ')
    (hφ : φ ≫ muNRootsSchemeπ D = b) :
    muNRootsRead D b φ hφ = muNRootsRead D b' φ' ((hf ▸ hφ).trans hb) := by
  subst hb; subst hf; rfl

open scoped FintypeCatDiscrete in
/-- **[T-CV-3b]** The pairing-side comparison twists by the same power endo under the
diagonal action: the `Γ`-read of `zx γ ≫ eZMap` is the `σZ γ`-restriction of the
universal pairing value ([H3] `univLevel_eval_restrict`), which is its
`det γ`-power — the read of `eZMap ≫ pow`. -/
theorem eZMap_zxAction (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxAction D dE γ ≫ eZMap D dE =
      eZMap D dE ≫ muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  have hπφ : (zxAction D dE γ ≫ eZMap D dE) ≫ muNRootsSchemeπ D =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.f ≫ X.structMap := by
    rw [Category.assoc, eZMap_π, reassoc_of% (zxAction_fst D dE γ),
      reassoc_of% (dE.over_base (Subgroup.topEquiv.symm γ))]
  have hπψ : (eZMap D dE ≫ muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val) ≫
        muNRootsSchemeπ D =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.f ≫ X.structMap := by
    rw [Category.assoc, muNRootsPowScheme_π, eZMap_π]
  have hbL : pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
      dE.f ≫ X.structMap =
    (zxAction D dE γ ≫
        pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
      (dE.f ≫ X.structMap) := by
    rw [zxAction_fst, Category.assoc,
      reassoc_of% (dE.over_base (Subgroup.topEquiv.symm γ))]
  refine muNRoots_hom_ext D hπφ hπψ ?_
  refine Eq.trans (muNRootsRead_congr D hbL rfl hπφ) ?_
  refine Eq.trans (eZMap_read D dE (zxAction D dE γ)) ?_
  refine Eq.trans (congrArg
    (fun m : pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶ dE.Z =>
      (Scheme.Γ.map m.op).hom
        ((X.curve.baseChange dE.f).weilPairingEval (univP dE) (univQ dE)
          (univLevel_fst_killed dE) (univLevel_snd_killed dE)).1)
    (zxAction_fst D dE γ)) ?_
  rw [op_comp, CategoryTheory.Functor.map_comp, CommRingCat.hom_comp,
    RingHom.comp_apply, univLevel_eval_restrict dE γ]
  refine Eq.trans (map_pow _ _ _) ?_
  refine Eq.symm ?_
  refine Eq.trans (muNRootsRead_pow D _ (eZMap D dE) (eZMap_π D dE) _) ?_
  refine congrArg
    (· ^ (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val) ?_
  refine Eq.trans (muNRootsRead_congr D
    (show pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        dE.f ≫ X.structMap =
      (𝟙 (pullback dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        (dE.f ≫ X.structMap) from by rw [Category.id_comp])
    ((Category.id_comp (eZMap D dE)).symm) (eZMap_π D dE)) ?_
  refine Eq.trans (eZMap_read D dE (𝟙 _)) ?_
  exact congrArg
    (fun m : pullback dE.f (pullback.fst X.structMap (wFramesπ D)) ⟶ dE.Z =>
      (Scheme.Γ.map m.op).hom
        ((X.curve.baseChange dE.f).weilPairingEval (univP dE) (univQ dE)
          (univLevel_fst_killed dE) (univLevel_snd_killed dE)).1)
    (Category.id_comp _)

/-- **[T-CV-3b-iv]** The locus inclusion equalises the two comparisons (the factoring
criterion at the identity witness). -/
theorem sympLocusι_agree (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    sympLocusι D dE ≫ eZMap D dE = sympLocusι D dE ≫ dZMap D dE :=
  (sympLocus_factor_iff D dE (sympLocusι D dE)).mp ⟨𝟙 _, Category.id_comp _⟩

/-- **[T-CV-3b-iv]** The diagonal action preserves the agreement locus: both
comparisons twist by the *same* power endo (`eZMap_zxAction` + `dZMap_zxAction`), so
the translated inclusion still equalises them. -/
theorem sympLocus_zxAction_stable (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    ∃ w : sympLocus D dE ⟶ sympLocus D dE,
      w ≫ sympLocusι D dE = sympLocusι D dE ≫ zxAction D dE γ :=
  (sympLocus_factor_iff D dE (sympLocusι D dE ≫ zxAction D dE γ)).mpr (by
    simp only [Category.assoc]
    rw [eZMap_zxAction D dE γ, dZMap_zxAction D dE γ,
      reassoc_of% (sympLocusι_agree D dE)])

/-- **[T-CV-3b-iv]** The restricted diagonal action on the symplectic locus. -/
noncomputable def zxSympAction (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    sympLocus D dE ⟶ sympLocus D dE :=
  (sympLocus_zxAction_stable D dE γ).choose

/-- **[T-CV-3b-iv]** The restricted action lies over the ambient action. -/
theorem zxSympAction_ι (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxSympAction D dE γ ≫ sympLocusι D dE =
      sympLocusι D dE ≫ zxAction D dE γ :=
  (sympLocus_zxAction_stable D dE γ).choose_spec

/-- **[T-CV-3b-iv]** The restricted action at the identity. -/
theorem zxSympAction_one (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    zxSympAction D dE 1 = 𝟙 (sympLocus D dE) := by
  haveI := sympLocusι_isOpenImmersion D dE
  rw [← cancel_mono (sympLocusι D dE), zxSympAction_ι, zxAction_one,
    Category.comp_id, Category.id_comp]

/-- **[T-CV-3b-iv]** The restricted action is multiplicative. -/
theorem zxSympAction_mul (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    (γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    zxSympAction D dE (γ₁ * γ₂) =
      zxSympAction D dE γ₁ ≫ zxSympAction D dE γ₂ := by
  haveI := sympLocusι_isOpenImmersion D dE
  rw [← cancel_mono (sympLocusι D dE), zxSympAction_ι, zxAction_mul,
    Category.assoc, zxSympAction_ι, reassoc_of% (zxSympAction_ι D dE γ₁)]

/-- **[T-CV-3c-1]** The value-level pairing-side comparison at an arbitrary framed
value: evaluate the Weil pairing on the pair and read the value in the roots scheme
(the `eZMap`-tail with the universal pair replaced by `(P, Q)`). This is the
MAP-LEVEL symplectic datum — contentful over every base, no pointwise vacuity. -/
noncomputable def pairEZMap (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T) (P Q : E.Section)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) : T ⟶ muNRootsScheme D :=
  pullback.lift
      (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
      (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
      ((E.pointToTorsion_torsionπ _ _).trans
        (E.pointToTorsion_torsionπ _ _).symm) ≫
    E.weilPairing N ≫ muNMapAlong sT N ≫ (muNSpecQIso D).hom

/-- **[T-CV-3c-1]** The value-level pairing comparison lies over the base. -/
theorem pairEZMap_π (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T) (P Q : E.Section)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    pairEZMap D sT E P Q hP hQ ≫ muNRootsSchemeπ D = sT := by
  rw [pairEZMap]
  simp only [Category.assoc]
  rw [muNSpecQIso_π, muNMapAlong_π, reassoc_of% (E.weilPairing_over N),
    pullback.lift_fst_assoc, ← Category.assoc, E.pointToTorsion_torsionπ,
    Category.id_comp]

/-- **[T-CV-3c-1]** The value-level determinant-side comparison at an arbitrary
frame. -/
noncomputable def frameDetMap (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (h : T ⟶ wFrames D) : T ⟶ muNRootsScheme D :=
  h ≫ detFrameScheme D ≫ detCompScheme D

/-- **[T-CV-3c-1]** The value-level determinant comparison lies over the base. -/
theorem frameDetMap_π (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    {sT : T ⟶ Spec (CommRingCat.of ℚ)} {h : T ⟶ wFrames D}
    (hover : h ≫ wFramesπ D = sT) :
    frameDetMap D h ≫ muNRootsSchemeπ D = sT := by
  rw [frameDetMap]
  simp only [Category.assoc]
  rw [detCompScheme_π, detFrameScheme_π, hover]

/-- **[T-CV-3c-1]** The universal pairing comparison factors through the value-level
one at the universal pair. -/
theorem eZMap_eq_pairEZMap (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    eZMap D dE =
      pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        pairEZMap D (dE.f ≫ X.structMap) (X.curve.baseChange dE.f)
          (univP dE) (univQ dE) (univLevel dE).2.1.1 (univLevel dE).2.1.2 := rfl

/-- **[T-CV-3c-1]** The universal determinant comparison factors through the
value-level one at the universal frame. -/
theorem dZMap_eq_frameDetMap (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X) :
    dZMap D dE =
      (pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
        pullback.snd X.structMap (wFramesπ D)) ≫
        frameDetMap D (𝟙 (wFrames D)) ≫ 𝟙 _ := by
  rw [dZMap, frameDetMap, Category.id_comp, Category.comp_id, Category.assoc]

/-- **[T-CV-3c-2]** The `Γ`-read of the value-level pairing comparison along a test
map is the restriction of the pairing evaluation (the generic form of `eZMap_read` —
no representing-scheme spelling in sight). -/
theorem pairEZMap_read (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T) (P Q : E.Section)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    {W : Scheme.{0}} (k : W ⟶ T) :
    muNRootsRead D (k ≫ sT) (k ≫ pairEZMap D sT E P Q hP hQ)
        (by rw [Category.assoc, pairEZMap_π]) =
      (Scheme.Γ.map k.op).hom
        (E.weilPairingEval P Q
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP)
          ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ)).1 := by
  have hw : E.pointToTorsion P
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP) ≫ E.torsionπ N =
      E.pointToTorsion Q
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ) ≫ E.torsionπ N := by
    simp
  have hover : pullback.lift
        (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
        (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
        hw ≫ E.weilPairing N ≫ muNπ T N = 𝟙 T := by
    rw [E.weilPairing_over N, ← Category.assoc, pullback.lift_fst,
      E.pointToTorsion_torsionπ]
  have hcancel : (k ≫ pairEZMap D sT E P Q hP hQ) ≫ (muNSpecQIso D).inv =
      k ≫ ((pullback.lift
          (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
          (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
          hw ≫ E.weilPairing N) ≫ muNMapAlong sT N) := by
    rw [pairEZMap]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id, Category.comp_id]
    try simp only [Category.assoc]
    try rfl
  have hsub1 : (⟨(k ≫ pairEZMap D sT E P Q hP hQ) ≫ (muNSpecQIso D).inv, by
      rw [Category.assoc, muNSpecQIso_π_inv, Category.assoc, pairEZMap_π]⟩ :
      { m : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = k ≫ sT }) =
    ⟨(k ≫ (pullback.lift
        (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
        (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
        hw ≫ E.weilPairing N)) ≫ muNMapAlong sT N, by
      try simp only [Category.assoc]
      rw [muNMapAlong_π]
      try simp only [Category.assoc]
      rw [reassoc_of% hover]⟩ :=
    Subtype.ext (hcancel.trans (Category.assoc _ _ _).symm)
  refine Eq.trans (congrArg
    (fun v : { m : W ⟶ muN (Spec (CommRingCat.of ℚ)) N //
        m ≫ muNπ (Spec (CommRingCat.of ℚ)) N = k ≫ sT } =>
      (muNPointsEquiv (Spec (CommRingCat.of ℚ)) N _ v : Γ(W, ⊤))) hsub1) ?_
  refine Eq.trans (muNPointsEquiv_mapAlong sT N k
    ⟨k ≫ (pullback.lift
        (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
        (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
        hw ≫ E.weilPairing N), by
      try simp only [Category.assoc]
      rw [hover]
      exact Category.comp_id k⟩) ?_
  have hnat := muNPointsEquiv_natural T N (𝟙 T) k
    ⟨pullback.lift
        (E.pointToTorsion P ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP))
        (E.pointToTorsion Q ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ))
        hw ≫ E.weilPairing N, hover⟩
  refine Eq.trans ?_ hnat
  refine congrArg
    (fun v : { m : W ⟶ muN T N // m ≫ muNπ T N = k ≫ 𝟙 T } =>
      (muNPointsEquiv T N _ v : Γ(W, ⊤))) ?_
  exact Subtype.ext rfl

/-- **[T-CV-3c-2]** The self-read of the value-level pairing comparison is the
pairing evaluation itself. -/
theorem pairEZMap_read_self (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T) (P Q : E.Section)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    muNRootsRead D sT (pairEZMap D sT E P Q hP hQ)
        (pairEZMap_π D sT E P Q hP hQ) =
      (E.weilPairingEval P Q
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N P).mp hP)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N Q).mp hQ)).1 := by
  refine Eq.trans (muNRootsRead_congr D (Category.id_comp sT).symm
    (Category.id_comp (pairEZMap D sT E P Q hP hQ)).symm
    (pairEZMap_π D sT E P Q hP hQ)) ?_
  refine Eq.trans (pairEZMap_read D sT E P Q hP hQ (𝟙 T)) ?_
  simp only [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **[T-CV-3c-3]** Naturality of the value-level pairing comparison: the comparison
of the pulled framed value is the base-restriction of the comparison (the map-level
symplectic condition is functorial — proven through the `Γ`-reads and the DS4
registers, the `H3`-chain at an arbitrary value). -/
theorem pairEZMap_pullSection (D : GaloisRepData N) [Fact (1 < N)]
    {A B : EllObj (CommRingCat.of ℚ)} (g : A ⟶ B)
    (P Q : B.curve.Section) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    pairEZMap D A.structMap A.curve
        (EllHom.pullSection (CommRingCat.of ℚ) g P)
        (EllHom.pullSection (CommRingCat.of ℚ) g Q)
        (pullSection_kill g hP) (pullSection_kill g hQ) =
      g.baseHom ≫ pairEZMap D B.structMap B.curve P Q hP hQ := by
  have hPraw : P.1 ≫ B.curve.mulByHom N = 𝟙 B.base ≫ B.curve.zero :=
    (B.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 B.base) N P).mp hP
  have hQraw : Q.1 ≫ B.curve.mulByHom N = 𝟙 B.base ≫ B.curve.zero :=
    (B.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 B.base) N Q).mp hQ
  have hψ : (g.baseHom ≫ pairEZMap D B.structMap B.curve P Q hP hQ) ≫
      muNRootsSchemeπ D = A.structMap := by
    rw [Category.assoc, pairEZMap_π, g.base_w]
  have kres₁ : (EllipticCurve.Point.restrict B.curve g.baseHom P).1 ≫
        B.curve.mulByHom N = (g.baseHom ≫ 𝟙 B.base) ≫ B.curve.zero := by
    show (g.baseHom ≫ P.1) ≫ _ = _
    rw [Category.assoc, hPraw, ← Category.assoc]
  have kres₂ : (EllipticCurve.Point.restrict B.curve g.baseHom Q).1 ≫
        B.curve.mulByHom N = (g.baseHom ≫ 𝟙 B.base) ≫ B.curve.zero := by
    show (g.baseHom ≫ Q.1) ≫ _ = _
    rw [Category.assoc, hQraw, ← Category.assoc]
  have hlift₁ : (EllHom.pullSection (CommRingCat.of ℚ) g P).1 ≫ g.top =
      g.baseHom ≫ P.1 := g.isPullback.lift_fst _ _ _
  have hlift₂ : (EllHom.pullSection (CommRingCat.of ℚ) g Q).1 ≫ g.top =
      g.baseHom ≫ Q.1 := g.isPullback.lift_fst _ _ _
  have hraw₁ : (EllipticCurve.Point.restrict B.curve g.baseHom P).1 =
      (EllHom.mapPoint g (𝟙 A.base)
        (EllHom.pullSection (CommRingCat.of ℚ) g P)).1 :=
    hlift₁.symm.trans (EllHom.mapPoint_coe _ _ _).symm
  have hraw₂ : (EllipticCurve.Point.restrict B.curve g.baseHom Q).1 =
      (EllHom.mapPoint g (𝟙 A.base)
        (EllHom.pullSection (CommRingCat.of ℚ) g Q)).1 :=
    hlift₂.symm.trans (EllHom.mapPoint_coe _ _ _).symm
  refine muNRoots_hom_ext D (pairEZMap_π D _ _ _ _ _ _) hψ ?_
  refine Eq.trans (pairEZMap_read_self D _ _ _ _ _ _) ?_
  refine Eq.symm ?_
  refine Eq.trans (muNRootsRead_congr D g.base_w.symm rfl hψ) ?_
  refine Eq.trans (pairEZMap_read D B.structMap B.curve P Q hP hQ g.baseHom) ?_
  refine Eq.trans
    ((B.curve.weilPairingEval_restrict g.baseHom P Q hPraw hQraw
      kres₁ kres₂).symm) ?_
  refine Eq.trans (weilPairingEval_congr_raw
    ((Category.comp_id g.baseHom).trans (Category.id_comp g.baseHom).symm)
    hraw₁ hraw₂ kres₁ kres₂
    (EllHom.mapPoint_torsion g (EllHom.pullSection (CommRingCat.of ℚ) g P)
      ((A.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 A.base) N _).mp
        (pullSection_kill g hP)))
    (EllHom.mapPoint_torsion g (EllHom.pullSection (CommRingCat.of ℚ) g Q)
      ((A.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 A.base) N _).mp
        (pullSection_kill g hQ)))) ?_
  exact weilPairingEval_mapPoint g (𝟙 A.base)
    (EllHom.pullSection (CommRingCat.of ℚ) g P)
    (EllHom.pullSection (CommRingCat.of ℚ) g Q)
    ((A.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 A.base) N _).mp
      (pullSection_kill g hP))
    ((A.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 A.base) N _).mp
      (pullSection_kill g hQ))

/-- **[T-CV-3c-3]** Naturality of the value-level determinant comparison. -/
theorem frameDetMap_baseHom (D : GaloisRepData N) [Fact (1 < N)]
    {T T' : Scheme.{0}} (k : T' ⟶ T) (h : T ⟶ wFrames D) :
    frameDetMap D (k ≫ h) = k ≫ frameDetMap D h := by
  rw [frameDetMap, frameDetMap, Category.assoc]

/-- **[T-CV-3c-4]** The Weil pairing of a `glSmul`-combined full-level pair is the
`det`-power of the pairing (the generic form of `univLevel_glSmul_eval` — the
registered symplectic formula at an arbitrary value). -/
theorem fullLevel_glSmul_eval {T : Scheme.{0}} (E : EllipticCurve T)
    (L : E.FullLevelPt N) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (E.weilPairingEval
        ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L.1.1 +
          (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L.1.2)
        ((((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1).val : ℤ) • L.1.1 +
          (((γ : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 1).val : ℤ) • L.1.2)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N
            _).mp (comb_kill L.2.1.1 L.2.1.2 _ _))
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N
            _).mp (comb_kill L.2.1.1 L.2.1.2 _ _))).1 =
      (E.weilPairingEval L.1.1 L.1.2
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1)
        ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2)).1 ^
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  set m : Matrix (Fin 2) (Fin 2) (ZMod N) := (γ : Matrix (Fin 2) (Fin 2) (ZMod N))
    with hm
  have hW := E.weilPairingEval_symplectic L.1.1 L.1.2
    (((m 0 0).val : ℤ)) (((m 1 0).val : ℤ)) (((m 0 1).val : ℤ))
    (((m 1 1).val : ℤ))
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.1).mp L.2.1.1)
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N L.1.2).mp L.2.1.2)
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N
        _).mp (comb_kill L.2.1.1 L.2.1.2 _ _))
    ((E.smul_eq_zero_iff_comp_mulByHom (𝟙 T) N
        _).mp (comb_kill L.2.1.1 L.2.1.2 _ _))
  refine hW.trans ?_
  congr 1
  have hcoedet : ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      ((((m 0 0).val : ℤ) * ((m 1 1).val : ℤ) -
        ((m 1 0).val : ℤ) * ((m 0 1).val : ℤ) : ℤ) : ZMod N) := by
    rw [show ((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) (ZMod N)).det from rfl, Matrix.det_fin_two]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [hcoedet]
  exact ((congrArg Int.toNat (ZMod.val_intCast _)).symm.trans
    (Int.toNat_natCast _))

/-- **[T-CV-3c-4]** The value-level pairing comparison twists by the power endo under
the diagonal `glSmul`-translation. -/
theorem pairEZMap_glSmul (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) (E : EllipticCurve T)
    (L : E.FullLevelPt N) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    pairEZMap D sT E (E.glSmul γ L).1.1 (E.glSmul γ L).1.2
        (E.glSmul γ L).2.1.1 (E.glSmul γ L).2.1.2 =
      pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 ≫
        muNRootsPowScheme D
          (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  have hπψ : (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2 ≫
      muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val) ≫
      muNRootsSchemeπ D = sT := by
    rw [Category.assoc, muNRootsPowScheme_π, pairEZMap_π]
  refine muNRoots_hom_ext D (pairEZMap_π D _ _ _ _ _ _) hπψ ?_
  refine Eq.trans (pairEZMap_read_self D _ _ _ _ _ _) ?_
  refine Eq.trans (fullLevel_glSmul_eval E L γ) ?_
  refine Eq.symm ?_
  refine Eq.trans (muNRootsRead_pow D _
    (pairEZMap D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2)
    (pairEZMap_π D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2) _) ?_
  exact congrArg
    (· ^ (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val)
    (pairEZMap_read_self D sT E L.1.1 L.1.2 L.2.1.1 L.2.1.2)

/-- **[T-CV-3c-4]** The value-level determinant comparison twists by the same power
endo under the right frame translation. -/
theorem frameDetMap_rightMul (D : GaloisRepData N) [Fact (1 < N)] {T : Scheme.{0}}
    (h : T ⟶ wFrames D) (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    frameDetMap D (h ≫ wFramesRightMul D γ) =
      frameDetMap D h ≫ muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val := by
  rw [frameDetMap, frameDetMap]
  simp only [Category.assoc]
  rw [reassoc_of% (detFrameScheme_rightMul D γ),
    detCompScheme_mul D (Matrix.GeneralLinearGroup.det γ)]

/-- **[T-CV-3c-5]** The MAP-LEVEL symplectically framed problem: bare framed values
whose value-level pairing comparison equals the value-level determinant comparison
(an equality of morphisms into the roots scheme — contentful over every base; the
`ℚ̄`-pointwise `FramedSymp` follows by composing with points, and agrees on reduced
finite-type bases). Functorial by `pairEZMap_pullSection`/`frameDetMap_baseHom`. -/
noncomputable def sympFramedProblem (D : GaloisRepData N) [Fact (1 < N)] :
    ModularCurves.ModuliProblem (CommRingCat.of ℚ) where
  obj X := { Lh : (bareFramedProblem D).obj X //
    pairEZMap D X.unop.structMap X.unop.curve Lh.1.1.1 Lh.1.1.2
        Lh.1.2.1.1 Lh.1.2.1.2 = frameDetMap D Lh.2.1 }
  map f := ↾fun Lh => ⟨(bareFramedProblem D).map f Lh.val, by
    exact (pairEZMap_pullSection D f.unop Lh.val.1.1.1 Lh.val.1.1.2
        Lh.val.1.2.1.1 Lh.val.1.2.1.2).trans
      ((congrArg (f.unop.baseHom ≫ ·) Lh.property).trans
        (frameDetMap_baseHom D f.unop.baseHom Lh.val.2.val).symm)⟩
  map_id X := by
    ext Lh : 3
    exact Subtype.ext
      (FunctorToTypes.map_id_apply (bareFramedProblem D) Lh.val)
  map_comp f g := by
    ext Lh : 3
    exact Subtype.ext
      (FunctorToTypes.map_comp_apply (bareFramedProblem D) f g Lh.val)

/-- **[T-CV-3c-5]** The diagonal translation of the symplectically framed problem
(the condition twists by the same power endo on both sides). -/
noncomputable def sympFramedSmulNat (D : GaloisRepData N) [Fact (1 < N)]
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    sympFramedProblem D ⟶ sympFramedProblem D where
  app X := ↾fun Lh => ⟨⟨X.unop.curve.glSmul γ Lh.val.1,
    ⟨Lh.val.2.val ≫ wFramesRightMul D γ, by
      rw [Category.assoc, wFramesRightMul_π, Lh.val.2.property]⟩⟩, by
    refine Eq.trans (pairEZMap_glSmul D X.unop.structMap X.unop.curve
      Lh.val.1 γ) ?_
    refine Eq.trans (congrArg
      (· ≫ muNRootsPowScheme D
        (((Matrix.GeneralLinearGroup.det γ : (ZMod N)ˣ) : ZMod N)).val)
      Lh.property) ?_
    exact (frameDetMap_rightMul D Lh.val.2.val γ).symm⟩
  naturality X Y f := by
    ext Lh
    exact Subtype.ext (Prod.ext
      (EllHom.pullSection_glSmul (CommRingCat.of ℚ) f.unop γ Lh.val.1)
      (Subtype.ext (Category.assoc _ _ _)))

/-- **[T-CV-3c-5]** The `GL₂(ℤ/N)`-action on the symplectically framed problem
(the `γ⁻¹`-hom convention, mirroring `bareFramedAut`). -/
noncomputable def sympFramedAut (D : GaloisRepData N) [Fact (1 < N)] :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod N) →* Aut (sympFramedProblem D) where
  toFun γ :=
    { hom := sympFramedSmulNat D γ⁻¹
      inv := sympFramedSmulNat D γ
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

/-- **[T-CV-3c-5]** The diagonal action on the symplectically framed problem is free
over nonempty bases (the full-level component already is). -/
theorem sympFramedAut_freeAction (D : GaloisRepData N) [Fact (1 < N)] :
    ModuliProblem.FreeAction (sympFramedAut D) := by
  intro X hne γ hγ a hfix
  apply hγ
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hL : X.curve.glSmul γ⁻¹ a.val.1 = a.val.1 :=
    congrArg (fun z => z.val.1) hfix
  have hg1 : (γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) = 1 :=
    glSmul_eq_one_of_eq_self N hinvQ X hne γ⁻¹ a.val.1 hL
  rwa [inv_eq_one] at hg1

/-- **[T-CV-3c-6]** The value-level pairing comparison of the classified full-level
structure at a test map `h` into the framed space is `h ≫ eZMap` (the [B1]-bridge:
the classified value's components are the `h`-pull of the universal pair, and the
value-level comparison is natural; the classifying-map equality is `subst`-ed away
so no `eqToHom` appears). -/
theorem pairEZMap_classified (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} {g : T ⟶ X.base}
    (h : T ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D)))
    (p : (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
      dE.f = g) :
    pairEZMap D (X.pullbackAlong g).structMap (X.pullbackAlong g).curve
        (dE.eqv g ⟨h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)),
          p⟩).1.1
        (dE.eqv g ⟨h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)),
          p⟩).1.2
        (dE.eqv g ⟨h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)),
          p⟩).2.1.1
        (dE.eqv g ⟨h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)),
          p⟩).2.1.2 =
      h ≫ eZMap D dE := by
  subst p
  have h1 := dE.nat dE.f
    (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)))
    ⟨𝟙 dE.Z, Category.id_comp dE.f⟩
  have h3 := relRep_eqv_congr dE.toRelRepData
    ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫ dE.f)
    (Category.comp_id
      (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))))
    (by rw [Category.comp_id])
  have hVAL : dE.eqv
      ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫ dE.f)
      ⟨h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)), rfl⟩ =
      (gammaFullNaiveProblem (CommRingCat.of ℚ) N).map
        (X.pullbackAlongMap dE.f
          (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)))).op
        (univLevel dE) :=
    h3.symm.trans h1
  refine Eq.trans (congrArg
    (fun w : (gammaFullNaiveProblem (CommRingCat.of ℚ) N).obj
        (Opposite.op (X.pullbackAlong
          ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            dE.f))) =>
      pairEZMap D
        (X.pullbackAlong
          ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            dE.f)).structMap
        (X.pullbackAlong
          ((h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
            dE.f)).curve
        w.1.1 w.1.2 w.2.1.1 w.2.1.2) hVAL) ?_
  refine Eq.trans (pairEZMap_pullSection D
    (X.pullbackAlongMap dE.f
      (h ≫ pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D))))
    (univP dE) (univQ dE) (univLevel dE).2.1.1 (univLevel dE).2.1.2) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (h ≫ ·) (eZMap_eq_pairEZMap D dE).symm

/-- **[T-CV-3c-6]** The bare framed classifying bijection is `zxAction`-equivariant
(the standalone form of the `bareFramed_equivariantRelRepData` equivariance field,
reused by the carved datum through the `zxSympAction`-conjugation). -/
theorem bareFramed_zxAction_eqv (D : GaloisRepData N)
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} (g : T ⟶ X.base)
    (u : { h : T ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D)) //
      h ≫ (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f) =
        g })
    (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) :
    (bareFramedRelRepData D dE.toRelRepData).eqv g
        ⟨u.1 ≫ zxAction D dE γ, by
          show (u.1 ≫ zxAction D dE γ) ≫
            (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
              dE.f) = g
          rw [Category.assoc]
          rw [show zxAction D dE γ ≫
              (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
                dE.f) =
              pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
                dE.f from by
            rw [← Category.assoc, zxAction_fst, Category.assoc, dE.over_base]]
          exact u.2⟩ =
      ((bareFramedAut D) γ⁻¹).hom.app (Opposite.op (X.pullbackAlong g))
        ((bareFramedRelRepData D dE.toRelRepData).eqv g u) := by
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

/-- **[T-CV-3c-6]** A classified bare framed value is map-level symplectic iff its
classifying map equalises the two comparisons (the [B1]-bridge packaged as an iff:
`pairEZMap_classified` on the pairing side, associativity on the determinant
side). -/
theorem sympLocus_agree_iff_symp (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} (g : T ⟶ X.base)
    (h₀ : T ⟶ pullback dE.f (pullback.fst X.structMap (wFramesπ D)))
    (p₀ : h₀ ≫ (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
      dE.f) = g) :
    (h₀ ≫ eZMap D dE = h₀ ≫ dZMap D dE) ↔
      pairEZMap D (X.pullbackAlong g).structMap (X.pullbackAlong g).curve
          ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.1.1
          ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.1.2
          ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.2.1.1
          ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.2.1.2 =
        frameDetMap D
          ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).2.1 := by
  have he : pairEZMap D (X.pullbackAlong g).structMap (X.pullbackAlong g).curve
      ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.1.1
      ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.1.2
      ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.2.1.1
      ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).1.2.1.2 =
      h₀ ≫ eZMap D dE :=
    pairEZMap_classified D dE h₀ (by simp only [Category.assoc]; exact p₀)
  have hd : h₀ ≫ dZMap D dE = frameDetMap D
      ((bareFramedRelRepData D dE.toRelRepData).eqv g ⟨h₀, p₀⟩).2.1 := by
    show h₀ ≫ dZMap D dE = frameDetMap D
      ((h₀ ≫ pullback.snd dE.f (pullback.fst X.structMap (wFramesπ D))) ≫
        pullback.snd X.structMap (wFramesπ D))
    rw [dZMap, frameDetMap]
    simp only [Category.assoc]
  exact ⟨fun hag => he.trans (hag.trans hd),
    fun hs => he.symm.trans (hs.trans hd.symm)⟩

/-- **[T-CV-3c-6]** A map-level symplectic value's classifying map factors through
the symplectic locus. -/
theorem sympLocusSection_exists (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} {g : T ⟶ X.base}
    (v : (sympFramedProblem D).obj (Opposite.op (X.pullbackAlong g))) :
    ∃ w : T ⟶ sympLocus D dE, w ≫ sympLocusι D dE =
      (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).1 :=
  (sympLocus_factor_iff D dE
    (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).1).mpr
    ((sympLocus_agree_iff_symp D dE g
        (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).1
        (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).2).mpr
      ((congrArg (fun w : (bareFramedProblem D).obj
          (Opposite.op (X.pullbackAlong g)) =>
        pairEZMap D (X.pullbackAlong g).structMap (X.pullbackAlong g).curve
          w.1.1.1 w.1.1.2 w.1.2.1.1 w.1.2.1.2)
        (Equiv.apply_symm_apply
          ((bareFramedRelRepData D dE.toRelRepData).eqv g) v.val)).trans
        (v.property.trans (congrArg (fun w : (bareFramedProblem D).obj
            (Opposite.op (X.pullbackAlong g)) => frameDetMap D w.2.1)
          (Equiv.apply_symm_apply
            ((bareFramedRelRepData D dE.toRelRepData).eqv g) v.val).symm))))

/-- **[T-CV-3c-6]** The locus-section classifying a map-level symplectic value. -/
noncomputable def sympLocusSection (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} {g : T ⟶ X.base}
    (v : (sympFramedProblem D).obj (Opposite.op (X.pullbackAlong g))) :
    T ⟶ sympLocus D dE :=
  (sympLocusSection_exists D dE v).choose

/-- **[T-CV-3c-6]** Its defining property. -/
theorem sympLocusSection_ι (D : GaloisRepData N) [Fact (1 < N)]
    {X : EllObj (CommRingCat.of ℚ)}
    (dE : ModuliProblem.EquivariantRelRepData
      (gammaHAut (CommRingCat.of ℚ) N ⊤) X)
    {T : Scheme.{0}} {g : T ⟶ X.base}
    (v : (sympFramedProblem D).obj (Opposite.op (X.pullbackAlong g))) :
    sympLocusSection D dE v ≫ sympLocusι D dE =
      (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).1 :=
  (sympLocusSection_exists D dE v).choose_spec

/-- **[T-CV-3c-6]** The symplectically framed problem has equivariant relative data
at every `X`: the symplectic locus of the framed test space carrying the restricted
diagonal action; the classifying bijection is the bare one conjugated by the clopen
locus inclusion, with the symplectic condition matched by the [B1]-bridge and the
factoring criterion. -/
theorem sympFramed_equivariantRelRepData (D : GaloisRepData N) [Fact (1 < N)]
    (X : EllObj (CommRingCat.of ℚ)) :
    Nonempty (ModuliProblem.EquivariantRelRepData (sympFramedAut D) X) := by
  have hinvQ : IsUnit ((N : ℕ) : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  obtain ⟨dE⟩ := gammaFullNaive_equivariantRelRepData (CommRingCat.of ℚ) N ⊤ hinvQ X
  haveI hOI : IsOpenImmersion (sympLocusι D dE) := sympLocusι_isOpenImmersion D dE
  haveI hCI : IsClosedImmersion (sympLocusι D dE) :=
    sympLocusι_isClosedImmersion D dE
  refine ⟨{
    Z := sympLocus D dE
    f := sympLocusι D dE ≫
      (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f)
    eqv := fun {T} g =>
      { toFun := fun u => ⟨(bareFramedRelRepData D dE.toRelRepData).eqv g
            ⟨u.1 ≫ sympLocusι D dE, by
              show (u.1 ≫ sympLocusι D dE) ≫
                (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
                  dE.f) = g
              simpa only [Category.assoc] using u.2⟩,
          (sympLocus_agree_iff_symp D dE g (u.1 ≫ sympLocusι D dE) _).mp
            ((sympLocus_factor_iff D dE (u.1 ≫ sympLocusι D dE)).mp
              ⟨u.1, rfl⟩)⟩
        invFun := fun v => ⟨sympLocusSection D dE v, by
          show sympLocusSection D dE v ≫ (sympLocusι D dE ≫
            (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
              dE.f)) = g
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (congrArg (· ≫ (pullback.fst dE.f
            (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f))
            (sympLocusSection_ι D dE v)).trans ?_
          exact (((bareFramedRelRepData D dE.toRelRepData).eqv g).symm v.val).2⟩
        left_inv := fun u => Subtype.ext (by
          rw [← cancel_mono (sympLocusι D dE)]
          refine (sympLocusSection_ι D dE _).trans ?_
          exact congrArg Subtype.val (Equiv.symm_apply_apply
            ((bareFramedRelRepData D dE.toRelRepData).eqv g)
            ⟨u.1 ≫ sympLocusι D dE, by
              show (u.1 ≫ sympLocusι D dE) ≫
                (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
                  dE.f) = g
              simpa only [Category.assoc] using u.2⟩))
        right_inv := fun v => Subtype.ext ((congrArg
            ((bareFramedRelRepData D dE.toRelRepData).eqv g)
            (Subtype.ext (sympLocusSection_ι D dE v))).trans
          (Equiv.apply_symm_apply
            ((bareFramedRelRepData D dE.toRelRepData).eqv g) v.val)) }
    nat := ?_
    σZ := ⟨fun γ => zxSympAction D dE γ, zxSympAction_one D dE,
      zxSympAction_mul D dE⟩
    over_base := ?_
    equivariant := ?_
    finite := ?_
    etale := ?_ }⟩
  · intro T T' g k u
    refine Subtype.ext (Eq.trans
      (relRep_eqv_congr (bareFramedRelRepData D dE.toRelRepData) (k ≫ g)
        (Category.assoc k u.1 (sympLocusι D dE)) (by
          show ((k ≫ u.1) ≫ sympLocusι D dE) ≫
            (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
              dE.f) = k ≫ g
          simp only [Category.assoc]
          exact congrArg (k ≫ ·) (by
            simpa only [Category.assoc] using u.2))) ?_)
    exact (bareFramedRelRepData D dE.toRelRepData).nat g k
      ⟨u.1 ≫ sympLocusι D dE, by
        show (u.1 ≫ sympLocusι D dE) ≫
          (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
            dE.f) = g
        simpa only [Category.assoc] using u.2⟩
  · intro γ
    show zxSympAction D dE γ ≫ (sympLocusι D dE ≫
      (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f)) =
      sympLocusι D dE ≫
        (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f)
    rw [← Category.assoc, zxSympAction_ι, Category.assoc,
      reassoc_of% (zxAction_fst D dE γ), dE.over_base]
  · intro T g u γ
    refine Subtype.ext (Eq.trans
      (relRep_eqv_congr (bareFramedRelRepData D dE.toRelRepData) g
        (show (u.1 ≫ zxSympAction D dE γ) ≫ sympLocusι D dE =
            (u.1 ≫ sympLocusι D dE) ≫ zxAction D dE γ from by
          rw [Category.assoc, zxSympAction_ι, ← Category.assoc]) (by
          show ((u.1 ≫ zxSympAction D dE γ) ≫ sympLocusι D dE) ≫
            (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
              dE.f) = g
          simp only [Category.assoc]
          rw [reassoc_of% (zxSympAction_ι D dE γ),
            reassoc_of% (zxAction_fst D dE γ), dE.over_base]
          simpa only [Category.assoc] using u.2)) ?_)
    exact bareFramed_zxAction_eqv D dE g
      ⟨u.1 ≫ sympLocusι D dE, by
        show (u.1 ≫ sympLocusι D dE) ≫
          (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫
            dE.f) = g
        simpa only [Category.assoc] using u.2⟩ γ
  · haveI h1 : IsFinite (wFramesπ D) := (wFramesπ_finite_etale D).1
    haveI h2 : IsFinite (pullback.fst X.structMap (wFramesπ D)) :=
      MorphismProperty.pullback_fst _ _ h1
    haveI h3 : IsFinite (pullback.fst dE.f
        (pullback.fst X.structMap (wFramesπ D))) :=
      MorphismProperty.pullback_fst _ _ h2
    haveI h4 : IsFinite dE.f := dE.finite
    haveI h5 : IsFinite (sympLocusι D dE) := inferInstance
    show IsFinite (sympLocusι D dE ≫
      (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f))
    exact inferInstance
  · haveI h1 : Etale (wFramesπ D) := (wFramesπ_finite_etale D).2
    haveI h2 : Etale (pullback.fst X.structMap (wFramesπ D)) :=
      MorphismProperty.pullback_fst _ _ h1
    haveI h3 : Etale (pullback.fst dE.f
        (pullback.fst X.structMap (wFramesπ D))) :=
      MorphismProperty.pullback_fst _ _ h2
    haveI h4 : Etale dE.f := dE.etale
    haveI h5 : Etale (sympLocusι D dE) := inferInstance
    show Etale (sympLocusι D dE ≫
      (pullback.fst dE.f (pullback.fst X.structMap (wFramesπ D)) ≫ dE.f))
    exact inferInstance

/-- **[T-CV-4]** The free `GL₂`-quotient of the symplectically framed problem exists
as a quotient-problem package (the carved mirror of
`bareFramed_quotientProblemData`). -/
theorem sympFramed_quotientProblemData (D : GaloisRepData N) [Fact (1 < N)] :
    Nonempty (ModuliProblem.QuotientProblemData (sympFramedAut D)) :=
  ModuliProblem.exists_quotientProblemData (sympFramedAut D)
    (sympFramedAut_freeAction D) (sympFramed_equivariantRelRepData D)

/-- **[T-CV-4]** The carved quotient is affine over `Ell/ℚ`. -/
theorem sympFramed_quotient_affineOverEll (D : GaloisRepData N) [Fact (1 < N)]
    (pkg : ModuliProblem.QuotientProblemData (sympFramedAut D)) :
    pkg.prob.AffineOverEll :=
  pkg.affineOverEll

end FramedProblemFunctor


-- **(T-F6 = expert review Q9: the symplectic Isom-scheme route)** Relative
-- representability of the ρ-level problem is **proved** as
-- `rhoLevel_relativelyRepresentable` in `ModularCurve/RhoSections.lean`. It cannot be
-- stated here: the symplectic Isom-scheme construction imports this file.

/-- The `Ell/ℚ`-morphism induced by a pointed isomorphism of elliptic curves over the
same base `T` (identity on the base). -/
noncomputable def ellHomOfCurveIso {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ))
    {E E' : EllipticCurve T} (f : E ≅ E') :
    (⟨T, sT, E⟩ : EllObj (CommRingCat.of ℚ)) ⟶ ⟨T, sT, E'⟩ where
  baseHom := 𝟙 T
  base_w := Category.id_comp sT
  top := f.hom.hom
  isPullback := by
    haveI : IsIso f.hom.hom :=
      ⟨f.inv.hom, congrArg EllipticCurve.HomOver.hom f.hom_inv_id,
        congrArg EllipticCurve.HomOver.hom f.inv_hom_id⟩
    exact IsPullback.of_horiz_isIso ⟨by rw [f.hom.over_w, Category.comp_id]⟩
  zero_w := by
    show E.zero ≫ f.hom.hom = 𝟙 T ≫ E'.zero
    rw [f.hom.zero_w, Category.id_comp]

/-- The representing property for the twisted modular curve: `(Y, sY)` is a smooth
affine `ℚ`-curve whose `T`-points over `ℚ` are naturally the isomorphism classes of
pairs `(E, α)` — the quotient by pointed over-`T` isomorphisms **carrying the level
structure to the level structure** (DEF-4). Extracted as a predicate so that geometric
irreducibility (T-F5) can be asserted OF THE REPRESENTING CURVE, not of arbitrary
smooth curves (DEF-6).

**DEF-17 (2026-07-25, adversarial pass).** The relation was previously stated by
*equality of coordinates at `ℚ̄`-points*; that clause is **vacuous** over a base with
no `ℚ̄`-points (e.g. `Spec K` for `K/ℚ` of positive transcendence degree, or `Spec ℝ`),
where it degenerates into "the underlying curves are isomorphic" — the residual form of
the DEF-4 defect, and refutable (for trivial `ρ̄` the fibre over one curve class has
`|GL₂(ℤ/N)|/2 > 1` points). The relation is therefore stated scheme-theoretically:
`f` carries `b`'s structure to `a`'s, i.e. `a.2 = RhoLevelStructure.pull D _ b.2`.
The old coordinate identity is a **consequence**, by `coord_pull`. -/
def RepresentsYRho {N : ℕ} [NeZero N] (D : GaloisRepData N) (Y : Scheme.{0})
    (sY : Y ⟶ Spec (.of ℚ)) : Prop :=
  SmoothOfRelativeDimension 1 sY ∧ IsAffineHom sY ∧
    ∀ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℚ)),
      Nonempty ({ h : T ⟶ Y // h ≫ sY = sT } ≃
        Quot (fun (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E) =>
          ∃ f : a.1 ≅ b.1,
            a.2 = RhoLevelStructure.pull D (ellHomOfCurveIso sT f) b.2))

-- **(T-F4 = Buzzard p. 33, the main statement)** The twisted modular curve exists:
-- `yRho_representable`, **proved** in `ModularCurve/RhoPoints.lean` via the level-three
-- rigidifier. It cannot be stated here: that route imports this file through `RhoSmooth`.

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
