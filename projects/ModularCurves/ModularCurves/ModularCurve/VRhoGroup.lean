import ModularCurves.ModularCurve.YRho

/-!
# The group structure on `V_ρ` (T-F1c)

The `ρ`-twisted `(ℤ/N)²` is a *group* in continuous Galois sets — the addition is
Galois-equivariant because `ρ σ` acts linearly.  This file constructs the addition
morphism on the `ContAction` side (leaf F1c-1) and will transport it through the
Galois correspondence to a group-scheme structure on `V_ρ` (leaves F1c-2..5).
-/

universe u

open CategoryTheory Limits CommAlgCat

open scoped FintypeCatDiscrete

namespace ModularCurves

open ModularCurves.FiniteEtaleGalois

variable {N : ℕ} [NeZero N]

/-- The square of the `ρ`-twisted fiber: carrier `(ℤ/N)² × (ℤ/N)²` with the diagonal
Galois action. -/
noncomputable abbrev rhoSqAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun vw => (D.ρ (galSepMulEquivGalQ σ) • vw.1, D.ρ (galSepMulEquivGalQ σ) • vw.2))
      map_one' := FintypeCat.hom_ext _ _ fun vw => by
        show (D.ρ (galSepMulEquivGalQ 1) • vw.1, D.ρ (galSepMulEquivGalQ 1) • vw.2) = vw
        rw [map_one, map_one, one_smul, one_smul]
      map_mul' := fun σ τ => FintypeCat.hom_ext _ _ fun vw => by
        show (D.ρ (galSepMulEquivGalQ (σ * τ)) • vw.1,
          D.ρ (galSepMulEquivGalQ (σ * τ)) • vw.2) = _
        rw [map_mul, map_mul, mul_smul, mul_smul]
        rfl }

open scoped Pointwise in
/-- The diagonal action on the square is continuous: the kernel of `ρ` acts trivially. -/
lemma rhoSqAction_isContinuous (D : GaloisRepData N) :
    (rhoSqAction D).IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj (rhoSqAction D) :
          Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun w => ?_
  have hdecomp : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
        (CategoryTheory.forget₂ _ TopCat).obj (rhoSqAction D) => p.1 • p.2) ⁻¹'
        ({w} : Set _) =
      ⋃ v : (CategoryTheory.forget₂ _ TopCat).obj (rhoSqAction D),
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
  have hAct : (rhoSqAction D).ρ τ = 𝟙 _ := by
    refine FintypeCat.hom_ext _ _ fun x => ?_
    show (D.ρ (galSepMulEquivGalQ τ) • x.1, D.ρ (galSepMulEquivGalQ τ) • x.2) = x
    rw [hτ1, one_smul, one_smul]
  calc (σ₀ * τ) • v = σ₀ • τ • v := mul_smul σ₀ τ v
    _ = σ₀ • v := by
        congr 1
        show ((CategoryTheory.forget₂ _ TopCat).map ((rhoSqAction D).ρ τ)) v = v
        rw [hAct, CategoryTheory.Functor.map_id]
        rfl
    _ = w := hσ₀

/-- The square as a continuous Galois set. -/
noncomputable abbrev rhoSqContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoSqAction D, rhoSqAction_isContinuous D⟩

/-- Coordinatewise addition is Galois-equivariant (`ρ σ` is linear), giving the
addition morphism of continuous Galois sets. -/
noncomputable def rhoAddMor (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vw => vw.1 + vw.2)
      comm := fun σ => FintypeCat.hom_ext _ _ fun vw => by
        show D.ρ (galSepMulEquivGalQ σ) • vw.1 + D.ρ (galSepMulEquivGalQ σ) • vw.2 =
          D.ρ (galSepMulEquivGalQ σ) • (vw.1 + vw.2)
        rw [smul_add] }

/-- The one-point Galois set. -/
noncomputable abbrev pointAction :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of PUnit
  ρ := { toFun := fun _ => FintypeCat.homMk id
         map_one' := rfl
         map_mul' := fun _ _ => rfl }

lemma pointAction_isContinuous : pointAction.IsContinuous := by
  constructor
  haveI : DiscreteTopology
      ((CategoryTheory.forget₂ (Action FintypeCat.{0}
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) TopCat).obj pointAction :
          Type 0) := ⟨rfl⟩
  refine continuous_discrete_rng.mpr fun y => ?_
  have huniv : (fun p : (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ×
      (CategoryTheory.forget₂ _ TopCat).obj pointAction => p.1 • p.2) ⁻¹'
      ({y} : Set _) = Set.univ := by
    ext p
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  rw [huniv]
  exact isOpen_univ

/-- The zero section: the one-point continuous Galois set. -/
noncomputable abbrev rhoPointContAction :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨pointAction, pointAction_isContinuous⟩

/-- The zero morphism of continuous Galois sets. -/
noncomputable def rhoZeroMor (D : GaloisRepData N) :
    rhoPointContAction ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun _ => 0)
      comm := fun σ => FintypeCat.hom_ext _ _ fun _ => by
        show (0 : Fin 2 → ZMod N) = D.ρ (galSepMulEquivGalQ σ) • (0 : Fin 2 → ZMod N)
        rw [smul_zero] }

/-- Negation is Galois-equivariant, giving the inverse morphism. -/
noncomputable def rhoNegMor (D : GaloisRepData N) :
    rhoContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun v => -v)
      comm := fun σ => FintypeCat.hom_ext _ _ fun v => by
        show -(D.ρ (galSepMulEquivGalQ σ) • v) = D.ρ (galSepMulEquivGalQ σ) • (-v)
        rw [smul_neg] }

/-- First projection of the square. -/
noncomputable def rhoSqFst (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.fst
      comm := fun σ => FintypeCat.hom_ext _ _ fun vw => rfl }

/-- Second projection of the square. -/
noncomputable def rhoSqSnd (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun σ => FintypeCat.hom_ext _ _ fun vw => rfl }

/-- The square with its projections is the categorical binary product in the category
of continuous Galois sets (leaf F1c-2). -/
noncomputable def rhoSqIsProduct (D : GaloisRepData N) :
    IsLimit (BinaryFan.mk (rhoSqFst D) (rhoSqSnd D)) := by
  refine BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun x => (s.fst.hom.hom x, s.snd.hom.hom x))
        comm := fun σ => FintypeCat.hom_ext _ _ fun x => ?_ })
    (fun s => rfl) (fun s => rfl) (fun s m h₁ h₂ => ?_)
  · have h1 := congrArg (fun q => q x) (s.fst.hom.comm σ)
    have h2 := congrArg (fun q => q x) (s.snd.hom.comm σ)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
    exact Prod.ext h1 h2
  · ext x
    · exact congrFun
        (congrArg (fun q : s.pt ⟶ rhoContAction D => q.hom.hom x) h₁) _
    · exact congrFun
        (congrArg (fun q : s.pt ⟶ rhoContAction D => q.hom.hom x) h₂) _

/-- Transport of the square through the Galois correspondence: the algebra of the
`ρ`-square is the tensor square of `vRhoAlgebra` (leaf F1c-3). -/
noncomputable def vRhoSqAlgebraIso (D : GaloisRepData N) :
    (finiteEtaleEquivContAction ℚ).inverse.obj (rhoSqContAction D) ≅
      Opposite.op (FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D)) := by
  have h1 : IsLimit ((finiteEtaleEquivContAction ℚ).inverse.mapCone
      (BinaryFan.mk (rhoSqFst D) (rhoSqSnd D))) :=
    isLimitOfPreserves _ (rhoSqIsProduct D)
  have h1' := (IsLimit.postcomposeHomEquiv
    (Limits.pairComp (rhoContAction D) (rhoContAction D)
      (finiteEtaleEquivContAction ℚ).inverse) _).symm h1
  exact h1'.conePointUniqueUpToIso
    (FiniteEtaleGalois.tensorBinaryFanOpIsLimit (vRhoAlgebra D) (vRhoAlgebra D))

end ModularCurves
