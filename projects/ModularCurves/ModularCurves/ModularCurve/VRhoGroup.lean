/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

/-- The diagonal action on the square is continuous: the kernel of `ρ` acts trivially.
(`isContinuous_of_isOpen_of_trivial` at `K = ker ρ`, as for `rhoAction`.) -/
lemma rhoSqAction_isContinuous (D : GaloisRepData N) :
    (rhoSqAction D).IsContinuous :=
  isContinuous_of_isOpen_of_trivial _ _ (rhoAction_ker_open D)
    (by simp only [Set.mem_setOf_eq, map_one]) fun τ hτ =>
      FintypeCat.hom_ext _ _ fun x => by
        show (D.ρ (galSepMulEquivGalQ τ) • x.1, D.ρ (galSepMulEquivGalQ τ) • x.2) = x
        rw [show D.ρ (galSepMulEquivGalQ τ) = 1 from hτ, one_smul, one_smul]

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

/-- The one-point Galois set is continuous: *everything* acts trivially on it
(`isContinuous_of_isOpen_of_trivial` at `K = univ`). -/
lemma pointAction_isContinuous : pointAction.IsContinuous :=
  isContinuous_of_isOpen_of_trivial _ Set.univ isOpen_univ (Set.mem_univ _) fun _ _ =>
    FintypeCat.hom_ext _ _ fun _ => rfl

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
      comm := fun _ => FintypeCat.hom_ext _ _ fun _ => rfl }

/-- Second projection of the square. -/
noncomputable def rhoSqSnd (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun _ => FintypeCat.hom_ext _ _ fun _ => rfl }

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

/-- The comultiplication: the finite étale algebra map corresponding to the addition
of the `ρ`-twisted Galois module (leaf F1c-4). -/
noncomputable def vRhoComulHom (D : GaloisRepData N) :
    vRhoAlgebra D ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D) :=
  ((vRhoSqAlgebraIso D).inv ≫
    (finiteEtaleEquivContAction ℚ).inverse.map (rhoAddMor D)).unop

/-- **(T-F1c)** The addition morphism of `V_ρ`: `V_ρ ×_ℚ V_ρ ⟶ V_ρ`, `Spec` of the
comultiplication through the tensor identification of the fibre product. -/
noncomputable def vRhoAdd (D : GaloisRepData N) :
    pullback (vRhoπ D) (vRhoπ D) ⟶ vRho D :=
  (AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
    (vRhoAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (vRhoComulHom D).hom.hom.toRingHom)

end ModularCurves
