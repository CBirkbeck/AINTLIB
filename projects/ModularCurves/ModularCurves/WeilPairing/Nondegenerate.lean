/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.SelfUniversalVanishing

/-!
# Leaf B — fibrewise nondegeneracy of the Weil pairing (KM 2.8)

Over an algebraically closed field `k` in which `N` is invertible, an `N`-torsion point
pairing trivially with every `N`-torsion point is zero. The argument crosses to the
`HasseWeil` field-level pairing and uses its nondegeneracy:

* `weilPairingEval_nondegenerate_model` — at the projective Weierstrass model: the
  scheme value is the field pairing (`weilPairingEval_eq_weilPairing_model`, the
  [VALUE-CROSSING]), the point dictionary is surjective onto the torsion subgroup, and
  `HasseWeil.WeilPairing.weilPairing_nondegenerate` (second slot, reached through
  `weilPairing_antisymm`) closes it;
* `weilPairingEval_nondegenerate_of_field` — for an arbitrary record over `Spec k`, by
  transporting along the pointed record iso of `exists_projModelIso_of_field` (U1);
* `weilPairingEval_nondegenerate_general` — for a record over an arbitrary base and a
  point over `Spec k`, by the [BC-SWAP] `asSection` bridge.

The last is the axiom-clean replacement for the register entry
`EllipticCurve.weilPairingEval_nondegenerate`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ModularCurves

namespace EllipticCurve

section MapIso

variable {S : Scheme.{u}}

/-- Transport along a record iso is inverted by transport along its inverse. -/
theorem Point.mapIso_symm_mapIso {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g) :
    Point.mapIso φ.symm (Point.mapIso φ x) = x := by
  have hid : φ.hom.left ≫ φ.inv.left = 𝟙 E.asOver.left := by
    have h := congrArg CommaMorphism.left φ.hom_inv_id
    simpa only [Over.comp_left, Over.id_left] using h
  refine Subtype.ext ?_
  show (x.1 ≫ φ.hom.left) ≫ φ.inv.left = x.1
  rw [Category.assoc, hid]
  exact Category.comp_id _

/-- Transport along the inverse of a record iso is inverted by the record iso. -/
theorem Point.mapIso_mapIso_symm {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    {T : Scheme.{u}} {g : T ⟶ S} (y : F.Point g) :
    Point.mapIso φ (Point.mapIso φ.symm y) = y := by
  have hid : φ.inv.left ≫ φ.hom.left = 𝟙 F.asOver.left := by
    have h := congrArg CommaMorphism.left φ.inv_hom_id
    simpa only [Over.comp_left, Over.id_left] using h
  refine Subtype.ext ?_
  show (y.1 ≫ φ.inv.left) ≫ φ.hom.left = y.1
  rw [Category.assoc, hid]
  exact Category.comp_id _

/-- A pointed record iso carries the zero point to the zero point. -/
theorem Point.mapIso_zeroPoint {E F : EllipticCurve S} (φ : E.asOver ≅ F.asOver)
    [IsMonHom φ.hom] {T : Scheme.{u}} (g : T ⟶ S) :
    Point.mapIso φ (E.zeroPoint g) = F.zeroPoint g := by
  refine Subtype.ext ?_
  show (g ≫ E.zero) ≫ φ.hom.left = g ≫ F.zero
  rw [Category.assoc, zero_comp_left_of_isMonHom φ.hom]

end MapIso

section Dictionary

variable {K : Type u} [Field K] [DecidableEq K]

/-- The scheme point of the model underlying a `K`-point of the projective model. -/
def modelPointOfSpecPoint (W : WeierstrassCurve K) [W.IsElliptic]
    (q : SpecPoints (projModel W) (projModelπ W) K) :
    (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))) :=
  ⟨q.1, q.2.trans specMap_algebraMap_self⟩

omit [DecidableEq K] in
@[simp] theorem specPointOfModelPoint_modelPointOfSpecPoint (W : WeierstrassCurve K)
    [W.IsElliptic] (q : SpecPoints (projModel W) (projModelπ W) K) :
    specPointOfModelPoint W (modelPointOfSpecPoint W q) = q := rfl

/-- `basePointCast` is injective (it is a transport along `W.baseChange K = W`). -/
theorem basePointCast_injective' (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective (EllipticCurve.basePointCast W) := by
  have hcast : ∀ {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) (X Y : V₁.toAffine.Point),
      (h ▸ X : V₂.toAffine.Point) = (h ▸ Y : V₂.toAffine.Point) → X = Y := by
    intro V₁ V₂ h X Y hXY; subst h; exact hXY
  intro X Y hXY
  rw [basePointCast_eq_cast, basePointCast_eq_cast] at hXY
  exact hcast (EllipticCurve.baseChange_self_eq W) X Y hXY

/-- `basePointCast` is surjective (it is a transport along `W.baseChange K = W`). -/
theorem basePointCast_surjective (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Surjective (EllipticCurve.basePointCast W) := by
  have hcast : ∀ {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) (Y : V₂.toAffine.Point),
      (h ▸ (h.symm ▸ Y : V₁.toAffine.Point) : V₂.toAffine.Point) = Y := by
    intro V₁ V₂ h Y; subst h; rfl
  intro Y
  refine ⟨((EllipticCurve.baseChange_self_eq W).symm ▸ Y : ((W.baseChange K).toAffine).Point), ?_⟩
  exact (basePointCast_eq_cast W _).trans (hcast (EllipticCurve.baseChange_self_eq W) Y)

omit [DecidableEq K] in
/-- The `Point`-group transport of a model point over `𝟙` is its `K`-point. -/
theorem pointCongr_eq_specPointOfModelPoint (W : WeierstrassCurve K) [W.IsElliptic]
    (x : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K)))) :
    pointCongr (modelEllipticCurve W) specMap_algebraMap_self.symm x =
      specPointOfModelPoint W x :=
  Subtype.ext (pointCongr_apply_coe _ _ _)

/-- **([SPECPT-TORSION], converse)** If the image of a model point in the Weierstrass point
group is `N`-torsion, the point is killed by `[N]`. -/
theorem kill_of_basePointCast_specPointOfModelPoint_torsion (W : WeierstrassCurve K)
    [W.IsElliptic] {N : ℕ} [NeZero N]
    (x : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))))
    (hS : (N : ℤ) • EllipticCurve.basePointCast W
      (projModelPointsEquiv W K (specPointOfModelPoint W x)) = 0) :
    x.1 ≫ (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero := by
  -- strip `basePointCast`
  rw [← basePointCast_zsmul W (N : ℤ)] at hS
  have h1 : (N : ℤ) • projModelPointsEquiv W K (specPointOfModelPoint W x) = 0 :=
    basePointCast_injective' W (hS.trans (EllipticCurve.basePointCast_zero W).symm)
  -- strip the dictionary
  have h2 : (N : ℤ) • (pointCongr (modelEllipticCurve W)
      (specMap_algebraMap_self (K := K)).symm x) = 0 := by
    refine (projModelPointsAddEquiv W K).injective ?_
    rw [map_zsmul, map_zero, pointCongr_eq_specPointOfModelPoint]
    exact h1
  -- strip the base transport
  have h3 : (N : ℤ) • x = 0 := by
    refine (pointCongr (modelEllipticCurve W)
      (specMap_algebraMap_self (K := K)).symm).injective ?_
    rw [map_zsmul, map_zero]
    exact h2
  exact ((modelEllipticCurve W).smul_eq_zero_iff_comp_mulByHom
    (𝟙 (Spec (CommRingCat.of K))) N x).mp h3

end Dictionary

section ModelNondeg

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- **([LEAF-B model core])** Nondegeneracy at the projective Weierstrass model over an
algebraically closed field in which `N` is invertible: cross each value to the `HasseWeil`
field pairing ([VALUE-CROSSING]), swap the slots by antisymmetry, and apply
`weilPairing_nondegenerate`. -/
theorem weilPairingEval_nondegenerate_model (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hNK : (N : K) ≠ 0)
    (x : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))))
    (hx : x.1 ≫ (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero)
    (h : ∀ (y : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))))
      (hy : y.1 ≫ (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero),
      ((modelEllipticCurve W).weilPairingEval x y hx hy :
        Γ(Spec (CommRingCat.of K), ⊤)) = 1) :
    x = (modelEllipticCurve W).zeroPoint (𝟙 (Spec (CommRingCat.of K))) := by
  have hNZ : ((N : ℤ) : K) ≠ 0 := by exact_mod_cast hNK
  have hTt := basePointCast_specPointOfModelPoint_torsion W x hx
  have hzero : EllipticCurve.basePointCast W
      (projModelPointsEquiv W K (specPointOfModelPoint W x)) = 0 := by
    refine HasseWeil.WeilPairing.weilPairing_nondegenerate W (N : ℤ) hNZ _ hTt ?_
    intro Sp hSp
    -- every torsion Weierstrass point comes from a torsion model point
    obtain ⟨X, hX⟩ := basePointCast_surjective W Sp
    set y : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))) :=
      modelPointOfSpecPoint W ((projModelPointsEquiv W K).symm X) with hydef
    have hyval : EllipticCurve.basePointCast W
        (projModelPointsEquiv W K (specPointOfModelPoint W y)) = Sp := by
      rw [hydef, specPointOfModelPoint_modelPointOfSpecPoint, Equiv.apply_symm_apply, hX]
    have hykill : y.1 ≫ (modelEllipticCurve W).mulByHom N =
        𝟙 _ ≫ (modelEllipticCurve W).zero :=
      kill_of_basePointCast_specPointOfModelPoint_torsion W y (by rw [hyval]; exact hSp)
    subst hyval
    -- the value crossing at `(x, y)` plus antisymmetry
    have hone : HasseWeil.WeilPairing.weilPairing W (N : ℤ) hNZ
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K (specPointOfModelPoint W x)))
        (EllipticCurve.basePointCast W (projModelPointsEquiv W K (specPointOfModelPoint W y)))
        (basePointCast_specPointOfModelPoint_torsion W x hx)
        (basePointCast_specPointOfModelPoint_torsion W y hykill) = 1 := by
      rw [← weilPairingEval_eq_weilPairing_model W hNZ x y hx hykill, h y hykill, map_one]
    have hanti := HasseWeil.WeilPairing.weilPairing_antisymm W (N : ℤ) hNZ
      (EllipticCurve.basePointCast W (projModelPointsEquiv W K (specPointOfModelPoint W x)))
      (EllipticCurve.basePointCast W (projModelPointsEquiv W K (specPointOfModelPoint W y)))
      (basePointCast_specPointOfModelPoint_torsion W x hx)
      (basePointCast_specPointOfModelPoint_torsion W y hykill)
    rw [hone, _root_.one_mul] at hanti
    exact hanti
  -- transport the vanishing back through the dictionary
  have h1 : projModelPointsEquiv W K (specPointOfModelPoint W x) = 0 :=
    basePointCast_injective' W (hzero.trans (EllipticCurve.basePointCast_zero W).symm)
  have h2 : pointCongr (modelEllipticCurve W)
      (specMap_algebraMap_self (K := K)).symm x = 0 := by
    refine (projModelPointsAddEquiv W K).injective ?_
    rw [map_zero, pointCongr_eq_specPointOfModelPoint]
    exact h1
  have h3 : x = 0 := by
    refine (pointCongr (modelEllipticCurve W)
      (specMap_algebraMap_self (K := K)).symm).injective ?_
    rw [map_zero]
    exact h2
  exact h3.trans (Subtype.ext ((modelEllipticCurve W).point_zero_val _))

end ModelNondeg

section FieldNondeg

variable {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- **([LEAF-B field])** Nondegeneracy for an arbitrary elliptic record over an
algebraically closed field: transport to the projective model along the pointed record
iso of `exists_projModelIso_of_field` (U1) and apply the model core. -/
theorem weilPairingEval_nondegenerate_of_field (E : EllipticCurve (Spec (CommRingCat.of K)))
    {N : ℕ} [NeZero N] (hNK : (N : K) ≠ 0)
    (x : E.Point (𝟙 (Spec (CommRingCat.of K))))
    (hx : x.1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero)
    (h : ∀ (y : E.Point (𝟙 (Spec (CommRingCat.of K))))
      (hy : y.1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero),
      (E.weilPairingEval x y hx hy : Γ(Spec (CommRingCat.of K), ⊤)) = 1) :
    x = E.zeroPoint (𝟙 (Spec (CommRingCat.of K))) := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := by
    haveI : IsNoetherianRing K := inferInstance
    infer_instance
  obtain ⟨W, hell, ψ, hψπ, hψz⟩ := exists_projModelIso_of_field E
  haveI := hell
  have hΦw : ψ.hom ≫ (modelEllipticCurve W).asOver.hom = E.asOver.hom := hψπ
  set Φ : E.asOver ≅ (modelEllipticCurve W).asOver := Over.isoMk ψ hΦw with hΦ
  have hΦη : (η[E.asOver] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.asOver) ≫ Φ.hom =
      η[(modelEllipticCurve W).asOver] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, E.one_eq_zero, (modelEllipticCurve W).one_eq_zero]
    exact (Category.assoc _ _ _).trans
      (congrArg _ (show E.zero ≫ ψ.hom = (modelEllipticCurve W).zero from hψz))
  haveI hmon : IsMonHom Φ.hom := isMonHom_of_pointed Φ.hom hΦη
  haveI hmon' : IsMonHom Φ.symm.hom := isMonHom_symm Φ
  have hx' : (Point.mapIso Φ x).1 ≫ (modelEllipticCurve W).mulByHom N =
      𝟙 _ ≫ (modelEllipticCurve W).zero :=
    Point.mapIso_killedBy Φ hx
  -- the value at a model point is the value at its `Φ⁻¹`-preimage
  have hcongr : ∀ (y₁ y₂ : (modelEllipticCurve W).Point (𝟙 (Spec (CommRingCat.of K))))
      (hy₁ : y₁.1 ≫ (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero)
      (hy₂ : y₂.1 ≫ (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero),
      y₁ = y₂ →
      ((modelEllipticCurve W).weilPairingEval (Point.mapIso Φ x) y₁ hx' hy₁ :
          Γ(Spec (CommRingCat.of K), ⊤)) =
        ((modelEllipticCurve W).weilPairingEval (Point.mapIso Φ x) y₂ hx' hy₂ :
          Γ(Spec (CommRingCat.of K), ⊤)) := by
    intro y₁ y₂ hy₁ hy₂ hEq; subst hEq; rfl
  have hmodel := weilPairingEval_nondegenerate_model W hNK (Point.mapIso Φ x) hx' ?_
  · -- transport the conclusion back along `Φ`
    have hz : Point.mapIso Φ x = Point.mapIso Φ (E.zeroPoint (𝟙 (Spec (CommRingCat.of K)))) := by
      rw [hmodel, Point.mapIso_zeroPoint]
    have hz' := congrArg (Point.mapIso Φ.symm) hz
    rwa [Point.mapIso_symm_mapIso, Point.mapIso_symm_mapIso] at hz'
  · intro yhat hyhat
    have hyy : (Point.mapIso Φ.symm yhat).1 ≫ E.mulByHom N = 𝟙 _ ≫ E.zero :=
      Point.mapIso_killedBy Φ.symm hyhat
    have hyy' : (Point.mapIso Φ (Point.mapIso Φ.symm yhat)).1 ≫
        (modelEllipticCurve W).mulByHom N = 𝟙 _ ≫ (modelEllipticCurve W).zero :=
      Point.mapIso_killedBy Φ hyy
    refine (hcongr yhat (Point.mapIso Φ (Point.mapIso Φ.symm yhat)) hyhat hyy'
      (Point.mapIso_mapIso_symm Φ yhat).symm).trans ?_
    rw [weilPairingEval_mapIso Φ x (Point.mapIso Φ.symm yhat) hx hyy hx' hyy']
    exact h (Point.mapIso Φ.symm yhat) hyy

end FieldNondeg

section Bridge

/-- **([BC-SWAP bridge, two-point])** The value of the base-changed record at the
`asSection` images of two points is the value of the original record at those points. -/
theorem weilPairingEval_asSection_bridge {S : Scheme.{u}} (E : EllipticCurve S)
    {T : Scheme.{u}} {N : ℕ} [NeZero N] (g : T ⟶ S) (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (EllipticCurve.Point.asSection E g x).1 ≫ (E.baseChange g).mulByHom N =
      𝟙 T ≫ (E.baseChange g).zero)
    (hy' : (EllipticCurve.Point.asSection E g y).1 ≫ (E.baseChange g).mulByHom N =
      𝟙 T ≫ (E.baseChange g).zero) :
    ((E.baseChange g).weilPairingEval (EllipticCurve.Point.asSection E g x)
        (EllipticCurve.Point.asSection E g y) hx' hy' : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) := by
  haveI hsepE : IsSeparated E.π := inferInstance
  haveI hsepBC : IsSeparated ((E.baseChange g).π) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π g hsepE
  have hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange g).π) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ E.smooth
  have hswcondx : ((EllipticCurve.Point.asSection E g x).1 ≫ (bcSwapIso E g).inv) ≫
      pullback.snd ((E.baseChange g).π) (𝟙 T) = 𝟙 T := by
    rw [← asSection_eq_bcSwap E g (EllipticCurve.Point.asSection E g x)]
    exact (EllipticCurve.Point.asSection (E.baseChange g) (𝟙 T)
      (EllipticCurve.Point.asSection E g x)).2
  have hswcondy : ((EllipticCurve.Point.asSection E g y).1 ≫ (bcSwapIso E g).inv) ≫
      pullback.snd ((E.baseChange g).π) (𝟙 T) = 𝟙 T := by
    rw [← asSection_eq_bcSwap E g (EllipticCurve.Point.asSection E g y)]
    exact (EllipticCurve.Point.asSection (E.baseChange g) (𝟙 T)
      (EllipticCurve.Point.asSection E g y)).2
  have hswptx : EllipticCurve.Point.asSection (E.baseChange g) (𝟙 T)
      (EllipticCurve.Point.asSection E g x) =
      (⟨(EllipticCurve.Point.asSection E g x).1 ≫ (bcSwapIso E g).inv, hswcondx⟩ :
        ((E.baseChange g).baseChange (𝟙 T)).Point (𝟙 T)) :=
    Subtype.ext (asSection_eq_bcSwap E g (EllipticCurve.Point.asSection E g x))
  have hswpty : EllipticCurve.Point.asSection (E.baseChange g) (𝟙 T)
      (EllipticCurve.Point.asSection E g y) =
      (⟨(EllipticCurve.Point.asSection E g y).1 ≫ (bcSwapIso E g).inv, hswcondy⟩ :
        ((E.baseChange g).baseChange (𝟙 T)).Point (𝟙 T)) :=
    Subtype.ext (asSection_eq_bcSwap E g (EllipticCurve.Point.asSection E g y))
  have hswtx : (⟨(EllipticCurve.Point.asSection E g x).1 ≫ (bcSwapIso E g).inv, hswcondx⟩ :
      ((E.baseChange g).baseChange (𝟙 T)).Point (𝟙 T)) ∈
      torsionPoints (E.baseChange g) (𝟙 T) N :=
    hswptx ▸ asSection_mem_torsionPoints (E.baseChange g)
      (EllipticCurve.Point.asSection E g x) hx'
  have hswty : (⟨(EllipticCurve.Point.asSection E g y).1 ≫ (bcSwapIso E g).inv, hswcondy⟩ :
      ((E.baseChange g).baseChange (𝟙 T)).Point (𝟙 T)) ∈
      torsionPoints (E.baseChange g) (𝟙 T) N :=
    hswpty ▸ asSection_mem_torsionPoints (E.baseChange g)
      (EllipticCurve.Point.asSection E g y) hy'
  rw [(E.baseChange g).weilPairingEval_eq_weilPairingKM
      (EllipticCurve.Point.asSection E g x) (EllipticCurve.Point.asSection E g y) hx' hy',
    E.weilPairingEval_eq_weilPairingKM x y hx hy]
  refine congrArg Units.val ?_
  rw [weilPairingKM_congr (E.baseChange g) (E.baseChange g).smooth (𝟙 T) N
    hswptx hswpty
    (asSection_mem_torsionPoints (E.baseChange g) (EllipticCurve.Point.asSection E g x) hx')
    (asSection_mem_torsionPoints (E.baseChange g) (EllipticCurve.Point.asSection E g y) hy')]
  exact weilPairingKM_bcSwap E g E.smooth hsmBC N
    (EllipticCurve.Point.asSection E g x) (asSection_mem_torsionPoints E x hx)
    (EllipticCurve.Point.asSection E g y) (asSection_mem_torsionPoints E y hy)
    hswcondx hswtx hswcondy hswty

/-- `Point.asSection` as an additive equivalence onto the points of the base change over
the identity. -/
noncomputable def asSectionEquiv {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) : E.Point g ≃+ (E.baseChange g).Point (𝟙 T) :=
  (pointCongr E (Category.id_comp g).symm).trans
    (EllipticCurve.Point.baseChangeEquiv E g (𝟙 T)).symm

@[simp] theorem asSectionEquiv_apply {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (x : E.Point g) :
    asSectionEquiv E g x = EllipticCurve.Point.asSection E g x :=
  (asSection_eq_baseChangeEquiv_symm E g x).symm

end Bridge

section GeneralNondeg

/-- **([LEAF B] = T-C3 = KM 2.8, fibrewise nondegeneracy)** For a record over an arbitrary
base and a geometric point of the base at which `N` is invertible, an `N`-torsion point
pairing trivially with every `N`-torsion point is the zero point.

This is the axiom-clean replacement for the register entry
`EllipticCurve.weilPairingEval_nondegenerate`. -/
theorem weilPairingEval_nondegenerate_general {S : Scheme.{u}} (E : EllipticCurve S)
    {N : ℕ} [NeZero N] (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (t : Spec (CommRingCat.of k) ⟶ S) (x : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (h : ∀ (y : E.Point t) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      (E.weilPairingEval x y hx hy : Γ(Spec (CommRingCat.of k), ⊤)) = 1) :
    x = E.zeroPoint t := by
  classical
  have hkill : ∀ (z : E.Point t), z.1 ≫ E.mulByHom N = t ≫ E.zero →
      (EllipticCurve.Point.asSection E t z).1 ≫ (E.baseChange t).mulByHom N =
        𝟙 _ ≫ (E.baseChange t).zero := by
    intro z hz
    rw [← (E.baseChange t).smul_eq_zero_iff_comp_mulByHom (𝟙 _) N
      (EllipticCurve.Point.asSection E t z)]
    exact asSection_mem_torsionPoints E z hz
  have hcongr : ∀ (y₁ y₂ : (E.baseChange t).Point (𝟙 (Spec (CommRingCat.of k))))
      (h₁ : y₁.1 ≫ (E.baseChange t).mulByHom N = 𝟙 _ ≫ (E.baseChange t).zero)
      (h₂ : y₂.1 ≫ (E.baseChange t).mulByHom N = 𝟙 _ ≫ (E.baseChange t).zero),
      y₁ = y₂ →
      ((E.baseChange t).weilPairingEval (EllipticCurve.Point.asSection E t x) y₁
          (hkill x hx) h₁ : Γ(Spec (CommRingCat.of k), ⊤)) =
        ((E.baseChange t).weilPairingEval (EllipticCurve.Point.asSection E t x) y₂
          (hkill x hx) h₂ : Γ(Spec (CommRingCat.of k), ⊤)) := by
    intro y₁ y₂ h₁ h₂ hEq; subst hEq; rfl
  have hnd := weilPairingEval_nondegenerate_of_field (E.baseChange t) hNk
    (EllipticCurve.Point.asSection E t x) (hkill x hx) ?_
  · -- transport the conclusion back through `asSectionEquiv`
    have h0 : asSectionEquiv E t x = 0 := by
      rw [asSectionEquiv_apply, hnd]
      exact Subtype.ext ((E.baseChange t).point_zero_val _).symm
    have hx0 : x = 0 := by
      refine (asSectionEquiv E t).injective ?_
      rw [map_zero]
      exact h0
    exact hx0.trans (Subtype.ext (E.point_zero_val t))
  · intro yhat hyhat
    -- every point of the base change over `𝟙` is an `asSection`
    have hyyval : EllipticCurve.Point.asSection E t ((asSectionEquiv E t).symm yhat) = yhat := by
      rw [← asSectionEquiv_apply, AddEquiv.apply_symm_apply]
    have hyykill : ((asSectionEquiv E t).symm yhat).1 ≫ E.mulByHom N = t ≫ E.zero := by
      refine (E.smul_eq_zero_iff_comp_mulByHom t N _).mp ?_
      refine (asSectionEquiv E t).injective ?_
      rw [map_zsmul, map_zero, asSectionEquiv_apply, hyyval]
      exact ((E.baseChange t).smul_eq_zero_iff_comp_mulByHom (𝟙 _) N yhat).mpr hyhat
    refine (hcongr yhat (EllipticCurve.Point.asSection E t ((asSectionEquiv E t).symm yhat))
      hyhat (hkill _ hyykill) hyyval.symm).trans ?_
    rw [weilPairingEval_asSection_bridge E t x ((asSectionEquiv E t).symm yhat) hx hyykill
      (hkill x hx) (hkill _ hyykill)]
    exact h ((asSectionEquiv E t).symm yhat) hyykill

end GeneralNondeg

end EllipticCurve

end ModularCurves
