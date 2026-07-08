/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.Moduli.WeierstrassAtlas

/-!
# The Weierstrass coordinate-change action and the moduli groupoid `M_ell^W = [U/G]`

AINTLIB ModularCurves T-W4 (+ the T-W6 substrate): the coordinate-change group
`G = WeierstrassCurve.VariableChange` acting on the universal Weierstrass atlas
`U = weierstrassAtlas = Spec ℤ[a₁,…,a₆][Δ⁻¹]` (T-W5), at the level demanded by the
v9.2 severance and the v10.36 architecture finding: `G` is an affine group **scheme**
(`𝔾_m ⋉ 𝔸³`), so the quotient groupoid at a base `S` must use the `S`-points
`G(Γ) = VariableChange Γ` acting on `U(Γ) = {W : WeierstrassCurve Γ // IsUnit W.Δ}` —
ring-by-ring, functorially — rather than a single abstract group acting by scheme
automorphisms (`SchemeAction` is the Q-finite vocabulary, not this one).

Everything is mathlib-native: `WeierstrassCurve.map`/`map_Δ` (coefficient base change),
`VariableChange` group + `•` action, `VariableChange.map` + `map_variableChange`
(base-change naturality of the action). The atlas dictionary
`(WeierstrassAtlasRing →+* B) ≃ ellipticW B` is the universal property of
`MvPolynomial (Fin 5) ℤ` localized away from `Δ`.

* `ellipticW B`: Weierstrass curves over `B` with invertible discriminant — the
  `B`-points of `U`.
* `ellipticW.map`: functorial base change; `smul` preserves `ellipticW` (the action of
  `VariableChange B`).
* `toRingHom` / `ofRingHom`: the atlas dictionary, with round-trip and naturality
  lemmas (sorried leaves of this ticket).

The groupoid-valued functor `M_ell^W` and the T-W6 equivalence with Weierstrass-data
records (T-A8) build on this layer in the same file, next increment. Decomposition
notes: board v10.36; v10.24(b) interfaces accompany each heavy definition as it lands.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

namespace ModularCurves

universe u

variable {B C : Type*} [CommRing B] [CommRing C]

/-- Weierstrass curves with invertible discriminant over `B`: the `B`-points of the
universal Weierstrass atlas `U` (T-W5). -/
def ellipticW (B : Type*) [CommRing B] : Type _ :=
  {W : WeierstrassCurve B // IsUnit W.Δ}

namespace ellipticW

/-- Base change of an atlas point along a ring map. -/
def map (f : B →+* C) (W : ellipticW B) : ellipticW C :=
  ⟨W.1.map f, by rw [map_Δ]; exact W.2.map f⟩

@[simp] theorem map_coe (f : B →+* C) (W : ellipticW B) : (W.map f).1 = W.1.map f :=
  rfl

theorem map_id (W : ellipticW B) : W.map (RingHom.id B) = W :=
  Subtype.ext W.1.map_id

theorem map_comp {D : Type*} [CommRing D] (f : B →+* C) (g : C →+* D) (W : ellipticW B) :
    (W.map f).map g = W.map (g.comp f) :=
  Subtype.ext (W.1.map_map f g)

/-- The coordinate-change action preserves invertibility of the discriminant
(`variableChange_Δ`: `Δ` scales by the unit `u⁻¹²`). -/
theorem isUnit_smul_Δ (C' : VariableChange B) (W : ellipticW B) :
    IsUnit (C' • W.1).Δ := by
  rw [variableChange_Δ]
  exact ((C'.u⁻¹).isUnit.pow 12).mul W.2

/-- The action of the coordinate-change group `G(B) = VariableChange B` on the
`B`-points of the atlas. -/
instance : SMul (VariableChange B) (ellipticW B) :=
  ⟨fun C' W => ⟨C' • W.1, isUnit_smul_Δ C' W⟩⟩

@[simp] theorem smul_coe (C' : VariableChange B) (W : ellipticW B) :
    (C' • W).1 = C' • W.1 :=
  rfl

instance : MulAction (VariableChange B) (ellipticW B) where
  one_smul W := Subtype.ext (one_smul _ _)
  mul_smul C₁ C₂ W := Subtype.ext (mul_smul _ _ _)

/-- Base-change naturality of the action (mathlib's `map_variableChange`). -/
theorem map_smul (f : B →+* C) (C' : VariableChange B) (W : ellipticW B) :
    (C' • W).map f = C'.map f • W.map f :=
  Subtype.ext (map_variableChange _ _ _).symm

end ellipticW

/-- The atlas dictionary, forward direction: a ring map out of the atlas ring gives a
Weierstrass curve with invertible discriminant (push the universal curve forward). -/
noncomputable def ellipticWOfRingHom (φ : WeierstrassAtlasRing →+* B) : ellipticW B :=
  ⟨universalWeierstrassLoc.map φ, by
    rw [map_Δ]
    exact universalWeierstrassLoc.isUnit_Δ.map φ⟩

/-- Specialisation of the universal coefficient ring at the coefficients of `W`. -/
noncomputable def specializeAt (W : WeierstrassCurve B) :
    MvPolynomial (Fin 5) ℤ →+* B :=
  (MvPolynomial.aeval ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]).toRingHom

/-- The universal curve specialises to `W` at `W`'s own coefficients. -/
theorem universalWeierstrass_map_specializeAt (W : WeierstrassCurve B) :
    universalWeierstrass.map (specializeAt W) = W := by
  ext <;>
    simp [universalWeierstrass, WeierstrassCurve.map, specializeAt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.cons_val_four]

theorem specializeAt_Δ (W : WeierstrassCurve B) :
    specializeAt W universalWeierstrass.Δ = W.Δ := by
  rw [← map_Δ, universalWeierstrass_map_specializeAt]

/-- The atlas dictionary, reverse direction: an atlas point gives a ring map out of the
atlas ring, by the universal property of `ℤ[a₁,…,a₆][Δ⁻¹]`. -/
noncomputable def ringHomOfEllipticW (W : ellipticW B) : WeierstrassAtlasRing →+* B :=
  IsLocalization.Away.lift universalWeierstrass.Δ
    (g := specializeAt W.1) (by rw [specializeAt_Δ]; exact W.2)

theorem ellipticWOfRingHom_ringHomOfEllipticW (W : ellipticW B) :
    ellipticWOfRingHom (ringHomOfEllipticW W) = W := by
  apply Subtype.ext
  show universalWeierstrassLoc.map _ = W.1
  rw [universalWeierstrassLoc, map_map]
  have h : (ringHomOfEllipticW W).comp (algebraMap (MvPolynomial (Fin 5) ℤ)
      WeierstrassAtlasRing) = specializeAt W.1 :=
    IsLocalization.lift_comp _
  rw [h]
  exact universalWeierstrass_map_specializeAt W.1

/-- The Weierstrass moduli groupoid `[U/G](B)`: objects are atlas points (Weierstrass
curves with unit discriminant), morphisms `W ⟶ W'` are coordinate changes carrying `W`
to `W'`. This is the action groupoid of `G(B) = VariableChange B` on `U(B)`,
v9.2-severance-faithfully (the group's `B`-points, not a fixed abstract group). -/
def MellWGroupoid (B : Type*) [CommRing B] : Type _ := ellipticW B

namespace MellWGroupoid

/-- Interpret an atlas point as an object of the moduli groupoid. -/
def mk (W : ellipticW B) : MellWGroupoid B := W

/-- The underlying atlas point. -/
def pt (W : MellWGroupoid B) : ellipticW B := W

@[simp] theorem pt_mk (W : ellipticW B) : pt (mk W) = W := rfl

instance : Groupoid (MellWGroupoid B) where
  Hom W W' := {C' : VariableChange B // C' • W.pt = W'.pt}
  id W := ⟨1, one_smul _ _⟩
  comp f g := ⟨g.1 * f.1, by rw [mul_smul, f.2, g.2]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm
  inv f := ⟨f.1⁻¹, inv_smul_eq_iff.mpr f.2.symm⟩
  inv_comp f := Subtype.ext (mul_inv_cancel _)
  comp_inv f := Subtype.ext (inv_mul_cancel _)

@[simp] theorem comp_val {W W' W'' : MellWGroupoid B} (f : W ⟶ W') (g : W' ⟶ W'') :
    (f ≫ g).1 = g.1 * f.1 :=
  rfl

@[simp] theorem id_val (W : MellWGroupoid B) : (𝟙 W : W ⟶ W).1 = 1 :=
  rfl

/-- Base change of the moduli groupoid along a ring map, as a functor. -/
@[simps]
def mapFunctor (f : B →+* C) : MellWGroupoid B ⥤ MellWGroupoid C where
  obj W := mk (W.pt.map f)
  map {W W'} g := ⟨g.1.map f, by
    show g.1.map f • W.pt.map f = W'.pt.map f
    rw [← ellipticW.map_smul, g.2]⟩
  map_id W := Subtype.ext (map_one (VariableChange.mapHom f))
  map_comp g h := Subtype.ext (by
    show (h.1 * g.1).map f = h.1.map f * g.1.map f
    exact map_mul (VariableChange.mapHom f) h.1 g.1)

@[simp] theorem eqToHom_val {W W' : MellWGroupoid B} (h : W = W') :
    (eqToHom h).1 = 1 := by
  subst h; rfl

private theorem mapFunctor_id :
    mapFunctor (RingHom.id B) = 𝟭 (MellWGroupoid B) := by
  refine CategoryTheory.Functor.ext (fun W => congrArg mk (ellipticW.map_id W.pt)) ?_
  intro W W' g
  apply Subtype.ext
  simp [VariableChange.map_id]

private theorem mapFunctor_comp {D : Type*} [CommRing D] (f : B →+* C) (g : C →+* D) :
    mapFunctor (g.comp f) = mapFunctor f ⋙ mapFunctor g := by
  refine CategoryTheory.Functor.ext
    (fun W => congrArg mk (ellipticW.map_comp f g W.pt).symm) ?_
  intro W W' h
  apply Subtype.ext
  simp [VariableChange.map_map]

end MellWGroupoid

/-- **`M_ell^W` on coefficient rings**: the `[U/G]`-groupoid, as a `Cat`-valued functor
on commutative rings. The scheme-level moduli functor is `Scheme.Γ ⋙ MellW`
(`MellWScheme` below). Interface: the `@[simps]` projections. -/
@[simps]
def MellW : CommRingCat.{u} ⥤ Cat.{u, u} where
  obj B := Cat.of (MellWGroupoid B)
  map f := (MellWGroupoid.mapFunctor f.hom).toCatHom
  map_id B := congrArg Functor.toCatHom MellWGroupoid.mapFunctor_id
  map_comp f g := congrArg Functor.toCatHom (MellWGroupoid.mapFunctor_comp f.hom g.hom)

/-- **The Weierstrass moduli stack functor `M_ell^W = [U/G]` on schemes** (T-W6's
object): groupoid-valued via global sections. Contravariant: a morphism of schemes
pulls Weierstrass data back along its `Γ`-map. -/
def MellWScheme : Scheme.{u}ᵒᵖ ⥤ Cat.{u, u} :=
  Scheme.Γ ⋙ MellW

theorem ringHomOfEllipticW_ellipticWOfRingHom (φ : WeierstrassAtlasRing →+* B) :
    ringHomOfEllipticW (ellipticWOfRingHom φ) = φ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers universalWeierstrass.Δ)
  have h : (ringHomOfEllipticW (ellipticWOfRingHom φ)).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing)
      = specializeAt (ellipticWOfRingHom φ).1 :=
    IsLocalization.lift_comp _
  rw [h]
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [specializeAt, map_intCast]
  · intro i
    fin_cases i <;>
      simp [specializeAt, ellipticWOfRingHom, universalWeierstrassLoc,
        WeierstrassCurve.map, universalWeierstrass, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_three, Matrix.cons_val_four]

/-- **The atlas dictionary, bundled** (T-W4's headline): ring maps out of the atlas
ring — equivalently, by `Γ`–`Spec` adjunction, scheme maps into `U = weierstrassAtlas`
— correspond exactly to Weierstrass curves with invertible discriminant. -/
noncomputable def atlasDictionary : (WeierstrassAtlasRing →+* B) ≃ ellipticW B where
  toFun := ellipticWOfRingHom
  invFun := ringHomOfEllipticW
  left_inv := ringHomOfEllipticW_ellipticWOfRingHom
  right_inv := ellipticWOfRingHom_ringHomOfEllipticW

/-- The classifying map of an atlas point over `S`: the morphism `S ⟶ U` whose
`Γ`-transpose specialises the universal coefficients at `W`'s. The universal curve
pulled back along `classify W` is the curve presented by `W` (T-W6 tail). -/
noncomputable def classify {S : Scheme.{0}} (W : ellipticW Γ(S, ⊤)) :
    S ⟶ weierstrassAtlas :=
  S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))

/-- **The curve presented by an atlas point** (T-W6): the universal elliptic curve
pulled back along the classifying map — an elliptic curve over `S` in the
definition-of-record sense (T-A8), with all structure transported by base change. -/
noncomputable def curveOf {S : Scheme.{0}} (W : ellipticW Γ(S, ⊤)) :
    EllipticCurveGeom S where
  E := pullback universalCurveπ (classify W)
  π := pullback.snd universalCurveπ (classify W)
  zero := pullback.lift (classify W ≫ universalCurveZero) (𝟙 S)
    (by rw [Category.assoc, universalCurveZero_π, Category.comp_id, Category.id_comp])
  zero_π := pullback.lift_snd _ _ _
  smooth := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ universalCurve_smooth
  proper := MorphismProperty.pullback_snd _ _ inferInstance
  localModel := universalEllipticCurve.localModel.baseChange (classify W)

section CurveOfPasting

variable {S : Scheme.{0}} (W : ellipticW Γ(S, ⊤))

/-- **(T-W6c-i)** The presented curve is the pullback of `W`'s own projective model
along `S ⟶ Spec Γ(S,⊤)`: paste the classifying composite, identify the middle fibre by
`isPullback_projModelBaseChange`, and rewrite along the dictionary round-trip. -/
private theorem eqToHom_projModelπ {V V' : WeierstrassCurve ↑Γ(S, ⊤)} (h : V = V') :
    eqToHom (congrArg (projModel ·) h) ≫ projModelπ V' = projModelπ V := by
  subst h; simp

private theorem uWL_map_ringHomOf :
    universalWeierstrassLoc.map
      (@algebraMap _ _ _ _ ((ringHomOfEllipticW W).toAlgebra)) = W.1 := by
  rw [RingHom.algebraMap_toAlgebra]
  exact congrArg Subtype.val (ellipticWOfRingHom_ringHomOfEllipticW W)

/-- The middle-fibre identification: the fibre of the universal curve over
`Spec Γ(S,⊤)` is `W`'s own projective model. -/
private noncomputable def curveOfMiddle :
    pullback universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)))
      ≅ projModel W.1 :=
  (@isPullback_projModelBaseChange _ _ _ _ (ringHomOfEllipticW W).toAlgebra
      universalWeierstrassLoc).isoPullback.symm ≪≫
    eqToIso (congrArg (projModel ·) (uWL_map_ringHomOf W))

private theorem curveOfMiddle_π :
    (curveOfMiddle W).hom ≫ projModelπ W.1 =
      pullback.snd universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) := by
  simp only [curveOfMiddle, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [eqToHom_projModelπ (uWL_map_ringHomOf W)]
  exact (@isPullback_projModelBaseChange _ _ _ _ (ringHomOfEllipticW W).toAlgebra
    universalWeierstrassLoc).isoPullback_inv_snd

noncomputable def curveOfPasting :
    (curveOf W).E ≅ pullback (projModelπ W.1) S.toSpecΓ := by
  refine (pullbackLeftPullbackSndIso universalCurveπ
      (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) S.toSpecΓ).symm ≪≫ ?_
  have hmapiso : IsIso (pullback.map
      (pullback.snd universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))))
      S.toSpecΓ (projModelπ W.1) S.toSpecΓ
      (curveOfMiddle W).hom (𝟙 S) (𝟙 _)
      (by rw [Category.comp_id, curveOfMiddle_π]) (by simp)) := by
    infer_instance
  exact @asIso _ _ _ _ _ hmapiso

/-- The pasting identification is a morphism over `S`. -/
theorem curveOfPasting_snd :
    (curveOfPasting W).hom ≫ pullback.snd (projModelπ W.1) S.toSpecΓ = (curveOf W).π := by
  simp only [curveOfPasting, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullback.lift_snd, Category.comp_id]
  rw [Iso.inv_comp_eq]
  exact (pullbackLeftPullbackSndIso_hom_snd universalCurveπ
    (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) S.toSpecΓ).symm

private theorem eqToHom_projModelZero {V V' : WeierstrassCurve ↑Γ(S, ⊤)} (h : V = V') :
    projModelZero V ≫ eqToHom (congrArg (projModel ·) h) = projModelZero V' := by
  subst h; simp

private theorem zliftComm :
    (classify W ≫ universalCurveZero) ≫ universalCurveπ =
      S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)) := by
  rw [Category.assoc, universalCurveZero_π, Category.comp_id]; rfl

/-- The middle-fibre identification matches zero sections: the universal zero section,
pulled back to `S`'s fibre, is `W`'s own `projModelZero`. -/
private theorem curveOfMiddle_zero :
    pullback.lift (classify W ≫ universalCurveZero) S.toSpecΓ (zliftComm W) ≫
        (curveOfMiddle W).hom = S.toSpecΓ ≫ projModelZero W.1 := by
  have key : pullback.lift (classify W ≫ universalCurveZero) S.toSpecΓ (zliftComm W) ≫
      (@isPullback_projModelBaseChange _ _ _ _ ((ringHomOfEllipticW W).toAlgebra)
        universalWeierstrassLoc).isoPullback.inv
      = S.toSpecΓ ≫ projModelZero (universalWeierstrassLoc.map
          (@algebraMap _ _ _ _ ((ringHomOfEllipticW W).toAlgebra))) := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [(@isPullback_projModelBaseChange _ _ _ _ ((ringHomOfEllipticW W).toAlgebra)
          universalWeierstrassLoc).isoPullback_hom_fst]
      rw [pullback.lift_fst]
      erw [@projModelZero_baseChange _ _ _ _ ((ringHomOfEllipticW W).toAlgebra)
        universalWeierstrassLoc]
      show _ = S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)) ≫
        projModelZero universalWeierstrassLoc
      rw [← Category.assoc]
      rfl
    · rw [Category.assoc, Category.assoc]
      erw [(@isPullback_projModelBaseChange _ _ _ _ ((ringHomOfEllipticW W).toAlgebra)
          universalWeierstrassLoc).isoPullback_hom_snd]
      rw [pullback.lift_snd, projModelZero_projModelπ]
      exact (Category.comp_id _).symm
  simp only [curveOfMiddle, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, ← Category.assoc]
  rw [key, Category.assoc, eqToHom_projModelZero (uWL_map_ringHomOf W)]

/-- The pasting identification matches the zero sections.

ROUTE (decomposed per v10.24(a), board v10.40): `pullback.hom_ext`; the `snd`-leg is
`curveOfPasting_snd` + `zero_π`; the `fst`-leg needs (i) `pullbackLeftPullbackSndIso_inv_fst`
+ `_inv_fst_snd` to compute `zero ≫ pasting.inv ≫ fst` as the evident lift, and (ii) a
`curveOfMiddle_zero` compat (`lift ≫ (curveOfMiddle W).hom = S.toSpecΓ ≫ projModelZero W.1`)
via `IsPullback.isoPullback`-projections + `projModelZero_baseChange` — the exact analogue
of the atlas file's T-W5a case-c2 battle, one seam-lemma per step. -/
theorem curveOfPasting_zero :
    (curveOf W).zero ≫ (curveOfPasting W).hom =
      pullback.lift (S.toSpecΓ ≫ projModelZero W.1) (𝟙 S)
        (by rw [Category.assoc, projModelZero_projModelπ]
            exact (Category.comp_id _).trans (Category.id_comp _).symm) := by
  have hz : (curveOf W).zero ≫ (pullbackLeftPullbackSndIso universalCurveπ
      (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) S.toSpecΓ).inv ≫
      pullback.fst (pullback.snd universalCurveπ
        (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)))) S.toSpecΓ
      = pullback.lift (classify W ≫ universalCurveZero) S.toSpecΓ (zliftComm W) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      rw [pullback.lift_fst]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, Category.assoc]
      erw [pullbackLeftPullbackSndIso_inv_fst_snd]
      rw [pullback.lift_snd]
      erw [pullback.lift_snd_assoc]
      rw [Category.id_comp]
  apply pullback.hom_ext
  · simp only [curveOfPasting, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullback.lift_fst]
    rw [reassoc_of% hz, curveOfMiddle_zero]
  · rw [Category.assoc, curveOfPasting_snd, pullback.lift_snd]
    exact (curveOf W).zero_π

end CurveOfPasting


section VCTransport

variable {S : Scheme.{0}} (C' : VariableChange ↑Γ(S, ⊤)) {W W' : ellipticW ↑Γ(S, ⊤)}

/-- The variable-change map of projective models, retargeted along `C' • W = W'`
(T-W7.0h's `projModelVCIso`, inverted and transported). -/
private noncomputable def vcModelHom (hC : C' • W = W') :
    projModel W.1 ⟶ projModel W'.1 :=
  (projModelVCIso C' W.1).inv ≫
    eqToHom (congrArg (projModel ·) (show C' • W.1 = W'.1 from congrArg Subtype.val hC))

private theorem vcModelHom_π (hC : C' • W = W') :
    vcModelHom C' hC ≫ projModelπ W'.1 = projModelπ W.1 := by
  rw [vcModelHom, Category.assoc,
    eqToHom_projModelπ (show C' • W.1 = W'.1 from congrArg Subtype.val hC),
    Iso.inv_comp_eq]
  exact (projModelVCIso_π C' W.1).symm

private theorem zero_vcModelHom (hC : C' • W = W') :
    projModelZero W.1 ≫ vcModelHom C' hC = projModelZero W'.1 := by
  rw [vcModelHom, ← Category.assoc,
    show projModelZero W.1 ≫ (projModelVCIso C' W.1).inv = projModelZero (C' • W.1) from
      (Iso.comp_inv_eq _).mpr (projModelVCIso_zero C' W.1).symm]
  exact eqToHom_projModelZero (show C' • W.1 = W'.1 from congrArg Subtype.val hC)

private theorem vcMiddle_eq₁ (hC : C' • W = W') :
    projModelπ W.1 ≫ 𝟙 (Spec (CommRingCat.of ↑Γ(S, ⊤))) =
      vcModelHom C' hC ≫ projModelπ W'.1 := by
  rw [Category.comp_id, vcModelHom_π]

private theorem vcMiddle_eq₂ :
    S.toSpecΓ ≫ 𝟙 (Spec (CommRingCat.of ↑Γ(S, ⊤))) = 𝟙 S ≫ S.toSpecΓ :=
  (Category.comp_id _).trans (Category.id_comp _).symm

private noncomputable def vcMiddleMap (hC : C' • W = W') :
    pullback (projModelπ W.1) S.toSpecΓ ⟶ pullback (projModelπ W'.1) S.toSpecΓ :=
  pullback.map _ _ _ _ (vcModelHom C' hC) (𝟙 S) (𝟙 (Spec (CommRingCat.of ↑Γ(S, ⊤))))
    (vcMiddle_eq₁ C' hC) vcMiddle_eq₂

private theorem isIso_vcMiddleMap (hC : C' • W = W') : IsIso (vcMiddleMap C' hC) := by
  have : IsIso (vcModelHom C' hC) := by rw [vcModelHom]; infer_instance
  rw [vcMiddleMap]
  infer_instance

private noncomputable def vcMiddleIso (hC : C' • W = W') :
    pullback (projModelπ W.1) S.toSpecΓ ≅ pullback (projModelπ W'.1) S.toSpecΓ :=
  @asIso _ _ _ _ (vcMiddleMap C' hC) (isIso_vcMiddleMap C' hC)

private theorem vcMiddleIso_snd (hC : C' • W = W') :
    (vcMiddleIso C' hC).hom ≫ pullback.snd (projModelπ W'.1) S.toSpecΓ =
      pullback.snd (projModelπ W.1) S.toSpecΓ := by
  simp only [vcMiddleIso, asIso_hom, vcMiddleMap]
  rw [pullback.lift_snd, Category.comp_id]

private theorem vcMiddleIso_zerolift (hC : C' • W = W') :
    pullback.lift (S.toSpecΓ ≫ projModelZero W.1) (𝟙 S)
        (by rw [Category.assoc, projModelZero_projModelπ]
            exact (Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (vcMiddleIso C' hC).hom =
    pullback.lift (S.toSpecΓ ≫ projModelZero W'.1) (𝟙 S)
        (by rw [Category.assoc, projModelZero_projModelπ]
            exact (Category.comp_id _).trans (Category.id_comp _).symm) := by
  apply pullback.hom_ext
  · simp only [vcMiddleIso, asIso_hom, vcMiddleMap]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      Category.assoc, zero_vcModelHom, pullback.lift_fst]
  · simp only [vcMiddleIso, asIso_hom, vcMiddleMap]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.comp_id]

/-- **(T-W6c-ii)** A coordinate change carrying `W` to `W'` induces an isomorphism of
the presented curves. -/
noncomputable def curveOfVCIso (hC : C' • W = W') : (curveOf W).E ≅ (curveOf W').E :=
  curveOfPasting W ≪≫ vcMiddleIso C' hC ≪≫ (curveOfPasting W').symm

/-- `curveOfVCIso` is a morphism over `S`. -/
theorem curveOfVCIso_π (hC : C' • W = W') :
    (curveOfVCIso C' hC).hom ≫ (curveOf W').π = (curveOf W).π := by
  have h3 : (curveOfPasting W').inv ≫ (curveOf W').π
      = pullback.snd (projModelπ W'.1) S.toSpecΓ := by
    rw [Iso.inv_comp_eq]
    exact (curveOfPasting_snd W').symm
  rw [curveOfVCIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Category.assoc, h3, vcMiddleIso_snd, curveOfPasting_snd]

/-- `curveOfVCIso` matches the zero sections. -/
theorem curveOfVCIso_zero (hC : C' • W = W') :
    (curveOf W).zero ≫ (curveOfVCIso C' hC).hom = (curveOf W').zero := by
  rw [curveOfVCIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    ← Category.assoc, curveOfPasting_zero, Iso.comp_inv_eq, curveOfPasting_zero]
  exact vcMiddleIso_zerolift C' hC

end VCTransport

end ModularCurves
