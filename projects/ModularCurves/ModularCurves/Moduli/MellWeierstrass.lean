/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularCurves.EllipticCurve.GroupLawAxioms
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
* `ellipticWOfRingHom` / `ringHomOfEllipticW`: the atlas dictionary, with its round-trip
  lemmas, bundled as the equivalence `atlasDictionary`.

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
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

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

set_option backward.isDefEq.respectTransparency false in
private theorem mapFunctor_id :
    mapFunctor (RingHom.id B) = 𝟭 (MellWGroupoid B) := by
  refine CategoryTheory.Functor.ext (fun W => congrArg mk (ellipticW.map_id W.pt)) ?_
  intro W W' g
  apply Subtype.ext
  simp [VariableChange.map_id]

set_option backward.isDefEq.respectTransparency false in
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
  map_id _ := congrArg Functor.toCatHom MellWGroupoid.mapFunctor_id
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
  smooth := (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback universalCurveπ (classify W)) universalCurve_smooth
  proper := inferInstance
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
    universalWeierstrassLoc.map (ringHomOfEllipticW W) = W.1 :=
  congrArg Subtype.val (ellipticWOfRingHom_ringHomOfEllipticW W)

/-- The middle base-change square: `W`'s own projective model is the fibre of the universal
curve over `Spec Γ(S,⊤)`. This is `isPullback_projModelBaseChangeOf` — the `eqToHom`-free
base-change API — at the classifying ring hom. -/
private theorem isPullback_curveOfMiddle :
    IsPullback
      (projModelBaseChangeOf (ringHomOfEllipticW W) universalWeierstrassLoc W.1
        (uWL_map_ringHomOf W))
      (projModelπ W.1) universalCurveπ
      (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) :=
  isPullback_projModelBaseChangeOf _ _ _ _

/-- The middle-fibre identification: the fibre of the universal curve over
`Spec Γ(S,⊤)` is `W`'s own projective model. -/
private noncomputable def curveOfMiddle :
    pullback universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)))
      ≅ projModel W.1 :=
  (isPullback_curveOfMiddle W).isoPullback.symm

/-- The other leg of the middle square: `curveOfMiddle` intertwines the pullback projection to
the universal curve with the base-change map of projective models. -/
private theorem curveOfMiddle_baseChange :
    (curveOfMiddle W).hom ≫
        projModelBaseChangeOf (ringHomOfEllipticW W) universalWeierstrassLoc W.1
          (uWL_map_ringHomOf W) =
      pullback.fst universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) :=
  (isPullback_curveOfMiddle W).isoPullback_inv_fst

private theorem curveOfMiddle_π :
    (curveOfMiddle W).hom ≫ projModelπ W.1 =
      pullback.snd universalCurveπ (Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W))) :=
  (isPullback_curveOfMiddle W).isoPullback_inv_snd

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

set_option backward.isDefEq.respectTransparency false in
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

/-- The commutation making `S.toSpecΓ ≫ projModelZero V.1` a section of `projModel V.1` over
`S`: the zero-section lift used on both sides of the pasting and coordinate-change squares. -/
private theorem zerolift_comm (V : ellipticW ↑Γ(S, ⊤)) :
    (S.toSpecΓ ≫ projModelZero V.1) ≫ projModelπ V.1 = 𝟙 S ≫ S.toSpecΓ := by
  rw [Category.assoc, projModelZero_projModelπ]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem zliftComm :
    (classify W ≫ universalCurveZero) ≫ universalCurveπ =
      S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ringHomOfEllipticW W)) := by
  rw [Category.assoc, universalCurveZero_π, Category.comp_id]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The middle-fibre identification matches zero sections: the universal zero section,
pulled back to `S`'s fibre, is `W`'s own `projModelZero`. -/
private theorem curveOfMiddle_zero :
    pullback.lift (classify W ≫ universalCurveZero) S.toSpecΓ (zliftComm W) ≫
        (curveOfMiddle W).hom = S.toSpecΓ ≫ projModelZero W.1 := by
  simp only [curveOfMiddle, Iso.symm_hom, Iso.comp_inv_eq]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    erw [(isPullback_curveOfMiddle W).isoPullback_hom_fst]
    rw [Category.assoc]
    exact ((congrArg (fun m => S.toSpecΓ ≫ m)
      (projModelZero_baseChangeOf (ringHomOfEllipticW W) universalWeierstrassLoc W.1
        (uWL_map_ringHomOf W))).trans (Category.assoc _ _ _).symm).symm
  · rw [pullback.lift_snd, Category.assoc]
    erw [(isPullback_curveOfMiddle W).isoPullback_hom_snd]
    rw [Category.assoc, projModelZero_projModelπ]
    exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pasting identification matches the zero sections.

ROUTE (decomposed per v10.24(a), board v10.40): `pullback.hom_ext`; the `snd`-leg is
`curveOfPasting_snd` + `zero_π`; the `fst`-leg needs (i) `pullbackLeftPullbackSndIso_inv_fst`
+ `_inv_fst_snd` to compute `zero ≫ pasting.inv ≫ fst` as the evident lift, and (ii) a
`curveOfMiddle_zero` compat (`lift ≫ (curveOfMiddle W).hom = S.toSpecΓ ≫ projModelZero W.1`)
via `IsPullback.isoPullback`-projections + `projModelZero_baseChange` — the exact analogue
of the atlas file's T-W5a case-c2 battle, one seam-lemma per step. -/
theorem curveOfPasting_zero :
    (curveOf W).zero ≫ (curveOfPasting W).hom =
      pullback.lift (S.toSpecΓ ≫ projModelZero W.1) (𝟙 S) (zerolift_comm W) := by
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
    pullback.lift (S.toSpecΓ ≫ projModelZero W.1) (𝟙 S) (zerolift_comm W) ≫
      (vcMiddleIso C' hC).hom =
    pullback.lift (S.toSpecΓ ≫ projModelZero W'.1) (𝟙 S) (zerolift_comm W') := by
  apply pullback.hom_ext
  · simp only [vcMiddleIso, asIso_hom, vcMiddleMap]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      Category.assoc, zero_vcModelHom, pullback.lift_fst]
  · simp only [vcMiddleIso, asIso_hom, vcMiddleMap]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.comp_id]

private theorem vcIso_inv_transport {V V' : WeierstrassCurve ↑Γ(S, ⊤)} (e : V = V')
    (C'' : VariableChange ↑Γ(S, ⊤)) {Z : Scheme} (k : projModel (C'' • V') ⟶ Z) :
    eqToHom (congrArg (projModel ·) e) ≫ (projModelVCIso C'' V').inv ≫ k
      = (projModelVCIso C'' V).inv ≫
          eqToHom (congrArg (projModel ·) (congrArg (C'' • ·) e)) ≫ k := by
  subst e; simp

private theorem vcIso_congrC {D D' : VariableChange ↑Γ(S, ⊤)} (h : D = D')
    (V : WeierstrassCurve ↑Γ(S, ⊤)) :
    (projModelVCIso D V).hom =
      eqToHom (congrArg (fun c => projModel (c • V)) h) ≫ (projModelVCIso D' V).hom := by
  subst h; simp

private theorem vcIso_congrW (D : VariableChange ↑Γ(S, ⊤))
    {V V' : WeierstrassCurve ↑Γ(S, ⊤)} (h : V = V') :
    (projModelVCIso D V).hom =
      eqToHom (congrArg (fun w => projModel (D • w)) h) ≫ (projModelVCIso D V').hom ≫
        eqToHom (congrArg projModel h.symm) := by
  subst h; simp

/-- The coordinate-change model iso at the identity is the identity transport — proven
from the PUBLIC cocycle `projModelVCIso_mul` alone (instantiate at `1, 1`, right-cancel
the iso), per the v10.59 dispatch; no private transport machinery consumed. -/
private theorem projModelVCIso_one_hom (V : WeierstrassCurve ↑Γ(S, ⊤)) :
    (projModelVCIso (1 : VariableChange ↑Γ(S, ⊤)) V).hom =
      eqToHom (congrArg projModel (one_smul (VariableChange ↑Γ(S, ⊤)) V)) :=
  projModelVCIso_one V

private theorem vcModelHom_mul {W W' W'' : ellipticW ↑Γ(S, ⊤)}
    (Cf Cg : VariableChange ↑Γ(S, ⊤)) (hf : Cf • W = W') (hg : Cg • W' = W'')
    (h : (Cg * Cf) • W = W'') :
    vcModelHom (Cg * Cf) h = vcModelHom Cf hf ≫ vcModelHom Cg hg := by
  have hinv : (projModelVCIso (Cg * Cf) W.1).inv =
      (projModelVCIso Cf W.1).inv ≫ (projModelVCIso Cg (Cf • W.1)).inv ≫
        eqToHom (congrArg (projModel ·) (mul_smul Cg Cf W.1).symm) := by
    apply Iso.inv_ext
    rw [projModelVCIso_mul, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id_assoc, eqToHom_trans, eqToHom_refl]
  rw [vcModelHom, vcModelHom, vcModelHom, hinv]
  simp only [Category.assoc]
  rw [eqToHom_trans, vcIso_inv_transport (congrArg Subtype.val hf) Cg, eqToHom_trans]
  rfl

private theorem vcMiddleMap_mul {W W' W'' : ellipticW ↑Γ(S, ⊤)}
    (Cf Cg : VariableChange ↑Γ(S, ⊤)) (hf : Cf • W = W') (hg : Cg • W' = W'')
    (h : (Cg * Cf) • W = W'') :
    vcMiddleMap (Cg * Cf) h = vcMiddleMap Cf hf ≫ vcMiddleMap Cg hg := by
  apply pullback.hom_ext
  · simp only [vcMiddleMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [vcModelHom_mul Cf Cg hf hg h]
  · simp only [vcMiddleMap, Category.assoc, pullback.lift_snd, Category.comp_id]

private theorem vcModelHom_one {W : ellipticW ↑Γ(S, ⊤)}
    (hC : (1 : VariableChange ↑Γ(S, ⊤)) • W = W) :
    vcModelHom 1 hC = 𝟙 (projModel W.1) := by
  rw [vcModelHom]
  have hinv : (projModelVCIso (1 : VariableChange ↑Γ(S, ⊤)) W.1).inv =
      eqToHom (congrArg projModel (one_smul (VariableChange ↑Γ(S, ⊤)) W.1)).symm :=
    Iso.inv_ext (by rw [projModelVCIso_one_hom, eqToHom_trans, eqToHom_refl])
  rw [hinv, eqToHom_trans, eqToHom_refl]

private theorem vcMiddleMap_one {W : ellipticW ↑Γ(S, ⊤)}
    (hC : (1 : VariableChange ↑Γ(S, ⊤)) • W = W) :
    vcMiddleMap 1 hC = 𝟙 (pullback (projModelπ W.1) S.toSpecΓ) := by
  apply pullback.hom_ext
  · simp only [vcMiddleMap, pullback.lift_fst, Category.id_comp]
    rw [vcModelHom_one]
    simp
  · simp only [vcMiddleMap, pullback.lift_snd, Category.id_comp, Category.comp_id]

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

section PresentedCurves

variable (S : Scheme.{0})

/-- A **Weierstrass-presented elliptic curve** over `S`: an elliptic curve in the
definition-of-record sense (T-A8) together with a global Weierstrass presentation —
an atlas point and a pointed identification with the curve it presents. -/
structure PresentedCurve where
  /-- The underlying elliptic curve over `S`. -/
  curve : EllipticCurveGeom S
  /-- The presenting atlas point. -/
  W : ellipticW ↑Γ(S, ⊤)
  /-- The identification with the presented curve. -/
  pres : curve.E ≅ (curveOf W).E
  pres_π : pres.hom ≫ (curveOf W).π = curve.π
  pres_zero : curve.zero ≫ pres.hom = (curveOf W).zero

variable {S}

instance : Category (PresentedCurve S) where
  Hom E₁ E₂ := {f : E₁.curve.E ⟶ E₂.curve.E //
    f ≫ E₂.curve.π = E₁.curve.π ∧ E₁.curve.zero ≫ f = E₂.curve.zero}
  id E := ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
  comp f g := ⟨f.1 ≫ g.1,
    by rw [Category.assoc, g.2.1, f.2.1],
    by rw [← Category.assoc, f.2.2, g.2.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

/-- **(T-W6c-iii) The presentation functor**: the `[U/G]`-groupoid maps to
Weierstrass-presented elliptic curves — objects present themselves via `curveOf`,
morphisms act by `curveOfVCIso`. The functor laws come from `vcMiddleMap_one`
(itself the public `projModelVCIso_one`) and `vcMiddleMap_mul` (the `_mul` cocycle). -/
noncomputable def presentationFunctor :
    MellWGroupoid ↑Γ(S, ⊤) ⥤ PresentedCurve S where
  obj W := ⟨curveOf W.pt, W.pt, Iso.refl _, Category.id_comp _, Category.comp_id _⟩
  map {W W'} g := ⟨(curveOfVCIso g.1 g.2).hom, curveOfVCIso_π g.1 g.2,
    curveOfVCIso_zero g.1 g.2⟩
  map_id W := by
    apply Subtype.ext
    show (curveOfVCIso (1 : VariableChange ↑Γ(S, ⊤)) (one_smul _ W.pt)).hom =
      𝟙 (curveOf W.pt).E
    simp only [curveOfVCIso, Iso.trans_hom, Iso.symm_hom, vcMiddleIso, asIso_hom]
    rw [vcMiddleMap_one]
    simp
  map_comp f g := by
    apply Subtype.ext
    show (curveOfVCIso (g.1 * f.1) (by rw [mul_smul, f.2, g.2])).hom =
      (curveOfVCIso f.1 f.2).hom ≫ (curveOfVCIso g.1 g.2).hom
    simp only [curveOfVCIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, vcMiddleIso,
      asIso_hom, Iso.inv_hom_id_assoc]
    rw [vcMiddleMap_mul f.1 g.1 f.2 g.2]
    simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-W6c-iii, essential surjectivity — the "almost definitional" half of the v8
equivalence)**: every Weierstrass-presented curve is isomorphic, in the groupoid of
presented curves, to the self-presentation of its own atlas point. -/
theorem presentationFunctor_essSurj (E : PresentedCurve S) :
    Nonempty ((presentationFunctor.obj (MellWGroupoid.mk E.W)) ≅ E) := by
  refine ⟨⟨⟨E.pres.inv, ?_, ?_⟩, ⟨E.pres.hom, E.pres_π, E.pres_zero⟩, ?_, ?_⟩⟩
  · rw [Iso.inv_comp_eq]
    exact E.pres_π.symm
  · show (curveOf E.W).zero ≫ E.pres.inv = E.curve.zero
    rw [Iso.comp_inv_eq]
    exact E.pres_zero.symm
  · exact Subtype.ext E.pres.inv_hom_id
  · exact Subtype.ext E.pres.hom_inv_id

end PresentedCurves

end ModularCurves
