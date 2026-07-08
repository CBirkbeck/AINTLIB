/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

open AlgebraicGeometry CategoryTheory WeierstrassCurve

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

end ModularCurves
