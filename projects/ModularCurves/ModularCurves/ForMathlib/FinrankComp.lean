/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import ModularCurves.ForMathlib.FinrankTower
import ModularCurves.EllipticCurve.FinrankFractionField
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# Composition multiplicativity of `Scheme.Hom.finrank` over integral schemes

`Scheme.Hom.finrank` (the fibre rank of a finite flat morphism, mathlib
`AlgebraicGeometry/Morphisms/FlatRank.lean`) is multiplicative under composition of finite flat
surjective morphisms of **integral** schemes:

    (f ≫ g).finrank z = f.finrank y * g.finrank z.

Route: restrict to an affine chart `U ∋ z` of the target (`finrank_morphismRestrict` +
`morphismRestrict_comp`), where all three schemes are affine and integral because preimages of
nonempty opens under surjections are nonempty opens of integral schemes; there the rank of each
finite flat morphism is the global-sections module rank (`finrank_eq_module_finrank_of_isAffine`,
via KM's domain identity `finrank_SpecMap_algebraMap_eq_finrank`), and the module ranks multiply
in towers over domains (`finrank_tower_of_flat`). Since over a domain each rank is *constant*,
the `f`-factor can be read at the generic point, which lies in every chart; local constancy
(`isLocallyConstant_finrank` + irreducibility) then moves it to an arbitrary `y`.

Also provides the two transport helpers `finrank_comp_right_of_isIso` (invariance under
post-composition with an isomorphism) and `finrank_morphismRestrict` (compatibility with
restriction to a target open) — reproving on this branch the Y1-wave helpers of the same names.

This is the scheme engine of the `endDeg_comp` multiplicativity pin of the endomorphism-degree
keystone (`ModularCurves/EllipticCurve/EndomorphismDegree.lean`, KM 2.6.1).
-/

-- v4.33 bump: opens/hom coercions are no longer transparent enough for the
-- `≫`-associativity and `comp_apply` rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- The fibre rank is invariant under post-composition with an isomorphism:
`(h ≫ e).finrank (e y) = h.finrank y`. (`finrank_comp_left_of_isIso` is the mathlib
pre-composition version; this is its target-side companion, via the pullback square with
horizontal isomorphisms `𝟙` and `e`.) -/
theorem Scheme.Hom.finrank_comp_right_of_isIso (h : X ⟶ Y) (e : Y ⟶ Z) [IsIso e]
    [Flat h] [IsFinite h] (y : Y) :
    (h ≫ e).finrank (e.base y) = h.finrank y := by
  haveI : Flat (h ≫ e) := by
    rw [MorphismProperty.cancel_right_of_respectsIso @Flat]
    infer_instance
  haveI : IsFinite (h ≫ e) := by
    rw [MorphismProperty.cancel_right_of_respectsIso @IsFinite]
    infer_instance
  exact (Scheme.Hom.finrank_of_isPullback (𝟙 X) h (h ≫ e) e
    (IsPullback.of_horiz_isIso ⟨by simp⟩) y).symm

/-- The fibre rank is compatible with restriction to a target open:
`(f ∣_ U).finrank u = f.finrank u` (via `isPullback_morphismRestrict`). -/
theorem Scheme.Hom.finrank_morphismRestrict (f : X ⟶ Y) [Flat f] [IsFinite f]
    (U : Y.Opens) (u : U) :
    (f ∣_ U).finrank u = f.finrank u.1 :=
  Scheme.Hom.finrank_of_isPullback _ _ f U.ι (isPullback_morphismRestrict f U).flip u

/-- Over an affine **integral** target, the fibre rank of a finite flat morphism from an affine
scheme is the module rank of global sections (in particular constant): conjugate to
`Spec.map h.appTop` by `toSpecΓ`-naturality and apply the domain identity
`finrank_SpecMap_algebraMap_eq_finrank`. -/
theorem Scheme.Hom.finrank_eq_module_finrank_of_isAffine [IsAffine X] [IsAffine Y] [IsIntegral Y]
    (h : X ⟶ Y) [Flat h] [IsFinite h] (y : Y) :
    h.finrank y =
      letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
      Module.finrank Γ(Y, ⊤) Γ(X, ⊤) := by
  have hfin : h.appTop.hom.Finite := h.finite_appTop
  have hflat : h.appTop.hom.Flat := h.flat_appTop
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := hfin
  haveI : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := hflat
  -- conjugate `h` to `Spec.map h.appTop`
  have hnat : h ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map h.appTop := Scheme.toSpecΓ_naturality h
  have hconj : h = X.toSpecΓ ≫ Spec.map h.appTop ≫ inv Y.toSpecΓ := by
    rw [← Category.assoc, ← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hpt : y = (inv Y.toSpecΓ).base (Y.toSpecΓ.base y) := by
    show y = (Y.toSpecΓ ≫ inv Y.toSpecΓ).base y
    rw [IsIso.hom_inv_id]
    rfl
  haveI : Flat (Spec.map h.appTop ≫ inv Y.toSpecΓ) := by
    rw [MorphismProperty.cancel_right_of_respectsIso @Flat, Flat.SpecMap_iff]
    exact hflat
  haveI : IsFinite (Spec.map h.appTop ≫ inv Y.toSpecΓ) := by
    rw [MorphismProperty.cancel_right_of_respectsIso @IsFinite, IsFinite.SpecMap_iff]
    exact hfin
  haveI : Flat (Spec.map h.appTop) := by rw [Flat.SpecMap_iff]; exact hflat
  haveI : IsFinite (Spec.map h.appTop) := by rw [IsFinite.SpecMap_iff]; exact hfin
  calc h.finrank y
      = (X.toSpecΓ ≫ Spec.map h.appTop ≫ inv Y.toSpecΓ).finrank y := by rw [← hconj]
    _ = (Spec.map h.appTop ≫ inv Y.toSpecΓ).finrank y := by
        rw [Scheme.Hom.finrank_comp_left_of_isIso]
    _ = (Spec.map h.appTop ≫ inv Y.toSpecΓ).finrank ((inv Y.toSpecΓ).base (Y.toSpecΓ.base y)) := by
        rw [← hpt]
    _ = (Spec.map h.appTop).finrank (Y.toSpecΓ.base y) :=
        Scheme.Hom.finrank_comp_right_of_isIso (Spec.map h.appTop) (inv Y.toSpecΓ) _
    _ = Module.finrank Γ(Y, ⊤) Γ(X, ⊤) := by
        have hmap : Spec.map h.appTop
            = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤))) := by
          rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
        rw [hmap]
        exact ModularCurves.finrank_SpecMap_algebraMap_eq_finrank Γ(Y, ⊤) Γ(X, ⊤) _

/-- **Composition multiplicativity of the fibre rank, affine integral case**:
`(f ≫ g).finrank z = f.finrank y * g.finrank z` for finite flat morphisms of affine integral
schemes (at *every* pair of points — over domains the ranks are constant). The module ranks of
the global-sections tower multiply by `finrank_tower_of_flat`. -/
theorem Scheme.Hom.finrank_comp_of_isAffine [IsAffine X] [IsAffine Y] [IsAffine Z]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [IsFinite f] [Flat g] [IsFinite g]
    (y : Y) (z : Z) :
    (f ≫ g).finrank z = f.finrank y * g.finrank z := by
  haveI : Flat (f ≫ g) := MorphismProperty.comp_mem _ f g ‹_› ‹_›
  haveI : IsFinite (f ≫ g) := MorphismProperty.comp_mem _ f g ‹_› ‹_›
  have h1 := Scheme.Hom.finrank_eq_module_finrank_of_isAffine f y
  have h2 := Scheme.Hom.finrank_eq_module_finrank_of_isAffine g z
  have h3 := Scheme.Hom.finrank_eq_module_finrank_of_isAffine (f ≫ g) z
  rw [h1, h2, h3]
  -- align the composite algebra with the tower composite
  have hcomp : (f ≫ g).appTop.hom = f.appTop.hom.comp g.appTop.hom := rfl
  rw [hcomp]
  -- the three algebra structures and the tower
  letI aZY : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI aYX : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI aZX : Algebra Γ(Z, ⊤) Γ(X, ⊤) := (f.appTop.hom.comp g.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite Γ(Z, ⊤) Γ(Y, ⊤) := g.finite_appTop
  haveI : Module.Flat Γ(Z, ⊤) Γ(Y, ⊤) := g.flat_appTop
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  haveI : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := f.flat_appTop
  rw [mul_comm]
  exact ModularCurves.finrank_tower_of_flat Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤)

/-- The fibre rank of a finite flat locally finitely presented morphism into an **irreducible**
base is a constant function (locally constant + preconnected). -/
theorem Scheme.Hom.finrank_eq_finrank (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f] [IrreducibleSpace Y] (y y' : Y) :
    f.finrank y = f.finrank y' :=
  f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y'

/-- **Composition multiplicativity of `Scheme.Hom.finrank` (integral schemes)**:
for finite flat surjective morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` of integral schemes with `f`
locally of finite presentation,

    (f ≫ g).finrank z = f.finrank y * g.finrank z

at every `y : Y`, `z : Z` — "the degree of a composite of isogeny-like coverings is the product
of the degrees". Reduce to an affine chart at `z` (all preimages are nonempty by surjectivity,
affine because finite morphisms are affine, and integral as opens of integral schemes), apply the
affine case with the `f`-factor read at the generic point (which lies in every chart), and move
it to `y` by constancy. -/
theorem Scheme.Hom.finrank_comp [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [IsFinite f] [Flat g] [IsFinite g]
    [Surjective f] [Surjective g] [LocallyOfFinitePresentation f]
    (y : Y) (z : Z) :
    (f ≫ g).finrank z = f.finrank y * g.finrank z := by
  haveI : Flat (f ≫ g) := MorphismProperty.comp_mem _ f g ‹_› ‹_›
  haveI : IsFinite (f ≫ g) := MorphismProperty.comp_mem _ f g ‹_› ‹_›
  -- an affine chart at `z`
  obtain ⟨_, ⟨U₀, hUaff, rfl⟩, hzU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  set U : Z.Opens := U₀ with hUdef
  -- preimages: nonempty affine integral opens
  set V : Y.Opens := g ⁻¹ᵁ U with hV
  set W : X.Opens := f ⁻¹ᵁ V with hW
  haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨y₀, hy₀⟩ := g.surjective z
  have hy₀V : y₀ ∈ V := by
    show g.base y₀ ∈ U
    rw [hy₀]
    exact hzU
  obtain ⟨x₀, hx₀⟩ := f.surjective y₀
  have hx₀W : x₀ ∈ W := by
    show f.base x₀ ∈ V
    rwa [hx₀]
  haveI : Nonempty V := ⟨⟨y₀, hy₀V⟩⟩
  haveI : Nonempty W := ⟨⟨x₀, hx₀W⟩⟩
  have hUaff' : IsAffineOpen U := hUaff
  have hVaff : IsAffineOpen V := hUaff'.preimage g
  have hWaff : IsAffineOpen W := hVaff.preimage f
  haveI : IsAffine U.toScheme := hUaff'
  haveI : IsAffine V.toScheme := hVaff
  haveI : IsAffine W.toScheme := hWaff
  -- restricted morphisms are finite and flat
  haveI : Flat (g ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Flat g› U
  haveI : IsFinite (g ∣_ U) := IsZariskiLocalAtTarget.restrict ‹IsFinite g› U
  haveI : Flat (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Flat f› V
  haveI : IsFinite (f ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsFinite f› V
  -- the generic point lies in the chart `V`
  have hgen : genericPoint Y ∈ V := by
    have hne : (V : Set Y).Nonempty := ⟨y₀, hy₀V⟩
    exact (genericPoint_spec Y).mem_open_set_iff V.2 |>.mpr (by simpa using hne)
  -- assemble
  calc (f ≫ g).finrank z
      = ((f ≫ g) ∣_ U).finrank ⟨z, hzU⟩ :=
        (Scheme.Hom.finrank_morphismRestrict (f ≫ g) U ⟨z, hzU⟩).symm
    _ = ((f ∣_ V) ≫ (g ∣_ U)).finrank ⟨z, hzU⟩ := by
        rw [morphismRestrict_comp]
    _ = (f ∣_ V).finrank ⟨genericPoint Y, hgen⟩ * (g ∣_ U).finrank ⟨z, hzU⟩ :=
        Scheme.Hom.finrank_comp_of_isAffine (f ∣_ V) (g ∣_ U) _ _
    _ = f.finrank (genericPoint Y) * g.finrank z := by
        rw [Scheme.Hom.finrank_morphismRestrict f V ⟨genericPoint Y, hgen⟩,
          Scheme.Hom.finrank_morphismRestrict g U ⟨z, hzU⟩]
    _ = f.finrank y * g.finrank z := by
        rw [Scheme.Hom.finrank_eq_finrank f (genericPoint Y) y]

end AlgebraicGeometry
