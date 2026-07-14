/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.EndomorphismDegree

/-!
# Pointed endomorphisms restrict to torsion ([RIG-1a], step 1)

A pointed endomorphism `ε` of `E/S` commutes with `[n]` (both post- and pre-composition
are the `n`-th power of `ε` in the pointwise hom-group, by `endMonHom` and
`GrpObj.comp_zpow`), fixes the zero section, and therefore restricts along the kernel
`E[M] = ker [M]`: `torsionRestrict ε hη M : E[M] ⟶ E[M]` with
`torsionRestrict ≫ torsionι = torsionι ≫ ε.left`.

This is the restriction half of the [RIG-1] detection route: the fibrewise-trivial
automorphism is compared with the identity on the finite étale `E[M]` (where the
`UnramifiedEqualizer` engine applies), and `aut_endo_eq_one` then closes.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- A pointed endomorphism fixes the zero section at the scheme level. -/
theorem zero_comp_left (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) : E.zero ≫ ε.left = E.zero := by
  have h : (η[E.asOver]).left ≫ ε.left = (η[E.asOver]).left :=
    congrArg CommaMorphism.left hη
  rw [E.one_eq_zero] at h
  have h2 : (𝟙 S ≫ E.zero) ≫ ε.left = 𝟙 S ≫ E.zero := h
  rwa [Category.id_comp] at h2

/-- A pointed endomorphism commutes with `[n]`, at the `Over S` level: both composites
are `ε ^ n` in the pointwise hom-group (post-composition through the monoid
homomorphism `endMonHom`, pre-composition through `GrpObj.comp_zpow`). -/
theorem mulBy_comp_comm [IsLocallyNoetherian S] (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) (n : ℤ) :
    E.mulBy n ≫ ε = ε ≫ E.mulBy n := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom ε := { one_hom := hη, mul_hom := E.endMonHom ε hη }
  have hpost : E.mulBy n ≫ ε = ((𝟙 E.asOver) ≫ ε) ^ n := by
    have hmap := (IsMonHom.monoidHom ε E.asOver).map_zpow (𝟙 E.asOver) n
    simp only [IsMonHom.monoidHom_apply] at hmap
    exact hmap
  have hpre : ε ≫ E.mulBy n = (ε ≫ 𝟙 E.asOver) ^ n := GrpObj.comp_zpow ε (𝟙 E.asOver) n
  rw [hpost, hpre, Category.id_comp, Category.comp_id]

/-- A pointed endomorphism commutes with `[n]`, at the scheme level. -/
theorem mulByHom_comp_comm [IsLocallyNoetherian S] (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) (n : ℤ) :
    E.mulByHom n ≫ ε.left = ε.left ≫ E.mulByHom n :=
  congrArg CommaMorphism.left (E.mulBy_comp_comm ε hη n)

/-- **([RIG-1a] restriction)** A pointed endomorphism of `E/S` restricts to the
`M`-torsion kernel `E[M]`. -/
noncomputable def torsionRestrict [IsLocallyNoetherian S] (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) (M : ℕ) : E.torsion M ⟶ E.torsion M :=
  pullback.lift (E.torsionι M ≫ ε.left) (E.torsionπ M) (by
    have s1 : (E.torsionι M ≫ ε.left) ≫ E.mulByHom (M : ℕ)
        = E.torsionι M ≫ ε.left ≫ E.mulByHom (M : ℕ) := Category.assoc _ _ _
    have s2 : E.torsionι M ≫ ε.left ≫ E.mulByHom (M : ℕ)
        = E.torsionι M ≫ E.mulByHom (M : ℕ) ≫ ε.left :=
      congrArg (fun t => E.torsionι M ≫ t) (E.mulByHom_comp_comm ε hη (M : ℕ)).symm
    have s3 : E.torsionι M ≫ E.mulByHom (M : ℕ) ≫ ε.left
        = (E.torsionι M ≫ E.mulByHom (M : ℕ)) ≫ ε.left := (Category.assoc _ _ _).symm
    have s4 : (E.torsionι M ≫ E.mulByHom (M : ℕ)) ≫ ε.left
        = (E.torsionπ M ≫ E.zero) ≫ ε.left :=
      congrArg (fun t => t ≫ ε.left) pullback.condition
    have s5 : (E.torsionπ M ≫ E.zero) ≫ ε.left
        = E.torsionπ M ≫ E.zero ≫ ε.left := Category.assoc _ _ _
    have s6 : E.torsionπ M ≫ E.zero ≫ ε.left = E.torsionπ M ≫ E.zero :=
      congrArg (fun t => E.torsionπ M ≫ t) (E.zero_comp_left ε hη)
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6)))))

/-- The defining square of `torsionRestrict`: it lifts `ε` along `torsionι`. -/
@[reassoc]
theorem torsionRestrict_ι [IsLocallyNoetherian S] (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) (M : ℕ) :
    E.torsionRestrict ε hη M ≫ E.torsionι M = E.torsionι M ≫ ε.left :=
  pullback.lift_fst _ _ _

/-- `torsionRestrict` lies over the base. -/
@[reassoc (attr := simp)]
theorem torsionRestrict_π [IsLocallyNoetherian S] (ε : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ ε = η[E.asOver]) (M : ℕ) :
    E.torsionRestrict ε hη M ≫ E.torsionπ M = E.torsionπ M :=
  pullback.lift_snd _ _ _

/-- If the restriction of `ε` to `E[M]` is the identity, `ε` fixes the `M`-torsion in
the `aut_endo_eq_one` input form. -/
theorem torsionι_comp_left_eq_of_torsionRestrict_eq_id [IsLocallyNoetherian S]
    (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver]) (M : ℕ)
    (h : E.torsionRestrict ε hη M = 𝟙 (E.torsion M)) :
    E.torsionι M ≫ ε.left = E.torsionι M := by
  rw [← E.torsionRestrict_ι ε hη M, h, Category.id_comp]

end EllipticCurve

end ModularCurves
