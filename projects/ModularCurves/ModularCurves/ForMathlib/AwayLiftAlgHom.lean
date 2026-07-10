import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The algebra-hom lift of an `Away` localization (ForMathlib)

`IsLocalization.Away.liftAlgHom`: an `R`-algebra map `g : A →ₐ[R] P` sending `a` to a unit lifts to
an `R`-algebra map `Localization.Away a →ₐ[R] P`. Mathlib has the ring-hom lift
(`IsLocalization.Away.lift`) and the algebra-map `awayMapₐ` between two `Away` localizations, but not
this direct algebra lift of an arbitrary target algebra. The R-linearity is a general fact; stated
here at variable rings so instantiation at concrete rings never forces a `whnf` blow-up.

Upstream candidate.
-/

namespace IsLocalization.Away

/-- An `R`-algebra map `g : A →ₐ[R] P` sending `a` to a unit lifts to an `R`-algebra map
`Localization.Away a →ₐ[R] P`. -/
noncomputable def liftAlgHom {R A P : Type*} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (g : A →ₐ[R] P) (a : A) (hg : IsUnit (g a)) :
    Localization.Away a →ₐ[R] P :=
  AlgHom.mk' (IsLocalization.Away.lift a (g := g.toRingHom) hg) (fun c x => by
    have key : ∀ y : A, IsLocalization.Away.lift a (g := g.toRingHom) hg
        (algebraMap A (Localization.Away a) y) = g y := IsLocalization.Away.lift_eq a hg
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]; congr 1
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away a), key]; exact g.commutes c)

@[simp]
lemma liftAlgHom_algebraMap {R A P : Type*} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (g : A →ₐ[R] P) (a : A) (hg : IsUnit (g a)) (x : A) :
    liftAlgHom g a hg (algebraMap A (Localization.Away a) x) = g x :=
  IsLocalization.Away.lift_eq a hg x

end IsLocalization.Away
