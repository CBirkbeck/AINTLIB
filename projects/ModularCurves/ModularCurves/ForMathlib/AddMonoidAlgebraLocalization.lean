/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing additive monoid algebras

An additive localization map away from `x` induces a localization of additive monoid algebras
away from the monomial supported at `x`. This supplies the algebraic bridge from standard
projective intersections to Laurent monomials.
-/

namespace AddMonoidAlgebra

universe u v w

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [AddCommMonoid A] {B : Type w} [AddCommMonoid B]

private noncomputable def awayExponentHom (x : A) :
    A →+ Additive (Localization.Away
      (single x (1 : R) : AddMonoidAlgebra R A)) :=
  MonoidHom.toAdditiveRight
    ((algebraMap (AddMonoidAlgebra R A)
      (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A))).toMonoidHom.comp
      (of R A))

private lemma awayExponentHom_isAddUnit (x : A) :
    IsAddUnit (awayExponentHom (R := R) x x) := by
  rw [show awayExponentHom (R := R) x x = Additive.ofMul
    (algebraMap (AddMonoidAlgebra R A)
      (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A)) (single x 1)) by rfl]
  have hx := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (single x (1 : R) : AddMonoidAlgebra R A))
    (single x (1 : R) : AddMonoidAlgebra R A)
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  apply IsAddUnit.of_add_eq_zero (Additive.ofMul y)
  apply Additive.ext
  exact hy

private noncomputable def awayBack {x : A}
    (F : AddSubmonoid.LocalizationMap.AwayMap x B) :
    AddMonoidAlgebra R B →+*
      Localization.Away (single x (1 : R) : AddMonoidAlgebra R A) :=
  liftNCRingHom
    ((algebraMap (AddMonoidAlgebra R A)
      (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A))).comp
      singleZeroRingHom)
    ((F.lift x (awayExponentHom_isAddUnit (R := R) x)).toMultiplicativeLeft)
    fun _ _ => Commute.all _ _

private theorem awayBack_mapDomain {x : A}
    (F : AddSubmonoid.LocalizationMap.AwayMap x B) (p : AddMonoidAlgebra R A) :
    awayBack (R := R) F (mapDomain F.toAddMonoidHom p) =
      algebraMap (AddMonoidAlgebra R A)
        (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A)) p := by
  have h : (awayBack (R := R) F).comp (mapDomainRingHom R F.toAddMonoidHom) =
      algebraMap (AddMonoidAlgebra R A)
        (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A)) := by
    apply ringHom_ext
    · intro r
      simp [awayBack, awayExponentHom]
      have hF0 : F.toAddHom 0 = 0 := by
        change F.toAddMonoidHom 0 = 0
        exact F.toAddMonoidHom.map_zero
      rw [hF0, map_zero]
      rw [toMul_zero, mul_one]
    · intro a
      simp [awayBack, awayExponentHom]
      rw [show (single 0 (1 : R) : AddMonoidAlgebra R A) = 1 by rfl,
        map_one, one_mul]
      have hlift : F.lift x (awayExponentHom_isAddUnit (R := R) x)
          (F.toAddHom a) = awayExponentHom (R := R) x a := by
        change F.lift x (awayExponentHom_isAddUnit (R := R) x)
          (F.toAddMonoidHom a) = awayExponentHom (R := R) x a
        exact F.lift_eq x (awayExponentHom_isAddUnit (R := R) x) a
      simpa [awayExponentHom] using congrArg Additive.toMul hlift
  exact RingHom.congr_fun h p

/-- An additive monoid localization away from `x` induces a ring localization of additive
monoid algebras away from the monomial supported at `x`. -/
theorem isLocalizationAway_of_isLocalizationMap {x : A}
    (F : AddSubmonoid.LocalizationMap.AwayMap x B) :
    letI := (mapDomainRingHom R F.toAddMonoidHom).toAlgebra
    IsLocalization.Away (single x (1 : R) : AddMonoidAlgebra R A)
      (AddMonoidAlgebra R B) := by
  letI := (mapDomainRingHom R F.toAddMonoidHom).toAlgebra
  change IsLocalization (Submonoid.powers
    (single x (1 : R) : AddMonoidAlgebra R A)) (AddMonoidAlgebra R B)
  rw [isLocalization_iff]
  constructor
  · intro y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    have hx : IsUnit (algebraMap (AddMonoidAlgebra R A)
        (AddMonoidAlgebra R B) (single x 1)) := by
      obtain ⟨b, hb⟩ :=
        (F.map_addUnits (⟨x, AddSubmonoid.mem_multiples x⟩ :
          AddSubmonoid.multiples x)).exists_neg
      have hb' : F.toAddMonoidHom x + b = 0 := by
        simpa using hb
      rw [RingHom.algebraMap_toAlgebra]
      rw [show (mapDomainRingHom R F.toAddMonoidHom) (single x 1) =
        single (F.toAddMonoidHom x) 1 by exact mapDomain_single]
      apply IsUnit.of_mul_eq_one (single b 1)
      rw [single_mul_single, mul_one, hb']
      rfl
    rw [← hn, map_pow]
    exact hx.pow n
  constructor
  · intro z
    induction z using AddMonoidAlgebra.induction_linear with
    | zero =>
        exact ⟨⟨0, 1⟩, by simp⟩
    | add p q hp hq =>
        obtain ⟨⟨a, s⟩, ha⟩ := hp
        obtain ⟨⟨b, t⟩, hb⟩ := hq
        refine ⟨⟨a * (t : AddMonoidAlgebra R A) +
          b * (s : AddMonoidAlgebra R A), s * t⟩, ?_⟩
        calc
          (p + q) * (algebraMap (AddMonoidAlgebra R A)
              (AddMonoidAlgebra R B) (s * t : AddMonoidAlgebra R A)) =
              (p * algebraMap (AddMonoidAlgebra R A)
                (AddMonoidAlgebra R B) s) *
                algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) t +
              (q * algebraMap (AddMonoidAlgebra R A)
                (AddMonoidAlgebra R B) t) *
                algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) s := by
            simp only [map_mul]
            ring
          _ = algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) a *
                algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) t +
              algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) b *
                algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B) s := by
            rw [ha, hb]
          _ = algebraMap (AddMonoidAlgebra R A) (AddMonoidAlgebra R B)
              (a * (t : AddMonoidAlgebra R A) +
                b * (s : AddMonoidAlgebra R A)) := by
            simp only [map_add, map_mul]
    | single b r =>
        obtain ⟨⟨a, s⟩, hs⟩ := F.surj b
        obtain ⟨n, hn⟩ := s.2
        refine ⟨⟨single a r, ⟨(single x 1) ^ n, ?_⟩⟩, ?_⟩
        · exact ⟨n, rfl⟩
        · change single b r * mapDomain F.toAddMonoidHom ((single x 1) ^ n) =
            mapDomain F.toAddMonoidHom (single a r)
          simp only [single_pow, mapDomain_single, map_nsmul, one_pow,
            single_mul_single, mul_one]
          have hns : n • F.toAddMonoidHom x = F.toAddMonoidHom s :=
            (F.toAddMonoidHom.map_nsmul n x).symm.trans
              (congrArg F.toAddMonoidHom hn)
          have hs' : b + F.toAddMonoidHom s = F.toAddMonoidHom a := by
            simpa using hs
          rw [hns, hs']
  · intro a b hab
    rw [RingHom.algebraMap_toAlgebra] at hab
    change mapDomain F.toAddMonoidHom a = mapDomain F.toAddMonoidHom b at hab
    have hcanonical : algebraMap (AddMonoidAlgebra R A)
        (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A)) a =
      algebraMap (AddMonoidAlgebra R A)
        (Localization.Away (single x (1 : R) : AddMonoidAlgebra R A)) b := by
      rw [← awayBack_mapDomain (R := R) F a,
        ← awayBack_mapDomain (R := R) F b]
      exact congrArg (awayBack (R := R) F) hab
    exact IsLocalization.exists_of_eq (S := Localization.Away
      (single x (1 : R) : AddMonoidAlgebra R A)) hcanonical

end AddMonoidAlgebra
