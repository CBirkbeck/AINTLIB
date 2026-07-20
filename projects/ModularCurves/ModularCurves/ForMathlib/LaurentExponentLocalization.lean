/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.AddMonoidAlgebraLocalization
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-!
# Localizing natural exponent vectors

Localizing natural exponent vectors away from `m` gives the additive monoid of integer exponent
vectors whose negative coordinates occur only in the support of `m`. This is the exponent normal
form for Laurent monomials on standard projective intersections.
-/

namespace MvPolynomial

universe u

variable {σ : Type u}

/-- Integer exponent vectors whose negative coordinates occur only where `m` is supported. -/
def laurentExponentSubmonoid (m : σ →₀ ℕ) : AddSubmonoid (σ →₀ ℤ) where
  carrier := {e | ∀ i, e i < 0 → m i ≠ 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb i hi
    rw [Finsupp.add_apply] at hi
    intro hmi
    exact (not_lt_of_ge (add_nonneg (le_of_not_gt fun h => ha i h hmi)
      (le_of_not_gt fun h => hb i h hmi))) hi

private noncomputable def natToLaurentExponent (m : σ →₀ ℕ) :
    (σ →₀ ℕ) →+ laurentExponentSubmonoid m :=
  (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)).codRestrict
    (laurentExponentSubmonoid m) fun a i hi =>
      False.elim ((not_lt_of_ge (Int.natCast_nonneg (a i))) hi)

@[simp]
private lemma natToLaurentExponent_apply (m a : σ →₀ ℕ) (i : σ) :
    ((natToLaurentExponent m a : laurentExponentSubmonoid m) : σ →₀ ℤ) i = (a i : ℤ) := by
  rfl

private noncomputable def negLaurentExponent (m : σ →₀ ℕ) : laurentExponentSubmonoid m :=
  ⟨-(Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ) m), by
    intro i hi
    simp only [Finsupp.neg_apply, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_apply, Nat.coe_castAddMonoidHom] at hi
    exact Nat.ne_of_gt (by exact_mod_cast (neg_lt_zero.mp hi))⟩

private lemma natToLaurentExponent_isAddUnit (m : σ →₀ ℕ) :
    IsAddUnit (natToLaurentExponent m m) := by
  apply IsAddUnit.of_add_eq_zero (negLaurentExponent m)
  apply Subtype.ext
  ext i
  simp [negLaurentExponent]

private lemma laurentExponent_clear_denominators (m : σ →₀ ℕ)
    (z : laurentExponentSubmonoid m) :
    let n := z.1.support.sum fun i => Int.natAbs (z.1 i)
    ∀ i, 0 ≤ z.1 i + (n : ℤ) * (m i : ℤ) := by
  dsimp
  intro i
  by_cases hi : z.1 i < 0
  · have him : m i ≠ 0 := z.2 i hi
    have hisupp : i ∈ z.1.support := Finsupp.mem_support_iff.mpr (ne_of_lt hi)
    have habs : Int.natAbs (z.1 i) ≤ z.1.support.sum fun j => Int.natAbs (z.1 j) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (Int.natAbs (z.1 j))) hisupp
    have hm : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr him
    have hmul : z.1.support.sum (fun j => Int.natAbs (z.1 j)) ≤
        z.1.support.sum (fun j => Int.natAbs (z.1 j)) * m i := by
      simpa using Nat.mul_le_mul_left (z.1.support.sum fun j => Int.natAbs (z.1 j)) hm
    have hbound : Int.natAbs (z.1 i) ≤
        z.1.support.sum (fun j => Int.natAbs (z.1 j)) * m i := habs.trans hmul
    have hbound' : (Int.natAbs (z.1 i) : ℤ) ≤
        (z.1.support.sum (fun j => Int.natAbs (z.1 j)) : ℤ) * (m i : ℤ) := by
      exact_mod_cast hbound
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hi)] at hbound'
    omega
  · exact add_nonneg (le_of_not_gt hi)
      (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))

private noncomputable def laurentExponentNumerator (m : σ →₀ ℕ)
    (z : laurentExponentSubmonoid m) : σ →₀ ℕ :=
  let n := z.1.support.sum fun i => Int.natAbs (z.1 i)
  (z.1 + n • Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ) m).mapRange
    Int.toNat Int.toNat_zero

private lemma natToLaurentExponent_surj (m : σ →₀ ℕ)
    (z : laurentExponentSubmonoid m) :
    ∃ x : (σ →₀ ℕ) × AddSubmonoid.multiples m,
      z + natToLaurentExponent m x.2 = natToLaurentExponent m x.1 := by
  let n := z.1.support.sum fun i => Int.natAbs (z.1 i)
  refine ⟨⟨laurentExponentNumerator m z, ⟨n • m, ⟨n, rfl⟩⟩⟩, ?_⟩
  apply Subtype.ext
  ext i
  have hi := laurentExponent_clear_denominators m z i
  change z.1 i + ((n • m) i : ℕ) = (laurentExponentNumerator m z i : ℕ)
  simp only [Finsupp.nsmul_apply, nsmul_eq_mul, laurentExponentNumerator,
    Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply, Finsupp.add_apply,
    Nat.coe_castAddMonoidHom]
  rw [Int.toNat_of_nonneg hi]
  simp [n]

/-- The natural exponent map is the additive localization away from `m` whose target consists of
the Laurent exponent vectors with negative coordinates only in the support of `m`. -/
noncomputable def laurentExponentAwayMap (m : σ →₀ ℕ) :
    AddSubmonoid.LocalizationMap.AwayMap m (laurentExponentSubmonoid m) :=
  (natToLaurentExponent m).toLocalizationMap
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_nsmul]
      exact IsAddUnit.map (nsmulAddMonoidHom n) (natToLaurentExponent_isAddUnit m))
    (natToLaurentExponent_surj m)
    (fun x y h => by
      have hxy : x = y := by
        ext i
        have hi := congrArg (fun z : laurentExponentSubmonoid m => (z.1 i : ℤ)) h
        simpa using hi
      exact ⟨⟨0, AddSubmonoid.zero_mem _⟩, by simp [hxy]⟩)

@[simp]
theorem laurentExponentAwayMap_apply (m a : σ →₀ ℕ) (i : σ) :
    (((laurentExponentAwayMap m) a : laurentExponentSubmonoid m) : σ →₀ ℤ) i = (a i : ℤ) := by
  rfl

end MvPolynomial
