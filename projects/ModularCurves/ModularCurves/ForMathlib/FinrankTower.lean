/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Tower multiplicativity of module rank for finite flat algebras over domains

For a tower `R → B → A` of **domains** with each step finite and flat,
`finrank R A = finrank R B * finrank B A`.

Over a domain the rank of a finite flat module is its generic-fibre dimension, so the tower
identity is the multiplicativity of fraction-field extension degrees: sandwich each level with
`Algebra.IsAlgebraic.finrank_of_isFractionRing` (`[Frac B : Frac R] = finrank R B`, etc.) and
apply the field tower law `Module.finrank_mul_finrank` to `Frac R ⊆ Frac B ⊆ Frac A`.

This is the algebraic core of the composition multiplicativity of `Scheme.Hom.finrank`
(`deg (f ≫ g) = deg f * deg g` for finite flat morphisms of integral schemes), which in turn is
the `endDeg_comp` multiplicativity pin of the endomorphism-degree keystone
(`ModularCurves/EllipticCurve/EndomorphismDegree.lean`). Companion to STREAM-KM's
`FinrankFractionField.lean` (the single-level `finrank = [Frac S : Frac R]` bridge).

The helper `FaithfulSMul.of_flat_of_nontrivial` (a finite flat nontrivial algebra over a domain
has injective structure map — its rank is a positive constant) is of independent use.
-/

open Module

namespace ModularCurves

universe u

section FaithfulSMul

/-- A **finite flat** algebra `B ≠ 0` over a domain `R` has injective structure map: over a
domain the rank of a finite flat module is constant (`Ideal.finrank_fiber_eq_finrank`), a rank-`0`
finite flat module is trivial (`rankAtStalk_eq_zero_iff_subsingleton`), and everywhere-positive
rank forces injectivity (`rankAtStalk_pos_iff_algebraMap_injective`). -/
theorem FaithfulSMul.of_flat_of_nontrivial (R B : Type*) [CommRing R] [IsDomain R] [CommRing B]
    [Nontrivial B] [Algebra R B] [Module.Finite R B] [Module.Flat R B] : FaithfulSMul R B := by
  rw [faithfulSMul_iff_algebraMap_injective,
    ← Module.rankAtStalk_pos_iff_algebraMap_injective]
  have hconst : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = Module.finrank R B := by
    intro p
    rw [← p.asIdeal.finrank_fiber_eq_rankAtStalk, p.asIdeal.finrank_fiber_eq_finrank]
  rcases Nat.eq_zero_or_pos (Module.finrank R B) with h0 | hpos
  · exfalso
    have hzero : Module.rankAtStalk (R := R) B = 0 := by
      funext p
      rw [hconst p, h0, Pi.zero_apply]
    haveI : Subsingleton B := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hzero
    exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial B›) ‹Subsingleton B›
  · intro p
    rw [hconst p]
    exact hpos

end FaithfulSMul

section Tower

variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [IsDomain R] [IsDomain B] [IsDomain A]
  [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
  [Module.Finite R B] [Module.Flat R B] [Module.Finite B A] [Module.Flat B A]

/-- **Tower multiplicativity of finite flat ranks over domains**:
`finrank R A = finrank R B * finrank B A` for a tower of domains `R → B → A` with each step
finite and flat. Over a domain each rank is the corresponding fraction-field extension degree
(`Algebra.IsAlgebraic.finrank_of_isFractionRing`), and field degrees multiply in towers
(`Module.finrank_mul_finrank` on `Frac R ⊆ Frac B ⊆ Frac A`). -/
theorem finrank_tower_of_flat : finrank R A = finrank R B * finrank B A := by
  -- injectivity of each structure map (positive constant rank)
  haveI hRB : FaithfulSMul R B := FaithfulSMul.of_flat_of_nontrivial R B
  haveI hBA : FaithfulSMul B A := FaithfulSMul.of_flat_of_nontrivial B A
  haveI hRA : FaithfulSMul R A := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R B A]
    exact (FaithfulSMul.algebraMap_injective B A).comp (FaithfulSMul.algebraMap_injective R B)
  -- the composite step is finite flat
  haveI : Module.Finite R A := Module.Finite.trans B A
  haveI : Module.Flat R A := Module.Flat.trans R B A
  -- integrality/algebraicity of each step
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI : Algebra.IsAlgebraic R B := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : Algebra.IsAlgebraic B A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  -- the fraction-field tower `Frac R ⊆ Frac B ⊆ Frac A`
  letI : Algebra (FractionRing R) (FractionRing B) := FractionRing.liftAlgebra R (FractionRing B)
  letI : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B (FractionRing A)
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  haveI : IsScalarTower R B (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply B A (FractionRing A),
        ← IsScalarTower.algebraMap_apply R B A, IsScalarTower.algebraMap_apply R A (FractionRing A)]
  -- each level's rank is the fraction-field degree
  have hRB' : finrank (FractionRing R) (FractionRing B) = finrank R B :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) B (FractionRing B)
  have hBA' : finrank (FractionRing B) (FractionRing A) = finrank B A :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing B (FractionRing B) A (FractionRing A)
  have hRA' : finrank (FractionRing R) (FractionRing A) = finrank R A :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) A (FractionRing A)
  -- the field tower law
  rw [← hRA', ← hRB', ← hBA', Module.finrank_mul_finrank]

end Tower

end ModularCurves
