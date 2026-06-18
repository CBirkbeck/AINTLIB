import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Formal Group Laws (Silverman IV.2, definition)

This file defines the abstract notion of a commutative one-parameter formal
group law over a commutative ring `R`, following Silverman, *The Arithmetic of
Elliptic Curves*, Chapter IV, Section 2.

## Main definitions

* `HasseWeil.FormalGroup.FormalGroup R`: a one-parameter commutative formal
  group law over `R`, specifically a bivariate power series
  `F(X, Y) ∈ R[[X, Y]]` satisfying
  - Left unit:     `F(X, 0) = X`
  - Right unit:    `F(0, Y) = Y`
  - Associativity: `F(F(X, Y), Z) = F(X, F(Y, Z))`
  - Commutativity: `F(X, Y) = F(Y, X)`

The existence of an inverse series `i(T)` with `F(T, i(T)) = 0` is derivable
from these axioms (see T-IV-2-009 for the power series invertibility lemma);
it is therefore not part of the structure.

## Design notes

The formal group law lives in `MvPowerSeries (Fin 2) R`, with the two variables
`X, Y` corresponding to `MvPowerSeries.X 0, MvPowerSeries.X 1`. The axioms are
expressed using `MvPowerSeries.subst` from
`Mathlib/RingTheory/MvPowerSeries/Substitution.lean`.

Associativity is stated as an identity in `MvPowerSeries (Fin 3) R`, where the
three variables correspond to `X, Y, Z`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.2 (Definition of formal
  group law, p. 120).
-/

open MvPowerSeries

namespace HasseWeil.FormalGroup

variable (R : Type*) [CommRing R]

set_option linter.dupNamespace false in

/-- A **commutative one-parameter formal group law** over `R`, in the sense of
Silverman IV.2.

A formal group law is a bivariate power series `F(X, Y) ∈ R[[X, Y]]` satisfying
the four axioms:
* `F(X, 0) = X`               (left unit)
* `F(0, Y) = Y`               (right unit)
* `F(F(X, Y), Z) = F(X, F(Y, Z))` (associativity)
* `F(X, Y) = F(Y, X)`         (commutativity)

The existence of an inverse `i(T) ∈ R[[T]]` with `F(T, i(T)) = 0` is *derivable*
from these axioms and is not carried as data here; see the power series
invertibility lemma (T-IV-2-009).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2. -/
structure FormalGroup where
  /-- The bivariate power series `F(X, Y) ∈ R[[X, Y]]` defining the group law. -/
  toSeries : MvPowerSeries (Fin 2) R
  /-- Left unit: `F(X, 0) = X`. -/
  lunit :
    MvPowerSeries.subst
        (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R)
        toSeries =
      MvPowerSeries.X 0
  /-- Right unit: `F(0, Y) = Y`. -/
  runit :
    MvPowerSeries.subst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R)
        toSeries =
      MvPowerSeries.X 1
  /-- Associativity: `F(F(X, Y), Z) = F(X, F(Y, Z))`.

  The equation lives in `MvPowerSeries (Fin 3) R`, where the three variables
  are `X = X 0`, `Y = X 1`, `Z = X 2`. -/
  assoc :
    MvPowerSeries.subst
        (![MvPowerSeries.subst
              (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
                Fin 2 → MvPowerSeries (Fin 3) R)
              toSeries,
            MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        toSeries =
      MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3),
            MvPowerSeries.subst
              (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
                Fin 2 → MvPowerSeries (Fin 3) R)
              toSeries] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        toSeries
  /-- Commutativity: `F(X, Y) = F(Y, X)`. -/
  comm :
    MvPowerSeries.subst
        (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R)
        toSeries =
      toSeries

variable {R}

/-- A **homomorphism of formal group laws** `f : F → G` over `R`.

A homomorphism is a univariate power series `f(T) ∈ R[[T]]` with `f(0) = 0`
satisfying
`f(F(X, Y)) = G(f(X), f(Y))`,
where `F(X, Y), G(X, Y) ∈ R[[X, Y]]` are the bivariate series defining the
formal group laws, and `f(X), f(Y)` are the univariate `f` with its variable
substituted for the first or second variable, respectively.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2 (definition of
homomorphism of formal groups). -/
structure FormalGroupHom (F G : FormalGroup R) where
  /-- The univariate power series `f(T) ∈ R[[T]]` defining the homomorphism. -/
  toSeries : PowerSeries R
  /-- `f` has vanishing constant term: `f(0) = 0`. -/
  zero_const : PowerSeries.constantCoeff (R := R) toSeries = 0
  /-- `f` intertwines the group laws: `f(F(X, Y)) = G(f(X), f(Y))`.

  The LHS `f(F(X, Y))` is the univariate `toSeries` with its variable substituted
  by `F.toSeries`, yielding a bivariate power series. The RHS `G(f(X), f(Y))`
  first lifts `toSeries` to a bivariate series in each slot (substituting `X 0`
  or `X 1` for the variable of `f`) and then substitutes the pair into
  `G.toSeries`. -/
  preserves_add :
    PowerSeries.subst F.toSeries toSeries =
      MvPowerSeries.subst
        (![PowerSeries.subst
              (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) toSeries,
            PowerSeries.subst
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) toSeries] :
          Fin 2 → MvPowerSeries (Fin 2) R)
        G.toSeries

/-! ### Examples: the additive and multiplicative formal group laws -/

variable (R)

/-- The **additive formal group law** `Ĝ_a` over `R`: `F(X, Y) = X + Y`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2.1. -/
noncomputable def additiveFormalGroup : FormalGroup R where
  toSeries := MvPowerSeries.X 0 + MvPowerSeries.X 1
  lunit := by
    have ha : MvPowerSeries.HasSubst
        (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha]
    show MvPowerSeries.subst _ (MvPowerSeries.X 0) +
         MvPowerSeries.subst _ (MvPowerSeries.X 1) = MvPowerSeries.X 0
    rw [MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    simp
  runit := by
    have ha : MvPowerSeries.HasSubst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha]
    show MvPowerSeries.subst _ (MvPowerSeries.X 0) +
         MvPowerSeries.subst _ (MvPowerSeries.X 1) = MvPowerSeries.X 1
    rw [MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    simp
  assoc := by
    -- Inner substs: first compute subst ![X 0, X 1] (X 0 + X 1) = X 0 + X 1
    -- and subst ![X 1, X 2] (X 0 + X 1) = X 1 + X 2.
    have h_XY : MvPowerSeries.HasSubst
        (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have h_YZ : MvPowerSeries.HasSubst
        (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have e_XY : MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
      rw [MvPowerSeries.subst_add h_XY,
          MvPowerSeries.subst_X h_XY 0, MvPowerSeries.subst_X h_XY 1]
      rfl
    have e_YZ : MvPowerSeries.subst
        (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        MvPowerSeries.X 1 + MvPowerSeries.X 2 := by
      rw [MvPowerSeries.subst_add h_YZ,
          MvPowerSeries.subst_X h_YZ 0, MvPowerSeries.subst_X h_YZ 1]
      rfl
    rw [e_XY, e_YZ]
    -- Outer substs
    have h_L : MvPowerSeries.HasSubst
        (![(MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
           MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have h_R : MvPowerSeries.HasSubst
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
           MvPowerSeries.X 1 + MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add h_L,
        MvPowerSeries.subst_X h_L 0, MvPowerSeries.subst_X h_L 1]
    rw [MvPowerSeries.subst_add h_R,
        MvPowerSeries.subst_X h_R 0, MvPowerSeries.subst_X h_R 1]
    show ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) +
           MvPowerSeries.X 2) =
         (MvPowerSeries.X 0 + (MvPowerSeries.X 1 + MvPowerSeries.X 2))
    ring
  comm := by
    have ha : MvPowerSeries.HasSubst
        (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha]
    show MvPowerSeries.subst _ (MvPowerSeries.X 0) +
         MvPowerSeries.subst _ (MvPowerSeries.X 1) =
         MvPowerSeries.X 0 + MvPowerSeries.X 1
    rw [MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    show ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 0) =
         MvPowerSeries.X 0 + MvPowerSeries.X 1
    ring

/-- The **multiplicative formal group law** `Ĝ_m` over `R`:
    `F(X, Y) = X + Y + XY = (1+X)(1+Y) − 1`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.2.2. -/
noncomputable def multiplicativeFormalGroup : FormalGroup R where
  toSeries := MvPowerSeries.X 0 + MvPowerSeries.X 1 +
              MvPowerSeries.X 0 * MvPowerSeries.X 1
  lunit := by
    have ha : MvPowerSeries.HasSubst
        (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
        MvPowerSeries.subst_mul ha,
        MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + 0 + MvPowerSeries.X 0 * 0
      = MvPowerSeries.X 0
    ring
  runit := by
    have ha : MvPowerSeries.HasSubst
        (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
        MvPowerSeries.subst_mul ha,
        MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    show (0 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 1 + 0 * MvPowerSeries.X 1
      = MvPowerSeries.X 1
    ring
  assoc := by
    -- Inner substs
    have h_XY : MvPowerSeries.HasSubst
        (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have h_YZ : MvPowerSeries.HasSubst
        (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have e_XY : MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        ((MvPowerSeries.X 0 + MvPowerSeries.X 1 +
          MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        MvPowerSeries.X 0 + MvPowerSeries.X 1 +
          MvPowerSeries.X 0 * MvPowerSeries.X 1 := by
      rw [MvPowerSeries.subst_add h_XY, MvPowerSeries.subst_add h_XY,
          MvPowerSeries.subst_mul h_XY,
          MvPowerSeries.subst_X h_XY 0, MvPowerSeries.subst_X h_XY 1]
      rfl
    have e_YZ : MvPowerSeries.subst
        (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R)
        ((MvPowerSeries.X 0 + MvPowerSeries.X 1 +
          MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) =
        MvPowerSeries.X 1 + MvPowerSeries.X 2 +
          MvPowerSeries.X 1 * MvPowerSeries.X 2 := by
      rw [MvPowerSeries.subst_add h_YZ, MvPowerSeries.subst_add h_YZ,
          MvPowerSeries.subst_mul h_YZ,
          MvPowerSeries.subst_X h_YZ 0, MvPowerSeries.subst_X h_YZ 1]
      rfl
    rw [e_XY, e_YZ]
    -- Outer substs
    have h_L : MvPowerSeries.HasSubst
        (![(MvPowerSeries.X 0 + MvPowerSeries.X 1 +
            MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
           MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    have h_R : MvPowerSeries.HasSubst
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
           MvPowerSeries.X 1 + MvPowerSeries.X 2 +
             MvPowerSeries.X 1 * MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add h_L, MvPowerSeries.subst_add h_L,
        MvPowerSeries.subst_mul h_L,
        MvPowerSeries.subst_X h_L 0, MvPowerSeries.subst_X h_L 1]
    rw [MvPowerSeries.subst_add h_R, MvPowerSeries.subst_add h_R,
        MvPowerSeries.subst_mul h_R,
        MvPowerSeries.subst_X h_R 0, MvPowerSeries.subst_X h_R 1]
    show (((MvPowerSeries.X 0 + MvPowerSeries.X 1 +
             MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) +
           MvPowerSeries.X 2) +
          (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
             MvPowerSeries.X 0 * MvPowerSeries.X 1) *
            MvPowerSeries.X 2) =
          ((MvPowerSeries.X 0 +
             (MvPowerSeries.X 1 + MvPowerSeries.X 2 +
              MvPowerSeries.X 1 * MvPowerSeries.X 2)) +
           MvPowerSeries.X 0 *
             (MvPowerSeries.X 1 + MvPowerSeries.X 2 +
              MvPowerSeries.X 1 * MvPowerSeries.X 2))
    ring
  comm := by
    have ha : MvPowerSeries.HasSubst
        (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
          Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s; fin_cases s <;> simp
    rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
        MvPowerSeries.subst_mul ha,
        MvPowerSeries.subst_X ha 0, MvPowerSeries.subst_X ha 1]
    show ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) + MvPowerSeries.X 0 +
           MvPowerSeries.X 1 * MvPowerSeries.X 0) =
         MvPowerSeries.X 0 + MvPowerSeries.X 1 +
           MvPowerSeries.X 0 * MvPowerSeries.X 1
    ring

/-! ### Multiplication-by-m on formal groups (Silverman IV.2.3)

The iterated m-fold sum `[m](T)` is defined recursively:
- `[0](T) = 0`
- `[m+1](T) = F([m](T), T)` (adding T to the m-fold sum using the group law)

The key property (Silverman Prop. IV.2.3a) is that `[m](T) = m·T + O(T²)`. -/

end HasseWeil.FormalGroup

namespace HasseWeil.FG

variable {R : Type*} [CommRing R]

/-- Evaluate the formal group law at two power series: `F(f, g)` where
    `f(0) = g(0) = 0`. The result is a univariate power series.
    Reference: Silverman IV.2.3 (implicit in the recursive definition of [m]). -/
noncomputable def fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R) :
    PowerSeries R :=
  MvPowerSeries.subst (show Fin 2 → MvPowerSeries Unit R from ![f, g]) F.toSeries

/-- The multiplication-by-m series `[m](T)` for `m : ℕ`, defined recursively:
    `[0](T) = 0`, `[m+1](T) = F([m](T), T)`.
    Reference: Silverman IV.2.3. -/
noncomputable def mulByNatSeries (F : FormalGroup.FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => fAdd F (mulByNatSeries F n) (PowerSeries.X)

/-! ### Properties of fAdd and mulByNatSeries -/

variable {R : Type*} [CommRing R]

lemma hasSubst_pair (f g : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (show Fin 2 → MvPowerSeries Unit R from ![f, g]) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simpa

lemma subst_matrix_X0 {σ : Type*} (a : Fin 2 → MvPowerSeries σ R)
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = a 0 :=
  @MvPowerSeries.subst_X (Fin 2) R _ σ R _ _ _ ha 0

lemma subst_matrix_X1 {σ : Type*} (a : Fin 2 → MvPowerSeries σ R)
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = a 1 :=
  @MvPowerSeries.subst_X (Fin 2) R _ σ R _ _ _ ha 1

lemma subst_fin3_X {σ : Type*} (a : Fin 3 → MvPowerSeries σ R)
    (ha : MvPowerSeries.HasSubst a) (i : Fin 3) :
    MvPowerSeries.subst a (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = a i :=
  @MvPowerSeries.subst_X (Fin 3) R _ σ R _ _ _ ha i

lemma subst_zero_eq {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [show (0 : MvPowerSeries σ R) = (↑(0 : MvPolynomial σ R)) from by simp,
      MvPowerSeries.subst_coe]; simp

/-- `constantCoeff (subst a f) = constantCoeff f` when all `a s` have vanishing
    constant coefficient (i.e., when `a` maps all variables to series vanishing at 0). -/
theorem constantCoeff_subst_vanishing {σ τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (hcc : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) =
      MvPowerSeries.constantCoeff f := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff]
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · simp [Finsupp.prod_zero_index, smul_eq_mul, mul_one]
  · intro d hd
    have : MvPowerSeries.constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
      exact Finset.prod_eq_zero hs
        (by rw [map_pow, hcc, zero_pow (Finsupp.mem_support_iff.mp hs)])
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff] at this
    rw [this, smul_zero]

/-- The constant coefficient of `F(X, Y)` is zero: `F(0, 0) = 0`. -/
theorem constantCoeff_FG_toSeries (F : FormalGroup.FormalGroup R) :
    MvPowerSeries.constantCoeff F.toSeries = 0 := by
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have := congr_arg MvPowerSeries.constantCoeff F.lunit
  rw [constantCoeff_subst_vanishing ha (fun s ↦ by fin_cases s <;> simp)] at this
  simpa using this

/-- `constantCoeff (fAdd F f g) = 0` when `f(0) = g(0) = 0`. -/
theorem constantCoeff_fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (fAdd F f g) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ F.toSeries) = 0
  rw [constantCoeff_subst_vanishing (hasSubst_pair f g hf hg)
    (fun s ↦ by fin_cases s <;> simpa)]
  exact constantCoeff_FG_toSeries F

/-- The formal group law preserves the maximal ideal `𝔪 = {f : 0 < f.order}`:
    if `f` and `g` both vanish at the origin (equivalently, have positive order),
    then so does `F(f, g)`. This is the formal-neighbourhood (QF Layer-1) brick
    expressing that `fAdd` maps `𝔪 × 𝔪 → 𝔪`.
    Reference: Silverman IV.2.3 (the group law on the formal neighbourhood). -/
theorem formalGroup_preserves_positive_order (F : FormalGroup.FormalGroup R)
    (f g : PowerSeries R) (hf : 0 < f.order) (hg : 0 < g.order) :
    0 < (fAdd F f g).order := by
  -- Bridge `0 < order` with `constantCoeff = 0` via `order ≠ 0 ↔ constantCoeff = 0`.
  rw [pos_iff_ne_zero, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero] at hf hg ⊢
  exact constantCoeff_fAdd F f g hf hg

/-- `F(0, g) = g`: the formal group law with first argument zero returns the second. -/
theorem fAdd_zero_left (F : FormalGroup.FormalGroup R) (g : PowerSeries R)
    (hg : PowerSeries.constantCoeff g = 0) :
    fAdd F 0 g = g := by
  unfold fAdd
  have ha : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have hb := hasSubst_pair (0 : PowerSeries R) g (by simp) hg
  have step := congr_arg
    (MvPowerSeries.subst (show Fin 2 → MvPowerSeries Unit R from ![0, g])) F.runit
  rw [MvPowerSeries.subst_comp_subst_apply ha hb, subst_matrix_X1 _ hb] at step
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at step
  have heq : (fun s ↦ MvPowerSeries.subst
      (show Fin 2 → MvPowerSeries Unit R from ![0, g])
      ((![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) s)) =
    (show Fin 2 → MvPowerSeries Unit R from ![0, g]) := by
    funext s; fin_cases s
    · simp only []; exact subst_zero_eq hb
    · exact subst_matrix_X1 (show Fin 2 → MvPowerSeries Unit R from ![0, g]) hb
  rw [heq] at step; exact step

/-- `[1](T) = T`: multiplication by 1 is the identity. -/
theorem mulByNatSeries_one (F : FormalGroup.FormalGroup R) :
    mulByNatSeries F 1 = PowerSeries.X :=
  fAdd_zero_left F PowerSeries.X (by simp)

/-! ### Leading coefficient: `[m](T) = m·T + O(T²)` (Silverman IV.2.3a) -/

private lemma coeff_one_high_deg (f g : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (a b : ℕ) (hab : 2 ≤ a + b) :
    PowerSeries.coeff 1 (f ^ a * g ^ b) = 0 := by
  have : PowerSeries.X ^ (a + b) ∣ f ^ a * g ^ b := by
    rw [pow_add]
    exact mul_dvd_mul
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hf) _)
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg) _)
  exact (PowerSeries.X_pow_dvd_iff.mp this) 1 (by omega)

/-- The coefficient of `X¹Y⁰` in `F(X, Y)` is `1` (from `F(X, 0) = X`). -/
theorem FormalGroup.coeff_10 (F : FormalGroup.FormalGroup R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F.toSeries = 1 := by
  have key := congr_arg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) F.lunit
  rw [MvPowerSeries.coeff_index_single_self_X] at key
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  rw [MvPowerSeries.coeff_subst ha,
      finsum_eq_single _ (Finsupp.single (0 : Fin 2) 1)] at key
  · simp only [Finsupp.prod_single_index, pow_zero, pow_one, Matrix.cons_val_zero] at key
    rwa [MvPowerSeries.coeff_index_single_self_X, smul_eq_mul, mul_one] at key
  · intro d hd
    suffices MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (d.prod fun s e ↦
          (![MvPowerSeries.X 0, (0 : MvPowerSeries (Fin 2) R)] s) ^ e) = 0 by
      rw [this, smul_zero]
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    by_cases hd1 : d 1 = 0
    · simp only [hd1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
      have : d 0 ≠ 1 :=
        fun h ↦ hd (Finsupp.ext (fun i ↦ by fin_cases i <;> simp [h, hd1]))
      split_ifs with h
      · exact absurd (by simpa [Finsupp.single_eq_same] using
            (DFunLike.congr_fun h 0).symm) this
      · rfl
    · rw [zero_pow hd1, mul_zero, map_zero]

/-- The coefficient of `X⁰Y¹` in `F(X, Y)` is `1` (from `F(0, Y) = Y`). -/
theorem FormalGroup.coeff_01 (F : FormalGroup.FormalGroup R) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F.toSeries = 1 := by
  have key := congr_arg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) F.runit
  rw [MvPowerSeries.coeff_index_single_self_X] at key
  have ha : MvPowerSeries.HasSubst
      (![0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  rw [MvPowerSeries.coeff_subst ha,
      finsum_eq_single _ (Finsupp.single (1 : Fin 2) 1)] at key
  · simp only [Finsupp.prod_single_index, pow_zero, pow_one,
      Matrix.cons_val_one, Matrix.cons_val_zero] at key
    rwa [MvPowerSeries.coeff_index_single_self_X, smul_eq_mul, mul_one] at key
  · intro d hd
    suffices MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        (d.prod fun s e ↦
          (![(0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] s) ^ e) = 0 by
      rw [this, smul_zero]
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> simp),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
    by_cases hd0 : d 0 = 0
    · simp only [hd0, pow_zero, one_mul, MvPowerSeries.coeff_X_pow]
      have : d 1 ≠ 1 :=
        fun h ↦ hd (Finsupp.ext (fun i ↦ by fin_cases i <;> simp [h, hd0]))
      split_ifs with h
      · exact absurd (by simpa [Finsupp.single_eq_same] using
            (DFunLike.congr_fun h 1).symm) this
      · rfl
    · rw [zero_pow hd0, zero_mul, map_zero]

/-- The linear coefficient of `F(f, g)` is `coeff_1(f) + coeff_1(g)` when `f(0) = g(0) = 0`.
    This is the abstract analogue of `pullbackCoeff_add` (Silverman III.5.6). -/
theorem coeff_one_fAdd (F : FormalGroup.FormalGroup R) (f g : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (fAdd F f g) =
      PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  show MvPowerSeries.coeff (Finsupp.single () 1)
    (MvPowerSeries.subst _ F.toSeries) = _
  have ha := hasSubst_pair f g hf hg
  rw [MvPowerSeries.coeff_subst ha]
  conv_lhs =>
    arg 1; ext d; rw [smul_eq_mul]; arg 2
    change MvPowerSeries.coeff (Finsupp.single () 1)
      (d.prod fun s e ↦ (![f, g]) s ^ e)
    rw [Finsupp.prod_fintype _ _ (fun i ↦ by fin_cases i <;> exact pow_zero _),
        Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  change (∑ᶠ d, MvPowerSeries.coeff d F.toSeries *
    PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1))) = _
  have vanish : ∀ d : Fin 2 →₀ ℕ, d ≠ Finsupp.single 0 1 → d ≠ Finsupp.single 1 1 →
      MvPowerSeries.coeff d F.toSeries *
        PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1)) = 0 := by
    intro d hd0 hd1
    by_cases hsum : 2 ≤ d 0 + d 1
    · rw [coeff_one_high_deg f g hf hg (d 0) (d 1) hsum, mul_zero]
    · push Not at hsum
      have hd : d = 0 := by
        ext i; fin_cases i <;> simp_all [Finsupp.ext_iff, Fin.forall_fin_two] <;> omega
      subst hd
      simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero]
      norm_num [PowerSeries.coeff_one, constantCoeff_FG_toSeries]
  have hsub : Function.support (fun d : Fin 2 →₀ ℕ ↦
      MvPowerSeries.coeff d F.toSeries *
        PowerSeries.coeff 1 (f ^ (d 0) * g ^ (d 1))) ⊆
      ({Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra h; simp at h
    exact hd (vanish d h.1 h.2)
  rw [finsum_eq_finsetSum_of_support_subset _ hsub]
  have hne : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    exact absurd (DFunLike.congr_fun h 0) (by simp [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide)])
  rw [Finset.sum_pair hne]
  simp only [Finsupp.single_eq_same, pow_one, pow_zero,
    Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
    Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),
    FormalGroup.coeff_10, FormalGroup.coeff_01, one_mul]
  rw [mul_one]

/-- The constant coefficient of `[m](T)` is `0`. -/
theorem constantCoeff_mulByNatSeries (F : FormalGroup.FormalGroup R) (n : ℕ) :
    PowerSeries.constantCoeff (mulByNatSeries F n) = 0 := by
  induction n with
  | zero => simp [mulByNatSeries]
  | succ n ih => exact constantCoeff_fAdd F _ _ ih (by simp)

/-- The leading coefficient of `[m](T)` is `m`: `[m](T) = m·T + O(T²)`.
    Reference: Silverman IV.2.3(a). -/
theorem coeff_one_mulByNatSeries (F : FormalGroup.FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (mulByNatSeries F n) = (n : R) := by
  induction n with
  | zero => simp [mulByNatSeries]
  | succ n ih =>
    show PowerSeries.coeff 1 (fAdd F (mulByNatSeries F n) PowerSeries.X) = _
    rw [coeff_one_fAdd F _ _ (constantCoeff_mulByNatSeries F n) (by simp)]
    simp [ih, Nat.cast_succ]

/-! ### Additional fAdd properties: zero_right, commutativity, associativity -/

/-- `F(f, 0) = f`: the formal group law with second argument zero returns the first. -/
theorem fAdd_zero_right (F : FormalGroup.FormalGroup R) (f : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) :
    fAdd F f 0 = f := by
  unfold fAdd
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have hb := hasSubst_pair f (0 : PowerSeries R) hf (by simp)
  have step := congr_arg
    (MvPowerSeries.subst (show Fin 2 → MvPowerSeries Unit R from ![f, 0])) F.lunit
  rw [MvPowerSeries.subst_comp_subst_apply ha hb, subst_matrix_X0 _ hb] at step
  simp only [Matrix.cons_val_zero] at step
  have heq : (fun s ↦ MvPowerSeries.subst
      (show Fin 2 → MvPowerSeries Unit R from ![f, 0])
      ((![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) R) s)) =
    (show Fin 2 → MvPowerSeries Unit R from ![f, 0]) := by
    funext s; fin_cases s
    · exact subst_matrix_X0 (show Fin 2 → MvPowerSeries Unit R from ![f, 0]) hb
    · simp only []; exact subst_zero_eq hb
  rw [heq] at step; exact step

/-- `F(f, g) = F(g, f)`: commutativity of the formal addition. -/
theorem fAdd_comm (F : FormalGroup.FormalGroup R) (f g : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    fAdd F f g = fAdd F g f := by
  unfold fAdd
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have hb := hasSubst_pair f g hf hg
  have step := congr_arg
    (MvPowerSeries.subst (show Fin 2 → MvPowerSeries Unit R from ![f, g])) F.comm
  rw [MvPowerSeries.subst_comp_subst_apply ha hb] at step
  have heq : (fun s ↦ MvPowerSeries.subst
      (show Fin 2 → MvPowerSeries Unit R from ![f, g])
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s)) =
    (show Fin 2 → MvPowerSeries Unit R from ![g, f]) := by
    funext s; fin_cases s
    · simp only []
      exact subst_matrix_X1 (show Fin 2 → MvPowerSeries Unit R from ![f, g]) hb
    · simp only []
      exact subst_matrix_X0 (show Fin 2 → MvPowerSeries Unit R from ![f, g]) hb
  rw [heq] at step; exact step.symm

set_option maxHeartbeats 800000 in
/-- `F(F(f, g), h) = F(f, F(g, h))`: associativity of the formal addition. -/
theorem fAdd_assoc (F : FormalGroup.FormalGroup R) (f g h : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0) :
    fAdd F (fAdd F f g) h = fAdd F f (fAdd F g h) := by
  -- Strategy: apply subst ![f,g,h] to F.assoc, then show each side equals fAdd ∘ fAdd.
  -- HasSubst for variable embeddings (Fin 2 → Fin 3)
  have h_XY : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  have h_YZ : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s <;> simp
  -- HasSubst for the outer substitutions in F.assoc (Fin 2 → Fin 3)
  have h_FXY_Z : MvPowerSeries.HasSubst
      (![MvPowerSeries.subst
            (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
              Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
          MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s
    · simp only []
      exact (constantCoeff_subst_vanishing h_XY (fun s ↦ by fin_cases s <;> simp)
        F.toSeries).trans (constantCoeff_FG_toSeries F)
    · simp
  have h_X_FYZ : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 3),
          MvPowerSeries.subst
            (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
              Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries] :
        Fin 2 → MvPowerSeries (Fin 3) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s
    · simp
    · simp only []
      exact (constantCoeff_subst_vanishing h_YZ (fun s ↦ by fin_cases s <;> simp)
        F.toSeries).trans (constantCoeff_FG_toSeries F)
  -- HasSubst for the specialization map (Fin 3 → Unit)
  have h_fgh : MvPowerSeries.HasSubst
      (show Fin 3 → MvPowerSeries Unit R from ![f, g, h]) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero; intro s; fin_cases s
    · simpa [PowerSeries.constantCoeff_eq] using hf
    · simpa [PowerSeries.constantCoeff_eq] using hg
    · simpa [PowerSeries.constantCoeff_eq] using hh
  -- Specialized pair HasSubst
  have hfg := hasSubst_pair f g hf hg
  -- Helper: subst_X lemmas for the Fin 3 → Unit substitution
  have subst_fgh_X0 : MvPowerSeries.subst
      (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])
      (MvPowerSeries.X (0 : Fin 3)) = f :=
    subst_fin3_X _ h_fgh 0
  have subst_fgh_X1 : MvPowerSeries.subst
      (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])
      (MvPowerSeries.X (1 : Fin 3)) = g :=
    subst_fin3_X _ h_fgh 1
  have subst_fgh_X2 : MvPowerSeries.subst
      (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])
      (MvPowerSeries.X (2 : Fin 3)) = h :=
    subst_fin3_X _ h_fgh 2
  -- Helper: composed substitution for LHS
  -- subst ![f,g,h] (subst ![F(X,Y), Z] F) = subst ![F(f,g), h] F
  have comp_L : MvPowerSeries.subst (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])
      (MvPowerSeries.subst
        (![MvPowerSeries.subst
              (![MvPowerSeries.X (0 : Fin 3), MvPowerSeries.X 1] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries,
            MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries) =
      MvPowerSeries.subst
        (show Fin 2 → MvPowerSeries Unit R from ![fAdd F f g, h]) F.toSeries := by
    rw [MvPowerSeries.subst_comp_subst_apply h_FXY_Z h_fgh]
    congr 1; funext s; fin_cases s
    · -- s = 0: subst ![f,g,h] (subst ![X0, X1] F) = fAdd F f g
      show MvPowerSeries.subst _ (MvPowerSeries.subst _ F.toSeries) = _
      simp only []; unfold fAdd
      rw [MvPowerSeries.subst_comp_subst_apply h_XY h_fgh]
      congr 1; funext s; fin_cases s
      · exact subst_fin3_X _ h_fgh 0
      · exact subst_fin3_X _ h_fgh 1
    · -- s = 1: subst ![f,g,h] (X 2) = h
      show MvPowerSeries.subst _ (MvPowerSeries.X 2) = _
      exact subst_fin3_X _ h_fgh 2
  -- Helper: composed substitution for RHS
  -- subst ![f,g,h] (subst ![X, F(Y,Z)] F) = subst ![f, F(g,h)] F
  have comp_R : MvPowerSeries.subst (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])
      (MvPowerSeries.subst
        (![MvPowerSeries.X (0 : Fin 3),
            MvPowerSeries.subst
              (![MvPowerSeries.X (1 : Fin 3), MvPowerSeries.X 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries] :
          Fin 2 → MvPowerSeries (Fin 3) R) F.toSeries) =
      MvPowerSeries.subst
        (show Fin 2 → MvPowerSeries Unit R from ![f, fAdd F g h]) F.toSeries := by
    rw [MvPowerSeries.subst_comp_subst_apply h_X_FYZ h_fgh]
    congr 1; funext s; fin_cases s
    · -- s = 0: subst ![f,g,h] (X 0) = f
      show MvPowerSeries.subst _ (MvPowerSeries.X 0) = _
      exact subst_fin3_X _ h_fgh 0
    · -- s = 1: subst ![f,g,h] (subst ![X1, X2] F) = fAdd F g h
      show MvPowerSeries.subst _ (MvPowerSeries.subst _ F.toSeries) = _
      simp only []; unfold fAdd
      rw [MvPowerSeries.subst_comp_subst_apply h_YZ h_fgh]
      congr 1; funext s; fin_cases s
      · exact subst_fin3_X _ h_fgh 1
      · exact subst_fin3_X _ h_fgh 2
  -- Main proof: apply subst ![f,g,h] to F.assoc, use comp_L and comp_R
  have step := congr_arg
    (MvPowerSeries.subst (show Fin 3 → MvPowerSeries Unit R from ![f, g, h])) F.assoc
  rw [comp_L, comp_R] at step
  exact step

set_option maxHeartbeats 1600000 in
/-- `[m + n](T) = F([m](T), [n](T))`: addition formula for mulByNatSeries. -/
theorem mulByNatSeries_add (F : FormalGroup.FormalGroup R) (m n : ℕ) :
    mulByNatSeries F (m + n) = fAdd F (mulByNatSeries F m) (mulByNatSeries F n) := by
  induction n with
  | zero =>
    simp only [Nat.add_zero, mulByNatSeries]
    exact (fAdd_zero_right F _ (constantCoeff_mulByNatSeries F m)).symm
  | succ n ih =>
    show fAdd F (mulByNatSeries F (m + n)) PowerSeries.X =
      fAdd F (mulByNatSeries F m) (fAdd F (mulByNatSeries F n) PowerSeries.X)
    rw [ih]
    have hm := constantCoeff_mulByNatSeries F m
    have hn := constantCoeff_mulByNatSeries F n
    have hX : PowerSeries.constantCoeff (R := R) PowerSeries.X = 0 := by simp
    exact fAdd_assoc F (mulByNatSeries F m) (mulByNatSeries F n) PowerSeries.X hm hn hX

end HasseWeil.FG
