/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Tickets T-Q3a, T-Q3b, T-Q3c.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# Group actions on localizations at an invariant element

For a group `G` acting on a commutative ring `B` and an element `h : B` fixed by the
action, the action descends to the localization away from `h`:

* `MulSemiringAction.away hfix : MulSemiringAction G (Localization.Away h)` — a `def`,
  not an instance (it depends on the hypothesis `hfix : ∀ g, g • h = h`); consumers
  bring it into scope with `letI`, following the `IsFractionRing.mulSemiringAction`
  precedent.
* `smul_away_algebraMap`, `smul_away_mk'` — the action on numerators.
* `IsLocalization.Away.exists_smul_eq_of_forall_smul_eq` (T-Q3b): for **finite** `G`,
  every fixed element of `Localization.Away h` is of the form `b / hⁿ` with `b`
  invariant — "invariants of the localization = localization of the invariants",
  surjectivity half. No averaging: the proof multiplies by a large power of `h`
  instead of dividing by `|G|`, so there is no invertibility hypothesis on `|G|`.
* `IsLocalization.Away.map_algebraMap_fixedPoints_injective` (T-Q3c(i)): the induced
  map `(Bᴳ)_h → B_h` is injective.

This is the algebra backend of the affine quotient `Spec B → Spec Bᴳ` by a finite
group ([Loeffler, *Modular curves*, Prop 3.6.1] "one can show that these patch
nicely"; SGA I V.1.1; Stacks 07S5): the scheme-level universal property is
`ModularCurves/ForMathlib/AffineQuotient.lean` (ticket T-Q3).
-/

universe u

variable {G : Type*} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]
variable {h : B}

open MulSemiringAction in
private theorem powers_le_comap_toRingHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Submonoid.powers h ≤ (Submonoid.powers h).comap (toRingHom G B g) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, by rw [toRingHom_apply, smul_pow, hfix]⟩

/-- The action of `G` on `Localization.Away h` induced by localizing each `g • ·` at
the invariant element `h`. Not an instance (it depends on the invariance hypothesis):
bring it into scope with `letI := MulSemiringAction.away hfix`. -/
noncomputable def MulSemiringAction.away (hfix : ∀ g : G, g • h = h) :
    MulSemiringAction G (Localization.Away h) where
  smul g := IsLocalization.map (Localization.Away h) (toRingHom G B g)
    (powers_le_comap_toRingHom hfix g)
  one_smul x := DFunLike.congr_fun (IsLocalization.map_unique _ (RingHom.id _)
    fun b => by simp) x
  mul_smul g g' x := DFunLike.congr_fun (IsLocalization.map_unique _
    ((IsLocalization.map _ (toRingHom G B g) (powers_le_comap_toRingHom hfix g)).comp
      (IsLocalization.map _ (toRingHom G B g') (powers_le_comap_toRingHom hfix g')))
    fun b => by simp [IsLocalization.map_eq, mul_smul]) x
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

theorem smul_away_algebraMap (hfix : ∀ g : G, g • h = h) (g : G) (b : B) :
    letI := MulSemiringAction.away hfix
    g • algebraMap B (Localization.Away h) b = algebraMap B (Localization.Away h) (g • b) :=
  IsLocalization.map_eq _ b

theorem smul_away_mk' (hfix : ∀ g : G, g • h = h) (g : G) (b : B) (n : ℕ) :
    letI := MulSemiringAction.away hfix
    g • IsLocalization.mk' (Localization.Away h) b (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) =
      IsLocalization.mk' (Localization.Away h) (g • b)
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) := by
  letI := MulSemiringAction.away hfix
  show IsLocalization.map _ _ (powers_le_comap_toRingHom hfix g) _ = _
  rw [IsLocalization.map_mk']
  congr 1
  exact Subtype.ext (by rw [MulSemiringAction.toRingHom_apply, smul_pow, hfix])

/-- **Invariants of a localization are the localization of the invariants**
(surjectivity half, T-Q3b): for a finite group and an invariant element `h`, every
fixed element of `Localization.Away h` is `b / hⁿ` for an invariant numerator `b`.

No averaging over `G` — the numerator is corrected by a power of `h` instead, so
there is no hypothesis on `|G|` being invertible. -/
theorem IsLocalization.Away.exists_smul_eq_of_forall_smul_eq [Finite G]
    (hfix : ∀ g : G, g • h = h) (x : Localization.Away h)
    (hx : ∀ g : G, (MulSemiringAction.away hfix).smul g x = x) :
    ∃ (b : B) (n : ℕ), (∀ g : G, g • b = b) ∧
      IsLocalization.mk' (Localization.Away h) b
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) = x := by
  letI := MulSemiringAction.away hfix
  sorry

/-- The localization of the inclusion of the fixed subring is injective (T-Q3c(i)). -/
theorem IsLocalization.Away.map_algebraMap_fixedPoints_injective
    (R : Type u) [CommRing R] [Algebra R B] [SMulCommClass G R B]
    (h : FixedPoints.subalgebra R B G) :
    Function.Injective (IsLocalization.Away.map
      (Localization.Away h) (Localization.Away (h : B))
      (algebraMap (FixedPoints.subalgebra R B G) B) h) := by
  sorry
