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
* `smul_away_algebraMap`, `smul_away_mk'` — the action acts on numerators.
* `exists_fixed_mk'_eq_of_forall_smul_eq` (T-Q3b): for **finite** `G`, every fixed
  element of `Localization.Away h` is of the form `b / hⁿ` with `b` invariant —
  "invariants of the localization = localization of the invariants", surjectivity
  half. No averaging: the numerator is corrected by a power of `h` instead of
  dividing by `|G|`, so there is no invertibility hypothesis on `|G|`.
* `fixedPoints_awayMap_injective` (T-Q3c(i)): the induced map `(Bᴳ)_h → B_h` is
  injective.

This is the algebra backend of the affine quotient `Spec B → Spec Bᴳ` by a finite
group ([Loeffler, *Modular curves*, Prop 3.6.1] "one can show that these patch
nicely"; SGA I V.1.1; Stacks 07S5): the scheme-level universal property is
`ModularCurves/ForMathlib/AffineQuotient.lean` (ticket T-Q3).
-/

universe u

variable {G : Type*} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]
variable {h : B}

open MulSemiringAction in
theorem Submonoid.powers_le_comap_toRingHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Submonoid.powers h ≤ (Submonoid.powers h).comap (toRingHom G B g) := by
  rintro x ⟨n, rfl⟩
  refine Submonoid.mem_comap.mpr ⟨n, ?_⟩
  rw [toRingHom_apply, smul_pow, hfix]

/-- The action of `G` on `Localization.Away h` induced by localizing each `g • ·` at
the invariant element `h`. Not an instance (it depends on the invariance hypothesis):
bring it into scope with `letI := MulSemiringAction.away hfix`. -/
noncomputable def MulSemiringAction.away (hfix : ∀ g : G, g • h = h) :
    MulSemiringAction G (Localization.Away h) where
  smul g := IsLocalization.map (Localization.Away h) (toRingHom G B g)
    (Submonoid.powers_le_comap_toRingHom hfix g)
  one_smul x := DFunLike.congr_fun (IsLocalization.map_unique _ (RingHom.id _)
    fun b => by simp) x
  mul_smul g g' x := DFunLike.congr_fun (IsLocalization.map_unique _
    ((IsLocalization.map _ (toRingHom G B g)
        (Submonoid.powers_le_comap_toRingHom hfix g)).comp
      (IsLocalization.map _ (toRingHom G B g')
        (Submonoid.powers_le_comap_toRingHom hfix g')))
    fun b => by simp [IsLocalization.map_eq, mul_smul]) x
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

theorem smul_away_algebraMap (hfix : ∀ g : G, g • h = h) (g : G) (b : B) :
    letI := MulSemiringAction.away hfix
    g • algebraMap B (Localization.Away h) b =
      algebraMap B (Localization.Away h) (g • b) :=
  IsLocalization.map_eq _ b

theorem smul_away_mk' (hfix : ∀ g : G, g • h = h) (g : G) (b : B)
    (s : Submonoid.powers h) :
    letI := MulSemiringAction.away hfix
    g • IsLocalization.mk' (Localization.Away h) b s =
      IsLocalization.mk' (Localization.Away h) (g • b)
        ⟨g • (s : B), Submonoid.powers_le_comap_toRingHom hfix g s.2⟩ :=
  IsLocalization.map_mk' _ b s

/-- **Invariants of a localization are the localization of the invariants**
(surjectivity half, T-Q3b): for a finite group and an invariant element `h`, every
fixed element of `Localization.Away h` is `b / hⁿ` for an invariant numerator `b`.

No averaging over `G` — the numerator is corrected by a power of `h` instead, so
there is no hypothesis on `|G|` being invertible in `B`. -/
theorem exists_fixed_mk'_eq_of_forall_smul_eq [Finite G]
    (hfix : ∀ g : G, g • h = h) (x : Localization.Away h) :
    letI := MulSemiringAction.away hfix
    (∀ g : G, g • x = x) →
      ∃ (b : B) (n : ℕ), (∀ g : G, g • b = b) ∧
        IsLocalization.mk' (Localization.Away h) b
          (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) = x := by
  letI := MulSemiringAction.away hfix
  intro hx
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  obtain ⟨sv, N, rfl⟩ := s
  have key : ∀ g : G, ∃ m : ℕ, h ^ m * (g • b) = h ^ m * b := by
    intro g
    have hg := hx g
    rw [smul_away_mk' hfix g b] at hg
    have h2 : algebraMap B (Localization.Away h) (g • b) =
        algebraMap B (Localization.Away h) b := by
      have := congrArg (· * algebraMap B (Localization.Away h) (h ^ N)) hg
      simpa [IsLocalization.mk'_spec, MulSemiringAction.toRingHom_apply, smul_pow,
        hfix] using this
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp h2
    obtain ⟨cv, m, rfl⟩ := c
    exact ⟨m, hc⟩
  choose m hm using key
  cases nonempty_fintype G
  refine ⟨h ^ (Finset.univ.sup m) * b, N + Finset.univ.sup m, fun g => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (Finset.mem_univ g))
    rw [smul_mul', smul_pow, hfix, hk, pow_add, mul_assoc, mul_assoc, hm g]
  · rw [show h ^ (N + Finset.univ.sup m) = h ^ (Finset.univ.sup m) * h ^ N by
      rw [← pow_add, Nat.add_comm]]
    exact IsLocalization.mk'_cancel _ _ _ ▸ rfl

section FixedSubalgebra

variable (R : Type u) [CommRing R] [Algebra R B] [SMulCommClass G R B]

theorem Submonoid.powers_le_comap_algebraMap (h : FixedPoints.subalgebra R B G) :
    Submonoid.powers h ≤ (Submonoid.powers (h : B)).comap
      (algebraMap (FixedPoints.subalgebra R B G) B) := by
  rintro x ⟨n, rfl⟩
  exact Submonoid.mem_comap.mpr ⟨n, by rw [map_pow]; rfl⟩

/-- The localization at `h` of the inclusion of the fixed subalgebra is injective
(T-Q3c(i)). -/
theorem fixedPoints_awayMap_injective (h : FixedPoints.subalgebra R B G) :
    Function.Injective (IsLocalization.map (Localization.Away (h : B))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R h) :
        Localization.Away h →+* Localization.Away (h : B)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := hx
  obtain ⟨cv, k, rfl⟩ := c
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨h ^ k, k, rfl⟩, Subtype.ext ?_⟩
  simpa using hc

end FixedSubalgebra
