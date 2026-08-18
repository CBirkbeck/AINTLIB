/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Roots of unity descend to an integrally closed ring (WP-A7.2)

Route A's remaining input is a root of unity on the trivialising cover, and the plan sources
it from the **universal** object: construct the root over the fraction field of the universal
moduli ring (where Galois descent applies), then observe that it automatically lies in the
ring itself.

That last step is this file's lemma, and it is general-purpose: an `N`-th root of unity in
the fraction field of an integrally closed domain is a root of the monic `X ^ N - 1`, hence
integral, hence in the ring.
-/

universe u v

namespace ModularCurves

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.2)** A root of unity in the fraction field of an integrally closed domain
comes from the ring: it is a root of the monic polynomial `X ^ N - 1`, hence integral. -/
theorem exists_algebraMap_eq_of_pow_eq_one {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] {x : K} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ∃ a : A, algebraMap A K a = x := by
  have hint : IsIntegral A x := by
    refine ⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hN, ?_⟩
    simp [hx]
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.2, bundled)** The ring element produced by
`exists_algebraMap_eq_of_pow_eq_one` is itself an `N`-th root of unity. -/
theorem pow_eq_one_of_algebraMap_eq {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {x : K} {N : ℕ} {a : A} (ha : algebraMap A K a = x) (hx : x ^ N = 1) :
    a ^ N = 1 := by
  have h : algebraMap A K (a ^ N) = algebraMap A K 1 := by
    rw [map_pow, ha, hx, map_one]
  exact IsFractionRing.injective A K h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.2, primitivity)** …and it has the *same order*: a root of unity descending from
the fraction field is primitive in the ring exactly when it is primitive in the field.

This is what replaces the clopen primitive-root-locus argument on the scheme side. The
nondegeneracy of the field-level Weil pairing gives primitivity at the generic point; because
`A ↪ K` is injective, no separate argument is needed downstairs. -/
theorem pow_ne_one_of_algebraMap_eq {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {x : K} {a : A} {k : ℕ} (ha : algebraMap A K a = x) (hx : x ^ k ≠ 1) :
    a ^ k ≠ 1 := by
  intro h
  exact hx (by rw [← ha, ← map_pow, h, map_one])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(WP-A7.2, packaged — the form WP-D3d consumes)** A root of unity in the fraction field of an
integrally closed domain descends to one in the ring, **bundled**: the subtype element
`{ a : A // a ^ N = 1 }` that `nonempty_weilPairing_of_cover_of_values` wants for `ζ`. -/
noncomputable def rootOfUnityDescend {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    {N : ℕ} (hN : N ≠ 0) (x : { u : K // u ^ N = 1 }) : { a : A // a ^ N = 1 } :=
  ⟨(exists_algebraMap_eq_of_pow_eq_one hN x.2).choose,
    pow_eq_one_of_algebraMap_eq (exists_algebraMap_eq_of_pow_eq_one hN x.2).choose_spec x.2⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- …and it does map to the given root of unity. -/
theorem algebraMap_rootOfUnityDescend {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    {N : ℕ} (hN : N ≠ 0) (x : { u : K // u ^ N = 1 }) :
    algebraMap A K (rootOfUnityDescend hN x).1 = (x : K) :=
  (exists_algebraMap_eq_of_pow_eq_one hN x.2).choose_spec

/- The primitivity companion is `pow_ne_one_of_algebraMap_eq` above, composed with
`algebraMap_rootOfUnityDescend` at the use site: from `(x : K) ^ k ≠ 1` it gives
`(rootOfUnityDescend hN x).1 ^ k ≠ 1`. Stating that as its own lemma here makes the elaborator unify
`A` with `ℕ` (it reports `failed to synthesize CommRing ℕ`), so it is left to the caller. -/

end ModularCurves
