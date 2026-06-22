/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.FractionRing
import HasseWeil.Curves.Infinity
import HasseWeil.Curves.Valuation

/-!
# Adic-valuation transport under ring equivalences

This file proves that a ring equivalence between Dedekind domains transports height-one
prime ideals and their adic valuations. The main algebraic result is
`valuation_map_ringEquiv`; the later lemmas record coordinate-ring and curve-cast transport
facts used by Weil-pairing Galois descent.
-/

open IsDedekindDomain

namespace HasseWeil.WeilPairing

variable {R R' : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [CommRing R'] [IsDomain R'] [IsDedekindDomain R']

section IdealTransport

/-- `Ideal.map Φ` preserves `≤` both ways for a ring iso (it is an order isomorphism). -/
theorem map_le_map_iff_ringEquiv (Φ : R ≃+* R') (A B : Ideal R) :
    Ideal.map Φ.toRingHom A ≤ Ideal.map Φ.toRingHom B ↔ A ≤ B := by
  constructor
  · intro h
    have h2 := Ideal.comap_mono (f := Φ.toRingHom) h
    rwa [Ideal.comap_map_of_bijective Φ.toRingHom (EquivLike.bijective Φ),
      Ideal.comap_map_of_bijective Φ.toRingHom (EquivLike.bijective Φ)] at h2
  · exact Ideal.map_mono

/-- `Ideal.map Φ p` is prime for a ring iso `Φ` and prime `p`. -/
theorem map_prime_ringEquiv (Φ : R ≃+* R') (p : Ideal R) (hp : Prime p) :
    Prime (Ideal.map Φ.toRingHom p) := by
  have hpI : p.IsPrime := (Ideal.prime_iff_isPrime hp.ne_zero).mp hp
  have hmap : (Ideal.map Φ.toRingHom p).IsPrime := Ideal.map_isPrime_of_equiv Φ
  rw [Ideal.prime_iff_isPrime]
  · exact hmap
  · intro h
    have hbot : p = ⊥ := by
      have hle : Ideal.map Φ.toRingHom p ≤ Ideal.map Φ.toRingHom ⊥ := by
        rw [Ideal.map_bot]; exact le_of_eq h
      exact le_antisymm ((map_le_map_iff_ringEquiv Φ p ⊥).mp hle) bot_le
    exact hp.ne_zero hbot

/-- `Ideal.map Φ I` is nonzero for a ring iso `Φ` and `I ≠ ⊥`. -/
theorem map_ne_bot_ringEquiv (Φ : R ≃+* R') (I : Ideal R) (hI : I ≠ ⊥) :
    Ideal.map Φ.toRingHom I ≠ ⊥ := by
  intro h
  apply hI
  have hle : Ideal.map Φ.toRingHom I ≤ Ideal.map Φ.toRingHom ⊥ := by
    rw [Ideal.map_bot]; exact le_of_eq h
  exact le_antisymm ((map_le_map_iff_ringEquiv Φ I ⊥).mp hle) bot_le

/-- The divisibility `A ∣ B` transports under the ring iso `Φ` via `Ideal.mapHom`, both
ways. -/
theorem map_dvd_iff_ringEquiv (Φ : R ≃+* R') (A B : Ideal R) :
    Ideal.map Φ.toRingHom A ∣ Ideal.map Φ.toRingHom B ↔ A ∣ B := by
  have hcomp : Φ.symm.toRingHom.comp Φ.toRingHom = RingHom.id R := by
    ext x
    simp
  constructor
  · intro h
    have h2 := map_dvd (Ideal.mapHom Φ.symm.toRingHom) h
    simp only [Ideal.mapHom_apply, Ideal.map_map, hcomp, Ideal.map_id] at h2
    exact h2
  · intro h
    have h2 := map_dvd (Ideal.mapHom Φ.toRingHom) h
    simpa only [Ideal.mapHom_apply] using h2

/-- The prime-power divisibility `p ^ n ∣ I` transports under the ring iso `Φ`. -/
theorem pow_dvd_iff_map_ringEquiv (Φ : R ≃+* R') (p I : Ideal R) (n : ℕ) :
    Ideal.map Φ.toRingHom p ^ n ∣ Ideal.map Φ.toRingHom I ↔ p ^ n ∣ I := by
  rw [← Ideal.map_pow]
  exact map_dvd_iff_ringEquiv Φ (p ^ n) I

/-- Multiplicity is preserved by the ideal-lattice isomorphism `Ideal.map Φ`: the
`Associates` count of `p` in the factorization of `I` equals the count of `Φ(p)` in
`Φ(I)`. -/
theorem count_map_ringEquiv (Φ : R ≃+* R') (p I : Ideal R) (hp : Prime p) (hI : I ≠ ⊥) :
    (Associates.mk (Ideal.map Φ.toRingHom p)).count
        (Associates.mk (Ideal.map Φ.toRingHom I)).factors =
      (Associates.mk p).count (Associates.mk I).factors := by
  classical
  have hpmap : Prime (Ideal.map Φ.toRingHom p) := map_prime_ringEquiv Φ p hp
  have hImap_ne : Ideal.map Φ.toRingHom I ≠ ⊥ := map_ne_bot_ringEquiv Φ I hI
  have hpirr : Irreducible (Associates.mk (Ideal.map Φ.toRingHom p)) :=
    Associates.irreducible_mk.mpr hpmap.irreducible
  have hpirr0 : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
  have hImap0 : Associates.mk (Ideal.map Φ.toRingHom I) ≠ 0 := Associates.mk_ne_zero.mpr hImap_ne
  have hI0 : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI
  -- Both counts satisfy the same `n ≤ ·` characterisation via `prime_pow_dvd_iff_le`.
  have key : ∀ n : ℕ,
      n ≤ (Associates.mk (Ideal.map Φ.toRingHom p)).count
          (Associates.mk (Ideal.map Φ.toRingHom I)).factors ↔
        n ≤ (Associates.mk p).count (Associates.mk I).factors := by
    intro n
    rw [← Associates.prime_pow_dvd_iff_le hImap0 hpirr,
      ← Associates.prime_pow_dvd_iff_le hI0 hpirr0,
      ← Associates.mk_pow, ← Associates.mk_pow,
      Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd]
    exact pow_dvd_iff_map_ringEquiv Φ p I n
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end IdealTransport

section ValuationTransport

/-- The integer adic valuation transports under a ring iso `Φ`: for height-one primes with
`vQ.asIdeal = Ideal.map Φ vP.asIdeal`, `vQ.intValuation (Φ r) = vP.intValuation r`. -/
theorem intValuation_map_ringEquiv (Φ : R ≃+* R')
    (vP : HeightOneSpectrum R) (vQ : HeightOneSpectrum R')
    (hPQ : vQ.asIdeal = Ideal.map Φ.toRingHom vP.asIdeal) (r : R) :
    vQ.intValuation (Φ r) = vP.intValuation r := by
  classical
  by_cases hr : r = 0
  · subst hr
    simp [map_zero]
  · have hΦr : Φ r ≠ 0 := by
      simpa using (map_ne_zero_iff Φ.toRingHom (EquivLike.injective Φ)).mpr hr
    rw [HeightOneSpectrum.intValuation_if_neg _ hΦr,
      HeightOneSpectrum.intValuation_if_neg _ hr, hPQ]
    have hspan : Ideal.span {Φ r} = Ideal.map Φ.toRingHom (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]; rfl
    rw [hspan, count_map_ringEquiv Φ vP.asIdeal (Ideal.span {r})
      ((Ideal.prime_iff_isPrime vP.ne_bot).mpr vP.isPrime)
      (by simpa [Ideal.span_singleton_eq_bot] using hr)]

/-- The fraction-field adic valuation transports on `algebraMap r` (the building block). -/
theorem valuation_map_ringEquiv_algebraMap {K K' : Type*} [Field K] [Field K']
    [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']
    (Φ : R ≃+* R') (vP : HeightOneSpectrum R) (vQ : HeightOneSpectrum R')
    (hPQ : vQ.asIdeal = Ideal.map Φ.toRingHom vP.asIdeal) (r : R) :
    vQ.valuation K' (IsFractionRing.ringEquivOfRingEquiv Φ (algebraMap R K r)) =
      vP.valuation K (algebraMap R K r) := by
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap Φ r,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact intValuation_map_ringEquiv Φ vP vQ hPQ r

/-- The fraction-field adic valuation transports under a ring iso `Φ` for all `f`
(the divisor-Galois-descent engine): with `σ = ringEquivOfRingEquiv Φ` and
`vQ.asIdeal = Ideal.map Φ vP.asIdeal`, `vQ.valuation K' (σ f) = vP.valuation K f`. -/
theorem valuation_map_ringEquiv {K K' : Type*} [Field K] [Field K']
    [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']
    (Φ : R ≃+* R') (vP : HeightOneSpectrum R) (vQ : HeightOneSpectrum R')
    (hPQ : vQ.asIdeal = Ideal.map Φ.toRingHom vP.asIdeal) (f : K) :
    vQ.valuation K' (IsFractionRing.ringEquivOfRingEquiv Φ f) = vP.valuation K f := by
  obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, Valuation.map_div, Valuation.map_div,
    valuation_map_ringEquiv_algebraMap Φ vP vQ hPQ u,
    valuation_map_ringEquiv_algebraMap Φ vP vQ hPQ v]

end ValuationTransport

open WeierstrassCurve Polynomial

/-- `CoordinateRing.map f` sends `XClass x` to `XClass (f x)` (on the mapped curve). -/
theorem map_XClass {A B : Type*} [CommRing A] [CommRing B] (W' : WeierstrassCurve.Affine A)
    (f : A →+* B) (x : A) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f
        (WeierstrassCurve.Affine.CoordinateRing.XClass W' x) =
      WeierstrassCurve.Affine.CoordinateRing.XClass (W'.map f).toAffine (f x) := by
  rw [WeierstrassCurve.Affine.CoordinateRing.XClass,
    WeierstrassCurve.Affine.CoordinateRing.map_mk]
  congr 1
  simp [Polynomial.map_C, Polynomial.map_sub]

/-- `CoordinateRing.map f` sends `YClass y` to `YClass (y.map f)` (on the mapped curve). -/
theorem map_YClass {A B : Type*} [CommRing A] [CommRing B] (W' : WeierstrassCurve.Affine A)
    (f : A →+* B) (y : A[X]) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f
        (WeierstrassCurve.Affine.CoordinateRing.YClass W' y) =
      WeierstrassCurve.Affine.CoordinateRing.YClass (W'.map f).toAffine (y.map f) := by
  rw [WeierstrassCurve.Affine.CoordinateRing.YClass,
    WeierstrassCurve.Affine.CoordinateRing.map_mk]
  congr 1
  simp [Polynomial.map_sub]

/-- `CoordinateRing.map f` sends `XYIdeal x y` to `XYIdeal (f x) (y.map f)` on the
mapped curve. -/
theorem map_XYIdeal {A B : Type*} [CommRing A] [CommRing B] (W' : WeierstrassCurve.Affine A)
    (f : A →+* B) (x : A) (y : A[X]) :
    Ideal.map (WeierstrassCurve.Affine.CoordinateRing.map W' f)
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W' x y) =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal (W'.map f).toAffine (f x) (y.map f) := by
  rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal,
    WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.map_span]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, map_XClass, map_YClass]

open HasseWeil.Curves

/-- `pointValuation` transports through a curve-equality `RingEquiv.cast`. -/
theorem pointValuation_ringEquivCast {F : Type*} [Field F] [DecidableEq F]
    (V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂)
    (P₁ : (⟨V₁.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (P₂ : (⟨V₂.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hP : HEq P₁ P₂) (g : V₁.toAffine.FunctionField) :
    (⟨V₂.toAffine⟩ : SmoothPlaneCurve F).pointValuation P₂
        (RingEquiv.cast (R := fun (V : WeierstrassCurve F) ↦ V.toAffine.FunctionField) hV g) =
      (⟨V₁.toAffine⟩ : SmoothPlaneCurve F).pointValuation P₁ g := by
  subst hV
  obtain rfl := eq_of_heq hP
  rfl

/-- `ord_P` transports through a curve-equality `RingEquiv.cast` (additive form of
`pointValuation_ringEquivCast`). -/
theorem ord_P_ringEquivCast {F : Type*} [Field F] [DecidableEq F]
    (V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂)
    (P₁ : (⟨V₁.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (P₂ : (⟨V₂.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hP : HEq P₁ P₂) (g : V₁.toAffine.FunctionField) :
    (⟨V₂.toAffine⟩ : SmoothPlaneCurve F).ord_P P₂
        (RingEquiv.cast (R := fun (V : WeierstrassCurve F) ↦ V.toAffine.FunctionField) hV g) =
      (⟨V₁.toAffine⟩ : SmoothPlaneCurve F).ord_P P₁ g := by
  subst hV
  obtain rfl := eq_of_heq hP
  rfl

/-- Equal affine curves with matching coordinates have heterogeneously-equal smooth points. -/
theorem heq_smoothPoint {F : Type*} [Field F] (W₁ W₂ : WeierstrassCurve.Affine F)
    (hW : W₁ = W₂)
    (P₁ : (⟨W₁⟩ : SmoothPlaneCurve F).SmoothPoint)
    (P₂ : (⟨W₂⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hx : P₁.x = P₂.x) (hy : P₁.y = P₂.y) :
    HEq P₁ P₂ := by
  subst hW
  have : P₁ = P₂ :=
    HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext hx hy
  rw [this]

/-- `ordAtInfty` transports through a curve-equality `RingEquiv.cast`. -/
theorem ordAtInfty_ringEquivCast {F : Type*} [Field F] [DecidableEq F]
    (V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂)
    (g : V₁.toAffine.FunctionField) :
    (⟨V₂.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty
        (RingEquiv.cast (R := fun (V : WeierstrassCurve F) ↦ V.toAffine.FunctionField) hV g) =
      (⟨V₁.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty g := by
  subst hV
  rfl

end HasseWeil.WeilPairing
