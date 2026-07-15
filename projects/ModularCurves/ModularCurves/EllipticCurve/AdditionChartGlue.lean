/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartAgree
import ModularCurves.EllipticCurve.AdditionChartHom

/-!
# Proportional triples define the same chart morphism (T-W7.0c-c5β, β4(b))

The gluing input. Two projective triples with vanishing `2 × 2` minors define the *same* chart
morphism wherever both are regular:

* `ratio_eq_of_minor` — the minors force the ratios to agree: `s m / s k = t m / t k`. No
  cancellation is needed; the identity `s m * v = t m * u` follows by rewriting with the two
  unit witnesses and one minor.
* `isUnit_of_minor` — on `D(t k) ⊓ D(s l)` the coordinate `s k` is automatically invertible
  (its product with `t l` is the unit `s l * t k`), so both triples are regular *at the same
  index* there. This is why the overlap is covered by the same-index pieces.
* `chartHomOfTriple_congr` — chart morphisms depend on a triple only through its ratios.

Applied to `lawOneTriple` / `lawTwoTriple` — whose minors are `lawOneTriple_mul_lawTwoTriple`
(389c933f, the six certified minors) — this says `addOnZPieceHom` and `addOnYPieceHom` agree on
the overlap of the two regularity opens: the two Bosma–Lenstra laws glue.
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type*} [CommRing S] [Algebra R S]

/-- **(β4(b))** Vanishing minors force the ratios to agree: if `t k` and `s k` are invertible
(witnesses `u`, `v`) and `s m * t k = s k * t m`, then `s m * v = t m * u`. -/
lemma ratio_eq_of_minor (t s : Fin 3 → S) (u v : S) (k m : Fin 3)
    (hu : t k * u = 1) (hv : s k * v = 1) (hmin : s m * t k = s k * t m) :
    s m * v = t m * u := by
  calc s m * v = s m * v * (t k * u) := by rw [hu, mul_one]
    _ = s m * t k * (v * u) := by ring
    _ = s k * t m * (v * u) := by rw [hmin]
    _ = s k * v * (t m * u) := by ring
    _ = t m * u := by rw [hv, one_mul]

/-- **(β4(b))** On `D(t k) ⊓ D(s l)` the coordinate `s k` is invertible too: its product with
`t l` is the unit `s l * t k`. Hence the two triples are regular at the *same* index there. -/
lemma isUnit_of_minor (t s : Fin 3 → S) (k l : Fin 3) (ht : IsUnit (t k)) (hs : IsUnit (s l))
    (hmin : s k * t l = s l * t k) : IsUnit (s k) := by
  refine isUnit_of_mul_isUnit_left (y := t l) ?_
  rw [hmin]
  exact hs.mul ht

/-- **(β4(b))** A chart morphism depends on its triple only through the ratios: proportional
triples give the same morphism. -/
lemma chartHomOfTriple_congr (k : Fin 3) (t s : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : s k * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hs : (W.map (algebraMap R S)).toProjective.Equation s)
    (h : ∀ m, s m * v = t m * u) :
    chartHomOfTriple W k s v hv hs = chartHomOfTriple W k t u hu ht := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun m => ?_)
  show chartHomOfTriple W k s v hv hs (Ideal.Quotient.mk _ (X m)) =
    chartHomOfTriple W k t u hu ht (Ideal.Quotient.mk _ (X m))
  rw [chartHomOfTriple_coord, chartHomOfTriple_coord]
  exact h m

/-- **(β4(b), the two laws glue)** Wherever both Bosma–Lenstra laws are regular at index `k`,
they define the same chart morphism — the minors (`lawOneTriple_mul_lawTwoTriple`) say exactly
that their ratios agree. -/
theorem chartHomOfTriple_lawOne_eq_lawTwo (i j k : Fin 3) (u v : S)
    (φ : biChartRing W i j →+* S)
    (t s : Fin 3 → S) (hts : ∀ m, t m = φ (lawTwoTriple W i j m))
    (hss : ∀ m, s m = φ (lawOneTriple W i j m))
    (hu : t k * u = 1) (hv : s k * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hs : (W.map (algebraMap R S)).toProjective.Equation s) :
    chartHomOfTriple W k s v hv hs = chartHomOfTriple W k t u hu ht := by
  refine chartHomOfTriple_congr W k t s u v hu hv ht hs fun m => ?_
  refine ratio_eq_of_minor t s u v k m hu hv ?_
  rw [hss, hss, hts, hts, ← map_mul, ← map_mul]
  exact congrArg φ (lawOneTriple_mul_lawTwoTriple W i j m k)

/-- **(β4(b), the two laws glue — `Away`-chart form)** The `chartAway` presentation of
`chartHomOfTriple_lawOne_eq_lawTwo`: wherever both laws are regular at index `k`, they induce the
same `chartAway W k`-algebra map. Post-composing the `chartHomOfTriple` agreement with
`chartCoordAlgEquiv⁻¹` (the presentation `Proj.awayι` consumes). This is the ring-level input the
scheme-level `addOn_agree` (the two Bosma–Lenstra laws agree on `blOpenZ ⊓ blOpenY`) consumes on
each same-index overlap piece. -/
theorem chartAwayHomOfTriple_lawOne_eq_lawTwo (i j k : Fin 3) (u v : S)
    (φ : biChartRing W i j →+* S)
    (t s : Fin 3 → S) (hts : ∀ m, t m = φ (lawTwoTriple W i j m))
    (hss : ∀ m, s m = φ (lawOneTriple W i j m))
    (hu : t k * u = 1) (hv : s k * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hs : (W.map (algebraMap R S)).toProjective.Equation s) :
    chartAwayHomOfTriple W k s v hv hs = chartAwayHomOfTriple W k t u hu ht :=
  congrArg (·.comp (chartCoordAlgEquiv W k).symm.toAlgHom)
    (chartHomOfTriple_lawOne_eq_lawTwo W i j k u v φ t s hts hss hu hv ht hs)

/-- **(β4(b), general form)** Two triples `s`, `t` in `S`, regular at index `k` (witnesses `v`,
`u`), whose `2×2` minors vanish (`s m * t k = s k * t m` for all `m`), induce the same chart
morphism. The minor hypothesis is exactly what `ratio_eq_of_minor` needs;
`chartHomOfTriple_lawOne_eq_lawTwo` is the `lawOne`/`lawTwo` instance. -/
theorem chartHomOfTriple_cross_eq (k : Fin 3) (u v : S) (t s : Fin 3 → S)
    (hmin : ∀ m, s m * t k = s k * t m) (hu : t k * u = 1) (hv : s k * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hs : (W.map (algebraMap R S)).toProjective.Equation s) :
    chartHomOfTriple W k s v hv hs = chartHomOfTriple W k t u hu ht :=
  chartHomOfTriple_congr W k t s u v hu hv ht hs
    fun m => ratio_eq_of_minor t s u v k m hu hv (hmin m)

/-- The `chartAway` form of `chartHomOfTriple_cross_eq`. -/
theorem chartAwayHomOfTriple_cross_eq (k : Fin 3) (u v : S) (t s : Fin 3 → S)
    (hmin : ∀ m, s m * t k = s k * t m) (hu : t k * u = 1) (hv : s k * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hs : (W.map (algebraMap R S)).toProjective.Equation s) :
    chartAwayHomOfTriple W k s v hv hs = chartAwayHomOfTriple W k t u hu ht :=
  congrArg (·.comp (chartCoordAlgEquiv W k).symm.toAlgHom)
    (chartHomOfTriple_cross_eq W k u v t s hmin hu hv ht hs)

end WeierstrassCurve.Projective
