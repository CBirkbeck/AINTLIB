/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Algebra
import «Adic spaces».Presheaf
import «Adic spaces».RelativePieceKeystone

/-!
# The small perturbation lemma ([WP] §6.3, lem:small-perturbation)

Source ([WP] lines 949–966): "Let `(E,E⁺)` be a complete Tate Huber pair and choose a
closed ring of definition `E₀ ⊆ E⁺`.  Let `α=(f_1,…,f_m;g)` be a rational datum whose
entries lie in `E₀`. … Suppose that for some `ℓ ≥ 0` there are `a_0,…,a_m ∈ E₀` with
`ϖ^ℓ = ∑ a_j d_j`.  Let `d_j' ∈ E₀` satisfy `d_j' − d_j ∈ ϖ^{ℓ+1}E₀`.  Then `α'` is a
rational datum, `α` and `α'` define the same rational subset of `Spa(E,E⁺)`, and their
completed rational localizations are canonically isomorphic."

Formalization scope (documented specialization): stated for a complete NORMED
ultrametric Tate ring with a norm-scaling pseudouniformizer (the FJP `(t, htu, ht1,
ht0, hscale)` bundle) — `E₀` is the unit ball; this covers every use in this project.
The setup is bundled in `PerturbSetup`.  Because covering data arrive with arbitrary
pairs of definition, this file also states pod-independence of `presheafValue`
(search first: `CompletionModelIndependence.lean` / `PresheafIdentification.lean`).
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] [ValuationSpectrum.PlusSubring E]

/-- Pod-independence of the completed rational localization for Tate rings: two data
with the same `(T, s)` have canonically isomorphic presheaf values.  (Any two rings of
definition of a Tate ring are commensurable; search first —
`CompletionModelIndependence` provides the global case.) -/
noncomputable def podCongrEquiv (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : presheafValue D ≃+* presheafValue D' := by sorry

theorem podCongrEquiv_continuous (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : Continuous (podCongrEquiv D D' hT hs) := by sorry

theorem podCongrEquiv_symm_continuous (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : Continuous (podCongrEquiv D D' hT hs).symm := by sorry

theorem podCongrEquiv_canonicalMap (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) (x : E) :
    podCongrEquiv D D' hT hs (D.canonicalMap x) = D'.canonicalMap x := by sorry

/-- The bundled data of a small perturbation of a rational datum
([WP] lem:small-perturbation): a norm-scaling pseudouniformizer `t`, a rational datum
`D` with unit-ball entries and the redundant `s ∈ T` coordinate, an integral Bezout
relation `∑_{x ∈ T} a_x·x = t^ℓ` with unit-ball coefficients, and a perturbation
`pert` moving each entry by at most `‖t‖^{ℓ+1}`. -/
structure PerturbSetup (E : Type*) [NormedCommRing E] [IsUltrametricDist E]
    [NormOneClass E] : Type _ where
  /-- The pseudouniformizer. -/
  t : E
  htu : IsUnit t
  ht1 : ‖t‖ < 1
  ht0 : 0 < ‖t‖
  hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖
  /-- The rational datum being perturbed. -/
  D : RationalLocData E
  hsT : D.s ∈ D.T
  hT1 : ∀ x ∈ D.T, ‖x‖ ≤ 1
  /-- The Bezout level ([WP] eq:integral-bezout). -/
  ℓ : ℕ
  /-- The Bezout coefficients. -/
  a : E → E
  ha1 : ∀ x, ‖a x‖ ≤ 1
  hbez : ∑ x ∈ D.T, a x * x = t ^ ℓ
  /-- The perturbation of the entries. -/
  pert : E → E
  hpert1 : ∀ x ∈ D.T, ‖pert x‖ ≤ 1
  hpert : ∀ x ∈ D.T, ‖pert x - x‖ ≤ ‖t‖ ^ (ℓ + 1)

namespace PerturbSetup

variable [DecidableEq E]

/-- The perturbed rational datum `α'` ([WP] lem:small-perturbation), with the
unit-ball pair of definition. -/
noncomputable def datum (S : PerturbSetup E) : RationalLocData E := by
  have := S; sorry

theorem datum_T (S : PerturbSetup E) : S.datum.T = S.D.T.image S.pert := by sorry

theorem datum_s (S : PerturbSetup E) : S.datum.s = S.pert S.D.s := by sorry

/-- The perturbed datum is rational ([WP]: "`α'` is a rational datum" — the primed
integral Bezout relation `∑ a_j d_j' = ϖ^ℓ(1 + ϖH)` with `1 + ϖH` a unit of `E₀`). -/
theorem datum_isRational (S : PerturbSetup E) : S.datum.IsRational := by sorry

/-- Perturbation does not change the rational subset ([WP]: "`α` and `α'` define the
same rational subset of `Spa(E,E⁺)`" — at every point of the subset
`|ϖ|^ℓ ≤ |g(x)|`, and the perturbations have value `≤ |ϖ|^{ℓ+1} < |g(x)|`). -/
theorem rationalOpen_datum (S : PerturbSetup E) :
    rationalOpen S.datum.T S.datum.s = rationalOpen S.D.T S.D.s := by sorry

/-- **The canonical isomorphism of completed localizations** ([WP]
lem:small-perturbation: "their completed rational localizations are canonically
isomorphic" — `g'/g` is a 1-unit with power-bounded inverse; both universal-property
maps exist and are mutually inverse). -/
noncomputable def equiv (S : PerturbSetup E) :
    presheafValue S.D ≃+* presheafValue S.datum := by sorry

theorem equiv_continuous (S : PerturbSetup E) : Continuous S.equiv := by sorry

theorem equiv_symm_continuous (S : PerturbSetup E) : Continuous S.equiv.symm := by sorry

/-- The perturbation isomorphism commutes with the canonical maps from `E`
("Both composites restrict to the identity on `E`"). -/
theorem equiv_canonicalMap (S : PerturbSetup E) (x : E) :
    S.equiv (S.D.canonicalMap x) = S.datum.canonicalMap x := by sorry

end PerturbSetup

/-- Existence of an integral Bezout relation for a rational datum in a normed Tate
ring ([WP] cor:finite-head-presentation, first step: "Choose an integral Bezout
relation `ϖ^ℓ = ∑ a_j d_j, a_j ∈ 𝒜₀`"). -/
theorem exists_integral_bezout (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (D : RationalLocData E) (hD : D.IsRational) (hT1 : ∀ x ∈ D.T, ‖x‖ ≤ 1) :
    ∃ (ℓ : ℕ) (a : E → E), (∀ x, ‖a x‖ ≤ 1) ∧ ∑ x ∈ D.T, a x * x = t ^ ℓ := by sorry

end WeightedParity
