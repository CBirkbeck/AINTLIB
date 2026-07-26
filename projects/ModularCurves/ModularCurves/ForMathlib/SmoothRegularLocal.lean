/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.KrullDimQuotientSpan
import ModularCurves.ForMathlib.MvPolynomialMaximalHeight
import ModularCurves.ForMathlib.SmoothCotangentPrincipal

/-!
# A curve smooth over an algebraically closed field has domain local rings (T-SMOOTH-REG)

Assembling the four bricks:

* **brick 2** (`MvPolynomialMaximalHeight`) — a maximal ideal of `k[x_i : i ∈ ι]` has height
  `≥ #ι`;
* **brick 3'** (`KrullDimQuotientSpan`) — cutting by `#σ` equations drops the height of a
  prime by at most `#σ`;
* **brick 4** (`SmoothCotangentPrincipal`) — at a `k`-rational point of a formally smooth
  algebra with `rank Ω ≤ 1`, the maximal ideal satisfies `𝔪 ≤ (x) + 𝔪²`;
* **`ForMathlib/RegularLocalDomain`** — a regular local ring is a domain (Matsumura 14.3).

Together: for `A` standard smooth of relative dimension one over an algebraically closed
field `k`, every localization `A_𝔭` is a **regular local domain**. Geometrically: a smooth
curve over `k̄` is locally irreducible, which is the missing algebraic leaf of
`yRho_geometricallyIrreducible` (`ModularCurve/IrreducibilityScoping.lean`).
-/

universe u

open IsLocalRing

namespace ModularCurves

section Height

/-- **(brick 5a)** At a maximal ideal of a `k`-algebra standard smooth of relative
dimension one (`k` algebraically closed), the height is at least one: pull back to the
polynomial ring of a submersive presentation, where the height is the number of variables
(brick 2), and lose at most the number of relations (brick 3'). -/
theorem one_le_height_of_isMaximal (k : Type u) [Field k] [IsAlgClosed k] {A : Type u}
    [CommRing A] [Algebra k A] [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] : 1 ≤ 𝔪.height := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ :=
    (‹Algebra.IsStandardSmoothOfRelativeDimension 1 k A›).out
  haveI : Finite σ := hσ
  haveI : Finite ι := hι
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype σ := Fintype.ofFinite σ
  -- the presentation surjection and its kernel
  set f : MvPolynomial ι k →+* A := algebraMap P.Ring A with hf
  have hsurj : Function.Surjective f := P.algebraMap_surjective
  have hker : RingHom.ker f = Ideal.span (Set.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  set s : Finset (MvPolynomial ι k) := Finset.image P.relation Finset.univ with hs
  have hspan : Ideal.span (↑s : Set (MvPolynomial ι k)) = RingHom.ker f := by
    rw [hker, hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hscard : s.card ≤ Fintype.card σ := by
    rw [hs]
    simpa using Finset.card_image_le (s := (Finset.univ : Finset σ)) (f := P.relation)
  -- pull `𝔪` back
  set 𝔮 : Ideal (MvPolynomial ι k) := 𝔪.comap f with h𝔮
  haveI : 𝔮.IsMaximal := Ideal.comap_isMaximal_of_surjective f hsurj
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  have hlow : (Fintype.card ι : ℕ∞) ≤ 𝔮.height := card_le_height_of_isMaximal ‹𝔮.IsMaximal›
  have hup : 𝔮.height ≤ 𝔪.height + s.card :=
    height_comap_le_height_add_card_of_surjective f hsurj hspan 𝔪
  -- `#ι = #σ + 1`
  have hcards : Fintype.card σ ≤ Fintype.card ι := Fintype.card_le_of_injective _ P.map_inj
  have hdim' : Fintype.card ι = Fintype.card σ + 1 := by
    have hd : P.dimension = Nat.card ι - Nat.card σ := rfl
    rw [hdim] at hd
    simp only [Nat.card_eq_fintype_card] at hd
    omega
  -- combine
  have hchain : (Fintype.card ι : ℕ∞) ≤ 𝔪.height + (Fintype.card σ : ℕ∞) :=
    le_trans hlow (le_trans hup (by gcongr))
  rw [hdim'] at hchain
  push_cast at hchain
  by_contra hcon
  have hzero : 𝔪.height = 0 := Order.lt_one_iff.mp (not_le.mp hcon)
  rw [hzero, zero_add] at hchain
  have hnat : (Fintype.card σ : ℕ) + 1 ≤ (Fintype.card σ : ℕ) := by exact_mod_cast hchain
  omega

end Height

end ModularCurves
