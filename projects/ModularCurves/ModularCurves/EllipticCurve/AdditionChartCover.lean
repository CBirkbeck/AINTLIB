/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartMor

/-!
# The regularity open of an addition law on a chart-product (T-W7.0c-c5β, β3 cover)

A projective triple `t : Fin 3 → A` is regular exactly where some coordinate is invertible: the
open `regularityOpen t := ⨆ k, D(t k) ⊆ Spec A`. The three `D(t k)` cover it by construction,
and `regularityOpen t = ⊤` precisely when the coordinates generate the unit ideal
(`PrimeSpectrum.iSup_basicOpen_eq_top_iff`) — which for a Bosma–Lenstra law is FALSE on the whole
chart-product (a single (2,2) law always has a nonempty exceptional divisor, B–L Thm 1) and is
exactly why two laws are needed.

For law 2 on the `(i,j)` chart-product this open is the piece's contribution to `blOpenY`; for
law 1, to `blOpenZ`. Each `D(t k)` carries the morphism `addOn{Y,Z}PieceMor` (f1dd27ad); β4 glues
them over `k` (via the six certified minors) and over `(i,j)` (dehomogenisation compatibility).

`regularityOpen_law_ne_top_of_exceptional` records the sharp form of "one law never suffices":
if the triple has a common zero (a point of the exceptional divisor), the open is not everything.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.Projective

variable {A : Type*} [CommRing A]

/-- The regularity open of a projective triple: where some coordinate is invertible. -/
def regularityOpen (t : Fin 3 → A) : TopologicalSpace.Opens (PrimeSpectrum A) :=
  ⨆ k, PrimeSpectrum.basicOpen (t k)

lemma basicOpen_le_regularityOpen (t : Fin 3 → A) (k : Fin 3) :
    PrimeSpectrum.basicOpen (t k) ≤ regularityOpen t :=
  le_iSup (fun k => PrimeSpectrum.basicOpen (t k)) k

/-- The three basic opens cover the regularity open, by construction. -/
lemma iSup_basicOpen_eq_regularityOpen (t : Fin 3 → A) :
    (⨆ k, PrimeSpectrum.basicOpen (t k)) = regularityOpen t := rfl

/-- The regularity open is everything exactly when the coordinates generate the unit ideal. -/
lemma regularityOpen_eq_top_iff (t : Fin 3 → A) :
    regularityOpen t = ⊤ ↔ Ideal.span (Set.range t) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff

/-- **(c2 core, joint cover ↔ joint-unit-ideal)** The two regularity opens of triples `t`, `s` cover
`Spec A` exactly when the six coordinates *jointly* generate the unit ideal. The two-law analogue of
`regularityOpen_eq_top_iff` — the ⊔ of the two `⨆ basicOpen` families is a single `⨆` over `t ⊕ s`.
This is what reduces `blOpenZ ⊔ blOpenY = ⊤` (the two Bosma–Lenstra laws cover `E × E`, T-W7.0c·c2)
to `span (range lawOneTriple ∪ range lawTwoTriple) = ⊤` per chart-product. -/
lemma regularityOpen_sup_eq_top_iff (t s : Fin 3 → A) :
    regularityOpen t ⊔ regularityOpen s = ⊤ ↔
      Ideal.span (Set.range t ∪ Set.range s) = ⊤ := by
  have h : regularityOpen t ⊔ regularityOpen s = ⨆ x : Fin 3 ⊕ Fin 3,
      PrimeSpectrum.basicOpen (Sum.elim t s x) := by
    rw [regularityOpen, regularityOpen, iSup_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h, PrimeSpectrum.iSup_basicOpen_eq_top_iff, Set.Sum.elim_range]

/-- **The reason two laws are needed.** If the triple has a common zero — a point of its
exceptional divisor, which every bidegree-`(2,2)` addition law has (B–L Thm 1) — then its
regularity open is not the whole chart-product. -/
lemma regularityOpen_ne_top_of_forall_mem (t : Fin 3 → A) (p : PrimeSpectrum A)
    (hp : ∀ k, t k ∈ p.asIdeal) : regularityOpen t ≠ ⊤ := by
  intro htop
  rw [regularityOpen_eq_top_iff, Ideal.eq_top_iff_one] at htop
  have hle : Ideal.span (Set.range t) ≤ p.asIdeal :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hp)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hle htop))

/-- **(c3, the cross-law overlap is same-index)** For two triples `t`, `s` with vanishing `2×2`
minors
(`s m * t n = s n * t m`), the overlap of their regularity opens is covered by the **same-index**
loci
`D(t k · s k)`. The `⊇` half is `basicOpen_mul`; the `⊆` half is the minor argument: a prime `p`
avoiding
`t k` and `s l` also avoids `s k` (since `s k · t l = s l · t k ∉ p`), hence avoids `t k · s k`.
This is
why `addOn_agree` reduces to the same-index piece agreement (`isUnit_of_minor` at the point level).
-/
lemma regularityOpen_inf_eq_iSup_basicOpen (t s : Fin 3 → A)
    (hmin : ∀ m n, s m * t n = s n * t m) :
    regularityOpen t ⊓ regularityOpen s =
      ⨆ k, PrimeSpectrum.basicOpen (t k * s k) := by
  apply le_antisymm
  · rintro p ⟨hpt, hps⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hpt
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hps
    rw [PrimeSpectrum.mem_basicOpen] at hk hl
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨k, ?_⟩
    rw [PrimeSpectrum.mem_basicOpen]
    have hlk : s l * t k ∈ p.asIdeal.primeCompl := mul_mem hl hk
    rw [← hmin k l] at hlk
    have hsk : s k ∈ p.asIdeal.primeCompl := fun h => hlk (Ideal.mul_mem_right _ _ h)
    exact mul_mem hk hsk
  · refine iSup_le fun k => ?_
    rw [PrimeSpectrum.basicOpen_mul]
    exact le_inf (le_trans inf_le_left (basicOpen_le_regularityOpen t k))
      (le_trans inf_le_right (basicOpen_le_regularityOpen s k))

end WeierstrassCurve.Projective
