import ModularCurves.EllipticCurve.AdditionChartCover

/-!
# The regularity opens on a chart-product piece (T-W7.0c-c5β, c4.1)

Transporting `regularityOpen` (7ba4314e) through `chartPieceIso` (bb5c86d9) gives, on each
`(i,j)` chart-product piece of `E ×_R E`, the open where the corresponding Bosma–Lenstra law is
regular. These are the pieces of `blOpenY` / `blOpenZ`; the global opens are their supremum over
`(i,j)` along the chart-product cover (c4.2).

Over a Jacobson domain (the universal atlas) both laws land on the curve there (β2b), each
`D(t_k)` carries the chart morphism (β3), the two laws agree where both are regular (β4(b)), and
a single law's `k`- and `l`-pieces agree (`chartι_comp_specMap_chartAwayHom_eq`, 3166d104). So
these opens are exactly the domains on which `addOnY` / `addOnZ` are about to be glued.
-/

open AlgebraicGeometry CategoryTheory ModularCurves

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

/-- The regularity open of the second Bosma–Lenstra law on the `(i,j)` chart-product piece. -/
noncomputable def blOpenYPiece :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ regularityOpen (lawTwoTriple W i j)

/-- The regularity open of mathlib's addition law (law 1) on the `(i,j)` chart-product piece. -/
noncomputable def blOpenZPiece :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ regularityOpen (lawOneTriple W i j)

/-- The three `D(t_k)` cover the law-2 regularity open, by construction. -/
lemma blOpenYPiece_eq_iSup :
    blOpenYPiece W i j =
      ⨆ k, (chartPieceIso W i j).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (lawTwoTriple W i j k) := by
  rw [blOpenYPiece, regularityOpen]
  exact TopologicalSpace.Opens.map_iSup _ _

/-- The three `D(s_k)` cover the law-1 regularity open, by construction. -/
lemma blOpenZPiece_eq_iSup :
    blOpenZPiece W i j =
      ⨆ k, (chartPieceIso W i j).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (lawOneTriple W i j k) := by
  rw [blOpenZPiece, regularityOpen]
  exact TopologicalSpace.Opens.map_iSup _ _

/-- The three `D(t_k)` as opens of the `(i,j)` piece — the cover of `blOpenYPiece`. -/
noncomputable def blOpenYPieceFamily (k : Fin 3) :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (lawTwoTriple W i j k)

/-- The three `D(s_k)` as opens of the `(i,j)` piece — the cover of `blOpenZPiece`. -/
noncomputable def blOpenZPieceFamily (k : Fin 3) :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (lawOneTriple W i j k)

lemma iSup_blOpenYPieceFamily : ⨆ k, blOpenYPieceFamily W i j k = blOpenYPiece W i j :=
  (blOpenYPiece_eq_iSup W i j).symm

lemma iSup_blOpenZPieceFamily : ⨆ k, blOpenZPieceFamily W i j k = blOpenZPiece W i j :=
  (blOpenZPiece_eq_iSup W i j).symm

/-- **(c4.2b)** The open cover of `blOpenYPiece` by the three `D(t_k)`, via mathlib's
`Scheme.Opens.iSupOpenCover` transported along `iSup_blOpenYPieceFamily`. -/
noncomputable def blOpenYPieceCover :
    (blOpenYPiece W i j).toScheme.OpenCover :=
  (iSup_blOpenYPieceFamily W i j) ▸ Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j)

/-- **(c4.2b)** The open cover of `blOpenZPiece` by the three `D(s_k)`. -/
noncomputable def blOpenZPieceCover :
    (blOpenZPiece W i j).toScheme.OpenCover :=
  (iSup_blOpenZPieceFamily W i j) ▸ Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j)

end WeierstrassCurve.Projective
