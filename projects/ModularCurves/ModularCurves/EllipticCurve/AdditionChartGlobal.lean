import ModularCurves.EllipticCurve.AdditionChartOpen
import ModularCurves.EllipticCurve.AdditionChartTransition

/-!
# The two Bosma–Lenstra laws on `E ×_R E` (T-W7.0c-c5β, c4.3 assembly)

The per-chart-product laws (`addOnYOnSup`, `addOnZOnSup`, f91b91ec) are assembled into morphisms on
opens of `E ×_R E` itself.

**Why four chart-products, not nine.** `E` is covered by its `Y`- and `Z`-charts alone: a point with
`y = z = 0` would be `[1:0:0]`, and the Weierstrass equation forces `x = 0` there, so no such point
lies on the curve. Accordingly the covering chart-products of `E ×_R E` are the four
`(i,j) ∈ {1,2}²`, and those are exactly the pairs whose chart-product ring is known to be a domain
(`instIsDomainBiChartRing{YY,YZ,ZY,ZZ}`, d38f52b9 + 7c9ddc07) — which is what
`equation_lawTwoTriple_of_isDomain` needs. The family is therefore indexed by `Fin 2 × Fin 2`, and
each branch is spelled with a *literal* index so the domain instances fire.

Each piece is transported into `E ×_R E` along `pieceι` (an open immersion) using
`Scheme.Hom.isoImage`. The `iSup` form `⨆ k, blOpenYPieceFamily` is used throughout rather than
`blOpenYPiece`: the two are equal (`iSup_blOpenYPieceFamily`), but `addOnYOnSup` already lives on the
former, and a `▸` transport across that equality would be gratuitous.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

section Opens

/-- The `(i,j)` chart-product's law-2 regularity open, pushed into `E ×_R E`. -/
noncomputable def blOpenYImage (i j : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  pieceι W i j ''ᵁ (⨆ k, blOpenYPieceFamily W i j k)

/-- The `(i,j)` chart-product's law-1 regularity open, pushed into `E ×_R E`. -/
noncomputable def blOpenZImage (i j : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  pieceι W i j ''ᵁ (⨆ k, blOpenZPieceFamily W i j k)

/-- The four covering chart-products, `{Y,Z}²`. The indices are literals so that the
`IsDomain (biChartRing W i j)` instances apply in each branch. -/
noncomputable def blOpenYFamily : Fin 2 × Fin 2 → (pullback (projModelπ W) (projModelπ W)).Opens
  | (0, 0) => blOpenYImage W 1 1
  | (0, 1) => blOpenYImage W 1 2
  | (1, 0) => blOpenYImage W 2 1
  | (1, 1) => blOpenYImage W 2 2

/-- The law-1 analogue of `blOpenYFamily`. -/
noncomputable def blOpenZFamily : Fin 2 × Fin 2 → (pullback (projModelπ W) (projModelπ W)).Opens
  | (0, 0) => blOpenZImage W 1 1
  | (0, 1) => blOpenZImage W 1 2
  | (1, 0) => blOpenZImage W 2 1
  | (1, 1) => blOpenZImage W 2 2

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the second Bosma–Lenstra law on `E ×_R E`. -/
noncomputable def blOpenY : (pullback (projModelπ W) (projModelπ W)).Opens :=
  ⨆ p, blOpenYFamily W p

/-- **(T-W7.0c·c1-Z, the open)** The regularity open of the first Bosma–Lenstra law (mathlib's
`addXYZ`) on `E ×_R E`. -/
noncomputable def blOpenZ : (pullback (projModelπ W) (projModelπ W)).Opens :=
  ⨆ p, blOpenZFamily W p

/-- The cover of `blOpenY` by the four chart-products' regularity opens. -/
noncomputable def blOpenYCover : (blOpenY W).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (blOpenYFamily W)

/-- The cover of `blOpenZ` by the four chart-products' regularity opens. -/
noncomputable def blOpenZCover : (blOpenZ W).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (blOpenZFamily W)

end Opens

section Morphisms

variable [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ)

/-- The law-2 morphism on the image of the `(i,j)` chart-product's regularity open. -/
noncomputable def addOnYOnImage (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    (blOpenYImage W i j).toScheme ⟶ projModel W :=
  (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv ≫
    addOnYOnSup W i j hΔ

/-- The law-1 morphism on the image of the `(i,j)` chart-product's regularity open. -/
noncomputable def addOnZOnImage (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    (blOpenZImage W i j).toScheme ⟶ projModel W :=
  (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv ≫
    addOnZOnSup W i j hΔ

/-- The law-2 morphisms on the four covering chart-products. -/
noncomputable def addOnYFamily : ∀ p : Fin 2 × Fin 2, (blOpenYFamily W p).toScheme ⟶ projModel W
  | (0, 0) => addOnYOnImage W hΔ 1 1
  | (0, 1) => addOnYOnImage W hΔ 1 2
  | (1, 0) => addOnYOnImage W hΔ 2 1
  | (1, 1) => addOnYOnImage W hΔ 2 2

/-- The law-1 morphisms on the four covering chart-products. -/
noncomputable def addOnZFamily : ∀ p : Fin 2 × Fin 2, (blOpenZFamily W p).toScheme ⟶ projModel W
  | (0, 0) => addOnZOnImage W hΔ 1 1
  | (0, 1) => addOnZOnImage W hΔ 1 2
  | (1, 0) => addOnZOnImage W hΔ 2 1
  | (1, 1) => addOnZOnImage W hΔ 2 2

end Morphisms

end WeierstrassCurve.Projective
