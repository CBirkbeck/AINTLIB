/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartCover
import ModularCurves.EllipticCurve.AdditionChartOverlap
import ModularCurves.ForMathlib.SpecBasicOpenAway

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

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

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
      ⨆ k,
        (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (lawTwoTriple W i j k) := by
  rw [blOpenYPiece, regularityOpen]
  exact TopologicalSpace.Opens.map_iSup _ _

/-- The three `D(s_k)` cover the law-1 regularity open, by construction. -/
lemma blOpenZPiece_eq_iSup :
    blOpenZPiece W i j =
      ⨆ k,
        (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (lawOneTriple W i j k) := by
  rw [blOpenZPiece, regularityOpen]
  exact TopologicalSpace.Opens.map_iSup _ _

/-- **(c3, the two-law overlap on a chart-product piece is same-index)** The overlap of the two
laws'
regularity opens on the `(i,j)` piece is covered by the SAME-index loci `D(lawTwo_k · lawOne_k)`
— the
piece-level form of `regularityOpen_inf_eq_iSup_basicOpen`
  (the vanishing minors force regularity at the
same index), pushed through the `chartPieceIso` preimage. -/
lemma blOpenYPiece_inf_blOpenZPiece_eq_iSup :
    blOpenYPiece W i j ⊓ blOpenZPiece W i j =
      ⨆ k, (chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k * lawOneTriple W i j k) :=
  (congrArg ((chartPieceIso W i j).hom ⁻¹ᵁ ·)
    (regularityOpen_inf_eq_iSup_basicOpen (lawTwoTriple W i j) (lawOneTriple W i j)
      (fun m n => lawOneTriple_mul_lawTwoTriple W i j m n))).trans
    (TopologicalSpace.Opens.map_iSup _ _)

/-- The three `D(t_k)` as opens of the `(i,j)` piece — the cover of `blOpenYPiece`. -/
noncomputable def blOpenYPieceFamily (k : Fin 3) :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
    (lawTwoTriple W i j k)

/-- The three `D(s_k)` as opens of the `(i,j)` piece — the cover of `blOpenZPiece`. -/
noncomputable def blOpenZPieceFamily (k : Fin 3) :
    (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens :=
  (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
    (lawOneTriple W i j k)

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

section Morphisms

variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

/-- **(c4.2c, per-piece)** The `k`-th piece of `addOnY`, as a morphism out of the open
`D(t_k)` of the chart-product piece: restrict `chartPieceIso` to the basic open, undo
`specBasicOpenIsoAway`, then apply β3's `addOnYPieceMor`. -/
noncomputable def addOnYOnFamily (k : Fin 3) (hΔ : IsUnit W.Δ) :
    (blOpenYPieceFamily W i j k).toScheme ⟶ projModel W :=
  morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
      (lawTwoTriple W i j k)).inv ≫
    addOnYPieceMor W i j k hΔ

/-- **(c4.2c, per-piece)** The `k`-th piece of `addOnZ` (mathlib's addition law). -/
noncomputable def addOnZOnFamily (k : Fin 3) (hΔ : IsUnit W.Δ) :
    (blOpenZPieceFamily W i j k).toScheme ⟶ projModel W :=
  morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
      (lawOneTriple W i j k)).inv ≫
    addOnZPieceMor W i j k hΔ

omit [IsJacobsonRing R] [IsDomain (biChartRing W i j)] in
/-- The intersection of two `D(t_k)` opens of the piece is the `D(t_k · t_l)` open — where BOTH
coordinates are invertible, i.e. exactly the hypotheses of the cross-index crux
`chartι_comp_specMap_chartAwayHom_eq`. -/
lemma blOpenYPieceFamily_inf (k l : Fin 3) :
    blOpenYPieceFamily W i j k ⊓ blOpenYPieceFamily W i j l =
      (chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k * lawTwoTriple W i j l) := by
  rw [blOpenYPieceFamily, blOpenYPieceFamily, specBasicOpen_mul]
  rfl

omit [IsJacobsonRing R] [IsDomain (biChartRing W i j)] in
/-- The law-1 analogue of `blOpenYPieceFamily_inf`. -/
lemma blOpenZPieceFamily_inf (k l : Fin 3) :
    blOpenZPieceFamily W i j k ⊓ blOpenZPieceFamily W i j l =
      (chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawOneTriple W i j k * lawOneTriple W i j l) := by
  rw [blOpenZPieceFamily, blOpenZPieceFamily, specBasicOpen_mul]
  rfl

section Agreement

variable (hΔ : IsUnit W.Δ)

/-- **(c4.2c)** The `k`-th and `l`-th pieces of `addOnY` agree on any open contained in both —
necessarily the `D(t_k · t_l)` locus, where both coordinates are invertible.

Stated with the overlap `Ω` as a parameter (plus the identifying equation `hΩ`) so that the
`≤`-proofs stay irrelevant and no dependent rewriting is needed. After `subst hΩ` this is a bare
application of the general transport lemma `homOfLE_morphismRestrict_agree` (ForMathlib), fed the
ring-level `addOnYPieceMor_agree`.

The transport lemma is stated over *variable* schemes on purpose: rewriting with
`morphismRestrict_homOfLE` directly at this instantiation makes `whnf` unfold `Limits.pullback`,
`MvPolynomial` and the quotient carrier of `biChartRing`, and no heartbeat budget survives that. -/
lemma addOnYOnFamily_agree (k l : Fin 3) (hkl : l ≠ k)
    (Ω : (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens)
    (hk : Ω ≤ (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k))
    (hl : Ω ≤ (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j l))
    (hΩ : Ω = (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j))
        (lawTwoTriple W i j k * lawTwoTriple W i j l)) :
    Scheme.homOfLE _ hk ≫ addOnYOnFamily W i j k hΔ =
      Scheme.homOfLE _ hl ≫ addOnYOnFamily W i j l hΔ := by
  subst hΩ
  have hagree := addOnYPieceMor_agree W i j hΔ k l hkl
  simp only [awayPairRight_toRingHom, awayPairLeft_toRingHom] at hagree
  exact homOfLE_morphismRestrict_agree (CommRingCat.of (biChartRing W i j))
    (chartPieceIso W i j).hom (lawTwoTriple W i j k) (lawTwoTriple W i j l) _ _ hagree

/-- **(c4.2c)** The law-1 analogue of `addOnYOnFamily_agree`. -/
lemma addOnZOnFamily_agree (k l : Fin 3) (hkl : l ≠ k)
    (Ω : (Limits.pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W)).Opens)
    (hk : Ω ≤ (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k))
    (hl : Ω ≤ (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j l))
    (hΩ : Ω = (chartPieceIso W i j).hom ⁻¹ᵁ
      specBasicOpen (CommRingCat.of (biChartRing W i j))
        (lawOneTriple W i j k * lawOneTriple W i j l)) :
    Scheme.homOfLE _ hk ≫ addOnZOnFamily W i j k hΔ =
      Scheme.homOfLE _ hl ≫ addOnZOnFamily W i j l hΔ := by
  subst hΩ
  have hagree := addOnZPieceMor_agree W i j hΔ k l hkl
  simp only [awayPairRight_toRingHom, awayPairLeft_toRingHom] at hagree
  exact homOfLE_morphismRestrict_agree (CommRingCat.of (biChartRing W i j))
    (chartPieceIso W i j).hom (lawOneTriple W i j k) (lawOneTriple W i j l) _ _ hagree

end Agreement

section Glue

open CategoryTheory.Limits

variable (hΔ : IsUnit W.Δ)

/-- Pairwise agreement of the three pieces of `addOnY`, in the shape
`glueMorphisms_hf_of_agree` consumes: on `U k ⊓ U l`, which `blOpenYPieceFamily_inf` identifies
with the `D(t_k · t_l)` locus. The diagonal `k = l` is proof-irrelevance. -/
lemma addOnYOnFamily_agree_inf (k l : Fin 3) :
    Scheme.homOfLE _ (inf_le_left : blOpenYPieceFamily W i j k ⊓ blOpenYPieceFamily W i j l ≤ _) ≫
        addOnYOnFamily W i j k hΔ =
      Scheme.homOfLE _
        (inf_le_right : blOpenYPieceFamily W i j k ⊓ blOpenYPieceFamily W i j l ≤ _) ≫
        addOnYOnFamily W i j l hΔ := by
  rcases eq_or_ne l k with rfl | hkl
  · rfl
  · exact addOnYOnFamily_agree W i j hΔ k l hkl _ inf_le_left inf_le_right
      (blOpenYPieceFamily_inf W i j k l)

/-- The law-1 analogue of `addOnYOnFamily_agree_inf`. -/
lemma addOnZOnFamily_agree_inf (k l : Fin 3) :
    Scheme.homOfLE _ (inf_le_left : blOpenZPieceFamily W i j k ⊓ blOpenZPieceFamily W i j l ≤ _) ≫
        addOnZOnFamily W i j k hΔ =
      Scheme.homOfLE _
        (inf_le_right : blOpenZPieceFamily W i j k ⊓ blOpenZPieceFamily W i j l ≤ _) ≫
        addOnZOnFamily W i j l hΔ := by
  rcases eq_or_ne l k with rfl | hkl
  · rfl
  · exact addOnZOnFamily_agree W i j hΔ k l hkl _ inf_le_left inf_le_right
      (blOpenZPieceFamily_inf W i j k l)

/-- **(c4.2c)** The second Bosma–Lenstra law as a single morphism on the whole regularity open of
the `(i,j)` chart-product — glued from its three chart pieces.

Stated on `⨆ k, blOpenYPieceFamily`, which `iSup_blOpenYPieceFamily` identifies with
`blOpenYPiece`. Consumers should use only the interface below (`ι_addOnYOnSup`), never this body:
it is a `glueMorphisms` term over a `Proj` chart-product and unfolding it is not viable. -/
noncomputable irreducible_def addOnYOnSup :
    (⨆ k, blOpenYPieceFamily W i j k).toScheme ⟶ projModel W :=
  (Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j)).glueMorphisms
    (fun k => addOnYOnFamily W i j k hΔ)
    (glueMorphisms_hf_of_agree _ _ (addOnYOnFamily_agree_inf W i j hΔ))

/-- **(c4.2c)** The first Bosma–Lenstra law (mathlib's `addXYZ`) as a single morphism on the whole
regularity open of the `(i,j)` chart-product. -/
noncomputable irreducible_def addOnZOnSup :
    (⨆ k, blOpenZPieceFamily W i j k).toScheme ⟶ projModel W :=
  (Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j)).glueMorphisms
    (fun k => addOnZOnFamily W i j k hΔ)
    (glueMorphisms_hf_of_agree _ _ (addOnZOnFamily_agree_inf W i j hΔ))

/-- **(rule 3, the opaque interface)** `addOnYOnSup` restricts on the `k`-th piece to
`addOnYOnFamily k`. This characterises it: by `Scheme.Cover.hom_ext`, any two morphisms with
this property are equal (`addOnYOnSup_ext`). -/
@[reassoc (attr := simp)]
lemma ι_addOnYOnSup (k : Fin 3) :
    (Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j)).f k ≫ addOnYOnSup W i j hΔ =
      addOnYOnFamily W i j k hΔ := by
  rw [addOnYOnSup]
  exact Scheme.Cover.ι_glueMorphisms (Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j))
    (fun k => addOnYOnFamily W i j k hΔ)
    (glueMorphisms_hf_of_agree _ _ (addOnYOnFamily_agree_inf W i j hΔ)) k

/-- The law-1 analogue of `ι_addOnYOnSup`. -/
@[reassoc (attr := simp)]
lemma ι_addOnZOnSup (k : Fin 3) :
    (Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j)).f k ≫ addOnZOnSup W i j hΔ =
      addOnZOnFamily W i j k hΔ := by
  rw [addOnZOnSup]
  exact Scheme.Cover.ι_glueMorphisms (Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j))
    (fun k => addOnZOnFamily W i j k hΔ)
    (glueMorphisms_hf_of_agree _ _ (addOnZOnFamily_agree_inf W i j hΔ)) k

omit [IsJacobsonRing R] [IsDomain (biChartRing W i j)] in
/-- **(rule 3, uniqueness)** `addOnYOnSup` is the unique morphism restricting to the pieces. -/
lemma addOnYOnSup_ext {g₁ g₂ : (⨆ k, blOpenYPieceFamily W i j k).toScheme ⟶ projModel W}
    (h : ∀ k, (Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j)).f k ≫ g₁ =
      (Scheme.Opens.iSupOpenCover (blOpenYPieceFamily W i j)).f k ≫ g₂) : g₁ = g₂ :=
  Scheme.Cover.hom_ext _ _ _ h

omit [IsJacobsonRing R] [IsDomain (biChartRing W i j)] in
/-- The law-1 analogue of `addOnYOnSup_ext`. -/
lemma addOnZOnSup_ext {g₁ g₂ : (⨆ k, blOpenZPieceFamily W i j k).toScheme ⟶ projModel W}
    (h : ∀ k, (Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j)).f k ≫ g₁ =
      (Scheme.Opens.iSupOpenCover (blOpenZPieceFamily W i j)).f k ≫ g₂) : g₁ = g₂ :=
  Scheme.Cover.hom_ext _ _ _ h

end Glue

end Morphisms

end WeierstrassCurve.Projective
