import ModularCurves.EllipticCurve.AdditionChartMor
import ModularCurves.EllipticCurve.AdditionChartProj

/-!
# The piece morphisms agree on overlaps (T-W7.0c-c5β, c4.2c step 2b)

The three pieces `pieceMorOfTriple W t k` of an on-curve triple `t : Fin 3 → A` are defined on
`Spec (Localization.Away (t k))`. On the overlap of the `k`-th and `l`-th piece — i.e. over
`Localization.Away (t k * t l)`, where *both* coordinates are invertible — they agree:

  `pieceMorOfTriple_agree`.

This is the ring-level form of the `hf` obligation of `Scheme.OpenCover.glueMorphisms`. Two
ingredients, both already proven:

* `chartHomOfTriple_naturality` — restricting a piece morphism along `Away (t k) → Away (t k * t l)`
  is the chart morphism of the *same* triple, read over the smaller ring;
* `chartι_comp_specMap_chartAwayHom_eq` (the c4.2 crux) — one triple, two invertible coordinates,
  two chart immersions: the same morphism into `projModel W`.

The only thing between the two is bookkeeping: `IsLocalization.Away.awayToAwayRight/Left` supply
the two restriction maps into the common ring, and `awayToAway*_eq` says they fix the image of `A`,
so both sides feed the crux the *same* triple `algebraMap A (Away (t k * t l)) ∘ t`.

Nothing here is specific to the Bosma–Lenstra laws: `addOnYPieceMor`/`addOnZPieceMor` are the
special cases `t := lawTwoTriple`/`lawOneTriple` (`addOnYPieceMor_eq`, `addOnZPieceMor_eq`, both
`rfl`). The *cover* obligation — that the three `D(t k)` cover the regularity open — is
`regularityOpen_eq_top_iff`, and the *law-1-vs-law-2* agreement is
`chartHomOfTriple_lawOne_eq_lawTwo`; this file is only the within-one-law, across-charts half.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {A : Type} [CommRing A] [Algebra R A]

section MapTriple

variable {S : Type} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

/-- An on-curve triple stays on the curve in any `A`-algebra. -/
lemma equation_mapTriple (t : Fin 3 → A)
    (ht : (W.map (algebraMap R A)).toProjective.Equation t) :
    (W.map (algebraMap R S)).toProjective.Equation (fun m => algebraMap A S (t m)) := by
  have h := ht.map (algebraMap A S)
  have hmap : (W.map (algebraMap R A)).map (algebraMap A S) = W.map (algebraMap R S) := by
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  exact hmap ▸ h

end MapTriple

/-- The `k`-th piece morphism of an on-curve triple `t` in an `R`-algebra `A`: on the locus where
`t k` is invertible, the ratios `t m / t k` are the chart-`k` coordinates of a point of the model.

`addOnYPieceMor` and `addOnZPieceMor` are the cases `t := lawTwoTriple` / `lawOneTriple`. -/
noncomputable def pieceMorOfTriple (t : Fin 3 → A)
    (ht : (W.map (algebraMap R A)).toProjective.Equation t) (k : Fin 3) :
    Spec (CommRingCat.of (Localization.Away (t k))) ⟶ projModel W :=
  Spec.map (CommRingCat.ofHom
    (chartAwayHomOfTriple W k (fun m => algebraMap A (Localization.Away (t k)) (t m))
      (IsLocalization.Away.invSelf (t k)) (IsLocalization.Away.mul_invSelf _)
      (equation_mapTriple W t ht)).toRingHom) ≫ chartι W k

section Away

variable (R)

/-- `Localization.Away a → Localization.Away (a * b)` as an `R`-algebra map. -/
noncomputable def awayPairRight (a b : A) :
    Localization.Away a →ₐ[R] Localization.Away (a * b) where
  __ := IsLocalization.Away.awayToAwayRight (S := Localization.Away a) a b
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away a)]
    exact (IsLocalization.Away.awayToAwayRight_eq a b _).trans
      (IsScalarTower.algebraMap_apply R A (Localization.Away (a * b)) r).symm

/-- `Localization.Away b → Localization.Away (a * b)` as an `R`-algebra map. -/
noncomputable def awayPairLeft (a b : A) :
    Localization.Away b →ₐ[R] Localization.Away (a * b) where
  __ := IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) b a
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away b)]
    exact (IsLocalization.Away.awayToAwayLeft_eq b a _).trans
      (IsScalarTower.algebraMap_apply R A (Localization.Away (a * b)) r).symm

@[simp]
lemma awayPairRight_algebraMap (a b c : A) :
    awayPairRight R a b (algebraMap A (Localization.Away a) c) =
      algebraMap A (Localization.Away (a * b)) c :=
  IsLocalization.Away.awayToAwayRight_eq a b c

@[simp]
lemma awayPairLeft_algebraMap (a b c : A) :
    awayPairLeft R a b (algebraMap A (Localization.Away b) c) =
      algebraMap A (Localization.Away (a * b)) c :=
  IsLocalization.Away.awayToAwayLeft_eq b a c

end Away

section Naturality

variable {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

/-- `chartHomOfTriple_naturality`, transported through `chartCoordAlgEquiv`. -/
lemma chartAwayHomOfTriple_naturality (φ : S →ₐ[R] S') (k : Fin 3) (t : Fin 3 → S) (u : S)
    (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hu' : φ (t k) * φ u = 1)
    (ht' : (W.map (algebraMap R S')).toProjective.Equation (fun m => φ (t m))) :
    chartAwayHomOfTriple W k (fun m => φ (t m)) (φ u) hu' ht' =
      φ.comp (chartAwayHomOfTriple W k t u hu ht) := by
  rw [chartAwayHomOfTriple, chartAwayHomOfTriple,
    chartHomOfTriple_naturality W φ k t u hu ht hu' ht', AlgHom.comp_assoc]

/-- Chart morphisms depend on the triple only through the data, not its presentation. -/
lemma chartAwayHomOfTriple_congr (k : Fin 3) (t s : Fin 3 → S) (u : S) (hts : t = s)
    (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hu' : s k * u = 1) (ht' : (W.map (algebraMap R S)).toProjective.Equation s) :
    chartAwayHomOfTriple W k t u hu ht = chartAwayHomOfTriple W k s u hu' ht' := by
  subst hts; rfl

end Naturality

/-- **(c4.2c, the agreement)** The `k`-th and `l`-th piece morphisms of an on-curve triple agree
after restriction to the common locus `D(t k · t l)`, where both coordinates are invertible.

This is the `hf` obligation of `Scheme.OpenCover.glueMorphisms` for the three-piece cover of the
regularity open of `t`, in ring-level form. The two restrictions present the *same* chart data —
the triple `algebraMap A (Away (t k * t l)) ∘ t` — read in charts `k` and `l`; the c4.2 crux
`chartι_comp_specMap_chartAwayHom_eq` says those two readings are the same morphism into the
model. -/
theorem pieceMorOfTriple_agree (t : Fin 3 → A)
    (ht : (W.map (algebraMap R A)).toProjective.Equation t) (k l : Fin 3) (hkl : l ≠ k) :
    Spec.map (CommRingCat.ofHom (awayPairRight R (t k) (t l)).toRingHom) ≫
        pieceMorOfTriple W t ht k =
      Spec.map (CommRingCat.ofHom (awayPairLeft R (t k) (t l)).toRingHom) ≫
        pieceMorOfTriple W t ht l := by
  have hTeq : (W.map (algebraMap R (Localization.Away (t k * t l)))).toProjective.Equation
      (fun m => algebraMap A (Localization.Away (t k * t l)) (t m)) := equation_mapTriple W t ht
  have hTk : algebraMap A (Localization.Away (t k * t l)) (t k) *
      awayPairRight R (t k) (t l) (IsLocalization.Away.invSelf (t k)) = 1 := by
    rw [← awayPairRight_algebraMap R (t k) (t l) (t k), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hTl : algebraMap A (Localization.Away (t k * t l)) (t l) *
      awayPairLeft R (t k) (t l) (IsLocalization.Away.invSelf (t l)) = 1 := by
    rw [← awayPairLeft_algebraMap R (t k) (t l) (t l), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have halgk : (awayPairRight R (t k) (t l)).comp
      (chartAwayHomOfTriple W k (fun m => algebraMap A (Localization.Away (t k)) (t m))
        (IsLocalization.Away.invSelf (t k)) (IsLocalization.Away.mul_invSelf _)
        (equation_mapTriple W t ht)) =
      chartAwayHomOfTriple W k (fun m => algebraMap A (Localization.Away (t k * t l)) (t m))
        (awayPairRight R (t k) (t l) (IsLocalization.Away.invSelf (t k))) hTk hTeq := by
    rw [← chartAwayHomOfTriple_naturality W (awayPairRight R (t k) (t l)) k
      (fun m => algebraMap A (Localization.Away (t k)) (t m))
      (IsLocalization.Away.invSelf (t k)) (IsLocalization.Away.mul_invSelf _)
      (equation_mapTriple W t ht)
      (by rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one])
      (by simpa only [awayPairRight_algebraMap] using hTeq)]
    exact chartAwayHomOfTriple_congr W k _ _ _
      (funext fun m => awayPairRight_algebraMap R (t k) (t l) (t m)) _ _ hTk hTeq
  have halgl : (awayPairLeft R (t k) (t l)).comp
      (chartAwayHomOfTriple W l (fun m => algebraMap A (Localization.Away (t l)) (t m))
        (IsLocalization.Away.invSelf (t l)) (IsLocalization.Away.mul_invSelf _)
        (equation_mapTriple W t ht)) =
      chartAwayHomOfTriple W l (fun m => algebraMap A (Localization.Away (t k * t l)) (t m))
        (awayPairLeft R (t k) (t l) (IsLocalization.Away.invSelf (t l))) hTl hTeq := by
    rw [← chartAwayHomOfTriple_naturality W (awayPairLeft R (t k) (t l)) l
      (fun m => algebraMap A (Localization.Away (t l)) (t m))
      (IsLocalization.Away.invSelf (t l)) (IsLocalization.Away.mul_invSelf _)
      (equation_mapTriple W t ht)
      (by rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one])
      (by simpa only [awayPairLeft_algebraMap] using hTeq)]
    exact chartAwayHomOfTriple_congr W l _ _ _
      (funext fun m => awayPairLeft_algebraMap R (t k) (t l) (t m)) _ _ hTl hTeq
  have hk : Spec.map (CommRingCat.ofHom (awayPairRight R (t k) (t l)).toRingHom) ≫
      pieceMorOfTriple W t ht k =
      Spec.map (CommRingCat.ofHom
        (chartAwayHomOfTriple W k (fun m => algebraMap A (Localization.Away (t k * t l)) (t m))
          (awayPairRight R (t k) (t l) (IsLocalization.Away.invSelf (t k)))
          hTk hTeq).toRingHom) ≫ chartι W k := by
    rw [pieceMorOfTriple, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ]
    congr 2
    exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom halgk)
  have hl : Spec.map (CommRingCat.ofHom (awayPairLeft R (t k) (t l)).toRingHom) ≫
      pieceMorOfTriple W t ht l =
      Spec.map (CommRingCat.ofHom
        (chartAwayHomOfTriple W l (fun m => algebraMap A (Localization.Away (t k * t l)) (t m))
          (awayPairLeft R (t k) (t l) (IsLocalization.Away.invSelf (t l)))
          hTl hTeq).toRingHom) ≫ chartι W l := by
    rw [pieceMorOfTriple, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ]
    congr 2
    exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom halgl)
  rw [hk, hl]
  exact chartι_comp_specMap_chartAwayHom_eq W k l hkl _ _ _ hTk hTl hTeq

section BosmaLenstra

variable (i j : Fin 3) [IsJacobsonRing R] [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ)

/-- The `k`-th piece of `addOnY` is the `k`-th piece morphism of the law-2 triple. -/
lemma addOnYPieceMor_eq (k : Fin 3) :
    addOnYPieceMor W i j k hΔ =
      pieceMorOfTriple W (lawTwoTriple W i j) (equation_lawTwoTriple_of_isDomain W i j hΔ) k :=
  rfl

/-- The `k`-th piece of `addOnZ` is the `k`-th piece morphism of the law-1 triple. -/
lemma addOnZPieceMor_eq (k : Fin 3) :
    addOnZPieceMor W i j k hΔ =
      pieceMorOfTriple W (lawOneTriple W i j) (equation_lawOneTriple_of_isDomain W i j hΔ) k :=
  rfl

/-- **(c4.2c)** The three pieces of `addOnY` agree on their pairwise overlaps. -/
theorem addOnYPieceMor_agree (k l : Fin 3) (hkl : l ≠ k) :
    Spec.map (CommRingCat.ofHom
        (awayPairRight R (lawTwoTriple W i j k) (lawTwoTriple W i j l)).toRingHom) ≫
        addOnYPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom
        (awayPairLeft R (lawTwoTriple W i j k) (lawTwoTriple W i j l)).toRingHom) ≫
        addOnYPieceMor W i j l hΔ := by
  rw [addOnYPieceMor_eq, addOnYPieceMor_eq]
  exact pieceMorOfTriple_agree W _ _ k l hkl

/-- **(c4.2c)** The three pieces of `addOnZ` agree on their pairwise overlaps. -/
theorem addOnZPieceMor_agree (k l : Fin 3) (hkl : l ≠ k) :
    Spec.map (CommRingCat.ofHom
        (awayPairRight R (lawOneTriple W i j k) (lawOneTriple W i j l)).toRingHom) ≫
        addOnZPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom
        (awayPairLeft R (lawOneTriple W i j k) (lawOneTriple W i j l)).toRingHom) ≫
        addOnZPieceMor W i j l hΔ := by
  rw [addOnZPieceMor_eq, addOnZPieceMor_eq]
  exact pieceMorOfTriple_agree W _ _ k l hkl

end BosmaLenstra

end WeierstrassCurve.Projective
