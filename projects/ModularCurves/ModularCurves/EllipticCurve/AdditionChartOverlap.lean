/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartMor
import ModularCurves.EllipticCurve.AdditionChartProj
import ModularCurves.EllipticCurve.AdditionChartGlue

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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {A : Type u} [CommRing A] [Algebra R A]

section MapTriple

variable {S : Type u} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

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

@[simp]
lemma awayPairRight_toRingHom (a b : A) :
    (awayPairRight R a b).toRingHom =
      IsLocalization.Away.awayToAwayRight (S := Localization.Away a) a b :=
  rfl

@[simp]
lemma awayPairLeft_toRingHom (a b : A) :
    (awayPairLeft R a b).toRingHom =
      IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) b a :=
  rfl

end Away

section Naturality

variable {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

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

/-- A projective triple stays on the curve after rescaling by a unit — mathlib's `equation_smul`,
with the scalar action spelled out pointwise (they are definitionally equal). -/
lemma equation_mul_left (c : S) (hc : IsUnit c) (t : Fin 3 → S)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    (W.map (algebraMap R S)).toProjective.Equation (fun m => c * t m) :=
  (equation_smul t hc).mpr ht

/-- **(c4.3 core)** The chart morphism of a triple is invariant under rescaling by a unit: the
ratios `t m / t k` do not see the scalar. This is what makes the per-chart-product laws agree on
overlaps of chart-products, where the two law-2 triples differ by the bidegree-`(2,2)` transition
factor rather than being equal. -/
lemma chartHomOfTriple_smul (k : Fin 3) (t : Fin 3 → S) (u c d : S) (hcd : c * d = 1)
    (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hu' : (fun m => c * t m) k * (d * u) = 1) :
    chartHomOfTriple W k (fun m => c * t m) (d * u) hu' (equation_mul_left W c ⟨⟨c, d, hcd,
      (mul_comm d c).trans hcd⟩, rfl⟩ t ht) =
      chartHomOfTriple W k t u hu ht := by
  refine chartHomOfTriple_congr W k t (fun m => c * t m) u (d * u) hu hu' ht
    (equation_mul_left W c ⟨⟨c, d, hcd, (mul_comm d c).trans hcd⟩, rfl⟩ t ht) fun m => ?_
  show c * t m * (d * u) = t m * u
  rw [show c * t m * (d * u) = (c * d) * (t m * u) by ring, hcd, one_mul]

/-- The `Away`-presentation form of `chartHomOfTriple_smul`. -/
lemma chartAwayHomOfTriple_smul (k : Fin 3) (t : Fin 3 → S) (u c d : S) (hcd : c * d = 1)
    (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hu' : (fun m => c * t m) k * (d * u) = 1) :
    chartAwayHomOfTriple W k (fun m => c * t m) (d * u) hu' (equation_mul_left W c ⟨⟨c, d, hcd,
      (mul_comm d c).trans hcd⟩, rfl⟩ t ht) =
      chartAwayHomOfTriple W k t u hu ht := by
  rw [chartAwayHomOfTriple, chartAwayHomOfTriple, chartHomOfTriple_smul W k t u c d hcd hu ht hu']

/-- **(c4.3 core, sharpened)** If two on-curve triples are proportional — `t' = e • t` for ANY
scalar `e`, not assumed a unit — then their chart morphisms coincide. The unit witnesses do the
work: `t k * u = 1` and `t' k * u' = 1` force `u = e * u'`, so the ratios agree.

This is the form the chart-product transition needs: there `e` is the bidegree-`(2,2)` transition
factor, and one never has to name its inverse. -/
lemma chartHomOfTriple_congr_of_smul (k : Fin 3) (t t' : Fin 3 → S) (u u' e : S)
    (hsmul : ∀ m, t' m = e * t m) (hu : t k * u = 1) (hu' : t' k * u' = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (ht' : (W.map (algebraMap R S)).toProjective.Equation t') :
    chartHomOfTriple W k t' u' hu' ht' = chartHomOfTriple W k t u hu ht := by
  have hue : u = e * u' :=
    calc u = u * (t' k * u') := by rw [hu', mul_one]
      _ = (t k * u) * (e * u') := by rw [hsmul k]; ring
      _ = e * u' := by rw [hu, one_mul]
  refine chartHomOfTriple_congr W k t t' u u' hu hu' ht ht' fun m => ?_
  rw [hsmul m, hue]
  ring

/-- The `Away`-presentation form of `chartHomOfTriple_congr_of_smul`. -/
lemma chartAwayHomOfTriple_congr_of_smul (k : Fin 3) (t t' : Fin 3 → S) (u u' e : S)
    (hsmul : ∀ m, t' m = e * t m) (hu : t k * u = 1) (hu' : t' k * u' = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (ht' : (W.map (algebraMap R S)).toProjective.Equation t') :
    chartAwayHomOfTriple W k t' u' hu' ht' = chartAwayHomOfTriple W k t u hu ht := by
  rw [chartAwayHomOfTriple, chartAwayHomOfTriple,
    chartHomOfTriple_congr_of_smul W k t t' u u' e hsmul hu hu' ht ht']

/-- **(c4.3, the law-2 transition)** Rescaling the two input points of the second Bosma–Lenstra law
does not change the chart morphism it defines: the law is bidegree `(2,2)` (`dblAddXYZ_smul`), so
the output triple is rescaled by `(c·d)²`, and a chart morphism does not see scalars.

Over the overlap of two chart-products, the two tautological points differ exactly by the chart
transition scalars — so this is the cross-chart-product agreement, at ring level. -/
lemma chartAwayHomOfTriple_dblAddXYZ_smul (k : Fin 3) (P Q : Fin 3 → S) (c d u u' : S)
    (hu : (W.map (algebraMap R S)).toProjective.dblAddXYZ P Q k * u = 1)
    (hu' : (W.map (algebraMap R S)).toProjective.dblAddXYZ (c • P) (d • Q) k * u' = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation
      ((W.map (algebraMap R S)).toProjective.dblAddXYZ P Q))
    (ht' : (W.map (algebraMap R S)).toProjective.Equation
      ((W.map (algebraMap R S)).toProjective.dblAddXYZ (c • P) (d • Q))) :
    chartAwayHomOfTriple W k
        ((W.map (algebraMap R S)).toProjective.dblAddXYZ (c • P) (d • Q)) u' hu' ht' =
      chartAwayHomOfTriple W k ((W.map (algebraMap R S)).toProjective.dblAddXYZ P Q) u hu ht :=
  chartAwayHomOfTriple_congr_of_smul W k _ _ u u' ((c * d) ^ 2)
    (fun m => by rw [dblAddXYZ_smul]; rfl) hu hu' ht ht'

/-- **(the crux, in its final form)** Two on-curve triples that are PROPORTIONAL, each with an
invertible coordinate — at possibly different indices `k` and `l` — define the same morphism to the
model.

This subsumes both agreements of the construction. Taking `e = 1` gives the within-chart-product
agreement of c4.2c (`pieceMorOfTriple_agree`); taking `e` the bidegree-`(2,2)` transition factor
gives the cross-chart-product agreement of c4.3. Neither needs `e` to be a unit: `hu'` forces it. -/
theorem chartι_comp_specMap_chartAwayHom_smul_eq {S : Type u} [CommRing S] [Algebra R S]
    (k l : Fin 3) (t t' : Fin 3 → S) (u u' e : S) (hsmul : ∀ m, t' m = e * t m)
    (hu : t k * u = 1) (hu' : t' l * u' = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (ht' : (W.map (algebraMap R S)).toProjective.Equation t') :
    Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W l t' u' hu' ht').toRingHom) ≫ chartι W l =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k t u hu ht).toRingHom) ≫ chartι W k := by
  have hv : t l * (e * u') = 1 := by
    rw [show t l * (e * u') = (e * t l) * u' by ring, ← hsmul l]; exact hu'
  rw [show chartAwayHomOfTriple W l t' u' hu' ht' = chartAwayHomOfTriple W l t (e * u') hv ht from
    chartAwayHomOfTriple_congr_of_smul W l t t' (e * u') u' e hsmul hv hu' ht ht']
  rcases eq_or_ne l k with rfl | hlk
  · congr 2
    exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom
      (chartAwayHomOfTriple_congr_of_smul W l t t u (e * u') 1
        (fun m => (one_mul _).symm) hu hv ht ht))
  · exact (chartι_comp_specMap_chartAwayHom_eq W k l hlk t u (e * u') hu hv ht).symm

/-- Composing `pieceMorOfTriple` with a further `R`-algebra map `ψ` out of the localization gives
the chart morphism of the pushed-forward triple — naturality of `chartAwayHomOfTriple`. This is the
bridge from `pieceMorOfTriple` to the cross-chart crux: over the overlap ring both readings become
`chartAwayHomOfTriple(image triple) ≫ chartι`. -/
lemma specMap_comp_pieceMorOfTriple {S : Type u} [CommRing S] [Algebra R S]
    (t : Fin 3 → A) (ht : (W.map (algebraMap R A)).toProjective.Equation t) (k : Fin 3)
    (ψ : Localization.Away (t k) →ₐ[R] S)
    (hψ : ψ (algebraMap A (Localization.Away (t k)) (t k)) *
      ψ (IsLocalization.Away.invSelf (t k)) = 1)
    (ht' : (W.map (algebraMap R S)).toProjective.Equation
      (fun m => ψ (algebraMap A (Localization.Away (t k)) (t m)))) :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ pieceMorOfTriple W t ht k =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k
        (fun m => ψ (algebraMap A (Localization.Away (t k)) (t m)))
        (ψ (IsLocalization.Away.invSelf (t k))) hψ ht').toRingHom) ≫ chartι W k := by
  rw [pieceMorOfTriple, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (· ≫ chartι W k) (congrArg Spec.map (congrArg CommRingCat.ofHom ?_))
  exact congrArg AlgHom.toRingHom (chartAwayHomOfTriple_naturality W ψ k
    (fun m => algebraMap A (Localization.Away (t k)) (t m))
    (IsLocalization.Away.invSelf (t k)) (IsLocalization.Away.mul_invSelf _)
    (equation_mapTriple W t ht) hψ ht').symm

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

/-- Away-pair factorization of a piece morphism: precomposing `pieceMorOfTriple W r hr k` with
`Spec.map` of an `R`-algebra map `pair : Away (r k) → B` that transports the triple coordinates
(`hpair`) factors it through `chartι W k` via `chartAwayHomOfTriple` over `B`. Instantiated at
`awayPairRight`/`awayPairLeft` to compare the two overlap charts. -/
lemma pieceMor_awayPair_factor (r : Fin 3 → A)
    (hr : (W.map (algebraMap R A)).toProjective.Equation r) (k : Fin 3)
    {B : Type u} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (pair : Localization.Away (r k) →ₐ[R] B)
    (hpk : algebraMap A B (r k) * pair (IsLocalization.Away.invSelf (r k)) = 1)
    (hTeqr : (W.map (algebraMap R B)).toProjective.Equation (fun m => algebraMap A B (r m)))
    (hpair : ∀ m, pair (algebraMap A (Localization.Away (r k)) (r m)) = algebraMap A B (r m)) :
    Spec.map (CommRingCat.ofHom pair.toRingHom) ≫ pieceMorOfTriple W r hr k =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k (fun m => algebraMap A B (r m))
        (pair (IsLocalization.Away.invSelf (r k))) hpk hTeqr).toRingHom) ≫ chartι W k := by
  have halg : pair.comp
        (chartAwayHomOfTriple W k (fun m => algebraMap A (Localization.Away (r k)) (r m))
          (IsLocalization.Away.invSelf (r k)) (IsLocalization.Away.mul_invSelf _)
          (equation_mapTriple W r hr)) =
      chartAwayHomOfTriple W k (fun m => algebraMap A B (r m))
        (pair (IsLocalization.Away.invSelf (r k))) hpk hTeqr := by
    rw [← chartAwayHomOfTriple_naturality W pair k
      (fun m => algebraMap A (Localization.Away (r k)) (r m))
      (IsLocalization.Away.invSelf (r k)) (IsLocalization.Away.mul_invSelf _)
      (equation_mapTriple W r hr)
      (by rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one])
      (by simpa only [hpair] using hTeqr)]
    exact chartAwayHomOfTriple_congr W k _ _ _ (funext hpair) _ _ hpk hTeqr
  rw [pieceMorOfTriple, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom halg)

/-- **(c3, general per-piece cross-triple agreement)** Two on-curve triples `t`, `s` in an
`R`-algebra `A` with vanishing `2×2` minors (`s m * t k = s k * t m`) — their `k`-th piece
morphisms agree over the common regular locus `D(t k · s k)`. SAME index `k` (`isUnit_of_minor`),
so — unlike the within-law `pieceMorOfTriple_agree` — no cross-index crux is needed: both localise
to `chartAwayHomOfTriple k`, which agree by `chartAwayHomOfTriple_cross_eq`. -/
theorem pieceMorOfTriple_cross_agree (t s : Fin 3 → A)
    (ht : (W.map (algebraMap R A)).toProjective.Equation t)
    (hs : (W.map (algebraMap R A)).toProjective.Equation s) (k : Fin 3)
    (hmin : ∀ m, s m * t k = s k * t m) :
    Spec.map (CommRingCat.ofHom (awayPairRight R (t k) (s k)).toRingHom) ≫
        pieceMorOfTriple W t ht k =
      Spec.map (CommRingCat.ofHom (awayPairLeft R (t k) (s k)).toRingHom) ≫
        pieceMorOfTriple W s hs k := by
  have hTeqt : (W.map (algebraMap R (Localization.Away (t k * s k)))).toProjective.Equation
      (fun m => algebraMap A (Localization.Away (t k * s k)) (t m)) := equation_mapTriple W t ht
  have hTeqs : (W.map (algebraMap R (Localization.Away (t k * s k)))).toProjective.Equation
      (fun m => algebraMap A (Localization.Away (t k * s k)) (s m)) := equation_mapTriple W s hs
  have hTk : algebraMap A (Localization.Away (t k * s k)) (t k) *
      awayPairRight R (t k) (s k) (IsLocalization.Away.invSelf (t k)) = 1 := by
    rw [← awayPairRight_algebraMap R (t k) (s k) (t k), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hSk : algebraMap A (Localization.Away (t k * s k)) (s k) *
      awayPairLeft R (t k) (s k) (IsLocalization.Away.invSelf (s k)) = 1 := by
    rw [← awayPairLeft_algebraMap R (t k) (s k) (s k), ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hkt := pieceMor_awayPair_factor W t ht k (awayPairRight R (t k) (s k)) hTk hTeqt
    (fun m => awayPairRight_algebraMap R (t k) (s k) (t m))
  have hks := pieceMor_awayPair_factor W s hs k (awayPairLeft R (t k) (s k)) hSk hTeqs
    (fun m => awayPairLeft_algebraMap R (t k) (s k) (s m))
  rw [hkt, hks]
  exact congrArg (fun f : chartAway W k →ₐ[R] _ => Spec.map
    (CommRingCat.ofHom f.toRingHom) ≫ chartι W k)
    (chartAwayHomOfTriple_cross_eq W k
      (awayPairRight R (t k) (s k) (IsLocalization.Away.invSelf (t k)))
      (awayPairLeft R (t k) (s k) (IsLocalization.Away.invSelf (s k)))
      (fun m => algebraMap A (Localization.Away (t k * s k)) (t m))
      (fun m => algebraMap A (Localization.Away (t k * s k)) (s m))
      (fun m => by rw [← map_mul, hmin m, map_mul]) hTk hSk hTeqt hTeqs).symm

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

/-- **(c3, per-piece cross-law agreement)** On `D(lawTwo_k · lawOne_k)`, the k-th law-2 piece and
the
k-th law-1 piece of the two Bosma–Lenstra laws agree. `pieceMorOfTriple_cross_agree` at the two
triples,
fed the certified minors `lawOneTriple_mul_lawTwoTriple`. -/
theorem addOnYPieceMor_eq_addOnZPieceMor (k : Fin 3) :
    Spec.map (CommRingCat.ofHom
        (awayPairRight R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        addOnYPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom
        (awayPairLeft R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        addOnZPieceMor W i j k hΔ := by
  rw [addOnYPieceMor_eq, addOnZPieceMor_eq]
  exact pieceMorOfTriple_cross_agree W (lawTwoTriple W i j) (lawOneTriple W i j)
    (equation_lawTwoTriple_of_isDomain W i j hΔ)
    (equation_lawOneTriple_of_isDomain W i j hΔ) k
    (fun m => lawOneTriple_mul_lawTwoTriple W i j m k)

end BosmaLenstra

end WeierstrassCurve.Projective
