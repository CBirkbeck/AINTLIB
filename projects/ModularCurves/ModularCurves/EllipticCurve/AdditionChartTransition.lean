import ModularCurves.EllipticCurve.AdditionChartOverlap

/-!
# The chart-product transition (T-W7.0c-c5β, c4.3 ring layer)

The `(i,j)` and `(i',j')` chart-products of `E ×_R E` overlap in the locus where the two transition
coordinates `X_{i'}/X_i` and `X_{j'}/X_j` are invertible. Those coordinates are, tautologically,
the `i'`-th coordinate of the first chart-point and the `j'`-th coordinate of the second:

  `transFst W i j i' = biChartPointFst W i j i'`,  `transSnd W i j j' = biChartPointSnd W i j j'`.

Over `transRing := Localization.Away (transFst * transSnd)` both are units, so the two chart-points
of the `(i,j)` product, rescaled by their inverses, are the chart-points of the `(i',j')` product.
That rescaling is realised by an honest `R`-algebra map

  `transHom : biChartRing W i' j' →ₐ[R] transRing W i j i' j'`

built — and this is the point — out of `chartHomOfTriple`, one factor at a time: an on-curve triple
with an invertible `i'`-th coordinate is exactly the datum of a map out of the `i'`-th chart ring.
No new universal property, no explicit transition matrices.

The payoff (`transHom_lawTwoTriple`): under `transHom`, the `(i',j')` law-2 triple is the `(i,j)`
law-2 triple rescaled by the bidegree-`(2,2)` factor. Combined with
`chartAwayHomOfTriple_dblAddXYZ_smul` (ac80a22d) this says the two chart-products define the SAME
morphism on their overlap — the cross-chart-product agreement, at ring level.
-/

open MvPolynomial ModularCurves TensorProduct

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (i j i' j' : Fin 3)

/-- The transition coordinate of the first factor: `X_{i'}/X_i`, read in the `(i,j)` chart. -/
noncomputable def transFst : biChartRing W i j := biChartPointFst W i j i'

/-- The transition coordinate of the second factor: `X_{j'}/X_j`. -/
noncomputable def transSnd : biChartRing W i j := biChartPointSnd W i j j'

/-- The coordinate ring of the overlap of the `(i,j)` and `(i',j')` chart-products. -/
noncomputable abbrev transRing : Type :=
  Localization.Away (transFst W i j i' * transSnd W i j j')

section

/-- The first chart-point, over the overlap ring. -/
noncomputable def transPointFst : Fin 3 → transRing W i j i' j' :=
  fun m => algebraMap (biChartRing W i j) _ (biChartPointFst W i j m)

/-- The second chart-point, over the overlap ring. -/
noncomputable def transPointSnd : Fin 3 → transRing W i j i' j' :=
  fun m => algebraMap (biChartRing W i j) _ (biChartPointSnd W i j m)

lemma isUnit_transPointFst : IsUnit (transPointFst W i j i' j' i') :=
  IsLocalization.Away.isUnit_of_dvd (S := transRing W i j i' j')
    (transFst W i j i' * transSnd W i j j') ⟨transSnd W i j j', rfl⟩

lemma isUnit_transPointSnd : IsUnit (transPointSnd W i j i' j' j') :=
  IsLocalization.Away.isUnit_of_dvd (S := transRing W i j i' j')
    (transFst W i j i' * transSnd W i j j') ⟨transFst W i j i', mul_comm _ _⟩

/-- The inverse of the first transition coordinate. -/
noncomputable def transInvFst : transRing W i j i' j' :=
  ↑(isUnit_transPointFst W i j i' j').unit⁻¹

/-- The inverse of the second transition coordinate. -/
noncomputable def transInvSnd : transRing W i j i' j' :=
  ↑(isUnit_transPointSnd W i j i' j').unit⁻¹

lemma transPointFst_mul_transInvFst :
    transPointFst W i j i' j' i' * transInvFst W i j i' j' = 1 :=
  (isUnit_transPointFst W i j i' j').mul_val_inv

lemma transPointSnd_mul_transInvSnd :
    transPointSnd W i j i' j' j' * transInvSnd W i j i' j' = 1 :=
  (isUnit_transPointSnd W i j i' j').mul_val_inv

lemma equation_transPointFst :
    (W.map (algebraMap R (transRing W i j i' j'))).toProjective.Equation
      (transPointFst W i j i' j') :=
  equation_mapTriple W _ (equation_biChartPointFst W i j)

lemma equation_transPointSnd :
    (W.map (algebraMap R (transRing W i j i' j'))).toProjective.Equation
      (transPointSnd W i j i' j') :=
  equation_mapTriple W _ (equation_biChartPointSnd W i j)

/-- The first factor's transition map: the chart-`i'` ring maps to the overlap ring, because the
first chart-point is on the curve there and its `i'`-th coordinate is invertible. -/
noncomputable def transHomFst : affineChartRing W i' →ₐ[R] transRing W i j i' j' :=
  chartHomOfTriple W i' (transPointFst W i j i' j') (transInvFst W i j i' j')
    (transPointFst_mul_transInvFst W i j i' j') (equation_transPointFst W i j i' j')

/-- The second factor's transition map. -/
noncomputable def transHomSnd : affineChartRing W j' →ₐ[R] transRing W i j i' j' :=
  chartHomOfTriple W j' (transPointSnd W i j i' j') (transInvSnd W i j i' j')
    (transPointSnd_mul_transInvSnd W i j i' j') (equation_transPointSnd W i j i' j')

/-- **(c4.3)** The chart-product transition: the `(i',j')` chart-product ring maps to the overlap
ring, factor by factor. -/
noncomputable def transHom : biChartRing W i' j' →ₐ[R] transRing W i j i' j' :=
  (Algebra.TensorProduct.lift (transHomFst W i j i' j') (transHomSnd W i j i' j')
    fun _ _ => Commute.all _ _).comp (biChartRingTensorEquiv W i' j').toAlgHom

lemma transHom_mk_inl (p : MvPolynomial {k : Fin 3 // k ≠ i'} R) :
    transHom W i j i' j' (Ideal.Quotient.mk _ (rename Sum.inl p)) =
      transHomFst W i j i' j' (Ideal.Quotient.mk _ p) := by
  show Algebra.TensorProduct.lift (transHomFst W i j i' j') (transHomSnd W i j i' j')
      (fun _ _ => Commute.all _ _)
      (biChartRingTensorEquiv W i' j' (Ideal.Quotient.mk _ (rename Sum.inl p))) = _
  rw [biChartRingTensorEquiv_mk_rename_inl, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

lemma transHom_mk_inr (p : MvPolynomial {k : Fin 3 // k ≠ j'} R) :
    transHom W i j i' j' (Ideal.Quotient.mk _ (rename Sum.inr p)) =
      transHomSnd W i j i' j' (Ideal.Quotient.mk _ p) := by
  show Algebra.TensorProduct.lift (transHomFst W i j i' j') (transHomSnd W i j i' j')
      (fun _ _ => Commute.all _ _)
      (biChartRingTensorEquiv W i' j' (Ideal.Quotient.mk _ (rename Sum.inr p))) = _
  rw [biChartRingTensorEquiv_mk_rename_inr, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- **(c4.3, the transition on points)** The `(i',j')` chart-point of the first factor is the
`(i,j)` one, rescaled by the inverse transition coordinate. -/
lemma transHom_biChartPointFst (m : Fin 3) :
    transHom W i j i' j' (biChartPointFst W i' j' m) =
      transInvFst W i j i' j' * transPointFst W i j i' j' m := by
  rw [biChartPointFst]
  split_ifs with h
  · have hm : transPointFst W i j i' j' m = transPointFst W i j i' j' i' := by rw [h]
    rw [map_one, hm]
    exact (transPointFst_mul_transInvFst W i j i' j').symm.trans (mul_comm _ _)
  · rw [← rename_X (R := R) (Sum.inl : {k : Fin 3 // k ≠ i'} → _) ⟨m, h⟩,
      transHom_mk_inl, transHomFst, chartHomOfTriple_coord]
    exact mul_comm _ _

/-- The second-factor analogue of `transHom_biChartPointFst`. -/
lemma transHom_biChartPointSnd (m : Fin 3) :
    transHom W i j i' j' (biChartPointSnd W i' j' m) =
      transInvSnd W i j i' j' * transPointSnd W i j i' j' m := by
  rw [biChartPointSnd]
  split_ifs with h
  · have hm : transPointSnd W i j i' j' m = transPointSnd W i j i' j' j' := by rw [h]
    rw [map_one, hm]
    exact (transPointSnd_mul_transInvSnd W i j i' j').symm.trans (mul_comm _ _)
  · rw [← rename_X (R := R) (Sum.inr : {k : Fin 3 // k ≠ j'} → _) ⟨m, h⟩,
      transHom_mk_inr, transHomSnd, chartHomOfTriple_coord]
    exact mul_comm _ _

lemma transHom_comp_biChartPointFst :
    (transHom W i j i' j').toRingHom ∘ biChartPointFst W i' j' =
      transInvFst W i j i' j' • transPointFst W i j i' j' :=
  funext fun m => transHom_biChartPointFst W i j i' j' m

lemma transHom_comp_biChartPointSnd :
    (transHom W i j i' j').toRingHom ∘ biChartPointSnd W i' j' =
      transInvSnd W i j i' j' • transPointSnd W i j i' j' :=
  funext fun m => transHom_biChartPointSnd W i j i' j' m

lemma map_transHom :
    (W.map (algebraMap R (biChartRing W i' j'))).map (transHom W i j i' j').toRingHom =
      W.map (algebraMap R (transRing W i j i' j')) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  exact (transHom W i j i' j').comp_algebraMap

/-- **(c4.3, the payoff)** Under the chart-product transition, the `(i',j')` law-2 triple is the
`(i,j)` law-2 triple evaluated at the rescaled chart-points. With `dblAddXYZ_smul` (bidegree
`(2,2)`) this makes the two triples proportional, hence — by
`chartAwayHomOfTriple_congr_of_smul` — defining of the same morphism. -/
lemma transHom_lawTwoTriple :
    (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m)) =
      (W.map (algebraMap R (transRing W i j i' j'))).toProjective.dblAddXYZ
        (transInvFst W i j i' j' • transPointFst W i j i' j')
        (transInvSnd W i j i' j' • transPointSnd W i j i' j') := by
  have key := map_dblAddXYZ (W' := (W.map (algebraMap R (biChartRing W i' j'))).toProjective)
    (transHom W i j i' j').toRingHom (biChartPointFst W i' j') (biChartPointSnd W i' j')
  rw [transHom_comp_biChartPointFst, transHom_comp_biChartPointSnd] at key
  rw [← map_transHom W i j i' j'] at *
  exact key.symm

/-- The law-1 analogue of `transHom_lawTwoTriple`. -/
lemma transHom_lawOneTriple :
    (fun m => transHom W i j i' j' (lawOneTriple W i' j' m)) =
      (W.map (algebraMap R (transRing W i j i' j'))).toProjective.addXYZ
        (transInvFst W i j i' j' • transPointFst W i j i' j')
        (transInvSnd W i j i' j' • transPointSnd W i j i' j') := by
  have key := map_addXYZ (W' := (W.map (algebraMap R (biChartRing W i' j'))).toProjective)
    (f := (transHom W i j i' j').toRingHom) (P := biChartPointFst W i' j')
    (Q := biChartPointSnd W i' j')
  rw [transHom_comp_biChartPointFst, transHom_comp_biChartPointSnd] at key
  rw [← map_transHom W i j i' j'] at *
  exact key.symm

lemma map_algebraMap_transRing :
    (W.map (algebraMap R (biChartRing W i j))).map
        (algebraMap (biChartRing W i j) (transRing W i j i' j')) =
      W.map (algebraMap R (transRing W i j i' j')) := by
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

/-- The `(i,j)` law-2 triple, pushed into the overlap ring, is the law evaluated at the (unrescaled)
chart-points there. -/
lemma algebraMap_lawTwoTriple :
    (fun m => algebraMap (biChartRing W i j) (transRing W i j i' j') (lawTwoTriple W i j m)) =
      (W.map (algebraMap R (transRing W i j i' j'))).toProjective.dblAddXYZ
        (transPointFst W i j i' j') (transPointSnd W i j i' j') := by
  have key := map_dblAddXYZ (W' := (W.map (algebraMap R (biChartRing W i j))).toProjective)
    (algebraMap (biChartRing W i j) (transRing W i j i' j'))
    (biChartPointFst W i j) (biChartPointSnd W i j)
  rw [← map_algebraMap_transRing W i j i' j'] at *
  exact key.symm

/-- The law-1 analogue of `algebraMap_lawTwoTriple`. -/
lemma algebraMap_lawOneTriple :
    (fun m => algebraMap (biChartRing W i j) (transRing W i j i' j') (lawOneTriple W i j m)) =
      (W.map (algebraMap R (transRing W i j i' j'))).toProjective.addXYZ
        (transPointFst W i j i' j') (transPointSnd W i j i' j') := by
  have key := map_addXYZ (W' := (W.map (algebraMap R (biChartRing W i j))).toProjective)
    (f := algebraMap (biChartRing W i j) (transRing W i j i' j'))
    (P := biChartPointFst W i j) (Q := biChartPointSnd W i j)
  rw [← map_algebraMap_transRing W i j i' j'] at *
  exact key.symm

/-- **(c4.3, the cross-chart-product agreement — ring level)** Over the overlap ring, the law-2
chart morphism computed in the `(i',j')` chart-product is the one computed in the `(i,j)`
chart-product.

Nothing is inverted or transported by hand: the two triples are the law evaluated at chart-points
that differ by the transition scalars, the law is bidegree `(2,2)`
(`chartAwayHomOfTriple_dblAddXYZ_smul`), and a chart morphism does not see scalars. -/
theorem chartAwayHomOfTriple_lawTwoTriple_trans (k : Fin 3) (u u' : transRing W i j i' j')
    (hu : (fun m => algebraMap (biChartRing W i j) _ (lawTwoTriple W i j m)) k * u = 1)
    (hu' : (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m)) k * u' = 1)
    (ht : (W.map (algebraMap R (transRing W i j i' j'))).toProjective.Equation
      (fun m => algebraMap (biChartRing W i j) _ (lawTwoTriple W i j m)))
    (ht' : (W.map (algebraMap R (transRing W i j i' j'))).toProjective.Equation
      (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m))) :
    chartAwayHomOfTriple W k (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m)) u' hu' ht' =
      chartAwayHomOfTriple W k
        (fun m => algebraMap (biChartRing W i j) _ (lawTwoTriple W i j m)) u hu ht := by
  rw [chartAwayHomOfTriple_congr W k _ _ u' (transHom_lawTwoTriple W i j i' j') hu' ht'
      (by rw [← transHom_lawTwoTriple W i j i' j']; exact hu')
      (by rw [← transHom_lawTwoTriple W i j i' j']; exact ht'),
    chartAwayHomOfTriple_congr W k _ _ u (algebraMap_lawTwoTriple W i j i' j') hu ht
      (by rw [← algebraMap_lawTwoTriple W i j i' j']; exact hu)
      (by rw [← algebraMap_lawTwoTriple W i j i' j']; exact ht)]
  exact chartAwayHomOfTriple_dblAddXYZ_smul W k _ _ _ _ u u' _ _ _ _

end

section Inclusions

lemma biChartPointFst_self : biChartPointFst W i j i * 1 = 1 := by
  rw [biChartPointFst, dif_pos rfl, one_mul]

lemma biChartPointSnd_self : biChartPointSnd W i j j * 1 = 1 := by
  rw [biChartPointSnd, dif_pos rfl, one_mul]

/-- **(the bridge to the geometry)** The left inclusion `affineChartRing W i → biChartRing W i j`
— the ring map underlying `pullback.fst` of the `(i,j)` chart-product — is the chart morphism of the
first tautological point.

This is what lets the crux `chartι_comp_specMap_chartAwayHom_eq` discharge the SOURCE-side chart
compatibility, exactly as it discharges the target side: both legs of the chart-product, and both
legs of the transition, are `chartHomOfTriple`s of on-curve triples. -/
lemma chartHomOfTriple_biChartPointFst :
    chartHomOfTriple W i (biChartPointFst W i j) 1 (biChartPointFst_self W i j)
        (equation_biChartPointFst W i j) =
      (biChartRingTensorEquiv W i j).symm.toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (S := R)) := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun m => ?_)
  show chartHomOfTriple W i (biChartPointFst W i j) 1 (biChartPointFst_self W i j)
      (equation_biChartPointFst W i j) (Ideal.Quotient.mk _ (X m)) =
    (biChartRingTensorEquiv W i j).symm (Ideal.Quotient.mk _ (X m) ⊗ₜ[R] 1)
  rw [chartHomOfTriple_coord, mul_one]
  refine ((biChartRingTensorEquiv W i j).symm_apply_eq).mpr ?_ |>.symm
  rw [biChartPointFst, dif_neg m.2, ← rename_X (R := R) (Sum.inl : {k : Fin 3 // k ≠ i} → _) m,
    biChartRingTensorEquiv_mk_rename_inl]

/-- The second-factor analogue of `chartHomOfTriple_biChartPointFst`. -/
lemma chartHomOfTriple_biChartPointSnd :
    chartHomOfTriple W j (biChartPointSnd W i j) 1 (biChartPointSnd_self W i j)
        (equation_biChartPointSnd W i j) =
      (biChartRingTensorEquiv W i j).symm.toAlgHom.comp
        (Algebra.TensorProduct.includeRight (R := R)) := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun m => ?_)
  show chartHomOfTriple W j (biChartPointSnd W i j) 1 (biChartPointSnd_self W i j)
      (equation_biChartPointSnd W i j) (Ideal.Quotient.mk _ (X m)) =
    (biChartRingTensorEquiv W i j).symm (1 ⊗ₜ[R] Ideal.Quotient.mk _ (X m))
  rw [chartHomOfTriple_coord, mul_one]
  refine ((biChartRingTensorEquiv W i j).symm_apply_eq).mpr ?_ |>.symm
  rw [biChartPointSnd, dif_neg m.2, ← rename_X (R := R) (Sum.inr : {k : Fin 3 // k ≠ j} → _) m,
    biChartRingTensorEquiv_mk_rename_inr]

end Inclusions

end WeierstrassCurve.Projective
