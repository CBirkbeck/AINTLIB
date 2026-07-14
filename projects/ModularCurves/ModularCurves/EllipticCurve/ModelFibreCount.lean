import ModularCurves.EllipticCurve.MulByHomFibres

/-!
# The model fibre-count (BB-QF, ALPHA leg)

Topological input for the BB-QF wall-break, entirely on the affine side of the projective
Weierstrass model: for `W` an elliptic Weierstrass curve over a field `K`,

* **[KEY-INF]** `PrimeSpectrum W.CoordinateRing` is infinite — the coordinate ring is a
  Jacobson domain (finitely generated over a field) that is not a field, and a Jacobson
  domain with finitely many maximal ideals has `∩ maximals = nilradical = ⊥`, forcing a
  product of nonzero elements to vanish.
* **[KEY-TOP]** every irreducible closed subset of `Spec W.CoordinateRing` is either a
  single closed point or the whole space — `dim ≤ 1` (`coordinateRing_krullDimLE_one`)
  makes every nonzero prime maximal, and `V(m) = {m}`.

These feed the fibre-count case analysis on `projModel W` (whose complement of the affine
`zChart` is contained in the single-point range of the zero section), which the BETA leg's
transport assembly consumes.
-/

open AlgebraicGeometry CategoryTheory WeierstrassCurve

universe u

namespace ModularCurves

section JacobsonInfinite

variable {R : Type u} [CommRing R] [IsDomain R] [IsJacobsonRing R]

/-- **A Jacobson domain that is not a field has infinitely many maximal ideals.** With
finitely many maximals `m₁, …, m_r` (all nonzero since `R` is not a field), a choice of
`0 ≠ aᵢ ∈ mᵢ` gives `∏ aᵢ ∈ ∩ mᵢ = jacobson ⊥ = nilradical = ⊥`, contradicting
domain-ness. -/
theorem infinite_setOf_isMaximal_of_not_isField (hR : ¬ IsField R) :
    {I : Ideal R | I.IsMaximal}.Infinite := by
  intro hfin
  -- every maximal ideal is nonzero
  have hne : ∀ I ∈ hfin.toFinset, ∃ a : R, a ∈ I ∧ a ≠ 0 := by
    intro I hI
    rw [Set.Finite.mem_toFinset] at hI
    exact Submodule.exists_mem_ne_zero_of_ne_bot
      (Ring.ne_bot_of_isMaximal_of_not_isField hI hR)
  choose a ha ha0 using hne
  -- the product of the chosen elements lies in every maximal ideal
  have hmem : ∀ I (hI : I ∈ hfin.toFinset), ∏ J ∈ hfin.toFinset.attach, a J.1 J.2 ∈ I := by
    intro I hI
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach hfin.toFinset ⟨I, hI⟩)]
    exact Ideal.mul_mem_right _ _ (ha I hI)
  -- hence in the Jacobson radical of ⊥, which is ⊥ in a Jacobson domain
  have hjac : ∏ J ∈ hfin.toFinset.attach, a J.1 J.2 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ideal.jacobson]
    refine Ideal.mem_sInf.mpr fun {J} hJ => hmem J ?_
    exact (Set.Finite.mem_toFinset _).mpr hJ.2
  rw [IsJacobsonRing.out ‹IsJacobsonRing R›
    (Ideal.radical_bot_of_noZeroDivisors (R := R) ▸ Ideal.radical_isRadical (⊥ : Ideal R))] at hjac
  obtain ⟨⟨J, hJ⟩, -, hz⟩ := Finset.prod_eq_zero_iff.mp (Ideal.mem_bot.mp hjac)
  exact ha0 J hJ hz

/-- A Jacobson domain that is not a field has infinite prime spectrum. -/
theorem infinite_primeSpectrum_of_not_isField (hR : ¬ IsField R) :
    Infinite (PrimeSpectrum R) := by
  haveI := Set.infinite_coe_iff.mpr (infinite_setOf_isMaximal_of_not_isField (R := R) hR)
  exact Infinite.of_injective
    (fun I : {I : Ideal R | I.IsMaximal} => (⟨I.1, I.2.isPrime⟩ : PrimeSpectrum R))
    fun I J hIJ => Subtype.ext (congrArg PrimeSpectrum.asIdeal hIJ)

end JacobsonInfinite

section DimOneTopology

variable {R : Type u} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]

/-- **Irreducible closed subsets of a `dim ≤ 1` affine spectrum are points or
everything**: the vanishing ideal is prime; if `⊥` the set is the whole space, otherwise
it is maximal and the zero locus is the corresponding singleton. -/
theorem isClosed_isIrreducible_singleton_or_univ {C : Set (PrimeSpectrum R)}
    (hCc : IsClosed C) (hCi : IsIrreducible C) :
    (∃ x, C = {x}) ∨ C = Set.univ := by
  have hC : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set R) = C := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hCc.closure_eq]
  haveI hp : (PrimeSpectrum.vanishingIdeal C).IsPrime :=
    (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hCi)
  rcases eq_or_ne (PrimeSpectrum.vanishingIdeal C) ⊥ with hbot | hbot
  · right
    rw [← hC, hbot]
    simpa using PrimeSpectrum.zeroLocus_bot
  · left
    haveI hmax := hp.isMaximal_of_ne_bot hbot
    refine ⟨⟨PrimeSpectrum.vanishingIdeal C, hp⟩, ?_⟩
    have hZ : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set R)
        = {⟨PrimeSpectrum.vanishingIdeal C, hp⟩} := by
      ext x
      simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff]
      constructor
      · intro hx
        have hle : PrimeSpectrum.vanishingIdeal C ≤ x.asIdeal := hx
        exact PrimeSpectrum.ext (hmax.eq_of_le x.isPrime.ne_top hle).symm
      · rintro rfl
        exact subset_rfl
    exact hC.symm.trans hZ


end DimOneTopology

/-! ### The coordinate ring is a Jacobson non-field

`W.CoordinateRing` is module-finite over `K[X]` (the power basis `{1, y}`), hence
integral, so it inherits Jacobson-ness from `K[X]` and — being a domain mapping
injectively from `K[X]` — cannot be a field (else `K[X]` would be one). Together with
`coordinateRing_krullDimLE_one` this activates the whole `DimOne`/`Jacobson` toolkit
above for the affine chart of the projective model. -/

section CoordinateRingInstances

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

noncomputable instance : Module.Finite (Polynomial K) W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)

instance : Algebra.IsIntegral (Polynomial K) W.toAffine.CoordinateRing :=
  Algebra.IsIntegral.of_finite _ _

instance : IsJacobsonRing W.toAffine.CoordinateRing :=
  isJacobsonRing_of_isIntegral (R := Polynomial K)

/-- The structure map `K[X] → K[W]` is injective (`AdjoinRoot.of` of a degree-`2`
polynomial over a domain). -/
theorem coordinateRing_algebraMap_injective :
    Function.Injective (algebraMap (Polynomial K) W.toAffine.CoordinateRing) := by
  have hdeg : (W.toAffine.polynomial).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree W.toAffine.monic_polynomial.ne_zero,
      WeierstrassCurve.Affine.natDegree_polynomial]
    exact Nat.cast_ne_zero.mpr two_ne_zero
  exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg

/-- **The coordinate ring of a Weierstrass curve is not a field**: it is integral over
`K[X]` with injective structure map, and `K[X]` is not a field. -/
theorem not_isField_coordinateRing : ¬ IsField W.toAffine.CoordinateRing := fun hF =>
  Polynomial.not_isField K
    (isField_of_isIntegral_of_isField (R := Polynomial K)
      (coordinateRing_algebraMap_injective W) hF)

end CoordinateRingInstances

end ModularCurves
