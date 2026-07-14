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

/-! ### The generic curve-topology fibre-count

Pure topology: on a `T0` Noetherian space in which every irreducible closed subset is
finite or everything ("curvelike"), a continuous closed self-map with infinite range has
finite fibres. This is KM 2.3.1's "a nonconstant morphism of proper smooth connected
curves has finite fibres", axiomatised so the scheme side only has to supply the three
inputs (curvelike-ness from `dim ≤ 1` charts, infinitude from Jacobson-ness, infinite
range from the HasseWeil torsion witness). -/

section CurvelikeFibres

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [T0Space X] [NoetherianSpace X] [Infinite X]

/-- **Fibre finiteness on a curvelike space.** If every irreducible closed subset of `X`
is finite or all of `X`, and `f : X → X` is continuous, closed, with infinite range,
then every fibre `f ⁻¹' {y}` is finite. -/
theorem Curvelike.finite_preimage_singleton
    (hclass : ∀ C : Set X, IsClosed C → IsIrreducible C → C.Finite ∨ C = Set.univ)
    {f : X → X} (hfc : Continuous f) (hfcl : IsClosedMap f)
    (hfim : (Set.range f).Infinite) (y : X) : (f ⁻¹' {y}).Finite := by
  rcases hclass (closure {y}) isClosed_closure (isIrreducible_singleton.closure)
    with hyfin | hyuniv
  · -- `closure {y}` finite: an infinite preimage would force `f⁻¹(closure {y}) = X`,
    -- making the whole range land in the finite `closure {y}`.
    by_contra hinf
    rw [Set.not_finite] at hinf
    have hCy : (f ⁻¹' closure {y}).Infinite :=
      hinf.mono (Set.preimage_mono subset_closure)
    have hCyc : IsClosed (f ⁻¹' closure {y}) := isClosed_closure.preimage hfc
    -- decompose the closed set into finitely many irreducible closeds; one is infinite
    obtain ⟨S, hSfin, hSc, hSi, hSU⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hCyc
    have hZ : ∃ Z ∈ S, Z.Infinite := by
      by_contra hall
      push_neg at hall
      exact hCy (hSU ▸ Set.Finite.sUnion hSfin fun t ht => hall t ht)
    obtain ⟨Z, hZS, hZinf⟩ := hZ
    have hZuniv : Z = Set.univ := by
      rcases hclass Z (hSc Z hZS) (hSi Z hZS) with h | h
      · exact absurd h hZinf
      · exact h
    have hrange : Set.range f ⊆ closure {y} := by
      rintro b ⟨x, rfl⟩
      have hxC : x ∈ f ⁻¹' closure {y} := by
        rw [hSU]
        exact Set.subset_sUnion_of_mem hZS (hZuniv ▸ Set.mem_univ x)
      exact hxC
    exact hfim (hyfin.subset hrange)
  · -- `closure {y} = univ`: `y` is the unique generic point; any `x` in the fibre has
    -- `f(closure {x}) = X`, so `closure {x}` is infinite, hence everything — so the
    -- fibre is a subsingleton by `T0`.
    have hgen : ∀ x ∈ f ⁻¹' {y}, closure ({x} : Set X) = Set.univ := by
      intro x hx
      have hcl : IsClosed (f '' closure {x}) := hfcl _ isClosed_closure
      have hy : y ∈ f '' closure {x} := ⟨x, subset_closure rfl, hx⟩
      have himg : f '' closure {x} = Set.univ :=
        Set.eq_univ_of_univ_subset
          (hyuniv ▸ closure_minimal (Set.singleton_subset_iff.mpr hy) hcl)
      have hclx_inf : (closure ({x} : Set X)).Infinite := by
        intro hfin
        have : (Set.univ : Set X).Finite := himg ▸ hfin.image f
        exact Set.infinite_univ this
      rcases hclass (closure {x}) isClosed_closure (isIrreducible_singleton.closure)
        with h | h
      · exact absurd h hclx_inf
      · exact h
    refine Set.Subsingleton.finite fun x hx x' hx' => ?_
    have h1 := hgen x hx
    have h2 := hgen x' hx'
    exact (inseparable_iff_closure_eq.mpr (h1.trans h2.symm)).eq

end CurvelikeFibres

/-! ### Instantiation on the projective model

The four inputs of `Curvelike.finite_preimage_singleton` for `X := projModel W` over a
field, as named leaves: the chart homeomorphism, the curvelike classification (chart
transfer + finite complement), infinitude, and the Noetherian instance. The HasseWeil
range-infinitude witness is the remaining ALPHA leaf, consumed as a hypothesis by the
assembly so everything below it is sorry-free. -/

section ProjModelCurvelike

open EllipticCurve

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **(leaf g1)** The affine chart of the projective model, as a homeomorphism onto the
spectrum of the coordinate ring: `isoSpec` for the affine `zChart` composed with
`Spec` of `zChartSectionCoordRingEquiv`. -/
noncomputable def zChartHomeo :
    ((zChart W).toScheme : Scheme.{u}) ≃ₜ PrimeSpectrum W.toAffine.CoordinateRing :=
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : IsAffine (zChart W).toScheme := hZaff
  Scheme.homeoOfIso ((zChart W).toScheme.isoSpec ≪≫
    Scheme.Spec.mapIso ((zChartSectionCoordRingEquiv W).toCommRingCatIso).symm.op)

/-- **(leaf g3, DISCHARGED)** The projective model is topologically infinite: the chart
carrier is homeomorphic to the infinite `Spec K[W]`, and the chart inclusion is
injective. -/
theorem projModel_infinite' : Infinite (projModel W) := by
  haveI := coordinateRing_krullDimLE_one W
  haveI : Infinite (PrimeSpectrum W.toAffine.CoordinateRing) :=
    infinite_primeSpectrum_of_not_isField (not_isField_coordinateRing W)
  haveI : Infinite ((zChart W).toScheme : Scheme.{u}) := (zChartHomeo W).symm.injective
    |> Infinite.of_injective _
  exact Infinite.of_injective ((zChart W).ι).base
    ((zChart W).ι.isOpenEmbedding.injective)

/-- Preirreducibility reflects along open embeddings (preimage form). -/
theorem IsPreirreducible.preimage_isOpenEmbedding {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set Y} (hs : IsPreirreducible s) {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) : IsPreirreducible (f ⁻¹' s) := by
  intro u v hu hv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩
  obtain ⟨w, hws, hwu, hwv⟩ := hs (f '' u) (f '' v) (hf.isOpenMap u hu) (hf.isOpenMap v hv)
    ⟨f a, has, ⟨a, hau, rfl⟩⟩ ⟨f b, hbs, ⟨b, hbv, rfl⟩⟩
  obtain ⟨a', hau', rfl⟩ := hwu
  obtain ⟨b', hbv', hb'⟩ := hwv
  exact ⟨a', hws, hau', hf.injective hb'.symm ▸ hbv'⟩

/-- **(leaf g2, DISCHARGED)** The projective Weierstrass model is curvelike: every
irreducible closed subset is finite or everything — chart transfer of the `dim ≤ 1`
classification plus the single-point off-chart complement. -/
theorem projModel_isClosed_isIrreducible_finite_or_univ
    {C : Set (projModel W)} (hCc : IsClosed C) (hCi : IsIrreducible C) :
    C.Finite ∨ C = Set.univ := by
  haveI := coordinateRing_krullDimLE_one W
  set U : Set (projModel W) := (zChart W : Set (projModel W)) with hUdef
  set ι : ((zChart W).toScheme : Scheme.{u}) → projModel W := ⇑(((zChart W).ι).base) with hιdef
  have hιemb : Topology.IsOpenEmbedding ι := ((zChart W).ι).isOpenEmbedding
  have hUrange : Set.range ι = U := Scheme.Opens.range_ι _
  by_cases hU : (C ∩ U).Nonempty
  · -- the chart slice, transported to `Spec K[W]`
    have hApre : IsPreirreducible (ι ⁻¹' C) :=
      IsPreirreducible.preimage_isOpenEmbedding hCi.2 hιemb
    have hAne : (ι ⁻¹' C).Nonempty := by
      obtain ⟨x, hxC, hxU⟩ := hU
      obtain ⟨a, rfl⟩ := hUrange ▸ hxU
      exact ⟨a, hxC⟩
    have hAc : IsClosed (ι ⁻¹' C) := hCc.preimage (Scheme.Hom.continuous _)
    set h := zChartHomeo W with hhdef
    have hDc : IsClosed (h '' (ι ⁻¹' C)) := h.isClosedMap _ hAc
    have hDi : IsIrreducible (h '' (ι ⁻¹' C)) :=
      IsIrreducible.image ⟨hAne, hApre⟩ _ h.continuous.continuousOn
    rcases isClosed_isIrreducible_singleton_or_univ hDc hDi with ⟨d, hd⟩ | hduniv
    · -- singleton case: `C ∩ U = {x₀}` and `closure {x₀} ⊆ {x₀} ∪ Uᶜ ⊆ {x₀} ∪ (finite)`
      left
      have hA : ι ⁻¹' C = {h.symm d} := by
        have := congrArg (fun t => h.symm '' t) hd
        simpa [Set.image_image, Set.image_singleton] using this
      have hCU : C ∩ U = {ι (h.symm d)} := by
        rw [← hUrange, ← Set.image_preimage_eq_inter_range, hA, Set.image_singleton]
      -- density of the chart slice in `C`
      have hdense : C ⊆ closure (C ∩ U) := by
        intro c hc
        rw [mem_closure_iff]
        intro V hVopen hcV
        obtain ⟨w, hwC, hwV, hwU⟩ := hCi.2 V U hVopen (zChart W).2 ⟨c, hc, hcV⟩ hU
        exact ⟨w, hwV, hwC, hwU⟩
      -- the chart point is closed in the chart, so its closure adds only off-chart points
      have hclosure : closure ({ι (h.symm d)} : Set (projModel W)) ⊆
          {ι (h.symm d)} ∪ Uᶜ := by
        intro y hy
        by_cases hyU : y ∈ U
        · left
          obtain ⟨b, rfl⟩ := hUrange ▸ hyU
          have hbA : b ∈ ι ⁻¹' C := by
            rw [hA]
            have hbcl : b ∈ closure ({h.symm d} : Set _) := by
              rw [mem_closure_iff]
              intro O hOopen hbO
              have hmeet := (mem_closure_iff.mp hy) (ι '' O) (hιemb.isOpenMap O hOopen)
                ⟨b, hbO, rfl⟩
              obtain ⟨z, hzO, hz1⟩ := hmeet
              obtain ⟨a', ha'O, ha'z⟩ := hzO
              rw [Set.mem_singleton_iff] at hz1
              have ha'd : a' = h.symm d := hιemb.injective (ha'z.trans hz1)
              exact ⟨h.symm d, ha'd ▸ ha'O, rfl⟩
            have hAcl : closure ({h.symm d} : Set _) = {h.symm d} := by
              rw [← hA]
              exact hAc.closure_eq
            rwa [hAcl] at hbcl
          rw [hA] at hbA
          exact congrArg ι hbA
        · right; exact hyU
      have hCsub : C ⊆ {ι (h.symm d)} ∪ Uᶜ := fun c hc => by
        have := hdense hc
        rw [hCU] at this
        exact hclosure this
      refine Set.Finite.subset ?_ hCsub
      refine (Set.finite_singleton _).union (Set.Finite.subset
        (Set.finite_range (projModelZero W).base) fun x hx => ?_)
      exact mem_range_zero_of_not_mem_zChart hx
    · -- univ case: the chart lies in `C`, and a closed set containing a nonempty open
      -- of an irreducible space is everything
      right
      have hUC : U ⊆ C := by
        intro x hxU
        obtain ⟨a, rfl⟩ := hUrange ▸ hxU
        have : (h a) ∈ h '' (ι ⁻¹' C) := hduniv ▸ Set.mem_univ _
        obtain ⟨a', ha', haa⟩ := this
        exact h.injective haa ▸ ha'
      by_contra hne
      have hCcne : Cᶜ.Nonempty := Set.nonempty_compl.mpr hne
      obtain ⟨w, hw⟩ := nonempty_preirreducible_inter hCc.isOpen_compl
        ((zChart W).2) hCcne ⟨hU.choose, hU.choose_spec.2⟩
      exact hw.1 (hUC hw.2)
  · -- no chart points: `C` sits in the single-point complement
    left
    refine Set.Finite.subset (Set.finite_range (projModelZero W).base) fun x hx => ?_
    exact mem_range_zero_of_not_mem_zChart fun hmem => hU ⟨x, hx, hmem⟩

/-- **(leaf g3)** The projective model is topologically infinite (the chart is the
spectrum of a Jacobson non-field domain). -/
theorem projModel_infinite : Infinite (projModel W) :=
  projModel_infinite' W

/-- **(leaf g4, DISCHARGED)** The projective model is a Noetherian topological space:
every open is the union of a compact chart piece (any subset of the Noetherian
`Spec K[W]` is compact) and a finite off-chart piece (inside the single-point range of
the zero section). -/
theorem projModel_noetherianSpace : TopologicalSpace.NoetherianSpace (projModel W) := by
  haveI : TopologicalSpace.NoetherianSpace ((zChart W).toScheme : Scheme.{u}) := by
    rw [TopologicalSpace.noetherianSpace_iff_opens]
    intro s
    exact (zChartHomeo W).isCompact_image.mp
      (TopologicalSpace.NoetherianSpace.isCompact _)
  rw [TopologicalSpace.noetherianSpace_iff_opens]
  intro V
  have hUrange : Set.range ((zChart W).ι).base = (zChart W : Set (projModel W)) :=
    Scheme.Opens.range_ι _
  have hV : (V : Set (projModel W)) =
      (((zChart W).ι).base '' (((zChart W).ι).base ⁻¹' (V : Set (projModel W)))) ∪
        ((V : Set (projModel W)) \ (zChart W : Set (projModel W))) := by
    rw [Set.image_preimage_eq_inter_range, hUrange]
    exact (Set.inter_union_diff _ _).symm
  rw [hV]
  refine IsCompact.union ?_ ?_
  · exact (TopologicalSpace.NoetherianSpace.isCompact _).image
      (Scheme.Hom.continuous _)
  · refine Set.Finite.isCompact (Set.Finite.subset (Set.finite_range
      (projModelZero W).base) fun x hx => ?_)
    exact mem_range_zero_of_not_mem_zChart hx.2

/-- **THE MODEL FIBRE-COUNT (assembly; sorry-free given the leaves).** If the range of
`[N]` on the projective model is topologically infinite (the HasseWeil witness, the
remaining ALPHA leaf), then every fibre of `[N]` is finite. -/
theorem modelMulByHom_finite_preimage_singleton (N : ℤ)
    (hfim : (Set.range ((modelEllipticCurve W).mulByHom N).base).Infinite)
    (y : projModel W) :
    (((modelEllipticCurve W).mulByHom N).base ⁻¹' {y}).Finite := by
  haveI := projModel_noetherianSpace W
  haveI := projModel_infinite W
  haveI : IsProper ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_isProper N
  exact Curvelike.finite_preimage_singleton
    (fun C hCc hCi => projModel_isClosed_isIrreducible_finite_or_univ W hCc hCi)
    (Scheme.Hom.continuous _)
    ((modelEllipticCurve W).mulByHom N).isClosedMap
    hfim y

end ProjModelCurvelike

/-! ### g5 — the range-infinitude witness (HasseWeil import; ALPHA's last leaf)

Over an algebraically closed field: pick a prime `ℓ` exceeding both `|N|` and the
characteristic exponent (w1); `#E[ℓⁿ] = ℓ²ⁿ` (HasseWeil `card_torsion_ellPow_nat`, w2);
`N•` is injective on `E[ℓⁿ]` since `N` is a unit mod `ℓⁿ` (w3); so the image of `N•` on
the point group is infinite (w4); transport points to sections of the projective model
(`projModelPointsEquivEll` at `K := F`, `baseChange_self`/`map_id`, w5), `N•` to
composition with `[N]` (`projModelPointsEquiv_zsmul`-family, w6); distinct `F`-rational
sections over an algebraically closed field have distinct image points (residue field
`= F`, w7) — so the topological range of `[N]` is infinite. The non-closed-base descent
(closed points, finite `κ(w) ⊗ κ̄` fibres) is the BETA-side κ-descent step boarded at
v10.221. -/

section RangeWitness

open scoped Classical in
/-- **(g5, alg-closed case — TODO w1–w7 per the section header)** The topological range
of `[N]` on the projective model over an algebraically closed field is infinite. -/
theorem modelMulByHom_range_infinite {F : Type u} [Field F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℤ) (hN : N ≠ 0) :
    (Set.range ((modelEllipticCurve W).mulByHom N).base).Infinite := by
  sorry

end RangeWitness

end ModularCurves
