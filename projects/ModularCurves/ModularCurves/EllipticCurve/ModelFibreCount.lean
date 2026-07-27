import ModularCurves.EllipticCurve.MulByHomFibres
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

/-- **(w1)** For `N ≠ 0` over any field there is a prime `ℓ` not dividing `N` with
`(ℓ : F) ≠ 0`: any prime beyond `max |N| (ringChar F)` works. -/
theorem exists_good_prime (F : Type u) [Field F] (N : ℤ) (hN : N ≠ 0) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ((ℓ : ℤ) ∣ N) ∧ (ℓ : F) ≠ 0 := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (max N.natAbs (ringChar F) + 1)
  have hgtN : N.natAbs < ℓ := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_of_succ_le hle)
  have hgtC : ringChar F < ℓ := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_of_succ_le hle)
  refine ⟨ℓ, hℓ, fun hdvd => ?_, fun h0 => ?_⟩
  · have h1 : ℓ ∣ N.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd)
    have h2 : ℓ ≤ N.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1
    omega
  · have hchar : ringChar F ∣ ℓ := ringChar.dvd (by exact_mod_cast h0)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hℓ _ hchar) with h1 | h1
    · exact CharP.ringChar_ne_one (R := F) h1
    · omega

/-- **(w3)** Multiplication by `N` is injective on `ℓⁿ`-torsion elements of any abelian
group when the prime `ℓ` does not divide `N` (Bézout: `N` is invertible mod `ℓⁿ`). -/
theorem zsmul_injOn_torsionBy {G : Type u} [AddCommGroup G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {N : ℤ} (hdvd : ¬ ((ℓ : ℤ) ∣ N)) (n : ℕ) {P Q : G}
    (hP : ((ℓ : ℤ) ^ n) • P = 0) (hQ : ((ℓ : ℤ) ^ n) • Q = 0)
    (h : N • P = N • Q) : P = Q := by
  have hcop : IsCoprime N ((ℓ : ℤ) ^ n) :=
    ((((Nat.prime_iff_prime_int.mp hℓ)).coprime_iff_not_dvd.mpr hdvd).symm).pow_right
  obtain ⟨a, b, hab⟩ := hcop
  have key : ∀ R : G, ((ℓ : ℤ) ^ n) • R = 0 → R = a • (N • R) := by
    intro R hR
    calc R = (1 : ℤ) • R := (one_smul ℤ R).symm
      _ = (a * N + b * (ℓ : ℤ) ^ n) • R := by rw [hab]
      _ = a • (N • R) + b • (((ℓ : ℤ) ^ n) • R) := by
          rw [add_smul, mul_smul, mul_smul]
      _ = a • (N • R) := by rw [hR, smul_zero, add_zero]
  rw [key P hP, key Q hQ, h]

/-- Dependent-point congruence for `descResidueField ∘ stalkClosedPointTo` on `Spec F`:
equal morphisms give descents matching across `residueFieldCongr` (the rintro-rfl
generalization trick — never rewrite a morphism equality under `stalkClosedPointTo`). -/
theorem descResidueField_stalkClosedPointTo_congr {F : Type u} [Field F]
    (g₁ g₂ : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F)) (hg : g₁ = g₂)
    (e : g₁.base (IsLocalRing.closedPoint F) = g₂.base (IsLocalRing.closedPoint F)) :
    Scheme.descResidueField (Scheme.stalkClosedPointTo g₁)
      = (Scheme.residueFieldCongr e).hom ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) := by
  subst hg
  simp

/-- The canonical sections-to-residue composite retracts the descent of any morphism
equal to the identity: `σ = id` — the triangle killing the twisted endomorphism in the
`hiso` leaf (stated for a variable morphism so the `IsLocalHom` instance fires). -/
theorem phi0_desc_stalkClosedPointTo_of_eq_id {F : Type u} [Field F]
    (g : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F)) (hg : g = 𝟙 _) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec (CommRingCat.of F)).presheaf.germ ⊤ (g.base (IsLocalRing.closedPoint F))
        trivial ≫
      (Spec (CommRingCat.of F)).residue (g.base (IsLocalRing.closedPoint F)) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo g)
    = 𝟙 (CommRingCat.of F) := by
  subst hg
  rw [Scheme.residue_descResidueField]
  have h := AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec (𝟙 (CommRingCat.of F))
  rw [Spec.map_id] at h
  rw [h]
  simp

/-- **(w7)** Distinct sections of a scheme over `Spec F`, `F` a field, have distinct
image points whenever their common image point has residue field `F` — over an
algebraically closed base every rational section is determined by its topological
point. Route: a section factors through `Spec κ(x) → X` (`fromSpecResidueField`), and
`F → κ(x) → F` forces the residue comparison to be the identity. -/
theorem section_base_injective_of_isAlgClosed {F : Type u} [Field F] [IsAlgClosed F]
    {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of F))
    (P Q : { g : Spec (CommRingCat.of F) ⟶ X // g ≫ π = 𝟙 _ })
    (h : ∀ p : Spec (CommRingCat.of F), P.1.base p = Q.1.base p) : P = Q := by
  apply Subtype.ext
  apply (Scheme.SpecToEquivOfField F X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨h _, ?_⟩
  -- the two `descResidueField ∘ stalkClosedPointTo` composition identities, brought to
  -- the common `𝟙`-source by the generalization trick
  have key : ∀ (g₁ g₂ : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F)) (hg : g₁ = g₂)
      (e : g₁.base (IsLocalRing.closedPoint F) = g₂.base (IsLocalRing.closedPoint F)),
      Scheme.descResidueField (Scheme.stalkClosedPointTo g₁)
        = (Scheme.residueFieldCongr e).hom ≫
            Scheme.descResidueField (Scheme.stalkClosedPointTo g₂) := by
    rintro g₁ g₂ rfl e
    simp
  have e' : (P.1 ≫ π).base (IsLocalRing.closedPoint F)
      = (Q.1 ≫ π).base (IsLocalRing.closedPoint F) := by
    rw [P.2, Q.2]
  have hcP := Scheme.descResidueField_stalkClosedPointTo_comp (f := π) P.1
  have hcQ := Scheme.descResidueField_stalkClosedPointTo_comp (f := π) Q.1
  have hlink := key (P.1 ≫ π) (Q.1 ≫ π) (P.2.trans Q.2.symm) e'
  have hchain := hcP.symm.trans (hlink.trans
    (congrArg (fun t => (Scheme.residueFieldCongr e').hom ≫ t) hcQ))
  -- naturality of the point-congruence under `residueFieldMap`
  have natMap : ∀ {x y : ↥X} (e : x = y) (eY : π.base x = π.base y),
      (Scheme.residueFieldCongr eY).hom ≫ π.residueFieldMap y
        = π.residueFieldMap x ≫ (Scheme.residueFieldCongr e).hom := by
    rintro x y rfl eY
    simp
  -- the descents are SPLIT EPIS (canonical retraction triangles) and monos (field
  -- homs), hence isos; the congruence identity then follows from the canonical maps.
  have htriP0 := phi0_desc_stalkClosedPointTo_of_eq_id (P.1 ≫ π) P.2
  have htriQ0 := phi0_desc_stalkClosedPointTo_of_eq_id (Q.1 ≫ π) Q.2
  have htriP := (congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec (CommRingCat.of F)).presheaf.germ ⊤
        ((P.1 ≫ π) (IsLocalRing.closedPoint F)) trivial ≫
      (Spec (CommRingCat.of F)).residue
        ((P.1 ≫ π) (IsLocalRing.closedPoint F)) ≫ t) hcP).symm.trans htriP0
  have htriQ := (congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec (CommRingCat.of F)).presheaf.germ ⊤
        ((Q.1 ≫ π) (IsLocalRing.closedPoint F)) trivial ≫
      (Spec (CommRingCat.of F)).residue
        ((Q.1 ≫ π) (IsLocalRing.closedPoint F)) ≫ t) hcQ).symm.trans htriQ0
  have hsecP : ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec (CommRingCat.of F)).presheaf.germ ⊤
        ((P.1 ≫ π) (IsLocalRing.closedPoint F)) trivial) ≫
      (Spec (CommRingCat.of F)).residue
        ((P.1 ≫ π) (IsLocalRing.closedPoint F))) ≫
      π.residueFieldMap (P.1 (IsLocalRing.closedPoint F))) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo P.1) = 𝟙 _ := by
    exact htriP
  have hsecQ : ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
      (Spec (CommRingCat.of F)).presheaf.germ ⊤
        ((Q.1 ≫ π) (IsLocalRing.closedPoint F)) trivial) ≫
      (Spec (CommRingCat.of F)).residue
        ((Q.1 ≫ π) (IsLocalRing.closedPoint F))) ≫
      π.residueFieldMap (Q.1 (IsLocalRing.closedPoint F))) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1) = 𝟙 _ := by
    exact htriQ
  haveI hmonoP : Mono (Scheme.descResidueField (Scheme.stalkClosedPointTo P.1)) :=
    ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  haveI hmonoQ : Mono (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)) :=
    ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  haveI hseP : IsSplitEpi (Scheme.descResidueField (Scheme.stalkClosedPointTo P.1)) :=
    IsSplitEpi.mk' ⟨_, hsecP⟩
  haveI hseQ : IsSplitEpi (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)) :=
    IsSplitEpi.mk' ⟨_, hsecQ⟩
  haveI hisoP : IsIso (Scheme.descResidueField (Scheme.stalkClosedPointTo P.1)) :=
    isIso_of_mono_of_isSplitEpi _
  haveI hisoQ : IsIso (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)) :=
    isIso_of_mono_of_isSplitEpi _
  -- the canonical sections `φ₀ ≫ j` match across the point congruence
  have hcanon : ∀ {x y : ↥X} (e : x = y) (eY : π.base x = π.base y),
      ((((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
        (Spec (CommRingCat.of F)).presheaf.germ ⊤ (π.base x) trivial) ≫
        (Spec (CommRingCat.of F)).residue (π.base x)) ≫ π.residueFieldMap x) ≫
        (Scheme.residueFieldCongr e).hom
      = (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
        (Spec (CommRingCat.of F)).presheaf.germ ⊤ (π.base y) trivial) ≫
        (Spec (CommRingCat.of F)).residue (π.base y)) ≫ π.residueFieldMap y := by
    rintro x y rfl eY
    simp
  have hkey := hcanon (h (IsLocalRing.closedPoint F)) e'
  -- turn the two triangles into inverse identities and conclude
  have hinvP : inv (Scheme.descResidueField (Scheme.stalkClosedPointTo P.1))
      = (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
        (Spec (CommRingCat.of F)).presheaf.germ ⊤
          ((P.1 ≫ π) (IsLocalRing.closedPoint F)) trivial) ≫
        (Spec (CommRingCat.of F)).residue
          ((P.1 ≫ π).base (IsLocalRing.closedPoint F))) ≫
        π.residueFieldMap (P.1 (IsLocalRing.closedPoint F)) := by
    rw [← Category.id_comp (inv _), ← hsecP, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinvQ : inv (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1))
      = (((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
        (Spec (CommRingCat.of F)).presheaf.germ ⊤
          ((Q.1 ≫ π) (IsLocalRing.closedPoint F)) trivial) ≫
        (Spec (CommRingCat.of F)).residue
          ((Q.1 ≫ π).base (IsLocalRing.closedPoint F))) ≫
        π.residueFieldMap (Q.1 (IsLocalRing.closedPoint F)) := by
    rw [← Category.id_comp (inv _), ← hsecQ, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hfinal : inv (Scheme.descResidueField (Scheme.stalkClosedPointTo P.1)) ≫
      (Scheme.residueFieldCongr (h (IsLocalRing.closedPoint F))).hom
      = inv (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)) := by
    rw [hinvP, hinvQ]
    exact hkey
  have h2 : (Scheme.residueFieldCongr (h (IsLocalRing.closedPoint F))).hom
      = Scheme.descResidueField (Scheme.stalkClosedPointTo P.1) ≫
        inv (Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)) := by
    rw [← hfinal, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  show Scheme.descResidueField (Scheme.stalkClosedPointTo P.1)
    = (Scheme.residueFieldCongr (h (IsLocalRing.closedPoint F))).hom ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo Q.1)
  rw [h2, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **(g5, alg-closed case — w1–w6 per the section header; w7 above)** The topological
range of `[N]` on the projective model over an algebraically closed field is
infinite. -/
theorem modelMulByHom_range_infinite {F : Type u} [Field F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℤ) (hN : N ≠ 0) :
    (Set.range ((modelEllipticCurve W).mulByHom N).base).Infinite := by
  haveI := Classical.decEq F
  intro hfin
  obtain ⟨ℓ, hℓ, hℓN, hℓF⟩ := exists_good_prime F N hN
  -- the Spec-side base morphism is the identity
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap F F))
      = 𝟙 (Spec (CommRingCat.of F)) := by
    have : CommRingCat.ofHom (algebraMap F F) = 𝟙 (CommRingCat.of F) := by
      ext a
      simp
    rw [this, Spec.map_id]
  -- Spec of a field is a single point
  haveI hsing : Subsingleton (↥(Spec (CommRingCat.of F))) := by
    constructor
    intro a b
    haveI := a.isPrime
    haveI := b.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans
      (Ideal.eq_bot_of_prime b.asIdeal).symm)
  -- per-level injections of `ℓⁿ`-torsion into the range
  have hinj : ∀ n : ℕ,
      ∃ f : ↥(HasseWeil.torsionSubgroup (W.baseChange F).toAffine ((ℓ ^ n : ℕ) : ℤ)) →
        ↥(Set.range ((modelEllipticCurve W).mulByHom N).base),
      Function.Injective f := by
    intro n
    set e := EllipticCurve.projModelPointsAddEquiv W F with he
    refine ⟨fun t => ⟨((e.symm ((N : ℤ) • (t : (W.baseChange F).toAffine.Point))).1).base
      (IsLocalRing.closedPoint F), ?_⟩, ?_⟩
    · -- the point of the `N`-multiple lies in the range of `[N]`
      set Pt := e.symm (t : (W.baseChange F).toAffine.Point) with hPt
      have hsm : e.symm ((N : ℤ) • (t : (W.baseChange F).toAffine.Point))
          = (N : ℤ) • Pt := map_zsmul e.symm (N : ℤ) _
      have hval := (modelEllipticCurve W).point_smul_eq_comp_mulBy
        (Spec.map (CommRingCat.ofHom (algebraMap F F))) (N : ℤ) Pt
      refine ⟨(Pt.1).base (IsLocalRing.closedPoint F), ?_⟩
      have hb := congrArg
        (fun m : Spec (CommRingCat.of F) ⟶ projModel W =>
          m.base (IsLocalRing.closedPoint F)) hval
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hb
      rw [hsm]
      exact hb.symm
    · -- injectivity: same point ⟹ same section (w7) ⟹ same multiple ⟹ same torsion elt
      intro t₁ t₂ hpt
      set Pt₁ := e.symm (t₁ : (W.baseChange F).toAffine.Point) with hPt₁
      set Pt₂ := e.symm (t₂ : (W.baseChange F).toAffine.Point) with hPt₂
      have hsm₁ : e.symm ((N : ℤ) • (t₁ : (W.baseChange F).toAffine.Point))
          = (N : ℤ) • Pt₁ := map_zsmul e.symm (N : ℤ) _
      have hsm₂ : e.symm ((N : ℤ) • (t₂ : (W.baseChange F).toAffine.Point))
          = (N : ℤ) • Pt₂ := map_zsmul e.symm (N : ℤ) _
      have hpt' := congrArg Subtype.val hpt
      simp only [hsm₁, hsm₂] at hpt'
      -- w7 at the two sections
      have hmul : (N : ℤ) • Pt₁ = (N : ℤ) • Pt₂ := by
        have h12 := section_base_injective_of_isAlgClosed (projModelπ W)
          ⟨((N : ℤ) • Pt₁).1, (((N : ℤ) • Pt₁).2).trans hbase⟩
          ⟨((N : ℤ) • Pt₂).1, (((N : ℤ) • Pt₂).2).trans hbase⟩
          (fun p => by
            have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
            rw [hp]
            exact hpt')
        have hval := congrArg Subtype.val h12
        exact Subtype.ext hval
      have hmul' : (N : ℤ) • (t₁ : (W.baseChange F).toAffine.Point)
          = (N : ℤ) • (t₂ : (W.baseChange F).toAffine.Point) := by
        have := congrArg e hmul
        simpa [hPt₁, hPt₂, map_zsmul] using this
      -- torsion hypotheses for the Bézout cancellation
      have htor₁ : ((ℓ : ℤ) ^ n) • (t₁ : (W.baseChange F).toAffine.Point) = 0 := by
        have := t₁.2
        rw [HasseWeil.mem_torsionSubgroup] at this
        exact_mod_cast this
      have htor₂ : ((ℓ : ℤ) ^ n) • (t₂ : (W.baseChange F).toAffine.Point) = 0 := by
        have := t₂.2
        rw [HasseWeil.mem_torsionSubgroup] at this
        exact_mod_cast this
      exact Subtype.ext (zsmul_injOn_torsionBy hℓ hℓN n htor₁ htor₂ hmul')
  -- cardinality explosion against the finite range
  haveI hfinT := hfin.to_subtype
  have hCbound : ∀ n : ℕ, (ℓ ^ n) ^ 2 ≤
      Nat.card ↥(Set.range ((modelEllipticCurve W).mulByHom N).base) := by
    intro n
    obtain ⟨f, hf⟩ := hinj n
    calc (ℓ ^ n) ^ 2
        = Nat.card (↥(HasseWeil.torsionSubgroup (W.baseChange F).toAffine ((ℓ ^ n : ℕ) : ℤ))) :=
          (HasseWeil.NTorsion.card_torsion_ellPow_nat (W.baseChange F) ℓ hℓF n).symm
      _ ≤ _ := Nat.card_le_card_of_injective f hf
  set C := Nat.card ↥(Set.range ((modelEllipticCurve W).mulByHom N).base) with hC
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self (n := C)
  have h2 : 2 ^ C ≤ ℓ ^ C := Nat.pow_le_pow_left hℓ.two_le C
  have h3 : ℓ ^ C ≤ (ℓ ^ C) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h4 := hCbound C
  omega

/-- **THE MODEL FIBRE-COUNT, unconditional (BB-QF ALPHA complete)**: over an
algebraically closed field, every topological fibre of `[N]` (`N ≠ 0`) on the projective
Weierstrass model is finite. -/
theorem modelMulByHom_finite_fibres {F : Type u} [Field F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℤ) (hN : N ≠ 0) (y : projModel W) :
    (((modelEllipticCurve W).mulByHom N).base ⁻¹' {y}).Finite :=
  modelMulByHom_finite_preimage_singleton W N (modelMulByHom_range_infinite W N hN) y

/-- **THE MODEL LQF (the interface BETA consumes)**: over an algebraically closed
field, `[N]` on the projective Weierstrass model is locally quasi-finite (`N ≠ 0`) —
`of_finite_preimage_singleton` on the axiom-clean fibre count (`LocallyOfFiniteType`
is free from properness). -/
theorem modelMulByHom_locallyQuasiFinite {F : Type u} [Field F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) [NeZero N] :
    LocallyQuasiFinite ((modelEllipticCurve W).mulByHom N) :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ fun y =>
    modelMulByHom_finite_fibres W N (by exact_mod_cast (NeZero.ne N)) y

end RangeWitness

end ModularCurves
