import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.FinrankFractionField
import HasseWeil.Foundation.Basic

/-!
# The degree of `[N]` on the projective model: `finrank = N²` (K4 field-level crux)

This file builds the **field-level crux** of the endomorphism-degree keystone (STREAM-KM):
over a field `K`, the scheme-theoretic fibre rank `Scheme.Hom.finrank` of multiplication-by-`N`
on the projective Weierstrass model `projModel W` is `N²`.

It is the anchor that connects the *scheme* world (`Scheme.Hom.finrank`, `modelEllipticCurve`,
`mulByHom`) to AINTLIB's *HasseWeil* function-field world (`WeierstrassCurve.Affine.Isogeny.degree`,
`mulByInt_degree = N²`). The bridge factors as:

* `Scheme.Hom.finrank` of the model `[N]` at the generic point = the degree of the induced
  function-field extension `[K(projModel W) : K(projModel W)]` via `[N]*`
  (`FinrankFractionField.finrank_SpecMap_algebraMap_eq_finrank`, the algebraic core, over the
  domain coordinate ring);
* the model `[N]` and HasseWeil's `mulByInt W N` agree on points via the *green* dictionary
  `PointsDictionary.projModelPointsEquiv` (+ `modelEllipticCurve_point_add_val`), hence induce
  the same function-field pullback (points determine morphisms on reduced/separated schemes,
  `hom_ext_of_forall_specPoint`);
* `mulByInt_degree` (HasseWeil) gives that degree `= N²`.

For an arbitrary elliptic curve `E/S`, `Torsion.mulByHom_finrank` reduces to this field-level
statement fibre-by-fibre (the fibre `E_s` over `κ(s)` is `≅ projModel W_s` by
`E.localModel : LocallyWeierstrass`, `S = Spec κ(s)` being a one-point base).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

namespace EllipticCurve

/-- **(dictionary additivity)** The points dictionary `projModelPointsEquiv` carries the model's
group addition (`modelEllipticCurve_point_add_val` via `mulModelHom`) to mathlib's `Affine.Point`
addition. This is `mulModelHom_specPoints` re-read through `modelEllipticCurve_point_add_val`, so
`projModelPointsEquiv` is an additive bijection of point groups. -/
theorem projModelPointsEquiv_add {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {K' : Type u} [Field K'] [Algebra K K'] [DecidableEq K']
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :
    projModelPointsEquiv W K' (P + Q)
      = projModelPointsEquiv W K' P + projModelPointsEquiv W K' Q := by
  rw [← mulModelHom_specPoints W K' P Q]
  congr 1

/-- **(dictionary as an additive equivalence)** The points dictionary bundled with its additivity
(`projModelPointsEquiv_add`): the model's `K'`-point group is `≃+` to mathlib's `Affine.Point`. -/
noncomputable def projModelPointsAddEquiv {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (K' : Type u) [Field K'] [Algebra K K'] [DecidableEq K'] :
    (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      ≃+ (W.baseChange K').toAffine.Point :=
  { projModelPointsEquiv W K' with map_add' := projModelPointsEquiv_add W }

/-- **(K4 point-`[N]`-match)** Under the points dictionary, the model's `zsmul` (multiplication
by `n` in the point group) is mathlib's `zsmul` on `Affine.Point`. Specialised to `n = N` this is
the point-level statement that the scheme `mulByHom N` realises mathlib's `[N]` (via
`point_smul_eq_comp_mulBy`, which rewrites `(n • P).1 = P.1 ≫ mulByHom n`). -/
theorem projModelPointsEquiv_zsmul {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {K' : Type u} [Field K'] [Algebra K K'] [DecidableEq K'] (n : ℤ)
    (P : (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :
    projModelPointsEquiv W K' (n • P) = n • projModelPointsEquiv W K' P :=
  map_zsmul (projModelPointsAddEquiv W K') n P

/-- **(K4 (B): function-field identity)** The scheme function field of the integral projective
model `projModel W` (mathlib `Scheme.functionField`) is `W.toAffine.FunctionField`: both are
fraction fields of the isomorphic coordinate rings `Γ(projModel W, Z-chart) ≃+* W.CoordinateRing`
(`coordRingToZSection`), via `functionField_isFractionRing_of_isAffineOpen`. -/
noncomputable def projModelFunctionFieldEquiv {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    (projModel W).functionField ≃+* W.toAffine.FunctionField := by
  set Z : (projModel W).Opens := Proj.basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) with hZ
  haveI hZaff : IsAffineOpen Z :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
  haveI hnt : Nontrivial Γ(projModel W, Z) :=
    (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty Z := ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI : IsFractionRing Γ(projModel W, Z) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) Z hZaff
  exact (IsLocalization.ringEquivOfRingEquiv (M := (nonZeroDivisors Γ(projModel W, Z)))
    (T := (nonZeroDivisors W.toAffine.CoordinateRing))
    (projModel W).functionField W.toAffine.FunctionField
    (coordRingToZSection W).symm (MulEquivClass.map_nonZeroDivisors (coordRingToZSection W).symm))

/-- **(generic helper)** The fibre rank of a finite flat morphism of *affine* schemes equals the
`RingHom.finrank` of its ring map `f.appTop` (reindexing the point through `Y.isoSpec`). This is the
public counterpart of mathlib's private `finrank_eq_of_isAffine`, assembled from `isoSpec` naturality
+ `finrank_SpecMap_eq_finrank` + the iso-square reindex `finrank_of_isPullback`. -/
lemma finrank_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [Flat f] [IsFinite f] (s : Y) :
    f.finrank s = f.appTop.hom.finrank (Y.isoSpec.hom.base s) := by
  have pb : IsPullback (𝟙 X) f (f ≫ Y.isoSpec.hom) Y.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hreindex : f.finrank s = (f ≫ Y.isoSpec.hom).finrank (Y.isoSpec.hom.base s) :=
    Scheme.Hom.finrank_of_isPullback (𝟙 X) f (f ≫ Y.isoSpec.hom) Y.isoSpec.hom pb s
  haveI : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
  haveI : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr f.flat_appTop
  rw [hreindex, ← Scheme.isoSpec_hom_naturality f,
    Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]

/-- **(K4b-1, general form)** For a finite flat morphism `g : A ⟶ B` of affine schemes with `Γ(B)`
a domain, the `RingHom.finrank` of the ring map `g.appTop` at any prime equals the module rank of
`Γ(A)` over `Γ(B)` — turning the affine `appTop` rank produced by `finrank_of_isAffine` into a
concrete `Module.finrank` over the (domain) base coordinate ring (`finrank_algebraMap_eq_module_finrank`). -/
lemma appTop_finrank_eq_module_finrank {A B : Scheme.{u}} (g : A ⟶ B) [IsAffine A] [IsAffine B]
    [Flat g] [IsFinite g] [IsDomain Γ(B, ⊤)] (pt : PrimeSpectrum Γ(B, ⊤)) :
    letI := g.appTop.hom.toAlgebra
    g.appTop.hom.finrank pt = Module.finrank Γ(B, ⊤) Γ(A, ⊤) := by
  letI := g.appTop.hom.toAlgebra
  haveI : Module.Finite Γ(B, ⊤) Γ(A, ⊤) := g.finite_appTop
  haveI : Module.Flat Γ(B, ⊤) Γ(A, ⊤) := g.flat_appTop
  exact _root_.ModularCurves.finrank_algebraMap_eq_module_finrank Γ(B, ⊤) Γ(A, ⊤) pt

/-- The affine `Z`-chart of `projModel W` (the `X₂ ≠ 0` basic open), on which the global
sections are `W.toAffine.CoordinateRing` (`coordRingToZSection`). -/
noncomputable abbrev zChart {K : Type u} [Field K] (W : WeierstrassCurve K) : (projModel W).Opens :=
  Proj.basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))

/-- **(K4 (D) chart-reduction, step 1)** The fibre rank of the model `[N]` at a point of the affine
`Z`-chart equals the fibre rank of its base-change along the chart inclusion — reducing the degree
computation to the affine morphism `[N]⁻¹(Z) → Z` (`finrank_pullback_snd`, needs `[N]` finite flat). -/
theorem modelEllipticCurve_finrank_zChart {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ)
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    (x : (zChart W : (projModel W).Opens)) :
    ((modelEllipticCurve W).mulByHom N).finrank ((zChart W).ι.base x)
      = (pullback.snd ((modelEllipticCurve W).mulByHom N) (zChart W).ι).finrank x :=
  (Scheme.Hom.finrank_pullback_snd ((modelEllipticCurve W).mulByHom N) (zChart W).ι x).symm

/-- **(K4 (D) local-constancy)** The fibre rank of the model `[N]` is constant on the (connected,
integral) projective model: it suffices to compute it at one convenient point. Uses mathlib's
`isLocallyConstant_finrank` (finite flat locally-of-finite-presentation) + preconnectedness of the
integral `projModel W`. -/
theorem modelEllipticCurve_finrank_const {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ)
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)]
    (x x' : (modelEllipticCurve W).E) :
    ((modelEllipticCurve W).mulByHom N).finrank x
      = ((modelEllipticCurve W).mulByHom N).finrank x' := by
  haveI : PreconnectedSpace (modelEllipticCurve W).E :=
    inferInstanceAs (PreconnectedSpace (projModel W))
  have hlc : IsLocallyConstant ((modelEllipticCurve W).mulByHom N).finrank :=
    Scheme.Hom.isLocallyConstant_finrank _
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _)

/-- **(K4 (D) chart-reduction, general form)** For a finite flat locally-finitely-presented
endomorphism `f : X ⟶ X` of a preconnected scheme, the fibre rank at *any* point equals the
`RingHom.finrank` of the ring map of the affine restriction `f⁻¹(U) → U`, for any affine open `U`
with a chosen point `x₀`. Combines local constancy (`isLocallyConstant_finrank`),
`finrank_pullback_snd`, and `finrank_of_isAffine` — stated generically (plain `f`, no structure
projection) so the `modelEllipticCurve` `.E`-projection never enters instance synthesis. -/
lemma finrank_eq_appTop_finrank_of_affineOpen {X : Scheme.{u}} (f : X ⟶ X)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] [PreconnectedSpace X]
    (U : X.Opens) [IsAffine U.toScheme] (x₀ : U) (x : X) :
    f.finrank x = (pullback.snd f U.ι).appTop.hom.finrank (U.toScheme.isoSpec.hom.base x₀) := by
  haveI : IsAffine (pullback f U.ι) := isAffine_of_isAffineHom (pullback.snd f U.ι)
  have hconst : f.finrank x = f.finrank (U.ι.base x₀) :=
    (Scheme.Hom.isLocallyConstant_finrank f).apply_eq_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _)
  rw [hconst, ← Scheme.Hom.finrank_pullback_snd f U.ι x₀, finrank_of_isAffine]

/-- **([N] is surjective)** Multiplication-by-`N` on the projective model is surjective: its fibre
rank is `≥ 1` at the image of any source point (`one_le_finrank_map`) and is constant on the
connected integral model (`isLocallyConstant_finrank`), hence `≥ 1` everywhere, which is exactly
surjectivity (`one_le_finrank_iff_surjective`). This is the isogeny-surjectivity fact behind the
nonemptiness of the preimage chart `[N]⁻¹Z` (the `[N]⁻¹Z`-side input to the K4b-2 fraction fields). -/
theorem mulByHom_surjective {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ)
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)] :
    AlgebraicGeometry.Surjective ((modelEllipticCurve W).mulByHom N) := by
  haveI : AlgebraicGeometry.IsIntegral (modelEllipticCurve W).E :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (projModel W))
  haveI : PreconnectedSpace (modelEllipticCurve W).E :=
    inferInstanceAs (PreconnectedSpace (projModel W))
  rw [← Scheme.Hom.one_le_finrank_iff_surjective]
  intro y
  obtain ⟨x₀⟩ : Nonempty (modelEllipticCurve W).E := inferInstance
  have h1 := Scheme.Hom.one_le_finrank_map ((modelEllipticCurve W).mulByHom N) x₀
  have hconst := (Scheme.Hom.isLocallyConstant_finrank ((modelEllipticCurve W).mulByHom N)
    ).apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ y)
    (Set.mem_univ (((modelEllipticCurve W).mulByHom N).base x₀))
  rw [hconst]
  exact h1

/-- **([N] is dominant — L4-iii enabler)** Multiplication-by-`N` on the projective model is dominant
(dense range), being surjective (`mulByHom_surjective`). This is the instance that makes the scheme
function-field pullback `(mulByHom N).functionFieldMap : K(E) → K(E)` (the LHS of the L4-iii
coordinate↔division-polynomial identity `functionFieldMap [N] = mulByInt_pullbackAlgHom`)
well-defined without manual dominance plumbing. -/
instance mulByHom_isDominant {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ)
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)] :
    IsDominant ((modelEllipticCurve W).mulByHom N) :=
  haveI := mulByHom_surjective W N
  inferInstance

/-- **(K4b-2, [N]⁻¹Z nonempty)** The preimage chart `[N]⁻¹Z = pullback [N] Z.ι` is nonempty: `[N]` is
surjective (`mulByHom_surjective`), so any point `z₀` of the (nonempty) affine chart `Z` has an
`[N]`-preimage, which lifts to a point of the pullback (`Scheme.Pullback.exists_preimage_pullback`).
This is the `Nonempty` fibre input for the `[N]⁻¹Z`-side fraction field (feeds
`isFractionRing_top_of_isOpenImmersion` and `isIntegral_of_isOpenImmersion`). -/
lemma nonempty_preimage_pullback {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ) [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)]
    (z₀ : ((modelEllipticCurve W).E)) (hz₀ : z₀ ∈ (zChart W : (projModel W).Opens)) :
    Nonempty (pullback ((modelEllipticCurve W).mulByHom N)
      (show ((modelEllipticCurve W).E).Opens from zChart W).ι : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := (mulByHom_surjective W N).surj z₀
  obtain ⟨z, -, -⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
    (f := (modelEllipticCurve W).mulByHom N)
    (g := (show ((modelEllipticCurve W).E).Opens from zChart W).ι)
    x ⟨z₀, hz₀⟩ hx
  exact ⟨z⟩

/-- **(K4 (D) chart-reduction to a module rank, general form)** Chaining
`finrank_eq_appTop_finrank_of_affineOpen` with the `appTop`-to-`Module.finrank` bridge
`appTop_finrank_eq_module_finrank`: for a finite flat LFP endomorphism `f` of a preconnected scheme,
the fibre rank at any point equals the module rank of `Γ(f⁻¹U)` over the (domain) coordinate ring
`Γ(U)` of any affine open. All scheme plumbing is discharged generically — the crux then reduces to
the pure ring-theoretic identity `Module.finrank Γ(U) Γ(f⁻¹U) = (mulByInt N).degree`. -/
lemma finrank_eq_module_finrank_of_affineOpen {X : Scheme.{u}} (f : X ⟶ X)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] [PreconnectedSpace X]
    (U : X.Opens) [IsAffine U.toScheme] [IsDomain Γ(U.toScheme, ⊤)] (x₀ : U) (x : X) :
    letI := (pullback.snd f U.ι).appTop.hom.toAlgebra
    f.finrank x = Module.finrank Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := by
  haveI : IsAffine (pullback f U.ι) := isAffine_of_isAffineHom (pullback.snd f U.ι)
  rw [finrank_eq_appTop_finrank_of_affineOpen f U x₀ x, appTop_finrank_eq_module_finrank]

/-- **(K4b-2, birational leaf)** An open immersion `f : X ⟶ Y` of irreducible schemes induces an
isomorphism on function fields `Y.functionField ≅ X.functionField`: the generic point is preserved
(`genericPoint_eq_of_isOpenImmersion`) and `f`'s stalk maps are isomorphisms. This is the
birational-invariance input for the `[N]⁻¹Z`-side of the K4b-2 identity — the preimage `[N]⁻¹Z` is
an open of the integral `projModel W`, so its function field is `W.toAffine.FunctionField`. -/
noncomputable def functionFieldIsoOfOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    Y.functionField ≅ X.functionField :=
  eqToIso (show Y.functionField = Y.presheaf.stalk (f.base (genericPoint X)) from
      congrArg (Y.presheaf.stalk) (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint X))

/-- The whole space is a nonempty open of a nonempty scheme — the instance needed to form
`germToFunctionField ⊤` (the global-section-to-function-field map) from `Nonempty X` alone. -/
instance nonempty_top_opens {X : Scheme.{u}} [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.arbitrary X, TopologicalSpace.Opens.mem_top _⟩⟩

/-- **(K4b-2, birational fraction-field, general form)** For an open immersion `j : V ⟶ X` with `V`
integral affine and `X` irreducible, the global sections `Γ(V, ⊤)` localise to *any* field
`L ≃+* X.functionField`: `V`'s own function field is `Frac Γ(V, ⊤)`
(`functionField_isFractionRing_of_isAffineOpen`), and the birational iso
`functionFieldIsoOfOpenImmersion` identifies it with `X.functionField ≃+* L`. The algebra is the
composite `Γ(V, ⊤) → K(V) ≅ K(X) ≃+* L`. This is the reusable engine behind both sides of the K4b-2
`[Frac : Frac]` reduction — in particular the `[N]⁻¹Z`-side, where `V = [N]⁻¹Z` sits in the integral
`projModel W` via `pullback.fst` and `L = W.toAffine.FunctionField` via `projModelFunctionFieldEquiv`. -/
lemma isFractionRing_top_of_isOpenImmersion {V X : Scheme.{u}} (j : V ⟶ X) (L : Type u) [Field L]
    [IsOpenImmersion j] [AlgebraicGeometry.IsIntegral V] [IsAffine V] [IrreducibleSpace X]
    [Nonempty V] (e : X.functionField ≃+* L) :
    letI : Algebra Γ(V, ⊤) L :=
      (e.toRingHom.comp ((functionFieldIsoOfOpenImmersion j).inv.hom.comp
        (V.germToFunctionField ⊤).hom)).toAlgebra
    IsFractionRing Γ(V, ⊤) L := by
  haveI hfrV : IsFractionRing Γ(V, ⊤) V.functionField :=
    functionField_isFractionRing_of_isAffineOpen V ⊤ (isAffineOpen_top V)
  letI φ : V.functionField ≃+* L :=
    ((functionFieldIsoOfOpenImmersion j).commRingCatIsoToRingEquiv.symm).trans e
  exact (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors Γ(V, ⊤)) φ).mp hfrV

/-- **(K4b-2, leaf L1)** The global sections of the affine `Z`-chart `(zChart W).toScheme` are `W`'s
affine coordinate ring: `Γ(zChart, ⊤) ≃+* W.CoordinateRing`. Via `Scheme.Opens.topIso` (identifying
`Γ(U.toScheme, ⊤)` with `Γ(projModel W, U)`) composed with the fixed chart identification
`coordRingToZSection`. This is the base-ring half of the K4b-2 identity: it presents the domain base
`Γ(Z)` of the module rank `Module.finrank Γ(Z) Γ([N]⁻¹Z)` as `W.CoordinateRing`. -/
noncomputable def zChartSectionCoordRingEquiv {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    Γ((zChart W).toScheme, ⊤) ≃+* W.toAffine.CoordinateRing :=
  (zChart W).topIso.commRingCatIsoToRingEquiv.trans (coordRingToZSection W).symm

/-- **(K4b-2, leaf L2)** `W.toAffine.FunctionField` is a fraction field of the `Z`-chart sections
`Γ((zChart W).toScheme, ⊤)`, for the algebra structure induced by `zChartSectionCoordRingEquiv` (L1)
followed by `W.CoordinateRing → W.FunctionField`. Transports the canonical
`IsFractionRing W.CoordinateRing W.FunctionField` along the L1 ring iso
(`IsFractionRing.of_ringEquiv_left`). This is the `Frac Γ(Z) = K(E)` half of `L3`
(`finrank_of_isFractionRing`) — completing the base (`Γ(Z)`) side of the K4b-2 identity. -/
lemma isFractionRing_zChartSection {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    letI : Algebra Γ((zChart W).toScheme, ⊤) W.toAffine.FunctionField :=
      ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
        (zChartSectionCoordRingEquiv W).toRingHom).toAlgebra
    IsFractionRing Γ((zChart W).toScheme, ⊤) W.toAffine.FunctionField := by
  letI : Algebra Γ((zChart W).toScheme, ⊤) W.toAffine.FunctionField :=
    ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
      (zChartSectionCoordRingEquiv W).toRingHom).toAlgebra
  exact IsFractionRing.of_ringEquiv_left (zChartSectionCoordRingEquiv W) (fun _ => rfl)

/-- **(L4-iv, public form — the HasseWeil side of the L4-iii identity on the generator)** The
`[n]`-pullback of the generic x-coordinate is the division-polynomial quotient:
`[n]* x_gen = mulByInt_x = Φₙ/Ψₙ²`. Public restatement of HasseWeil's private
`mulByIntCompAlgHom_algebraMap_X` (ZERO HasseWeil edit), replayed from the public pieces:
`mulByInt_pullbackRingHom` is the `IsLocalization.lift` of `mulByInt_coordHom`, which is the
`AdjoinRoot.lift` of `mulByInt_xHom` — and that sends `X` to `mulByInt_x`. This is the anchor the
L4-iii comparison (`functionFieldMap [N] = mulByInt_pullbackAlgHom` mod `projModelFunctionFieldEquiv`)
must hit on the `x`-generator; its `functionFieldMap`-side counterpart is
`functionFieldMap_germToFunctionField` on the chart coordinate. -/
theorem mulByInt_pullbackAlgHom_x_gen {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    HasseWeil.mulByInt_pullbackAlgHom W n hn (HasseWeil.x_gen W)
      = HasseWeil.mulByInt_x W n := by
  show HasseWeil.mulByInt_pullbackRingHom W n hn (HasseWeil.x_gen W) = _
  rw [HasseWeil.x_gen, HasseWeil.mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  rw [show algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X
      = WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) from rfl]
  rw [HasseWeil.mulByInt_coordHom, AdjoinRoot.lift_mk]
  simp [Polynomial.eval₂_C, HasseWeil.mulByInt_xHom, HasseWeil.mulByInt_x]

/-- **(L4-iv, public form, `y`-side)** The `[n]`-pullback of the generic y-coordinate is the
division-polynomial quotient `mulByInt_y = ωₙ/ψₙ³`: the coordinate hom is the `AdjoinRoot.lift`
sending the adjoined root — which is `y_gen` — to `mulByInt_y` (`AdjoinRoot.lift_root`). Companion
of `mulByInt_pullbackAlgHom_x_gen`; together they pin `mulByInt_pullbackAlgHom` on both generators
(for `functionField_algHom_ext`). -/
theorem mulByInt_pullbackAlgHom_y_gen {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    HasseWeil.mulByInt_pullbackAlgHom W n hn (HasseWeil.y_gen W)
      = HasseWeil.mulByInt_y W n := by
  show HasseWeil.mulByInt_pullbackRingHom W n hn (HasseWeil.y_gen W) = _
  rw [HasseWeil.y_gen, HasseWeil.mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  rw [HasseWeil.mulByInt_coordHom, AdjoinRoot.lift_root]

/-- **(L4-v enabler: generator extensionality for `K(E)`)** Two `K`-algebra homomorphisms out of
the function field agree iff they agree on the generic coordinates `x_gen`, `y_gen`: `K(E)` is the
fraction field of the coordinate ring (`IsLocalization.ringHom_ext`), which is
`AdjoinRoot W.polynomial` over `K[X]` (`AdjoinRoot.ringHom_ext` + `Polynomial.ringHom_ext`, with
the `C`-scalars fixed by `K`-algebra-hood). This is the final L4-v step's engine: once the L4-iii
comparison shows `functionFieldMap [N]` and `mulByInt_pullbackAlgHom` agree on `x_gen`/`y_gen`
(anchors: `functionFieldMap_germToFunctionField` and `mulByInt_pullbackAlgHom_x_gen`), they are
equal as field maps. Generally reusable: any two isogeny pullbacks are compared on `x, y` alone. -/
theorem functionField_algHom_ext {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] {L : Type u} [CommRing L] [Algebra K L]
    (φ ψ : W.toAffine.FunctionField →ₐ[K] L)
    (hx : φ (HasseWeil.x_gen W) = ψ (HasseWeil.x_gen W))
    (hy : φ (HasseWeil.y_gen W) = ψ (HasseWeil.y_gen W)) : φ = ψ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.ringHom_ext
  · -- agreement on the `K[X]`-part: ring homs out of `K[X]` agree on `C`-scalars and `X`
    apply Polynomial.ringHom_ext
    · intro a
      have hsc : (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a))
          = algebraMap K W.toAffine.FunctionField a := by
        rw [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
          show (Polynomial.C a : Polynomial K) = algebraMap K (Polynomial K) a from rfl,
          ← IsScalarTower.algebraMap_apply]
      show φ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a)))
        = ψ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a)))
      rw [hsc, AlgHom.commutes, AlgHom.commutes]
    · show φ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
          ((AdjoinRoot.of W.toAffine.polynomial) Polynomial.X))
        = ψ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
          ((AdjoinRoot.of W.toAffine.polynomial) Polynomial.X))
      rw [show (AdjoinRoot.of W.toAffine.polynomial) Polynomial.X
          = algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X from rfl]
      exact hx
  · show φ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
        (AdjoinRoot.root W.toAffine.polynomial))
      = ψ ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
        (AdjoinRoot.root W.toAffine.polynomial))
    exact hy

/-- **(K4 crux — the HasseWeil coupling)** Over a field `K`, the scheme-theoretic fibre rank of the
model `[N]` equals the degree of HasseWeil's multiplication-by-`N` isogeny `mulByInt W.toAffine N`
(the function-field extension degree `[K(E) : [N]* K(E)]`).

This is the one deep identification the field-level keystone rests on: the scheme morphism
`mulByHom N` and HasseWeil's `mulByInt N` both realise mathlib's `[N]` on points (the *green*
dictionary `projModelPointsEquiv_zsmul` on the model side; `mulByInt_apply : (mulByInt W n).toAddMonoidHom P
= n • P` on the HasseWeil side), so the maps they induce on the function field
(`projModelFunctionFieldEquiv : (projModel W).functionField ≃+* W.toAffine.FunctionField`) agree.
Hence the scheme fibre rank — computed over the affine `Z`-chart as
`Module.finrank Γ(Z) Γ([N]⁻¹Z)` (`finrank_of_isAffine` + `finrank_algebraMap_eq_module_finrank`),
`= [Frac : Frac]` over the domain coordinate ring — equals `(mulByInt N).degree
= Module.finrank K(E) K(E)` via `mulByInt`'s pullback. This is the BB-DIFF-scale coordinate ↔
division-polynomial comparison (shared with `formallyUnramified_torsionπ`). -/
theorem modelEllipticCurve_finrank_eq_mulByInt_degree {K : Type u} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)]
    (x : (modelEllipticCurve W).E) :
    ((modelEllipticCurve W).mulByHom N).finrank x = (HasseWeil.mulByInt W.toAffine (N : ℤ)).degree := by
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : IsAffine (zChart W).toScheme := hZaff
  haveI hZaffE : IsAffine ((show ((modelEllipticCurve W).E).Opens from zChart W).toScheme) := hZaff
  haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
  haveI : Nontrivial Γ(projModel W, zChart W) := (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty (zChart W).toScheme := ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  obtain ⟨x₀⟩ := hNe
  haveI : PreconnectedSpace (modelEllipticCurve W).E :=
    inferInstanceAs (PreconnectedSpace (projModel W))
  haveI : IsIntegral (modelEllipticCurve W).E := inferInstanceAs (IsIntegral (projModel W))
  haveI : Nonempty (show ((modelEllipticCurve W).E).Opens from zChart W).toScheme := ⟨x₀⟩
  refine (finrank_eq_module_finrank_of_affineOpen
    ((modelEllipticCurve W).mulByHom N) (show ((modelEllipticCurve W).E).Opens from zChart W)
    x₀ x).trans ?_
  -- K4b (the isolated deep identity): `Module.finrank Γ(Z) Γ([N]⁻¹Z) = (mulByInt N).degree`.
  -- All scheme plumbing is discharged; what remains is the coordinate ↔ division-polynomial
  -- comparison: `Γ(Z) = W.CoordinateRing` (`coordRingToZSection`), and the `[N]`-pullback of
  -- `Γ([N]⁻¹Z)` = HasseWeil `mulByInt`'s pullback (both realise `[N]`), so the module rank over the
  -- domain coordinate ring = the function-field degree `(mulByInt N).degree = N²`.
  sorry

/-- **(K4 field-level target)** Over a field `K`, the scheme-theoretic fibre rank of
multiplication-by-`N` on the projective model of an elliptic Weierstrass curve is `N²`.

The finiteness/flatness of `[N]` (the accepted KM 2.3.1 `BB-QF`/`BB-FLAT` fibre inputs) are taken
as hypotheses — this lemma supplies the *degree* content on top of them (the charter's scope (i)):
the fibre rank is the HasseWeil isogeny degree (`modelEllipticCurve_finrank_eq_mulByInt_degree`),
which `mulByInt_degree` evaluates to `N²`. The arbitrary-`E/S` assembly
(`Torsion.mulByHom_finrank`) discharges the fibre hypotheses from `mulByHom_flat`/`mulByHom_isFinite`. -/
theorem modelEllipticCurve_mulByHom_finrank {K : Type u} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)]
    (x : (modelEllipticCurve W).E) :
    ((modelEllipticCurve W).mulByHom N).finrank x = N ^ 2 := by
  rw [modelEllipticCurve_finrank_eq_mulByInt_degree W N x,
    HasseWeil.mulByInt_degree W.toAffine (N : ℤ) (by exact_mod_cast NeZero.ne N),
    show ((N : ℤ)) ^ 2 = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]

end EllipticCurve

end ModularCurves
