import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.FinrankFractionField
import ModularCurves.ForMathlib.DominantFunctionField
import HasseWeil.Foundation.Basic
import HasseWeil.Foundation.EC.GenericPoint

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

section GenericPointSmul

open WeierstrassCurve HasseWeil

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
  [W.toAffine.IsElliptic]

/-- The division-polynomial triple at the generic point, componentwise
(`smulEval_generic_X/Y/Z` bundled as a function identity). -/
lemma smulEval_generic (n : ℤ) :
    smulEval (W_KE W) (x_gen W) (y_gen W) n = ![Φ_ff W n, ω_ff W n, ψ_ff W n] := by
  funext i
  fin_cases i
  · simpa using smulEval_generic_X W n
  · simpa using smulEval_generic_Y W n
  · simpa using smulEval_generic_Z W n

/-- The Jacobian point class of `n • genericPoint` is the division-polynomial triple
(HasseWeil `zsmul_eq_smulEval` + `smulEval_generic`). -/
lemma zsmul_genericPoint_point (n : ℤ) :
    (n • Jacobian.Point.fromAffine (genericPoint W)).point
      = (⟦![Φ_ff W n, ω_ff W n, ψ_ff W n]⟧ :
          Jacobian.PointClass W.toAffine.FunctionField) := by
  rw [show genericPoint W
      = WeierstrassCurve.Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W) from rfl,
    zsmul_eq_smulEval (W := W_KE W) (generic_nonsingular W) n, smulEval_generic]

/-- Coordinate helper: the affine `x`-slot of the division-polynomial triple. -/
lemma divTriple_x_div_z_sq (n : ℤ) :
    (![Φ_ff W n, ω_ff W n, ψ_ff W n]) 0 / (![Φ_ff W n, ω_ff W n, ψ_ff W n]) 2 ^ 2
      = mulByInt_x W n := by
  show Φ_ff W n / ψ_ff W n ^ 2 = mulByInt_x W n
  rw [mulByInt_x, ψ_ff_sq_eq_ΨSq_ff]

/-- Coordinate helper: the affine `y`-slot of the division-polynomial triple. -/
lemma divTriple_y_div_z_cb (n : ℤ) :
    (![Φ_ff W n, ω_ff W n, ψ_ff W n]) 1 / (![Φ_ff W n, ω_ff W n, ψ_ff W n]) 2 ^ 3
      = mulByInt_y W n := rfl

/-- **(L4-iii brick 1 — the generic-point `[n]`-image is the division-polynomial point)**
Multiplication by `n ≠ 0` sends the generic point `(x_gen, y_gen)` of `W_KE` to
`(mulByInt_x, mulByInt_y) = (Φₙ/Ψₙ², ωₙ/ψₙ³)`: HasseWeil's Jacobian smul formula
`zsmul_eq_smulEval` evaluated at the generic point (`smulEval_generic_X/Y/Z`), converted to
affine coordinates through `toAffineAddEquiv`/`toAffineLift_of_Z_ne_zero` (`ψₙ ≠ 0` for `n ≠ 0`).
Realises the promise in `HasseWeil.genericPoint`'s docstring; the (c)-leg of the L4-iii chain
(dictionary τ ↦ genericPoint, then `N•` on both sides, then this identity reads off the
coordinates that `mulByInt_pullbackAlgHom_x_gen/_y_gen` match on the pullback side). -/
theorem zsmul_genericPoint {n : ℤ} (hn : n ≠ 0) :
    ∃ h, n • genericPoint W
      = WeierstrassCurve.Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) h := by
  have hround : n • genericPoint W
      = (n • Jacobian.Point.fromAffine (genericPoint W)).toAffineLift := by
    conv_lhs => rw [show genericPoint W
        = (Jacobian.Point.toAffineAddEquiv (W_KE W).toJacobian)
            (Jacobian.Point.fromAffine (genericPoint W)) from
      ((Jacobian.Point.toAffineAddEquiv (W_KE W).toJacobian).apply_symm_apply
        (genericPoint W)).symm]
    rw [← map_zsmul (Jacobian.Point.toAffineAddEquiv (W_KE W).toJacobian)]
    rfl
  have hψ : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  have hψz : (![Φ_ff W n, ω_ff W n, ψ_ff W n]) (2 : Fin 3) ≠ 0 := by simpa using hψ
  rcases hE : n • Jacobian.Point.fromAffine (genericPoint W) with @⟨p, hp⟩
  have hpt : p = (⟦![Φ_ff W n, ω_ff W n, ψ_ff W n]⟧ :
      Jacobian.PointClass W.toAffine.FunctionField) := by
    have h := zsmul_genericPoint_point W n
    rw [hE] at h
    exact h
  subst hpt
  have hns : (W_KE W).toAffine.Nonsingular (mulByInt_x W n) (mulByInt_y W n) := by
    rw [← divTriple_x_div_z_sq W n, ← divTriple_y_div_z_cb W n]
    exact (Jacobian.nonsingular_of_Z_ne_zero hψz).mp hp
  refine ⟨hns, ?_⟩
  rw [hround, hE, Jacobian.Point.toAffineLift_of_Z_ne_zero hψz]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨divTriple_x_div_z_sq W n, divTriple_y_div_z_cb W n⟩

end GenericPointSmul

section TautologicalPoint

open WeierstrassCurve HasseWeil

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
  [W.IsElliptic]
variable {L : Type u} [Field L] [Algebra K L]

/-- Base change preserves ellipticity (the `W_KE_isElliptic` pattern: `baseChange = map`). -/
instance : (W.baseChange L).IsElliptic :=
  show (W.map (algebraMap K L)).IsElliptic from inferInstance

instance : (W.baseChange L).toAffine.IsElliptic :=
  inferInstanceAs ((W.baseChange L).IsElliptic)

/-- **(L4-iii chart-point kit)** An affine Weierstrass point `(x, y)` over `L` as a `Z`-chart
solution of the dehomogenised cubic. -/
noncomputable def chartSolution (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    { v : {j : Fin 3 // j ≠ 2} → L //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux K 2 W.toProjective.polynomial) = 0 } := by
  refine ⟨fun j => if j.1 = 0 then x else y, ?_⟩
  have heval : MvPolynomial.aeval (fun j : {j : Fin 3 // j ≠ 2} =>
        if j.1 = 0 then x else y)
      (MvPolynomial.dehomogenizeAux K 2 W.toProjective.polynomial)
      = y ^ 2 + algebraMap K L W.a₁ * x * y + algebraMap K L W.a₃ * y
        - (x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x
          + algebraMap K L W.a₆) := by
    rw [WeierstrassCurve.Projective.polynomial]
    simp only [map_sub, map_add, map_mul, map_pow,
      MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]
    norm_num
  rw [heval]
  have heq := h
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at heq
  linear_combination heq

/-- **(L4-iii chart-point kit)** The `L`-point of the model attached to an affine Weierstrass
point `(x, y)`, built through the `Z`-chart machinery so its dictionary readout is free
(`apply_symm_apply`). -/
noncomputable def chartSpecPointZ (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    { g : SpecPoints (projModel W) (projModelπ W) L // InZChart W g } :=
  (chartHomEquiv W 2 L).symm
    ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h))

/-- The underlying model point of `chartSpecPointZ`. -/
noncomputable def chartSpecPoint (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    SpecPoints (projModel W) (projModelπ W) L :=
  (chartSpecPointZ W x y h).1

theorem inZChart_chartSpecPoint (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    InZChart W (chartSpecPoint W x y h) :=
  (chartSpecPointZ W x y h).2

/-- The chart-hom readout of `chartSpecPoint` is the solution hom (free by `Subtype.coe_eta` +
`apply_symm_apply`). -/
lemma chartHomEquiv_chartSpecPoint (x y : L) (h : (W.baseChange L).toAffine.Equation x y)
    (hZ : InZChart W (chartSpecPoint W x y h)) :
    chartHomEquiv W 2 L ⟨chartSpecPoint W x y h, hZ⟩
      = (chartSolutionsEquiv W 2 L).symm (chartSolution W x y h) := by
  rw [show (⟨chartSpecPoint W x y h, hZ⟩ :
      { g : SpecPoints (projModel W) (projModelπ W) L // InZChart W g })
      = chartSpecPointZ W x y h from Subtype.coe_eta _ _]
  exact Equiv.apply_symm_apply _ _

/-- **(L4-iii chart-point kit, forward readout)** The dictionary reads `chartSpecPoint x y` as the
affine point `some x y`. -/
theorem projModelPointsEquiv_chartSpecPoint (x y : L)
    (h : (W.baseChange L).toAffine.Equation x y) :
    projModelPointsEquiv W L (chartSpecPoint W x y h)
      = WeierstrassCurve.Affine.Point.some x y
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mp h) := by
  refine projModelPointsEquiv_some W L (chartSpecPoint W x y h)
    (inZChart_chartSpecPoint W x y h) x y
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp h) ?_ ?_
  · rw [chartHomEquiv_chartSpecPoint W x y h (inZChart_chartSpecPoint W x y h),
      Equiv.apply_symm_apply]
    rfl
  · rw [chartHomEquiv_chartSpecPoint W x y h (inZChart_chartSpecPoint W x y h),
      Equiv.apply_symm_apply]
    rfl


set_option maxHeartbeats 1600000

open HomogeneousLocalization

/-- The solution ring hom attached to a chart point datum (the underlying hom of
`chartSolutionsEquiv.symm`). -/
noncomputable def chartSolutionHom (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* L :=
  ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h)).1

/-- **(T1a)** The solution hom sends the `X₀/X₂` localization element to `x`. -/
lemma chartSolutionHom_x (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    chartSolutionHom W x y h (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) = x := by
  have hval : ((chartSolutionsEquiv W 2 L)
      ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h))).1 ⟨0, by decide⟩
      = (chartSolution W x y h).1 ⟨0, by decide⟩ := by
    rw [Equiv.apply_symm_apply]
  have hread : ((chartSolutionsEquiv W 2 L)
      ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h))).1 ⟨0, by decide⟩
      = chartSolutionHom W x y h (chartCoordEquiv W 2 (Ideal.Quotient.mk _
          (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})))) := rfl
  rw [chartCoordEquiv_mk_X] at hread
  have : chartSolutionHom W x y h (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0))
      = (chartSolution W x y h).1 ⟨0, by decide⟩ := by
    rw [← hread, hval]
  rw [this]
  rfl

/-- **(T1b)** The solution hom sends the `X₁/X₂` localization element to `y`. -/
lemma chartSolutionHom_y (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    chartSolutionHom W x y h (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) = y := by
  have hval : ((chartSolutionsEquiv W 2 L)
      ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h))).1 ⟨1, by decide⟩
      = (chartSolution W x y h).1 ⟨1, by decide⟩ := by
    rw [Equiv.apply_symm_apply]
  have hread : ((chartSolutionsEquiv W 2 L)
      ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h))).1 ⟨1, by decide⟩
      = chartSolutionHom W x y h (chartCoordEquiv W 2 (Ideal.Quotient.mk _
          (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2})))) := rfl
  rw [chartCoordEquiv_mk_X] at hread
  have hcomb : chartSolutionHom W x y h (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1))
      = (chartSolution W x y h).1 ⟨1, by decide⟩ := by
    rw [← hread, hval]
  rw [hcomb]
  rfl

/-- **(T2 — the chart factoring of `chartSpecPoint`)** The underlying morphism of the
chart-constructed point is `Spec.map` of its solution hom followed by the chart immersion. -/
lemma chartSpecPoint_val (x y : L) (h : (W.baseChange L).toAffine.Equation x y) :
    (chartSpecPoint W x y h).1
      = Spec.map (CommRingCat.ofHom (chartSolutionHom W x y h))
          ≫ Proj.awayι (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos := by
  set φ := (chartSolutionsEquiv W 2 L).symm (chartSolution W x y h) with hφ
  -- the tautological chart-factored point of φ
  have hover : (Spec.map (CommRingCat.ofHom φ.1)
      ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos) ≫ projModelπ W
      = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [Category.assoc, awayι_projModelπ W 2, ← Spec.map_comp]
    congr 1
    ext r
    exact RingHom.congr_fun φ.2 r
  set g' : { g : SpecPoints (projModel W) (projModelπ W) L //
      ∃ h' : Spec (.of L) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h' ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 } :=
    ⟨⟨Spec.map (CommRingCat.ofHom φ.1)
      ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos, hover⟩,
      ⟨Spec.map (CommRingCat.ofHom φ.1), rfl⟩⟩ with hg'
  have h1 : chartHomEquiv W 2 L g' = φ :=
    chartHomEquiv_eq_of_specMap W 2 g' φ rfl
  have h2 : chartHomEquiv W 2 L ⟨chartSpecPoint W x y h, inZChart_chartSpecPoint W x y h⟩
      = φ := chartHomEquiv_chartSpecPoint W x y h (inZChart_chartSpecPoint W x y h)
  have h3 : (⟨chartSpecPoint W x y h, inZChart_chartSpecPoint W x y h⟩ :
      { g : SpecPoints (projModel W) (projModelπ W) L //
        ∃ h' : Spec (.of L) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
          h' ≫ Proj.awayι (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 }) = g' :=
    (chartHomEquiv W 2 L).injective (h2.trans h1.symm)
  have := congrArg (fun z => z.1.1) h3
  exact this

/-- **(T1c)** The solution hom is `K`-algebra compatible on grade-zero constants. -/
lemma chartSolutionHom_fromZero (x y : L) (h : (W.baseChange L).toAffine.Equation x y) (r : K) :
    chartSolutionHom W x y h ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      ((algebraMapGradeZero (projIdeal W)) r)) = algebraMap K L r :=
  RingHom.congr_fun ((chartSolutionsEquiv W 2 L).symm (chartSolution W x y h)).2 r

/-- **(T3-away — the chart immersion evaluates sections through `awayToSection`)** The
`appLE`-pullback of `basicOpen`-sections along `awayι`, read through `ΓSpecIso`, is the inverse of
the `awayToSection` presentation. -/
lemma awayι_appLE_eval
    (hZle : (⊤ : (Spec (CommRingCat.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).Opens)
      ≤ (Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos) ⁻¹ᵁ (zChart W : (projModel W).Opens)) :
    (Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos).appLE
      (zChart W : (projModel W).Opens) ⊤ hZle
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).hom
    = (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv := by
  show ((Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv
        ≫ (Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι).appLE
      (zChart W : (projModel W).Opens) ⊤ hZle
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).hom
    = (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv
  rw [← Scheme.Hom.appLE_comp_appLE
    (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos).inv
    (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι
    (zChart W : (projModel W).Opens) ⊤ ⊤
    (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι_preimage_self.ge le_rfl]
  -- the ι-part is the top-sections identification
  have hι : (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι.appLE
      (zChart W : (projModel W).Opens) ⊤
      (Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι_preimage_self.ge
      = (Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
    show (projModel W).presheaf.map _ = ((projModel W).presheaf.mapIso _).inv
    rw [Functor.mapIso_inv]
    exact congrArg (projModel W).presheaf.map (Subsingleton.elim _ _)
  rw [hι]
  -- the isoSpec-inverse part: appTop of the inverse is the inverse of the appTop
  have hspec : (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appLE ⊤ ⊤ le_rfl
      = (Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).topIso.hom
        ≫ (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).inv := by
    have happ : (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appLE ⊤ ⊤ le_rfl
        = (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appTop := by
      exact (Scheme.Hom.app_eq_appLE _).symm
    have hround : (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos).hom.appTop
        ≫ (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
    have hBA : ((Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).topIso.hom
          ≫ (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
              (mk_X_mem_quotientGrading_one W 2) one_pos).inv
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (Away (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).inv)
        ≫ (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos).hom.appTop = 𝟙 _ := by
      rw [show (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos).hom
          = Proj.basicOpenToSpec (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) from
        Proj.basicOpenIsoSpec_hom _ _ _ _]
      rw [show (Proj.basicOpenToSpec (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).appTop
          = (Scheme.ΓSpecIso _).hom
            ≫ Proj.awayToSection _ _
            ≫ (Proj.basicOpen (quotientGrading (projIdeal W))
                ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).topIso.inv from
        Proj.basicOpenToSpec_app_top _ _]
      rw [show Proj.awayToSection (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          = (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
              (mk_X_mem_quotientGrading_one W 2) one_pos).hom from rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    calc (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appLE ⊤ ⊤ le_rfl
        = ((_ ≫ (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
              (mk_X_mem_quotientGrading_one W 2) one_pos).hom.appTop)
          ≫ (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
              (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appTop) := by
          rw [hBA, Category.id_comp, happ]
      _ = _ ≫ ((Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
              (mk_X_mem_quotientGrading_one W 2) one_pos).hom.appTop
            ≫ (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W)) _
              (mk_X_mem_quotientGrading_one W 2) one_pos).inv.appTop) := by
          rw [Category.assoc]
      _ = _ := by rw [hround, Category.comp_id]
  rw [hspec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- **(T3 — evaluation of a chart-factored point on chart sections)** Pulling a `zChart`-section
back along `chartSpecPoint` and reading the global section of `Spec L` computes the solution hom
through the `awayToSection` presentation. -/
lemma chartSpecPoint_appLE_eval (x y : L) (h : (W.baseChange L).toAffine.Equation x y)
    (hle : ⊤ ≤ (chartSpecPoint W x y h).1 ⁻¹ᵁ (zChart W : (projModel W).Opens)) :
    (chartSpecPoint W x y h).1.appLE (zChart W : (projModel W).Opens) ⊤ hle
        ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv
          ≫ CommRingCat.ofHom (chartSolutionHom W x y h) := by
  have hZle : (⊤ : (Spec (CommRingCat.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).Opens)
      ≤ (Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos) ⁻¹ᵁ (zChart W : (projModel W).Opens) := by
    intro x _
    have hx : (Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos).base x
        ∈ (Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange := ⟨x, rfl⟩
    rwa [Proj.opensRange_awayι] at hx
  simp only [chartSpecPoint_val W x y h]
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (chartSolutionHom W x y h)))
    (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos)
    (zChart W : (projModel W).Opens) ⊤ ⊤ hZle le_rfl]
  have happ2 : (Spec.map (CommRingCat.ofHom (chartSolutionHom W x y h))).appLE ⊤ ⊤ le_rfl
      = (Spec.map (CommRingCat.ofHom (chartSolutionHom W x y h))).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [happ2, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    awayι_appLE_eval W hZle]


/-- **(L4-iii brick 4 — the readout-back)** A model point whose dictionary value is the affine
point `some x y` IS the chart-constructed point `chartSpecPoint x y` — by injectivity of the
dictionary. This turns a computed dictionary value into an explicit chart factorization (with a
known chart-hom), the step that reads the division-polynomial coordinates of `[N]∘τ` back into
the scheme world. -/
theorem eq_chartSpecPoint_of_projModelPointsEquiv_some
    {g : SpecPoints (projModel W) (projModelπ W) L} {x y : L}
    {hxy : (W.baseChange L).toAffine.Nonsingular x y}
    (hg : projModelPointsEquiv W L g = WeierstrassCurve.Affine.Point.some x y hxy) :
    g = chartSpecPoint W x y (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr hxy) := by
  apply (projModelPointsEquiv W L).injective
  rw [hg, projModelPointsEquiv_chartSpecPoint]

/-- **(L4-iii brick 2a — the tautological `K(E)`-point of the model)** The chart-constructed
point with the generic coordinates `(x_gen, y_gen)`. -/
noncomputable def genericSpecPoint :
    SpecPoints (projModel W) (projModelπ W) W.toAffine.FunctionField :=
  chartSpecPoint W (x_gen W) (y_gen W) (generic_equation W)

theorem inZChart_genericSpecPoint : InZChart W (genericSpecPoint W) :=
  inZChart_chartSpecPoint W _ _ (generic_equation W)

/-- **(L4-iii brick 2b — the dictionary reads the tautological point as the generic point)** -/
theorem projModelPointsEquiv_genericSpecPoint :
    projModelPointsEquiv W W.toAffine.FunctionField (genericSpecPoint W)
      = genericPoint W :=
  projModelPointsEquiv_chartSpecPoint W (x_gen W) (y_gen W) (generic_equation W)

/-- The `[n]`-image coordinates satisfy the Weierstrass equation (extracted from
`zsmul_genericPoint`'s witness). -/
theorem mulByInt_equation {n : ℤ} (hn : n ≠ 0) :
    (W.baseChange W.toAffine.FunctionField).toAffine.Equation
      (mulByInt_x W n) (mulByInt_y W n) := by
  obtain ⟨h, -⟩ := zsmul_genericPoint W hn
  exact WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h

/-- **(PHI — the tautological solution hom is the canonical embedding)** The solution hom of the
generic datum `(x_gen, y_gen)`, transported through the chart identification `chartZRingEquiv`,
is the canonical coordinate-ring embedding into the function field. -/
lemma chartSolutionHom_generic_comp :
    (chartSolutionHom W (x_gen W.toAffine) (y_gen W.toAffine) (generic_equation W.toAffine)).comp
        ((chartZRingEquiv W).symm : W.toAffine.CoordinateRing →+* _)
      = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      show chartSolutionHom W _ _ _ ((chartZRingEquiv W).symm
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a))) = _
      have h1 : (AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C a)
          = algebraMap K W.toAffine.CoordinateRing a := rfl
      rw [h1, show (chartZRingEquiv W).symm (algebraMap K W.toAffine.CoordinateRing a)
          = (HomogeneousLocalization.fromZeroRingHom
              (quotientGrading (projIdeal W)) (Submonoid.powers
                ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
            ((algebraMapGradeZero (projIdeal W)) a) from
        (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_fromZero W a).symm]
      rw [chartSolutionHom_fromZero]
      exact (IsScalarTower.algebraMap_apply K W.toAffine.CoordinateRing
        W.toAffine.FunctionField a).symm
    · show chartSolutionHom W _ _ _ ((chartZRingEquiv W).symm
          ((AdjoinRoot.of W.toAffine.polynomial) Polynomial.X)) = _
      have h1 : (AdjoinRoot.of W.toAffine.polynomial) Polynomial.X = coordX W := rfl
      rw [h1, show (chartZRingEquiv W).symm (coordX W)
          = HomogeneousLocalization.Away.isLocalizationElem
              (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0) from
        (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_x W).symm]
      rw [chartSolutionHom_x]
      rfl
  · show chartSolutionHom W _ _ _ ((chartZRingEquiv W).symm
        (AdjoinRoot.root W.toAffine.polynomial)) = _
    have h1 : AdjoinRoot.root W.toAffine.polynomial = coordY W := rfl
    rw [h1, show (chartZRingEquiv W).symm (coordY W)
        = HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1) from
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_y W).symm]
    rw [chartSolutionHom_y]
    rfl

/-- The tautological solution hom is injective (it is the canonical embedding, PHI). -/
lemma chartSolutionHom_generic_injective :
    Function.Injective
      (chartSolutionHom W (x_gen W.toAffine) (y_gen W.toAffine)
        (generic_equation W.toAffine)) := by
  have hcomp := chartSolutionHom_generic_comp W
  have : (chartSolutionHom W (x_gen W.toAffine) (y_gen W.toAffine)
      (generic_equation W.toAffine))
      = (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
          ((chartZRingEquiv W) : _ →+* W.toAffine.CoordinateRing) := by
    rw [← hcomp, RingHom.comp_assoc]
    ext a
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply]
  rw [this]
  exact (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    (chartZRingEquiv W).injective

/-- **(τ hits the generic point)** The tautological `K(E)`-point lands on the generic point of the
projective model. -/
lemma genericSpecPoint_base_closedPoint :
    (genericSpecPoint W).1.base
        (IsLocalRing.closedPoint (W.toAffine.FunctionField))
      = genericPoint (projModel W) := by
  haveI : IsDomain (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
    (chartZRingEquiv W).toMulEquiv.isDomain W.toAffine.CoordinateRing
  haveI : IrreducibleSpace (projModel W) :=
    inferInstanceAs (IrreducibleSpace (projModel W))
  haveI : Nontrivial (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) := inferInstance
  haveI : IsDominant (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos) := by
    constructor
    have hrange : Set.range (Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos).base
        = ((zChart W : (projModel W).Opens) : Set (projModel W)) := by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    haveI : Nonempty (Spec (CommRingCat.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))
    rw [DenseRange, hrange]
    refine (zChart W : (projModel W).Opens).isOpen.dense ?_
    refine ⟨(Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W 2) one_pos).base (Classical.arbitrary _), ?_⟩
    rw [← hrange]
    exact Set.mem_range_self _
  -- the underlying morphism factors through the chart
  have hval : (genericSpecPoint W).1
      = Spec.map (CommRingCat.ofHom (chartSolutionHom W (x_gen W.toAffine)
          (y_gen W.toAffine) (generic_equation W.toAffine)))
        ≫ Proj.awayι (quotientGrading (projIdeal W)) _
            (mk_X_mem_quotientGrading_one W 2) one_pos :=
    chartSpecPoint_val W _ _ _
  rw [hval]
  have hstep : (Spec.map (CommRingCat.ofHom (chartSolutionHom W (x_gen W.toAffine)
      (y_gen W.toAffine) (generic_equation W.toAffine)))).base
        (IsLocalRing.closedPoint (W.toAffine.FunctionField))
      = genericPoint (Spec (CommRingCat.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) := by
    rw [genericPoint_eq_bot_of_affine]
    show PrimeSpectrum.comap (chartSolutionHom W _ _ _)
        (IsLocalRing.closedPoint (W.toAffine.FunctionField)) = ⊥
    have hclosed : (IsLocalRing.closedPoint (W.toAffine.FunctionField)).asIdeal = ⊥ :=
      IsLocalRing.maximalIdeal_eq_bot
    ext1
    show Ideal.comap (chartSolutionHom W _ _ _)
        (IsLocalRing.closedPoint (W.toAffine.FunctionField)).asIdeal = ⊥
    rw [hclosed]
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (chartSolutionHom_generic_injective W)
  rw [Scheme.Hom.comp_apply, hstep]
  exact genericPoint_eq_of_isDominant
    (Proj.awayι (quotientGrading (projIdeal W)) _
      (mk_X_mem_quotientGrading_one W 2) one_pos)
    (X := Spec (CommRingCat.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))


/-- **(L4-iii brick 5 — the explicit chart factorization of `τ ≫ [n]`)** Composing the
tautological point with multiplication-by-`n` gives exactly the chart-constructed point with the
division-polynomial coordinates. -/
theorem genericSpecPoint_comp_mulByHom {n : ℤ} (hn : n ≠ 0) :
    (genericSpecPoint W).1 ≫ (modelEllipticCurve W).mulByHom n
      = (chartSpecPoint W (mulByInt_x W n) (mulByInt_y W n) (mulByInt_equation W hn)).1 := by
  -- view τ as a point of the model elliptic curve over `Spec K(E)`
  set g : Spec (CommRingCat.of W.toAffine.FunctionField) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K W.toAffine.FunctionField)) with hg
  set τP : (modelEllipticCurve W).Point g := genericSpecPoint W with hτ
  -- the smul acts by composition with [n]
  have hsm : ((n • τP : (modelEllipticCurve W).Point g) :
      Spec (CommRingCat.of W.toAffine.FunctionField) ⟶ (modelEllipticCurve W).E)
      = (τP : Spec (CommRingCat.of W.toAffine.FunctionField) ⟶ (modelEllipticCurve W).E)
        ≫ (modelEllipticCurve W).mulByHom n :=
    point_smul_eq_comp_mulBy (modelEllipticCurve W) g n τP
  -- the dictionary value of n • τ
  have hdict : projModelPointsEquiv W W.toAffine.FunctionField (n • τP)
      = n • genericPoint W := by
    rw [projModelPointsEquiv_zsmul W n τP]
    congr 1
    exact projModelPointsEquiv_genericSpecPoint W
  obtain ⟨hns, hzs⟩ := zsmul_genericPoint W hn
  rw [hzs] at hdict
  -- readback: n • τ is the chart point
  have hchart := eq_chartSpecPoint_of_projModelPointsEquiv_some W hdict
  have hval : ((n • τP : (modelEllipticCurve W).Point g) :
      Spec (CommRingCat.of W.toAffine.FunctionField) ⟶ (modelEllipticCurve W).E)
      = (chartSpecPoint W (mulByInt_x W n) (mulByInt_y W n)
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr hns)).1 :=
    congrArg Subtype.val hchart
  exact hsm.symm.trans hval

/-- **(G2 — germ-to-`appLE` converter at a field point)** For a morphism `q : Spec L ⟶ X` (`L` a
field) and an open `U` containing the image of the closed point, the germ composed with the
closed-point stalk evaluation is the `appLE`-pullback read through `ΓSpecIso`. -/
lemma germ_stalkClosedPointTo_eq_appLE {X : Scheme.{u}} {L : Type u} [Field L]
    (q : Spec (CommRingCat.of L) ⟶ X) (U : X.Opens)
    (hU : q.base (IsLocalRing.closedPoint L) ∈ U)
    (hle : ⊤ ≤ q ⁻¹ᵁ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo q
      = q.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  rw [Scheme.Hom.appLE]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  congr 1

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
  [W.IsElliptic]

/-- The generic point lies in the `Z`-chart. -/
lemma genericPoint_mem_zChart : genericPoint (projModel W) ∈ (zChart W : (projModel W).Opens) := by
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial Γ(projModel W, zChart W) := (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty (zChart W : (projModel W).Opens) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI : IrreducibleSpace (projModel W) := inferInstanceAs (IrreducibleSpace (projModel W))
  exact ((genericPoint_spec (projModel W)).mem_open_set_iff
    (zChart W : (projModel W).Opens).isOpen).mpr (by simpa using hNe)

/-- **(the germ value of the function-field equivalence)** `projModelFunctionFieldEquiv` sends the
germ of a `Z`-section to the canonical fraction-field image of its coordinate-ring form. -/
lemma projModelFunctionFieldEquiv_germ
    [Nonempty (zChart W : (projModel W).Opens)]
    [IsFractionRing Γ(projModel W, zChart W) (projModel W).functionField]
    (s : Γ(projModel W, zChart W)) :
    projModelFunctionFieldEquiv W
        (algebraMap Γ(projModel W, zChart W) (projModel W).functionField s)
      = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          ((coordRingToZSection W).symm s) := by
  unfold projModelFunctionFieldEquiv
  rw [IsLocalization.ringEquivOfRingEquiv_eq]

/-- **(M — the function-field equivalence IS the tautological-point stalk evaluation)** -/
lemma projModelFunctionFieldEquiv_eq_stalkClosedPointTo :
    ((projModelFunctionFieldEquiv W :
        (projModel W).functionField →+* W.toAffine.FunctionField))
      = (Scheme.stalkClosedPointTo (genericSpecPoint W).1).hom.comp
          ((eqToHom (congrArg (projModel W).presheaf.stalk
              (genericSpecPoint_base_closedPoint W).symm) :
            ((projModel W).functionField : CommRingCat)
              ⟶ (projModel W).presheaf.stalk ((genericSpecPoint W).1.base
                  (IsLocalRing.closedPoint (W.toAffine.FunctionField))))).hom := by
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial Γ(projModel W, zChart W) := (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty (zChart W : (projModel W).Opens) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI : IrreducibleSpace (projModel W) := inferInstanceAs (IrreducibleSpace (projModel W))
  haveI hFR : IsFractionRing Γ(projModel W, zChart W) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) (zChart W) hZaff
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(projModel W, zChart W))
  ext s
  -- LHS: the germ value of the equivalence
  show projModelFunctionFieldEquiv W
      (algebraMap Γ(projModel W, zChart W) (projModel W).functionField s) = _
  rw [projModelFunctionFieldEquiv_germ W s]
  -- RHS: transport the germ along τ-hits, then evaluate via G2 + T3 + PHI
  have hτZ : (genericSpecPoint W).1.base (IsLocalRing.closedPoint (W.toAffine.FunctionField))
      ∈ (zChart W : (projModel W).Opens) := by
    rw [genericSpecPoint_base_closedPoint W]
    exact genericPoint_mem_zChart W
  have hRHS : (Scheme.stalkClosedPointTo (genericSpecPoint W).1).hom
      ((eqToHom (congrArg (projModel W).presheaf.stalk
          (genericSpecPoint_base_closedPoint W).symm) :
        ((projModel W).functionField : CommRingCat) ⟶ _).hom
        (algebraMap Γ(projModel W, zChart W) (projModel W).functionField s))
      = ((genericSpecPoint W).1.appLE (zChart W : (projModel W).Opens) ⊤
          (Scheme.preimage_eq_top_of_closedPoint_mem (genericSpecPoint W).1 hτZ).ge
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (W.toAffine.FunctionField))).hom) s := by
    have htransport : (eqToHom (congrArg (projModel W).presheaf.stalk
          (genericSpecPoint_base_closedPoint W).symm) :
        ((projModel W).functionField : CommRingCat) ⟶ _).hom
          (algebraMap Γ(projModel W, zChart W) (projModel W).functionField s)
        = (projModel W).presheaf.germ (zChart W : (projModel W).Opens) _ hτZ s :=
      germ_eqToHom_stalk_apply (projModel W) (zChart W : (projModel W).Opens)
        (genericSpecPoint_base_closedPoint W).symm (genericPoint_mem_zChart W) hτZ s
    rw [htransport]
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (germ_stalkClosedPointTo_eq_appLE (genericSpecPoint W).1
        (zChart W : (projModel W).Opens) hτZ
        (Scheme.preimage_eq_top_of_closedPoint_mem (genericSpecPoint W).1 hτZ).ge)) s
  simp only [RingHom.comp_apply]
  rw [hRHS]
  -- evaluate through T3 at the generic datum, then PHI
  have hT3 := chartSpecPoint_appLE_eval W (x_gen W.toAffine) (y_gen W.toAffine)
    (generic_equation W.toAffine)
    (Scheme.preimage_eq_top_of_closedPoint_mem (genericSpecPoint W).1 hτZ).ge
  have hval := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hT3) s
  rw [show ((genericSpecPoint W).1.appLE (zChart W : (projModel W).Opens) ⊤
        (Scheme.preimage_eq_top_of_closedPoint_mem (genericSpecPoint W).1 hτZ).ge
      ≫ (Scheme.ΓSpecIso (CommRingCat.of (W.toAffine.FunctionField))).hom) s
      = chartSolutionHom W (x_gen W.toAffine) (y_gen W.toAffine)
          (generic_equation W.toAffine)
        ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv.hom s) from hval]
  have hPHI := DFunLike.congr_fun (chartSolutionHom_generic_comp W)
    ((chartZRingEquiv W) ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv.hom s))
  simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply] at hPHI
  rw [hPHI]
  rfl



/-- **(KEY-EVAL — the function-field equivalence evaluates germs through the tautological
point)** For any open `V` containing the generic point (equivalently, any nonempty open) and any
section `t`, the `projModelFunctionFieldEquiv`-image of the germ of `t` is the `appLE`-pullback of
`t` along the tautological point, read through `ΓSpecIso`. Corollary of the master lemma (M). -/
lemma projModelFunctionFieldEquiv_germ_eval (V : (projModel W).Opens)
    (hξ : genericPoint (projModel W) ∈ V)
    (hτ : (genericSpecPoint W).1.base
      (IsLocalRing.closedPoint (W.toAffine.FunctionField)) ∈ V)
    (hle : ⊤ ≤ (genericSpecPoint W).1 ⁻¹ᵁ V) (t : Γ(projModel W, V)) :
    projModelFunctionFieldEquiv W ((projModel W).presheaf.germ V _ hξ t)
      = ((genericSpecPoint W).1.appLE V ⊤ hle
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (W.toAffine.FunctionField))).hom).hom t := by
  have hM := DFunLike.congr_fun (projModelFunctionFieldEquiv_eq_stalkClosedPointTo W)
    ((projModel W).presheaf.germ V _ hξ t)
  rw [show ((projModelFunctionFieldEquiv W :
      (projModel W).functionField →+* W.toAffine.FunctionField))
      ((projModel W).presheaf.germ V _ hξ t)
      = projModelFunctionFieldEquiv W ((projModel W).presheaf.germ V _ hξ t) from rfl] at hM
  rw [hM]
  simp only [RingHom.comp_apply]
  have htransport : (eqToHom (congrArg (projModel W).presheaf.stalk
        (genericSpecPoint_base_closedPoint W).symm) :
      ((projModel W).functionField : CommRingCat) ⟶ _).hom
        ((projModel W).presheaf.germ V _ hξ t)
      = (projModel W).presheaf.germ V _ hτ t :=
    germ_eqToHom_stalk_apply (projModel W) V
      (genericSpecPoint_base_closedPoint W).symm hξ hτ t
  rw [htransport]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (germ_stalkClosedPointTo_eq_appLE (genericSpecPoint W).1 V hτ hle)) t


end TautologicalPoint

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

/-- **(L4-iii brick 6, step C+D — the field intertwining)** The scheme function-field pullback
`functionFieldMap [N]` on `K(pM) = (projModel W).functionField`, conjugated to
`W.toAffine.FunctionField` by `projModelFunctionFieldEquiv`, equals HasseWeil's division-polynomial
pullback `mulByInt_pullbackAlgHom`. By `functionField_algHom_ext` this reduces to the two generator
identities (FFM-X/FFM-Y), which discharge from **brick 5** (`genericSpecPoint_comp_mulByHom`, the
scheme-morphism identity `τ ≫ [n] = (division-polynomial chart point)`) transported to the germ
level through the tautological-point stalk map. -/
theorem brick6_intertwining {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)] (hn : (N : ℤ) ≠ 0) :
    haveI : IsIntegral (modelEllipticCurve W).E := inferInstanceAs (IsIntegral (projModel W))
    haveI : IrreducibleSpace (modelEllipticCurve W).E := inferInstance
    ∀ z : (projModel W).functionField,
      projModelFunctionFieldEquiv W (((modelEllipticCurve W).mulByHom N).functionFieldMap z)
        = HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn (projModelFunctionFieldEquiv W z) := by
  haveI iInt : IsIntegral (modelEllipticCurve W).E := inferInstanceAs (IsIntegral (projModel W))
  haveI iIrr : IrreducibleSpace (modelEllipticCurve W).E := inferInstance
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : IsAffine (zChart W).toScheme := hZaff
  haveI : Nontrivial W.toAffine.CoordinateRing := inferInstance
  haveI : Nontrivial Γ(projModel W, zChart W) := (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty (zChart W).toScheme := ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI hNe' : Nonempty ↥(zChart W) := hNe
  haveI hFR : IsFractionRing Γ(projModel W, zChart W) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) (zChart W) hZaff
  let fFMr : (projModel W).functionField →+* (projModel W).functionField :=
    (((modelEllipticCurve W).mulByHom N).functionFieldMap).hom
  set e := projModelFunctionFieldEquiv W with he
  set cRTZ := coordRingToZSection W with hcRTZ
  set ψ := HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn with hψ
  -- the three generator leaves (FFM-X/Y/C: the germ-of-[N]-pullback of the coordinates, evaluated
  -- through `projModelFunctionFieldEquiv`, are the division polynomials — via brick 5).
  have hτV : (genericSpecPoint W).1.base (IsLocalRing.closedPoint (W.toAffine.FunctionField))
      ∈ ((modelEllipticCurve W).mulByHom N) ⁻¹ᵁ (zChart W) := by
    show ((modelEllipticCurve W).mulByHom N).base _ ∈ (zChart W)
    rw [genericSpecPoint_base_closedPoint W]
    show ((modelEllipticCurve W).mulByHom N).base
        (genericPoint (modelEllipticCurve W).E) ∈ (zChart W)
    rw [genericPoint_eq_of_isDominant ((modelEllipticCurve W).mulByHom N)]
    exact genericPoint_mem_zChart W
  have hMASTER : ∀ c : W.toAffine.CoordinateRing,
      e (fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ c)))
        = chartSolutionHom W (HasseWeil.mulByInt_x W.toAffine (N : ℤ))
            (HasseWeil.mulByInt_y W.toAffine (N : ℤ)) (mulByInt_equation W hn)
            ((chartZRingEquiv W).symm c) := by
    intro c
    haveI hNe2 : Nonempty (zChart W : (projModel W).Opens) :=
      ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
    haveI hNe3 : Nonempty (↑(zChart W) : Set ↥(projModel W)) := hNe2
    haveI hNeE : Nonempty (show ((modelEllipticCurve W).E).Opens from zChart W) := hNe2
    have h1 : fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ c))
        = (projModel W).presheaf.germ
            (((modelEllipticCurve W).mulByHom N) ⁻¹ᵁ (zChart W))
            (genericPoint _)
            (genericPoint_mem_preimage ((modelEllipticCurve W).mulByHom N)
              (zChart W))
            (((modelEllipticCurve W).mulByHom N).app (zChart W) (cRTZ c)) :=
      functionFieldMap_germToFunctionField ((modelEllipticCurve W).mulByHom N)
        (zChart W) (cRTZ c)
    have h2 := projModelFunctionFieldEquiv_germ_eval W
      (((modelEllipticCurve W).mulByHom N) ⁻¹ᵁ (zChart W))
      (genericPoint_mem_preimage ((modelEllipticCurve W).mulByHom N)
        (zChart W)) hτV
      (Scheme.preimage_eq_top_of_closedPoint_mem _ hτV).ge
      (((modelEllipticCurve W).mulByHom N).app (zChart W) (cRTZ c))
    rw [he] at *
    rw [show fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ c))
        = (projModel W).presheaf.germ _ _ _ _ from h1, h2]
    have hfold : (((genericSpecPoint W).1.appLE
          (((modelEllipticCurve W).mulByHom N) ⁻¹ᵁ (zChart W)) ⊤
          (Scheme.preimage_eq_top_of_closedPoint_mem _ hτV).ge)
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (W.toAffine.FunctionField))).hom).hom
        ((((modelEllipticCurve W).mulByHom N).app (zChart W)).hom (cRTZ c))
        = ((((genericSpecPoint W).1 ≫ (modelEllipticCurve W).mulByHom N).appLE
            (zChart W) ⊤
            (le_trans (Scheme.preimage_eq_top_of_closedPoint_mem _ hτV).ge le_rfl))
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (W.toAffine.FunctionField))).hom).hom
            (cRTZ c) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [hfold]
    have hb5 : (genericSpecPoint W).1 ≫ (modelEllipticCurve W).mulByHom (N : ℤ)
        = (chartSpecPoint W (HasseWeil.mulByInt_x W.toAffine (N : ℤ))
            (HasseWeil.mulByInt_y W.toAffine (N : ℤ)) (mulByInt_equation W hn)).1 :=
      genericSpecPoint_comp_mulByHom W hn
    simp only [hb5]
    have hT3 := chartSpecPoint_appLE_eval W (HasseWeil.mulByInt_x W.toAffine (N : ℤ))
      (HasseWeil.mulByInt_y W.toAffine (N : ℤ)) (mulByInt_equation W hn)
      (by
        rw [← hb5]
        exact le_trans (Scheme.preimage_eq_top_of_closedPoint_mem _ hτV).ge le_rfl)
    refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hT3) (cRTZ c)).trans ?_
    show chartSolutionHom W _ _ _
        ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
            (mk_X_mem_quotientGrading_one W 2) one_pos).inv.hom (cRTZ c)) = _
    congr 1
    rw [hcRTZ]
    show (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv.hom
        ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).hom.hom
          ((chartZRingEquiv W).symm c)) = _
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).hom_inv_id)
      ((chartZRingEquiv W).symm c)
  have FFM_X :
      e (fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ (coordX W))))
        = HasseWeil.mulByInt_x W.toAffine (N : ℤ) := by
    rw [hMASTER (coordX W), show (chartZRingEquiv W).symm (coordX W)
        = HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0) from
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_x W).symm]
    exact chartSolutionHom_x W _ _ _
  have FFM_Y :
      e (fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ (coordY W))))
        = HasseWeil.mulByInt_y W.toAffine (N : ℤ) := by
    rw [hMASTER (coordY W), show (chartZRingEquiv W).symm (coordY W)
        = HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1) from
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_y W).symm]
    exact chartSolutionHom_y W _ _ _
  have FFM_C : ∀ r : K,
      e (fFMr ((projModel W).germToFunctionField (zChart W)
          (cRTZ (algebraMap K W.toAffine.CoordinateRing r))))
        = algebraMap K W.toAffine.FunctionField r := by
    intro r
    rw [hMASTER (algebraMap K W.toAffine.CoordinateRing r),
      show (chartZRingEquiv W).symm (algebraMap K W.toAffine.CoordinateRing r)
        = (HomogeneousLocalization.fromZeroRingHom
            (quotientGrading (projIdeal W)) (Submonoid.powers
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
          ((algebraMapGradeZero (projIdeal W)) r) from
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_fromZero W r).symm]
    exact chartSolutionHom_fromZero W _ _ _ r
  have he_gtff : ∀ c : W.toAffine.CoordinateRing,
      e ((projModel W).germToFunctionField (zChart W) (cRTZ c))
        = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField c := by
    intro c
    rw [he, hcRTZ]
    have h2 : projModelFunctionFieldEquiv W
        (algebraMap Γ(projModel W, zChart W) (projModel W).functionField
          (coordRingToZSection W c))
        = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            ((coordRingToZSection W).symm (coordRingToZSection W c)) := by
      unfold projModelFunctionFieldEquiv
      rw [IsLocalization.ringEquivOfRingEquiv_eq]
    rw [RingEquiv.symm_apply_apply] at h2
    exact h2
  have hxgen : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (coordX W)
      = HasseWeil.x_gen W.toAffine := by
    rw [HasseWeil.x_gen, coordX]; rfl
  have hygen : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (coordY W)
      = HasseWeil.y_gen W.toAffine := by
    rw [HasseWeil.y_gen, coordY]; rfl
  have hcgen : ∀ a : K, algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap K W.toAffine.CoordinateRing a) = algebraMap K W.toAffine.FunctionField a := by
    intro a; rw [← IsScalarTower.algebraMap_apply]
  suffices h :
      (e.toRingHom.comp fFMr).comp
          (algebraMap Γ(projModel W, zChart W) (projModel W).functionField)
        = (ψ.toRingHom.comp e.toRingHom).comp
            (algebraMap Γ(projModel W, zChart W) (projModel W).functionField) by
    have hAB : e.toRingHom.comp fFMr = ψ.toRingHom.comp e.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors Γ(projModel W, zChart W)) h
    intro z
    exact DFunLike.congr_fun hAB z
  rw [← RingHom.cancel_right (g₁ := (e.toRingHom.comp fFMr).comp
        (algebraMap Γ(projModel W, zChart W) (projModel W).functionField))
      (g₂ := (ψ.toRingHom.comp e.toRingHom).comp
        (algebraMap Γ(projModel W, zChart W) (projModel W).functionField))
      (f := cRTZ.toRingHom) cRTZ.surjective]
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      have hR : ψ (e ((projModel W).germToFunctionField (zChart W)
          (cRTZ (algebraMap K W.toAffine.CoordinateRing a))))
          = algebraMap K W.toAffine.FunctionField a := by
        rw [he_gtff, hcgen, hψ, AlgHom.commutes]
      show e (fFMr ((projModel W).germToFunctionField (zChart W)
            (cRTZ (algebraMap K W.toAffine.CoordinateRing a))))
          = ψ (e ((projModel W).germToFunctionField (zChart W)
            (cRTZ (algebraMap K W.toAffine.CoordinateRing a))))
      rw [FFM_C a, hR]
    · have hR : ψ (e ((projModel W).germToFunctionField (zChart W) (cRTZ (coordX W))))
          = HasseWeil.mulByInt_x W.toAffine (N : ℤ) := by
        rw [he_gtff, hxgen, hψ, mulByInt_pullbackAlgHom_x_gen (W := W.toAffine) hn]
      show e (fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ (coordX W))))
          = ψ (e ((projModel W).germToFunctionField (zChart W) (cRTZ (coordX W))))
      rw [FFM_X, hR]
  · have hR : ψ (e ((projModel W).germToFunctionField (zChart W) (cRTZ (coordY W))))
        = HasseWeil.mulByInt_y W.toAffine (N : ℤ) := by
      rw [he_gtff, hygen, hψ, mulByInt_pullbackAlgHom_y_gen (W := W.toAffine) hn]
    show e (fFMr ((projModel W).germToFunctionField (zChart W) (cRTZ (coordY W))))
        = ψ (e ((projModel W).germToFunctionField (zChart W) (cRTZ (coordY W))))
    rw [FFM_Y, hR]

/-- **(brick 6, steps B+C — the opens-level tower, direct-`K(E)` form)** `finrank Γ(Z) Γ([N]⁻¹Z)`
along the `[N]`-pullback of sections equals `(mulByInt N).degree`: localize both sides into
`W.toAffine.FunctionField` through `projModelFunctionFieldEquiv` (the `R`-leg is the fraction-field
structure of the `Z`-chart, the `S`-leg that of the preimage chart), take the `K(E)`-module
structure to be the division-polynomial pullback `mulByInt_pullbackAlgHom`, and observe that the
scalar-tower condition is exactly [banked square] + [PROVEN intertwining]. Then
`finrank_of_isFractionRing` evaluates the left side to the isogeny degree. -/
lemma towerBC {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)] (hn : (N : ℤ) ≠ 0)
    (φN : projModel W ⟶ projModel W) (hφN : φN = (modelEllipticCurve W).mulByHom N)
    (hDom : IsDominant φN) (hFin : IsFinite φN)
    (hfin : letI := (φN.app (zChart W)).hom.toAlgebra
      Module.Finite Γ(projModel W, zChart W) Γ(projModel W, φN ⁻¹ᵁ (zChart W))) :
    letI := (φN.app (zChart W)).hom.toAlgebra
    Module.finrank Γ(projModel W, zChart W) Γ(projModel W, φN ⁻¹ᵁ (zChart W))
      = (HasseWeil.mulByInt W.toAffine (N : ℤ)).degree := by
  haveI iInt : IsIntegral (projModel W) := inferInstance
  haveI iIrr : IrreducibleSpace (projModel W) := inferInstance
  haveI hφdom : IsDominant φN := hDom
  haveI hφfin : IsFinite φN := hFin
  haveI hZaff : IsAffineOpen (zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial Γ(projModel W, zChart W) := (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe2 : Nonempty (zChart W : (projModel W).Opens) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI hNeV : Nonempty (φN ⁻¹ᵁ (zChart W)) :=
    ⟨⟨_, genericPoint_mem_preimage φN (zChart W)⟩⟩
  haveI hFRZ : IsFractionRing Γ(projModel W, zChart W) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) (zChart W) hZaff
  haveI hVaff : IsAffineOpen (φN ⁻¹ᵁ (zChart W)) := by
    haveI hAff : IsAffineHom φN := hφfin.toIsAffineHom
    exact hZaff.preimage φN
  haveI hFRV : IsFractionRing Γ(projModel W, φN ⁻¹ᵁ (zChart W))
      (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) _ hVaff
  -- named building blocks (no ambient-instance dependence)
  set R := Γ(projModel W, zChart W)
  set S := Γ(projModel W, φN ⁻¹ᵁ (zChart W))
  set KE := W.toAffine.FunctionField with hKE
  set e := projModelFunctionFieldEquiv W with he
  -- the algebras: R' := K(pM) with the germ structure; S' := K(E) with the e-transported
  -- V-germ structure; the R'-module on S' is the division-polynomial pullback composed with e.
  letI algRS : Algebra ↑R ↑S := (φN.app (zChart W)).hom.toAlgebra
  letI algSKE : Algebra ↑S KE :=
    (e.toRingHom.comp (algebraMap ↑S (projModel W).functionField)).toAlgebra
  letI algRKE : Algebra ↑R KE :=
    ((e.toRingHom.comp (algebraMap ↑S (projModel W).functionField)).comp
      (φN.app (zChart W)).hom).toAlgebra
  letI algKpMKE : Algebra ↑(projModel W).functionField KE :=
    ((HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn).toRingHom.comp
      e.toRingHom).toAlgebra
  letI algKEKE : Algebra KE KE :=
    (HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn).toRingHom.toAlgebra
  letI modKpMKE : Module ↑(projModel W).functionField KE := algKpMKE.toModule
  -- the S-side fraction-ring structure transported along `e`
  haveI hFRV' : @IsFractionRing ↑S _ KE _ algSKE := by
    have := @IsLocalization.isLocalization_iff_of_ringEquiv ↑S _
      (nonZeroDivisors ↑S) (projModel W).functionField _ _ KE _ e
    exact this.mp hFRV
  -- the two scalar towers
  haveI towRSS' : IsScalarTower ↑R ↑S KE :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hkey : ∀ r : ↑R,
      (HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn)
        (e ((algebraMap ↑R (projModel W).functionField) r))
      = e ((algebraMap ↑S (projModel W).functionField)
          ((φN.app (zChart W)).hom r)) := by
    intro r
    have hsq : (algebraMap ↑S (projModel W).functionField)
          ((φN.app (zChart W)).hom r)
        = (φN.functionFieldMap).hom
            ((algebraMap ↑R (projModel W).functionField) r) :=
      (functionFieldMap_germToFunctionField φN (zChart W) r).symm
    rw [hsq]
    subst hφN
    exact (brick6_intertwining W N hn
      ((algebraMap ↑R (projModel W).functionField) r)).symm
  haveI towRR'S' : @IsScalarTower ↑R ↑(projModel W).functionField KE
      _ modKpMKE.toSMul _ := by
    refine ⟨fun r a x => ?_⟩
    show ((HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn).toRingHom.comp
        e.toRingHom) ((algebraMap ↑R (projModel W).functionField r) * a) * x
      = ((e.toRingHom.comp (algebraMap ↑S (projModel W).functionField)).comp
          (φN.app (zChart W)).hom) r
        * (((HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn).toRingHom.comp
            e.toRingHom) a * x)
    rw [map_mul, mul_assoc]
    congr 1
    exact hkey r
  -- side instances
  haveI hFaith : FaithfulSMul ↑R ↑S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have hgm : ∀ c : ↑R, (algebraMap ↑R (projModel W).functionField) c
        = (projModel W).germToFunctionField (zChart W) c := fun c => rfl
    have h3 : (φN.functionFieldMap).hom
        ((algebraMap ↑R (projModel W).functionField) a)
        = (φN.functionFieldMap).hom
          ((algebraMap ↑R (projModel W).functionField) b) := by
      rw [hgm a, hgm b, functionFieldMap_germToFunctionField φN (zChart W) a,
        functionFieldMap_germToFunctionField φN (zChart W) b]
      exact congrArg (algebraMap ↑S (projModel W).functionField) hab
    have h4 := functionFieldMap_injective φN h3
    exact IsFractionRing.injective ↑R ((projModel W).functionField : CommRingCat) h4
  haveI hNZD : NoZeroDivisors ↑S := by
    have hinj : Function.Injective
        ((projModel W).germToFunctionField (φN ⁻¹ᵁ (zChart W))) :=
      Scheme.germToFunctionField_injective _ _
    exact hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  haveI hfin' : Module.Finite ↑R ↑S := hfin
  haveI hInt : Algebra.IsIntegral ↑R ↑S := Algebra.IsIntegral.of_finite _ _
  haveI hAlgebraic : Algebra.IsAlgebraic ↑R ↑S := Algebra.IsIntegral.isAlgebraic
  -- the core: finrank over the fraction fields = finrank over the opens
  have hcore := Algebra.IsAlgebraic.finrank_of_isFractionRing
    (R := ↑R) (R' := ((projModel W).functionField : CommRingCat)) (S := ↑S) (S' := KE)
  rw [← hcore]
  -- the degree: `modKpMKE`-finrank transports along `e` to the ψ-module finrank = degree
  have hC := Algebra.finrank_eq_of_equiv_equiv
    (R₀ := ((projModel W).functionField : CommRingCat)) (S₀ := KE)
    (R₁ := KE) (S₁ := KE)
    (i := e) (j := RingEquiv.refl KE)
    (by
      ext z
      rfl)
  rw [hC]
  -- match the degree module (the isogeny pullback IS ψ for n ≠ 0)
  rw [HasseWeil.Isogeny.degree]
  have hpb : (HasseWeil.mulByInt W.toAffine (N : ℤ)).pullback
      = HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn := dif_neg hn
  have hMod : (HasseWeil.mulByInt W.toAffine (N : ℤ)).toAlgebra.toModule
      = algKEKE.toModule := by
    show (HasseWeil.mulByInt W.toAffine (N : ℤ)).pullback.toRingHom.toAlgebra.toModule = _
    rw [hpb]
  exact (congrArg (fun m : Module W.toAffine.FunctionField W.toAffine.FunctionField
    => @Module.finrank _ _ _ _ m) hMod).symm

/-- **(L4-iii brick 6, steps A+B — the fraction-field tower assembly)** Given the field intertwining,
the module rank `Module.finrank Γ(Z) Γ([N]⁻¹Z)` equals `(mulByInt N).degree`. Transport the appTop
module to `Γ(E, [N]⁻¹ᵁZ)` (`pullbackRestrictIsoRestrict`); both localise to `K(pM)` via
`germToFunctionField`; the scalar tower is the banked square `functionFieldMap_comp_germToFunctionField`;
`Algebra.IsAlgebraic.finrank_of_isFractionRing` gives `= Module.finrank K(pM) K(pM)` (via
`functionFieldMap [N]`), which the intertwining transports to `Module.finrank K(E) K(E)` (via
`mulByInt_pullbackAlgHom`) `= (mulByInt N).degree`. -/
theorem brick6_from_intertwining {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    [LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom N)] (hn : (N : ℤ) ≠ 0)
    (hinter :
      haveI : IsIntegral (modelEllipticCurve W).E := inferInstanceAs (IsIntegral (projModel W))
      haveI : IrreducibleSpace (modelEllipticCurve W).E := inferInstance
      ∀ z : (projModel W).functionField,
        projModelFunctionFieldEquiv W (((modelEllipticCurve W).mulByHom N).functionFieldMap z)
          = HasseWeil.mulByInt_pullbackAlgHom W.toAffine (N : ℤ) hn (projModelFunctionFieldEquiv W z)) :
    letI := (pullback.snd ((modelEllipticCurve W).mulByHom N) (zChart W).ι).appTop.hom.toAlgebra
    Module.finrank Γ((zChart W).toScheme, ⊤)
        Γ(pullback ((modelEllipticCurve W).mulByHom N) (zChart W).ι, ⊤)
      = (HasseWeil.mulByInt W.toAffine (N : ℤ)).degree := sorry

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
  -- K4b (brick 6): the field intertwining (via brick 5) + the fraction-field tower assembly.
  have hn : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  exact brick6_from_intertwining W N hn (brick6_intertwining W N hn)

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
