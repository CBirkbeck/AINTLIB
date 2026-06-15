/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.GenericCovarianceGeneral
import HasseWeil.WeilPairing.TorsionKernelRational
import HasseWeil.WeilPairing.TorsionGeometric
import HasseWeil.EC.IsogenyAG.MulByIntBasepoint

/-!
# The separable dual over `K̄`: fixed-field equality and `DualGaloisData` without `[Fintype F]`

`EC/IsogenyAG/DualGalois.lean` assembles `EC.Isogeny.DualGaloisData` for a separable isogeny
**over a finite field**, because the fixed-field equality it reuses
(`HasseWeil.pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`, `Hasse/PointFix.lean`)
carries `[Fintype F]`.  That hypothesis is an artifact: the only step in the PointFix chain that
consumes it is the generation fact `K(E) = F⟮x_gen, y_gen⟯`
(`functionField_eq_intermediateField_adjoin_xy`, stated in the `[Fintype K]` scope of
`Verschiebung/QthRoots.lean`), and the project has the field-general replacements
`algHom_ext_x_y_gen` (`EC/TranslationOrd.lean`) and `adjoin_x_gen_y_gen_eq_top`
(`WeilPairing/TorsionKernelRational.lean`).  The Artin input
`FixedPoints.finrank_eq_card` needs only a finite *group* acting faithfully — and both the
faithfulness (`faithfulSMul_kernel`) and the intrinsic finrank
(`finrank_pullback_fieldRange_eq_degree`) are already field-general in `Hasse/PointFix.lean`.

This file re-bases the chain over an arbitrary field (no `[Fintype F]`), with two further
upgrades over the PointFix shape:

* the `FiniteDimensional ↥β.pullback.fieldRange K(E)` instance hypothesis is **derived**
  (`finiteDimensional_pullback_fieldRange`: finrank `= deg β > 0`);
* the kernel-finiteness instance hypothesis is **derived** from the covariance itself
  (`finite_kernel_of_hcov`).

It then composes the dual end-to-end over `K̄` (`[IsAlgClosed F]`): the covariance engine
`mapTranslateGenericPoint_of_pullbackEvaluation` / the CoordHom instance `xy_family_of_coordHom`
(`WeilPairing/GenericCovarianceGeneral.lean`) discharges `hgcomm`, the re-based fixed-field
equality discharges `hfix`, `card_kernel_eq_degree_of_separable_concrete` discharges
`#ker β = deg β` (from the same `hgcomm`-derived `hcov` plus the two carried Galois witnesses
`h_normal`/`hdesc`), `hnu` is derived from Lagrange + the field-general `[m]`-covariance, and
`hrefl` is the unconditional `EC.Isogeny.reflects_ordAtInfty`.  The remaining per-isogeny
witnesses are exactly: `h_pb`, `hsep`, `hdeg`, the pullback-evaluation witness (`bad = ∅` for a
`CoordHom`), `h_normal`, `hdesc`, and the `[deg β]` basepoint `hν` (`MulByIntBasepoint`).

## Why `h_normal` and `hdesc` stay carried (generality audit)

The `[ℓ]` discharges (`h_normal_mulByInt`, `hdesc_mulByInt`,
`WeilPairing/TorsionKernelRational.lean`) are division-polynomial-gated and do **not**
generalise to an arbitrary isogeny with `{CoordHom, hgcomm, separability}`:

* both route through `kernelDescends_general`, whose "general" refers to a general coefficient
  *extension* `L/F`, not a general isogeny — its content is that an `L`-point killed by `[ℓ]`
  has `x`-coordinate a root of the `F`-coefficient division polynomial `Ψ²_ℓ`, hence descends
  to `F = K̄`.  For an abstract `β` there is no base-changed point map at all (`toAddMonoidHom`
  acts on `F`-points only), so neither "killed by `β` over `L`" nor its descent is statable;
* `hdesc` additionally needs the geometric action *over `K(E)`* at `σ(P_gen)` (for `[ℓ]` this
  is `zsmulAddGroupHom ℓ` + `map_zsmul`); the canonical action `Affine.Point.map β.pullback`
  is functorial coordinate transport, correct only *at* `P_gen`, and `β*(σ x_gen) ≠ β* x_gen`
  for `σ ≠ id`, so it cannot substitute;
* `h_normal` routes through embeddings `K(E) → Ω = AlgebraicClosure K(E)` agreeing on
  `β*K(E)` (`sigma_genCoord_mem_range_proto`) — the same descent wall over `Ω`;
* deriving the missing card/surjectivity content from the fixed-field side instead is
  circular: with the forward inclusion `Im(β*) ≤ Fix(ker β)` and the two unconditional
  finranks, `Im = Fix` *is equivalent to* `#ker = deg`, so one of them must come from
  geometry (Silverman III.4.10c proper).

They are therefore carried as named per-isogeny witnesses, exactly as in
`dualGaloisData_of_separable` (`DualGalois.lean`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10–4.11, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-! ### The fixed-field equality over an arbitrary base field

The field-general re-base of the `Hasse/PointFix.lean` chain
`translateAlgEquivOfPoint_pullback_invariance_of_xy → pullback_fieldRange_le_fixedField_of_xy_family
→ pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`, with
`algHom_ext_x_y_gen` (field-general) replacing the `[Fintype F]`-scoped
`algHom_ext_of_eq_on_xy`. -/

/-- **Generator-restricted covariance reducer, field-general** (the `[Fintype F]`-free
`translateAlgEquivOfPoint_pullback_invariance_of_xy`): covariance of `τ_k` with `β.pullback` on
`x_gen` and `y_gen` extends to all of `K(E)`, via the field-general generator extensionality
`algHom_ext_x_y_gen`. -/
theorem translate_pullback_invariance_of_xy_general
    (β : Isogeny W.toAffine W.toAffine) (k : W.toAffine.Point)
    (h_x : translateAlgEquivOfPoint W k (β.pullback (x_gen W)) = β.pullback (x_gen W))
    (h_y : translateAlgEquivOfPoint W k (β.pullback (y_gen W)) = β.pullback (y_gen W)) :
    ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k (β.pullback z) = β.pullback z := fun z =>
  DFunLike.congr_fun
    (algHom_ext_x_y_gen W
      (ψ₁ := (translateAlgEquivOfPoint W k).toAlgHom.comp β.pullback)
      (ψ₂ := β.pullback) h_x h_y) z

/-- **Forward inclusion of the fixed-field theorem, field-general** (the `[Fintype F]`-free
`pullback_fieldRange_le_fixedField_of_xy_family`): under the xy-covariance family,
`Im(β*) ⊆ Fix(Multiplicative (ker β))`. -/
theorem pullback_fieldRange_le_fixedField_general
    (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W))) :
    β.pullback.fieldRange ≤
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
  rintro z ⟨w, rfl⟩
  intro g
  change translateAlgEquivOfPoint W (Multiplicative.toAdd g).val
      (β.pullback w) = β.pullback w
  exact translate_pullback_invariance_of_xy_general W β
    (Multiplicative.toAdd g).val
    (h_xy_family (Multiplicative.toAdd g)).1
    (h_xy_family (Multiplicative.toAdd g)).2 w

/-- **`K(E)` is finite-dimensional over `Im(β*)`** — the `FiniteDimensional` instance carried by
the PointFix closure, derived: `finrank ↥Im(β*) K(E) = deg β` (intrinsic, field-general) and
`0 < deg β` (`isogeny_degree_pos`). -/
theorem finiteDimensional_pullback_fieldRange
    (β : Isogeny W.toAffine W.toAffine) :
    FiniteDimensional ↥β.pullback.fieldRange W.toAffine.FunctionField :=
  FiniteDimensional.of_finrank_pos
    ((finrank_pullback_fieldRange_eq_degree W β).symm ▸ isogeny_degree_pos W β)

/-- **The Galois fixed-field equality `Im(β*) = Fix(ker β)`, field-general** (Silverman
III.4.10c; the `[Fintype F]`-free `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`).
Inputs: the xy-covariance family and the cardinality match `#ker β = deg β` (`Nat.card` form).
Both finiteness instances of the PointFix version are *derived*: kernel finiteness from the
covariance (`finite_kernel_of_hcov`), `FiniteDimensional ↥Im(β*) K(E)` from
`finiteDimensional_pullback_fieldRange`.  The Artin step `FixedPoints.finrank_eq_card` needs only
the finite *group* `Multiplicative (ker β)` acting faithfully (`faithfulSMul_kernel`,
field-general). -/
theorem pullback_fieldRange_eq_fixedField_general
    (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
  have hcov : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_general W β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov W β hcov
  haveI : Fintype (Multiplicative β.kernel) := Fintype.ofFinite _
  haveI := finiteDimensional_pullback_fieldRange W β
  refine IntermediateField.eq_of_le_of_finrank_eq'
    (pullback_fieldRange_le_fixedField_general W β h_xy_family) ?_
  rw [finrank_pullback_fieldRange_eq_degree W β, ← h_card,
    Nat.card_congr (Multiplicative.ofAdd (α := β.kernel)), Nat.card_eq_fintype_card]
  exact (FixedPoints.finrank_eq_card (Multiplicative β.kernel)
    W.toAffine.FunctionField).symm

/-- **`hfix` from `xy_family` + `#ker = deg`, field-general** (Silverman III.4.10c, packaged for
the dual witness; the `[Fintype F]`-free `fixedField_hfix_of_xy_family_of_card`).  The image of
`β.pullback` is exactly the subset of `K(E)` fixed by the kernel translations — the `hfix` shape
consumed by `EC.Isogeny.DualGaloisData`. -/
theorem fixedField_hfix_general
    (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree) :
    ∀ z : W.toAffine.FunctionField,
      z ∈ β.pullback.range ↔
        ∀ σ ∈ (Set.range (fun k : β.kernel =>
            translateAlgEquivOfPoint W k.val)), σ z = z := by
  have hcov : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_general W β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov W β hcov
  haveI : Fintype (Multiplicative β.kernel) := Fintype.ofFinite _
  have h_eq := pullback_fieldRange_eq_fixedField_general W β h_xy_family h_card
  intro z
  constructor
  · rintro ⟨w, rfl⟩ σ ⟨k, rfl⟩
    have hmem : β.pullback w ∈ β.pullback.fieldRange := ⟨w, rfl⟩
    rw [h_eq] at hmem
    exact hmem (Multiplicative.ofAdd k)
  · intro hz
    have hmem : z ∈ (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) := by
      intro g
      exact hz _ ⟨Multiplicative.toAdd g, rfl⟩
    rw [← h_eq, AlgHom.mem_fieldRange] at hmem
    rw [AlgHom.mem_range]
    exact hmem

/-! ### `hnu` for `ν = [n]` over an arbitrary base field

The DualGalois `hnu_mulByInt_of_kernel_nsmul_zero` lives in the `[Fintype F]` scope only because
it cites the `[Fintype K]`-scoped `mulByInt_isGenuineWith` (`GapSpines.lean`); its ingredients
(`zsmul_genericPoint_eq`, `mulByInt_pullback_x/y`, `mapTranslateGenericPoint_mulByInt`,
`hcomm_of_isGenuineWith`) are all field-general.  We replicate the genuineness inline. -/

/-- **`[N]` is genuine, field-general** (`N ≠ 0`), with geometric action `P ↦ N • P` — the
`[Fintype K]`-free `mulByInt_isGenuineWith`, from the field-general division-polynomial facts
`zsmul_genericPoint_eq` + `mulByInt_pullback_x/y`. -/
theorem mulByInt_isGenuineWith_general (N : ℤ) (hN : N ≠ 0) :
    IsGenuineWith W (mulByInt W.toAffine N) (zsmulPointHom W N) := by
  obtain ⟨hns, hsmul⟩ := zsmul_genericPoint_eq W N hN
  refine ⟨mulByInt_x W N, mulByInt_y W N, hns, ?_, ?_, ?_⟩
  · rw [show zsmulPointHom W N (genericPoint W) = N • genericPoint W from rfl]
    exact Subsingleton.elim (instDecidableEqFunctionField W)
      FractionRing.instDecidableEq ▸ hsmul
  · exact (mulByInt_pullback_x W N hN).symm
  · exact (mulByInt_pullback_y W N hN).symm

/-- **`hnu` for `ν = [n]` from Lagrange, field-general** (Silverman III.6.1; the
`[Fintype F]`-free `hnu_mulByInt_of_kernel_nsmul_zero`): if `n • k = 0` on every kernel point of
`β`, the translation family `{τ_k : k ∈ ker β}` fixes the image of `[n]*`. -/
theorem hnu_mulByInt_general
    (β : Isogeny W.toAffine W.toAffine) (n : ℤ) (hn : n ≠ 0)
    (hdvd : ∀ k ∈ β.kernel, n • k = 0) :
    ∀ σ ∈ (Set.range (fun k : β.kernel => translateAlgEquivOfPoint W k.val)),
      ∀ w, σ ((mulByInt W.toAffine n).pullback w) = (mulByInt W.toAffine n).pullback w := by
  rintro σ ⟨k, rfl⟩ w
  -- `[n]`-covariance: `τ_k([n]* w) = [n]*(τ_{[n]k} w)` (field-general genuine leaf).
  rw [WeilPairing.hcomm_of_isGenuineWith W (mulByInt W.toAffine n)
    (mulByInt_isGenuineWith_general W n hn) k.val
    (WeilPairing.mapTranslateGenericPoint_mulByInt W n k.val) w]
  -- `[n] k = n • k = 0` for `k ∈ ker β` (Lagrange), so `τ_{[n]k} = τ_0 = refl`.
  have hk0 : (mulByInt W.toAffine n).toAddMonoidHom k.val = 0 := by
    rw [mulByInt_apply]; exact hdvd k.val k.property
  rw [hk0]
  rfl

/-- **The `[N]` basepoint condition `hν` is a theorem** (`EC.mulByIntBasepoint_holds`,
`EC/IsogenyAG/MulByIntBasepoint.lean`): the `hν` hypothesis carried by the
`DualGaloisData` assemblers below, discharged unconditionally for `N ≠ 0`. -/
theorem hν_mulByInt (N : ℤ) (hN : N ≠ 0) :
    ∀ f : W.toAffine.FunctionField,
      0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
        ((mulByInt W.toAffine N).pullback f) := by
  intro f hf
  have hpb : (mulByInt W.toAffine N).pullback = mulByInt_pullbackAlgHom W N hN :=
    dif_neg hN
  rw [hpb]
  exact EC.mulByIntBasepoint_holds W.toAffine hN f hf

/-! ### `DualGaloisData` over an arbitrary base field, from the per-`β` witnesses -/

/-- **`DualGaloisData` with `hfix` discharged by the field-general Galois closure** (the
`[Fintype F]`-free `dualGaloisData_of_basic_witnesses`), with `hrefl` additionally *derived*
(`EC.Isogeny.reflects_ordAtInfty`, unconditional) — the finite-field version still carried it. -/
noncomputable def dualGaloisData_of_basic_witnesses_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (νPb : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree)
    (hnu : ∀ σ ∈ (Set.range (fun k : β.kernel =>
        translateAlgEquivOfPoint W k.val)), ∀ w, σ (νPb w) = νPb w)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (νPb f)) :
    EC.Isogeny.DualGaloisData φ where
  νPb := νPb
  transAut := Set.range (fun k : β.kernel => translateAlgEquivOfPoint W k.val)
  hfix := by
    intro z
    rw [h_pb]
    exact fixedField_hfix_general W β h_xy_family h_card z
  hnu := hnu
  hν := hν
  hrefl := fun g hg => EC.Isogeny.reflects_ordAtInfty φ g hg

/-- **`DualGaloisData φ` for a separable isogeny from the generic-point leaf `hgcomm`**
(Silverman III.4.11 / III.6.1) — the field-general analogue of `dualGaloisData_of_separable`,
with `hramO`/`he` *eliminated* (`hrefl` is now the unconditional
`EC.Isogeny.reflects_ordAtInfty`) and the kernel-finiteness / `FiniteDimensional` instance
hypotheses *derived*.  Residuals: `h_pb`, `hsep`, `hdeg`, `hgcomm`, `h_normal`, `hdesc`, and the
`[deg β]` basepoint `hν` (`MulByIntBasepoint`). -/
noncomputable def dualGaloisData_of_separable_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (hgcomm : WeilPairing.MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback))
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f)) :
    EC.Isogeny.DualGaloisData φ :=
  -- the full kernel-translation covariance, from the single generic-point leaf
  have hcov : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z => WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β hgcomm k z
  -- the cardinality match `#ker β = deg β` (Silverman III.4.10c)
  have h_card : Nat.card β.kernel = β.degree :=
    card_kernel_eq_degree_of_separable_concrete W β hsep hcov h_normal hdesc
  -- Lagrange: `ker β ⊆ ker [deg β]`
  have hdvd : ∀ k ∈ β.kernel, (β.degree : ℤ) • k = 0 := by
    haveI : Finite β.kernel := finite_kernel_of_hcov W β hcov
    exact fun k hk => kernel_nsmul_degree_eq_zero β h_card hk
  dualGaloisData_of_basic_witnesses_general W φ β h_pb
    (mulByInt W.toAffine (β.degree : ℤ)).pullback
    (xy_family_of_genericPointCommutes W β hgcomm)
    h_card
    (hnu_mulByInt_general W β (β.degree : ℤ) (by exact_mod_cast hdeg) hdvd)
    hν

/-! ### The `K̄` capstone: the dual from the covariance engine -/

section AlgClosed

variable [IsAlgClosed F]

/-- **`DualGaloisData φ` from the cofinite pullback-evaluation witness over `K̄`** (Silverman
III.4.10–4.11, III.6.1).  The generic-point leaf `hgcomm` is *discharged* by the covariance
engine `mapTranslateGenericPoint_of_pullbackEvaluation`; everything else as in
`dualGaloisData_of_separable_general`.  Residuals: `h_pb`, `hsep`, `hdeg`, the
pullback-evaluation witness, `h_normal`, `hdesc`, `hν`. -/
noncomputable def dualGaloisData_of_pullbackEvaluation
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad)
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f)) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_separable_general W φ β h_pb hsep hdeg
    (WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw)
    h_normal hdesc hν

/-- **`DualGaloisData φ` for a separable isogeny with a `CoordHom` over `K̄`** (the capstone):
the pullback-evaluation witness holds with `bad = ∅` (`pullbackEvaluation_of_coordHom`).
Residuals: `h_pb`, `h_hom`, `hsep`, `hdeg`, `h_normal`, `hdesc`, `hν`. -/
noncomputable def dualGaloisData_of_coordHom
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φ.toPointMap cd P)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f)) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_pullbackEvaluation W φ β h_pb hsep hdeg Set.finite_empty
    (WeilPairing.pullbackEvaluation_of_coordHom W φ cd β h_pb h_hom) h_normal hdesc hν

/-- **`exists_dual` from the pullback-evaluation witness over `K̄`** (Silverman III.6.1): a
separable isogeny with the cofinite pullback-evaluation witness admits a reverse isogeny. -/
theorem exists_dual_of_pullbackEvaluation
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad)
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f)) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_pullbackEvaluation W φ β h_pb hsep hdeg hbad hw h_normal hdesc hν))

/-- **`exists_dual` for a separable isogeny with a `CoordHom` over `K̄`** (Silverman III.6.1
capstone). -/
theorem exists_dual_of_coordHom
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φ.toPointMap cd P)
    (hsep : β.IsSeparable) (hdeg : β.degree ≠ 0)
    (h_normal : letI := β.toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W)
    (hν : ∀ f : W.toAffine.FunctionField,
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
          ((mulByInt W.toAffine (β.degree : ℤ)).pullback f)) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_coordHom W φ cd β h_pb h_hom hsep hdeg h_normal hdesc hν))

/-! ### The concrete `[ℓ]` dual instance (Silverman III.6.1 for `φ = [ℓ]`) -/

/-- **`DualGaloisData` for `φ = [ℓ]` with every witness a theorem** (over `K̄`,
`(ℓ : F) ≠ 0`): `h_pb` is definitional, `hsep` is the `ω`-coefficient criterion
(`HasseWeil.mulByInt_isSeparable`, `RouteBGeneral.lean`), `hdeg` is `mulByInt_degree_ne_zero`,
`hgcomm` is the division-polynomial covariance `mapTranslateGenericPoint_mulByInt`
converted to the canonical action, `h_normal`/`hdesc` are the
`TorsionKernelRational` Galois witnesses, and `hν` is the `MulByIntBasepoint`
theorem (`hν_mulByInt`, at `N = deg [ℓ] = ℓ²`). -/
noncomputable def dualGaloisData_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    EC.Isogeny.DualGaloisData (EC.Isogeny.mulByInt W.toAffine hℓ) :=
  dualGaloisData_of_separable_general W (EC.Isogeny.mulByInt W.toAffine hℓ)
    (mulByInt W.toAffine ℓ)
    ((dif_neg hℓ : (mulByInt W.toAffine ℓ).pullback =
        mulByInt_pullbackAlgHom W ℓ hℓ).symm)
    (mulByInt_isSeparable W ℓ hℓF)
    (mulByInt_degree_ne_zero W.toAffine hℓ)
    (WeilPairing.mapTranslateGenericPoint_canonical_of_genuine W
      (mulByInt W.toAffine ℓ)
      (mulByInt_isGenuineWith_general W ℓ hℓ)
      (WeilPairing.mapTranslateGenericPoint_mulByInt W ℓ))
    (h_normal_mulByInt W ℓ hℓ)
    (hdesc_mulByInt W ℓ hℓ)
    (hν_mulByInt W ((mulByInt W.toAffine ℓ).degree : ℤ)
      (by exact_mod_cast mulByInt_degree_ne_zero W.toAffine hℓ))

/-- **The dual of `[ℓ]` as a concrete `EC.Isogeny`** (Silverman III.6.1, the first
fully-witnessed dual instance): every `DualGaloisData` field is now a theorem,
so the reverse isogeny exists with no carried hypotheses beyond
`ℓ ≠ 0`, `(ℓ : F) ≠ 0`, and `[IsAlgClosed F]`. -/
noncomputable def dualMulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    EC.Isogeny W.toAffine W.toAffine :=
  (EC.Isogeny.mulByInt W.toAffine hℓ).dual
    (EC.Isogeny.hasDualWitness_of_galoisData (dualGaloisData_mulByInt W ℓ hℓ hℓF))

omit [DecidableEq F] in
/-- **`exists_dual` for `[ℓ]`** — the first concrete dual instance with all Galois
witnesses discharged (`hν` was the last carried residual; it is now
`EC.mulByIntBasepoint_holds`). -/
theorem exists_dual_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) := by
  classical
  exact ⟨dualMulByInt W ℓ hℓ hℓF⟩

end AlgClosed

end HasseWeil
