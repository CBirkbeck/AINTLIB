/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.YOneAtlasClassify

/-!
# The marked Tate point and `Y₁(N)` (STREAM-Y1 cap file)

The cap of the `Y₁(N)` tower (T-E7): the classified marked point of the Tate atlas and
everything downstream of it — the `Y₁(N)` locus, its `Ell/R` object, the D-track
(`factors_yOne_iff`, `isNaiveGammaOne_pullSection_iff`, `yOne_representableBy`), the
E-track smoothness/affineness skeletons, and the T-E7 MASTER bridge
`gammaOneNaive_representable_assembly`.

**Why this file exists (v10.117 restructure, v10.111 relocation doctrine)**: the
`exists_tatePoint` classifying clause is proven in `YOneAtlasClassify.lean`
(`MarkedChartData.tateMarkedPoint_classifies`, PR #5225), which imports `YOneAssembly` —
so the filled theorem and its `tatePoint`-dependent consumers live HERE, downstream of
both.  Every declaration is statement-byte-identical to its former site in
`YOneAssembly.lean` (pointer comments left in place); `exists_tatePoint`'s former
`sorry` is DISCHARGED by the relocation, not deferred.

Axiom trail: `sorryAx` enters exactly through the designed **[T-A6b]**
(`abelEnrichment_exists`) and **[T-B6′]** (`geomFibrePointAddEquiv.map_add'`) trails,
plus the still-sorried E-track leaves of this file (each carrying its own leaf label).
-/

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- **(Y1-B2 = L-ATLAS, the master atlas leaf — Loeffler Cor 3.3.5 at scheme level)** There is a
marked point `P₀ = (0, 0)` of the universal Tate curve such that `(𝒴, E(A,B), P₀)` classifies:
`P₀` is nowhere of order `≤ 3`, and every pair `(E/T, P)` in `Ell/R` with `P` nowhere of order
`≤ 3` arises from a **unique** `Ell/R`-morphism to the atlas by pulling back `P₀`.

Loeffler Cor 3.3.5 (verbatim, p. 14): *"The pair `(Spec ℤ[A, B, ∆(A, B)⁻¹], E(A, B), (0:0:1))`
represents the functor … `S ↦ {eq. classes of pairs (E, P), E/S elliptic curve, P ∈ E(S) not of
order 1, 2, 3 in any fibre}`"*; existence/uniqueness from Prop 3.3.4, whose general case glues
chart classifications (verbatim, p. 14): *"there exists an affine covering `S = ⋃ᵢ Uᵢ`, such
that `E|_{Uᵢ}` has a Weierstrass equation over `Γ(Uᵢ, O_S)` … Since `αᵢ, βᵢ` are unique, they
must agree on `Uᵢ ∩ Uⱼ`. The sheaf property of `O_S` then implies that there exist
`α, β ∈ Γ(S, O_S)` … Then `(E, P) ≅ (E(α, β), (0, 0))`"* — "local uniqueness gives global
existence".

Proven: the witness is `tateMarkedPoint` with its `[Y1-vi]` order property; the classifying
∀-clause is `MarkedChartData.tateMarkedPoint_classifies` ([Y1-ATLAS], YOneAtlasClassify.lean):
per-chart T-E1 classification, sheaf gluing of the base and top maps over the chart cover, and
T7 uniqueness through the induced-chart comparison ENGINE. Inherited `sorryAx` enters exactly
through the designed trails **[T-A6b]** (`abelEnrichment_exists`) and **[T-B6′]**
(`geomFibrePointAddEquiv.map_add'`). -/
theorem exists_tatePoint :
    ∃ P₀ : (tateUniversal R).Section,
      (tateUniversal R).NowhereGeomOrderLEThree P₀ ∧
      ∀ (Y : EllObj R) (P : Y.curve.Section), Y.curve.NowhereGeomOrderLEThree P →
        ∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P :=
  -- Witness = `P₀ = (0,0)` (`tateMarkedPoint`); first conjunct is the [Y1-vi] leaf; the
  -- classifying ∀-clause is the [Y1-ATLAS] deliverable `tateMarkedPoint_classifies`
  -- (YOneAtlasClassify.lean, Loeffler Prop 3.3.4's general case).
  ⟨tateMarkedPoint R, tateMarkedPoint_nowhereGeomOrderLEThree R,
    fun Y P hP => MarkedChartData.tateMarkedPoint_classifies R Y P hP⟩

/-- The marked point `(0, 0)` of the universal Tate curve (Loeffler's `(0 : 0 : 1)`), extracted
from the master atlas leaf. Downstream consumers use only `tatePoint_nowhereGeomOrderLEThree`
and `tatePoint_classifies`. -/
noncomputable def tatePoint : (tateUniversal R).Section :=
  (exists_tatePoint R).choose

/-- **Opaque interface**: the marked point is nowhere of order `≤ 3` (Loeffler p. 13, the
display after Def 3.3.3: *"so `P` does not have order 1, 2 or 3 in any fibre"*). -/
theorem tatePoint_nowhereGeomOrderLEThree :
    (tateUniversal R).NowhereGeomOrderLEThree (tatePoint R) :=
  (exists_tatePoint R).choose_spec.1

/-- **Opaque interface**: the classifying universal property of the marked atlas
(Loeffler Cor 3.3.5). -/
theorem tatePoint_classifies :
    ∀ (Y : EllObj R) (P : Y.curve.Section), Y.curve.NowhereGeomOrderLEThree P →
      ∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f (tatePoint R) = P :=
  (exists_tatePoint R).choose_spec.2

variable (N : ℕ)

/-- The underlying set of `Y₁(N)` inside `Y_N`: the complement of the (finitely many) lower
killed loci `Y_d`, `d ∣ N`, `4 ≤ d < N` — Loeffler's `Y_N − ⋃_{d|N, 4≤d<N} Y_d` (Def 3.3.6,
p. 14) with his exact index set (divisors `d ≤ 3` need no removal: the atlas already has no
order-`≤ 3` points, Cor 3.3.5). -/
def yOneSet : Set ((tateUniversal R).killedLocus (tatePoint R) N) :=
  (⋃ d ∈ N.properDivisors.filter (fun d => 4 ≤ d),
    ((tateUniversal R).killedLocusπ (tatePoint R) N).base ⁻¹'
      Set.range ((tateUniversal R).killedLocusπ (tatePoint R) d).base)ᶜ

/-- **(Y1-C5)** `Y₁(N)` is open in `Y_N`: each removed `Y_d` has closed image (closed
immersion), the union is finite, and we take the complement of its preimage. -/
theorem yOneSet_isOpen : IsOpen (yOneSet R N) := by
  rw [yOneSet, isOpen_compl_iff]
  refine isClosed_biUnion_finset fun d _ => ?_
  refine IsClosed.preimage ((tateUniversal R).killedLocusπ (tatePoint R) N).continuous ?_
  exact ((tateUniversal R).killedLocusπ_isClosedImmersion (tatePoint R) d)
    |>.isClosedEmbedding.isClosed_range

/-- `Y₁(N)` as an open subscheme of the killed locus `Y_N` (Loeffler Def 3.3.6). -/
noncomputable def yOneOpens : ((tateUniversal R).killedLocus (tatePoint R) N).Opens :=
  ⟨yOneSet R N, yOneSet_isOpen R N⟩

/-- **The scheme `Y₁(N)` over `R`** (Loeffler Def 3.3.6: for `R = ℤ[1/N]` this is
`Y₁(N)_{ℤ[1/N]}`; general `R` with `N` invertible is the same construction over `R`).
Reducible so `yOne R N` unifies with `↑(yOneOpens R N)` (the open-immersion domain) without a
`whnf`, mirroring `@[reducible] tateBase` (v10.72(b)). -/
@[reducible] noncomputable def yOne : Scheme.{u} :=
  (yOneOpens R N).toScheme

/-- The locally closed inclusion `Y₁(N) ⟶ 𝒴` into the Tate atlas: open into `Y_N`, closed
into `𝒴`. -/
noncomputable def yOneBase : yOne R N ⟶ tateBase R :=
  (yOneOpens R N).ι ≫ (tateUniversal R).killedLocusπ (tatePoint R) N

/-- The structure morphism `Y₁(N) ⟶ Spec R`. -/
noncomputable def yOneStructMap : yOne R N ⟶ Spec R :=
  yOneBase R N ≫ tateStructMap R

/-- `Y₁(N)` with its universal elliptic curve, as an object of `Ell/R` — Loeffler's Remark
after Def 3.3.6 (verbatim, pp. 14–15): *"`Y₁(N)_{ℤ[1/N]}` has a universal elliptic curve over
it by restricting `E(α, β)/Y`, and this has a point `(0,0)`. The triple (`Y₁(N)_{ℤ[1/N]}`,
this curve, this point) represents the above functor."* The curve is the base change of the
universal Tate curve along `Y₁(N) ⟶ 𝒴`. -/
noncomputable def yOneEllObj : EllObj R where
  base := yOne R N
  structMap := yOneStructMap R N
  curve := (tateUniversal R).baseChange (yOneBase R N)

/-! ### D. Representability (Loeffler Def 3.3.6: "By construction, this represents the functor") -/

/-- **(Y1-D1, open-factoring split)** A morphism `t : T ⟶ 𝒴` factors through `Y₁(N)` iff it
factors through the closed `Y_N` by a morphism whose topological image lands in the open
`yOneSet`. Forward: precompose with the open immersion `yOneOpens.ι` (its range is `yOneSet`);
backward: `IsOpenImmersion.lift`. -/
theorem factors_yOne_iff_exists_range {T : Scheme.{u}} (t : T ⟶ tateBase R) :
    (∃ h : T ⟶ yOne R N, h ≫ yOneBase R N = t) ↔
      ∃ g : T ⟶ (tateUniversal R).killedLocus (tatePoint R) N,
        g ≫ (tateUniversal R).killedLocusπ (tatePoint R) N = t ∧
          Set.range g.base ⊆ yOneSet R N := by
  have hr : Set.range (yOneOpens R N).ι.base = yOneSet R N := Scheme.Opens.range_ι _
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h ≫ (yOneOpens R N).ι, ?_, ?_⟩
    · rw [Category.assoc]; exact hh
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans hr.le
  · rintro ⟨g, hg, hrange⟩
    refine ⟨IsOpenImmersion.lift (yOneOpens R N).ι g (hr ▸ hrange), ?_⟩
    show IsOpenImmersion.lift (yOneOpens R N).ι g (hr ▸ hrange) ≫
      ((yOneOpens R N).ι ≫ (tateUniversal R).killedLocusπ (tatePoint R) N) = t
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hg

/-- **(Y1-D1, the locus ↔ functor comparison — the "by construction" core)** A morphism
`t : T ⟶ 𝒴` factors through `Y₁(N)` iff the pulled-back marked point is a naive `Γ₁(N)`
structure on the pulled-back Tate curve. Factoring through the closed `Y_N` is the global
killing clause (`killedLocus_spec`); avoiding the removed sets is, fibrewise, "no proper
multiple `d • P` with `d ∣ N`, `4 ≤ d < N` vanishes" (`mem_killedLocus_range_iff` +
`pull_smul_eq_zero_iff_residue`), which together with `exists_properDivisor_smul_eq_zero`
(divisors) and `tatePoint_nowhereGeomOrderLEThree` (the `d ≤ 3` cases) is exactly the
fibrewise clause of `IsNaiveGammaOne`. The factoring `h` is unique (`yOneBase` is a
monomorphism). Loeffler Def 3.3.6 (verbatim, p. 14): *"By construction, this represents the
functor `S ↦ {elliptic curves E/S with point of exact order N}` on the category of
`ℤ[1/N]`-schemes."* -/
theorem factors_yOne_iff [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    {T : Scheme.{u}} (t : T ⟶ tateBase R) :
    (∃ h : T ⟶ yOne R N, h ≫ yOneBase R N = t) ↔
      ((tateUniversal R).baseChange t).IsNaiveGammaOne N
        (EllipticCurve.Point.asSection (tateUniversal R) t
          (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R))) := by
  rw [factors_yOne_iff_exists_range]
  constructor
  · rintro ⟨g, hg, hrange⟩
    have hkill : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R) = 0 :=
      ((tateUniversal R).killedLocus_spec (tatePoint R) N t).mp ⟨g, hg⟩
    have hc1 : (N : ℤ) • EllipticCurve.Point.asSection (tateUniversal R) t
        (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R)) = 0 :=
      ((tateUniversal R).zsmul_asSection_pull_eq_zero_iff (tatePoint R) t (N : ℤ)).mpr hkill
    refine ⟨hc1, fun k _ _ τ => ⟨?_, ?_⟩⟩
    · -- clause 2a: the fibrewise `N`-kill is the section `N`-kill pulled along `τ`
      rw [← EllipticCurve.Point.pull_zsmul, hc1, EllipticCurve.Point.pull_zero]
    · -- clause 2b: no proper multiple `a < N` kills the fibre
      intro a ha0 haN hbad
      rw [(tateUniversal R).zsmul_pull_baseChange_asSection_iff (tatePoint R) t τ] at hbad
      have hkillτ : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) (τ ≫ t) (tatePoint R)
          = 0 := by
        rw [(tateUniversal R).smul_eq_zero_iff_comp_mulByHom (τ ≫ t) N]
        have hk := ((tateUniversal R).smul_eq_zero_iff_comp_mulByHom t N
          (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R))).mp hkill
        have h1 : (EllipticCurve.Point.pull (tateUniversal R) (τ ≫ t) (tatePoint R)).1
            = τ ≫ (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R)).1 := by
          show (τ ≫ t) ≫ (tatePoint R).1 = τ ≫ t ≫ (tatePoint R).1
          rw [Category.assoc]
        rw [h1, Category.assoc, hk, Category.assoc]
      obtain ⟨d, hdmem, hd0, hdkill⟩ :=
        exists_properDivisor_smul_eq_zero hkillτ ha0 haN hbad
      rw [Nat.mem_properDivisors] at hdmem
      by_cases hd3 : d ≤ 3
      · exact tatePoint_nowhereGeomOrderLEThree R k (τ ≫ t) d hd0 hd3 hdkill
      · push_neg at hd3
        set cp := IsLocalRing.closedPoint k with hcp
        have hxres : (d : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
            ((tateBase R).fromSpecResidueField ((τ ≫ t).base cp)) (tatePoint R) = 0 :=
          ((tateUniversal R).pull_smul_eq_zero_iff_residue (tatePoint R) (d : ℤ) (τ ≫ t)
            ((τ ≫ t).base cp) ⟨cp, rfl⟩).mp hdkill
        have hxmem : (τ ≫ t).base cp ∈
            Set.range ((tateUniversal R).killedLocusπ (tatePoint R) d).base :=
          ((tateUniversal R).mem_killedLocus_range_iff (tatePoint R) d ((τ ≫ t).base cp)).mpr hxres
        have hy : g.base (τ.base cp) ∈ yOneSet R N := hrange ⟨τ.base cp, rfl⟩
        rw [yOneSet, Set.mem_compl_iff, Set.mem_iUnion₂] at hy
        push_neg at hy
        refine hy d (by rw [Finset.mem_filter, Nat.mem_properDivisors]
                        exact ⟨⟨hdmem.1, hdmem.2⟩, hd3⟩) ?_
        have hgt : ((tateUniversal R).killedLocusπ (tatePoint R) N).base (g.base (τ.base cp))
            = (τ ≫ t).base cp := by
          rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
        rw [Set.mem_preimage, hgt]
        exact hxmem
  · rintro ⟨hc1, hfib⟩
    have hkill : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R) = 0 :=
      ((tateUniversal R).zsmul_asSection_pull_eq_zero_iff (tatePoint R) t (N : ℤ)).mp hc1
    obtain ⟨g, hg⟩ := ((tateUniversal R).killedLocus_spec (tatePoint R) N t).mpr hkill
    refine ⟨g, hg, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [yOneSet, Set.mem_compl_iff, Set.mem_iUnion₂]
    rintro ⟨d, hd_filter, hmem⟩
    rw [Set.mem_preimage] at hmem
    rw [Finset.mem_filter, Nat.mem_properDivisors] at hd_filter
    obtain ⟨⟨hdN, hdlt⟩, hd4⟩ := hd_filter
    have hgtx : ((tateUniversal R).killedLocusπ (tatePoint R) N).base (g.base x) = t.base x := by
      rw [← Scheme.Hom.comp_apply, hg]
    rw [hgtx] at hmem
    have hres : (d : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
        ((tateBase R).fromSpecResidueField (t.base x)) (tatePoint R) = 0 :=
      ((tateUniversal R).mem_killedLocus_range_iff (tatePoint R) d (t.base x)).mp hmem
    set k := AlgebraicClosure (T.residueField x) with hk
    haveI : Subsingleton (Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    set τ : Spec (CommRingCat.of k) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) k)) ≫ T.fromSpecResidueField x
      with hτ
    have himg : (τ ≫ t).base (IsLocalRing.closedPoint k) = t.base x := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      rw [hτ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    have hτkill : (d : ℤ) • EllipticCurve.Point.pull (tateUniversal R) (τ ≫ t) (tatePoint R) = 0 := by
      rw [(tateUniversal R).pull_smul_eq_zero_iff_residue (tatePoint R) (d : ℤ) (τ ≫ t)
        ((τ ≫ t).base (IsLocalRing.closedPoint k)) ⟨IsLocalRing.closedPoint k, rfl⟩, himg]
      exact hres
    have hne := (hfib k τ).2 d (by omega) hdlt
    exact hne (((tateUniversal R).zsmul_pull_baseChange_asSection_iff (tatePoint R) t τ (d : ℤ)).mpr
      hτkill)

/-- **(Y1-D2 bridge)** A pulled section vanishes on the fibre over `τ` iff its `transportSection`
(along the `Ell/R`-morphism's cartesian comparison iso `curveIsoPullback`) does — pure
iso-cancellation on the total spaces (`curveIsoPullback` is an iso, hence mono). This is the
"barehanded" fibrewise transport of the wiring note. -/
private lemma pull_transportSection_eq_zero_iff {X Y : EllObj R} (f : X ⟶ Y) {k : Type u} [Field k]
    (τ : Spec (CommRingCat.of k) ⟶ X.base) (w : X.curve.Section) :
    EllipticCurve.Point.pull X.curve τ w = 0 ↔
      EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) τ (EllHom.transportSection R f w) = 0 := by
  -- `iso.hom`'s codomain is inferred as `(baseChange).E` from these equations, matching
  -- `zero_curveIsoPullback` (avoiding the `pullback … = (baseChange).E` syntactic mismatch).
  have key : (EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) τ
        (EllHom.transportSection R f w)).1
      = (EllipticCurve.Point.pull X.curve τ w).1 ≫ (EllHom.curveIsoPullback R f).hom :=
    (Category.assoc _ _ _).symm
  have keyzero : (0 : (Y.curve.baseChange f.baseHom).Point τ).1
      = (0 : X.curve.Point τ).1 ≫ (EllHom.curveIsoPullback R f).hom := by
    rw [EllipticCurve.point_zero_val, EllipticCurve.point_zero_val, Category.assoc]
    exact congrArg (τ ≫ ·) (EllHom.zero_curveIsoPullback R f).symm
  rw [Subtype.ext_iff, Subtype.ext_iff, key, keyzero]
  exact (CategoryTheory.cancel_mono (EllHom.curveIsoPullback R f).hom).symm

/-- **(Y1-D2, naive-structure transport along `Ell/R`-morphisms)** For an `Ell/R`-morphism
`f : X ⟶ Y` and a section `Q` of `Y.curve`, the pulled section `pullSection f Q` is naive-`Γ₁(N)`
on `X.curve` iff the pulled *point* is naive-`Γ₁(N)` on the base-changed curve
`Y.curve ×_{Y.base} X.base`. The cartesian square of `f` identifies the two curves pointedly;
the group-compatibility of that identification is the GME 2.2.5 canonicity chain — the same
**[T-E4-family]** machinery as `EllHom.pullSection_add` and the membership sorry inside
`gammaOneNaiveProblem.map` (held file), with which the discharge must be coordinated (prove
once, consume twice). -/
theorem isNaiveGammaOne_pullSection_iff [NeZero N] {X Y : EllObj R} (f : X ⟶ Y)
    (Q : Y.curve.Section) :
    X.curve.IsNaiveGammaOne N (EllHom.pullSection R f Q) ↔
      (Y.curve.baseChange f.baseHom).IsNaiveGammaOne N
        (EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom Q)) := by
  -- `transportSection` (along `f`'s cartesian comparison iso) as an additive hom — additivity is
  -- A's `T-E4-family` primitive (`transportSection_add_of_finitePresentation`), the "prove once".
  set Φ : X.curve.Section →+ (Y.curve.baseChange f.baseHom).Section :=
    AddMonoidHom.mk' (EllHom.transportSection R f)
      (EllHom.transportSection_add_of_finitePresentation R f) with hΦ
  have hinj : Function.Injective Φ := EllHom.transportSection_injective R f
  have hΦ0 : ∀ y, Φ y = 0 ↔ y = 0 := fun y => by rw [← map_zero Φ]; exact hinj.eq_iff
  -- dictionary: the transport of the pulled section IS the base-changed pulled point-section.
  have hdict : Φ (EllHom.pullSection R f Q)
      = EllipticCurve.Point.asSection Y.curve f.baseHom (EllipticCurve.Point.pull Y.curve f.baseHom Q) := by
    refine Subtype.ext ?_
    show (EllHom.transportSection R f (EllHom.pullSection R f Q)).1 = _
    rw [EllHom.transportSection_pullSection]
    rfl
  -- section-level killing transports through the injective additive hom.
  have killing_iff : ((N : ℤ) • EllHom.pullSection R f Q = 0) ↔
      ((N : ℤ) • EllipticCurve.Point.asSection Y.curve f.baseHom
        (EllipticCurve.Point.pull Y.curve f.baseHom Q) = 0) := by
    rw [← hdict, ← map_zsmul Φ, hΦ0]
  -- fibrewise, any integer scalar: pull ∘ (a • ·) then iso-cancel (`pull_transportSection_eq_zero_iff`).
  have hbridge : ∀ (a : ℤ) {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ X.base),
      (a • EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f Q) = 0 ↔
        a • EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) t
          (EllipticCurve.Point.asSection Y.curve f.baseHom
            (EllipticCurve.Point.pull Y.curve f.baseHom Q)) = 0) := by
    intro a k _ t
    rw [← EllipticCurve.Point.pull_zsmul, ← EllipticCurve.Point.pull_zsmul,
      pull_transportSection_eq_zero_iff (R := R) (f := f) (τ := t)
        (w := a • EllHom.pullSection R f Q),
      show EllHom.transportSection R f (a • EllHom.pullSection R f Q)
        = a • Φ (EllHom.pullSection R f Q) from map_zsmul Φ a _, hdict]
  constructor
  · rintro ⟨hkill, hfib⟩
    refine ⟨killing_iff.mp hkill, ?_⟩
    intro k _ _ t
    exact ⟨(hbridge (N : ℤ) t).mp (hfib k t).1,
      fun a ha haN => (not_congr (hbridge (a : ℤ) t)).mp ((hfib k t).2 a ha haN)⟩
  · rintro ⟨hkill, hfib⟩
    refine ⟨killing_iff.mpr hkill, ?_⟩
    intro k _ _ t
    exact ⟨(hbridge (N : ℤ) t).mpr (hfib k t).1,
      fun a ha haN => (not_congr (hbridge (a : ℤ) t)).mpr ((hfib k t).2 a ha haN)⟩

/-- **(Y1-D3 — Loeffler Def 3.3.6, representability half of T-E7)** `(Y₁(N), universal curve,
(0,0))` represents the naive `Γ₁(N)` moduli problem: for every `Y : Ell/R`,
`Ell/R`-morphisms `Y ⟶ Y₁(N)-object` correspond to naive `Γ₁(N)` structures on `Y.curve`,
naturally. Assembly: forward `f ↦ pullSection f (marked point)` (membership by Y1-D2 + Y1-D1
reflexivity); backward via `tatePoint_classifies` (through Y1-A2, `N ≥ 4`) followed by the
`Y₁(N)` factorisation (Y1-D1, through Y1-D2); round-trips by the atlas uniqueness clause;
naturality by `EllHom.pullSection_comp` (proven, held file). -/
theorem yOne_representableBy [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    Nonempty ((gammaOneNaiveProblem R N).RepresentableBy (yOneEllObj R N)) := by
  classical
  haveI : IsClosedImmersion ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
    (tateUniversal R).killedLocusπ_isClosedImmersion (tatePoint R) N
  haveI : Mono (yOneBase R N) := by
    show Mono ((yOneOpens R N).ι ≫ (tateUniversal R).killedLocusπ (tatePoint R) N)
    infer_instance
  -- **The D2 + D1 bridge**: for `g : Y ⟶ 𝒴`, the pulled marked section is naive `Γ₁(N)` on
  -- `Y.curve` iff `g`'s base map factors through `Y₁(N)`.
  have bridge : ∀ {Y : EllObj R} (g : Y ⟶ tateEllObj R),
      Y.curve.IsNaiveGammaOne N (EllHom.pullSection R g (tatePoint R)) ↔
        ∃ h : Y.base ⟶ yOne R N, h ≫ yOneBase R N = g.baseHom := fun {Y} g =>
    (isNaiveGammaOne_pullSection_iff R N g (tatePoint R)).trans
      (factors_yOne_iff R N hN hinv g.baseHom).symm
  -- **`e2`**: pairs `(g, factorisation)` ≃ naive `Γ₁(N)` sections, via the atlas classifier
  -- (`tatePoint_classifies`); bijective by classifier-uniqueness (+ `yOneBase` mono) and the
  -- two existentials. `Equiv.ofBijective` supplies the round-trip laws.
  let e2 : ∀ X : EllObj R,
      {p : (X ⟶ tateEllObj R) × (X.base ⟶ yOne R N) // p.2 ≫ yOneBase R N = p.1.baseHom} ≃
        {P : X.curve.Section // X.curve.IsNaiveGammaOne N P} := fun X =>
    Equiv.ofBijective
      (fun p => ⟨EllHom.pullSection R p.1.1 (tatePoint R), (bridge p.1.1).mpr ⟨p.1.2, p.2⟩⟩)
      ⟨fun p₁ p₂ hp => by
          obtain ⟨⟨g₁, h₁⟩, hgh₁⟩ := p₁
          obtain ⟨⟨g₂, h₂⟩, hgh₂⟩ := p₂
          simp only [Subtype.mk.injEq] at hp
          have hcl := tatePoint_classifies R X (EllHom.pullSection R g₁ (tatePoint R))
            (((bridge g₁).mpr ⟨h₁, hgh₁⟩).nowhereGeomOrderLEThree hN)
          have hg : g₁ = g₂ := hcl.unique rfl hp.symm
          have hh : h₁ = h₂ := by
            apply (cancel_mono (yOneBase R N)).mp
            rw [hgh₁, hgh₂, hg]
          subst hg; subst hh; rfl,
        fun P => by
          obtain ⟨P, hP⟩ := P
          obtain ⟨g, hg, -⟩ := tatePoint_classifies R X P (hP.nowhereGeomOrderLEThree hN)
          obtain ⟨h, hh⟩ := (bridge g).mp (by rw [hg]; exact hP)
          exact ⟨⟨(g, h), hh⟩, Subtype.ext hg⟩⟩
  refine ⟨{ homEquiv := fun {X} =>
              (EllObj.homPullbackAlongEquiv (tateEllObj R) (yOneBase R N) X).trans (e2 X)
            homEquiv_comp := fun {X X'} f v => ?_ }⟩
  refine Subtype.ext ?_
  show EllHom.pullSection R ((f ≫ v) ≫ (tateEllObj R).pullbackAlongπ (yOneBase R N)) (tatePoint R)
    = EllHom.pullSection R f
        (EllHom.pullSection R (v ≫ (tateEllObj R).pullbackAlongπ (yOneBase R N)) (tatePoint R))
  rw [Category.assoc, EllHom.pullSection_comp]

/-! ### E. Geometry of `Y₁(N)`: affine and smooth (Loeffler Thm 3.4.4, p. 15)

Loeffler Thm 3.4.4 (verbatim, p. 15): *"`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."* Proof
(verbatim): *"Let `A` be a local `ℤ[1/N]`–algebra, and let `I ⊂ A` be nilpotent. Let
`(E₀, P₀) ∈ Y₁(N)(A₀)`. The ring `A₀` is local, so `E₀` has a Weierstrass equation over
`Spec(A₀)`. Lift coefficients arbitrarily to `A` to get `E/A` lifting `E₀`; note that
`∆(E) ∈ Aˣ` since its image in `A₀` is in `A₀ˣ`. Can we lift `P₀` to an `N`-torsion point of
`E`, i.e. is `E[N]` smooth? Yes, since `[N] : E → E` is smooth, and a composition of smooth
morphisms is smooth. (We apply this to `[N]` composed with the structure map `E → Spec A`.)
Hence `(E₀, P₀)` lifts to `(E, P)`, and we are done."*

The étale input is Loeffler Lemma 3.4.2(2) (verbatim, p. 15): *"The morphism `[N]` multiplies
a global differential by `N`, so it induces an isomorphism of tangent space. In other words,
it is an étale morphism"* — in this repo that is exactly **[BB-DIFF]** (`torsionπ_etale`,
gated on `mulByHom_formallyUnramified'`, in flight). The same étale input makes the removed
loci **clopen** in `Y_N` (a section of an étale separated morphism is an open immersion), which
is what makes `Y₁(N)` affine for general `N` — Loeffler's `Spec` display is verbatim only for
`N = 5` (Def 3.3.6), so affineness is derived, not quoted (KM affine-over-`(Ell)` locator to be
attached when the KM text lands; the board's QUOTE-PARTIAL note). -/

/-- **(Y1-E1, the clopen split — gate [BB-DIFF])** Over a base where `N` is invertible, each
sub-killed-locus `{d • P = 0}` with `d ∣ N` is **open** inside the killed locus `{N • P = 0}`
(as well as closed): on `Y_N` the point `P` classifies into the finite étale `E[N]`
(`torsionπ_etale`, T-B5′ — Loeffler Lemma 3.4.2(2)), the zero section of an étale separated
family is an open immersion (its diagonal is; mathlib `FormallyUnramified` +
`IsOpenImmersion (pullback.diagonal _)`), and `{d • P = 0}` is the preimage of it under the
`d`-multiple classifying section. -/
theorem killedLocus_preimage_isOpen {S : Scheme.{u}} (E : EllipticCurve S) (P : E.Section)
    [NeZero N] (hN : NIsInvertible S N) {d : ℕ} (hd : d ∣ N) :
    IsOpen ((E.killedLocusπ P N).base ⁻¹' Set.range (E.killedLocusπ P d).base) := by
  sorry

/-- **(Y1-E2 — affineness, gate [BB-DIFF] via Y1-E1)** `Y₁(N)` is affine: by Y1-E1 the removed
locus is clopen in `Y_N`, so `Y₁(N)` is a *clopen* subscheme of the closed subscheme
`Y_N ⊆ 𝒴 = Spec R[A,B][∆⁻¹]`; a clopen subset of an affine scheme is the basic open of an
idempotent (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`), hence affine.
(Derived — Loeffler displays `Spec` only for `N = 5`; see section header.) -/
theorem yOne_isAffine [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    IsAffine (yOne R N) := by sorry

/-- **(Y1-E3)** The structure morphism of `Y₁(N)` is an affine morphism — source affine
(Y1-E2) and target `Spec R` affine (`HasAffineProperty @IsAffineHom`). -/
theorem yOneStructMap_isAffineHom [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    IsAffineHom (yOneStructMap R N) := by sorry

/-- **(Y1-E4 — finite presentation)** `Y₁(N) ⟶ Spec R` is locally of finite presentation: the
atlas ring is a localized polynomial ring; the zero section of the (smooth, separated,
finitely presented) universal curve is a finitely presented closed immersion
(`FinitePresentationCancel`, Stacks 01TX — the T-B pattern of
`mulByHom_locallyOfFinitePresentation`), so its pullback `Y_N ⟶ 𝒴` is; and `Y₁(N) ⟶ Y_N`
is an open immersion. Loeffler Prop 3.4.3 requires "of finite type … `R` noetherian" — over
general `R` finite *presentation* is the right form, and it is what mathlib's
`RingHom.Smooth` consumes. -/
theorem yOneStructMap_locallyOfFinitePresentation [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    LocallyOfFinitePresentation (yOneStructMap R N) := by
  -- The zero section is lfp: `zero ≫ π = 𝟙` is lfp and `π` is (smooth ⟹) of finite type.
  haveI hsm : Smooth (tateUniversal R).π := SmoothOfRelativeDimension.smooth (n := 1) _
  haveI hzero : LocallyOfFinitePresentation (tateUniversal R).zero := by
    have h : LocallyOfFinitePresentation ((tateUniversal R).zero ≫ (tateUniversal R).π) := by
      rw [(tateUniversal R).zero_π]; infer_instance
    exact LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h inferInstance
  -- `Y_N ⟶ 𝒴` is the base change of the zero section, hence lfp.
  haveI hkl : LocallyOfFinitePresentation ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
    MorphismProperty.pullback_fst _ _ hzero
  -- `Y₁(N) ⟶ Y_N` is an open immersion, hence lfp.
  haveI hι : LocallyOfFinitePresentation (yOneOpens R N).ι := inferInstance
  -- `𝒴 ⟶ Spec R` is `Spec` of `R → R[A,B] → R[A,B][Δ⁻¹]` — polynomial then localization away, fp.
  haveI hstr : LocallyOfFinitePresentation (tateStructMap R) := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    rw [CommRingCat.hom_ofHom]
    refine RingHom.FinitePresentation.comp ?_ ?_
    · rw [RingHom.finitePresentation_algebraMap]
      exact IsLocalization.Away.finitePresentation (tateCurveOver R).Δ
    · rw [← MvPolynomial.algebraMap_eq, RingHom.finitePresentation_algebraMap]
      infer_instance
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.comp_mem _ _ _ hι hkl) hstr

/-- **(Y1-E5, the infinitesimal lifting core — Loeffler Thm 3.4.4's proof body; gate
[BB-DIFF])** Points of `Y₁(N)` lift along nilpotent thickenings of affines over `R`:
given `f₀ : Spec (A/I) ⟶ Y₁(N)` over `Spec R` with `I` nilpotent, there is
`f : Spec A ⟶ Y₁(N)` over `Spec R` restricting to `f₀`.

Proof plan mirroring Loeffler (deviations adjudicated in the artifact, §E5): `f₀` classifies
`(E₀, P₀)` with `E₀` the Tate curve `E(α₀, β₀)` — representability replaces Loeffler's "`A₀`
is local, so `E₀` has a Weierstrass equation" (and lets the criterion run over *all*
square-zero test pairs, as mathlib's `Algebra.FormallySmooth` demands, not just local ones).
Lift `(α₀, β₀)` arbitrarily to `(α, β)` ("Lift coefficients arbitrarily to `A`"); `∆(α, β)`
is a unit since it is one mod the nilpotent `I` ("note that `∆(E) ∈ Aˣ`…"). Lift `P₀` through
the **étale affine** `E(α,β)[N] ∩ {affine chart} ⟶ Spec A` (Loeffler: "Can we lift `P₀` to an
`N`-torsion point of `E`, i.e. is `E[N]` smooth? Yes, since `[N] : E → E` is smooth" =
`torsionπ_etale` [BB-DIFF]; the chart intersection keeps the lifting ring-level —
`Algebra.FormallySmooth.lift` against the nilpotent `I`). The lifted `(E, P)` need not be
Tate-marked at `(0,0)`: re-normalise by **T-E1** `exists_unique_variableChange_isTateNormal`
(orders on fibres of `A` equal those on fibres of `A₀`); by T-E1 *uniqueness* over `A₀` the
correcting change reduces to the identity, so the corrected classifying map still lifts `f₀`.
Fibrewise exact order `N` persists (same fibres), so the corrected map lands in `Y₁(N)` by
`factors_yOne_iff`. -/
theorem yOne_infinitesimal_lifting [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    {A : Type u} [CommRing A] (φ : R ⟶ CommRingCat.of A) (I : Ideal A) (hI : IsNilpotent I)
    (f₀ : Spec (CommRingCat.of (A ⧸ I)) ⟶ yOne R N)
    (hf₀ : f₀ ≫ yOneStructMap R N =
      Spec.map (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ f : Spec (CommRingCat.of A) ⟶ yOne R N,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ f = f₀ ∧
      f ≫ yOneStructMap R N = Spec.map φ := by
  sorry

/-- **(Y1-E6 = Loeffler Thm 3.4.4, smoothness half of T-E7)** `Y₁(N) ⟶ Spec R` is smooth.
Loeffler (verbatim, p. 15): *"`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."* Assembly: `Y₁(N)`
is affine (Y1-E2) with finitely presented coordinate ring over `R` (Y1-E4); the lifting
(Y1-E5) rephrased through the Γ–Spec adjunction is `Algebra.FormallySmooth R Γ(Y₁(N))`
(mathlib quantifies over all square-zero pairs — Loeffler's Prop 3.4.3 "local `A`, `I`
nilpotent, `R` noetherian" is *upgraded*, soundly, because Y1-E5's proof never used locality;
artifact §E6). `FormallySmooth + FinitePresentation = Algebra.Smooth = RingHom.Smooth`, and
`HasRingHomProperty.Spec_iff` transports to the scheme morphism. -/
theorem yOneStructMap_smooth [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    Smooth (yOneStructMap R N) := by sorry

/-! ### F. Transport to arbitrary representing objects, and the T-E7 bridge -/

/-- **(Y1-F1)** Any object representing the naive `Γ₁(N)` problem has smooth affine structure
morphism: representing objects are unique up to isomorphism
(`Functor.RepresentableBy.uniqueUpToIso`), an isomorphism in `Ell/R` has an isomorphism of
bases compatible with the structure morphisms, and `Smooth`/`IsAffineHom` respect isomorphisms.
Instantiated at the explicit representative `yOneEllObj` with Y1-E6 + Y1-E3. -/
theorem representableBy_smooth_isAffineHom [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    (X : EllObj R) (hX : Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X)) :
    Smooth X.structMap ∧ IsAffineHom X.structMap := by sorry

/-- **(Y1-MASTER — the T-E7 bridge; statement identical to the held
`gammaOneNaive_representable`, `Moduli/Representability.lean:250`)** For `N ≥ 4` invertible in
`R`, the naive `Γ₁(N)` problem is representable (by `Y₁(N)` — Loeffler Def 3.3.6) and every
representing object is smooth and affine over `Spec R` (Loeffler Thm 3.4.4 + the clopen-split
affineness). Term-mode assembly from Y1-D3 and Y1-F1; no `sorry` of its own — discharging the
leaves above proves T-E7, and the held theorem can then be closed by `exact`. -/
theorem gammaOneNaive_representable_assembly [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) :=
  ⟨⟨⟨yOneEllObj R N, yOne_representableBy R N hN hinv⟩⟩,
    fun X hX => representableBy_smooth_isAffineHom R N hN hinv X hX⟩

end ModularCurves
