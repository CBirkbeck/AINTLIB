/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.MulByHomEtale
import ModularCurves.ForMathlib.SmoothSectionLift
import ModularCurves.ModularCurve.YFullRoute
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

Axiom trail (v10.152, CHARTER-Y1-CLOSER-2 close): the MASTER
`gammaOneNaive_representable` and its full input chain in this file audit at
`{propext, Classical.choice, Quot.sound}` — the [T-A6b]/[T-B6′] designed trails were
retired by the K-series record primitives, and the last `sorryAx` consumptions (the
unprimed `Torsionπ.etale`/`torsionπ_isFinite` in the E5 core) were swapped to the proven
invertible-case variants when BB-FLAT closed (`MulByHom.flat_of_nIsInvertible`,
`MulByHomSmooth.lean`).
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
T7 uniqueness through the induced-chart comparison ENGINE. Audits at
`{propext, Classical.choice, Quot.sound}` (v10.152 — the designed [T-A6b]/[T-B6′] trails
are retired). -/
theorem exists_tatePoint :
    ∃ P₀ : (tateUniversal R).Section,
      (tateUniversal R).NowhereGeomOrderLEThree P₀ ∧
      ∀ (Y : EllObj R) (P : Y.curve.Section), Y.curve.NowhereGeomOrderLEThree P →
        ∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P :=
  -- Witness = `P₀ = (0,0)` (`tateMarkedPoint`); first conjunct is the [Y1-vi] leaf; the
  -- classifying ∀-clause is the [Y1-ATLAS] deliverable `tateMarkedPoint_classifies`
  -- (YOneAtlasClassify.lean, Loeffler Prop 3.3.4's general case).
  ⟨tateMarkedPoint R, tateMarkedPoint_nowhereGeomOrderLEThree R,
    fun Y P hP ↦ MarkedChartData.tateMarkedPoint_classifies R Y P hP⟩

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
  (⋃ d ∈ N.properDivisors.filter (fun d ↦ 4 ≤ d),
    ((tateUniversal R).killedLocusπ (tatePoint R) N).base ⁻¹'
      Set.range ((tateUniversal R).killedLocusπ (tatePoint R) d).base)ᶜ

/-- **(Y1-C5)** `Y₁(N)` is open in `Y_N`: each removed `Y_d` has closed image (closed
immersion), the union is finite, and we take the complement of its preimage. -/
theorem yOneSet_isOpen : IsOpen (yOneSet R N) := by
  rw [yOneSet, isOpen_compl_iff]
  refine isClosed_biUnion_finset fun d _ ↦ ?_
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

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-D1 forward)** If `t : T ⟶ 𝒴` factors through the closed `Y_N` by a map whose image
lands in the open `yOneSet`, then the pulled-back marked point is a naive `Γ₁(N)` structure:
the global kill comes from `killedLocus_spec`; fibrewise, any proper multiple `d • P = 0` with
`d ∣ N` would put the fibre in a removed `Y_d`, contradicting the range condition (or is ruled
out by `tatePoint_nowhereGeomOrderLEThree` when `d ≤ 3`). -/
private theorem factors_yOne_iff_forward [NeZero N] {T : Scheme.{u}} (t : T ⟶ tateBase R)
    (h : ∃ g : T ⟶ (tateUniversal R).killedLocus (tatePoint R) N,
        g ≫ (tateUniversal R).killedLocusπ (tatePoint R) N = t ∧
          Set.range g.base ⊆ yOneSet R N) :
    ((tateUniversal R).baseChange t).IsNaiveGammaOne N
      (EllipticCurve.Point.asSection (tateUniversal R) t
        (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R))) := by
  obtain ⟨g, hg, hrange⟩ := h
  have hkill : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R) = 0 :=
    ((tateUniversal R).killedLocus_spec (tatePoint R) N t).mp ⟨g, hg⟩
  have hc1 : (N : ℤ) • EllipticCurve.Point.asSection (tateUniversal R) t
      (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R)) = 0 :=
    ((tateUniversal R).zsmul_asSection_pull_eq_zero_iff (tatePoint R) t (N : ℤ)).mpr hkill
  refine ⟨hc1, fun k _ _ τ ↦ ⟨?_, ?_⟩⟩
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
    · push Not at hd3
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
      push Not at hy
      refine hy d (by rw [Finset.mem_filter, Nat.mem_properDivisors]
                      exact ⟨⟨hdmem.1, hdmem.2⟩, hd3⟩) ?_
      have hgt : ((tateUniversal R).killedLocusπ (tatePoint R) N).base (g.base (τ.base cp))
          = (τ ≫ t).base cp := by
        rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
      rw [Set.mem_preimage, hgt]
      exact hxmem

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-D1 backward)** If the pulled-back marked point is a naive `Γ₁(N)` structure, then
`t` factors through `Y_N` with image in `yOneSet`: the global kill gives the factoring `g`
(`killedLocus_spec`); and if any fibre landed in a removed `Y_d`, the geometric point (over an
algebraic closure of the residue field) would kill a proper multiple `d • P`, contradicting the
exact-order clause `hfib`. -/
private theorem factors_yOne_iff_backward [NeZero N] {T : Scheme.{u}} (t : T ⟶ tateBase R)
    (h : ((tateUniversal R).baseChange t).IsNaiveGammaOne N
      (EllipticCurve.Point.asSection (tateUniversal R) t
        (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R)))) :
    ∃ g : T ⟶ (tateUniversal R).killedLocus (tatePoint R) N,
      g ≫ (tateUniversal R).killedLocusπ (tatePoint R) N = t ∧
        Set.range g.base ⊆ yOneSet R N := by
  obtain ⟨hc1, hfib⟩ := h
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
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set τ : Spec (CommRingCat.of k) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) k)) ≫ T.fromSpecResidueField x
    with hτ
  have himg : (τ ≫ t).base (IsLocalRing.closedPoint k) = t.base x := by
    rw [Scheme.Hom.comp_apply]
    congr 1
    rw [hτ, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hτkill : (d : ℤ) • EllipticCurve.Point.pull (tateUniversal R) (τ ≫ t) (tatePoint R) = 0 := by
    rw [(tateUniversal R).pull_smul_eq_zero_iff_residue (tatePoint R) (d : ℤ) (τ ≫ t)
      ((τ ≫ t).base (IsLocalRing.closedPoint k)) ⟨IsLocalRing.closedPoint k, rfl⟩, himg]
    exact hres
  have hne := (hfib k τ).2 d (by omega) hdlt
  exact hne (((tateUniversal R).zsmul_pull_baseChange_asSection_iff (tatePoint R) t τ (d : ℤ)).mpr
    hτkill)

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
theorem factors_yOne_iff [NeZero N] (_hN : 4 ≤ N) (_hinv : IsUnit (N : R))
    {T : Scheme.{u}} (t : T ⟶ tateBase R) :
    (∃ h : T ⟶ yOne R N, h ≫ yOneBase R N = t) ↔
      ((tateUniversal R).baseChange t).IsNaiveGammaOne N
        (EllipticCurve.Point.asSection (tateUniversal R) t
          (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R))) := by
  rw [factors_yOne_iff_exists_range]
  exact ⟨factors_yOne_iff_forward R N t, factors_yOne_iff_backward R N t⟩

set_option backward.isDefEq.respectTransparency false in
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
  have : IsClosedImmersion ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
    (tateUniversal R).killedLocusπ_isClosedImmersion (tatePoint R) N
  have : Mono (yOneBase R N) := by
    show Mono ((yOneOpens R N).ι ≫ (tateUniversal R).killedLocusπ (tatePoint R) N)
    infer_instance
  -- **The D2 + D1 bridge**: for `g : Y ⟶ 𝒴`, the pulled marked section is naive `Γ₁(N)` on
  -- `Y.curve` iff `g`'s base map factors through `Y₁(N)`.
  have bridge : ∀ {Y : EllObj R} (g : Y ⟶ tateEllObj R),
      Y.curve.IsNaiveGammaOne N (EllHom.pullSection R g (tatePoint R)) ↔
        ∃ h : Y.base ⟶ yOne R N, h ≫ yOneBase R N = g.baseHom := fun {Y} g ↦
    (isNaiveGammaOne_pullSection_iff R N g (tatePoint R)).trans
      (factors_yOne_iff R N hN hinv g.baseHom).symm
  -- **`e2`**: pairs `(g, factorisation)` ≃ naive `Γ₁(N)` sections, via the atlas classifier
  -- (`tatePoint_classifies`); bijective by classifier-uniqueness (+ `yOneBase` mono) and the
  -- two existentials. `Equiv.ofBijective` supplies the round-trip laws.
  let e2 : ∀ X : EllObj R,
      {p : (X ⟶ tateEllObj R) × (X.base ⟶ yOne R N) // p.2 ≫ yOneBase R N = p.1.baseHom} ≃
        {P : X.curve.Section // X.curve.IsNaiveGammaOne N P} := fun X ↦
    Equiv.ofBijective
      (fun p ↦ ⟨EllHom.pullSection R p.1.1 (tatePoint R), (bridge p.1.1).mpr ⟨p.1.2, p.2⟩⟩)
      ⟨fun p₁ p₂ hp ↦ by
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
        fun P ↦ by
          obtain ⟨P, hP⟩ := P
          obtain ⟨g, hg, -⟩ := tatePoint_classifies R X P (hP.nowhereGeomOrderLEThree hN)
          obtain ⟨h, hh⟩ := (bridge g).mp (by rw [hg]; exact hP)
          exact ⟨⟨(g, h), hh⟩, Subtype.ext hg⟩⟩
  refine ⟨{ homEquiv := fun {X} ↦
              (EllObj.homPullbackAlongEquiv (tateEllObj R) (yOneBase R N) X).trans (e2 X)
            homEquiv_comp := fun {X X'} f v ↦ ?_ }⟩
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
it is an étale morphism"* — in this repo that is exactly **[BB-DIFF]** (`Torsionπ.etale`,
gated on `MulByHom.formallyUnramified'`, in flight). The same étale input makes the removed
loci **clopen** in `Y_N` (a section of an étale separated morphism is an open immersion), which
is what makes `Y₁(N)` affine for general `N` — Loeffler's `Spec` display is verbatim only for
`N = 5` (Def 3.3.6), so affineness is derived, not quoted (KM affine-over-`(Ell)` locator to be
attached when the KM text lands; the board's QUOTE-PARTIAL note). -/

/-- A section of an étale (hence unramified) morphism is an open immersion: its diagonal is an
open immersion, so the section — a base change of that diagonal along itself — is one too. -/
private theorem isOpenImmersion_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal f) :=
    AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal _
  have hsq := Limits.pullback_lift_diagonal_isPullback s f
  have hliftP : IsOpenImmersion
      (Limits.pullback.lift (𝟙 Y) s (by simp) :
        Y ⟶ Limits.pullback (s ≫ f) f) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  have hdec : s = (Limits.pullback.lift (𝟙 Y) s (by simp) :
      Y ⟶ Limits.pullback (s ≫ f) f) ≫ Limits.pullback.snd _ _ :=
    (Limits.pullback.lift_snd _ _ _).symm
  rw [hdec]
  infer_instance

open EllipticCurve in
/-- **(Y1-E1, the clopen split — gate [BB-DIFF])** Over a base where `N` is invertible, each
sub-killed-locus `{d • P = 0}` with `d ∣ N` is **open** inside the killed locus `{N • P = 0}`
(as well as closed): on `Y_N` the point `P` classifies into the finite étale `E[N]`
(`Torsionπ.etale`, T-B5′ — Loeffler Lemma 3.4.2(2)), the zero section of an étale separated
family is an open immersion (its diagonal is; mathlib `FormallyUnramified` +
`IsOpenImmersion (pullback.diagonal _)`), and `{d • P = 0}` is the preimage of it under the
`d`-multiple classifying section. -/
theorem killedLocus_preimage_isOpen {S : Scheme.{u}} (E : EllipticCurve S) (P : E.Section)
    [NeZero N] (hN : NIsInvertible S N) {d : ℕ} (_hd : d ∣ N) :
    IsOpen ((E.killedLocusπ P N).base ⁻¹' Set.range (E.killedLocusπ P d).base) := by
  classical
  -- the tautological `N`-killed point of `Y_N` and its `d`-multiple's torsion classifier
  have hNP : (N : ℤ) • EllipticCurve.Point.pull E (E.killedLocusπ P N) P = 0 :=
    (E.killedLocus_spec P N (E.killedLocusπ P N)).mp ⟨𝟙 _, Category.id_comp _⟩
  have hkill : ((d : ℤ) • EllipticCurve.Point.pull E (E.killedLocusπ P N) P :
      E.Point (E.killedLocusπ P N)).1 ≫ E.mulByHom N = (E.killedLocusπ P N) ≫ E.zero := by
    rw [← E.smul_eq_zero_iff_comp_mulByHom, smul_comm, hNP, smul_zero]
  set gd := E.pointToTorsion _ hkill with hgd
  -- the zero section of the (étale) torsion family is an open immersion
  have hz0 : ((0 : E.Point (𝟙 S)) : S ⟶ E.E) ≫ E.mulByHom N = 𝟙 S ≫ E.zero := by
    rw [← E.smul_eq_zero_iff_comp_mulByHom, smul_zero]
  set zT := E.pointToTorsion _ hz0 with hzT
  have hEt : Etale (E.torsionπ N) := Torsionπ.etale' E N hN
  have hzTsec : zT ≫ E.torsionπ N = 𝟙 S := E.pointToTorsion_torsionπ _ _
  have hzTopen : IsOpenImmersion zT := isOpenImmersion_of_section (E.torsionπ N) zT hzTsec
  -- the two `ι`-composites
  have hι : gd ≫ E.torsionι N =
      ((d : ℤ) • EllipticCurve.Point.pull E (E.killedLocusπ P N) P :
        E.Point (E.killedLocusπ P N)).1 := E.pointToTorsion_torsionι _ _
  have hzι : zT ≫ E.torsionι N = ((0 : E.Point (𝟙 S)) : S ⟶ E.E) :=
    E.pointToTorsion_torsionι _ _
  have hιπ : E.torsionι N ≫ E.π = E.torsionπ N := by
    have hcond : E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero :=
      Limits.pullback.condition
    have h2 := congrArg (fun m ↦ m ≫ E.π) hcond
    simpa [E.mulByHom_π, E.zero_π] using h2
  -- the zero locus of the torsion is exactly the range of the zero section
  have hrange_z : Set.range zT.base = (E.torsionι N).base ⁻¹' Set.range E.zero.base := by
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [Set.mem_preimage]
      have h1 : (E.torsionι N).base (zT.base y) = ((0 : E.Point (𝟙 S)) : S ⟶ E.E).base y := by
        show (zT ≫ E.torsionι N).base y = _
        rw [hzι]
      rw [h1, E.point_zero_val, Category.id_comp]
      exact ⟨y, rfl⟩
    · intro tpt htpt
      obtain ⟨y, hy⟩ := htpt
      refine ⟨(E.torsionπ N).base tpt, ?_⟩
      have hinj : Function.Injective (E.torsionι N).base :=
        (Scheme.Hom.isClosedEmbedding (E.torsionι N)).injective
      apply hinj
      have hπtpt : (E.torsionπ N).base tpt = E.π.base ((E.torsionι N).base tpt) := by
        rw [← hιπ]; rfl
      have hy' : E.π.base ((E.torsionι N).base tpt) = y := by
        rw [← hy]
        show (E.zero ≫ E.π).base y = y
        rw [E.zero_π]
        rfl
      have h1 : (E.torsionι N).base (zT.base ((E.torsionπ N).base tpt)) =
          ((0 : E.Point (𝟙 S)) : S ⟶ E.E).base ((E.torsionπ N).base tpt) := by
        show (zT ≫ E.torsionι N).base _ = _
        rw [hzι]
      rw [h1, E.point_zero_val, Category.id_comp]
      show E.zero.base ((E.torsionπ N).base tpt) = _
      rw [hπtpt, hy', hy]
  -- the set identity
  have hrange_d : Set.range (E.killedLocusπ P d).base =
      (((d : ℤ) • P : E.Section).1).base ⁻¹' Set.range E.zero.base :=
    AlgebraicGeometry.Scheme.Pullback.range_fst _ _
  have hset : (E.killedLocusπ P N).base ⁻¹' Set.range (E.killedLocusπ P d).base =
      gd.base ⁻¹' Set.range zT.base := by
    ext x
    show (E.killedLocusπ P N).base x ∈ Set.range (E.killedLocusπ P d).base ↔ _
    rw [hrange_d, hrange_z]
    have hpt : (((d : ℤ) • P : E.Section).1).base ((E.killedLocusπ P N).base x) =
        (E.torsionι N).base (gd.base x) := by
      show ((E.killedLocusπ P N) ≫ (((d : ℤ) • P : E.Section)).1).base x =
        (gd ≫ E.torsionι N).base x
      rw [hι]
      have h2 : (E.killedLocusπ P N) ≫ (((d : ℤ) • P : E.Section)).1 =
          ((d : ℤ) • EllipticCurve.Point.pull E (E.killedLocusπ P N) P :
            E.Point (E.killedLocusπ P N)).1 := by
        rw [← EllipticCurve.Point.pull_zsmul]
        rfl
      rw [h2]
    show _ ∈ (((d : ℤ) • P : E.Section).1).base ⁻¹' Set.range E.zero.base ↔ _
    simp only [Set.mem_preimage, hpt]
  rw [hset]
  exact (IsOpenImmersion.isOpen_range zT).preimage gd.continuous

/-- A clopen subscheme of an affine scheme is affine: transport the clopen across the affine
identification `X.toSpecΓ` to a clopen of `Spec Γ`, which is the basic open of an idempotent
(`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`), hence an affine open. -/
private theorem isAffineOpen_of_isClopen {X : Scheme.{u}} [IsAffine X] (U : X.Opens)
    (hU : IsClopen (U : Set X)) : IsAffineOpen U := by
  classical
  have : IsIso X.toSpecΓ := IsAffine.affine
  set s' := (CategoryTheory.inv X.toSpecΓ).base ⁻¹' (U : Set X) with hs'
  have hs'clopen : IsClopen s' :=
    hU.preimage (CategoryTheory.inv X.toSpecΓ).continuous
  obtain ⟨e, he, hse⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hs'clopen
  have hy1 : (U : Set X) = X.toSpecΓ.base ⁻¹' s' := by
    rw [hs', ← Set.preimage_comp]
    have h1 : X.toSpecΓ ≫ CategoryTheory.inv X.toSpecΓ = 𝟙 X := IsIso.hom_inv_id _
    have h2 : (CategoryTheory.inv X.toSpecΓ).base ∘ X.toSpecΓ.base = id := by
      funext x
      show (X.toSpecΓ ≫ CategoryTheory.inv X.toSpecΓ).base x = x
      rw [h1]
      rfl
    rw [h2, Set.preimage_id]
  have hy2 : (U : Set X) = SetLike.coe (X.basicOpen e) := by
    rw [hy1, hse]
    exact X.toΓSpec_preimage_basicOpen_eq e
  have hopens : U = X.basicOpen e := TopologicalSpace.Opens.ext hy2
  rw [hopens]
  exact (isAffineOpen_top X).basicOpen e

/-- **(Y1-E2 — affineness, gate [BB-DIFF] via Y1-E1)** `Y₁(N)` is affine: by Y1-E1 the removed
locus is clopen in `Y_N`, so `Y₁(N)` is a *clopen* subscheme of the closed subscheme
`Y_N ⊆ 𝒴 = Spec R[A,B][∆⁻¹]`; a clopen subset of an affine scheme is the basic open of an
idempotent (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`), hence affine.
(Derived — Loeffler displays `Spec` only for `N = 5`; see section header.) -/
theorem yOne_isAffine [NeZero N] (_hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    IsAffine (yOne R N) := by
  classical
  -- the ambient killed locus is affine (closed in the affine Tate atlas)
  have hci : IsClosedImmersion ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
    (tateUniversal R).killedLocusπ_isClosedImmersion (tatePoint R) N
  have hXaff : IsAffine ((tateUniversal R).killedLocus (tatePoint R) N) :=
    isAffine_of_isAffineHom ((tateUniversal R).killedLocusπ (tatePoint R) N)
  -- `N` is invertible on the Tate atlas
  have hNinv : NIsInvertible (tateBase R) N := by
    show IsUnit ((N : ℕ) : Γ(tateBase R, ⊤))
    have h1 : IsUnit ((N : ℕ) : tateRingOver R) := by
      have h2 := hinv.map (algebraMap R (tateRingOver R))
      rwa [map_natCast] at h2
    have h3 := h1.map (Scheme.ΓSpecIso (CommRingCat.of (tateRingOver R))).inv.hom
    rwa [map_natCast] at h3
  -- `Y₁(N)` is clopen in the killed locus: open by construction, closed by Y1-E1
  have hclopen : IsClopen (yOneSet R N) := by
    constructor
    · rw [yOneSet]
      rw [isClosed_compl_iff]
      refine isOpen_biUnion fun d hd ↦ ?_
      have hdN : d ∣ N := (Nat.mem_properDivisors.mp (Finset.mem_filter.mp hd).1).1
      exact killedLocus_preimage_isOpen (N := N) (tateUniversal R) (tatePoint R) hNinv hdN
    · exact yOneSet_isOpen R N
  -- transport to the spectrum: a clopen of an affine scheme is an idempotent basic open
  exact isAffineOpen_of_isClopen (yOneOpens R N) hclopen

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-E3)** The structure morphism of `Y₁(N)` is an affine morphism — source affine
(Y1-E2) and target `Spec R` affine (`HasAffineProperty @IsAffineHom`). -/
theorem yOneStructMap_isAffineHom [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    IsAffineHom (yOneStructMap R N) := by
  have := yOne_isAffine R N hN hinv
  exact (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)).mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-E4 — finite presentation)** `Y₁(N) ⟶ Spec R` is locally of finite presentation: the
atlas ring is a localized polynomial ring; the zero section of the (smooth, separated,
finitely presented) universal curve is a finitely presented closed immersion
(`FinitePresentationCancel`, Stacks 01TX — the T-B pattern of
`MulByHom.locallyOfFinitePresentation`), so its pullback `Y_N ⟶ 𝒴` is; and `Y₁(N) ⟶ Y_N`
is an open immersion. Loeffler Prop 3.4.3 requires "of finite type … `R` noetherian" — over
general `R` finite *presentation* is the right form, and it is what mathlib's
`RingHom.Smooth` consumes. -/
theorem yOneStructMap_locallyOfFinitePresentation [NeZero N] (_hN : 4 ≤ N)
    (_hinv : IsUnit (N : R)) :
    LocallyOfFinitePresentation (yOneStructMap R N) := by
  -- The zero section is lfp: `zero ≫ π = 𝟙` is lfp and `π` is (smooth ⟹) of finite type.
  have hsm : Smooth (tateUniversal R).π := SmoothOfRelativeDimension.smooth (n := 1) _
  have hzero : LocallyOfFinitePresentation (tateUniversal R).zero := by
    have h : LocallyOfFinitePresentation ((tateUniversal R).zero ≫ (tateUniversal R).π) := by
      rw [(tateUniversal R).zero_π]; infer_instance
    exact LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h inferInstance
  -- `Y_N ⟶ 𝒴` is the base change of the zero section, hence lfp.
  have hkl : LocallyOfFinitePresentation ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
    MorphismProperty.pullback_fst _ _ hzero
  -- `Y₁(N) ⟶ Y_N` is an open immersion, hence lfp.
  have hι : LocallyOfFinitePresentation (yOneOpens R N).ι := inferInstance
  -- `𝒴 ⟶ Spec R` is `Spec` of `R → R[A,B] → R[A,B][Δ⁻¹]` — polynomial then localization away, fp.
  have hstr : LocallyOfFinitePresentation (tateStructMap R) := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    rw [CommRingCat.hom_ofHom]
    refine RingHom.FinitePresentation.comp ?_ ?_
    · rw [RingHom.finitePresentation_algebraMap]
      exact IsLocalization.Away.finitePresentation (tateCurveOver R).Δ
    · rw [← MvPolynomial.algebraMap_eq, RingHom.finitePresentation_algebraMap]
      infer_instance
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.comp_mem _ _ _ hι hkl) hstr

set_option backward.isDefEq.respectTransparency false in
/-- The `baseChangeEquiv` dictionary at any base point: the pull of the tautological
section is the pull of the marked point along the composite (the `pull∘asSection` bridge). -/
private theorem pullAsSection_dict {T T' : Scheme.{u}} (s : T' ⟶ tateBase R) (τ : T ⟶ T') :
    EllipticCurve.Point.baseChangeEquiv (tateUniversal R) s τ
      (EllipticCurve.Point.pull ((tateUniversal R).baseChange s) τ
        (EllipticCurve.Point.asSection (tateUniversal R) s
          (EllipticCurve.Point.pull (tateUniversal R) s (tatePoint R)))) =
    EllipticCurve.Point.pull (tateUniversal R) (τ ≫ s) (tatePoint R) := by
  refine Subtype.ext ?_
  rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
  show (τ ≫ (EllipticCurve.Point.asSection (tateUniversal R) s
    (EllipticCurve.Point.pull (tateUniversal R) s (tatePoint R))).1) ≫ _ = _
  rw [Category.assoc, EllipticCurve.Point.asSection_val_fst]
  rfl

/-- `EllHom.pullSection` along the tautological cartesian projection is the tautological
section of the pulled point: `pullSection (pullbackAlongπ g) P = asSection g (pull g P)`.
Companion to `YFull.pullSection_asSection` (the `pullbackAlongMap` case); stated generically
so the two sides carry the uniform `X.curve` spelling (whnf-cheap). -/
theorem pullSection_pullbackAlongπ {R : CommRingCat.{u}} (X : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X.base) (P : X.curve.Section) :
    EllHom.pullSection R (X.pullbackAlongπ g) P =
      EllipticCurve.Point.asSection X.curve g (EllipticCurve.Point.pull X.curve g P) := by
  refine Subtype.ext (Limits.pullback.hom_ext ?_ ?_)
  · refine ((X.pullbackAlongπ g).isPullback.lift_fst _ _ _).trans ?_
    exact (EllipticCurve.Point.asSection_val_fst X.curve g
      (EllipticCurve.Point.pull X.curve g P)).symm
  · refine (EllHom.pullSection R (X.pullbackAlongπ g) P).2.trans ?_
    exact (EllipticCurve.Point.asSection X.curve g
      (EllipticCurve.Point.pull X.curve g P)).2.symm

/-- `Point.baseChangeEquiv` commutes with `ℤ`-scalars, concrete-hom form (avoids the
`AddMonoidHomClass`-with-metavariable synthesis that times out under heavy import
closures). -/
private theorem bcEquiv_zsmul {S : Scheme.{u}} (E : EllipticCurve S) {T T' : Scheme.{u}}
    (σ : T ⟶ S) (t : T' ⟶ T) (n : ℤ) (P : (E.baseChange σ).Point t) :
    EllipticCurve.Point.baseChangeEquiv E σ t (n • P) =
      n • EllipticCurve.Point.baseChangeEquiv E σ t P :=
  map_zsmul (EllipticCurve.Point.baseChangeEquiv E σ t).toAddMonoidHom n P

private theorem bcEquiv_zero {S : Scheme.{u}} (E : EllipticCurve S) {T T' : Scheme.{u}}
    (σ : T ⟶ S) (t : T' ⟶ T) :
    EllipticCurve.Point.baseChangeEquiv E σ t 0 = 0 :=
  map_zero (EllipticCurve.Point.baseChangeEquiv E σ t).toAddMonoidHom

/-- Torsion transports across `Point.baseChangeEquiv`: a point of the base change is `n`-killed
iff its image under the (injective) `baseChangeEquiv` is. -/
private theorem bcEquiv_zsmul_eq_zero_iff {S : Scheme.{u}} (E : EllipticCurve S)
    {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T) (n : ℤ) (P : (E.baseChange σ).Point t) :
    n • P = 0 ↔ n • EllipticCurve.Point.baseChangeEquiv E σ t P = 0 := by
  constructor
  · intro h0
    rw [← bcEquiv_zsmul, h0, bcEquiv_zero]
  · intro h0
    refine (EllipticCurve.Point.baseChangeEquiv E σ t).injective ?_
    rw [bcEquiv_zsmul, bcEquiv_zero]
    exact h0

/-- A geometric point `τ : Spec k ⟶ Spec A` (with `k` a field, hence reduced) of an affine
scheme factors through the closed thickening `Spec (A ⧸ I)` when `I` is nilpotent: the induced
ring map `A → k` kills `I` (nilpotents map to `0` in a field), so it descends through `A ⧸ I`.
The shared "every geometric point factors through the quotient" step of the E5 lift. -/
private theorem exists_specMap_factor_of_nilpotent {A k : Type u} [CommRing A] [Field k]
    (I : Ideal A) (hI : IsNilpotent I)
    (τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ τ₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (A ⧸ I)),
      τ = τ₀ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  set u := Spec.preimage τ with hu
  have hIu : ∀ x ∈ I, u.hom x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := hI
    have hxn : x ^ n = 0 := by
      have h1 : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    have h2 : (u.hom x) ^ n = 0 := by
      rw [← map_pow, hxn, map_zero]
    exact IsNilpotent.eq_zero (⟨n, h2⟩ : IsNilpotent (u.hom x))
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I u.hom hIu)), ?_⟩
  rw [← Spec.map_comp]
  rw [show CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom (Ideal.Quotient.lift I u.hom hIu) = u from
    CommRingCat.hom_ext (RingHom.ext fun x ↦ Ideal.Quotient.lift_mk I u.hom hIu)]
  exact (Spec.map_preimage τ).symm

/-- The tautological Tate-marked section over any base `s : T ⟶ 𝒴`, namely
`asSection s (pull s P₀)`, is nowhere of geometric order `≤ 3` — inherited fibrewise from
`tatePoint_nowhereGeomOrderLEThree` through the base-change dictionary `pullAsSection_dict`. -/
private theorem nowhereGeomOrderLEThree_asSection_pull_tatePoint {T : Scheme.{u}}
    (s : T ⟶ tateBase R) :
    EllipticCurve.NowhereGeomOrderLEThree ((tateUniversal R).baseChange s)
      (EllipticCurve.Point.asSection (tateUniversal R) s
        (EllipticCurve.Point.pull (tateUniversal R) s (tatePoint R))) := by
  intro k _ _ τ a ha0 ha3 h0
  refine tatePoint_nowhereGeomOrderLEThree R k (τ ≫ s) a ha0 ha3 ?_
  have h1 : (a : ℤ) • (EllipticCurve.Point.baseChangeEquiv (tateUniversal R) s τ)
      (EllipticCurve.Point.pull ((tateUniversal R).baseChange s) τ
        (EllipticCurve.Point.asSection (tateUniversal R) s
          (EllipticCurve.Point.pull (tateUniversal R) s (tatePoint R)))) = 0 := by
    rw [← bcEquiv_zsmul, h0, bcEquiv_zero]
  rw [pullAsSection_dict R s τ] at h1
  exact h1

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-E5, order transports across a nilpotent thickening)** Being nowhere of geometric
order `≤ 3` transports along the closed thickening `Spec (A ⧸ I) ↪ Spec A` (`I` nilpotent):
if a point `P : E.Point t` restricts (mod `I`) to `P₀ : E.Point t₀` whose associated section
`asSection E t₀ P₀` is nowhere of order `≤ 3`, then so is `asSection E t P`. Every geometric
point of `Spec A` over a field factors through the reduced quotient
(`exists_specMap_factor_of_nilpotent`), so the fibrewise order condition is unchanged. -/
private theorem nowhereGeomOrderLEThree_asSection_of_nilpotent {S : Scheme.{u}}
    (E : EllipticCurve S) {A : Type u} [CommRing A] (I : Ideal A) (hI : IsNilpotent I)
    (t : Spec (CommRingCat.of A) ⟶ S) {t₀ : Spec (CommRingCat.of (A ⧸ I)) ⟶ S}
    (ht₀ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t = t₀)
    (P : E.Point t) (P₀ : E.Point t₀)
    (hrest : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      (P : Spec (CommRingCat.of A) ⟶ E.E) = (P₀ : Spec (CommRingCat.of (A ⧸ I)) ⟶ E.E))
    (hord₀ : (E.baseChange t₀).NowhereGeomOrderLEThree
      (EllipticCurve.Point.asSection E t₀ P₀)) :
    (E.baseChange t).NowhereGeomOrderLEThree (EllipticCurve.Point.asSection E t P) := by
  intro k _ _ τ a ha0 ha3 h0
  obtain ⟨τ₀, hτfac⟩ := exists_specMap_factor_of_nilpotent I hI τ
  refine hord₀ k τ₀ a ha0 ha3 ?_
  have hbase : τ ≫ t = τ₀ ≫ t₀ := by rw [hτfac, Category.assoc, ht₀]
  have hvaleq : τ ≫ (P : Spec (CommRingCat.of A) ⟶ E.E) =
      τ₀ ≫ (P₀ : Spec (CommRingCat.of (A ⧸ I)) ⟶ E.E) := by
    rw [hτfac, Category.assoc, hrest]
  have hL : (a : ℤ) • (EllipticCurve.Point.baseChangeEquiv E t τ)
      (EllipticCurve.Point.pull (E.baseChange t) τ
        (EllipticCurve.Point.asSection E t P)) = 0 := by
    rw [← bcEquiv_zsmul, h0, bcEquiv_zero]
  have hLval : ((EllipticCurve.Point.baseChangeEquiv E t τ)
      (EllipticCurve.Point.pull (E.baseChange t) τ
        (EllipticCurve.Point.asSection E t P)) : Spec (CommRingCat.of k) ⟶ E.E) =
      τ ≫ (P : Spec (CommRingCat.of A) ⟶ E.E) := by
    rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
    show (τ ≫ (EllipticCurve.Point.asSection E t P : _ ⟶ (E.baseChange t).E)) ≫
      Limits.pullback.fst E.π t = _
    rw [Category.assoc]
    exact congrArg (τ ≫ ·) (EllipticCurve.Point.asSection_val_fst E t P)
  have hRval : ((EllipticCurve.Point.baseChangeEquiv E t₀ τ₀)
      (EllipticCurve.Point.pull (E.baseChange t₀) τ₀
        (EllipticCurve.Point.asSection E t₀ P₀)) : Spec (CommRingCat.of k) ⟶ E.E) =
      τ₀ ≫ (P₀ : Spec (CommRingCat.of (A ⧸ I)) ⟶ E.E) := by
    rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
    show (τ₀ ≫ (EllipticCurve.Point.asSection E t₀ P₀ : _ ⟶ (E.baseChange t₀).E)) ≫
      Limits.pullback.fst E.π t₀ = _
    rw [Category.assoc]
    exact congrArg (τ₀ ≫ ·) (EllipticCurve.Point.asSection_val_fst E t₀ P₀)
  rw [bcEquiv_zsmul_eq_zero_iff]
  refine Subtype.ext ?_
  have h2 := congrArg Subtype.val hL
  rw [E.point_smul_eq_comp_mulBy, E.point_zero_val, hLval] at h2
  rw [E.point_smul_eq_comp_mulBy, E.point_zero_val, hRval, ← hvaleq, ← hbase]
  exact h2

open EllipticCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-E5 pure core)** The étale torsion-point lift against a nilpotent ideal, packaged
through the marked-atlas classification: an atlas algebra map to `A⧸I` whose marked point is
`N`-killed lifts, after T-E1-style renormalisation by the classifying morphism of the lifted
torsion point, to an atlas algebra map to `A` with `N`-killed marked point. Ring-level
interface (no `A⧸I`-algebra structure) so the caller's `letI` diamonds stay outside. -/
private theorem exists_tateAlgLift_core (N : ℕ) [NeZero N] (_hN : 4 ≤ N)
    (_hinv : IsUnit (N : R)) {A : Type u} [CommRing A] [Algebra ↑R A]
    (I : Ideal A) (hI : IsNilpotent I)
    (ψ₀r : tateRingOver R →+* (A ⧸ I)) (ψ : tateRingOver R →ₐ[↑R] A)
    (hmkψ : (Ideal.Quotient.mk I).comp (ψ : tateRingOver R →+* A) = ψ₀r)
    (hinvA : IsUnit ((N : ℕ) : A))
    (hkill₀r : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
      (Spec.map (CommRingCat.ofHom ψ₀r)) (tatePoint R) = 0) :
    ∃ ψ' : tateRingOver R →ₐ[↑R] A,
      (Ideal.Quotient.mk I).comp (ψ' : tateRingOver R →+* A) = ψ₀r ∧
      (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) (TateAtlas.baseSpecMap R ψ')
        (tatePoint R) = 0 := by
  classical
  set t₀ := Spec.map (CommRingCat.ofHom ψ₀r) with ht₀
  set t := TateAtlas.baseSpecMap R ψ with htdef
  have hrestRaw : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t = t₀ := by
    rw [htdef, TateAtlas.baseSpecMap, ← Spec.map_comp, ht₀]
    refine congrArg Spec.map (CommRingCat.hom_ext ?_)
    exact hmkψ
  set FA := (tateUniversal R).baseChange t with hFA
  have hNinvA : NIsInvertible (Spec (CommRingCat.of A)) N := by
    show IsUnit ((N : ℕ) : Γ(Spec (CommRingCat.of A), ⊤))
    have h3 := hinvA.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    rwa [map_natCast] at h3
  have hEt : Etale (FA.torsionπ N) := Torsionπ.etale' FA N hNinvA
  have : IsFinite (FA.torsionπ N) := Torsionπ.isFinite_of_nIsInvertible FA N hNinvA
  have : IsAffine (FA.torsion N) := isAffine_of_isAffineHom (FA.torsionπ N)
  -- the killed point over A⧸I, into the universal torsion then lifted through the
  -- base-change square
  have hkill₀ : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)
      = 0 := by
    rw [ht₀]
    exact hkill₀r
  -- the killed point as an `FA`-point over the thickening's closed immersion
  set P₀A : FA.Point (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    (EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).symm
      ⟨(EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)).1, by
        have h1 := (EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)).2
        rw [h1, ← hrestRaw]⟩ with hP₀A
  have hP₀Akill : (N : ℤ) • P₀A = 0 := by
    refine (EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).injective ?_
    rw [bcEquiv_zsmul, bcEquiv_zero, hP₀A, AddEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    have h2 := congrArg Subtype.val hkill₀
    have h3 : (((N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t₀
        (tatePoint R) : (tateUniversal R).Point t₀)) =
        (0 : (tateUniversal R).Point t₀) := hkill₀
    have h4 : (((N : ℤ) • (⟨(EllipticCurve.Point.pull (tateUniversal R) t₀
        (tatePoint R)).1, by
          have h1 := (EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)).2
          rw [h1, ← hrestRaw]⟩ : (tateUniversal R).Point
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t))) :
          (tateUniversal R).Point _).1 =
        (((N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R) :
          (tateUniversal R).Point t₀)).1 := by
      rw [(tateUniversal R).point_smul_eq_comp_mulBy,
        (tateUniversal R).point_smul_eq_comp_mulBy]
    rw [h4, h3, (tateUniversal R).point_zero_val, (tateUniversal R).point_zero_val,
      hrestRaw]
  -- into the torsion, then lift the section along the thickening
  set s₀T := (FA.torsionPointsEquiv N
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).symm
    ⟨P₀A, (Submodule.mem_torsionBy_iff _ _).mpr hP₀Akill⟩ with hs₀T
  obtain ⟨sT, hsTπ, hsTrest⟩ := exists_section_lift_of_smooth (FA.torsionπ N) I hI
    s₀T.1 s₀T.2
  -- the lifted N-torsion point of the pulled universal curve over `A`
  set PTfa := (FA.torsionPointsEquiv N (𝟙 (Spec (CommRingCat.of A)))) ⟨sT, hsTπ⟩
    with hPTfa
  set PTbc := (EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t
    (𝟙 (Spec (CommRingCat.of A)))) PTfa.1 with hPTbc
  have hPTbckill : (N : ℤ) • PTbc = 0 := by
    rw [hPTbc, ← bcEquiv_zsmul, (Submodule.mem_torsionBy_iff _ _).mp PTfa.2, bcEquiv_zero]
  have hPTbcval : (PTbc : Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) =
      (sT ≫ FA.torsionι N) ≫ Limits.pullback.fst (tateUniversal R).π t := rfl
  set PT : (tateUniversal R).Point t := ⟨(PTbc : _ ⟶ (tateUniversal R).E), by
    rw [PTbc.2, Category.id_comp]⟩ with hPT
  have hPTval : (PT : Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) =
      (PTbc : Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) := rfl
  have hPTkill : (N : ℤ) • PT = 0 := by
    apply Subtype.ext
    have h2 := congrArg Subtype.val hPTbckill
    rw [(tateUniversal R).point_smul_eq_comp_mulBy,
      (tateUniversal R).point_zero_val] at h2
    rw [show (𝟙 (Spec (CommRingCat.of A)) ≫ t) ≫ (tateUniversal R).zero
        = t ≫ (tateUniversal R).zero by rw [Category.id_comp]] at h2
    rw [(tateUniversal R).point_smul_eq_comp_mulBy,
      (tateUniversal R).point_zero_val, hPTval]
    exact h2
  -- restriction of `PT` along the thickening is the killed `t₀`-pull point
  have hPTrest : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (PT :
        Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) =
      ((EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)) :
        Spec (CommRingCat.of (↑A ⧸ I)) ⟶ (tateUniversal R).E) := by
    have hsval : (s₀T.1 ≫ FA.torsionι N) ≫ Limits.pullback.fst (tateUniversal R).π t
        = ((EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)) :
          Spec (CommRingCat.of (↑A ⧸ I)) ⟶ (tateUniversal R).E) := by
      have h3 : s₀T.1 ≫ FA.torsionι N =
          ((P₀A : FA.Point (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
            Spec (CommRingCat.of (↑A ⧸ I)) ⟶ FA.E) := by
        have h4 := (FA.torsionPointsEquiv N
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).apply_symm_apply
          ⟨P₀A, (Submodule.mem_torsionBy_iff _ _).mpr hP₀Akill⟩
        have h5 := congrArg (fun z ↦
          ((z.1 : FA.Point (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
            Spec (CommRingCat.of (↑A ⧸ I)) ⟶ FA.E)) h4
        rw [hs₀T]
        exact h5
      rw [h3, hP₀A]
      exact congrArg Subtype.val
        ((EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).apply_symm_apply _)
    rw [hPTval, hPTbcval, ← Category.assoc, ← Category.assoc, hsTrest,
      Category.assoc]
    rw [Category.assoc] at hsval
    exact hsval
  -- (iv) classify the lifted section through the atlas universal property
  set PA := EllipticCurve.Point.asSection (tateUniversal R) t PT with hPA
  have hPAkill : (N : ℤ) • PA = 0 := by
    have hzeroPA : EllipticCurve.Point.asSection (tateUniversal R) t
        (0 : (tateUniversal R).Point t) = 0 := by
      have h0 := EllipticCurve.Point.asSection_zsmul (tateUniversal R) t 0
        (0 : (tateUniversal R).Point t)
      simpa using h0
    rw [hPA, ← EllipticCurve.Point.asSection_zsmul, hPTkill]
    exact hzeroPA
  -- the order condition transports along the thickening (fibres are unchanged)
  have hordPA : ((tateUniversal R).baseChange t).NowhereGeomOrderLEThree PA := by
    rw [hPA]
    exact nowhereGeomOrderLEThree_asSection_of_nilpotent (tateUniversal R) I hI t hrestRaw
      PT (EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R)) hPTrest
      (nowhereGeomOrderLEThree_asSection_pull_tatePoint R t₀)
  -- the classifying `Ell/R` morphism of the lifted pair
  obtain ⟨fc, hfc, -⟩ := tatePoint_classifies R ((tateEllObj R).pullbackAlong t)
    PA hordPA
  -- extract the algebra map under `Spec`
  have hover' : fc.baseHom ≫ tateStructMap R =
      Spec.map (CommRingCat.ofHom (algebraMap ↑R A)) := by
    refine fc.base_w.trans ?_
    show t ≫ tateStructMap R = Spec.map (CommRingCat.ofHom (algebraMap ↑R A))
    exact TateAtlas.BaseSpecMap.over R ψ
  set ψ'r := Spec.preimage fc.baseHom with hψ'r
  have hspec' : Spec.map ψ'r = fc.baseHom := Spec.map_preimage _
  have hcomp' : CommRingCat.ofHom ((algebraMap (MvPolynomial (Fin 2) R)
      (tateRingOver R)).comp MvPolynomial.C) ≫ ψ'r =
      CommRingCat.ofHom (algebraMap ↑R A) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hspec']
    exact hover'
  have hcomm' : ∀ r : ↑R, ψ'r.hom (algebraMap ↑R (tateRingOver R) r) =
      algebraMap ↑R A r := fun r ↦
    congrArg (fun (m : R ⟶ CommRingCat.of A) ↦ m.hom r) hcomp'
  set ψ' : tateRingOver R →ₐ[↑R] A :=
    { toRingHom := ψ'r.hom, commutes' := hcomm' } with hψ'
  have htspec' : TateAtlas.baseSpecMap R ψ' = fc.baseHom := by
    show Spec.map (CommRingCat.ofHom ψ'r.hom) = fc.baseHom
    exact hspec'
  -- clause (b): the pulled marked point is `N`-killed (pullSection is ℤ-linear)
  have hψ'kill : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
      (TateAtlas.baseSpecMap R ψ') (tatePoint R) = 0 := by
    have hNsec : EllHom.pullSection R fc ((N : ℤ) • tatePoint R) = 0 := by
      have hz := map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R fc)
        (EllHom.pullSection_add R fc)) (N : ℤ) (tatePoint R)
      rw [show EllHom.pullSection R fc ((N : ℤ) • tatePoint R) =
        (N : ℤ) • EllHom.pullSection R fc (tatePoint R) from hz, hfc]
      exact hPAkill
    have h3 : (EllHom.pullSection R fc ((N : ℤ) • tatePoint R)).1 ≫ fc.top =
        fc.baseHom ≫ (((N : ℤ) • tatePoint R : (tateUniversal R).Section) :
          tateBase R ⟶ (tateUniversal R).E) :=
      fc.isPullback.lift_fst _ _ _
    rw [hNsec] at h3
    have h4 : (0 : ((tateEllObj R).pullbackAlong t).curve.Section).1 ≫
          fc.top = fc.baseHom ≫ (tateUniversal R).zero := by
      rw [EllipticCurve.point_zero_val, Category.id_comp]
      exact fc.zero_w
    rw [h4] at h3
    refine Subtype.ext ?_
    rw [(tateUniversal R).point_smul_eq_comp_mulBy, (tateUniversal R).point_zero_val]
    show (TateAtlas.baseSpecMap R ψ' ≫ ((tatePoint R) : tateBase R ⟶ (tateUniversal R).E))
        ≫ (tateUniversal R).mulByHom (N : ℤ) =
      TateAtlas.baseSpecMap R ψ' ≫ (tateUniversal R).zero
    rw [htspec', Category.assoc]
    rw [show ((tatePoint R) : tateBase R ⟶ (tateUniversal R).E) ≫
        (tateUniversal R).mulByHom (N : ℤ) =
        (((N : ℤ) • tatePoint R : (tateUniversal R).Section) :
          tateBase R ⟶ (tateUniversal R).E) from
      ((tateUniversal R).point_smul_eq_comp_mulBy _ _ _).symm]
    exact h3.symm
  -- clause (a): reduction mod `I` is `ψ₀`, via uniqueness of the classification over
  -- the quotient (both `ι₀ ≫ fc` and the tautological projection classify the
  -- restricted point)
  have hψ'res : (Ideal.Quotient.mk I).comp (ψ' : tateRingOver R →+* A) = ψ₀r := by
    set ι₀ := (tateEllObj R).pullbackAlongMap t
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) with hι₀
    set P₀sec := EllipticCurve.Point.asSection (tateUniversal R)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t)
      (EllipticCurve.Point.pull (tateUniversal R)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) (tatePoint R))
      with hP₀sec
    have hord₀sec : EllipticCurve.NowhereGeomOrderLEThree
        ((tateUniversal R).baseChange
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t)) P₀sec := by
      rw [hP₀sec]
      exact nowhereGeomOrderLEThree_asSection_pull_tatePoint R _
    have hrestPT : EllipticCurve.Point.restrict (tateUniversal R)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) PT =
        EllipticCurve.Point.pull (tateUniversal R)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) (tatePoint R) := by
      refine Subtype.ext ?_
      show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
          (PT : Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫
          ((tatePoint R) : tateBase R ⟶ (tateUniversal R).E)
      rw [hPTrest, hrestRaw]
      rfl
    have hcl1 : EllHom.pullSection R (ι₀ ≫ fc) (tatePoint R) = P₀sec := by
      rw [EllHom.pullSection_comp, hfc, hPA, hι₀]
      refine (YFull.pullSection_asSection (tateEllObj R) t
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) PT).trans ?_
      rw [hP₀sec]
      exact congrArg (EllipticCurve.Point.asSection (tateUniversal R) _) hrestPT
    have hπ₀sec : EllHom.pullSection R ((tateEllObj R).pullbackAlongπ
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t)) (tatePoint R) =
        P₀sec := by
      rw [hP₀sec]
      exact pullSection_pullbackAlongπ (tateEllObj R) _ (tatePoint R)
    obtain ⟨f₀c, -, hf₀uniq⟩ := tatePoint_classifies R
      ((tateEllObj R).pullbackAlong
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t)) P₀sec hord₀sec
    have h6ell : ι₀ ≫ fc = (tateEllObj R).pullbackAlongπ
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) :=
      (hf₀uniq _ hcl1).trans (hf₀uniq _ hπ₀sec).symm
    have hbases : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ fc.baseHom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t := by
      have h6 := congrArg EllHom.baseHom h6ell
      exact h6
    have h7 : ψ'r ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
        CommRingCat.ofHom (ψ : tateRingOver R →+* A) ≫
          CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      refine Spec.map_injective ?_
      rw [Spec.map_comp, Spec.map_comp, hspec']
      exact hbases
    refine RingHom.ext fun x ↦ ?_
    have h8 := congrArg
      (fun m : CommRingCat.of (tateRingOver R) ⟶ CommRingCat.of (↑A ⧸ I) ↦
        m.hom x) h7
    have h9 := DFunLike.congr_fun hmkψ x
    show Ideal.Quotient.mk I (ψ'r.hom x) = ψ₀r x
    exact h8.trans h9
  exact ⟨ψ', hψ'res, hψ'kill⟩

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
`Torsionπ.etale` [BB-DIFF]; the chart intersection keeps the lifting ring-level —
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
  /- E5 EXECUTION LEDGER (all gates PROVEN as of v10.123-Y1):
  1. CLASSIFY: `t₀ := f₀ ≫ yOneBase R N : Spec (A⧸I) ⟶ tateBase R`; `tateRing_homEquiv`
     (T-E2) turns `Spec.preimage t₀`-side into `(α₀, β₀) : (A⧸I)²` with `Δ(α₀,β₀)` unit;
     the classified point is `pull t₀ (tatePoint R)`, killed by `N` and of fibrewise exact
     order `N` (`factors_yOne_iff` applied to `f₀`'s factoring, via
     `factors_yOne_iff_exists_range`).
  2. LIFT COEFFICIENTS: choose preimages `(α, β) : A²` (`Ideal.Quotient.mk_surjective`);
     `Δ(α, β)` is a unit since its `A⧸I`-image is and `I` is nilpotent
     (`IsNilpotent.isUnit_of_isUnit_map`-style: unit mod nilpotent ⟹ unit — mathlib
     `IsNilpotent.isUnit_quotient_mk_iff`-ish; hunt). Get `t : Spec A ⟶ tateBase R` with
     `Spec.map (mk I) ≫ ... = t₀`-square via `tateRing_homEquiv`-naturality.
  3. LIFT THE POINT: `T := (tateUniversal R).baseChange`-free route — work with the killed
     locus: `f₀` factors through `Y_N`; the lifting needed is against
     `κN := killedLocusπ (tatePoint R) N`, whose base change to `Spec A` along `t` is... —
     SIMPLER: lift through the étale `(E(α,β))[N] ⟶ Spec A` directly:
     `haveI := Torsionπ.etale` at the `modelEllipticCurve (tateCurve-of α β)`; étale =
     formally étale ⟹ the `A⧸I`-torsion-point `P₀` (from step 1 transported through the
     `t₀`-pullback dictionary) lifts uniquely to an `A`-torsion point `P`
     (`FormallyUnramified.hom_ext` gives uniqueness; existence via `Smooth`/`FormallySmooth`
     scheme-level nilpotent lifting — mathlib `Etale` + `IsSmooth.exists_lift`-family; if
     the scheme-level lifting API is thin, run it affinely: the torsion of the model over
     `Spec A` is affine (closed in the projective model's affine chart around zero... or
     directly: finite over affine ⟹ affine) and `Algebra.FormallySmooth`/`Algebra.Etale`
     ring-level lifting applies).
  4. RENORMALISE: `P` gives `(x, y) : A²` through the `Z`-chart dictionary
     (`chartSolutionsEquiv`/`ZChart.eval` as in `pt_hord`); `NowhereOrderLEThree` holds
     because orders are fibrewise and `Spec A`, `Spec (A⧸I)` share fibres (nilpotent `I`);
     T-E1 `exists_unique_variableChange_isTateNormal` yields the unique `vc` with
     `vc • E(α,β)` Tate-normal marking `(x,y) ↦ (0,0)`; the corrected coefficients define
     `t' : Spec A ⟶ tateBase R`.
  5. LAND IN `Y₁(N)`: `t'` factors through `Y_N` (`killedLocus_spec`, the killing is
     `N • P = 0` transported through the `vc`-action) and through the open `yOneSet`
     (exact order persists fibrewise; `factors_yOne_iff`) — giving `f : Spec A ⟶ yOne R N`.
  6. RESTRICTION: over `A⧸I` the lifted-then-renormalised datum reduces to the original
     `(α₀, β₀, (0,0))`: `P` restricts to `P₀` (uniqueness of the étale lift against `f₀`'s
     own witness), so the T-E1 `vc` over `A⧸I` compares two Tate-normal presentations of
     the SAME marked curve and is the identity by T-E1-uniqueness ⟹ `Spec.map (mk I) ≫ f`
     and `f₀` classify equal data ⟹ equal by `yOne`'s open-immersion mono + `Y_N`-closed
     mono + `tateRing_homEquiv`-injectivity. `f ≫ yOneStructMap = Spec.map φ` by the
     `t'`-construction over `φ`. -/
  classical
  have : Mono (yOneBase R N) := by
    have : IsClosedImmersion ((tateUniversal R).killedLocusπ (tatePoint R) N) :=
      (tateUniversal R).killedLocusπ_isClosedImmersion (tatePoint R) N
    exact mono_comp _ _
  set t₀ := f₀ ≫ yOneBase R N with ht₀
  have hstruct₀ := (factors_yOne_iff R N hN hinv t₀).mp ⟨f₀, rfl⟩
  -- THE LIFT-CORE (ledger steps 2–4): lift the classifying map with its structure, over `φ`
  obtain ⟨t, hrest, hover, hstruct⟩ :
      ∃ t : Spec (CommRingCat.of A) ⟶ tateBase R,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t = t₀ ∧
        t ≫ tateStructMap R = Spec.map φ ∧
        ((tateUniversal R).baseChange t).IsNaiveGammaOne N
          (EllipticCurve.Point.asSection (tateUniversal R) t
            (EllipticCurve.Point.pull (tateUniversal R) t (tatePoint R))) := by
    -- ledger steps 1–2: the algebra form of `t₀` and an arbitrary coefficient lift
    letI : Algebra ↑R A := φ.hom.toAlgebra
    letI : Algebra ↑R (A ⧸ I) :=
      ((φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.toAlgebra
    have hover₀ : t₀ ≫ tateStructMap R =
        Spec.map (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [ht₀, Category.assoc]
      exact hf₀
    set ψ₀r := Spec.preimage t₀ with hψ₀r
    have hspec₀ : Spec.map ψ₀r = t₀ := Spec.map_preimage t₀
    have hcomp₀ : CommRingCat.ofHom ((algebraMap (MvPolynomial (Fin 2) R)
        (tateRingOver R)).comp MvPolynomial.C) ≫ ψ₀r =
        φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      refine Spec.map_injective ?_
      rw [Spec.map_comp, hspec₀]
      exact hover₀
    have hcomm₀ : ∀ r : ↑R, ψ₀r.hom (algebraMap ↑R (tateRingOver R) r) =
        algebraMap ↑R (A ⧸ I) r := fun r ↦
      congrArg (fun (m : R ⟶ CommRingCat.of (A ⧸ I)) ↦ m.hom r) hcomp₀
    set ψ₀ : tateRingOver R →ₐ[↑R] (A ⧸ I) :=
      { toRingHom := ψ₀r.hom, commutes' := hcomm₀ } with hψ₀
    -- the classified coefficients and their lift
    set α₀ := ψ₀ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
      (MvPolynomial.X 0)) with hα₀
    set β₀ := ψ₀ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
      (MvPolynomial.X 1)) with hβ₀
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := I) α₀
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := I) β₀
    -- Δ of the lift is a unit: its image mod the nilpotent `I` is `ψ₀` of the atlas unit
    have hΔ₀unit : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom
        (algebraMap ↑R (A ⧸ I)) (fun i : Fin 2 ↦ if i = 0 then α₀ else β₀))).Δ) := by
      have hev : (MvPolynomial.eval₂Hom (algebraMap ↑R (A ⧸ I))
          (fun i : Fin 2 ↦ if i = 0 then α₀ else β₀)) =
          (ψ₀ : tateRingOver R →+* (A ⧸ I)).comp
            (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
          exact (ψ₀.commutes r).symm
        · intro i
          fin_cases i <;> simp [hα₀, hβ₀]
      rw [WeierstrassCurve.map_Δ, hev]
      have h1 : IsUnit ((algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R))
          (tateCurveOver R).Δ) := IsLocalization.Away.algebraMap_isUnit (tateCurveOver R).Δ
      have h2 := h1.map (ψ₀ : tateRingOver R →+* (A ⧸ I))
      simpa [RingHom.comp_apply] using h2
    have hΔ : IsUnit (((tateCurveOver R).map (MvPolynomial.eval₂Hom
        (algebraMap ↑R A) (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ) := by
      rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) hI]
      have hmkev : (Ideal.Quotient.mk I).comp (MvPolynomial.eval₂Hom (algebraMap ↑R A)
          (fun i : Fin 2 ↦ if i = 0 then α else β)) =
          MvPolynomial.eval₂Hom (algebraMap ↑R (A ⧸ I))
            (fun i : Fin 2 ↦ if i = 0 then α₀ else β₀) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          rfl
        · intro i
          fin_cases i <;> simp [hα, hβ]
      have h3 : (Ideal.Quotient.mk I) (((tateCurveOver R).map (MvPolynomial.eval₂Hom
          (algebraMap ↑R A) (fun i : Fin 2 ↦ if i = 0 then α else β))).Δ) =
          ((tateCurveOver R).map (MvPolynomial.eval₂Hom (algebraMap ↑R (A ⧸ I))
            (fun i : Fin 2 ↦ if i = 0 then α₀ else β₀))).Δ := by
        rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ, ← hmkev]
        rfl
      rw [h3]
      exact hΔ₀unit
    -- THE PURE CORE (ledger steps 3–4): a renormalised classifying algebra map whose
    -- marked point is globally N-killed. Its production = the étale torsion-point lift
    -- (affine ring-level, against the nilpotent I) + T-E1 renormalisation; the raw lift
    -- (α, β, hΔ, ψ := TateAtlas.ringOverAlgLift) above feeds it.
    set ψ := TateAtlas.ringOverAlgLift R α β hΔ with hψ
    obtain ⟨ψ', hψ'res, hψ'kill⟩ :
        ∃ ψ' : tateRingOver R →ₐ[↑R] A,
          (Ideal.Quotient.mkₐ ↑R I).comp ψ' = ψ₀ ∧
          (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) (TateAtlas.baseSpecMap R ψ')
            (tatePoint R) = 0 := by
      have hinvA : IsUnit ((N : ℕ) : A) := by
        have h2 := hinv.map φ.hom
        rwa [map_natCast] at h2
      have hmkψ : (Ideal.Quotient.mkₐ ↑R I).comp ψ = ψ₀ := by
        have h0 : ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
            (MvPolynomial.X 0)) = α := by
          rw [hψ]; exact TateAtlas.ringOverAlgLift_X_zero R α β hΔ
        have h1 : ψ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
            (MvPolynomial.X 1)) = β := by
          rw [hψ]; exact TateAtlas.ringOverAlgLift_X_one R α β hΔ
        apply TateAtlas.RingOver.algHom_ext
        · rw [AlgHom.comp_apply, h0]
          show Ideal.Quotient.mk I α = _
          exact hα.trans hα₀
        · rw [AlgHom.comp_apply, h1]
          show Ideal.Quotient.mk I β = _
          exact hβ.trans hβ₀
      have hmkψr : (Ideal.Quotient.mk I).comp (ψ : tateRingOver R →+* A) =
          (ψ₀ : tateRingOver R →+* (A ⧸ I)) :=
        congrArg AlgHom.toRingHom hmkψ
      have hkill₀r : (N : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
          (Spec.map (CommRingCat.ofHom (ψ₀ : tateRingOver R →+* (A ⧸ I))))
          (tatePoint R) = 0 := by
        rw [show Spec.map (CommRingCat.ofHom (ψ₀ : tateRingOver R →+* (A ⧸ I))) = t₀
          from hspec₀]
        exact ((tateUniversal R).zsmul_asSection_pull_eq_zero_iff (tatePoint R) t₀
          (N : ℤ)).mp hstruct₀.1
      obtain ⟨ψ', h1, h2⟩ := exists_tateAlgLift_core R N hN hinv I hI
        (ψ₀ : tateRingOver R →+* (A ⧸ I)) ψ hmkψr hinvA hkill₀r
      refine ⟨ψ', ?_, h2⟩
      exact AlgHom.ext fun x ↦ DFunLike.congr_fun h1 x

    -- assembly: witness with the renormalised map
    refine ⟨TateAtlas.baseSpecMap R ψ', ?_, ?_, ?_⟩
    · -- restriction (the proven raw-leg template, at ψ')
      rw [TateAtlas.baseSpecMap, ← Spec.map_comp, ← hspec₀]
      refine congrArg Spec.map (CommRingCat.hom_ext ?_)
      exact congrArg AlgHom.toRingHom hψ'res
    · exact (TateAtlas.BaseSpecMap.over R ψ').trans
        (congrArg Spec.map (CommRingCat.hom_ext rfl))
    · -- the naive structure: killing from the core, fibrewise clauses transported from
      -- `hstruct₀` (every geometric point of `Spec A` factors through `Spec (A⧸I)`)
      set t' := TateAtlas.baseSpecMap R ψ' with ht'
      have hrest' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t' = t₀ := by
        rw [ht', TateAtlas.baseSpecMap, ← Spec.map_comp, ← hspec₀]
        exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hψ'res))
      have hkill' : (N : ℤ) • EllipticCurve.Point.asSection (tateUniversal R) t'
          (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)) = 0 := by
        refine (EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t'
          (𝟙 _)).injective ?_
        rw [bcEquiv_zsmul, bcEquiv_zero]
        refine Subtype.ext ?_
        have hval : ((EllipticCurve.Point.baseChangeEquiv (tateUniversal R) t' (𝟙 _))
            (EllipticCurve.Point.asSection (tateUniversal R) t'
              (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)))).1 =
            (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)).1 := by
          rw [EllipticCurve.Point.baseChangeEquiv_apply_coe]
          exact EllipticCurve.Point.asSection_val_fst _ _ _
        have hsmulval : (((N : ℤ) • (EllipticCurve.Point.baseChangeEquiv (tateUniversal R)
            t' (𝟙 _)) (EllipticCurve.Point.asSection (tateUniversal R) t'
              (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)))) :
            _ ⟶ (tateUniversal R).E) =
            (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)).1 ≫
              (tateUniversal R).mulByHom (N : ℤ) := by
          rw [(tateUniversal R).point_smul_eq_comp_mulBy]
          rw [hval]
        rw [hsmulval]
        have hkval : (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)).1 ≫
            (tateUniversal R).mulByHom (N : ℤ) =
            ((((N : ℤ) • EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R)) :
              (tateUniversal R).Point t') : _ ⟶ (tateUniversal R).E) :=
          ((tateUniversal R).point_smul_eq_comp_mulBy _ _ _).symm
        rw [hkval, hψ'kill]
        show ((0 : (tateUniversal R).Point t') :
            Spec (CommRingCat.of A) ⟶ (tateUniversal R).E) =
          ((0 : (tateUniversal R).Point (𝟙 (Spec (CommRingCat.of A)) ≫ t')) :
            Spec (CommRingCat.of A) ⟶ (tateUniversal R).E)
        rw [(tateUniversal R).point_zero_val, (tateUniversal R).point_zero_val,
          Category.id_comp]
      refine ⟨hkill', ?_⟩
      -- fibrewise clauses: geometric points of `Spec A` factor through the quotient
      intro k _ _ τ
      obtain ⟨τ₀, hτfac⟩ := exists_specMap_factor_of_nilpotent I hI τ
      have hcomp : τ ≫ t' = τ₀ ≫ t₀ := by
        rw [hτfac, Category.assoc, hrest']
      have hbridge : ∀ (a : ℤ),
          a • EllipticCurve.Point.pull ((tateUniversal R).baseChange t') τ
            (EllipticCurve.Point.asSection (tateUniversal R) t'
              (EllipticCurve.Point.pull (tateUniversal R) t' (tatePoint R))) = 0 ↔
          a • EllipticCurve.Point.pull ((tateUniversal R).baseChange t₀) τ₀
            (EllipticCurve.Point.asSection (tateUniversal R) t₀
              (EllipticCurve.Point.pull (tateUniversal R) t₀ (tatePoint R))) = 0 := by
        intro a
        have h1 := bcEquiv_zsmul_eq_zero_iff (tateUniversal R) t' τ a
        have h2 := bcEquiv_zsmul_eq_zero_iff (tateUniversal R) t₀ τ₀ a
        rw [h1, h2, pullAsSection_dict R t' τ, pullAsSection_dict R t₀ τ₀, hcomp]
      obtain ⟨hk₀, hord₀⟩ := hstruct₀.2 k τ₀
      exact ⟨(hbridge (N : ℤ)).mpr hk₀,
        fun a ha haN h0 ↦ hord₀ a ha haN ((hbridge (a : ℤ)).mp h0)⟩
  obtain ⟨f, hf⟩ := (factors_yOne_iff R N hN hinv t).mpr hstruct
  refine ⟨f, ?_, ?_⟩
  · rw [← cancel_mono (yOneBase R N), Category.assoc, hf, hrest]
  · rw [show yOneStructMap R N = yOneBase R N ≫ tateStructMap R from rfl, ← Category.assoc,
      hf, hover]

set_option backward.isDefEq.respectTransparency false in
/-- **(Y1-E6 = Loeffler Thm 3.4.4, smoothness half of T-E7)** `Y₁(N) ⟶ Spec R` is smooth.
Loeffler (verbatim, p. 15): *"`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."* Assembly: `Y₁(N)`
is affine (Y1-E2) with finitely presented coordinate ring over `R` (Y1-E4); the lifting
(Y1-E5) rephrased through the Γ–Spec adjunction is `Algebra.FormallySmooth R Γ(Y₁(N))`
(mathlib quantifies over all square-zero pairs — Loeffler's Prop 3.4.3 "local `A`, `I`
nilpotent, `R` noetherian" is *upgraded*, soundly, because Y1-E5's proof never used locality;
artifact §E6). `FormallySmooth + FinitePresentation = Algebra.Smooth = RingHom.Smooth`, and
`HasRingHomProperty.Spec_iff` transports to the scheme morphism. -/
theorem yOneStructMap_smooth [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    Smooth (yOneStructMap R N) := by
  have := yOne_isAffine R N hN hinv
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  have hFP : RingHom.FinitePresentation ((yOneStructMap R N).appTop).hom := by
    have h := yOneStructMap_locallyOfFinitePresentation R N hN hinv
    rwa [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h
  show RingHom.Smooth _
  rw [RingHom.Smooth]
  letI : Algebra ↑Γ(Spec R, ⊤) ↑Γ(yOne R N, ⊤) := ((yOneStructMap R N).appTop).hom.toAlgebra
  refine ⟨?_, hFP⟩
  /- The `FormallySmooth` leg: transport E5's nilpotent lifting through the Γ–Spec
  adjunction. Constructor: `comp_surjective` over square-zero test pairs. -/
  rw [Algebra.FormallySmooth.iff_comp_surjective]
  intro B _ _ I hI g₀
  -- the test pair, Spec-side
  set φB : R ⟶ CommRingCat.of B := (Scheme.ΓSpecIso R).inv ≫
    CommRingCat.ofHom (algebraMap ↑Γ(Spec R, ⊤) B) with hφB
  set s₀ : Spec (CommRingCat.of (B ⧸ I)) ⟶ yOne R N :=
    Spec.map (CommRingCat.ofHom g₀.toRingHom) ≫ CategoryTheory.inv (yOne R N).toSpecΓ
    with hs₀def
  have : IsIso (yOne R N).toSpecΓ := IsAffine.affine
  -- the structure triangle of `yOneStructMap` (the hftri pattern)
  have hytri : yOneStructMap R N = (yOne R N).toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (yOneStructMap R N).appTop) :=
    toSpecΓ_appTop_triangle (yOneStructMap R N)
  have hinvy : CategoryTheory.inv (yOne R N).toSpecΓ ≫ yOneStructMap R N =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (yOneStructMap R N).appTop) := by
    have h3 := congrArg (fun m ↦ CategoryTheory.inv (yOne R N).toSpecΓ ≫ m) hytri
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h3
    exact h3
  have hf₀ : s₀ ≫ yOneStructMap R N =
      Spec.map (φB ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
    rw [hs₀def, Category.assoc, hinvy, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
    have hc := g₀.commutes ((Scheme.ΓSpecIso R).inv.hom r)
    exact hc
  obtain ⟨fL, hfLrest, hfLover⟩ :=
    yOne_infinitesimal_lifting R N hN hinv φB I ⟨2, hI⟩ s₀ hf₀
  set qf := Spec.preimage (fL ≫ (yOne R N).toSpecΓ) with hqf
  have hqfspec : Spec.map qf = fL ≫ (yOne R N).toSpecΓ := Spec.map_preimage _
  have hqfcomp : ((Scheme.ΓSpecIso R).inv ≫ (yOneStructMap R N).appTop) ≫ qf = φB := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hqfspec, Category.assoc, ← hytri]
    exact hfLover
  refine ⟨{ toRingHom := qf.hom
            commutes' := fun c ↦ ?_ }, ?_⟩
  · obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso R).inv.hom r = c :=
      ⟨(Scheme.ΓSpecIso R).hom.hom c, by
        have h1 := congrArg (fun (m : Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤)) ↦ m.hom c)
          (Iso.hom_inv_id (Scheme.ΓSpecIso R))
        exact h1⟩
    exact congrArg (fun (m : R ⟶ CommRingCat.of B) ↦ m.hom r) hqfcomp
  · refine AlgHom.ext fun c ↦ ?_
    have hmkqf : qf ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
        CommRingCat.ofHom g₀.toRingHom := by
      refine Spec.map_injective ?_
      rw [Spec.map_comp, hqfspec]
      have h1 := congrArg (fun m ↦ m ≫ (yOne R N).toSpecΓ) hfLrest
      simp only [Category.assoc] at h1
      rw [h1, hs₀def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact congrArg (fun (m : Γ(yOne R N, ⊤) ⟶ CommRingCat.of (B ⧸ I)) ↦ m.hom c) hmkqf

/-! ### F. Transport to arbitrary representing objects, and the T-E7 bridge -/

/-- **(Y1-F1)** Any object representing the naive `Γ₁(N)` problem has smooth affine structure
morphism: representing objects are unique up to isomorphism
(`Functor.RepresentableBy.uniqueUpToIso`), an isomorphism in `Ell/R` has an isomorphism of
bases compatible with the structure morphisms, and `Smooth`/`IsAffineHom` respect isomorphisms.
Instantiated at the explicit representative `yOneEllObj` with Y1-E6 + Y1-E3. -/
theorem representableBy_smooth_isAffineHom [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    (X : EllObj R) (hX : Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X)) :
    Smooth X.structMap ∧ IsAffineHom X.structMap := by
  obtain ⟨r₀⟩ := yOne_representableBy R N hN hinv
  exact YFull.smooth_affine_of_representableBy R r₀ (yOneStructMap_smooth R N hN hinv)
    (yOneStructMap_isAffineHom R N hN hinv) X hX

/-- **(Y1-MASTER — the T-E7 bridge; statement identical to the held
`gammaOneNaive_representable`, `Moduli/Representability.lean`)** For `N ≥ 4` invertible in
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
    fun X hX ↦ representableBy_smooth_isAffineHom R N hN hinv X hX⟩

/-- **(T-E7 MASTER, relocated per v10.111/117 — Y1-CLOSER S6)** = Loeffler Thm 3.4.4 + Def 3.3.6;
KM 5.x for the Drinfeld upgrade)** For
`N ≥ 4` and `N` invertible in `R`, the naive `Γ₁(N)` problem is representable, and the
representing base scheme is smooth and affine over `Spec R`.
Loeffler (verbatim, Thm 3.4.4): "`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."

Notes (adversarial pass 2026-07-06): TRUE only after `IsNaiveGammaOne` gained its
global killing clause (without it a `ℚ̄[ε]`-family gave pro-representation
`ℚ̄[[t,s]]`, contradicting smooth + quasi-finite-over-j). General `R` follows from
`ℤ[1/N]` by base change (`Smooth`, `IsAffineHom` stable). Affineness for general `N`
is QUOTE-PARTIAL: Loeffler's `Spec` display is verbatim only for `N = 5`; attach the
KM affine-over-the-j-line locator when the full text lands. -/
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) :=
          gammaOneNaive_representable_assembly R N hN hinv

/-- **Y₁(N), display form (names the scheme).** For `4 ≤ N` invertible in `R`, the explicit
scheme `yOne R N` — an open subscheme of the `N`-torsion killed locus of the universal Tate
curve, packaged as the marked object `yOneEllObj R N` — represents the naive `Γ₁(N)` moduli
problem, and its structure morphism `yOneStructMap R N` to `Spec R` is smooth and affine.
This is `gammaOneNaive_representable` with its existential witness named. -/
theorem yOne_representable_smooth_affine (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    Nonempty ((gammaOneNaiveProblem R N).RepresentableBy (yOneEllObj R N)) ∧
      Smooth (yOneStructMap R N) ∧ IsAffineHom (yOneStructMap R N) :=
  ⟨yOne_representableBy R N hN hinv, yOneStructMap_smooth R N hN hinv,
    yOneStructMap_isAffineHom R N hN hinv⟩

/-- **Y₁(N) over `ℤ[1/N]`** (Loeffler Thm 3.4.4 in its literal arithmetic form): over
`ℤ[1/N] = Localization.Away (N : ℤ)` the naive `Γ₁(N)` moduli problem is representable and
every representing scheme is smooth and affine over `Spec ℤ[1/N]`. The universal statement
`gammaOneNaive_representable` specialised at the initial base. -/
theorem gammaOneNaive_representable_zInv (N : ℕ) [NeZero N] (hN : 4 ≤ N) :
    (gammaOneNaiveProblem (CommRingCat.of (Localization.Away (N : ℤ))) N).Representable ∧
      ∀ X : EllObj (CommRingCat.of (Localization.Away (N : ℤ))),
        Nonempty ((gammaOneNaiveProblem
            (CommRingCat.of (Localization.Away (N : ℤ))) N).RepresentableBy X) →
          (Smooth X.structMap ∧ IsAffineHom X.structMap) :=
  gammaOneNaive_representable (CommRingCat.of (Localization.Away (N : ℤ))) N hN <| by
    have h := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (N : ℤ)) (N : ℤ)
    rwa [eq_intCast, Int.cast_natCast] at h

end ModularCurves
