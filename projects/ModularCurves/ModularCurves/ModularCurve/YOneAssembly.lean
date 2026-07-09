/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.GammaH
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.ForMathlib.GeometricFibreComparison
import Mathlib.NumberTheory.Divisors

/-!
# The Y₁(N) assembly (T-E7 / STREAM-Y1): Loeffler Def 3.3.6 + Thm 3.4.4

`/develop --decompose` skeleton for **T-E7** = `gammaOneNaive_representable`
(`Moduli/Representability.lean:250`, HELD — not edited here): for `N ≥ 4` and `N` invertible in
`R`, the naive `Γ₁(N)` moduli problem is representable, and any representing object has smooth
affine structure morphism. This file mirrors **Loeffler, modcurvesnotes.pdf** —
Definition 3.3.6 (printed p. 14, §3.3) and Theorem 3.4.4 (printed p. 15, §3.4) — leaf by leaf:

* build the **marked Tate atlas** `(𝒴 = Spec R[A,B][Δ⁻¹], E(A,B), (0,0))` and its scheme-level
  universal property (Loeffler Cor 3.3.5, via Prop 3.3.4 = T-E1 + T-E2 + affine-cover gluing);
* cut the **killed loci** `Y_d = {d·(0,0) = 0}` (closed, Loeffler's "`N · (0:0:1) = (0:1:0)`");
* remove the lower-order loci: `Y₁(N) := Y_N ∖ ⋃_{d∣N, 4≤d<N} Y_d` (open in `Y_N`;
  Loeffler's display verbatim — inverting `N` is the standing hypothesis `IsUnit (N : R)`);
* prove `Y₁(N)` represents the naive problem ("**By construction, this represents the functor**
  `S ↦ {elliptic curves E/S with point of exact order N}`", Def 3.3.6);
* prove `Y₁(N) → Spec R` is smooth (Thm 3.4.4: infinitesimal lifting through the étale `E[N]`)
  and affine (the lower-order loci are *clopen* in `Y_N` over `ℤ[1/N]`, again by `E[N]` étale).

The final wiring into the held `gammaOneNaive_representable` is stated here as the bridge
`gammaOneNaive_representable_assembly` (statement byte-identical to the held target), assembled
term-mode from the leaves.

Full decomposition — prose proof, verbatim quotes, Lean ↔ source match paragraphs, adversarial
attack blocks, gate register and LOC grounding — in
`.mathlib-quality/decomposition-y1-assembly.md`.

## Named gates consumed (cited, NOT rebuilt here)
* **[T-A6b]** `EllipticCurve.abelEnrichment_exists` (`GroupLaw.lean:75`, sorried) — enriches the
  projective Tate model to the working record. (Alt discharge: the T-W7 A-lane chart group law.)
* **[T-W7]** `pointedIso_exists_variableChange` + `projModelVCIso_injective`
  (`EllipticCurve/Comparison.lean`, A-lane in flight) — inside the atlas subtree (L-ATLAS).
* **[BB-DIFF MASTER]** `mulByHom_formallyUnramified'` (`EllipticCurve/MulByHomUnramified.lean`,
  in flight) ⟹ `torsionπ_etale` — feeds the clopen split (affineness) and the lifting (smoothness).
* **[T-E4-family]** canonicity transport of level structures along `Ell/R`-morphisms
  (`EllHom.pullSection_add` + the `gammaOneNaiveProblem.map` membership sorry, held file) —
  the same GME 2.2.5 canonicity chain discharges `isNaiveGammaOne_pullSection_iff` below.

AINTLIB ModularCurves STREAM-Y1 (T-E7; planning-only skeleton, all leaves `sorry`).
-/

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

/-! ### A. Fibrewise vocabulary (Loeffler §3.3, pp. 13–14)

Loeffler Prop 3.3.4 (verbatim, p. 13): *"For any scheme `S`, `E/S` an elliptic curve and
`P ∈ E(S)` such that `P, 2P, 3P ≠ 0` in any fibre, there exist unique `α, β ∈ Γ(S, O_S)` such
that `∆(α, β) ∈ Γ(S, O_S)ˣ` and a unique isomorphism `E(α, β) ≅ E` mapping `(0 : 0 : 1)` to
`P`."* The hypothesis "`P, 2P, 3P ≠ 0` in any fibre" is the geometric-fibre predicate below,
phrased with the same quantifier shape as `IsNaiveGammaOne` (all algebraically closed
`k : Type u`, all `Spec k ⟶ S`). -/

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **Loeffler's "`P, 2P, 3P ≠ 0` in any fibre"** (Prop 3.3.4 hypothesis, p. 13): on every
geometric fibre no multiple `a • P` with `1 ≤ a ≤ 3` vanishes. This is the membership condition
of the marked Tate atlas (Cor 3.3.5). Quantifier shape mirrors `IsNaiveGammaOne`. -/
def NowhereGeomOrderLEThree (P : E.Section) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
    ∀ a : ℕ, 0 < a → a ≤ 3 → (a : ℤ) • Point.pull E t P ≠ 0

/-- **(Y1-A2)** A naive `Γ₁(N)` structure with `N ≥ 4` is nowhere of order `≤ 3` — the pivot
that admits `Y₁(N)`-classified pairs into the Tate atlas. Loeffler Def 3.3.6 (p. 14) opens
"For `N ≥ 4`" precisely for this. Discharge: the fibrewise clause of `IsNaiveGammaOne` at
`a ∈ {1,2,3}`, using `a < N` from `a ≤ 3 < 4 ≤ N`. Pure logic; no geometry. -/
theorem IsNaiveGammaOne.nowhereGeomOrderLEThree {E : EllipticCurve S} {P : E.Section}
    {N : ℕ} [NeZero N] (hN : 4 ≤ N) (h : E.IsNaiveGammaOne N P) :
    E.NowhereGeomOrderLEThree P := by
  intro k _ _ t a ha0 ha3
  exact (h.2 k t).2 a ha0 (by omega)

end EllipticCurve

/-- **(Y1-A3, the divisor pivot)** In an abelian group, if `N • x = 0` and some `a • x = 0` with
`0 < a < N`, then already `d • x = 0` for a *proper divisor* `d` of `N` (namely
`d = gcd a N`). This is why Loeffler's removed loci range over proper divisors only
(Def 3.3.6, p. 14: *"`⋃_{d|N, 4≤d<N} Y_d`"*) while the naive functor forbids **all** proper
multiples from vanishing. Discharge: `addOrderOf` divisibility / Bézout; mathlib group theory. -/
theorem exists_properDivisor_smul_eq_zero {G : Type u} [AddCommGroup G] {x : G} {N a : ℕ}
    (hNx : (N : ℤ) • x = 0) (ha0 : 0 < a) (haN : a < N) (hax : (a : ℤ) • x = 0) :
    ∃ d ∈ N.properDivisors, 0 < d ∧ (d : ℤ) • x = 0 := by
  refine ⟨Nat.gcd a N, ?_, Nat.gcd_pos_iff.mpr (Or.inl ha0), ?_⟩
  · exact Nat.mem_properDivisors.mpr
      ⟨Nat.gcd_dvd_right a N, lt_of_le_of_lt (Nat.gcd_le_left N ha0) haN⟩
  · have hax' : a • x = 0 := by exact_mod_cast hax
    have hNx' : N • x = 0 := by exact_mod_cast hNx
    have hg : Nat.gcd a N • x = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp
        (Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hax')
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hNx'))
    exact_mod_cast hg

/-! ### B. The marked Tate atlas (Loeffler Def 3.3.3 + Prop 3.3.4 + Cor 3.3.5, pp. 13–14)

Loeffler Def 3.3.3 (verbatim, p. 13): *"For `S` a scheme, `α, β ∈ Γ(S, O_S)`, let `E(α, β)` be
the subscheme of `P²_S` defined by `Y²Z + αXYZ + βYZ² = X³ + βX²Z`, and let
`∆(α, β) = β³(α⁴ − α³ + 8α²β − 36αβ + 16β² + 27β)` be its discriminant. If
`∆(α, β) ∈ Γ(S, O_S)ˣ`, this is an elliptic curve over `S`."*

Loeffler Cor 3.3.5 (verbatim, p. 14): *"The pair `(Spec ℤ[A, B, ∆(A, B)⁻¹], E(A, B), (0:0:1))`
represents the functor `Schᵒᵖ → Set`, `S ↦ {eq. classes of pairs (E, P), E/S elliptic curve,
P ∈ E(S) not of order 1, 2, 3 in any fibre}`."*

We build the atlas over an arbitrary `R` at once (Loeffler's "`× Spec ℤ[1/N]`" becomes the
standing `IsUnit (N : R)` of the T-E7 statement; the ring-level dictionaries T-E1/T-E2 are
already proven for every ring). `tateCurve` (over `ℤ[A,B]`) is reused from
`Moduli/Representability.lean` (T-E2) — its base change to `R[A,B]` is the universal Tate-normal
curve here. -/

variable (R : CommRingCat.{u})

/-- The universal Tate-normal curve `E(A, B) : Y² + AXY + BY = X³ + BX²` over `R[A, B]`:
the base change of `tateCurve` (Loeffler Def 3.3.3; T-E2's curve) along `ℤ[A,B] → R[A,B]`. -/
noncomputable def tateCurveOver : WeierstrassCurve (MvPolynomial (Fin 2) R) :=
  tateCurve.map (MvPolynomial.map (Int.castRingHom R))

/-- The marked-Tate atlas ring `R[A, B][∆(A,B)⁻¹]` (Loeffler Cor 3.3.5's
`ℤ[A, B, ∆(A, B)⁻¹]`, base-changed to `R`). -/
noncomputable abbrev tateRingOver : Type u :=
  Localization.Away (tateCurveOver R).Δ

/-- The universal Tate-normal curve pushed to the atlas ring (discriminant inverted). -/
noncomputable def tateCurveLocOver : WeierstrassCurve (tateRingOver R) :=
  (tateCurveOver R).map (algebraMap _ _)

/-- Over the atlas ring the discriminant is a unit, so the universal Tate curve is elliptic
(Loeffler Def 3.3.3: "If `∆(α, β) ∈ Γ(S, O_S)ˣ`, this is an elliptic curve"). -/
instance : (tateCurveLocOver R).IsElliptic :=
  WeierstrassCurve.IsElliptic.mk <| by
    rw [tateCurveLocOver, WeierstrassCurve.map_Δ]
    exact IsLocalization.map_units (Localization.Away (tateCurveOver R).Δ)
      ⟨(tateCurveOver R).Δ, Submonoid.mem_powers _⟩

/-- Δ of the universal Tate curve is divisible by `B³` (`B = X 1`): the Tate-normal discriminant
factors as `Δ(A, B) = B³·(A⁴ − A³ + 8A²B − 36AB + 16B² + 27B)` (Loeffler Def 3.3.3). -/
lemma tateB_cube_dvd_Δ :
    ((MvPolynomial.X 1 : MvPolynomial (Fin 2) R)) ^ 3 ∣ (tateCurveOver R).Δ := by
  refine ⟨-(MvPolynomial.X 0 ^ 2 + 4 * MvPolynomial.X 1) ^ 2 - 8 * MvPolynomial.X 0 ^ 3 +
    9 * MvPolynomial.X 0 * (MvPolynomial.X 0 ^ 2 + 4 * MvPolynomial.X 1) - 27 * MvPolynomial.X 1, ?_⟩
  simp only [tateCurveOver, tateCurve, WeierstrassCurve.map, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    MvPolynomial.map_X, map_zero]
  ring

/-- **The atlas marking is `≠ 0` in every fibre, ring level.** `B = a₃` is a unit of the atlas
ring `R[A, B][Δ⁻¹]`: `B³ ∣ Δ` and `Δ` is inverted, so `B` is a unit. This is the `P ≠ 0` /
`2P ≠ 0` / `3P ≠ 0` engine for `P₀ = (0, 0)`, since `ψ₂(0,0) = B` and `ψ₃(0,0) = b₈ = B³`. -/
lemma isUnit_algebraMap_tateB :
    IsUnit (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) := by
  have hΔ : IsUnit (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (tateCurveOver R).Δ) :=
    IsLocalization.Away.algebraMap_isUnit (tateCurveOver R).Δ
  have h3 : IsUnit ((algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1)) ^ 3) := by
    rw [← map_pow]
    exact isUnit_of_dvd_unit ((algebraMap _ (tateRingOver R)).map_dvd (tateB_cube_dvd_Δ R)) hΔ
  exact (isUnit_pow_iff (by norm_num)).mp h3

/-- `a₃` of the atlas curve is a unit (`= B`, the atlas marking). -/
lemma isUnit_tateA₃ : IsUnit (tateCurveLocOver R).a₃ := by
  have h : (tateCurveLocOver R).a₃ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1) := by
    simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  rw [h]; exact isUnit_algebraMap_tateB R

/-- `a₂` of the atlas curve is a unit (`= B`; Tate normal form `a₂ = a₃`, both the atlas marking). -/
lemma isUnit_tateA₂ : IsUnit (tateCurveLocOver R).a₂ := by
  have h : (tateCurveLocOver R).a₂ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (MvPolynomial.X 1) := by
    simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]
  rw [h]; exact isUnit_algebraMap_tateB R

/-- `a₄` of the atlas curve vanishes (Loeffler's Tate form `Y² + AXY + BY = X³ + BX²`). -/
lemma tateA₄_eq_zero : (tateCurveLocOver R).a₄ = 0 := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map]; simp [tateCurve]

/-- `a₆` of the atlas curve vanishes (so the marked point `(0, 0)` lies on the curve). -/
lemma tateA₆_eq_zero : (tateCurveLocOver R).a₆ = 0 := by
  simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map]; simp [tateCurve]

/-- The base of the marked Tate atlas: `𝒴 = Spec R[A, B][∆⁻¹]` (Loeffler's `Y`, Def 3.3.6).
Reducible so that unification aligns `tateBase R` with `Spec (CommRingCat.of (tateRingOver R))`
without an expensive `whnf` (needed by the `pointSpecPointsEquiv`/`geomFibrePointAddEquiv` atlas
leaves, whose ambient scheme is spelled `Spec (of _)`). -/
@[reducible] noncomputable def tateBase : Scheme.{u} :=
  Spec (CommRingCat.of (tateRingOver R))

/-- The structure morphism `𝒴 ⟶ Spec R` (Spec of `R → R[A,B] → R[A,B][∆⁻¹]`). -/
noncomputable def tateStructMap : tateBase R ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)).comp MvPolynomial.C))

/-- Generic form of the T-W5a `crux_test` (`Moduli/WeierstrassAtlas.lean`): on an affine scheme
the top-chart `isoSpec.hom` composed with the scheme's own `isoSpec.inv` is the top inclusion. -/
theorem isAffineOpen_top_isoSpec_hom_scheme_isoSpec_inv {X : Scheme.{u}} [IsAffine X]
    (h : IsAffineOpen (⊤ : X.Opens)) :
    h.isoSpec.hom ≫ X.isoSpec.inv = (⊤ : X.Opens).ι := by
  rw [← IsAffineOpen.fromSpec_top, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- **(Y1-B1, generalising the proven `universalCurve_localModel`)** The projective model of any
elliptic Weierstrass curve over a ring is locally Weierstrass — the whole affine base, on the
single chart `⊤`, witnesses it. The T-W5a proof in `Moduli/WeierstrassAtlas.lean` is this
statement instantiated at `universalWeierstrassLoc`; nothing there is specific to that curve.
Source: Loeffler Prop 3.3.2 (trivially, for a global Weierstrass model); KM 2.2.5–2.2.6. -/
theorem projModel_locallyWeierstrass {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] :
    LocallyWeierstrass (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) := by
  intro s
  letI : Algebra A ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (Spec (CommRingCat.of A)).Opens).ι := by
    rw [← Scheme.topIso_hom]; infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))))) := by
    have : CommRingCat.ofHom (algebraMap A
        ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))) =
        (Scheme.ΓSpecIso (.of A)).inv := rfl
    rw [this]; infer_instance
  have hφ_eq : Spec.map (CommRingCat.ofHom (algebraMap A
      ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)))) =
      (Spec (CommRingCat.of A)).isoSpec.inv :=
    (Scheme.isoSpec_Spec_inv (.of A)).symm
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    W.map (algebraMap A _), inferInstance,
    asIso (pullback.fst (projModelπ W) (⊤ : (Spec (CommRingCat.of A)).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
        (algebraMap A
          ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))))))).symm ≪≫
      (isPullback_projModelBaseChange W).isoPullback.symm,
    ?c1, ?c2⟩
  have hcrux : ∀ (h : (⊤ : (Spec (CommRingCat.of A)).Opens) ∈
        (Spec (CommRingCat.of A)).affineOpens),
      (IsAffineOpen.isoSpec h).hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))))
      = (⊤ : (Spec (CommRingCat.of A)).Opens).ι :=
    fun h => hφ_eq ▸ isAffineOpen_top_isoSpec_hom_scheme_isoSpec_inv h
  case c1 =>
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap A
        ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)))))]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      IsPullback.isoPullback_inv_snd]
    conv_rhs => erw [hcrux]
    erw [← pullback.condition, IsIso.inv_hom_id_assoc]
    exact pullback.condition
  case c2 =>
    have hcrux2 : (isAffineOpen_top (Spec (CommRingCat.of A))).isoSpec.inv ≫
        (⊤ : (Spec (CommRingCat.of A)).Opens).ι = Spec.map (CommRingCat.ofHom (algebraMap
          A ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)))) :=
      hφ_eq ▸ (IsAffineOpen.isoSpec_inv_ι _).trans IsAffineOpen.fromSpec_top
    have hcrux2' : ∀ {Z : Scheme.{u}} (g : Spec (CommRingCat.of A) ⟶ Z),
        (isAffineOpen_top (Spec (CommRingCat.of A))).isoSpec.inv ≫
          (⊤ : (Spec (CommRingCat.of A)).Opens).ι ≫ g
          = Spec.map (CommRingCat.ofHom (algebraMap A
            ↑Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)))) ≫ g :=
      fun g => by rw [← Category.assoc]; exact congrArg (· ≫ g) hcrux2
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
    rw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    conv_lhs => erw [hcrux2']
    erw [← reassoc_of% projModelZero_baseChange W,
      ← (isPullback_projModelBaseChange W).isoPullback_hom_fst_assoc,
      IsIso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The universal Tate curve over the atlas, as a geometric record: the projective model of
`tateCurveLocOver R`, with its smoothness, properness and local-model witnesses. -/
noncomputable def tateGeom : EllipticCurveGeom (tateBase R) where
  E := projModel (tateCurveLocOver R)
  π := projModelπ (tateCurveLocOver R)
  zero := projModelZero (tateCurveLocOver R)
  zero_π := projModelZero_projModelπ (tateCurveLocOver R)
  smooth := projModel_smooth (tateCurveLocOver R)
  proper := projModelπ_isProper (tateCurveLocOver R)
  localModel := projModel_locallyWeierstrass (tateCurveLocOver R)

/-- The universal Tate curve as a **working record** (with its group law), through the
canonicity gate **[T-A6b]** `abelEnrichment_exists`. Heavy definition: downstream leaves consume
only the pin `tateUniversal_geom` (opaque-interface discipline, v10.24(b)). -/
noncomputable def tateUniversal : EllipticCurve (tateBase R) :=
  (EllipticCurve.abelEnrichment_exists (tateGeom R)).choose

/-- **Opaque interface** for `tateUniversal`: its geometry is `tateGeom` — total space the
projective Tate model, zero section the point at infinity `(0:1:0)`. -/
theorem tateUniversal_geom : (tateUniversal R).toEllipticCurveGeom = tateGeom R :=
  (EllipticCurve.abelEnrichment_exists (tateGeom R)).choose_spec

/-! #### The marked point `P₀ = (0,0)` of the atlas (Loeffler's `(0:0:1)`)

Constructed through the affine chart `X₂ ≠ 0` (the `Z`-chart): the origin `(0,0)` is the affine
solution `v ≡ 0` of the dehomogenised cubic (constant term `-a₆ = 0`), promoted to a section of the
projective model by the chart dictionary `chartSolutionsEquiv`/`chartHomEquiv`, then transported to
`tateUniversal` across the `tateUniversal_geom` bridge. This is the *witness* for `exists_tatePoint`
(B2); its two universal properties (nowhere-order-≤3 and the classification) are the remaining
atlas leaves. -/

open MvPolynomial in
/-- The `(0,0)` affine solution of the atlas curve in chart `X₂` (constant term `-a₆ = 0`). -/
noncomputable def tateP0sol :
    {v : {j : Fin 3 // j ≠ 2} → tateRingOver R //
      aeval v (dehomogenizeAux (tateRingOver R) 2 (tateCurveLocOver R).toProjective.polynomial)
        = 0} :=
  ⟨fun _ => 0, by
    have h6 : (tateCurveLocOver R).a₆ = 0 := by
      simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map]; simp [tateCurve]
    have h4 : (tateCurveLocOver R).a₄ = 0 := by
      simp only [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map]; simp [tateCurve]
    simp only [WeierstrassCurve.Projective.polynomial, dehomogenizeAux]
    simp [h4, h6]⟩

/-- The marked point `P₀ = (0,0)` as a morphism into the projective atlas model, via the
chart-`X₂` dictionary. -/
noncomputable def tateP0mor : tateBase R ⟶ projModel (tateCurveLocOver R) :=
  ((chartHomEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
    ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R))).1.1

/-- `P₀` is a section of the projective model: it splits `projModelπ`. -/
lemma tateP0mor_π :
    tateP0mor R ≫ projModelπ (tateCurveLocOver R) = 𝟙 (tateBase R) := by
  have h := ((chartHomEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
    ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R))).1.2
  exact h.trans (by simp [tateBase])

/-- Transport compatibility: for equal geometric records `G₁ = G₂`, the `eqToHom` bridge on
total spaces intertwines the two structure morphisms. -/
private lemma eqToHom_toGeom_π {S : Scheme.{u}} {G₁ G₂ : EllipticCurveGeom S} (h : G₁ = G₂) :
    eqToHom (congrArg EllipticCurveGeom.E h).symm ≫ G₁.π = G₂.π := by
  subst h; simp

/-- Transport compatibility, `hπ`-orientation: `G₁.π = eqToHom (E-bridge) ≫ G₂.π`. -/
private lemma eqToHom_toGeom_π' {S : Scheme.{u}} {G₁ G₂ : EllipticCurveGeom S} (h : G₁ = G₂) :
    G₁.π = eqToHom (congrArg EllipticCurveGeom.E h) ≫ G₂.π := by
  subst h; simp

/-- The total space of `tateUniversal` is the projective atlas model (through the bridge). -/
lemma tateUniversal_E_eq : (tateUniversal R).E = projModel (tateCurveLocOver R) :=
  congrArg EllipticCurveGeom.E (tateUniversal_geom R)

/-- The atlas `π`, seen through the `tateUniversal ≟ tateGeom` bridge, is `projModelπ`. -/
lemma tateUniversal_eqToHom_π :
    eqToHom (tateUniversal_E_eq R).symm ≫ (tateUniversal R).π
      = projModelπ (tateCurveLocOver R) :=
  eqToHom_toGeom_π (tateUniversal_geom R)

/-- The atlas `π` written with the bridge on the *other* side (the `hπ` datum of
`geomFibrePointAddEquiv`/`pointSpecPointsEquiv`): `π = eqToHom hE ≫ projModelπ`. -/
lemma tateUniversal_π_eq :
    (tateUniversal R).π
      = eqToHom (tateUniversal_E_eq R) ≫ projModelπ (tateCurveLocOver R) :=
  eqToHom_toGeom_π' (tateUniversal_geom R)

/-- **The marked point `P₀ = (0,0)`** of the universal Tate curve `tateUniversal R`, transported
from the projective-model chart construction across the `tateUniversal_geom` bridge. This is the
witness for `exists_tatePoint` (B2). -/
noncomputable def tateMarkedPoint : (tateUniversal R).Section :=
  ⟨tateP0mor R ≫ eqToHom (tateUniversal_E_eq R).symm, by
    rw [Category.assoc, tateUniversal_eqToHom_π]
    exact tateP0mor_π R⟩

/-- The marked Tate atlas as an object of `Ell/R`. -/
noncomputable def tateEllObj : EllObj R where
  base := tateBase R
  structMap := tateStructMap R
  curve := tateUniversal R

/-! #### [Y1-vi] The marked point is nowhere of order `≤ 3` (Loeffler p. 13 display)

The atlas curve is Tate normal (`a₄ = 0`, `a₂` and `a₃` units), so its affine marked point `(0, 0)`
is nowhere of order `1, 2, 3` — `affine_origin_order_gt_three`. Transferred to the scheme fibres
through the group iso `geomFibrePointAddEquiv` and the *transfer pin* below (proved by chart
naturality: the pulled `P₀` factors through the `Z`-chart via the base change of the chart hom
defining `tateP0mor`, so its coordinates are the `algebraMap`-images of `tateP0sol = (0, 0)`). -/

/-- Base change of the atlas curve to a fibre keeps `a₄ = 0`. -/
lemma baseChange_tateA₄_eq_zero (k : Type u) [CommRing k] [Algebra (tateRingOver R) k] :
    ((tateCurveLocOver R).baseChange k).a₄ = 0 := by
  show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) k)).a₄ = 0
  rw [WeierstrassCurve.map_a₄, tateA₄_eq_zero R, map_zero]

/-- Base change of the atlas curve to a fibre keeps `a₆ = 0`. -/
lemma baseChange_tateA₆_eq_zero (k : Type u) [CommRing k] [Algebra (tateRingOver R) k] :
    ((tateCurveLocOver R).baseChange k).a₆ = 0 := by
  show ((tateCurveLocOver R).map (algebraMap (tateRingOver R) k)).a₆ = 0
  rw [WeierstrassCurve.map_a₆, tateA₆_eq_zero R, map_zero]

/-- Base change of the atlas curve to a fibre keeps `a₂` a unit. -/
lemma baseChange_isUnit_tateA₂ (k : Type u) [CommRing k] [Algebra (tateRingOver R) k] :
    IsUnit ((tateCurveLocOver R).baseChange k).a₂ := by
  show IsUnit ((tateCurveLocOver R).map (algebraMap (tateRingOver R) k)).a₂
  rw [WeierstrassCurve.map_a₂]
  exact (isUnit_tateA₂ R).map _

/-- Base change of the atlas curve to a fibre keeps `a₃` a unit. -/
lemma baseChange_isUnit_tateA₃ (k : Type u) [CommRing k] [Algebra (tateRingOver R) k] :
    IsUnit ((tateCurveLocOver R).baseChange k).a₃ := by
  show IsUnit ((tateCurveLocOver R).map (algebraMap (tateRingOver R) k)).a₃
  rw [WeierstrassCurve.map_a₃]
  exact (isUnit_tateA₃ R).map _

/-- The affine marked point `(0, 0)` is nonsingular on every fibre (`a₆ = 0`, `a₃` a unit). -/
lemma baseChange_nonsingular_zero (k : Type u) [Field k] [Algebra (tateRingOver R) k] :
    ((tateCurveLocOver R).baseChange k).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  exact ⟨baseChange_tateA₆_eq_zero R k, Or.inl (baseChange_isUnit_tateA₃ R k).ne_zero⟩

/-- The chart-`X₂` coordinate of the atlas marked point `P₀`'s chart hom is `0`: the round-trip
`chartSolutionsEquiv (chartSolutionsEquiv.symm (0,0)) = (0,0)`. Proved as a standalone lemma so the
heavy `chartSolutionsEquiv` `whnf` (the `rfl` coordinate read-off) is spent here, not in the
consuming atlas proof. -/
private lemma tateP0_chartCoord_eq_zero (R : CommRingCat.{u}) (j : {j : Fin 3 // j ≠ 2}) :
    ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1
        (chartCoordEquiv (tateCurveLocOver R) 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) = 0 := by
  have hrfl : ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm
        (tateP0sol R)).1
        (chartCoordEquiv (tateCurveLocOver R) 2 (Ideal.Quotient.mk _ (MvPolynomial.X j)))
      = (chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)
          ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R))).1 j :=
    rfl
  rw [hrfl, Equiv.apply_symm_apply]
  rfl

/-- **(Y1-vi setup)** `tateP0mor` factors through the `Z`-chart via its chart hom `φ_B`
(= `chartSolutionsEquiv.symm (0,0)`). Standalone so the `chartHomEquiv` interface application sits
in its own heartbeat budget (the chart machinery over the localization ring `tateRingOver R` is
`whnf`-heavy). The `hdef` `rfl` matches by congruence on the shared `chartHomEquiv` head — cheap;
`chartHomEquiv_symm_coe` is then chained as a *term* (`Eq.trans`), never `rw` (whose matching would
`whnf`-explode the `ofBijective` equiv). -/
private lemma tateP0mor_factor (R : CommRingCat.{u}) :
    tateP0mor R = Spec.map (CommRingCat.ofHom ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1) ≫
      Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos := by
  have hdef : tateP0mor R
      = ((chartHomEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R))).1.1 := rfl
  exact hdef.trans (chartHomEquiv_symm_coe (tateCurveLocOver R) 2 ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)))

/-- **(Y1-vi setup)** The pulled marked point's underlying model morphism is `geomPoint ≫ tateP0mor`
(the two `eqToHom` bridges of `pointSpecPointsEquiv`/`tateMarkedPoint` cancel). -/
private lemma tateMarkedPoint_pull_fst (R : CommRingCat.{u}) (k : Type u) [Field k]
    [Algebra (tateRingOver R) k] :
    (EllipticCurve.pointSpecPointsEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k
      (EllipticCurve.Point.pull (tateUniversal R) (EllipticCurve.geomPoint (tateRingOver R) k)
        (tateMarkedPoint R))).1
      = EllipticCurve.geomPoint (tateRingOver R) k ≫ tateP0mor R := by
  show (EllipticCurve.geomPoint (tateRingOver R) k ≫
      (tateP0mor R ≫ eqToHom (tateUniversal_E_eq R).symm)) ≫ eqToHom (tateUniversal_E_eq R)
      = EllipticCurve.geomPoint (tateRingOver R) k ≫ tateP0mor R
  rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Generic `Spec.map`/`ofHom` composition-associativity fold, in its **own** heartbeat budget so
the `whnf`-heavy chart-hom `φ` of `[Y1-vi-FACTOR]` is never unfolded during the fold (the fvar `φ`
is passed opaquely; this lemma only ever sees generic ring homs). -/
private lemma spec_map_ofHom_comp_awayι {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) {X : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ X) :
    Spec.map (CommRingCat.ofHom (g.comp f)) ≫ ι
      = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) ≫ ι := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **(Y1-vi setup)** The pulled marked point factors through the `Z`-chart via the base change
`(algebraMap) ∘ φ_B` of `tateP0mor`'s chart hom.

**GAP [Y1-vi-FACTOR]** — the *only* `sorry` in the vi assembly. The identity is a pure categorical
computation: `pull P₀ = geomPoint ≫ tateP0mor` (`tateMarkedPoint_pull_fst`, PROVEN), and
`tateP0mor = Spec.map (ofHom φ_B) ≫ awayι` (`tateP0mor_factor`, PROVEN); composing and folding
`geomPoint = Spec.map (ofHom (algebraMap …))` through `CommRingCat.ofHom_comp` + `Spec.map_comp` +
`Category.assoc` gives the claim. But the *closing* `isDefEq` on `Spec.map (ofHom φ_B.1)` — where
`φ_B.1 = ((chartSolutionsEquiv …).symm (tateP0sol R)).1` over the localization ring `tateRingOver R`
— `whnf`-explodes past `maxHeartbeats` (the "concrete-module whnf-explosion" pattern; the
`chartSolutionsEquiv`/`chartHomEquiv` interface over a `Localization` base is `whnf`-heavy). Bumping
heartbeats is forbidden; further decomposition does not help since this is already a minimal
`Spec.map_comp` identity. Discharge route: an `irreducible` wrapper for `φ_B` (so `isDefEq` treats
it atomically), or `Spec`-functoriality lemmas keyed to avoid unfolding the chart equiv. All other
pieces of the transfer pin, `[Y1-vi]`, and the atlas leaf are `sorry`-free modulo this. -/
private lemma tateMarkedPoint_pull_factor (R : CommRingCat.{u}) (k : Type u) [Field k]
    [Algebra (tateRingOver R) k] :
    Spec.map (CommRingCat.ofHom ((algebraMap (tateRingOver R) k).comp ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1)) ≫
      Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos =
      (EllipticCurve.pointSpecPointsEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k
      (EllipticCurve.Point.pull (tateUniversal R) (EllipticCurve.geomPoint (tateRingOver R) k)
        (tateMarkedPoint R))).1 := by
  set φ := ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1
    with hφ
  have htp : tateP0mor R = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos := tateP0mor_factor R
  rw [tateMarkedPoint_pull_fst R k, htp]
  simp only [EllipticCurve.geomPoint]
  exact spec_map_ofHom_comp_awayι φ (algebraMap (tateRingOver R) k) _

/-- **[Y1-vi], transfer pin (chart naturality).** Over any fibre field `k`, the affine image of the
pulled marked point `P₀ = (0, 0)` is the affine origin `some 0 0`. Assembled from the setup lemmas
above (each own budget): `g` factors through the `Z`-chart via `(algebraMap) ∘ φ_B`, so its chart
coordinates are the `algebraMap`-images of `tateP0sol = (0, 0)` — read off by
`projModelPointsEquiv_some`.

Stated on the composite `projModelPointsEquiv ∘ pointSpecPointsEquiv` (v10.72 deviation (a),
APPROVED): this composite **is** the underlying map of the `[T-B6′]` group iso
`geomFibrePointAddEquiv` — definitionally, by `geomFibrePointAddEquiv_apply` (its `toEquiv` is
exactly `(pointSpecPointsEquiv …).trans (projModelPointsEquiv …)`). Phrasing it this way keeps the
statement free of a `(tateCurveLocOver R).baseChange k).IsElliptic` obligation; the group structure
(and hence `[T-B6′]`) enters only in `tateMarkedPoint_nowhereGeomOrderLEThree`, which rewrites the
goal through `geomFibrePointAddEquiv_apply` before invoking this pin. -/
theorem projModelPointsEquiv_pull_tateMarkedPoint (k : Type u) [Field k]
    [Algebra (tateRingOver R) k] [DecidableEq k]
    (hns : ((tateCurveLocOver R).baseChange k).toAffine.Nonsingular 0 0) :
    projModelPointsEquiv (tateCurveLocOver R) k
      (EllipticCurve.pointSpecPointsEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k
      (EllipticCurve.Point.pull (tateUniversal R) (EllipticCurve.geomPoint (tateRingOver R) k)
        (tateMarkedPoint R))) =
      WeierstrassCurve.Affine.Point.some 0 0 hns := by
  set g := EllipticCurve.pointSpecPointsEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k
      (EllipticCurve.Point.pull (tateUniversal R) (EllipticCurve.geomPoint (tateRingOver R) k)
        (tateMarkedPoint R)) with hgdef
  have hfac : Spec.map (CommRingCat.ofHom ((algebraMap (tateRingOver R) k).comp ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1)) ≫
      Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos = g.1 := by
    rw [hgdef]; exact tateMarkedPoint_pull_factor R k
  have hZ : InZChart (tateCurveLocOver R) g :=
    ⟨Spec.map (CommRingCat.ofHom ((algebraMap (tateRingOver R) k).comp ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1)), hfac⟩
  have hφg : (chartHomEquiv (tateCurveLocOver R) 2 k ⟨g, hZ⟩).1
      = (algebraMap (tateRingOver R) k).comp ((chartSolutionsEquiv (tateCurveLocOver R) 2 (tateRingOver R)).symm (tateP0sol R)).1 := by
    have h1 : Spec.map (CommRingCat.ofHom (chartHomEquiv (tateCurveLocOver R) 2 k ⟨g, hZ⟩).1) ≫
        Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos = g.1 := by
      rw [← chartHomEquiv_symm_coe (tateCurveLocOver R) 2
        (chartHomEquiv (tateCurveLocOver R) 2 k ⟨g, hZ⟩), Equiv.symm_apply_apply]
    have hcancel := (cancel_mono (Proj.awayι (quotientGrading (projIdeal (tateCurveLocOver R)))
        ((quotientGradingHom (projIdeal (tateCurveLocOver R))) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one (tateCurveLocOver R) 2) one_pos)).mp (h1.trans hfac.symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hcancel)
  have hcoord : ∀ j : {j : Fin 3 // j ≠ 2},
      (chartSolutionsEquiv (tateCurveLocOver R) 2 k
        (chartHomEquiv (tateCurveLocOver R) 2 k ⟨g, hZ⟩)).1 j = 0 := by
    intro j
    rw [coord_val (tateCurveLocOver R) k g hZ j, hφg, RingHom.comp_apply,
      tateP0_chartCoord_eq_zero R j, map_zero]
  exact projModelPointsEquiv_some (tateCurveLocOver R) k g hZ 0 0 hns
    (hcoord ⟨0, by decide⟩).symm (hcoord ⟨1, by decide⟩).symm

/-- **[Y1-vi]** The marked point `P₀ = (0, 0)` of the universal Tate curve is nowhere of order
`≤ 3` (Loeffler Prop 3.3.4 hypothesis / p. 13 display *"`P` does not have order 1, 2 or 3 in any
fibre"*). This is the first conjunct of `exists_tatePoint` (the atlas leaf B2). Consumes the
transfer pin `projModelPointsEquiv_pull_tateMarkedPoint` + `affine_origin_order_gt_three` through the
`[T-B6′]` group iso `geomFibrePointAddEquiv` (whose `map_add'` carries the tracked T-B6 `sorry`). -/
theorem tateMarkedPoint_nowhereGeomOrderLEThree :
    (tateUniversal R).NowhereGeomOrderLEThree (tateMarkedPoint R) := by
  intro k _ _ t a ha0 ha3
  classical
  letI : Algebra (tateRingOver R) k := (Spec.preimage
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (tateRingOver R)))).hom.toAlgebra
  have ht : t = EllipticCurve.geomPoint (tateRingOver R) k := by
    show t = Spec.map (CommRingCat.ofHom (algebraMap (tateRingOver R) k))
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  haveI : ((tateCurveLocOver R).baseChange k).IsElliptic :=
    inferInstanceAs ((tateCurveLocOver R).map (algebraMap (tateRingOver R) k)).IsElliptic
  have hns := baseChange_nonsingular_zero R k
  have htransfer : EllipticCurve.geomFibrePointAddEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k
      (EllipticCurve.Point.pull (tateUniversal R) (EllipticCurve.geomPoint (tateRingOver R) k)
        (tateMarkedPoint R)) = WeierstrassCurve.Affine.Point.some 0 0 hns := by
    rw [EllipticCurve.geomFibrePointAddEquiv_apply]
    exact projModelPointsEquiv_pull_tateMarkedPoint R k hns
  rw [ht]
  intro hzero
  apply affine_origin_order_gt_three ((tateCurveLocOver R).baseChange k)
    (baseChange_tateA₄_eq_zero R k) (baseChange_isUnit_tateA₂ R k) (baseChange_isUnit_tateA₃ R k)
    hns a ha0 ha3
  have key : (EllipticCurve.geomFibrePointAddEquiv (tateCurveLocOver R) (tateUniversal R)
      (tateUniversal_E_eq R) (tateUniversal_π_eq R) k)
      ((a : ℤ) • EllipticCurve.Point.pull (tateUniversal R)
        (EllipticCurve.geomPoint (tateRingOver R) k) (tateMarkedPoint R)) = 0 := by
    rw [hzero]; exact map_zero _
  rw [map_zsmul, htransfer] at key
  exact key

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

API-GAP subtree (artifact §B2, ordered): (i) affine-point extraction — a nowhere-vanishing
section of a projective model factors through the affine chart; (ii) the fibrewise order
conditions make `ψ₂ψ₃(P)` a **unit** (converse of `TateNormalForm.twiceNeZero_of_isUnit`, via
"non-unit ⟹ dies at a maximal ideal"); (iii) per-chart classification = **T-E1**
`exists_unique_variableChange_isTateNormal` (PROVEN) + **T-E2** `tateRing_homEquiv` (PROVEN)
+ **[T-W7]** `pointedIso_exists_variableChange`/`projModelVCIso_injective` (gate, A-lane);
(iv) gluing along the structure sheaf (maps to the affine `𝒴` glue by Γ–Spec adjunction);
(v) uniqueness of the `top` component: a pointed automorphism fixing the Tate marking is the
identity, by T-E1's *uniqueness* clause chartwise (this is where the atlas is rigid — no `N`
needed). -/
theorem exists_tatePoint :
    ∃ P₀ : (tateUniversal R).Section,
      (tateUniversal R).NowhereGeomOrderLEThree P₀ ∧
      ∀ (Y : EllObj R) (P : Y.curve.Section), Y.curve.NowhereGeomOrderLEThree P →
        ∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P := by
  -- Witness = `P₀ = (0,0)` (`tateMarkedPoint`); first conjunct is the vi leaf
  -- `tateMarkedPoint_nowhereGeomOrderLEThree` (PROVEN modulo the `[Y1-vi-FACTOR]` + `[T-B6′]` gaps).
  refine ⟨tateMarkedPoint R, tateMarkedPoint_nowhereGeomOrderLEThree R, ?_⟩
  -- Classifying universal property (atlas subtree iii/iv/v): per-chart T-E1/T-E2 + [T-W7]
  -- (comparison theorem landed v10.48) + sheaf gluing + top-component uniqueness. Remaining atlas work.
  sorry

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

/-! ### C. The killed loci and `Y₁(N)` (Loeffler Def 3.3.6, p. 14)

Loeffler Def 3.3.6 (verbatim, p. 14): *"For `N ≥ 4`, let `Y_N` be the closed subscheme of
`Y = Spec ℤ[A, B, ∆(A, B)⁻¹]`, where `N · (0 : 0 : 1) = (0 : 1 : 0)`, and let
`Y₁(N)_{ℤ[1/N]} = (Y_N − ⋃_{d|N, 4≤d<N} Y_d) ×_{Spec ℤ} Spec ℤ[1/N]`."*

`Y_d` is cut as the pullback of the zero section along the section `d • P₀` — closed because
the zero section of a separated family is a closed immersion. The removal of the lower-order
loci is an honest open subscheme of `Y_N` (only their underlying *sets* matter); inverting `N`
is the ambient hypothesis `IsUnit (N : R)`. -/

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (P : E.Section)

/-- The **killed locus** `{d • P = 0} ⊆ S` of a section `P ∈ E(S)`: the pullback of the zero
section along `d • P`. For the Tate atlas this is Loeffler's `Y_d` ("the closed subscheme of
`Y` where `d · (0:0:1) = (0:1:0)`", Def 3.3.6, p. 14). -/
noncomputable def killedLocus (d : ℕ) : Scheme.{u} :=
  pullback (((d : ℤ) • P : E.Section).1) E.zero

/-- The (closed) inclusion of the killed locus into the base. -/
noncomputable def killedLocusπ (d : ℕ) : E.killedLocus P d ⟶ S :=
  pullback.fst _ _

/-- **(Y1-C1)** `Y_d ⟶ S` is a closed immersion ("`Y_N` … the *closed* subscheme of `Y`",
Def 3.3.6): the zero section of the separated `E/S` is a closed immersion (as in
`torsionι_isClosedImmersion`, T-B3), and closed immersions pull back. -/
theorem killedLocusπ_isClosedImmersion (d : ℕ) :
    IsClosedImmersion (E.killedLocusπ P d) := by
  have h1 : IsClosedImmersion (E.zero ≫ E.π) := by
    rw [E.zero_π]
    infer_instance
  have h2 : IsClosedImmersion E.zero := IsClosedImmersion.of_comp (f := E.zero) (g := E.π)
  exact MorphismProperty.pullback_fst _ _ h2

/-- **(Y1-C2)** The universal property of the killed locus: a base change `t : T ⟶ S` factors
through `Y_d` iff the pulled-back section is killed by `d`. This is the scheme-theoretic
reading of Loeffler's "`N · (0:0:1) = (0:1:0)`" cut, and delivers exactly the **global killing
clause** of `IsNaiveGammaOne` (the clause the 2026-07-06 adversarial pass showed is required).
Discharge: pullback universal property + `point_smul_eq_comp_mulBy` + `Point.pull_zsmul`;
the factoring `h` is unique since closed immersions are monomorphisms. -/
theorem killedLocus_spec (d : ℕ) {T : Scheme.{u}} (t : T ⟶ S) :
    (∃ h : T ⟶ E.killedLocus P d, h ≫ E.killedLocusπ P d = t) ↔
      (d : ℤ) • Point.pull E t P = 0 := by
  rw [E.smul_eq_zero_iff_comp_mulByHom t d (Point.pull E t P)]
  have hpull : (Point.pull E t P : T ⟶ E.E) = t ≫ P.1 := rfl
  have hf : (((d : ℤ) • P : E.Section).1) = P.1 ≫ E.mulByHom (d : ℤ) :=
    E.point_smul_eq_comp_mulBy (𝟙 S) d P
  have hsecf : (((d : ℤ) • P : E.Section).1) ≫ E.π = 𝟙 S := ((d : ℤ) • P : E.Section).2
  have hfs : pullback.fst (((d : ℤ) • P : E.Section).1) E.zero
      = pullback.snd (((d : ℤ) • P : E.Section).1) E.zero := by
    have hc := pullback.condition (f := ((d : ℤ) • P : E.Section).1) (g := E.zero)
    calc pullback.fst (((d : ℤ) • P : E.Section).1) E.zero
        = pullback.fst _ _ ≫ ((((d : ℤ) • P : E.Section).1) ≫ E.π) := by
          rw [hsecf, Category.comp_id]
      _ = (pullback.fst _ _ ≫ ((d : ℤ) • P : E.Section).1) ≫ E.π := by rw [Category.assoc]
      _ = (pullback.snd _ _ ≫ E.zero) ≫ E.π := by rw [hc]
      _ = pullback.snd _ _ ≫ (E.zero ≫ E.π) := by rw [Category.assoc]
      _ = pullback.snd _ _ := by rw [E.zero_π, Category.comp_id]
  rw [hpull, Category.assoc, ← hf]
  constructor
  · rintro ⟨h, rfl⟩
    have hcond : E.killedLocusπ P d ≫ ((d : ℤ) • P : E.Section).1
        = pullback.snd (((d : ℤ) • P : E.Section).1) E.zero ≫ E.zero :=
      pullback.condition
    have hfs' : E.killedLocusπ P d = pullback.snd (((d : ℤ) • P : E.Section).1) E.zero := hfs
    rw [Category.assoc, hcond, ← hfs']
    exact (Category.assoc h (E.killedLocusπ P d) E.zero).symm
  · intro hcond
    exact ⟨pullback.lift t t hcond, pullback.lift_fst _ _ _⟩

/-- **(Y1-C4, geometric-point/residue-point bridge)** Vanishing of a pulled section along any
field-valued point is detected at the residue field of its image: the field-valued point factors
through `Spec κ(x)`, and `Spec` of a field embedding is an epimorphism, so pulling points back
along it is injective. This converts Loeffler's set-theoretic removal of `Y_d` into the
geometric-fibre quantifier of `IsNaiveGammaOne` (all `k` algebraically closed, all `Spec k ⟶ S`).
Discharge: `descResidueField_stalkClosedPointTo_fromSpecResidueField` factorisation +
`Scheme.hom_ext_of_comp_specMap_field` (field-embedding epi) + `point_smul_eq_comp_mulBy`. -/
theorem pull_smul_eq_zero_iff_residue (a : ℤ) {k : Type u} [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (x : S) (hx : x ∈ Set.range t.base) :
    a • Point.pull E t P = 0 ↔
      a • Point.pull E (S.fromSpecResidueField x) P = 0 := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have key : ∀ {T : Scheme.{u}} (τ : T ⟶ S),
      (a • Point.pull E τ P = 0) ↔ ((τ ≫ P.1) ≫ E.mulByHom a = τ ≫ E.zero) := by
    intro T τ
    rw [Subtype.ext_iff, E.point_smul_eq_comp_mulBy τ a (Point.pull E τ P), E.point_zero_val τ]
    exact Iff.rfl
  obtain ⟨p, hp⟩ := hx
  have hxeq : x = t (IsLocalRing.closedPoint k) := by
    rw [← hp]; exact congrArg _ (Subsingleton.elim p _)
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S t
  rw [hxeq]
  set g := Spec.map (S.descResidueField (Scheme.stalkClosedPointTo t)) with hg
  set s := S.fromSpecResidueField (t (IsLocalRing.closedPoint k)) with hs
  rw [key t, key s]
  constructor
  · intro h
    rw [← hfac] at h
    simp only [Category.assoc] at h ⊢
    exact Scheme.hom_ext_of_comp_specMap_field
      (S.descResidueField (Scheme.stalkClosedPointTo t)).hom _ _
      (by rw [CommRingCat.ofHom_hom, ← hg]; exact h)
  · intro h
    rw [← hfac]
    simp only [Category.assoc] at h ⊢
    rw [h]

/-- **(Y1-C3, the range/residue dictionary)** A point `x` of the base lies in the killed locus
iff the section dies on the residue-field fibre at `x`. Loeffler removes the `Y_d` as *loci*
(sets), while the naive functor speaks of fibres; this is the bridge's first half.
Discharge: `killedLocus_spec` at `t = S.fromSpecResidueField x` (⟸) and, for the forward
direction, a residue point over a chosen preimage `x'` fed through `pull_smul_eq_zero_iff_residue`
(Y1-C4). -/
theorem mem_killedLocus_range_iff (d : ℕ) (x : S) :
    x ∈ Set.range (E.killedLocusπ P d).base ↔
      (d : ℤ) • Point.pull E (S.fromSpecResidueField x) P = 0 := by
  constructor
  · rintro ⟨x', hx'⟩
    have hτz : (d : ℤ) • Point.pull E
        ((E.killedLocus P d).fromSpecResidueField x' ≫ E.killedLocusπ P d) P = 0 :=
      (E.killedLocus_spec P d _).mp ⟨(E.killedLocus P d).fromSpecResidueField x', rfl⟩
    have hxrange : x ∈ Set.range
        ((E.killedLocus P d).fromSpecResidueField x' ≫ E.killedLocusπ P d).base := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      show (E.killedLocusπ P d) (((E.killedLocus P d).fromSpecResidueField x')
        (IsLocalRing.closedPoint _)) = x
      rw [Scheme.fromSpecResidueField_apply]; exact hx'
    exact (E.pull_smul_eq_zero_iff_residue P (d : ℤ) _ x hxrange).mp hτz
  · intro hz
    obtain ⟨hlift, hh⟩ := (E.killedLocus_spec P d (S.fromSpecResidueField x)).mpr hz
    refine ⟨hlift (IsLocalRing.closedPoint _), ?_⟩
    show (E.killedLocusπ P d) (hlift (IsLocalRing.closedPoint _)) = x
    rw [← Scheme.Hom.comp_apply, hh, Scheme.fromSpecResidueField_apply]

/-- **(Y1-D1 bridge, fibrewise)** Pulling the base-changed marked section `asSection E t (pull t P)`
back along a geometric point `τ : Spec k ⟶ T` is, under the `baseChange` point iso, pulling `P`
along `τ ≫ t`; so its `a`-torsion is detected on the fibre over `τ ≫ t`. -/
theorem zsmul_pull_baseChange_asSection_iff {T : Scheme.{u}} (t : T ⟶ S) {k : Type u} [Field k]
    (τ : Spec (CommRingCat.of k) ⟶ T) (a : ℤ) :
    a • Point.pull (E.baseChange t) τ (Point.asSection E t (Point.pull E t P)) = 0
      ↔ a • Point.pull E (τ ≫ t) P = 0 := by
  have hbeq : Point.baseChangeEquiv E t τ
      (Point.pull (E.baseChange t) τ (Point.asSection E t (Point.pull E t P)))
      = Point.pull E (τ ≫ t) P := by
    apply Subtype.ext
    rw [Point.baseChangeEquiv_apply_coe]
    show (τ ≫ (Point.asSection E t (Point.pull E t P)).1) ≫ pullback.fst E.π t
      = (τ ≫ t) ≫ P.1
    rw [Category.assoc, Point.asSection_val_fst]
    show τ ≫ t ≫ P.1 = (τ ≫ t) ≫ P.1
    rw [Category.assoc]
  rw [← (Point.baseChangeEquiv E t τ).map_eq_zero_iff, map_zsmul, hbeq]

end EllipticCurve

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
`Y₁(N)_{ℤ[1/N]}`; general `R` with `N` invertible is the same construction over `R`). -/
noncomputable def yOne : Scheme.{u} :=
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
  sorry

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
  sorry

/-- **(Y1-D3 — Loeffler Def 3.3.6, representability half of T-E7)** `(Y₁(N), universal curve,
(0,0))` represents the naive `Γ₁(N)` moduli problem: for every `Y : Ell/R`,
`Ell/R`-morphisms `Y ⟶ Y₁(N)-object` correspond to naive `Γ₁(N)` structures on `Y.curve`,
naturally. Assembly: forward `f ↦ pullSection f (marked point)` (membership by Y1-D2 + Y1-D1
reflexivity); backward via `tatePoint_classifies` (through Y1-A2, `N ≥ 4`) followed by the
`Y₁(N)` factorisation (Y1-D1, through Y1-D2); round-trips by the atlas uniqueness clause;
naturality by `EllHom.pullSection_comp` (proven, held file). -/
theorem yOne_representableBy [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R)) :
    Nonempty ((gammaOneNaiveProblem R N).RepresentableBy (yOneEllObj R N)) := by
  sorry

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
