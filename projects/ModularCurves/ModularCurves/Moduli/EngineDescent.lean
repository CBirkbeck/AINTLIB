/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.ForMathlib.PullbackLocalAtTarget
import ModularCurves.ForMathlib.SchemeActionFree
import ModularCurves.ForMathlib.GaloisDescentModule
import ModularCurves.ForMathlib.QuotientCurveModel
import ModularCurves.ForMathlib.QuotientLift
import ModularCurves.ForMathlib.WeierstrassInvariantLocal

/-!
# Route (a): the KM 4.7 ⇐-curve as a quotient `E/G` (T-E5c leaves a2–a5)

The Katz–Mazur engine (KM p. 114) descends the universal curve `(E, α_univ)` along the
`G`-torsor `π : X → X/G` (`X = 𝕸(𝒫,δ)`, affine) and cites SGA I Exp. VIII 7.8 (*"Because `E`
is projective, via `I⁻¹(0)`, it descends"*) — **effective fppf descent of projective schemes,
absent from mathlib and B3-scale to build**.

`[T-E5c-ROUTE-A]`'s verdict: this is avoidable. KM's cocycle `θ(g)` *is* a `G`-action on the
total space `E` lifting the action on `X` — see `ModuliProblem.simulSchemeActionTotal`
(leaf `[a1]`, PROVEN) — so the descended curve is literally the **quotient** `E/G`, produced
by AINTLIB's own `SchemeAction.quotient` (T-Q5, proven, sorry-free). No SGA, no algebraic
spaces, no relative Proj, no `ω`.

This file develops the resulting descent, in the generality of *any* free lift of a free
action to a geometric elliptic curve:

* `IsCurveAction` — the (Prop-valued) axioms of a lift: `π` and the zero section are
  equivariant, and each `γ` acts cartesianly. All three are supplied by `[a1]`.
* `orbit_mem_isAffineOpen_of_charts` (**PROVEN**) — the orbit-in-an-affine-open hypothesis of
  `SchemeAction.exists_isStableOpen_isAffineOpen` follows from **two** charts: an affine open
  containing the whole zero section, and an affine open containing its complement. The
  dichotomy is clean because the zero section's image is `G`-stable.
* `exists_isStableOpen_isAffineOpen_of_orbit` (**PROVEN**) — hence a `G`-stable affine atlas
  of `E`, which is exactly what `SchemeAction.quotient` consumes.
* `isAffineOpen_zeroComplement` / `exists_isAffineOpen_zeroSection` — the two charts
  (leaves `[a2-α]`, `[a2-β]`).
* `exists_ellipticCurveGeom_quotient` — the route-(a) descent theorem (leaves `[a3]`–`[a5]`).

The group law on the quotient is *not* part of this file: `EllipticCurveGeom.toEllipticCurve`
(T-W7, beastmode-A/P3b3) upgrades any geometric elliptic curve to the full record, so route
(a) only ever has to produce an `EllipticCurveGeom`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace ModularCurves

namespace RouteA

variable {G : Type u} [Group G] {X : Scheme.{u}}

/-- **The axioms of a lift of a scheme action to a geometric elliptic curve** (`[a1]`'s
output, packaged). `σE` lifts `σ` if the structure morphism and the zero section are
equivariant and each `γ ∈ G` acts by a *cartesian* square over the base action.

For KM's action this is `simulSchemeActionTotal_π`, `simulSchemeActionTotal_zero` and
`simulSchemeActionTotal_isPullback` — i.e. exactly the three fields of `EllHom`. -/
structure IsCurveAction (σ : SchemeAction G X) (C : EllipticCurveGeom X)
    (σE : SchemeAction G C.E) : Prop where
  /-- `π` intertwines the two actions. -/
  π_equivariant : ∀ γ : G, σE.hom γ ≫ C.π = C.π ≫ σ.hom γ
  /-- The zero section intertwines the two actions. -/
  zero_equivariant : ∀ γ : G, C.zero ≫ σE.hom γ = σ.hom γ ≫ C.zero
  /-- Each `γ` acts cartesianly: `E` is the pullback of itself along `σ γ`. -/
  cartesian : ∀ γ : G, IsPullback (σE.hom γ) C.π C.π (σ.hom γ)

variable {C : EllipticCurveGeom X} {σ : SchemeAction G X} {σE : SchemeAction G C.E}

/-- The image of the zero section is stable under the lifted action, as a set of points. -/
theorem mem_range_zero_of_smul (hact : IsCurveAction σ C σE) (γ : G) {e : C.E}
    (he : e ∈ Set.range C.zero.base) : (σE.hom γ).base e ∈ Set.range C.zero.base := by
  obtain ⟨x, rfl⟩ := he
  refine ⟨(σ.hom γ).base x, ?_⟩
  have := congrArg (fun f : X ⟶ C.E => f.base x) (hact.zero_equivariant γ)
  exact this.symm

/-- Conversely, the complement of the zero section is stable: if `γ · e` lies on the zero
section then so does `e`. -/
theorem mem_range_zero_of_smul_mem (hact : IsCurveAction σ C σE) (γ : G) {e : C.E}
    (he : (σE.hom γ).base e ∈ Set.range C.zero.base) : e ∈ Set.range C.zero.base := by
  have hinv : (σE.hom γ⁻¹).base ((σE.hom γ).base e) = e := by
    have h1 : σE.hom γ ≫ σE.hom γ⁻¹ = 𝟙 C.E := by
      rw [← σE.hom_mul, mul_inv_cancel, σE.hom_one]
    have h2 := congrArg (fun f : C.E ⟶ C.E => f.base e) h1
    simpa using h2
  rw [← hinv]
  exact mem_range_zero_of_smul hact γ⁻¹ he

/-- **([a2], the orbit-in-an-affine-open input)** Two affine charts suffice: one containing
the whole image of the zero section, one containing its complement. Every `G`-orbit lies in
one of them, because the image of the zero section is `G`-stable
(`mem_range_zero_of_smul`, `mem_range_zero_of_smul_mem`).

This is the hypothesis of `SchemeAction.exists_isStableOpen_isAffineOpen`, and hence — via
`exists_isStableOpen_isAffineOpen_of_orbit` below — the only geometric input route (a) needs
in order to form `E/G`. It replaces "`E` is quasi-projective over the affine base, so a
finite set of points lies in an affine open" (Stacks 01ZY, absent from mathlib). -/
theorem orbit_mem_isAffineOpen_of_charts (hact : IsCurveAction σ C σE)
    {U₀ U₁ : (C.E).Opens} (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁)
    (hU₀mem : ∀ x : X, C.zero.base x ∈ U₀)
    (hU₁mem : ∀ e : C.E, e ∉ Set.range C.zero.base → e ∈ U₁) (e : C.E) :
    ∃ U : (C.E).Opens, IsAffineOpen U ∧ ∀ γ : G, (σE.hom γ).base e ∈ U := by
  by_cases he : e ∈ Set.range C.zero.base
  · refine ⟨U₀, hU₀, fun γ => ?_⟩
    obtain ⟨x, hx⟩ := mem_range_zero_of_smul hact γ he
    rw [← hx]
    exact hU₀mem x
  · exact ⟨U₁, hU₁, fun γ => hU₁mem _ fun hmem => he (mem_range_zero_of_smul_mem hact γ hmem)⟩

/-- **([a2], the `G`-stable affine atlas of `E`)** With the orbit hypothesis discharged, the
`G`-stable affine atlas of `E` required by `SchemeAction.quotient` exists: shrink an affine
open containing the orbit to `⨅ γ, (σE γ)⁻¹ U`. -/
theorem exists_isStableOpen_isAffineOpen_of_orbit [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U) (e : C.E) :
    ∃ W : (C.E).Opens, σE.IsStableOpen W ∧ IsAffineOpen W ∧ e ∈ W := by
  obtain ⟨U, hU, horb⟩ := horbit e
  exact σE.exists_isStableOpen_isAffineOpen hU e horb

/-- **([a3-ii] semilinearity, PROVEN)** The comparison ring map `C.π.appLE U W : Γ(X, U) → Γ(E, W)`
is `G`-equivariant: `g • (φ a) = φ (g • a)`, where the two actions are the `gammaMulSemiringAction`s
on the stable affine opens `U ⊆ X` and `W ⊆ E`.

This is exactly `appLE`-functoriality applied to the equivariance square `IsCurveAction.π_equivariant`
(`σE.hom g ≫ C.π = C.π ≫ σ.hom g`). It is what makes `Γ(E, W)` a *semilinear* `Γ(X,U)[G]`-module, the
hypothesis `hslC` of `MulSemiringAction.isPushout_fixedPoints`. -/
theorem appLE_π_equivariant (hact : IsCurveAction σ C σE)
    {U : X.Opens} (hU : σ.IsStableOpen U) {W : (C.E).Opens} (hW : σE.IsStableOpen W)
    (h : W ≤ C.π ⁻¹ᵁ U) (g : G) :
    C.π.appLE U W h ≫ (σE.hom g).appLE W W (hW.le_preimage g) =
      (σ.hom g).appLE U U (hU.le_preimage g) ≫ C.π.appLE U W h := by
  have key : ∀ {m m' : C.E ⟶ X} (_ : m = m') (e : W ≤ m ⁻¹ᵁ U) (e' : W ≤ m' ⁻¹ᵁ U),
      m.appLE U W e = m'.appLE U W e' := by
    rintro m m' rfl e e'; rfl
  rw [Scheme.Hom.appLE_comp_appLE (σE.hom g) C.π U W W,
    Scheme.Hom.appLE_comp_appLE C.π (σ.hom g) U U W]
  exact key (hact.π_equivariant g) _ _

set_option backward.isDefEq.respectTransparency false in
/-- **([a3-ii] affine core, PROVEN)** For an `IsCurveAction` with `σ` free
on the stable affine open `U ⊆ X`, and `W ⊆ E` stable affine with `W ≤ C.π⁻¹U`, the invariant-
quotient square

    ↥W ──localQuotientπ──▶ W/G
    │                       │
    C.π.resLE               q'
    ▼                       ▼
    ↥U ──localQuotientπ──▶ U/G

is **cartesian**. This is `MulSemiringAction.isPullback_Spec_fixedPoints` (Galois descent of the
semilinear `Γ(X,U)[G]`-module `Γ(E,W)`) transported by the two `IsAffineOpen.isoSpec` corner isos;
the quotient corners match by defeq (`localQuotient = Spec (FixedPoints ℤ …)` and the fixed-points
bases are defeq), and the commuting squares are `localQuotientπ_eq` / `toSpecΓ_SpecMap_appLE`. -/
theorem isPullback_localQuotientπ [Finite G] (hact : IsCurveAction σ C σE)
    {U : X.Opens} (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U)
    {W : (C.E).Opens} (hW : σE.IsStableOpen W) (hWa : IsAffineOpen W)
    (h : W ≤ C.π ⁻¹ᵁ U)
    (hfreeU : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T) :
    ∃ q' : σE.localQuotient hW ⟶ σ.localQuotient hU,
      IsPullback (σE.localQuotientπ hW hWa) (C.π.resLE U W h) q' (σ.localQuotientπ hU hUa) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  letI aX : MulSemiringAction G ↑Γ(X, U) := σ.gammaMulSemiringAction hU
  letI aE : MulSemiringAction G ↑Γ(C.E, W) := σE.gammaMulSemiringAction hW
  letI algInst : Algebra (↑Γ(X, U)) (↑Γ(C.E, W)) := (C.π.appLE U W h).hom.toAlgebra
  have hφ : ∀ (g : G) (a : ↑Γ(X, U)),
      g • (algebraMap (↑Γ(X,U)) (↑Γ(C.E,W)) a) = algebraMap _ _ (g • a) := by
    intro g a
    have hm := appLE_π_equivariant hact hU hW h g
    have e2 := congrArg (fun m : Γ(X, U) ⟶ Γ(C.E, W) => m.hom a) hm
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    simp only [SchemeAction.gammaMulSemiringAction_smul_def, RingHom.algebraMap_toAlgebra]
    exact e2
  haveI hsl : SMulCommClass G (↥(FixedPoints.subalgebra ℤ (↑Γ(X, U)) G)) (↑Γ(C.E, W)) := by
    refine ⟨fun g b c => ?_⟩
    show g • ((b : ↑Γ(X,U)) • c) = (b : ↑Γ(X,U)) • (g • c)
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hφ g, b.2 g]
  have hslC : ∀ (g : G) (a : ↑Γ(X,U)) (c : ↑Γ(C.E,W)), g • a • c = (g • a) • g • c := by
    intro g a c
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hφ g]
  have hfreeA : IsFreeAlgebraAction G ℤ ↑Γ(X, U) :=
    σ.isFreeAlgebraAction_of_free hU hUa hfreeU
  have hpb := MulSemiringAction.isPullback_Spec_fixedPoints G ℤ (↑Γ(X, U)) (↑Γ(C.E, W)) hslC hfreeA
  refine ⟨Spec.map (CommRingCat.ofHom (algebraMap
      (↥(FixedPoints.subalgebra ℤ (↑Γ(X, U)) G))
      (↥(FixedPoints.subalgebra (↥(FixedPoints.subalgebra ℤ (↑Γ(X, U)) G)) (↑Γ(C.E, W)) G)))),
    hpb.flip.of_iso hWa.isoSpec.symm (Iso.refl _) hUa.isoSpec.symm (Iso.refl _)
    ?_ ?_ ?_ ?_⟩
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [SchemeAction.localQuotientπ_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  · simp only [Iso.symm_hom]
    rw [Iso.comp_inv_eq, Category.assoc, hUa.isoSpec_hom,
      ← Scheme.Opens.toSpecΓ_SpecMap_appLE, ← Category.assoc, ← hWa.isoSpec_hom,
      Iso.inv_hom_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [SchemeAction.localQuotientπ_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl

/-! ### The two charts (leaves `[a2-α]`, `[a2-β]`) — PROVEN for a globally-modelled curve -/

attribute [local instance] MvPolynomial.gradedAlgebra

open WeierstrassCurve.Projective HomogeneousIdeal WeierstrassCurve in
/-- **([a2-α] + [a2-β], PROVEN)** A geometric elliptic curve with a **global** projective
Weierstrass model has the two affine charts required by `orbit_mem_isAffineOpen_of_charts`:

* `U₀` = the `Y`-chart `D₊(X₁)` contains the whole image of the zero section
  (`projModelZero_preimage_yChart`: the section at infinity lands entirely in the `Y`-chart);
* `U₁` = the `Z`-chart `D₊(X₂)` contains everything *off* the zero section
  (`mem_range_zero_of_not_mem_zChart`: a point outside the `Z`-chart lies on the zero section).

Both are affine because they are basic opens of `Proj` (`Proj.isAffineOpen_basicOpen`), and
affineness is preserved by preimage along the isomorphism `φ`.

This is the situation route (a) is in: `X = 𝕸(𝒫,δ)` is affine and the universal curve upstairs
is the pullback of the bootstrap object's explicit projective model (T-E15; the `VariableChange`
presentation of the `G`-action is T-W7.1b). Only surjectivity of `z` on points is needed — no
affineness of `X`, no properness, no `LocallyWeierstrass` gluing. -/
theorem exists_charts_of_globalModel {R : Type u} [CommRing R] {C : EllipticCurveGeom X}
    {W : WeierstrassCurve R} (φ : C.E ≅ projModel W)
    {z : X ⟶ Spec (CommRingCat.of R)} (hz : Function.Surjective z.base)
    (hzero : C.zero ≫ φ.hom = z ≫ projModelZero W) :
    ∃ U₀ U₁ : (C.E).Opens, IsAffineOpen U₀ ∧ IsAffineOpen U₁ ∧
      (∀ x : X, C.zero.base x ∈ U₀) ∧
      (∀ e : C.E, e ∉ Set.range C.zero.base → e ∈ U₁) := by
  refine ⟨φ.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))),
    φ.hom ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))),
    ?_, ?_, ?_, ?_⟩
  · exact (Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 1)
      one_pos).preimage_of_isIso φ.hom
  · exact (Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2)
      one_pos).preimage_of_isIso φ.hom
  · intro x
    have hmem : z.base x ∈ (projModelZero W) ⁻¹ᵁ (Proj.basicOpen
        (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) := by
      rw [projModelZero_preimage_yChart W]; trivial
    have hx : φ.hom.base (C.zero.base x) = (projModelZero W).base (z.base x) :=
      congrArg (fun f : X ⟶ projModel W => f.base x) hzero
    show φ.hom.base (C.zero.base x) ∈ (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))
    rw [hx]
    exact hmem
  · intro e he
    by_contra hcon
    have hcon' : φ.hom.base e ∉ Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) := hcon
    obtain ⟨r, hr⟩ := mem_range_zero_of_not_mem_zChart hcon'
    obtain ⟨x, rfl⟩ := hz r
    refine he ⟨x, ?_⟩
    have hx : φ.hom.base (C.zero.base x) = (projModelZero W).base (z.base x) :=
      congrArg (fun f : X ⟶ projModel W => f.base x) hzero
    exact (Scheme.homeoOfIso φ).injective (hx.trans (hr.trans rfl))

/-- **([a2], PROVEN end-to-end for a globally-modelled curve)** Composing
`exists_charts_of_globalModel` with `orbit_mem_isAffineOpen_of_charts` and
`exists_isStableOpen_isAffineOpen_of_orbit`: a free action lifted to a curve with a global
projective Weierstrass model admits the **`G`-stable affine atlas** that `SchemeAction.quotient`
consumes. `E/G` therefore exists. -/
theorem exists_isStableOpen_isAffineOpen_of_globalModel [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE) {R : Type u} [CommRing R] {W : WeierstrassCurve R}
    (φ : C.E ≅ projModel W) {z : X ⟶ Spec (CommRingCat.of R)}
    (hz : Function.Surjective z.base) (hzero : C.zero ≫ φ.hom = z ≫ projModelZero W)
    (e : C.E) :
    ∃ V : (C.E).Opens, σE.IsStableOpen V ∧ IsAffineOpen V ∧ e ∈ V := by
  obtain ⟨U₀, U₁, h0, h1, hz0, hz1⟩ := exists_charts_of_globalModel φ hz hzero
  exact exists_isStableOpen_isAffineOpen_of_orbit
    (fun e' => orbit_mem_isAffineOpen_of_charts hact h0 h1 hz0 hz1 e') e

/-! ### [a5-P2′] The global-model transport: `IsCurveAction` ⇝ the `VariableChange` cocycle

Rule-5 note ([OWNER-FLW], v10.94): these lemmas stay strictly on the Weierstrass-model side —
they transport a *given* global model along the action; the fibrewise ⟷ locally-Weierstrass
comparison is owner-reserved and never used or duplicated here. -/

/-- The whole space is a stable open. -/
theorem isStableOpen_top (σ : SchemeAction G X) : σ.IsStableOpen (⊤ : X.Opens) :=
  fun _ => rfl

/-- The global-sections action, as `Spec.map` data: `toRingHom` of `gammaMulSemiringAction ⊤` is
the `appTop` of the geometric action. -/
theorem ofHom_toRingHom_eq_appTop [IsAffine X] (σ : SchemeAction G X) (g : G) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g) = (σ.hom g).appTop := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  ext s
  show ((σ.hom g).appLE ⊤ ⊤ ((isStableOpen_top σ).le_preimage g)).hom s
    = ((σ.hom g).app ⊤).hom s
  exact congrArg (fun h => CommRingCat.Hom.hom h s) (Scheme.Hom.appLE_eq_app (σ.hom g))

/-- Base-matching over the whole affine: under `X ≅ Spec Γ(X,⊤)`, the geometric action `σ.hom g`
is `Spec` of the global-sections action. -/
theorem hom_isoSpec_toRingHom [IsAffine X] (σ : SchemeAction G X) (g : G) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    σ.hom g ≫ X.isoSpec.hom
      = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g)) := by
  rw [ofHom_toRingHom_eq_appTop, Scheme.isoSpec_hom_naturality]

/-- **([a5-P2′], cartesian leg)** The transported action `(σE.transport φ).hom g` on
`projModel W₀` is cartesian over `Spec (toRingHom g)`: `IsPullback.of_iso` of
`IsCurveAction.cartesian g` along `φ`/`isoSpec`, base-matched by `hom_isoSpec_toRingHom`. -/
theorem isPullback_transport_globalModel [IsAffine X] (hact : IsCurveAction σ C σE)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hπ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom) (g : G) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    IsPullback ((σE.transport φ).hom g) (projModelπ W₀) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g))) := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  refine (hact.cartesian g).of_iso φ φ X.isoSpec X.isoSpec ?_ hπ.symm hπ.symm ?_
  · rw [SchemeAction.transport_hom, Iso.hom_inv_id_assoc]
  · exact hom_isoSpec_toRingHom σ g

/-- **([a5-P2′], zero leg)** The transported action is zero-equivariant over
`Spec (toRingHom g)`. -/
theorem projModelZero_transport_globalModel [IsAffine X] (hact : IsCurveAction σ C σE)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hzero : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) (g : G) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    projModelZero W₀ ≫ (σE.transport φ).hom g
      = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g))
          ≫ projModelZero W₀ := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  have hz' : projModelZero W₀ = X.isoSpec.inv ≫ C.zero ≫ φ.hom := by
    rw [hzero, Iso.inv_hom_id_assoc]
  rw [hz', SchemeAction.transport_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (hact.zero_equivariant g), hzero,
    reassoc_of% (hom_isoSpec_toRingHom σ g)]
  simp only [Iso.inv_hom_id_assoc]

/-- **([a5-P2′], the GLOBAL-MODEL transport)** If the curve carries a global Weierstrass model
`φ : C.E ≅ projModel W₀` over the affine base (`W₀` over `Γ(X,⊤)`), compatible with `π` and the
zero sections, then the geometric `G`-action transports to the raw action family on `projModel W₀`
that `isVCocycle_of_curveActionFamily` consumes: `act g = φ⁻¹ ≫ σE g ≫ φ`, multiplicative,
cartesian over `Spec (toRingHom g)` (`IsPullback.of_iso` of `IsCurveAction.cartesian` along
`φ`/`isoSpec`, base-matched by `hom_isoSpec_toRingHom`), and zero-equivariant. -/
theorem curveAction_actionFamily_of_globalModel [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hπ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzero : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∃ act : G → (projModel W₀ ⟶ projModel W₀),
      (∀ g h, act (g * h) = act g ≫ act h) ∧
      (∀ g, IsPullback (act g) (projModelπ W₀) (projModelπ W₀)
        (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g)))) ∧
      (∀ g, projModelZero W₀ ≫ act g
        = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g))
            ≫ projModelZero W₀) := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  exact ⟨(σE.transport φ).hom, (σE.transport φ).hom_mul,
    fun g => isPullback_transport_globalModel hact W₀ φ hπ g,
    fun g => projModelZero_transport_globalModel hact W₀ φ hzero g⟩

open WeierstrassCurve in
/-- **([a5-ii∘P2′], the cocycle from a global model)** `IsCurveAction` + a compatible global
Weierstrass model over the affine base yield the `VariableChange` cocycle over `Γ(X,⊤)` that
`exists_invariant_descent` consumes. Chains the global transport into
`isVCocycle_of_curveActionFamily` (the a5-ii capstone). -/
theorem exists_cocycle_of_globalModel [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hπ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzero : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∃ Cvc : G → VariableChange Γ(X, ⊤), IsVCocycle Cvc ∧
      ∀ g, Cvc g • (W₀.map (MulSemiringAction.toRingHom G Γ(X, ⊤) g)) = W₀ := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  obtain ⟨act, hmul, hcart, hz⟩ :=
    curveAction_actionFamily_of_globalModel hact W₀ φ hπ hzero
  exact isVCocycle_of_curveActionFamily W₀ act hmul hcart hz

open WeierstrassCurve in
/-- **([a5-ii∘P2′], primed)** The cocycle from a global model, with the `hΨ` link against the
concrete transported action `(σE.transport φ).hom` — the form the fppf-comparison's
`G`-invariance consumes. -/
theorem exists_cocycle_of_globalModel' [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hπ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzero : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∃ (Cvc : G → VariableChange ↑Γ(X, ⊤))
      (hCvc : ∀ g, Cvc g • (W₀.map (MulSemiringAction.toRingHom G ↑Γ(X, ⊤) g)) = W₀),
      IsVCocycle Cvc ∧
      ∀ g, (projModelVCIso (Cvc g) (W₀.map (MulSemiringAction.toRingHom G ↑Γ(X, ⊤) g))).hom
          ≫ projModelBaseChange (MulSemiringAction.toRingHom G ↑Γ(X, ⊤) g) W₀
        = eqToHom (congrArg projModel (hCvc g)) ≫ (σE.transport φ).hom g := by
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  exact isVCocycle_of_curveActionFamily' W₀ (σE.transport φ).hom (σE.transport φ).hom_mul
    (fun g => isPullback_transport_globalModel hact W₀ φ hπ g)
    (fun g => projModelZero_transport_globalModel hact W₀ φ hzero g)

/-! ### The route-(a) descent theorem (leaves `[a3]`–`[a5]`) -/

/-- **([a3-i], PROVEN)** The structure morphism and the zero section descend to the quotient,
and remain a section: `E/G ⟶ X/G` and `X/G ⟶ E/G` with `zero' ≫ π' = 𝟙`.

Both are instances of the universal property `existsUnique_quotientπ_lift` (T-Q5, proven): the
composites `E → X → X/G` and `X → E → E/G` are `G`-invariant by `IsCurveAction.π_equivariant`
resp. `IsCurveAction.zero_equivariant` together with `hom_quotientπ`. That `zero'` is a section
of `π'` is then uniqueness of descent (`quotientπ_hom_ext`) applied to `C.zero_π`.

No new theory: the geometric content of the KM engine's descent step is already discharged by
the quotient's universal property. What remains of `[a3]` is the *cartesianness* of the square,
and of `[a4]`/`[a5]` the descent of `proper`/`smooth`/`localModel`. -/
theorem exists_quotient_π_zero [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e) :
    ∃ (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
      (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa),
      σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem ∧
        σ.quotientπ V hVs hVa hVmem ≫ zero' =
          C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem ∧
        zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa) := by
  obtain ⟨π', hπ', -⟩ := σE.existsUnique_quotientπ_lift VE hVEs hVEa hVEmem
    (C.π ≫ σ.quotientπ V hVs hVa hVmem) (fun γ => by
      rw [← Category.assoc, hact.π_equivariant γ, Category.assoc, σ.hom_quotientπ])
  obtain ⟨zero', hzero', -⟩ := σ.existsUnique_quotientπ_lift V hVs hVa hVmem
    (C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) (fun γ => by
      rw [← Category.assoc, ← hact.zero_equivariant γ, Category.assoc, σE.hom_quotientπ])
  refine ⟨π', zero', hπ', hzero', ?_⟩
  refine σ.quotientπ_hom_ext V hVs hVa hVmem _ _ ?_
  rw [Category.comp_id, ← Category.assoc, hzero', Category.assoc, hπ', ← Category.assoc,
    C.zero_π, Category.id_comp]



/-- **([a3-ii-chart])** The cartesian square, **on one affine chart**: for a `G`-stable affine
open `W ⊆ E`, `W ≅ (W/G) ×_{X/G} X`.

Plan (terminating in a proof, and *purely affine*): `W = Spec Γ(W)`, `W/G = Spec Γ(W)ᴳ`,
`X = Spec Γ(X)` (route (a)'s `X` is affine, so its atlas is the constant `⊤`) and
`X/G = Spec Γ(X)ᴳ`. The structure morphism makes `Γ(W)` a `Γ(X)`-algebra, and `π`-equivariance
(`IsCurveAction.π_equivariant`) makes the `G`-action on it **semilinear**. Then
`MulSemiringAction.isPullback_Spec_fixedPoints` (PROVEN, from Galois descent of semilinear
modules) says exactly that the square is cartesian; the four corners are matched to the
geometric ones by `IsAffineOpen.isoSpec` and `quotientChartIso`.

Freeness of the algebra action is `SchemeAction.isFreeAlgebraAction_of_free` (PROVEN), fed by
the geometric freeness of the action on `E` (`simulSchemeActionTotal_free_of_rigid`). -/
theorem isPullback_chart [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (hπ' : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (i : C.E) :
    IsPullback
      (σE.localQuotientπ (hVEs i) (hVEa i) ≫ (σE.quotientChartIso VE hVEs hVEa i).hom)
      ((VE i).ι ≫ C.π)
      ((σE.quotientChart VE hVEs hVEa i).ι ≫ π')
      (σ.quotientπ V hVs hVa hVmem) := by
  classical
  set x₀ : ↥X := C.π.base i with hx₀
  have hle : VE i ≤ C.π ⁻¹ᵁ V x₀ := by rw [hVtop x₀]; exact le_top
  -- the affine core square (∃ induced quotient map q')
  obtain ⟨q', hcore⟩ :=
    isPullback_localQuotientπ hact (hVs x₀) (hVa x₀) (hVEs i) (hVEa i) hle hfree
  -- σE is free too (from σ free + π-equivariance)
  have hfreeE : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ C.E),
      t ≫ σE.hom γ = t → IsEmpty T := by
    intro γ hγ T t ht
    refine hfree γ hγ T (t ≫ C.π) ?_
    rw [Category.assoc, ← hact.π_equivariant γ, ← Category.assoc, ht]
  -- corner isos
  set e₃ := Scheme.isoOfEq X (hVtop x₀) ≪≫ Scheme.topIso X with he₃
  set e₄ := σ.quotientChartIso V hVs hVa x₀ ≪≫
      (Scheme.isoOfEq (σ.quotient V hVs hVa)
          (σ.quotientChart_eq_top V hVs hVa hVmem x₀ (hVtop x₀)) ≪≫
        Scheme.topIso (σ.quotient V hVs hVa)) with he₄
  -- e₃.hom = (V x₀).ι
  have he₃hom : e₃.hom = (V x₀).ι := by
    simp only [he₃, Iso.trans_hom, Scheme.topIso_hom, Scheme.isoOfEq_hom_ι]
  -- e₄.hom = chartIso_X.hom ≫ chart_X.ι
  have he₄hom : e₄.hom = (σ.quotientChartIso V hVs hVa x₀).hom ≫
      (σ.quotientChart V hVs hVa x₀).ι := by
    simp only [he₄, Iso.trans_hom, Category.assoc, Scheme.topIso_hom, Scheme.isoOfEq_hom_ι]
  -- assemble by transport of the affine core
  refine hcore.of_iso (Iso.refl _) (σE.quotientChartIso VE hVEs hVEa i) e₃ e₄ ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
  · rw [Iso.refl_hom, Category.id_comp, he₃hom]
    exact Scheme.Hom.resLE_comp_ι C.π hle
  · -- commf: q' ≫ e₄.hom = chartIso_W.hom ≫ (chart_W.ι ≫ π'), by epi-cancelling localQuotientπ_W
    haveI : Epi (σE.localQuotientπ (hVEs i) (hVEa i)) :=
      σE.epi_localQuotientπ (hVEs i) (hVEa i) hfreeE
    have hL : σE.localQuotientπ (hVEs i) (hVEa i) ≫ q' ≫ e₄.hom =
        (VE i).ι ≫ C.π ≫ σ.quotientπ V hVs hVa hVmem := by
      rw [← Category.assoc, hcore.w, Category.assoc, he₄hom,
        σ.localQuotientπ_quotientChartIso V hVs hVa hVmem x₀, ← Category.assoc,
        Scheme.Hom.resLE_comp_ι C.π hle, Category.assoc]
    have hR : σE.localQuotientπ (hVEs i) (hVEa i) ≫ (σE.quotientChartIso VE hVEs hVEa i).hom ≫
        (σE.quotientChart VE hVEs hVEa i).ι ≫ π' =
        (VE i).ι ≫ C.π ≫ σ.quotientπ V hVs hVa hVmem := by
      rw [← Category.assoc (σE.quotientChartIso VE hVEs hVEa i).hom, ← Category.assoc,
        σE.localQuotientπ_quotientChartIso VE hVEs hVEa hVEmem i, Category.assoc, hπ']
    rw [← cancel_epi (σE.localQuotientπ (hVEs i) (hVEa i)), hL, hR]
  · -- commg: localQuotientπ_U ≫ e₄.hom = e₃.hom ≫ quotientπ_X
    rw [he₄hom, he₃hom]
    exact σ.localQuotientπ_quotientChartIso V hVs hVa hVmem x₀

/-- **([a3-ii], the square is cartesian)** `E ≅ (E/G) ×_{X/G} X`.

**PROVEN**, modulo the affine chart square `isPullback_chart`: cartesianness is Zariski-local at
the target (`isPullback_of_iSup_eq_top`, a mathlib gap filled in
`ForMathlib/PullbackLocalAtTarget.lean`), the quotient charts of `E/G` cover it
(`iSup_quotientChart_eq_top`), and over the `i`-th chart the projection `E ⟶ E/G` *is* the local
quotient `VE i ⟶ Spec Γ(E, VE i)ᴳ` (`morphismRestrict_quotientπ`).

This replaces KM's appeal to SGA I Exp. VIII 7.8 (effective fppf descent of projective schemes,
absent from mathlib) by a pushout of rings. -/
theorem isPullback_quotientπ [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (hπ' : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem) :
    IsPullback (σE.quotientπ VE hVEs hVEa hVEmem) C.π π'
      (σ.quotientπ V hVs hVa hVmem) := by
  refine isPullback_of_iSup_eq_top hπ' (σE.quotientChart VE hVEs hVEa)
    (σE.iSup_quotientChart_eq_top VE hVEs hVEa) fun i => ?_
  have hW : σE.quotientπ VE hVEs hVEa hVEmem ⁻¹ᵁ σE.quotientChart VE hVEs hVEa i = VE i :=
    σE.quotientπ_preimage_quotientChart VE hVEs hVEa hVEmem i
  refine (isPullback_chart hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ' i).of_iso
    ((C.E).isoOfEq hW).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      σE.morphismRestrict_quotientπ VE hVEs hVEa hVEmem i, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
      Scheme.isoOfEq_inv_ι]

/-- **([a4], properness — PROVEN, from the local model)** A morphism admitting a Zariski-local
Weierstrass model is **proper**.

`IsProper` is Zariski-local at the target (mathlib), and over each affine `U` of the base the
restriction is, up to isomorphism, `projModelπ W`, which is proper (`projModelπ_isProper`).

This is the route `[a4]` should take: mathlib descends `Smooth`, `UniversallyClosed`,
`LocallyOfFiniteType` and `Etale` along fppf covers, but **not** `IsSeparated` and **not**
`SmoothOfRelativeDimension n` — so descending `IsProper`/`smooth` along `X ⟶ X/G` would open two
fresh mathlib gaps. Deriving them from `localModel` (leaf `[a5]`) opens none. -/
theorem isProper_of_locallyWeierstrass {S E' : Scheme.{u}} {p : E' ⟶ S} {z : S ⟶ E'}
    {hz : z ≫ p = 𝟙 S} (hlw : LocallyWeierstrass p z hz) : IsProper p := by
  classical
  choose U hUmem W hW using hlw
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun s : S => (U s).1) ?_ ?_
  · refine top_le_iff.mp fun s _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hUmem s⟩
  · intro s
    obtain ⟨-, e, he₁, -⟩ := hW s
    have hres : p ∣_ (U s).1 =
        (pullbackRestrictIsoRestrict p (U s).1).inv ≫ pullback.snd p (U s).1.ι := rfl
    have hsnd : pullback.snd p (U s).1.ι = e.hom ≫ projModelπ (W s) ≫ (U s).2.isoSpec.inv := by
      rw [← Category.assoc, he₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hres, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper), hsnd,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsProper),
      MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
    exact projModelπ_isProper (W s)

/-- **([a4]/[a5], smoothness from the local model — LEAF, waits on T-A3)** A morphism admitting a
Zariski-local Weierstrass model is **smooth of relative dimension 1**.

Same Zariski-local-at-target argument as `isProper_of_locallyWeierstrass`: over each affine chart
the morphism is `projModelπ W` up to isomorphism, and `SmoothOfRelativeDimension 1 (projModelπ W)`
is **T-A3** (model smooth ⟺ discriminant a unit, the chartwise Jacobian analysis; owner:
beastmode-A). `SmoothOfRelativeDimension n` is `IsZariskiLocalAtTarget`
(`smoothOfRelativeDimension_isZariskiLocalAtTarget`), so this reduces exactly to T-A3.

This is the sole leaf standing between the engine and smoothness of the quotient curve. -/
theorem smoothOfRelativeDimension_of_locallyWeierstrass {S E' : Scheme.{u}} {p : E' ⟶ S}
    {z : S ⟶ E'} {hz : z ≫ p = 𝟙 S} (hlw : LocallyWeierstrass p z hz) :
    SmoothOfRelativeDimension 1 p := by
  classical
  choose U hUmem W hW using hlw
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun s : S => (U s).1) ?_ ?_
  · refine top_le_iff.mp fun s _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hUmem s⟩
  · intro s
    obtain ⟨hell, e, he₁, -⟩ := hW s
    haveI := hell
    have hres : p ∣_ (U s).1 =
        (pullbackRestrictIsoRestrict p (U s).1).inv ≫ pullback.snd p (U s).1.ι := rfl
    have hsnd : pullback.snd p (U s).1.ι = e.hom ≫ projModelπ (W s) ≫ (U s).2.isoSpec.inv := by
      rw [← Category.assoc, he₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hres, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1),
      hsnd, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1),
      MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
    exact projModel_smooth (W s)

end RouteA

/-! ### The seam: KM's action *is* a `RouteA.IsCurveAction` -/

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- **([a1] ⟹ route (a)'s hypotheses)** The KM 4.7 action of `G` on the universal curve over
`𝕸(𝒫,δ)` satisfies the three axioms of `RouteA.IsCurveAction`. This is the seam between
`Moduli/QuotientProblem.lean` (the engine) and this file (the descent): everything route (a)
needs of the KM cocycle is already proven in `[a1]`. -/
theorem isCurveAction_simulSchemeActionTotal (P Q : ModuliProblem R) {G : Type u} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) :
    RouteA.IsCurveAction (P.simulSchemeAction Q φ rM) XM.curve.toEllipticCurveGeom
      (P.simulSchemeActionTotal Q φ rM) where
  π_equivariant := P.simulSchemeActionTotal_π Q φ rM
  zero_equivariant := P.simulSchemeActionTotal_zero Q φ rM
  cartesian := P.simulSchemeActionTotal_isPullback Q φ rM

/-- **([a1] ⟹ route (a)'s freeness hypothesis)** For a rigid `𝒫` with a finite étale
`G`-torsor rigidifier `δ`, the KM action on the base of `𝕸(𝒫,δ)` is free in the shape
`exists_ellipticCurveGeom_quotient` consumes. -/
theorem free_simulSchemeAction (P Q : ModuliProblem R) {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    (hrig : P.Rigid) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X)) :
    ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ XM.base),
      t ≫ (P.simulSchemeAction Q φ rM).hom γ = t → IsEmpty T :=
  fun γ hγ T t ht => P.simulSchemeAction_free_of_rigid Q φ rM hrig htors γ hγ T t ht

end ModuliProblem

end ModularCurves

/-! ### [a5-W5a] The quotient identification under a `⊤`-atlas (generic `SchemeAction` layer) -/

namespace AlgebraicGeometry.SchemeAction
variable {G : Type u} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

/-- Transport of the fixed subalgebra along a `G`-equivariant ring equivalence. -/
private def fixedPointsCongr {A B : Type u} [CommRing A] [CommRing B]
    [MulSemiringAction G A] [MulSemiringAction G B]
    (e : A ≃+* B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    FixedPoints.subalgebra ℤ A G ≃+* FixedPoints.subalgebra ℤ B G where
  toFun a := ⟨e a.1, fun g => by rw [← he g a.1, a.2 g]⟩
  invFun b := ⟨e.symm b.1, fun g => e.injective (by
    rw [he g (e.symm b.1), e.apply_symm_apply]; exact b.2 g)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.1)
  right_inv b := Subtype.ext (e.apply_symm_apply b.1)
  map_mul' a b := Subtype.ext (map_mul e a.1 b.1)
  map_add' a b := Subtype.ext (map_add e a.1 b.1)

/-- The restriction map along `W ≤ U` between stable opens is `G`-equivariant for the
section-ring actions (`appLE` naturality). -/
private theorem gamma_res_smul {U W : X.Opens} (hU : σ.IsStableOpen U)
    (hW : σ.IsStableOpen W) (hWU : W ≤ U) (g : G) (s : ↑Γ(X, U)) :
    letI := σ.gammaMulSemiringAction hU
    letI := σ.gammaMulSemiringAction hW
    (X.presheaf.map (homOfLE hWU).op).hom (g • s)
      = g • (X.presheaf.map (homOfLE hWU).op).hom s := by
  letI := σ.gammaMulSemiringAction hU
  letI := σ.gammaMulSemiringAction hW
  have hcomp : (σ.hom g).appLE U U (hU.le_preimage g) ≫ X.presheaf.map (homOfLE hWU).op
      = X.presheaf.map (homOfLE hWU).op ≫ (σ.hom g).appLE W W (hW.le_preimage g) := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  show (X.presheaf.map (homOfLE hWU).op).hom
      (((σ.hom g).appLE U U (hU.le_preimage g)).hom s)
    = ((σ.hom g).appLE W W (hW.le_preimage g)).hom ((X.presheaf.map (homOfLE hWU).op).hom s)
  exact congrArg (fun f : Γ(X, U) ⟶ Γ(X, W) => f.hom s) hcomp

/-- **([a5-W5a], the quotient identification)** Under a `⊤`-atlas (`hVtop`), the scheme quotient
is `Spec` of the global invariants, compatibly with the quotient projection. -/
theorem exists_quotientIsoSpec_top [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤) (x₀ : X) :
    letI := σ.gammaMulSemiringAction (ModularCurves.RouteA.isStableOpen_top σ)
    ∃ qiso : σ.quotient V hVs hVa ≅
        Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G)),
      σ.quotientπ V hVs hVa hVmem ≫ qiso.hom
        = X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := by
  letI := σ.gammaMulSemiringAction (ModularCurves.RouteA.isStableOpen_top σ)
  letI := σ.gammaMulSemiringAction (hVs x₀)
  have hle : V x₀ ≤ ⊤ := le_top
  -- (1) the `G`-invariant global morphism descends through the quotient
  have hFinv : ∀ g : G, σ.hom g ≫ X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ
      = X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := fun g => by
    rw [← Category.assoc, ModularCurves.RouteA.hom_isoSpec_toRingHom σ g, Category.assoc,
      show Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, ⊤) g))
          = specSMul g from rfl,
      specSMul_invariantsπ]
  obtain ⟨q, hq⟩ := σ.exists_quotientπ_lift V hVs hVa hVmem
    (X.isoSpec.hom ≫ invariantsπ G ↑Γ(X, ⊤) ℤ) hFinv
  -- (2) the restriction `Γ(X,⊤) ⟶ Γ(X, V x₀)` is a `G`-equivariant ring isomorphism
  haveI : IsIso (homOfLE hle) := ⟨eqToHom (hVtop x₀).symm, rfl, rfl⟩
  let eρ : ↑Γ(X, ⊤) ≃+* ↑Γ(X, V x₀) :=
    (asIso (X.presheaf.map (homOfLE hle).op)).commRingCatIsoToRingEquiv
  have heρ : ∀ (g : G) (s : ↑Γ(X, ⊤)), eρ (g • s) = g • eρ s := fun g s =>
    σ.gamma_res_smul (ModularCurves.RouteA.isStableOpen_top σ) (hVs x₀) hle g s
  -- (3) the induced iso of fixed rings and its `Spec`-square against the invariants maps
  let eG : FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G ≃+* FixedPoints.subalgebra ℤ ↑Γ(X, V x₀) G :=
    fixedPointsCongr eρ heρ
  have hring : CommRingCat.ofHom eG.toRingHom
        ≫ CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(X, V x₀) G) ↑Γ(X, V x₀))
      = CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G) ↑Γ(X, ⊤))
        ≫ X.presheaf.map (homOfLE hle).op := by
    ext a
    rfl
  have hsq : invariantsπ G ↑Γ(X, V x₀) ℤ ≫ Spec.map (CommRingCat.ofHom eG.toRingHom)
      = Spec.map (X.presheaf.map (homOfLE hle).op) ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  -- (4) the geometric bridge between the two affine identifications
  have hbridge : (hVa x₀).isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE hle).op)
      = (V x₀).ι ≫ X.isoSpec.hom := by
    rw [← cancel_mono X.isoSpec.inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.map_fromSpec _ (hVa x₀) ((homOfLE hle).op),
      IsAffineOpen.isoSpec_hom_fromSpec]
  -- (5) the chart inclusion `κ` is an isomorphism (the `⊤`-chart is the whole quotient) …
  haveI hι : IsIso (σ.quotientChart V hVs hVa x₀).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (by rw [Scheme.Opens.opensRange_ι, σ.quotientChart_eq_top V hVs hVa hVmem x₀ (hVtop x₀)])
  -- (6) … and `κ ≫ q` is `Spec` of the fixed-ring iso, so `q` is an isomorphism
  have hLQ : σ.localQuotientπ (hVs x₀) (hVa x₀)
      ≫ ((σ.quotientChartIso V hVs hVa x₀).hom ≫ (σ.quotientChart V hVs hVa x₀).ι) ≫ q
      = (hVa x₀).isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE hle).op)
        ≫ invariantsπ G ↑Γ(X, ⊤) ℤ := by
    rw [← Category.assoc, σ.localQuotientπ_quotientChartIso V hVs hVa hVmem x₀,
      Category.assoc, hq, ← Category.assoc, ← hbridge, Category.assoc]
  have hκq : ((σ.quotientChartIso V hVs hVa x₀).hom ≫ (σ.quotientChart V hVs hVa x₀).ι) ≫ q
      = Spec.map (CommRingCat.ofHom eG.toRingHom) := by
    refine invariantsπ_hom_ext G ↑Γ(X, V x₀) ℤ _ _ ?_
    rw [hsq, ← cancel_epi (hVa x₀).isoSpec.hom, ← Category.assoc,
      ← σ.localQuotientπ_eq (hVs x₀) (hVa x₀)]
    exact hLQ
  haveI : IsIso (CommRingCat.ofHom eG.toRingHom) :=
    ⟨CommRingCat.ofHom eG.symm.toRingHom,
      by ext a; exact congrArg Subtype.val (eG.symm_apply_apply a),
      by ext a; exact congrArg Subtype.val (eG.apply_symm_apply a)⟩
  haveI : IsIso (((σ.quotientChartIso V hVs hVa x₀).hom
      ≫ (σ.quotientChart V hVs hVa x₀).ι) ≫ q) := by
    rw [hκq]; infer_instance
  haveI : IsIso q := IsIso.of_isIso_comp_left
    ((σ.quotientChartIso V hVs hVa x₀).hom ≫ (σ.quotientChart V hVs hVa x₀).ι) q
  exact ⟨asIso q, hq⟩

end AlgebraicGeometry.SchemeAction

/-! ### [a5-W6] The final assembly (Phase A): the quotient's local Weierstrass model -/

namespace ModularCurves.RouteA

open WeierstrassCurve
open scoped Pointwise

variable {G : Type u} [Group G] {X : Scheme.{u}} {C : EllipticCurveGeom X}
  {σ : SchemeAction G X} {σE : SchemeAction G C.E}

/-- The localized action `MulSemiringAction.awayHom` fixes the image of the localized
invariants `fixedAwayMap a : (Aᴳ)_a ⟶ A_a` (checked on `algebraMap`-generators). -/
private theorem awayHom_comp_fixedAwayMap {A : Type u} [CommRing A] [MulSemiringAction G A]
    (a : FixedPoints.subring A G) (g : G) :
    (MulSemiringAction.awayHom (fun g' : G => a.2 g') g).comp (fixedAwayMap a)
      = fixedAwayMap a := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun v => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [fixedAwayMap_algebraMap, MulSemiringAction.awayHom_algebraMap, v.2 g]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Mixed-ring functoriality of the projective-model base change (the three-ring form of
`projModelBaseChange_comp`). -/
private theorem projModelBaseChange_comp₃ {S₀ S₁ S₂ : Type u} [CommRing S₀] [CommRing S₁]
    [CommRing S₂] (F : S₁ →+* S₂) (φ : S₀ →+* S₁) (V : WeierstrassCurve S₀) :
    projModelBaseChange (F.comp φ) V
      = projModelBaseChange F (V.map φ) ≫ projModelBaseChange φ V := by
  have bmk : ∀ {T T' : Type u} [CommRing T] [CommRing T'] (ψ : T →+* T')
      (V' : WeierstrassCurve T) (p : MvPolynomial (Fin 3) T),
      baseChangeGradedHom ψ V' (Ideal.Quotient.mk (projIdeal V').toIdeal p)
        = Ideal.Quotient.mk (projIdeal (V'.map ψ)).toIdeal (MvPolynomial.map ψ p) :=
    fun ψ V' p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded ψ) (projIdeal V')
      (projIdeal (V'.map ψ)) (projIdeal_le_comap ψ V') p
  have hgraded : baseChangeGradedHom (F.comp φ) V
      = (baseChangeGradedHom F (V.map φ)).comp (baseChangeGradedHom φ V) := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show baseChangeGradedHom (F.comp φ) V (Ideal.Quotient.mk _ p)
      = baseChangeGradedHom F (V.map φ) (baseChangeGradedHom φ V (Ideal.Quotient.mk _ p))
    rw [bmk, bmk, bmk]
    exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_map φ F p).symm
  have key := Proj.map_comp (baseChangeGradedHom φ V) (baseChangeGradedHom F (V.map φ))
    (baseChangeGradedHom_irrelevant_le φ V) (baseChangeGradedHom_irrelevant_le F (V.map φ))
  refine Eq.trans ?_ key
  show Proj.map (baseChangeGradedHom (F.comp φ) V)
      (baseChangeGradedHom_irrelevant_le (F.comp φ) V)
    = Proj.map ((baseChangeGradedHom F (V.map φ)).comp (baseChangeGradedHom φ V)) _
  congr 1

/-- Naturality of `projModelBaseChange φ` under an equality of source curves
(two-ring form). -/
private theorem projModelBaseChange_natEq₂ {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (φ : S₀ →+* S₁) {V1 V2 : WeierstrassCurve S₀} (hV : V1 = V2) :
    projModelBaseChange φ V1 ≫ eqToHom (congrArg projModel hV)
      = eqToHom (congrArg projModel (congrArg (WeierstrassCurve.map · φ) hV))
        ≫ projModelBaseChange φ V2 := by
  subst hV
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Naturality of `(projModelVCIso C V).hom` under equalities of the variable change and the
curve. -/
private theorem projModelVCIso_natEq₂ {S : Type u} [CommRing S] {C1 C2 : VariableChange S}
    {V1 V2 : WeierstrassCurve S} (hC : C1 = C2) (hV : V1 = V2) :
    (projModelVCIso C1 V1).hom ≫ eqToHom (congrArg projModel hV)
      = eqToHom (congrArg projModel (by rw [hC, hV])) ≫ (projModelVCIso C2 V2).hom := by
  subst hC; subst hV
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Transport of `(projModelVCIso C V).hom` along an equality of variable changes. -/
private theorem projModelVCIso_congr₂ {S : Type u} [CommRing S] {C1 C2 : VariableChange S}
    (hC : C1 = C2) (V : WeierstrassCurve S) :
    (projModelVCIso C1 V).hom
      = eqToHom (congrArg projModel (by rw [hC])) ≫ (projModelVCIso C2 V).hom := by
  subst hC; simp

/-- Base-change naturality of the change-of-variables iso, for an arbitrary ring hom `ρ`
(the two-ring form of `projModelVCIso_map_hom`). -/
private theorem projModelVCIso_map₂ {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (ρ : S₀ →+* S₁) (C : VariableChange S₀) (V : WeierstrassCurve S₀) :
    projModelBaseChange ρ (C • V) ≫ (projModelVCIso C V).hom =
      eqToHom (by rw [map_variableChange]) ≫
        (projModelVCIso (C.map ρ) (V.map ρ)).hom ≫ projModelBaseChange ρ V := by
  letI : Algebra S₀ S₁ := ρ.toAlgebra
  have h := projModelVCIso_map (R' := S₁) C V
  have he : (algebraMap S₀ S₁ : S₀ →+* S₁) = ρ := ρ.algebraMap_toAlgebra
  rw [he] at h
  exact h

/-- Two-ring form of `isPullback_projModelBaseChange` (for an arbitrary ring hom, via
`RingHom.toAlgebra`). -/
private theorem isPullback_projModelBaseChange₂ {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (ρ : S₀ →+* S₁) (V : WeierstrassCurve S₀) :
    IsPullback (projModelBaseChange ρ V) (projModelπ (V.map ρ)) (projModelπ V)
      (Spec.map (CommRingCat.ofHom ρ)) := by
  letI : Algebra S₀ S₁ := ρ.toAlgebra
  have h := isPullback_projModelBaseChange (R := S₀) (R' := S₁) V
  have he : (algebraMap S₀ S₁ : S₀ →+* S₁) = ρ := ρ.algebraMap_toAlgebra
  rw [he] at h
  exact h

/-- Two-ring form of `projModelZero_baseChange`. -/
private theorem projModelZero_baseChange₂ {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (ρ : S₀ →+* S₁) (V : WeierstrassCurve S₀) :
    projModelZero (V.map ρ) ≫ projModelBaseChange ρ V
      = Spec.map (CommRingCat.ofHom ρ) ≫ projModelZero V := by
  letI : Algebra S₀ S₁ := ρ.toAlgebra
  have h := projModelZero_baseChange (R := S₀) (R' := S₁) V
  have he : (algebraMap S₀ S₁ : S₀ →+* S₁) = ρ := ρ.algebraMap_toAlgebra
  rw [he] at h
  exact h

/-- Two-ring form of `isIso_projModelBaseChange`. -/
private theorem isIso_projModelBaseChange₂ {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (ρ : S₀ →+* S₁) [IsIso (Spec.map (CommRingCat.ofHom ρ))] (V : WeierstrassCurve S₀) :
    IsIso (projModelBaseChange ρ V) := by
  have hP := isPullback_projModelBaseChange₂ ρ V
  rw [← hP.isoPullback_hom_fst]
  infer_instance

/-- Rearranged form of `projModelVCIso_map₂` with no leading `eqToHom`. -/
private theorem projModelVCIso_map₂' {S₀ S₁ : Type u} [CommRing S₀] [CommRing S₁]
    (ρ : S₀ →+* S₁) (C : VariableChange S₀) (V : WeierstrassCurve S₀) :
    (projModelVCIso (C.map ρ) (V.map ρ)).hom ≫ projModelBaseChange ρ V
      = eqToHom (congrArg projModel (map_variableChange (W := V) (φ := ρ) (C := C)))
        ≫ projModelBaseChange ρ (C • V) ≫ (projModelVCIso C V).hom := by
  rw [projModelVCIso_map₂ ρ C V, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

/-- **The key base-change compatibility of the localized action datum.** If `act` is the
`Ψ`-composite of the cocycle value `CA` over `A` and `CR = CA.map ρ` is its localization,
then the localized `Ψ`-composite commutes with `projModelBaseChange ρ` into `act`. -/
private theorem actLoc_baseChange {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)
    (τA : A →+* A) (τR : R →+* R) (hcomm : τR.comp ρ = ρ.comp τA)
    (W₀ : WeierstrassCurve A) (CA : VariableChange A) (CR : VariableChange R)
    (hCR : CR = CA.map ρ)
    (hCA : CA • (W₀.map τA) = W₀) (hCR' : CR • ((W₀.map ρ).map τR) = W₀.map ρ)
    (act : projModel W₀ ⟶ projModel W₀)
    (hΨA : (projModelVCIso CA (W₀.map τA)).hom ≫ projModelBaseChange τA W₀
      = eqToHom (congrArg projModel hCA) ≫ act) :
    (eqToHom (congrArg projModel hCR'.symm) ≫ (projModelVCIso CR ((W₀.map ρ).map τR)).hom
        ≫ projModelBaseChange τR (W₀.map ρ)) ≫ projModelBaseChange ρ W₀
      = projModelBaseChange ρ W₀ ≫ act := by
  have hVeq : (W₀.map ρ).map τR = (W₀.map τA).map ρ := by
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hcomm]
  have hbcc : ∀ {f f' : A →+* R} (p : f = f'),
      projModelBaseChange f W₀ = eqToHom (by rw [p]) ≫ projModelBaseChange f' W₀ := by
    intro f f' p
    subst p
    simp
  have hswap : projModelBaseChange τR (W₀.map ρ) ≫ projModelBaseChange ρ W₀
      = eqToHom (congrArg projModel hVeq) ≫ projModelBaseChange ρ (W₀.map τA)
        ≫ projModelBaseChange τA W₀ := by
    rw [← projModelBaseChange_comp₃ τR ρ W₀, ← projModelBaseChange_comp₃ ρ τA W₀,
      hbcc hcomm]
    congr 1
  simp only [Category.assoc]
  rw [hswap, projModelVCIso_congr₂ hCR ((W₀.map ρ).map τR)]
  simp only [Category.assoc]
  rw [reassoc_of% projModelVCIso_natEq₂ (rfl : CA.map ρ = CA.map ρ) hVeq,
    reassoc_of% projModelVCIso_map₂' ρ CA (W₀.map τA), hΨA,
    reassoc_of% projModelBaseChange_natEq₂ ρ hCA]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

open scoped Pointwise in
/-- **The localized action datum on the model of `W₀A ⊗ A_a`.** Packaged for the per-point
chart: an endomorphism `actR` of the localized model that (i) coequalizes into the
`descentComparison`, (ii) covers the given action `act g` through the base change to `A`,
and (iii) fixes the composite `projModelπ ≫ κ` for any `κ` fixed by the localized action. -/
private theorem exists_actLoc {A : Type u} [CommRing A] [MulSemiringAction G A]
    (a : FixedPoints.subring A G)
    [Algebra (Localization.Away a) (Localization.Away ((a : A)))]
    (halg : algebraMap (Localization.Away a) (Localization.Away ((a : A))) = fixedAwayMap a)
    (W₀A : WeierstrassCurve A) (Cvc : G → VariableChange A)
    (hCvc : ∀ g, Cvc g • (W₀A.map (MulSemiringAction.toRingHom G A g)) = W₀A)
    (act : G → (projModel W₀A ⟶ projModel W₀A))
    (hΨ : ∀ g, (projModelVCIso (Cvc g) (W₀A.map (MulSemiringAction.toRingHom G A g))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G A g) W₀A
      = eqToHom (congrArg projModel (hCvc g)) ≫ act g)
    (W₁ : WeierstrassCurve (Localization.Away a))
    (E : VariableChange (Localization.Away ((a : A))))
    (hW₁' : W₁.map (algebraMap (Localization.Away a) (Localization.Away ((a : A))))
      = E⁻¹ • (W₀A.map (algebraMap A (Localization.Away ((a : A))))))
    (hcob : ∀ g : G, (Cvc g).map (algebraMap A (Localization.Away ((a : A))))
      = E * (E.map (MulSemiringAction.awayHom (fun g' => a.2 g') g))⁻¹)
    {T : Scheme.{u}} (κ : Spec (CommRingCat.of (Localization.Away ((a : A)))) ⟶ T)
    (hκfix : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom
      (fun g' : G => a.2 g') g)) ≫ κ = κ)
    (g : G) :
    ∃ actR : projModel (W₀A.map (algebraMap A (Localization.Away ((a : A)))))
        ⟶ projModel (W₀A.map (algebraMap A (Localization.Away ((a : A))))),
      (actR ≫ descentComparison (W₀A.map (algebraMap A (Localization.Away ((a : A)))))
          W₁ E hW₁' = descentComparison _ W₁ E hW₁') ∧
      (actR ≫ projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A
        = projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A ≫ act g) ∧
      (actR ≫ (projModelπ (W₀A.map (algebraMap A (Localization.Away ((a : A))))) ≫ κ)
        = projModelπ (W₀A.map (algebraMap A (Localization.Away ((a : A))))) ≫ κ) := by
  have hfixA : ∀ g' : G, g' • ((a : A)) = (a : A) := fun g' => a.2 g'
  letI := MulSemiringAction.away hfixA
  -- ring-level compatibilities of the localized action
  have hcomm : ∀ g' : G,
      (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g').comp
        (algebraMap A (Localization.Away ((a : A))))
      = (algebraMap A (Localization.Away ((a : A)))).comp
          (MulSemiringAction.toRingHom G A g') := by
    intro g'
    refine RingHom.ext fun r => ?_
    show g' • (algebraMap A (Localization.Away ((a : A))) r)
      = algebraMap A (Localization.Away ((a : A))) (g' • r)
    exact MulSemiringAction.awayHom_algebraMap hfixA g' r
  -- the localized cocycle
  have hCvc' : ∀ g' : G, ((Cvc g').map (algebraMap A (Localization.Away ((a : A)))))
      • ((W₀A.map (algebraMap A (Localization.Away ((a : A))))).map
          (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g'))
      = W₀A.map (algebraMap A (Localization.Away ((a : A)))) := by
    intro g'
    rw [WeierstrassCurve.map_map, hcomm g', ← WeierstrassCurve.map_map,
      WeierstrassCurve.map_variableChange, hCvc g']
  -- the coboundary identity over the localization
  have hE : ∀ g' : G, (Cvc g').map (algebraMap A (Localization.Away ((a : A))))
      = E * (g' • E)⁻¹ := by
    intro g'
    have h2 : E.map (MulSemiringAction.awayHom (fun g'' : G => a.2 g'') g') = g' • E :=
      variableChange_map_awayHom (fun g'' : G => a.2 g'') g' E
    rw [hcob g', h2]
  -- the fixed subring maps to fixed elements
  have hR₀ : ∀ (g' : G) (r₀ : Localization.Away a),
      g' • (algebraMap (Localization.Away a) (Localization.Away ((a : A))) r₀)
        = algebraMap (Localization.Away a) (Localization.Away ((a : A))) r₀ := by
    intro g' r₀
    rw [halg]
    show MulSemiringAction.awayHom hfixA g' (fixedAwayMap a r₀) = fixedAwayMap a r₀
    exact congrArg
      (fun f : Localization.Away a →+* Localization.Away ((a : A)) => f r₀)
      (awayHom_comp_fixedAwayMap a g')
  -- `Spec` of the localized action fixes `κ`
  have hτfix : ∀ g' : G, Spec.map (CommRingCat.ofHom
      (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g')) ≫ κ = κ := by
    intro g'
    have hτ : CommRingCat.ofHom (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g')
        = CommRingCat.ofHom (MulSemiringAction.awayHom (fun g'' : G => a.2 g'') g') := rfl
    rw [hτ]
    exact hκfix g'
  have transπ' : ∀ {V V' : WeierstrassCurve (Localization.Away ((a : A)))} (h : V = V'),
      eqToHom (congrArg projModel h) ≫ projModelπ V' = projModelπ V := by
    rintro V V' rfl; simp
  refine ⟨eqToHom (congrArg projModel (hCvc' g).symm)
    ≫ (projModelVCIso ((Cvc g).map (algebraMap A (Localization.Away ((a : A)))))
        ((W₀A.map (algebraMap A (Localization.Away ((a : A))))).map
          (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g))).hom
    ≫ projModelBaseChange (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g)
        (W₀A.map (algebraMap A (Localization.Away ((a : A))))), ?_, ?_, ?_⟩
  · -- (i) coequalizes into the descent comparison
    refine descentComparison_invariant _ W₁ E hW₁'
      (fun g' => (Cvc g').map (algebraMap A (Localization.Away ((a : A))))) hCvc' hE hR₀
      (fun g' => eqToHom (congrArg projModel (hCvc' g').symm)
        ≫ (projModelVCIso ((Cvc g').map (algebraMap A (Localization.Away ((a : A)))))
            ((W₀A.map (algebraMap A (Localization.Away ((a : A))))).map
              (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g'))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g')
            (W₀A.map (algebraMap A (Localization.Away ((a : A)))))) (fun g' => ?_) g
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · -- (ii) covers the action through the base change
    exact actLoc_baseChange (algebraMap A (Localization.Away ((a : A))))
      (MulSemiringAction.toRingHom G A g)
      (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g) (hcomm g) W₀A
      (Cvc g) ((Cvc g).map (algebraMap A (Localization.Away ((a : A))))) rfl (hCvc g)
      (hCvc' g) (act g) (hΨ g)
  · -- (iii) fixes the `κ`-composite
    have hπ : (eqToHom (congrArg projModel (hCvc' g).symm)
        ≫ (projModelVCIso ((Cvc g).map (algebraMap A (Localization.Away ((a : A)))))
            ((W₀A.map (algebraMap A (Localization.Away ((a : A))))).map
              (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g)
            (W₀A.map (algebraMap A (Localization.Away ((a : A))))))
        ≫ projModelπ (W₀A.map (algebraMap A (Localization.Away ((a : A)))))
        = projModelπ (W₀A.map (algebraMap A (Localization.Away ((a : A)))))
          ≫ Spec.map (CommRingCat.ofHom
              (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g)) := by
      simp only [Category.assoc]
      rw [projModelBaseChange_π,
        reassoc_of% (projModelVCIso_π ((Cvc g).map (algebraMap A (Localization.Away ((a : A)))))
          ((W₀A.map (algebraMap A (Localization.Away ((a : A))))).map
            (MulSemiringAction.toRingHom G (Localization.Away ((a : A))) g))),
        reassoc_of% (transπ' (hCvc' g).symm)]
    rw [← Category.assoc, hπ, Category.assoc, hτfix g]

/-- Ellipticity descends along the localized-invariants inclusion `(Aᴳ)_a ⟶ A_a`: the
discriminant's inverse is a `G`-fixed unit, hence a fraction with fixed numerator
(`exists_fixed_smul_mk'_eq`), hence in the image of `fixedAwayMap`; injectivity of
`fixedAwayMap` (the `mk'`-level argument of `fixedPoints_awayMap_injective`) transports the
unit equation back. -/
private theorem isElliptic_of_map_fixedAwayMap {A : Type u} [CommRing A]
    [MulSemiringAction G A] [Finite G] (a : FixedPoints.subring A G)
    {W₁ : WeierstrassCurve (Localization.Away a)}
    (h : (W₁.map (fixedAwayMap a)).IsElliptic) : W₁.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff] at h ⊢
  rw [WeierstrassCurve.map_Δ] at h
  -- the localized action on `A_a`
  have hfixA : ∀ g : G, g • ((a : A)) = (a : A) := fun g => a.2 g
  letI := MulSemiringAction.away hfixA
  have hcomp : ∀ (g : G) (r : A),
      g • (algebraMap A (Localization.Away ((a : A))) r)
        = algebraMap A (Localization.Away ((a : A))) (g • r) := fun g r =>
    MulSemiringAction.awayHom_algebraMap hfixA g r
  have hS : ∀ (g : G), ∀ x ∈ Submonoid.powers ((a : A)), g • x = x := by
    rintro g x ⟨n, rfl⟩
    rw [smul_pow', hfixA]
  -- the image of `fixedAwayMap` is `G`-fixed
  have hcompim : ∀ g : G, (MulSemiringAction.awayHom hfixA g).comp (fixedAwayMap a)
      = fixedAwayMap a := by
    intro g
    refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun v => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [fixedAwayMap_algebraMap, MulSemiringAction.awayHom_algebraMap, v.2 g]
  have hfixim : ∀ (g : G) (z : Localization.Away a),
      g • fixedAwayMap a z = fixedAwayMap a z := by
    intro g z
    show MulSemiringAction.awayHom hfixA g (fixedAwayMap a z) = fixedAwayMap a z
    exact congrArg
      (fun f : Localization.Away a →+* Localization.Away ((a : A)) => f z) (hcompim g)
  -- the inverse of the image unit is fixed …
  obtain ⟨u, hu⟩ := h
  have hufix : ∀ g : G, g • ((u : Localization.Away ((a : A)))) = (u : _) := by
    intro g; rw [hu]; exact hfixim g W₁.Δ
  have hfixinv : ∀ g : G, g • ((↑u⁻¹ : Localization.Away ((a : A)))) = ↑u⁻¹ := by
    intro g
    have h₁ : (g • (↑u⁻¹ : Localization.Away ((a : A)))) * u = 1 := by
      have h0 := congrArg (g • · : Localization.Away ((a : A)) → _) u.inv_mul
      simp only [smul_mul'] at h0
      rw [hufix g] at h0
      simpa using h0
    calc g • (↑u⁻¹ : Localization.Away ((a : A)))
        = (g • (↑u⁻¹ : Localization.Away ((a : A)))) * (↑u * ↑u⁻¹) := by
          rw [u.mul_inv, mul_one]
      _ = ((g • (↑u⁻¹ : Localization.Away ((a : A)))) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h₁, one_mul]
  -- … hence a fraction with fixed numerator, i.e. in the image of `fixedAwayMap`
  obtain ⟨b, t, hb, hmk⟩ := exists_fixed_smul_mk'_eq hcomp hS (↑u⁻¹) hfixinv
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((a : A)) ^ n = (t : A) := t.2
  have hmkc : ∀ (b₁ b₂ : A) (s₁ s₂ : Submonoid.powers ((a : A))), b₁ = b₂ →
      (s₁ : A) = (s₂ : A) → IsLocalization.mk' (Localization.Away ((a : A))) b₁ s₁
        = IsLocalization.mk' _ b₂ s₂ := by
    rintro b₁ b₂ s₁ s₂ rfl hs
    exact congrArg _ (Subtype.ext hs)
  have hz : fixedAwayMap a (IsLocalization.mk' (Localization.Away a)
      (⟨b, hb⟩ : FixedPoints.subring A G) (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)) = ↑u⁻¹ := by
    rw [fixedAwayMap, IsLocalization.map_mk']
    refine (hmkc _ _ _ _ rfl ?_).trans hmk
    show ((algebraMap (FixedPoints.subring A G) A) (a ^ n) : A) = (t : A)
    rw [map_pow, ← hn]
    rfl
  -- injectivity of `fixedAwayMap` (mk'-level)
  have hinj : Function.Injective (fixedAwayMap a) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, t'⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
    rw [fixedAwayMap, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨d, hd⟩ := hx
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((a : A)) ^ k = (d : A) := d.2
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨a ^ k, k, rfl⟩, Subtype.ext ?_⟩
    show ((a : A)) ^ k * (c : A) = 0
    rw [hk]
    exact hd
  -- transport the unit equation back
  have hone : W₁.Δ * IsLocalization.mk' (Localization.Away a)
      (⟨b, hb⟩ : FixedPoints.subring A G) (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = 1 := by
    refine hinj ?_
    rw [map_mul, map_one, hz, ← hu]
    exact u.mul_inv
  exact IsUnit.of_mul_eq_one _ hone

/-- **([a5-W6], the per-point chart — ABSTRACT)** The `LocallyWeierstrass` chart package at a
point `s` of `Spec Aᴳ`, over an abstract ring `A` (all instances opaque — no `whnf` grind).
The geometry (the quotient cover `qE`, the model `φA`, the action family, the restricted
morphism-descent and the fppf data) is threaded as explicit hypotheses; the engine discharges
them over `Γ(X,⊤)` once. -/
theorem lw_chart_at {A : Type u} [CommRing A] [MulSemiringAction G A]
    [Fintype G] [DecidableEq G]
    -- the descended family over Spec Aᴳ
    {Qe : Scheme.{u}}
    (π'' : Qe ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)))
    (zero'' : Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)) ⟶ Qe)
    (hz'' : zero'' ≫ π'' = 𝟙 _)
    -- the total space, its cover of the quotient, and the model
    {EE : Scheme.{u}} (qE : EE ⟶ Qe) (πE : EE ⟶ Spec (CommRingCat.of A))
    (zeroE : Spec (CommRingCat.of A) ⟶ EE)
    (hsq : IsPullback qE πE π'' (invariantsπ G A ℤ))
    (hzeroSq : invariantsπ G A ℤ ≫ zero'' = zeroE ≫ qE)
    (W₀A : WeierstrassCurve A) (hW₀A : W₀A.IsElliptic)
    (φA : EE ≅ projModel W₀A)
    (hπφA : φA.hom ≫ projModelπ W₀A = πE)
    (hzeroφA : zeroE ≫ φA.hom = projModelZero W₀A)
    -- the action family and its cocycle
    (act : G → (projModel W₀A ⟶ projModel W₀A))
    (hEact : ∀ g, (φA.hom ≫ act g ≫ φA.inv) ≫ qE = qE)
    (Cvc : G → VariableChange A)
    (hCvc : ∀ g, Cvc g • (W₀A.map (MulSemiringAction.toRingHom G A g)) = W₀A)
    (hcoc : IsVCocycle Cvc)
    (hΨ : ∀ g, (projModelVCIso (Cvc g) (W₀A.map (MulSemiringAction.toRingHom G A g))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G A g) W₀A
      = eqToHom (congrArg projModel (hCvc g)) ≫ act g)
    -- the restricted morphism-descent and epi property of the cover
    (hlift : ∀ {Q' Y : Scheme.{u}} (j : Q' ⟶ Qe) [IsOpenImmersion j]
      (f : pullback qE j ⟶ Y),
      (∀ g, pullback.map qE j qE j (φA.hom ≫ act g ≫ φA.inv) (𝟙 Q') (𝟙 _)
          (by rw [Category.comp_id, hEact g]) (by simp) ≫ f = f) →
      ∃ q : Q' ⟶ Y, pullback.snd qE j ≫ q = f)
    (hepi : ∀ {Q' : Scheme.{u}} (j : Q' ⟶ Qe) [IsOpenImmersion j],
      Epi (pullback.snd qE j))
    -- the fppf data of the invariants cover
    (hfsur : Surjective (invariantsπ G A ℤ)) (hffl : Flat (invariantsπ G A ℤ))
    (hfqc : QuasiCompact (invariantsπ G A ℤ))
    -- the freeness (for the localized fixed-point identifications)
    (hfreeA : IsFreeAlgebraAction G ℤ A)
    -- the point and the descended local model
    (s : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))))
    (a : FixedPoints.subring A G) (hap : a ∉ s.asIdeal)
    (W₁ : WeierstrassCurve (Localization.Away a))
    (E : VariableChange (Localization.Away ((a : A))))
    (hW₁ : W₁.map (fixedAwayMap a)
      = E⁻¹ • (W₀A.map (algebraMap A (Localization.Away ((a : A))))))
    (hcob : ∀ g : G, (Cvc g).map (algebraMap A (Localization.Away ((a : A))))
      = E * (E.map (MulSemiringAction.awayHom (fun g' => a.2 g') g))⁻¹) :
    ∃ (U : (Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))).affineOpens)
      (_ : s ∈ U.1) (W : WeierstrassCurve ↑Γ(Spec (CommRingCat.of
        (FixedPoints.subalgebra ℤ A G)), U.1)),
      W.IsElliptic ∧
      ∃ e : pullback π'' U.1.ι ≅ projModel W,
        e.hom ≫ projModelπ W = pullback.snd π'' U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
            (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ e.hom =
          projModelZero W := by
  classical
  -- ## Step 1: the chart `U = D(a)` and its ring of sections
  let iA0 := CommRingCat.ofHom
    (algebraMap (FixedPoints.subring A G) (Localization.Away a))
  set iA : Spec (CommRingCat.of (Localization.Away a))
      ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)) :=
    Spec.map iA0 with hiA
  haveI : IsOpenImmersion iA := by
    rw [hiA]
    exact IsOpenImmersion.of_isLocalization a
  have hrange : iA.opensRange = (PrimeSpectrum.basicOpen a :
      (Spec (CommRingCat.of (FixedPoints.subring A G))).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  set U : (Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))).affineOpens :=
    ⟨iA.opensRange, isAffineOpen_opensRange iA⟩ with hUdef
  have hsU : s ∈ U.1 := by
    show s ∈ iA.opensRange
    rw [hrange]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr hap
  -- the scheme-level chart iso `Spec (Aᴳ)_a ≅ Spec Γ(Spec Aᴳ, U)` through `fromSpec`
  have hfsRange : Set.range ⇑iA.base = Set.range ⇑U.2.fromSpec.base := by
    rw [U.2.range_fromSpec]; rfl
  let kF : Spec (CommRingCat.of (Localization.Away a))
      ≅ Spec Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    IsOpenImmersion.isoOfRangeEq iA U.2.fromSpec hfsRange
  have hkF : kF.inv ≫ iA = U.2.fromSpec :=
    IsOpenImmersion.isoOfRangeEq_inv_fac iA U.2.fromSpec hfsRange
  -- the ring identification, through `Spec`-full-faithfulness
  let qp : CommRingCat.of (Localization.Away a)
      ≅ Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    { hom := Spec.preimage kF.inv
      inv := Spec.preimage kF.hom
      hom_inv_id := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Iso.hom_inv_id]
      inv_hom_id := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Iso.inv_hom_id] }
  set req : Localization.Away a ≃+*
      ↑Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    qp.commRingCatIsoToRingEquiv with hreq
  have hsR : Spec.map (CommRingCat.ofHom req.toRingHom) = kF.inv := by
    rw [hreq]
    show Spec.map (CommRingCat.ofHom qp.hom.hom) = kF.inv
    rw [CommRingCat.ofHom_hom]
    exact Spec.map_preimage kF.inv
  have hBridge : Spec.map (CommRingCat.ofHom req.toRingHom) ≫ iA = U.2.fromSpec := by
    rw [hsR, hkF]
  -- the descended model over the chart ring
  set W : WeierstrassCurve ↑Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    W₁.map req.toRingHom with hWdef
  -- ## Step 2: ellipticity
  haveI hW₁ell : W₁.IsElliptic := by
    refine isElliptic_of_map_fixedAwayMap a ?_
    rw [hW₁]
    haveI := hW₀A
    infer_instance
  haveI hWell : W.IsElliptic := by
    rw [hWdef]
    infer_instance
  refine ⟨U, hsU, W, hWell, ?_⟩
  -- ## Step 3a: the chart square over `Spec A`
  set iAA := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))))
    with hiAA
  haveI : IsOpenImmersion iAA := by
    rw [hiAA]
    exact IsOpenImmersion.of_isLocalization ((a : A))
  have hrangeAA : iAA.opensRange = (PrimeSpectrum.basicOpen ((a : A)) :
      (Spec (CommRingCat.of A)).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away ((a : A))) ((a : A))
  -- the preimage of the chart is the basic open `D((a : A))`
  have hpreU : invariantsπ G A ℤ ⁻¹ᵁ U.1 = iAA.opensRange := by
    rw [hrangeAA]
    ext x
    show invariantsπ G A ℤ x ∈ iA.opensRange ↔ x ∈ PrimeSpectrum.basicOpen ((a : A))
    rw [hrange]
    exact Iff.rfl
  -- the restricted invariants map `κ` and the chart square
  set specFam := Spec.map (CommRingCat.ofHom (fixedAwayMap a)) with hspecFam
  have hRingSq : iA0 ≫ CommRingCat.ofHom (fixedAwayMap a)
      = CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)
        ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))) := by
    ext v
    show fixedAwayMap a (algebraMap _ _ v)
      = algebraMap A (Localization.Away ((a : A))) (algebraMap _ A v)
    rw [fixedAwayMap_algebraMap]
    rfl
  have hSpecSq : specFam ≫ iA = iAA ≫ invariantsπ G A ℤ := by
    have h1 : specFam ≫ iA = Spec.map (iA0 ≫ CommRingCat.ofHom (fixedAwayMap a)) :=
      (Spec.map_comp _ _).symm
    have h2 : iAA ≫ invariantsπ G A ℤ
        = Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)
          ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A))))) :=
      (Spec.map_comp _ _).symm
    rw [h1, h2, hRingSq]
  -- `κ` : the restriction of the invariants cover to the chart
  have hκsub : Set.range ⇑(iAA ≫ invariantsπ G A ℤ).base ⊆ Set.range ⇑U.1.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : iAA z ∈ invariantsπ G A ℤ ⁻¹ᵁ U.1 := by
      rw [hpreU]
      exact ⟨z, rfl⟩
    exact hz
  set κ : Spec (CommRingCat.of (Localization.Away ((a : A)))) ⟶ U.1.toScheme :=
    IsOpenImmersion.lift U.1.ι (iAA ≫ invariantsπ G A ℤ) hκsub with hκdef
  have hκι : κ ≫ U.1.ι = iAA ≫ invariantsπ G A ℤ := IsOpenImmersion.lift_fac ..
  have hAsq : IsPullback iAA κ (invariantsπ G A ℤ) U.1.ι := by
    refine (IsOpenImmersion.isPullback κ iAA U.1.ι (invariantsπ G A ℤ) ?_ ?_).flip
    · rw [hκι]
    · rw [Scheme.Opens.opensRange_ι]
      exact hpreU
  haveI hκsur : Surjective κ := MorphismProperty.of_isPullback (P := @Surjective) hAsq hfsur
  haveI hκfl : Flat κ := MorphismProperty.of_isPullback (P := @Flat) hAsq hffl
  haveI hκqc : QuasiCompact κ := MorphismProperty.of_isPullback (P := @QuasiCompact) hAsq hfqc
  -- the chart bridge: `κ` through `isoSpec` is the `Spec`-side composite
  have hkFhom : kF.hom ≫ U.2.fromSpec = iA :=
    IsOpenImmersion.isoOfRangeEq_hom_fac iA U.2.fromSpec hfsRange
  have hκiso : κ ≫ U.2.isoSpec.hom = specFam ≫ kF.hom := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec, hκι, hkFhom, hSpecSq]
  -- ## Step 3b: the model-side squares
  set W₀R := W₀A.map (algebraMap A (Localization.Away ((a : A)))) with hW₀Rdef
  have hbcsq : IsPullback (projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A)
      (projModelπ W₀R) (projModelπ W₀A) iAA := by
    rw [hiAA]
    exact isPullback_projModelBaseChange W₀A
  -- the `descentComparison` and its cartesian square over `specFam`
  letI : Algebra (Localization.Away a) (Localization.Away ((a : A))) :=
    (fixedAwayMap a).toAlgebra
  have halg : algebraMap (Localization.Away a) (Localization.Away ((a : A)))
      = fixedAwayMap a := RingHom.algebraMap_toAlgebra _
  have hW₁' : W₁.map (algebraMap (Localization.Away a) (Localization.Away ((a : A))))
      = E⁻¹ • W₀R := by
    rw [halg]
    exact hW₁
  set ψ₀ : projModel W₀R ⟶ projModel W₁ := descentComparison W₀R W₁ E hW₁' with hψ₀def
  have hspecAlg : Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) (Localization.Away ((a : A))))) = specFam := by
    rw [halg, hspecFam]
  have transπ : ∀ {V V' : WeierstrassCurve (Localization.Away ((a : A)))} (h : V = V'),
      eqToHom (congrArg projModel h) ≫ projModelπ V' = projModelπ V := by
    rintro V V' rfl; simp
  have hψsq : IsPullback ψ₀ (projModelπ W₀R) (projModelπ W₁) specFam := by
    have hι₀ : IsPullback ((projModelVCIso E⁻¹ W₀R).inv
        ≫ eqToHom (congrArg projModel hW₁'.symm)) (projModelπ W₀R)
        (projModelπ (W₁.map (algebraMap (Localization.Away a)
          (Localization.Away ((a : A)))))) (𝟙 _) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Category.comp_id, Category.assoc, transπ hW₁'.symm, Iso.inv_comp_eq,
        projModelVCIso_π]
    have hpaste := hι₀.paste_horiz (isPullback_projModelBaseChange
      (R := Localization.Away a) (R' := Localization.Away ((a : A))) W₁)
    rw [Category.id_comp, hspecAlg] at hpaste
    rw [hψ₀def, descentComparison, ← Category.assoc]
    exact hpaste
  -- the `req`-transport square
  haveI hsRqIso : IsIso (Spec.map (CommRingCat.ofHom req.toRingHom)) := by
    rw [hsR]
    infer_instance
  have hbcW : IsPullback (projModelBaseChange req.toRingHom W₁)
      (projModelπ W) (projModelπ W₁) kF.inv := by
    have h := isPullback_projModelBaseChange₂ req.toRingHom W₁
    rw [hsR] at h
    exact h
  haveI hbcRIso : IsIso (projModelBaseChange req.toRingHom W₁) :=
    isIso_projModelBaseChange₂ req.toRingHom W₁
  set ν : projModel W₁ ⟶ projModel W := inv (projModelBaseChange req.toRingHom W₁) with hνdef
  have hνsq : IsPullback ν (projModelπ W₁) (projModelπ W) kF.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [hνdef, ← cancel_epi (projModelBaseChange req.toRingHom W₁), IsIso.hom_inv_id_assoc,
      ← Category.assoc, hbcW.w, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- the pasted comparison square over `bmap := specFam ≫ kF.hom`
  have hψν : IsPullback (ψ₀ ≫ ν) (projModelπ W₀R) (projModelπ W) (specFam ≫ kF.hom) :=
    hψsq.paste_horiz hνsq
  -- ## Step 3c: the two pullback presentations of the chart-restricted total space
  set j : pullback π'' U.1.ι ⟶ Qe := pullback.fst π'' U.1.ι with hjdef
  haveI : IsOpenImmersion j := by
    rw [hjdef]
    infer_instance
  set pU : pullback π'' U.1.ι ⟶ U.1.toScheme := pullback.snd π'' U.1.ι with hpUdef
  set pE : pullback qE j ⟶ EE := pullback.fst qE j with hpEdef
  set pQ : pullback qE j ⟶ pullback π'' U.1.ι := pullback.snd qE j with hpQdef
  have hQ'sq : IsPullback j pU π'' U.1.ι := IsPullback.of_hasPullback π'' U.1.ι
  have hPBsq : IsPullback pE pQ qE j := IsPullback.of_hasPullback qE j
  -- the `U`-cospan presentation of `pullback qE j`
  have hbig : IsPullback (pQ ≫ pU) pE U.1.ι (πE ≫ invariantsπ G A ℤ) := by
    have h1 := hPBsq.flip.paste_horiz hQ'sq.flip
    rw [hsq.w] at h1
    exact h1
  -- the `U`-cospan presentation of the localized model
  have hs' : IsPullback (projModelπ W₀R)
      (projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A ≫ φA.inv)
      iAA πE := by
    have hφsq : IsPullback (projModelπ W₀A) φA.inv (𝟙 (Spec (CommRingCat.of A))) πE := by
      refine IsPullback.of_vert_isIso ⟨?_⟩
      rw [Category.comp_id, Iso.eq_inv_comp, hπφA]
    have h2 := hbcsq.flip.paste_vert hφsq
    rw [Category.comp_id] at h2
    exact h2
  have hW₀Rsq : IsPullback (projModelπ W₀R ≫ κ)
      (projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A ≫ φA.inv)
      U.1.ι (πE ≫ invariantsπ G A ℤ) :=
    hs'.paste_horiz hAsq.flip
  -- the comparison iso
  set θ : (pullback qE j : Scheme) ≅ projModel W₀R :=
    hbig.isoIsPullback _ _ hW₀Rsq with hθdef
  have hθfst : θ.hom ≫ (projModelπ W₀R ≫ κ) = pQ ≫ pU :=
    hbig.isoIsPullback_hom_fst _ _ hW₀Rsq
  have hθsnd : θ.hom ≫ (projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A
      ≫ φA.inv) = pE :=
    hbig.isoIsPullback_hom_snd _ _ hW₀Rsq
  have hθbc : θ.hom ≫ projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A
      = pE ≫ φA.hom := by
    rw [← hθsnd, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- ## Step 4: the comparison morphism and its `G`-invariance
  -- `Spec` of the localized action fixes `κ`
  have hκfix : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom
      (fun g' : G => a.2 g') g)) ≫ κ = κ := by
    intro g
    have hringL : CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A))))
        ≫ CommRingCat.ofHom (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)
        = CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)
          ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))) := by
      ext r
      exact MulSemiringAction.awayHom_algebraMap (fun g' : G => a.2 g') g r
    have hL : Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom
        (fun g' : G => a.2 g') g)) ≫ iAA = iAA ≫ specSMul g := by
      rw [hiAA, ← Spec.map_comp, hringL, Spec.map_comp]
      rfl
    rw [← cancel_mono U.1.ι, Category.assoc, hκι, ← Category.assoc, hL, Category.assoc,
      specSMul_invariantsπ]
  -- the localized action family
  choose actR hactψ hactbc hactπκ using
    fun g : G => exists_actLoc a halg W₀A Cvc hCvc act hΨ W₁ E hW₁' hcob κ hκfix g
  have hactψ' : ∀ g : G, actR g ≫ ψ₀ = ψ₀ := fun g => hactψ g
  have hactπκ' : ∀ g : G, actR g ≫ (projModelπ W₀R ≫ κ) = projModelπ W₀R ≫ κ :=
    fun g => hactπκ g
  -- the comparison morphism on the chart-restricted cover
  set f : (pullback qE j : Scheme.{u}) ⟶ projModel W := θ.hom ≫ ψ₀ ≫ ν with hfdef
  -- invariance of `f`, for an abstract endomorphism with the two projection properties
  have hMkey : ∀ (g : G) (M : (pullback qE j : Scheme.{u}) ⟶ pullback qE j),
      M ≫ pQ = pQ → M ≫ pE = pE ≫ (φA.hom ≫ act g ≫ φA.inv) → M ≫ f = f := by
    intro g M hMpQ hMpE
    have hMθ : M ≫ θ.hom = θ.hom ≫ actR g := by
      refine hW₀Rsq.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hactπκ' g, hθfst, ← Category.assoc, hMpQ]
      · simp only [Category.assoc]
        rw [reassoc_of% (hactbc g), reassoc_of% hθbc, Iso.hom_inv_id, Category.comp_id,
          hMpE, reassoc_of% hθbc]
    rw [hfdef, ← Category.assoc, hMθ, Category.assoc, reassoc_of% (hactψ' g)]
  -- ## the descended morphism
  obtain ⟨cmp, hcmp₀⟩ := hlift j f (fun g => hMkey g _
    (by rw [hpQdef]; simp only [pullback.lift_snd, Category.comp_id])
    (by rw [hpEdef]; simp only [pullback.lift_fst]))
  have hcmp : pQ ≫ cmp = f := hcmp₀
  haveI hpQepi : Epi pQ := by
    rw [hpQdef]
    exact hepi j
  -- the `π`-leg of the comparison
  have hcmpπ : cmp ≫ projModelπ W = pU ≫ U.2.isoSpec.hom := by
    rw [← cancel_epi pQ, ← Category.assoc, hcmp, hfdef, Category.assoc, Category.assoc,
      hνsq.w, reassoc_of% hψsq.w, ← reassoc_of% hθfst, hκiso]
  -- ## Step 5: `cmp` is an isomorphism (fppf descent of `θ`)
  have hPBR : IsPullback (θ.hom ≫ projModelπ W₀R) pQ κ pU := by
    refine IsPullback.of_right ?_ ?_ hAsq
    · have h1 := hPBsq.paste_horiz hsq.flip
      rw [hQ'sq.w] at h1
      have hfst : (θ.hom ≫ projModelπ W₀R) ≫ iAA = pE ≫ πE := by
        rw [Category.assoc, ← hbcsq.w, reassoc_of% hθbc, hπφA]
      rw [← hfst] at h1
      exact h1
    · rw [Category.assoc]
      exact hθfst
  have hs₅ : IsPullback (θ.hom ≫ projModelπ W₀R) pQ (specFam ≫ kF.hom)
      (pU ≫ U.2.isoSpec.hom) := by
    have h2 : IsPullback pU (𝟙 (pullback π'' U.1.ι : Scheme.{u})) U.2.isoSpec.hom
        (pU ≫ U.2.isoSpec.hom) := by
      refine IsPullback.of_vert_isIso ⟨?_⟩
      rw [Category.id_comp]
    have h3 := hPBR.paste_vert h2
    rw [Category.comp_id, hκiso] at h3
    exact h3
  have hspecFamFppf : specFam = κ ≫ U.2.isoSpec.hom ≫ kF.inv := by
    rw [← Category.assoc, hκiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : Surjective specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : Flat specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : QuasiCompact specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : Surjective ψ₀ := MorphismProperty.of_isPullback (P := @Surjective) hψsq.flip ‹_›
  haveI : Flat ψ₀ := MorphismProperty.of_isPullback (P := @Flat) hψsq.flip ‹_›
  haveI : QuasiCompact ψ₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) hψsq.flip ‹_›
  haveI : IsIso cmp := by
    have hLsq : IsPullback θ.hom pQ (ψ₀ ≫ ν) cmp := by
      refine IsPullback.of_right ?_ ?_ hψν.flip
      · rw [← hcmpπ] at hs₅
        exact hs₅
      · rw [hcmp, hfdef]
    exact isIso_of_isPullback_of_fppf hLsq
  -- ## Step 6: packaging
  refine ⟨asIso cmp, ?_, ?_⟩
  · show cmp ≫ projModelπ W = pullback.snd π'' U.1.ι ≫ U.2.isoSpec.hom
    rw [← hpUdef]
    exact hcmpπ
  · -- the zero-section leg, by cancelling the fppf cover
    show (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ cmp
      = projModelZero W
    haveI hpUepi : Epi pU := by
      have hsplit : (pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
          (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ pU = 𝟙 _ := by
        rw [hpUdef]
        exact pullback.lift_snd _ _ _
      refine ⟨fun {Z} u v huv => ?_⟩
      rw [← Category.id_comp u, ← hsplit, Category.assoc, huv, ← Category.assoc, hsplit,
        Category.id_comp]
    haveI hκepi : Epi κ := by
      haveI h2 : Epi ((θ.hom ≫ projModelπ W₀R) ≫ κ) := by
        rw [Category.assoc, hθfst]
        exact epi_comp pQ pU
      exact epi_of_epi (θ.hom ≫ projModelπ W₀R) κ
    haveI hbmapepi : Epi (specFam ≫ kF.hom) := by
      rw [← hκiso]
      exact epi_comp κ U.2.isoSpec.hom
    -- the ingredients of the zero-section chase
    have hbmapinv : (specFam ≫ kF.hom) ≫ U.2.isoSpec.inv = κ := by
      rw [← hκiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hζw : (iAA ≫ zeroE) ≫ qE = (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ j := by
      rw [Category.assoc, ← hzeroSq, hjdef, Category.assoc, pullback.lift_fst,
        reassoc_of% hκι]
    have hζpQ : pullback.lift (iAA ≫ zeroE) (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) hζw ≫ pQ
        = κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
          (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp]) := by
      rw [hpQdef]
      exact pullback.lift_snd _ _ _
    have hzφinv : projModelZero W₀A ≫ φA.inv = zeroE := by
      rw [← hzeroφA, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hzbc : projModelZero W₀R
        ≫ projModelBaseChange (algebraMap A (Localization.Away ((a : A)))) W₀A
        = iAA ≫ projModelZero W₀A := by
      rw [hiAA]
      exact projModelZero_baseChange₂ (algebraMap A (Localization.Away ((a : A)))) W₀A
    have hζθ : pullback.lift (iAA ≫ zeroE) (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) hζw ≫ θ.hom
        = projModelZero W₀R := by
      refine hW₀Rsq.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hθfst, ← Category.assoc, hζpQ, Category.assoc,
          reassoc_of% projModelZero_projModelπ]
        rw [hpUdef, pullback.lift_snd, Category.comp_id]
      · simp only [Category.assoc]
        rw [hθsnd, hpEdef, pullback.lift_fst, ← Category.assoc, hzbc, Category.assoc, hzφinv]
    have hz2 : projModelZero W ≫ projModelBaseChange req.toRingHom W₁
        = kF.inv ≫ projModelZero W₁ := by
      have h := projModelZero_baseChange₂ req.toRingHom W₁
      rw [hsR] at h
      exact h
    have hzν : projModelZero W₁ ≫ ν = kF.hom ≫ projModelZero W := by
      rw [hνdef, ← cancel_mono (projModelBaseChange req.toRingHom W₁), Category.assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, hz2, Iso.hom_inv_id_assoc]
    have hzψ : projModelZero W₀R ≫ ψ₀ = specFam ≫ projModelZero W₁ := by
      rw [hψ₀def, descentComparison_zero, hspecAlg]
    -- assemble
    rw [← cancel_epi (specFam ≫ kF.hom)]
    simp only [Category.assoc]
    rw [reassoc_of% hbmapinv, ← reassoc_of% hζpQ, hcmp, hfdef, reassoc_of% hζθ,
      reassoc_of% hzψ, hzν]

set_option maxHeartbeats 800000 in
/-- **([a5-W6-loc], the per-point chart from a LOCALIZED model — ABSTRACT)** The `lw_chart_at`
engine with the global-model inputs (`W₀A`, `φA`, `act`, `Cvc`, `hΨ`) replaced by their
restrictions to the invariant basic localization `A_a`, `a ∉ s`: a Weierstrass model
`W₀R / A_a` of the restricted total space (`ρR`/`hρsq`/`hρzero` — `projModel W₀R` presented as
the pullback of `EE` along `Spec A_a ⟶ Spec A`), the `VariableChange` cocycle `CvcR / A_a`
presenting the geometric action through `ρR` (`hCvcR`/`hρact`), and the descended curve
`W₁ / (Aᴳ)_a` with the coboundary identity (`hW₁`/`hcob`). This is the engine of the general
(`C.localModel`-only) route `[a5-P-loc]`, where a *global* model upstairs is obstructed by the
class of `ω` in `Pic A`. The geometric action is carried by the abstract family `actE` (no
`φ`-conjugation — instantiated with `σE.hom` directly). The proof is `lw_chart_at`'s verbatim,
with Step 3a (the base-change presentation of the restricted total space) replaced by the given
`hρsq`, and `exists_actLoc` inlined one localization level down (its base-change leg (ii)
becomes the hypothesis `hρact`). -/
theorem lw_chart_at_of_localModel {A : Type u} [CommRing A] [MulSemiringAction G A]
    [Fintype G] [DecidableEq G]
    -- the descended family over Spec Aᴳ
    {Qe : Scheme.{u}}
    (π'' : Qe ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)))
    (zero'' : Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)) ⟶ Qe)
    (hz'' : zero'' ≫ π'' = 𝟙 _)
    -- the total space, its cover of the quotient, and the geometric action
    {EE : Scheme.{u}} (qE : EE ⟶ Qe) (πE : EE ⟶ Spec (CommRingCat.of A))
    (zeroE : Spec (CommRingCat.of A) ⟶ EE)
    (hsq : IsPullback qE πE π'' (invariantsπ G A ℤ))
    (hzeroSq : invariantsπ G A ℤ ≫ zero'' = zeroE ≫ qE)
    (actE : G → (EE ⟶ EE)) (hEact : ∀ g, actE g ≫ qE = qE)
    -- the restricted morphism-descent and epi property of the cover
    (hlift : ∀ {Q' Y : Scheme.{u}} (j : Q' ⟶ Qe) [IsOpenImmersion j]
      (f : pullback qE j ⟶ Y),
      (∀ g, pullback.map qE j qE j (actE g) (𝟙 Q') (𝟙 _)
          (by rw [Category.comp_id, hEact g]) (by simp) ≫ f = f) →
      ∃ q : Q' ⟶ Y, pullback.snd qE j ≫ q = f)
    (hepi : ∀ {Q' : Scheme.{u}} (j : Q' ⟶ Qe) [IsOpenImmersion j],
      Epi (pullback.snd qE j))
    -- the fppf data of the invariants cover
    (hfsur : Surjective (invariantsπ G A ℤ)) (hffl : Flat (invariantsπ G A ℤ))
    (hfqc : QuasiCompact (invariantsπ G A ℤ))
    -- the point, and the localized model/cocycle/descent package at an invariant `a ∉ s`
    (s : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))))
    (a : FixedPoints.subring A G) (hap : a ∉ s.asIdeal)
    (W₀R : WeierstrassCurve (Localization.Away ((a : A)))) (hW₀R : W₀R.IsElliptic)
    (ρR : projModel W₀R ⟶ EE)
    (hρsq : IsPullback (projModelπ W₀R) ρR
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))))) πE)
    (hρzero : projModelZero W₀R ≫ ρR
      = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A))))) ≫ zeroE)
    (CvcR : G → VariableChange (Localization.Away ((a : A))))
    (hCvcR : ∀ g, CvcR g
      • (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)) = W₀R)
    (hρact : ∀ g, (eqToHom (congrArg projModel (hCvcR g).symm)
        ≫ (projModelVCIso (CvcR g)
            (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
        ≫ projModelBaseChange (MulSemiringAction.awayHom (fun g' : G => a.2 g') g) W₀R)
        ≫ ρR = ρR ≫ actE g)
    (W₁ : WeierstrassCurve (Localization.Away a))
    (E : VariableChange (Localization.Away ((a : A))))
    (hW₁ : W₁.map (fixedAwayMap a) = E⁻¹ • W₀R)
    (hcob : ∀ g : G, CvcR g
      = E * (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹) :
    ∃ (U : (Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))).affineOpens)
      (_ : s ∈ U.1) (W : WeierstrassCurve ↑Γ(Spec (CommRingCat.of
        (FixedPoints.subalgebra ℤ A G)), U.1)),
      W.IsElliptic ∧
      ∃ e : pullback π'' U.1.ι ≅ projModel W,
        e.hom ≫ projModelπ W = pullback.snd π'' U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
            (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ e.hom =
          projModelZero W := by
  classical
  -- ## Step 1: the chart `U = D(a)` and its ring of sections
  let iA0 := CommRingCat.ofHom
    (algebraMap (FixedPoints.subring A G) (Localization.Away a))
  set iA : Spec (CommRingCat.of (Localization.Away a))
      ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)) :=
    Spec.map iA0 with hiA
  haveI : IsOpenImmersion iA := by
    rw [hiA]
    exact IsOpenImmersion.of_isLocalization a
  have hrange : iA.opensRange = (PrimeSpectrum.basicOpen a :
      (Spec (CommRingCat.of (FixedPoints.subring A G))).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  set U : (Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G))).affineOpens :=
    ⟨iA.opensRange, isAffineOpen_opensRange iA⟩ with hUdef
  have hsU : s ∈ U.1 := by
    show s ∈ iA.opensRange
    rw [hrange]
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr hap
  -- the scheme-level chart iso `Spec (Aᴳ)_a ≅ Spec Γ(Spec Aᴳ, U)` through `fromSpec`
  have hfsRange : Set.range ⇑iA.base = Set.range ⇑U.2.fromSpec.base := by
    rw [U.2.range_fromSpec]; rfl
  let kF : Spec (CommRingCat.of (Localization.Away a))
      ≅ Spec Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    IsOpenImmersion.isoOfRangeEq iA U.2.fromSpec hfsRange
  have hkF : kF.inv ≫ iA = U.2.fromSpec :=
    IsOpenImmersion.isoOfRangeEq_inv_fac iA U.2.fromSpec hfsRange
  -- the ring identification, through `Spec`-full-faithfulness
  let qp : CommRingCat.of (Localization.Away a)
      ≅ Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    { hom := Spec.preimage kF.inv
      inv := Spec.preimage kF.hom
      hom_inv_id := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Iso.hom_inv_id]
      inv_hom_id := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id, Iso.inv_hom_id] }
  set req : Localization.Away a ≃+*
      ↑Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    qp.commRingCatIsoToRingEquiv with hreq
  have hsR : Spec.map (CommRingCat.ofHom req.toRingHom) = kF.inv := by
    rw [hreq]
    show Spec.map (CommRingCat.ofHom qp.hom.hom) = kF.inv
    rw [CommRingCat.ofHom_hom]
    exact Spec.map_preimage kF.inv
  have hBridge : Spec.map (CommRingCat.ofHom req.toRingHom) ≫ iA = U.2.fromSpec := by
    rw [hsR, hkF]
  -- the descended model over the chart ring
  set W : WeierstrassCurve ↑Γ(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ A G)), U.1) :=
    W₁.map req.toRingHom with hWdef
  -- ## Step 2: ellipticity
  haveI hW₁ell : W₁.IsElliptic := by
    refine isElliptic_of_map_fixedAwayMap a ?_
    rw [hW₁]
    haveI := hW₀R
    infer_instance
  haveI hWell : W.IsElliptic := by
    rw [hWdef]
    infer_instance
  refine ⟨U, hsU, W, hWell, ?_⟩
  -- ## Step 3a: the chart square over `Spec A`
  set iAA := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))))
    with hiAA
  haveI : IsOpenImmersion iAA := by
    rw [hiAA]
    exact IsOpenImmersion.of_isLocalization ((a : A))
  have hrangeAA : iAA.opensRange = (PrimeSpectrum.basicOpen ((a : A)) :
      (Spec (CommRingCat.of A)).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away ((a : A))) ((a : A))
  -- the preimage of the chart is the basic open `D((a : A))`
  have hpreU : invariantsπ G A ℤ ⁻¹ᵁ U.1 = iAA.opensRange := by
    rw [hrangeAA]
    ext x
    show invariantsπ G A ℤ x ∈ iA.opensRange ↔ x ∈ PrimeSpectrum.basicOpen ((a : A))
    rw [hrange]
    exact Iff.rfl
  -- the restricted invariants map `κ` and the chart square
  set specFam := Spec.map (CommRingCat.ofHom (fixedAwayMap a)) with hspecFam
  have hRingSq : iA0 ≫ CommRingCat.ofHom (fixedAwayMap a)
      = CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)
        ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))) := by
    ext v
    show fixedAwayMap a (algebraMap _ _ v)
      = algebraMap A (Localization.Away ((a : A))) (algebraMap _ A v)
    rw [fixedAwayMap_algebraMap]
    rfl
  have hSpecSq : specFam ≫ iA = iAA ≫ invariantsπ G A ℤ := by
    have h1 : specFam ≫ iA = Spec.map (iA0 ≫ CommRingCat.ofHom (fixedAwayMap a)) :=
      (Spec.map_comp _ _).symm
    have h2 : iAA ≫ invariantsπ G A ℤ
        = Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)
          ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A))))) :=
      (Spec.map_comp _ _).symm
    rw [h1, h2, hRingSq]
  -- `κ` : the restriction of the invariants cover to the chart
  have hκsub : Set.range ⇑(iAA ≫ invariantsπ G A ℤ).base ⊆ Set.range ⇑U.1.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : iAA z ∈ invariantsπ G A ℤ ⁻¹ᵁ U.1 := by
      rw [hpreU]
      exact ⟨z, rfl⟩
    exact hz
  set κ : Spec (CommRingCat.of (Localization.Away ((a : A)))) ⟶ U.1.toScheme :=
    IsOpenImmersion.lift U.1.ι (iAA ≫ invariantsπ G A ℤ) hκsub with hκdef
  have hκι : κ ≫ U.1.ι = iAA ≫ invariantsπ G A ℤ := IsOpenImmersion.lift_fac ..
  have hAsq : IsPullback iAA κ (invariantsπ G A ℤ) U.1.ι := by
    refine (IsOpenImmersion.isPullback κ iAA U.1.ι (invariantsπ G A ℤ) ?_ ?_).flip
    · rw [hκι]
    · rw [Scheme.Opens.opensRange_ι]
      exact hpreU
  haveI hκsur : Surjective κ := MorphismProperty.of_isPullback (P := @Surjective) hAsq hfsur
  haveI hκfl : Flat κ := MorphismProperty.of_isPullback (P := @Flat) hAsq hffl
  haveI hκqc : QuasiCompact κ := MorphismProperty.of_isPullback (P := @QuasiCompact) hAsq hfqc
  -- the chart bridge: `κ` through `isoSpec` is the `Spec`-side composite
  have hkFhom : kF.hom ≫ U.2.fromSpec = iA :=
    IsOpenImmersion.isoOfRangeEq_hom_fac iA U.2.fromSpec hfsRange
  have hκiso : κ ≫ U.2.isoSpec.hom = specFam ≫ kF.hom := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec, hκι, hkFhom, hSpecSq]
  -- ## Step 3b: the model-side squares
  letI : Algebra (Localization.Away a) (Localization.Away ((a : A))) :=
    (fixedAwayMap a).toAlgebra
  have halg : algebraMap (Localization.Away a) (Localization.Away ((a : A)))
      = fixedAwayMap a := RingHom.algebraMap_toAlgebra _
  have hW₁' : W₁.map (algebraMap (Localization.Away a) (Localization.Away ((a : A))))
      = E⁻¹ • W₀R := by
    rw [halg]
    exact hW₁
  set ψ₀ : projModel W₀R ⟶ projModel W₁ := descentComparison W₀R W₁ E hW₁' with hψ₀def
  have hspecAlg : Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) (Localization.Away ((a : A))))) = specFam := by
    rw [halg, hspecFam]
  have transπ : ∀ {V V' : WeierstrassCurve (Localization.Away ((a : A)))} (h : V = V'),
      eqToHom (congrArg projModel h) ≫ projModelπ V' = projModelπ V := by
    rintro V V' rfl; simp
  have hψsq : IsPullback ψ₀ (projModelπ W₀R) (projModelπ W₁) specFam := by
    have hι₀ : IsPullback ((projModelVCIso E⁻¹ W₀R).inv
        ≫ eqToHom (congrArg projModel hW₁'.symm)) (projModelπ W₀R)
        (projModelπ (W₁.map (algebraMap (Localization.Away a)
          (Localization.Away ((a : A)))))) (𝟙 _) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Category.comp_id, Category.assoc, transπ hW₁'.symm, Iso.inv_comp_eq,
        projModelVCIso_π]
    have hpaste := hι₀.paste_horiz (isPullback_projModelBaseChange
      (R := Localization.Away a) (R' := Localization.Away ((a : A))) W₁)
    rw [Category.id_comp, hspecAlg] at hpaste
    rw [hψ₀def, descentComparison, ← Category.assoc]
    exact hpaste
  -- the `req`-transport square
  haveI hsRqIso : IsIso (Spec.map (CommRingCat.ofHom req.toRingHom)) := by
    rw [hsR]
    infer_instance
  have hbcW : IsPullback (projModelBaseChange req.toRingHom W₁)
      (projModelπ W) (projModelπ W₁) kF.inv := by
    have h := isPullback_projModelBaseChange₂ req.toRingHom W₁
    rw [hsR] at h
    exact h
  haveI hbcRIso : IsIso (projModelBaseChange req.toRingHom W₁) :=
    isIso_projModelBaseChange₂ req.toRingHom W₁
  set ν : projModel W₁ ⟶ projModel W := inv (projModelBaseChange req.toRingHom W₁) with hνdef
  have hνsq : IsPullback ν (projModelπ W₁) (projModelπ W) kF.hom := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [hνdef, ← cancel_epi (projModelBaseChange req.toRingHom W₁), IsIso.hom_inv_id_assoc,
      ← Category.assoc, hbcW.w, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- the pasted comparison square over `bmap := specFam ≫ kF.hom`
  have hψν : IsPullback (ψ₀ ≫ ν) (projModelπ W₀R) (projModelπ W) (specFam ≫ kF.hom) :=
    hψsq.paste_horiz hνsq
  -- ## Step 3c: the two pullback presentations of the chart-restricted total space
  set j : pullback π'' U.1.ι ⟶ Qe := pullback.fst π'' U.1.ι with hjdef
  haveI : IsOpenImmersion j := by
    rw [hjdef]
    infer_instance
  set pU : pullback π'' U.1.ι ⟶ U.1.toScheme := pullback.snd π'' U.1.ι with hpUdef
  set pE : pullback qE j ⟶ EE := pullback.fst qE j with hpEdef
  set pQ : pullback qE j ⟶ pullback π'' U.1.ι := pullback.snd qE j with hpQdef
  have hQ'sq : IsPullback j pU π'' U.1.ι := IsPullback.of_hasPullback π'' U.1.ι
  have hPBsq : IsPullback pE pQ qE j := IsPullback.of_hasPullback qE j
  -- the `U`-cospan presentation of `pullback qE j`
  have hbig : IsPullback (pQ ≫ pU) pE U.1.ι (πE ≫ invariantsπ G A ℤ) := by
    have h1 := hPBsq.flip.paste_horiz hQ'sq.flip
    rw [hsq.w] at h1
    exact h1
  -- the `U`-cospan presentation of the localized model, from the given restriction square
  have hW₀Rsq : IsPullback (projModelπ W₀R ≫ κ) ρR U.1.ι (πE ≫ invariantsπ G A ℤ) :=
    hρsq.paste_horiz hAsq.flip
  -- the comparison iso
  set θ : (pullback qE j : Scheme) ≅ projModel W₀R :=
    hbig.isoIsPullback _ _ hW₀Rsq with hθdef
  have hθfst : θ.hom ≫ (projModelπ W₀R ≫ κ) = pQ ≫ pU :=
    hbig.isoIsPullback_hom_fst _ _ hW₀Rsq
  have hθsnd : θ.hom ≫ ρR = pE :=
    hbig.isoIsPullback_hom_snd _ _ hW₀Rsq
  -- ## Step 4: the localized action family and its invariance properties
  -- `Spec` of the localized action fixes `κ`
  have hκfix : ∀ g : G, Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom
      (fun g' : G => a.2 g') g)) ≫ κ = κ := by
    intro g
    have hringL : CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A))))
        ≫ CommRingCat.ofHom (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)
        = CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)
          ≫ CommRingCat.ofHom (algebraMap A (Localization.Away ((a : A)))) := by
      ext r
      exact MulSemiringAction.awayHom_algebraMap (fun g' : G => a.2 g') g r
    have hL : Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom
        (fun g' : G => a.2 g') g)) ≫ iAA = iAA ≫ specSMul g := by
      rw [hiAA, ← Spec.map_comp, hringL, Spec.map_comp]
      rfl
    rw [← cancel_mono U.1.ι, Category.assoc, hκι, ← Category.assoc, hL, Category.assoc,
      specSMul_invariantsπ]
  -- the localized action family (`exists_actLoc` inlined, one localization level down)
  have hfixA : ∀ g' : G, g' • ((a : A)) = (a : A) := fun g' => a.2 g'
  letI := MulSemiringAction.away hfixA
  set actR : G → (projModel W₀R ⟶ projModel W₀R) := fun g =>
    eqToHom (congrArg projModel (hCvcR g).symm)
      ≫ (projModelVCIso (CvcR g)
          (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
      ≫ projModelBaseChange (MulSemiringAction.awayHom (fun g' : G => a.2 g') g) W₀R
    with hactRdef
  have transπ' : ∀ {V V' : WeierstrassCurve (Localization.Away ((a : A)))} (h : V = V'),
      eqToHom (congrArg projModel h) ≫ projModelπ V' = projModelπ V := by
    rintro V V' rfl; simp
  -- (π-leg) `actR g` is over `Spec (awayHom g)`
  have hactπ : ∀ g : G, actR g ≫ projModelπ W₀R
      = projModelπ W₀R ≫ Spec.map (CommRingCat.ofHom
          (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)) := by
    intro g
    show (eqToHom (congrArg projModel (hCvcR g).symm)
        ≫ (projModelVCIso (CvcR g)
            (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
        ≫ projModelBaseChange (MulSemiringAction.awayHom (fun g' : G => a.2 g') g) W₀R)
        ≫ projModelπ W₀R = _
    simp only [Category.assoc]
    rw [projModelBaseChange_π,
      reassoc_of% (projModelVCIso_π (CvcR g)
        (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))),
      reassoc_of% (transπ' (hCvcR g).symm)]
  -- (κ-leg) `actR g` fixes the `κ`-composite
  have hactπκ : ∀ g : G, actR g ≫ (projModelπ W₀R ≫ κ) = projModelπ W₀R ≫ κ := by
    intro g
    rw [← Category.assoc, hactπ g, Category.assoc, hκfix g]
  -- (ρ-leg) `actR g` intertwines `ρR` with the geometric action — the hypothesis
  have hactρ : ∀ g : G, actR g ≫ ρR = ρR ≫ actE g := fun g => hρact g
  -- (comparison leg) `actR g` coequalizes into the descent comparison
  have hR₀ : ∀ (g : G) (r₀ : Localization.Away a),
      g • (algebraMap (Localization.Away a) (Localization.Away ((a : A))) r₀)
        = algebraMap (Localization.Away a) (Localization.Away ((a : A))) r₀ := by
    intro g r₀
    rw [halg]
    show MulSemiringAction.awayHom hfixA g (fixedAwayMap a r₀) = fixedAwayMap a r₀
    exact congrArg
      (fun f : Localization.Away a →+* Localization.Away ((a : A)) => f r₀)
      (awayHom_comp_fixedAwayMap a g)
  have hE : ∀ g : G, CvcR g = E * (g • E)⁻¹ := by
    intro g
    have h2 : E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g) = g • E :=
      variableChange_map_awayHom (fun g' : G => a.2 g') g E
    rw [hcob g, h2]
  have hactψ : ∀ g : G, actR g ≫ ψ₀ = ψ₀ := by
    intro g
    refine descentComparison_invariant W₀R W₁ E hW₁' CvcR (fun g' => hCvcR g') hE hR₀
      actR (fun g' => ?_) g
    show (projModelVCIso (CvcR g')
        (W₀R.map (MulSemiringAction.awayHom (fun g'' : G => a.2 g'') g'))).hom
      ≫ projModelBaseChange (MulSemiringAction.awayHom (fun g'' : G => a.2 g'') g') W₀R
      = eqToHom (congrArg projModel (hCvcR g')) ≫ actR g'
    rw [hactRdef]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  -- the comparison morphism on the chart-restricted cover
  set f : (pullback qE j : Scheme.{u}) ⟶ projModel W := θ.hom ≫ ψ₀ ≫ ν with hfdef
  -- invariance of `f`, for an abstract endomorphism with the two projection properties
  have hMkey : ∀ (g : G) (M : (pullback qE j : Scheme.{u}) ⟶ pullback qE j),
      M ≫ pQ = pQ → M ≫ pE = pE ≫ actE g → M ≫ f = f := by
    intro g M hMpQ hMpE
    have hMθ : M ≫ θ.hom = θ.hom ≫ actR g := by
      refine hW₀Rsq.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hactπκ g, hθfst, ← Category.assoc, hMpQ]
      · simp only [Category.assoc]
        rw [hactρ g, reassoc_of% hθsnd, hθsnd, hMpE]
    rw [hfdef, ← Category.assoc, hMθ, Category.assoc, reassoc_of% (hactψ g)]
  -- ## the descended morphism
  obtain ⟨cmp, hcmp₀⟩ := hlift j f (fun g => hMkey g _
    (by rw [hpQdef]; simp only [pullback.lift_snd, Category.comp_id])
    (by rw [hpEdef]; simp only [pullback.lift_fst]))
  have hcmp : pQ ≫ cmp = f := hcmp₀
  haveI hpQepi : Epi pQ := by
    rw [hpQdef]
    exact hepi j
  -- the `π`-leg of the comparison
  have hcmpπ : cmp ≫ projModelπ W = pU ≫ U.2.isoSpec.hom := by
    rw [← cancel_epi pQ, ← Category.assoc, hcmp, hfdef, Category.assoc, Category.assoc,
      hνsq.w, reassoc_of% hψsq.w, ← reassoc_of% hθfst, hκiso]
  -- ## Step 5: `cmp` is an isomorphism (fppf descent of `θ`)
  have hPBR : IsPullback (θ.hom ≫ projModelπ W₀R) pQ κ pU := by
    refine IsPullback.of_right ?_ ?_ hAsq
    · have h1 := hPBsq.paste_horiz hsq.flip
      rw [hQ'sq.w] at h1
      have hfst : (θ.hom ≫ projModelπ W₀R) ≫ iAA = pE ≫ πE := by
        rw [Category.assoc, hρsq.w, ← Category.assoc, hθsnd]
      rw [← hfst] at h1
      exact h1
    · rw [Category.assoc]
      exact hθfst
  have hs₅ : IsPullback (θ.hom ≫ projModelπ W₀R) pQ (specFam ≫ kF.hom)
      (pU ≫ U.2.isoSpec.hom) := by
    have h2 : IsPullback pU (𝟙 (pullback π'' U.1.ι : Scheme.{u})) U.2.isoSpec.hom
        (pU ≫ U.2.isoSpec.hom) := by
      refine IsPullback.of_vert_isIso ⟨?_⟩
      rw [Category.id_comp]
    have h3 := hPBR.paste_vert h2
    rw [Category.comp_id, hκiso] at h3
    exact h3
  have hspecFamFppf : specFam = κ ≫ U.2.isoSpec.hom ≫ kF.inv := by
    rw [← Category.assoc, hκiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : Surjective specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : Flat specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : QuasiCompact specFam := by
    rw [hspecFamFppf]
    infer_instance
  haveI : Surjective ψ₀ := MorphismProperty.of_isPullback (P := @Surjective) hψsq.flip ‹_›
  haveI : Flat ψ₀ := MorphismProperty.of_isPullback (P := @Flat) hψsq.flip ‹_›
  haveI : QuasiCompact ψ₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) hψsq.flip ‹_›
  haveI : IsIso cmp := by
    have hLsq : IsPullback θ.hom pQ (ψ₀ ≫ ν) cmp := by
      refine IsPullback.of_right ?_ ?_ hψν.flip
      · rw [← hcmpπ] at hs₅
        exact hs₅
      · rw [hcmp, hfdef]
    exact isIso_of_isPullback_of_fppf hLsq
  -- ## Step 6: packaging
  refine ⟨asIso cmp, ?_, ?_⟩
  · show cmp ≫ projModelπ W = pullback.snd π'' U.1.ι ≫ U.2.isoSpec.hom
    rw [← hpUdef]
    exact hcmpπ
  · -- the zero-section leg, by cancelling the fppf cover
    show (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ cmp
      = projModelZero W
    haveI hpUepi : Epi pU := by
      have hsplit : (pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
          (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ pU = 𝟙 _ := by
        rw [hpUdef]
        exact pullback.lift_snd _ _ _
      refine ⟨fun {Z} u v huv => ?_⟩
      rw [← Category.id_comp u, ← hsplit, Category.assoc, huv, ← Category.assoc, hsplit,
        Category.id_comp]
    haveI hκepi : Epi κ := by
      haveI h2 : Epi ((θ.hom ≫ projModelπ W₀R) ≫ κ) := by
        rw [Category.assoc, hθfst]
        exact epi_comp pQ pU
      exact epi_of_epi (θ.hom ≫ projModelπ W₀R) κ
    haveI hbmapepi : Epi (specFam ≫ kF.hom) := by
      rw [← hκiso]
      exact epi_comp κ U.2.isoSpec.hom
    -- the ingredients of the zero-section chase
    have hbmapinv : (specFam ≫ kF.hom) ≫ U.2.isoSpec.inv = κ := by
      rw [← hκiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hζw : (iAA ≫ zeroE) ≫ qE = (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) ≫ j := by
      rw [Category.assoc, ← hzeroSq, hjdef, Category.assoc, pullback.lift_fst,
        reassoc_of% hκι]
    have hζpQ : pullback.lift (iAA ≫ zeroE) (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) hζw ≫ pQ
        = κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
          (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp]) := by
      rw [hpQdef]
      exact pullback.lift_snd _ _ _
    have hζθ : pullback.lift (iAA ≫ zeroE) (κ ≫ pullback.lift (U.1.ι ≫ zero'') (𝟙 _)
        (by rw [Category.assoc, hz'', Category.comp_id, Category.id_comp])) hζw ≫ θ.hom
        = projModelZero W₀R := by
      refine hW₀Rsq.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hθfst, ← Category.assoc, hζpQ, Category.assoc,
          reassoc_of% projModelZero_projModelπ]
        rw [hpUdef, pullback.lift_snd, Category.comp_id]
      · simp only [Category.assoc]
        rw [hθsnd, hpEdef, pullback.lift_fst, hρzero]
    have hz2 : projModelZero W ≫ projModelBaseChange req.toRingHom W₁
        = kF.inv ≫ projModelZero W₁ := by
      have h := projModelZero_baseChange₂ req.toRingHom W₁
      rw [hsR] at h
      exact h
    have hzν : projModelZero W₁ ≫ ν = kF.hom ≫ projModelZero W := by
      rw [hνdef, ← cancel_mono (projModelBaseChange req.toRingHom W₁), Category.assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, hz2, Iso.hom_inv_id_assoc]
    have hzψ : projModelZero W₀R ≫ ψ₀ = specFam ≫ projModelZero W₁ := by
      rw [hψ₀def, descentComparison_zero, hspecAlg]
    -- assemble
    rw [← cancel_epi (specFam ≫ kF.hom)]
    simp only [Category.assoc]
    rw [reassoc_of% hbmapinv, ← reassoc_of% hζpQ, hcmp, hfdef, reassoc_of% hζθ,
      reassoc_of% hzψ, hzν]

/-- Opaque-shape zero-square transport. -/
private theorem zeroSq_transport {Xs Qs EQ ET Ss Ss' : Scheme.{u}}
    {qX : Xs ⟶ Qs} {z' : Qs ⟶ EQ} {cz : Xs ⟶ ET} {qE : ET ⟶ EQ}
    {i : Xs ≅ Ss} {qiso : Qs ≅ Ss'} {ip : Ss ⟶ Ss'}
    (hz'c : qX ≫ z' = cz ≫ qE) (hq : qX ≫ qiso.hom = i.hom ≫ ip) :
    ip ≫ qiso.inv ≫ z' = (i.inv ≫ cz) ≫ qE := by
  have hip : ip = i.inv ≫ qX ≫ qiso.hom := by rw [hq, Iso.inv_hom_id_assoc]
  rw [hip]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hz'c]

/-- Opaque-shape section transport along an iso. -/
private theorem zero_transport {A B E P : Scheme.{u}} {i : A ≅ B} {cz : A ⟶ E}
    {f : E ⟶ P} {pz : B ⟶ P} (h : cz ≫ f = i.hom ≫ pz) :
    (i.inv ≫ cz) ≫ f = pz := by
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Opaque-shape conjugation coequalization. -/
private theorem conj_coequalize {E P Q : Scheme.{u}} {e : E ≅ P} {sE : E ⟶ E} {q : E ⟶ Q}
    (hsE : sE ≫ q = q) :
    (e.hom ≫ (e.inv ≫ sE ≫ e.hom) ≫ e.inv) ≫ q = q := by
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simpa using hsE

/-- Abstract corner transport for pullback squares (opaque-schemes shape, so applications are
first-order): compose the `snd`/`f` legs with corner isos. -/
private theorem isPullback_transport_corner {P Xc Y Z Y' Z' : Scheme.{u}} {fst : P ⟶ Xc}
    {snd : P ⟶ Y} {f : Xc ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (eY : Y ≅ Y') (eZ : Z ≅ Z') {snd' : P ⟶ Y'} {f' : Xc ⟶ Z'} {g' : Y' ⟶ Z'}
    (hsnd : snd ≫ eY.hom = snd') (hf : f ≫ eZ.hom = f') (hg : g ≫ eZ.hom = eY.hom ≫ g') :
    IsPullback fst snd' f' g' := by
  refine h.of_iso (Iso.refl _) (Iso.refl _) eY eZ ?_ ?_ ?_ hg
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.id_comp, hsnd]
  · rw [Iso.refl_hom, Category.id_comp, hf]

/-- Abstract reduction: `LocallyWeierstrass` transports along an iso of the base (with the total
space fixed). Stated over opaque schemes so the application never unfolds the heavy quotient/Spec
objects. -/
private theorem lw_of_baseIso {Q S T : Scheme.{u}} (π' : Q ⟶ S) (zero' : S ⟶ Q)
    (hz : zero' ≫ π' = 𝟙 S) (qiso : S ≅ T)
    (hspec : LocallyWeierstrass (π' ≫ qiso.hom) (qiso.inv ≫ zero')
      (by rw [Category.assoc, ← Category.assoc zero', hz, Category.id_comp, Iso.inv_hom_id])) :
    LocallyWeierstrass π' zero' hz := by
  refine hspec.of_iso (Iso.refl _) qiso ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable (σ σE) in
/-- Freeness of the lifted action, from freeness on the base (own heartbeat budget). -/
private theorem discharge_freeE (hact : IsCurveAction σ C σE)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T) :
    ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ C.E), t ≫ σE.hom γ = t → IsEmpty T := by
  intro γ hγ T t ht
  refine hfreeX γ hγ T (t ≫ C.π) ?_
  rw [Category.assoc, ← hact.π_equivariant γ, ← Category.assoc, ht]

/-- The conjugated transport action is coequalized by the quotient cover (own budget). -/
private theorem discharge_hEact [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀) :
    ∀ g, (φ.hom ≫ (σE.transport φ).hom g ≫ φ.inv)
      ≫ σE.quotientπ VE hVEs hVEa hVEmem = σE.quotientπ VE hVEs hVEa hVEmem := by
  intro g
  rw [SchemeAction.transport_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact σE.hom_quotientπ VE hVEs hVEa hVEmem g

/-- The restricted morphism-descent, in the conjugated-action shape (own budget). -/
private theorem discharge_hlift [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfreeE : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ C.E),
      t ≫ σE.hom γ = t → IsEmpty T)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀)
    (hEact : ∀ g, (φ.hom ≫ (σE.transport φ).hom g ≫ φ.inv)
      ≫ σE.quotientπ VE hVEs hVEa hVEmem = σE.quotientπ VE hVEs hVEa hVEmem) :
    ∀ {Q' Y : Scheme.{u}} (j : Q' ⟶ σE.quotient VE hVEs hVEa)
      [IsOpenImmersion j] (f : pullback (σE.quotientπ VE hVEs hVEa hVEmem) j ⟶ Y),
      (∀ g, pullback.map (σE.quotientπ VE hVEs hVEa hVEmem) j
          (σE.quotientπ VE hVEs hVEa hVEmem) j
          (φ.hom ≫ (σE.transport φ).hom g ≫ φ.inv) (𝟙 Q') (𝟙 _)
          (by rw [Category.comp_id, hEact g]) (by simp) ≫ f = f) →
      ∃ q : Q' ⟶ Y, pullback.snd (σE.quotientπ VE hVEs hVEa hVEmem) j ≫ q = f := by
  intro Q' Y j hj f hf
  -- adapt the local (old-order) free-action hypothesis to the canonical
  -- `SchemeQuotient` order `∀ {T} (t) (g), …` that the consumer now expects.
  refine σE.exists_quotientπ_lift_of_isOpenImmersion VE hVEs hVEa hVEmem
    (fun t g hg h => hfreeE g hg _ t h) j f ?_
  intro g
  have hmap_eq : pullback.map (σE.quotientπ VE hVEs hVEa hVEmem) j
      (σE.quotientπ VE hVEs hVEa hVEmem) j (σE.hom g) (𝟙 Q') (𝟙 _)
      (by rw [Category.comp_id, σE.hom_quotientπ]) (by simp)
    = pullback.map (σE.quotientπ VE hVEs hVEa hVEmem) j
      (σE.quotientπ VE hVEs hVEa hVEmem) j
      (φ.hom ≫ (σE.transport φ).hom g ≫ φ.inv) (𝟙 Q') (𝟙 _)
      (by rw [Category.comp_id, hEact g]) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, SchemeAction.transport_hom,
        Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp only [Category.assoc, pullback.lift_snd]
  rw [hmap_eq]
  exact hf g

/-- The restricted morphism-descent, in the plain (unconjugated) action shape consumed by
`lw_chart_at_of_localModel` (own budget). -/
private theorem discharge_hlift' [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfreeE : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ C.E),
      t ≫ σE.hom γ = t → IsEmpty T) :
    ∀ {Q' Y : Scheme.{u}} (j : Q' ⟶ σE.quotient VE hVEs hVEa)
      [IsOpenImmersion j] (f : pullback (σE.quotientπ VE hVEs hVEa hVEmem) j ⟶ Y),
      (∀ g, pullback.map (σE.quotientπ VE hVEs hVEa hVEmem) j
          (σE.quotientπ VE hVEs hVEa hVEmem) j (σE.hom g) (𝟙 Q') (𝟙 _)
          (by rw [Category.comp_id, σE.hom_quotientπ]) (by simp) ≫ f = f) →
      ∃ q : Q' ⟶ Y, pullback.snd (σE.quotientπ VE hVEs hVEa hVEmem) j ≫ q = f := by
  intro Q' Y j hj f hf
  exact σE.exists_quotientπ_lift_of_isOpenImmersion VE hVEs hVEa hVEmem
    (fun t g hg h => hfreeE g hg _ t h) j f hf

/-- The restricted-cover epi property, in ∀-shape (own budget). -/
private theorem discharge_hepi [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfreeE : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ C.E),
      t ≫ σE.hom γ = t → IsEmpty T) :
    ∀ {Q' : Scheme.{u}} (j : Q' ⟶ σE.quotient VE hVEs hVEa) [IsOpenImmersion j],
      Epi (pullback.snd (σE.quotientπ VE hVEs hVEa hVEmem) j) := by
  intro Q' j hj
  exact σE.epi_pullback_snd_quotientπ VE hVEs hVEa hVEmem
    (fun t g hg h => hfreeE g hg _ t h) j

set_option backward.isDefEq.respectTransparency false in
theorem locallyWeierstrass_quotientπ_of_globalModel [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀) (hW₀ : W₀.IsElliptic)
    (hπφ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzeroφ : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa)
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa))
    (hπ'c : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (hzero'c : σ.quotientπ V hVs hVa hVmem ≫ zero'
      = C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) :
    LocallyWeierstrass π' zero' hz := by
  classical
  cases nonempty_fintype G
  rcases isEmpty_or_nonempty (↥X) with hX | hX
  · intro s
    obtain ⟨x, -⟩ := σ.quotientπ_surjective V hVs hVa hVmem s
    exact (hX.false x).elim
  obtain ⟨x₀⟩ := hX
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  obtain ⟨qiso, hqiso⟩ := σ.exists_quotientIsoSpec_top V hVs hVa hVmem hVtop x₀
  have hz'' : (qiso.inv ≫ zero') ≫ (π' ≫ qiso.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc zero', hz, Category.id_comp, Iso.inv_hom_id]
  -- the cocycle + freeness over Γ(X,⊤)
  have hfreeA : IsFreeAlgebraAction G ℤ ↑Γ(X, ⊤) :=
    σ.isFreeAlgebraAction_of_free (isStableOpen_top σ) (isAffineOpen_top X) hfreeX
  obtain ⟨Cvc, hCvc, hcoc, hΨ⟩ := exists_cocycle_of_globalModel' hact W₀ φ hπφ hzeroφ
  -- the Spec-side local model
  have hfreeE := discharge_freeE σ σE hact hfreeX
  have hspec : LocallyWeierstrass (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz'' := by
    intro s
    haveI := s.isPrime
    obtain ⟨a, hap, W₁, E, hW₁, hcob⟩ :=
      exists_away_invariant_descent hfreeA W₀ hcoc hCvc s.asIdeal
    exact lw_chart_at (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz''
      (σE.quotientπ VE hVEs hVEa hVEmem) (C.π ≫ X.isoSpec.hom) (X.isoSpec.inv ≫ C.zero)
      (isPullback_transport_corner
        (isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfreeX π' hπ'c)
        X.isoSpec qiso rfl rfl hqiso)
      (zeroSq_transport hzero'c hqiso)
      W₀ hW₀ φ hπφ (zero_transport hzeroφ) ((σE.transport φ).hom)
      (discharge_hEact VE hVEs hVEa hVEmem W₀ φ)
      Cvc hCvc hcoc hΨ
      (discharge_hlift VE hVEs hVEa hVEmem hfreeE W₀ φ
        (discharge_hEact VE hVEs hVEa hVEmem W₀ φ))
      (discharge_hepi VE hVEs hVEa hVEmem hfreeE)
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.2
      hfreeA s a hap W₁ E hW₁ hcob
  exact lw_of_baseIso π' zero' hz qiso hspec

/-! #### The `[a5]` reduction: splitting off the section-pair gap

`locallyWeierstrass_quotientπ` below quantifies over a pair `(π', zero')` carrying the descent
compatibilities `hπ'c`/`hzero'c` tying it to the descended structure maps (the board's v10.94
owed statement fix — for a wild pair the statement is FALSE, see the deleted `[a5-pair]`
counterexample in the git history). `locallyWeierstrass_quotientπ_of_compat` is the true,
board-owned `[a5]` content. Its engine consumption is now PROVEN in full generality
(`lw_chart_at_of_localModel`, no global model needed); the ONE residual leaf is the localized
model package `exists_localModel_package_at` — the a5-P-loc semilocal gluing. The empty-base
case and the assembly are proven. -/

open WeierstrassCurve in
/-- **([a5-P-loc], the localized model package — THE residual leaf, board-owned)** At every
prime `s` of `Aᴳ = Γ(X,⊤)ᴳ` there is an invariant `a ∉ s` over whose basic open the curve
acquires a global Weierstrass model compatible with the `G`-action: the model `W₀R / A_a`,
with `projModel W₀R` presented as the restriction of `E` along `Spec A_a ⟶ Spec A ≅ X`
(`ρR`/the pullback square/the zero-leg), the `VariableChange` cocycle `CvcR / A_a` presenting
the geometric action through `ρR` (T-W7.1b at the `A_a`-level), and the Hilbert-90 descent
data `W₁ / (Aᴳ)_a`, `E` with the coboundary identity.

Everything downstream is PROVEN: `lw_chart_at_of_localModel` consumes exactly this package
and lands the `LocallyWeierstrass` chart at `s` (see
`locallyWeierstrass_quotientπ_of_compat` below). With a *global* model the package is
immediate (`W₀R := W₀.map (algebraMap _ _)`, `ρR := projModelBaseChange ≫ φ.inv`,
`CvcR g := (Cvc g).map _` — this is how `locallyWeierstrass_quotientπ_of_globalModel`
specializes), but in general a global model is obstructed by the class of `ω` in
`Pic Γ(X,⊤)`, and the package must be produced semilocally:

Proof plan (KM 2.2.5–2.2.6 + the a5-P-loc board): the fibre of `Spec A → Spec Aᴳ` over `s` is
one finite `G`-orbit (`Aᴳ ⊆ A` is an invariant-integral extension; mathlib's
`Algebra.IsInvariant` transitivity). Each orbit point has a `C.localModel` chart; shrink the
charts to basic opens `D(f_i)`. Over the orbit's semilocalization `L := Localization S`,
`S = s.primeCompl.map (algebraMap Aᴳ A)` (the ring of `exists_away_invariant_descent`,
Part 1 — its fixed subring is LOCAL by `isLocalRing_fixedPoints_of_isLocalization`), the
`D(f_i)` cover `Spec L` (every prime of the semilocal `L` lies under an orbit maximal, and
`f_i ∉ q_i`), and the chart-difference `VariableChange` Čech 1-cocycle on this finite cover
splits: the unit part because a unit-valued Čech cocycle on a semilocal ring is a coboundary
(the maximal ideals are the finitely many orbit primes — the avoidance argument of
`exists_unit_smul_eq_of_isLocalRing`), the additive part by the affine Čech vanishing
(partition of unity in the `f_i`; cf. `exists_sub_smul_eq_of_isCocycle`). The corrected charts
glue to a model over `L` (sheaf condition for the basic cover); T-W7.1b over `L`
(`pointedIso_exists_variableChange`) gives the `G`-cocycle; `exists_coboundary` over `L`
splits it and `descendFixed` produces `W₁`. Finally SPREAD: the finitely many coefficients,
variable changes and identities have finitely many denominators in `S` — clear them into a
single invariant `a ∉ s` exactly as in Part 2 of `exists_away_invariant_descent` — and glue
the finitely many corrected chart isos over the basic cover of `D((a : A))` (e.g. by
`Scheme.OpenCover.glueMorphisms`) to produce `ρR` and its two legs. -/
private theorem exists_localModel_package_at [Finite G] [IsAffine X]
    (hact : IsCurveAction σ C σE)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
    ∀ _s : ↥(Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, ⊤) G))),
    ∃ (a : FixedPoints.subring ↑Γ(X, ⊤) G) (_ : a ∉ _s.asIdeal)
      (W₀R : WeierstrassCurve (Localization.Away ((a : ↑Γ(X, ⊤))))),
      W₀R.IsElliptic ∧
      ∃ ρR : projModel W₀R ⟶ C.E,
        IsPullback (projModelπ W₀R) ρR
          (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
            (Localization.Away ((a : ↑Γ(X, ⊤))))))) (C.π ≫ X.isoSpec.hom) ∧
        projModelZero W₀R ≫ ρR
          = Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤)
              (Localization.Away ((a : ↑Γ(X, ⊤)))))) ≫ X.isoSpec.inv ≫ C.zero ∧
        ∃ (CvcR : G → VariableChange (Localization.Away ((a : ↑Γ(X, ⊤)))))
          (hCvcR : ∀ g, CvcR g
            • (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g)) = W₀R),
          (∀ g, (eqToHom (congrArg projModel (hCvcR g).symm)
              ≫ (projModelVCIso (CvcR g)
                  (W₀R.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))).hom
              ≫ projModelBaseChange (MulSemiringAction.awayHom
                  (fun g' : G => a.2 g') g) W₀R) ≫ ρR = ρR ≫ σE.hom g) ∧
          ∃ (W₁ : WeierstrassCurve (Localization.Away a))
            (E : VariableChange (Localization.Away ((a : ↑Γ(X, ⊤))))),
            W₁.map (fixedAwayMap a) = E⁻¹ • W₀R ∧
            ∀ g : G, CvcR g
              = E * (E.map (MulSemiringAction.awayHom (fun g' : G => a.2 g') g))⁻¹ := by
  sorry

/-- **([a5-compat], the true half — ENGINE PROVEN; residual = the localized model package)**
`locallyWeierstrass_quotientπ` for a section pair carrying the descent compatibilities
`hπ'c`/`hzero'c` of `exists_quotient_π_zero` — the shape the board's owed `[a5]` statement fix
arrives at.

PROVEN via the localized Phase-A engine: per point `s` of `X/G ≅ Spec Aᴳ`
(`exists_quotientIsoSpec_top`), the localized model package `exists_localModel_package_at`
(the ONE residual sorry — the a5-P-loc semilocal gluing, see its docstring for the boarded
proof) feeds `lw_chart_at_of_localModel`, which lands the chart at `s`; `lw_of_baseIso`
transports back along `qiso`. This is the general (`C.localModel`-only) route: `hVtop`
trivialises the **base** atlas `V` only — a global model upstairs is genuinely obstructed
(the class of `ω` in `Pic Γ(X,⊤)`), which is why the model data enters localized at an
invariant basic open `D(a)`, `a ∉ s`. -/
private theorem locallyWeierstrass_quotientπ_of_compat [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (hX : Nonempty ↥X)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa)
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa))
    (hπ'c : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (hzero'c : σ.quotientπ V hVs hVa hVmem ≫ zero'
      = C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) :
    LocallyWeierstrass π' zero' hz := by
  classical
  cases nonempty_fintype G
  obtain ⟨x₀⟩ := hX
  letI := σ.gammaMulSemiringAction (isStableOpen_top σ)
  obtain ⟨qiso, hqiso⟩ := σ.exists_quotientIsoSpec_top V hVs hVa hVmem hVtop x₀
  have hz'' : (qiso.inv ≫ zero') ≫ (π' ≫ qiso.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc zero', hz, Category.id_comp, Iso.inv_hom_id]
  -- the freeness over Γ(X,⊤), upstairs and on the fibre product
  have hfreeA : IsFreeAlgebraAction G ℤ ↑Γ(X, ⊤) :=
    σ.isFreeAlgebraAction_of_free (isStableOpen_top σ) (isAffineOpen_top X) hfree
  have hfreeE := discharge_freeE σ σE hact hfree
  -- the Spec-side local model, per point from the localized model package
  have hspec : LocallyWeierstrass (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz'' := by
    intro s
    obtain ⟨a, hap, W₀R, hW₀R, ρR, hρsq, hρzero, CvcR, hCvcR, hρact, W₁, E, hW₁, hcob⟩ :=
      exists_localModel_package_at hact hfree s
    exact lw_chart_at_of_localModel (π' ≫ qiso.hom) (qiso.inv ≫ zero') hz''
      (σE.quotientπ VE hVEs hVEa hVEmem) (C.π ≫ X.isoSpec.hom) (X.isoSpec.inv ≫ C.zero)
      (isPullback_transport_corner
        (isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ'c)
        X.isoSpec qiso rfl rfl hqiso)
      (zeroSq_transport hzero'c hqiso)
      σE.hom (σE.hom_quotientπ VE hVEs hVEa hVEmem)
      (discharge_hlift' VE hVEs hVEa hVEmem hfreeE)
      (discharge_hepi VE hVEs hVEa hVEmem hfreeE)
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.1
      (fppf_invariantsπ (G := G) (B := ↑Γ(X, ⊤)) hfreeA).2.2
      s a hap W₀R hW₀R ρR hρsq hρzero CvcR hCvcR hρact W₁ E hW₁ hcob
  exact lw_of_baseIso π' zero' hz qiso hspec

/-- **([a5], the descended Weierstrass model — LEAF; STATEMENT FIX EXECUTED v10.324-FIN)** The
quotient curve `E/G ⟶ X/G` admits a Zariski-local Weierstrass model, for the section pair
COMPATIBLE with the quotient charts (`hπ'c`/`hzero'c` — the v10.94 owed interface fix; the
unconstrained form was FALSE, see the deleted `[a5-pair]` counterexample in the git history:
twist the canonical pair by a split endomorphism of `Spec ℚ[x₁,x₂,…]`).

Plan (terminating in a proof; the one genuinely new-math leaf of route (a)): the universal curve
upstairs has a global model `E = projModel W` (in the bootstrap `E` is pulled back from T-E15's
explicit `ℰ₃`), and each `γ ∈ G` acts on it by a `VariableChange` `C_γ = (u_γ, r_γ, s_γ, t_γ)`
(**T-W7.1b** = `pointedIso_exists_variableChange`, now DONE). Splitting the cocycle:
* the additive part `(r, s, t) ∈ Z¹(G, A⁺)` is a coboundary by `exists_sub_smul_eq_of_isCocycle`
  (additive Hilbert 90, PROVEN);
* the multiplicative part `u ∈ Z¹(G, Aˣ)` is **Zariski-locally** a coboundary by
  `exists_unit_smul_eq_of_isLocalRing` ([A711-DESC], PROVEN).
So over a Zariski neighbourhood of each prime of `Aᴳ`, a variable change makes `W` `G`-invariant,
and the invariant model descends to give the local Weierstrass model of `E/G`. -/
theorem locallyWeierstrass_quotientπ [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (zero' : σ.quotient V hVs hVa ⟶ σE.quotient VE hVEs hVEa)
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa))
    (hπ'c : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem)
    (hzero'c : σ.quotientπ V hVs hVa hVmem ≫ zero'
      = C.zero ≫ σE.quotientπ VE hVEs hVEa hVEmem) :
    LocallyWeierstrass π' zero' hz := by
  rcases isEmpty_or_nonempty (↥X) with hX | hX
  · intro s
    obtain ⟨x, -⟩ := σ.quotientπ_surjective V hVs hVa hVmem s
    exact (hX.false x).elim
  · exact locallyWeierstrass_quotientπ_of_compat hact V hVs hVa hVmem hVtop
      VE hVEs hVEa hVEmem hfree hX π' zero' hz hπ'c hzero'c

/-- **([a3]–[a5], the route-(a) descent theorem — ASSEMBLED)** Let `G` act freely on an affine
scheme `X`, and let the action lift to a geometric elliptic curve `C/X` (an `IsCurveAction`) with
an orbit-in-affine-open chart datum. Then the quotient `E/G` carries a geometric elliptic curve
structure over `X/G`, and the square

    E ──────▶ E/G
    │           │
    π           π'
    ▼           ▼
    X ──────▶ X/G

is **cartesian** and compatible with the zero sections — precisely an `Ell/R`-morphism, which is
what the KM engine consumes.

**This assembly is sorry-free.** It consumes exactly:
* `exists_quotient_π_zero` (PROVEN) — the descended `π'`, `zero'` and `zero' ≫ π' = 𝟙`;
* `locallyWeierstrass_quotientπ` (leaf `[a5]`, gated on nothing — T-W7.1b is DONE) — the local
  Weierstrass model of the quotient curve;
* `isProper_of_locallyWeierstrass` (PROVEN) and `smoothOfRelativeDimension_of_locallyWeierstrass`
  (leaf, waits on T-A3) — `proper` and `smooth` from that model;
* `isPullback_quotientπ` (PROVEN modulo the affine chart square `isPullback_chart`) — the
  cartesian square.

So the KM 4.7 ⇐-engine's geometric core is **structurally complete**: the two residual sorries are
the isolated affine computations `isPullback_chart` (Galois descent of `Γ(W)`) and
`locallyWeierstrass_quotientπ`/`smoothOfRelativeDimension_of_locallyWeierstrass` ([a5] + T-A3). -/
theorem exists_ellipticCurveGeom_quotient [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    (horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U) :
    ∃ (C' : EllipticCurveGeom (σ.quotient V hVs hVa)) (q : C.E ⟶ C'.E),
      IsPullback q C.π C'.π (σ.quotientπ V hVs hVa hVmem) ∧
        C.zero ≫ q = σ.quotientπ V hVs hVa hVmem ≫ C'.zero := by
  -- the `G`-stable affine atlas of `E` (from the orbit chart datum)
  choose VE hVEs hVEa hVEmem using
    fun e => exists_isStableOpen_isAffineOpen_of_orbit horbit e
  -- descend `π` and the zero section
  obtain ⟨π', zero', hπ', hzero', hzπ'⟩ :=
    exists_quotient_π_zero hact V hVs hVa hVmem VE hVEs hVEa hVEmem
  -- the descended local Weierstrass model, and proper/smooth from it
  have hlw := locallyWeierstrass_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree
    π' zero' hzπ' hπ' hzero'
  haveI hproper : IsProper π' := isProper_of_locallyWeierstrass hlw
  haveI hsmooth : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_of_locallyWeierstrass hlw
  -- assemble the geometric elliptic curve on `E/G`
  refine ⟨{ E := σE.quotient VE hVEs hVEa, π := π', zero := zero', zero_π := hzπ'
            smooth := hsmooth, proper := hproper, localModel := hlw },
    σE.quotientπ VE hVEs hVEa hVEmem, ?_, ?_⟩
  · exact isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ'
  · exact hzero'.symm


/-- **([a3]–[a5] ASSEMBLED, global-model form — the KM 4.7 ⇐-engine, Phase A)** Let `G` act
freely on an affine `X`, lifted to a geometric elliptic curve `C/X` carrying a compatible global
Weierstrass model `φ : C.E ≅ projModel W₀` (as the intended applications do — Hesse/Legendre).
Then `E/G` carries a geometric elliptic curve structure over `X/G`, cartesian over `X → X/G` and
compatible with the zero sections — precisely the `Ell/R`-morphism the KM engine consumes.
The orbit-in-affine-open datum is *derived* from the global model
(`exists_charts_of_globalModel`), and the local Weierstrass model of the quotient is
`locallyWeierstrass_quotientπ_of_globalModel` ([a5], PROVEN). Smoothness routes through
`smoothOfRelativeDimension_of_locallyWeierstrass` (T-A3, the one open leaf, owner beastmode-A). -/
theorem exists_ellipticCurveGeom_quotient_of_globalModel [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x) (hVtop : ∀ x, V x = ⊤)
    (hfreeX : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (W₀ : WeierstrassCurve Γ(X, ⊤)) (φ : C.E ≅ projModel W₀) (hW₀ : W₀.IsElliptic)
    (hπφ : φ.hom ≫ projModelπ W₀ = C.π ≫ X.isoSpec.hom)
    (hzeroφ : C.zero ≫ φ.hom = X.isoSpec.hom ≫ projModelZero W₀) :
    ∃ (C' : EllipticCurveGeom (σ.quotient V hVs hVa)) (q : C.E ⟶ C'.E),
      IsPullback q C.π C'.π (σ.quotientπ V hVs hVa hVmem) ∧
        C.zero ≫ q = σ.quotientπ V hVs hVa hVmem ≫ C'.zero ∧
        ∀ γ : G, σE.hom γ ≫ q = q := by
  -- the `G`-stable affine atlas of `E`, derived from the global model
  have horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U := by
    obtain ⟨U₀, U₁, h0, h1, hz0, hz1⟩ := exists_charts_of_globalModel φ
      (Scheme.homeoOfIso X.isoSpec).surjective hzeroφ
    exact fun e => orbit_mem_isAffineOpen_of_charts hact h0 h1 hz0 hz1 e
  choose VE hVEs hVEa hVEmem using
    fun e => exists_isStableOpen_isAffineOpen_of_orbit horbit e
  -- descend `π` and the zero section
  obtain ⟨π', zero', hπ', hzero', hzπ'⟩ :=
    exists_quotient_π_zero hact V hVs hVa hVmem VE hVEs hVEa hVEmem
  -- the descended local Weierstrass model ([a5], PROVEN), and proper/smooth from it
  have hlw := locallyWeierstrass_quotientπ_of_globalModel hact V hVs hVa hVmem hVtop
    VE hVEs hVEa hVEmem hfreeX W₀ φ hW₀ hπφ hzeroφ π' zero' hzπ' hπ' hzero'
  haveI hproper : IsProper π' := isProper_of_locallyWeierstrass hlw
  haveI hsmooth : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_of_locallyWeierstrass hlw
  refine ⟨{ E := σE.quotient VE hVEs hVEa, π := π', zero := zero', zero_π := hzπ',
            smooth := hsmooth, proper := hproper, localModel := hlw },
    σE.quotientπ VE hVEs hVEa hVEmem, ?_, hzero'.symm, ?_⟩
  · exact isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfreeX π' hπ'
  · exact fun γ => σE.hom_quotientπ VE hVEs hVEa hVEmem γ

end ModularCurves.RouteA
