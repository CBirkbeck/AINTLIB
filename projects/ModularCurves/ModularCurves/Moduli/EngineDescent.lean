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
  sorry

/-- **([a5], the descended Weierstrass model — LEAF)** The quotient curve `E/G ⟶ X/G` admits a
Zariski-local Weierstrass model.

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
    (hz : zero' ≫ π' = 𝟙 (σ.quotient V hVs hVa)) :
    LocallyWeierstrass π' zero' hz := by
  sorry

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
    π' zero' hzπ'
  haveI hproper : IsProper π' := isProper_of_locallyWeierstrass hlw
  haveI hsmooth : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_of_locallyWeierstrass hlw
  -- assemble the geometric elliptic curve on `E/G`
  refine ⟨{ E := σE.quotient VE hVEs hVEa, π := π', zero := zero', zero_π := hzπ'
            smooth := hsmooth, proper := hproper, localModel := hlw },
    σE.quotientπ VE hVEs hVEa hVEmem, ?_, ?_⟩
  · exact isPullback_quotientπ hact V hVs hVa hVmem hVtop VE hVEs hVEa hVEmem hfree π' hπ'
  · exact hzero'.symm

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
