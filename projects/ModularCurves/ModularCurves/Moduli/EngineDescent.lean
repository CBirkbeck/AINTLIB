/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.EllipticCurve.ModelVariableChange

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

/-! ### The route-(a) descent theorem (leaves `[a3]`–`[a5]`) -/

/-- **([a3]–[a5], the route-(a) descent theorem)** Let `G` act freely on an affine scheme `X`
with a `G`-stable affine atlas, and let the action lift to a geometric elliptic curve
`C/X` (an `IsCurveAction`) with an orbit-in-affine-open chart datum. Then the quotient
`E/G` carries a geometric elliptic curve structure over `X/G`, and the square

    E ──────▶ E/G
    │           │
    π           π'
    ▼           ▼
    X ──────▶ X/G

is **cartesian** and compatible with the zero sections — i.e. it is an `Ell/R`-morphism, which
is precisely what the KM engine consumes.

Plan (terminating in a proof; each item is a boarded leaf):
* `[a3]` `E/G` exists as `SchemeAction.quotient σE VE hVEs hVEa`
  (`exists_isStableOpen_isAffineOpen_of_orbit` supplies the atlas), `π'` is the unique descent
  of `π ≫ quotientπ_X` (`existsUnique_quotientπ_lift`, invariance from `IsCurveAction.π_equivariant`),
  and `zero'` descends dually. The square is cartesian because both horizontal maps are
  `G`-torsors: on a stable affine chart both quotients are `Spec` of invariants, and
  `torsorMul_bijective_of_isFreeAlgebraAction` (T-Q2, PROVEN) identifies
  `Γ(E) ⊗_{Γ(E)ᴳ} Γ(X)ᴳ ≅ Γ(E) ⊗_{Γ(X)} Γ(X)`… i.e. `E ≅ (E/G) ×_{X/G} X`.
* `[a4]` `π'` is proper and smooth of relative dimension 1: both properties descend along the
  finite étale surjection `X → X/G` (`Algebra.Etale.of_isFreeAlgebraAction_of_isNoetherianRing`
  + `Module.Finite.of_isFreeAlgebraAction` + `torsorMul_bijective_of_isFreeAlgebraAction`,
  all PROVEN) via AINTLIB's DESC engine for fppf-local-at-target morphism properties.
* `[a5]` `localModel`: Zariski-locally on `X/G = Spec Aᴳ`, the Weierstrass model of `E`
  descends. The `G`-action on `E = projModel W` is by `VariableChange`s `C_γ = (u_γ, r_γ, s_γ, t_γ)`
  (T-W7.1b, in flight, beastmode-A/P3b3); the additive part `(r, s, t)` is a coboundary by
  `exists_sub_smul_eq_of_isCocycle` (additive Hilbert 90, PROVEN) and the multiplicative part
  `u ∈ Z¹(G, Aˣ)` is *locally* a coboundary by `exists_unit_smul_eq_of_isLocalRing`
  ([A711-DESC], PROVEN) — so after a variable change over a Zariski neighbourhood of each
  prime of `Aᴳ`, `W` is `G`-invariant and descends. -/
theorem exists_ellipticCurveGeom_quotient [Finite G] [IsAffine X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T)
    (horbit : ∀ e : C.E, ∃ U : (C.E).Opens, IsAffineOpen U ∧
      ∀ γ : G, (σE.hom γ).base e ∈ U) :
    ∃ (C' : EllipticCurveGeom (σ.quotient V hVs hVa)) (q : C.E ⟶ C'.E),
      IsPullback q C.π C'.π (σ.quotientπ V hVs hVa hVmem) ∧
        C.zero ≫ q = σ.quotientπ V hVs hVa hVmem ≫ C'.zero := by
  sorry

end RouteA

end ModularCurves
