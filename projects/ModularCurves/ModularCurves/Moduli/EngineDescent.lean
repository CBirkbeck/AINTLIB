/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.ForMathlib.PullbackLocalAtTarget

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
    (hVmem : ∀ x, x ∈ V x)
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
  sorry

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
    (hVmem : ∀ x, x ∈ V x)
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
  refine (isPullback_chart hact V hVs hVa hVmem VE hVEs hVEa hVEmem hfree π' hπ' i).of_iso
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

/-- **([a4], properness and smoothness descend)** `π' : E/G ⟶ X/G` is proper and smooth of
relative dimension `1`.

Plan (terminating in a proof): `q : X ⟶ X/G` is a **finite étale surjection** — finite by
`Module.Finite.of_isFreeAlgebraAction`, étale by
`Algebra.Etale.of_isFreeAlgebraAction_of_isNoetherianRing` (general base = the tracked gap
[A711-FP]), surjective because it is a torsor — hence an fppf cover. `IsProper` and
`SmoothOfRelativeDimension 1` are fppf-local at the target, and `π' ×_{X/G} X ≅ π` by
`[a3-ii]`, which is proper and smooth by hypothesis. -/
theorem isProper_smooth_quotient [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from C.E))]
    (hact : IsCurveAction σ C σE)
    (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
    (hVmem : ∀ x, x ∈ V x)
    (VE : C.E → (C.E).Opens) (hVEs : ∀ e, σE.IsStableOpen (VE e))
    (hVEa : ∀ e, IsAffineOpen (VE e)) (hVEmem : ∀ e, e ∈ VE e)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (π' : σE.quotient VE hVEs hVEa ⟶ σ.quotient V hVs hVa)
    (hπ' : σE.quotientπ VE hVEs hVEa hVEmem ≫ π' = C.π ≫ σ.quotientπ V hVs hVa hVmem) :
    IsProper π' ∧ SmoothOfRelativeDimension 1 π' := by
  sorry

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
