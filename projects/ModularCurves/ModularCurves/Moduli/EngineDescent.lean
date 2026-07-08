/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem

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

/-! ### The two charts (leaves `[a2-α]`, `[a2-β]`) -/

/-- **([a2-α], the zero-section complement is an affine chart)** For a geometric elliptic
curve over an **affine** base, the complement of (the image of) the zero section is an affine
open of `E`.

Plan (terminating in a proof): the zero section of a proper morphism is a closed immersion,
so the complement `U₁` is open. Affineness is Zariski-local on the base: `LocallyWeierstrass`
covers `X` by affine opens `Uᵢ` over which `E|Uᵢ ≅ projModel Wᵢ` carrying `zero` to
`projModelZero Wᵢ`, and `projModel W ∖ [0:1:0]` is the **affine Weierstrass curve**
`Spec Γ(Uᵢ)[x,y]/(W)` (the `Z ≠ 0` chart of `Proj`). Hence `π|U₁ : U₁ ⟶ X` is an affine
morphism (`IsAffineHom` is local at the target), and `X` is affine, so `U₁` is affine
(`isAffine_of_isAffineHom`).

Note this chart is *canonical*, hence automatically `G`-stable — the reason the dichotomy in
`orbit_mem_isAffineOpen_of_charts` works. -/
theorem isAffineOpen_zeroComplement [IsAffine X] (C : EllipticCurveGeom X)
    (U₁ : (C.E).Opens) (hU₁ : (U₁ : Set C.E) = (Set.range C.zero.base)ᶜ) :
    IsAffineOpen U₁ := by
  sorry

/-- **([a2-β], an affine chart around the zero section)** For a geometric elliptic curve over
an **affine** base admitting a section `s` disjoint from the zero section, there is an affine
open of `E` containing the whole image of the zero section.

Plan (terminating in a proof): translation by `s` is an automorphism `τ_s` of `E` over `X`
(the group law, `EllipticCurveGeom.toEllipticCurve`, T-W7); `τ_s` carries the zero section to
`s`, hence carries the affine open `E ∖ s(X)` (affine by `isAffineOpen_zeroComplement`
transported along `τ_{-s}`) onto an affine open containing the zero section. Equivalently and
without the group law: over each Weierstrass chart the `Y ≠ 0` chart of `projModel W` is an
affine open containing `[0:1:0]`, and these glue over an affine base because `π` restricted to
them is an affine morphism.

In the KM bootstrap the section `s` is free: `δ` = naive level `N` supplies a universal point
of exact order `N`, disjoint from the zero section by definition of a level structure. -/
theorem exists_isAffineOpen_zeroSection [IsAffine X] (C : EllipticCurveGeom X)
    (s : X ⟶ C.E) (hs : s ≫ C.π = 𝟙 X)
    (hsz : ∀ x : X, s.base x ≠ C.zero.base x) :
    ∃ U₀ : (C.E).Opens, IsAffineOpen U₀ ∧ ∀ x : X, C.zero.base x ∈ U₀ := by
  sorry

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
