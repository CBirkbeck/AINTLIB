import ModularCurves.EllipticCurve.Basic

/-!
# The pole-order filtration and global sections of the projective Weierstrass model

**(T-W7 skeleton, lane P3 — `/develop --decompose` 2026-07-07.)** Uniform-in-`R` chart
computations on `projModel W`: the pole-order filtration `F_n` along the zero section on the
affine coordinate ring, its low-degree freeness (`F₁ = R`, `F₂ = R ⊕ Rx`, `F₃ = R ⊕ Rx ⊕ Ry`),
the global-sections theorem `Γ(projModel W, ⊤) ≅ R` for **every** ring (no cohomology, no base
change: universality is by instantiation), scheme-density of the affine part, and the
pushforward identity `π_*O_E = O_S` for locally-Weierstrass families.

Sources: reviewer round 1 §Q2 (uniform chart computation; `.mathlib-quality/expert-review/
2026-07-07-tw7/reply.md`); audit A3 (`integration.md`); Bosma–Lenstra-independent. None of the
statements require `W.IsElliptic` — the chart rings are free `R`-modules with universal bases
for arbitrary Weierstrass data.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- The affine coordinate `x` in the coordinate ring `R[x,y]/(W)` of the affine part.
Source: audit A3 normal form; mathlib `WeierstrassCurve.Affine.CoordinateRing`. -/
noncomputable def coordX (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X)

/-- The affine coordinate `y` in the coordinate ring `R[x,y]/(W)` of the affine part. -/
noncomputable def coordY (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial Polynomial.X

/-- **(T-W7.0i·i1)** The pole-order filtration along the zero section: `F n` is the
`R`-submodule of functions on the affine part extending to sections of `O(n·O)` — pole order
`≤ n` along the section at infinity, measured in the infinity chart via the section's ideal
`(s)` on the open where `t = s³·(unit)`. Source: KM §2.2-style "Weierstrass sections",
re-derived uniformly (audit A1/A3); GIT-independent. -/
noncomputable def poleOrderFiltration (W : WeierstrassCurve R) (n : ℕ) :
    Submodule R W.toAffine.CoordinateRing :=
  sorry

/-- **(T-W7.0i·i2a)** No nonconstant functions of pole order `≤ 1`: `F 1 = R·1`. This is the
elementary genus-1 input (the missing pole order 1 = the rank-1 `H¹` witness `x²y⁻¹` lies in
neither chart image). Source: audit A3 normal-form basis, one element per pole order. -/
theorem poleOrderFiltration_one (W : WeierstrassCurve R) :
    poleOrderFiltration W 1 = Submodule.span R {1} := by
  sorry

/-- **(T-W7.0i·i2b)** `F 2 = R·1 ⊕ R·x` (as a span; freeness is `poleOrderFiltration_free`).
Source: audit A3; classical `L(2O) = ⟨1, x⟩`. -/
theorem poleOrderFiltration_two (W : WeierstrassCurve R) :
    poleOrderFiltration W 2 = Submodule.span R {1, coordX W} := by
  sorry

/-- **(T-W7.0i·i2c)** `F 3 = R·1 ⊕ R·x ⊕ R·y`. Source: audit A3; classical
`L(3O) = ⟨1, x, y⟩`. -/
theorem poleOrderFiltration_three (W : WeierstrassCurve R) :
    poleOrderFiltration W 3 = Submodule.span R {1, coordX W, coordY W} := by
  sorry

/-- **(T-W7.0i·i2d)** The filtration is multiplicative: `F m · F n ⊆ F (m + n)`. Needed for
the coefficient extraction in the comparison theorem (matching the two cubic relations).
Source: pole orders add; audit A1 (b3). -/
theorem poleOrderFiltration_mul_le (W : WeierstrassCurve R) (m n : ℕ) :
    poleOrderFiltration W m * poleOrderFiltration W n ≤ poleOrderFiltration W (m + n) := by
  sorry

/-- **(T-W7.0i·i2e)** `1, x, y` are `R`-linearly independent in the coordinate ring (the
`F₃`-span is free of rank 3): the coefficient extraction `Φ(x') = αx + β`,
`Φ(y') = γy + δx + ε` in the comparison theorem reads coefficients off this basis. Source:
mathlib `CoordinateRing` freeness (`{1, y}` over `R[x]`); audit A3. -/
theorem linearIndependent_one_coordX_coordY (W : WeierstrassCurve R) :
    LinearIndependent R ![1, coordX W, coordY W] := by
  sorry

/-- **(T-W7.0i·i3, decl `projModel_globalSections_eq_baseRing`)** The global sections of the
projective Weierstrass model are exactly the base ring, for **every** commutative ring `R`:
the canonical map `R = Γ(Spec R, ⊤) ⟶ Γ(projModel W, ⊤)` is an isomorphism. Universality for
rigidity is **by instantiation** at `W.map φ` — never by a cohomology-and-base-change
argument (equalizers do not commute with base change). Source: reviewer round 1 §Q2; audit A3
(2-chart equalizer; `x²y⁻¹` excluded). -/
theorem projModel_globalSections_eq_baseRing (W : WeierstrassCurve R) :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (projModelπ W).appTop) := by
  sorry

/-- **(T-W7.0i·i4-core)** In the infinity-chart ring (chart `i = 1`, coordinates
`s = X/Y, t = Z/Y`), the coordinate `s` is a nonzerodivisor. This is the McCoy computation
(the monic-in-`s` chart relation has constant-coefficient-1 `t`-content) powering
scheme-density of the affine part. Source: audit A1 (b4 derivation). -/
theorem infChart_s_nonZeroDivisor (W : WeierstrassCurve R) :
    (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 1
        W.toProjective.polynomial}) (MvPolynomial.X ⟨0, by decide⟩)) ∈
      nonZeroDivisors (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) := by
  sorry

/-- **(T-W7.0i·i4)** Morphisms out of the projective model into a separated scheme are
determined by their restriction to the affine part (the `Z`-chart, whose complement is the
zero section): the affine part is *scheme-theoretically dense*, valid over arbitrary — in
particular non-reduced — `R` via `infChart_s_nonZeroDivisor` (NOT via topological density +
reducedness). Consumed by the comparison theorem (b4). Source: audit A1 (b4). -/
theorem projModel_hom_ext_of_affine (W : WeierstrassCurve R) {Z : Scheme.{u}}
    [Z.IsSeparated] {f g : projModel W ⟶ Z}
    (h : (modelChartCover W).openCover.f (2 : Fin 3) ≫ f =
      (modelChartCover W).openCover.f (2 : Fin 3) ≫ g) :
    f = g := by
  sorry

/-- **(T-W7.0i·i5, decl `locallyWeierstrass_pushforward_O_eq_O`)** For any locally-Weierstrass
family `π : E ⟶ S` the structure map on sections `Γ(S, U) ⟶ Γ(E, π⁻¹U)` is an isomorphism for
every open `U` — i.e. `O_S ≅ π_*O_E` as sheaves. Universally valid (base changes are again
locally Weierstrass, so this statement instantiates). Sheafification of
`projModel_globalSections_eq_baseRing` over chart opens. Source: reviewer round 1 §Q2. -/
theorem locallyWeierstrass_pushforward_O_eq_O {S : Scheme.{u}} (G : EllipticCurveGeom S)
    (U : S.Opens) : IsIso (G.π.app U) := by
  sorry

end ModularCurves
