import ModularCurves.EllipticCurve.Basic
import Mathlib.RingTheory.AdjoinRoot

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

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

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
  Submodule.span R
    ({g | ∃ i : ℕ, 2 * i ≤ n ∧ g = coordX W ^ i} ∪
      {g | ∃ i : ℕ, 2 * i + 3 ≤ n ∧ g = coordX W ^ i * coordY W})

/-- **(T-W7.0i·i2a)** No nonconstant functions of pole order `≤ 1`: `F 1 = R·1`. This is the
elementary genus-1 input (the missing pole order 1 = the rank-1 `H¹` witness `x²y⁻¹` lies in
neither chart image). Source: audit A3 normal-form basis, one element per pole order. -/
theorem poleOrderFiltration_one (W : WeierstrassCurve R) :
    poleOrderFiltration W 1 = Submodule.span R {1} := by
  unfold poleOrderFiltration
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain rfl : i = 0 := by omega
      exact pow_zero _
    · omega
  · rintro rfl
    exact Or.inl ⟨0, by omega, (pow_zero _).symm⟩

/-- **(T-W7.0i·i2b)** `F 2 = R·1 ⊕ R·x` (as a span; freeness is `poleOrderFiltration_free`).
Source: audit A3; classical `L(2O) = ⟨1, x⟩`. -/
theorem poleOrderFiltration_two (W : WeierstrassCurve R) :
    poleOrderFiltration W 2 = Submodule.span R {1, coordX W} := by
  unfold poleOrderFiltration
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · exact Or.inl (pow_zero _)
      · exact Or.inr (pow_one _)
    · omega
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0, by omega, (pow_zero _).symm⟩
    · exact Or.inl ⟨1, by omega, (pow_one _).symm⟩

/-- **(T-W7.0i·i2c)** `F 3 = R·1 ⊕ R·x ⊕ R·y`. Source: audit A3; classical
`L(3O) = ⟨1, x, y⟩`. -/
theorem poleOrderFiltration_three (W : WeierstrassCurve R) :
    poleOrderFiltration W 3 = Submodule.span R {1, coordX W, coordY W} := by
  unfold poleOrderFiltration
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · exact Or.inl (pow_zero _)
      · exact Or.inr (Or.inl (pow_one _))
    · obtain rfl : i = 0 := by omega
      exact Or.inr (Or.inr (by rw [pow_zero, one_mul]))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨0, by omega, (pow_zero _).symm⟩
    · exact Or.inl ⟨1, by omega, (pow_one _).symm⟩
    · exact Or.inr ⟨0, by omega, by rw [pow_zero, one_mul]⟩

/-- The Weierstrass relation in the coordinate ring, solved for `y²` (ring form, with
`algebraMap` multiplications): `y² = x³ + a₂x² + a₄x + a₆ − a₁xy − a₃y`. -/
lemma coordY_mul_coordY (W : WeierstrassCurve R) :
    coordY W * coordY W =
      coordX W ^ 3 + algebraMap R _ W.toAffine.a₂ * coordX W ^ 2 +
        algebraMap R _ W.toAffine.a₄ * coordX W + algebraMap R _ W.toAffine.a₆ -
          algebraMap R _ W.toAffine.a₁ * (coordX W * coordY W) -
            algebraMap R _ W.toAffine.a₃ * coordY W := by
  have halg : ∀ r : R, algebraMap R W.toAffine.CoordinateRing r =
      AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (Polynomial.C r)) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (Polynomial R) W.toAffine.CoordinateRing,
      AdjoinRoot.algebraMap_eq, Polynomial.algebraMap_eq]
    rfl
  have h2 : AdjoinRoot.mk W.toAffine.polynomial
      (Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C W.toAffine.a₁ * Polynomial.X +
          Polynomial.C W.toAffine.a₃) * Polynomial.X -
        Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C W.toAffine.a₄ * Polynomial.X + Polynomial.C W.toAffine.a₆)) = 0 := by
    rw [show (Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C W.toAffine.a₁ * Polynomial.X +
          Polynomial.C W.toAffine.a₃) * Polynomial.X -
        Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C W.toAffine.a₄ * Polynomial.X + Polynomial.C W.toAffine.a₆)) =
      W.toAffine.polynomial from rfl]
    exact AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow] at h2
  simp only [coordX, coordY, halg]
  linear_combination h2

/-- **(T-W7.0i·i2d)** The filtration is multiplicative: `F m · F n ⊆ F (m + n)`. Needed for
the coefficient extraction in the comparison theorem (matching the two cubic relations).
Source: pole orders add; audit A1 (b3). -/
theorem poleOrderFiltration_mul_le (W : WeierstrassCurve R) (m n : ℕ) :
    poleOrderFiltration W m * poleOrderFiltration W n ≤ poleOrderFiltration W (m + n) := by
  unfold poleOrderFiltration
  rw [Submodule.span_mul_span]
  refine Submodule.span_le.mpr ?_
  have hxmem : ∀ j : ℕ, 2 * j ≤ m + n →
      coordX W ^ j ∈ poleOrderFiltration W (m + n) := fun j hj =>
    Submodule.subset_span (Or.inl ⟨j, hj, rfl⟩)
  have hymem : ∀ j : ℕ, 2 * j + 3 ≤ m + n →
      coordX W ^ j * coordY W ∈ poleOrderFiltration W (m + n) := fun j hj =>
    Submodule.subset_span (Or.inr ⟨j, hj, rfl⟩)
  rintro g ⟨a, ha, b, hb, rfl⟩
  show a * b ∈ poleOrderFiltration W (m + n)
  obtain ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ := ha <;> obtain ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ := hb
  · -- x^i · x^k
    rw [show coordX W ^ i * coordX W ^ k = coordX W ^ (i + k) by ring]
    exact hxmem _ (by omega)
  · -- x^i · (x^k y)
    rw [show coordX W ^ i * (coordX W ^ k * coordY W) =
      coordX W ^ (i + k) * coordY W by ring]
    exact hymem _ (by omega)
  · -- (x^i y) · x^k
    rw [show coordX W ^ i * coordY W * coordX W ^ k =
      coordX W ^ (i + k) * coordY W by ring]
    exact hymem _ (by omega)
  · -- (x^i y) · (x^k y): reduce y² by the Weierstrass relation
    rw [show coordX W ^ i * coordY W * (coordX W ^ k * coordY W) =
      coordX W ^ (i + k) * (coordY W * coordY W) by ring, coordY_mul_coordY,
      show coordX W ^ (i + k) *
          (coordX W ^ 3 + algebraMap R _ W.toAffine.a₂ * coordX W ^ 2 +
            algebraMap R _ W.toAffine.a₄ * coordX W + algebraMap R _ W.toAffine.a₆ -
              algebraMap R _ W.toAffine.a₁ * (coordX W * coordY W) -
                algebraMap R _ W.toAffine.a₃ * coordY W) =
        coordX W ^ (i + k + 3) + algebraMap R _ W.toAffine.a₂ * coordX W ^ (i + k + 2) +
          algebraMap R _ W.toAffine.a₄ * coordX W ^ (i + k + 1) +
            algebraMap R _ W.toAffine.a₆ * coordX W ^ (i + k) -
              algebraMap R _ W.toAffine.a₁ * (coordX W ^ (i + k + 1) * coordY W) -
                algebraMap R _ W.toAffine.a₃ * (coordX W ^ (i + k) * coordY W) by ring]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
      · exact hxmem _ (by omega)
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (hxmem _ (by omega))
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (hxmem _ (by omega))
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (hxmem _ (by omega))
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hymem _ (by omega))
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hymem _ (by omega))

/-- **(T-W7.0i·i2e)** `1, x, y` are `R`-linearly independent in the coordinate ring (the
`F₃`-span is free of rank 3): the coefficient extraction `Φ(x') = αx + β`,
`Φ(y') = γy + δx + ε` in the comparison theorem reads coefficients off this basis. Source:
mathlib `CoordinateRing` freeness (`{1, y}` over `R[x]`); audit A3. -/
theorem linearIndependent_one_coordX_coordY (W : WeierstrassCurve R) :
    LinearIndependent R ![1, coordX W, coordY W] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hg
  have hx : coordX W = (Polynomial.X : Polynomial R) • (1 : W.toAffine.CoordinateRing) := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    rfl
  have hcast : ∀ (r : R) (z : W.toAffine.CoordinateRing),
      r • z = (Polynomial.C r : Polynomial R) • z := fun r z => by
    rw [← algebraMap_smul (Polynomial R) r z, Polynomial.algebraMap_eq]
  rw [hcast (g 0), hx, hcast (g 1), smul_smul, hcast (g 2), ← add_smul] at hg
  unfold coordY at hg
  obtain ⟨hpq, hq⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero hg
  have hg0 : g 0 = 0 := by
    have := congrArg (Polynomial.coeff · 0) hpq
    simpa using this
  have hg1 : g 1 = 0 := by
    have := congrArg (Polynomial.coeff · 1) hpq
    simpa using this
  have hg2 : g 2 = 0 := by
    simpa using congrArg (Polynomial.coeff · 0) hq
  intro i
  fin_cases i <;> assumption

/-- The `s = X/Y` coordinate index of the infinity chart. -/
abbrev infChartS : {j : Fin 3 // j ≠ 1} := ⟨0, by decide⟩

/-- The `t = Z/Y` coordinate index of the infinity chart. -/
abbrev infChartT : {j : Fin 3 // j ≠ 1} := ⟨2, by decide⟩

/-- **(T-W7.0i-b1)** The dehomogenised infinity-chart cubic, explicitly:
`t + a₁st + a₃t² − s³ − a₂s²t − a₄st² − a₆t³`. Source: audit A3 (`t = s³·u` normal form). -/
lemma dehomogenizeAux_projective_polynomial (W : WeierstrassCurve R) :
    MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial =
      MvPolynomial.X infChartT +
        MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X infChartS * MvPolynomial.X infChartT +
        MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X infChartT ^ 2 -
        (MvPolynomial.X infChartS ^ 3 +
          MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X infChartS ^ 2 *
            MvPolynomial.X infChartT +
          MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X infChartS *
            MvPolynomial.X infChartT ^ 2 +
          MvPolynomial.C W.toProjective.a₆ * MvPolynomial.X infChartT ^ 3) := by
  rw [show W.toProjective.polynomial =
    MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 *
        MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 -
      (MvPolynomial.X 0 ^ 3 +
        MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 +
        MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 +
        MvPolynomial.C W.toProjective.a₆ * MvPolynomial.X 2 ^ 3) from rfl]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.dehomogenizeAux_C,
    MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne R 1 (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne R 1 (show (2 : Fin 3) ≠ 1 by decide)]
  ring

/-- **(T-W7.0i-b1)** The infinity-chart cubic as a *monic* polynomial in `s` over `R[t]`
(the negation of the dehomogenised cubic, collected in the outer variable `s`):
`s³ + (a₂t)s² + (a₄t² − a₁t)s + (a₆t³ − a₃t² − t)`. -/
noncomputable def infChartCubic (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  Polynomial.X ^ 3 + Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
    Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 -
      Polynomial.C W.a₁ * Polynomial.X) * Polynomial.X +
    Polynomial.C (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
      Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X)

/-- **(T-W7.0i-b1)** The chart cubic is monic (in the outer variable `s`). -/
lemma infChartCubic_monic (W : WeierstrassCurve R) : (infChartCubic W).Monic := by
  unfold infChartCubic
  monicity!

/-- **(T-W7.0i-b1)** The chart cubic has degree 3 in the outer variable `s` (nontriviality is
genuinely needed: over the zero ring every polynomial has `natDegree 0`). -/
lemma infChartCubic_natDegree (W : WeierstrassCurve R) [Nontrivial R] :
    (infChartCubic W).natDegree = 3 := by
  unfold infChartCubic
  compute_degree!

/-- The index bijection of the infinity chart: `s ↦ 0`, `t ↦ 1`. -/
def infChartIndexEquiv : {j : Fin 3 // j ≠ 1} ≃ Fin 2 where
  toFun j := if j.1 = 0 then 0 else 1
  invFun i := if i = 0 then infChartS else infChartT
  left_inv := by decide
  right_inv := by decide

/-- **(T-W7.0i-b1)** The infinity-chart polynomial ring as an iterated polynomial ring:
`s` becomes the outer variable, `t` the inner. -/
noncomputable def infChartPolyEquiv :
    MvPolynomial {j : Fin 3 // j ≠ 1} R ≃ₐ[R] Polynomial (Polynomial R) :=
  (MvPolynomial.renameEquiv R infChartIndexEquiv).trans <|
    (MvPolynomial.finSuccEquiv R 1).trans <|
      Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))

@[simp]
lemma infChartPolyEquiv_X_s :
    infChartPolyEquiv (R := R) (MvPolynomial.X infChartS) = Polynomial.X := by
  simp [infChartPolyEquiv, infChartIndexEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp]
lemma infChartPolyEquiv_X_t :
    infChartPolyEquiv (R := R) (MvPolynomial.X infChartT) = Polynomial.C Polynomial.X := by
  simp [infChartPolyEquiv, infChartIndexEquiv]
  rw [show ((1 : Fin 2) : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- **(T-W7.0i-b1)** The equiv carries the dehomogenised chart cubic to (minus) the monic
chart cubic. -/
lemma infChartPolyEquiv_dehomogenize (W : WeierstrassCurve R) :
    infChartPolyEquiv (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) =
      -infChartCubic W := by
  rw [dehomogenizeAux_projective_polynomial]
  have hC : ∀ r : R, infChartPolyEquiv (MvPolynomial.C r) =
      Polynomial.C (Polynomial.C r) := fun r => by
    have := (infChartPolyEquiv (R := R)).commutes r
    simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] using this
  unfold infChartCubic
  simp only [map_add, map_sub, map_mul, map_pow, infChartPolyEquiv_X_s,
    infChartPolyEquiv_X_t, hC]
  ring

/-- **(T-W7.0i-b1, the bridge)** The infinity-chart quotient ring is `AdjoinRoot` of the
monic chart cubic over `R[t]`. -/
noncomputable def infChartQuotEquiv (W : WeierstrassCurve R) :
    (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) ≃ₐ[R]
        AdjoinRoot (infChartCubic W) :=
  Ideal.quotientEquivAlg _ _ (infChartPolyEquiv (R := R)) <| by
    rw [Ideal.map_span, Set.image_singleton,
      show ((infChartPolyEquiv (R := R)) :
          MvPolynomial {j : Fin 3 // j ≠ 1} R →+* Polynomial (Polynomial R))
          (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) =
        -infChartCubic W from infChartPolyEquiv_dehomogenize W,
      Ideal.span_singleton_neg]

/-- **(T-W7.0i-b2, general)** The root adjoined to a polynomial whose constant coefficient is
a nonzerodivisor is itself a nonzerodivisor: from `q·X = f·g`, the constant coefficient gives
`g(0) = 0`, so `X ∣ g`, and cancelling `X` exhibits `f ∣ q`. (The one-variable form of the
mod-variable two-step; audit A1/b4.) -/
lemma adjoinRoot_root_mem_nonZeroDivisors {R' : Type*} [CommRing R'] {f : Polynomial R'}
    (hf : f.coeff 0 ∈ nonZeroDivisors R') :
    AdjoinRoot.root f ∈ nonZeroDivisors (AdjoinRoot f) := by
  have key : ∀ m : AdjoinRoot f, m * AdjoinRoot.root f = 0 → m = 0 := by
    intro m hm
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective m
    rw [show AdjoinRoot.root f = AdjoinRoot.mk f Polynomial.X from rfl, ← map_mul,
      AdjoinRoot.mk_eq_zero] at hm
    obtain ⟨g, hg⟩ := hm
    have hg0 : g.coeff 0 = 0 := by
      have h0 := congrArg (Polynomial.coeff · 0) hg
      simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero] at h0
      exact (mem_nonZeroDivisors_iff.mp hf).1 _ (by linear_combination -h0)
    obtain ⟨g₁, rfl⟩ := Polynomial.X_dvd_iff.mpr hg0
    have hq : q = f * g₁ := by
      have hX := Polynomial.X_mem_nonzeroDivisors (R := R')
      rw [mem_nonZeroDivisors_iff] at hX
      have h1 : (q - f * g₁) * Polynomial.X = 0 := by linear_combination hg
      have h2 := hX.2 _ h1
      linear_combination h2
    rw [AdjoinRoot.mk_eq_zero, hq]
    exact Dvd.intro g₁ rfl
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

/-- **(T-W7.0i-b2)** The power basis `{1, s, s²}` of the infinity chart over `R[t]`
(the chart cubic is monic of degree 3). Pattern: mathlib `Affine.CoordinateRing.basis`. -/
noncomputable def infChartBasis (W : WeierstrassCurve R) [Nontrivial R] :
    Module.Basis (Fin 3) (Polynomial R) (AdjoinRoot (infChartCubic W)) :=
  (AdjoinRoot.powerBasis' (infChartCubic_monic W)).basis.reindex
    (finCongr (infChartCubic_natDegree W))

/-- **(T-W7.0i-b2)** A scalar that is a nonzerodivisor acts injectively on the (free)
infinity chart: the `t`-side nonzerodivisor supply. -/
lemma infChart_algebraMap_mem_nonZeroDivisors (W : WeierstrassCurve R) [Nontrivial R]
    {p : Polynomial R} (hp : p ∈ nonZeroDivisors (Polynomial R)) :
    algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) p ∈
      nonZeroDivisors (AdjoinRoot (infChartCubic W)) := by
  have key : ∀ m : AdjoinRoot (infChartCubic W),
      m * algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) p = 0 → m = 0 := by
    intro m hm
    have hsmul : p • m = 0 := by
      rw [Algebra.smul_def, mul_comm]
      exact hm
    have hrepr := congrArg (infChartBasis W).repr hsmul
    rw [map_smul, map_zero] at hrepr
    have hzero : ∀ i, (infChartBasis W).repr m i = 0 := fun i => by
      have h1 := congrArg (fun l => l i) hrepr
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h1
      exact (mem_nonZeroDivisors_iff.mp hp).2 _ (by linear_combination h1)
    have hm0 : (infChartBasis W).repr m = 0 := Finsupp.ext hzero
    simpa using congrArg (infChartBasis W).repr.symm hm0
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

/-- **(T-W7.0i-b2, the `t`-nonzerodivisor)** The overlap coordinate `t = Z/Y` is a
nonzerodivisor in the infinity chart — the input for scheme-density of the `Z`-chart
(`projModel_hom_ext_of_affine`). -/
lemma infChart_t_mem_nonZeroDivisors (W : WeierstrassCurve R) [Nontrivial R] :
    algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) Polynomial.X ∈
      nonZeroDivisors (AdjoinRoot (infChartCubic W)) :=
  infChart_algebraMap_mem_nonZeroDivisors W Polynomial.X_mem_nonzeroDivisors

/-- **(T-W7.0i-b2, the `s`-nonzerodivisor)** The uniformizer `s = X/Y` at the section is a
nonzerodivisor in the infinity chart: the chart cubic's constant coefficient
`a₆t³ − a₃t² − t` has `t`-coefficient `−1`, a nonzerodivisor. -/
lemma infChart_root_mem_nonZeroDivisors (W : WeierstrassCurve R) :
    AdjoinRoot.root (infChartCubic W) ∈ nonZeroDivisors (AdjoinRoot (infChartCubic W)) := by
  refine adjoinRoot_root_mem_nonZeroDivisors ?_
  refine Polynomial.mem_nonzeroDivisors_of_coeff_mem 1 ?_
  have hc : (infChartCubic W).coeff 0 = Polynomial.C W.a₆ * Polynomial.X ^ 3 -
      Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X := by
    unfold infChartCubic
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    norm_num
  have h1 : ((infChartCubic W).coeff 0).coeff 1 = -1 := by
    rw [hc]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X_one]
    norm_num
  rw [h1]
  rw [mem_nonZeroDivisors_iff]
  constructor <;> intro x hx <;>
    simpa [neg_eq_zero] using hx

/-- Nonzerodivisors transport backwards along ring equivalences. -/
lemma mem_nonZeroDivisors_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) {x : A} (h : e x ∈ nonZeroDivisors B) : x ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff] at h ⊢
  constructor <;> intro z hz
  · exact e.injective (by
      simpa using h.1 (e z) (by rw [← map_mul, hz, map_zero]))
  · exact e.injective (by
      simpa using h.2 (e z) (by rw [← map_mul, hz, map_zero]))

/-- The chart-0 index bijection: `z ↦ 0` (outer), `y ↦ 1` (inner). -/
def zChartIndexEquiv : {k : Fin 3 // k ≠ 0} ≃ Fin 2 where
  toFun k := if k.1 = 2 then 0 else 1
  invFun i := if i = 0 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- The chart-0 polynomial ring as an iterated polynomial ring, `z` outer. -/
noncomputable def zChartPolyEquiv :
    MvPolynomial {k : Fin 3 // k ≠ 0} R ≃ₐ[R] Polynomial (Polynomial R) :=
  (MvPolynomial.renameEquiv R zChartIndexEquiv).trans <|
    (MvPolynomial.finSuccEquiv R 1).trans <|
      Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))

@[simp]
lemma zChartPolyEquiv_X_z :
    zChartPolyEquiv (R := R) (MvPolynomial.X ⟨2, by decide⟩) = Polynomial.X := by
  simp [zChartPolyEquiv, zChartIndexEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp]
lemma zChartPolyEquiv_X_y :
    zChartPolyEquiv (R := R) (MvPolynomial.X ⟨1, by decide⟩) =
      Polynomial.C Polynomial.X := by
  simp [zChartPolyEquiv, zChartIndexEquiv]
  rw [show ((1 : Fin 2) : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- The chart-0 dehomogenised cubic, explicitly:
`y²z + a₁yz + a₃yz² − (1 + a₂z + a₄z² + a₆z³)`. -/
lemma dehomogenizeAux_zero_projective_polynomial (W : WeierstrassCurve R) :
    MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial =
      MvPolynomial.X ⟨1, by decide⟩ ^ 2 * MvPolynomial.X ⟨2, by decide⟩ +
        MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X ⟨1, by decide⟩ *
          MvPolynomial.X ⟨2, by decide⟩ +
        MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X ⟨1, by decide⟩ *
          MvPolynomial.X ⟨2, by decide⟩ ^ 2 -
        (1 + MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X ⟨2, by decide⟩ +
          MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X ⟨2, by decide⟩ ^ 2 +
          MvPolynomial.C W.toProjective.a₆ * MvPolynomial.X ⟨2, by decide⟩ ^ 3) := by
  rw [show W.toProjective.polynomial =
    MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 *
        MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 -
      (MvPolynomial.X 0 ^ 3 +
        MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 +
        MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 +
        MvPolynomial.C W.toProjective.a₆ * MvPolynomial.X 2 ^ 3) from rfl]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.dehomogenizeAux_C,
    MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne R 0 (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne R 0 (show (2 : Fin 3) ≠ 0 by decide)]
  ring

/-- The chart-0 cubic in the `z`-outer presentation (NOT monic in `z`; only its constant
coefficient `−1` matters). -/
noncomputable def zChartCubic (W : WeierstrassCurve R) : Polynomial (Polynomial R) :=
  Polynomial.C (Polynomial.X ^ 2 + Polynomial.C W.a₁ * Polynomial.X -
      Polynomial.C W.a₂) * Polynomial.X +
    Polynomial.C (Polynomial.C W.a₃ * Polynomial.X - Polynomial.C W.a₄) * Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.C W.a₆) * Polynomial.X ^ 3 - 1

lemma zChartPolyEquiv_dehomogenize (W : WeierstrassCurve R) :
    zChartPolyEquiv (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial) =
      zChartCubic W := by
  rw [dehomogenizeAux_zero_projective_polynomial]
  have hC : ∀ r : R, zChartPolyEquiv (MvPolynomial.C r) =
      Polynomial.C (Polynomial.C r) := fun r => by
    have := (zChartPolyEquiv (R := R)).commutes r
    simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] using this
  unfold zChartCubic
  simp only [map_add, map_sub, map_mul, map_pow, map_one, zChartPolyEquiv_X_z,
    zChartPolyEquiv_X_y, hC]
  ring

lemma zChartCubic_coeff_zero (W : WeierstrassCurve R) :
    (zChartCubic W).coeff 0 = -1 := by
  unfold zChartCubic
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero]
  norm_num

/-- The chart-0 quotient as `AdjoinRoot` of the `z`-outer cubic. -/
noncomputable def zChartQuotEquiv (W : WeierstrassCurve R) :
    (MvPolynomial {k : Fin 3 // k ≠ 0} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial}) ≃ₐ[R]
        AdjoinRoot (zChartCubic W) :=
  Ideal.quotientEquivAlg _ _ (zChartPolyEquiv (R := R)) <| by
    rw [Ideal.map_span, Set.image_singleton,
      show ((zChartPolyEquiv (R := R)) :
          MvPolynomial {k : Fin 3 // k ≠ 0} R →+* Polynomial (Polynomial R))
          (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial) =
        zChartCubic W from zChartPolyEquiv_dehomogenize W]

/-- **(chart-0 `z`-nonzerodivisor)** The class of the `Z/X`-coordinate in the chart-0 ring
is a nonzerodivisor: the chart cubic has constant coefficient `−1` in the `z`-outer
presentation. -/
lemma zChart_z_nonZeroDivisor (W : WeierstrassCurve R) :
    (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 0
        W.toProjective.polynomial}) (MvPolynomial.X ⟨2, by decide⟩)) ∈
      nonZeroDivisors (MvPolynomial {k : Fin 3 // k ≠ 0} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial}) := by
  refine mem_nonZeroDivisors_of_ringEquiv (zChartQuotEquiv W).toRingEquiv ?_
  show (zChartQuotEquiv W) (Ideal.Quotient.mk _ (MvPolynomial.X ⟨2, by decide⟩)) ∈
    nonZeroDivisors (AdjoinRoot (zChartCubic W))
  have hz : zChartQuotEquiv W (Ideal.Quotient.mk _
      (MvPolynomial.X ⟨2, by decide⟩)) = AdjoinRoot.root (zChartCubic W) := by
    show Ideal.quotientEquivAlg _ _ (zChartPolyEquiv (R := R)) _
      (Ideal.Quotient.mk _ (MvPolynomial.X ⟨2, by decide⟩)) = _
    rw [Ideal.quotientEquivAlg_mk, zChartPolyEquiv_X_z]
    rfl
  rw [hz]
  refine adjoinRoot_root_mem_nonZeroDivisors ?_
  rw [zChartCubic_coeff_zero]
  rw [mem_nonZeroDivisors_iff]
  constructor <;> intro x hx <;> simpa [neg_eq_zero] using hx

/-- **(chart-1 `t`-nonzerodivisor, quotient spelling)** The class of the `Z/Y`-coordinate
in the infinity-chart ring is a nonzerodivisor. -/
lemma infChart_t_nonZeroDivisor (W : WeierstrassCurve R) :
    (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 1
        W.toProjective.polynomial}) (MvPolynomial.X infChartT)) ∈
      nonZeroDivisors (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) :=
      Module.subsingleton R _
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z _ => Subsingleton.elim _ _, fun z _ => Subsingleton.elim _ _⟩
  · refine mem_nonZeroDivisors_of_ringEquiv (infChartQuotEquiv W).toRingEquiv ?_
    show (infChartQuotEquiv W) (Ideal.Quotient.mk _ (MvPolynomial.X infChartT)) ∈
      nonZeroDivisors (AdjoinRoot (infChartCubic W))
    have ht : infChartQuotEquiv W (Ideal.Quotient.mk _
        (MvPolynomial.X infChartT)) =
        algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) Polynomial.X := by
      show Ideal.quotientEquivAlg _ _ (infChartPolyEquiv (R := R)) _
        (Ideal.Quotient.mk _ (MvPolynomial.X infChartT)) = _
      rw [Ideal.quotientEquivAlg_mk, infChartPolyEquiv_X_t]
      rfl
    rw [ht]
    exact infChart_t_mem_nonZeroDivisors W

/-- **(T-W7.0i-b3-1)** The `Y`-chart and `Z`-chart opens cover the model: the complement of
the `Z`-chart is the zero section, which lies in the `Y`-chart. (Two charts suffice for the
global-sections equalizer — single overlap.) Source: audit A3. -/
theorem chartY_sup_chartZ_eq_top (W : WeierstrassCurve R) :
    ((modelChartCover W).openCover.f (1 : Fin 3)).opensRange ⊔
      ((modelChartCover W).openCover.f (2 : Fin 3)).opensRange = ⊤ := by
  sorry

/-- **(T-W7.0i-b3-2)** Sections over the `Y`-chart open are the chart ring (open-immersion
`Γ`-comparison composed with the repo's `chartCoordEquiv`). -/
noncomputable def chartYSectionsEquiv (W : WeierstrassCurve R) :
    Γ(projModel W, ((modelChartCover W).openCover.f (1 : Fin 3)).opensRange) ≃+*
      (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) :=
  sorry

/-- **(T-W7.0i-b3-3)** Sections over the `Z`-chart open are the chart ring. -/
noncomputable def chartZSectionsEquiv (W : WeierstrassCurve R) :
    Γ(projModel W, ((modelChartCover W).openCover.f (2 : Fin 3)).opensRange) ≃+*
      (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial}) :=
  sorry

/-- The `x = X/Z` coordinate index of the affine chart. -/
abbrev affChartX : {j : Fin 3 // j ≠ 2} := ⟨0, by decide⟩

/-- The `y = Y/Z` coordinate index of the affine chart. -/
abbrev affChartY : {j : Fin 3 // j ≠ 2} := ⟨1, by decide⟩

/-- **(T-W7.0i-b4-0)** The dehomogenised affine-chart polynomial, explicitly:
`y² + a₁xy + a₃y − (x³ + a₂x² + a₄x + a₆)`. -/
lemma dehomogenizeAux_two_projective_polynomial (W : WeierstrassCurve R) :
    MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial =
      MvPolynomial.X affChartY ^ 2 +
        MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X affChartX * MvPolynomial.X affChartY +
        MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X affChartY -
        (MvPolynomial.X affChartX ^ 3 +
          MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X affChartX ^ 2 +
          MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X affChartX +
          MvPolynomial.C W.toProjective.a₆) := by
  rw [show W.toProjective.polynomial =
    MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 *
        MvPolynomial.X 2 +
      MvPolynomial.C W.toProjective.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 -
      (MvPolynomial.X 0 ^ 3 +
        MvPolynomial.C W.toProjective.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 +
        MvPolynomial.C W.toProjective.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 +
        MvPolynomial.C W.toProjective.a₆ * MvPolynomial.X 2 ^ 3) from rfl]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.dehomogenizeAux_C,
    MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne R 2 (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne R 2 (show (1 : Fin 3) ≠ 2 by decide)]
  ring

/-- The index bijection of the affine chart: `y ↦ 0` (outer), `x ↦ 1` (inner). -/
def affChartIndexEquiv : {j : Fin 3 // j ≠ 2} ≃ Fin 2 where
  toFun j := if j.1 = 1 then 0 else 1
  invFun i := if i = 0 then affChartY else affChartX
  left_inv := by decide
  right_inv := by decide

/-- **(T-W7.0i-b4-0)** The affine-chart polynomial ring as an iterated polynomial ring:
`y` becomes the outer variable, `x` the inner — matching mathlib's `R[X][Y]` convention
for `WeierstrassCurve.Affine.polynomial`. -/
noncomputable def affChartPolyEquiv :
    MvPolynomial {j : Fin 3 // j ≠ 2} R ≃ₐ[R] Polynomial (Polynomial R) :=
  (MvPolynomial.renameEquiv R affChartIndexEquiv).trans <|
    (MvPolynomial.finSuccEquiv R 1).trans <|
      Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1))

@[simp]
lemma affChartPolyEquiv_X_y :
    affChartPolyEquiv (R := R) (MvPolynomial.X affChartY) = Polynomial.X := by
  simp [affChartPolyEquiv, affChartIndexEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp]
lemma affChartPolyEquiv_X_x :
    affChartPolyEquiv (R := R) (MvPolynomial.X affChartX) = Polynomial.C Polynomial.X := by
  simp [affChartPolyEquiv, affChartIndexEquiv]
  rw [show ((1 : Fin 2) : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- **(T-W7.0i-b4-0)** The equiv carries the dehomogenised affine-chart polynomial to
mathlib's affine Weierstrass polynomial (sign match is exact — no negation). -/
lemma affChartPolyEquiv_dehomogenize (W : WeierstrassCurve R) :
    affChartPolyEquiv (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      W.toAffine.polynomial := by
  rw [dehomogenizeAux_two_projective_polynomial]
  have hC : ∀ r : R, affChartPolyEquiv (MvPolynomial.C r) =
      Polynomial.C (Polynomial.C r) := fun r => by
    have := (affChartPolyEquiv (R := R)).commutes r
    simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] using this
  rw [show W.toAffine.polynomial = Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C W.toAffine.a₁ * Polynomial.X +
        Polynomial.C W.toAffine.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.toAffine.a₂ * Polynomial.X ^ 2 +
        Polynomial.C W.toAffine.a₄ * Polynomial.X + Polynomial.C W.toAffine.a₆) from rfl]
  simp only [map_add, map_sub, map_mul, map_pow, affChartPolyEquiv_X_x,
    affChartPolyEquiv_X_y, hC]
  ring

/-- **(T-W7.0i-b4-0)** The `Z`-chart quotient ring is mathlib's affine coordinate ring
(`x = X⟨0⟩`, `y = X⟨1⟩`) — the ring-level sibling of the repo's points-level
`zSolutionsToAffine`. -/
noncomputable def chartZAffineEquiv (W : WeierstrassCurve R) :
    (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial}) ≃ₐ[R]
        W.toAffine.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ (affChartPolyEquiv (R := R)) <| by
    rw [Ideal.map_span, Set.image_singleton,
      show ((affChartPolyEquiv (R := R)) :
          MvPolynomial {j : Fin 3 // j ≠ 2} R →+* Polynomial (Polynomial R))
          (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
        W.toAffine.polynomial from affChartPolyEquiv_dehomogenize W]

/-- The `t`-element of the infinity chart (the element the overlap localization inverts). -/
noncomputable abbrev infChartTElem (W : WeierstrassCurve R) :
    AdjoinRoot (infChartCubic W) :=
  algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) Polynomial.X

/-- `1/t` in the localized infinity chart. -/
noncomputable def overlapInvT (W : WeierstrassCurve R) :
    Localization.Away (infChartTElem W) :=
  Localization.mk 1 ⟨infChartTElem W, ⟨1, pow_one _⟩⟩

/-- `s/t` in the localized infinity chart. -/
noncomputable def overlapXElem (W : WeierstrassCurve R) :
    Localization.Away (infChartTElem W) :=
  Localization.mk (AdjoinRoot.root (infChartCubic W)) ⟨infChartTElem W, ⟨1, pow_one _⟩⟩

/-- **(T-W7.0i-b4-1rel)** The affine Weierstrass relation holds at `(s/t, 1/t)` in the
localized infinity chart: the chart-cubic relation for `root`, divided by `t³`. -/
lemma overlap_eval₂_polynomial (W : WeierstrassCurve R) :
    Polynomial.eval₂
      (Polynomial.eval₂RingHom
        ((algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))).comp
          ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C))
        (overlapXElem W))
      (overlapInvT W) W.toAffine.polynomial = 0 := by
  have hrel : AdjoinRoot.root (infChartCubic W) ^ 3 +
      algebraMap (Polynomial R) _ (Polynomial.C W.a₂ * Polynomial.X) *
        AdjoinRoot.root (infChartCubic W) ^ 2 +
      algebraMap (Polynomial R) _ (Polynomial.C W.a₄ * Polynomial.X ^ 2 -
        Polynomial.C W.a₁ * Polynomial.X) * AdjoinRoot.root (infChartCubic W) +
      algebraMap (Polynomial R) _ (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
        Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X) = 0 := by
    have h : Polynomial.eval₂ (AdjoinRoot.of (infChartCubic W))
        (AdjoinRoot.root (infChartCubic W))
        (Polynomial.X ^ 3 +
          Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
          Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 -
            Polynomial.C W.a₁ * Polynomial.X) * Polynomial.X +
          Polynomial.C (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
            Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X)) = 0 := by
      rw [show (Polynomial.X ^ 3 +
          Polynomial.C (Polynomial.C W.a₂ * Polynomial.X) * Polynomial.X ^ 2 +
          Polynomial.C (Polynomial.C W.a₄ * Polynomial.X ^ 2 -
            Polynomial.C W.a₁ * Polynomial.X) * Polynomial.X +
          Polynomial.C (Polynomial.C W.a₆ * Polynomial.X ^ 3 -
            Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X) :
          Polynomial (Polynomial R)) = infChartCubic W from rfl]
      exact AdjoinRoot.eval₂_root _
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    rw [show (AdjoinRoot.of (infChartCubic W) : Polynomial R →+* _) =
      algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) from rfl] at h
    linear_combination h
  rw [show W.toAffine.polynomial = Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C W.toAffine.a₁ * Polynomial.X +
        Polynomial.C W.toAffine.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.toAffine.a₂ * Polynomial.X ^ 2 +
        Polynomial.C W.toAffine.a₄ * Polynomial.X + Polynomial.C W.toAffine.a₆) from rfl]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.coe_eval₂RingHom, RingHom.coe_comp, Function.comp_apply]
  unfold overlapInvT overlapXElem
  simp only [← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul,
    sub_eq_add_neg, Localization.neg_mk, Localization.add_mk]
  rw [← Localization.mk_zero (1 : Submonoid.powers (infChartTElem W)),
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  simp only [map_sub, map_mul, map_pow] at hrel
  linear_combination (-(infChartTElem W ^ 7)) * hrel


/-- **(T-W7.0i-b4-1)** The overlap map from the affine part into the localized infinity
chart: `x ↦ s/t`, `y ↦ 1/t`. -/
noncomputable def overlapMap (W : WeierstrassCurve R) :
    W.toAffine.CoordinateRing →+*
      Localization.Away (algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
        Polynomial.X) :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom
      ((algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))).comp
        ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C))
      (overlapXElem W))
    (overlapInvT W) (overlap_eval₂_polynomial W)

/-- **(T-W7.0i-b4-1x)** `overlapMap` sends `x` to `s/t`. -/
theorem overlapMap_coordX (W : WeierstrassCurve R) :
    overlapMap W (coordX W) = overlapXElem W := by
  rw [show coordX W = AdjoinRoot.of W.toAffine.polynomial Polynomial.X from rfl]
  unfold overlapMap
  rw [AdjoinRoot.lift_of]
  exact Polynomial.eval₂_X _ _

/-- **(T-W7.0i-b4-1y)** `overlapMap` sends `y` to `1/t`. -/
theorem overlapMap_coordY (W : WeierstrassCurve R) :
    overlapMap W (coordY W) = overlapInvT W := by
  rw [show coordY W = AdjoinRoot.root W.toAffine.polynomial from rfl]
  unfold overlapMap
  rw [AdjoinRoot.lift_root]

/-- **(T-W7.0i-b4, the equalizer core)** A pair — a function on the affine part and a
function on the infinity chart — agreeing in the overlap localization is a (shared)
constant. Shared-witness `∃`-with-`∧` (statement-splitting exception: one witness `r`
serves both charts). This is the algebraic heart of `Γ ≅ R`; the `x²y⁻¹` pole-order-1
exclusion lives inside its proof (audit A3 normal form on the free bases from 0i-a/b2). -/
theorem overlap_pair_eq_baseRing (W : WeierstrassCurve R)
    (a : W.toAffine.CoordinateRing) (b : AdjoinRoot (infChartCubic W))
    (hab : overlapMap W a = algebraMap _ _ b) :
    ∃ r : R, a = algebraMap R _ r ∧ b = algebraMap R _ r := by
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
  have hs : infChartQuotEquiv W (Ideal.Quotient.mk _ (MvPolynomial.X infChartS)) =
      AdjoinRoot.root (infChartCubic W) := by
    show Ideal.quotientEquivAlg _ _ (infChartPolyEquiv (R := R)) _
      (Ideal.Quotient.mk _ (MvPolynomial.X infChartS)) = _
    rw [Ideal.quotientEquivAlg_mk, infChartPolyEquiv_X_s]
    rfl
  have key : ∀ m, m * (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 1
      W.toProjective.polynomial}) (MvPolynomial.X ⟨0, by decide⟩)) = 0 → m = 0 := by
    intro m hm
    have h1 : infChartQuotEquiv W m * AdjoinRoot.root (infChartCubic W) = 0 := by
      rw [← hs, ← map_mul, hm, map_zero]
    have h2 := (mem_nonZeroDivisors_iff.mp (infChart_root_mem_nonZeroDivisors W)).2 _ h1
    exact (infChartQuotEquiv W).injective (by rw [h2, map_zero])
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

/-- **(T-W7.0i·i4-core, general)** Two morphisms from `Spec A` to a separated scheme that
agree after inverting a nonzerodivisor are equal — the NON-reduced replacement for
density arguments: the equalizer is a closed immersion (separatedness), the localization
factors through it, and injectivity of `A → A[1/a]` kills the ideal. Mirrors the
Over-packaging of mathlib's `ext_of_isDominant_of_isSeparated`; the ending is
`IsClosedImmersion.isIso_of_injective_of_isAffine` instead of reducedness. -/
theorem spec_hom_ext_of_nonZeroDivisor {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) [IsLocalization.Away a B] {Z : Scheme.{u}}
    [Z.IsSeparated] {f g : Spec (CommRingCat.of A) ⟶ Z}
    (ha : a ∈ nonZeroDivisors A)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ g) : f = g := by
  have hfg : f ≫ terminal.from Z = g ≫ terminal.from Z := terminal.hom_ext _ _
  let X' : Over (⊤_ Scheme.{u}) := Over.mk (f ≫ terminal.from Z)
  let Y' : Over (⊤_ Scheme.{u}) := Over.mk (terminal.from Z)
  let U' : Over (⊤_ Scheme.{u}) := Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f ≫ terminal.from Z)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  let ι' : U' ⟶ X' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  haveI : IsSeparated Y'.hom :=
    show IsSeparated (terminal.from Z) from Scheme.IsSeparated.isSeparated_terminal_from
  have hlift : (equalizer.lift ι' (by ext1; exact h)).left ≫ (equalizer.ι f' g').left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hinj : Function.Injective ((equalizer.ι f' g').left.appTop) := by
    have happ := congrArg Scheme.Hom.appTop hlift
    rw [Scheme.Hom.comp_appTop] at happ
    have hloc : Function.Injective
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop) := by
      have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
      have halg : Function.Injective (algebraMap A B) :=
        IsLocalization.injective B (Submonoid.powers_le.mpr ha)
      have : (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop =
          (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
            CommRingCat.ofHom (algebraMap A B) ≫
              (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
        rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [this]
      intro x y hxy
      simp only [CommRingCat.comp_apply] at hxy
      have h1 := (ConcreteCategory.isIso_iff_bijective
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).mp
        inferInstance |>.injective hxy
      have h2 := halg h1
      exact ((ConcreteCategory.isIso_iff_bijective
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom).mp inferInstance).injective h2
    intro x y hxy
    have h1 := congrArg (fun φ => φ.hom x) happ
    have h2 := congrArg (fun φ => φ.hom y) happ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
    exact hloc ((h1.symm.trans (congrArg _ hxy)).trans h2)
  haveI : IsAffine X'.left := show IsAffine (Spec (CommRingCat.of A)) from inferInstance
  haveI := IsClosedImmersion.isIso_of_injective_of_isAffine
    (f := (equalizer.ι f' g').left) hinj
  exact (cancel_epi (equalizer.ι f' g').left).mp congr($(equalizer.condition f' g').left)

/-- **(T-W7.0i·i4-ζ)** In each chart `j` of the model, the localization element carrying the
`Z`-coordinate (`Xⱼ`-denominator) is a nonzerodivisor: `j = 2` trivially (it is `1`-ish);
`j = 1` via the infinity-chart bridge (`infChart_t_mem_nonZeroDivisors`); `j = 0` via the
constant-coefficient-unit form of the chart cubic in the `z`-variable
(`adjoinRoot_root_mem_nonZeroDivisors`-style). -/
lemma chart_isLocalizationElem_nonZeroDivisor (W : WeierstrassCurve R) (j : Fin 3) :
    HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W j) (mk_X_mem_quotientGrading_one W 2) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))) := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · -- chart 0: the z-coordinate, via the z-outer bridge
    refine mem_nonZeroDivisors_of_ringEquiv (chartCoordEquiv W 0).symm ?_
    have hkey : (chartCoordEquiv W 0).symm (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 0) (mk_X_mem_quotientGrading_one W 2)) =
        Ideal.Quotient.mk _ (MvPolynomial.X (⟨2, by decide⟩ : {k : Fin 3 // k ≠ 0})) := by
      rw [RingEquiv.symm_apply_eq]
      exact (chartCoordEquiv_mk_X W 0 ⟨2, by decide⟩).symm
    exact hkey.symm ▸ zChart_z_nonZeroDivisor W
  · -- chart 1: the t-coordinate, via the infinity-chart bridge
    refine mem_nonZeroDivisors_of_ringEquiv (chartCoordEquiv W 1).symm ?_
    have hkey : (chartCoordEquiv W 1).symm (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) =
        Ideal.Quotient.mk _ (MvPolynomial.X infChartT) := by
      rw [RingEquiv.symm_apply_eq]
      exact (chartCoordEquiv_mk_X W 1 infChartT).symm
    exact hkey.symm ▸ infChart_t_nonZeroDivisor W
  · -- chart 2: the element is 1
    have h1 : HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 2) = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        show (1 : Localization (Submonoid.powers ((quotientGradingHom (projIdeal W))
          (MvPolynomial.X 2)))) = Localization.mk 1 1 from Localization.mk_one.symm,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by push_cast; ring⟩
    exact h1.symm ▸ Submonoid.one_mem _

theorem projModel_hom_ext_of_affine (W : WeierstrassCurve R) {Z : Scheme.{u}}
    [Z.IsSeparated] {f g : projModel W ⟶ Z}
    (h : (modelChartCover W).openCover.f (2 : Fin 3) ≫ f =
      (modelChartCover W).openCover.f (2 : Fin 3) ≫ g) :
    f = g := by
  apply (modelChartCover W).openCover.hom_ext
  intro j
  letI := (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X j) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _)).toAlgebra
  haveI := HomogeneousLocalization.Away.isLocalization_mul
    (mk_X_mem_quotientGrading_one W j) (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X j) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _) one_ne_zero
  refine spec_hom_ext_of_nonZeroDivisor
    (B := HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
    (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W j) (mk_X_mem_quotientGrading_one W 2))
    (chart_isLocalizationElem_nonZeroDivisor W j) ?_
  -- **(T-W7.0i·i4)** the affine part is scheme-theoretically dense: agreement on the Z-chart
  -- extends chart-by-chart through the overlap localizations (audit A1/b4; non-reduced-safe).
  have hsqj : Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
        (modelChartCover W).openCover.f j =
      Proj.awayι (quotientGrading (projIdeal W)) _
        (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W j)
          (mk_X_mem_quotientGrading_one W 2)) (by omega) :=
    Proj.SpecMap_awayMap_awayι _ _ _ _ rfl
  have hsq2 : Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
        (modelChartCover W).openCover.f (2 : Fin 3) =
      Proj.awayι (quotientGrading (projIdeal W)) _
        (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W j)
          (mk_X_mem_quotientGrading_one W 2)) (by omega) :=
    Proj.SpecMap_awayMap_awayι _ _ _ _ (mul_comm _ _)
  have hcomp : Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
        (modelChartCover W).openCover.f j =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
        (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
        (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
          (modelChartCover W).openCover.f (2 : Fin 3) := by
    rw [hsqj]
    exact hsq2.symm
  show Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
        ((modelChartCover W).openCover.f j ≫ f) =
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
        ((modelChartCover W).openCover.f j ≫ g)
  calc Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
        ((modelChartCover W).openCover.f j ≫ f)
      = (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
          (modelChartCover W).openCover.f j) ≫ f := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
          (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
          (modelChartCover W).openCover.f (2 : Fin 3)) ≫ f := congrArg (· ≫ f) hcomp
    _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
          (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
          ((modelChartCover W).openCover.f (2 : Fin 3) ≫ f) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
          (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
          ((modelChartCover W).openCover.f (2 : Fin 3) ≫ g) := congrArg _ h
    _ = (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W j)
          (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))) ≫
          (modelChartCover W).openCover.f (2 : Fin 3)) ≫ g := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
          (modelChartCover W).openCover.f j) ≫ g := congrArg (· ≫ g) hcomp.symm
    _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) rfl)) ≫
          ((modelChartCover W).openCover.f j ≫ g) := Category.assoc _ _ _

/-- **(T-W7.0i·i5, decl `locallyWeierstrass_pushforward_O_eq_O`)** For any locally-Weierstrass
family `π : E ⟶ S` the structure map on sections `Γ(S, U) ⟶ Γ(E, π⁻¹U)` is an isomorphism for
every open `U` — i.e. `O_S ≅ π_*O_E` as sheaves. Universally valid (base changes are again
locally Weierstrass, so this statement instantiates). Sheafification of
`projModel_globalSections_eq_baseRing` over chart opens. Source: reviewer round 1 §Q2. -/
theorem locallyWeierstrass_pushforward_O_eq_O {S : Scheme.{u}} (G : EllipticCurveGeom S)
    (U : S.Opens) : IsIso (G.π.app U) := by
  sorry

end ModularCurves
