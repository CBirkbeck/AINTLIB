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

/-- The chart opens of the model are the `basicOpen`s of the coordinate classes. -/
lemma chartOpensRange_eq_basicOpen (W : WeierstrassCurve R) (j : Fin 3) :
    ((modelChartCover W).openCover.f j).opensRange =
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) := by
  show (Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
    (mk_X_mem_quotientGrading_one W j) one_pos).opensRange = _
  exact Proj.opensRange_awayι _ _ _ _

/-- **(T-W7.0i-b3-1, `basicOpen` form)** The `Y`- and `Z`-coordinate basic opens cover. -/
theorem basicOpen_X1_sup_basicOpen_X2_eq_top (W : WeierstrassCurve R) :
    Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) ⊔
      Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  rw [TopologicalSpace.Opens.mem_sup]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Proj.mem_basicOpen, not_not] at h1 h2
  -- The Weierstrass relation puts `(mk X₀)³` in the span of `mk X₁, mk X₂`.
  have hpoly : (quotientGradingHom (projIdeal W)) W.toProjective.polynomial = 0 := by
    rw [quotientGradingHom_apply, Ideal.Quotient.eq_zero_iff_mem, projIdeal_toIdeal]
    exact Ideal.mem_span_singleton_self _
  have h3 : ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 0)) ^ 3 ∈
      x.asHomogeneousIdeal.toIdeal := by
    have hrel : ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 0)) ^ 3 =
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.C W.a₃ * MvPolynomial.X 2 ^ 2) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) -
        (quotientGradingHom (projIdeal W)) (MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 +
          MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 2) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) := by
      have hz : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 0 ^ 3 -
          ((MvPolynomial.X 1 * MvPolynomial.X 2 +
            MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 2 +
            MvPolynomial.C W.a₃ * MvPolynomial.X 2 ^ 2) * MvPolynomial.X 1 -
          (MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 +
            MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 +
            MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 2) * MvPolynomial.X 2)) = 0 := by
        rw [show MvPolynomial.X 0 ^ 3 -
            ((MvPolynomial.X 1 * MvPolynomial.X 2 +
              MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 2 +
              MvPolynomial.C W.a₃ * MvPolynomial.X 2 ^ 2) * MvPolynomial.X 1 -
            (MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 +
              MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 +
              MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 2) * MvPolynomial.X 2) =
          -W.toProjective.polynomial from by
            rw [WeierstrassCurve.Projective.polynomial]; ring, map_neg, hpoly, neg_zero]
      simp only [map_sub, map_mul, map_pow] at hz
      linear_combination hz
    rw [hrel]
    exact sub_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  have h0 : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 0) ∈
      x.asHomogeneousIdeal.toIdeal :=
    x.isPrime.mem_of_pow_mem 3 h3
  -- A prime containing all three coordinates contains the irrelevant ideal.
  refine x.not_irrelevant_le fun z hz => ?_
  refine Ideal.span_le.mpr ?_ (quotient_irrelevant_le_span_mk_X W hz)
  rintro _ ⟨i, rfl⟩
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  · exact h0
  · exact h1
  · exact h2

/-- **(T-W7.0i-b3-1)** The `Y`-chart and `Z`-chart opens cover the model: the complement of
the `Z`-chart is the zero section, which lies in the `Y`-chart. (Two charts suffice for the
global-sections equalizer — single overlap.) Source: audit A3. -/
theorem chartY_sup_chartZ_eq_top (W : WeierstrassCurve R) :
    ((modelChartCover W).openCover.f (1 : Fin 3)).opensRange ⊔
      ((modelChartCover W).openCover.f (2 : Fin 3)).opensRange = ⊤ := by
  rw [chartOpensRange_eq_basicOpen, chartOpensRange_eq_basicOpen]
  exact basicOpen_X1_sup_basicOpen_X2_eq_top W

/-- **(the `Γ`-bridge, ForMathlib-grade)** For a positive-degree homogeneous `f`, the
global-sections map of `awayι` is restriction to the basic open followed by the canonical
`awayToSection`-inverse: `Γ(awayι) ≫ ΓSpec = res ≫ (A_f)₀-identification`. -/
private lemma Proj_awayι_appTop_ΓSpecIso {R₀ A : Type u} [CommRing R₀] [CommRing A]
    [Algebra R₀ A] (𝒜 : ℕ → Submodule R₀ A) [GradedAlgebra 𝒜]
    {m : ℕ} (f : A) (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom =
    (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv := by
  rw [Iso.eq_comp_inv, Category.assoc]
  have hσ : (Proj.basicOpenIsoAway 𝒜 f f_deg hm).hom = Proj.awayToSection 𝒜 f := rfl
  rw [hσ]
  have hhomTop : (Proj.basicOpenToSpec 𝒜 f).appTop ≫
      (Proj.basicOpen 𝒜 f).topIso.hom =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f := by
    rw [show (Proj.basicOpenToSpec 𝒜 f).appTop =
      (Proj.basicOpenToSpec 𝒜 f).app ⊤ from rfl]
    rw [Proj.basicOpenToSpec_app_top, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← hhomTop]
  rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm]
  rw [Scheme.Hom.comp_appTop, Category.assoc]
  rw [show Proj.basicOpenToSpec 𝒜 f =
    (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom from rfl]
  rw [← Category.assoc ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop)]
  rw [show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop ≫
      (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop = 𝟙 _ from by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp]
  rw [Category.id_comp, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  refine ((Proj 𝒜).presheaf.map_comp _ _).symm.trans
    (congrArg ((Proj 𝒜).presheaf.map) ?_)
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- **(the structure square)** The composite `R → Γ(model, ⊤) → Γ(model, D₊(F)) ≅ (A_F)₀`
is the canonical grade-zero algebra map. -/
private lemma structure_section_square (W : WeierstrassCurve R) {m : ℕ}
    (F : MvPolynomial (Fin 3) R ⧸ (projIdeal W).toIdeal)
    (F_deg : F ∈ quotientGrading (projIdeal W) m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (projModelπ W).appTop ≫
      (projModel W).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway (quotientGrading (projIdeal W)) F F_deg hm).inv =
    CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers F)).comp
      (algebraMapGradeZero (projIdeal W))) := by
  have hbridge := Proj_awayι_appTop_ΓSpecIso (quotientGrading (projIdeal W)) F F_deg hm
  have hscheme : Proj.awayι (quotientGrading (projIdeal W)) F F_deg hm ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom
        (quotientGrading (projIdeal W)) (Submonoid.powers F)).comp
        (algebraMapGradeZero (projIdeal W)))) := by
    rw [show projModelπ W = Proj.toSpecZero (quotientGrading (projIdeal W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W))) from rfl]
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hΓ := congrArg Scheme.Hom.appTop hscheme
  rw [Scheme.Hom.comp_appTop] at hΓ
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (projModelπ W).appTop ≫
        (projModel W).presheaf.map (homOfLE le_top).op ≫
        (Proj.basicOpenIsoAway (quotientGrading (projIdeal W)) F F_deg hm).inv
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ((projModelπ W).appTop ≫
          (Proj.awayι (quotientGrading (projIdeal W)) F F_deg hm).appTop) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
            (quotientGrading (projIdeal W)) F))).hom := by
        rw [← hbridge]
        simp only [Category.assoc]
    _ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom
            (quotientGrading (projIdeal W)) (Submonoid.powers F)).comp
            (algebraMapGradeZero (projIdeal W))))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
            (quotientGrading (projIdeal W)) F))).hom := by rw [hΓ]
    _ = _ := by
        rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Sections over a chart open are the chart's degree-zero localization: open-immersion
`Γ`-comparison (`appIso` at `⊤`) composed with `ΓSpecIso`. -/
private noncomputable def chartSectionsIso (W : WeierstrassCurve R) (j : Fin 3) :
    Γ(projModel W, ((modelChartCover W).openCover.f j).opensRange) ≅
      (modelChartCover W).X j :=
  (((projModel W).presheaf.mapIso (eqToIso
      (Scheme.Hom.image_top_eq_opensRange ((modelChartCover W).openCover.f j))).op).trans
    (((modelChartCover W).openCover.f j).appIso ⊤)).trans
    (Scheme.ΓSpecIso ((modelChartCover W).X j))

/-- **(T-W7.0i-b3-2)** Sections over the `Y`-chart open are the chart ring (open-immersion
`Γ`-comparison composed with the repo's `chartCoordEquiv`). -/
noncomputable def chartYSectionsEquiv (W : WeierstrassCurve R) :
    Γ(projModel W, ((modelChartCover W).openCover.f (1 : Fin 3)).opensRange) ≃+*
      (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial}) :=
  (chartSectionsIso W 1).commRingCatIsoToRingEquiv.trans (chartCoordEquiv W 1).symm

/-- **(T-W7.0i-b3-3)** Sections over the `Z`-chart open are the chart ring. -/
noncomputable def chartZSectionsEquiv (W : WeierstrassCurve R) :
    Γ(projModel W, ((modelChartCover W).openCover.f (2 : Fin 3)).opensRange) ≃+*
      (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial}) :=
  (chartSectionsIso W 2).commRingCatIsoToRingEquiv.trans (chartCoordEquiv W 2).symm

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

/-- **(T-W7.0i-b4-1rel)** The chart-cubic relation for `root`, in `algebraMap` form:
`s³ + (a₂t)s² + (a₄t² − a₁t)s + (a₆t³ − a₃t² − t) = 0` in the infinity-chart ring. -/
lemma infChart_root_relation (W : WeierstrassCurve R) :
    AdjoinRoot.root (infChartCubic W) ^ 3 +
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
  have hrel := infChart_root_relation W
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

/-- The `1`-coordinate of `s³` in the infinity chart: `t + a₃t² − a₆t³`. -/
private noncomputable def sCubeCoord₀ (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.X + Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.C W.a₆ * Polynomial.X ^ 3

/-- The `s`-coordinate of `s³` in the infinity chart: `a₁t − a₄t²`. -/
private noncomputable def sCubeCoord₁ (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C W.a₁ * Polynomial.X - Polynomial.C W.a₄ * Polynomial.X ^ 2

/-- The `s²`-coordinate of `s³` in the infinity chart: `−a₂t`. -/
private noncomputable def sCubeCoord₂ (W : WeierstrassCurve R) : Polynomial R :=
  -(Polynomial.C W.a₂ * Polynomial.X)

private lemma X_dvd_sCubeCoord₀ (W : WeierstrassCurve R) : Polynomial.X ∣ sCubeCoord₀ W :=
  ⟨1 + Polynomial.C W.a₃ * Polynomial.X - Polynomial.C W.a₆ * Polynomial.X ^ 2, by
    unfold sCubeCoord₀; ring⟩

private lemma X_dvd_sCubeCoord₁ (W : WeierstrassCurve R) : Polynomial.X ∣ sCubeCoord₁ W :=
  ⟨Polynomial.C W.a₁ - Polynomial.C W.a₄ * Polynomial.X, by unfold sCubeCoord₁; ring⟩

private lemma X_dvd_sCubeCoord₂ (W : WeierstrassCurve R) : Polynomial.X ∣ sCubeCoord₂ W :=
  ⟨-Polynomial.C W.a₂, by unfold sCubeCoord₂; ring⟩

/-- `s³` expanded in the basis `(1, s, s²)` of the infinity chart over `R[t]`. -/
private lemma root_cube_eq (W : WeierstrassCurve R) :
    AdjoinRoot.root (infChartCubic W) ^ 3 =
      algebraMap (Polynomial R) _ (sCubeCoord₀ W) +
        algebraMap (Polynomial R) _ (sCubeCoord₁ W) * AdjoinRoot.root (infChartCubic W) +
        algebraMap (Polynomial R) _ (sCubeCoord₂ W) *
          AdjoinRoot.root (infChartCubic W) ^ 2 := by
  have h := infChart_root_relation W
  unfold sCubeCoord₀ sCubeCoord₁ sCubeCoord₂
  simp only [map_sub, map_add, map_mul, map_pow, map_neg] at h ⊢
  linear_combination h

/-- Coordinates of `sⁱ` in the basis `(1, s, s²)` of the infinity chart over `R[t]`: the
3-term recursion induced by the chart cubic (all recursion coefficients are divisible by
`t`, which encodes `t = s³·unit` — the pole-order bookkeeping). -/
private noncomputable def sPowCoord (W : WeierstrassCurve R) : ℕ → Fin 3 → Polynomial R
  | 0 => ![1, 0, 0]
  | i + 1 =>
    ![sPowCoord W i 2 * sCubeCoord₀ W,
      sPowCoord W i 0 + sPowCoord W i 2 * sCubeCoord₁ W,
      sPowCoord W i 1 + sPowCoord W i 2 * sCubeCoord₂ W]

private lemma sPowCoord_succ_zero (W : WeierstrassCurve R) (i : ℕ) :
    sPowCoord W (i + 1) 0 = sPowCoord W i 2 * sCubeCoord₀ W := rfl

private lemma sPowCoord_succ_one (W : WeierstrassCurve R) (i : ℕ) :
    sPowCoord W (i + 1) 1 = sPowCoord W i 0 + sPowCoord W i 2 * sCubeCoord₁ W := rfl

private lemma sPowCoord_succ_two (W : WeierstrassCurve R) (i : ℕ) :
    sPowCoord W (i + 1) 2 = sPowCoord W i 1 + sPowCoord W i 2 * sCubeCoord₂ W := rfl

/-- `sⁱ` expanded in the basis `(1, s, s²)`: correctness of the coordinate recursion. -/
private lemma root_pow_eq (W : WeierstrassCurve R) (i : ℕ) :
    AdjoinRoot.root (infChartCubic W) ^ i =
      algebraMap (Polynomial R) _ (sPowCoord W i 0) +
        algebraMap (Polynomial R) _ (sPowCoord W i 1) * AdjoinRoot.root (infChartCubic W) +
        algebraMap (Polynomial R) _ (sPowCoord W i 2) *
          AdjoinRoot.root (infChartCubic W) ^ 2 := by
  induction i with
  | zero => simp [sPowCoord]
  | succ i ih =>
    rw [pow_succ, ih, sPowCoord_succ_zero, sPowCoord_succ_one, sPowCoord_succ_two]
    simp only [map_add, map_mul]
    linear_combination
      algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) (sPowCoord W i 2) *
        root_cube_eq W

/-- **(K1, slotwise)** T-adic order lower bounds for the three coordinates of `sⁱ`:
`t^⌈i/3⌉ ∣ c₀(sⁱ)`, `t^⌈(i−1)/3⌉ ∣ c₁(sⁱ)`, `t^⌊i/3⌋ ∣ c₂(sⁱ)`. -/
private lemma X_pow_dvd_sPowCoord_aux (W : WeierstrassCurve R) (i : ℕ) :
    Polynomial.X ^ ((i + 2) / 3) ∣ sPowCoord W i 0 ∧
      Polynomial.X ^ ((i + 1) / 3) ∣ sPowCoord W i 1 ∧
        Polynomial.X ^ (i / 3) ∣ sPowCoord W i 2 := by
  induction i with
  | zero => exact ⟨by simp [sPowCoord], by simp [sPowCoord], by simp [sPowCoord]⟩
  | succ i ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [sPowCoord_succ_zero, show (i + 1 + 2) / 3 = i / 3 + 1 by omega, pow_succ]
      exact mul_dvd_mul h2 (X_dvd_sCubeCoord₀ W)
    · rw [sPowCoord_succ_one]
      refine dvd_add ((pow_dvd_pow _ (by omega)).trans h0) ?_
      refine (pow_dvd_pow (Polynomial.X : Polynomial R)
        (show (i + 1 + 1) / 3 ≤ i / 3 + 1 by omega)).trans ?_
      rw [pow_succ]
      exact mul_dvd_mul h2 (X_dvd_sCubeCoord₁ W)
    · rw [sPowCoord_succ_two]
      refine dvd_add ((pow_dvd_pow _ (by omega)).trans h1) ?_
      refine (pow_dvd_pow (Polynomial.X : Polynomial R)
        (show (i + 1) / 3 ≤ i / 3 + 1 by omega)).trans ?_
      rw [pow_succ]
      exact mul_dvd_mul h2 (X_dvd_sCubeCoord₂ W)

/-- **(K1)** T-adic order lower bound: the `sʲ`-coordinate of `sⁱ` is divisible by
`t^⌈(i−j)/3⌉`. -/
private lemma X_pow_dvd_sPowCoord (W : WeierstrassCurve R) (i : ℕ) (j : Fin 3) :
    Polynomial.X ^ ((i - (j : ℕ) + 2) / 3) ∣ sPowCoord W i j := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_sPowCoord_aux W i).1
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_sPowCoord_aux W i).2.1
  · exact (pow_dvd_pow _ (by omega)).trans (X_pow_dvd_sPowCoord_aux W i).2.2

/-- **(K1, coefficient form)** Coefficients of the `sʲ`-coordinate of `sⁱ` vanish below the
leading T-adic level: `3c + j < i` kills `coeff c`. -/
private lemma sPowCoord_coeff_eq_zero (W : WeierstrassCurve R) {i c : ℕ} {j : Fin 3}
    (h : 3 * c + (j : ℕ) < i) : (sPowCoord W i j).coeff c = 0 :=
  Polynomial.X_pow_dvd_iff.mp (X_pow_dvd_sPowCoord W i j) c
    (by have hj := j.isLt; omega)

/-- **(K2, slotwise)** The leading coefficient is exactly `1`: on the matching slot
`j = i % 3`, the coordinate is `t^(i/3) + O(t^(i/3+1))`. -/
private lemma sPowCoord_sub_lead_aux (W : WeierstrassCurve R) (i : ℕ) :
    (i % 3 = 0 → Polynomial.X ^ (i / 3 + 1) ∣ sPowCoord W i 0 - Polynomial.X ^ (i / 3)) ∧
      (i % 3 = 1 → Polynomial.X ^ (i / 3 + 1) ∣ sPowCoord W i 1 - Polynomial.X ^ (i / 3)) ∧
        (i % 3 = 2 → Polynomial.X ^ (i / 3 + 1) ∣ sPowCoord W i 2 - Polynomial.X ^ (i / 3)) := by
  induction i with
  | zero =>
    refine ⟨fun _ => by simp [sPowCoord], fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  | succ i ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨A, hA⟩ := ih2 (by omega)
      have hs : sPowCoord W i 2 =
          Polynomial.X ^ (i / 3 + 1) * A + Polynomial.X ^ (i / 3) := by
        linear_combination hA
      rw [sPowCoord_succ_zero, hs, show (i + 1) / 3 = i / 3 + 1 by omega]
      refine ⟨A * (1 + Polynomial.C W.a₃ * Polynomial.X -
        Polynomial.C W.a₆ * Polynomial.X ^ 2) +
        Polynomial.C W.a₃ - Polynomial.C W.a₆ * Polynomial.X, ?_⟩
      unfold sCubeCoord₀
      ring
    · obtain ⟨A, hA⟩ := ih0 (by omega)
      obtain ⟨B, hB⟩ := (X_pow_dvd_sPowCoord_aux W i).2.2
      rw [sPowCoord_succ_one, show (i + 1) / 3 = i / 3 by omega]
      have hsplit : sPowCoord W i 0 + sPowCoord W i 2 * sCubeCoord₁ W -
          Polynomial.X ^ (i / 3) =
          (sPowCoord W i 0 - Polynomial.X ^ (i / 3)) +
            sPowCoord W i 2 * sCubeCoord₁ W := by ring
      rw [hsplit]
      refine dvd_add ⟨A, hA⟩ ?_
      rw [hB]
      exact ⟨B * (Polynomial.C W.a₁ - Polynomial.C W.a₄ * Polynomial.X), by
        unfold sCubeCoord₁; ring⟩
    · obtain ⟨A, hA⟩ := ih1 (by omega)
      obtain ⟨B, hB⟩ := (X_pow_dvd_sPowCoord_aux W i).2.2
      rw [sPowCoord_succ_two, show (i + 1) / 3 = i / 3 by omega]
      have hsplit : sPowCoord W i 1 + sPowCoord W i 2 * sCubeCoord₂ W -
          Polynomial.X ^ (i / 3) =
          (sPowCoord W i 1 - Polynomial.X ^ (i / 3)) +
            sPowCoord W i 2 * sCubeCoord₂ W := by ring
      rw [hsplit]
      refine dvd_add ⟨A, hA⟩ ?_
      rw [hB]
      exact ⟨B * -Polynomial.C W.a₂, by unfold sCubeCoord₂; ring⟩

/-- **(K2)** For `i ≡ j (mod 3)`, the `sʲ`-coordinate of `sⁱ` is
`t^((i−j)/3) + O(t^((i−j)/3+1))`. -/
private lemma X_pow_dvd_sPowCoord_sub (W : WeierstrassCurve R) (i : ℕ) (j : Fin 3)
    (hmod : i % 3 = (j : ℕ)) :
    Polynomial.X ^ ((i - (j : ℕ)) / 3 + 1) ∣
      sPowCoord W i j - Polynomial.X ^ ((i - (j : ℕ)) / 3) := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · rw [show ((i - ((0 : Fin 3) : ℕ)) / 3) = i / 3 by omega]
    exact (sPowCoord_sub_lead_aux W i).1 hmod
  · rw [show ((i - ((1 : Fin 3) : ℕ)) / 3) = i / 3 by omega]
    exact (sPowCoord_sub_lead_aux W i).2.1 hmod
  · rw [show ((i - ((2 : Fin 3) : ℕ)) / 3) = i / 3 by omega]
    exact (sPowCoord_sub_lead_aux W i).2.2 hmod

/-- **(K2, coefficient form)** The leading coefficient of the matching coordinate is `1`. -/
private lemma sPowCoord_coeff_lead (W : WeierstrassCurve R) {i : ℕ} {j : Fin 3}
    (hmod : i % 3 = (j : ℕ)) :
    (sPowCoord W i j).coeff ((i - (j : ℕ)) / 3) = 1 := by
  obtain ⟨A, hA⟩ := X_pow_dvd_sPowCoord_sub W i j hmod
  have h := congrArg (Polynomial.coeff · ((i - (j : ℕ)) / 3)) hA
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_true] at h
  have hzero : (Polynomial.X ^ ((i - (j : ℕ)) / 3 + 1) * A).coeff ((i - (j : ℕ)) / 3) = 0 :=
    Polynomial.X_pow_dvd_iff.mp (dvd_mul_right _ _) _ (Nat.lt_succ_self _)
  rw [hzero] at h
  linear_combination h

private lemma tel_mul_overlapInvT (W : WeierstrassCurve R) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
      (infChartTElem W) * overlapInvT W = 1 := by
  unfold overlapInvT
  rw [Localization.mk_eq_mk', IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [mul_comm]

private lemma tel_mul_overlapXElem (W : WeierstrassCurve R) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) * overlapXElem W =
      algebraMap _ _ (AdjoinRoot.root (infChartCubic W)) := by
  unfold overlapXElem
  rw [Localization.mk_eq_mk', IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [mul_comm]

/-- The `sʲ`-coordinate of the `t`-cleared image of `f(x)`: `Σᵢ fᵢ·cⱼ(sⁱ)·t^(N−i)`. -/
private noncomputable def coordOf (W : WeierstrassCurve R) (f : Polynomial R) (N : ℕ)
    (j : Fin 3) : Polynomial R :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (f.coeff i) * (sPowCoord W i j * Polynomial.X ^ (N - i))

private lemma coordOf_zero (W : WeierstrassCurve R) (N : ℕ) (j : Fin 3) :
    coordOf W 0 N j = 0 := by
  unfold coordOf
  simp

private lemma coordOf_C (W : WeierstrassCurve R) (r : R) (N : ℕ) (j : Fin 3) :
    coordOf W (Polynomial.C r) N j =
      Polynomial.C r * (sPowCoord W 0 j * Polynomial.X ^ N) := by
  unfold coordOf
  rw [Finset.sum_eq_single 0]
  · rw [Polynomial.coeff_C_zero, Nat.sub_zero]
  · intro i _ hne
    rw [Polynomial.coeff_C, if_neg hne, Polynomial.C_0, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **(cross-kill)** Every coefficient of `coordOf` strictly below the leading T-adic level
`3N − 2·deg f` vanishes. -/
private lemma coordOf_coeff_eq_zero (W : WeierstrassCurve R) {f : Polynomial R} {N k : ℕ}
    {j : Fin 3} (h : 3 * k + (j : ℕ) + 2 * f.natDegree < 3 * N) :
    (coordOf W f N j).coeff k = 0 := by
  unfold coordOf
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hiN : i < N + 1 := Finset.mem_range.mp hi
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  rcases Nat.lt_or_ge k (N - i) with hlt | hle
  · rw [if_neg (not_le.mpr hlt), mul_zero]
  · rcases Nat.lt_or_ge f.natDegree i with hid | hid
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hid, zero_mul]
    · rw [if_pos hle, sPowCoord_coeff_eq_zero W (by have := j.isLt; omega), mul_zero]

/-- **(the leading slot)** At the leading T-adic level of `f` — coordinate `deg f % 3`,
T-order `N − deg f + deg f/3` — the coefficient of `coordOf` is exactly the leading
coefficient of `f`. -/
private lemma coordOf_coeff_lead (W : WeierstrassCurve R) {f : Polynomial R} {N : ℕ}
    (hfN : f.natDegree ≤ N) {j : Fin 3}
    (hj : f.natDegree % 3 = (j : ℕ)) :
    (coordOf W f N j).coeff (N - f.natDegree + f.natDegree / 3) = f.leadingCoeff := by
  unfold coordOf
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single f.natDegree]
  · have hj3 := j.isLt
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow', if_pos (by omega),
      show N - f.natDegree + f.natDegree / 3 - (N - f.natDegree) = (f.natDegree - (j : ℕ)) / 3
        by omega,
      sPowCoord_coeff_lead W hj, mul_one]
    rfl
  · intro i hi hne
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    have hj3 := j.isLt
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    rcases Nat.lt_or_ge (N - f.natDegree + f.natDegree / 3) (N - i) with hlt | hle
    · rw [if_neg (not_le.mpr hlt), mul_zero]
    · rcases Nat.lt_or_ge f.natDegree i with hid | hid
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hid, zero_mul]
      · have hilt : i < f.natDegree := lt_of_le_of_ne hid hne
        rw [if_pos hle, sPowCoord_coeff_eq_zero W (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The `t`-cleared evaluation, reduced to the basis `(1, s, s²)`: the `Σᵢ fᵢ·sⁱ·t^(N−i)`
element of the infinity chart in coordinate form. -/
private lemma sum_range_eq_coordOf (W : WeierstrassCurve R) (f : Polynomial R) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1),
        algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
            (Polynomial.C (f.coeff i) * Polynomial.X ^ (N - i)) *
          AdjoinRoot.root (infChartCubic W) ^ i =
      algebraMap (Polynomial R) _ (coordOf W f N 0) +
        algebraMap (Polynomial R) _ (coordOf W f N 1) *
          AdjoinRoot.root (infChartCubic W) +
        algebraMap (Polynomial R) _ (coordOf W f N 2) *
          AdjoinRoot.root (infChartCubic W) ^ 2 := by
  unfold coordOf
  rw [map_sum, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [root_pow_eq W i]
  simp only [map_mul]
  ring

/-- One cleared term: `t^N·(φ(c)·(s/t)ⁱ) = image of (c·t^(N−i))·sⁱ` for `i ≤ N`. -/
private lemma cleared_term (W : WeierstrassCurve R) (c : R) {i N : ℕ} (hiN : i ≤ N) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) ^ N *
        (((algebraMap (AdjoinRoot (infChartCubic W))
            (Localization.Away (infChartTElem W))).comp
          ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C)) c *
          overlapXElem W ^ i) =
      algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
            (Polynomial.C c * Polynomial.X ^ (N - i)) *
          AdjoinRoot.root (infChartCubic W) ^ i) := by
  have hxel := tel_mul_overlapXElem W
  rw [RingHom.comp_apply, RingHom.comp_apply]
  simp only [map_mul, map_pow]
  rw [← hxel, mul_pow]
  rw [show (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) ^ N =
    (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) ^ (N - i) *
    (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) ^ i from by
      rw [← pow_add, Nat.sub_add_cancel hiN]]
  rw [show algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) Polynomial.X =
    infChartTElem W from rfl]
  ring

private lemma infChartBasis_apply (W : WeierstrassCurve R) [Nontrivial R] (j : Fin 3) :
    infChartBasis W j = AdjoinRoot.root (infChartCubic W) ^ (j : ℕ) := by
  simp [infChartBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis,
    AdjoinRoot.powerBasis'_gen]

/-- Absorb one `t` of `t^N` into `1/t`: `t^N·(z/t) = t^(N−1)·z` for `N ≥ 1`. -/
private lemma pow_mul_mul_overlapInvT (W : WeierstrassCurve R) {N : ℕ} (hN : 1 ≤ N)
    (z : Localization.Away (infChartTElem W)) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) ^ N * (z * overlapInvT W) =
      algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) ^ (N - 1) * z := by
  rw [show (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) ^ N =
    (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) ^ (N - 1) *
    algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W) from by
      rw [← pow_succ, Nat.sub_add_cancel hN]]
  calc algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
          (infChartTElem W) ^ (N - 1) *
        algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
          (infChartTElem W) * (z * overlapInvT W) =
      algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
          (infChartTElem W) ^ (N - 1) * z *
        (algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
          (infChartTElem W) * overlapInvT W) := by ring
    _ = _ := by rw [tel_mul_overlapInvT W, mul_one]

/-- **(the cleared coordinate identity)** From agreement of `p(x) + q(x)y` with a chart
function `b` in the overlap, clearing `t^N` and comparing `(1, s, s²)`-coordinates:
`coordOf p N j + coordOf q (N−1) j = t^N·(repr b)ⱼ` in `R[t]`. -/
private lemma overlap_coordOf_eq (W : WeierstrassCurve R) [Nontrivial R]
    (p q : Polynomial R) (b : AdjoinRoot (infChartCubic W)) {N : ℕ}
    (hp : p.natDegree < N + 1) (hq : q.natDegree < N)
    (hab : Polynomial.eval₂
        (((algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))).comp
          ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C)))
        (overlapXElem W) p +
      Polynomial.eval₂
        (((algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))).comp
          ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C)))
        (overlapXElem W) q * overlapInvT W =
      algebraMap _ _ b) (j : Fin 3) :
    coordOf W p N j + coordOf W q (N - 1) j =
      Polynomial.X ^ N * ((infChartBasis W).repr b j) := by
  have htel := tel_mul_overlapInvT W
  have hNpos : 1 ≤ N := by omega
  -- Clear `t^N` in the localization and pull back along the injective `algebraMap`.
  have hinj : Function.Injective (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr (infChart_t_mem_nonZeroDivisors W))
  have key : (∑ i ∈ Finset.range (N + 1),
        algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
            (Polynomial.C (p.coeff i) * Polynomial.X ^ (N - i)) *
          AdjoinRoot.root (infChartCubic W) ^ i) +
      (∑ i ∈ Finset.range (N - 1 + 1),
        algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))
            (Polynomial.C (q.coeff i) * Polynomial.X ^ (N - 1 - i)) *
          AdjoinRoot.root (infChartCubic W) ^ i) =
      infChartTElem W ^ N * b := by
    apply hinj
    rw [map_add, map_sum, map_sum, map_mul, map_pow, ← hab, mul_add]
    congr 1
    · rw [Polynomial.eval₂_eq_sum_range' _ hp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N := by have := Finset.mem_range.mp hi; omega
      exact (cleared_term W (p.coeff i) hiN).symm
    · rw [Polynomial.eval₂_eq_sum_range' _
        (show q.natDegree < N - 1 + 1 by omega),
        pow_mul_mul_overlapInvT W hNpos, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N - 1 := by have := Finset.mem_range.mp hi; omega
      exact (cleared_term W (q.coeff i) hiN).symm
  -- Reduce both sides to `(1, s, s²)`-coordinates and compare via the basis.
  rw [sum_range_eq_coordOf W p N, sum_range_eq_coordOf W q (N - 1)] at key
  have hb : b = algebraMap (Polynomial R) _ ((infChartBasis W).repr b 0) +
      algebraMap (Polynomial R) _ ((infChartBasis W).repr b 1) *
        AdjoinRoot.root (infChartCubic W) +
      algebraMap (Polynomial R) _ ((infChartBasis W).repr b 2) *
        AdjoinRoot.root (infChartCubic W) ^ 2 := by
    conv_lhs => rw [← (infChartBasis W).sum_repr b]
    rw [Fin.sum_univ_three]
    simp only [infChartBasis_apply, Algebra.smul_def,
      show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
      show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_zero, pow_one, mul_one]
  rw [hb] at key
  have hT : infChartTElem W ^ N =
      algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W)) (Polynomial.X ^ N) := by
    rw [map_pow]
  rw [hT] at key
  have hz : ∀ j : Fin 3,
      (coordOf W p N j + coordOf W q (N - 1) j) -
        Polynomial.X ^ N * ((infChartBasis W).repr b j) = 0 := by
    have hli := Fintype.linearIndependent_iff.mp (infChartBasis W).linearIndependent
      (fun j => (coordOf W p N j + coordOf W q (N - 1) j) -
        Polynomial.X ^ N * ((infChartBasis W).repr b j))
    have hsum : ∑ j : Fin 3,
        ((coordOf W p N j + coordOf W q (N - 1) j) -
          Polynomial.X ^ N * ((infChartBasis W).repr b j)) • infChartBasis W j = 0 := by
      rw [Fin.sum_univ_three]
      simp only [infChartBasis_apply, Algebra.smul_def,
        show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_zero, pow_one, mul_one,
        map_sub, map_add, map_mul]
      linear_combination key
    exact hli hsum
  have := hz j
  linear_combination this

/-- **(T-W7.0i-b4, the equalizer core)** A pair — a function on the affine part and a
function on the infinity chart — agreeing in the overlap localization is a (shared)
constant. Shared-witness `∃`-with-`∧` (statement-splitting exception: one witness `r`
serves both charts). This is the algebraic heart of `Γ ≅ R`; the `x²y⁻¹` pole-order-1
exclusion lives inside its proof (audit A3 normal form on the free bases from 0i-a/b2). -/
theorem overlap_pair_eq_baseRing (W : WeierstrassCurve R)
    (a : W.toAffine.CoordinateRing) (b : AdjoinRoot (infChartCubic W))
    (hab : overlapMap W a = algebraMap _ _ b) :
    ∃ r : R, a = algebraMap R _ r ∧ b = algebraMap R _ r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton W.toAffine.CoordinateRing := Module.subsingleton R _
    haveI : Subsingleton (AdjoinRoot (infChartCubic W)) := Module.subsingleton R _
    exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  -- Rewrite the overlap agreement into evaluated form.
  have hof : ∀ f : Polynomial R,
      overlapMap W (AdjoinRoot.of W.toAffine.polynomial f) =
        Polynomial.eval₂ (((algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))).comp
          ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C)))
          (overlapXElem W) f := fun f => by
    unfold overlapMap
    rw [AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom]
  rw [map_add, WeierstrassCurve.Affine.CoordinateRing.smul,
    WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, map_mul,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C p) =
      AdjoinRoot.of W.toAffine.polynomial p from rfl,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C q) =
      AdjoinRoot.of W.toAffine.polynomial q from rfl,
    show WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X =
      coordY W from rfl,
    overlapMap_coordY, hof p, hof q] at hab
  -- The cleared coordinate identities at level `N`.
  have h1 := le_max_left p.natDegree (q.natDegree + 1)
  have h2 := le_max_right p.natDegree (q.natDegree + 1)
  set N := max p.natDegree (q.natDegree + 1) with hN
  have hstar := fun j => overlap_coordOf_eq W p q b
    (show p.natDegree < N + 1 by omega) (show q.natDegree < N by omega) hab j
  have hXN : (Polynomial.X : Polynomial R) ^ N ∈ nonZeroDivisors (Polynomial R) :=
    pow_mem Polynomial.X_mem_nonzeroDivisors N
  -- Step 1: `q = 0` — its leading coefficient dies at an odd pole-order slot.
  have hq0 : q = 0 := by
    by_contra hq0
    rcases Nat.lt_or_ge (2 * q.natDegree + 3) (2 * p.natDegree) with hcase | hcase
    · -- The `p`-side leads: kill `p.leadingCoeff`, contradicting `p ≠ 0` (deg ≥ 2).
      have hp0 : p ≠ 0 := by
        intro h
        rw [h] at hcase
        simp at hcase
      have hstar_d := hstar ⟨p.natDegree % 3, by omega⟩
      have hcoeff := congrArg
        (Polynomial.coeff · (N - p.natDegree + p.natDegree / 3)) hstar_d
      simp only [Polynomial.coeff_add] at hcoeff
      rw [coordOf_coeff_lead (W := W) (f := p) (N := N)
          (j := ⟨p.natDegree % 3, by omega⟩) (by omega) rfl,
        coordOf_coeff_eq_zero (W := W) (f := q) (N := N - 1)
          (k := N - p.natDegree + p.natDegree / 3) (j := ⟨p.natDegree % 3, by omega⟩)
          (show 3 * (N - p.natDegree + p.natDegree / 3) + p.natDegree % 3 +
            2 * q.natDegree < 3 * (N - 1) by omega),
        Polynomial.X_pow_dvd_iff.mp (dvd_mul_right _ _) _ (show
          N - p.natDegree + p.natDegree / 3 < N by omega)] at hcoeff
      exact hp0 (Polynomial.leadingCoeff_eq_zero.mp (by linear_combination hcoeff))
    · -- The `q`-side leads (parity: `2·deg p ≠ 2·deg q + 3`): kill `q.leadingCoeff`.
      have hstar_m := hstar ⟨q.natDegree % 3, by omega⟩
      have hcoeff := congrArg
        (Polynomial.coeff · (N - 1 - q.natDegree + q.natDegree / 3)) hstar_m
      simp only [Polynomial.coeff_add] at hcoeff
      rw [coordOf_coeff_lead (W := W) (f := q) (N := N - 1)
          (j := ⟨q.natDegree % 3, by omega⟩) (by omega) rfl,
        coordOf_coeff_eq_zero (W := W) (f := p) (N := N)
          (k := N - 1 - q.natDegree + q.natDegree / 3) (j := ⟨q.natDegree % 3, by omega⟩)
          (show 3 * (N - 1 - q.natDegree + q.natDegree / 3) + q.natDegree % 3 +
            2 * p.natDegree < 3 * N by omega),
        Polynomial.X_pow_dvd_iff.mp (dvd_mul_right _ _) _ (show
          N - 1 - q.natDegree + q.natDegree / 3 < N by omega)] at hcoeff
      exact hq0 (Polynomial.leadingCoeff_eq_zero.mp (by linear_combination hcoeff))
  subst hq0
  -- Step 2: `p` is a constant — a positive degree dies at an even pole-order slot.
  have hpdeg : p.natDegree = 0 := by
    by_contra hpd
    have hp0 : p ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hstar_d := hstar ⟨p.natDegree % 3, by omega⟩
    have hcoeff := congrArg
      (Polynomial.coeff · (N - p.natDegree + p.natDegree / 3)) hstar_d
    simp only [Polynomial.coeff_add] at hcoeff
    rw [coordOf_coeff_lead (W := W) (f := p) (N := N)
        (j := ⟨p.natDegree % 3, by omega⟩) (by omega) rfl,
      coordOf_zero,
      Polynomial.X_pow_dvd_iff.mp (dvd_mul_right _ _) _ (show
        N - p.natDegree + p.natDegree / 3 < N by omega)] at hcoeff
    simp only [Polynomial.coeff_zero] at hcoeff
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp (by linear_combination hcoeff))
  have hpC := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  -- Step 3: read off `b`'s coordinates.
  have h0 := hstar 0
  rw [hpC, coordOf_C, coordOf_zero, add_zero,
    show sPowCoord W 0 0 = 1 from rfl, one_mul] at h0
  have hb0 : (infChartBasis W).repr b 0 = Polynomial.C (p.coeff 0) :=
    ((mul_cancel_left_mem_nonZeroDivisors hXN).mp (by linear_combination h0)).symm
  have hb1 : (infChartBasis W).repr b 1 = 0 := by
    have h1' := hstar 1
    rw [hpC, coordOf_C, coordOf_zero, add_zero,
      show sPowCoord W 0 1 = 0 from rfl, zero_mul, mul_zero] at h1'
    exact (mul_cancel_left_mem_nonZeroDivisors hXN).mp (by linear_combination -h1')
  have hb2 : (infChartBasis W).repr b 2 = 0 := by
    have h2' := hstar 2
    rw [hpC, coordOf_C, coordOf_zero, add_zero,
      show sPowCoord W 0 2 = 0 from rfl, zero_mul, mul_zero] at h2'
    exact (mul_cancel_left_mem_nonZeroDivisors hXN).mp (by linear_combination -h2')
  refine ⟨p.coeff 0, ?_, ?_⟩
  · conv_lhs => rw [zero_smul, add_zero, hpC]
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, ← Algebra.algebraMap_eq_smul_one]
  · have hbexp : b = algebraMap (Polynomial R) _ ((infChartBasis W).repr b 0) +
        algebraMap (Polynomial R) _ ((infChartBasis W).repr b 1) *
          AdjoinRoot.root (infChartCubic W) +
        algebraMap (Polynomial R) _ ((infChartBasis W).repr b 2) *
          AdjoinRoot.root (infChartCubic W) ^ 2 := by
      conv_lhs => rw [← (infChartBasis W).sum_repr b]
      rw [Fin.sum_univ_three]
      simp only [infChartBasis_apply, Algebra.smul_def,
        show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_zero, pow_one, mul_one]
    rw [hbexp, hb0, hb1, hb2, map_zero, zero_mul, add_zero, zero_mul, add_zero,
      IsScalarTower.algebraMap_apply R (Polynomial R) (AdjoinRoot (infChartCubic W)),
      Polynomial.algebraMap_eq]

/-- The `Y`-chart ring as the infinity-chart `AdjoinRoot` (ring form). -/
private noncomputable def chartYRingEquiv (W : WeierstrassCurve R) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) ≃+*
      AdjoinRoot (infChartCubic W) :=
  (chartCoordEquiv W 1).symm.trans (infChartQuotEquiv W).toRingEquiv

/-- The `Z`-chart ring as mathlib's affine coordinate ring (ring form). -/
private noncomputable def chartZRingEquiv (W : WeierstrassCurve R) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≃+*
      W.toAffine.CoordinateRing :=
  (chartCoordEquiv W 2).symm.trans (chartZAffineEquiv W).toRingEquiv

private lemma chartYRingEquiv_isLocalizationElem (W : WeierstrassCurve R) :
    chartYRingEquiv W (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) =
    infChartTElem W := by
  unfold chartYRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 1).symm (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) =
      Ideal.Quotient.mk _ (MvPolynomial.X infChartT) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_X W 1 infChartT).symm
  rw [hkey]
  simp only [AlgEquiv.coe_ringEquiv]
  show Ideal.quotientEquivAlg _ _ (infChartPolyEquiv (R := R)) _
    (Ideal.Quotient.mk _ (MvPolynomial.X infChartT)) = _
  rw [Ideal.quotientEquivAlg_mk, infChartPolyEquiv_X_t]
  rfl

private lemma chartYRingEquiv_sElem (W : WeierstrassCurve R) :
    chartYRingEquiv W (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 0)) =
    AdjoinRoot.root (infChartCubic W) := by
  unfold chartYRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 1).symm (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 0)) =
      Ideal.Quotient.mk _ (MvPolynomial.X infChartS) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_X W 1 infChartS).symm
  rw [hkey]
  simp only [AlgEquiv.coe_ringEquiv]
  show Ideal.quotientEquivAlg _ _ (infChartPolyEquiv (R := R)) _
    (Ideal.Quotient.mk _ (MvPolynomial.X infChartS)) = _
  rw [Ideal.quotientEquivAlg_mk, infChartPolyEquiv_X_s]
  rfl

private lemma chartYRingEquiv_fromZero (W : WeierstrassCurve R) (r : R) :
    chartYRingEquiv W ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      ((algebraMapGradeZero (projIdeal W)) r)) =
    algebraMap R (AdjoinRoot (infChartCubic W)) r := by
  unfold chartYRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 1).symm ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))
      ((algebraMapGradeZero (projIdeal W)) r)) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_C W 1 r).symm
  rw [hkey]
  have : (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 1
      W.toProjective.polynomial}) (MvPolynomial.C r)) =
      algebraMap R _ r := rfl
  rw [this]
  exact (infChartQuotEquiv W).commutes r

private lemma chartZRingEquiv_x (W : WeierstrassCurve R) :
    chartZRingEquiv W (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) =
    coordX W := by
  unfold chartZRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 2).symm (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) =
      Ideal.Quotient.mk _ (MvPolynomial.X affChartX) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_X W 2 affChartX).symm
  rw [hkey]
  simp only [AlgEquiv.coe_ringEquiv]
  show Ideal.quotientEquivAlg _ _ (affChartPolyEquiv (R := R)) _
    (Ideal.Quotient.mk _ (MvPolynomial.X affChartX)) = _
  rw [Ideal.quotientEquivAlg_mk, affChartPolyEquiv_X_x]
  rfl

private lemma chartZRingEquiv_y (W : WeierstrassCurve R) :
    chartZRingEquiv W (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) =
    coordY W := by
  unfold chartZRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 2).symm (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) =
      Ideal.Quotient.mk _ (MvPolynomial.X affChartY) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_X W 2 affChartY).symm
  rw [hkey]
  simp only [AlgEquiv.coe_ringEquiv]
  show Ideal.quotientEquivAlg _ _ (affChartPolyEquiv (R := R)) _
    (Ideal.Quotient.mk _ (MvPolynomial.X affChartY)) = _
  rw [Ideal.quotientEquivAlg_mk, affChartPolyEquiv_X_y]
  rfl

private lemma chartZRingEquiv_fromZero (W : WeierstrassCurve R) (r : R) :
    chartZRingEquiv W ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      ((algebraMapGradeZero (projIdeal W)) r)) =
    algebraMap R W.toAffine.CoordinateRing r := by
  unfold chartZRingEquiv
  rw [RingEquiv.trans_apply]
  have hkey : (chartCoordEquiv W 2).symm ((HomogeneousLocalization.fromZeroRingHom
      (quotientGrading (projIdeal W)) (Submonoid.powers
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      ((algebraMapGradeZero (projIdeal W)) r)) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) := by
    rw [RingEquiv.symm_apply_eq]
    exact (chartCoordEquiv_mk_C W 2 r).symm
  rw [hkey]
  have : (Ideal.Quotient.mk (Ideal.span {MvPolynomial.dehomogenizeAux R 2
      W.toProjective.polynomial}) (MvPolynomial.C r)) =
      algebraMap R _ r := rfl
  rw [this]
  exact (chartZAffineEquiv W).commutes r

/-- **(the overlap transport)** The overlap chart ring `(A_{x₁x₂})₀` as the localization of
the infinity chart at `t`: transport of `Away.isLocalization_mul` along `chartYRingEquiv`. -/
private noncomputable def overlapLocEquiv (W : WeierstrassCurve R) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≃+*
      Localization.Away (infChartTElem W) :=
  letI := (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _)).toAlgebra
  haveI := HomogeneousLocalization.Away.isLocalization_mul
    (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _) one_ne_zero
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)))
    (T := Submonoid.powers (infChartTElem W)) _ _
    (chartYRingEquiv W)
    (by
      rw [Submonoid.map_powers]
      rw [show (chartYRingEquiv W).toMonoidHom
          (HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) =
        chartYRingEquiv W (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) from rfl]
      rw [chartYRingEquiv_isLocalizationElem])

/-- Transport compatibility on the `Y`-chart side: `ℓ ∘ α₁ = algebraMap ∘ chartYRingEquiv`. -/
private lemma overlapLocEquiv_awayMap_y (W : WeierstrassCurve R) (z :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) :
    overlapLocEquiv W ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 2)
      (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _)) z) =
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
      (chartYRingEquiv W z) := by
  letI := (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _)).toAlgebra
  haveI := HomogeneousLocalization.Away.isLocalization_mul
    (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)
    (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _) one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

/-- `x`-fraction relation in the overlap chart: `α₂(x-frac)·α₁(t-frac) = α₁(s-frac)`. -/
private lemma awayMap_x_mul_t (W : WeierstrassCurve R) :
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 1)
        (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0)) *
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 2)
        (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) =
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 2)
        (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 0)) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- `y`-fraction relation in the overlap chart: `α₂(y-frac)·α₁(t-frac) = 1`. -/
private lemma awayMap_y_mul_t (W : WeierstrassCurve R) :
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 1)
        (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1)) *
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 2)
        (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 1) (mk_X_mem_quotientGrading_one W 2)) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    HomogeneousLocalization.val_one]
  rw [show (1 : Localization (Submonoid.powers
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) =
    Localization.mk 1 1 from Localization.mk_one.symm]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- Generator value: the `x`-fraction of the `Z`-chart maps to `s/t` in the overlap. -/
private lemma overlapLocEquiv_x_frac (W : WeierstrassCurve R) :
    overlapLocEquiv W ((HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0))) =
    overlapXElem W := by
  have hu : IsUnit (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) :=
    IsLocalization.map_units _
      (⟨infChartTElem W, ⟨1, pow_one _⟩⟩ : Submonoid.powers (infChartTElem W))
  have h := congrArg (overlapLocEquiv W) (awayMap_x_mul_t W)
  rw [map_mul, overlapLocEquiv_awayMap_y, overlapLocEquiv_awayMap_y,
    chartYRingEquiv_isLocalizationElem, chartYRingEquiv_sElem] at h
  refine hu.mul_right_cancel ?_
  rw [h, ← tel_mul_overlapXElem W]
  ring

/-- Generator value: the `y`-fraction of the `Z`-chart maps to `1/t` in the overlap. -/
private lemma overlapLocEquiv_y_frac (W : WeierstrassCurve R) :
    overlapLocEquiv W ((HomogeneousLocalization.awayMap
      (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1))) =
    overlapInvT W := by
  have hu : IsUnit (algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W)) (infChartTElem W)) :=
    IsLocalization.map_units _
      (⟨infChartTElem W, ⟨1, pow_one _⟩⟩ : Submonoid.powers (infChartTElem W))
  have h := congrArg (overlapLocEquiv W) (awayMap_y_mul_t W)
  rw [map_mul, map_one, overlapLocEquiv_awayMap_y,
    chartYRingEquiv_isLocalizationElem] at h
  refine hu.mul_right_cancel ?_
  rw [h, ← tel_mul_overlapInvT W]
  ring

/-- `R`-compatibility of the left composite `ℓ ∘ α₂` on grade zero. -/
private lemma overlapLocEquiv_awayMap_gradeZero (W : WeierstrassCurve R) (r : R) :
    overlapLocEquiv W ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      ((HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r))) =
    algebraMap R (Localization.Away (infChartTElem W)) r := by
  rw [HomogeneousLocalization.awayMap_fromZeroRingHom]
  rw [show (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
      (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      ((algebraMapGradeZero (projIdeal W)) r) =
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 2)
      (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      ((HomogeneousLocalization.fromZeroRingHom _ _)
        ((algebraMapGradeZero (projIdeal W)) r)) from
    (HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _).symm]
  rw [overlapLocEquiv_awayMap_y, chartYRingEquiv_fromZero]
  exact (IsScalarTower.algebraMap_apply R (AdjoinRoot (infChartCubic W)) _ r).symm

/-- `R`-compatibility of the right composite `overlapMap ∘ chartZRingEquiv` on grade zero. -/
private lemma overlapMap_chartZRingEquiv_gradeZero (W : WeierstrassCurve R) (r : R) :
    overlapMap W (chartZRingEquiv W
      ((HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r))) =
    algebraMap R (Localization.Away (infChartTElem W)) r := by
  rw [chartZRingEquiv_fromZero]
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) W.toAffine.CoordinateRing r]
  rw [show algebraMap (Polynomial R) W.toAffine.CoordinateRing =
    AdjoinRoot.of W.toAffine.polynomial from rfl]
  unfold overlapMap
  rw [AdjoinRoot.lift_of]
  rw [show (Polynomial.eval₂RingHom ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))).comp
      ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C))
      (overlapXElem W)) (algebraMap R (Polynomial R) r) =
    Polynomial.eval₂ ((algebraMap (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))).comp
      ((algebraMap (Polynomial R) (AdjoinRoot (infChartCubic W))).comp Polynomial.C))
      (overlapXElem W) (Polynomial.C r) from by rw [Polynomial.algebraMap_eq]; rfl]
  rw [Polynomial.eval₂_C]
  show algebraMap (AdjoinRoot (infChartCubic W)) _
    (algebraMap (Polynomial R) _ (Polynomial.C r)) = _
  rw [← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply R (Polynomial R) (AdjoinRoot (infChartCubic W)),
    ← IsScalarTower.algebraMap_apply R (AdjoinRoot (infChartCubic W))]

/-- Transport compatibility on the `Z`-chart side: `ℓ ∘ α₂ = overlapMap ∘ chartZRingEquiv`. -/
private lemma overlapLocEquiv_awayMap_z (W : WeierstrassCurve R)
    (w : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
    overlapLocEquiv W ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) w) =
    overlapMap W (chartZRingEquiv W w) := by
  have hφ₁ : (((overlapLocEquiv W) : _ →+* _).comp
      ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W 1)
        (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R (Localization.Away (infChartTElem W)) :=
    RingHom.ext fun r => overlapLocEquiv_awayMap_gradeZero W r
  have hφ₂ : ((overlapMap W).comp
      ((chartZRingEquiv W) : _ →+* W.toAffine.CoordinateRing)).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R (Localization.Away (infChartTElem W)) :=
    RingHom.ext fun r => overlapMap_chartZRingEquiv_gradeZero W r
  obtain ⟨q, rfl⟩ := (chartCoordEquiv W 2).surjective w
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h₁ := chart_hom_aeval (K := Localization.Away (infChartTElem W)) W 2
    (((overlapLocEquiv W) : _ →+* _).comp
    ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))) hφ₁ p
  have h₂ := chart_hom_aeval (K := Localization.Away (infChartTElem W)) W 2
    ((overlapMap W).comp
    ((chartZRingEquiv W) : _ →+* W.toAffine.CoordinateRing)) hφ₂ p
  show (((overlapLocEquiv W) : _ →+* _).comp
    ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))))
    ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ p)) =
    ((overlapMap W).comp ((chartZRingEquiv W) : _ →+* W.toAffine.CoordinateRing))
    ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ p))
  rw [h₁, h₂]
  congr 1
  congr 1
  funext j
  obtain ⟨jv, hj⟩ := j
  obtain rfl | rfl | rfl : jv = 0 ∨ jv = 1 ∨ jv = 2 := by omega
  · show overlapLocEquiv W ((HomogeneousLocalization.awayMap _ _ _)
      ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ (MvPolynomial.X affChartX)))) =
      overlapMap W (chartZRingEquiv W
        ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ (MvPolynomial.X affChartX))))
    rw [chartCoordEquiv_mk_X W 2 affChartX, overlapLocEquiv_x_frac,
      chartZRingEquiv_x, overlapMap_coordX]
  · show overlapLocEquiv W ((HomogeneousLocalization.awayMap _ _ _)
      ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ (MvPolynomial.X affChartY)))) =
      overlapMap W (chartZRingEquiv W
        ((chartCoordEquiv W 2) (Ideal.Quotient.mk _ (MvPolynomial.X affChartY))))
    rw [chartCoordEquiv_mk_X W 2 affChartY, overlapLocEquiv_y_frac,
      chartZRingEquiv_y, overlapMap_coordY]
  · exact absurd rfl hj


private lemma algebraMap_adjoinRoot_injective (W : WeierstrassCurve R) [Nontrivial R] :
    Function.Injective (algebraMap R (AdjoinRoot (infChartCubic W))) := by
  intro r r' h
  have h0 : algebraMap R (AdjoinRoot (infChartCubic W)) (r - r') = 0 := by
    rw [map_sub, h, sub_self]
  have hsmul : (Polynomial.C (r - r') : Polynomial R) • (1 : AdjoinRoot (infChartCubic W)) =
      0 := by
    rw [Algebra.smul_def, mul_one, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
    exact h0
  have hrepr := congrArg (fun z => ((infChartBasis W).repr z) 0) hsmul
  simp only [map_smul, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply,
    smul_eq_mul] at hrepr
  have h1 : (infChartBasis W).repr 1 0 = 1 := by
    have hb : (1 : AdjoinRoot (infChartCubic W)) = infChartBasis W 0 := by
      rw [infChartBasis_apply]
      simp
    rw [hb, Module.Basis.repr_self]
    simp
  rw [h1, mul_one] at hrepr
  have := Polynomial.C_eq_zero.mp hrepr
  exact sub_eq_zero.mp this

/-- Two global sections agreeing on the two covering charts are equal. -/
private lemma sections_ext (W : WeierstrassCurve R) (s t : Γ(projModel W, ⊤))
    (h₁ : ((projModel W).presheaf.map (homOfLE (le_top (a := Proj.basicOpen
        (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))))).op).hom s =
      ((projModel W).presheaf.map (homOfLE le_top).op).hom t)
    (h₂ : ((projModel W).presheaf.map (homOfLE (le_top (a := Proj.basicOpen
        (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))).op).hom s =
      ((projModel W).presheaf.map (homOfLE le_top).op).hom t) : s = t := by
  refine (projModel W).sheaf.eq_of_locally_eq₂
    (homOfLE (le_top : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) ≤ ⊤))
    (homOfLE (le_top : Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≤ ⊤))
    (basicOpen_X1_sup_basicOpen_X2_eq_top W).ge s t ?_ ?_
  · exact h₁
  · exact h₂


/-- Elementwise structure square: the value of the canonical composite on `r`. -/
private lemma structure_section_square_apply (W : WeierstrassCurve R) {m : ℕ}
    (F : MvPolynomial (Fin 3) R ⧸ (projIdeal W).toIdeal)
    (F_deg : F ∈ quotientGrading (projIdeal W) m) (hm : 0 < m) (r : R) :
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W)) F F_deg hm).inv).hom
      (((projModel W).presheaf.map (homOfLE le_top).op).hom
        (((projModelπ W).appTop).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r))) =
    (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
      (Submonoid.powers F)) ((algebraMapGradeZero (projIdeal W)) r) := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ r)
    (structure_section_square W F F_deg hm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h

/-- Elementwise `awayMap`-restriction square, chart-`1` side. -/
private lemma awayIso_res_squareY (W : WeierstrassCurve R)
    (u : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) :
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W 1)
          (mk_X_mem_quotientGrading_one W 2)) (by omega)).inv).hom
      (((projModel W).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _
        ⟨_, rfl⟩)).op).hom u) =
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 2)
      (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos).inv).hom u) := by
  have hsq := Proj.awayMap_awayToSection (𝒜 := quotientGrading (projIdeal W))
    (f := (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
    (g_deg := mk_X_mem_quotientGrading_one W 2)
    (hx := rfl)
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ
    (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos).inv).hom u)) hsq
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hcancel : (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))).hom
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos).inv).hom u) = u := by
    have := congrArg (fun φ => CommRingCat.Hom.hom φ u)
      ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos).inv_hom_id)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at this
    exact this
  rw [hcancel] at h
  rw [← h]
  have := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 2)
      (rfl : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) = _))
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos).inv).hom u)))
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W 1)
        (mk_X_mem_quotientGrading_one W 2)) (by omega)).hom_inv_id)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  exact this

/-- Elementwise `awayMap`-restriction square, chart-`2` side. -/
private lemma awayIso_res_squareZ (W : WeierstrassCurve R)
    (u : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) :
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
          (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W 1)
          (mk_X_mem_quotientGrading_one W 2)) (by omega)).inv).hom
      (((projModel W).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _
        ⟨_, mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))⟩)).op).hom u) =
    (HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv).hom u) := by
  have hsq := Proj.awayMap_awayToSection (𝒜 := quotientGrading (projIdeal W))
    (f := (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (g_deg := mk_X_mem_quotientGrading_one W 1)
    (hx := mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ
    (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).inv).hom u)) hsq
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hcancel : (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv).hom u) = u := by
    have := congrArg (fun φ => CommRingCat.Hom.hom φ u)
      ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv_hom_id)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at this
    exact this
  rw [hcancel] at h
  rw [← h]
  have := congrArg (fun φ => CommRingCat.Hom.hom φ
    ((HomogeneousLocalization.awayMap (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 1)
      (mul_comm ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
      (((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv).hom u)))
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) *
        (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W 1)
        (mk_X_mem_quotientGrading_one W 2)) (by omega)).hom_inv_id)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  exact this

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
