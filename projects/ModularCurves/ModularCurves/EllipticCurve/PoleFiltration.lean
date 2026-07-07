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

/-! ### T-W7.0i-b1: the infinity chart as a monic cubic over `R[t]` -/

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

/-! ### T-W7.0i-b2: basis and nonzerodivisors of the infinity chart -/

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
