/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodMap
import LeanModularForms.Modularforms.PeterssonLevelN
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Γ-invariance of the period pairing (ES-3b-inv)

This file discharges the `Γ₁(N)`-invariance hypothesis `IsPeriodInvariant` of `PeriodMap.lean`,
making the period map `periodMap` unconditional.  Mathematically this is the contour-deformation /
path-independence statement (Shimura §8.2): the period pairing of a cusp form against a divisor of
degree `0` is unchanged under the simultaneous `γ`-action on the cusps and the `symRep`-action on
the polynomial coefficient.
-/

noncomputable section

/-! ## A primitive of a holomorphic function on the upper half-plane (reusable)

A holomorphic function on a *ball* has a primitive (Morera, `DifferentiableOn.isExactOn_ball`).  We
upgrade this to the open upper half-plane `{0 < im}` (which is convex but not a ball) by exhausting
it with the increasing family of balls `ball (n·i) n` (`n ≥ 1`): the normalized primitives on these
balls agree on the connected overlaps (their difference has zero derivative on a connected open
set),
so they glue to a global primitive.  Applied to `periodForm f P`, this makes the period integral of
the holomorphic form path-independent via the fundamental theorem of calculus, and is reused by
ES-3c/ES-4. -/

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every point of the ball `ball (n·i) n` has positive imaginary part. -/
theorem im_pos_mem_ball_nI (n : ℕ) {z : ℂ} (hz : z ∈ Metric.ball ((n : ℂ) * Complex.I) n) :
    0 < z.im := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im] at hz
  have hre : ((n : ℂ) * Complex.I).re = 0 := by simp
  have him : ((n : ℂ) * Complex.I).im = n := by simp
  rw [hre, him, sub_zero] at hz
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsq : z.re ^ 2 + (z.im - n) ^ 2 < n ^ 2 := by
    by_cases hnz : (0 : ℝ) < n
    · rw [Real.sqrt_lt' hnz] at hz; exact hz
    · have : (n : ℝ) = 0 := le_antisymm (not_lt.mp hnz) hn0
      rw [this] at hz; simp at hz
      exact absurd hz (not_lt_of_ge (Real.sqrt_nonneg _))
  nlinarith [sq_nonneg z.re]

/-- The center `i` lies in `ball (n·i) n` for `n ≥ 1`. -/
theorem mem_ball_nI_center (n : ℕ) (hn : 1 ≤ n) :
    (Complex.I) ∈ Metric.ball ((n : ℂ) * Complex.I) n := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  have hre : (Complex.I.re - ((n : ℂ) * Complex.I).re) = 0 := by simp
  have him : (Complex.I.im - ((n : ℂ) * Complex.I).im) = 1 - n := by simp
  rw [hre, him]
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith

/-- The exhausting balls are nested: `ball (m·i) m ⊆ ball (n·i) n` for `1 ≤ m ≤ n`. -/
theorem ball_nI_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Metric.ball ((m : ℂ) * Complex.I) m ⊆ Metric.ball ((n : ℂ) * Complex.I) n := by
  intro z hz
  rw [Metric.mem_ball, Complex.dist_eq_re_im] at hz ⊢
  have hmre : ((m : ℂ) * Complex.I).re = 0 := by simp
  have hmim : ((m : ℂ) * Complex.I).im = m := by simp
  have hnre : ((n : ℂ) * Complex.I).re = 0 := by simp
  have hnim : ((n : ℂ) * Complex.I).im = n := by simp
  rw [hmre, hmim, sub_zero] at hz
  rw [hnre, hnim, sub_zero]
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : z.re ^ 2 + (z.im - m) ^ 2 < m ^ 2 := by
    rw [Real.sqrt_lt' (by linarith)] at hz; exact hz
  have him0 : 0 < z.im := by nlinarith [sq_nonneg z.re]
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith [sq_nonneg z.re]

/-- **Primitive on the upper half-plane.**  A function holomorphic on the open upper half-plane has
a primitive there.  Proof: the upper half-plane is exhausted by the increasing balls `ball (n·i) n`;
each carries a primitive (`DifferentiableOn.isExactOn_ball`) normalized at `i`, and these agree on
the connected overlaps, hence glue to a global primitive. -/
theorem isExactOn_upperHalf {g : ℂ → E} [CompleteSpace E]
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) :
    ∃ F : ℂ → E, ∀ z : ℂ, 0 < z.im → HasDerivAt F (g z) z := by
  set B : ℕ → Set ℂ := fun n => Metric.ball ((n : ℂ) * Complex.I) n with hB
  have hBopen : ∀ n, IsOpen (B n) := fun n => Metric.isOpen_ball
  have hBsub : ∀ n, B n ⊆ {z : ℂ | 0 < z.im} := fun n _ hz => im_pos_mem_ball_nI n hz
  have hex : ∀ n : ℕ, ∃ F : ℂ → E, F Complex.I = 0 ∧ ∀ z ∈ B n, HasDerivAt F (g z) z := by
    intro n
    have hball : DifferentiableOn ℂ g (B n) := hg.mono (hBsub n)
    obtain ⟨F, hFI, hF⟩ := (hball.isExactOn_ball).with_val_at Complex.I 0
    exact ⟨F, hFI, hF⟩
  choose F hFI hF using hex
  have hagree : ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ z ∈ B m, ∀ _ : z ∈ B n, F m z = F n z := by
    have key : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → ∀ z ∈ B m, F m z = F n z := by
      intro m n hm hmn z hz
      have hsubset := ball_nI_mono hm hmn
      refine IsOpen.eqOn_of_deriv_eq (x := Complex.I) (hBopen m)
        ((convex_ball ((m : ℂ) * Complex.I) m).isPreconnected)
        (fun w hw => (hF m w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hF n w (hsubset hw)).differentiableAt.differentiableWithinAt)
        (fun w hw => by rw [(hF m w hw).deriv, (hF n w (hsubset hw)).deriv]) ?_ ?_ hz
      · exact mem_ball_nI_center m hm
      · rw [hFI m, hFI n]
    intro m n hm hn z hzm hzn
    rcases le_total m n with h | h
    · exact key hm h z hzm
    · exact (key hn h z hzn).symm
  set Nz : ℂ → ℕ := fun z => max 1 (Classical.choose
    (exists_nat_gt ((z.re ^ 2 + z.im ^ 2) / (2 * z.im)))) with hNz
  have hNz1 : ∀ z, 1 ≤ Nz z := fun z => le_max_left _ _
  have hmemNz : ∀ z, 0 < z.im → z ∈ B (Nz z) := by
    intro z hz
    have hspec := Classical.choose_spec
      (exists_nat_gt ((z.re ^ 2 + z.im ^ 2) / (2 * z.im)))
    set n0 := Classical.choose (exists_nat_gt ((z.re ^ 2 + z.im ^ 2) / (2 * z.im))) with hn0
    have hzB : z ∈ B n0 := by
      rw [hB]; rw [Metric.mem_ball, Complex.dist_eq_re_im]
      have hre : (z.re - ((n0 : ℂ) * Complex.I).re) = z.re := by simp
      have him : (z.im - ((n0 : ℂ) * Complex.I).im) = z.im - n0 := by simp
      rw [hre, him]
      have h2 : z.re ^ 2 + z.im ^ 2 < 2 * z.im * n0 := by
        rw [div_lt_iff₀ (by positivity)] at hspec; linarith
      rw [Real.sqrt_lt' (by
        rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ n0) with h | h
        · exfalso; rw [← h] at h2; nlinarith [sq_nonneg z.re, hz]
        · exact h)]
      nlinarith
    rcases Nat.eq_zero_or_pos n0 with h1 | h1
    · rw [h1] at hzB
      simp only [hB, Nat.cast_zero, zero_mul, Metric.ball_zero, Set.mem_empty_iff_false] at hzB
    · exact ball_nI_mono h1 (le_max_right _ _) hzB
  refine ⟨fun z => F (Nz z) z, fun z hz => ?_⟩
  have hmem := hmemNz z hz
  have hderiv : HasDerivAt (F (Nz z)) (g z) z := hF (Nz z) z hmem
  apply hderiv.congr_of_eventuallyEq
  have hball_nhds : B (Nz z) ∈ nhds z := (hBopen (Nz z)).mem_nhds hmem
  filter_upwards [hball_nhds] with w hw
  have hwim : 0 < w.im := im_pos_mem_ball_nI (Nz z) hw
  have hwmem : w ∈ B (Nz w) := hmemNz w hwim
  exact hagree (hNz1 w) (hNz1 z) w hwmem hw

end Complex

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise TensorProduct Interval OnePoint
open UpperHalfPlane Complex MeasureTheory Filter Asymptotics CongruenceSubgroup
  Matrix.SpecialLinearGroup MvPolynomial ConjAct

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## Compatibility of the integral cast with `symRep` -/

/-- `substAlgHom` commutes with the entrywise ring-map cast on coefficients: substituting by the
cast matrix after mapping equals mapping after substituting. -/
theorem map_substAlgHom_intCast (g : SL(2, ℤ)) (p : MvPolynomial (Fin 2) ℤ) :
    substAlgHom (symMat ℂ g) (MvPolynomial.map (Int.castRingHom ℂ) p) =
      MvPolynomial.map (Int.castRingHom ℂ) (substAlgHom (symMat ℤ g) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [substAlgHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, substAlgHom_X, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    simp [symMat, Matrix.map_apply]

/-- The integral cast `castSymPow` intertwines the integral and complex `symRep` actions:
`castSymPow (symRep_ℤ g P) = symRep_ℂ g (castSymPow P)`. -/
theorem castSymPow_symRep {m : ℕ} (g : SL(2, ℤ)) (P : SymPow ℤ m) :
    castSymPow m (symRep ℤ m g P) = symRep ℂ m g (castSymPow m P) := by
  apply Subtype.ext
  rw [symRep_apply]
  show MvPolynomial.map (Int.castRingHom ℂ) ((symRep ℤ m g P : SymPow ℤ m) :
    MvPolynomial (Fin 2) ℤ) = _
  rw [symRep_apply]
  exact (map_substAlgHom_intCast g (P : MvPolynomial (Fin 2) ℤ)).symm

/-! ## The action on cusps and the cusp-difference function -/

/-- The action of `γ : Gamma1 N` on a projective cusp `c`, via `SL(2,ℤ) → SL(2,ℚ)`. -/
abbrev cuspAction (γ : CongruenceSubgroup.Gamma1 N)
    (c : Projectivization ℚ (Fin 2 → ℚ)) : Projectivization ℚ (Fin 2 → ℚ) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) (γ : SL(2, ℤ))) • c

/-- The cusp-difference function `G(c)` whose `c`-independence is the heart of the invariance:
`G(c) = cuspValue f (symRep γ P)(γ • c) − cuspValue f P (c)`. -/
def cuspDiff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (γ : CongruenceSubgroup.Gamma1 N)
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) : ℂ :=
  cuspValue f (symRep ℂ m (γ : SL(2, ℤ)) P) (cuspAction γ c) - cuspValue f P c

/-- **Reduction step.**  On a generator `D ⊗ P` of `Div⁰ ⊗ Sym`, the invariance
`rawPairing f (modSymRep γ (D ⊗ P)) = rawPairing f (D ⊗ P)` is exactly the statement that the
`c`-weighted sum of `cuspDiff` against the degree-`0` divisor `D` vanishes. -/
theorem rawPairing_modSymRep_sub (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (γ : CongruenceSubgroup.Gamma1 N) (D : Div0 ℤ) (P : SymPow ℤ m) :
    rawPairing f (modSymRep N m γ (D ⊗ₜ P)) - rawPairing f (D ⊗ₜ P) =
      (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.sum
        (fun c n => (n : ℂ) * cuspDiff f γ (castSymPow m P) c) := by
  have h1 : modSymRep N m γ (D ⊗ₜ[ℤ] P) =
      (div0Rep ℤ (γ : SL(2, ℤ)) D) ⊗ₜ[ℤ] (symRep ℤ m (γ : SL(2, ℤ)) P) := rfl
  rw [h1, rawPairing_tmul, rawPairing_tmul]
  -- Expand `rawBilin` as a `Finsupp.sum` against `cuspValue`.
  have hrb : ∀ (D' : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P' : SymPow ℤ m),
      rawBilin f D' P' = D'.sum (fun c n => (n : ℂ) * cuspValue f (castSymPow m P') c) := by
    intro D' P'
    simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.smul_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      zsmul_eq_mul]
  rw [hrb, hrb, castSymPow_symRep]
  -- The divisor of `div0Rep γ D` is `mapDomain (γ • ·) D`, reindex the sum injectively.
  set g := Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) (γ : SL(2, ℤ)) with hg
  have hdiv : ((div0Rep ℤ (γ : SL(2, ℤ)) D) :
        MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff =
      Finsupp.mapDomain (g • ·)
        (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff := by
    rw [div0Rep_apply]
  have hinj : Function.Injective (fun c : Projectivization ℚ (Fin 2 → ℚ) => g • c) :=
    MulAction.injective g
  rw [hdiv, Finsupp.sum_mapDomain_index_inj hinj]
  -- Combine the two sums over the same support into a single sum of the difference.
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cuspDiff, cuspAction, ← hg, mul_sub]

/-- A degree-`0` divisor `D` has vanishing total weight `Σ_c D(c) = 0`. -/
theorem Div0.sum_coeff_eq_zero (D : Div0 ℤ) :
    (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.sum (fun _ n => n) = 0 := by
  have hD := D.2
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply, Finsupp.sum] at hD
  simp only [smul_eq_mul, mul_one] at hD
  rwa [Finsupp.sum]

/-- **The degree-`0` cancellation.**  If the cusp-difference `cuspDiff f γ Q` is independent of the
cusp (constant in `c`), then its `D`-weighted sum vanishes for any degree-`0` divisor `D`, because
the constant pulls out of the degree-`0` sum.  This is the algebraic step turning `c`-independence
into the modular-symbol invariance. -/
theorem sum_cuspDiff_eq_zero_of_const (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (γ : CongruenceSubgroup.Gamma1 N) (Q : SymPow ℂ m) (D : Div0 ℤ)
    (hconst : ∀ c₁ c₂ : Projectivization ℚ (Fin 2 → ℚ),
      cuspDiff f γ Q c₁ = cuspDiff f γ Q c₂) :
    (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.sum
      (fun c n => (n : ℂ) * cuspDiff f γ Q c) = 0 := by
  by_cases hsupp : (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support = ∅
  · simp [Finsupp.sum, hsupp]
  · obtain ⟨c₀, hc₀⟩ := Finset.nonempty_of_ne_empty hsupp
    have hconst' : ∀ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        (fun c n => (n : ℂ) * cuspDiff f γ Q c) c
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c) =
        (fun c n => (n : ℂ) * cuspDiff f γ Q c₀) c
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c) := by
      intro c _; simp only []; rw [hconst c c₀]
    rw [Finsupp.sum, Finset.sum_congr rfl hconst']
    have : ∑ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ) * cuspDiff f γ Q c₀ =
        (∑ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
          ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ)) *
        cuspDiff f γ Q c₀ := by
      rw [Finset.sum_mul]
    rw [this]
    have hsum0 : (∑ c ∈ (D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff.support,
        ((D : MonoidAlgebra ℤ (Projectivization ℚ (Fin 2 → ℚ))).coeff c : ℂ)) = 0 := by
      rw [← Int.cast_sum]
      have := Div0.sum_coeff_eq_zero D
      rw [Finsupp.sum] at this
      rw [this, Int.cast_zero]
    rw [hsum0, zero_mul]

/-! ## The contour-deformation engine (reusable)

We build the reusable analytic engine for path-independence of the holomorphic period form on `ℍ`.
The integrand, as a function `ℂ → ℂ`, is `periodForm f P := (f ∘ ofComplex)(z) · evalSym1 P z`,
holomorphic on the open upper half-plane `{z | 0 < z.im}`.  Cauchy's theorem on a rectangle
(`integral_boundary_rect_eq_zero_of_differentiableOn`) then relates the integral up two vertical
segments to the integrals along the connecting horizontal segments; letting the top of the rectangle
tend to `i∞` and using cusp decay kills the top cap, giving the horizontal-slide path-independence.
These lemmas are reused by ES-3c/ES-4. -/

/-- The period integrand as a function on `ℂ` (rather than `ℍ`): `z ↦ f(z) · evalSym1 P z`, where
`f` is extended off `ℍ` by `ofComplex`.  Holomorphic on `{0 < im}` (`differentiableOn_periodForm`).
-/
def periodForm {F : Type*} [FunLike F ℍ ℂ] (f : F) {m : ℕ} (P : SymPow ℂ m) : ℂ → ℂ :=
  fun z => (f (UpperHalfPlane.ofComplex z)) * evalSym1 m P z

omit [NeZero N] in
/-- On the open upper half-plane, `periodForm f P` agrees with `f` evaluated at the genuine point of
`ℍ` times `evalSym1 P`. -/
theorem periodForm_apply_of_im_pos {F : Type*} [FunLike F ℍ ℂ] (f : F) {m : ℕ} (P : SymPow ℂ m)
    {z : ℂ} (hz : 0 < z.im) :
    periodForm f P z = f ⟨z, hz⟩ * evalSym1 m P z := by
  rw [periodForm, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- **Holomorphy of the period form.**  For a modular form `f` (any class), `periodForm f P` is
complex-differentiable on the open upper half-plane `{z | 0 < z.im}`. -/
theorem differentiableOn_periodForm {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [ModularFormClass F Γ k] (f : F) {m : ℕ} (P : SymPow ℂ m) :
    DifferentiableOn ℂ (periodForm f P) {z : ℂ | 0 < z.im} := by
  have hf : DifferentiableOn ℂ (⇑f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp (ModularFormClass.holo f)
  have hP : DifferentiableOn ℂ (evalSym1 m P) {z : ℂ | 0 < z.im} :=
    (differentiable_evalSym1 m P).differentiableOn
  exact hf.mul hP

/-- **Rectangle Cauchy identity for vertical segments.**  For `G` holomorphic on the open upper
half-plane and a rectangle `[a,b] × [Y₀,Y₁]` with `0 < Y₀ ≤ Y₁` and `a ≤ b`, the integral of `G` up
the left vertical edge equals the integral up the right vertical edge plus the bottom horizontal cap
minus the top horizontal cap.  This is the reusable core of contour deformation. -/
theorem vertical_segment_cauchy (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im})
    {a b Y₀ Y₁ : ℝ} (_hab : a ≤ b) (hY : Y₀ ≤ Y₁) (hY₀ : 0 < Y₀) :
    (Complex.I * ∫ y in Y₀..Y₁, G (a + y * Complex.I)) =
      (Complex.I * ∫ y in Y₀..Y₁, G (b + y * Complex.I)) +
        ((∫ x in a..b, G (x + Y₀ * Complex.I)) - ∫ x in a..b, G (x + Y₁ * Complex.I)) := by
  set z : ℂ := a + Y₀ * Complex.I with hz
  set w : ℂ := b + Y₁ * Complex.I with hw
  have hzre : z.re = a := by simp [hz]
  have hzim : z.im = Y₀ := by simp [hz]
  have hwre : w.re = b := by simp [hw]
  have hwim : w.im = Y₁ := by simp [hw]
  have hrect : ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ {z : ℂ | 0 < z.im} := by
    intro p hp
    rw [Complex.mem_reProdIm] at hp
    rw [Set.mem_setOf_eq]
    rw [hzim, hwim] at hp
    have : Y₀ ≤ p.im := (Set.uIcc_of_le hY ▸ hp.2).1
    linarith
  have hd : DifferentiableOn ℂ G ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := hG.mono hrect
  have hcauchy := integral_boundary_rect_eq_zero_of_differentiableOn G z w hd
  rw [hzre, hzim, hwre, hwim] at hcauchy
  -- Rearrange the rectangle identity.
  simp only [smul_eq_mul] at hcauchy
  linear_combination -hcauchy

/-- **Uniform exponential decay of the period form on a horizontal strip top.**  For a cusp form,
`‖periodForm f P (x + y·i)‖` is bounded by `C·(max 1 √(M²+y²))^D · exp(-c·y)` for `y` large and
`x ∈ [-M, M]`, uniformly in `x`.  (Cusp decay beats polynomial growth.) -/
theorem periodForm_norm_le {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ} (P : SymPow ℂ m) :
    ∃ (c : ℝ), 0 < c ∧ ∃ (C A : ℝ), ∀ (x y : ℝ), A ≤ y →
      ‖periodForm f P (x + y * Complex.I)‖ ≤
        C * (max 1 ‖(x : ℂ) + y * Complex.I‖) ^ (P : MvPolynomial (Fin 2) ℂ).totalDegree *
          Real.exp (-c * y) := by
  obtain ⟨c, hc, C, A, hbound⟩ := exists_exp_decay_bound f
  set K := ∑ d ∈ (P : MvPolynomial (Fin 2) ℂ).support,
    ‖(P : MvPolynomial (Fin 2) ℂ).coeff d‖ with hK
  set D := (P : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨c, hc, max C 0 * K, max A 1, fun x y hy => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_right A 1) hy
  have hyA : A ≤ y := le_trans (le_max_left A 1) hy
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hypos
  set z : ℍ := ⟨(x : ℂ) + y * Complex.I, him⟩ with hz
  have hzim : z.im = y := by show ((x : ℂ) + y * Complex.I).im = y; simp
  rw [periodForm_apply_of_im_pos f P him]
  rw [norm_mul]
  have hfb : ‖f z‖ ≤ max C 0 * Real.exp (-c * y) := by
    have := hbound z (by rw [hzim]; exact hyA)
    rw [hzim] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hPb : ‖evalSym1 m P ((x : ℂ) + y * Complex.I)‖ ≤
      K * (max 1 ‖(x : ℂ) + y * Complex.I‖) ^ D := by
    have h := norm_evalSym1_le m P ((x : ℂ) + y * Complex.I)
    rw [← hK, ← hD] at h
    exact h
  calc ‖f z‖ * ‖evalSym1 m P ((x : ℂ) + y * Complex.I)‖
      ≤ (max C 0 * Real.exp (-c * y)) * (K * (max 1 ‖(x : ℂ) + y * Complex.I‖) ^ D) :=
        mul_le_mul hfb hPb (norm_nonneg _) (by positivity)
    _ = max C 0 * K * (max 1 ‖(x : ℂ) + y * Complex.I‖) ^ D * Real.exp (-c * y) := by ring

/-- **The top horizontal cap vanishes at `i∞`.**  For a cusp form, the integral of `periodForm f P`
over the horizontal segment `[a, b]` at height `Y` tends to `0` as `Y → +∞`.  This is the
cap-vanishing limit that turns the rectangle Cauchy identity into path-independence to `i∞`. -/
theorem tendsto_horizontal_cap {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ} (P : SymPow ℂ m) (a b : ℝ) :
    Tendsto (fun Y : ℝ => ∫ x in a..b, periodForm f P (x + Y * Complex.I)) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, A, hbound⟩ := periodForm_norm_le f P
  set D := (P : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  set M := max |a| |b| with hM
  have hMnn : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
  -- The dominating function `g(Y) = |C|·(1+M+Y)^D·exp(-c·Y)` tends to `0`.
  set g : ℝ → ℝ := fun Y => |C| * (1 + M + Y) ^ D * Real.exp (-c * Y) with hg
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hbase : Tendsto (fun Y : ℝ => (1 + M + Y) ^ D * Real.exp (-c * (1 + M + Y)))
        atTop (𝓝 0) := by
      have hcomp := (tendsto_zpow_mul_exp_neg_atTop c hc (D : ℤ)).comp
        (tendsto_atTop_add_const_left atTop (1 + M) tendsto_id)
      refine hcomp.congr fun Y => ?_
      simp only [Function.comp_apply, zpow_natCast, id_eq]
    have hrw : ∀ Y : ℝ, g Y =
        (|C| * Real.exp (c * (1 + M))) * ((1 + M + Y) ^ D * Real.exp (-c * (1 + M + Y))) := by
      intro Y
      rw [hg, show -c * (1 + M + Y) = -(c * (1 + M)) + (-c * Y) by ring, Real.exp_add,
        Real.exp_neg]
      field_simp
    rw [show (0 : ℝ) = (|C| * Real.exp (c * (1 + M))) * 0 by ring]
    exact (hbase.const_mul (|C| * Real.exp (c * (1 + M)))).congr fun Y => (hrw Y).symm
  -- Squeeze the cap integral norm by `g(Y)·|b - a|`.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqueeze : Tendsto (fun Y : ℝ => g Y * |b - a|) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 * |b - a| by ring]
    exact hg0.mul_const _
  refine squeeze_zero_norm' ?_ hsqueeze
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop 0] with Y hYA hY0
  rw [norm_norm]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := g Y) fun x hx => ?_).trans
    (by rw [mul_comm])
  -- Pointwise bound on the segment `x ∈ uIoc a b`.
  have hxM : |x| ≤ M := by
    have hxmem : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    rw [Set.uIcc_eq_union, Set.mem_union] at hxmem
    rw [abs_le]
    rcases hxmem with h | h
    · refine ⟨?_, ?_⟩
      · exact le_trans (neg_le_neg (le_max_left |a| |b|)) ((neg_abs_le a).trans h.1)
      · exact le_trans h.2 ((le_abs_self b).trans (le_max_right |a| |b|))
    · refine ⟨?_, ?_⟩
      · exact le_trans (neg_le_neg (le_max_right |a| |b|)) ((neg_abs_le b).trans h.1)
      · exact le_trans h.2 ((le_abs_self a).trans (le_max_left |a| |b|))
  have hnorm : ‖(x : ℂ) + Y * Complex.I‖ ≤ M + Y := by
    rw [Complex.norm_add_mul_I]
    calc Real.sqrt (x ^ 2 + Y ^ 2) ≤ Real.sqrt ((M + Y) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hMnn, hY0, abs_nonneg x, sq_abs x, abs_le.mp hxM]
      _ = M + Y := Real.sqrt_sq (by linarith)
  refine (hbound x Y hYA).trans ?_
  show C * max 1 ‖(x : ℂ) + Y * Complex.I‖ ^ D * Real.exp (-c * Y) ≤
    |C| * (1 + M + Y) ^ D * Real.exp (-c * Y)
  gcongr
  · exact le_abs_self C
  · exact max_le (by linarith [hMnn, hY0]) (by linarith [hnorm])

/-! ### Identifying the cusp integral as an improper vertical integral of `periodForm`

`cuspToInftyIntegral f P q` is the integral of the holomorphic form `periodForm f P` up the vertical
line `Re = q` from the real axis to `i∞`.  We record this identification and the integrability of
the
shifted integrand, so the contour-deformation engine applies directly to `cuspValue`. -/

omit [NeZero N] in
/-- The genIntegrand of the `transMat q`-translate against `shiftPoly q P` equals `periodForm f P`
along the vertical line `Re = q`, scaled by `I`. -/
theorem genIntegrand_transMat_eq_periodForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) {t : ℝ} (ht : 0 < t) :
    genIntegrand (⇑(CuspForm.translate f (transMat q))) (shiftPoly q P) t =
      periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I := by
  rw [cuspToInftyIntegral_integrand f P q ht,
    show (Complex.I * (t : ℂ) + (q : ℂ)) = (q : ℂ) + (t : ℂ) * Complex.I by ring]
  rfl

/-- `cuspToInftyIntegral f P q` is the improper integral of `periodForm f P · I` up the vertical
line `Re = q`. -/
theorem cuspToInftyIntegral_eq_periodForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegral f P q =
      ∫ t in Set.Ioi (0 : ℝ), periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I := by
  haveI : (toConjAct (transMat q)⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_conj_transMat q
  rw [cuspToInftyIntegral, genPeriodIntegral]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  exact genIntegrand_transMat_eq_periodForm f P q ht

/-- The shifted integrand `t ↦ periodForm f P (q + t·i)·i` is integrable on `(0, ∞)`. -/
theorem integrableOn_periodForm_vertical (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    IntegrableOn (fun t : ℝ => periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I)
      (Set.Ioi 0) := by
  refine (integrableOn_cuspToInftyIntegrand f P q).congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at ht
  exact genIntegrand_transMat_eq_periodForm f P q ht

/-! ### Improper horizontal-slide path-independence (the engine capstone)

Combining the rectangle Cauchy identity `vertical_segment_cauchy` with the cap-vanishing limit
`tendsto_horizontal_cap`, the integral of `periodForm f P` up the vertical ray from `a + iY₀` to
`i∞` differs from the ray from `b + iY₀` only by the horizontal segment integral at height `Y₀`.
This is the central reusable contour-deformation statement (ES-3c/ES-4 reuse it). -/

/-- Continuity of the period form along a vertical line on the closed ray `[Y₀, ∞)` (`Y₀ > 0`). -/
theorem continuousOn_periodForm_vertical {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [ModularFormClass F Γ k] (f : F) {m : ℕ} (P : SymPow ℂ m) (a : ℝ) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ContinuousOn (fun y : ℝ => periodForm f P ((a : ℂ) + y * Complex.I)) (Set.Ici Y₀) := by
  apply ContinuousOn.comp (g := periodForm f P) (f := fun y : ℝ => (a : ℂ) + y * Complex.I)
    (s := Set.Ici Y₀) (t := {z : ℂ | 0 < z.im})
  · exact (differentiableOn_periodForm f P).continuousOn
  · fun_prop
  · intro y hy
    rw [Set.mem_Ici] at hy
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, Complex.ofReal_im, zero_add, mul_zero]
    linarith

/-- **Improper horizontal-slide path-independence.**  For a cusp form `f`, real base points `a, b`
and height `Y₀ > 0`, the integral of `periodForm f P` up the vertical ray from `a + iY₀` equals the
ray from `b + iY₀` plus the horizontal cap at height `Y₀`.  Provided the vertical-ray integrals
converge.  This is the reusable engine lemma assembled from `vertical_segment_cauchy` (Cauchy) and
`tendsto_horizontal_cap` (cap vanishing). -/
theorem horizontal_slide {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ} (P : SymPow ℂ m) {a b Y₀ : ℝ}
    (hab : a ≤ b) (hY₀ : 0 < Y₀)
    (hia : IntegrableOn (fun y : ℝ => periodForm f P ((a : ℂ) + y * Complex.I)) (Set.Ici Y₀))
    (hib : IntegrableOn (fun y : ℝ => periodForm f P ((b : ℂ) + y * Complex.I)) (Set.Ici Y₀)) :
    (Complex.I * ∫ y in Set.Ioi Y₀, periodForm f P ((a : ℂ) + y * Complex.I)) =
      (Complex.I * ∫ y in Set.Ioi Y₀, periodForm f P ((b : ℂ) + y * Complex.I)) +
        ∫ x in a..b, periodForm f P ((x : ℂ) + Y₀ * Complex.I) := by
  have hiaIoi : IntegrableOn (fun y : ℝ => periodForm f P ((a : ℂ) + y * Complex.I))
      (Set.Ioi Y₀) := hia.mono_set Set.Ioi_subset_Ici_self
  have hibIoi : IntegrableOn (fun y : ℝ => periodForm f P ((b : ℂ) + y * Complex.I))
      (Set.Ioi Y₀) := hib.mono_set Set.Ioi_subset_Ici_self
  -- The truncated vertical integrals converge to the improper ones.
  have hTa := (MeasureTheory.intervalIntegral_tendsto_integral_Ioi Y₀ hiaIoi
    tendsto_id).const_mul Complex.I
  have hTb := (MeasureTheory.intervalIntegral_tendsto_integral_Ioi Y₀ hibIoi
    tendsto_id).const_mul Complex.I
  -- The top cap vanishes.
  have hcap := tendsto_horizontal_cap f P a b
  -- The finite Cauchy identity, valid eventually (for `Y₁ ≥ Y₀`).
  have hCauchy : ∀ᶠ Y₁ : ℝ in atTop,
      (Complex.I * ∫ y in Y₀..Y₁, periodForm f P ((a : ℂ) + y * Complex.I)) =
        (Complex.I * ∫ y in Y₀..Y₁, periodForm f P ((b : ℂ) + y * Complex.I)) +
          ((∫ x in a..b, periodForm f P ((x : ℂ) + Y₀ * Complex.I)) -
            ∫ x in a..b, periodForm f P ((x : ℂ) + Y₁ * Complex.I)) := by
    filter_upwards [eventually_ge_atTop Y₀] with Y₁ hY₁
    exact vertical_segment_cauchy (periodForm f P) (differentiableOn_periodForm f P) hab hY₁ hY₀
  -- Take the limit `Y₁ → ∞`.
  have hlimLHS : Tendsto (fun Y₁ : ℝ =>
      Complex.I * ∫ y in Y₀..Y₁, periodForm f P ((a : ℂ) + y * Complex.I)) atTop
      (𝓝 (Complex.I * ∫ y in Set.Ioi Y₀, periodForm f P ((a : ℂ) + y * Complex.I))) := hTa
  have hlimRHS : Tendsto (fun Y₁ : ℝ =>
      (Complex.I * ∫ y in Y₀..Y₁, periodForm f P ((b : ℂ) + y * Complex.I)) +
        ((∫ x in a..b, periodForm f P ((x : ℂ) + Y₀ * Complex.I)) -
          ∫ x in a..b, periodForm f P ((x : ℂ) + Y₁ * Complex.I))) atTop
      (𝓝 ((Complex.I * ∫ y in Set.Ioi Y₀, periodForm f P ((b : ℂ) + y * Complex.I)) +
        ((∫ x in a..b, periodForm f P ((x : ℂ) + Y₀ * Complex.I)) - 0))) :=
    hTb.add (tendsto_const_nhds.sub hcap)
  rw [sub_zero] at hlimRHS
  exact tendsto_nhds_unique (hlimLHS.congr' hCauchy) hlimRHS

/-! ## The Möbius change-of-variables (reusable)

The substitution `z = γ•w` in the contour integral.  We record the Möbius map `mob γ : ℂ → ℂ`, its
derivative `(c₀w+d)⁻²` (det `= 1`), the automorphy `f(γ•z) = (c₀z+d)^k f(z)` for `γ ∈ Γ₁(N)`, and
the
integrand-level change-of-variables identity `periodForm f (symRep γ P̂)(γ•w)·(c₀w+d)⁻² =
periodForm f P̂ (w)` in which all automorphy factors cancel (`(c₀w+d)^{k-m-2} = 1`, `m = k-2`).
This
is the algebraic core of the `γ`-covariance and is reused by ES-3c/ES-4. -/

/-- The Möbius transformation `w ↦ (a w + b)/(c₀ w + d)` as a map `ℂ → ℂ` for `γ ∈ SL(2, ℤ)`. -/
def mob (γ : SL(2, ℤ)) (w : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))

omit [NeZero N] in
/-- On the upper half-plane, `mob γ` is the Möbius action of `γ`. -/
theorem mob_eq_smul (γ : SL(2, ℤ)) (z : ℍ) : mob γ (z : ℂ) = ((γ • z : ℍ) : ℂ) := by
  rw [mob, UpperHalfPlane.coe_specialLinearGroup_apply]; norm_cast

omit [NeZero N] in
/-- The denominator `c₀ w + d` is nonzero for `w` in the open upper half-plane. -/
theorem denom_mob_ne (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ≠ 0 := by
  have hd := UpperHalfPlane.denom_ne_zero_of_im (Matrix.SpecialLinearGroup.mapGL ℝ γ) hw.ne'
  rw [UpperHalfPlane.denom] at hd
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe] at hd
  intro hc; apply hd
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, algebraMap_int_eq, eq_intCast]
  push_cast at hc ⊢; rw [← hc]

omit [NeZero N] in
/-- **The Möbius derivative.**  `d/dw[(aw+b)/(c₀w+d)] = (det)/(c₀w+d)² = (c₀w+d)⁻²`
(since `det γ = 1`). -/
theorem hasDerivAt_mob (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (mob γ) (((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ^ (2 : ℤ))⁻¹ w := by
  have hne := denom_mob_ne γ hw
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
      have := γ.2; rwa [Matrix.det_fin_two] at this
    exact_mod_cast h
  have hnum : HasDerivAt (fun w : ℂ => (γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) (γ 0 0 : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (γ 0 0 : ℂ)).add_const (γ 0 1 : ℂ)
  have hden : HasDerivAt (fun w : ℂ => (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) (γ 1 0 : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)
  have hdiv := hnum.div hden hne
  have hfun : mob γ = (fun w : ℂ => (γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) /
      (fun w : ℂ => (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) := rfl
  rw [hfun]
  have hnum1 : (γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) -
      ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ) = 1 := by linear_combination hdet
  have hval : (((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ^ (2 : ℤ))⁻¹ =
      ((γ 0 0 : ℂ) * ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) -
        ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) * (γ 1 0 : ℂ)) /
        ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) ^ 2 := by
    rw [hnum1, zpow_two, sq, one_div]
  rw [hval]
  exact hdiv

/-- **Automorphy of the cusp form.**  `f(γ•z) = (c₀ z + d)^k · f(z)` for `γ ∈ Γ₁(N)` (this is the
slash-invariance `⇑f ∣[k] γ = ⇑f` repackaged). -/
theorem automorphy (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : CongruenceSubgroup.Gamma1 N)
    (z : ℍ) :
    f ((γ : SL(2, ℤ)) • z) =
      ((((γ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ : SL(2, ℤ)) 1 1 : ℂ)) ^ k) * f z := by
  have hslash : ⇑f ∣[k] (γ : SL(2, ℤ)) = ⇑f := slash_Gamma1_eq f γ γ.2
  have happ := congrFun hslash z
  rw [ModularForm.SL_slash_apply] at happ
  have hden : UpperHalfPlane.denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
        (γ : SL(2, ℤ)))) z = ((γ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ : SL(2, ℤ)) 1 1 : ℂ) := by
    rw [UpperHalfPlane.denom]; norm_cast
  rw [hden] at happ
  have hne : (((γ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ : SL(2, ℤ)) 1 1 : ℂ)) ≠ 0 :=
    denom_mob_ne (γ : SL(2, ℤ)) z.im_pos
  have hrw : f ((γ : SL(2, ℤ)) • z) =
      f z * (((γ : SL(2, ℤ)) 1 0 : ℂ) * z + ((γ : SL(2, ℤ)) 1 1 : ℂ)) ^ k := by
    rw [← happ, mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one]
  rw [hrw]; ring

/-- **Möbius change-of-variables (integrand level).**  For `γ ∈ Γ₁(N)`, `w` in the upper half-plane,
weight `k ≥ 2`, and `Q = symRep γ P̂`, the period integrand of `Q` at `γ•w` times the Möbius
derivative `(c₀w+d)⁻²` equals the period integrand of `P̂` at `w` — all automorphy factors cancel
(`(c₀w+d)^{k - m - 2} = 1` with `m = (k-2).toNat = k-2`).  This packages
`evalSym1_symRep_smul` + `automorphy` + `hasDerivAt_mob`. -/
theorem periodForm_mob (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : CongruenceSubgroup.Gamma1 N) (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k) {w : ℂ}
    (hw : 0 < w.im) :
    periodForm (⇑f) (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P))
          (mob (γ : SL(2, ℤ)) w) *
        (((((γ : SL(2, ℤ)) 1 0 : ℂ) * w + ((γ : SL(2, ℤ)) 1 1 : ℂ)) ^ (2 : ℤ))⁻¹)
      = periodForm (⇑f) (castSymPow (k - 2).toNat P) w := by
  have hne : ((γ : SL(2, ℤ)) 1 0 : ℂ) * w + ((γ : SL(2, ℤ)) 1 1 : ℂ) ≠ 0 :=
    denom_mob_ne (γ : SL(2, ℤ)) hw
  set D : ℂ := ((γ : SL(2, ℤ)) 1 0 : ℂ) * w + ((γ : SL(2, ℤ)) 1 1 : ℂ) with hD
  set wH : ℍ := ⟨w, hw⟩ with hwH
  have hmob : mob (γ : SL(2, ℤ)) w = (((γ : SL(2, ℤ)) • wH : ℍ) : ℂ) :=
    mob_eq_smul (γ : SL(2, ℤ)) wH
  rw [periodForm, periodForm, hmob]
  have hofc : UpperHalfPlane.ofComplex (((γ : SL(2, ℤ)) • wH : ℍ) : ℂ) = (γ : SL(2, ℤ)) • wH :=
    UpperHalfPlane.ofComplex_apply ((γ : SL(2, ℤ)) • wH)
  have hofw : UpperHalfPlane.ofComplex w = wH := by
    rw [show w = (wH : ℂ) from rfl, UpperHalfPlane.ofComplex_apply wH]
  rw [hofc, hofw]
  have haut : f ((γ : SL(2, ℤ)) • wH) = (D ^ k) * f wH := automorphy f γ wH
  have hev : evalSym1 (k - 2).toNat
      (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P))
        (((γ : SL(2, ℤ)) • wH : ℍ) : ℂ)
      = (D ^ (k - 2).toNat)⁻¹ * evalSym1 (k - 2).toNat (castSymPow (k - 2).toNat P) (wH : ℂ) :=
    evalSym1_symRep_smul (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P) wH
  rw [hev]
  erw [haut]
  have hkm : (k : ℤ) = ((k - 2).toNat : ℤ) + 2 := by
    rw [Int.toNat_of_nonneg (by linarith)]; ring
  have hwcoe : (wH : ℂ) = w := rfl
  rw [hwcoe]
  rw [show (D ^ k * ⇑f wH) *
        ((D ^ (k - 2).toNat)⁻¹ * evalSym1 (k - 2).toNat (castSymPow (k - 2).toNat P) w) *
          (D ^ (2 : ℤ))⁻¹
      = (D ^ k * (D ^ (k - 2).toNat)⁻¹ * (D ^ (2 : ℤ))⁻¹) *
          (⇑f wH * evalSym1 (k - 2).toNat (castSymPow (k - 2).toNat P) w) by ring]
  have hDk : D ^ k = D ^ (k - 2).toNat * D ^ (2 : ℤ) := by
    rw [← zpow_natCast D (k - 2).toNat, ← zpow_add₀ hne, ← hkm]
  have hpow : D ^ k * (D ^ (k - 2).toNat)⁻¹ * (D ^ (2 : ℤ))⁻¹ = 1 := by
    rw [hDk]
    have h1 : (D ^ (k - 2).toNat : ℂ) ≠ 0 := pow_ne_zero _ hne
    have h2 : (D ^ (2 : ℤ) : ℂ) ≠ 0 := zpow_ne_zero _ hne
    field_simp
  rw [hpow, one_mul]
  rfl

/-! ## Vertical-ray cusp decay and the geodesic geometry (reusable)

We assemble the analytic facts about the behaviour of the period form near a *finite* rational cusp,
along the geodesic rays that bound the cusp-to-`i∞` integral.  These are the genuine analytic
ingredients of the geodesic-period invariance and are reused by ES-4. -/

/-- **Vertical-ray cusp decay.**  For a cusp form `f`, the period form `periodForm f P` tends to `0`
along the *vertical* ray `t ↦ q + i t` as `t → 0⁺`, for every rational cusp `q`.  This is the honest
finite-cusp decay (the cusp form vanishes at the cusp *along the vertical geodesic*): it follows
from
`tendsto_genIntegrand_nhdsGT_zero` applied to the horizontal translate `f ∣ transMat q`, since
`genIntegrand (f ∣ transMat q)(shiftPoly q P) t = periodForm f P (q + i t)·i`.

NB.  The decay is genuinely *directional*: the full 2-D limit `periodForm f P z → 0` as `z → q` over
the whole half-plane neighbourhood filter is **false** (e.g. for `f = Δ`, `q = 0`, along the
parabolic approach `z = s + i s²` one has `Δ(z) = (σ_0⁻¹ z)^{12}·Δ(σ_0⁻¹ z)` with `Re(σ_0⁻¹ z)→-∞`,
so `|Δ(z)| → ∞`).  Only the *non-tangential* rays (vertical, and `SL₂(ℤ)`-images of vertical, i.e.
geodesics meeting `ℝ` perpendicularly) carry decay. -/
theorem tendsto_periodForm_vertical_nhdsGT_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (P : SymPow ℂ m) (q : ℚ) :
    Tendsto (fun Y : ℝ => periodForm (⇑f) P ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0) (𝓝 0) := by
  haveI : (toConjAct (transMat q)⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_conj_transMat q
  have hgi := tendsto_genIntegrand_nhdsGT_zero (CuspForm.translate f (transMat q)) (shiftPoly q P)
  have heq : ∀ᶠ Y : ℝ in 𝓝[>] (0:ℝ),
      genIntegrand (⇑(CuspForm.translate f (transMat q))) (shiftPoly q P) Y =
        periodForm (⇑f) P ((q : ℂ) + Y * Complex.I) * Complex.I := by
    filter_upwards [self_mem_nhdsWithin] with Y hY
    rw [Set.mem_Ioi] at hY
    exact genIntegrand_transMat_eq_periodForm f P q hY
  rw [tendsto_congr' heq] at hgi
  have h2 := hgi.mul_const (Complex.I⁻¹)
  simp only [zero_mul] at h2
  refine h2.congr fun Y => ?_
  rw [mul_assoc, Complex.mul_inv_cancel Complex.I_ne_zero, mul_one]

/-- **Geometric core of the cusp geometry.**  If `q` is the pole of `g : GL(2,ℝ)` (i.e.
`g 1 0 ≠ 0` and `g 1 0 · q + g 1 1 = 0`, so the Möbius map `g` sends `q ↦ ∞`), then the imaginary
part of `g • z` along the vertical ray `z = q + i Y`, namely `|det g|·Y / ‖denom g (q+iY)‖²`, tends
to `+∞` as `Y → 0⁺`.  (Along this perpendicular approach `denom g (q+iY) = (g 1 0 · Y) i`, so the
ratio is `(|det g|/(g 1 0)²)·Y⁻¹`.)  This is the geometric reason the `g`-image of the vertical ray
at the pole runs off to `i∞`, used in the conjugate-frame argument for the geodesic-period fact. -/
theorem tendsto_im_div_normSq_denom_vertical (g : GL (Fin 2) ℝ) (q : ℝ)
    (hg10 : (g 1 0 : ℝ) ≠ 0) (hpole : (g 1 0 : ℝ) * q + (g 1 1 : ℝ) = 0)
    (hdet : 0 < |g.det.val|) :
    Tendsto (fun Y : ℝ => |g.det.val| * Y /
        Complex.normSq (UpperHalfPlane.denom g ((q : ℂ) + Y * Complex.I)))
      (𝓝[>] (0:ℝ)) atTop := by
  have hdenom : ∀ Y : ℝ, UpperHalfPlane.denom g ((q : ℂ) + Y * Complex.I)
      = ((g 1 0 : ℝ) * Y : ℝ) * Complex.I := by
    intro Y
    rw [UpperHalfPlane.denom]
    have h0 : (g 1 0 : ℂ) * (q : ℂ) + (g 1 1 : ℂ) = 0 := by
      rw [show (g 1 0 : ℂ) * (q : ℂ) + (g 1 1 : ℂ)
        = (((g 1 0 : ℝ) * q + (g 1 1 : ℝ) : ℝ) : ℂ) by push_cast; ring, hpole]
      simp
    push_cast
    linear_combination h0
  have hnormSq : ∀ Y : ℝ, Complex.normSq (UpperHalfPlane.denom g ((q : ℂ) + Y * Complex.I))
      = (g 1 0 : ℝ) ^ 2 * Y ^ 2 := by
    intro Y
    rw [hdenom Y, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_one]
    ring
  have heq : ∀ᶠ Y : ℝ in 𝓝[>] (0:ℝ),
      |g.det.val| * Y / Complex.normSq (UpperHalfPlane.denom g ((q : ℂ) + Y * Complex.I))
        = (|g.det.val| / (g 1 0 : ℝ) ^ 2) * Y⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with Y hY
    rw [Set.mem_Ioi] at hY
    rw [hnormSq Y]
    field_simp
  rw [tendsto_congr' heq]
  exact Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero

/-- **FTC derivative of a period primitive along a vertical line.**  If `Fp` is a primitive of
`periodForm f P` on the open upper half-plane (e.g. from `Complex.isExactOn_upperHalf`), then the
restriction `t ↦ Fp(q + i t)` to the vertical line `Re = q` has derivative
`periodForm f P (q + i Y)·i` at every height `Y > 0`.  This is the FTC engine that turns the cusp
integral into boundary values of `Fp`; combined with `tendsto_horizontal_cap` (top cap) and
`tendsto_periodForm_vertical_nhdsGT_zero` (bottom decay) it computes the cusp value as
`Fp(i∞) − Fp(q⁺)`. -/
theorem hasDerivAt_periodForm_primitive_vertical {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k] (f : F) {m : ℕ} (P : SymPow ℂ m)
    (Fp : ℂ → ℂ) (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm f P z) z)
    (q : ℝ) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun t : ℝ => Fp ((q : ℂ) + t * Complex.I))
      (periodForm f P ((q : ℂ) + Y * Complex.I) * Complex.I) Y := by
  have him : 0 < ((q : ℂ) + (Y : ℂ) * Complex.I).im := by simp [hY]
  have h1 : HasDerivAt Fp (periodForm f P ((q : ℂ) + (Y : ℂ) * Complex.I))
      ((q : ℂ) + (Y : ℂ) * Complex.I) := hFp _ him
  have hpath : HasDerivAt (fun t : ℝ => (q : ℂ) + (t : ℂ) * Complex.I) Complex.I Y := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := Y)).mul_const Complex.I).const_add (q : ℂ)
    simpa using this
  have h2 := h1.scomp Y hpath
  rw [smul_eq_mul, mul_comm Complex.I] at h2
  exact h2

/-! ### The cusp value as a difference of boundary values of a primitive (FTC)

Combining the FTC derivative `hasDerivAt_periodForm_primitive_vertical` with the integrability of
the
vertical integrand and the convergence of the improper integral, the cusp-to-`i∞` integral
`cuspToInftyIntegral f P q` along the vertical line `Re = q` equals the difference of the *top*
boundary value `lim_{Y→∞} Fp(q + iY)` and the *bottom* boundary value `lim_{Y→0⁺} Fp(q + iY)` of any
primitive `Fp` of `periodForm f P` on `ℍ`.  This is the reusable FTC bridge from the concrete
improper integral to boundary values of the primitive. -/

/-- **Bottom boundary value of a primitive along a vertical ray.**  For `Fp` a primitive of
`periodForm f P` on the open upper half-plane, the value `Fp(q + iY)` converges as `Y → 0⁺` to
`Fp(q + i) − ∫₀¹ periodForm f P (q + it)·i dt`.  (FTC on `[Y, 1]` plus continuity of the truncated
integral in its lower endpoint.) -/
theorem tendsto_primitive_vertical_nhdsGT_zero (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f) P z) z) :
    Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (Fp ((q : ℂ) + Complex.I) -
        ∫ t in (0 : ℝ)..1, periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I)) := by
  set g : ℝ → ℂ := fun t => periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I with hg
  -- The integrand is integrable on `Ioi 0`.
  have hint : IntegrableOn g (Set.Ioi 0) := integrableOn_periodForm_vertical f P q
  -- FTC: for `0 < Y`, `∫_Y^1 g = Fp(q+i) - Fp(q+iY)`.
  have hFTC : ∀ Y : ℝ, 0 < Y →
      (∫ t in Y..1, g t) = Fp ((q : ℂ) + Complex.I) - Fp ((q : ℂ) + Y * Complex.I) := by
    intro Y hY
    have hsub : Set.uIcc Y 1 ⊆ {t : ℝ | 0 < t} := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rw [Set.mem_setOf_eq]
      rcases ht with h | h
      · linarith [h.1]
      · linarith [h.1]
    have hderiv : ∀ t ∈ Set.uIcc Y 1,
        HasDerivAt (fun s : ℝ => Fp ((q : ℂ) + s * Complex.I)) (g t) t := by
      intro t ht
      exact hasDerivAt_periodForm_primitive_vertical f P Fp hFp q (hsub ht)
    have hii : IntervalIntegrable g MeasureTheory.volume Y 1 :=
      (hint.mono_set (fun t ht => hsub ht)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    push_cast; ring_nf
  -- `Y ↦ ∫_1^Y g` is continuous at `0⁺`, with value `∫_1^0 g = -∫_0^1 g`.
  have hii01 : IntervalIntegrable g MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  have hcont : ContinuousWithinAt (fun b : ℝ => ∫ t in (1 : ℝ)..b, g t) (Set.Icc 0 1) 0 :=
    intervalIntegral.continuousWithinAt_primitive (by simp) (by
      simpa using hii01)
  have hcont' : Tendsto (fun Y : ℝ => ∫ t in (1 : ℝ)..Y, g t) (𝓝[>] 0)
      (𝓝 (∫ t in (1 : ℝ)..(0 : ℝ), g t)) := by
    refine hcont.tendsto.mono_left (nhdsWithin_le_iff.mpr ?_)
    have h0 : Set.Ici (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      Filter.mem_of_superset self_mem_nhdsWithin Set.Ioi_subset_Ici_self
    have h1 : Set.Iic (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
    rw [show Set.Icc (0 : ℝ) 1 = Set.Ici 0 ∩ Set.Iic 1 from rfl]
    exact Filter.inter_mem h0 h1
  -- Assemble: `Fp(q+iY) = Fp(q+i) - ∫_Y^1 g = Fp(q+i) + ∫_1^Y g`.
  have hkey : Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..(0 : ℝ), g t)) := by
    have h1 : (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) =ᶠ[𝓝[>] 0]
        (fun Y : ℝ => Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..Y, g t) := by
      filter_upwards [self_mem_nhdsWithin] with Y hY
      rw [Set.mem_Ioi] at hY
      have hh := hFTC Y hY
      rw [intervalIntegral.integral_symm Y 1]
      linear_combination hh
    rw [tendsto_congr' h1]
    exact tendsto_const_nhds.add hcont'
  -- Identify the limit constant.
  have hval : Fp ((q : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..(0 : ℝ), g t =
      Fp ((q : ℂ) + Complex.I) - ∫ t in (0 : ℝ)..1, g t := by
    rw [intervalIntegral.integral_symm 1 0]; ring
  rw [hval] at hkey
  exact hkey

/-- **The cusp value as top-minus-bottom boundary values of a primitive (improper FTC).**  Let `Fp`
be a primitive of `periodForm f P` on the open upper half-plane.  If `Fp(q + iY)` converges to
`Ttop`
as `Y → +∞` (top boundary value at `i∞` along the vertical ray) and to `Bbot` as `Y → 0⁺` (bottom
boundary value at the finite cusp `q`), then the cusp-to-`i∞` integral equals `Ttop − Bbot`.  This
is the FTC bridge identifying the concrete improper integral with boundary values of any primitive.
-/
theorem cuspToInftyIntegral_eq_top_sub_bot (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f) P z) z) (Ttop Bbot : ℂ)
    (hTtop : Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Ttop))
    (hBbot : Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[>] 0) (𝓝 Bbot)) :
    cuspToInftyIntegral f P q = Ttop - Bbot := by
  set g : ℝ → ℂ := fun t => periodForm (⇑f) P ((q : ℂ) + t * Complex.I) * Complex.I with hg
  have hint : IntegrableOn g (Set.Ioi 0) := integrableOn_periodForm_vertical f P q
  -- Rewrite the cusp integral as the improper integral of `g`.
  have hcv : cuspToInftyIntegral f P q = ∫ t in Set.Ioi (0 : ℝ), g t :=
    cuspToInftyIntegral_eq_periodForm f P q
  -- The truncated integrals converge to the improper one.
  have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  -- For each `Y₁ > 0`, the finite FTC: `∫_0^{Y₁} g = Fp(q+iY₁) - Bbot`.
  have hFTC : ∀ Y₁ : ℝ, 0 < Y₁ →
      (∫ t in (0 : ℝ)..Y₁, g t) = Fp ((q : ℂ) + Y₁ * Complex.I) - Bbot := by
    intro Y₁ hY₁
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) Y₁,
        HasDerivAt (fun s : ℝ => Fp ((q : ℂ) + s * Complex.I)) (g t) t := by
      intro t ht
      exact hasDerivAt_periodForm_primitive_vertical f P Fp hFp q ht.1
    have hii : IntervalIntegrable g MeasureTheory.volume 0 Y₁ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY₁.le]
      exact hint.mono_set Set.Ioc_subset_Ioi_self
    -- top boundary value: left-continuity at `Y₁` (the function is continuous there).
    have htop : Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) (𝓝[<] Y₁)
        (𝓝 (Fp ((q : ℂ) + Y₁ * Complex.I))) := by
      have hcont : ContinuousAt (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) Y₁ :=
        (hasDerivAt_periodForm_primitive_vertical f P Fp hFp q hY₁).continuousAt
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hY₁ hderiv hii hBbot htop]
  -- The truncated FTC integrals converge to `Ttop - Bbot`.
  have hTrunc2 : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop (𝓝 (Ttop - Bbot)) := by
    have heq : (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) =ᶠ[atTop]
        (fun Y₁ : ℝ => Fp ((q : ℂ) + Y₁ * Complex.I) - Bbot) := by
      filter_upwards [eventually_gt_atTop 0] with Y₁ hY₁
      exact hFTC Y₁ hY₁
    rw [tendsto_congr' heq]
    exact hTtop.sub_const Bbot
  rw [hcv]
  exact tendsto_nhds_unique hTrunc hTrunc2

/-- **FTC derivative of a period primitive along a horizontal line.**  If `Fp` is a primitive of
`periodForm f P` on the open upper half-plane, then the restriction `x ↦ Fp(x + iY)` to the
horizontal line `Im = Y > 0` has derivative `periodForm f P (x + iY)` at every `x`.  (Used with
`tendsto_horizontal_cap` to slide the top boundary value of `Fp` across real parts.) -/
theorem hasDerivAt_periodForm_primitive_horizontal {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [ModularFormClass F Γ k] (f : F) {m : ℕ} (P : SymPow ℂ m)
    (Fp : ℂ → ℂ) (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm f P z) z)
    {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    HasDerivAt (fun s : ℝ => Fp ((s : ℂ) + Y * Complex.I))
      (periodForm f P ((x : ℂ) + Y * Complex.I)) x := by
  have him : 0 < ((x : ℂ) + (Y : ℂ) * Complex.I).im := by simp [hY]
  have h1 : HasDerivAt Fp (periodForm f P ((x : ℂ) + (Y : ℂ) * Complex.I))
      ((x : ℂ) + (Y : ℂ) * Complex.I) := hFp _ him
  have hpath : HasDerivAt (fun s : ℝ => (s : ℂ) + (Y : ℂ) * Complex.I) 1 x := by
    have := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((Y : ℂ) * Complex.I)
    simpa using this
  have h2 := h1.scomp x hpath
  rw [smul_eq_mul, one_mul] at h2
  exact h2

/-- **The top boundary value of a period primitive is independent of the real part.**  For a cusp
form `f` and a primitive `Fp` of `periodForm f P` on the open upper half-plane, there is a single
complex number `L` (the value of `Fp` at the cusp `i∞`) with `Fp(q + iY) → L` as `Y → +∞` for
*every* real part `q`.  Existence is the convergence of the vertical-ray integral at `q = 0`; the
`q`-independence is the vanishing of the top horizontal cap `tendsto_horizontal_cap`. -/
theorem exists_tendsto_primitive_vertical_atTop (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f) P z) z) :
    ∃ L : ℂ, ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L) := by
  -- Horizontal-cap slide: top limits at different real parts agree.
  have hslide : ∀ a b : ℝ, Tendsto
      (fun Y : ℝ => Fp ((b : ℂ) + Y * Complex.I) - Fp ((a : ℂ) + Y * Complex.I)) atTop (𝓝 0) := by
    intro a b
    have hcap := tendsto_horizontal_cap f P a b
    refine hcap.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Y hY
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun s : ℝ => Fp ((s : ℂ) + Y * Complex.I))
          (periodForm (⇑f) P ((x : ℂ) + Y * Complex.I)) x :=
      fun x _ => hasDerivAt_periodForm_primitive_horizontal f P Fp hFp hY x
    have hii : IntervalIntegrable (fun x : ℝ => periodForm (⇑f) P ((x : ℂ) + Y * Complex.I))
        MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp (g := periodForm (⇑f) P) (f := fun x : ℝ => (x : ℂ) + Y * Complex.I)
        (s := Set.uIcc a b) (t := {z : ℂ | 0 < z.im})
      · exact (differentiableOn_periodForm f P).continuousOn
      · fun_prop
      · intro x _; simp [hY]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
  -- Existence at `q = 0`: the vertical-ray integral converges, so `Fp(iY)` converges.
  set g0 : ℝ → ℂ := fun t => periodForm (⇑f) P ((0 : ℂ) + t * Complex.I) * Complex.I with hg0
  have hint0 : IntegrableOn g0 (Set.Ioi 0) := by
    have h := integrableOn_periodForm_vertical f P 0
    simpa only [hg0, Rat.cast_zero] using h
  set L0 : ℂ := Fp ((0 : ℂ) + Complex.I) +
    (∫ t in Set.Ioi (1 : ℝ), g0 t) with hL0
  have hexists0 : Tendsto (fun Y : ℝ => Fp ((0 : ℂ) + Y * Complex.I)) atTop (𝓝 L0) := by
    -- FTC on `[1, Y₁]` plus convergence of `∫_1^{Y₁} g0 → ∫_{Ioi 1} g0`.
    have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (1 : ℝ)..Y₁, g0 t) atTop
        (𝓝 (∫ t in Set.Ioi (1 : ℝ), g0 t)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
        (hint0.mono_set (Set.Ioi_subset_Ioi (by norm_num))) tendsto_id
    have hFTC : ∀ Y₁ : ℝ, 1 ≤ Y₁ →
        (∫ t in (1 : ℝ)..Y₁, g0 t) = Fp ((0 : ℂ) + Y₁ * Complex.I) - Fp ((0 : ℂ) + Complex.I) := by
      intro Y₁ hY₁
      have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) Y₁,
          HasDerivAt (fun s : ℝ => Fp ((0 : ℂ) + s * Complex.I)) (g0 t) t := by
        intro t ht
        have ht0 : 0 < t := by
          rw [Set.uIcc_of_le hY₁, Set.mem_Icc] at ht; linarith [ht.1]
        exact hasDerivAt_periodForm_primitive_vertical f P Fp hFp 0 ht0
      have hii : IntervalIntegrable g0 MeasureTheory.volume 1 Y₁ :=
        (hint0.mono_set (fun t ht => by
          rw [Set.uIcc_of_le hY₁, Set.mem_Icc] at ht
          rw [Set.mem_Ioi]; linarith [ht.1])).intervalIntegrable
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
      norm_num
    have heq : (fun Y₁ : ℝ => Fp ((0 : ℂ) + Y₁ * Complex.I)) =ᶠ[atTop]
        (fun Y₁ : ℝ => Fp ((0 : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..Y₁, g0 t) := by
      filter_upwards [eventually_ge_atTop 1] with Y₁ hY₁
      rw [hFTC Y₁ hY₁]; ring
    rw [tendsto_congr' heq, hL0]
    exact tendsto_const_nhds.add hTrunc
  -- Transport to all `q` by the cap-slide.
  refine ⟨L0, fun q => ?_⟩
  have hsum := (hslide 0 q).add hexists0
  rw [zero_add] at hsum
  refine hsum.congr fun Y => ?_
  simp only [Complex.ofReal_zero, zero_add]
  ring

/-- **Generic vertical integrability at `q = 0`.**  For any arithmetic cusp form `f`, the vertical
integrand `t ↦ periodForm f P (it)·i` is integrable on `(0, ∞)`.  This is `genIntegrableOn` (the
`q = 0` polymorphic period integral) repackaged through `periodForm`. -/
theorem integrableOn_periodForm_vertical_zero {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (P : SymPow ℂ m) :
    IntegrableOn (fun t : ℝ => periodForm (⇑f0) P ((0 : ℂ) + t * Complex.I) * Complex.I)
      (Set.Ioi 0) := by
  refine (genIntegrableOn f0 P).congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at ht
  rw [genIntegrand_apply_of_pos (⇑f0) P ht]
  rw [periodForm_apply_of_im_pos (⇑f0) P
    (show (0:ℝ) < ((0:ℂ) + (t:ℂ) * Complex.I).im by simp [ht])]
  have hptH : (⟨Complex.I * t, by simp [ht]⟩ : ℍ) = ⟨(0:ℂ) + (t:ℂ) * Complex.I, by simp [ht]⟩ := by
    ext; simp [mul_comm]
  rw [hptH]
  rfl

/-- **The top boundary value, for an arbitrary arithmetic cusp form.**  Generic version of
`exists_tendsto_primitive_vertical_atTop`: for any arithmetic cusp form `f` and primitive `Fp` of
`periodForm f P` on `ℍ`, there is a single `L` (the `i∞`-value) with `Fp(q + iY) → L` as `Y → ∞` for
every `q`.  Needed to extract the `σ`-frame top value of the conjugate cusp form `f ∣ σ`. -/
theorem exists_tendsto_primitive_vertical_atTop' {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (P : SymPow ℂ m) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f0) P z) z) :
    ∃ L : ℂ, ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L) := by
  have hslide : ∀ a b : ℝ, Tendsto
      (fun Y : ℝ => Fp ((b : ℂ) + Y * Complex.I) - Fp ((a : ℂ) + Y * Complex.I)) atTop (𝓝 0) := by
    intro a b
    have hcap := tendsto_horizontal_cap f0 P a b
    refine hcap.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Y hY
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun s : ℝ => Fp ((s : ℂ) + Y * Complex.I))
          (periodForm (⇑f0) P ((x : ℂ) + Y * Complex.I)) x :=
      fun x _ => hasDerivAt_periodForm_primitive_horizontal f0 P Fp hFp hY x
    have hii : IntervalIntegrable (fun x : ℝ => periodForm (⇑f0) P ((x : ℂ) + Y * Complex.I))
        MeasureTheory.volume a b := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp (g := periodForm (⇑f0) P) (f := fun x : ℝ => (x : ℂ) + Y * Complex.I)
        (s := Set.uIcc a b) (t := {z : ℂ | 0 < z.im})
      · exact (differentiableOn_periodForm f0 P).continuousOn
      · fun_prop
      · intro x _; simp [hY]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
  set g0 : ℝ → ℂ := fun t => periodForm (⇑f0) P ((0 : ℂ) + t * Complex.I) * Complex.I with hg0
  have hint0 : IntegrableOn g0 (Set.Ioi 0) := integrableOn_periodForm_vertical_zero f0 P
  set L0 : ℂ := Fp ((0 : ℂ) + Complex.I) + (∫ t in Set.Ioi (1 : ℝ), g0 t) with hL0
  have hexists0 : Tendsto (fun Y : ℝ => Fp ((0 : ℂ) + Y * Complex.I)) atTop (𝓝 L0) := by
    have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (1 : ℝ)..Y₁, g0 t) atTop
        (𝓝 (∫ t in Set.Ioi (1 : ℝ), g0 t)) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
        (hint0.mono_set (Set.Ioi_subset_Ioi (by norm_num))) tendsto_id
    have hFTC : ∀ Y₁ : ℝ, 1 ≤ Y₁ →
        (∫ t in (1 : ℝ)..Y₁, g0 t) = Fp ((0 : ℂ) + Y₁ * Complex.I) - Fp ((0 : ℂ) + Complex.I) := by
      intro Y₁ hY₁
      have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) Y₁,
          HasDerivAt (fun s : ℝ => Fp ((0 : ℂ) + s * Complex.I)) (g0 t) t := by
        intro t ht
        have ht0 : 0 < t := by
          rw [Set.uIcc_of_le hY₁, Set.mem_Icc] at ht; linarith [ht.1]
        exact hasDerivAt_periodForm_primitive_vertical f0 P Fp hFp 0 ht0
      have hii : IntervalIntegrable g0 MeasureTheory.volume 1 Y₁ :=
        (hint0.mono_set (fun t ht => by
          rw [Set.uIcc_of_le hY₁, Set.mem_Icc] at ht
          rw [Set.mem_Ioi]; linarith [ht.1])).intervalIntegrable
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
      norm_num
    have heq : (fun Y₁ : ℝ => Fp ((0 : ℂ) + Y₁ * Complex.I)) =ᶠ[atTop]
        (fun Y₁ : ℝ => Fp ((0 : ℂ) + Complex.I) + ∫ t in (1 : ℝ)..Y₁, g0 t) := by
      filter_upwards [eventually_ge_atTop 1] with Y₁ hY₁
      rw [hFTC Y₁ hY₁]; ring
    rw [tendsto_congr' heq, hL0]
    exact tendsto_const_nhds.add hTrunc
  refine ⟨L0, fun q => ?_⟩
  have hsum := (hslide 0 q).add hexists0
  rw [zero_add] at hsum
  refine hsum.congr fun Y => ?_
  simp only [Complex.ofReal_zero, zero_add]
  ring

omit [NeZero N] in
/-- The Möbius image `mob γ w` lies in the open upper half-plane when `w` does. -/
theorem im_mob_pos (γ : CongruenceSubgroup.Gamma1 N) {w : ℂ} (hw : 0 < w.im) :
    0 < (mob (γ : SL(2, ℤ)) w).im := by
  rw [mob_eq_smul (γ : SL(2, ℤ)) ⟨w, hw⟩]
  exact (((γ : SL(2, ℤ)) • (⟨w, hw⟩ : ℍ)) : ℍ).im_pos

/-- **The Möbius-pullback primitive.**  If `F` is a primitive of `periodForm f Q` on the open upper
half-plane (where `Q = symRep γ (cast P)`), then `F ∘ mob γ` is a primitive of
`periodForm f (cast P)`: its derivative at `w` is the Möbius change-of-variables of `F`'s, which by
`periodForm_mob` is exactly `periodForm f (cast P) w` (all automorphy factors cancel).  This
realises
the change of variables `z = γ•w` at the level of primitives. -/
theorem hasDerivAt_primitive_mob (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : CongruenceSubgroup.Gamma1 N) (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k)
    (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im →
      HasDerivAt Fp (periodForm (⇑f)
        (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P)) z) z)
    {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun z => Fp (mob (γ : SL(2, ℤ)) z))
      (periodForm (⇑f) (castSymPow (k - 2).toNat P) w) w := by
  set Q := symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P) with hQ
  have hmobpos : 0 < (mob (γ : SL(2, ℤ)) w).im := im_mob_pos γ hw
  have hF' : HasDerivAt Fp (periodForm (⇑f) Q (mob (γ : SL(2, ℤ)) w)) (mob (γ : SL(2, ℤ)) w) :=
    hFp (mob (γ : SL(2, ℤ)) w) hmobpos
  have hmob' : HasDerivAt (mob (γ : SL(2, ℤ)))
      (((((γ : SL(2, ℤ)) 1 0 : ℂ) * w + ((γ : SL(2, ℤ)) 1 1 : ℂ)) ^ (2 : ℤ))⁻¹) w :=
    hasDerivAt_mob (γ : SL(2, ℤ)) hw
  have hcomp := hF'.comp w hmob'
  -- The chain-rule derivative equals `periodForm f (cast P) w` by the Möbius covariance.
  have hcov := periodForm_mob f γ P hk hw
  rw [← hcov]
  exact hcomp

omit [NeZero N] in
/-- The `SL(2, ℤ)`-action on `ℙ¹(ℚ)` underlying `cuspAction` agrees with the `GL(2, ℚ)`-action of
`mapGL ℚ γ` (same underlying matrix). -/
theorem cuspAction_eq_mapGL_smul (γ : CongruenceSubgroup.Gamma1 N)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspAction γ c = (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ))) • c := by
  show (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) (γ : SL(2, ℤ))) • c = _
  rw [Projectivization.matrixSpecialLinearGroup_smul_def]
  rfl

omit [NeZero N] in
/-- **The cusp dictionary.**  The `OnePoint ℚ` representative of `cuspAction γ c` is the
`GL(2, ℚ)`-Möbius image `mapGL ℚ γ • (representative of c)`.  This translates the projective cusp
action into the `OnePoint` (Möbius) action that governs `cuspValue`. -/
theorem equivProjectivization_symm_cuspAction (γ : CongruenceSubgroup.Gamma1 N)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    (OnePoint.equivProjectivization ℚ).symm (cuspAction γ c) =
      (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ))) •
        (OnePoint.equivProjectivization ℚ).symm c := by
  rw [cuspAction_eq_mapGL_smul, Equiv.symm_apply_eq, OnePoint.equivProjectivization_smul,
    Equiv.apply_symm_apply]

/-! ## The cusp-difference is independent of the cusp (the contour-deformation crux)

The remaining analytic content is that `cuspDiff f γ Q c` does not depend on `c`.  This is the
contour-deformation / path-independence statement: writing `Q = symRep γ (cast P)`, the integral of
the holomorphic form `f(z)·(symRep γ P)(z,1) dz` up the vertical geodesic from `γ•c` to `i∞` equals
(by the substitution `z = γ•w`) the integral of `f(w)·P(w,1) dw` along the *geodesic arc*
`γ⁻¹·(vertical ray at γc)` from `c` to `γ⁻¹·∞`, and the difference from the vertical cusp integral
at
`c` is a `c`-independent tail.

Three reusable ingredients are **proven, sorry-free**, above:

* the **Möbius change of variables** at the integrand level, `periodForm_mob`: with `m = k-2`
  (`k ≥ 2`), `periodForm f (symRep γ P) (γ•w) · (c₀w+d)⁻² = periodForm f P (w)` — all automorphy
  factors cancel (`(c₀w+d)^{k-m-2} = 1`), packaging `evalSym1_symRep_smul` + `automorphy` +
  `hasDerivAt_mob`;
* a **primitive of the period form on the upper half-plane**, `Complex.isExactOn_upperHalf`:
  `periodForm f Q` is holomorphic on the convex `{0 < im}`, hence has a global primitive `F`, with
  derivative recorded along verticals by `hasDerivAt_periodForm_primitive_vertical`;
* the **vertical-ray cusp decay** `tendsto_periodForm_vertical_nhdsGT_zero` and the **top-cap
  vanishing** `tendsto_horizontal_cap`, which (via the FTC) compute the cusp value as the difference
  of the boundary values `F(i∞) − F(q⁺)` of the primitive `F`.

Combining them: let `F` be a primitive of `periodForm f Q` on `ℍ`.  The Möbius CoV makes `F ∘ mob γ`
a primitive of `periodForm f P` (its derivative is `periodForm f P` by `periodForm_mob`), so by FTC
along verticals
`cuspValue f Q (γc) = F(i∞) − F_v(γc)`,  `cuspValue f P c = F(γ·∞) − F_a(γc)`,
where `F_v(γc) = lim_{Y→0⁺} F(γc + iY)` is the **vertical** bottom limit and
`F_a(γc) = lim_{Y→0⁺} F(γ·(c + iY))` is the **arc** bottom limit of `F` at the finite cusp `γc`
(both limits exist by `genIntegrableOn`), while `F(i∞)` and `F(γ·∞)` are top limits independent of
`c` (the latter is the top limit of `F` at the *fixed* cusp `γ·∞`).  Hence
`cuspValue f Q (γc) − cuspValue f P (c) = (F(i∞) − F(γ·∞)) + μ(c)`,
with `μ(c) := F_a(γc) − F_v(γc)` the **arc-minus-vertical** mismatch of `F` at `γc`.

**The single remaining deep analytic input** is `μ ≡ 0`: the primitive `F` has the *same*
non-tangential boundary limit at the finite cusp `γc` along the vertical ray and along the geodesic
arc.  (NB: this is **not** continuity of `F` for the full 2-D filter — that is false, see
`tendsto_periodForm_vertical_nhdsGT_zero` — only equality of the two perpendicular geodesic limits.)
The standard proof conjugates by `σ ∈ SL(2,ℤ)` with `σ·∞ = γc`: in the `u = σ⁻¹·z` frame the cusp
`γc` becomes `∞`, both rays become curves tending to `i∞`, and `F_v − F_a` equals a *horizontal cap*
integral of the period form of the conjugate cusp form `f ∣ σ` (arithmetic, hence exponentially
decaying at `i∞`), which vanishes by the cap-vanishing mechanism of `tendsto_horizontal_cap`.  This
is the integral Eichler–Shimura geodesic-period fact (Shimura §8.2); its full formalization is a
self-contained development of the conjugate-frame cap (the `SL(2,ℤ)`-twisted analogue of
`horizontal_slide`) and is left as the isolated input below.  Everything else in this file — the
reduction, the Möbius CoV, the primitive, the FTC verticals, and both decay/cap limits — is
sorry-free. -/

/-- The bottom (finite-cusp) boundary value of a primitive `Fp` of `periodForm f P` at the rational
cusp `r`: the value `lim_{Y→0⁺} Fp(r + iY)`, computed by `tendsto_primitive_vertical_nhdsGT_zero` as
`Fp(r + i) − ∫₀¹ periodForm f P (r + it)·i dt`. -/
def botVal (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (P : SymPow ℂ m) (Fp : ℂ → ℂ)
    (r : ℚ) : ℂ :=
  Fp ((r : ℂ) + Complex.I) -
    ∫ t in (0 : ℝ)..1, periodForm (⇑f) P ((r : ℂ) + t * Complex.I) * Complex.I

/-- **The cusp value as `(top boundary) − (cusp boundary)` of a primitive.**  Given a primitive `Fp`
of `periodForm f P` on the upper half-plane whose vertical top boundary value is the constant `L`
(at
every real part), the cusp value at any projective cusp `c` is `L` minus the cusp boundary value of
`Fp` at `c` (which is `L` itself at `∞`, and the finite bottom value `botVal` at a finite cusp).
This
packages `cuspToInftyIntegral_eq_top_sub_bot` (finite cusp) with the definitional value `0` at
`∞`. -/
theorem cuspValue_eq_top_sub_botVal (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im → HasDerivAt Fp (periodForm (⇑f) P z) z) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => Fp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L))
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue f P c =
      L - (match (OnePoint.equivProjectivization ℚ).symm c with
            | (r : ℚ) => botVal f P Fp r
            | .infty => L) := by
  rw [cuspValue]
  cases ho : (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe r =>
    simp only []
    rw [cuspToInftyIntegral_eq_top_sub_bot f P r Fp hFp L (botVal f P Fp r) (hL r) ?_]
    have hbot := tendsto_primitive_vertical_nhdsGT_zero f P r Fp hFp
    exact hbot

/-! ### The σ-conjugate frame (general `SL(2,ℤ)`, not necessarily in `Γ₁(N)`)

To prove the boundary naturality `μ ≡ 0` we conjugate by an `σ ∈ SL(2,ℤ)` sending `∞` to the
finite cusp `γ•o`.  Such `σ` need *not* lie in `Γ₁(N)`, so the automorphy `f(σ•z) = (cz+d)^k f(z)`
fails; instead `f` transforms into the conjugate cusp form `f ∣ σ`, a `CuspForm` for the arithmetic
conjugate group `σ⁻¹ • Γ`.  The Möbius change of variables therefore holds with `f` replaced by
`f ∣ σ` on the codomain.  These two lemmas generalise `periodForm_mob` / `hasDerivAt_primitive_mob`
to arbitrary `g : SL(2,ℤ)` using the slash relation `f(g•z) = (cz+d)^k (f∣g)(z)`. -/

/-- **Möbius change of variables for a general `g ∈ SL(2,ℤ)` (slash form).**  For any function
`h0 : ℍ → ℂ`, weight `k ≥ 2`, `w` in the upper half-plane and `R : Sym^{k-2}`, the period integrand
of `symRep g R` evaluated at `mob g w` times the Möbius derivative `(c₀w+d)⁻²` equals the period
integrand of the slashed function `h0 ∣ g` at `w`.  Unlike `periodForm_mob` (which needs
`γ ∈ Γ₁(N)` so that `h0 ∣ γ = h0`), here the surviving slash appears on the codomain; the automorphy
factors `(c₀w+d)^{k-(k-2)-2} = 1` cancel exactly. -/
theorem periodForm_mob_general (h0 : ℍ → ℂ) (g : SL(2, ℤ)) (R : SymPow ℂ (k - 2).toNat)
    (hk : 2 ≤ k) {w : ℂ} (hw : 0 < w.im) :
    periodForm h0 (symRep ℂ (k - 2).toNat g R) (mob g w) *
          ((((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (2 : ℤ))⁻¹)
      = periodForm (h0 ∣[k] g) R w := by
  have hne : (g 1 0 : ℂ) * w + (g 1 1 : ℂ) ≠ 0 := denom_mob_ne g hw
  set D : ℂ := (g 1 0 : ℂ) * w + (g 1 1 : ℂ) with hD
  set wH : ℍ := ⟨w, hw⟩ with hwH
  have hofw : UpperHalfPlane.ofComplex w = wH := by
    rw [show w = (wH : ℂ) from rfl, UpperHalfPlane.ofComplex_apply wH]
  have hmobcoe : mob g w = ((g • wH : ℍ) : ℂ) := mob_eq_smul g wH
  rw [periodForm, periodForm, hmobcoe, hofw]
  -- The evaluation factor via the `symRep` Möbius covariance.
  have hev : evalSym1 (k - 2).toNat (symRep ℂ (k - 2).toNat g R) ((g • wH : ℍ) : ℂ)
      = (D ^ (k - 2).toNat)⁻¹ * evalSym1 (k - 2).toNat R (wH : ℂ) :=
    evalSym1_symRep_smul g R wH
  -- The automorphy factor: `h0(ofComplex ↑(g•wH)) = (cz+d)^k (h0∣g)(wH)` via the slash relation.
  have haut : h0 (UpperHalfPlane.ofComplex ((g • wH : ℍ) : ℂ)) = (D ^ k) * (h0 ∣[k] g) wH := by
    rw [UpperHalfPlane.ofComplex_apply (g • wH)]
    have happ := ModularForm.SL_slash_apply (k := k) h0 g wH
    have hden : UpperHalfPlane.denom
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) wH = D := by
      rw [UpperHalfPlane.denom]; norm_cast
    rw [hden] at happ
    rw [happ, mul_comm, mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one]
  have hkm : (k : ℤ) = ((k - 2).toNat : ℤ) + 2 := by rw [Int.toNat_of_nonneg (by linarith)]; ring
  have hDk : D ^ k = D ^ (k - 2).toNat * D ^ (2 : ℤ) := by
    rw [← zpow_natCast D (k - 2).toNat, ← zpow_add₀ hne, ← hkm]
  have h1 : (D ^ (k - 2).toNat : ℂ) ≠ 0 := pow_ne_zero _ hne
  have h2 : (D ^ (2 : ℤ) : ℂ) ≠ 0 := zpow_ne_zero _ hne
  have hwcoe : (wH : ℂ) = w := rfl
  rw [hev, hwcoe]
  -- Substitute the automorphy value through `congrArg` (definitional matching of the `h0`-term),
  -- then clear the surviving automorphy factor `D^{k-(k-2)-2} = 1` by `field_simp`.
  refine (congrArg (fun t => t * ((D ^ (k - 2).toNat)⁻¹ * evalSym1 (k - 2).toNat R w)
    * (D ^ (2 : ℤ))⁻¹) haut).trans ?_
  rw [hDk]
  field_simp
  exact mul_comm _ _

/-- **The `σ`-pullback primitive (general `SL(2,ℤ)`).**  If `Fp` is a primitive of
`periodForm h0 (symRep g R)` on the upper half-plane, then `Fp ∘ mob g` is a primitive of
`periodForm (h0 ∣ g) R`: its derivative at `w` is the Möbius change of variables of `Fp`'s, which by
`periodForm_mob_general` equals `periodForm (h0 ∣ g) R w`.  Generalises `hasDerivAt_primitive_mob`
to arbitrary `g` (with the conjugate function `h0 ∣ g`). -/
theorem hasDerivAt_primitive_mob_general (h0 : ℍ → ℂ) (g : SL(2, ℤ))
    (R : SymPow ℂ (k - 2).toNat) (hk : 2 ≤ k) (Fp : ℂ → ℂ)
    (hFp : ∀ z : ℂ, 0 < z.im →
      HasDerivAt Fp (periodForm h0 (symRep ℂ (k - 2).toNat g R) z) z)
    {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun z => Fp (mob g z)) (periodForm (h0 ∣[k] g) R w) w := by
  have hmobpos : 0 < (mob g w).im := by
    rw [mob_eq_smul g ⟨w, hw⟩]; exact ((g • (⟨w, hw⟩ : ℍ) : ℍ)).im_pos
  have hF' : HasDerivAt Fp (periodForm h0 (symRep ℂ (k - 2).toNat g R) (mob g w)) (mob g w) :=
    hFp (mob g w) hmobpos
  have hmob' : HasDerivAt (mob g)
      ((((g 1 0 : ℂ) * w + (g 1 1 : ℂ)) ^ (2 : ℤ))⁻¹) w := hasDerivAt_mob g hw
  have hcomp := hF'.comp w hmob'
  have hcov := periodForm_mob_general h0 g R hk hw
  rw [← hcov]
  exact hcomp

/-! ### The top boundary value along any curve tending to `i∞`

The key analytic fact for the geodesic-period vanishing: a primitive `Hp` of `periodForm h R`
(`h` an arithmetic cusp form) has the *same* boundary value `L` at the cusp `i∞` along **any** curve
`φ Y → i∞` whose real part stays bounded.  The difference from the vertical ray `0 + i·Im(φ Y)` is a
horizontal cap of `periodForm h R`, which vanishes uniformly because the cusp decay
`exp(-c·Im)` beats the polynomial growth on the bounded real strip
(`tendsto_uniform_horizontal_cap`,
the uniform-in-`x` analogue of `tendsto_horizontal_cap`). -/

/-- **Uniform top horizontal cap.**  For a cusp form `f`, the cap integral
`∫₀^{x(i)} periodForm f P (t + i·I(i)) dt` tends to `0` along any filter where `I(i) → +∞`,
uniformly
over the endpoints `x(i)` confined to a fixed band `|x(i)| ≤ M`.  (Cusp decay beats polynomial
growth
on the band.)  This is the uniform-endpoint strengthening of `tendsto_horizontal_cap`. -/
theorem tendsto_uniform_horizontal_cap {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ} (P : SymPow ℂ m)
    {ι : Type*} {l : Filter ι} (M : ℝ) (hMnn : 0 ≤ M) (xf If : ι → ℝ)
    (hx : ∀ᶠ i in l, |xf i| ≤ M) (hI : Tendsto If l atTop) :
    Tendsto (fun i => ∫ t in (0:ℝ)..(xf i), periodForm f0 P ((t : ℂ) + (If i : ℂ) * Complex.I))
      l (𝓝 0) := by
  obtain ⟨c, hc, C, A, hbound⟩ := periodForm_norm_le f0 P
  set D := (P : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  set g : ℝ → ℝ := fun Y => |C| * (1 + M + Y) ^ D * Real.exp (-c * Y) with hg
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hbase : Tendsto (fun Y : ℝ => (1 + M + Y) ^ D * Real.exp (-c * (1 + M + Y)))
        atTop (𝓝 0) := by
      have hcomp := (tendsto_zpow_mul_exp_neg_atTop c hc (D : ℤ)).comp
        (tendsto_atTop_add_const_left atTop (1 + M) tendsto_id)
      refine hcomp.congr fun Y => ?_
      simp only [Function.comp_apply, zpow_natCast, id_eq]
    have hrw : ∀ Y : ℝ, g Y =
        (|C| * Real.exp (c * (1 + M))) * ((1 + M + Y) ^ D * Real.exp (-c * (1 + M + Y))) := by
      intro Y
      rw [hg, show -c * (1 + M + Y) = -(c * (1 + M)) + (-c * Y) by ring, Real.exp_add, Real.exp_neg]
      field_simp
    rw [show (0 : ℝ) = (|C| * Real.exp (c * (1 + M))) * 0 by ring]
    exact (hbase.const_mul (|C| * Real.exp (c * (1 + M)))).congr fun Y => (hrw Y).symm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqueeze : Tendsto (fun i => g (If i) * M) l (𝓝 0) := by
    rw [show (0:ℝ) = 0 * M by ring]
    exact (hg0.comp hI).mul_const M
  refine squeeze_zero_norm' ?_ hsqueeze
  filter_upwards [hI.eventually_ge_atTop (max A 0), hx] with i hi hxi
  have hIA : A ≤ If i := le_trans (le_max_left A 0) hi
  have hI0 : 0 ≤ If i := le_trans (le_max_right A 0) hi
  have hgnn : 0 ≤ g (If i) := by rw [hg]; positivity
  rw [norm_norm]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := g (If i))
    fun t ht => ?_).trans ?_
  · have htM : |t| ≤ M := by
      have hmem : t ∈ Set.uIcc 0 (xf i) := Set.uIoc_subset_uIcc ht
      have hbb := abs_le.mp hxi
      rw [Set.mem_uIcc] at hmem
      rw [abs_le]
      rcases hmem with h | h
      · exact ⟨by linarith [h.1, hbb.1, hMnn], by linarith [h.2, hbb.2]⟩
      · exact ⟨by linarith [h.1, hbb.1], by linarith [h.2, hbb.2, hMnn]⟩
    have hnorm : ‖(t : ℂ) + (If i) * Complex.I‖ ≤ M + If i := by
      rw [Complex.norm_add_mul_I]
      calc Real.sqrt (t ^ 2 + (If i) ^ 2) ≤ Real.sqrt ((M + If i) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [hMnn, hI0, abs_nonneg t, sq_abs t, abs_le.mp htM]
        _ = M + If i := Real.sqrt_sq (by linarith)
    refine (hbound t (If i) hIA).trans ?_
    show C * max 1 ‖(t : ℂ) + (If i) * Complex.I‖ ^ D * Real.exp (-c * If i) ≤
      |C| * (1 + M + If i) ^ D * Real.exp (-c * If i)
    gcongr
    · exact le_abs_self C
    · exact max_le (by linarith [hMnn, hI0]) (by linarith [hnorm])
  · have hxle : |xf i - 0| ≤ M := by rw [sub_zero]; exact hxi
    calc g (If i) * |xf i - 0| ≤ g (If i) * M := by gcongr
      _ = g (If i) * M := rfl

/-- **Top boundary value along a curve tending to `i∞`.**  Let `Hp` be a primitive of
`periodForm f P` on the upper half-plane with vertical top boundary value `L` (at every real part).
If `φ` is a curve whose imaginary part tends to `+∞` along `l` while its real part stays in a fixed
band `|Re(φ i)| ≤ M`, then `Hp(φ i) → L`.  Proof: the difference `Hp(φ i) − Hp(0 + i·Im(φ i))` is a
horizontal cap of `periodForm f P` (FTC), which vanishes by `tendsto_uniform_horizontal_cap`, while
`Hp(0 + i·Im(φ i)) → L` by the vertical top value (since `Im(φ i) → ∞`). -/
theorem tendsto_primitive_curve_atInfty {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (P : SymPow ℂ m) (Hp : ℂ → ℂ) (hHp : ∀ z : ℂ, 0 < z.im → HasDerivAt Hp (periodForm (⇑f0) P z) z)
    (L : ℂ) (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => Hp ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L))
    {ι : Type*} {l : Filter ι} (M : ℝ) (hMnn : 0 ≤ M) (φ : ι → ℂ)
    (hre : ∀ᶠ i in l, |(φ i).re| ≤ M) (him : Tendsto (fun i => (φ i).im) l atTop) :
    Tendsto (fun i => Hp (φ i)) l (𝓝 L) := by
  -- The cap difference `Hp(φ i) − Hp(0 + i·Im(φ i)) → 0`.
  have hcap := tendsto_uniform_horizontal_cap f0 P M hMnn (fun i => (φ i).re) (fun i => (φ i).im)
    hre him
  -- FTC: the cap difference equals the horizontal cap integral (eventually, where `Im(φ i) > 0`).
  have hev : ∀ᶠ i in l, Hp (φ i) - Hp ((0 : ℂ) + (φ i).im * Complex.I)
      = ∫ t in (0:ℝ)..((φ i).re), periodForm (⇑f0) P ((t : ℂ) + ((φ i).im : ℂ) * Complex.I) := by
    filter_upwards [him.eventually_gt_atTop 0] with i hi
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) ((φ i).re),
        HasDerivAt (fun s : ℝ => Hp ((s : ℂ) + ((φ i).im : ℂ) * Complex.I))
          (periodForm (⇑f0) P ((x : ℂ) + ((φ i).im : ℂ) * Complex.I)) x :=
      fun x _ => hasDerivAt_periodForm_primitive_horizontal f0 P Hp hHp hi x
    have hii : IntervalIntegrable
        (fun x : ℝ => periodForm (⇑f0) P ((x : ℂ) + ((φ i).im : ℂ) * Complex.I))
        MeasureTheory.volume 0 ((φ i).re) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp (g := periodForm (⇑f0) P)
        (f := fun x : ℝ => (x : ℂ) + ((φ i).im : ℂ) * Complex.I)
        (s := Set.uIcc 0 ((φ i).re)) (t := {z : ℂ | 0 < z.im})
      · exact (differentiableOn_periodForm f0 P).continuousOn
      · fun_prop
      · intro x _; simp [hi]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
    rw [hftc]
    have hcoe : ((φ i).re : ℂ) + ((φ i).im : ℂ) * Complex.I = φ i := Complex.re_add_im (φ i)
    rw [hcoe]
    norm_num
  -- The vertical ray at real part `0` and height `Im(φ i) → ∞` tends to `L`.
  have hvert : Tendsto (fun i => Hp ((0 : ℂ) + (φ i).im * Complex.I)) l (𝓝 L) := (hL 0).comp him
  have hcombine : Tendsto (fun i => (Hp (φ i) - Hp ((0:ℂ) + (φ i).im * Complex.I))
      + Hp ((0:ℂ) + (φ i).im * Complex.I)) l (𝓝 (0 + L)) :=
    (hcap.congr' (hev.mono fun i h => h.symm)).add hvert
  rw [zero_add] at hcombine
  refine hcombine.congr fun i => ?_
  ring

/-! ### Geometry of the geodesic ray at a finite cusp

When `g ∈ SL(2,ℤ)` sends `q` to `∞` (its lower row annihilates `q`), the Möbius image of the
vertical ray at `q` runs off to `i∞`: `mob g (q + iY) = g₀₀/g₁₀ + i/(g₁₀² Y)`, so its real part is
the *constant* `g₀₀/g₁₀` and its imaginary part `1/(g₁₀² Y) → +∞` as `Y → 0⁺`.  This is the precise
sense in which the `g`-image of a perpendicular approach to the finite cusp `q` is a curve tending
to
`i∞` with bounded real part — exactly the hypotheses of `tendsto_primitive_curve_atInfty`. -/

/-- **Closed form of the Möbius image of the vertical ray at a pole.**  If `g ∈ SL(2,ℤ)` has
`g₁₀ ≠ 0` and `g₁₀·q + g₁₁ = 0` (so `g • q = ∞`), then for `Y > 0`,
`mob g (q + iY) = g₀₀/g₁₀ + i/(g₁₀²·Y)`. -/
theorem mob_pole_eq (g : SL(2, ℤ)) {q Y : ℝ} (hc : (g 1 0 : ℝ) ≠ 0)
    (hpole : (g 1 0 : ℝ) * q + (g 1 1 : ℝ) = 0) (hY : 0 < Y) :
    mob g ((q : ℂ) + (Y : ℂ) * Complex.I)
      = (((g 0 0 : ℝ) / (g 1 0 : ℝ) : ℝ) : ℂ)
        + (((1 : ℝ) / ((g 1 0 : ℝ) ^ 2 * Y) : ℝ) : ℂ) * Complex.I := by
  have hcC : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpoleC : (g 1 0 : ℂ) * (q : ℂ) + (g 1 1 : ℂ) = 0 := by exact_mod_cast hpole
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    have h : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
      have := g.2; rwa [Matrix.det_fin_two] at this
    exact_mod_cast h
  simp only [mob]
  have hden : (g 1 0 : ℂ) * ((q : ℂ) + (Y : ℂ) * Complex.I) + (g 1 1 : ℂ)
      = (g 1 0 : ℂ) * (Y : ℂ) * Complex.I := by linear_combination hpoleC
  rw [hden]
  have hdenne : (g 1 0 : ℂ) * (Y : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcC hYC) Complex.I_ne_zero
  rw [div_eq_iff hdenne]
  have hII : Complex.I ^ 2 = -1 := Complex.I_sq
  push_cast
  field_simp
  linear_combination (g 0 0 : ℂ) * hpoleC - hdet - hII

/-- The real part of the Möbius image of the vertical ray at a pole is the constant `g₀₀/g₁₀`. -/
theorem re_mob_pole (g : SL(2, ℤ)) {q Y : ℝ} (hc : (g 1 0 : ℝ) ≠ 0)
    (hpole : (g 1 0 : ℝ) * q + (g 1 1 : ℝ) = 0) (hY : 0 < Y) :
    (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).re = (g 0 0 : ℝ) / (g 1 0 : ℝ) := by
  rw [mob_pole_eq g hc hpole hY, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the Möbius image of the vertical ray at a pole tends to `+∞` as
`Y → 0⁺`: the perpendicular approach to the finite cusp `q` is sent to a curve running off to
`i∞`. -/
theorem tendsto_im_mob_pole (g : SL(2, ℤ)) {q : ℝ} (hc : (g 1 0 : ℝ) ≠ 0)
    (hpole : (g 1 0 : ℝ) * q + (g 1 1 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).im) (𝓝[>] 0) atTop := by
  have hY0 : ∀ Y : ℝ, 0 < Y → (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).im
      = ((g 1 0 : ℝ) ^ 2)⁻¹ * Y⁻¹ := by
    intro Y hY
    rw [mob_pole_eq g hc hpole hY, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [one_div, mul_inv]; ring
  have heq : (fun Y : ℝ => (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).im) =ᶠ[𝓝[>] 0]
      (fun Y : ℝ => ((g 1 0 : ℝ) ^ 2)⁻¹ * Y⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with Y hY
    exact hY0 Y (Set.mem_Ioi.mp hY)
  rw [tendsto_congr' heq]
  exact Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero

/-- For `g ∈ SL(2,ℤ)` upper-triangular (`g₁₀ = 0`), `g₀₀ g₁₁ = 1`. -/
theorem g00_mul_g11_of_upper (g : SL(2, ℤ)) (hc : (g 1 0 : ℝ) = 0) :
    (g 0 0 : ℝ) * (g 1 1 : ℝ) = 1 := by
  have hR : (g 0 0 : ℝ) * (g 1 1 : ℝ) - (g 0 1 : ℝ) * (g 1 0 : ℝ) = 1 := by
    have h : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
      have := g.2; rwa [Matrix.det_fin_two] at this
    exact_mod_cast h
  rw [hc, mul_zero, sub_zero] at hR; exact hR

/-- `g₀₀ ≠ 0` when `g ∈ SL(2,ℤ)` is upper-triangular (`g₁₀ = 0`), since `g₀₀ g₁₁ = 1`. -/
theorem g00_ne_zero_of_upper (g : SL(2, ℤ)) (hc : (g 1 0 : ℝ) = 0) : (g 0 0 : ℝ) ≠ 0 := by
  have hc11 := g00_mul_g11_of_upper g hc
  rintro h0; rw [h0, zero_mul] at hc11; norm_num at hc11

/-- **Closed form of the Möbius image of the vertical ray for an upper-triangular `g`.**  If
`g ∈ SL(2,ℤ)` has `g₁₀ = 0` (so `g • ∞ = ∞`), then `mob g (q + iY) = (g₀₀ q + g₀₁) g₀₀ + i g₀₀² Y`
(using `g₀₀ g₁₁ = 1`). -/
theorem mob_upper_eq (g : SL(2, ℤ)) {q Y : ℝ} (hc : (g 1 0 : ℝ) = 0) :
    mob g ((q : ℂ) + (Y : ℂ) * Complex.I)
      = ((((g 0 0 : ℝ) * q + (g 0 1 : ℝ)) * (g 0 0 : ℝ) : ℝ) : ℂ)
        + (((g 0 0 : ℝ) ^ 2 * Y : ℝ) : ℂ) * Complex.I := by
  have hc11 := g00_mul_g11_of_upper g hc
  have hg11 : (g 1 1 : ℝ) ≠ 0 := by rintro h0; rw [h0, mul_zero] at hc11; norm_num at hc11
  have hcC : (g 1 0 : ℂ) = 0 := by exact_mod_cast hc
  have hg11C : (g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hg11
  simp only [mob]
  rw [hcC, zero_mul, zero_add, div_eq_iff hg11C]
  have hc11C : (g 0 0 : ℂ) * (g 1 1 : ℂ) = 1 := by exact_mod_cast hc11
  push_cast
  linear_combination (-(((g 0 0 : ℂ) * (q : ℂ) + (g 0 1 : ℂ))
    + (g 0 0 : ℂ) * (Y : ℂ) * Complex.I)) * hc11C

/-- The real part of the upper-triangular Möbius image of the vertical ray is the constant
`(g₀₀ q + g₀₁) g₀₀`. -/
theorem re_mob_upper (g : SL(2, ℤ)) {q Y : ℝ} (hc : (g 1 0 : ℝ) = 0) :
    (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).re = ((g 0 0 : ℝ) * q + (g 0 1 : ℝ)) * (g 0 0 : ℝ) := by
  rw [mob_upper_eq g hc, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the upper-triangular Möbius image of the vertical ray tends to `+∞` as
`Y → +∞` (the vertical ray is sent to a curve `→ i∞`). -/
theorem tendsto_im_mob_upper (g : SL(2, ℤ)) {q : ℝ} (hc : (g 1 0 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).im) atTop atTop := by
  have heq : (fun Y : ℝ => (mob g ((q : ℂ) + (Y : ℂ) * Complex.I)).im)
      = (fun Y : ℝ => (g 0 0 : ℝ) ^ 2 * Y) := by
    ext Y
    rw [mob_upper_eq g hc, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [heq]
  exact Tendsto.const_mul_atTop (by positivity [g00_ne_zero_of_upper g hc]) tendsto_id

/-- **Boundary value of `F` along a `σ`-frame curve.**  Let `F` be a primitive of `periodForm f Q`
on the upper half-plane, `σ ∈ SL(2,ℤ)`, and `L` the `σ`-frame top boundary value of `F` (i.e.
`F(mob σ (q + iY)) → L` as `Y → ∞`, for every `q`).  If `ψ` is a curve in the upper half-plane whose
`σ⁻¹`-image `mob σ⁻¹ ∘ ψ` tends to `i∞` (imaginary part `→ ∞`, real part in a fixed band), then
`F(ψ i) → L`.  This is the heart of the geodesic-period vanishing: conjugating by `σ` turns the
finite-cusp boundary value into the `i∞`-boundary value of the conjugate cusp form `f ∣ σ`, which is
approach-independent by `tendsto_primitive_curve_atInfty`. -/
theorem tendsto_F_curve (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (Q : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Q z) z)
    (σ : SL(2, ℤ)) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop (𝓝 L))
    {ι : Type*} {l : Filter ι} (M : ℝ) (hMnn : 0 ≤ M) (ψ : ι → ℂ) (hψ : ∀ᶠ i in l, 0 < (ψ i).im)
    (hre : ∀ᶠ i in l, |(mob σ⁻¹ (ψ i)).re| ≤ M)
    (him : Tendsto (fun i => (mob σ⁻¹ (ψ i)).im) l atTop) :
    Tendsto (fun i => F (ψ i)) l (𝓝 L) := by
  -- The conjugate cusp form `h = f ∣ σ`, for the arithmetic conjugate group.
  haveI harith : (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ •
      ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
    have hmap : (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ = ((mapGL ℚ σ)⁻¹).map (algebraMap ℚ ℝ) := by
      rw [map_inv, map_mapGL]
    rw [hmap]
    exact Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
  set h := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ) with hh
  have hhcoe : ⇑h = ⇑f ∣[k] σ := by rw [hh, ModularForm.SL_slash]; rfl
  -- `R := symRep σ⁻¹ Q`, so that `symRep σ R = Q`.
  set R := symRep ℂ (k - 2).toNat σ⁻¹ Q with hR
  have hsymRepR : symRep ℂ (k - 2).toNat σ R = Q := by
    rw [hR, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  -- `Hσ = F ∘ mob σ` is a primitive of `periodForm h R`.
  set Hσ : ℂ → ℂ := fun z => F (mob σ z) with hHσ
  have hHσderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt Hσ (periodForm (⇑h) R z) z := by
    intro z hz
    have := hasDerivAt_primitive_mob_general (⇑f) σ R hk F (by rwa [hsymRepR]) hz
    rwa [← hhcoe] at this
  -- `L` is the vertical top value of `Hσ`.
  have hLvert : ∀ q : ℝ, Tendsto (fun Y : ℝ => Hσ ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L) := hL
  -- The curve `φ i = mob σ⁻¹ (ψ i)` tends to `i∞`, so `Hσ(φ i) → L`.
  have hcurve := tendsto_primitive_curve_atInfty h R Hσ hHσderiv L hLvert M hMnn
    (fun i => mob σ⁻¹ (ψ i)) hre him
  -- `Hσ(mob σ⁻¹ (ψ i)) = F(ψ i)` since `mob σ ∘ mob σ⁻¹ = id` on `ℍ` (eventually in `ℍ`).
  refine hcurve.congr' (hψ.mono fun i hi => ?_)
  show F (mob σ (mob σ⁻¹ (ψ i))) = F (ψ i)
  have hinv : mob σ (mob σ⁻¹ (ψ i)) = ψ i := by
    have h1 : mob σ⁻¹ (ψ i) = ((σ⁻¹ • (⟨ψ i, hi⟩ : ℍ) : ℍ) : ℂ) := mob_eq_smul σ⁻¹ ⟨ψ i, hi⟩
    rw [h1, mob_eq_smul σ (σ⁻¹ • ⟨ψ i, hi⟩), ← mul_smul, mul_inv_cancel, one_smul]
  rw [hinv]

/-- **Boundary value of `F` along a Möbius-pole geodesic.**  Specialisation of `tendsto_F_curve`
to the curve `Y ↦ mob g (q₀ + iY)` as `Y → 0⁺`, for `g ∈ SL(2,ℤ)`: if `σ⁻¹ g` sends `q₀` to `∞`
(its lower row annihilates `q₀`), the curve's `σ⁻¹`-image is the pole geodesic
`mob (σ⁻¹ g)(q₀ + iY)` which runs off to `i∞` (`tendsto_im_mob_pole`, `re_mob_pole`), so
`F(mob g (q₀ + iY)) → Lσ`.  This is the workhorse for every finite-cusp case of the boundary
naturality. -/
theorem tendsto_F_pole (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (Q : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Q z) z) (σ : SL(2, ℤ)) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop (𝓝 L))
    (gg : SL(2, ℤ)) (q₀ : ℝ) (hc : ((σ⁻¹ * gg) 1 0 : ℝ) ≠ 0)
    (hpole : ((σ⁻¹ * gg) 1 0 : ℝ) * q₀ + ((σ⁻¹ * gg) 1 1 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => F (mob gg ((q₀ : ℂ) + Y * Complex.I))) (𝓝[>] 0) (𝓝 L) := by
  have hmobpos : ∀ Y : ℝ, 0 < Y → 0 < (mob gg ((q₀ : ℂ) + Y * Complex.I)).im := by
    intro Y hY
    rw [mob_eq_smul gg ⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩]
    exact (gg • (⟨(q₀:ℂ) + Y * Complex.I, by simp [hY]⟩ : ℍ)).im_pos
  -- The `σ⁻¹`-image of the curve is the pole geodesic `mob (σ⁻¹ g)(q₀ + iY)`.
  have hcomp : ∀ Y : ℝ, 0 < Y →
      mob σ⁻¹ (mob gg ((q₀:ℂ) + Y * Complex.I)) = mob (σ⁻¹ * gg) ((q₀:ℂ) + Y * Complex.I) := by
    intro Y hYp
    have h1 : mob gg ((q₀:ℂ) + Y * Complex.I)
        = ((gg • (⟨(q₀:ℂ) + Y * Complex.I, by simp [hYp]⟩ : ℍ) : ℍ) : ℂ) :=
      mob_eq_smul gg ⟨_, by simp [hYp]⟩
    rw [h1, mob_eq_smul σ⁻¹ (gg • _), ← mul_smul, mob_eq_smul (σ⁻¹ * gg) ⟨_, by simp [hYp]⟩]
  refine tendsto_F_curve f hk Q F hF σ L hL
    (|((σ⁻¹ * gg) 0 0 : ℝ) / ((σ⁻¹ * gg) 1 0 : ℝ)|) (abs_nonneg _)
    (fun Y : ℝ => mob gg ((q₀:ℂ) + (Y:ℂ) * Complex.I)) ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with Y hY; exact hmobpos Y (Set.mem_Ioi.mp hY)
  · filter_upwards [self_mem_nhdsWithin] with Y hY
    rw [hcomp Y (Set.mem_Ioi.mp hY), re_mob_pole (σ⁻¹ * gg) hc hpole (Set.mem_Ioi.mp hY)]
  · have heq : (fun Y : ℝ => (mob σ⁻¹ (mob gg ((q₀:ℂ) + Y * Complex.I))).im) =ᶠ[𝓝[>] 0]
        (fun Y : ℝ => (mob (σ⁻¹ * gg) ((q₀:ℂ) + Y * Complex.I)).im) := by
      filter_upwards [self_mem_nhdsWithin] with Y hY
      rw [hcomp Y (Set.mem_Ioi.mp hY)]
    rw [tendsto_congr' heq]
    exact tendsto_im_mob_pole (σ⁻¹ * gg) hc hpole

/-- **Boundary value of `F` along an upper-triangular geodesic to `i∞`.**  For `F` a primitive of
`periodForm f Q` with identity-frame top value `Finf`, and `g ∈ SL(2,ℤ)` upper-triangular
(`g₁₀ = 0`, so `g • ∞ = ∞`), the vertical ray's image `mob g (q₀ + iY)` runs off to `i∞` as
`Y → ∞`, so `F(mob g (q₀ + iY)) → Finf`. -/
theorem tendsto_F_upper (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (Q : SymPow ℂ (k - 2).toNat) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Q z) z) (Finf : ℂ)
    (hFinf : ∀ q : ℝ, Tendsto (fun Y : ℝ => F ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Finf))
    (gg : SL(2, ℤ)) (q₀ : ℝ) (hc : (gg 1 0 : ℝ) = 0) :
    Tendsto (fun Y : ℝ => F (mob gg ((q₀ : ℂ) + (Y:ℂ) * Complex.I))) atTop (𝓝 Finf) := by
  refine tendsto_primitive_curve_atInfty f Q F hF Finf hFinf
    (|((gg 0 0 : ℝ) * q₀ + (gg 0 1 : ℝ)) * (gg 0 0 : ℝ)|) (abs_nonneg _)
    (fun Y : ℝ => mob gg ((q₀:ℂ) + (Y:ℂ) * Complex.I)) ?_ (tendsto_im_mob_upper gg hc)
  filter_upwards with Y; rw [re_mob_upper gg hc]

/-- The relevant entries of `g⁻¹` for `g ∈ SL(2,ℤ)`: `(g⁻¹)₁₀ = -g₁₀`, `(g⁻¹)₁₁ = g₀₀`. -/
theorem inv_entries (g : SL(2, ℤ)) :
    (g⁻¹ 1 0 : ℝ) = -(g 1 0 : ℝ) ∧ (g⁻¹ 1 1 : ℝ) = (g 0 0 : ℝ) := by
  refine ⟨?_, ?_⟩ <;>
    (rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp)

/-- **Pole data from a cusp mapping to `∞`.**  If `h ∈ SL(2,ℤ)` sends the rational cusp `c` to `∞`
(`mapGL ℚ h • c = ∞`), then its lower row `(h₁₀, h₁₁)` annihilates `c` and `h₁₀ ≠ 0` (over `ℝ`).
This translates the `OnePoint` pole condition into the matrix pole condition used by
`tendsto_F_pole`. -/
theorem pole_of_smul_infty (h : SL(2, ℤ)) (c : ℚ)
    (hsmul : (Matrix.SpecialLinearGroup.mapGL ℚ h) • (c : OnePoint ℚ) = ∞) :
    (h 1 0 : ℝ) ≠ 0 ∧ (h 1 0 : ℝ) * (c:ℝ) + (h 1 1 : ℝ) = 0 := by
  have hent : ∀ i j : Fin 2, (Matrix.SpecialLinearGroup.mapGL ℚ h) i j = ((h i j : ℤ) : ℚ) := by
    intro i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [OnePoint.smul_some_eq_ite] at hsmul
  have hpoleQ : (Matrix.SpecialLinearGroup.mapGL ℚ h) 1 0 * c
      + (Matrix.SpecialLinearGroup.mapGL ℚ h) 1 1 = 0 := by
    by_contra hne; rw [if_neg hne] at hsmul; exact absurd hsmul (by simp)
  rw [hent 1 0, hent 1 1] at hpoleQ
  have hpoleR : (h 1 0 : ℝ) * (c:ℝ) + (h 1 1 : ℝ) = 0 := by exact_mod_cast hpoleQ
  refine ⟨?_, hpoleR⟩
  intro hz
  rw [hz, zero_mul, zero_add] at hpoleR
  have hdet : (h 0 0 : ℝ) * (h 1 1 : ℝ) - (h 0 1 : ℝ) * (h 1 0 : ℝ) = 1 := by
    have hh : (h 0 0) * (h 1 1) - (h 0 1) * (h 1 0) = 1 := by
      have := h.2; rwa [Matrix.det_fin_two] at this
    exact_mod_cast hh
  rw [hpoleR] at hdet
  have hz' : (h 1 0 : ℝ) = 0 := by exact_mod_cast hz
  rw [hz'] at hdet; simp at hdet

/-- **Naturality of the cusp boundary value under the Möbius pullback (the isolated geodesic-period
crux, `μ ≡ 0`).**  Let `F` be a primitive of `periodForm f Q` on the upper half-plane
(`Q = symRep γ (cast P)`) with vertical top boundary value `F∞`, and `G := F ∘ mob γ` the Möbius
pullback, a primitive of `periodForm f (cast P)` with top boundary value `G∞`.  Then the cusp
boundary value of `G` at any cusp `o ∈ ℙ¹(ℚ)` equals the cusp boundary value of `F` at the
Möbius-translated cusp `γ • o`:
`(o = ∞ ? G∞ : botVal G o) = (γ•o = ∞ ? F∞ : botVal F (γ•o))`.

This is the equality of the two non-tangential boundary limits of `F` at the finite cusp `γ•o` — the
vertical-ray limit and the geodesic-arc limit `F(mob γ ·)` — together with the matching top-limit
reconciliations at `∞`.  It is the integral Eichler–Shimura geodesic-period fact (Shimura §8.2),
proven by conjugating with `σ ∈ SL(2,ℤ)`, `σ•∞ = γ•o`, so that both rays become curves tending to
`i∞` in the `σ`-frame and their difference is a horizontal cap of the period form of the conjugate
(arithmetic) cusp form `f ∣ σ`, vanishing by `tendsto_horizontal_cap`.  All the surrounding
reduction
(`cuspValue_eq_top_sub_botVal`, `hasDerivAt_primitive_mob`,
`exists_tendsto_primitive_vertical_atTop`,
the cusp dictionary) is proven; this naturality is the lone remaining analytic input. -/
theorem cuspBoundary_mob_naturality (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : CongruenceSubgroup.Gamma1 N) (P : SymPow ℤ (k - 2).toNat) (hk : 2 ≤ k)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F (periodForm (⇑f)
        (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P)) z) z)
    (Finf Ginf : ℂ)
    (hFinf : ∀ q : ℝ, Tendsto (fun Y : ℝ => F ((q : ℂ) + Y * Complex.I)) atTop (𝓝 Finf))
    (hGinf : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => F (mob (γ : SL(2, ℤ)) ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf))
    (o : OnePoint ℚ) :
    (match o with
      | (s : ℚ) => botVal f (castSymPow (k - 2).toNat P) (fun z => F (mob (γ : SL(2, ℤ)) z)) s
      | .infty => Ginf) =
    (match (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ))) • o with
      | (r : ℚ) => botVal f (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P)) F r
      | .infty => Finf) := by
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symRep ℂ (k - 2).toNat g cP with hQ
  set G : ℂ → ℂ := fun z => F (mob g z) with hG
  -- `G = F ∘ mob g` is a primitive of `periodForm f cP`.
  have hGderiv : ∀ z : ℂ, 0 < z.im → HasDerivAt G (periodForm (⇑f) cP z) z :=
    fun z hz => hasDerivAt_primitive_mob f γ P hk F hF hz
  -- Entries of `mapGL ℚ γ` are the integer entries of `γ`, cast.
  have hent : ∀ i j : Fin 2, (Matrix.SpecialLinearGroup.mapGL ℚ g) i j = ((g i j : ℤ) : ℚ) := by
    intro i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  -- Bottom boundary value of `F` at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotF : ∀ r : ℚ, Tendsto (fun Y : ℝ => F ((r : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botVal f Q F r)) := fun r => tendsto_primitive_vertical_nhdsGT_zero f Q r F hF
  -- Bottom boundary value of `G` at a finite cusp, as a `𝓝[>] 0` limit.
  have hbotG : ∀ s : ℚ, Tendsto (fun Y : ℝ => G ((s : ℂ) + Y * Complex.I)) (𝓝[>] 0)
      (𝓝 (botVal f cP G s)) := fun s => tendsto_primitive_vertical_nhdsGT_zero f cP s G hGderiv
  -- `mob 1 = id`.
  have hmob1 : ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z := fun z => by simp [mob]
  cases o with
  | infty =>
    -- LHS = `Ginf`.  Split on whether `γ • ∞ = ∞`.
    show Ginf = _
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 = 0
    · -- `γ` upper-triangular: `γ • ∞ = ∞`, RHS = `Finf`; show `Ginf = Finf` (case A).
      rw [if_pos hc]
      have hc0 : (g 1 0 : ℝ) = 0 := by
        have : ((g 1 0 : ℤ) : ℚ) = 0 := by rw [← hent 1 0]; exact hc
        exact_mod_cast this
      exact tendsto_nhds_unique (hGinf 0) (tendsto_F_upper f Q F hF Finf hFinf g 0 hc0)
    · -- `γ • ∞ = γ₀₀/γ₁₀` finite, RHS = `botVal f Q F r`; show `Ginf = botVal f Q F r` (case B).
      rw [if_neg hc]
      set r : ℚ := (Matrix.SpecialLinearGroup.mapGL ℚ g) 0 0 /
        (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 with hr
      show Ginf = botVal f Q F r
      -- `σ = g` is a representative of `r`: `g • ∞ = r`, so `g⁻¹ • r = ∞`.
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) • (r : OnePoint ℚ) = ∞ := by
        have hgr : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (∞ : OnePoint ℚ) = (r : OnePoint ℚ) := by
          rw [OnePoint.smul_infty_eq_ite, if_neg hc]
        rw [map_inv, ← hgr, ← mul_smul, inv_mul_cancel, one_smul]
      obtain ⟨hcinv, hpoleinv⟩ := pole_of_smul_infty g⁻¹ r hsmulr
      have hbotr := tendsto_F_pole f hk Q F hF g Ginf hGinf 1 (r:ℝ)
        (by simpa using hcinv) (by simpa using hpoleinv)
      simp only [hmob1] at hbotr
      exact (tendsto_nhds_unique (hbotF r) hbotr).symm
  | coe s =>
    -- LHS = `botVal f cP G s`.  Split on whether `γ • s = ∞`.
    show botVal f cP G s = _
    rw [OnePoint.smul_some_eq_ite]
    by_cases hc : (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 * (s:ℚ)
        + (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 1 = 0
    · -- `γ • s = ∞`, RHS = `Finf`; show `botVal f cP G s = Finf` (case C).
      rw [if_pos hc]
      have hsmuls : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (s : OnePoint ℚ) = ∞ := by
        rw [OnePoint.smul_some_eq_ite, if_pos hc]
      obtain ⟨hcs, hpoles⟩ := pole_of_smul_infty g s hsmuls
      -- Identity-frame pole curve `σ = 1`: `botVal f cP G s = lim F(mob g (s+iY)) = Finf`.
      have hbots := tendsto_F_pole f hk Q F hF 1 Finf
        (by intro q; simpa only [hmob1] using hFinf q) g (s:ℝ)
        (by simpa using hcs) (by simpa using hpoles)
      -- `G(s + iY) = F(mob g (s + iY))`, so `hbotG s` is about the same function.
      have hbotGs : Tendsto (fun Y : ℝ => F (mob g ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botVal f cP G s)) := hbotG s
      exact tendsto_nhds_unique hbotGs hbots
    · -- `γ • s = r` finite, RHS = `botVal f Q F r`; show LHS = RHS (case D).
      rw [if_neg hc]
      set r : ℚ := ((Matrix.SpecialLinearGroup.mapGL ℚ g) 0 0 * (s:ℚ)
          + (Matrix.SpecialLinearGroup.mapGL ℚ g) 0 1)
        / ((Matrix.SpecialLinearGroup.mapGL ℚ g) 1 0 * (s:ℚ)
          + (Matrix.SpecialLinearGroup.mapGL ℚ g) 1 1) with hr
      show botVal f cP G s = botVal f Q F r
      have hgsr : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (s : OnePoint ℚ) = (r : OnePoint ℚ) := by
        rw [OnePoint.smul_some_eq_ite, if_neg hc]
      -- Pick `σ` with `σ • ∞ = r` (transitivity).
      obtain ⟨σ, hσ⟩ := ((r : OnePoint ℚ)).exists_mem_SL2 ℤ
      haveI harith : (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ •
          ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
        have hmap : (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
            = ((mapGL ℚ σ)⁻¹).map (algebraMap ℚ ℝ) := by rw [map_inv, map_mapGL]
        rw [hmap]
        exact Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
      -- σ-frame top value of `F` (top value of `F ∘ mob σ`).
      obtain ⟨Lσ, hLσ⟩ := exists_tendsto_primitive_vertical_atTop'
        (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ))
        (symRep ℂ (k - 2).toNat σ⁻¹ Q) (fun z => F (mob σ z)) (by
          intro z hz
          have hsr : symRep ℂ (k - 2).toNat σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) = Q := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
          have hd := hasDerivAt_primitive_mob_general (⇑f) σ (symRep ℂ (k - 2).toNat σ⁻¹ Q) hk F
            (by rwa [hsr]) hz
          have hcoe : ⇑(CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ))
              = ⇑f ∣[k] σ := by rw [ModularForm.SL_slash]; rfl
          rw [hcoe]; exact hd)
      have hLσ' : ∀ q : ℝ, Tendsto (fun Y : ℝ => F (mob σ ((q : ℂ) + Y * Complex.I))) atTop
          (𝓝 Lσ) := hLσ
      -- `σ⁻¹ • r = ∞` and `(σ⁻¹ γ) • s = ∞`.
      have hsmulr : (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) • (r : OnePoint ℚ) = ∞ := by
        rw [map_inv, ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
      have hsmulσγs : (Matrix.SpecialLinearGroup.mapGL ℚ (σ⁻¹ * g)) • (s : OnePoint ℚ) = ∞ := by
        rw [map_mul, mul_smul, hgsr, map_inv, ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
      -- LHS = `Lσ` (arc curve, pole `σ⁻¹ γ` at `s`).
      obtain ⟨hcD, hpoleD⟩ := pole_of_smul_infty (σ⁻¹ * g) s hsmulσγs
      have hLHS := tendsto_F_pole f hk Q F hF σ Lσ hLσ' g (s:ℝ) hcD hpoleD
      -- `G(s + iY) = F(mob g (s + iY))`, so `hbotG s` is about the same arc curve.
      have hbotGs : Tendsto (fun Y : ℝ => F (mob g ((s : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botVal f cP G s)) := hbotG s
      -- RHS = `Lσ` (vertical ray, pole `σ⁻¹` at `r`).
      obtain ⟨hcR, hpoleR⟩ := pole_of_smul_infty σ⁻¹ r hsmulr
      have hRHS := tendsto_F_pole f hk Q F hF σ Lσ hLσ' 1 (r:ℝ)
        (by simpa using hcR) (by simpa using hpoleR)
      simp only [hmob1] at hRHS
      rw [tendsto_nhds_unique hbotGs hLHS, tendsto_nhds_unique (hbotF r) hRHS]

/-- **The `γ`-covariance of the cusp value up to a `c`-independent constant** (`k ≥ 2`).  For
`γ ∈ Γ₁(N)` there is a constant `T` (a `c`-independent tail period) with
`cuspValue f (symRep γ (cast P)) (γ • c) = cuspValue f (cast P) c + T` for every cusp `c`.

This is assembled, axiom-cleanly modulo `cuspBoundary_mob_naturality`, from: a primitive
`F` of `periodForm f Q` on `ℍ` (`Complex.isExactOn_upperHalf`); its Möbius pullback `G = F ∘ mob γ`,
a primitive of `periodForm f (cast P)` (`hasDerivAt_primitive_mob`); the `c`-independent top
boundary
values `F∞`, `G∞` (`exists_tendsto_primitive_vertical_atTop`); the cusp-value formula
`cuspValue = (top) − (cusp boundary)` (`cuspValue_eq_top_sub_botVal`); and the cusp dictionary
(`equivProjectivization_symm_cuspAction`).  Then `T = F∞ − G∞`, and the residual identity is exactly
the cusp-boundary naturality `cuspBoundary_mob_naturality` (`μ ≡ 0`).

The weight hypothesis `2 ≤ k` is essential: for `k < 2` the `(k-2).toNat` truncation collapses the
intended `Sym^{k-2}` coefficient system to the trivial `Sym⁰`, and the Möbius change of variables
leaves a *surviving* automorphy factor `(cw+d)^{k-2}` that does **not** cancel (e.g. at `k = 1` the
weight-`1` differential `n·f(z)\,dz` is not `Γ`-invariant, so the `c`-independence genuinely fails).
The modular-symbol period formalism applies only for `k ≥ 2`. -/
theorem cuspValue_symRep_gamma (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : CongruenceSubgroup.Gamma1 N) (P : SymPow ℤ (k - 2).toNat) :
    ∃ T : ℂ, ∀ c : Projectivization ℚ (Fin 2 → ℚ),
      cuspValue f (symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) (castSymPow (k - 2).toNat P))
          (cuspAction γ c) =
        cuspValue f (castSymPow (k - 2).toNat P) c + T := by
  -- Build the two primitives and reduce to the boundary naturality.
  set cP := castSymPow (k - 2).toNat P with hcP
  set Q := symRep ℂ (k - 2).toNat (γ : SL(2, ℤ)) cP with hQ
  obtain ⟨F, hF⟩ := Complex.isExactOn_upperHalf (differentiableOn_periodForm f Q)
  have hFz : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Q z) z := hF
  -- `G := F ∘ mob γ` is a primitive of `periodForm f cP`.
  have hG : ∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun w => F (mob (γ : SL(2, ℤ)) w)) (periodForm (⇑f) cP z) z := by
    intro z hz
    exact hasDerivAt_primitive_mob f γ P hk F hFz hz
  -- Top boundary values.
  obtain ⟨Finf, hFinf⟩ := exists_tendsto_primitive_vertical_atTop f Q F hFz
  obtain ⟨Ginf, hGinf⟩ := exists_tendsto_primitive_vertical_atTop f cP
    (fun w => F (mob (γ : SL(2, ℤ)) w)) hG
  -- The top-limit of `G` along the `q`-vertical is `Ginf`, also as the `mob`-pulled limit.
  have hGinf' : ∀ q : ℝ,
      Tendsto (fun Y : ℝ => F (mob (γ : SL(2, ℤ)) ((q : ℂ) + Y * Complex.I))) atTop (𝓝 Ginf) :=
    hGinf
  refine ⟨Finf - Ginf, fun c => ?_⟩
  -- Cusp-value formulas for both sides.
  have hcvQ := cuspValue_eq_top_sub_botVal f Q F hFz Finf hFinf (cuspAction γ c)
  have hcvP := cuspValue_eq_top_sub_botVal f cP (fun w => F (mob (γ : SL(2, ℤ)) w)) hG Ginf
    hGinf c
  rw [hcvQ, hcvP]
  -- Translate the cusp via the dictionary.
  rw [equivProjectivization_symm_cuspAction]
  -- Reduce to the boundary naturality.
  have hnat := cuspBoundary_mob_naturality f γ P hk F hFz Finf Ginf hFinf hGinf'
    ((OnePoint.equivProjectivization ℚ).symm c)
  rw [hnat]
  ring

/-- **The contour-deformation crux.**  For `γ ∈ Γ₁(N)`, weight `k`, and the substituted polynomial
`Q = symRep γ (cast P)`, the cusp-difference `cuspDiff f γ Q` is independent of the cusp `c`.  This
follows immediately from `cuspValue_symRep_gamma`: the `c`-dependent parts cancel. -/
theorem cuspDiff_const (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : CongruenceSubgroup.Gamma1 N)
    (P : SymPow ℤ (k - 2).toNat) (c₁ c₂ : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspDiff f γ (castSymPow (k - 2).toNat P) c₁ =
      cuspDiff f γ (castSymPow (k - 2).toNat P) c₂ := by
  obtain ⟨T, hT⟩ := cuspValue_symRep_gamma hk f γ P
  simp only [cuspDiff, hT]
  ring

/-! ## `isPeriodInvariant_all` -/

/-- **The period pairing is `Γ₁(N)`-invariant** for every cusp form `f`.  This discharges the
hypothesis `IsPeriodInvariant` of `PeriodMap.lean`, making `periodMap` unconditional. -/
theorem isPeriodInvariant_all (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsPeriodInvariant f := by
  intro γ
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  -- It suffices to prove the difference `rawPairing f (γ • x) − rawPairing f x` vanishes.
  rw [← sub_eq_zero]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul D P =>
    rw [rawPairing_modSymRep_sub f γ D P]
    exact sum_cuspDiff_eq_zero_of_const f γ (castSymPow (k - 2).toNat P) D
      (fun c₁ c₂ => cuspDiff_const hk f γ P c₁ c₂)
  | add x y hx hy =>
    simp only [map_add]; linear_combination hx + hy

/-! ## The unconditional period map -/

variable (N k) in
/-- **The period map for weight `k ≥ 2`** (Shimura §8.2): the `ℂ`-linear map sending a cusp form `f`
to the `ℤ`-linear functional `⟦((α)-(β)) ⊗ P⟧ ↦ ∫_β^α f(z)·P(z,1) dz` on the modular-symbol module
`𝕄 N k`.  This is `periodMap` with the `Γ`-invariance input discharged by `isPeriodInvariant_all`,
so it requires only the weight hypothesis `2 ≤ k` (which is essential: see `cuspValue_symRep_gamma`,
the modular-symbol formalism is valid only for `k ≥ 2`). -/
noncomputable def periodMap' (hk : 2 ≤ k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ) :=
  periodMap (fun f => isPeriodInvariant_all hk f)

@[simp]
theorem periodMap'_apply_mk (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    periodMap' N k hk f (𝕄.mk N k x) = rawPairing f x :=
  rfl

end HeckeRing.GL2.ModularSymbols
