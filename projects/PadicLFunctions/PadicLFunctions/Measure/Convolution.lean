import PadicLFunctions.Measure.MahlerTransform

/-!
# The convolution algebra structure on measures on ℤ_p

RJW (arXiv:2309.15692) §3.3: the Iwasawa algebra structure on `ℳ(ℤ_p, ℤ_p)`. The source
obtains the ring structure "by transport of structure" (Rem. 3.11,
`RemarkConvolution`, TeX line 908) and describes it by the convolution formula

  `∫ φ d(μ*λ) = ∫ (∫ φ(x+y) dλ(y)) dμ(x)`,

leaving "one checks that this does give an algebra structure" to the reader. We follow
the source exactly: the multiplication is *defined* by transporting the power-series
multiplication along `mahlerLinearEquiv`, and the convolution formula is the theorem
`PadicMeasure.mul_apply`, proved on the Mahler basis via the Chu–Vandermonde identity
(`Ring.add_choose_eq`); injectivity of the Mahler transform supplies the extension to
all continuous functions.

## Main results

* `instCommRing : CommRing (PadicMeasure p ℤ_[p])` — the Iwasawa algebra `Λ(ℤ_p)`.
* `PadicMeasure.mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* ℤ_p[[T]]` — RJW Thm. 3.20.
* `PadicMeasure.mul_apply` — the convolution formula (RJW Rem. 3.11).
* `PadicMeasure.dirac_mul_dirac` — `δ_a * δ_b = δ_{a+b}` (`[a]·[b] = [a+b]`).
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- Multiplication of measures on `ℤ_p`, transported from `ℤ_p[[T]]` along the Mahler
transform. RJW Rem. 3.11: "by transport of structure we obtain such a structure on
`ℳ(ℤ_p, 𝒪_L)`". The convolution description is `PadicMeasure.mul_apply`. -/
noncomputable instance : Mul (PadicMeasure p ℤ_[p]) :=
  ⟨fun μ ν => (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν)⟩

/-- The unit measure: `δ_0` (whose Mahler transform is `(1+T)^0 = 1`). -/
noncomputable instance : One (PadicMeasure p ℤ_[p]) := ⟨dirac p 0⟩

lemma mul_def (μ ν : PadicMeasure p ℤ_[p]) :
    μ * ν = (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν) :=
  rfl

lemma one_def : (1 : PadicMeasure p ℤ_[p]) = dirac p 0 := rfl

/-- The Mahler transform is multiplicative: `𝓐_{μ·ν} = 𝓐_μ · 𝓐_ν`. -/
@[simp]
theorem mahlerTransform_mul (μ ν : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (μ * ν) = mahlerTransform p μ * mahlerTransform p ν := by
  rw [mul_def, ← mahlerLinearEquiv_apply, LinearEquiv.apply_symm_apply,
    mahlerLinearEquiv_apply, mahlerLinearEquiv_apply]

/-- `𝓐_{δ_0} = 1`. -/
@[simp]
theorem mahlerTransform_one : mahlerTransform p (1 : PadicMeasure p ℤ_[p]) = 1 := by
  rw [one_def, mahlerTransform_dirac, binomialSeries_zero]

@[simp]
theorem mahlerTransform_add (μ ν : PadicMeasure p ℤ_[p]) :
    mahlerTransform p (μ + ν) = mahlerTransform p μ + mahlerTransform p ν := by
  ext n; simp

@[simp]
theorem mahlerTransform_zero : mahlerTransform p (0 : PadicMeasure p ℤ_[p]) = 0 := by
  ext n; simp

/-- The Iwasawa algebra `Λ(ℤ_p) = ℳ(ℤ_p, ℤ_p)` as a commutative ring.

Source: RJW Rem. 3.11 (`RemarkConvolution`, TeX lines 907–911); ring laws are inherited
from `ℤ_p[[T]]` through the Mahler bijection. -/
noncomputable instance : CommRing (PadicMeasure p ℤ_[p]) where
  mul_assoc a b c := mahlerTransform_injective p (by simp [mul_assoc])
  one_mul a := mahlerTransform_injective p (by simp)
  mul_one a := mahlerTransform_injective p (by simp)
  left_distrib a b c := mahlerTransform_injective p (by simp [mul_add])
  right_distrib a b c := mahlerTransform_injective p (by simp [add_mul])
  zero_mul a := mahlerTransform_injective p (by simp)
  mul_zero a := mahlerTransform_injective p (by simp)
  mul_comm a b := mahlerTransform_injective p (by simp [mul_comm])

/-- **RJW Theorem 3.20 (`thm:mahler`)**: the Mahler transform is an isomorphism of
`ℤ_[p]`-algebras `ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L[[T]]` (here `𝒪 = ℤ_p`). -/
noncomputable def mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* PowerSeries ℤ_[p] :=
  { mahlerLinearEquiv p with
    map_mul' := mahlerTransform_mul p }

/-- The inner convolution integrand `x ↦ ∫ f(x+y) dν(y)`, as a continuous map.
Continuity comes from `ContinuousMap.curry` and the continuity of measures. -/
noncomputable def convInner (ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    C(ℤ_[p], ℤ_[p]) where
  toFun x := ν (f.comp ⟨fun y => x + y, by fun_prop⟩)
  continuous_toFun := by
    have key : ∀ x : ℤ_[p], f.comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p]))
        = (ContinuousMap.curry ⟨fun q : ℤ_[p] × ℤ_[p] => f (q.1 + q.2), by fun_prop⟩) x :=
      fun x => ContinuousMap.ext fun y => rfl
    simp only [key]
    exact (continuous p ν).comp (map_continuous _)

@[simp]
lemma convInner_apply (ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) (x : ℤ_[p]) :
    convInner p ν f x = ν (f.comp ⟨fun y => x + y, by fun_prop⟩) := rfl

/-- **The convolution formula** (RJW Rem. 3.11, TeX line 909):
`∫ φ d(μ*ν) = ∫ (∫ φ(x+y) dν(y)) dμ(x)`. Proved by checking Mahler coefficients
(Chu–Vandermonde: `binom(x+y, n) = ∑_{i+j=n} binom(x,i)·binom(y,j)`, mathlib's
`Ring.add_choose_eq`); injectivity of the Mahler transform extends the identity from
the Mahler basis to all continuous functions. -/
theorem mul_apply (μ ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    (μ * ν) f = μ (convInner p ν f) := by
  -- package the right-hand side as a measure
  set ρ : PadicMeasure p ℤ_[p] :=
    { toFun := fun f => μ (convInner p ν f)
      map_add' := fun f g => by
        have h : convInner p ν (f + g) = convInner p ν f + convInner p ν g :=
          ContinuousMap.ext fun x => by
            simp [ContinuousMap.add_comp]
        rw [h, map_add]
      map_smul' := fun c f => by
        have h : convInner p ν (c • f) = c • convInner p ν f :=
          ContinuousMap.ext fun x => by
            simp [ContinuousMap.smul_comp]
        rw [h, map_smul, RingHom.id_apply] } with hρ
  suffices h : μ * ν = ρ by rw [h]; rfl
  apply mahlerTransform_injective p
  ext n
  rw [mahlerTransform_mul, PowerSeries.coeff_mul, coeff_mahlerTransform]
  change _ = μ (convInner p ν (mahler n))
  -- Chu–Vandermonde on the Mahler basis
  have hcomp : ∀ x : ℤ_[p],
      (mahler n).comp (⟨fun y => x + y, by fun_prop⟩ : C(ℤ_[p], ℤ_[p]))
        = ∑ ij ∈ Finset.antidiagonal n,
            Ring.choose x ij.1 • (mahler ij.2 : C(ℤ_[p], ℤ_[p])) := by
    intro x
    ext y
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, mahler_apply,
      ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    exact Ring.add_choose_eq n (Commute.all x y)
  have key : convInner p ν (mahler n)
      = ∑ ij ∈ Finset.antidiagonal n,
          ν (mahler ij.2) • (mahler ij.1 : C(ℤ_[p], ℤ_[p])) := by
    ext x
    simp only [convInner_apply, hcomp x, map_sum, map_smul, smul_eq_mul,
      ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply]
    exact Finset.sum_congr rfl fun ij _ => by rw [mahler_apply, mul_comm]
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_smul, smul_eq_mul, coeff_mahlerTransform, coeff_mahlerTransform, mul_comm]

/-- `δ_a * δ_b = δ_{a+b}`: in Iwasawa-algebra notation, `[a]·[b] = [a+b]`.

Source: RJW Ex. 3.12 + Ex. 3.16 (Dirac measures correspond to group elements `[a]`,
and `(1+T)^a (1+T)^b = (1+T)^{a+b}` — mathlib's `binomialSeries_add`). -/
@[simp]
theorem dirac_mul_dirac (a b : ℤ_[p]) :
    dirac p a * dirac p b = dirac p (a + b) := by
  apply mahlerTransform_injective p
  rw [mahlerTransform_mul, mahlerTransform_dirac, mahlerTransform_dirac,
    mahlerTransform_dirac, binomialSeries_add]

end PadicMeasure
