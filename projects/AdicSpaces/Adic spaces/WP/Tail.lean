/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Heads

/-!
# The tail decomposition and the twisted `c₀`-sum ([WP] §6.4)

The isometric Banach-decomposition `𝒜 ≅ ⊕̂^{c₀}_μ 𝒜_N e_μ` ([WP]
eq:tail-decomposition) is carried COEFFICIENTWISE: for each tail index `μ` the
`μ`-th component of `f ∈ 𝒜` is a head element (`tailCoeff`), the `μ = 0` component is
the norm-nonincreasing algebra retraction `ρ_N` ([WP] eq:head-retraction), and
multiplication obeys the twisted rule `e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`
([WP] eq:tail-multiplication).

The abstract receptacle is `TailC0`: for a normed ultrametric commutative ring `P`
and a "twist element" `ρ` of norm `≤ 1` (the image of `W`), the null families
`TailIdx N → P` with sup norm and `ρ`-twisted convolution.  Instances of `TailC0`
appear as: the model of every rational localization of `𝒜`
([WP] prop:coefficientwise-localization, cor:finite-head-presentation) and the bad
chart `ℬ` itself ([WP] §6.2 — the weighted norm of eq:weighted-chart-norm is exactly
the plain sup norm in the twisted coordinates).

The embedding `Φ : TailC0 → MvPowerSeries` ([WP] eq:formal-embedding,
`x ↦ ∑ ρ^{ω(μ)} x_μ U^μ`) is also defined here; it is multiplicative BECAUSE of the
twist and injective when `ρ` is regular, and serves both the reducedness theorem
([WP] thm:parity-rationally-reduced) and the domain property of the chart
([WP] prop:weighted-chart-domain-nonuniform).
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver Filter Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise tail decomposition of `𝒜` -/

/-- The `μ`-th tail coefficient of `f ∈ 𝒜`: the head element whose `h`-th coefficient
is the `(h + tailShift μ)`-th coefficient of `f` ([WP] eq:tail-decomposition, read
coefficientwise via the exponent splitting of `WP/Weight.lean`). -/
noncomputable def tailCoeff (μ : TailIdx N) (f : WPA K w) : WPHead K w N := by sorry

@[simp] theorem coeffA_tailCoeff (μ : TailIdx N) (f : WPA K w) {h : ℕ →₀ ℕ}
    (hh : HeadMem w N h) :
    MvPowerSeries.coeff h (tailCoeff K w N μ f).1.1 =
      coeffA K w (h + tailShift w μ) f := by sorry

theorem tailCoeff_add (μ : TailIdx N) (f g : WPA K w) :
    tailCoeff K w N μ (f + g) = tailCoeff K w N μ f + tailCoeff K w N μ g := by sorry

theorem norm_tailCoeff_le (μ : TailIdx N) (f : WPA K w) :
    ‖tailCoeff K w N μ f‖ ≤ ‖f‖ := by sorry

/-- The tail coefficients of a fixed element form a null family ([WP]
eq:tail-decomposition: the decomposition is a `c₀`-sum). -/
theorem tendsto_norm_tailCoeff_cofinite (f : WPA K w) :
    Tendsto (fun μ : TailIdx N => ‖tailCoeff K w N μ f‖) cofinite (𝓝 0) := by sorry

theorem norm_eq_iSup_tailCoeff (f : WPA K w) :
    ‖f‖ = ⨆ μ : TailIdx N, ‖tailCoeff K w N μ f‖ := by sorry

/-- Separation: an element of `𝒜` is determined by its tail coefficients. -/
theorem tailCoeff_injective :
    Function.Injective (fun (f : WPA K w) (μ : TailIdx N) => tailCoeff K w N μ f) := by
  sorry

/-- The `e_μ` basis element `W^{ω(μ)} U^μ` of `𝒜` ([WP] eq:tail-basis). -/
noncomputable def eTail (μ : TailIdx N) : WPA K w :=
  wpMonomial K w (wpMem_tailShift w μ) 1

@[simp] theorem tailCoeff_headIncl_mul_eTail (μ ν : TailIdx N) (x : WPHead K w N) :
    tailCoeff K w N ν (headIncl K w N x * eTail K w N μ) =
      if ν = μ then x else 0 := by sorry

/-- The head retraction `ρ_N` — the `μ = 0` tail coefficient — is a ring homomorphism
([WP] eq:head-retraction: "Projection to the coefficient of `e_0` is a
norm-nonincreasing algebra retraction"). -/
noncomputable def rhoHead : WPA K w →+* WPHead K w N := by sorry

@[simp] theorem rhoHead_apply (f : WPA K w) :
    rhoHead K w N f = tailCoeff K w N 0 f := by sorry

@[simp] theorem rhoHead_headIncl (x : WPHead K w N) :
    rhoHead K w N (headIncl K w N x) = x := by sorry

theorem norm_rhoHead_le (f : WPA K w) : ‖rhoHead K w N f‖ ≤ ‖f‖ := by sorry

/-- The variable `W` as a head element. -/
noncomputable def WaHead : WPHead K w N := by sorry

@[simp] theorem headIncl_WaHead : headIncl K w N (WaHead K w N) = Wa K w := by sorry

/-- **The twisted multiplication rule** ([WP] eq:tail-multiplication:
`e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}`; the excess exponent is `≥ 0` by
subadditivity of `ω`). -/
theorem eTail_mul (μ ν : TailIdx N) :
    eTail K w N μ * eTail K w N ν =
      headIncl K w N (WaHead K w N ^
          (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) *
        eTail K w N (μ + ν) := by sorry

/-! ### The twisted `c₀`-sum `TailC0` -/

/-- A twist element: a norm-`≤ 1` element of a normed ring (the image of `W`).
Norm `≤ 1` is what keeps the twisted convolution submultiplicative and `c₀`-valued. -/
structure TwistElem (P : Type*) [NormedCommRing P] where
  /-- The underlying element. -/
  val : P
  /-- The twist element lies in the unit ball. -/
  norm_le_one : ‖val‖ ≤ 1

/-- The twisted `c₀`-sum `⊕̂^{c₀}_μ P e_μ` ([WP] eq:tail-decomposition's receptacle):
null families `TailIdx N → P` with sup norm and `ρ`-twisted convolution
`(x*y)_τ = ∑_{μ+λ=τ} ρ^{ω(μ)+ω(λ)−ω(τ)} x_μ y_λ` (the weight `w` enters through the
twist exponents, so it is a genuine parameter of the ring structure). -/
def TailC0 (w : ℕ → ℕ) (N : ℕ) (P : Type*) [NormedCommRing P] [IsUltrametricDist P]
    (ρ : TwistElem P) : Type _ :=
  have _ := w
  have _ := ρ
  {x : TailIdx N → P // Tendsto (fun μ => ‖x μ‖) cofinite (𝓝 0)}

namespace TailC0

variable {w : ℕ → ℕ} {N : ℕ} {P : Type*} [NormedCommRing P] [IsUltrametricDist P]
  {ρ : TwistElem P}

noncomputable instance : CommRing (TailC0 w N P ρ) := by sorry

noncomputable instance : NormedCommRing (TailC0 w N P ρ) := by sorry

instance : IsUltrametricDist (TailC0 w N P ρ) := by sorry

instance [CompleteSpace P] : CompleteSpace (TailC0 w N P ρ) := by sorry

instance [NormOneClass P] [Nontrivial P] : NormOneClass (TailC0 w N P ρ) := by sorry

/-- The coefficient of a twisted `c₀`-family. -/
def coeff (μ : TailIdx N) (x : TailC0 w N P ρ) : P := x.1 μ

/-- The single-index family `p·e_μ`. -/
noncomputable def single (μ : TailIdx N) (p : P) : TailC0 w N P ρ := by
  sorry

@[simp] theorem coeff_single (μ ν : TailIdx N) (p : P) :
    coeff ν (single (w := w) (ρ := ρ) μ p) = if ν = μ then p else 0 := by sorry

/-- The twisted product of single families ([WP] eq:tail-multiplication in the
abstract model): `(p·e_μ)(q·e_ν) = ρ^{ω(μ)+ω(ν)−ω(μ+ν)}·pq·e_{μ+ν}`. -/
theorem single_mul_single (μ ν : TailIdx N) (p q : P) :
    single (w := w) (ρ := ρ) μ p * single (w := w) (ρ := ρ) ν q =
      single (w := w) (ρ := ρ) (μ + ν)
        (ρ.val ^ (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1) * (p * q)) := by
  sorry

theorem norm_eq_iSup_coeff (x : TailC0 w N P ρ) :
    ‖x‖ = ⨆ μ : TailIdx N, ‖coeff μ x‖ := by sorry

/-- The head inclusion `P → TailC0` at `μ = 0` is an isometric ring homomorphism. -/
noncomputable def ofHead : P →+* TailC0 w N P ρ := by sorry

@[simp] theorem norm_ofHead (p : P) :
    ‖ofHead (w := w) (N := N) (ρ := ρ) p‖ = ‖p‖ := by sorry

/-- The head projection `TailC0 → P` at `μ = 0` is a norm-nonincreasing ring
homomorphism splitting `ofHead`. -/
noncomputable def toHead : TailC0 w N P ρ →+* P := by sorry

@[simp] theorem toHead_ofHead (p : P) :
    toHead (ofHead (w := w) (N := N) (ρ := ρ) p) = p := by
  sorry

end TailC0

/-! ### The formal-series embedding `Φ` ([WP] eq:formal-embedding) -/

/-- The tail variable type `{n : ℕ // N < n}` — the `U_n`, `n > N`. -/
def TailVar (N : ℕ) : Type := {n : ℕ // N < n}

/-- Tail indices are finitely supported exponent vectors on the tail variables. -/
noncomputable def tailIdxEquivFinsupp : TailIdx N ≃ (TailVar N →₀ ℕ) := by sorry

variable {P : Type*} [NormedCommRing P] [IsUltrametricDist P]

/-- **The formal-series embedding** `Φ : TailC0 → ℱ_J(P) = MvPowerSeries J P`,
`Φ(∑ x_μ e_μ) = ∑ ρ^{ω(μ)} x_μ U^μ` ([WP] eq:formal-embedding).  Multiplicative
because the `ρ`-powers absorb the twist (eq:tail-multiplication); it forgets the
topology (the target is the full formal product). -/
noncomputable def tailC0ToMvPowerSeries (w : ℕ → ℕ) (N : ℕ) (ρ : TwistElem P) :
    TailC0 w N P ρ →+* MvPowerSeries (TailVar N) P := by sorry

/-- `Φ` is injective when the twist element is regular
([WP] thm:parity-rationally-reduced: "The `W`-regularity of `P` then gives
`x_μ = 0`"). -/
theorem tailC0ToMvPowerSeries_injective (ρ : TwistElem P)
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    Function.Injective (tailC0ToMvPowerSeries w N ρ) := by sorry

/-- Reducedness descends through `Φ` ([WP] thm:parity-rationally-reduced, final
step; with `WP/Reduced.lean`'s `IsReduced (MvPowerSeries J P)`). -/
theorem isReduced_tailC0 (ρ : TwistElem P) [IsReduced P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsReduced (TailC0 w N P ρ) := by sorry

/-- Domain-ness descends through `Φ` (used for the bad chart ℬ,
[WP] prop:weighted-chart-domain-nonuniform; with mathlib's
`NoZeroDivisors (MvPowerSeries σ R)`). -/
theorem isDomain_tailC0 (ρ : TwistElem P) [IsDomain P]
    (hρ : ∀ x : P, ρ.val * x = 0 → x = 0) :
    IsDomain (TailC0 w N P ρ) := by sorry

end WeightedParity
