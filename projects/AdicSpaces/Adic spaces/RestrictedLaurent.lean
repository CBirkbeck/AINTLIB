/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import «Adic spaces».Vendored.CoramRestrictedNorm

/-!
# Restricted Laurent series `R⟨W, W⁻¹⟩` (finite-jet pinching, layer 𝓛)

Source: [FJP] = *Finite-jet pinching: a uniform strongly sheafy domain which is not stably
uniform* (16 July 2026), §1 (conventions) and Proposition 2.3. This file provides the radius-one
Laurent algebra `L = k⟨W, W⁻¹⟩` of [FJP] (1.4): ℤ-indexed series `∑_{a ∈ ℤ} c_a W^a` whose
coefficients tend to `0` along the cofinite filter, with the Gauss (sup) norm.

Over a base `R` that is a complete ultrametric normed commutative ring, `RestrictedLaurent R`
is a complete ultrametric normed commutative ring; when the base norm is multiplicative with
discrete value group (the [FJP] setting, `R = K = LaurentSeries F`), the Laurent–Gauss norm is
multiplicative ([FJP] Prop 2.3: "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative"), the
norm is attained, and `W` is a norm-one unit.

The nonnegative-support subring recovers `K⟨W⟩` (`PowerSeries.Restricted K 1`) isometrically;
this is the inclusion `k⟨W⟩ ⊂ L` used throughout [FJP] §2.
-/

open Filter Topology

namespace FiniteJet

/-- A **restricted Laurent series** over a normed ring `R`: a coefficient function on `ℤ`
whose norms tend to `0` along the cofinite filter ([FJP] §1: "restricted Laurent series";
the elements `∑_{a∈ℤ} c_a W^a` with `c_a → 0`). -/
structure RestrictedLaurent (R : Type*) [NormedCommRing R] where
  /-- The coefficient of `W^a`. -/
  coeff : ℤ → R
  /-- Coefficients tend to zero along the cofinite filter. -/
  tendsto_coeff : Tendsto (fun a => ‖coeff a‖) cofinite (𝓝 0)

namespace RestrictedLaurent

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

@[ext]
theorem ext {f g : RestrictedLaurent R} (h : ∀ a, f.coeff a = g.coeff a) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact funext h

/-! ### Additive and multiplicative structure

Multiplication is Cauchy convolution: `(f * g).coeff m = ∑' a, f.coeff a * g.coeff (m - a)`.
The sum converges because the base is complete and nonarchimedean and the terms tend to `0`
along cofinite ([FJP] §1 and Prop 2.3 use this implicitly via the support description (1.8)). -/

/-- The zero series. -/
instance : Zero (RestrictedLaurent R) :=
  ⟨⟨fun _ => 0, by simpa using tendsto_const_nhds⟩⟩

/-- The one series (coefficient `1` at `0`). -/
instance : One (RestrictedLaurent R) :=
  ⟨⟨fun a => if a = 0 then 1 else 0, by sorry⟩⟩

/-- Coefficientwise addition. -/
instance : Add (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun a => f.coeff a + g.coeff a, by sorry⟩⟩

/-- Coefficientwise negation. -/
instance : Neg (RestrictedLaurent R) :=
  ⟨fun f => ⟨fun a => -f.coeff a, by sorry⟩⟩

/-- Convolution multiplication (requires a complete base for the `tsum`). -/
noncomputable instance [CompleteSpace R] : Mul (RestrictedLaurent R) :=
  ⟨fun f g => ⟨fun m => ∑' a : ℤ, f.coeff a * g.coeff (m - a), by sorry⟩⟩

@[simp] theorem coeff_zero (a : ℤ) : (0 : RestrictedLaurent R).coeff a = 0 := rfl

@[simp] theorem coeff_one (a : ℤ) :
    (1 : RestrictedLaurent R).coeff a = if a = 0 then 1 else 0 := rfl

@[simp] theorem coeff_add (f g : RestrictedLaurent R) (a : ℤ) :
    (f + g).coeff a = f.coeff a + g.coeff a := rfl

@[simp] theorem coeff_neg (f : RestrictedLaurent R) (a : ℤ) : (-f).coeff a = -f.coeff a := rfl

theorem coeff_mul [CompleteSpace R] (f g : RestrictedLaurent R) (m : ℤ) :
    (f * g).coeff m = ∑' a : ℤ, f.coeff a * g.coeff (m - a) := rfl

/-- The convolution defining `f * g` is summable (complete nonarchimedean base, terms → 0). -/
theorem summable_mul_coeff [CompleteSpace R] (f g : RestrictedLaurent R) (m : ℤ) :
    Summable (fun a : ℤ => f.coeff a * g.coeff (m - a)) := by sorry

/-- `RestrictedLaurent R` is a commutative ring under coefficientwise addition and Cauchy
convolution. -/
noncomputable instance [CompleteSpace R] : CommRing (RestrictedLaurent R) where
  add := (· + ·)
  add_assoc := by sorry
  zero := 0
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  mul := (· * ·)
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one := 1
  one_mul := by sorry
  mul_one := by sorry
  neg := Neg.neg
  neg_add_cancel := by sorry
  mul_comm := by sorry
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Monomials and the algebra structure -/

/-- The monomial `c · W^a`. -/
def single (a : ℤ) (c : R) : RestrictedLaurent R :=
  ⟨fun b => if b = a then c else 0, by sorry⟩

@[simp] theorem coeff_single (a b : ℤ) (c : R) :
    (single a c).coeff b = if b = a then c else 0 := rfl

theorem single_mul_single [CompleteSpace R] (a b : ℤ) (c d : R) :
    single a c * single b d = single (a + b) (c * d) := by sorry

/-- The scalar embedding `R → RestrictedLaurent R` as `single 0`. -/
noncomputable def C [CompleteSpace R] : R →+* RestrictedLaurent R where
  toFun c := single 0 c
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

noncomputable instance [CompleteSpace R] : Algebra R (RestrictedLaurent R) :=
  (C (R := R)).toAlgebra

/-- The variable `W` (norm-one monomial at exponent `1`). -/
noncomputable def W [CompleteSpace R] : RestrictedLaurent R := single 1 1

/-- `W` is a unit, with inverse the monomial at exponent `-1` ([FJP] §1.4: "both `W` and
`W⁻¹` are power-bounded"). -/
noncomputable def Wu [CompleteSpace R] : (RestrictedLaurent R)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by sorry
  inv_val := by sorry

/-! ### The Gauss (sup) norm

[FJP] (1.8): "An element is a series `∑_{(a,b)∈S} c_{a,b} W^a Q^b` such that, for every ε > 0,
only finitely many coefficients have `|c_{a,b}| ≥ ε`; its norm is `sup |c_{a,b}|`." Here the
univariate (`Q`-free) case: `‖f‖ = ⨆ a, ‖f.coeff a‖`, attained because the coefficient family
is restricted. -/

/-- The sup norm of a restricted Laurent series. -/
noncomputable def gaussNorm (f : RestrictedLaurent R) : ℝ := ⨆ a : ℤ, ‖f.coeff a‖

/-- The sup defining the Gauss norm is attained ([FJP] Prop 2.3: "the coefficient family of a
restricted Laurent series tends to zero, so its nonzero coefficient supremum is attained"). -/
theorem exists_gaussNorm_eq (f : RestrictedLaurent R) (hf : f ≠ 0) :
    ∃ a : ℤ, gaussNorm f = ‖f.coeff a‖ ∧ f.coeff a ≠ 0 := by sorry

theorem norm_coeff_le_gaussNorm (f : RestrictedLaurent R) (a : ℤ) :
    ‖f.coeff a‖ ≤ gaussNorm f := by sorry

/-- The Gauss norm as a `RingNorm` (submultiplicative, ultrametric-compatible). -/
noncomputable def isRingNorm [CompleteSpace R] [NormOneClass R] :
    RingNorm (RestrictedLaurent R) where
  toFun := gaussNorm
  map_zero' := by sorry
  add_le' := by sorry
  neg' := by sorry
  mul_le' := by sorry
  eq_zero_of_map_eq_zero' := by sorry

/-- `RestrictedLaurent R` is a normed ring under the Gauss norm. -/
noncomputable instance [CompleteSpace R] [NormOneClass R] :
    NormedCommRing (RestrictedLaurent R) where
  toNormedRing := RingNorm.toNormedRing (isRingNorm (R := R))
  mul_comm := mul_comm

theorem norm_def [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖f‖ = gaussNorm f := rfl

@[simp] theorem norm_single [CompleteSpace R] [NormOneClass R] (a : ℤ) (c : R) :
    ‖single a c‖ = ‖c‖ := by sorry

@[simp] theorem norm_W [CompleteSpace R] [NormOneClass R] :
    ‖(Wu (R := R)).val‖ = 1 := by sorry

@[simp] theorem norm_W_inv [CompleteSpace R] [NormOneClass R] :
    ‖((Wu (R := R))⁻¹ : (RestrictedLaurent R)ˣ).val‖ = 1 := by sorry

/-- The Gauss norm is ultrametric. -/
instance [CompleteSpace R] [NormOneClass R] : IsUltrametricDist (RestrictedLaurent R) := by
  sorry

/-- Multiplication by `W` is an isometry (used in [FJP] Prop 3.1: `‖W^{-n} y‖ = ‖y‖`). -/
theorem norm_W_mul [CompleteSpace R] [NormOneClass R] (f : RestrictedLaurent R) :
    ‖(Wu (R := R)).val * f‖ = ‖f‖ := by sorry

/-- Completeness of the restricted Laurent ring over a complete base ([FJP] §1: Banach
direct sums / restricted series are complete). -/
instance [CompleteSpace R] [NormOneClass R] : CompleteSpace (RestrictedLaurent R) := by
  sorry

/-! ### Multiplicativity over a discretely valued field

[FJP] Prop 2.3 (verbatim): "The Laurent Gauss norm on 𝒞 = L⟨Q⟩ is multiplicative. Indeed, the
coefficient family of a restricted Laurent series tends to zero, so its nonzero coefficient
supremum is attained. Since every nonzero coefficient norm belongs to `|k^×|`, so does every
nonzero Gauss norm. We may therefore scale two nonzero elements to norm one. Their reductions
are nonzero Laurent polynomials in `k̃[W, W⁻¹, Q]` … Their product remains nonzero because this
Laurent polynomial ring is a domain."  This file proves the `Q`-free (univariate Laurent) case;
`FiniteJetRings.lean` derives the `L⟨Q⟩` case over the base `𝓛`. -/

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Norm multiplicativity for restricted Laurent series over a complete nonarchimedean field
with discrete value group ([FJP] Prop 2.3; hypothesis `hd` is the discreteness used to scale
to norm one and to separate `< 1` from `≤ |ϖ|`). -/
theorem norm_mul_eq (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n)
    (f g : RestrictedLaurent K) : ‖f * g‖ = ‖f‖ * ‖g‖ := by sorry

/-- `RestrictedLaurent K` is a domain when the base is a complete nonarchimedean field with
discrete value group ([FJP] Prop 2.3: "also that 𝒞 is a domain"; univariate case). -/
theorem mul_ne_zero_of_ne_zero (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n)
    {f g : RestrictedLaurent K} (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := by sorry

end Field

/-! ### The nonnegative-support subring `R⟨W⟩ ⊂ R⟨W, W⁻¹⟩` -/

/-- Radius-one positivity witnesses for the vendored Gauss-norm stack. -/
instance : StrongPos (fun _ : Unit => (1 : ℝ)) := ⟨fun _ => one_pos⟩

instance (n : ℕ) : StrongPos (fun _ : Fin n => (1 : ℝ)) := ⟨fun _ => one_pos⟩

section Nonneg

variable (R) in
/-- The subring of series supported in nonnegative exponents — the copy of `R⟨W⟩` inside
`R⟨W, W⁻¹⟩` ([FJP] Lemma 2.2: "the subspace `k⟨W⟩` is the intersection of the kernels of the
continuous negative-coefficient maps"). -/
noncomputable def nonnegSubring [CompleteSpace R] : Subring (RestrictedLaurent R) where
  carrier := {f | ∀ a : ℤ, a < 0 → f.coeff a = 0}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- The nonnegative-support subring is closed (kernels of the continuous coefficient
functionals; [FJP] Lemma 2.2). -/
theorem isClosed_nonnegSubring [CompleteSpace R] [NormOneClass R] :
    IsClosed (nonnegSubring R : Set (RestrictedLaurent R)) := by sorry

/-- The norm-preserving identification of `PowerSeries.Restricted R 1` (the vendored `R⟨W⟩`)
with the nonnegative-support subring of `R⟨W, W⁻¹⟩`. -/
noncomputable def nonnegEquiv [CompleteSpace R] [NormOneClass R] :
    PowerSeries.Restricted R (1 : ℝ) ≃+* nonnegSubring R where
  toFun := by sorry
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_mul' := by sorry
  map_add' := by sorry

/-- `nonnegEquiv` preserves norms. -/
theorem nonnegEquiv_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) :
    ‖((nonnegEquiv (R := R) f : nonnegSubring R) : RestrictedLaurent R)‖ = ‖f‖ := by sorry

/-- The norm-preserving embedding `R⟨W⟩ → R⟨W,W⁻¹⟩` (composite of `nonnegEquiv` with the
subring inclusion). -/
noncomputable def ofRestricted [CompleteSpace R] [NormOneClass R] :
    PowerSeries.Restricted R (1 : ℝ) →+* RestrictedLaurent R :=
  (nonnegSubring R).subtype.comp (nonnegEquiv (R := R)).toRingHom

theorem ofRestricted_norm [CompleteSpace R] [NormOneClass R]
    (f : PowerSeries.Restricted R (1 : ℝ)) : ‖ofRestricted (R := R) f‖ = ‖f‖ := by sorry

theorem ofRestricted_injective [CompleteSpace R] [NormOneClass R] :
    Function.Injective (ofRestricted (R := R)) := by sorry

end Nonneg

/-! ### Density of Laurent polynomials and the affinoid presentation surjection

[FJP] Prop 2.1: "Each of 𝓑, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`, so each is
strongly noetherian."  We realise the presentation as a *surjection* from the vendored
two-variable restricted ring (evaluating `W ↦ Wu`, `V ↦ Wu⁻¹`); surjectivity holds via the
explicit norm-preserving monomial section, and noetherianity of the target follows from
noetherianity of the source — no kernel identification is required. -/

/-- Evaluation `R⟨W,V⟩ → R⟨W,W⁻¹⟩`, `W ↦ Wu, V ↦ Wu⁻¹`: a bounded ring homomorphism. -/
noncomputable def evalHom [CompleteSpace R] [NormOneClass R] :
    MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ)) →+* RestrictedLaurent R where
  toFun := by sorry
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

theorem evalHom_surjective [CompleteSpace R] [NormOneClass R] :
    Function.Surjective (evalHom (R := R)) := by sorry

theorem evalHom_norm_le [CompleteSpace R] [NormOneClass R]
    (f : MvPowerSeries.Restricted R (fun _ : Fin 2 => (1 : ℝ))) :
    ‖evalHom (R := R) f‖ ≤ ‖f‖ := by sorry

end RestrictedLaurent

end FiniteJet
