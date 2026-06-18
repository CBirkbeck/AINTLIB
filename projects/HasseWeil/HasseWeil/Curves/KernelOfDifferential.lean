/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Differentials
import HasseWeil.GapQfKernel
import HasseWeil.EC.IsogenyAG.DualReduction

/-!
# The kernel of `d` and the image of an inseparable pullback (ticket G1)

Silverman II.2.12's *existence input*: over a perfect field of characteristic `p`, the
kernel of the universal derivation on the function field of an elliptic curve is exactly
the subfield of `p`-th powers, and consequently the pullback image of every **inseparable**
isogeny lands in `K(E)^p`.

The kernel computation itself (`ker d = K(E)^p`) is the already-shipped
`kaehlerD_eq_zero_iff_mem_pth_powers` (`GapQfKernel.lean`, built from
`finrank_KE_over_frobeniusRange_p : [K(E) : K(E)ᵖ] = p` and `kaehlerD_ne_zero`); this file
restates it in subfield form and derives the G1 payoff:

* **Basic world** (`HasseWeil.Isogeny`, where `IsSeparable = Algebra.IsSeparable`):
  `¬ α.IsSeparable` forces `omegaPullbackCoeff W α = 0`
  (`isSeparable_iff_omegaPullbackCoeff_ne_zero`, Silverman II.4.2(c)), hence the induced
  map on the one-dimensional `Ω[K(E)/F]` vanishes identically, hence `d ∘ α* = 0`, hence
  `Im(α*) ⊆ K(E)^p` by the kernel computation.
* **EC world** (`HasseWeil.EC.Isogeny`, where `IsSeparable` is `deg_i = 1`): the same
  conclusion, via the bridge `Algebra.IsSeparable → deg_i = 1` (using the unconditional
  finite-dimensionality `isogeny_finiteDimensional` through a pullback-only repackaging).
* **The II.2.12 wiring** (`EC/IsogenyAG/DualReduction.lean`): over `𝔽_q` the single
  `p`-step gives the inseparability data `Im(φ*) ⊆ Im(π*)` whenever `q = p` is prime
  (`pullback_range_le_frobeniusPower_one_of_not_isSeparable`), and the **iteration
  skeleton** `frobeniusFactorization_of_qStep` upgrades any such single `q`-step to the
  full `FrobeniusFactorization` predicate by strong induction on the degree. Over a prime
  field the two combine into the unconditional `frobeniusFactorization_of_card_eq_prime`.

## Honest scope (the G2 dependency)

Over `𝔽_q` with `q = pᵃ`, `a > 1`, the single step only gives `Im(φ*) ⊆ K(E)^p`, which is
*weaker* than the `q`-step `Im(φ*) ⊆ K(E)^q` required by the same-curve `frobeniusPower`
factorization: iterating the `p`-step passes through the cross-curve Frobenius twist
`E^{(p)} ≠ E` (the `p`-power relative Frobenius), which the project does not have — see
the "general `p^k` twist gap" in `DualReduction.lean` and the witness-parametric
`Conditional.mulByNat_p_factors_through_frobenius_of_witnesses` (`Curves/Maps.lean`).
Building that cross-curve `p`-power Frobenius is **ticket G2**; once its single `q`-step
`hstep` is available for composite `q`, `frobeniusFactorization_of_qStep` here closes
II.2.12 existence for it with no further work.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.11–2.12, II.4.2(c).
-/

open WeierstrassCurve

namespace HasseWeil

/-! ### The Basic world: `ker d = K(E)^p` in subfield form, and inseparable images -/

section BasicWorld

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

omit [DecidableEq F] in
/-- **`ker d = K(E)^p` in subfield form** (G1 main lemma, restated): over a perfect base
of characteristic `p`, a function has vanishing differential iff it lies in the subfield
`K(E)^p = (frobenius K(E) p).fieldRange` of `p`-th powers. Wrapper around the shipped
`kaehlerD_eq_zero_iff_mem_pth_powers`. -/
theorem kaehlerD_eq_zero_iff_mem_frobenius_fieldRange (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectField F] (w : KE) :
    haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    (KaehlerDifferential.D F KE w = 0 ↔ w ∈ (frobenius KE p).fieldRange) := by
  letI : DecidableEq F := Classical.decEq F
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  rw [kaehlerD_eq_zero_iff_mem_pth_powers W p w]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [frobenius_def]; exact hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg, frobenius_def]⟩

/-- **An inseparable isogeny kills all differentials**: if `α` is not separable, the
induced additive map `α.pullbackKaehler` on the one-dimensional `Ω[K(E)/F]` is
identically zero. From `isSeparable_iff_omegaPullbackCoeff_ne_zero` (II.4.2(c)) and the
`α`-semilinearity of `pullbackKaehler` against `kaehler_rank_one`. -/
theorem pullbackKaehler_eq_zero_of_not_isSeparable (α : Isogeny W.toAffine W.toAffine)
    (h : ¬α.IsSeparable) (η : KaehlerDifferential F KE) :
    α.pullbackKaehler η = 0 := by
  have hcoeff : omegaPullbackCoeff W α = 0 := by
    by_contra hne
    exact h ((isSeparable_iff_omegaPullbackCoeff_ne_zero W α).mpr hne)
  have hω : α.pullbackKaehler (invariantDifferential W.toAffine) = 0 := by
    rw [Isogeny.pullbackKaehler_invariantDifferential, hcoeff, zero_smul]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine) η
  rw [← ha, Isogeny.pullbackKaehler_smul_KE, hω, smul_zero]

/-- **`d ∘ α* = 0` for inseparable `α`**: the differential of every pullback vanishes. -/
theorem kaehlerD_pullback_eq_zero_of_not_isSeparable (α : Isogeny W.toAffine W.toAffine)
    (h : ¬α.IsSeparable) (f : KE) :
    KaehlerDifferential.D F KE (α.pullback f) = 0 := by
  rw [← Isogeny.pullbackKaehler_D]
  exact pullbackKaehler_eq_zero_of_not_isSeparable W α h _

/-- **G1 corollary (Basic world, element form)**: the pullback image of an inseparable
isogeny consists of `p`-th powers — `Im(α*) ⊆ K(E)^p` (Silverman II.2.12's existence
input, single `p`-step). -/
theorem pullback_mem_pth_powers_of_not_isSeparable (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectField F] (α : Isogeny W.toAffine W.toAffine) (h : ¬α.IsSeparable) (f : KE) :
    ∃ g : KE, g ^ p = α.pullback f :=
  (kaehlerD_eq_zero_iff_mem_pth_powers W p _).mp
    (kaehlerD_pullback_eq_zero_of_not_isSeparable W α h f)

/-- **G1 corollary (Basic world, subfield form)**: `Im(α*) ⊆ K(E)^p` as an inclusion of
subfields of `K(E)`. -/
theorem pullback_fieldRange_le_frobenius_fieldRange_of_not_isSeparable (p : ℕ)
    [Fact p.Prime] [CharP F p] [PerfectField F] (α : Isogeny W.toAffine W.toAffine)
    (h : ¬α.IsSeparable) :
    haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
    α.pullback.toRingHom.fieldRange ≤ (frobenius KE p).fieldRange := by
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap F KE).injective p
  rintro _ ⟨f, rfl⟩
  obtain ⟨g, hg⟩ := pullback_mem_pth_powers_of_not_isSeparable W p α h f
  exact ⟨g, by rw [frobenius_def]; exact hg⟩

end BasicWorld

namespace EC

/-! ### The EC world: the separability bridge and the inseparable-image inclusion -/

section Bridge

variable {K : Type*} [Field K] {V : WeierstrassCurve.Affine K} [V.IsElliptic]

/-- **Positivity of the EC-isogeny degree**: `0 < deg φ`, unconditionally. Transport of
the Basic-world `isogeny_degree_pos` through a pullback-only repackaging (the point-map
field of the Basic structure is irrelevant to the function-field degree). -/
theorem Isogeny.degree_pos (φ : Isogeny V V) : 0 < φ.degree := by
  letI : DecidableEq K := Classical.decEq K
  exact isogeny_degree_pos V ⟨φ.toCurveMap.pullback, 0⟩

/-- **The separability bridge (EC ← algebra)**: if the pullback algebra of `φ` is
separable in the `Algebra.IsSeparable` sense, then `φ` is separable in the EC sense
(`deg_i φ = 1`). Uses `Field.finSepDegree_eq_finrank_of_isSeparable` and the
unconditional degree positivity. -/
theorem Isogeny.isSeparable_of_algebra_isSeparable (φ : Isogeny V V)
    (hsep : @Algebra.IsSeparable V.FunctionField V.FunctionField _ _
      φ.toCurveMap.toAlgebra) :
    φ.IsSeparable := by
  letI : Algebra V.FunctionField V.FunctionField := φ.toCurveMap.toAlgebra
  haveI : Algebra.IsSeparable V.FunctionField V.FunctionField := hsep
  have heq : φ.toCurveMap.separableDegree = φ.toCurveMap.degree :=
    Field.finSepDegree_eq_finrank_of_isSeparable V.FunctionField V.FunctionField
  have hpos : 0 < φ.toCurveMap.degree := φ.degree_pos
  change φ.toCurveMap.degree / φ.toCurveMap.separableDegree = 1
  rw [heq]
  exact Nat.div_self hpos

/-- **G1 corollary (EC world)**: the pullback image of an inseparable EC-isogeny consists
of `p`-th powers — `Im(φ*) ⊆ K(E)^p` (Silverman II.2.12's existence input for the
`DualReduction` factorization). -/
theorem Isogeny.pullback_mem_pth_powers_of_not_isSeparable (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K] (φ : Isogeny V V) (h : ¬φ.IsSeparable)
    (f : V.FunctionField) :
    ∃ g : V.FunctionField, g ^ p = φ.toCurveMap.pullback f := by
  letI : DecidableEq K := Classical.decEq K
  have hα : ¬(⟨φ.toCurveMap.pullback, 0⟩ : HasseWeil.Isogeny V V).IsSeparable := fun hs ↦
    h (φ.isSeparable_of_algebra_isSeparable hs)
  exact HasseWeil.pullback_mem_pth_powers_of_not_isSeparable V p
    ⟨φ.toCurveMap.pullback, 0⟩ hα f

end Bridge

/-! ### The II.2.12 wiring: single step and the iteration skeleton -/

section SingleStep

variable {K : Type*} [Field K] [Fintype K] {V : WeierstrassCurve.Affine K} [V.IsElliptic]

/-- **The single-step inseparability data over a prime field** (`q = p`): an inseparable
isogeny has `Im(φ*) ⊆ Im(π*)` — exactly the `r = 1` instance of the `hincl` hypothesis of
`Isogeny.separablePart` (`DualReduction.lean`). -/
theorem Isogeny.pullback_range_le_frobeniusPower_one_of_not_isSeparable (p : ℕ)
    [Fact p.Prime] [CharP K p] (hcard : Fintype.card K = p) (φ : Isogeny V V)
    (h : ¬φ.IsSeparable) :
    φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V 1).toCurveMap.pullback.range := by
  refine φ.rangeIncl_frobeniusPower_of_pow_roots 1 fun z ↦ ?_
  rw [hcard, pow_one]
  exact φ.pullback_mem_pth_powers_of_not_isSeparable p h z

/-- Factoring through `π⁰ = id` recovers `φ`. -/
theorem Isogeny.separablePart_zero_eq (φ : Isogeny V V)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V 0).toCurveMap.pullback.range) :
    φ.separablePart 0 hincl = φ := by
  refine Isogeny.ext_toCurveMap (Curves.CurveMap.ext (AlgHom.ext fun z ↦ ?_))
  have h := φ.separablePart_pullback_pow 0 hincl z
  rwa [pow_zero, pow_one] at h

/-- The two-stage factorization computes the `q^(r+1)`-th power back to `φ*`:
`((φ_sep₁)_sep_r)* z ^ (q^(r+1)) = φ* z`. -/
theorem Isogeny.separablePart_separablePart_pullback_pow (φ : Isogeny V V)
    (hincl1 : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V 1).toCurveMap.pullback.range) (r : ℕ)
    (hincl' : (φ.separablePart 1 hincl1).toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V r).toCurveMap.pullback.range)
    (z : V.FunctionField) :
    ((φ.separablePart 1 hincl1).separablePart r hincl').toCurveMap.pullback z
        ^ Fintype.card K ^ (r + 1) =
      φ.toCurveMap.pullback z := by
  rw [pow_succ, pow_mul, (φ.separablePart 1 hincl1).separablePart_pullback_pow r hincl' z]
  have h1 := φ.separablePart_pullback_pow 1 hincl1 z
  rwa [pow_one] at h1

/-- If the one-step separable part factors through `πʳ`, then `φ` factors through
`π^(r+1)` — the inclusion-chaining step of the iteration. -/
theorem Isogeny.rangeIncl_succ_of_separablePart (φ : Isogeny V V)
    (hincl1 : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V 1).toCurveMap.pullback.range) (r : ℕ)
    (hincl' : (φ.separablePart 1 hincl1).toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V r).toCurveMap.pullback.range) :
    φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V (r + 1)).toCurveMap.pullback.range := by
  rintro _ ⟨z, rfl⟩
  rw [Isogeny.mem_frobeniusPower_pullback_range_iff]
  exact ⟨((φ.separablePart 1 hincl1).separablePart r hincl').toCurveMap.pullback z,
    φ.separablePart_separablePart_pullback_pow hincl1 r hincl' z⟩

/-- **Coherence of iterated separable parts**: factoring `φ` through `π^(r+1)` in one go
agrees with factoring the one-step part through `πʳ` (pullback-injectivity of `πʳ⁺¹`). -/
theorem Isogeny.separablePart_succ_eq (φ : Isogeny V V)
    (hincl1 : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V 1).toCurveMap.pullback.range) (r : ℕ)
    (hincl' : (φ.separablePart 1 hincl1).toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V r).toCurveMap.pullback.range)
    (hincl'' : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower V (r + 1)).toCurveMap.pullback.range) :
    φ.separablePart (r + 1) hincl'' = (φ.separablePart 1 hincl1).separablePart r hincl' := by
  refine Isogeny.ext_toCurveMap (Curves.CurveMap.ext (AlgHom.ext fun z ↦ ?_))
  apply (Isogeny.frobeniusPower V (r + 1)).pullback_injective
  rw [Isogeny.frobeniusPower_pullback, Isogeny.frobeniusPower_pullback,
    φ.separablePart_pullback_pow (r + 1) hincl'' z,
    φ.separablePart_separablePart_pullback_pow hincl1 r hincl' z]

end SingleStep

section IterationSkeleton

variable {K : Type*} [Field K] [Fintype K]

/-- **The II.2.12 iteration skeleton** (Silverman II.2.12, induction on the degree): if
every inseparable isogeny `E → E` carries the single `q`-step inseparability data
`Im(φ*) ⊆ Im(π*)`, then every isogeny factors through some `πʳ` with separable quotient —
the full `FrobeniusFactorization` predicate of `DualReduction.lean`.

The hypothesis `hstep` is a theorem over a prime field
(`pullback_range_le_frobeniusPower_one_of_not_isSeparable`); for composite `q = pᵃ` it is
the **G2 dependency** (the cross-curve `p`-power relative Frobenius through the twist
`E^{(p)}`), cf. the module docstring. -/
theorem frobeniusFactorization_of_qStep (V : WeierstrassCurve.Affine K) [V.IsElliptic]
    (hstep : ∀ φ : Isogeny V V, ¬φ.IsSeparable →
      φ.toCurveMap.pullback.range ≤
        (Isogeny.frobeniusPower V 1).toCurveMap.pullback.range) :
    FrobeniusFactorization V := by
  have main : ∀ (n : ℕ) (φ : Isogeny V V), φ.degree ≤ n →
      ∃ (r : ℕ) (hincl : φ.toCurveMap.pullback.range ≤
        (Isogeny.frobeniusPower V r).toCurveMap.pullback.range),
        (φ.separablePart r hincl).IsSeparable := by
    intro n
    induction n with
    | zero =>
      intro φ hdeg
      have := φ.degree_pos
      omega
    | succ n ih =>
      intro φ hdeg
      by_cases hsep : φ.IsSeparable
      · -- Separable: factor through `π⁰ = id`.
        have hincl0 : φ.toCurveMap.pullback.range ≤
            (Isogeny.frobeniusPower V 0).toCurveMap.pullback.range := by
          rintro _ ⟨z, rfl⟩
          rw [Isogeny.mem_frobeniusPower_pullback_range_iff]
          exact ⟨φ.toCurveMap.pullback z, by rw [pow_zero, pow_one]; rfl⟩
        refine ⟨0, hincl0, ?_⟩
        rw [φ.separablePart_zero_eq hincl0]
        exact hsep
      · -- Inseparable: peel one Frobenius via `hstep` and recurse on the smaller degree.
        have hincl1 := hstep φ hsep
        have hdψ : (φ.separablePart 1 hincl1).degree ≤ n := by
          have h1 := φ.degree_eq_pow_mul_separablePart_degree 1 hincl1
          rw [pow_one] at h1
          have h2 : 2 * (φ.separablePart 1 hincl1).degree ≤
              Fintype.card K * (φ.separablePart 1 hincl1).degree :=
            Nat.mul_le_mul_right _ Fintype.one_lt_card
          have h3 := (φ.separablePart 1 hincl1).degree_pos
          omega
        obtain ⟨r, hincl', hsep'⟩ := ih (φ.separablePart 1 hincl1) hdψ
        refine ⟨r + 1, φ.rangeIncl_succ_of_separablePart hincl1 r hincl', ?_⟩
        rw [φ.separablePart_succ_eq hincl1 r hincl']
        exact hsep'
  intro φ
  exact main φ.degree φ le_rfl

/-- **Silverman II.2.12 existence over a prime field** (`#K = p`): the
`FrobeniusFactorization` predicate holds unconditionally — every isogeny `E → E` over
`𝔽_p` factors as a separable isogeny after a power of Frobenius. Combines the single
`p`-step (from `ker d = K(E)^p`) with the iteration skeleton. -/
theorem frobeniusFactorization_of_card_eq_prime (p : ℕ) [Fact p.Prime] [CharP K p]
    (hcard : Fintype.card K = p) (V : WeierstrassCurve.Affine K) [V.IsElliptic] :
    FrobeniusFactorization V :=
  frobeniusFactorization_of_qStep V fun φ h ↦
    φ.pullback_range_le_frobeniusPower_one_of_not_isSeparable p hcard h

end IterationSkeleton

end EC

end HasseWeil
