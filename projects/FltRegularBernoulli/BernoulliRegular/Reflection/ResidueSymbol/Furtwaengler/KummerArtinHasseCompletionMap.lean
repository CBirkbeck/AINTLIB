module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHassePadicBase
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# The rational `p`-adic map into the lambda completion

This file proves the valuation-comparison input needed to extend the rational
map `ℚ → K` to completions.  The comparison is concrete: the cyclotomic
`lambda` prime lies over `(p)`, so the lambda valuation on `K`, restricted to
`ℚ`, is equivalent to the rational `p`-adic valuation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped NumberField TensorProduct Topology WithZero

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The `Nat.Primes` object attached to the current rational prime `p`. -/
abbrev lambdaPadicPrime : Nat.Primes :=
  ⟨p, Fact.out⟩

@[simp]
theorem lambdaPadicPrime_val : (lambdaPadicPrime p).1 = p :=
  rfl

/-- The `p`-adic field indexed by a bundled prime.  This avoids asking typeclass
search for a separate `Fact` while casting between bundled rational primes. -/
abbrev PadicOfPrime (q : Nat.Primes) : Type :=
  @Padic q.1 ⟨q.2⟩

/-- Integer membership in the cyclotomic `lambda` prime is exactly membership
in the rational prime `(p)`. -/
theorem intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal (n : ℤ) :
    algebraMap ℤ (𝓞 K) n ∈ zetaPrime p K ↔
      n ∈ lambdaRationalPrimeIdeal p := by
  letI : (zetaPrime p K).LiesOver (lambdaRationalPrimeIdeal p) :=
    zetaPrime_liesOver_lambdaRationalPrimeIdeal (p := p) (K := K)
  simpa using
    (Ideal.mem_of_liesOver (A := ℤ) (B := 𝓞 K)
      (P := zetaPrime p K) (p := lambdaRationalPrimeIdeal p) n).symm

/-- The rational `p`-adic valuation detects exactly whether the denominator
is prime to `(p)`. -/
theorem lambdaRationalValuation_le_one_iff_den (x : ℚ) :
    (lambdaRationalHeightOneSpectrum p).valuation ℚ x ≤ 1 ↔
      (x.den : ℤ) ∉ lambdaRationalPrimeIdeal p := by
  simpa [lambdaRationalHeightOneSpectrum_asIdeal, lambdaRationalPrimeIdeal] using
    (Rat.valuation_le_one_iff_den
      (R := ℤ) (𝔭 := lambdaRationalHeightOneSpectrum p) (x := x))

theorem lambdaRationalHeightOneSpectrum_eq_primesEquiv_symm :
    lambdaRationalHeightOneSpectrum p =
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm (lambdaPadicPrime p) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  apply Ideal.ext
  intro z
  simp [Rat.HeightOneSpectrum.primesEquiv, lambdaRationalHeightOneSpectrum,
    lambdaRationalPrimeIdeal, lambdaPadicPrime, Rat.IsIntegralClosure.intEquiv,
    Ideal.mem_comap, Ideal.mem_span_singleton]

theorem primesEquiv_lambdaRationalHeightOneSpectrum :
    Rat.HeightOneSpectrum.primesEquiv
        (R := ℤ) (lambdaRationalHeightOneSpectrum p) =
      lambdaPadicPrime p := by
  rw [lambdaRationalHeightOneSpectrum_eq_primesEquiv_symm]
  exact Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (lambdaPadicPrime p)

/-- The lambda valuation on `K`, restricted to rational elements, detects the
same denominators as the rational `p`-adic valuation. -/
theorem lambdaValuation_algebraMap_rat_le_one_iff_den (x : ℚ) :
    (lambdaHeightOneSpectrum p K).valuation K (algebraMap ℚ K x) ≤ 1 ↔
      (x.den : ℤ) ∉ lambdaRationalPrimeIdeal p := by
  classical
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hden_ne : (algebraMap ℤ (𝓞 K) (x.den : ℤ)) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast x.den_nz)
  have hcop :
      algebraMap ℤ (𝓞 K) (x.den : ℤ) ∈ zetaPrime p K →
        algebraMap ℤ (𝓞 K) x.num ∉ zetaPrime p K := by
    intro hden hnum
    have hdenZ :
        (x.den : ℤ) ∈ lambdaRationalPrimeIdeal p :=
      (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
        (p := p) (K := K) (x.den : ℤ)).mp hden
    have hnumZ :
        x.num ∈ lambdaRationalPrimeIdeal p :=
      (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
        (p := p) (K := K) x.num).mp hnum
    haveI : (lambdaRationalPrimeIdeal p).IsPrime := by
      simpa [lambdaRationalHeightOneSpectrum_asIdeal] using
        (lambdaRationalHeightOneSpectrum p).isPrime
    exact (Ideal.IsPrime.notMem_of_isCoprime_of_mem
      x.isCoprime_num_den.symm hdenZ) hnumZ
  have hx :
      algebraMap ℚ K x =
        (algebraMap ℤ (𝓞 K) x.num : K) /
          (algebraMap ℤ (𝓞 K) (x.den : ℤ) : K) := by
    conv_lhs => rw [← Rat.num_div_den x]
    norm_num
  rw [hx]
  simpa [lambdaHeightOneSpectrum] using
    ((lambdaHeightOneSpectrum p K).valuation_div_le_one_iff
      (K := K) (a := algebraMap ℤ (𝓞 K) x.num)
      (b := algebraMap ℤ (𝓞 K) (x.den : ℤ)) hden_ne hcop)
      |>.trans
        (not_congr
          (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
            (p := p) (K := K) (x.den : ℤ)))

/-- The lambda valuation on `K`, pulled back to `ℚ`, is equivalent to the
rational `p`-adic valuation. -/
theorem lambdaValuation_comap_rat_isEquiv :
    ((lambdaRationalHeightOneSpectrum p).valuation ℚ).IsEquiv
      (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply,
    lambdaRationalValuation_le_one_iff_den (p := p) x,
    lambdaValuation_algebraMap_rat_le_one_iff_den (p := p) (K := K) x]

/-- The exact-comap valued map from rational elements to the lambda-valued
cyclotomic field. -/
def rationalToLambdaComapWithValRingHom :
    WithVal (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K)) →+*
      WithVal ((lambdaHeightOneSpectrum p K).valuation K) :=
  (WithVal.equiv ((lambdaHeightOneSpectrum p K).valuation K)).symm.toRingHom.comp
    ((algebraMap ℚ K).comp
      (WithVal.equiv
        (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K))).toRingHom)

@[simp]
theorem rationalToLambdaComapWithValRingHom_apply
    (x : WithVal (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K))) :
    rationalToLambdaComapWithValRingHom (p := p) (K := K) x =
      (WithVal.equiv ((lambdaHeightOneSpectrum p K).valuation K)).symm
        (algebraMap ℚ K
          ((WithVal.equiv
            (((lambdaHeightOneSpectrum p K).valuation K).comap
              (algebraMap ℚ K))) x)) :=
  rfl

/-- The rational `p`-adic valued map into the lambda-valued cyclotomic field. -/
def rationalToLambdaWithValRingHom :
    WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ) →+*
      WithVal ((lambdaHeightOneSpectrum p K).valuation K) :=
  (rationalToLambdaComapWithValRingHom (p := p) (K := K)).comp
    (lambdaValuation_comap_rat_isEquiv (p := p) (K := K)).orderRingIso.toRingHom

@[simp]
theorem rationalToLambdaWithValRingHom_apply
    (x : WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ)) :
    rationalToLambdaWithValRingHom (p := p) (K := K) x =
      (WithVal.equiv ((lambdaHeightOneSpectrum p K).valuation K)).symm
        (algebraMap ℚ K
          ((WithVal.equiv ((lambdaRationalHeightOneSpectrum p).valuation ℚ)) x)) :=
  rfl

/-- Continuity of the rational `p`-adic valued map into the lambda-valued
cyclotomic field.  This is the theorem consumed by
`UniformSpace.Completion.mapRingHom`. -/
theorem continuous_rationalToLambdaWithValRingHom :
    Continuous (rationalToLambdaWithValRingHom (p := p) (K := K)) := by
  let vQ := (lambdaRationalHeightOneSpectrum p).valuation ℚ
  let vK := (lambdaHeightOneSpectrum p K).valuation K
  let targetP : WithVal vK :=
    (WithVal.equiv vK).symm (algebraMap ℚ K (p : ℚ))
  have hp_mem_rat : (p : ℤ) ∈ lambdaRationalPrimeIdeal p := by
    simp [lambdaRationalPrimeIdeal]
  have hp_mem_zeta : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ zetaPrime p K :=
    (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
      (p := p) (K := K) (p : ℤ)).mpr hp_mem_rat
  have hp_lt : Valued.v targetP < 1 := by
    have h :
        vK (algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) (p : ℤ))) < 1 :=
      ((lambdaHeightOneSpectrum p K).valuation_lt_one_iff_mem
        (K := K) (algebraMap ℤ (𝓞 K) (p : ℤ))).mpr hp_mem_zeta
    rw [show Valued.v targetP = vK (algebraMap ℚ K (p : ℚ)) from rfl,
      show (algebraMap ℚ K (p : ℚ)) = (p : K) by push_cast; ring]
    rw [show algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) (p : ℤ)) = (p : K) by
      push_cast; ring] at h
    exact h
  have hp_tendsto : Tendsto (fun n : ℕ => targetP ^ n) atTop (𝓝 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hp_lt
  refine (uniformContinuous_of_continuousAt_zero
    (rationalToLambdaWithValRingHom (p := p) (K := K)).toAddMonoidHom ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  have hγ_mem :
      {z : WithVal vK | Valued.v.restrict z < γ.1} ∈ 𝓝 (0 : WithVal vK) :=
    (Valued.hasBasis_nhds_zero (WithVal vK) ℤᵐ⁰).mem_of_mem (i := γ) trivial
  obtain ⟨n, hn⟩ := (eventually_atTop.1 (hp_tendsto hγ_mem))
  let sourceP : WithVal vQ :=
    (WithVal.equiv vQ).symm ((p : ℚ) ^ n)
  have hsourceP_ne : Valued.v.restrict sourceP ≠ 0 :=
    ne_of_gt <| by
      rw [Valuation.restrict_pos_iff]
      have hpq_ne : ((p : ℚ) ^ n) ≠ 0 :=
        pow_ne_zero n (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))
      have hsourceP_nz : sourceP ≠ 0 := by
        intro hzero
        apply hpq_ne
        have := congrArg (WithVal.equiv vQ) hzero
        simpa [sourceP] using this
      exact zero_lt_iff.mpr <|
        (Valuation.ne_zero_iff
          (Valued.v : Valuation (WithVal vQ) ℤᵐ⁰)).mpr hsourceP_nz
  refine ⟨Units.mk0 (Valued.v.restrict sourceP) hsourceP_ne, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding]
  have hx_val : Valued.v x < Valued.v sourceP := by
    rwa [Valuation.restrict_lt_iff] at hx
  have hx_rat :
      vQ ((WithVal.equiv vQ) x) < vQ ((p : ℚ) ^ n) := by
    rw [WithVal.val_apply_equiv]
    rw [show vQ ((p : ℚ) ^ n) = Valued.v sourceP from rfl]
    exact hx_val
  have hx_comap :
      (vK.comap (algebraMap ℚ K)) ((WithVal.equiv vQ) x) <
        (vK.comap (algebraMap ℚ K)) ((p : ℚ) ^ n) :=
    (lambdaValuation_comap_rat_isEquiv (p := p) (K := K)).lt_iff_lt.mp hx_rat
  have hx_target :
      Valued.v (rationalToLambdaWithValRingHom (p := p) (K := K) x) <
        Valued.v (targetP ^ n) := by
    have hL : Valued.v (rationalToLambdaWithValRingHom (p := p) (K := K) x) =
        (vK.comap (algebraMap ℚ K)) ((WithVal.equiv vQ) x) := by
      rw [rationalToLambdaWithValRingHom_apply, Valuation.comap_apply]
      rfl
    have hR : Valued.v (targetP ^ n) =
        (vK.comap (algebraMap ℚ K)) ((p : ℚ) ^ n) := by
      rw [map_pow, map_pow,
        show Valued.v targetP = (vK.comap (algebraMap ℚ K)) (p : ℚ) from rfl]
    rw [hL, hR]
    exact hx_comap
  exact hx_target.trans <| by
    have hn' : Valued.v.restrict (targetP ^ n) < γ.1 := hn n le_rfl
    rwa [Valuation.restrict_lt_iff_lt_embedding] at hn'

/-- The completion-level map from the rational `p`-adic completion to the
lambda-adic completion of `K`. -/
def rationalToLambdaCompletionRingHom :
    (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ →+*
      LambdaValuedCompletion p K :=
  UniformSpace.Completion.mapRingHom
    (rationalToLambdaWithValRingHom (p := p) (K := K))
    (continuous_rationalToLambdaWithValRingHom (p := p) (K := K))

@[simp]
theorem rationalToLambdaCompletionRingHom_coe
    (x : WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ)) :
    rationalToLambdaCompletionRingHom (p := p) (K := K) x =
      (rationalToLambdaWithValRingHom (p := p) (K := K) x :
        LambdaValuedCompletion p K) :=
  UniformSpace.Completion.mapRingHom_coe
    (continuous_rationalToLambdaWithValRingHom (p := p) (K := K)) x

@[simp]
theorem rationalToLambdaCompletionRingHom_algebraMap (q : ℚ) :
    rationalToLambdaCompletionRingHom (p := p) (K := K)
        (algebraMap ℚ ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) q) =
      algebraMap K (LambdaValuedCompletion p K) (algebraMap ℚ K q) := by
  let vQ := (lambdaRationalHeightOneSpectrum p).valuation ℚ
  let vK := (lambdaHeightOneSpectrum p K).valuation K
  change rationalToLambdaCompletionRingHom (p := p) (K := K)
        ((UniformSpace.Completion.coeRingHom :
            WithVal vQ →+* (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
          ((WithVal.equiv vQ).symm q)) =
      (UniformSpace.Completion.coeRingHom :
          WithVal vK →+* LambdaValuedCompletion p K)
        ((WithVal.equiv vK).symm (algebraMap ℚ K q))
  simp [rationalToLambdaCompletionRingHom, rationalToLambdaWithValRingHom,
    rationalToLambdaComapWithValRingHom, vQ, vK]

/-- The canonical continuous `ℚ`-algebra equivalence from mathlib's `ℚ_[p]`
to the rational completion used in the λ-extension map. -/
def lambdaPadicToRationalCompletionAlgEquiv :
    ℚ_[lambdaPadicPrime p] ≃A[ℚ]
      (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ :=
  (Padic.adicCompletionEquiv ℤ (lambdaPadicPrime p)).trans
    (ContinuousAlgEquiv.cast (R := ℚ)
      (A := fun v : IsDedekindDomain.HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (lambdaRationalHeightOneSpectrum_eq_primesEquiv_symm (p := p)).symm)

/-- The concrete ring homomorphism from `ℚ_[p]` to the lambda-adic completion
of `K`. -/
def padicToLambdaCompletionRingHom :
    ℚ_[lambdaPadicPrime p] →+* LambdaValuedCompletion p K :=
  (rationalToLambdaCompletionRingHom (p := p) (K := K)).comp
    (lambdaPadicToRationalCompletionAlgEquiv (p := p)).toAlgEquiv.toRingEquiv.toRingHom

@[simp]
theorem padicToLambdaCompletionRingHom_algebraMap (q : ℚ) :
    padicToLambdaCompletionRingHom (p := p) (K := K)
        (algebraMap ℚ ℚ_[lambdaPadicPrime p] q) =
      algebraMap K (LambdaValuedCompletion p K) (algebraMap ℚ K q) := by
  change rationalToLambdaCompletionRingHom (p := p) (K := K)
      (lambdaPadicToRationalCompletionAlgEquiv (p := p)
        (algebraMap ℚ ℚ_[lambdaPadicPrime p] q)) =
    algebraMap K (LambdaValuedCompletion p K) (algebraMap ℚ K q)
  have hcomm :
      lambdaPadicToRationalCompletionAlgEquiv (p := p)
          (algebraMap ℚ ℚ_[lambdaPadicPrime p] q) =
        algebraMap ℚ ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) q :=
    (lambdaPadicToRationalCompletionAlgEquiv (p := p)).commutes q
  rw [hcomm]
  exact rationalToLambdaCompletionRingHom_algebraMap (p := p) (K := K) q

/-- The `ℚ_[p]`-algebra structure on the lambda-adic completion of `K`
induced by the explicit completion map.  This is a definition, not a global
instance, so downstream trace constructions can opt into it locally. -/
@[reducible]
def lambdaValuedCompletionAlgebraPadic :
    Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
  (padicToLambdaCompletionRingHom (p := p) (K := K)).toAlgebra

theorem algebraMap_lambdaValuedCompletionAlgebraPadic :
    letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
      lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
    algebraMap ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) =
      padicToLambdaCompletionRingHom (p := p) (K := K) := by
  rfl

/-- The rational-completion algebra structure on the lambda completion before
identifying the rational completion with mathlib's `ℚ_[p]`. -/
@[reducible]
def rationalCompletionToLambdaAlgebra :
    Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
  (rationalToLambdaCompletionRingHom (p := p) (K := K)).toAlgebra

theorem algebraMap_rationalCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalCompletionToLambdaAlgebra (p := p) (K := K)
    algebraMap ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) =
      rationalToLambdaCompletionRingHom (p := p) (K := K) := by
  rfl

theorem continuous_algebraMap_rationalCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalCompletionToLambdaAlgebra (p := p) (K := K)
    Continuous (algebraMap ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K)) := by
  change Continuous (rationalToLambdaCompletionRingHom (p := p) (K := K))
  rw [rationalToLambdaCompletionRingHom, UniformSpace.Completion.coe_mapRingHom]
  exact UniformSpace.Completion.continuous_map

theorem continuousSMul_rationalCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalCompletionToLambdaAlgebra (p := p) (K := K)
    ContinuousSMul ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) := by
  letI : Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalCompletionToLambdaAlgebra (p := p) (K := K)
  exact continuousSMul_of_algebraMap _ _
    (continuous_algebraMap_rationalCompletionToLambdaAlgebra (p := p) (K := K))

/-- The `ℚ_[p]`-algebra structure on the rational completion transported by
mathlib's `Padic.adicCompletionEquiv`. -/
@[reducible]
def padicToRationalCompletionAlgebra :
    Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
  (lambdaPadicToRationalCompletionAlgEquiv (p := p)).toAlgEquiv.toRingEquiv.toRingHom.toAlgebra

theorem padicToRationalCompletion_moduleFinite :
    letI : Algebra ℚ_[lambdaPadicPrime p]
        ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
      padicToRationalCompletionAlgebra (p := p)
    Module.Finite ℚ_[lambdaPadicPrime p]
      ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) := by
  letI : Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
    padicToRationalCompletionAlgebra (p := p)
  change (lambdaPadicToRationalCompletionAlgEquiv (p := p)).toAlgEquiv.toRingEquiv.toRingHom.Finite
  exact (lambdaPadicToRationalCompletionAlgEquiv (p := p)).toAlgEquiv.toRingEquiv.finite

/-- The rational finite place attached to `(p)`, stated in `𝓞 ℚ` so that
mathlib's finite-place completion theorem applies directly. -/
abbrev lambdaRationalIntegerHeightOneSpectrum :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm (lambdaPadicPrime p)

theorem primesEquiv_lambdaRationalIntegerHeightOneSpectrum :
    Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ) (lambdaRationalIntegerHeightOneSpectrum p) =
      lambdaPadicPrime p :=
  Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (lambdaPadicPrime p)

/-- The continuous algebra equivalence from the rational integer completion to
mathlib's `ℚ_[p]`. -/
def lambdaRationalIntegerToPadicAlgEquiv :
    (lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ ≃A[ℚ]
      PadicOfPrime (lambdaPadicPrime p) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
      (lambdaRationalIntegerHeightOneSpectrum p)).trans
    (ContinuousAlgEquiv.cast (R := ℚ)
      (A := PadicOfPrime)
      (primesEquiv_lambdaRationalIntegerHeightOneSpectrum (p := p)))

theorem continuous_padicToLambdaCompletionRingHom :
    Continuous (padicToLambdaCompletionRingHom (p := p) (K := K)) := by
  change Continuous fun x =>
    rationalToLambdaCompletionRingHom (p := p) (K := K)
      (lambdaPadicToRationalCompletionAlgEquiv (p := p) x)
  exact (UniformSpace.Completion.continuous_map.comp
    (lambdaPadicToRationalCompletionAlgEquiv (p := p)).continuous)

/-- The rational-integer completion algebra on the lambda completion, routed
through `ℚ_[p]`. -/
@[reducible]
def rationalIntegerCompletionToLambdaAlgebra :
    Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
  ((padicToLambdaCompletionRingHom (p := p) (K := K)).comp
    (lambdaRationalIntegerToPadicAlgEquiv (p := p)).toAlgEquiv.toRingEquiv.toRingHom).toAlgebra

theorem continuousSMul_rationalIntegerCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
    ContinuousSMul ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) := by
  letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  refine continuousSMul_of_algebraMap _ _ ?_
  change Continuous fun x =>
    padicToLambdaCompletionRingHom (p := p) (K := K)
      (lambdaRationalIntegerToPadicAlgEquiv (p := p) x)
  exact (continuous_padicToLambdaCompletionRingHom (p := p) (K := K)).comp
    (lambdaRationalIntegerToPadicAlgEquiv (p := p)).continuous

theorem isScalarTower_rationalIntegerCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
    IsScalarTower ℚ ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) := by
  letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  refine IsScalarTower.of_algebraMap_eq fun q => ?_
  rw [RingHom.algebraMap_toAlgebra]
  change algebraMap ℚ (LambdaValuedCompletion p K) q =
    padicToLambdaCompletionRingHom (p := p) (K := K)
      (lambdaRationalIntegerToPadicAlgEquiv (p := p)
        (algebraMap ℚ ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) q))
  have hcomm :
      lambdaRationalIntegerToPadicAlgEquiv (p := p)
          (algebraMap ℚ ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) q) =
        algebraMap ℚ (PadicOfPrime (lambdaPadicPrime p)) q :=
    (lambdaRationalIntegerToPadicAlgEquiv (p := p)).commutes q
  rw [hcomm, padicToLambdaCompletionRingHom_algebraMap (p := p) (K := K) q]
  exact IsScalarTower.algebraMap_apply ℚ K (LambdaValuedCompletion p K) q

theorem lambdaValuedCompletion_moduleFinite_rationalIntegerCompletion :
    letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
    Module.Finite ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) := by
  letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  haveI : ContinuousSMul ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    continuousSMul_rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  haveI : IsScalarTower ℚ ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    isScalarTower_rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  exact inferInstance

/-- The `ℚ_[p]`-algebra structure on the rational integer completion transported
by the inverse of `lambdaRationalIntegerToPadicAlgEquiv`. -/
@[reducible]
def padicToRationalIntegerCompletionAlgebra :
    Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
  (lambdaRationalIntegerToPadicAlgEquiv (p := p)).symm.toAlgEquiv.toRingEquiv.toRingHom.toAlgebra

theorem padicToRationalIntegerCompletion_moduleFinite :
    letI : Algebra ℚ_[lambdaPadicPrime p]
        ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
      padicToRationalIntegerCompletionAlgebra (p := p)
    Module.Finite ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) := by
  letI : Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
    padicToRationalIntegerCompletionAlgebra (p := p)
  change
    ((lambdaRationalIntegerToPadicAlgEquiv (p := p)).symm.toAlgEquiv.toRingEquiv.toRingHom).Finite
  exact (lambdaRationalIntegerToPadicAlgEquiv (p := p)).symm.toAlgEquiv.toRingEquiv.finite

theorem isScalarTower_padic_rationalIntegerCompletion_lambdaCompletion :
    letI : Algebra ℚ_[lambdaPadicPrime p]
        ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
      padicToRationalIntegerCompletionAlgebra (p := p)
    letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
    letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
      lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
    IsScalarTower ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) := by
  letI : Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
    padicToRationalIntegerCompletionAlgebra (p := p)
  letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change padicToLambdaCompletionRingHom (p := p) (K := K) x =
    padicToLambdaCompletionRingHom (p := p) (K := K)
      (lambdaRationalIntegerToPadicAlgEquiv (p := p)
        ((lambdaRationalIntegerToPadicAlgEquiv (p := p)).symm x))
  rw [(lambdaRationalIntegerToPadicAlgEquiv (p := p)).apply_symm_apply]

theorem lambdaValuedCompletion_moduleFinitePadic :
    letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
      lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
    Module.Finite ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) := by
  letI : Algebra ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
    padicToRationalIntegerCompletionAlgebra (p := p)
  letI : Algebra ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    rationalIntegerCompletionToLambdaAlgebra (p := p) (K := K)
  letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
    lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
  haveI : IsScalarTower ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    isScalarTower_padic_rationalIntegerCompletion_lambdaCompletion (p := p) (K := K)
  haveI : Module.Finite ℚ_[lambdaPadicPrime p]
      ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ) :=
    padicToRationalIntegerCompletion_moduleFinite (p := p)
  haveI : Module.Finite ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
    lambdaValuedCompletion_moduleFinite_rationalIntegerCompletion (p := p) (K := K)
  exact Module.Finite.trans ((lambdaRationalIntegerHeightOneSpectrum p).adicCompletion ℚ)
    (LambdaValuedCompletion p K)

theorem lambdaValuedCompletion_finiteDimensionalPadic :
    letI : Algebra ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
      lambdaValuedCompletionAlgebraPadic (p := p) (K := K)
    FiniteDimensional ℚ_[lambdaPadicPrime p] (LambdaValuedCompletion p K) :=
  lambdaValuedCompletion_moduleFinitePadic (p := p) (K := K)

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
