import PadicLFunctions.Iwasawa.StructureTheory.StructureTheorem
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The characteristic ideal and its multiplicativity  (S13-S4)

For a finitely generated torsion `Λ`-module `M`, the structure theorem (S13-S3)
gives `M ~ ⨁ Λ/(gᵢ^eᵢ)`; its **characteristic ideal** is the product
`Ch_Λ(M) = ∏ᵢ (gᵢ^eᵢ) = (ϖ^n)·∏ⱼ(fⱼ^mⱼ)` (RJW TeX 3652–3657).  It is a
pseudo-isomorphism invariant — finite modules have characteristic ideal `(1) = ⊤` —
and it is **multiplicative in short exact sequences** (CS06, Appendix A.1, Prop 1;
RJW TeX 3679–3681).

## Main declarations

* `Iwasawa.charIdeal M hM`: the characteristic ideal `Ch_Λ(M) ⊆ Λ` of a finitely
  generated torsion module, read off from `fg_pseudoIso_canonical` (S13-S3).
* `Iwasawa.charIdeal_eq_of_pseudoIso`: well-definedness — `Ch_Λ` is constant on
  pseudo-isomorphism classes.
* `Iwasawa.charIdeal_mul_of_exact`: **multiplicativity** — for a short exact
  sequence `0 → M' → M → M'' → 0` of finitely generated torsion modules,
  `Ch_Λ(M) = Ch_Λ(M') · Ch_Λ(M'')` (CS06 A.1 Prop 1).
-/

noncomputable section

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- The **local multiplicity** of a `Λ`-module `M` at a prime `P`: the length of the
localisation `M_P` as a module over `Λ_P = Localization.AtPrime P`.  For a height-one
prime of the UFD `Λ`, `Λ_P` is a DVR (`iwasawaAlgebra_localization_atPrime_isDVR`, S3b)
and this is finite for finitely generated torsion `M`.  This is the per-prime "order of
vanishing" whose product over height-one primes is the characteristic ideal — the
length-theoretic route that avoids the full structure theorem. -/
noncomputable def localMult (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] : ℕ∞ :=
  Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

/-- **Additivity of the local multiplicity in short exact sequences** — the heart of the
characteristic ideal's multiplicativity.  For `0 → M' → M → M'' → 0`, localisation at `P`
is exact (`LocalizedModule.map_exact`) and module length is additive in short exact
sequences (`Module.length_eq_add_of_exact`), so the local multiplicities add.  No structure
theorem is used. -/
theorem localMult_add_of_exact (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime]
    {M' M M'' : Type*} [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M']
    [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M'']
    (f : M' →ₗ[IwasawaAlgebra 𝒪] M) (g : M →ₗ[IwasawaAlgebra 𝒪] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    localMult 𝒪 P M = localMult 𝒪 P M' + localMult 𝒪 P M'' :=
  Module.length_eq_add_of_exact
    (LocalizedModule.map P.primeCompl f) (LocalizedModule.map P.primeCompl g)
    (LocalizedModule.map_injective _ f hf) (LocalizedModule.map_surjective _ g hg)
    (LocalizedModule.map_exact _ f g hfg)

/-- **Finiteness of the local multiplicity**: for a finitely generated torsion `Λ`-module `M`
and a height-one prime `P`, `localMult P M` is finite.  `Λ_P` is Noetherian of Krull
dimension `1` (`IsLocalization.AtPrime.ringKrullDim_eq_height`), `M` is killed by a nonzero
`c` (`iwasawaAlgebra_exists_ne_zero_smul_eq_zero`), so `M_P` is finite length: it is a
finitely generated module over the Artinian ring `Λ_P/(c)` (a one-dimensional Noetherian
domain modulo a nonzero element, `isFiniteLength_quotient_span_singleton`).  This makes
`.toNat` additive, completing the multiplicativity. -/
theorem localMult_ne_top [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime] (hP1 : P.height = 1)
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M) :
    localMult 𝒪 P M ≠ ⊤ := by
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  haveI hKdim : Ring.KrullDimLE 1 (Localization.AtPrime P) := by
    refine Ring.krullDimLE_iff.mpr ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hP1]
    norm_cast
  -- `M` is killed by a nonzero `c`; its image `c'` in `Λ_P` kills `M_P`.
  obtain ⟨c, hc0, hcM⟩ := iwasawaAlgebra_exists_ne_zero_smul_eq_zero 𝒪 M hM
  set c' : Localization.AtPrime P := algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime P) c
    with hc'
  have hkill : Module.IsTorsionBy (Localization.AtPrime P) (LocalizedModule P.primeCompl M) c' := by
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      rw [hc', algebraMap_smul, LocalizedModule.smul'_mk, hcM m, LocalizedModule.zero_mk]
  -- `c'` is a nonzerodivisor of the domain `Λ_P`, so `Λ_P/(c')` is Artinian (finite length).
  have hc'nzd : c' ∈ nonZeroDivisors (Localization.AtPrime P) := by
    rw [mem_nonZeroDivisors_iff_ne_zero, hc', Ne,
      ← map_zero (algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime P))]
    exact fun h => hc0
      (IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P) h)
  haveI hflq : IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ Ideal.span {c'}) :=
    isFiniteLength_quotient_span_singleton _ hc'nzd
  haveI : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {c'}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hflq).2
  haveI : IsArtinianRing (Localization.AtPrime P ⧸ Ideal.span {c'}) :=
    isArtinian_of_tower (Localization.AtPrime P) ‹_›
  -- `M_P` is finitely generated over the Artinian ring `Λ_P/(c')`, hence finite length;
  -- transfer the length back to `Λ_P` along the surjection `Λ_P ↠ Λ_P/(c')`.
  letI := hkill.module
  haveI : Module.Finite (Localization.AtPrime P ⧸ Ideal.span {c'}) (LocalizedModule P.primeCompl M) :=
    Module.Finite.of_restrictScalars_finite (Localization.AtPrime P) _ _
  rw [localMult, Module.length_eq_of_surjective
    (S := Localization.AtPrime P) (R := Localization.AtPrime P ⧸ Ideal.span {c'})
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

/-- The mul-support of `P ↦ P ^ (localMult P M).toNat` over height-one primes is finite: a
height-one prime where the local multiplicity is nonzero lies in the support of `M`, hence
contains `Ann M`, and (being height-one) is therefore *minimal* over `Ann M`; the minimal
primes of `Ann M` are finite (`Ideal.finite_minimalPrimes_of_isNoetherianRing`). -/
theorem localMult_pow_mulSupport_finite [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M) :
    (Function.mulSupport fun P : {P : Ideal (IwasawaAlgebra 𝒪) // P.IsPrime ∧ P.height = 1} =>
      letI : P.1.IsPrime := P.2.1; P.1 ^ (localMult 𝒪 P.1 M).toNat).Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine ((Module.annihilator (IwasawaAlgebra 𝒪) M).finite_minimalPrimes_of_isNoetherianRing).subset ?_
  rintro Q ⟨⟨P, hP, hP1⟩, hmem, rfl⟩
  haveI := hP
  obtain ⟨c, hc0, hcM⟩ := iwasawaAlgebra_exists_ne_zero_smul_eq_zero 𝒪 M hM
  have hcann : c ∈ Module.annihilator (IwasawaAlgebra 𝒪) M := Module.mem_annihilator.mpr hcM
  -- `localMult P M ≠ 0`, so `M_P` is nontrivial, so `P` lies in the support, so `Ann M ≤ P`.
  rw [Function.mem_mulSupport] at hmem
  have hlm : localMult 𝒪 P M ≠ 0 := fun h0 => hmem (by rw [h0, ENat.toNat_zero, pow_zero])
  have hns : ¬ Subsingleton (LocalizedModule P.primeCompl M) :=
    fun hs => hlm (Module.length_eq_zero_iff.mpr hs)
  have hannP : Module.annihilator (IwasawaAlgebra 𝒪) M ≤ P := by
    have hmemsupp : (⟨P, hP⟩ : PrimeSpectrum (IwasawaAlgebra 𝒪)) ∈
        Module.support (IwasawaAlgebra 𝒪) M := by
      by_contra hc
      exact hns (Module.notMem_support_iff.mp hc)
    exact Module.mem_support_iff_of_finite.mp hmemsupp
  -- a minimal prime `Q ≤ P` of `Ann M` must equal `P`: `Q ⊇ (c)` forces `height Q ≥ 1`, but
  -- `Q < P` would force `height Q + 1 ≤ height P = 1`.
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hannP
  rcases eq_or_lt_of_le hQP with rfl | hlt
  · exact hQ
  · exfalso
    haveI : Q.IsPrime := hQ.1.1
    have hcQ : Ideal.span {c} ≤ Q :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hQ.1.2 hcann))
    have hQpos : 1 ≤ Q.height :=
      le_trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hc0)) (Ideal.height_mono hcQ)
    have hcontra : Q.height + 1 ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hP1] at hcontra
    have hbad : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) hcontra
    norm_num at hbad

/-- The **characteristic ideal** `Ch_Λ(M) ⊆ Λ` of a finitely generated torsion `Λ`-module,
defined the length-theoretic way: the product over height-one primes `P` of
`P ^ localMult P M` (RJW TeX 3652–3657).  Only finitely many factors are non-trivial (the
support is finite, `iwasawaAlgebra_associatedPrimes_finite`), so the `finprod` is genuine.
This definition needs no structure theorem; its multiplicativity is `localMult_add_of_exact`
through `finprod`. -/
noncomputable def charIdeal (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] (_hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M) :
    Ideal (IwasawaAlgebra 𝒪) :=
  ∏ᶠ (P : {P : Ideal (IwasawaAlgebra 𝒪) // P.IsPrime ∧ P.height = 1}),
    letI : P.1.IsPrime := P.2.1
    P.1 ^ (localMult 𝒪 P.1 M).toNat

variable {𝒪}
variable {M M' M'' : Type*}
  [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] [Module.Finite (IwasawaAlgebra 𝒪) M]
  [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M'] [Module.Finite (IwasawaAlgebra 𝒪) M']
  [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M''] [Module.Finite (IwasawaAlgebra 𝒪) M'']

/-- **Well-definedness of the characteristic ideal**: it depends only on the
pseudo-isomorphism class of `M`.  In particular a finite (pseudo-null) module has
characteristic ideal `⊤ = (1)`.  (The `gᵢ^eᵢ` data is the pseudo-iso invariant of
the structure theorem.) -/
theorem charIdeal_eq_of_pseudoIso (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M)
    (hM' : Module.IsTorsion (IwasawaAlgebra 𝒪) M') (h : IsPseudoIso 𝒪 M M') :
    charIdeal 𝒪 M hM = charIdeal 𝒪 M' hM' := by
  sorry

/-- **Multiplicativity of the characteristic ideal in short exact sequences**
(CS06, App. A.1, Prop 1; RJW TeX 3679–3681): given `0 → M' → M → M'' → 0` with
`M', M, M''` finitely generated torsion `Λ`-modules,
`Ch_Λ(M) = Ch_Λ(M') · Ch_Λ(M'')`. -/
theorem charIdeal_mul_of_exact [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M)
    (hM' : Module.IsTorsion (IwasawaAlgebra 𝒪) M')
    (hM'' : Module.IsTorsion (IwasawaAlgebra 𝒪) M'')
    (f : M' →ₗ[IwasawaAlgebra 𝒪] M) (g : M →ₗ[IwasawaAlgebra 𝒪] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    charIdeal 𝒪 M hM = charIdeal 𝒪 M' hM' * charIdeal 𝒪 M'' hM'' := by
  have hexact : Function.Exact f g := LinearMap.exact_iff.mpr hfg.symm
  -- at each height-one prime the exponents add: `localMult` is additive (`localMult_add_of_exact`)
  -- and finite (`localMult_ne_top`), so `.toNat` is additive
  have hadd : ∀ P : {P : Ideal (IwasawaAlgebra 𝒪) // P.IsPrime ∧ P.height = 1},
      (letI : P.1.IsPrime := P.2.1; P.1 ^ (localMult 𝒪 P.1 M).toNat)
        = (letI : P.1.IsPrime := P.2.1; P.1 ^ (localMult 𝒪 P.1 M').toNat)
          * (letI : P.1.IsPrime := P.2.1; P.1 ^ (localMult 𝒪 P.1 M'').toNat) := by
    rintro ⟨P, hP, hP1⟩
    haveI := hP
    rw [← pow_add, localMult_add_of_exact 𝒪 P f g hf hg hexact,
      ENat.toNat_add (localMult_ne_top 𝒪 P hP1 M' hM') (localMult_ne_top 𝒪 P hP1 M'' hM'')]
  rw [charIdeal, charIdeal, charIdeal, ← finprod_mul_distrib
    (localMult_pow_mulSupport_finite 𝒪 M' hM') (localMult_pow_mulSupport_finite 𝒪 M'' hM'')]
  exact finprod_congr hadd

end Iwasawa
