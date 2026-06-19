import PadicLFunctions.Iwasawa.StructureTheory.CharIdeal
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# The characteristic ideal of a cyclic quotient  (part (ii) of the Main Conjecture)

For the Iwasawa algebra `Λ = 𝒪⟦T⟧` over a discrete valuation ring `𝒪` (standing case
`𝒪 = ℤ_p`), `Λ` is a 2-dimensional regular UFD whose height-one localisations are DVRs.
This file computes the characteristic ideal of the cyclic torsion module `Λ ⧸ (f)`:

    charIdeal 𝒪 (Λ ⧸ (f)) htor = (f)        (for `f ≠ 0`).

This is the core algebraic input to "part (ii)" of the Iwasawa Main Conjecture — the
statement that the characteristic ideal of the relevant cyclic module recovers the
generating element `f` (e.g. the `p`-adic `L`-function).

## Main declarations

* `Iwasawa.localMult_quotient_span`: at a height-one prime `P`, the local multiplicity of
  `Λ ⧸ (f)` equals the order of vanishing of `f` in the DVR `Λ_P`:
  `localMult P (Λ ⧸ (f)) = Ring.ord Λ_P (algebraMap f)`.
* `Iwasawa.charIdeal_quotient`: `charIdeal 𝒪 (Λ ⧸ (f)) htor = (f)`.
-/

noncomputable section

namespace Iwasawa

open IsLocalRing

variable (𝒪 : Type*) [CommRing 𝒪]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- **Lemma A.** At a height-one prime `P` of `Λ`, the local multiplicity of the cyclic
quotient `Λ ⧸ (f)` equals the order of vanishing of the image of `f` in the localisation
`Λ_P = Localization.AtPrime P`.  Unfolding `localMult`, the localised module
`(Λ ⧸ (f))_P` is `Λ_P ⧸ (f)·Λ_P` (`localizedQuotientEquiv` carries the localisation of the
quotient to the quotient of the localisation, and `Ideal.localized'_eq_map` identifies the
localised ideal `((f))_P` with `(algebraMap f)`); its length is exactly `Ring.ord` of
`algebraMap f` by definition. -/
theorem localMult_quotient_span
    (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime] (f : IwasawaAlgebra 𝒪) :
    localMult 𝒪 P (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f})
      = Ring.ord (Localization.AtPrime P)
          (algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime P) f) := by
  -- abbreviations
  set A := Localization.AtPrime P with hA
  -- the `Λ`-linear localisation isomorphism `Λ_P ≅ LocalizedModule p Λ`, upgraded to `Λ_P`-linear
  let iso : LocalizedModule P.primeCompl (IwasawaAlgebra 𝒪) ≃ₗ[IwasawaAlgebra 𝒪] A :=
    IsLocalizedModule.iso P.primeCompl (Algebra.linearMap (IwasawaAlgebra 𝒪) A)
  let isoA : LocalizedModule P.primeCompl (IwasawaAlgebra 𝒪) ≃ₗ[A] A :=
    iso.extendScalarsOfIsLocalization P.primeCompl A
  -- this iso carries the localised ideal `(f)_P` to `(algebraMap f)`
  have hmap : ((Ideal.span {f}).localized P.primeCompl).map (isoA : _ →ₗ[A] A)
      = Ideal.span {algebraMap (IwasawaAlgebra 𝒪) A f} := by
    have happ : (isoA : LocalizedModule P.primeCompl (IwasawaAlgebra 𝒪) →ₗ[A] A)
        (LocalizedModule.mkLinearMap P.primeCompl (IwasawaAlgebra 𝒪) f)
          = algebraMap (IwasawaAlgebra 𝒪) A f := by
      show iso (LocalizedModule.mkLinearMap P.primeCompl (IwasawaAlgebra 𝒪) f) = _
      rw [LocalizedModule.mkLinearMap_apply, IsLocalizedModule.iso_mk_one]
      rfl
    rw [Submodule.localized, Submodule.localized'_span, Submodule.map_span,
      Set.image_singleton, Set.image_singleton, happ, ← Ideal.submodule_span_eq]
  -- the equiv on quotients
  let quotEquiv :
      (LocalizedModule P.primeCompl (IwasawaAlgebra 𝒪) ⧸ (Ideal.span {f}).localized P.primeCompl)
        ≃ₗ[A] (A ⧸ Ideal.span {algebraMap (IwasawaAlgebra 𝒪) A f}) :=
    Submodule.Quotient.equiv _ _ isoA hmap
  rw [localMult, Ring.ord,
    ← LinearEquiv.length_eq (localizedQuotientEquiv P.primeCompl (Ideal.span {f})),
    ← LinearEquiv.length_eq quotEquiv]

/-- **Lemma B.** At a *principal* height-one prime `P = (g)` (`g` prime), the local
multiplicity of `Λ ⧸ (f)` is the `P`-adic valuation of `f`: combining Lemma A with
`Ring.ord_eq_addVal` in the DVR `Λ_P = Localization.AtPrime (g)`
(`iwasawaAlgebra_localization_atPrime_isDVR`). -/
theorem localMult_quotient_span_eq_addVal [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {g : IwasawaAlgebra 𝒪} (hg : Prime g)
    [(Ideal.span {g} : Ideal (IwasawaAlgebra 𝒪)).IsPrime] (f : IwasawaAlgebra 𝒪) :
    haveI := iwasawaAlgebra_localization_atPrime_isDVR 𝒪 hg
    localMult 𝒪 (Ideal.span {g}) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f})
      = IsDiscreteValuationRing.addVal (Localization.AtPrime (Ideal.span {g}))
          (algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime (Ideal.span {g})) f) := by
  haveI := iwasawaAlgebra_localization_atPrime_isDVR 𝒪 hg
  rw [localMult_quotient_span, Ring.ord_eq_addVal]

variable {𝒪}

/-- The cyclic module `Λ ⧸ (f)` is torsion for `f ≠ 0`: every class `[y]` is killed by the
nonzerodivisor `f`. -/
theorem isTorsion_quotient_span [IsDomain 𝒪] {f : IwasawaAlgebra 𝒪} (hf : f ≠ 0) :
    Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}) := by
  intro x
  refine ⟨⟨f, mem_nonZeroDivisors_of_ne_zero hf⟩, ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, smul_eq_mul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))

/-- **Vanishing away from `(g)`.** If `P` is a height-one prime distinct from the height-one
prime `(g)` (`g` prime), then `g ∉ P`, so `g` maps to a unit in `Λ_P` and the local
multiplicity of `Λ ⧸ (g)` at `P` vanishes (`Ring.ord_of_isUnit`). -/
theorem localMult_quotient_span_prime_eq_zero [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {g : IwasawaAlgebra 𝒪} (hg : Prime g)
    (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime] (hP1 : P.height = 1)
    (hne : P ≠ Ideal.span {g}) :
    localMult 𝒪 P (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g}) = 0 := by
  -- `g ∉ P`: otherwise `(g) ≤ P` are distinct height-one primes, impossible.
  have hgP : g ∉ P := by
    intro hgmem
    apply hne
    have hle : Ideal.span {g} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgmem)
    haveI : (Ideal.span {g} : Ideal (IwasawaAlgebra 𝒪)).IsPrime :=
      (Ideal.span_singleton_prime hg.ne_zero).mpr hg
    rcases eq_or_lt_of_le hle with h | hlt
    · exact h.symm
    · exfalso
      have hcontra : (Ideal.span {g}).height + 1 ≤ P.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [hP1, Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hg.ne_zero) hg.not_unit] at hcontra
      norm_num at hcontra
  -- hence `algebraMap g` is a unit in `Λ_P`, so its order of vanishing is `0`.
  rw [localMult_quotient_span]
  refine Ring.ord_of_isUnit ?_
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P g]
  exact hgP

/-- **Value at `(g)`.** The local multiplicity of `Λ ⧸ (g)` at the prime `(g)` itself is `1`:
in the DVR `Λ_(g)`, the image of `g` generates the maximal ideal, hence is a uniformiser
(`irreducible_of_span_eq_maximalIdeal`), and its order of vanishing is `1`
(`Ring.ord_of_irreducible`). -/
theorem localMult_quotient_span_self [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {g : IwasawaAlgebra 𝒪} (hg : Prime g)
    [(Ideal.span {g} : Ideal (IwasawaAlgebra 𝒪)).IsPrime] :
    localMult 𝒪 (Ideal.span {g}) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g}) = 1 := by
  haveI := iwasawaAlgebra_localization_atPrime_isDVR 𝒪 hg
  rw [localMult_quotient_span]
  -- the maximal ideal of `Λ_(g)` is generated by the image of `g`
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {g}))
      = Ideal.span {algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime (Ideal.span {g})) g} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  -- the image of `g` is nonzero (localisation is injective on the domain `Λ`)
  have hg0 : algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime (Ideal.span {g})) g ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (IwasawaAlgebra 𝒪) (Localization.AtPrime (Ideal.span {g})))]
    exact fun h => hg.ne_zero
      (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {g})) h)
  exact Ring.ord_of_irreducible
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hg0 hmax)

open scoped Pointwise in
/-- **Multiplicativity for cyclic quotients.** For `g, h` with `g·h ≠ 0`,
`Ch_Λ(Λ ⧸ (g·h)) = Ch_Λ(Λ ⧸ (g)) · Ch_Λ(Λ ⧸ (h))`.  The short exact sequence
`0 → Λ/(h) →[·g] Λ/(g·(h)) → Λ/(g) → 0` (`Ideal.exact_mulQuot_quotOfMul`) feeds
`charIdeal_mul_of_exact`; the middle term `Λ/(g·(h))` is identified with `Λ/(g·h)` via
`g·(h) = (g·h)`. -/
theorem charIdeal_quotient_span_mul [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {g h : IwasawaAlgebra 𝒪} (hg : g ≠ 0) (_hh : h ≠ 0)
    (htor : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g * h}))
    (htorg : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g}))
    (htorh : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {h})) :
    charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g * h}) htor
      = charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g}) htorg
        * charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {h}) htorh := by
  -- `g • (h) = (g * h)` as submodules of `Λ`
  have hsmul : (g • (Ideal.span {h} : Ideal (IwasawaAlgebra 𝒪))
      : Submodule (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪)) = Ideal.span {g * h} := by
    rw [← Submodule.ideal_span_singleton_smul g (Ideal.span {h})]
    exact Ideal.span_singleton_mul_span_singleton g h
  -- torsion of the literal middle term `Λ/(g•(h))`, transported across `hsmul`
  haveI : Module.IsTorsion (IwasawaAlgebra 𝒪)
      (IwasawaAlgebra 𝒪 ⧸ (g • (Ideal.span {h} : Ideal (IwasawaAlgebra 𝒪)))) := by
    rw [hsmul]; exact htor
  -- multiplicativity on the exact sequence `0 → Λ/(h) → Λ/(g•(h)) → Λ/(g) → 0`
  have hmul := charIdeal_mul_of_exact (𝒪 := 𝒪)
    (M := IwasawaAlgebra 𝒪 ⧸ (g • (Ideal.span {h} : Ideal (IwasawaAlgebra 𝒪))))
    (M' := IwasawaAlgebra 𝒪 ⧸ Ideal.span {h}) (M'' := IwasawaAlgebra 𝒪 ⧸ Ideal.span {g})
    ‹_› htorh htorg (Ideal.mulQuot g (Ideal.span {h})) (Ideal.quotOfMul g (Ideal.span {h}))
    (Ideal.mulQuot_injective _ (mem_nonZeroDivisors_of_ne_zero hg))
    (Ideal.quotOfMul_surjective _)
    (LinearMap.exact_iff.mp (Ideal.exact_mulQuot_quotOfMul _)).symm
  -- transport the middle characteristic ideal across `Λ/(g•(h)) ≃ Λ/(g*h)`
  rw [charIdeal_eq_of_linearEquiv (M := IwasawaAlgebra 𝒪 ⧸ Ideal.span {g * h})
    (M' := IwasawaAlgebra 𝒪 ⧸ (g • (Ideal.span {h} : Ideal (IwasawaAlgebra 𝒪)))) htor ‹_›
    (Submodule.quotEquivOfEq _ _ hsmul.symm), hmul, mul_comm]

/-- **Lemma C (prime case).** For a prime element `g` of `Λ`, the characteristic ideal of the
cyclic module `Λ ⧸ (g)` is `(g)`.  The product over height-one primes
(`finprod_eq_single`) collapses to the single factor `(g) ^ 1`: the local multiplicity is `1`
at `(g)` (`localMult_quotient_span_self`) and `0` at every other height-one prime
(`localMult_quotient_span_prime_eq_zero`). -/
theorem charIdeal_quotient_span_prime [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {g : IwasawaAlgebra 𝒪} (hg : Prime g)
    (htor : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g})) :
    charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {g}) htor = Ideal.span {g} := by
  haveI hgP : (Ideal.span {g} : Ideal (IwasawaAlgebra 𝒪)).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr hg
  have hheight : (Ideal.span {g} : Ideal (IwasawaAlgebra 𝒪)).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg.ne_zero) hg.not_unit
  -- the distinguished height-one prime `(g)`
  set a : {P : Ideal (IwasawaAlgebra 𝒪) // P.IsPrime ∧ P.height = 1} :=
    ⟨Ideal.span {g}, hgP, hheight⟩ with ha
  rw [charIdeal, finprod_eq_single _ a ?_]
  · -- the value at `a` is `(g) ^ 1 = (g)`
    simp only [ha]
    rw [localMult_quotient_span_self hg, ENat.toNat_one, pow_one]
  · -- every other height-one prime contributes the trivial factor
    rintro ⟨P, hP, hP1⟩ hPa
    haveI := hP
    have hne : P ≠ Ideal.span {g} := fun h => hPa (Subtype.ext h)
    rw [localMult_quotient_span_prime_eq_zero hg P hP1 hne, ENat.toNat_zero, pow_zero]

/-- **The characteristic ideal of a unit quotient is `⊤`.** If `f` is a unit then `Λ ⧸ (f)`
is the zero module (`(f) = ⊤`), so every local multiplicity vanishes and the product over
height-one primes is `⊤ = (f)`. -/
theorem charIdeal_quotient_span_isUnit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {f : IwasawaAlgebra 𝒪} (hf : IsUnit f)
    (htor : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f})) :
    charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}) htor = Ideal.span {f} := by
  have htop : (Ideal.span {f} : Ideal (IwasawaAlgebra 𝒪)) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hf
  haveI : Subsingleton (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  rw [charIdeal]
  refine (finprod_eq_one_of_forall_eq_one fun P => ?_).trans (Ideal.one_eq_top.trans htop.symm)
  haveI := P.2.1
  -- the local multiplicity of the zero module vanishes (its localisation is subsingleton)
  have hz : (localMult 𝒪 P.1 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f})).toNat = 0 := by
    rw [localMult, Module.length_eq_zero]; rfl
  rw [hz, pow_zero]

/-- **Lemma C — the characteristic-ideal computation (part (ii) of the Main Conjecture).**
For any nonzero `f ∈ Λ`, the characteristic ideal of the cyclic torsion module `Λ ⧸ (f)`
is `(f)`.  Proof by `UniqueFactorizationMonoid.induction_on_prime` on `f` in the UFD `Λ`:
the unit case is `charIdeal_quotient_span_isUnit`, the prime base case is
`charIdeal_quotient_span_prime`, and the inductive step `f = p · a` uses multiplicativity
`charIdeal_quotient_span_mul` together with `(p) · (a) = (p · a)`. -/
theorem charIdeal_quotient [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {f : IwasawaAlgebra 𝒪} (hf : f ≠ 0)
    (htor : Module.IsTorsion (IwasawaAlgebra 𝒪) (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f})) :
    charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}) htor = Ideal.span {f} := by
  -- the predicate carried through the UFD induction (independent of the torsion proof)
  suffices H : ∀ f : IwasawaAlgebra 𝒪, ∀ htor : Module.IsTorsion (IwasawaAlgebra 𝒪)
      (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}),
      f ≠ 0 → charIdeal 𝒪 (IwasawaAlgebra 𝒪 ⧸ Ideal.span {f}) htor = Ideal.span {f} from
    H f htor hf
  clear htor hf f
  intro f
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun _ h0 => absurd rfl h0
  | h₂ x hx => exact fun htor _ => charIdeal_quotient_span_isUnit hx htor
  | h₃ a p ha hp ih =>
    intro htor _
    have hpa : p * a ≠ 0 := mul_ne_zero hp.ne_zero ha
    rw [charIdeal_quotient_span_mul hp.ne_zero ha htor
      (isTorsion_quotient_span hp.ne_zero) (isTorsion_quotient_span ha),
      charIdeal_quotient_span_prime hp _, ih (isTorsion_quotient_span ha) ha,
      Ideal.span_singleton_mul_span_singleton]

end Iwasawa
