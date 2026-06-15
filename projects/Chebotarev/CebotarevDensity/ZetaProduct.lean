module

public import CebotarevDensity.Frobenius
public import CebotarevDensity.CyclotomicNormResidue
public import CebotarevDensity.ForMathlib.IdealCongruenceCount
public import CebotarevDensity.ForMathlib.LatticePointCount
public import CebotarevDensity.ForMathlib.NormLeOneLipschitz
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Zeta factorisation for an abelian extension

For an abelian Galois extension `L/K` of number fields, the Dedekind zeta
function `ζ_L(s)` factors as a product of Artin L-functions over the
characters of `Gal(L/K)`:

  ζ_L(s) = ∏_{χ : Gal(L/K) → ℂ^×} L(χ, s)   on Re s > 1.

The character `χ` is extended to a character on nonzero ideals of `𝓞 K` by
`χ(𝔭) = χ(σ_𝔭)` for `𝔭` unramified in `L`, and `0` otherwise. The
nontrivial-`χ` L-function is holomorphic and nonvanishing on `Re s ≥ 1`
(Sharifi §7.1.19); the trivial-character L-function is `ζ_K(s)`.

This factorisation is the analytic engine of the Chebotarev proof for the
cyclotomic case.

This file does **not** introduce a top-level `artinLSeries` definition —
the L-functions enter the argument only via existence statements packaged
as the theorems below, with the Euler-product / Dirichlet-series content
of each `L(χ, ·)` being an internal detail of the proof of
`dedekindZeta_eq_prod_artinLSeries`. The user can read the proof to see
how each `L(χ, ·)` is constructed.

## Main results

* `Chebotarev.exists_artinLSeries_eulerProduct_abelian` — the Euler product
  `L(χ,s) = ∏_𝔭 (1 - χ(𝔭) N𝔭⁻ˢ)⁻¹ = Σ_𝔞 χ(𝔞) N𝔞⁻ˢ` of an abelian character
  (Sharifi 7.1.18), with `χ(𝔞)` the multiplicative `galoisCharacterOnIdeal`.
* `Chebotarev.dedekindZeta_local_factor_eq_product_artin_local` — the local
  factorisation of `ζ_L` into Artin local factors at an unramified prime
  (Sharifi 7.1.16).
* `Chebotarev.artinLSeries_one_ne_zero` — non-vanishing `L(χ,1) ≠ 0` for
  nontrivial `χ`, via the pole-order argument (Sharifi 7.1.19 step 2), modulo
  the geometry-of-numbers analytic extension `artinLSeries_analytic_extension`.

## References

* Sharifi, *Algebraic Number Theory*, §7.1.15–7.1.19 (`docs/algnum.pdf`).
* The analogous factorisation for the prime cyclotomic field `ℚ(μ_p)/ℚ`
  is available in `flt-regular-bernoulli`'s
  `BernoulliRegular.ZetaFactorisation.EulerProduct`; this module
  generalises it to an arbitrary abelian extension `L/K`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

/-- A character of `Gal(L/K)` valued in `ℂ^×`. -/
abbrev galoisCharacter
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Type _ := Gal(L/K) →* ℂˣ

open Classical in
/-- The multiplicative extension of a Galois character `χ` to the nonzero ideals of `𝓞 K`
(Sharifi Notation 7.1.17): on a prime `𝔭` it is `χ(Frob 𝔭)` if `𝔭` is unramified in `L` and `0`
otherwise, extended completely multiplicatively via the prime factorisation. The L-function
coefficient `χ(𝔞)`. -/
noncomputable def galoisCharacterOnIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  ∏ 𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset,
    (if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)
      ^ (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭

open Classical in
/-- `galoisCharacterOnIdeal` written as the product over the prime factors **with
multiplicity** — i.e. a `Multiset.map`-product over `normalizedFactors 𝔞` — rather than the
`toFinset`+`count` form of the definition. This form makes the multiplicativity proof immediate
(`Multiset.map_add` + `Multiset.prod_add`). -/
private theorem galoisCharacterOnIdeal_eq_map_prod
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterOnIdeal K L χ 𝔞 =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 ↦ if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)).prod := by
  rw [galoisCharacterOnIdeal, Finset.prod_multiset_map_count]

open Classical in
/-- On a nonzero prime `𝔭`, the ideal character `χ(𝔭)` is `χ(Frob 𝔭)` when `𝔭` is unramified in
`L` and `0` otherwise (Sharifi Notation 7.1.17). The hypothesis `𝔭 ≠ ⊥` is needed: at the zero
ideal the product is the empty product `1`, whereas the right-hand side is `0` (the zero ideal
is never unramified). -/
theorem galoisCharacterOnIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ 𝔭 =
      if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- The ideal character is completely multiplicative: `χ(𝔞 * 𝔟) = χ(𝔞) · χ(𝔟)` for nonzero
ideals `𝔞`, `𝔟` (Sharifi Notation 7.1.17). -/
theorem galoisCharacterOnIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ (𝔞 * 𝔟) =
      galoisCharacterOnIdeal K L χ 𝔞 * galoisCharacterOnIdeal K L χ 𝔟 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, galoisCharacterOnIdeal_eq_map_prod,
    galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- The ideal character of the unit ideal `⊤` is `1` (empty product). -/
@[simp] theorem galoisCharacterOnIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) :
    galoisCharacterOnIdeal K L χ ⊤ = 1 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-! ### Sub-lemmas for `exists_dedekindZeta_factorisation`

Decomposed per Sharifi 7.1.16 (factorisation), 7.1.18 (abelian Euler
product), and 7.1.19 (analytic extension + non-vanishing). Each
sub-lemma is supported by a verbatim source quote in
`.mathlib-quality/chebotarev-decomposition.md`.

(i) Euler product for an abelian character (Sharifi 7.1.18, p. 141):
    `L(χ,s) = ∏_𝔭(1 - χ(𝔭) N𝔭^{-s})^{-1} = Σ_𝔞 χ(𝔞) N𝔞^{-s}` for `Re s > 1`.

(ii) Local Euler-factor decomposition at an unramified `𝔭`:
    `∏_{𝔓|𝔭}(1 - N𝔓^{-s})^{-1} = ∏_χ(1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`. Standard
    identity from finite cyclic group theory applied to the residue
    Galois group.

(iii) Multiplicative assembly: combining (i) and (ii) over all unramified
    `𝔭` yields `ζ_L = ∏_χ L(χ, ·)` (Sharifi 7.1.16 in the abelian case).

(iv) Analytic extension via geometry of numbers (Sharifi 7.1.19 step 1,
    p. 142): `Σ_{N𝔞≤N} χ(𝔞) = O(N^{1-d^{-1}})` where `d = [K:ℚ]`. This
    gives convergence of `L(χ,·)` on `Z(1-d^{-1})` via Lemma 7.1.5.

(v) Non-vanishing `L(χ,1) ≠ 0` for nontrivial `χ` (Sharifi 7.1.19 step 2,
    p. 142): the bounded-function + vanishing-order contradiction
    argument.
-/

/-- The value of a Galois character on the representative of a conjugacy class has norm `1`:
it is a root of unity, since `Gal(L/K)` is finite. -/
private theorem norm_galoisCharacter_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (c : ConjClasses Gal(L/K)) :
    ‖(χ c.out : ℂ)‖ = 1 :=
  (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite c.out)).norm_eq_one

open Classical in
/-- The ideal character has norm `≤ 1`: each prime-factor contribution is either `0` (ramified)
or a norm-`1` root of unity (unramified), so the product over factors has norm `≤ 1`. -/
private theorem norm_galoisCharacterOnIdeal_le_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    ‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1 := by
  rw [galoisCharacterOnIdeal, norm_prod]
  refine Finset.prod_le_one (fun i _ ↦ norm_nonneg _) (fun 𝔭 _ ↦ ?_)
  rw [norm_pow]
  by_cases h : UnramifiedIn K L 𝔭
  · rw [if_pos h, norm_galoisCharacter_out, one_pow]
  · rw [if_neg h, norm_zero]
    exact zero_pow_le_one _

/-- Sharifi 7.1.18 (p. 141): Euler product for an abelian Galois
character `χ : Gal(L/K) → ℂ^×`. For `Re s > 1` the Euler product over unramified primes
equals the Dirichlet series `Σ_𝔞 χ(𝔞) N𝔞^{-s}`, where `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞`
is the completely-multiplicative ideal character.

The proof instantiates the generic weighted prime-ideal Euler product
`weighted_eulerProduct_eq_tsum` with the weight `w = galoisCharacterOnIdeal K L χ`
(completely multiplicative with `‖w‖ ≤ 1`). The product on the left ranges over *unramified*
primes, whereas the weighted Euler product ranges over *all* nonzero primes; the two agree
because `w(𝔭) = 0` at a ramified prime, so its local factor `(1 - 0)⁻¹ = 1` drops out of the
product. At an unramified prime `w(𝔭) = χ(Frob 𝔭)` by `galoisCharacterOnIdeal_apply_prime`. -/
theorem exists_artinLSeries_eulerProduct_abelian
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) :
    ∀ s : ℂ, 1 < s.re →
      (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  intro s hs
  set w : Ideal (𝓞 K) → ℂ := galoisCharacterOnIdeal K L χ with hw
  rw [← weighted_eulerProduct_eq_tsum K (s := s) hs w (galoisCharacterOnIdeal_one K L χ)
    (fun {𝔞 𝔟} h𝔞 h𝔟 ↦ galoisCharacterOnIdeal_mul K L χ h𝔞 h𝔟)
    (norm_galoisCharacterOnIdeal_le_one K L χ)]
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} →
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := fun 𝔭 ↦ ⟨𝔭.1, 𝔭.2.1, 𝔭.2.2.ne_bot⟩ with hg
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 ↦ (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ with hf
  have hg_inj : Function.Injective g := fun _ _ hab ↦
    Subtype.ext (congrArg (fun x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ x.1) hab)
  have hsupp : Function.mulSupport f ⊆ Set.range g := by
    intro 𝔭 hmem
    simp only [Function.mem_mulSupport, hf] at hmem
    haveI := 𝔭.2.1
    have hunr : UnramifiedIn K L 𝔭.1 := by
      by_contra hnr
      apply hmem
      rw [hw, galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2, if_neg hnr, zero_mul, sub_zero,
        inv_one]
    exact ⟨⟨𝔭.1, 𝔭.2.1, hunr⟩, rfl⟩
  rw [← hg_inj.tprod_eq hsupp]
  refine tprod_congr fun 𝔭 ↦ ?_
  simp only [hf, hg, hw]
  haveI := 𝔭.2.1
  rw [galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2.ne_bot, if_pos 𝔭.2.2]

/-! ### Sub-lemmas for `dedekindZeta_local_factor_eq_product_artin_local`

The local-factor identity (Sharifi 7.1.16, p. 141) reduces to a finite-group computation. Both
sides are finite products that evaluate to `(1 - Y ^ f)⁻ᵍ` where `Y = N𝔭^{-s}`, `f = orderOf σ`
is the residue degree and `g = |G| / f` is the number of primes above `𝔭`:

* the left side has `g` factors (`card_primesAbove_mul_orderOf_eq`), each equal to `(1 - Y^f)⁻¹`
  because `N𝔓 = N𝔭^f` (`absNorm_eq_pow_inertiaDeg_of_liesOver`, `inertiaDeg = f`);
* the right side is `∏_{χ : G →* ℂˣ} (1 - χ(σ) Y)⁻¹`, and the evaluation map `χ ↦ χ(σ)`
  surjects `Ĝ` onto the `f`-th roots of unity with uniform fibres of size `g`, so
  `∏_χ (1 - χ(σ) Y) = (∏_{ζ ∈ μ_f} (1 - ζ Y))^g = (1 - Y^f)^g`.
-/

/-- `∏_{ζ ∈ μ_f} (1 - ζ Y) = 1 - Y ^ f` over `ℂ`: the `x = 1` case of the roots-of-unity
factorisation `x^f - y^f = ∏_{ζ ∈ μ_f} (x - ζ y)`
(`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`). -/
private theorem prod_one_sub_nthRoots (f : ℕ) (hf : 0 < f) (Y : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset f (1 : ℂ), (1 - ζ * Y) = 1 - Y ^ f := by
  rw [← (Complex.isPrimitiveRoot_exp f hf.ne').pow_sub_pow_eq_prod_sub_mul 1 Y hf, one_pow]

/-- The evaluation homomorphism `Ĝ → ℂˣ`, `χ ↦ χ σ`, for a finite commutative group `G`.
Realised as `(monoidHomMonoidHomEquiv G ℂ).symm σ` (the double-dual identification). -/
private noncomputable def charEval {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    (G →* ℂˣ) →* ℂˣ := (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ

private theorem charEval_apply {G : Type*} [CommGroup G] [Finite G] (σ : G) (φ : G →* ℂˣ) :
    charEval σ φ = φ σ := by rw [charEval, CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]

/-- The kernel of `χ ↦ χ σ` consists of the characters trivial on `⟨σ⟩`, so it has order
`|G ⧸ ⟨σ⟩| = |G| / orderOf σ` (`CommGroup.card_restrictHom_ker` + Lagrange + `Nat.card_zpowers`). -/
private theorem charEval_ker_card {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    Nat.card (charEval σ).ker = Nat.card G / orderOf σ := by
  have h1 : (charEval σ).ker = (MonoidHom.restrictHom (Subgroup.zpowers σ) ℂˣ).ker := by
    ext φ
    simp only [MonoidHom.mem_ker, MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff]
    refine ⟨fun hφ y hy ↦ ?_, fun hφ ↦ ?_⟩
    · rw [charEval_apply] at hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hφ, one_zpow]
    · rw [charEval_apply]
      exact hφ σ (Subgroup.mem_zpowers σ)
  rw [h1, CommGroup.card_restrictHom_ker]
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have key : Nat.card G = Nat.card (G ⧸ Subgroup.zpowers σ) * orderOf σ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers σ), Nat.card_zpowers]
  rw [key, Nat.mul_div_cancel _ hpos]

open Finset in
/-- **Character-product identity** (the group-theoretic heart of Sharifi 7.1.16). For a finite
commutative group `G`, an element `σ`, and `Y : ℂ`,
`∏_{χ : G →* ℂˣ} (1 - χ(σ) Y) = (1 - Y ^ orderOf σ) ^ (|G| / orderOf σ)`.
The map `χ ↦ χ(σ)` surjects `Ĝ` onto the `f`-th roots of unity `μ_f` (`f = orderOf σ`) with
uniform fibres of size `g = |G| / f` (`MonoidHom.card_fiber_eq_of_mem_range`, `charEval_ker_card`),
so the product factors over `μ_f` and collapses by `prod_one_sub_nthRoots`. -/
private theorem prod_galoisCharacter_one_sub {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] (σ : G) (Y : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = (1 - Y ^ orderOf σ) ^ (Nat.card G / orderOf σ) := by
  classical
  set f := orderOf σ with hf
  have hfpos : 0 < f := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  set evC : (G →* ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (charEval σ) with hevC
  have hevC_apply : ∀ χ : G →* ℂˣ, evC χ = ((χ σ : ℂˣ) : ℂ) := fun χ ↦ by
    rw [hevC, MonoidHom.comp_apply, Units.coeHom_apply, charEval_apply]
  have hfib1 : #{χ : G →* ℂˣ | evC χ = 1} = Nat.card (charEval σ).ker := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun χ ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker, hevC_apply]
    rw [Units.val_eq_one, ← charEval_apply σ χ]
  have huniform : ∀ c ∈ Set.range evC, #{χ : G →* ℂˣ | evC χ = c} = Nat.card (charEval σ).ker := by
    intro c hc
    rw [MonoidHom.card_fiber_eq_of_mem_range evC hc (⟨1, map_one _⟩ : (1 : ℂ) ∈ Set.range evC),
      hfib1]
  set t : Finset ℂ := Polynomial.nthRootsFinset f (1 : ℂ) with ht
  have hmaps : ∀ χ ∈ (Finset.univ : Finset (G →* ℂˣ)), evC χ ∈ t := by
    intro χ _
    rw [ht, Polynomial.mem_nthRootsFinset hfpos, hevC_apply,
      ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hsub : Finset.univ.image evC ⊆ t := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨χ, _, rfl⟩ := hc
    exact hmaps χ (Finset.mem_univ χ)
  have hcardG : Nat.card G = (Finset.univ.image evC).card * Nat.card (charEval σ).ker := by
    have hsum := Finset.card_eq_sum_card_image evC (Finset.univ : Finset (G →* ℂˣ))
    rw [show (Finset.univ : Finset (G →* ℂˣ)).card = Nat.card (G →* ℂˣ) by
      rw [Nat.card_eq_fintype_card, Finset.card_univ],
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity] at hsum
    rw [hsum, Finset.sum_congr rfl (fun c hc ↦ huniform c ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.mem_image] at hc
    obtain ⟨χ, _, rfl⟩ := hc
    exact Set.mem_range_self χ
  have himgcard : (Finset.univ.image evC).card = f := by
    have hdvd : f ∣ Nat.card G := orderOf_dvd_natCard σ
    have hkereq : Nat.card (charEval σ).ker = Nat.card G / f := charEval_ker_card σ
    rw [hkereq] at hcardG
    exact Nat.eq_of_mul_eq_mul_right (hkereq ▸ Nat.card_pos)
      (by rw [← hcardG, ← (Nat.mul_div_cancel' hdvd).symm])
  have himg : Finset.univ.image evC = t :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [himgcard, ht, (Complex.isPrimitiveRoot_exp f hfpos.ne').card_nthRootsFinset])
  have hfiber := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (G →* ℂˣ)))
    (t := t) (g := evC) (f := fun c : ℂ ↦ 1 - c * Y) hmaps
  have hLHS : ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = ∏ χ : G →* ℂˣ, (1 - evC χ * Y) :=
    Finset.prod_congr rfl fun χ _ ↦ by rw [hevC_apply]
  rw [hLHS, ← hfiber]
  have hinner : ∀ c ∈ t, (∏ _χ ∈ {χ ∈ (Finset.univ : Finset (G →* ℂˣ)) | evC χ = c},
      (1 - c * Y)) = (1 - c * Y) ^ Nat.card (charEval σ).ker := by
    intro c hc
    have hrange : c ∈ Set.range evC := by
      rw [← himg, Finset.mem_image] at hc
      obtain ⟨χ, _, rfl⟩ := hc
      exact Set.mem_range_self χ
    rw [Finset.prod_const, huniform c hrange]
  rw [Finset.prod_congr rfl hinner, charEval_ker_card σ, Finset.prod_pow, ht,
    prod_one_sub_nthRoots f hfpos Y]

/-- For an unramified prime `𝔭` and a prime `𝔓` of `𝓞 L` above it with residue degree `f`,
`N𝔓 = N𝔭 ^ f`, hence `(N𝔓)^{-s} = ((N𝔭)^{-s})^f`. -/
private theorem cpow_neg_absNorm_eq_pow {a b : ℕ} (f : ℕ) (s : ℂ)
    (h : b = a ^ f) : ((b : ℂ)) ^ (-s) = ((a : ℂ) ^ (-s)) ^ f := by
  rw [h, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Sharifi 7.1.16 (p. 141) local step: the local Euler factor at an
unramified prime `𝔭` of `K` factors as a product over characters.
Source quote (paraphrased identity): the local factor
`∏_{𝔓|𝔭}(1-N𝔓^{-s})^{-1}` equals `∏_χ(1-χ(σ_𝔭) N𝔭^{-s})^{-1}`. -/
theorem dedekindZeta_local_factor_eq_product_artin_local
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (s : ℂ) (_hs : 1 < s.re) :
    ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
      = ∏' χ : galoisCharacter K L,
        (1 - (χ (frobeniusClass K L 𝔭).out : ℂ) * (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  classical
  open scoped IsMulCommutative in
  letI : CommGroup Gal(L/K) := inferInstance
  set σ : Gal(L/K) := (frobeniusClass K L 𝔭).out
  set Y : ℂ := (Ideal.absNorm 𝔭 : ℂ) ^ (-s) with hY
  set f : ℕ := orderOf σ with hf
  haveI : Fintype Gal(L/K) := Fintype.ofFinite _
  haveI : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
  have hfpos : 0 < f := hf ▸ orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hcount : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
      = Nat.card Gal(L/K) / f := by
    have hmul := card_primesAbove_mul_orderOf_eq K L σ (frobeniusClass K L 𝔭)
      (Quotient.out_eq _) 𝔭 _hunr rfl
    rw [← hf] at hmul
    exact (Nat.div_eq_of_eq_mul_left hfpos hmul.symm).symm
  have hRHS : (∏' χ : galoisCharacter K L,
        (1 - ((χ σ : ℂˣ) : ℂ) * Y)⁻¹)
      = ((1 - Y ^ f) ^ (Nat.card Gal(L/K) / f))⁻¹ := by
    rw [tprod_fintype, Finset.prod_inv_distrib, prod_galoisCharacter_one_sub σ Y, hf]
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L _hunr
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
  haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
  haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
    Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
        (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
      fun _ _ hab ↦ Subtype.ext (by simpa using hab)
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := Fintype.ofFinite _
  have hterm : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ = (1 - Y ^ f)⁻¹ := by
    intro 𝔓
    haveI := 𝔓.2.1
    haveI hlo : 𝔓.1.LiesOver 𝔭 := 𝔓.2.2.1
    have hdeg : (𝔓.1.under (𝓞 K)).inertiaDeg 𝔓.1 = f := by
      rw [Ideal.inertiaDeg_algebraMap, hf]
      exact finrank_residue_eq_orderOf K L σ (frobeniusClass K L 𝔭) (Quotient.out_eq _)
        𝔭 _hunr rfl 𝔓.1 hlo
    haveI : 𝔓.1.LiesOver (𝔓.1.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)
    have hpubot : 𝔓.1.under (𝓞 K) ≠ ⊥ := hlo.over ▸ hpbot
    haveI : (𝔓.1.under (𝓞 K)).IsPrime := hlo.over ▸ ‹𝔭.IsPrime›
    have hnorm : Ideal.absNorm 𝔓.1 = Ideal.absNorm 𝔭 ^ f := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.1 (𝔓.1.under (𝓞 K)) inferInstance hpubot,
        hdeg, ← hlo.over]
    rw [cpow_neg_absNorm_eq_pow f s hnorm, hY]
  rw [tprod_congr hterm, tprod_fintype, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcount, hRHS, Nat.card_eq_fintype_card, inv_pow]

/-! ### Sub-lemmas for `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (leaf G)

The geometry-of-numbers bridge (Sharifi 7.1.19 step 1, p. 142).

For `L = K(μ_m)` cyclotomic, `galoisCharacterOnIdeal K L χ 𝔞 = χ(Frob_𝔞)` on
unramified-supported `𝔞` — i.e. on `𝔞` satisfying `U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞,
UnramifiedIn K L 𝔭` — where `Frob_𝔞 ∈ Gal(L/K)` is the completely-multiplicative ideal Frobenius
(abelian, so a genuine group element, not just a conjugacy class). `U 𝔞` is the exact support
condition `χ(𝔞) ≠ 0`: a single ramified factor zeroes the product. Hence the value-fibre
`{𝔞 : χ(𝔞) = ζ}` (for `ζ ≠ 0`) equals the unramified-supported Frobenius-value-fibre
`{𝔞 : U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, which in turn is a finite union of unramified-supported
Frobenius-fibres `{𝔞 : U 𝔞 ∧ Frob_𝔞 = g}` over `g` in the coset `χ⁻¹(ζ) ⊆ G`. The decomposition:

* `frobeniusIdeal` — the `G`-valued completely-multiplicative ideal Frobenius: the `Multiset.map`-
  product of `(frobeniusClass K L 𝔭).out` over the prime factors, like `galoisCharacterOnIdeal`.
* Helper 1 (`galoisCharacterOnIdeal_eq_char_frobeniusIdeal`) and Helper 1a
  (`card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`) — the cyclotomic identity
  `χ(𝔞) = χ(Frob_𝔞)` on unramified-supported `𝔞` (Sharifi p. 142) and the value-fibre =
  unramified-supported Frobenius-value-fibre set equality.
* L2 (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`) — unramified-supported Frobenius-fibre
  equidistribution `∃ κ, ∀ g, |#{𝔞 ≠ ⊥ : N𝔞 ≤ N, U 𝔞, Frob_𝔞 = g} − κ·N| ≤ C·N^{1−1/d}` with `κ`
  independent of `g`. An unramified-supported `𝔞` splits as (bad part)·(good part), where the bad
  primes (unramified but with `N𝔭` not coprime to `m`) range over a finite set and the good part
  (coprime norm) is counted by the effective lattice-point count L1 on the ideal lattice intersected
  with each congruence sublattice (`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, fed the
  Lipschitz-frontier cover `normLeOne_frontier_lipschitz_cover`); summing over the bad-part set
  keeps `κ` independent of `g`.

Leaf G follows from Helper 1a and L2 (set equality plus coset counting). -/

open Classical in
/-- The `Gal(L/K)`-valued completely-multiplicative **ideal Frobenius**: on a prime `𝔭` it is the
chosen representative `(frobeniusClass K L 𝔭).out` of the Frobenius conjugacy class (a genuine
group element since `Gal(L/K)` is abelian, so the class is a singleton), extended completely
multiplicatively over the prime factorisation. Companion of `galoisCharacterOnIdeal`: the
character value is `χ` applied to this element (Helper 1). The `Multiset.prod` over the (unordered)
prime factors needs commutativity, supplied by `IsMulCommutative Gal(L/K)`. -/
noncomputable def frobeniusIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (𝔞 : Ideal (𝓞 K)) : Gal(L/K) :=
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
    (fun 𝔭 ↦ (frobeniusClass K L 𝔭).out)).prod

open Classical in
/-- `frobeniusIdeal` of a prime is the chosen Frobenius representative. -/
@[simp] theorem frobeniusIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- `frobeniusIdeal` is completely multiplicative on nonzero ideals. -/
theorem frobeniusIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
    UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]

/-- `frobeniusIdeal` of the unit ideal is `1` (empty product). -/
@[simp] theorem frobeniusIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] :
    frobeniusIdeal K L ⊤ = 1 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

open Classical in
/-- **Helper 1 (cyclotomic identity `χ(𝔞) = χ(Frob_𝔞)` on unramified-supported `𝔞`).** For
`L = K(μ_m)` cyclotomic and `𝔞` all of whose prime factors are unramified in `L`, the multiplicative
ideal character `χ(𝔞)` equals `χ` of the ideal Frobenius `Frob_𝔞 = frobeniusIdeal K L 𝔞`.
The support hypothesis `hU : ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭` is the exact condition
under which `galoisCharacterOnIdeal K L χ 𝔞 ≠ 0` (a single ramified factor zeroes the product). -/
theorem galoisCharacterOnIdeal_eq_char_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
    (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) :
    galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ) := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
    rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
      Multiset.map_map, Multiset.map_map]
    rfl
  rw [galoisCharacterOnIdeal_eq_map_prod, hfrob]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 ↦ ?_)
  rw [if_pos (hU 𝔭 h𝔭)]

open Classical in
/-- If the ideal character `χ(𝔞)` is nonzero then every prime factor of `𝔞` is unramified in `L`
(a single ramified factor zeroes the completely-multiplicative product). -/
private theorem unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {𝔞 𝔭 : Ideal (𝓞 K)} (h : galoisCharacterOnIdeal K L χ 𝔞 ≠ 0)
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞) : UnramifiedIn K L 𝔭 := by
  by_contra hnr
  refine h ?_
  rw [galoisCharacterOnIdeal_eq_map_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hnr⟩)

open Classical in
/-- **Helper 1a (cardinality form) — value-fibre = unramified-supported Frobenius-value-fibre.** For
`ζ ≠ 0`, the value-fibre `{𝔞 : χ(𝔞) = ζ}` and the unramified-supported Frobenius-value-fibre
`{𝔞 : U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, where `U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭`, are the
same set, hence have equal `Nat.card`. `U 𝔞` is the exact support condition
`galoisCharacterOnIdeal χ 𝔞 ≠ 0`: a single ramified factor zeroes the product, so the value-fibre
(for `ζ ≠ 0`) contains only `𝔞` with every factor unramified, on which `χ(𝔞) = χ(Frob_𝔞)` by
Helper 1. Keeping the `U` field on the Frobenius side is what makes this an exact equality (the
unconditional `frobeniusIdeal` ignores ramified factors, enlarging the fibre by a `Θ(N)` set). -/
theorem card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (hζ : ζ ≠ 0) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ}
        = Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 ↦ and_congr_right fun h𝔞 ↦
    and_congr_right fun _hN ↦ ?_)
  constructor
  · intro hval
    have hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭 :=
      fun 𝔭 ↦ unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero K L χ
        (hval ▸ hζ)
    exact ⟨hU, by rwa [← galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]⟩
  · rintro ⟨hU, hfrob⟩
    rw [galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]
    exact hfrob

/-- The image of a character `χ` of a finite abelian group is exactly `μ_{orderOf χ}`, so every
`ζ` with `ζ ^ orderOf χ = 1` lies in the image of `χ`. -/
theorem charFibre_mem_range {G : Type*} [CommGroup G] [Finite G] (χ : G →* ℂˣ) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    ∃ g : G, χ g = ζ := by
  classical
  haveI : NeZero (orderOf χ) := ⟨(orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'⟩
  haveI : Finite (MonoidHom.range χ) :=
    Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hpow : ∀ g : G, (χ g) ^ orderOf χ = 1 := fun g ↦ by
    rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have hsub : MonoidHom.range χ ≤ rootsOfUnity (orderOf χ) ℂ := by
    rintro x ⟨g, rfl⟩
    exact (mem_rootsOfUnity (orderOf χ) (χ g)).mpr (hpow g)
  have hpowexp : ∀ g : G, (χ g) ^ Monoid.exponent (MonoidHom.range χ) = 1 := fun g ↦ by
    have hmem : χ g ∈ MonoidHom.range χ := ⟨g, rfl⟩
    simpa using congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨χ g, hmem⟩ : MonoidHom.range χ))
  have hoe : orderOf χ = Monoid.exponent (MonoidHom.range χ) := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact MonoidHom.ext fun g ↦ by simpa [MonoidHom.pow_apply] using hpowexp g
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨x, g, rfl⟩
      exact Subtype.ext (by simpa [Subgroup.coe_pow] using hpow g)
  have heq : MonoidHom.range χ = rootsOfUnity (orderOf χ) ℂ :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity, hoe,
        IsCyclic.exponent_eq_card (α := MonoidHom.range χ)])
  exact χ.mem_range.mp (heq ▸ (mem_rootsOfUnity (orderOf χ) ζ).mpr hζ)

/-- **Helper 1b.** For a character `χ : G →* ℂˣ` of a finite abelian group and any `ζ` with
`ζ ^ orderOf χ = 1`, the fibre `{g : χ g = ζ}` is a coset of `ker χ`, so
`Nat.card {g : χ g = ζ} = Nat.card (MonoidHom.ker χ)`, independent of `ζ`. This `ζ`-independence is
what makes leaf G's leading constant `C = |ker χ| · κ` independent of `ζ`. -/
theorem card_charFibre_eq_card_ker {G : Type*} [CommGroup G] [Finite G] (χ : G →* ℂˣ) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    Nat.card {g : G // χ g = ζ} = Nat.card (MonoidHom.ker χ) := by
  obtain ⟨g₀, hg₀⟩ := charFibre_mem_range χ ζ hζ
  refine Nat.card_congr ((Equiv.subtypeEquivProp ?_).trans (χ.fiberEquivKer g₀))
  ext g
  simp [Set.mem_preimage, hg₀]

/-! ### Sub-lemmas for `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le` (L2: the
unramified-supported Frobenius-fibre equidistribution)

The assembly route: (1) a prime with norm coprime to `m` is unramified in `L = K(μ_m)`
(different-ideal criterion + `minpoly ∣ X^m − 1`); (2) on coprime-norm ideals the cyclotomic
character sends `frobeniusIdeal` to the norm residue (multiplicative extension of
`autToPow_frobeniusClass_out`), and `autToPow` is injective, so the Frobenius fibre IS a
norm-residue class; (3) the per-residue count with one constant across the realized subgroup
is `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`; (4) an unramified-supported
ideal splits uniquely as (bad part)·(good part), where the bad primes — unramified but with
norm sharing a factor with `m` — divide `(m)` and are finitely many; the count regroups as a
sum over bad parts of shifted good counts; (5) with `hm : m % 4 ≠ 2`, either `d ≥ 2` (the
bad-part Euler tail converges) or the bad set is empty (`d = 1`), so the per-bad-part errors
sum to `O(N^{1−1/d})`. -/

section GapBAssembly

/-- A nonzero prime of `𝓞 K` whose norm is coprime to `m` is unramified in `L = K(μ_m)`:
a ramified prime would divide the different ideal, which divides
`(aeval ζ (minpoly 𝓞K ζ).derivative)` by the conductor formula; since `minpoly ∣ X^m − 1`,
that derivative value divides `m·ζ^{m−1}`, so `m ∈ 𝔓`, hence `(m) ≤ 𝔭` and
`N𝔭 ∣ N((m)) = m^d`, contradicting coprimality. -/
private theorem unramifiedIn_of_coprime_absNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    UnramifiedIn K L 𝔭 := by
  classical
  refine ⟨h𝔭, fun 𝔓 h𝔓max h𝔓lo ↦ ?_⟩
  haveI := h𝔓lo
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  rw [← not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
  intro hdvd
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) (NeZero.ne m)
  set ζ𝓞 : 𝓞 L := hζ.toInteger with hζ𝓞
  have hpow : ζ𝓞 ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hdvd_pol : minpoly (𝓞 K) ζ𝓞 ∣ Polynomial.X ^ m - 1 := by
    refine minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral ζ𝓞) ?_
    simp [hpow]
  obtain ⟨g, hg⟩ := hdvd_pol
  have hkey : (m : 𝓞 L) * ζ𝓞 ^ (m - 1)
      = Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))
        * Polynomial.aeval ζ𝓞 g := by
    have hder := congrArg (Polynomial.aeval ζ𝓞 ∘ Polynomial.derivative) hg
    simp only [Function.comp_apply, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.derivative_mul, map_sub, map_mul, map_add,
      map_pow, Polynomial.aeval_X, minpoly.aeval, zero_mul, add_zero,
      sub_zero, Polynomial.aeval_C] at hder
    simpa using hder
  have hadj : Algebra.adjoin K {algebraMap (𝓞 L) L ζ𝓞} = ⊤ := by
    have : algebraMap (𝓞 L) L ζ𝓞 = ζ := hζ.coe_toInteger
    rw [this]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hdiff_dvd : differentIdeal (𝓞 K) (𝓞 L)
      ∣ Ideal.span {Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))} :=
    ⟨conductor (𝓞 K) ζ𝓞, by
      rw [← conductor_mul_differentIdeal (𝓞 K) K L ζ𝓞 hadj]; ring⟩
  have hmem : (m : 𝓞 L) * ζ𝓞 ^ (m - 1) ∈ 𝔓 := by
    rw [hkey]
    exact Ideal.mul_mem_right _ _
      ((Ideal.dvd_iff_le.mp (dvd_trans hdvd hdiff_dvd)) (Ideal.mem_span_singleton_self _))
  have hm𝔓 : ((m : ℕ) : 𝓞 L) ∈ 𝔓 := by
    rcases ‹𝔓.IsPrime›.mem_or_mem hmem with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h
        ((IsUnit.of_pow_eq_one hpow (NeZero.ne m)).pow _)) ‹𝔓.IsPrime›.ne_top
  have hm𝔭 : ((m : ℕ) : 𝓞 K) ∈ 𝔭 := by
    have hmap : algebraMap (𝓞 K) (𝓞 L) ((m : ℕ) : 𝓞 K) ∈ 𝔓 := by
      rwa [map_natCast]
    rw [h𝔓lo.over]
    exact Ideal.mem_comap.mpr hmap
  have hdvd_norm : Ideal.absNorm 𝔭 ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    have hle : Ideal.span {((m : ℕ) : 𝓞 K)} ≤ 𝔭 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hm𝔭
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rwa [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by
        push_cast; rfl,
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
  exact absurd (Ideal.absNorm_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop.pow_right _) dvd_rfl hdvd_norm))
    ‹𝔭.IsPrime›.ne_top

/-- The cyclotomic character sends `frobeniusIdeal` of a coprime-norm ideal to its norm
residue: multiplicative extension of the per-prime `autToPow_frobeniusClass_out` over the
normalized factors. -/
private theorem autToPow_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥)
    (hcop : (Ideal.absNorm 𝔠).Coprime m) :
    hζ.autToPow K (frobeniusIdeal K L 𝔠) = ZMod.unitOfCoprime (Ideal.absNorm 𝔠) hcop := by
  classical
  revert h𝔠 hcop
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h𝔠 _ ↦ absurd rfl h𝔠
  | h₂ u hu =>
      intro _ hcop
      obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
      rw [frobeniusIdeal_one, map_one]
      exact Units.ext (by simp [ZMod.coe_unitOfCoprime])
  | h₃ a p ha hp ih =>
      intro hpa hcop
      have hp' : p ≠ ⊥ := hp.ne_zero
      have ha' : a ≠ ⊥ := ha
      haveI : p.IsPrime := Ideal.isPrime_of_prime hp
      have hsplit : Ideal.absNorm (p * a) = Ideal.absNorm p * Ideal.absNorm a :=
        map_mul Ideal.absNorm p a
      have hcp : (Ideal.absNorm p).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) (hsplit ▸ hcop)
      have hca : (Ideal.absNorm a).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) (hsplit ▸ hcop)
      rw [frobeniusIdeal_mul K L hp' ha', map_mul,
        frobeniusIdeal_apply_prime K L p hp',
        autToPow_frobeniusClass_out K L m hζ p
          (unramifiedIn_of_coprime_absNorm K L m p hp' hcp) hcp,
        ih ha' hca]
      exact Units.ext (by push_cast [ZMod.coe_unitOfCoprime, hsplit]; ring)

open nonZeroDivisors in
/-- The good-fibre count is a norm-residue count: for `h : Gal(L/K)`, the ideals with norm
`≤ X`, norm coprime to `m`, and `frobeniusIdeal = h` are exactly the ideals with norm `≤ X`
and norm residue `(hζ.autToPow K h : ZMod m)` — coprimality and the unramified support come
for free from the residue being a unit, and the Frobenius condition is the residue condition
by injectivity of the cyclotomic character. -/
private theorem card_good_fibre_eq_card_residue
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (h : Gal(L/K)) (X : ℕ) :
    Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ X ∧
        (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = h}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ X ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
          = ((hζ.autToPow K h : (ZMod m)ˣ) : ZMod m)} := by
  classical
  refine Nat.card_congr
    { toFun := fun 𝔠 ↦ ⟨⟨𝔠.1, mem_nonZeroDivisors_of_ne_zero 𝔠.2.1⟩, 𝔠.2.2.1, by
        obtain ⟨𝔠, h0, hX, hcp, hfr⟩ := 𝔠
        subst hfr
        rw [autToPow_frobeniusIdeal K L m hζ 𝔠 h0 hcp, ZMod.coe_unitOfCoprime]⟩
      invFun := fun I ↦ ⟨(I.1 : Ideal (𝓞 K)), ?_⟩
      left_inv := fun 𝔠 ↦ Subtype.ext rfl
      right_inv := fun I ↦ Subtype.ext (Subtype.ext rfl) }
  have h0 : (I.1 : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using nonZeroDivisors.coe_ne_zero I.1
  have hcp : (Ideal.absNorm (I.1 : Ideal (𝓞 K))).Coprime m := by
    refine (ZMod.isUnit_iff_coprime _ m).mp ?_
    rw [I.2.2]
    exact (hζ.autToPow K h).isUnit
  have hfr : frobeniusIdeal K L (I.1 : Ideal (𝓞 K)) = h := by
    refine hζ.autToPow_injective (K := K) ?_
    rw [autToPow_frobeniusIdeal K L m hζ _ h0 hcp]
    exact Units.ext (by rw [ZMod.coe_unitOfCoprime, I.2.2])
  exact ⟨h0, I.2.1, hcp, hfr⟩

/-- The **bad part** of an ideal at level `m`: the product of its normalized prime factors
whose norm is not coprime to `m`. For an unramified-supported ideal these are the finitely
many factors lying over divisors of `m` that are unramified despite `𝔭 ∣ (m)`. -/
private noncomputable def badPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ ¬(Ideal.absNorm 𝔭).Coprime m).prod

/-- The **good part**: the product of the factors with norm coprime to `m`. -/
private noncomputable def goodPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ (Ideal.absNorm 𝔭).Coprime m).prod

section BadGoodSplit

variable (K : Type*) [Field K] [NumberField K] (m : ℕ)

private theorem prod_filter_normalizedFactors_ne_bot (𝔞 : Ideal (𝓞 K))
    (p : Ideal (𝓞 K) → Prop) [DecidablePred p] :
    ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter p).prod ≠ ⊥ :=
  Multiset.prod_ne_zero fun h0 ↦ (UniqueFactorizationMonoid.prime_of_normalized_factor _
    (Multiset.mem_of_mem_filter h0)).ne_zero rfl

private theorem goodPart_mul_badPart (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    goodPart K m 𝔞 * badPart K m 𝔞 = 𝔞 := by
  rw [goodPart, badPart, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self h𝔞

private theorem badPart_ne_bot (𝔞 : Ideal (𝓞 K)) : badPart K m 𝔞 ≠ ⊥ :=
  prod_filter_normalizedFactors_ne_bot K 𝔞 _

private theorem goodPart_ne_bot (𝔞 : Ideal (𝓞 K)) : goodPart K m 𝔞 ≠ ⊥ :=
  prod_filter_normalizedFactors_ne_bot K 𝔞 _

private theorem absNorm_goodPart_coprime (𝔞 : Ideal (𝓞 K)) :
    (Ideal.absNorm (goodPart K m 𝔞)).Coprime m := by
  rw [goodPart, map_multiset_prod]
  refine Multiset.prod_induction (fun n : ℕ ↦ n.Coprime m) _
    (fun a b ha hb ↦ Nat.Coprime.mul_left ha hb) (Nat.coprime_one_left m) fun n hn ↦ ?_
  obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hn
  exact (Multiset.mem_filter.mp h𝔭).2

private theorem mem_factors_badPart {𝔞 : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (badPart K m 𝔞)) :
    𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞 ∧ ¬(Ideal.absNorm 𝔭).Coprime m := by
  classical
  rw [badPart, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun 𝔮 h𝔮 ↦
    UniqueFactorizationMonoid.prime_of_normalized_factor _
      (Multiset.mem_of_mem_filter h𝔮))] at h𝔭
  exact ⟨Multiset.mem_of_mem_filter h𝔭, (Multiset.mem_filter.mp h𝔭).2⟩

/-- Every prime factor of a coprime-norm ideal has coprime norm (a factor's norm divides the
ideal's norm). -/
private theorem coprime_absNorm_of_mem_factors_of_coprime {𝔠 : Ideal (𝓞 K)}
    (hcop : (Ideal.absNorm 𝔠).Coprime m) {𝔮 : Ideal (𝓞 K)}
    (h𝔮 : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠) :
    (Ideal.absNorm 𝔮).Coprime m :=
  Nat.Coprime.coprime_dvd_left
    (Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮))) hcop

/-- **Good part of a coprime·bad product.** If every factor of `𝔠` has coprime norm and every
factor of `𝔟` does not, then the good part of `𝔠 * 𝔟` is `𝔠` (the coprime side of the
factor-filter split). -/
private theorem goodPart_mul_eq {𝔠 𝔟 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
    (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    goodPart K m (𝔠 * 𝔟) = 𝔠 := by
  classical
  rw [goodPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
    Multiset.filter_eq_self.mpr hc, Multiset.filter_eq_nil.mpr hb, add_zero]
  exact Ideal.prod_normalizedFactors_eq_self h𝔠

/-- **Bad part of a coprime·bad product.** Symmetrically, the bad part of `𝔠 * 𝔟` is `𝔟`. -/
private theorem badPart_mul_eq {𝔠 𝔟 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
    (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    badPart K m (𝔠 * 𝔟) = 𝔟 := by
  classical
  rw [badPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
    Multiset.filter_eq_nil.mpr (fun 𝔭 h𝔭 ↦ not_not.mpr (hc 𝔭 h𝔭)),
    Multiset.filter_eq_self.mpr hb, zero_add]
  exact Ideal.prod_normalizedFactors_eq_self h𝔟

end BadGoodSplit

end GapBAssembly

section FibrePartition

open UniqueFactorizationMonoid in
/-- **Per-bad-part fibre bijection (Sharifi 7.2.2 geometry-of-numbers step C).** Fix a nonzero,
"bad-supported" ideal `𝔟` (every factor unramified with norm *not* coprime to `m`) and a target
Frobenius `g`. The unramified-supported ideals `𝔞` of norm `≤ N` with `Frob 𝔞 = g` whose bad part
is exactly `𝔟` are in bijection with the *coprime-norm* ideals `𝔠` of norm `≤ ⌊N / N𝔟⌋` with
`Frob 𝔠 = g · (Frob 𝔟)⁻¹`, via `𝔞 ↦ goodPart 𝔞` (inverse `𝔠 ↦ 𝔠 * 𝔟`). The norm bound transfers
through `N(goodPart 𝔞) · N𝔟 = N𝔞` (`Nat.le_div_iff_mul_le`), the Frobenius condition through
multiplicativity and group cancellation, and the bad/good split through `goodPart_mul_eq` /
`badPart_mul_eq`. -/
private theorem card_fibre_eq_card_good_fibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (g : Gal(L/K)) (N : ℕ) {𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥)
    (hbU : ∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭)
    (hbn : ∀ 𝔭 ∈ normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟}
        = Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ N / Ideal.absNorm 𝔟 ∧
            (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = g * (frobeniusIdeal K L 𝔟)⁻¹} := by
  classical
  have hNb : 0 < Ideal.absNorm 𝔟 :=
    Nat.pos_of_ne_zero fun h ↦ h𝔟 (Ideal.absNorm_eq_zero_iff.mp h)
  refine Nat.card_congr
    { toFun := fun 𝔞 ↦ ⟨goodPart K m 𝔞.1, goodPart_ne_bot K m 𝔞.1, ?_, ?_, ?_⟩
      invFun := fun 𝔠 ↦ ⟨𝔠.1 * 𝔟, ?_, ?_, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨𝔞, h0, hN, _, _, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := hbad ▸ goodPart_mul_badPart K m 𝔞 h0
    refine (Nat.le_div_iff_mul_le hNb).mpr ?_
    rw [← map_mul Ideal.absNorm, hgood]
    exact hN
  · exact absNorm_goodPart_coprime K m 𝔞.1
  · obtain ⟨𝔞, h0, _, _, hfr, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := hbad ▸ goodPart_mul_badPart K m 𝔞 h0
    refine eq_mul_inv_of_mul_eq ?_
    rw [← frobeniusIdeal_mul K L (goodPart_ne_bot K m 𝔞) h𝔟, hgood, hfr]
  · exact mul_ne_zero 𝔠.2.1 h𝔟
  · obtain ⟨𝔠, h0, hN, _, _⟩ := 𝔠
    rw [map_mul Ideal.absNorm]
    exact (Nat.le_div_iff_mul_le hNb).mp hN
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    intro 𝔭 h𝔭
    rw [normalizedFactors_mul h0 h𝔟, Multiset.mem_add] at h𝔭
    rcases h𝔭 with h𝔭 | h𝔭
    · haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor _ h𝔭)
      exact unramifiedIn_of_coprime_absNorm K L m 𝔭
        (prime_of_normalized_factor _ h𝔭).ne_zero
        (coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭)
    · exact hbU 𝔭 h𝔭
  · obtain ⟨𝔠, h0, _, _, hfr⟩ := 𝔠
    rw [frobeniusIdeal_mul K L h0 h𝔟, hfr, inv_mul_cancel_right]
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    exact badPart_mul_eq K m h0 h𝔟
      (fun 𝔭 h𝔭 ↦ coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭) hbn
  · rintro ⟨𝔞, h0, _, _, _, hbad⟩
    apply Subtype.ext
    simp only
    rw [← hbad, goodPart_mul_badPart K m 𝔞 h0]
  · rintro ⟨𝔠, h0, _, hcop, _⟩
    apply Subtype.ext
    simp only
    exact goodPart_mul_eq K m h0 h𝔟
      (fun 𝔭 h𝔭 ↦ coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭) hbn

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
  [IsCyclotomicExtension {m} K L]

open UniqueFactorizationMonoid in
/-- The "bad-supported" ideals of norm `≤ N`: nonzero, with every prime factor unramified in `L`
and of norm not coprime to `m`. -/
private def IsBadPart (N : ℕ) (𝔟 : Ideal (𝓞 K)) : Prop :=
  𝔟 ≠ ⊥ ∧ (∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭 ∧ ¬(Ideal.absNorm 𝔭).Coprime m) ∧
    Ideal.absNorm 𝔟 ≤ N

omit [NumberField L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] [NeZero m]
  [IsCyclotomicExtension {m} K L] in
/-- The bad-supported ideals of norm `≤ N` form a finite set: they are a subset of the (finitely
many) ideals of norm `≤ N`. -/
private theorem finite_isBadPart (N : ℕ) : {𝔟 : Ideal (𝓞 K) | IsBadPart K L m N 𝔟}.Finite :=
  (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).subset fun _ h𝔟 ↦ h𝔟.2.2

open UniqueFactorizationMonoid in
/-- The L2 fibre subtype at `g` is finite (subset of all ideals of norm `≤ N`). -/
private instance finite_L2 (g : Gal(L/K)) (N : ℕ) :
    Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
      (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  exact Finite.of_injective (β := {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N})
    (fun 𝔞 ↦ ⟨𝔞.1, 𝔞.2.2.1⟩)
    (fun _ _ hab ↦ Subtype.ext (by simpa using hab))

omit [FiniteDimensional K L] [NeZero m] [IsCyclotomicExtension {m} K L] in
open UniqueFactorizationMonoid in
/-- **The partition (Sharifi 7.2.2 step B).** The L2 fibre count at `g` is the sum over the finite
bad-part set of the per-bad-part fibre counts. The fibration is `𝔞 ↦ badPart 𝔞`
(`Equiv.sigmaFiberEquiv` + `Nat.card_sigma`); membership `badPart 𝔞 ∈ B_N` uses
`badPart_ne_bot`/`mem_factors_badPart` and `N(badPart) ∣ N𝔞`. -/
private theorem card_L2_eq_sum_fibres (g : Gal(L/K)) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
        = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟} := by
  classical
  set L2 := {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
    (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
  have hbadmem : ∀ 𝔞 : L2, IsBadPart K L m N (badPart K m 𝔞.1) := by
    rintro ⟨𝔞, h0, hN, hU, _⟩
    refine ⟨badPart_ne_bot K m 𝔞, fun 𝔭 h𝔭 ↦ ?_, ?_⟩
    · exact ⟨hU 𝔭 (mem_factors_badPart K m h𝔭).1, (mem_factors_badPart K m h𝔭).2⟩
    · have hdvd : badPart K m 𝔞 ∣ 𝔞 := by
        rw [badPart]
        conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
        exact Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero
        (fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)))
        (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))) hN
  set F : L2 → (finite_isBadPart K L m N).toFinset :=
    fun 𝔞 ↦ ⟨badPart K m 𝔞.1, (finite_isBadPart K L m N).mem_toFinset.mpr (hbadmem 𝔞)⟩
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
    ← Finset.sum_coe_sort (finite_isBadPart K L m N).toFinset]
  refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
  refine Nat.card_congr
    { toFun := fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2,
        Subtype.ext_iff.mp x.2⟩
      invFun := fun y ↦ ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1⟩,
        Subtype.ext y.2.2.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

open UniqueFactorizationMonoid nonZeroDivisors in
/-- **The L2 count as a sum of norm-residue counts.** Chaining the partition
(`card_L2_eq_sum_fibres`), the per-bad-part bijection (`card_fibre_eq_card_good_fibre`), and the
good-fibre↔residue dictionary (`card_good_fibre_eq_card_residue`): the L2 fibre count at `g` is the
sum over the finite bad-part set of the norm-residue counts of modulus `m` at residue
`autToPow (g · Frob(𝔟)⁻¹)`, each up to norm `⌊N / N𝔟⌋`. -/
private theorem card_L2_eq_sum_residue {ζ : L} (hζ : IsPrimitiveRoot ζ m) (g : Gal(L/K)) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
        = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          Nat.card {I : (Ideal (𝓞 K))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
              ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
                = ((hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹) : (ZMod m)ˣ) : ZMod m)} := by
  rw [card_L2_eq_sum_fibres K L m g N]
  refine Finset.sum_congr rfl fun 𝔟 h𝔟 ↦ ?_
  rw [Set.Finite.mem_toFinset] at h𝔟
  obtain ⟨h0, hbfac, _⟩ := h𝔟
  rw [card_fibre_eq_card_good_fibre K L m g N h0 (fun 𝔭 h ↦ (hbfac 𝔭 h).1)
      (fun 𝔭 h ↦ (hbfac 𝔭 h).2),
    card_good_fibre_eq_card_residue K L m hζ (g * (frobeniusIdeal K L 𝔟)⁻¹) (N / Ideal.absNorm 𝔟)]

end FibrePartition

section L2Assembly

/-! ### The κ-uniformity input: realizing the cyclotomic-character image as norm residues

To apply the ICC κ-uniform count (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`) we
must produce its Fourier-decay hypothesis `hF`, which the ICC producer
`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` derives from the **realizer hypothesis**
`hS`: every element of the residue subgroup `S` is the norm residue `(N𝔟 mod m)` of some nonzero
ideal `𝔟`. We take `S = range (autToPow)` (the image of the cyclotomic character) and prove `hS` via
the coprime-restricted Frobenii-generation theorem
`subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
(CNR): the set `R` of realized residues is a subgroup, and its `autToPow`-preimage contains the
Frobenius of every coprime-norm unramified prime (`autToPow_frobeniusClass_out`), hence is `⊤`, so
every `autToPow`-value is realized. -/

open nonZeroDivisors in
/-- The **realized-residue subgroup** `R ≤ (ℤ/m)ˣ`: the residues `a` that are the norm residue
`(N𝔟 mod m)` of some nonzero ideal `𝔟` of `𝓞 K`. A genuine subgroup: `1` is realized by `⊤`
(`N⊤ = 1`), products by ideal products (`absNorm_mul`), and inverses by the finite-order power
`𝔟^{ord a − 1}` (so `N(𝔟^{ord a − 1}) ↦ a^{ord a − 1} = a⁻¹`). -/
private noncomputable def realizedResidues (K : Type*) [Field K] [NumberField K] (m : ℕ)
    [NeZero m] : Subgroup (ZMod m)ˣ where
  carrier := {a : (ZMod m)ˣ | ∃ 𝔟 : (Ideal (𝓞 K))⁰,
    ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m)}
  one_mem' := ⟨1, by
    rw [Submonoid.coe_one, Ideal.one_eq_top, Ideal.absNorm_top, Nat.cast_one, Units.val_one]⟩
  mul_mem' := by
    rintro a b ⟨𝔟₁, h₁⟩ ⟨𝔟₂, h₂⟩
    exact ⟨𝔟₁ * 𝔟₂, by rw [Submonoid.coe_mul, map_mul, Nat.cast_mul, h₁, h₂, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨𝔟, h⟩
    refine ⟨𝔟 ^ (orderOf a - 1), ?_⟩
    have hpow : ((𝔟 ^ (orderOf a - 1) : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = (𝔟 : Ideal (𝓞 K)) ^ (orderOf a - 1) := by push_cast; ring
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := inv_eq_of_mul_eq_one_right
      (by rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one])
    rw [hpow, map_pow, Nat.cast_pow, h, hinv, Units.val_pow_eq_pow_val]

open nonZeroDivisors in
/-- **Every cyclotomic-character value is a realized norm residue.** The image
`range (hζ.autToPow K)` is contained in the realized-residue subgroup `realizedResidues K m`:
applying the coprime-restricted Frobenii-generation
`subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
to `H = comap (autToPow) R` (which contains every coprime-norm unramified prime's Frobenius, since
`autToPow_frobeniusClass_out` realizes it as `N𝔭 mod m` with the prime `𝔭` itself as the realizer)
forces `H = ⊤`, i.e. every `autToPow`-value lies in `R`. -/
private theorem autToPow_range_le_realizedResidues
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow K).range ≤ realizedResidues K m := by
  set R := realizedResidues K m with hR
  set H := Subgroup.comap (hζ.autToPow K) R with hH
  have hHtop : H = ⊤ := by
    refine subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L m H
      (fun 𝔭 h𝔭p h𝔭ne h𝔭unr h𝔭cop ↦ ?_)
    haveI := h𝔭p
    rw [hH, Subgroup.mem_comap, autToPow_frobeniusClass_out K L m hζ 𝔭 h𝔭unr h𝔭cop]
    exact ⟨⟨𝔭, mem_nonZeroDivisors_of_ne_zero h𝔭ne⟩, by rw [ZMod.coe_unitOfCoprime]⟩
  intro a ha
  obtain ⟨g, rfl⟩ := ha
  have : g ∈ H := hHtop ▸ Subgroup.mem_top g
  rwa [hH, Subgroup.mem_comap] at this

open nonZeroDivisors in
/-- The **realizer hypothesis** `hS` for `S = range (hζ.autToPow K)`, in the exact shape consumed by
the ICC producer `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`: every residue in the
cyclotomic-character image is the norm residue of some nonzero ideal. -/
private theorem realizes_autToPow_range
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    ∀ a ∈ (hζ.autToPow K).range, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m) :=
  fun _ ha ↦ autToPow_range_le_realizedResidues K L m hζ ha

/-! ### The bad-part Euler tail bound

The L2 error assembly sums per-bad-part residue counts over the finite bad-part set. The error
control reduces to bounding `∑_{𝔟 ∈ badFinset N} (N𝔟)^e` for a negative real exponent `e`, uniformly
in `N`. Since every bad-supported `𝔟` factors as `∏_{𝔭 ∈ P} 𝔭^{e_𝔭}` over the **fixed finite**
bad-prime set `P` (`finite_badPrimes`), the sum injects into the exponent vectors
`P → {0,…,⌊log₂ N⌋}`
and the product-of-sums expansion (`Finset.prod_sum`) bounds it by the convergent geometric Euler
product `∏_{𝔭 ∈ P} (1 − (N𝔭)^e)⁻¹` (each factor `< 1` since `N𝔭 ≥ 2` and `e < 0`). -/

/-- `a ^ (count a s)` divides `s.prod`: the `count a s` copies of `a` form a sub-multiset of `s`. -/
private theorem pow_count_dvd_prod {α : Type*} [CommMonoid α] [DecidableEq α] (a : α)
    (s : Multiset α) : a ^ s.count a ∣ s.prod :=
  (Multiset.prod_replicate (s.count a) a) ▸
    Multiset.prod_dvd_prod_of_le (Multiset.le_count_iff_replicate_le.mp le_rfl)

/-- A nonzero ideal `𝔠` whose normalized factors all lie in a finite set `P` factors as
`𝔠 = ∏_{𝔭 ∈ P} 𝔭 ^ count 𝔭`, the count being its multiplicity in `normalizedFactors 𝔠`. -/
private theorem prod_pow_count_normalizedFactors_eq (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) {𝔠 : Ideal (𝓞 K)} (h0 : 𝔠 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, 𝔭 ∈ P) :
    𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔠).count 𝔭 := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
  rw [Finset.prod_multiset_count]
  refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
  intro 𝔭 _ hnotin
  rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]

/-- The multiplicity of a nonzero prime `𝔭` in a nonzero ideal `𝔟` of norm `≤ N` is at most
`Nat.log 2 N`: `𝔭 ^ count ∣ 𝔟` forces `2 ^ count ≤ N𝔭 ^ count ≤ N𝔟 ≤ N`. -/
private theorem count_normalizedFactors_le_log {K : Type*} [Field K] [NumberField K]
    {𝔭 𝔟 : Ideal (𝓞 K)} (h𝔭p : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥) (hb0 : 𝔟 ≠ ⊥) {N : ℕ}
    (hbN : Ideal.absNorm 𝔟 ≤ N) :
    (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ≤ Nat.log 2 N := by
  have hk : 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ∣ 𝔟 := by
    have hd := pow_count_dvd_prod 𝔭 (UniqueFactorizationMonoid.normalizedFactors 𝔟)
    rwa [Ideal.prod_normalizedFactors_eq_self hb0] at hd
  have hN𝔭2 : 2 ≤ Ideal.absNorm 𝔭 := by
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭p.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭0 (Ideal.absNorm_eq_zero_iff.mp h)
    omega
  have hb0' : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hb0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hdvd : Ideal.absNorm 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭
      ∣ Ideal.absNorm 𝔟 := by
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hk); rwa [map_pow] at this
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hN𝔭2 _)
    (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0') hdvd) hbN))

/-- The real `e`-power of the norm of a nonzero ideal `𝔟` supported on `P` distributes over the
prime factorization: `(N𝔟)^e = ∏_{𝔭 ∈ P} ((N𝔭)^e) ^ count 𝔭` (product over `P.attach`). -/
private theorem absNorm_rpow_eq_prod_attach_count (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) {𝔟 : Ideal (𝓞 K)} (h0 : 𝔟 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) (e : ℝ) :
    (Ideal.absNorm 𝔟 : ℝ) ^ e = ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^
      (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭.1 := by
  have hNprod : Ideal.absNorm 𝔟 =
      ∏ 𝔭 ∈ P, (Ideal.absNorm 𝔭) ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 := by
    conv_lhs => rw [prod_pow_count_normalizedFactors_eq K P h0 hP, map_prod]
    exact Finset.prod_congr rfl fun 𝔭 _ ↦ by rw [map_pow]
  rw [Finset.prod_attach P
    (fun 𝔭 ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^
      (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭), hNprod]
  push_cast
  rw [← Real.finsetProd_rpow P _ (fun 𝔭 _ ↦ by positivity) e]
  refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
  rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭 : ℝ)) _,
    ← Real.rpow_natCast (((Ideal.absNorm 𝔭 : ℝ)) ^ e) _,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]

/-- **The bad-part Euler bound** (negative-exponent geometry-of-numbers tail). For a finite set `P`
of nonzero primes and a finite set `BF` of ideals each nonzero, supported on `P`
(`∀ 𝔭 ∈ normalizedFactors 𝔟, 𝔭 ∈ P`), and of norm `≤ N`, if every `(N𝔭)^e < 1` (`𝔭 ∈ P`), then
`∑_{𝔟 ∈ BF} (N𝔟)^e ≤ ∏_{𝔭 ∈ P} (1 − (N𝔭)^e)⁻¹`. Proof: each `𝔟 = ∏_{𝔭 ∈ P} 𝔭^{count 𝔭}`
(`Ideal.prod_normalizedFactors_eq_self` + `Finset.prod_multiset_count`), so `(N𝔟)^e =
∏_{𝔭} ((N𝔭)^e)^{count 𝔭}`; the count map `𝔟 ↦ (count 𝔭)_{𝔭 ∈ P}` is injective into the bounded
exponent vectors (`count 𝔭 ≤ ⌊log₂ N⌋` since `𝔭^{count} ∣ 𝔟` and `N𝔭 ≥ 2`), and `Finset.prod_sum`
turns `∏_𝔭 ∑_{k ≤ ⌊log₂ N⌋} ((N𝔭)^e)^k` into a sum over those vectors dominating the `BF`-sum; the
geometric partial sum is `≤ (1 − (N𝔭)^e)⁻¹` (`geom_sum_mul`). -/
private theorem sum_rpow_le_euler_prod (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) (hPprime : ∀ 𝔭 ∈ P, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥)
    (N : ℕ) (BF : Finset (Ideal (𝓞 K)))
    (hBF : ∀ 𝔟 ∈ BF, 𝔟 ≠ ⊥ ∧
      (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) ∧ Ideal.absNorm 𝔟 ≤ N)
    (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  classical
  set Kn := Nat.log 2 N with hKn
  have hx0 : ∀ 𝔭 ∈ P, (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ)) ^ e :=
    fun 𝔭 _ ↦ Real.rpow_nonneg (by positivity) e
  set cnt : Ideal (𝓞 K) → ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) :=
    fun 𝔟 𝔭 _ ↦ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 with hcnt
  set F : ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) → ℝ :=
    fun g ↦ ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (g 𝔭.1 𝔭.2) with hF
  have hterm : ∀ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e = F (cnt 𝔟) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 h𝔟
    simpa only [hF, hcnt] using absNorm_rpow_eq_prod_attach_count K P hb0 hbP e
  have hmaps : ∀ 𝔟 ∈ BF, cnt 𝔟 ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, hbN⟩ := hBF 𝔟 h𝔟
    rw [Finset.mem_pi]; intro 𝔭 h𝔭
    rw [hcnt]; simp only; rw [Finset.mem_range, Nat.lt_succ_iff]
    obtain ⟨h𝔭p, h𝔭0⟩ := hPprime 𝔭 h𝔭
    exact count_normalizedFactors_le_log h𝔭p h𝔭0 hb0 hbN
  have hinj : Set.InjOn cnt BF := by
    intro 𝔞 ha 𝔟 hb hcnteq
    obtain ⟨ha0, haP, _⟩ := hBF 𝔞 ha
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 hb
    have hcc : ∀ 𝔭 ∈ P, (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭
        = (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 :=
      fun 𝔭 h𝔭 ↦ congrFun (congrFun hcnteq 𝔭) h𝔭
    rw [prod_pow_count_normalizedFactors_eq K P ha0 haP,
      prod_pow_count_normalizedFactors_eq K P hb0 hbP]
    exact Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ by rw [hcc 𝔭 h𝔭]
  calc ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      = ∑ 𝔟 ∈ BF, F (cnt 𝔟) := Finset.sum_congr rfl hterm
    _ = ∑ g ∈ BF.image cnt, F g := (Finset.sum_image (fun a ha b hb ↦ hinj ha hb)).symm
    _ ≤ ∑ g ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)), F g := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun g _ _ ↦
          Finset.prod_nonneg fun 𝔭 _ ↦ pow_nonneg (hx0 𝔭.1 𝔭.2) _)
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨𝔟, h𝔟, rfl⟩ := hg
        exact hmaps 𝔟 h𝔟
    _ = ∏ 𝔭 ∈ P, ∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k := by
        rw [Finset.prod_sum P (fun _ ↦ Finset.range (Kn + 1))
          (fun 𝔭 k ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)]
    _ ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
        refine Finset.prod_le_prod
          (fun 𝔭 h𝔭 ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hx0 𝔭 h𝔭) k) (fun 𝔭 h𝔭 ↦ ?_)
        have h1x : 0 < 1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e := by have := hxlt 𝔭 h𝔭; linarith
        have hkey := geom_sum_mul (((Ideal.absNorm 𝔭 : ℝ)) ^ e) (Kn + 1)
        have hxK : (0 : ℝ) ≤ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := pow_nonneg (hx0 𝔭 h𝔭) _
        have hmul : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)
            = 1 - (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := by nlinarith [hkey]
        have hle : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e) ≤ 1 := by rw [hmul]; linarith
        rw [← le_div_iff₀ h1x] at hle; rwa [one_div] at hle

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
  [IsCyclotomicExtension {m} K L]

omit [NumberField L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] [NeZero m]
  [IsCyclotomicExtension {m} K L] in
open UniqueFactorizationMonoid in
/-- The finite **bad-part set** `badFinset N = {𝔟 : IsBadPart}` grows with the norm bound `N`. -/
private theorem badFinset_subset_of_le {N M : ℕ} (hNM : N ≤ M) :
    (finite_isBadPart K L m N).toFinset ⊆ (finite_isBadPart K L m M).toFinset := by
  intro 𝔟 h
  rw [Set.Finite.mem_toFinset] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.trans hNM⟩

omit [NumberField L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
  [IsCyclotomicExtension {m} K L] in
open UniqueFactorizationMonoid in
/-- The bad-part Euler bound specialised to `BF = badFinset N`, `P = badPrimes`: for a negative
exponent `e` (more precisely `(N𝔭)^e < 1` on the finite bad-prime set), the bad-part norm sum is
bounded by the geometric Euler product over the bad primes, **uniformly in `N`**. -/
private theorem sum_rpow_badFinset_le (N : ℕ) (e : ℝ)
    (hxlt : ∀ 𝔭 ∈ (finite_badPrimes K m).toFinset, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ (finite_badPrimes K m).toFinset, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  refine sum_rpow_le_euler_prod K (finite_badPrimes K m).toFinset (fun 𝔭 h𝔭 ↦ ?_) N _
    (fun 𝔟 h𝔟 ↦ ?_) e hxlt
  · rw [Set.Finite.mem_toFinset] at h𝔭; exact ⟨h𝔭.1, h𝔭.2.1⟩
  · rw [Set.Finite.mem_toFinset] at h𝔟
    refine ⟨h𝔟.1, fun 𝔭 h𝔭 ↦ ?_, h𝔟.2.2⟩
    have hprime := prime_of_normalized_factor 𝔭 h𝔭
    rw [Set.Finite.mem_toFinset]
    exact ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, (h𝔟.2.1 𝔭 h𝔭).2⟩

open nonZeroDivisors in
/-- **(C) The `g`-uniform per-residue ideal count.** Combining the ICC κ-uniform count
(`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`) at the subgroup `S = range autToPow`
with its Fourier-decay hypothesis `hF` discharged by the ICC producer
(`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`) fed the realizer hypothesis
(`realizes_autToPow_range`): there is one pair `(κ₀, C₀)` so that for every residue
`a ∈ range autToPow` and every `N ≥ 1`, the count of nonzero ideals with `N(I) ≤ N` and
`N(I) ≡ a (mod m)` is `κ₀·N + O(N^{1−1/d})`. The residues `autToPow (g·Frob𝔟⁻¹)` arising in the L2
sum all lie in this range, so the same `(κ₀, C₀)` governs every good-fibre count. -/
private theorem exists_kappa_uniform {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    ∃ κ₀ C₀ : ℝ, ∀ a ∈ (hζ.autToPow K).range, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m)} : ℝ)
          - κ₀ * N|
        ≤ C₀ * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) :=
  exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform K m (hζ.autToPow K).range
    (fun χ hχ ↦ tendsto_sum_char_mul_cardNormLeResidue_div_of_realized K m (hζ.autToPow K).range
      (realizes_autToPow_range K L m hζ) χ hχ)

/-- **Per-bad-part floor→real-division error transfer** (real-arithmetic kernel of the L2 error
assembly). Given the `g`-uniform residue-count estimate `heff` for the integer window `⌊N/Nb⌋`
(`Nb := N𝔟 ∈ [1, N]`), the error against the *real* target `κ₀·(N/Nb)` is controlled by the
real-power tail `C₀·N^α·Nb^{e₂}` plus the floor slack `|κ₀|`, where `α = -e₂`. The two extra
pieces are: the floor-rounding slack `N/Nb − ⌊N/Nb⌋ ∈ [0, 1]` (triangle inequality), and the
window-power bound `⌊N/Nb⌋^α ≤ (N/Nb)^α = N^α·Nb^{e₂}`. -/
private theorem abs_sub_kappa_mul_div_le {N Nb : ℕ} {RCb κ₀ C₀ α e₂ : ℝ} (hNb : 0 < Nb)
    (hαnn : 0 ≤ α) (hαe₂ : α = -e₂) (hC₀nn : 0 ≤ C₀)
    (heff : |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)| ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α) :
    |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))| ≤ C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| := by
  have hbposR : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast hNb
  have hWle : ((N / Nb : ℕ) : ℝ) ≤ (N : ℝ) / (Nb : ℝ) := by
    rw [le_div_iff₀ hbposR]; exact_mod_cast Nat.div_mul_le_self N Nb
  have hWslack : (N : ℝ) / (Nb : ℝ) - ((N / Nb : ℕ) : ℝ) ≤ 1 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hbposR]
    have hlt : N < (N / Nb + 1) * Nb := by
      have hm := Nat.mod_lt N hNb; have hdm := Nat.div_add_mod N Nb
      rw [add_mul, one_mul, mul_comm]; omega
    have : (N : ℝ) < ((N / Nb : ℕ) + 1) * (Nb : ℝ) := by exact_mod_cast hlt
    nlinarith [this]
  have hpow_le : ((N / Nb : ℕ) : ℝ) ^ α ≤ (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ := by
    have heq : (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ = ((N : ℝ) / (Nb : ℝ)) ^ α := by
      rw [Real.div_rpow (Nat.cast_nonneg N) hbposR.le, div_eq_mul_inv]
      congr 1
      rw [hαe₂, Real.rpow_neg hbposR.le, inv_inv]
    rw [heq]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hWle hαnn
  calc |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))|
      ≤ |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)|
        + |κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ))| := by
        simpa using abs_add_le (RCb - κ₀ * ((N / Nb : ℕ) : ℝ))
          (κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ)))
    _ ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α + |κ₀| * 1 := by
        gcongr
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> [linarith [hWle]; linarith [hWslack]]
    _ ≤ C₀ * ((N : ℝ) ^ α * (Nb : ℝ) ^ e₂) + |κ₀| := by rw [mul_one]; gcongr
    _ = C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| := by ring

open UniqueFactorizationMonoid in
/-- **The bad-part inverse-norm tail bound.** With `e₂ = 1/d − 1 < 0`, the bad-part partial sum
`T_N = ∑_{𝔟 ∈ badFinset N} (N𝔟)⁻¹` converges to `T = ⨆_N T_N` with tail
`T − T_N ≤ N^{−1/d}·E₂`, where `E₂` bounds the `e₂`-Euler sum (`hEuler`). On the difference set
`badFinset M ∖ badFinset N` (`N ≤ M`) each `N𝔟 > N`, so `(N𝔟)⁻¹ = (N𝔟)^{e₂}·(N𝔟)^{−1/d} ≤
N^{−1/d}·(N𝔟)^{e₂}`; summing and using `hEuler` gives `T_M − T_N ≤ N^{−1/d}·E₂` for all `M`. -/
private theorem ciSup_sum_inv_absNorm_sub_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {d : ℕ} {e₂ E₂ : ℝ} (he₂ : e₂ = (d : ℝ)⁻¹ - 1)
    (hE₂nn : 0 ≤ E₂)
    (hEuler : ∀ M : ℕ, ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset,
        ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂)
    (N : ℕ) (hN1 : 1 ≤ N) :
    (⨆ M : ℕ, ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹)
        - ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹
      ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := by
  set Tfun : ℕ → ℝ :=
    fun N ↦ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTmono : Monotone Tfun := fun N M hNM ↦
    Finset.sum_le_sum_of_subset_of_nonneg (badFinset_subset_of_le K L m hNM)
      (fun 𝔟 _ _ ↦ by positivity)
  have hNrpow_nn : (0 : ℝ) ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [sub_le_iff_le_add]
  refine ciSup_le fun M ↦ ?_
  rcases le_or_gt N M with hNM | hMN
  · have hsub : (finite_isBadPart K L m N).toFinset ⊆ (finite_isBadPart K L m M).toFinset :=
      badFinset_subset_of_le K L m hNM
    have hdiff : Tfun M - Tfun N
        = ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset \ (finite_isBadPart K L m N).toFinset,
            ((Ideal.absNorm 𝔟 : ℝ))⁻¹ := by
      simp only [hTfun]
      rw [sub_eq_iff_eq_add', ← Finset.sum_sdiff hsub, add_comm]
    have hperb : ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset \ (finite_isBadPart K L m N).toFinset,
          ((Ideal.absNorm 𝔟 : ℝ))⁻¹
        ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) *
          ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun 𝔟 h𝔟 ↦ ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun 𝔟 _ _ ↦ mul_nonneg hNrpow_nn (Real.rpow_nonneg (by positivity) _)))
      rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨hin, hnotin⟩ := h𝔟
      have hb0 : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hin.1 (Ideal.absNorm_eq_zero_iff.mp h)
      have hNb : N < Ideal.absNorm 𝔟 := by
        by_contra h; push Not at h; exact hnotin ⟨hin.1, hin.2.1, h⟩
      have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hb0
      have hNbR : (N : ℝ) ≤ (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hNb.le
      have hsplit : (Ideal.absNorm 𝔟 : ℝ)⁻¹
          = (Ideal.absNorm 𝔟 : ℝ) ^ e₂ * (Ideal.absNorm 𝔟 : ℝ) ^ (-(d : ℝ)⁻¹) := by
        rw [← Real.rpow_add hbposR, he₂,
          (by ring : ((d : ℝ)⁻¹ - 1) + (-(d : ℝ)⁻¹) = -1), Real.rpow_neg_one]
      rw [hsplit, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN1) hNbR (neg_nonpos.mpr (by positivity)))
        (le_of_lt (Real.rpow_pos_of_pos hbposR _))
    have : Tfun M - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ :=
      hdiff ▸ le_trans hperb (mul_le_mul_of_nonneg_left (hEuler M) hNrpow_nn)
    linarith
  · have : Tfun M ≤ Tfun N := hTmono hMN.le
    nlinarith [mul_nonneg hNrpow_nn hE₂nn]

open UniqueFactorizationMonoid in
/-- **The bad-part finset cardinality bound** `|badFinset N| ≤ N^α·E₂` (with `α = -e₂`). Each
`𝔟 ∈ badFinset N` has `N𝔟 ≤ N`, so `1 = (N𝔟)^α·(N𝔟)^{e₂} ≤ N^α·(N𝔟)^{e₂}`; summing the constant
`1` over the finset and bounding by the `e₂`-Euler sum `E₂` (`hsumE₂`) gives the result. -/
private theorem card_finite_isBadPart_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {α e₂ E₂ : ℝ} (hαnn : 0 ≤ α) (hαe₂ : α = -e₂)
    (N : ℕ) (hNα_nn : 0 ≤ (N : ℝ) ^ α)
    (hsumE₂ : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂) :
    (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) ≤ (N : ℝ) ^ α * E₂ := by
  calc (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ)
      = ∑ _𝔟 ∈ (finite_isBadPart K L m N).toFinset, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
        refine Finset.sum_le_sum fun 𝔟 h𝔟 ↦ ?_
        rw [Set.Finite.mem_toFinset] at h𝔟
        have hbpos : 0 < Ideal.absNorm 𝔟 :=
          Nat.pos_of_ne_zero fun h ↦ h𝔟.1 (Ideal.absNorm_eq_zero_iff.mp h)
        have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hbpos
        have hbNR : (Ideal.absNorm 𝔟 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h𝔟.2.2
        have h1eq : (1 : ℝ) = (Ideal.absNorm 𝔟 : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
          rw [← Real.rpow_add hbposR, hαe₂, neg_add_cancel, Real.rpow_zero]
        rw [h1eq]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hbposR.le hbNR hαnn)
          (Real.rpow_pos_of_pos hbposR _).le
    _ = (N : ℝ) ^ α * ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ α * E₂ := mul_le_mul_of_nonneg_left hsumE₂ hNα_nn

/-! ### The final error assembly

With the `g`-uniform per-residue constants `(κ₀, C₀)` (`exists_kappa_uniform`) and the uniform
bad-part Euler bounds (`sum_rpow_badFinset_le`), the L2 fibre count
`count_g(N) = ∑_{𝔟 ∈ badFinset N} RC(autToPow(g·Frob𝔟⁻¹), ⌊N/N𝔟⌋)` (`card_L2_eq_sum_residue`) is
estimated by a triangle inequality into three pieces, each `O(N^{1−1/d})`:
* the per-bad-part effective errors `∑_𝔟 |RC − κ₀·⌊N/N𝔟⌋|`, bounded via `(κ₀, C₀)`;
* the floor-rounding slack `κ₀·∑_𝔟 (⌊N/N𝔟⌋ − N/N𝔟)`, each term in `[−1,0]`;
* the bad-part tail `κ₀·N·(T − T_N)`, where `T = ⨆_N ∑_{𝔟 ∈ badFinset N} (N𝔟)⁻¹` and the tail
  `T − T_N ≤ N^{−1/d}·E₂` is read off the Euler bound at exponent `1/d − 1` on the difference set.
The leading constant is `κ = κ₀·T`, `g`-independent. This needs `d ≥ 2` so that `1/d − 1 < 0` and
the Euler products converge; the `d = 1` (`K = ℚ`) case has an **empty** bad-prime set
(`badFinset N = {⊤}`) and is handled separately. -/

open UniqueFactorizationMonoid nonZeroDivisors in
/-- **The L2 fibre bound, `d ≥ 2` branch.** The bad-part Euler tail converges. -/
private theorem card_fibre_bound_two_le {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set d : ℕ := Module.finrank ℚ K
  set α : ℝ := 1 - (d : ℝ)⁻¹ with hα
  set e₂ : ℝ := (d : ℝ)⁻¹ - 1 with he₂
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by lia)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have he₂neg : e₂ < 0 := by
    have hle : (d : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
    rw [he₂]; linarith [hle, (by norm_num : (2 : ℝ)⁻¹ < 1)]
  have hαnn : 0 ≤ α := by rw [hα]; linarith [he₂neg, he₂]
  have hαe₂ : α = -e₂ := by rw [hα, he₂]; ring
  set P : Finset (Ideal (𝓞 K)) := (finite_badPrimes K m).toFinset with hP
  have hN𝔭2 : ∀ 𝔭 ∈ P, (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    intro 𝔭 h𝔭
    rw [hP, Set.Finite.mem_toFinset] at h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h => h𝔭.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by lia)
  have hxlt : ∀ e : ℝ, e < 0 → ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1 := by
    intro e he 𝔭 h𝔭
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN𝔭2 𝔭 h𝔭]) he
  have hxlt1 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ) < 1 := hxlt _ (by norm_num)
  have hxlt2 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂ < 1 := hxlt _ he₂neg
  set E₁ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ))⁻¹
  set E₂ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂)⁻¹ with hE₂
  obtain ⟨κ₀, C₀, hunif⟩ := exists_kappa_uniform K L m hζ
  set Tfun : ℕ → ℝ :=
    fun N => ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTfun_eq : ∀ N, Tfun N
      = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ (-1 : ℝ) := by
    intro N
    rw [hTfun]; refine Finset.sum_congr rfl fun 𝔟 _ => ?_
    rw [Real.rpow_neg_one]
  have hTbdd : ∀ N, Tfun N ≤ E₁ := fun N => by
    rw [hTfun_eq N]; exact sum_rpow_badFinset_le K L m N (-1) hxlt1
  have hTmono : Monotone Tfun := by
    intro N M hNM
    exact Finset.sum_le_sum_of_subset_of_nonneg (badFinset_subset_of_le K L m hNM)
      (fun 𝔟 _ _ => by positivity)
  set T : ℝ := ⨆ N, Tfun N
  have hTbddAbove : BddAbove (Set.range Tfun) := ⟨E₁, fun y ⟨N, hN⟩ => hN ▸ hTbdd N⟩
  have hTfun_le_T : ∀ N, Tfun N ≤ T := fun N => le_ciSup hTbddAbove N
  have hE₂nn : 0 ≤ E₂ := by
    rw [hE₂]; refine Finset.prod_nonneg fun 𝔭 h𝔭 => ?_
    have := hxlt2 𝔭 h𝔭; positivity
  have htail : ∀ N : ℕ, 1 ≤ N → T - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := fun N hN1 =>
    ciSup_sum_inv_absNorm_sub_le K L m he₂ hE₂nn
      (fun M => sum_rpow_badFinset_le K L m M e₂ hxlt2) N hN1
  refine ⟨κ₀ * T, (C₀ + 2 * |κ₀|) * E₂, fun g N hN1 => ?_⟩
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNα_nn : (0 : ℝ) ≤ (N : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [card_L2_eq_sum_residue K L m hζ g N, Nat.cast_sum]
  set a : Ideal (𝓞 K) → (ZMod m)ˣ :=
    fun 𝔟 => hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹)
  set RC : Ideal (𝓞 K) → ℝ := fun 𝔟 =>
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m)) = ((a 𝔟 : (ZMod m)ˣ) : ZMod m)} : ℝ)
  change |(∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, RC 𝔟) - κ₀ * T * (N : ℝ)| ≤ _
  have hamem : ∀ 𝔟, a 𝔟 ∈ (hζ.autToPow K).range := fun 𝔟 => ⟨_, rfl⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h := hunif 1 (one_mem _) 1 (le_refl 1)
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hbadmem : ∀ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
      𝔟 ≠ ⊥ ∧ Ideal.absNorm 𝔟 ≤ N := fun 𝔟 h𝔟 => by
    rw [Set.Finite.mem_toFinset] at h𝔟; exact ⟨h𝔟.1, h𝔟.2.2⟩
  have hperbad : ∀ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
      |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀| := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbN⟩ := hbadmem 𝔟 h𝔟
    have hbpos : 0 < Ideal.absNorm 𝔟 :=
      Nat.pos_of_ne_zero fun h => hb0 (Ideal.absNorm_eq_zero_iff.mp h)
    exact abs_sub_kappa_mul_div_le hbpos hαnn hαe₂ hC₀nn
      (hunif (a 𝔟) (hamem 𝔟) _ ((Nat.one_le_div_iff hbpos).mpr hbN))
  have hsum_div : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)
      = (N : ℝ) * Tfun N := by
    rw [hTfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔟 _ => ?_
    rw [div_eq_mul_inv]
  have hsumE₂ : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂ :=
    sum_rpow_badFinset_le K L m N e₂ hxlt2
  have hcard_le : (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) ≤ (N : ℝ) ^ α * E₂ :=
    card_finite_isBadPart_le K L m hαnn hαe₂ N hNα_nn hsumE₂
  have hA : |∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
        (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)))|
      ≤ (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
            (C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀|) :=
          Finset.sum_le_sum hperbad
      _ = C₀ * (N : ℝ) ^ α * (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
            (Ideal.absNorm 𝔟 : ℝ) ^ e₂)
          + |κ₀| * (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ C₀ * (N : ℝ) ^ α * E₂ + |κ₀| * ((N : ℝ) ^ α * E₂) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hsumE₂ (mul_nonneg hC₀nn hNα_nn))
            (mul_le_mul_of_nonneg_left hcard_le (abs_nonneg _))
      _ = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by ring
  have hB : |κ₀ * ((∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
        (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ))|
      ≤ |κ₀| * ((N : ℝ) ^ α * E₂) := by
    rw [hsum_div, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hTrw : (N : ℝ) * Tfun N - T * (N : ℝ) = -((N : ℝ) * (T - Tfun N)) := by ring
    rw [hTrw, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (sub_nonneg.mpr (hTfun_le_T N)))]
    refine le_trans (mul_le_mul_of_nonneg_left (htail N hN1) (Nat.cast_nonneg N)) ?_
    rw [← mul_assoc, hα]
    have hNmul : (N : ℝ) * (N : ℝ) ^ (-(d : ℝ)⁻¹) = (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
      nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNposR, sub_eq_add_neg]
    rw [hNmul]
  have hdecomp : (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, RC 𝔟) - κ₀ * T * (N : ℝ)
      = (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))))
        + κ₀ * ((∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have hgoal : (C₀ + 2 * |κ₀|) * E₂ * (N : ℝ) ^ α
      = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) + |κ₀| * ((N : ℝ) ^ α * E₂) := by ring
  rw [hgoal]
  exact add_le_add hA hB

/-! ### Sub-lemmas for `coprime_absNorm_of_unramified_of_finrank_eq_one` (the `d = 1` branch)

The `d = 1` ramification fact is discharged **K-internally** (no `K ≃ ℚ` transport) via the
different ideal: a rational prime `p ∣ m` (with `m % 4 ≠ 2`) extracted from a non-coprime norm
gives a primitive `p^v`-th root `ζ'` in `𝓞 L`; the Eisenstein identity
`(p) = (ζ' − 1)^{φ(p^v)}` (with `φ(p^v) ≥ 2`) forces `𝔓² ∣ (𝔭)·𝓞 L` for any `𝔓` over `𝔭`,
hence `𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L)`
(`pow_sub_one_dvd_differentIdeal`), contradicting unramifiedness. -/

open Polynomial Finset in
/-- **Cyclotomic Eisenstein identity (element level, base-free).** For a primitive `p^(k+1)`-th root
of unity `ζ'` in a domain `A`, the prime `p` is associated to `(ζ' − 1)^{φ(p^{k+1})}` where
`φ(p^{k+1}) = p^k (p − 1)`: evaluating `cyclotomic (p^(k+1)) = ∏_{μ primitive} (X − μ)` at `1` gives
`p = ∏ (1 − μ)`, and each factor `1 − μ` is associated to `ζ' − 1`
(`IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`). -/
private theorem associated_natCast_sub_one_pow {A : Type*} [CommRing A] [IsDomain A] {p k : ℕ}
    [hp : Fact p.Prime] {ζ' : A} (hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1))) :
    Associated (p : A) ((ζ' - 1) ^ (p ^ k * (p - 1))) := by
  have hcard : (primitiveRoots (p ^ (k + 1)) A).card = p ^ k * (p - 1) := by
    rw [hζ'.card_primitiveRoots, Nat.totient_prime_pow_succ hp.out]
  have heval : (p : A) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) A, (1 - μ) := by
    have h1 := eval_one_cyclotomic_prime_pow (R := A) k (p := p)
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ'] at h1
    simp only [eval_prod, eval_sub, eval_X, eval_C] at h1
    rw [← h1]
  rw [heval]
  have hpos : 0 < p ^ (k + 1) := pow_pos hp.out.pos _
  have hassoc : ∀ μ ∈ primitiveRoots (p ^ (k + 1)) A, Associated (1 - μ) (ζ' - 1) := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ (p ^ (k + 1)) := isPrimitiveRoot_of_mem_primitiveRoots hμ
    obtain ⟨j, _, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hμp.pow_eq_one
    have hjc : j.Coprime (p ^ (k + 1)) := (hζ'.pow_iff_coprime hpos j).mp hμp
    rw [show (1 : A) - ζ' ^ j = -(ζ' ^ j - 1) by ring]
    exact (hζ'.associated_sub_one_pow_sub_one_of_coprime hjc).neg_right.symm
  calc Associated (∏ μ ∈ primitiveRoots (p ^ (k + 1)) A, (1 - μ))
        (∏ _μ ∈ primitiveRoots (p ^ (k + 1)) A, (ζ' - 1)) := Associated.prod _ _ _ hassoc
    _ = (ζ' - 1) ^ (p ^ k * (p - 1)) := by rw [Finset.prod_const, hcard]

/-- **Totient lower bound** `2 ≤ p^k (p − 1)` away from the degenerate case `(p, k) = (2, 0)`. -/
private theorem two_le_pow_mul_pred {p k : ℕ} (hp : p.Prime) (hbad : ¬ (p = 2 ∧ k = 0)) :
    2 ≤ p ^ k * (p - 1) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h => hbad ⟨rfl, h⟩
    calc 2 = 2 ^ 1 * (2 - 1) := by norm_num
      _ ≤ 2 ^ k * (2 - 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
  · have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
    calc 2 ≤ 1 * (p - 1) := by lia
      _ ≤ p ^ k * (p - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)

/-- The degenerate cyclotomic case `2 ∥ m` (i.e. `m.factorization 2 = 1`) is exactly `m ≡ 2 mod 4`,
ruled out by `hm`. -/
private theorem factorization_two_ne_one_of_mod_four {m : ℕ} (hm0 : m ≠ 0) (hm : m % 4 ≠ 2) :
    m.factorization 2 ≠ 1 := by
  intro hf
  have h2dvd : 2 ∣ m := by
    have h : (2 : ℕ) ^ 1 ∣ m :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mpr (by lia)
    simpa using h
  have h4ndvd : ¬ 4 ∣ m := fun h4 =>
    absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mp
      (by rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at h4)) (by lia)
  exact hm (by omega)

/-- **At `[K : ℚ] = 1`, a rational prime in a prime `𝔭` spans `𝔭`.** Since `N((p)) = p^{[K:ℚ]} = p`
and `𝔭 ∣ (p)` with `N𝔭 > 1`, the cofactor has norm `1`, so `(p) = 𝔭`. -/
private theorem span_singleton_natCast_eq_of_finrank_eq_one
    (hd1 : Module.finrank ℚ K = 1) (p : ℕ) (hp : p.Prime) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hmem : (p : 𝓞 K) ∈ 𝔭) : Ideal.span {(p : 𝓞 K)} = 𝔭 := by
  have hrank : Module.finrank ℤ (𝓞 K) = 1 := by rw [NumberField.RingOfIntegers.rank, hd1]
  have hNspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p := by
    rw [Ideal.absNorm_span_singleton,
      show ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by push_cast; rfl,
      Algebra.norm_algebraMap, hrank, Int.natAbs_pow, Int.natAbs_natCast, pow_one]
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNmul : Ideal.absNorm 𝔭 * Ideal.absNorm C = p := by rw [← map_mul, ← hC, hNspan]
  have hN𝔭1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN𝔭eq : Ideal.absNorm 𝔭 = p :=
    (Nat.Prime.eq_one_or_self_of_dvd hp _ ⟨_, hNmul.symm⟩).resolve_left hN𝔭1
  have hNC1 : Ideal.absNorm C = 1 := by
    rw [hN𝔭eq] at hNmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rwa [mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.mp hNC1, Ideal.mul_top]

omit [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] in
/-- **Bad primes are empty when `[K : ℚ] = 1`** (i.e. `K = ℚ`, the `d = 1` case). If `K` has degree
`1` over `ℚ`, then no nonzero prime `𝔭` of `𝓞 K` that is unramified in `L = K(μ_m)` can have norm
sharing a factor with `m`: a prime `𝔭` with `¬(N𝔭).Coprime m` lies over a rational prime `p ∣ m`,
and `p ∣ m` (with `m % 4 ≠ 2`) **ramifies** in the cyclotomic field `L = K(μ_m)`, contradicting
unramifiedness.

The ramification is proved **K-internally** (no `K ≃ ℚ` transport): extract the rational prime
`p ∣ m` with `(p : 𝓞 K) ∈ 𝔭` (`exists_primeFactor_natCast_mem_of_not_coprime`); set
`v = m.factorization p = k + 1 ≥ 1`, with `(p, v) ≠ (2, 1)` from `hm`
(`factorization_two_ne_one_of_mod_four`). A primitive `p^v`-th root `ζ'` lives in `𝓞 L`, and the
element-level Eisenstein identity `(p) = (ζ' − 1)^{φ(p^v)}` (`associated_natCast_sub_one_pow`) with
`φ(p^v) = p^k (p − 1) ≥ 2` (`two_le_pow_mul_pred`) gives `𝔓^{φ(p^v)} ∣ (𝔭)·𝓞 L`
(using `(p) = 𝔭` at `d = 1`, `span_singleton_natCast_eq_of_finrank_eq_one`), so `𝔓² ∣ (𝔭)·𝓞 L` and
`𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L)` (`pow_sub_one_dvd_differentIdeal`) — contradicting `UnramifiedIn`
via `not_dvd_differentIdeal_iff`. -/
private theorem coprime_absNorm_of_unramified_of_finrank_eq_one
    (hd1 : Module.finrank ℚ K = 1) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hunr : UnramifiedIn K L 𝔭) (hm : m % 4 ≠ 2) : (Ideal.absNorm 𝔭).Coprime m := by
  classical
  by_contra hncop
  obtain ⟨p, hpm, hpmem𝔭⟩ := exists_primeFactor_natCast_mem_of_not_coprime K m 𝔭 h𝔭 hncop
  have hp : p.Prime := (Nat.mem_primeFactors.mp hpm).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hm0 : m ≠ 0 := (Nat.mem_primeFactors.mp hpm).2.2
  set v := m.factorization p with hv
  have hv1 : 1 ≤ v := by rw [hv]; exact hp.factorization_pos_of_dvd hm0 hpdvd
  obtain ⟨k, hk⟩ : ∃ k, v = k + 1 := ⟨v - 1, by lia⟩
  have hbad : ¬ (p = 2 ∧ k = 0) := by
    rintro ⟨rfl, rfl⟩
    exact factorization_two_ne_one_of_mod_four hm0 hm (by rw [← hv, hk])
  have hpvdvd : p ^ v ∣ m := by rw [hv]; exact Nat.ordProj_dvd m p
  obtain ⟨ζm, hζm⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  set q := m / p ^ v with hq
  have hqdvd : q ∣ m := Nat.div_dvd_of_dvd hpvdvd
  have hq0 : q ≠ 0 := Nat.div_ne_zero_iff.mpr
    ⟨pow_ne_zero _ hp.ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpvdvd⟩
  set ζ' : 𝓞 L := hζm.toInteger ^ q
  have hmq : m / q = p ^ (k + 1) := by rw [hq, Nat.div_div_self hpvdvd hm0, ← hk]
  have hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1)) := by
    have h := hζm.toInteger_isPrimitiveRoot.pow_of_dvd hq0 hqdvd
    rwa [hmq] at h
  have hassoc : Associated (p : 𝓞 L) ((ζ' - 1) ^ (p ^ k * (p - 1))) :=
    associated_natCast_sub_one_pow hζ'
  have hφ2 : 2 ≤ p ^ k * (p - 1) := two_le_pow_mul_pred hp hbad
  have hspan𝔭 : Ideal.span {(p : 𝓞 K)} = 𝔭 :=
    span_singleton_natCast_eq_of_finrank_eq_one K hd1 p hp 𝔭 hpmem𝔭
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
  obtain ⟨𝔓, h𝔓max, h𝔓lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 L) 𝔭
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  haveI := h𝔓lo
  have hnotdvd : ¬ 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
    exact hunr.2 𝔓 h𝔓max h𝔓lo
  apply hnotdvd
  have hdvd2 : 𝔓 ^ 2 ∣ 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) := by
    have hmapeq : 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) = Ideal.span {(p : 𝓞 L)} := by
      rw [← hspan𝔭, Ideal.map_span, Set.image_singleton, map_natCast]
    have hspanL : Ideal.span {(p : 𝓞 L)} = (Ideal.span {ζ' - 1}) ^ (p ^ k * (p - 1)) := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
    have hpmem𝔓 : (p : 𝓞 L) ∈ 𝔓 := by
      have h1 : algebraMap (𝓞 K) (𝓞 L) (p : 𝓞 K) ∈ 𝔓 := by
        rw [h𝔓lo.over] at hpmem𝔭; exact hpmem𝔭
      rwa [map_natCast] at h1
    have hsub𝔓 : ζ' - 1 ∈ 𝔓 := by
      have hpow : (ζ' - 1) ^ (p ^ k * (p - 1)) ∈ 𝔓 := by
        obtain ⟨u, hu⟩ := hassoc
        rw [← hu]; exact Ideal.mul_mem_right _ _ hpmem𝔓
      exact ‹𝔓.IsPrime›.mem_of_pow_mem _ hpow
    have hdvd1 : 𝔓 ∣ Ideal.span {ζ' - 1} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsub𝔓)
    rw [hmapeq, hspanL]
    exact dvd_trans (pow_dvd_pow 𝔓 hφ2) (pow_dvd_pow_of_dvd hdvd1 _)
  simpa using pow_sub_one_dvd_differentIdeal (𝓞 K) 𝔓 2 h𝔭 hdvd2

open UniqueFactorizationMonoid nonZeroDivisors in
/-- **The L2 fibre bound, `d = 1` branch.** When `[K : ℚ] = 1` the bad-prime set is empty, so the
bad-part set is the single ideal `⊤` (`badFinset N = {⊤}`) and the L2 count is one good-fibre count
`RC(autToPow g, N)`, bounded directly by the `g`-uniform estimate (`exists_kappa_uniform`) with
`κ = κ₀`, `C' = C₀`. -/
private theorem card_fibre_bound_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (hd1 : Module.finrank ℚ K = 1) (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ₀, C₀, hunif⟩ := exists_kappa_uniform K L m hζ
  refine ⟨κ₀, C₀, fun g N hN1 => ?_⟩
  have hbadtop : (finite_isBadPart K L m N).toFinset = {⊤} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun 𝔟 h𝔟 => ?_⟩
    · rw [Set.Finite.mem_toFinset]
      refine ⟨by rw [Ne, ← Ideal.one_eq_top]; exact one_ne_zero, fun 𝔭 h𝔭 => ?_, ?_⟩
      · rw [← Ideal.one_eq_top, normalizedFactors_one] at h𝔭
        exact absurd h𝔭 (Multiset.notMem_zero _)
      · rw [Ideal.absNorm_top]; exact hN1
    · rw [Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨h0, hfac, _⟩ := h𝔟
      by_contra htop
      have hfac0 : normalizedFactors 𝔟 ≠ 0 := by
        intro h
        have : 𝔟 = 1 := by
          have hp := Ideal.prod_normalizedFactors_eq_self h0
          rw [h, Multiset.prod_zero] at hp; exact hp.symm
        rw [Ideal.one_eq_top] at this; exact htop this
      obtain ⟨𝔭, h𝔭⟩ := Multiset.exists_mem_of_ne_zero hfac0
      have hprime := prime_of_normalized_factor 𝔭 h𝔭
      haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime hprime
      exact (hfac 𝔭 h𝔭).2 (coprime_absNorm_of_unramified_of_finrank_eq_one K L m hd1 𝔭
        hprime.ne_zero (hfac 𝔭 h𝔭).1 hm)
  rw [card_L2_eq_sum_residue K L m hζ g N, hbadtop, Finset.sum_singleton,
    frobeniusIdeal_one, inv_one, mul_one, Ideal.absNorm_top, Nat.div_one]
  exact hunif (hζ.autToPow K g) ⟨g, rfl⟩ N hN1

end L2Assembly

/-- **L2 — unramified-supported Frobenius-fibre equidistribution.** For
`L = K(μ_m)` cyclotomic, the number of nonzero ideals `𝔞` with `N𝔞 ≤ N`, **every prime factor of
`𝔞` unramified in `L`** (`U 𝔞`) and `Frob_𝔞 = g` is `κ·N + O(N^{1−1/d})` with the leading constant
`κ` **independent of `g`** (`d = finrank ℚ K`).

`U 𝔞` is the exact support condition (`galoisCharacterOnIdeal χ 𝔞 ≠ 0`). The geometry-of-numbers
argument splits an unramified-supported `𝔞` multiplicatively into its **"bad-prime" part** — the
product of factors that are unramified but have `N𝔭` *not* coprime to `m` (so `𝔭 ∣ m`; these are
the finitely many primes lying over the `p ∣ m` for which `K_𝔭` already contains `μ_{p^{v_p(m)}}`,
hence unramified despite ramifying naively over `ℚ`), whose ideal Frobenius is **not** the
norm-power — times a **"good" part** with `N𝔭` coprime to `m`, on which
`cyclotomic_frobenius_acts_as_norm_power` gives `Frob_𝔭 = (Frob_p)^{f_𝔭}` cut out by `N𝔭 mod m`.

The bad-prime part ranges over a **fixed finite set** of ideals (products of the finitely many
bad primes, `finite_badPrimes`); the partition `card_L2_eq_sum_residue` rewrites the L2 count as a
sum over the finite bad-part set `badFinset N` of **good-fibre norm-residue counts** at the residue
`autToPow (g · Frob𝔟⁻¹) ∈ range autToPow`, each over the window `⌊N/N𝔟⌋`. The κ-uniform
per-residue count `exists_kappa_uniform` (one `(κ₀, C₀)` for every residue in `range autToPow`, the
`g`-independence input) comes from the ICC count `exists_card_norm_le_norm_residue_..._uniform` fed
its Fourier-decay hypothesis by the ICC producer + the realizer hypothesis `realizes_autToPow_range`
(every cyclotomic-character value is an ideal-norm residue, via the coprime-restricted
Frobenii-generation `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`). A triangle inequality
sums the per-bad-part errors and the bad-part Euler tail (`sum_rpow_le_euler_prod`, convergent for
`d ≥ 2`) into the effective `O(N^{1−1/d})` rate with `κ = κ₀·∑_{𝔟 bad}(N𝔟)⁻¹` `g`-independent; the
`d = 1` (`K = ℚ`) case has an empty bad set, so the count is one good-fibre residue count.

The `d = 1` "bad primes are empty" fact `coprime_absNorm_of_unramified_of_finrank_eq_one` is
discharged K-internally via the cyclotomic Eisenstein identity (no `K ≃ ℚ` transport); the whole
assembly is `sorry`-free. -/
theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  rcases Nat.lt_or_ge (Module.finrank ℚ K) 2 with hlt | hge
  · have hd1 : Module.finrank ℚ K = 1 := le_antisymm (by lia) Module.finrank_pos
    exact card_fibre_bound_eq_one K L m hζ hd1 hm
  · exact card_fibre_bound_two_le K L m hζ hge

/-- The unramified-supported Frobenius-value-fibre `{U 𝔞 ∧ χ(Frob_𝔞) = ζ}` partitions over the
character fibre `S_ζ = {g : χ g = ζ}` into the per-`g` unramified-supported Frobenius fibres
`{U 𝔞 ∧ Frob_𝔞 = g}` (drop the value `g = Frob_𝔞`). -/
private theorem card_unramifiedSupported_frobeniusValueFibre_eq_sum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ}
        = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              frobeniusIdeal K L 𝔞 = g.1} := by
  classical
  haveI hfinN : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  haveI hfin : ∀ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      Finite {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} := fun g =>
    Finite.of_injective
      (fun a => (⟨a.1, a.2.2.1⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
      (fun _ _ hab => by ext1; simpa using hab)
  rw [← Nat.card_sigma]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun a => (⟨a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, by rw [a.2.2.2.2.2]; exact a.1.2⟩ :
      {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ})) ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨g₁, hg₁⟩, ⟨𝔞, ha1, ha2, haU, ha3⟩⟩ ⟨⟨g₂, hg₂⟩, ⟨𝔟, hb1, hb2, hbU, hb3⟩⟩ hab
    have h𝔞𝔟 : 𝔞 = 𝔟 := congrArg Subtype.val hab
    subst h𝔞𝔟
    have hg : g₁ = g₂ := ha3.symm.trans hb3
    subst hg
    rfl
  · rintro ⟨𝔞, h1, h2, hU, h3⟩
    exact ⟨⟨⟨frobeniusIdeal K L 𝔞, h3⟩, ⟨𝔞, h1, h2, hU, rfl⟩⟩, rfl⟩

/-- **Geometry of numbers (Sharifi 7.1.19, p. 142).** For a nontrivial
character `χ` of order `n = orderOf χ`, the number of nonzero ideals `𝔞 ⊆ 𝓞 K` with `N𝔞 ≤ N`
and `χ(𝔞) = ζ` is `C·N + O(N^{1-1/d})` (`d = [K:ℚ]`), with the **leading constant `C` independent
of `ζ`**. Verbatim (p. 142):
> "The geometry of numbers can be used to show that the number of ideals `𝔞` of `𝒪_K` with
> `N𝔞 ≤ N` for `N ≥ 1` and `χ(𝔞) = ζ` is `CN + O(N^{1−d⁻¹})`, where `C` is a constant
> independent of `ζ`."

**Restated at cyclotomic generality** (expert review 2026-06-05): the general-abelian value-fibre
count needs class field theory, but for `L = K(μ_m)` it is CFT-free. The reduction is now an
**exact set equality** (not a thin-error bridge): for `ζ ≠ 0` the value-fibre `{χ(𝔞) = ζ}` equals
the **unramified-supported** Frobenius-value-fibre `{U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, where
`U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭`
(`card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`, Helper 1a) — `U` is the exact
support condition `χ(𝔞) ≠ 0`, since `χ(𝔞) = 0` whenever a factor is ramified while the junk-class
`Frob_𝔞` ignores ramified factors. Partitioning that fibre over `S_ζ = {g : χ g = ζ}`
(`|S_ζ| = |ker χ|`, `card_charFibre_eq_card_ker`) and applying the **unramified-supported**
Frobenius-fibre equidistribution (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`, L2) per `g`,
with leading density `κ` independent of `g`, gives `C = |ker χ|·κ` and `C' = |ker χ|·C₂`, both
independent of `ζ`. The
class-independent leading term is mathlib's `tendsto_norm_le_and_mk_eq_div_atTop`; the new content —
the project's deepest analytic input — is the effective `O(N^{1-1/d})` boundary rate, supplied
by `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the effective
Lipschitz-boundary lattice-point count in `ForMathlib/LatticePointCount.lean`, a standalone
mathlib-PR) fed by the Lipschitz-frontier input `normLeOne_frontier_lipschitz_cover`. -/
theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C C' : ℝ, ∀ ζ : ℂ, ζ ^ orderOf χ = 1 → ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ)
          - C * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ, C₂, hL2⟩ := exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le K L m hm
  set κ₀ : ℕ := Nat.card (MonoidHom.ker χ) with hκ₀
  refine ⟨(κ₀ : ℝ) * κ, (κ₀ : ℝ) * C₂, fun ζ hζ N hN => ?_⟩
  set P : ℝ := (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) with hP
  have hord : 0 < orderOf χ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)
  have hζ0 : ζ ≠ 0 := by
    intro h; subst h
    rw [zero_pow hord.ne'] at hζ
    exact zero_ne_one hζ
  set ζu : ℂˣ := Units.mk0 ζ hζ0
  have hζuval : (ζu : ℂ) = ζ := rfl
  have hζun : ζu ^ orderOf χ = 1 := by
    apply Units.ext; push_cast; rw [hζuval]; exact hζ
  set B : ℝ := (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
        (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
          (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} : ℝ) with hB
  have hAB : (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ) = B := by
    rw [hB]
    exact congrArg _
      (card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre K L m χ ζ hζ0 N)
  rw [hAB]
  have hpart : B = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      (Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} : ℝ) := by
    rw [hB, card_unramifiedSupported_frobeniusValueFibre_eq_sum K L m χ ζ N, Nat.cast_sum]
  have hSκ₀ : Nat.card {g : Gal(L/K) // (χ g : ℂ) = ζ} = κ₀ := by
    rw [hκ₀]
    have heq : {g : Gal(L/K) // (χ g : ℂ) = ζ} = {g : Gal(L/K) // χ g = ζu} := by
      congr 1; ext g
      rw [← hζuval]
      exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
    rw [heq]
    letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
    exact card_charFibre_eq_card_ker χ ζu hζun
  have hcardℝ : (Fintype.card {g : Gal(L/K) // (χ g : ℂ) = ζ} : ℝ) = (κ₀ : ℝ) := by
    rw [← Nat.card_eq_fintype_card, hSκ₀]
  rw [hpart]
  calc
    |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ)
          - (κ₀ : ℝ) * κ * N|
        = |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
            ((Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
                (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                  frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N)| := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]
          ring_nf
    _ ≤ ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, C₂ * P :=
          Finset.sum_le_sum fun g _ => hL2 g.1 N hN
    _ = (κ₀ : ℝ) * C₂ * P := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]; ring

private theorem sum_nthRootsFinset_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v = 0 := by
  classical
  have hn0 : n ≠ 0 := by lia
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0
  have hmem : ∀ {z : R}, z ∈ Polynomial.nthRootsFinset n (1 : R) ↔ z ^ n = 1 := fun {z} ↦
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0) 1
  have himg : (Polynomial.nthRootsFinset n (1 : R)).image (ζ * ·) =
      Polynomial.nthRootsFinset n 1 := by
    refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_)
      (Finset.card_image_of_injective _ (mul_right_injective₀ hζ0)).ge
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hmem.mpr (by rw [mul_pow, hζ.pow_eq_one, one_mul, hmem.mp hv])
  have hshift : ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v =
      ζ * ∑ v ∈ Polynomial.nthRootsFinset n 1, v := by
    nth_rewrite 1 [← himg]
    rw [Finset.sum_image fun a _ b _ h ↦ mul_right_injective₀ hζ0 h, Finset.mul_sum]
  rcases mul_eq_zero.mp (by rw [sub_mul, one_mul, ← hshift, sub_self] :
      (ζ - 1) * ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v = 0) with h | h
  · exact absurd (sub_eq_zero.mp h) (hζ.ne_one hn)
  · exact h

private theorem galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterOnIdeal K L χ 𝔞 ∈
      insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1) := by
  classical
  by_cases hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭
  · refine Finset.mem_insert_of_mem
      (Polynomial.mem_nthRootsFinset (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)) 1 |>.mpr ?_)
    rw [galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU,
      ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
      MonoidHom.one_apply, Units.val_one]
  · push Not at hU
    obtain ⟨𝔭, h𝔭, hram⟩ := hU
    rw [galoisCharacterOnIdeal_eq_map_prod,
      Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hram⟩)]
    exact Finset.mem_insert_self _ _

private theorem sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (hord2 : 1 < orderOf χ) (C₀ : ℝ)
    (N : ℕ) [Fintype {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}] :
    ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1
      = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1,
          (((Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
              - C₀ * N : ℝ) : ℂ) * v := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ (by lia)⟩
  have h0R : (0 : ℂ) ∉ Polynomial.nthRootsFinset (orderOf χ) 1 := fun h ↦ by
    rw [Polynomial.mem_nthRootsFinset (by lia) 1, zero_pow (by lia)] at h
    exact zero_ne_one h
  calc ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1
      = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
          ∑ 𝔞 ∈ (Finset.univ : Finset {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N})
            with galoisCharacterOnIdeal K L χ 𝔞.1 = v, v :=
        (Finset.sum_fiberwise_of_maps_to'
          (fun 𝔞 _ ↦ galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset K L m χ 𝔞.1)
          fun z : ℂ ↦ z).symm
    _ = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine congrArg (· * v) (congrArg (Nat.cast : ℕ → ℂ) ?_)
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
          (fun 𝔞 : Ideal (𝓞 K) ↦ 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N)
          (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞 = v)).trans
          (Equiv.subtypeEquivRight fun 𝔞 ↦ and_assoc))
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
        rw [Finset.sum_insert h0R, mul_zero, zero_add]
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, ((((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v + ((C₀ * N : ℝ) : ℂ) * v) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        push_cast
        ring
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_nthRootsFinset_eq_zero hζ₀ hord2, mul_zero, add_zero]

/-- The nonzero ideals of `𝓞 K` of bounded norm form a finite type: they embed into the (finitely
many) ideals of norm `≤ N`. -/
private theorem finite_nonzeroIdeal_absNorm_le (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N} :=
  haveI : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  Finite.of_injective (fun a ↦ (⟨a.1, a.2.2⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
    fun _ _ hab ↦ Subtype.ext (by simpa using hab)

/-- Sharifi 7.1.19 step 1 (p. 142): geometry-of-numbers bound. The
partial-sum character sum `Σ_{N𝔞≤N} χ(𝔞)` (with `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞` the
completely-multiplicative ideal character) is `O(N^{1-1/[K:ℚ]})` for a
nontrivial character `χ`. This is the convergence input that extends
`L(χ,·)` to `Z(1 - [K:ℚ]^{-1})`. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨C₀, C', hcount⟩ := exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow K L m hm χ _hχ
  refine ⟨(orderOf χ : ℝ) * C', fun N ↦ ?_⟩
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (by simpa using hcount 1 (one_pow _) 1 le_rfl)
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · haveI : IsEmpty {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ 0} :=
      ⟨fun 𝔞 ↦ 𝔞.2.1 (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp 𝔞.2.2))⟩
    rw [tsum_empty, norm_zero]
    positivity
  have hord0 : orderOf χ ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'
  have hord2 : 1 < orderOf χ :=
    lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hord0) fun h ↦ _hχ (orderOf_eq_one_iff.mp h.symm)
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ hord0⟩
  set R : Finset ℂ := Polynomial.nthRootsFinset (orderOf χ) (1 : ℂ) with hR
  have hmemR : ∀ {z : ℂ}, z ∈ R ↔ z ^ orderOf χ = 1 := fun {z} ↦
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hord0) 1
  haveI := finite_nonzeroIdeal_absNorm_le K N
  haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}
  rw [tsum_fintype, sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul K L m χ hord2 C₀ N]
  calc ‖∑ v ∈ R, (((Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
          - C₀ * N : ℝ) : ℂ) * v‖
      ≤ ∑ v ∈ R, ‖(((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ R, C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        rw [norm_mul, Complex.norm_eq_one_of_pow_eq_one (hmemR.mp hv) hord0, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        exact hcount v (hmemR.mp hv) N hN1
    _ = (orderOf χ : ℝ) * C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        rw [Finset.sum_const, hR, hζ₀.card_nthRootsFinset, nsmul_eq_mul]
        ring

/-- The `n`-th Dirichlet coefficient of the Artin L-series `L(χ,·)`, i.e. the sum of the ideal
character `χ̃(𝔞)` over the (finitely many) nonzero ideals `𝔞` of `𝓞 K` with `N𝔞 = n`. This is the
arithmetic function whose L-series is `∑_𝔞 χ̃(𝔞) N𝔞^{-s}`. -/
private noncomputable def galoisCharacterCoeff
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) : ℂ :=
  ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, galoisCharacterOnIdeal K L χ 𝔞.1.1

/-- Each norm-fibre `{𝔞 : 𝓞 K // 𝔞 ≠ ⊥ ∧ N𝔞 = n}` is finite (there are finitely many ideals of
bounded norm), so the defining `tsum` of `galoisCharacterCoeff` is over a finite type. -/
private theorem finite_nonzeroIdeal_absNorm_eq
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

/-- The `0`-th coefficient vanishes: no nonzero ideal has norm `0`, so the fibre is empty. -/
@[simp] private theorem galoisCharacterCoeff_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) : galoisCharacterCoeff K L χ 0 = 0 := by
  have : IsEmpty {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = 0} :=
    ⟨fun 𝔞 ↦ 𝔞.1.2 (Ideal.absNorm_eq_zero_iff.mp 𝔞.2)⟩
  rw [galoisCharacterCoeff, tsum_empty]

/-- The `n`-th coefficient is bounded in norm by the ideal-norm multiplicity: each ideal character
value has norm `≤ 1`, so the fibre sum has norm `≤` the number of fibre elements. -/
private theorem norm_galoisCharacterCoeff_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) :
    ‖galoisCharacterCoeff K L χ n‖ ≤ (idealNormMultiplicity K n : ℝ) := by
  haveI := finite_nonzeroIdeal_absNorm_eq K n
  haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}
  calc ‖galoisCharacterCoeff K L χ n‖
      ≤ ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
          ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ :=
        norm_tsum_le_tsum_norm Summable.of_finite
    _ = ∑ 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
          ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ := tsum_fintype _
    _ ≤ ∑ _𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, (1 : ℝ) :=
        Finset.sum_le_sum fun 𝔞 _ ↦ norm_galoisCharacterOnIdeal_le_one K L χ 𝔞.1.1
    _ = (idealNormMultiplicity K n : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, idealNormMultiplicity,
          Nat.card_eq_fintype_card]
        simp [Finset.card_univ]

/-- The partial sum of the coefficients `∑_{k ≤ n} galoisCharacterCoeff k` equals the character sum
`∑'_{N𝔞 ≤ n} χ̃(𝔞)` over nonzero ideals of bounded norm. Both sides are finite sums; the identity is
the fibrewise regrouping of the bounded-norm ideal sum by the value of `N𝔞 ∈ [1, n]`, matched
against the per-`n` fibre `tsum` defining each coefficient. -/
private theorem sum_galoisCharacterCoeff_eq_tsum_absNorm_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k =
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n},
        galoisCharacterOnIdeal K L χ 𝔞.1 := by
  classical
  haveI := finite_nonzeroIdeal_absNorm_le K n
  haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n}
  rw [tsum_fintype, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 1 n)
      (g := fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} ↦ Ideal.absNorm 𝔞.1)
      (fun 𝔞 _ ↦ Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp 𝔞.2.1), 𝔞.2.2⟩)
      (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞.1)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [galoisCharacterCoeff, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  haveI := finite_nonzeroIdeal_absNorm_eq K k
  haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = k}
  rw [tsum_fintype]
  exact Fintype.sum_equiv
    { toFun := fun ⟨⟨𝔞, h𝔞ne⟩, hnorm⟩ ↦
        (⟨⟨𝔞, h𝔞ne, hnorm.le.trans (Finset.mem_Icc.mp hk).2⟩, hnorm⟩ :
          {x : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} // Ideal.absNorm x.1 = k})
      invFun := fun ⟨⟨𝔞, h𝔞⟩, hnorm⟩ ↦ ⟨⟨𝔞, h𝔞.1⟩, hnorm⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl } _ _ fun _ ↦ rfl

/-- **Step 1 (the LF3 input).** The partial sums of the L-series coefficients grow like
`O(n^{1-1/d})`, `d = [K:ℚ]`. This is the geometry-of-numbers character-sum bound
`character_sum_geometry_of_numbers_bound` rewritten through the partial-sum bridge. -/
private theorem sum_galoisCharacterCoeff_isBigO
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k)
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) := by
  obtain ⟨C, hC⟩ := character_sum_geometry_of_numbers_bound K L m hm χ _hχ
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall fun n ↦ ?_⟩
  rw [sum_galoisCharacterCoeff_eq_tsum_absNorm_le K L χ n,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hC n

/-- **Step 2.** The partial sums of the coefficient *norms* grow like `O(n)`, the crude bound used
for absolute (`LSeriesSummable`) convergence on `Re s > 1`. Pointwise `‖coeff k‖ ≤
idealNormMultiplicity K k`, and the latter's partial sums are `O(n)` by
`sum_idealNormMultiplicity_isBigO`. -/
private theorem sum_norm_galoisCharacterCoeff_isBigO
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖galoisCharacterCoeff K L χ k‖)
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  refine (Asymptotics.isBigO_of_le Filter.atTop fun n ↦ ?_).trans
    (sum_idealNormMultiplicity_isBigO K)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦ norm_galoisCharacterCoeff_le K L χ k

/-- **Step 3.** On `Re s > 1` the L-series of the coefficient function equals the absolutely
convergent ideal sum `∑'_𝔞 χ̃(𝔞) N𝔞^{-s}`. The regrouping skeleton mirrors
`hasSum_nonzeroIdeal_absNorm_cpow`: `Equiv.sigmaFiberEquiv` partitions the ideal sum by the value
`N𝔞`, the per-fibre sum collapses to `galoisCharacterCoeff n · n^{-s}`, and `LSeries.term_def₀`
(coefficient at `0` vanishes) identifies the L-series. Absolute summability is by termwise
comparison `‖χ̃(𝔞) N𝔞^{-s}‖ ≤ N𝔞^{-s}` against `ζ_K`. -/
private theorem lseries_galoisCharacterCoeff_eq_tsum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) (hs : 1 < s.re) :
    LSeries (galoisCharacterCoeff K L χ) s =
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) with he
  have hsummable : Summable fun I : NonzeroIdeal K ↦
      ‖galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun I ↦ ?_)
      (hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_galoisCharacterOnIdeal_le_one K L χ I.1)
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
      galoisCharacterOnIdeal K L χ (e p).1 * (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal K ↦
      galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr hsummable.of_norm
  have hfiber_val : ∀ n : ℕ,
      (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s))
        = galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) := fun n ↦ by
    have hconst : ∀ y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s) =
          galoisCharacterOnIdeal K L χ (y.1).1 * (n : ℂ) ^ (-s) := fun y ↦ by rw [y.2]
    rw [tsum_congr hconst, tsum_mul_right, galoisCharacterCoeff]
  rw [show LSeries (galoisCharacterCoeff K L χ) s =
      ∑' n, galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) from
    tsum_congr fun n ↦ LSeries.term_def₀ (galoisCharacterCoeff_zero K L χ) s n,
    ← e.tsum_eq (fun I : NonzeroIdeal K ↦
      galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)),
    hsummable_sigma.tsum_sigma]
  exact (tsum_congr hfiber_val).symm

open MeasureTheory Set in
private theorem setIntegral_Ioi_one_mul_cpow_eq_mellin (S : ℝ → ℂ) (hS : ∀ t < 1, S t = 0) (s : ℂ) :
    ∫ t in Ioi (1 : ℝ), S t * (t : ℂ) ^ (-(s + 1)) = mellin S (-s) := by
  rw [mellin, show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • S t) =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) • S t from ?_]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [smul_eq_mul]
    ring_nf
  · have hinter : Ioi (0 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) :=
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num))
    rw [← hinter, ← setIntegral_indicator measurableSet_Ioi]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 1 from
      ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 1} = 0)] with t ht _
    rw [indicator_apply]
    by_cases h1 : t ∈ Ioi (1 : ℝ)
    · rw [if_pos h1]
    · rw [if_neg h1, hS t (lt_of_le_of_ne (not_lt.mp (by simpa using h1)) ht), smul_zero]

open Filter Topology Set MeasureTheory Asymptotics in
/-- Sharifi 7.1.19 step 1b (p. 142) — analytic extension of `L(χ,·)`.
Combining the geometry-of-numbers bound
`character_sum_geometry_of_numbers_bound`
with Sharifi Lemma 7.1.5 (p. 138, a generic Dirichlet-series
convergence criterion given a polynomial bound on partial sums), the
Dirichlet series `L(χ,s) = Σ_𝔞 χ(𝔞) N𝔞^{-s}` converges absolutely and
uniformly on every compact subset of `Z(1 - 1/[K:ℚ])`, defining an
analytic extension of `L(χ,·)` from `Re s > 1` to that half-plane.

Source quote (verbatim, p. 142):
> "By Lemma 7.1.5, we therefore have that `Σ_𝔞⊂𝓞_K χ(𝔞) N𝔞^{-s}`
> converges absolutely and uniformly on every compact subset of
> `Z(1 - d^{-1})`."

Mathlib analogue of Sharifi Lemma 7.1.5:
`LSeries.summable_of_partial_sums_le_const_mul_rpow` (or the
`LSeries.tendsto_neg_logDerivLSeries_eq_*` machinery in
`Mathlib.NumberTheory.LSeries.*`).

**Stated at cyclotomic generality** (`L = K(μ_m)`), like the geometry-of-numbers input it rests
on (`character_sum_geometry_of_numbers_bound`, leaf G — see the restatement note there, expert
review 2026-06-05): the general-abelian partial-sum bound needs class field theory, while for
`L = K(μ_m)` it is CFT-free. Every consumer (the non-vanishing chain, the cyclotomic Chebotarev
case) instantiates at a cyclotomic extension. -/
theorem artinLSeries_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        Lf s =
          ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 *
              (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) := by
  classical
  set r : ℝ := 1 - (Module.finrank ℚ K : ℝ)⁻¹ with hr_def
  have hrinv : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [inv_pos]; exact_mod_cast Module.finrank_pos
  have hr0 : 0 ≤ r := by
    rw [hr_def, sub_nonneg, inv_le_one_iff₀]; right; exact_mod_cast Module.finrank_pos
  have hr1 : r < 1 := by rw [hr_def]; linarith
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k with hS_def
  have hS_zero : ∀ t : ℝ, t < 1 → S t = 0 := fun t ht ↦ by
    change ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k = 0
    rw [Nat.floor_eq_zero.mpr ht, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
  have hS_bigO : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ r) :=
    ((sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ).comp_tendsto
      tendsto_nat_floor_atTop).trans <|
      isEquivalent_nat_floor.isBigO.rpow hr0 (Filter.eventually_ge_atTop 0)
  refine ⟨fun s ↦ s * mellin S (-s), ?_, fun s hs ↦ ?_⟩
  · refine DifferentiableOn.analyticOn (fun s₀ hs₀ ↦ ?_)
      (isOpen_lt continuous_const Complex.continuous_re)
    have hs₀' : r < s₀.re := hs₀
    have hfc : LocallyIntegrableOn S (Ioi (0 : ℝ)) := by
      simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (a := 0) (m := 1)
        (galoisCharacterCoeff K L χ) le_rfl (locallyIntegrableOn_const 1)).mono_set
          Set.Ioi_subset_Ici_self
    have hf_top : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ (-(-r))) := by rw [neg_neg]; exact hS_bigO
    have hf_bot : S =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (-(-s₀.re - 1))) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using
          hS_zero t (Set.mem_Ioo.mp ht).2) (Asymptotics.isBigO_zero _ _)
    have hmellin : DifferentiableAt ℂ (mellin S) (-s₀) :=
      mellin_differentiableAt_of_isBigO_rpow hfc hf_top (by rw [Complex.neg_re]; linarith)
        hf_bot (by rw [Complex.neg_re]; linarith)
    exact (differentiableAt_id.mul (hmellin.comp s₀ differentiableAt_id.neg)).differentiableWithinAt
  · have hssum : LSeriesSummable (galoisCharacterCoeff K L χ) s :=
      LSeriesSummable_of_sum_norm_bigO (sum_norm_galoisCharacterCoeff_isBigO K L χ) zero_le_one
        (by exact_mod_cast hs)
    rw [← lseries_galoisCharacterCoeff_eq_tsum K L χ s hs,
      LSeries_eq_mul_integral (galoisCharacterCoeff K L χ) hr0
        (lt_of_lt_of_le hr1 (by exact_mod_cast hs.le)) hssum
        (sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ),
      setIntegral_Ioi_one_mul_cpow_eq_mellin S hS_zero s]

/-! ### Sub-lemmas for `artinLSeries_one_ne_zero` (Sharifi 7.1.19 step 2, p. 142)

The non-vanishing of `L(χ, 1)` for nontrivial `χ` is Dirichlet's argument, run globally over all
characters. The contradiction is purely real-variable: on real `s ↓ 1`,

* **(B)** `log ζ_L(s) ≥ log(1/(s-1)) - C` diverges to `+∞` (the simple pole of `ζ_L`); this is
  `Density.logDedekindZeta_sub_log_inv_sub_one_bounded` applied to the field `L`.
* **(A)** the factorisation `ζ_L(s) = ∏_χ L_χ(s)` (Sharifi 7.1.16) makes
  `log ζ_L(s) = Σ_χ log‖L_χ(s)‖` (the product is over the *finite* character group and
  `ζ_L(s)` is a positive real for real `s`).
* **(C)** if one nontrivial factor `Lf` has `Lf 1 = 0`, then `log‖Lf(s)‖ ≤ -log(1/(s-1)) + C`
  (an analytic zero of order `≥ 1`), while every other factor is bounded above. Summing, the pole
  of `L_1 = ζ_K` is cancelled by the zero and `log ζ_L(s)` stays bounded — contradicting (B).
-/

open Filter Topology Set in
/-- **Ingredient B.** `log (ζ_L(s)).re → +∞` as the real argument `s ↓ 1`, driven by the simple
pole of the Dedekind zeta of `L` at `s = 1`. This is `logDedekindZeta_sub_log_inv_sub_one_bounded`
(Sharifi 7.1.12, in `Density.lean`) applied to the number field `L`, squeezed against
`log(1/(s-1)) → +∞`. -/
private theorem logDedekindZeta_re_tendsto_atTop
    (L : Type*) [Field L] [NumberField L] :
    Tendsto (fun s : ℝ ↦ Real.log (NumberField.dedekindZeta L (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) atTop := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded L
  have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)) + -C) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_log_one_div_sub_one_atTop.atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hC] with s hs
  linarith [(abs_le.mp hs).1]

open Filter Topology Set in
/-- **Ingredient C.** If `f` is analytic at `1`, has a zero there (`f 1 = 0`), and is not locally
identically zero, then near `s ↓ 1` (real) the log-norm `log‖f s‖` is bounded **above** by
`-log(1/(s-1)) + C`. Proof: `exists_eventuallyEq_pow_smul_nonzero_iff` factors `f z = (z-1)^n g z`
with `g 1 ≠ 0` and (since `f 1 = 0`) `n ≥ 1`; then `log‖f s‖ = n·log(s-1) + log‖g s‖`, and on a
right neighbourhood of `1` we have `s - 1 ∈ (0,1)` (so `log(s-1) < 0`, hence `n·log(s-1) ≤
log(s-1) = -log(1/(s-1))`) and `‖g s‖` is bounded by continuity. -/
private theorem analytic_log_norm_le_of_apply_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 1) (hf0 : f 1 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), f z = 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖f (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + C := by
  obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hf).mpr hne
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · refine absurd ?_ hg_ne
      have := hg_eq.self_of_nhds
      rw [pow_zero, one_smul] at this
      rw [← this, hf0]
    · exact h
  have hg_cont : ContinuousAt g 1 := hg_an.continuousAt
  have hCg : ∀ᶠ z in 𝓝 (1 : ℂ), ‖g z‖ ≤ ‖g 1‖ + 1 := by
    filter_upwards [hg_cont.norm.eventually (Metric.ball_mem_nhds ‖g 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  have hg0 : ∀ᶠ z in 𝓝 (1 : ℂ), g z ≠ 0 := hg_cont.eventually_ne hg_ne
  refine ⟨‖g 1‖ + 1, ?_⟩
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmap.eventually hg_eq, hmap.eventually hCg, hmap.eventually hg0, hIoo]
    with s hfeq hgle hgne hsmem
  obtain ⟨hs1, hs2⟩ := hsmem
  have hpos : (0 : ℝ) < s - 1 := by linarith
  have hlt1 : s - 1 < 1 := by linarith
  have hgpos : (0 : ℝ) < ‖g (s : ℂ)‖ := norm_pos_iff.mpr hgne
  have hnorm : ‖f (s : ℂ)‖ = (s - 1) ^ n * ‖g (s : ℂ)‖ := by
    rw [hfeq, norm_smul, norm_pow]
    congr 2
    rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
  rw [hnorm, Real.log_mul (by positivity) hgpos.ne', Real.log_pow]
  have hlog_neg : Real.log (s - 1) < 0 := Real.log_neg hpos hlt1
  have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn_step : (n : ℝ) * Real.log (s - 1) ≤ Real.log (s - 1) := by
    nlinarith [hn_ge, hlog_neg]
  have hloginv : -Real.log (1 / (s - 1)) = Real.log (s - 1) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hloginv]
  have hgle' : Real.log ‖g (s : ℂ)‖ ≤ ‖g 1‖ + 1 := by
    calc Real.log ‖g (s : ℂ)‖ ≤ Real.log (‖g 1‖ + 1) :=
          Real.log_le_log hgpos hgle
      _ ≤ ‖g 1‖ + 1 := Real.log_le_self (by positivity)
  linarith

/-- The character group `galoisCharacter K L = Gal(L/K) →* ℂˣ` is finite (`Gal(L/K)` is a finite
group). A local `Fintype` instance so the finite products/sums `∏ χ` / `∑ χ` over the character
group parse in the statements below. -/
local instance galoisCharacter.instFintype
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : Fintype (galoisCharacter K L) :=
  Fintype.ofFinite _

/-- The Dirichlet series `L_χ(s) = ∑'_{𝔞 ≠ ⊥} χ(𝔞) N𝔞^{-s}` of a Galois character, as a function
of `s`. This is the analytic engine of Sharifi 7.1.16–7.1.19; for `1 < Re s` it equals the Euler
product over unramified primes (`exists_artinLSeries_eulerProduct_abelian`). -/
noncomputable def artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
    galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)

/-- Pure-`ℂ` Euler-factor estimate: if `‖y‖ ≤ 1/2` then `‖(1 - y)^{-1} - 1‖ ≤ 2‖y‖`.
The shift is `(1 - y)^{-1} - 1 = y · (1 - y)^{-1}`, and `‖(1 - y)^{-1}‖ ≤ 2` because
`‖1 - y‖ ≥ 1 - ‖y‖ ≥ 1/2`. This is the per-factor bound feeding
`multipliable_one_add_of_summable` for both the Dedekind prime product and the χ-twisted local
Euler product. -/
private theorem norm_one_sub_inv_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have hyne1 : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hy)
  have heq : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by field_simp; ring
  rw [heq, norm_mul]
  have hnorm_lb : (2 : ℝ)⁻¹ ≤ ‖(1 : ℂ) - y‖ :=
    calc (2 : ℝ)⁻¹ = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - ‖y‖ := by linarith
      _ ≤ ‖(1 : ℂ)‖ - ‖y‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - y‖ := norm_sub_norm_le 1 y
  have hinv : ‖(1 - y)⁻¹‖ ≤ 2 := by
    rw [norm_inv, show (2 : ℝ) = (2⁻¹ : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hnorm_lb
  rw [mul_comm 2 ‖y‖]
  gcongr

/-- A nonzero prime ideal `𝔭` of a number ring has `2 ≤ N𝔭`: its norm is neither `0` (only `⊥` has
norm `0`) nor `1` (only `⊤` has norm `1`). -/
private theorem two_le_absNorm {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {𝔭 : Ideal R} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥) :
    2 ≤ Ideal.absNorm 𝔭 := by
  have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  lia

/-- For a nonzero prime `𝔭` of a number ring and `Re s > 1`, `‖N𝔭^{-s}‖ ≤ 1/2` (since `N𝔭 ≥ 2`,
`Re s > 1`). The bound that lets the Euler factors enter `norm_one_sub_inv_sub_one_le`. -/
private theorem norm_absNorm_cpow_neg_le_half {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal R // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have h2le : 2 ≤ Ideal.absNorm 𝔭.1 := two_le_absNorm 𝔭.2.1 𝔭.2.2
  have hpos : 0 < Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  have hb2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast h2le
  have hb1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := one_le_two.trans hb2
  calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
      ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    _ = ((Ideal.absNorm 𝔭.1 : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := by rw [inv_le_inv₀ (by linarith) (by norm_num)]; exact hb2
    _ = 1 / 2 := by norm_num

/-- The Euler factor `(1 - N𝔓^{-s})^{-1}` of a nonzero prime `𝔓` of `𝓞 L`, written additively as
`1 + g 𝔓` with `g 𝔓 = (1 - N𝔓^{-s})^{-1} - 1`. Its norm is `≤ 2‖N𝔓^{-s}‖`
(`norm_one_sub_inv_sub_one_le`), and `∑_𝔓 ‖N𝔓^{-s}‖` converges (a sub-sum of the absolutely
convergent `ζ_L`). -/
private theorem summable_norm_primeIdeal_factor_sub_one
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm
  have hsumP : Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (⟨𝔓.1, 𝔓.2.2⟩ : NonzeroIdeal L))
      (fun a b h ↦ Subtype.ext (by simpa using h))
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔓 ↦ ?_) (hsumP.mul_left 2)
  exact norm_one_sub_inv_sub_one_le (norm_absNorm_cpow_neg_le_half (R := 𝓞 L) hs 𝔓)

/-- The prime-ideal Euler product of `ζ_L` is `Multipliable`, with `HasProd` value `ζ_L(s)`.
`Multipliable` (hence the partition / fiberwise-regrouping lemmas) follows from absolute
convergence (`summable_norm_primeIdeal_factor_sub_one`), and the value is pinned by the
prime-ideal Euler product `dedekindZeta_eq_tprod_primeIdeal`. -/
private theorem hasProd_primeIdeal_factor
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹) (NumberField.dedekindZeta L s) := by
  have hmul : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
    simpa using multipliable_one_add_of_summable
      (f := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1)
      (summable_norm_primeIdeal_factor_sub_one L hs)
  rw [dedekindZeta_eq_tprod_primeIdeal L hs]
  exact hmul.hasProd

/-- The prime-ideal Euler factor restricted to any predicate-subtype of the nonzero primes is
`Multipliable`. (`Multipliable.subtype` is avoided — it `comp_injective`s and whnf-explodes on the
`Ideal (𝓞 L)` prime subtype; we restrict the *summable* norm via `Summable.subtype`, which does not,
then rebuild multipliability with `multipliable_one_add_of_summable`.) -/
private theorem multipliable_primeIdeal_factor_subtype
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re)
    (p : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → Prop) :
    Multipliable fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} =>
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} → ℝ) :=
    (summable_norm_primeIdeal_factor_sub_one L hs).subtype p
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} ↦
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsum

/-- The χ-twisted local Euler product `∏'_{𝔭 unram} (1 - χ(σ_𝔭) N𝔭^{-s})^{-1} = L_χ` is
`Multipliable`. As for `ζ_L`, this is absolute convergence: `‖χ(σ_𝔭)‖ = 1`
(`norm_galoisCharacter_out`), so `‖χ(σ_𝔭) N𝔭^{-s}‖ = ‖N𝔭^{-s}‖ ≤ 1/2`, and `∑_{𝔭 unram} ‖N𝔭^{-s}‖`
is a sub-sum of the absolutely convergent `ζ_K`. -/
private theorem multipliable_artinLocalFactor
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
  have hsumP : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (⟨𝔭.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ : NonzeroIdeal K))
      (fun _ _ h ↦ Subtype.ext (by simpa using h))
  have hsummable : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔭 ↦ ?_) (hsumP.mul_left 2)
    set y : ℂ := (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hy
    have hynorm : ‖y‖ ≤ 1 / 2 := by
      rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
      exact norm_absNorm_cpow_neg_le_half (R := 𝓞 K) hs
        ⟨𝔭.1, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩
    calc ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := norm_one_sub_inv_sub_one_le hynorm
      _ = 2 * ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ := by
          rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1) hsummable

/-- The map sending an unramified-below `L`-prime `𝔓` to the unramified `K`-prime `𝔓.under` below
it. -/
private def underUP
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} :=
  ⟨𝔓.1.under (𝓞 K), by haveI := 𝔓.2.1; exact inferInstance, 𝔓.2.2.2⟩

@[simp] private theorem underUP_val
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    (underUP K L 𝔓).1 = 𝔓.1.under (𝓞 K) := rfl

/-- The fibre of `underUP` over an unramified `K`-prime `c` is, after reindexing, the set of primes
`𝔓` of `𝓞 L` lying over `c` (`LiesOver`). Used to match the fibre product against
`dedekindZeta_local_factor_eq_product_artin_local`. -/
private def fiberUnderEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}) :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))} //
        underUP K L 𝔓 = c} ≃
      {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, ⟨by
    have h := congrArg Subtype.val 𝔓.2; rw [underUP_val] at h; rw [← h]⟩, 𝔓.1.2.2.1⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.2, by
      haveI := 𝔔.2.1; haveI := 𝔔.2.2.1; rw [← 𝔔.2.2.1.over]; exact c.2.2⟩, by
    haveI := 𝔔.2.1; haveI := 𝔔.2.2.1
    exact Subtype.ext (by rw [underUP_val]; exact 𝔔.2.2.1.over.symm)⟩
  left_inv 𝔓 := by ext; rfl
  right_inv 𝔔 := by ext; rfl

/-- Flatten the doubly-nested unramified-below prime subtype `{{𝔓 // prime ∧ ≠⊥} // unram}` to the
triply-nested `{𝔓 // prime ∧ ≠⊥ ∧ unram}`. Extracted as a top-level `def` (with a fully ascribed
signature) so the subtype equivalence is elaborated once, not re-`whnf`'d inside each big
reindexing proof. -/
private def unramifiedFlattenEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
      {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ UnramifiedIn K L (𝔔.under (𝓞 K))} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Flatten the doubly-nested ramified-below prime subtype `{{𝔓 // prime ∧ ≠⊥} // ¬unram}` to the
triply-nested `{𝔓 // prime ∧ ≠⊥ ∧ ¬unram}`. Extracted as a top-level `def` (with a fully ascribed
signature) so the subtype equivalence is elaborated once, not re-`whnf`'d inside the big reindexing
proof. -/
private def ramifiedFlattenEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
      {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔔.under (𝓞 K))} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unramified part of the prime-ideal Euler product equals `∏_χ L_χ`. Regroup the unramified
`L`-primes fibrewise over the `K`-prime below them (`Equiv.sigmaFiberEquiv` +
`Multipliable.tprod_sigma`); each fibre product is `∏_χ (1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`
(`dedekindZeta_local_factor_eq_product_artin_local`, `fiberUnderEquiv`); swap the finite character
product out (`Multipliable.tprod_finsetProd`) and apply the abelian Euler product
(`exists_artinLSeries_eulerProduct_abelian`). -/
private theorem tprod_unramified_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  classical
  set F : Ideal (𝓞 L) → ℂ := fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ with hF
  set G : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ :=
    fun c ↦ ∏' χ : galoisCharacter K L,
      (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹ with hG
  -- `Multipliable.subtype` is avoided: it whnf-explodes on the `Ideal (𝓞 L)` prime subtype.
  -- Restrict the *summable* norm via `Summable.subtype`, then rebuild multipliability.
  have hmulU : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))} ↦ F 𝔓.1 := by
    have hsumU : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
        {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (x.1.under (𝓞 K))} → ℝ) :=
      (summable_norm_primeIdeal_factor_sub_one L hs).subtype
        (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))
    have hmul1 : Multipliable fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (x.1.under (𝓞 K))} ↦ F 𝔓.1.1 := by
      simpa [hF] using multipliable_one_add_of_summable
        (f := fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
            UnramifiedIn K L (x.1.under (𝓞 K))} ↦
          (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsumU
    exact (Equiv.multipliable_iff (unramifiedFlattenEquiv K L).symm).mpr hmul1
  have hfibHasProd : ∀ c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      HasProd (fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} ↦ F 𝔓.1.1) (G c) := by
    intro c
    haveI : c.1.IsPrime := c.2.1
    haveI : c.1.IsMaximal := c.2.1.isMaximal (UnramifiedIn.ne_bot K L c.2.2)
    haveI : Finite (c.1.primesOver (𝓞 L)) :=
      (IsDedekindDomain.primesOver_finite c.1 (𝓞 L)).to_subtype
    haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} :=
      Finite.of_injective
        (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦
          (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : c.1.primesOver (𝓞 L)))
        (fun _ _ hab ↦ Subtype.ext (by simpa using hab))
    haveI : Finite {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
        UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} :=
      Finite.of_equiv _ (fiberUnderEquiv K L c).symm
    have hval : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c}, F 𝔓.1.1) = G c := by
      simp only [hG]
      rw [← dedekindZeta_local_factor_eq_product_artin_local K L c.1 c.2.2 s hs,
        ← (fiberUnderEquiv K L c).tprod_eq
          (fun 𝔔 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦ F 𝔔.1)]
      rfl
    rw [← hval]
    exact (Multipliable.of_finite).hasProd
  have hsig : HasProd G (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))}, F 𝔓.1) :=
    ((Equiv.sigmaFiberEquiv (underUP K L)).hasProd_iff.mpr hmulU.hasProd).sigma hfibHasProd
  rw [← hsig.tprod_eq]
  simp only [hG]
  simp_rw [tprod_fintype]
  rw [Multipliable.tprod_finsetProd (s := (Finset.univ : Finset (galoisCharacter K L)))
    (f := fun χ : galoisCharacter K L ↦
      fun c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
        (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹)
    (fun χ _ ↦ multipliable_artinLocalFactor K L χ hs)]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [artinDirichletSeries, ← exists_artinLSeries_eulerProduct_abelian K L χ s hs]

/-- Partition `ζ_L`'s prime-ideal Euler product into the unramified-below and ramified-below halves,
via `HasProd.mul_compl` (the off-the-shelf `tprod_subtype_mul_tprod_subtype_compl` `comp_injective`s
and whnf-times-out). Extracted from `dedekindZeta_eq_prod_artinDirichletSeries` so the
`HasProd.mul_compl`/`HasProd.unique` higher-order unification on the `Ideal (𝓞 L)` prime subtype is
elaborated once. -/
private theorem dedekindZeta_eq_unramifiedNested_mul_ramifiedNested
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹) *
        ∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  -- `f`/`S` are pinned explicitly so `HasProd.mul_compl` does no higher-order unification
  -- (`?f ∘ Subtype.val`) on the nested `Ideal (𝓞 L)` prime subtype — that is the `whnf` bomb.
  let f : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → ℂ :=
    fun 𝔓 ↦ (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
  let S : Set {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} :=
    {𝔓 | UnramifiedIn K L (𝔓.1.under (𝓞 K))}
  have hSU := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  have hSUc := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  exact ((hSU.mul_compl (f := f) (s := S) hSUc).unique
    (hasProd_primeIdeal_factor L hs)).symm

/-- The unramified-below half of `ζ_L`'s prime product (in nested-subtype form) equals `∏_χ L_χ`:
flatten the nested subtype with `unramifiedFlattenEquiv`, then apply
`tprod_unramified_eq_prod_artinDirichletSeries`. Extracted so the `Equiv.tprod_eq` reindexing is
elaborated once. -/
private theorem tprod_unramifiedNested_eq_prod_artin
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  rw [← tprod_unramified_eq_prod_artinDirichletSeries K L hs]
  exact Equiv.tprod_eq (unramifiedFlattenEquiv K L)
    (fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)

/-- The ramified-below half of `ζ_L`'s prime product (in nested-subtype form) equals the same
product indexed by the flat triply-nested ramified subtype: flatten with `ramifiedFlattenEquiv`.
Extracted so the `Equiv.tprod_eq` reindexing is elaborated once. -/
private theorem tprod_ramifiedNested_eq_ramified
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {s : ℂ} :
    (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ :=
  Equiv.tprod_eq (ramifiedFlattenEquiv K L) fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹

/-- **The zeta factorisation** (Sharifi 7.1.16, p. 141, with the ramified factor made explicit).
For `1 < Re s`, `ζ_L(s) = (∏_χ L_χ(s)) · R(s)`, where `L_χ = artinDirichletSeries K L χ` is the
Euler product over **unramified** primes only, and the correction `R(s)` is the (finite) product of
the Euler factors `(1 - N𝔓^{-s})^{-1}` over the primes `𝔓` of `𝓞 L` lying over a **ramified**
prime of `𝓞 K`.

The naive identity `ζ_L = ∏_χ L_χ` is false: `L_χ` drops the ramified primes (its ideal coefficient
`χ(𝔭)` is `0` at ramified `𝔭`), whereas `ζ_L = ∏'_{all 𝔓}(1 - N𝔓^{-s})^{-1}` keeps them; `R`
collects exactly the dropped factors. Only finitely many primes ramify, each with finitely many
`𝔓` above, so `R` is a finite product, nonzero for real `s > 1`. -/
theorem dedekindZeta_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))},
          (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
  rw [dedekindZeta_eq_unramifiedNested_mul_ramifiedNested K L hs,
    tprod_unramifiedNested_eq_prod_artin K L hs, tprod_ramifiedNested_eq_ramified K L]

/-- The primes `𝔓` of `𝓞 L` lying over a **ramified** `K`-prime form a finite set: only finitely
many `K`-primes ramify (`finite_ramifiedIn`), and each has finitely many primes above it. -/
private instance finite_ramifiedAbove
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := by
  classical
  haveI : Finite {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} :=
    (finite_ramifiedIn K L).to_subtype
  haveI : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
      Finite (𝔭.1.primesOver (𝓞 L)) := fun 𝔭 ↦ by
    haveI : 𝔭.1.IsPrime := 𝔭.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.1.isMaximal 𝔭.2.2.1
    exact (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 L)).to_subtype
  refine Finite.of_injective
    (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} ↦
      (show Σ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
          𝔭.1.primesOver (𝓞 L) by
        haveI := 𝔓.2.1
        exact ⟨⟨𝔓.1.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔓.2.2.1, 𝔓.2.2.2⟩,
          ⟨𝔓.1, 𝔓.2.1, Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)⟩⟩))
    (fun a b hab ↦ Subtype.ext (by simpa using congrArg (fun x ↦ (x.2 : Ideal (𝓞 L))) hab))

/-- For real `s > 1`, `ζ_L(s)` is a (positive) **real** number: it equals the real-cast of its real
part. This is the companion of `dedekindZeta_re_pos_of_one_lt` recording that the value, not just
its real part, is real — the Dirichlet series `∑ₙ (mult n) n^{-s}` has real terms. -/
private theorem dedekindZeta_eq_ofReal_re
    (L : Type*) [Field L] [NumberField L] {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta L (s : ℂ) = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]; norm_cast
    rw [hg]; push_cast [hcast]; ring
  have hval : NumberField.dedekindZeta L (s : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs', Complex.ofReal_tsum]
    exact tsum_congr key
  rw [hval, Complex.ofReal_re]

open Filter Topology Set in
/-- The ramified correction factor `R(s) = ∏'_{𝔓 ram-below} (1 - N𝔓^{-s})^{-1}` is a finite product
of factors each continuous at `s = 1` and tending to the finite nonzero limit `(1 - N𝔓^{-1})^{-1}`
(`N𝔓 ≥ 2`). Hence `‖R(s)‖` is bounded away from `0` and `∞` near `s ↓ 1`, so `|log ‖R(s)‖| ≤ C`.
This is the `O(1)` gap between `log ζ_L` and `Σ_χ log ‖L_χ‖` in the corrected factorisation. -/
private theorem log_norm_ramified_factor_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖| ≤
        C := by
  classical
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := Fintype.ofFinite _
  set R : ℝ → ℂ := fun s ↦ ∏ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ with hR
  have hbase : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (Ideal.absNorm 𝔓.1 : ℂ) ≠ 0 := fun 𝔓 ↦ by
    have hne0 : Ideal.absNorm 𝔓.1 ≠ 0 := fun h ↦ 𝔓.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast hne0
  have hden1 : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
    fun 𝔓 ↦ by
    have h2 : 2 ≤ Ideal.absNorm 𝔓.1 := two_le_absNorm 𝔓.2.1 𝔓.2.2.1
    have hlt : ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
      rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by lia : 1 < Ideal.absNorm 𝔓.1))
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hcont : ContinuousAt R 1 := by
    rw [ContinuousAt, hR]
    refine tendsto_finsetProd _ fun 𝔓 _ ↦ ?_
    have hcpow : ContinuousAt (fun s : ℝ ↦ (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ))) 1 :=
      (continuousAt_const_cpow (hbase 𝔓)).comp Complex.continuous_ofReal.continuousAt.neg
    exact (continuousAt_const.sub hcpow).inv₀ (by simpa using hden1 𝔓)
  have hR1_ne : R 1 ≠ 0 :=
    hR ▸ Finset.prod_ne_zero_iff.mpr fun 𝔓 _ ↦ inv_ne_zero (by simpa using hden1 𝔓)
  have hlogcont : ContinuousAt (fun s : ℝ ↦ Real.log ‖R s‖) 1 :=
    hcont.norm.log (norm_ne_zero_iff.mpr hR1_ne)
  refine ⟨|Real.log ‖R 1‖| + 1, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ),
      |Real.log ‖R s‖ - Real.log ‖R 1‖| ≤ 1 := by
    filter_upwards [hlogcont (Metric.closedBall_mem_nhds (Real.log ‖R 1‖) one_pos)] with s hs
    simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hs
  filter_upwards [nhdsWithin_le_nhds hev] with s hs
  rw [show (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) = R s
    by rw [hR]; exact tprod_fintype _]
  have htri : |Real.log ‖R s‖| ≤ |Real.log ‖R s‖ - Real.log ‖R 1‖| + |Real.log ‖R 1‖| := by
    simpa using abs_add_le (Real.log ‖R s‖ - Real.log ‖R 1‖) (Real.log ‖R 1‖)
  linarith

open Filter Topology Set in
/-- **Ingredient A, bounded real-log form.** Taking `log ‖·‖` of the corrected factorisation
`ζ_L(s) = (∏_χ L_χ(s)) · R(s)` and using that `ζ_L(s)` is a positive real gives
`log ζ_L(s) = Σ_χ log‖L_χ(s)‖ + log‖R(s)‖`. Since the ramified correction `‖R(s)‖` is bounded
away from `0` and `∞` near `s ↓ 1` (`log_norm_ramified_factor_bounded`), the gap between
`log ζ_L(s).re` and `Σ_χ log‖L_χ(s)‖` is `O(1)`. This `O(1)` slack is harmless for the pole-order
contradiction in `artinLSeries_one_ne_zero`. -/
private theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (NumberField.dedekindZeta L (s : ℂ)).re -
        ∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖| ≤ C := by
  obtain ⟨C, hC⟩ := log_norm_ramified_factor_bounded K L
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re :=
    dedekindZeta_re_pos_of_one_lt L s hs1
  have hfact : NumberField.dedekindZeta L (s : ℂ) =
      (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype]
  have hnorm : ‖NumberField.dedekindZeta L (s : ℂ)‖ = (NumberField.dedekindZeta L (s : ℂ)).re := by
    rw [dedekindZeta_eq_ofReal_re L hs1, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      Complex.ofReal_re]
  have hprodχ_ne : (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) ≠ 0 := fun h0 ↦
    hpos.ne' (by rw [hfact, h0, zero_mul, Complex.zero_re])
  have hR_ne : (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) ≠ 0 :=
    fun h0 ↦ hpos.ne' (by rw [hfact, h0, mul_zero, Complex.zero_re])
  have hχ_ne : ∀ χ ∈ (Finset.univ : Finset (galoisCharacter K L)),
      ‖artinDirichletSeries K L χ (s : ℂ)‖ ≠ 0 := fun χ _ ↦
    norm_ne_zero_iff.mpr fun hχ0 ↦ hprodχ_ne (Finset.prod_eq_zero (Finset.mem_univ χ) hχ0)
  have hsplit : Real.log (NumberField.dedekindZeta L (s : ℂ)).re =
      (∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖) +
        Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖ := by
    rw [← hnorm, hfact, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hprodχ_ne) (norm_ne_zero_iff.mpr hR_ne),
      norm_prod, Real.log_prod hχ_ne]
  rw [hsplit]
  simpa using hCs

/-- `1` lies in the L-function analyticity domain `{s : ℂ | 1 - [K:ℚ]⁻¹ < Re s}` (the
geometry-of-numbers half-plane), which is open, so `AnalyticOn` there upgrades to
`AnalyticAt ℂ Lf 1` at the interior point `1`. -/
private theorem analyticAt_one_of_analyticOn_finrankDomain (K : Type*) [Field K] [NumberField K]
    {Lf : ℂ → ℂ} (hLf : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re}) :
    AnalyticAt ℂ Lf 1 := by
  have hmem : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
    have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
      have : 0 < Module.finrank ℚ K := Module.finrank_pos
      positivity
    simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
  exact hLf.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)

open Filter Topology Set in
/-- **Assembly helper (ii).** For a nontrivial character `χ'`, the L-series `L_{χ'}` extends
analytically across `s = 1` (`artinLSeries_analytic_extension`, the LF4 leaf), hence `‖L_{χ'}(s)‖`
is bounded above on a right neighbourhood of `s = 1`. (Here `L_{χ'}(s) = artinDirichletSeries`,
which agrees with the analytic extension on `Re s > 1`.) -/
private theorem artinDirichletSeries_norm_le_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ' : galoisCharacter K L) (hχ' : χ' ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤ C := by
  obtain ⟨Lf', hLf'_an, hLf'_eq⟩ := artinLSeries_analytic_extension K L m hm χ' hχ'
  have hcont : ContinuousAt Lf' 1 :=
    (analyticAt_one_of_analyticOn_finrankDomain K hLf'_an).continuousAt
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hbdd : ∀ᶠ z in 𝓝 (1 : ℂ), ‖Lf' z‖ ≤ ‖Lf' 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (Metric.ball_mem_nhds ‖Lf' 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  refine ⟨‖Lf' 1‖ + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hmap.eventually hbdd] with s hs1 hbdd_s
  simp only [mem_Ioi] at hs1
  have heq : artinDirichletSeries K L χ' (s : ℂ) = Lf' (s : ℂ) := by
    rw [artinDirichletSeries, ← hLf'_eq (s : ℂ) (by simpa using hs1)]
  rwa [heq]

open Filter Topology Set in
/-- **Assembly helper (i).** The trivial-character L-series `L_1(s) = artinDirichletSeries K L 1 s`
is bounded above by the simple-pole asymptotic of `ζ_K`:
`log‖L_1(s)‖ ≤ log(1/(s-1)) + C` near `s ↓ 1`.

`L_1(s) = ∑'_{𝔞} χ̃_1(𝔞) N𝔞^{-s}` with `‖χ̃_1(𝔞)‖ ≤ 1` (`norm_galoisCharacterOnIdeal_le_one`), so
termwise `‖χ̃_1(𝔞) N𝔞^{-s}‖ ≤ N𝔞^{-s}` and hence `‖L_1(s)‖ ≤ ∑'_{𝔞} N𝔞^{-s} = ζ_K(s)`
(`hasSum_nonzeroIdeal_absNorm_cpow` for `K`). For real `s > 1`, `ζ_K(s) ≥ 1` (the unit-ideal term),
so `0 ≤ log ζ_K(s)` and `log ‖L_1(s)‖ ≤ log ζ_K(s) ≤ log(1/(s-1)) + C`
(`logDedekindZeta_sub_log_inv_sub_one_bounded` for `K`). -/
private theorem log_norm_artinDirichletSeries_one_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hζ := hasSum_nonzeroIdeal_absNorm_cpow K hs'
  have hnorm_eq : ∀ 𝔞 : NonzeroIdeal K,
      ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ = ((Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))).re := by
    intro 𝔞
    have hpos : 0 < Ideal.absNorm 𝔞.1 :=
      Nat.pos_of_ne_zero fun h ↦ 𝔞.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hcast : (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ)) =
        (((Ideal.absNorm 𝔞.1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]; norm_cast
    rw [hcast, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (by positivity)]
  have hsum_norm : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hζ.summable.norm
  have hsum_norm_eq : (∑' 𝔞 : NonzeroIdeal K, ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖)
      = (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [tsum_congr hnorm_eq, ← Complex.re_tsum hζ.summable, hζ.tsum_eq]
  have hterm : ∀ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ ≤
        ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
    intro 𝔞
    rw [norm_mul]
    calc ‖galoisCharacterOnIdeal K L 1 𝔞.1‖ * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖
        ≤ 1 * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
          gcongr; exact norm_galoisCharacterOnIdeal_le_one K L 1 𝔞.1
      _ = ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := one_mul _
  have hsum_term : Summable fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hsum_norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hL1_le : ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [artinDirichletSeries]
    refine (norm_tsum_le_tsum_norm hsum_term).trans ?_
    rw [← hsum_norm_eq]
    exact Summable.tsum_le_tsum hterm hsum_term hsum_norm
  have hζ_ge1 : (1 : ℝ) ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← hsum_norm_eq]
    refine le_trans ?_ (hsum_norm.le_tsum (⟨⊤, by simp⟩ : NonzeroIdeal K) fun 𝔞 _ ↦ norm_nonneg _)
    rw [Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, norm_one]
  have hlog_le : Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤
      Real.log (NumberField.dedekindZeta K (s : ℂ)).re := by
    rcases eq_or_lt_of_le (norm_nonneg (artinDirichletSeries K L 1 (s : ℂ))) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hζ_ge1
    · exact Real.log_le_log h0 hL1_le
  exact hlog_le.trans (by linarith [abs_le.mp hCs])

open Classical in
private theorem sum_ite_pole_zero_cancel
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] {χ : galoisCharacter K L} (hχ : χ ≠ 1) (a : ℝ) :
    ∑ χ' : galoisCharacter K L, (if χ' = 1 then a else if χ' = χ then -a else 0) = 0 := by
  have hsplit : ∀ χ' : galoisCharacter K L,
      (if χ' = 1 then a else if χ' = χ then -a else 0) =
        (if χ' = 1 then a else 0) + (if χ' = χ then -a else 0) := fun χ' ↦ by
    by_cases h1 : χ' = 1
    · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ Ne.symm hχ), add_zero]
    · rw [if_neg h1, if_neg h1]; by_cases hc : χ' = χ <;> simp [hc]
  rw [Finset.sum_congr rfl fun χ' _ ↦ hsplit χ', Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (1 : galoisCharacter K L), Finset.sum_ite_eq' Finset.univ χ]
  simp

open Classical Filter Topology Set in
/-- **Per-character log bound (Dirichlet's contradiction, assembled over all characters).** Given a
nontrivial `χ` whose χ-factor `L_χ` has an analytic-zero bound `log‖L_χ(s)‖ ≤ -log(1/(s-1)) + Cχ`
near `s ↓ 1`, every character factor `L_{χ'}` satisfies an eventual upper bound of the matching
shape `log‖L_{χ'}(s)‖ ≤ (pole at χ'=1) + (zero at χ'=χ) + C`: the trivial factor is the `ζ_K`-pole
(`log_norm_artinDirichletSeries_one_le`), the `χ`-factor is the supplied zero bound, and every other
factor is `O(1)` via its analytic extension (`artinDirichletSeries_norm_le_of_ne_one`). -/
private theorem log_norm_artinDirichletSeries_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) {χ : galoisCharacter K L} {Cχ : ℝ}
    (hCχ : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ)
    (χ' : galoisCharacter K L) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C := by
  by_cases h1 : χ' = 1
  · subst h1
    obtain ⟨C1, hC1⟩ := log_norm_artinDirichletSeries_one_le K L
    exact ⟨C1, by filter_upwards [hC1] with s hs; rwa [if_pos rfl]⟩
  · by_cases hc : χ' = χ
    · subst hc
      exact ⟨Cχ, by filter_upwards [hCχ] with s hs; rwa [if_neg h1, if_pos rfl]⟩
    · obtain ⟨C, hC⟩ := artinDirichletSeries_norm_le_of_ne_one K L m hm χ' h1
      refine ⟨Real.log (max C 1), ?_⟩
      filter_upwards [hC] with s hs
      simp only [if_neg h1, if_neg hc, zero_add]
      have hmax1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
      rcases le_total ‖artinDirichletSeries K L χ' (s : ℂ)‖ 0 with h0 | h0
      · have hz : ‖artinDirichletSeries K L χ' (s : ℂ)‖ = 0 := le_antisymm h0 (norm_nonneg _)
        rw [hz, Real.log_zero]
        exact Real.log_nonneg hmax1
      · rcases eq_or_lt_of_le h0 with h0' | h0'
        · rw [← h0', Real.log_zero]; exact Real.log_nonneg hmax1
        · exact Real.log_le_log h0' (le_trans hs (le_max_left _ _))

/-- For real `s > 1` the χ-factor `L_χ(s) = artinDirichletSeries K L χ s` is nonzero: it is a
factor of the corrected factorisation `ζ_L(s) = (∏_{χ'} L_{χ'}(s)) · R(s)`, and `ζ_L(s)` is a
positive real (`dedekindZeta_re_pos_of_one_lt`), so no factor can vanish. -/
private theorem artinDirichletSeries_ne_zero_of_one_lt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) {s : ℝ}
    (hs : 1 < s) : artinDirichletSeries K L χ (s : ℂ) ≠ 0 := fun hzero ↦ by
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re := dedekindZeta_re_pos_of_one_lt L s hs
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  rw [show NumberField.dedekindZeta L (s : ℂ) = 0 by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype,
      Finset.prod_eq_zero (Finset.mem_univ χ) hzero, zero_mul], Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

open Classical Filter Topology Set in
/-- **Pole-cancellation contradiction.** If for a nontrivial `χ` every character factor obeys the
ite-bound `log‖L_{χ'}(s)‖ ≤ (pole at χ'=1) + (zero at χ'=χ) + C χ'` near `s ↓ 1`, then summing over
the finite character group cancels the `ζ_K`-pole (χ'=1) against the supposed zero (χ'=χ), leaving
`log ζ_L(s).re` bounded above — contradicting its divergence to `+∞`
(`logDedekindZeta_re_tendsto_atTop`, modulo the ramified `O(1)` slack
`log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`). -/
private theorem false_of_eventually_log_norm_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {χ : galoisCharacter K L} (hχ : χ ≠ 1)
    {C : galoisCharacter K L → ℝ} (hC : ∀ χ' : galoisCharacter K L, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') : False := by
  obtain ⟨CR, hCR⟩ := log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded K L
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log (NumberField.dedekindZeta L (s : ℂ)).re ≤ (∑ χ', C χ') + CR := by
    filter_upwards [Filter.eventually_all.2 hC, hCR] with s hs_all hCRs
    have hsumle : ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
        ≤ ∑ χ', C χ' := by
      calc ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
          ≤ ∑ χ' : galoisCharacter K L,
              ((if χ' = 1 then Real.log (1 / (s - 1)) else
                if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') :=
            Finset.sum_le_sum fun χ' _ ↦ hs_all χ'
        _ = ∑ χ' : galoisCharacter K L, C χ' := by
            rw [Finset.sum_add_distrib, sum_ite_pole_zero_cancel K L hχ (Real.log (1 / (s - 1))),
              zero_add]
    have := abs_le.mp hCRs
    linarith [this.1, this.2]
  obtain ⟨s, hge, hle⟩ :=
    (((logDedekindZeta_re_tendsto_atTop L).eventually_ge_atTop ((∑ χ', C χ') + CR + 1)).and
      hbound).exists
  linarith

open Filter Topology Set in
/-- Sharifi 7.1.19 step 2 (p. 142): non-vanishing of `L(χ,1)` for
nontrivial `χ`. Source argument: if any `L(χ,1) = 0`, the
`log ζ_L = Σ_χ log L(χ,·)` decomposition leads to a sub-asymptotic
strictly weaker than the simple pole `log ζ_L ~ log(1/(s-1))`, a
contradiction. Uses `artinLSeries_analytic_extension` so that
"`L(χ, 1)` is defined" makes sense — the extension brings `s = 1` into
the analyticity domain.

**Stated at cyclotomic generality** (`L = K(μ_m)`): the proof bounds every other nontrivial
factor `L_{χ'}` near `s = 1` via its analytic extension
(`artinDirichletSeries_norm_le_of_ne_one` ⟸ `artinLSeries_analytic_extension`), which — like
the geometry-of-numbers leaf it rests on — is CFT-free only cyclotomically (see the restatement
note on `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`, expert review 2026-06-05). -/
theorem artinLSeries_one_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∀ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} →
      (∀ s : ℂ, 1 < s.re →
        Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
          galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) →
      Lf 1 ≠ 0 := by
  classical
  intro Lf hLf_an hLf_eq hLf0
  have hLf_eq' : ∀ s : ℂ, 1 < s.re → Lf s = artinDirichletSeries K L χ s :=
    fun s hs ↦ by rw [hLf_eq s hs, artinDirichletSeries]
  have hLf_at : AnalyticAt ℂ Lf 1 := analyticAt_one_of_analyticOn_finrankDomain K hLf_an
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hLf_ne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), Lf z = 0 := by
    intro hloc
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ℝ, Lf (s : ℂ) = 0 ∧ 1 < s :=
      ((hmap.eventually hloc).and self_mem_nhdsWithin).exists
    exact artinDirichletSeries_ne_zero_of_one_lt K L χ hs1
      (by rw [← hLf_eq' _ (by simpa using hs1), hs0])
  obtain ⟨Cχ, hCχ⟩ := analytic_log_norm_le_of_apply_eq_zero hLf_at hLf0 hLf_ne
  have hCχ' : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ := by
    filter_upwards [hCχ, self_mem_nhdsWithin] with s hs hs1
    simp only [mem_Ioi] at hs1
    rwa [← hLf_eq' (s : ℂ) (by simpa using hs1)]
  choose C hC using log_norm_artinDirichletSeries_le_pole_zero_ite K L m hm hCχ'
  exact false_of_eventually_log_norm_le_pole_zero_ite K L _hχ hC

end Chebotarev
