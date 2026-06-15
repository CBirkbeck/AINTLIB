module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import BernoulliRegular.GaussSum.Basic

/-!
# Cyclotomic field embedding into `ℂ`

For the cyclotomic field `L/ℚ` of conductor `n`, we construct the
`ℚ`-algebra embedding `emb : L →ₐ[ℚ] ℂ` sending a given primitive root
of `L` to a chosen primitive root of unity in `ℂ`. Under this embedding,
the Gauss sum `τ(χ) ∈ ℂ` — shown to lie in
`Algebra.adjoin ℤ {stickelbergerComplexRoot p}` by T027d1 — lifts
uniquely to an element of `L`, and (by integrality) to the ring of
integers `𝒪_L`.

This is T027d2 of the Stickelberger chain.

## Main results

* `BernoulliRegular.complexEmbedding_of_primitiveRoot`: given any
  primitive `n`-th root `ζ_ℂ ∈ ℂ`, the `ℚ`-algebra embedding
  `L →ₐ[ℚ] ℂ` sending `IsCyclotomicExtension.zeta n ℚ L` to `ζ_ℂ`.
* `BernoulliRegular.gaussSum_mem_range_stickelbergerEmbedding`: for
  non-trivial `χ`, the complex Gauss sum `τ(χ)` lies in the image of
  the canonical embedding `L →ₐ[ℚ] ℂ` of a cyclotomic field
  `L = ℚ(ζ_{p(p-1)})` sending its primitive root to
  `stickelbergerComplexRoot p`.
-/

@[expose] public section

noncomputable section


namespace BernoulliRegular

open Polynomial

section CyclotomicEmbedding

variable (n : ℕ) [hn : NeZero n]
variable (L : Type*) [Field L] [CharZero L] [Algebra ℚ L]
variable [IsCyclotomicExtension {n} ℚ L]

/-- Given a primitive `n`-th root of unity `ζ_ℂ ∈ ℂ`, the `ℚ`-algebra
embedding `L →ₐ[ℚ] ℂ` sending `IsCyclotomicExtension.zeta n ℚ L` to
`ζ_ℂ`. Existence and uniqueness come from
`IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`. -/
noncomputable def complexEmbedding_of_primitiveRoot
    {ζ_C : ℂ} (hζ_C : IsPrimitiveRoot ζ_C n) : L →ₐ[ℚ] ℂ := by
  have hirr : Irreducible (cyclotomic n ℚ) :=
    cyclotomic.irreducible_rat hn.out.bot_lt
  have hζL : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  exact (hζL.embeddingsEquivPrimitiveRoots (K := ℚ) (L := L) ℂ hirr).symm
    ⟨ζ_C, (mem_primitiveRoots hn.out.bot_lt).mpr hζ_C⟩

omit [CharZero L] in
/-- The complex embedding sends the distinguished primitive root of `L`
to the specified complex primitive root. -/
theorem complexEmbedding_of_primitiveRoot_apply_zeta {ζ_C : ℂ} (hζ_C : IsPrimitiveRoot ζ_C n) :
    complexEmbedding_of_primitiveRoot n L hζ_C
        (IsCyclotomicExtension.zeta n ℚ L) = ζ_C := by
  have hirr : Irreducible (cyclotomic n ℚ) :=
    cyclotomic.irreducible_rat hn.out.bot_lt
  have hζL : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L) n :=
    IsCyclotomicExtension.zeta_spec n ℚ L
  -- The bijection `embeddingsEquivPrimitiveRoots` characterizes the
  -- embedding by its image of `ζ_L`.
  have := hζL.embeddingsEquivPrimitiveRoots_apply_coe (K := ℚ) (L := L) ℂ hirr
    (complexEmbedding_of_primitiveRoot n L hζ_C)
  -- After applying `symm` the image is `ζ_C` by definition.
  simp only [complexEmbedding_of_primitiveRoot, Equiv.apply_symm_apply] at this
  exact this.symm

omit [CharZero L] in
/-- The image of the complex embedding contains the specified primitive
root, hence the entire `ℤ`-subalgebra it generates. -/
theorem complexEmbedding_of_primitiveRoot_range_contains_adjoin
    {ζ_C : ℂ} (hζ_C : IsPrimitiveRoot ζ_C n) :
    Algebra.adjoin ℤ ({ζ_C} : Set ℂ) ≤
      ((complexEmbedding_of_primitiveRoot n L hζ_C).range.restrictScalars ℤ) := by
  apply Algebra.adjoin_le
  simp only [Set.singleton_subset_iff, SetLike.mem_coe,
    Subalgebra.mem_restrictScalars]
  exact ⟨IsCyclotomicExtension.zeta n ℚ L,
    complexEmbedding_of_primitiveRoot_apply_zeta n L hζ_C⟩

end CyclotomicEmbedding

section StickelbergerEmbedding

variable (p : ℕ) [hp : Fact p.Prime]

/-- Positivity of `p * (p - 1)`. -/
theorem stickelberger_nsize_pos : 0 < p * (p - 1) :=
  Nat.mul_pos hp.out.pos (by have := hp.out.one_lt; omega)

/-- `NeZero` instance for `p * (p - 1)` when `p` is prime. -/
instance stickelberger_neZero : NeZero (p * (p - 1)) :=
  ⟨(stickelberger_nsize_pos p).ne'⟩

variable (L : Type*) [Field L] [CharZero L] [Algebra ℚ L]
variable [IsCyclotomicExtension {p * (p - 1)} ℚ L]

/-- The Stickelberger complex embedding: the `ℚ`-algebra embedding
`L →ₐ[ℚ] ℂ` from the cyclotomic field `L = ℚ(ζ_{p(p-1)})` to `ℂ` sending
the distinguished primitive root `IsCyclotomicExtension.zeta` to
`stickelbergerComplexRoot p = exp(2πi/(p(p-1)))`. -/
noncomputable def stickelbergerEmbedding : L →ₐ[ℚ] ℂ :=
  complexEmbedding_of_primitiveRoot (p * (p - 1)) L
    (stickelbergerComplexRoot_isPrimitiveRoot p)

omit [CharZero L] in
/-- The Stickelberger embedding sends `ζ_L` to the canonical complex
primitive root. -/
theorem stickelbergerEmbedding_apply_zeta :
    stickelbergerEmbedding p L
        (IsCyclotomicExtension.zeta (p * (p - 1)) ℚ L) =
      stickelbergerComplexRoot p :=
  complexEmbedding_of_primitiveRoot_apply_zeta (p * (p - 1)) L
    (stickelbergerComplexRoot_isPrimitiveRoot p)

omit [CharZero L] in
/-- **T027d2**: for any Dirichlet character `χ` mod a prime `p`, the
complex Gauss sum `τ(χ) = gaussSum χ ZMod.stdAddChar` lies in the image
of the Stickelberger embedding `L →ₐ[ℚ] ℂ`.

This combines T027d1 (`τ(χ) ∈ Algebra.adjoin ℤ {stickelbergerComplexRoot}`)
with the embedding's image containing that adjoin. The existential
consequence — that `τ(χ)` lifts to a canonical element of `L` — is the
content of `gaussSum_stickelbergerEmbedding_preimage`. -/
theorem gaussSum_mem_range_stickelbergerEmbedding
    (χ : DirichletCharacter ℂ p) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ∈
      (stickelbergerEmbedding p L).range := by
  have h_mem : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ∈
      Algebra.adjoin ℤ ({stickelbergerComplexRoot p} : Set ℂ) :=
    gaussSum_mem_algebraAdjoin_stickelbergerComplexRoot p χ
  have h_sub := complexEmbedding_of_primitiveRoot_range_contains_adjoin
    (p * (p - 1)) L (stickelbergerComplexRoot_isPrimitiveRoot p)
  exact h_sub h_mem

/-- The canonical lift of the complex Gauss sum `τ(χ)` into the cyclotomic
field `L = ℚ(ζ_{p(p-1)})`, as a preimage under the Stickelberger embedding.
The defining property `stickelbergerEmbedding p L (gaussSumLift p L χ) =
gaussSum χ stdAddChar` holds by construction; see
`stickelbergerEmbedding_gaussSumLift`. -/
noncomputable def gaussSumLift (χ : DirichletCharacter ℂ p) : L :=
  (gaussSum_mem_range_stickelbergerEmbedding p L χ).choose

omit [CharZero L] in
/-- The canonical lift `gaussSumLift` satisfies
`emb (gaussSumLift) = gaussSum χ stdAddChar`. -/
theorem stickelbergerEmbedding_gaussSumLift (χ : DirichletCharacter ℂ p) :
    stickelbergerEmbedding p L (gaussSumLift p L χ) =
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) :=
  (gaussSum_mem_range_stickelbergerEmbedding p L χ).choose_spec

omit [CharZero L] in
/-- **T027d2** (integrality refinement): the canonical lift
`gaussSumLift p L χ ∈ L` of the Gauss sum is an algebraic integer, i.e.,
lies in the ring of integers `𝒪_L`.

This combines T027c (integrality of `gaussSum χ stdAddChar` over `ℤ`
as an element of `ℂ`) with the injectivity of the Stickelberger
embedding `L →ₐ[ℚ] ℂ` via `RingHom.IsIntegralElem.map_iff`. -/
theorem isIntegral_gaussSumLift (χ : DirichletCharacter ℂ p) :
    IsIntegral ℤ (gaussSumLift p L χ) := by
  -- Injectivity of the Stickelberger embedding (as ring hom on a field).
  have h_inj : Function.Injective (stickelbergerEmbedding p L).toRingHom :=
    (stickelbergerEmbedding p L).toRingHom.injective
  -- `IsIntegral ℤ (gaussSum …)` by T027c, lifted to the bundled form.
  have h_integral_C : (algebraMap ℤ ℂ).IsIntegralElem
      (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) :=
    isIntegral_gaussSum_stdAddChar p χ
  -- Rewrite via the defining property of `gaussSumLift`.
  rw [← stickelbergerEmbedding_gaussSumLift p L χ] at h_integral_C
  -- Factor `algebraMap ℤ ℂ` as
  -- `(stickelbergerEmbedding p L).toRingHom ∘ algebraMap ℤ L`.
  have h_factor : (algebraMap ℤ ℂ : ℤ →+* ℂ) =
      (stickelbergerEmbedding p L).toRingHom.comp (algebraMap ℤ L) := by
    ext m
    simp
  rw [h_factor] at h_integral_C
  -- Use `RingHom.IsIntegralElem.map_iff` to strip the embedding.
  exact (RingHom.IsIntegralElem.map_iff h_inj).mp h_integral_C

/-- Non-vanishing of the Gauss sum for a non-trivial Dirichlet character
modulo a prime: `τ(χ) ≠ 0` in `ℂ`.

This is `gaussSum_ne_zero_of_nontrivial` applied to our setting (primitivity
of `ZMod.stdAddChar` plus the standard non-vanishing hypothesis). -/
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_card : (Fintype.card (ZMod p) : ℂ) ≠ 0 := by
    rw [ZMod.card]; exact_mod_cast hp.out.ne_zero
  exact gaussSum_ne_zero_of_nontrivial h_card hχ (ZMod.isPrimitive_stdAddChar p)

omit [CharZero L] in
/-- The canonical lift `gaussSumLift` is non-zero for any non-trivial
Dirichlet character. -/
theorem gaussSumLift_ne_zero {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    gaussSumLift p L χ ≠ 0 := by
  intro hzero
  have h := stickelbergerEmbedding_gaussSumLift p L χ
  rw [hzero, map_zero] at h
  exact gaussSum_ne_zero p hχ h.symm

/-- The canonical lift of the Gauss sum into the ring of integers `𝒪_L`.
Packaged from `gaussSumLift` and `isIntegral_gaussSumLift`. -/
noncomputable def gaussSumIntegers (χ : DirichletCharacter ℂ p) :
    NumberField.RingOfIntegers L :=
  haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
  ⟨gaussSumLift p L χ, isIntegral_gaussSumLift p L χ⟩

omit [CharZero L] in
/-- The underlying `L`-element of `gaussSumIntegers` is `gaussSumLift`. -/
theorem gaussSumIntegers_val (χ : DirichletCharacter ℂ p) :
    haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
    ((gaussSumIntegers p L χ : NumberField.RingOfIntegers L) : L) =
      gaussSumLift p L χ :=
  rfl

omit [CharZero L] in
/-- `gaussSumIntegers` is non-zero for non-trivial `χ`. -/
theorem gaussSumIntegers_ne_zero {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
    gaussSumIntegers p L χ ≠ 0 := by
  haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
  intro h
  apply gaussSumLift_ne_zero p L hχ
  have : ((gaussSumIntegers p L χ : NumberField.RingOfIntegers L) : L) = 0 := by
    rw [h]; rfl
  rwa [gaussSumIntegers_val] at this

omit [CharZero L] in
/-- **T027e** (Ideal factorisation of `(τ(χ))`).

In the ring of integers `𝒪_L = NumberField.RingOfIntegers L` of the
cyclotomic field `L = ℚ(ζ_{p(p-1)})`, the principal ideal generated by
the canonical lift `gaussSumIntegers p L χ` of the Gauss sum `τ(χ) ∈ ℂ`
factors as the product of its prime-power contributions.

This is the Dedekind-domain factorisation identity
`Ideal.span {τ} = ∏ 𝔭^{v_𝔭((τ))}` made concrete via
`UniqueFactorizationMonoid.normalizedFactors_prod` on the principal ideal.
The specific `v_𝔭` values at non-`p` primes is Stickelberger's theorem
(T027d, deferred); this lemma assembles the ideal-theoretic wrapper. -/
theorem gaussSum_ideal_factorisation {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
    (Ideal.span ({gaussSumIntegers p L χ} :
        Set (NumberField.RingOfIntegers L))) =
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({gaussSumIntegers p L χ} :
          Set (NumberField.RingOfIntegers L)))).prod := by
  haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
  -- In a Dedekind domain, any non-zero ideal equals the product of its
  -- normalized factors.
  have h_ne : Ideal.span ({gaussSumIntegers p L χ} :
      Set (NumberField.RingOfIntegers L)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact gaussSumIntegers_ne_zero p L hχ
  exact (Ideal.prod_normalizedFactors_eq_self h_ne).symm

/-- Auxiliary: `χ(-1) ∈ {1, -1}` for any Dirichlet character `χ` modulo a
prime `p`, since `χ(-1)² = χ(1) = 1` in a field of characteristic zero. -/
theorem DirichletCharacter.chi_neg_one_sq (χ : DirichletCharacter ℂ p) :
    χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h_sq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, show ((-1 : ZMod p) * -1) = 1 from by ring, map_one]
  rcases mul_self_eq_one_iff.mp h_sq with h | h
  · exact Or.inl h
  · exact Or.inr h

omit [CharZero L] in
/-- **T027d-i** (ideal form of T026): the product of the principal ideals
generated by `τ(χ)` and `τ(χ̄)` in `𝒪_L` equals the principal ideal `(p)`.

This is the "norm-squared" identity transferred from T026's complex
identity `τ(χ) · τ(χ̄) = χ(-1) · p` via the Stickelberger embedding,
using that `χ(-1) = ±1` is a unit.

As a step toward the full Stickelberger theorem (T027d), this pins down
the *total* `𝔭`-adic valuation contribution of `(τ(χ))·(τ(χ̄))` at each
prime above `p`, complementing the splitting information needed at other
primes. -/
theorem gaussSum_ideal_mul_inv_eq_span_p
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
    Ideal.span ({gaussSumIntegers p L χ} :
        Set (NumberField.RingOfIntegers L)) *
      Ideal.span ({gaussSumIntegers p L χ⁻¹} :
        Set (NumberField.RingOfIntegers L)) =
      Ideal.span ({(p : NumberField.RingOfIntegers L)} :
        Set (NumberField.RingOfIntegers L)) := by
  haveI : NumberField L := IsCyclotomicExtension.numberField {p * (p - 1)} ℚ L
  set a : NumberField.RingOfIntegers L := gaussSumIntegers p L χ
  set b : NumberField.RingOfIntegers L := gaussSumIntegers p L χ⁻¹
  set pL : NumberField.RingOfIntegers L := (p : NumberField.RingOfIntegers L)
  -- First: a * b = χ(-1)_lift * p in 𝒪_L, where χ(-1)_lift = ±1.
  rw [Ideal.span_singleton_mul_span_singleton]
  -- Show span {a * b} = span {pL}, i.e. a * b and pL are associates.
  -- Helper: equality in 𝒪_L reduces to equality on underlying L-values,
  -- and multiplication/negation distribute through the subring coercion.
  have embed_val : ∀ x : NumberField.RingOfIntegers L,
      stickelbergerEmbedding p L (x : L) = (stickelbergerEmbedding p L).toRingHom x := fun _ => rfl
  -- Compute `emb((p : 𝒪_L) : L) = (p : ℂ)`.
  have h_emb_p : stickelbergerEmbedding p L ((pL : NumberField.RingOfIntegers L) : L) =
      (p : ℂ) := by
    simp [pL]
  -- Core identity: `emb(gaussSumLift χ) * emb(gaussSumLift χ⁻¹) = χ(-1) * p` in ℂ.
  have h_core : stickelbergerEmbedding p L (gaussSumLift p L χ) *
      stickelbergerEmbedding p L (gaussSumLift p L χ⁻¹) = χ (-1) * (p : ℂ) := by
    rw [stickelbergerEmbedding_gaussSumLift, stickelbergerEmbedding_gaussSumLift]
    exact gaussSum_mul_gaussSum_inv_stdAddChar p hχ
  rcases DirichletCharacter.chi_neg_one_sq p χ with h_pos | h_neg
  · -- Case χ(-1) = 1: a * b = p in 𝒪_L.
    have h_eq : a * b = pL := by
      apply Subtype.ext
      change (a : L) * (b : L) = (pL : L)
      apply (stickelbergerEmbedding p L).injective
      rw [map_mul]
      change stickelbergerEmbedding p L (gaussSumLift p L χ) *
          stickelbergerEmbedding p L (gaussSumLift p L χ⁻¹) =
        stickelbergerEmbedding p L ((pL : L))
      rw [h_core, h_pos, one_mul, h_emb_p]
    rw [h_eq]
  · -- Case χ(-1) = -1: a * b = -p in 𝒪_L, same ideal as p.
    have h_eq : a * b = -pL := by
      apply Subtype.ext
      change (a : L) * (b : L) = ((-pL : NumberField.RingOfIntegers L) : L)
      apply (stickelbergerEmbedding p L).injective
      rw [map_mul]
      change stickelbergerEmbedding p L (gaussSumLift p L χ) *
          stickelbergerEmbedding p L (gaussSumLift p L χ⁻¹) =
        stickelbergerEmbedding p L (((-pL : NumberField.RingOfIntegers L) : L))
      rw [h_core, h_neg]
      have : ((-pL : NumberField.RingOfIntegers L) : L) = -(pL : L) := by
        push_cast; rfl
      rw [this, map_neg, h_emb_p]
      ring
    rw [h_eq, Ideal.span_singleton_neg]

end StickelbergerEmbedding

end BernoulliRegular
