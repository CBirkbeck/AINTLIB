module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

public import CebotarevDensity.Abelian
public import CebotarevDensity.FixedFieldDensity

/-!
# Chebotarev's density theorem

For a finite Galois extension `L/K` of number fields with Galois group
`G = Gal(L/K)` and a conjugacy class `C` of `G`, the Dirichlet density of
primes `𝔭` of `𝓞 K` (unramified in `L`) whose Frobenius conjugacy class is
`C` equals `|C| / |G|`.

The proof (Sharifi 7.2.2 Step 1; Stevenhagen–Lenstra Appendix paragraph 2)
reduces the conjugacy-class statement to the cyclic case via the
intermediate field `E = L^⟨σ⟩` for `σ ∈ C`:

- `L/E` is cyclic of degree `f = |⟨σ⟩|`, hence abelian, so the abelian case
  (`chebotarev_abelian`) gives density `1/f` for primes of `E` with
  Frobenius `σ`.
- A counting argument over the primes of `L` lying above a prime of `K`
  shows that, for the set `S` of primes `𝔭` of `K` whose Frobenius class is
  `C`, and `T_σ` the set of primes `P` of `E` with `σ_P = σ`,

      δ_K(S) = (f · |C| / |G|) · δ_E(T_σ).

  With `δ_E(T_σ) = 1/f` from the cyclic case, this gives `δ_K(S) = |C|/|G|`.

## Main results

* `Chebotarev.chebotarev_density` — Chebotarev's density
  theorem in conjugacy-class form.
* `Chebotarev.dirichlet_primes_in_AP` — Dirichlet's theorem
  on primes in arithmetic progressions, as a corollary.
* `Chebotarev.density_split_completely` — the density of
  primes of `K` that split completely in `L` is `1/[L:K]`.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (`docs/algnum.pdf`,
  pp. 142–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

open scoped ENNReal

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **Chebotarev's density theorem** (Sharifi 7.2.2; SL Appendix).

For a finite Galois extension `L/K` of number fields with Galois group `G`
and a conjugacy class `C ⊆ G`, the Dirichlet density of the set of primes
`𝔭` of `𝓞 K` (unramified in `L`) such that the Frobenius conjugacy class of
`𝔭` is `C` equals `|C| / |G|`. -/
theorem chebotarev_density
    [FiniteDimensional K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  let e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  have : IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul e x y, ← map_mul e y x, mul_comm' x y]
  exact density_lift_through_fixedField σ
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    (e ⟨σ, Subgroup.mem_zpowers σ⟩) rfl rfl
    (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))

/-- In a commutative finite monoid every conjugacy class is a singleton,
so `|C| = 1`. -/
theorem ConjClasses_carrier_card_eq_one_of_comm
    {G : Type*} [Monoid G] [IsMulCommutative G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1 := by
  letI : CommMonoid G := IsMulCommutative.instCommMonoid
  have h : (ConjClasses.mk g).carrier = {g} := by
    ext a
    simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
  simp [h]

/-- **Chebotarev's density theorem, abelian case.** For an abelian Galois
extension `L/K`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius conjugacy class is `C` is `|C| / |Gal(L/K)|`. -/
theorem chebotarev_density_of_comm
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  simpa [ConjClasses_carrier_card_eq_one_of_comm σ] using chebotarev_abelian K L σ

/-- A set of prime ideals with positive Dirichlet density is infinite. -/
theorem infinite_of_hasDirichletDensity_pos
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity S δ) (hδ : 0 < δ) :
    S.Infinite :=
  fun hfin ↦ hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))

/-- The carrier of a conjugacy class in a finite monoid has positive cardinality. -/
theorem ConjClasses_carrier_card_pos
    {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) :
    0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos

/-- Existence of *infinitely many* primes with each Frobenius conjugacy class
— a qualitative corollary of `chebotarev_density`. -/
theorem infinite_setOf_frobenius_class
    (C : ConjClasses Gal(L/K)) :
    Set.Infinite
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C} := by
  refine infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_
  apply div_pos
  · exact_mod_cast ConjClasses_carrier_card_pos C
  · exact_mod_cast Nat.card_pos (α := Gal(L/K))

/-- The identity conjugacy class in a finite monoid has carrier of cardinality `1`. -/
theorem ConjClasses_mk_one_carrier_card_eq_one
    (G : Type*) [Monoid G] [Finite G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  have h : (ConjClasses.mk (1 : G)).carrier = {1} := by
    simp [Set.ext_iff, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  simp [h]

/-- **Density of completely split primes** (Sharifi 7.1.14, as a corollary of
Chebotarev applied to the identity conjugacy class).

The Dirichlet density of primes `𝔭` of `𝓞 K` that split completely in `L`
equals `1 / [L : K]`. -/
theorem density_split_completely :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank K L : ℝ)⁻¹) := by
  have h := chebotarev_density (ConjClasses.mk (1 : Gal(L/K)))
  rw [ConjClasses_mk_one_carrier_card_eq_one Gal(L/K), IsGalois.card_aut_eq_finrank K L] at h
  simpa using h

/-! ### Sub-lemmas for `dirichlet_primes_in_AP`

The `K = ℚ`, `L = ℚ(μ_n)` specialisation of Chebotarev (Sharifi 7.2.3). The target image-set
of rational primes `p ≡ a [n]` is identified — up to a *finite* set of bad primes — with the
cyclotomic Frobenius-fibre of a Galois element `σ` chosen so that the cyclotomic character
sends `σ` to the unit `a`. Two ingredients beyond `chebotarev_cyclotomic`:

* density is insensitive to finite symmetric differences
  (`hasDirichletDensity_of_finite_symmDiff`), letting us discard the finitely many primes
  dividing `n` (or the single prime `2` in the degenerate `n ≡ 2 [4]` corner);
* the `𝓞 ℚ ≃+* ℤ` dictionary (`Rat.ringOfIntegersEquiv`): every nonzero prime of `𝓞 ℚ` is
  `span {(p)}` for a unique rational prime `p` with `N(span {(p)}) = p`. -/

section DirichletAP

variable {K : Type*} [Field K] [NumberField K]

/-- The partial Dirichlet series satisfies `Σ_T = Σ_S + Σ_{T∖S} − Σ_{S∖T}` (for `1 < s`),
from two disjoint-union splittings `T = (T∩S) ⊔ (T∖S)` and `S = (T∩S) ⊔ (S∖T)`. -/
private theorem primeIdealZetaSum_eq_add_sub_sdiff {S T : Set (Ideal (𝓞 K))} {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum T s
      = primeIdealZetaSum S s + primeIdealZetaSum (T \ S) s - primeIdealZetaSum (S \ T) s := by
  have hdisj : ∀ A B : Set (Ideal (𝓞 K)), Disjoint (A ∩ B) (A \ B) :=
    fun A B ↦ disjoint_of_subset_left inter_subset_right disjoint_sdiff_right
  have hT : primeIdealZetaSum T s
      = primeIdealZetaSum (T ∩ S) s + primeIdealZetaSum (T \ S) s := by
    conv_lhs => rw [← inter_union_diff T S]
    rw [primeIdealZetaSum_union_of_disjoint (hdisj T S) hs]
  have hS : primeIdealZetaSum S s
      = primeIdealZetaSum (T ∩ S) s + primeIdealZetaSum (S \ T) s := by
    conv_lhs => rw [← inter_union_diff S T]
    rw [primeIdealZetaSum_union_of_disjoint (hdisj S T) hs, inter_comm]
  rw [hT, hS]
  ring

/-- **Density is insensitive to finite symmetric differences.** If `S ∖ T` and `T ∖ S` are
both finite and `S` has Dirichlet density `δ`, then so does `T`: the two ratios differ by
`(Σ_{T∖S} − Σ_{S∖T}) / Σ_univ`, whose numerator is bounded while the denominator `→ ∞`. -/
private theorem hasDirichletDensity_of_finite_symmDiff {S T : Set (Ideal (𝓞 K))} {δ : ℝ}
    (hST : (S \ T).Finite) (hTS : (T \ S).Finite) (hS : HasDirichletDensity S δ) :
    HasDirichletDensity T δ := by
  have hTSden : HasDirichletDensity (T \ S) 0 := hasDirichletDensity_of_finite K hTS
  have hSTden : HasDirichletDensity (S \ T) 0 := hasDirichletDensity_of_finite K hST
  rw [HasDirichletDensity] at hS hTSden hSTden ⊢
  have h := (hS.add hTSden).sub hSTden
  refine (show (δ + 0 - 0 : ℝ) = δ by ring) ▸ h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  rw [primeIdealZetaSum_eq_add_sub_sdiff (S := S) (T := T) hs]
  ring

/-- **Chinese remainder injectivity.** Two elements of `ZMod (m * k)` (with `m`, `k` coprime)
that agree under both coordinate `castHom`s are equal — `ZMod.chineseRemainder` is injective. -/
private theorem zmod_eq_of_castHom_eq {m k : ℕ} (hcop : Nat.Coprime m k) (x y : ZMod (m * k))
    (h1 : (ZMod.castHom (dvd_mul_right m k) (ZMod m)) x
        = (ZMod.castHom (dvd_mul_right m k) (ZMod m)) y)
    (h2 : (ZMod.castHom (dvd_mul_left k m) (ZMod k)) x
        = (ZMod.castHom (dvd_mul_left k m) (ZMod k)) y) : x = y := by
  apply (ZMod.chineseRemainder hcop).injective
  have e1 : ∀ z : ZMod (m * k), ((ZMod.chineseRemainder hcop) z).1
      = (ZMod.castHom (dvd_mul_right m k) (ZMod m)) z := fun z ↦ by
    simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk, ZMod.castHom_apply,
      Prod.fst_zmod_cast]
  have e2 : ∀ z : ZMod (m * k), ((ZMod.chineseRemainder hcop) z).2
      = (ZMod.castHom (dvd_mul_left k m) (ZMod k)) z := fun z ↦ by
    simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk, ZMod.castHom_apply,
      Prod.snd_zmod_cast]
  exact Prod.ext (by rw [e1, e1, h1]) (by rw [e2, e2, h2])

end DirichletAP

/-- The absolute norm of `span {(p : 𝓞 ℚ)}` is `p`: `Ideal.absNorm_span_natCast` gives
`p ^ rank ℤ (𝓞 ℚ)`, and `rank ℤ (𝓞 ℚ) = rank ℚ ℚ = 1`. -/
private theorem absNorm_span_nat (p : ℕ) : Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p := by
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

/-- The rational prime `span {(p : 𝓞 ℚ)}` is the pullback of `span {(p : ℤ)}` along
`Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. -/
private theorem ratSpan_eq_comap_intSpan (p : ℕ) :
    Ideal.span {(p : 𝓞 ℚ)} = Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(p : ℤ)}) := by
  rw [← Ideal.map_symm Rat.ringOfIntegersEquiv, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [map_natCast]

/-- **Every nonzero prime of `𝓞 ℚ` is `span {(p)}` for a rational prime `p`.** Transport the
prime `𝔭` through `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`: its image is a nonzero prime of `ℤ`,
hence `span {(p : ℤ)}` for a prime `p` (`Ideal.isPrime_int_iff`); pull back. -/
private theorem ratPrime_eq_span (𝔭 : Ideal (𝓞 ℚ)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 𝔭 = Ideal.span {(p : 𝓞 ℚ)} := by
  set e := Rat.ringOfIntegersEquiv
  have hbij : Function.Bijective e := e.bijective
  have hJp : (Ideal.map e 𝔭).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcomap : Ideal.comap e (Ideal.map e 𝔭) = 𝔭 := Ideal.comap_map_of_bijective e hbij
  have hJne : Ideal.map e 𝔭 ≠ ⊥ := by
    intro h; apply hne; rw [← hcomap, h, Ideal.comap_bot_of_injective e hbij.injective]
  rcases (Ideal.isPrime_int_iff.mp hJp) with h | ⟨p, hpp, hpJ⟩
  · exact absurd h hJne
  · exact ⟨p, hpp, by rw [← hcomap, hpJ, ratSpan_eq_comap_intSpan]⟩

/-- The converse classification ingredient: `span {(p : 𝓞 ℚ)}` is prime for a rational prime
`p`, via the same `𝓞 ℚ ≃+* ℤ` transport (`comap` of the prime `span {(p : ℤ)}`). -/
private theorem span_nat_isPrime {p : ℕ} (hpp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)}).IsPrime := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hpp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpp)
  rw [ratSpan_eq_comap_intSpan]
  exact Ideal.comap_isPrime Rat.ringOfIntegersEquiv (Ideal.span {(p : ℤ)})

/-- **A coprime-norm prime is unramified in the cyclotomic extension** `L = K(μ_m)`. A
ramified prime divides the different, which divides `(f'(ζ))` (conductor formula); since
`minpoly ∣ X^m − 1`, that value divides `m·ζ^{m−1}`, forcing `m ∈ 𝔓`, hence `N𝔭 ∣ m^d`,
contradicting coprimality. (Replica of the private `unramifiedIn_of_coprime_absNorm` in
`ZetaProduct.lean`, which is not importable here.) -/
private theorem unramifiedIn_cyclotomic_of_coprime {K : Type*} [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
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
  set ζ𝓞 : 𝓞 L := hζ.toInteger
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
    ⟨conductor (𝓞 K) ζ𝓞, by rw [← conductor_mul_differentIdeal (𝓞 K) K L ζ𝓞 hadj]; ring⟩
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
    rw [h𝔓lo.over]
    exact Ideal.mem_comap.mpr (by rwa [map_natCast])
  have hdvd_norm : Ideal.absNorm 𝔭 ∣ m ^ Module.finrank ℤ (𝓞 K) :=
    Ideal.absNorm_span_natCast (S := 𝓞 K) m ▸
      Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm𝔭)
  exact absurd (Ideal.absNorm_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop.pow_right _) dvd_rfl hdvd_norm))
    ‹𝔭.IsPrime›.ne_top

/-- **Frobenius ↔ residue dictionary** for `L = ℚ(μ_n)` with `σ` chosen so the cyclotomic
character `autToPow` sends `σ` to the unit `a`. For a coprime-norm unramified prime `𝔭`, the
Frobenius class is `mk σ` iff `N𝔭 ≡ a [n]`: `autToPow_frobeniusClass_out` realises the
Frobenius as `N𝔭 mod n`, and `autToPow` is injective (and the group is abelian, so `mk` is). -/
private theorem frobeniusClass_eq_iff_residue
    (n : ℕ) [NeZero n] (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a)
    (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit)
    (𝔭 : Ideal (𝓞 ℚ)) [𝔭.IsPrime] (hunr : UnramifiedIn ℚ L 𝔭)
    (hcop : (Ideal.absNorm 𝔭).Coprime n) :
    frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ ↔ (Ideal.absNorm 𝔭 : ZMod n) = a := by
  letI : CommMonoid (L ≃ₐ[ℚ] L) := IsMulCommutative.instCommMonoid
  have hdict := autToPow_frobeniusClass_out ℚ L n hζ 𝔭 hunr hcop
  rw [show frobeniusClass ℚ L 𝔭 = ConjClasses.mk (frobeniusClass ℚ L 𝔭).out from
    (Quotient.out_eq _).symm, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
  constructor
  · intro h
    have he : hζ.autToPow ℚ (frobeniusClass ℚ L 𝔭).out = hζ.autToPow ℚ σ := by rw [h]
    rw [hdict, hσ] at he
    have hc := congrArg (Units.val) he
    rwa [ZMod.coe_unitOfCoprime, IsUnit.unit_spec] at hc
  · intro h
    apply hζ.autToPow_injective ℚ
    rw [hdict, hσ]
    apply Units.ext
    rwa [ZMod.coe_unitOfCoprime, IsUnit.unit_spec]

/-- For `n = 2·n'` with `n'` odd and an **odd** prime `p`, the residue condition mod `n`
matches the one mod `n'` (with `a' = a mod n'`): forward by `castHom`; backward by CRT, since
the `mod 2` coordinates agree — `(p : ZMod 2) = 1` and a unit of `ZMod n` is `1` mod `2`. -/
private theorem residue_iff_half (n' : ℕ) (hcop : Nat.Coprime 2 n')
    (a : ZMod (2 * n')) (ha : IsUnit a) (p : ℕ) (hpp : p.Prime) (hodd : p ≠ 2) :
    ((p : ZMod (2 * n')) = a ↔
      (p : ZMod n') = (ZMod.castHom (dvd_mul_left n' 2) (ZMod n')) a) := by
  constructor
  · intro h
    have hc := congrArg (ZMod.castHom (dvd_mul_left n' 2) (ZMod n')) h
    rwa [map_natCast] at hc
  · intro h
    apply zmod_eq_of_castHom_eq hcop
    · rw [map_natCast]
      have hp2 : (p : ZMod 2) = 1 := by
        have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hodd
        rw [← ZMod.natCast_mod p 2, h2]; norm_num
      rw [hp2]
      have hu : IsUnit ((ZMod.castHom (dvd_mul_right 2 n') (ZMod 2)) a) := ha.map _
      revert hu; generalize (ZMod.castHom (dvd_mul_right 2 n') (ZMod 2)) a = z
      revert z; decide
    · rwa [map_natCast]

/-- Primes in the Frobenius fibre `F = {𝔭 | frobeniusClass 𝔭 = mk σ}` but not the AP image-set
`I = {span p | p ≡ a [n]}` divide `n`: `F ∖ I ⊆ Bad`. A coprime-norm prime in `F` lands in `I`
by `frobeniusClass_eq_iff_residue`, so a prime of `F ∖ I` has norm sharing a factor with `n`. -/
private theorem dirichlet_AP_fibre_diff_image_subset_bad
    (n : ℕ) (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [NeZero n]
    [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a)
    (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) :
    {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ UnramifiedIn ℚ L 𝔭 ∧
        frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ} \
      (fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a} ⊆
      (fun q : ℕ ↦ Ideal.span {(q : 𝓞 ℚ)}) '' {q : ℕ | q.Prime ∧ q ∣ n} := by
  rintro 𝔭 ⟨⟨hpr, hunr, hfrob⟩, hnotI⟩
  haveI := hpr
  obtain ⟨q, hqp, hqeq⟩ := ratPrime_eq_span 𝔭 hpr (UnramifiedIn.ne_bot ℚ L hunr)
  have hnorm : Ideal.absNorm 𝔭 = q := by rw [hqeq, absNorm_span_nat]
  by_cases hcop : (Ideal.absNorm 𝔭).Coprime n
  · exfalso; apply hnotI
    refine ⟨q, ⟨hqp, ?_⟩, hqeq.symm⟩
    have hr := (frobeniusClass_eq_iff_residue n L hζ a ha σ hσ 𝔭 hunr hcop).mp hfrob
    rwa [hnorm] at hr
  · refine ⟨q, ⟨hqp, ?_⟩, hqeq.symm⟩
    rwa [hnorm, hqp.coprime_iff_not_dvd, not_not] at hcop

/-- Primes in the AP image-set `I = {span p | p ≡ a [n]}` but not the Frobenius fibre `F` divide
`n`: `I ∖ F ⊆ Bad`. A prime `p ≡ a [n]` with `p ∤ n` is unramified with coprime norm, so its
Frobenius is `mk σ` by `frobeniusClass_eq_iff_residue`, placing it in `F`. -/
private theorem dirichlet_AP_image_diff_fibre_subset_bad
    (n : ℕ) (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [NeZero n]
    [IsCyclotomicExtension {n} ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a)
    (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) :
    (fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a} \
      {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ UnramifiedIn ℚ L 𝔭 ∧
        frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ} ⊆
      (fun q : ℕ ↦ Ideal.span {(q : 𝓞 ℚ)}) '' {q : ℕ | q.Prime ∧ q ∣ n} := by
  rintro 𝔭 ⟨⟨p, ⟨hpp, hpa⟩, rfl⟩, hnotF⟩
  have hprime : (Ideal.span {(p : 𝓞 ℚ)}).IsPrime := span_nat_isPrime hpp
  haveI := hprime
  have hp0 : (p : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  by_cases hdvd : p ∣ n
  · exact ⟨p, ⟨hpp, hdvd⟩, rfl⟩
  · exfalso; apply hnotF
    have hcop : (Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)})).Coprime n := by
      rw [absNorm_span_nat]; exact (hpp.coprime_iff_not_dvd).mpr hdvd
    have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊥ :=
      Ideal.span_singleton_eq_bot.not.mpr hp0
    have hunr := unramifiedIn_cyclotomic_of_coprime L n _ hne hcop
    refine ⟨hprime, hunr, ?_⟩
    rw [frobeniusClass_eq_iff_residue n L hζ a ha σ hσ _ hunr hcop, absNorm_span_nat]
    exact hpa

/-- The main case of Dirichlet's AP theorem (`n ≢ 2 [4]`, so `chebotarev_cyclotomic` applies):
instantiate `L = ℚ(μ_n)`, pick `σ` with `autToPow σ = a`, and identify the target image-set
with the cyclotomic Frobenius-fibre up to the finite `Bad` set of primes dividing `n`. -/
private theorem dirichlet_AP_main (n : ℕ) (hn4 : n % 4 ≠ 2) (hn : 1 ≤ n)
    (a : ZMod n) (ha : IsUnit a) :
    HasDirichletDensity
      ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a})
      ((Nat.totient n : ℝ)⁻¹) := by
  have : NeZero n := ⟨by lia⟩
  -- The module system does not auto-synthesise `NeZero (n : ℚ)` for `CyclotomicField n ℚ` here.
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨by exact_mod_cast (show n ≠ 0 by lia)⟩
  set L := CyclotomicField n ℚ
  haveI : IsCyclotomicExtension {n} ℚ L := CyclotomicField.isCyclotomicExtension n ℚ
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  haveI : IsMulCommutative (L ≃ₐ[ℚ] L) :=
    IsCyclotomicExtension.isMulCommutative (S := {n}) ℚ L
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (by lia)
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L
    (Set.mem_singleton n) (NeZero.ne n)
  set E := IsCyclotomicExtension.autEquivPow L hirr with hE
  set σ : L ≃ₐ[ℚ] L := E.symm ha.unit with hσdef
  have hσ : hζ.autToPow ℚ σ = ha.unit := by
    have h1 : (E σ : (ZMod n)ˣ) = hζ.autToPow ℚ σ := by
      rw [hE, IsCyclotomicExtension.autEquivPow_apply]
      simp only [MonoidHom.toFun_eq_coe]
      rw [IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter,
        IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter]
    rw [← h1, hσdef, E.apply_symm_apply]
  have hfib := chebotarev_cyclotomic ℚ L n hn4 σ
  have hcard : (Nat.card (L ≃ₐ[ℚ] L) : ℝ)⁻¹ = (Nat.totient n : ℝ)⁻¹ := by
    congr 1
    rw [Nat.card_congr E.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hcard] at hfib
  set F := {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ UnramifiedIn ℚ L 𝔭 ∧
    frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ}
  set I := (fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
    {p : ℕ | p.Prime ∧ (p : ZMod n) = a}
  set Bad := (fun q : ℕ ↦ Ideal.span {(q : 𝓞 ℚ)}) '' {q : ℕ | q.Prime ∧ q ∣ n}
  have hBadfin : Bad.Finite := by
    apply Set.Finite.image
    apply Set.Finite.subset (Set.finite_Icc 0 n)
    intro q hq; simp only [Set.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.le_of_dvd (by lia) hq.2⟩
  exact hasDirichletDensity_of_finite_symmDiff
    (hBadfin.subset (dirichlet_AP_fibre_diff_image_subset_bad n L hζ a ha σ hσ))
    (hBadfin.subset (dirichlet_AP_image_diff_fibre_subset_bad n L hζ a ha σ hσ)) hfib

/-- The degenerate corner `n = 2 · n'` with `n'` odd (so `n ≡ 2 [4]`): `chebotarev_cyclotomic`
does not apply, but `ℚ(μ_{2n'}) = ℚ(μ_{n'})`, so the AP density for `2·n'` equals that for the
odd `n'`, the two image-sets differing only by the single prime `2`. -/
private theorem dirichlet_AP_two_mul (n' : ℕ) (hn'1 : 1 ≤ n') (hcop : Nat.Coprime 2 n')
    (a : ZMod (2 * n')) (ha : IsUnit a) :
    HasDirichletDensity
      ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod (2 * n')) = a})
      ((Nat.totient (2 * n') : ℝ)⁻¹) := by
  have hodd : ¬ 2 ∣ n' := Nat.prime_two.coprime_iff_not_dvd.mp hcop
  set a' : ZMod n' := (ZMod.castHom (dvd_mul_left n' 2) (ZMod n')) a
  have hmain := dirichlet_AP_main n' (by lia) hn'1 a' (ha.map _)
  have htot : (Nat.totient (2 * n') : ℝ)⁻¹ = (Nat.totient n' : ℝ)⁻¹ := by
    congr 1; rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
  rw [htot]
  set I2 := (fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
    {p : ℕ | p.Prime ∧ (p : ZMod (2 * n')) = a}
  set I' := (fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
    {p : ℕ | p.Prime ∧ (p : ZMod n') = a'}
  have hsub2 : I2 \ I' ⊆ {Ideal.span {(2 : 𝓞 ℚ)}} := by
    rintro 𝔭 ⟨⟨p, ⟨hpp, hpa⟩, rfl⟩, hnot⟩
    by_cases hp2 : p = 2
    · subst hp2; rfl
    · exact absurd ⟨p, ⟨hpp, (residue_iff_half n' hcop a ha p hpp hp2).mp hpa⟩, rfl⟩ hnot
  have hsub' : I' \ I2 ⊆ {Ideal.span {(2 : 𝓞 ℚ)}} := by
    rintro 𝔭 ⟨⟨p, ⟨hpp, hpa⟩, rfl⟩, hnot⟩
    by_cases hp2 : p = 2
    · subst hp2; rfl
    · exact absurd ⟨p, ⟨hpp, (residue_iff_half n' hcop a ha p hpp hp2).mpr hpa⟩, rfl⟩ hnot
  exact hasDirichletDensity_of_finite_symmDiff
    ((Set.finite_singleton _).subset hsub') ((Set.finite_singleton _).subset hsub2) hmain

/-- **Dirichlet's theorem on primes in arithmetic progressions**, as a
density refinement of `Nat.infinite_setOf_prime_and_eq_mod`.

For coprime integers `a, n` with `1 ≤ n` and `gcd a n = 1`, the Dirichlet
density of primes `p` with `p ≡ a mod n` equals `1 / φ(n)`. This is the
specialisation of Chebotarev to `K = ℚ`, `L = ℚ(μ_n)` (Sharifi 7.2.3). -/
theorem dirichlet_primes_in_AP (n : ℕ) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) :
    HasDirichletDensity
      ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
        {p : ℕ | p.Prime ∧ (p : ZMod n) = a})
      ((Nat.totient n : ℝ)⁻¹) := by
  by_cases hn4 : n % 4 = 2
  · obtain ⟨n', rfl⟩ : ∃ n', n = 2 * n' := ⟨n / 2, by lia⟩
    exact dirichlet_AP_two_mul n' (by lia)
      (by rw [Nat.prime_two.coprime_iff_not_dvd]; lia) a ha
  · exact dirichlet_AP_main n hn4 hn a ha

end Chebotarev
