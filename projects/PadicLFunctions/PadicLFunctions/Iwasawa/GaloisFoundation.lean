import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The Galois foundation for the Iwasawa Main Conjecture  (RJW §13.2) — ground-up construction

**Status: foundation in progress. This file builds the *real* objects of RJW §13.2 from the ground
up — there are NO abstract type-variable stand-ins and NO structures bundling the content.** It
replaces the retracted §13 "capstone", which assumed `X⁺_∞` etc. as `Type*` variables and bundled the
connecting isomorphisms as hypotheses (and therefore proved nothing about the actual Galois modules).

## The objects to construct (RJW §13.2, verbatim targets)

Write `Fₙ = ℚ(μ_{pⁿ})` and `Fₙ⁺` its maximal real subfield, `F∞ = ⋃ₙ Fₙ`, `F∞⁺ = ⋃ₙ Fₙ⁺`.

* `Mₙ` = the maximal abelian `p`-extension of `Fₙ` unramified outside `pₙ`; `Mₙ⁺` likewise for `Fₙ⁺`.
* `Lₙ` = the maximal *unramified* abelian `p`-extension of `Fₙ`; `Lₙ⁺` likewise.
* `M∞ = ⋃ₙ Mₙ`, `M∞⁺ = ⋃ₙ Mₙ⁺`, `L∞ = ⋃ₙ Lₙ`, `L∞⁺ = ⋃ₙ Lₙ⁺`.
* `X∞  = Gal(M∞/F∞)`,  `X∞⁺ = Gal(M∞⁺/F∞⁺)`,  `Y∞ = Gal(L∞/F∞)`,  `Y∞⁺ = Gal(L∞⁺/F∞⁺)`.
* (Remark 13.7) `Γ = Gal(F∞/F)` acts on `X∞` by `σ · x = σ̃ x σ̃⁻¹` (any lift `σ̃ ∈ Gal(M∞/ℚ)`),
  extending to a `Λ(Γ)`-module structure; identically `Λ(Γ⁺)` acts on `X∞⁺`, `Y∞⁺`.

## What mathlib provides vs. what must be built (honest dependency map)

PROVIDED: cyclotomic fields (`IsCyclotomicExtension`, `CyclotomicField`); `maximalRealSubfield` for CM
fields (`IsCMField`); finite-extension ramification (`IsUnramifiedAt`, `RamificationInertia/*`);
infinite Galois theory (`FieldTheory/Galois/{Infinite,Profinite,KrullTopology}`); `cyclotomicCharacter`.

THE WALL (not in mathlib — this is the genuine foundation work): there is **no** "maximal abelian
`p`-extension of a number field unramified outside a set `S`" as a field. `Mₙ`, `Lₙ` and their Galois
groups `Xₙ = Gal(Mₙ/Fₙ)` must be built as quotients of the absolute Galois group `G_{Fₙ}`:
`Xₙ` is the maximal pro-`p` abelian quotient of `G_{Fₙ}` killed by the inertia subgroups at all primes
`∤ pₙ` — assembled from `IsUnramifiedAt` + the abelianized/pro-`p` quotient of the Krull-topological
`G_{Fₙ}`. Then `X∞ = lim Xₙ` (or `Gal` of the union), with the `Λ(Γ)`-action of Remark 13.7.

This is a substantial, mathlib-PR-scale development. It is built here bottom-up; nothing downstream may
assume `Xₙ`/`X∞` until they are genuinely constructed.

## Bricks 1–2 (this file)

* **Brick 1** — the actual fields `Fₙ = ℚ(μ_{pⁿ})`, the layers of the tower.
* **Brick 2** — the real subfield `Fₙ⁺ = maximalRealSubfield Fₙ` (RJW: the maximal totally real
  subfield, i.e. the fixed field of complex conjugation), the CM structure of `Fₙ` (giving
  `[Fₙ : Fₙ⁺] = 2`), and the finite-level Galois group `Gal(Fₙ/ℚ) ≅ (ℤ/pⁿ)ˣ` (RJW §13.2 / the
  cyclotomic character at finite level). All real objects, no placeholders.
-/

noncomputable section

/-! ### General infrastructure: compositum of abelian extensions is abelian

`Gal(⨆ᵢ Eᵢ / F)` is commutative when each `Eᵢ/F` is abelian Galois. This is mathlib-missing (only
`normal_iSup` exists for the *normal* analogue, nothing for *abelian*), and is the keystone for the
`Λ(Γ⁺)`-module structure on `X⁺_∞`. Stated generally; a candidate for `Common/`/mathlib. -/

open IntermediateField in
/-- `Kᵢ`, viewed inside `↥(⨆ⱼ Kⱼ)` via `comap`, maps back to `Kᵢ` — used to transfer `IsAbelianGalois`. -/
noncomputable def restrAlgHom {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
    (K : ι → IntermediateField F E) (i : ι) :
    ↥(IntermediateField.comap (⨆ j, K j).val (K i)) →ₐ[F] ↥(K i) :=
  AlgHom.codRestrict (((⨆ j, K j).val).comp (IntermediateField.comap (⨆ j, K j).val (K i)).val)
    (K i).toSubalgebra (fun y => y.2)

open IntermediateField in
/-- **Compositum of abelian Galois extensions is abelian.** If each `Kᵢ/F` is abelian Galois, then the
Galois group of the compositum `⨆ᵢ Kᵢ` over `F` is commutative. -/
theorem isMulCommutative_iSup {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} (K : ι → IntermediateField F E) [∀ i, IsAbelianGalois F (K i)] :
    IsMulCommutative (↥(⨆ i, K i) ≃ₐ[F] ↥(⨆ i, K i)) := by
  haveI inst : ∀ i, IsAbelianGalois F ↥(comap (⨆ j, K j).val (K i)) :=
    fun i => IsAbelianGalois.of_algHom (restrAlgHom K i)
  have hsup : ⨆ i, comap (⨆ j, K j).val (K i) = ⊤ := by
    have hmap : map (⨆ j, K j).val (⨆ i, comap (⨆ j, K j).val (K i)) = ⨆ j, K j := by
      rw [IntermediateField.map_iSup]
      refine le_antisymm (iSup_le fun i => ?_) (iSup_le fun i => ?_)
      · rw [map_comap_eq]; exact inf_le_left.trans (le_iSup K i)
      · refine le_trans ?_ (le_iSup _ i)
        rw [map_comap_eq, inf_eq_left.mpr (by rw [IntermediateField.fieldRange_val]; exact le_iSup K i)]
    have htop : map (⨆ j, K j).val (⊤ : IntermediateField F ↥(⨆ j, K j)) = ⨆ j, K j := by
      apply SetLike.coe_injective; simp [IntermediateField.coe_map]
    exact (map_injective (⨆ j, K j).val) (hmap.trans htop.symm)
  rw [isMulCommutative_iff]; intro σ τ
  have key : ∀ i, ∀ x ∈ comap (⨆ j, K j).val (K i), (σ * τ) x = (τ * σ) x := by
    intro i x hx
    haveI := (inst i).toIsMulCommutative
    have hh : AlgEquiv.restrictNormalHom (comap (⨆ j, K j).val (K i)) (σ * τ)
            = AlgEquiv.restrictNormalHom (comap (⨆ j, K j).val (K i)) (τ * σ) := by
      rw [map_mul, map_mul]
      exact isMulCommutative_iff.mp (inst i).toIsMulCommutative _ _
    apply Subtype.val_injective
    rw [← AlgEquiv.restrictNormalHom_apply (comap (⨆ j, K j).val (K i)) (σ * τ) ⟨x, hx⟩,
        ← AlgEquiv.restrictNormalHom_apply (comap (⨆ j, K j).val (K i)) (τ * σ) ⟨x, hx⟩,
        congrArg (fun g => (g ⟨x, hx⟩ : ↥(comap (⨆ j, K j).val (K i)))) hh]
  refine AlgEquiv.ext fun y => ?_
  have hy : y ∈ adjoin F (⋃ i, (comap (⨆ j, K j).val (K i) : Set ↥(⨆ j, K j))) := by
    rw [← IntermediateField.iSup_eq_adjoin, hsup]; trivial
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx; exact key i x hxi
  | algebraMap x => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]

/-- Restriction-commute: for `B ⊆ F ⊆ M`, two `F`-automorphisms of `M` commute on any `B`-abelian
normal subfield `E` (restrict to the abelian `Gal(E/B)`). The base-change engine for `X⁺_∞` abelian:
an `F∞⁺`-automorphism, restricted to `Fₙ⁺`, lands in the abelian `Gal(Mₙ⁺/Fₙ⁺)`. -/
theorem commute_restrict {B F M : Type*} [Field B] [Field F] [Field M] [Algebra B F]
    [Algebra F M] [Algebra B M] [IsScalarTower B F M] (E : IntermediateField B M) [Normal B E]
    [IsMulCommutative (↥E ≃ₐ[B] ↥E)] (σ τ : M ≃ₐ[F] M) (x : ↥E) : σ (τ x) = τ (σ x) := by
  have h := isMulCommutative_iff.mp ‹IsMulCommutative (↥E ≃ₐ[B] ↥E)›
    ((τ.restrictScalars B).restrictNormal E) ((σ.restrictScalars B).restrictNormal E)
  have e := congrArg (fun g : ↥E ≃ₐ[B] ↥E => (algebraMap E M) (g x)) h
  simpa [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply] using e.symm

/-- `commute_restrict` packaged with `IsAbelianGalois` (which bundles `Normal` + abelian) — the form
used for base change to `X⁺_∞`. -/
theorem commute_restrict_AG {B F M : Type*} [Field B] [Field F] [Field M] [Algebra B F]
    [Algebra F M] [Algebra B M] [IsScalarTower B F M] (E : IntermediateField B M)
    [IsAbelianGalois B E] (σ τ : M ≃ₐ[F] M) (x : ↥E) : σ (τ x) = τ (σ x) := by
  haveI : Normal B ↥E := (‹IsAbelianGalois B ↥E›).toIsGalois.to_normal
  haveI : IsMulCommutative (↥E ≃ₐ[B] ↥E) := (‹IsAbelianGalois B ↥E›).toIsMulCommutative
  exact commute_restrict E σ τ x

namespace Iwasawa.GaloisFoundation

variable (p : ℕ) [Fact p.Prime]

/-- `Fₙ = ℚ(μ_{pⁿ})`, the `n`-th layer of the cyclotomic tower (RJW §9, §13.2). -/
abbrev Fcyc (n : ℕ) : Type _ := CyclotomicField (p ^ n) ℚ

/-- `Fₙ` is a cyclotomic extension of `ℚ` for `μ_{pⁿ}` — the defining property of the tower layer. -/
instance instIsCyclotomic (n : ℕ) :
    IsCyclotomicExtension {p ^ n} ℚ (Fcyc p n) :=
  CyclotomicField.isCyclotomicExtension (p ^ n) ℚ

/-- The conductor `pⁿ` is nonzero (so the cyclotomic API for `Fₙ` is available unconditionally). -/
instance instNeZeroPow (n : ℕ) : NeZero (p ^ n) :=
  ⟨pow_ne_zero n (Fact.out (p := p.Prime)).pos.ne'⟩

/-- `Fₙ` is a number field. -/
instance instNumberField (n : ℕ) : NumberField (Fcyc p n) :=
  inferInstanceAs (NumberField (CyclotomicField (p ^ n) ℚ))

open NumberField in
/-- `Fₙ⁺`, the maximal real subfield of `Fₙ = ℚ(μ_{pⁿ})` (RJW §13.2): the fixed field of complex
conjugation, i.e. the maximal totally real subfield. This is the base of the *real* tower `F∞⁺`.
A genuine `Subfield (Fcyc p n)`, defined unconditionally (no CM hypothesis needed to *define* it). -/
def FcycPlus (n : ℕ) : Subfield (Fcyc p n) :=
  maximalRealSubfield (Fcyc p n)

open NumberField in
/-- For odd `p` and `n ≥ 1` we have `2 < pⁿ`. -/
theorem two_lt_pow (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : 2 < p ^ n :=
  calc 2 < 3 := by norm_num
    _ ≤ p := (Fact.out (p := p.Prime)).two_le.lt_of_ne (Ne.symm hp2)
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out (p := p.Prime)).pos hn

open NumberField in
/-- `Fₙ = ℚ(μ_{pⁿ})` is a CM field whenever `2 < pⁿ` (in particular for odd `p`, `n ≥ 1`); this is
where `Fₙ⁺ = maximalRealSubfield Fₙ` becomes a genuine quadratic subextension, `[Fₙ : Fₙ⁺] = 2`. -/
theorem isCMField_Fcyc {n : ℕ} (h : 2 < p ^ n) : IsCMField (Fcyc p n) :=
  IsCyclotomicExtension.Rat.isCMField (Fcyc p n) (S := {p ^ n}) ⟨p ^ n, rfl, h⟩

/-- The finite-level Galois group `Gal(Fₙ/ℚ) ≅ (ℤ/pⁿ)ˣ` (RJW §13.2; the source of `Γ` and of the
cyclotomic character at finite level). A genuine multiplicative equivalence. -/
def galEquiv (n : ℕ) : (Fcyc p n ≃ₐ[ℚ] Fcyc p n) ≃* (ZMod (p ^ n))ˣ :=
  IsCyclotomicExtension.autEquivPow (Fcyc p n)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _))

/-! ### Brick 3 — the cyclotomic `ℤ_p`-tower `F∞ = ⋃ₙ Fₙ`, nested in one ambient closure

The abstract fields `Fcyc p n = CyclotomicField (pⁿ) ℚ` are pairwise unrelated *types*; the tower
`F∞ = ⋃ Fₙ` needs the `Fₙ` as genuine subfields of one ambient field. We fix `Ω = ℚ̄` and realise
each `Fₙ = ℚ(μ_{pⁿ})` as the `IntermediateField` generated by a primitive `pⁿ`-th root of unity.
Each nested `Fₙ` still satisfies `IsCyclotomicExtension {pⁿ} ℚ Fₙ`, so the brick-2 finite-level API
(CM structure, `Gal ≅ (ℤ/pⁿ)ˣ`) applies to it verbatim. `F∞` is then the supremum `⨆ₙ Fₙ`. -/

/-- The ambient field: a fixed algebraic closure of `ℚ`, inside which the whole tower lives. -/
abbrev Om : Type := AlgebraicClosure ℚ

/-- `(pⁿ : ℚ) ≠ 0` — needed for the "enough roots of unity" instance on `Ω`. -/
instance instNeZeroPowRat (n : ℕ) : NeZero ((p ^ n : ℕ) : ℚ) :=
  ⟨by exact_mod_cast (instNeZeroPow p n).ne⟩

/-- `Ω = ℚ̄` is algebraic over `ℚ`. (Registered explicitly: the library instance
`AlgebraicClosure.isAlgebraic` is elaborated under reduced transparency and is not found by bare
instance search, so we re-expose it as a clean instance here.) -/
instance instIsAlgebraicOm : Algebra.IsAlgebraic ℚ Om := AlgebraicClosure.isAlgebraic ℚ

/-- `Ω = ℚ̄` is integral over `ℚ` (now synthesised from `instIsAlgebraicOm`). -/
instance instIsIntegralOm : Algebra.IsIntegral ℚ Om := Algebra.IsAlgebraic.isIntegral

/-- A chosen primitive `pⁿ`-th root of unity in `Ω = ℚ̄` (exists: `ℚ̄` is algebraically closed). -/
def zeta (n : ℕ) : Om := (HasEnoughRootsOfUnity.exists_primitiveRoot Om (p ^ n)).choose

/-- `zeta p n` is indeed a primitive `pⁿ`-th root of unity. -/
theorem zeta_spec (n : ℕ) : IsPrimitiveRoot (zeta p n) (p ^ n) :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot Om (p ^ n)).choose_spec

/-- `Fₙ = ℚ(μ_{pⁿ})`, realised as the `IntermediateField` of `Ω` generated by `zeta p n`. -/
def F (n : ℕ) : IntermediateField ℚ Om := IntermediateField.adjoin ℚ {zeta p n}

/-- Each nested layer `Fₙ` is a cyclotomic extension — so all finite-level API applies to it. -/
instance instIsCyclotomicF (n : ℕ) : IsCyclotomicExtension {p ^ n} ℚ (F p n) :=
  (zeta_spec p n).intermediateField_adjoin_isCyclotomicExtension (K := ℚ)

/-- The tower is increasing: `Fₙ ⊆ Fₙ₊₁`. (`ζₙ` is a `pⁿ⁺¹`-th root of unity, hence a power of the
primitive `ζₙ₊₁`, hence lies in `Fₙ₊₁`.) -/
theorem F_mono (n : ℕ) : F p n ≤ F p (n + 1) := by
  have hpow : zeta p n ^ p ^ (n + 1) = 1 := by
    rw [pow_succ, pow_mul, (zeta_spec p n).pow_eq_one, one_pow]
  obtain ⟨i, -, hi⟩ := (zeta_spec p (n + 1)).eq_pow_of_pow_eq_one hpow
  rw [F, F, IntermediateField.adjoin_simple_le_iff, ← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

/-- The tower is monotone in the order `≤` on `ℕ`. -/
theorem F_monotone : Monotone (F p) :=
  monotone_nat_of_le_succ (F_mono p)

/-- `F∞ = ⋃ₙ Fₙ`, the cyclotomic `ℤ_p`-extension of `ℚ`, as an `IntermediateField` of `Ω`. -/
def Finf : IntermediateField ℚ Om := ⨆ n, F p n

/-- Every layer embeds in `F∞`. -/
theorem F_le_Finf (n : ℕ) : F p n ≤ Finf p := le_iSup (F p) n

/-! ### Brick 4 — the Galois group `Γ = Gal(F∞/ℚ)` of the cyclotomic tower

`F∞/ℚ` is Galois: it is the compositum `⨆ₙ Fₙ` of the Galois layers `Fₙ` (`normal_iSup`), and is
separable since `ℚ` is perfect. The Galois group `Γ` then carries the profinite Krull topology
(`IsGalois` + `FieldTheory/Galois/Infinite`). Abstractly `Γ ≅ ℤ_p^×`; that identification, and the
`ℤ_p`-quotient `Γ⁺ = Gal(F∞⁺/ℚ)`, are the next bricks. -/

/-- Each layer `Fₙ/ℚ` is Galois (cyclotomic extension). -/
instance instIsGaloisF (n : ℕ) : IsGalois ℚ (F p n) :=
  IsCyclotomicExtension.isGalois {p ^ n} ℚ (F p n)

/-- Each layer `Fₙ/ℚ` is normal (direct indexed instance, so the `⨆`-normality below synthesises). -/
instance instNormalF (n : ℕ) : Normal ℚ (F p n) := inferInstance

/-- `F∞` is algebraic over `ℚ` (it sits inside the algebraic `Ω`). -/
instance instIsAlgebraicFinf : Algebra.IsAlgebraic ℚ (Finf p) :=
  Algebra.IsAlgebraic.tower_bot ℚ (Finf p) Om

/-- `F∞/ℚ` is normal — a compositum of the normal layers `Fₙ`. -/
instance instNormalFinf : Normal ℚ (Finf p) := by
  rw [Finf]
  exact IntermediateField.normal_iSup (t := fun n => F p n) (h := fun i => instNormalF p i)

/-- `F∞/ℚ` is Galois (normal + separable, the latter since `ℚ` is perfect). -/
instance instIsGaloisFinf : IsGalois ℚ (Finf p) := ⟨⟩

/-- `Γ = Gal(F∞/ℚ)`, the Galois group of the cyclotomic `ℤ_p`-tower. Via `IsGalois` it carries the
profinite (Krull) topology. A genuine group of field automorphisms — no placeholder. -/
abbrev Gamma : Type := Finf p ≃ₐ[ℚ] Finf p

/-! ### Brick 4b — the maximal real tower `F∞⁺ = ⋃ₙ Fₙ⁺` and `Γ⁺ = Gal(F∞⁺/ℚ)`

`Fₙ⁺ = ℚ(ζₙ + ζₙ⁻¹)` is the maximal totally real subfield of `Fₙ` (RJW §13.2). We realise it as a
nested `IntermediateField` of `Ω`, generated by the real element `ηₙ = ζₙ + ζₙ⁻¹`. Monotonicity of
the real tower rests on the power-sum fact `ξᵐ + ξ⁻ᵐ ∈ ℚ(ξ + ξ⁻¹)` (a Chebyshev recurrence). -/

/-- Power-sum lemma: for `ξ ≠ 0`, every `ξᵐ + ξ⁻ᵐ` lies in `ℚ(ξ + ξ⁻¹)`. This is what makes
`ℚ(ξ + ξ⁻¹)` the maximal real subfield closed under the tower maps. -/
theorem powSum_mem_adjoin {ξ : Om} (hξ : ξ ≠ 0) (m : ℕ) :
    ξ ^ m + ξ⁻¹ ^ m ∈ IntermediateField.adjoin ℚ ({ξ + ξ⁻¹} : Set Om) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [pow_zero]; exact add_mem (one_mem _) (one_mem _)
  | one => simp only [pow_one]; exact IntermediateField.mem_adjoin_simple_self ℚ _
  | more k ih1 ih2 =>
    have h1 : ξ * ξ⁻¹ = 1 := mul_inv_cancel₀ hξ
    have key : ξ ^ (k + 2) + ξ⁻¹ ^ (k + 2)
        = (ξ + ξ⁻¹) * (ξ ^ (k + 1) + ξ⁻¹ ^ (k + 1)) - (ξ ^ k + ξ⁻¹ ^ k) := by
      linear_combination (-(ξ ^ k + ξ⁻¹ ^ k)) * h1
    rw [key]
    exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih2) ih1

/-- `ζₙ ≠ 0` (it is a root of unity). -/
theorem zeta_ne_zero (n : ℕ) : zeta p n ≠ 0 := (zeta_spec p n).ne_zero (instNeZeroPow p n).ne

/-- `Fₙ⁺ = ℚ(ζₙ + ζₙ⁻¹)`, the maximal real subfield of `Fₙ`, as a nested `IntermediateField` of `Ω`. -/
def FPlus (n : ℕ) : IntermediateField ℚ Om :=
  IntermediateField.adjoin ℚ {zeta p n + (zeta p n)⁻¹}

/-- The real subfield sits inside the full layer: `Fₙ⁺ ≤ Fₙ`. -/
theorem FPlus_le_F (n : ℕ) : FPlus p n ≤ F p n := by
  rw [FPlus, F, IntermediateField.adjoin_simple_le_iff]
  exact add_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
    (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ _))

/-- The real tower is increasing: `Fₙ⁺ ⊆ Fₙ₊₁⁺`. (`ζₙ = ζₙ₊₁ᵏ`, and `ζₙ₊₁ᵏ + ζₙ₊₁⁻ᵏ ∈ ℚ(ζₙ₊₁+ζₙ₊₁⁻¹)`
by the power-sum lemma.) -/
theorem FPlus_mono (n : ℕ) : FPlus p n ≤ FPlus p (n + 1) := by
  have hpow : zeta p n ^ p ^ (n + 1) = 1 := by
    rw [pow_succ, pow_mul, (zeta_spec p n).pow_eq_one, one_pow]
  obtain ⟨k, -, hk⟩ := (zeta_spec p (n + 1)).eq_pow_of_pow_eq_one hpow
  rw [FPlus, FPlus, IntermediateField.adjoin_simple_le_iff, ← hk]
  have hne : zeta p (n + 1) ≠ 0 := zeta_ne_zero p (n + 1)
  rw [← inv_pow]
  exact powSum_mem_adjoin hne k

/-- `F∞⁺ = ⋃ₙ Fₙ⁺`, the cyclotomic `ℤ_p`-extension of the maximal real field — the field over which
the Iwasawa Main Conjecture (RJW Thm 13.11) is stated. -/
def FinfPlus : IntermediateField ℚ Om := ⨆ n, FPlus p n

/-- `Γ⁺ = Gal(F∞⁺/ℚ)`, abstractly `≅ ℤ_p` — the Iwasawa group of RJW §13.2 / Thm 13.11. A genuine
group of field automorphisms. -/
abbrev GammaPlus : Type := FinfPlus p ≃ₐ[ℚ] FinfPlus p

/-! ### Brick 5 — toward `X⁺_∞`: number-field structure and the absolute Galois groups

`X⁺_∞ = Gal(M⁺_∞/F⁺_∞)`, where `M⁺_∞` is the maximal abelian pro-`p` extension of `F∞⁺` unramified
outside `p` (RJW §13.2). The faithful route (chosen): build `M⁺_∞` through its **finite layers**, each
finite over a **number field** `Fₙ⁺` — where mathlib's finite-extension ramification (`IsUnramifiedAt`,
rings of integers, `LiesOver`) applies — then take the compositum inside `Ω` and `X⁺_∞ = Gal`. This
brick lays the two prerequisites: (i) `Fₙ`, `Fₙ⁺` are genuinely number fields (finite over `ℚ`), so
they have rings of integers and primes; (ii) the absolute Galois groups, the ambient for `M⁺_∞ ⊆ Ω`. -/

/-- `Fₙ = ℚ(μ_{pⁿ})` is finite-dimensional over `ℚ` (cyclotomic). -/
instance instFiniteDimensionalF (n : ℕ) : FiniteDimensional ℚ (F p n) :=
  IsCyclotomicExtension.finiteDimensional {p ^ n} ℚ (F p n)

/-- `Fₙ` is a number field — so it has a ring of integers `𝓞_{Fₙ}` and primes. -/
instance instNumberFieldF (n : ℕ) : NumberField (F p n) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalF p n

/-- `Fₙ⁺ = ℚ(ζₙ+ζₙ⁻¹)` is finite-dimensional over `ℚ` (a single algebraic generator). -/
instance instFiniteDimensionalFPlus (n : ℕ) : FiniteDimensional ℚ (FPlus p n) := by
  rw [FPlus]
  exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

/-- `Fₙ⁺` is a number field — so it has a ring of integers `𝓞_{Fₙ⁺}` and primes. -/
instance instNumberFieldFPlus (n : ℕ) : NumberField (FPlus p n) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalFPlus p n

/-- The absolute Galois group `G_{Fₙ⁺} = Gal(ℚ̄/Fₙ⁺)` (`Ω` is an algebraic closure of `Fₙ⁺`).
`Mₙ⁺` will be cut out inside `Ω` as a subextension fixed by an appropriate closed subgroup. -/
abbrev AbsGalFPlus (n : ℕ) : Type := Om ≃ₐ[FPlus p n] Om

/-- The absolute Galois group `G_{F∞⁺} = Gal(ℚ̄/F∞⁺)`. `X⁺_∞` is a quotient of (the abelianisation
of) this group; `M⁺_∞ ⊆ Ω` is the corresponding fixed field. -/
abbrev AbsGalFinfPlus : Type := Om ≃ₐ[FinfPlus p] Om

/-! ### Brick 6 — the maximal extensions `M⁺ₙ`, `L⁺ₙ` and the Galois modules `X⁺_∞`, `Y⁺_∞`

**Verbatim from RJW §13.2** (the protagonists of the Galois side of the Main Conjecture):
* `M⁺ₙ` = maximal abelian `p`-extension of `F⁺ₙ` unramified outside `p⁺ₙ`,
* `L⁺ₙ` = maximal unramified abelian `p`-extension of `F⁺ₙ`,
* `M⁺_∞ = ⋃ₙ M⁺ₙ`, `L⁺_∞ = ⋃ₙ L⁺ₙ`,
* `X⁺_∞ = Gal(M⁺_∞/F⁺_∞)`, `Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)`.

Each maximal extension is realised as the compositum (`⨆`) inside `Ω` of its **finite** abelian
`p`-power layers carrying the required ramification — so the ramification condition is checked on
finite extensions of the number field `F⁺ₙ`, where mathlib's `IsUnramifiedAt` and
`FltRegular.NumberTheory.Unramified` apply. Since `p⁺ₙ` is the unique prime of `F⁺ₙ` above `p`,
"unramified outside `p⁺ₙ`" means: unramified at every prime `P` of `𝓞_L` with residue characteristic
`≠ p`, i.e. `p ∉ P`. This is the genuine construction — no `Type*` stand-in, no bundled isomorphism. -/

open NumberField in
/-- A finite layer `L` over the number field `F⁺ₙ` is itself a number field (tower `ℚ → F⁺ₙ → L`),
so it has a ring of integers `𝓞_L` and primes. -/
theorem numberField_of_finite_layer (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    [FiniteDimensional (FPlus p n) L] : NumberField L := by
  haveI : FiniteDimensional ℚ (FPlus p n) := instFiniteDimensionalFPlus p n
  haveI : FiniteDimensional ℚ (L : Type _) := Module.Finite.trans (FPlus p n) (L : Type _)
  exact ⟨⟩

open NumberField in
/-- (RJW §13.2) `L/F⁺ₙ` is **unramified outside `p`**: it is unramified at every prime `P` of `𝓞_L`
whose residue characteristic is `≠ p` (equivalently `p ∉ P`). As `p⁺ₙ` is the unique prime of `F⁺ₙ`
above `p`, this is exactly RJW's "unramified outside `p⁺ₙ`". -/
def IsUnramifiedOutsideP (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    [FiniteDimensional (FPlus p n) L] : Prop :=
  haveI := numberField_of_finite_layer p n L
  ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (p : 𝓞 L) ∉ P → Algebra.IsUnramifiedAt (𝓞 (FPlus p n)) P

/-- A finite **abelian `p`-power** layer over `F⁺ₙ` that is **unramified outside `p`** — the building
block of `M⁺ₙ`. A genuine predicate (not a bundled hypothesis): finiteness, Galois, commutative Galois
group, `p`-power degree, and the ramification condition above. -/
def IsAdmissibleM (n : ℕ) (L : IntermediateField (FPlus p n) Om) : Prop :=
  ∃ h : FiniteDimensional (FPlus p n) L,
    IsGalois (FPlus p n) L ∧
    (∀ σ τ : L ≃ₐ[FPlus p n] L, σ * τ = τ * σ) ∧
    (∃ k : ℕ, Module.finrank (FPlus p n) L = p ^ k) ∧
    @IsUnramifiedOutsideP p _ n L h

/-- `M⁺ₙ` = maximal abelian `p`-extension of `F⁺ₙ` unramified outside `p⁺ₙ` (RJW §13.2), realised as
the compositum inside `Ω` of all its finite admissible layers. A genuine field, not a stand-in. -/
def MPlusN (n : ℕ) : IntermediateField (FPlus p n) Om :=
  ⨆ (L : IntermediateField (FPlus p n) Om) (_ : IsAdmissibleM p n L), L

/-- A finite abelian `p`-power layer over `F⁺ₙ` that is **unramified everywhere** — the building
block of `L⁺ₙ` (the `p`-Hilbert class field tower). -/
def IsAdmissibleL (n : ℕ) (L : IntermediateField (FPlus p n) Om) : Prop :=
  ∃ _ : FiniteDimensional (FPlus p n) L,
    IsGalois (FPlus p n) L ∧
    (∀ σ τ : L ≃ₐ[FPlus p n] L, σ * τ = τ * σ) ∧
    (∃ k : ℕ, Module.finrank (FPlus p n) L = p ^ k) ∧
    Algebra.Unramified (NumberField.RingOfIntegers (FPlus p n)) (NumberField.RingOfIntegers L)

/-- `L⁺ₙ` = maximal unramified abelian `p`-extension of `F⁺ₙ` (RJW §13.2; the `p`-Hilbert class
field of `F⁺ₙ`), as the compositum inside `Ω` of its finite admissible layers. -/
def LPlusN (n : ℕ) : IntermediateField (FPlus p n) Om :=
  ⨆ (L : IntermediateField (FPlus p n) Om) (_ : IsAdmissibleL p n L), L

/-- `M⁺_∞ = ⋃ₙ M⁺ₙ` (RJW §13.2): the maximal abelian pro-`p` extension of `F⁺_∞` unramified outside
`p`, realised as the `F⁺_∞`-compositum inside `Ω` of the finite-level `M⁺ₙ`. An `IntermediateField`
over `F⁺_∞`, so its relative Galois group is immediate. -/
def MinfPlus : IntermediateField (FinfPlus p) Om :=
  IntermediateField.adjoin (FinfPlus p) (⋃ n, (↑(MPlusN p n) : Set Om))

/-- `L⁺_∞ = ⋃ₙ L⁺ₙ` (RJW §13.2): the maximal unramified abelian pro-`p` extension of `F⁺_∞`. -/
def LinfPlus : IntermediateField (FinfPlus p) Om :=
  IntermediateField.adjoin (FinfPlus p) (⋃ n, (↑(LPlusN p n) : Set Om))

/-- `X⁺_∞ = Gal(M⁺_∞/F⁺_∞)` (RJW §13.2) — **the central Galois module of the Iwasawa Main Conjecture**
(Thm 13.11: `X⁺_∞ ≅ Λ(Γ⁺)/I(Γ⁺)ζp`). A genuine relative Galois group of the constructed fields, which
carries the `Λ(Γ⁺)`-action of Remark 13.7. No `Type*` stand-in, no bundled isomorphism. -/
abbrev XinfPlus : Type := MinfPlus p ≃ₐ[FinfPlus p] MinfPlus p

/-- `Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)` (RJW §13.2); classically `≅ lim Cl(F⁺ₙ)⊗ℤp`, and `= 0` for a Vandiver
prime (Cor 13.16(i)). A genuine relative Galois group. -/
abbrev YinfPlus : Type := LinfPlus p ≃ₐ[FinfPlus p] LinfPlus p

/-! #### `L⁺ ⊆ M⁺` — the containment underlying the Galois SES `0→Gal(M⁺_∞/L⁺_∞)→X⁺_∞→Y⁺_∞→0`

An unramified-everywhere layer is in particular unramified outside `p`, so every admissible-`L` layer
is an admissible-`M` layer (reusing mathlib's `Algebra.formallyUnramified_iff_forall`: global
unramified ⟺ unramified at every prime). Hence `L⁺ₙ ⊆ M⁺ₙ` and `L⁺_∞ ⊆ M⁺_∞`. -/

open NumberField in
/-- Unramified everywhere ⟹ unramified outside `p`: every `L⁺`-layer is an `M⁺`-layer. -/
theorem isAdmissibleM_of_isAdmissibleL (n : ℕ) (L : IntermediateField (FPlus p n) Om)
    (hL : IsAdmissibleL p n L) : IsAdmissibleM p n L := by
  obtain ⟨hfin, hgal, hab, hpp, hunr⟩ := hL
  refine ⟨hfin, hgal, hab, hpp, ?_⟩
  intro P _ _
  haveI := numberField_of_finite_layer p n L
  haveI : Algebra.FormallyUnramified (𝓞 (FPlus p n)) (𝓞 L) := hunr.formallyUnramified
  exact Algebra.formallyUnramified_iff_forall.mp ‹_› ⟨P, ‹_›⟩

/-- `L⁺ₙ ⊆ M⁺ₙ`. -/
theorem LPlusN_le_MPlusN (n : ℕ) : LPlusN p n ≤ MPlusN p n :=
  iSup₂_le fun L hL => le_iSup₂_of_le L (isAdmissibleM_of_isAdmissibleL p n L hL) le_rfl

/-- `L⁺_∞ ⊆ M⁺_∞`. -/
theorem LinfPlus_le_MinfPlus : LinfPlus p ≤ MinfPlus p := by
  rw [LinfPlus, MinfPlus, IntermediateField.adjoin_le_iff]
  refine Set.iUnion_subset fun n => (SetLike.coe_subset_coe.mpr (LPlusN_le_MPlusN p n)).trans ?_
  exact (Set.subset_iUnion (fun n => (↑(MPlusN p n) : Set Om)) n).trans
    (IntermediateField.subset_adjoin _ _)

/-! #### `Mₙ⁺/Fₙ⁺` and `M∞⁺/F∞⁺` are abelian — toward the `Λ(Γ⁺)`-action and the SES

Each admissible layer is abelian Galois (the `IsAdmissibleM` predicate's fields), so the compositum
`Mₙ⁺` is abelian by `isMulCommutative_iSup`. -/

/-- An admissible layer is an abelian Galois extension of `Fₙ⁺`. -/
theorem isAbelianGalois_of_isAdmissibleM {n : ℕ} {L : IntermediateField (FPlus p n) Om}
    (h : IsAdmissibleM p n L) : IsAbelianGalois (FPlus p n) L :=
  haveI : IsGalois (FPlus p n) L := h.2.1
  haveI : IsMulCommutative (L ≃ₐ[FPlus p n] L) := ⟨⟨h.2.2.1⟩⟩
  ⟨⟩

/-- The `IsAdmissibleM`-collapsed layer `⨆ (_ : IsAdmissibleM L), L` (which is `L` or `⊥`) is always
abelian Galois — so the keystone `isMulCommutative_iSup` applies to `M⁺ₙ = ⨆ L, ⨆ (_:adm), L`. -/
instance isAbelianGalois_admissibleSummand (n : ℕ) (L : IntermediateField (FPlus p n) Om) :
    IsAbelianGalois (FPlus p n) ↥(⨆ _ : IsAdmissibleM p n L, L) := by
  by_cases h : IsAdmissibleM p n L
  · rw [iSup_pos h]; exact isAbelianGalois_of_isAdmissibleM p h
  · rw [iSup_neg h]; infer_instance

/-- `Gal(Mₙ⁺/Fₙ⁺)` is commutative (compositum of abelian layers). -/
theorem isMulCommutative_galMPlusN (n : ℕ) :
    IsMulCommutative (↥(MPlusN p n) ≃ₐ[FPlus p n] ↥(MPlusN p n)) :=
  isMulCommutative_iSup (fun L : IntermediateField (FPlus p n) Om => ⨆ _ : IsAdmissibleM p n L, L)

/-- An admissible-`L` layer is an abelian Galois extension of `Fₙ⁺`. -/
theorem isAbelianGalois_of_isAdmissibleL {n : ℕ} {L : IntermediateField (FPlus p n) Om}
    (h : IsAdmissibleL p n L) : IsAbelianGalois (FPlus p n) L :=
  haveI : IsGalois (FPlus p n) L := h.2.1
  haveI : IsMulCommutative (L ≃ₐ[FPlus p n] L) := ⟨⟨h.2.2.1⟩⟩
  ⟨⟩

instance isAbelianGalois_admissibleLSummand (n : ℕ) (L : IntermediateField (FPlus p n) Om) :
    IsAbelianGalois (FPlus p n) ↥(⨆ _ : IsAdmissibleL p n L, L) := by
  by_cases h : IsAdmissibleL p n L
  · rw [iSup_pos h]; exact isAbelianGalois_of_isAdmissibleL p h
  · rw [iSup_neg h]; infer_instance

/-- `Gal(Lₙ⁺/Fₙ⁺)` is commutative (compositum of unramified abelian layers). -/
theorem isMulCommutative_galLPlusN (n : ℕ) :
    IsMulCommutative (↥(LPlusN p n) ≃ₐ[FPlus p n] ↥(LPlusN p n)) :=
  isMulCommutative_iSup (fun L : IntermediateField (FPlus p n) Om => ⨆ _ : IsAdmissibleL p n L, L)

/-- `Mₙ⁺/Fₙ⁺` is normal (compositum of normal admissible layers). -/
instance instNormalMPlusN (n : ℕ) : Normal (FPlus p n) (MPlusN p n) := by
  rw [MPlusN]
  refine IntermediateField.normal_iSup (t := fun L => ⨆ _ : IsAdmissibleM p n L, L) (h := fun L => ?_)
  by_cases h : IsAdmissibleM p n L
  · rw [iSup_pos h]; haveI := isAbelianGalois_of_isAdmissibleM p h; infer_instance
  · rw [iSup_neg h]; infer_instance

/-- `Mₙ⁺/Fₙ⁺` is Galois (normal + separable). -/
instance instIsGaloisMPlusN (n : ℕ) : IsGalois (FPlus p n) (MPlusN p n) := ⟨⟩

/-- `Mₙ⁺/Fₙ⁺` is abelian Galois. -/
instance instIsAbelianGaloisMPlusN (n : ℕ) : IsAbelianGalois (FPlus p n) (MPlusN p n) :=
  haveI := isMulCommutative_galMPlusN p n; ⟨⟩

/-- `Mₙ⁺`, viewed as an `Fₙ⁺`-subfield of `M∞⁺` (via `comap`), is abelian Galois over `Fₙ⁺`. The
algebra/tower instances are explicit hypotheses so this elaborates in a clean context (no `letI`
interference) — the key to making `of_algHom` fast. -/
lemma isAbelianGalois_comap_MPlusN (n : ℕ) [Algebra ↥(FPlus p n) ↥(FinfPlus p)]
    [Algebra ↥(FPlus p n) ↥(MinfPlus p)] [IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om]
    [IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) ↥(MinfPlus p)] :
    IsAbelianGalois (FPlus p n)
      ↥(IntermediateField.comap ((MinfPlus p).val.restrictScalars ↥(FPlus p n)) (MPlusN p n)) := by
  let fEh : ↥(IntermediateField.comap ((MinfPlus p).val.restrictScalars ↥(FPlus p n)) (MPlusN p n))
      →ₐ[FPlus p n] ↥(MPlusN p n) :=
    AlgHom.codRestrict (((MinfPlus p).val.restrictScalars ↥(FPlus p n)).comp
      (IntermediateField.comap ((MinfPlus p).val.restrictScalars ↥(FPlus p n)) (MPlusN p n)).val)
      (MPlusN p n).toSubalgebra (fun w => w.2)
  exact IsAbelianGalois.of_algHom fEh

/-- **Base case for `X⁺_∞` abelian**: two `Gal(M∞⁺/F∞⁺)`-automorphisms commute on any point of `M∞⁺`
coming from a finite layer `Mₙ⁺`. Restrict to `Fₙ⁺` (where `Mₙ⁺` is abelian) via `commute_restrict_AG`
applied to `E = Mₙ⁺`-viewed-in-`M∞⁺`. All instances passed explicitly (no slow synthesis). -/
theorem commute_on_MPlusN (n : ℕ) (σ τ : MinfPlus p ≃ₐ[FinfPlus p] MinfPlus p)
    (z : ↥(MinfPlus p)) (hz : (z : Om) ∈ MPlusN p n) : σ (τ z) = τ (σ z) := by
  have hle : FPlus p n ≤ FinfPlus p := by rw [FinfPlus]; exact le_iSup (FPlus p) n
  letI : Algebra ↥(FPlus p n) ↥(FinfPlus p) := (IntermediateField.inclusion hle).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥(FPlus p n) ↥(MinfPlus p) :=
    ((algebraMap ↥(FinfPlus p) ↥(MinfPlus p)).comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) ↥(MinfPlus p) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact @commute_restrict_AG ↥(FPlus p n) ↥(FinfPlus p) ↥(MinfPlus p) _ _ _ _ _ _ _
    (IntermediateField.comap ((MinfPlus p).val.restrictScalars ↥(FPlus p n)) (MPlusN p n))
    (isAbelianGalois_comap_MPlusN p n) σ τ ⟨z, hz⟩

open IntermediateField in
/-- **`X⁺_∞ = Gal(M⁺_∞/F⁺_∞)` is abelian** (Remark 13.7 / RJW §13.2): `M⁺_∞` is generated over `F⁺_∞`
by the finite layers `M⁺ₙ`, each abelian over `F⁺ₙ`, so any two automorphisms commute on the
generators (`commute_on_MPlusN`) and hence everywhere (`adjoin_induction`). This is the prerequisite
for the `Λ(Γ⁺)`-module structure in which Thm 13.11 is stated. -/
instance isMulCommutative_XinfPlus : IsMulCommutative (XinfPlus p) := by
  rw [isMulCommutative_iff]; intro σ τ
  refine AlgEquiv.ext fun y => ?_
  set Sgen : Set ↥(MinfPlus p) := ⋃ n, ((MinfPlus p).val ⁻¹' (MPlusN p n)) with hS
  have himg : (MinfPlus p).val '' Sgen = ⋃ n, (MPlusN p n : Set Om) := by
    rw [hS, Set.image_iUnion]
    refine Set.iUnion_congr fun n => ?_
    rw [Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr (fun x hx =>
      ⟨⟨x, by rw [MinfPlus]; exact subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, hx⟩)⟩, rfl⟩)
  have htop : adjoin (FinfPlus p) Sgen = ⊤ := by
    apply IntermediateField.map_injective (MinfPlus p).val
    rw [IntermediateField.adjoin_map, himg]
    apply SetLike.coe_injective
    rw [IntermediateField.coe_map, IntermediateField.coe_top, Set.image_univ,
      IntermediateField.coe_val, Subtype.range_coe_subtype]
    rfl
  have hy : y ∈ adjoin (FinfPlus p) Sgen := htop ▸ mem_top
  induction hy using IntermediateField.adjoin_induction with
  | mem w hw =>
    obtain ⟨n, hwn⟩ := Set.mem_iUnion.mp hw
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact commute_on_MPlusN p n σ τ w hwn
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]

/-! #### `Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)` is abelian (TG3) — the same argument over the unramified tower `L⁺` -/

/-- `Lₙ⁺/Fₙ⁺` is normal (compositum of normal admissible-`L` layers). -/
instance instNormalLPlusN (n : ℕ) : Normal (FPlus p n) (LPlusN p n) := by
  rw [LPlusN]
  refine IntermediateField.normal_iSup (t := fun L => ⨆ _ : IsAdmissibleL p n L, L) (h := fun L => ?_)
  by_cases h : IsAdmissibleL p n L
  · rw [iSup_pos h]; haveI := isAbelianGalois_of_isAdmissibleL p h; infer_instance
  · rw [iSup_neg h]; infer_instance

/-- `Lₙ⁺/Fₙ⁺` is Galois. -/
instance instIsGaloisLPlusN (n : ℕ) : IsGalois (FPlus p n) (LPlusN p n) := ⟨⟩

/-- `Lₙ⁺/Fₙ⁺` is abelian Galois. -/
instance instIsAbelianGaloisLPlusN (n : ℕ) : IsAbelianGalois (FPlus p n) (LPlusN p n) :=
  haveI := isMulCommutative_galLPlusN p n; ⟨⟩

/-- `Lₙ⁺`, viewed as an `Fₙ⁺`-subfield of `L∞⁺` (via `comap`), is abelian Galois over `Fₙ⁺`. -/
lemma isAbelianGalois_comap_LPlusN (n : ℕ) [Algebra ↥(FPlus p n) ↥(FinfPlus p)]
    [Algebra ↥(FPlus p n) ↥(LinfPlus p)] [IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om]
    [IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) ↥(LinfPlus p)] :
    IsAbelianGalois (FPlus p n)
      ↥(IntermediateField.comap ((LinfPlus p).val.restrictScalars ↥(FPlus p n)) (LPlusN p n)) := by
  let fEh : ↥(IntermediateField.comap ((LinfPlus p).val.restrictScalars ↥(FPlus p n)) (LPlusN p n))
      →ₐ[FPlus p n] ↥(LPlusN p n) :=
    AlgHom.codRestrict (((LinfPlus p).val.restrictScalars ↥(FPlus p n)).comp
      (IntermediateField.comap ((LinfPlus p).val.restrictScalars ↥(FPlus p n)) (LPlusN p n)).val)
      (LPlusN p n).toSubalgebra (fun w => w.2)
  exact IsAbelianGalois.of_algHom fEh

/-- **Base case for `Y⁺_∞` abelian**: two `Gal(L∞⁺/F∞⁺)`-automorphisms commute on any point coming
from a finite layer `Lₙ⁺` (restrict to `Fₙ⁺`, where `Lₙ⁺` is abelian). -/
theorem commute_on_LPlusN (n : ℕ) (σ τ : LinfPlus p ≃ₐ[FinfPlus p] LinfPlus p)
    (z : ↥(LinfPlus p)) (hz : (z : Om) ∈ LPlusN p n) : σ (τ z) = τ (σ z) := by
  have hle : FPlus p n ≤ FinfPlus p := by rw [FinfPlus]; exact le_iSup (FPlus p) n
  letI : Algebra ↥(FPlus p n) ↥(FinfPlus p) := (IntermediateField.inclusion hle).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ↥(FPlus p n) ↥(LinfPlus p) :=
    ((algebraMap ↥(FinfPlus p) ↥(LinfPlus p)).comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) ↥(LinfPlus p) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact @commute_restrict_AG ↥(FPlus p n) ↥(FinfPlus p) ↥(LinfPlus p) _ _ _ _ _ _ _
    (IntermediateField.comap ((LinfPlus p).val.restrictScalars ↥(FPlus p n)) (LPlusN p n))
    (isAbelianGalois_comap_LPlusN p n) σ τ ⟨z, hz⟩

open IntermediateField in
/-- **`Y⁺_∞ = Gal(L⁺_∞/F⁺_∞)` is abelian** (TG3): `L⁺_∞` is generated over `F⁺_∞` by the finite
abelian layers `L⁺ₙ`, so any two automorphisms commute on generators and hence everywhere. -/
instance isMulCommutative_YinfPlus : IsMulCommutative (YinfPlus p) := by
  rw [isMulCommutative_iff]; intro σ τ
  refine AlgEquiv.ext fun y => ?_
  set Sgen : Set ↥(LinfPlus p) := ⋃ n, ((LinfPlus p).val ⁻¹' (LPlusN p n)) with hS
  have himg : (LinfPlus p).val '' Sgen = ⋃ n, (LPlusN p n : Set Om) := by
    rw [hS, Set.image_iUnion]
    refine Set.iUnion_congr fun n => ?_
    rw [Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_left.mpr (fun x hx =>
      ⟨⟨x, by rw [LinfPlus]; exact subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, hx⟩)⟩, rfl⟩)
  have htop : adjoin (FinfPlus p) Sgen = ⊤ := by
    apply IntermediateField.map_injective (LinfPlus p).val
    rw [IntermediateField.adjoin_map, himg]
    apply SetLike.coe_injective
    rw [IntermediateField.coe_map, IntermediateField.coe_top, Set.image_univ,
      IntermediateField.coe_val, Subtype.range_coe_subtype]
    rfl
  have hy : y ∈ adjoin (FinfPlus p) Sgen := htop ▸ mem_top
  induction hy using IntermediateField.adjoin_induction with
  | mem w hw =>
    obtain ⟨n, hwn⟩ := Set.mem_iUnion.mp hw
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact commute_on_LPlusN p n σ τ w hwn
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]

/-! ### Toward the `Γ⁺`-action (Remark 13.7): `F⁺_∞/ℚ` is Galois

`Γ⁺ = Gal(F∞⁺/ℚ)` acts on `X∞⁺` by `σ·x = σ̃xσ̃⁻¹` (conjugation by a lift `σ̃ ∈ Gal(M∞⁺/ℚ)`). The first
ingredient is that `F∞⁺/ℚ` is normal, so `X∞⁺ = ker(Gal(M∞⁺/ℚ) ↠ Γ⁺)` is a normal subgroup. -/

/-- `Gal(Fₙ/ℚ) ≅ (ℤ/pⁿ)ˣ` is commutative. -/
theorem isMulCommutative_galF (n : ℕ) : IsMulCommutative (F p n ≃ₐ[ℚ] F p n) := by
  have e : (F p n ≃ₐ[ℚ] F p n) ≃* (ZMod (p ^ n))ˣ :=
    IsCyclotomicExtension.autEquivPow (F p n) (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _))
  exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

/-- `Fₙ⁺/ℚ` is normal (an intermediate field of the abelian Galois extension `Fₙ/ℚ`). -/
theorem normal_FPlus (n : ℕ) : Normal ℚ (FPlus p n) := by
  haveI := isMulCommutative_galF p n
  set L : IntermediateField ℚ ↥(F p n) := IntermediateField.comap (F p n).val (FPlus p n)
  haveI : L.fixingSubgroup.Normal := ⟨fun a ha g => by
    rw [isMulCommutative_iff.mp (isMulCommutative_galF p n) g a, mul_inv_cancel_right]; exact ha⟩
  haveI : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp inferInstance
  let fh : ↥L →ₐ[ℚ] ↥(FPlus p n) :=
    AlgHom.codRestrict ((F p n).val.comp L.val) (FPlus p n).toSubalgebra (fun w => w.2)
  have hinj : Function.Injective fh := fun a b hab => by
    apply Subtype.ext; apply Subtype.ext; exact congrArg (fun w : ↥(FPlus p n) => (w : Om)) hab
  have hsurj : Function.Surjective fh := fun m =>
    ⟨⟨⟨m.1, FPlus_le_F p n m.2⟩, m.2⟩, Subtype.ext rfl⟩
  exact Normal.of_algEquiv (AlgEquiv.ofBijective fh ⟨hinj, hsurj⟩)

/-- `F∞⁺/ℚ` is normal (compositum of the normal layers `Fₙ⁺`). -/
theorem normal_FinfPlus : Normal ℚ (FinfPlus p) := by
  rw [FinfPlus]
  exact IntermediateField.normal_iSup (t := fun n => FPlus p n) (h := fun n => normal_FPlus p n)

/-! ### `M⁺_∞/ℚ` is Galois — the prerequisite for the `Γ⁺`-action (Remark 13.7)

`Γ⁺ = Gal(F∞⁺/ℚ)` acts on `X∞⁺ = Gal(M∞⁺/F∞⁺)` (Remark 13.7) via the group extension
`1 → X∞⁺ → Gal(M∞⁺/ℚ) → Γ⁺ → 1`; the surjection onto `Γ⁺` exists because `M∞⁺/ℚ` is normal.
`M∞⁺` is generated over `ℚ` by `F∞⁺` (normal) together with the finite layers `M⁺ₙ`, and each `M⁺ₙ`
is `Gal(Ω/ℚ)`-stable — its defining property (finite abelian `p`-power, unramified outside `p`) is
preserved by every `ℚ`-algebra map of `Ω` — hence normal over `ℚ`. -/

instance instIsAlgClosureOm : IsAlgClosure ℚ Om := ⟨inferInstance, inferInstance⟩

instance instNormalOm : Normal ℚ Om := IsAlgClosure.normal ℚ Om

instance instIsGaloisOm : IsGalois ℚ Om := ⟨⟩

/-- The base `F∞⁺` is contained in `M∞⁺` (as `ℚ`-subfields of `Ω`). -/
theorem FinfPlus_le_MinfPlus_restrict :
    FinfPlus p ≤ (MinfPlus p).restrictScalars ℚ := by
  intro x hx
  rw [IntermediateField.mem_restrictScalars]
  exact (MinfPlus p).algebraMap_mem ⟨x, hx⟩

/-- The base `F⁺ₙ` is contained in `M⁺ₙ` (as `ℚ`-subfields of `Ω`). -/
theorem FPlus_le_MPlusN_restrict (n : ℕ) :
    FPlus p n ≤ (MPlusN p n).restrictScalars ℚ := by
  intro x hx
  rw [IntermediateField.mem_restrictScalars]
  exact (MPlusN p n).algebraMap_mem ⟨x, hx⟩

/-- Each finite layer `M⁺ₙ` is contained in `M∞⁺` (as `ℚ`-subfields of `Ω`). -/
theorem MPlusN_le_MinfPlus_restrict (n : ℕ) :
    (MPlusN p n).restrictScalars ℚ ≤ (MinfPlus p).restrictScalars ℚ := by
  intro x hx
  rw [IntermediateField.mem_restrictScalars] at hx ⊢
  rw [MinfPlus]
  exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, hx⟩)

/-- A `ℚ`-restricted compositum of `F⁺ₙ`-intermediate fields is `≤ X` as soon as `X` contains the
base `F⁺ₙ` and each `ℚ`-restricted piece. (Replaces the missing `restrictScalars_iSup` for the one
direction we need.) -/
theorem restrictScalars_iSup_le {n : ℕ} {ι : Sort*} (f : ι → IntermediateField (FPlus p n) Om)
    {X : IntermediateField ℚ Om} (hbase : FPlus p n ≤ X)
    (hf : ∀ i, (f i).restrictScalars ℚ ≤ X) : (⨆ i, f i).restrictScalars ℚ ≤ X := by
  rw [IntermediateField.iSup_eq_adjoin]
  rw [show ((IntermediateField.adjoin (↑(FPlus p n)) (⋃ i, (↑(f i) : Set Om))).restrictScalars ℚ)
        = IntermediateField.adjoin ℚ ((↑(FPlus p n) : Set Om) ∪ ⋃ i, ↑(f i))
      from IntermediateField.restrictScalars_adjoin ℚ (FPlus p n) _,
    IntermediateField.adjoin_le_iff]
  rintro x (hxF | hxU)
  · exact hbase hxF
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    exact hf i hi

/-- A `ℚ`-algebra endomorphism of `Ω` is an automorphism (`Ω` is algebraic over `ℚ` and algebraically
closed, so every `ℚ`-algebra map `Ω → Ω` is bijective). -/
noncomputable def omAut (σ : Om →ₐ[ℚ] Om) : Om ≃ₐ[ℚ] Om :=
  AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)

@[simp] theorem omAut_apply (σ : Om →ₐ[ℚ] Om) (x : Om) : omAut σ x = σ x := rfl

/-- The image of an admissible-`M` layer `L` under `σ`, as an `F⁺ₙ`-intermediate field of `Ω`.
Equal (as a set) to `σ(L)`; its `ℚ`-restriction is `map σ (L.restrictScalars ℚ)`. -/
private noncomputable def sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om)
    {L : IntermediateField (FPlus p n) Om}
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    IntermediateField (FPlus p n) Om :=
  IntermediateField.extendScalars hFle

/-- **[a] finrank transport**: `[σ(L) : F⁺ₙ] = [L : F⁺ₙ]`. Proof: the `ℚ`-iso `σ : L ≅ σ(L)` gives
`[L:ℚ] = [σ(L):ℚ]`; divide by `[F⁺ₙ:ℚ]` via the tower formula. -/
theorem finrank_sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    [FiniteDimensional (FPlus p n) L]
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    Module.finrank (FPlus p n) (IntermediateField.extendScalars hFle)
      = Module.finrank (FPlus p n) L := by
  haveI : FiniteDimensional ℚ ↥(FPlus p n) := instFiniteDimensionalFPlus p n
  haveI : FiniteDimensional ℚ ↥L := Module.Finite.trans ↥(FPlus p n) ↥L
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := ↥(FPlus p n)))
  rw [Module.finrank_mul_finrank ℚ ↥(FPlus p n) ↥(IntermediateField.extendScalars hFle),
    Module.finrank_mul_finrank ℚ ↥(FPlus p n) ↥L]
  have e : ↥L ≃ₗ[ℚ] ↥(IntermediateField.extendScalars hFle) :=
    (IntermediateField.intermediateFieldMap (omAut σ) (L.restrictScalars ℚ)).toLinearEquiv
  exact (LinearEquiv.finrank_eq e).symm

/-- **[a'] finiteness transport**: `σ(L)/F⁺ₙ` is finite (the `ℚ`-iso `L ≅ σ(L)` + `L/ℚ` finite). -/
theorem finiteDimensional_sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    [FiniteDimensional (FPlus p n) L]
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    FiniteDimensional (FPlus p n) (IntermediateField.extendScalars hFle) := by
  haveI : FiniteDimensional ℚ ↥(FPlus p n) := instFiniteDimensionalFPlus p n
  haveI : FiniteDimensional ℚ ↥L := Module.Finite.trans ↥(FPlus p n) ↥L
  haveI : FiniteDimensional ℚ ↥(L.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ ↥L)
  haveI : FiniteDimensional ℚ ↥(IntermediateField.extendScalars hFle) :=
    (IntermediateField.intermediateFieldMap (omAut σ) (L.restrictScalars ℚ)).toLinearEquiv.finiteDimensional
  exact Module.Finite.of_restrictScalars_finite ℚ ↥(FPlus p n) ↥(IntermediateField.extendScalars hFle)

/-- A `ℚ`-algebra endomorphism of `Ω` that fixes `F⁺ₙ` pointwise is `F⁺ₙ`-linear — upgrade the scalar
ring (the underlying ring hom is unchanged; only the `commutes'` field is new). -/
def algHomFixingFPlus (n : ℕ) (f : Om →ₐ[ℚ] Om)
    (hf : ∀ c : ↥(FPlus p n), f (c : Om) = (c : Om)) : Om →ₐ[↥(FPlus p n)] Om :=
  { f with commutes' := fun c => hf c }

/-- **[b] Galois transport**: `σ(L)/F⁺ₙ` is Galois. Normality via `normal_iff_forall_map_le`: for an
`F⁺ₙ`-auto `τ` of `Ω`, `σ⁻¹ τ σ` fixes `F⁺ₙ` (`σ(F⁺ₙ)=F⁺ₙ`), so by `Normal F⁺ₙ L` it maps `L` into `L`,
whence `τ` maps `σ(L)` into `σ(L)`. Separability is automatic in char `0`. -/
theorem isGalois_sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    (hL : IsAdmissibleM p n L)
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    IsGalois (FPlus p n) (IntermediateField.extendScalars hFle) := by
  obtain ⟨hfin, hgalL, -, -, -⟩ := id hL
  haveI : FiniteDimensional (FPlus p n) ↥L := hfin
  haveI : IsGalois (FPlus p n) ↥L := hgalL
  haveI : FiniteDimensional (FPlus p n) ↥(IntermediateField.extendScalars hFle) :=
    finiteDimensional_sigmaL p n σ hFle
  have hσF : ∀ c : ↥(FPlus p n), (omAut σ) (c : Om) ∈ FPlus p n := fun c =>
    (IntermediateField.normal_iff_forall_map_le.mp (normal_FPlus p n) (omAut σ).toAlgHom)
      ⟨(c : Om), c.2, rfl⟩
  haveI : Normal (FPlus p n) ↥(IntermediateField.extendScalars hFle) := by
    refine (IntermediateField.normal_iff_forall_map_le).mpr fun τ => ?_
    rw [IntermediateField.map_le_iff_le_comap]
    intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show τ (σ y) ∈ IntermediateField.extendScalars hFle
    rw [IntermediateField.mem_extendScalars, IntermediateField.mem_map]
    have hgfix : ∀ c : ↥(FPlus p n),
        ((omAut σ).symm.toAlgHom.comp ((τ.restrictScalars ℚ).comp (omAut σ).toAlgHom)) (c : Om)
          = (c : Om) := by
      intro c
      have h1 : τ ((omAut σ) (c : Om)) = (omAut σ) (c : Om) := τ.commutes ⟨(omAut σ) (c : Om), hσF c⟩
      show (omAut σ).symm (τ ((omAut σ) (c : Om))) = (c : Om)
      rw [h1, AlgEquiv.symm_apply_apply]
    set g := algHomFixingFPlus p n
      ((omAut σ).symm.toAlgHom.comp ((τ.restrictScalars ℚ).comp (omAut σ).toAlgHom)) hgfix with hg
    have hgL : IntermediateField.map g L ≤ L :=
      IntermediateField.normal_iff_forall_map_le.mp inferInstance g
    refine ⟨g y, hgL ⟨y, hy, rfl⟩, ?_⟩
    show (omAut σ) ((omAut σ).symm (τ ((omAut σ) y))) = τ (σ y)
    rw [AlgEquiv.apply_symm_apply, omAut_apply]
  exact ⟨⟩

/-- **[b] abelian transport**: `Gal(σL/F⁺ₙ)` is commutative (conjugation iso to the abelian
`Gal(L/F⁺ₙ)`). -/
theorem mulComm_sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    (hL : IsAdmissibleM p n L)
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    ∀ φ ψ : IntermediateField.extendScalars hFle ≃ₐ[FPlus p n] IntermediateField.extendScalars hFle,
      φ * ψ = ψ * φ := by
  sorry

/-- **[c] unramified-outside-`p` transport** — the analytic core: `σ` induces a ring automorphism of
`𝓞_Ω` fixing `ℤ`, semilinear over `β = σ|F⁺ₙ : 𝓞_{F⁺ₙ} ≅ 𝓞_{F⁺ₙ}`; it carries primes `P ↦ σ(P)`
preserving residue characteristic and ramification index, and `β` fixes the unique prime over `p`,
so "unramified at every `P` with `p ∉ P`" is preserved. (Needs `RingOfIntegers` functoriality under
a base automorphism + `ramificationIdx` invariance.) -/
theorem isUnramifiedOutsideP_sigmaL (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    (hL : IsAdmissibleM p n L)
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ))
    [FiniteDimensional (FPlus p n) (IntermediateField.extendScalars hFle)] :
    @IsUnramifiedOutsideP p _ n (IntermediateField.extendScalars hFle) ‹_› := by
  sorry

/-- **Admissibility is `σ`-invariant** (the analytic heart of normality): if `L` is an admissible-`M`
layer over `F⁺ₙ` and `σ` is a `ℚ`-algebra map of `Ω` (which fixes `F⁺ₙ` setwise, `F⁺ₙ/ℚ` normal),
then `σ(L)` — viewed as an `F⁺ₙ`-extension via `extendScalars` — is again admissible: the iso `σ|_L`
transports finiteness, the (abelian) Galois structure, the `p`-power degree, and unramifiedness
outside `p`. -/
theorem isAdmissibleM_map (n : ℕ) (σ : Om →ₐ[ℚ] Om) {L : IntermediateField (FPlus p n) Om}
    (hL : IsAdmissibleM p n L)
    (hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ)) :
    IsAdmissibleM p n (IntermediateField.extendScalars hFle) := by
  obtain ⟨hfin, -, -, ⟨k, hk⟩, -⟩ := id hL
  haveI : FiniteDimensional (FPlus p n) L := hfin
  haveI hfd : FiniteDimensional (FPlus p n) (IntermediateField.extendScalars hFle) :=
    finiteDimensional_sigmaL p n σ hFle
  refine ⟨hfd, isGalois_sigmaL p n σ hL hFle, mulComm_sigmaL p n σ hL hFle, ⟨k, ?_⟩,
    isUnramifiedOutsideP_sigmaL p n σ hL hFle⟩
  rw [finrank_sigmaL p n σ hFle]; exact hk

/-- **Admissible-layer transport**: a `ℚ`-algebra map `σ` of `Ω` carries any admissible-`M` layer
over `F⁺ₙ` into `M⁺ₙ` (since `σ(L)` is again admissible, by `isAdmissibleM_map`). -/
theorem map_le_MPlusN_of_isAdmissibleM (n : ℕ) (σ : Om →ₐ[ℚ] Om)
    {L : IntermediateField (FPlus p n) Om} (hL : IsAdmissibleM p n L) :
    IntermediateField.map σ (L.restrictScalars ℚ) ≤ (MPlusN p n).restrictScalars ℚ := by
  have hFL : FPlus p n ≤ (L.restrictScalars ℚ) := by
    intro x hx
    rw [IntermediateField.mem_restrictScalars]
    exact L.algebraMap_mem ⟨x, hx⟩
  have hFle : FPlus p n ≤ IntermediateField.map σ (L.restrictScalars ℚ) :=
    le_of_eq_of_le (IntermediateField.normal_iff_forall_map_eq.mp (normal_FPlus p n) σ).symm
      (IntermediateField.map_mono σ hFL)
  rw [← IntermediateField.extendScalars_restrictScalars hFle]
  refine (IntermediateField.restrictScalars_le_iff ℚ).mpr ?_
  rw [MPlusN]
  exact le_iSup₂_of_le (IntermediateField.extendScalars hFle) (isAdmissibleM_map p n σ hL hFle) le_rfl

/-- Each finite layer `M⁺ₙ`, as a `ℚ`-subfield of `Ω`, is normal over `ℚ` (it is `Gal(Ω/ℚ)`-stable
by `map_le_MPlusN_of_isAdmissibleM`, with the base `F⁺ₙ` absorbed via `normal_FPlus`). -/
theorem normal_MPlusN_restrict (n : ℕ) : Normal ℚ ↥((MPlusN p n).restrictScalars ℚ) := by
  refine (IntermediateField.normal_iff_forall_map_le).mpr fun σ => ?_
  rw [IntermediateField.map_le_iff_le_comap]
  have hbotle : (⊥ : IntermediateField (FPlus p n) Om).restrictScalars ℚ ≤ FPlus p n := by
    intro x hx
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hx
    obtain ⟨y, rfl⟩ := hx
    exact y.2
  have hb : FPlus p n ≤ IntermediateField.comap σ ((MPlusN p n).restrictScalars ℚ) := by
    intro x hx
    show σ x ∈ (MPlusN p n).restrictScalars ℚ
    exact FPlus_le_MPlusN_restrict p n
      ((IntermediateField.normal_iff_forall_map_le.mp (normal_FPlus p n) σ) ⟨x, hx, rfl⟩)
  refine restrictScalars_iSup_le p (fun L => ⨆ _ : IsAdmissibleM p n L, L) hb (fun L => ?_)
  by_cases h : IsAdmissibleM p n L
  · rw [iSup_pos h, ← IntermediateField.map_le_iff_le_comap]
    exact map_le_MPlusN_of_isAdmissibleM p n σ h
  · rw [iSup_neg h]; exact le_trans hbotle hb

/-- **`M⁺_∞/ℚ` is normal.** `M∞⁺` is generated over `ℚ` by `F∞⁺` and the layers `M⁺ₙ`, each
`Gal(Ω/ℚ)`-stable, so `M∞⁺` is too. The prerequisite for the surjection `Gal(M∞⁺/ℚ) ↠ Γ⁺`. -/
theorem normal_MinfPlus : Normal ℚ ↥(MinfPlus p) := by
  have h : Normal ℚ ↥((MinfPlus p).restrictScalars ℚ) := by
    refine (IntermediateField.normal_iff_forall_map_le).mpr fun σ => ?_
    rw [IntermediateField.map_le_iff_le_comap]
    nth_rewrite 1 [MinfPlus]
    rw [show ((IntermediateField.adjoin (↑(FinfPlus p)) (⋃ n, (↑(MPlusN p n) : Set Om))).restrictScalars ℚ)
          = IntermediateField.adjoin ℚ ((↑(FinfPlus p) : Set Om) ∪ ⋃ n, ↑(MPlusN p n))
        from IntermediateField.restrictScalars_adjoin ℚ (FinfPlus p) _,
      IntermediateField.adjoin_le_iff]
    rintro x (hxF | hxM)
    · -- `x ∈ F∞⁺`: `σ x ∈ F∞⁺ ⊆ M∞⁺`
      show σ x ∈ (MinfPlus p).restrictScalars ℚ
      exact FinfPlus_le_MinfPlus_restrict p
        ((IntermediateField.normal_iff_forall_map_le.mp (normal_FinfPlus p) σ) ⟨x, hxF, rfl⟩)
    · -- `x ∈ M⁺ₙ` for some `n`: `σ x ∈ M⁺ₙ ⊆ M∞⁺`
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxM
      show σ x ∈ (MinfPlus p).restrictScalars ℚ
      refine MPlusN_le_MinfPlus_restrict p n ?_
      exact (IntermediateField.normal_iff_forall_map_le.mp (normal_MPlusN_restrict p n) σ)
        ⟨x, (IntermediateField.mem_restrictScalars ℚ).mpr hxn, rfl⟩
  exact h

/-! ### The `Γ⁺`-action on `X⁺_∞` (Remark 13.7)

`Γ⁺ = Gal(F∞⁺/ℚ)` acts on `X∞⁺ = Gal(M∞⁺/F∞⁺)` by `σ · x = σ̃ x σ̃⁻¹` for any lift `σ̃` to
`Gal(M∞⁺/ℚ)` — well-defined since `X∞⁺` is abelian. We realize it via the group extension
`1 → X∞⁺ → Gal(M∞⁺/ℚ) → Γ⁺ → 1`: `M∞⁺/ℚ` is normal (`normal_MinfPlus`) so the restriction onto
`Γ⁺` is surjective, and its kernel is `X∞⁺`. -/

/-- `F∞⁺` realized as a `ℚ`-subfield of `M∞⁺` (the kernel-target of `Gal(M∞⁺/ℚ) ↠ Γ⁺`). -/
def FinfPlusInMinf : IntermediateField ℚ ↥(MinfPlus p) :=
  IntermediateField.comap ((MinfPlus p).val.restrictScalars ℚ) (FinfPlus p)

/-- The carrier iso `F∞⁺-in-M∞⁺ ≃ₐ[ℚ] F∞⁺`. -/
noncomputable def FinfPlusInMinfEquiv : ↥(FinfPlusInMinf p) ≃ₐ[ℚ] ↥(FinfPlus p) :=
  AlgEquiv.ofBijective
    (AlgHom.codRestrict (((MinfPlus p).val.restrictScalars ℚ).comp (FinfPlusInMinf p).val)
      (FinfPlus p).toSubalgebra (fun w => w.2))
    ⟨fun a b hab => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun w : ↥(FinfPlus p) => (w : Om)) hab,
      fun y => ⟨⟨⟨(y : Om), FinfPlus_le_MinfPlus_restrict p y.2⟩, y.2⟩, Subtype.ext rfl⟩⟩

/-- `F∞⁺-in-M∞⁺` is normal over `ℚ` (transfer of `normal_FinfPlus` along the carrier iso). -/
instance normal_FinfPlusInMinf : Normal ℚ ↥(FinfPlusInMinf p) := by
  haveI := normal_FinfPlus p
  exact Normal.of_algEquiv (FinfPlusInMinfEquiv p).symm

/-- `Gal(M∞⁺/ℚ)`. -/
abbrev GalMinfPlusQ : Type := ↥(MinfPlus p) ≃ₐ[ℚ] ↥(MinfPlus p)

/-- The restriction `Gal(M∞⁺/ℚ) →* Gal(F∞⁺/ℚ) = Γ⁺` (composed with the carrier iso). -/
noncomputable def restrToGammaPlus : GalMinfPlusQ p →* GammaPlus p :=
  (AlgEquiv.autCongr (FinfPlusInMinfEquiv p)).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (FinfPlusInMinf p))

/-- `Gal(M∞⁺/ℚ) ↠ Γ⁺` is surjective (`M∞⁺/ℚ` normal). -/
theorem restrToGammaPlus_surjective : Function.Surjective (restrToGammaPlus p) := by
  haveI := normal_MinfPlus p
  refine (AlgEquiv.autCongr (FinfPlusInMinfEquiv p)).surjective.comp ?_
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ) ↥(MinfPlus p)

/-- An `F∞⁺`-automorphism of `M∞⁺` fixes every element whose value lies in `F∞⁺`. -/
theorem XinfPlus_fixes (f : XinfPlus p) {z : ↥(MinfPlus p)} (hz : (z : Om) ∈ FinfPlus p) :
    f z = z := by
  have hzeq : z = algebraMap ↥(FinfPlus p) ↥(MinfPlus p) ⟨(z : Om), hz⟩ := Subtype.ext rfl
  rw [hzeq]; exact f.commutes _

/-- A `(F∞⁺-in-M∞⁺)`-automorphism of `M∞⁺` fixes every element whose value lies in `F∞⁺`. -/
theorem GalFinfInMinf_fixes (g : ↥(MinfPlus p) ≃ₐ[↥(FinfPlusInMinf p)] ↥(MinfPlus p))
    {z : ↥(MinfPlus p)} (hz : (z : Om) ∈ FinfPlus p) : g z = z := by
  have hzeq : z = algebraMap ↥(FinfPlusInMinf p) ↥(MinfPlus p) ⟨z, hz⟩ := Subtype.ext rfl
  rw [hzeq]; exact g.commutes _

/-- Base-change `Gal(M∞⁺/F∞⁺) ≃* Gal(M∞⁺/F∞⁺-in-M∞⁺)` (same underlying maps; the two `ℚ`-iso bases
`F∞⁺` and its copy `F∞⁺-in-M∞⁺ ⊆ M∞⁺` cut out the same automorphisms). -/
def baseChangeEquiv :
    XinfPlus p ≃* (↥(MinfPlus p) ≃ₐ[↥(FinfPlusInMinf p)] ↥(MinfPlus p)) where
  toFun f := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun c => XinfPlus_fixes p f c.2)
  invFun g := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun y => GalFinfInMinf_fixes p g y.2)
  left_inv f := by ext x; rfl
  right_inv g := by ext x; rfl
  map_mul' a b := by ext x; rfl

/-- Transport automorphisms along a group isomorphism `e : A ≃* B`. -/
def autCongrHom {A B : Type*} [Group A] [Group B] (e : A ≃* B) : MulAut A →* MulAut B where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by ext b; simp
  map_mul' φ ψ := by ext b; simp [MulAut.mul_apply]

/-- `ker(Gal(M∞⁺/ℚ) ↠ Γ⁺) = Gal(M∞⁺/F∞⁺)` (the `F∞⁺`-in-`M∞⁺`-fixing subgroup). -/
theorem ker_restrToGammaPlus :
    (restrToGammaPlus p).ker = (FinfPlusInMinf p).fixingSubgroup := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ ↥(MinfPlus p) _ _ _ (FinfPlusInMinf p)
    (normal_FinfPlusInMinf p)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact map_eq_one_iff _ (AlgEquiv.autCongr (FinfPlusInMinfEquiv p)).injective

/-- `X∞⁺ = Gal(M∞⁺/F∞⁺) ≃* ker(Gal(M∞⁺/ℚ) ↠ Γ⁺)` — `X∞⁺` is the kernel of the group extension. -/
noncomputable def xinfEquivKer : XinfPlus p ≃* ↥((restrToGammaPlus p).ker) :=
  ((baseChangeEquiv p).trans (IntermediateField.fixingSubgroupEquiv (FinfPlusInMinf p)).symm).trans
    (MulEquiv.subgroupCongr (ker_restrToGammaPlus p).symm)

/-- `X∞⁺` (≅ the kernel) is commutative — transported from `isMulCommutative_XinfPlus`. -/
theorem mul_comm_ker (a b : ↥((restrToGammaPlus p).ker)) : a * b = b * a := by
  apply (xinfEquivKer p).symm.injective
  rw [map_mul, map_mul]
  exact isMulCommutative_iff.mp (isMulCommutative_XinfPlus p) _ _

/-- Conjugation by a kernel element is trivial (the kernel `X∞⁺` is abelian) — so the conjugation
action of `Gal(M∞⁺/ℚ)` on the kernel descends to `Γ⁺`. -/
theorem conjNormal_eq_one_of_mem_ker (x : GalMinfPlusQ p) (hx : x ∈ (restrToGammaPlus p).ker) :
    MulAut.conjNormal x = (1 : MulAut ↥((restrToGammaPlus p).ker)) := by
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [MulAut.conjNormal_apply]
  have hcomm : x * (a : GalMinfPlusQ p) = (a : GalMinfPlusQ p) * x :=
    congrArg (fun z : ↥((restrToGammaPlus p).ker) => (z : GalMinfPlusQ p))
      (mul_comm_ker p ⟨x, hx⟩ a)
  rw [hcomm, mul_inv_cancel_right]
  rfl

/-- The `Γ⁺`-action hom `Γ⁺ →* MulAut(X∞⁺)` (Remark 13.7): conjugation by lifts, descended through
`Γ⁺ ≃ Gal(M∞⁺/ℚ)/X∞⁺` and transported to `X∞⁺` via `xinfEquivKer`. -/
noncomputable def gammaPlusActionHom : GammaPlus p →* MulAut (XinfPlus p) :=
  ((autCongrHom (xinfEquivKer p).symm).comp
    (QuotientGroup.lift (restrToGammaPlus p).ker MulAut.conjNormal
      (conjNormal_eq_one_of_mem_ker p))).comp
    (QuotientGroup.quotientKerEquivOfSurjective (restrToGammaPlus p)
      (restrToGammaPlus_surjective p)).symm.toMonoidHom

/-- **The `Γ⁺`-action on `X⁺_∞` (Remark 13.7).** `Γ⁺ = Gal(F∞⁺/ℚ)` acts on `X∞⁺ = Gal(M∞⁺/F∞⁺)` by
`σ · x = σ̃ x σ̃⁻¹` (conjugation by any lift `σ̃ ∈ Gal(M∞⁺/ℚ)`), well-defined since `X∞⁺` is abelian.
This is the action making `X∞⁺` a `Λ(Γ⁺)`-module — the setting of Theorem 13.11. -/
noncomputable instance instMulDistribMulActionGammaPlusXinfPlus :
    MulDistribMulAction (GammaPlus p) (XinfPlus p) :=
  MulDistribMulAction.compHom (XinfPlus p) (gammaPlusActionHom p)

/-! ### The Galois SES `0 → Gal(M∞⁺/L∞⁺) → X∞⁺ → Y∞⁺ → 0` (TG4)

`M∞⁺/F∞⁺` and `L∞⁺/F∞⁺` are normal: an `F∞⁺`-automorphism `σ` of `Ω` fixes each `F⁺ₙ`, so it
stabilises the layers `M⁺ₙ`, `L⁺ₙ` (already Galois over `F⁺ₙ`). Restriction `X∞⁺ → Y∞⁺` is then
surjective with kernel `Gal(M∞⁺/L∞⁺)`. (Independent of the `isAdmissibleM_map` gap, which concerned
normality over `ℚ`.) -/

instance instIsAlgClosureFPlusOm (n : ℕ) : IsAlgClosure ↥(FPlus p n) Om :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ↥(FPlus p n)⟩

instance instNormalFPlusOm (n : ℕ) : Normal ↥(FPlus p n) Om := IsAlgClosure.normal ↥(FPlus p n) Om

instance instIsAlgClosureFinfOm : IsAlgClosure ↥(FinfPlus p) Om :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ↥(FinfPlus p)⟩

instance instNormalFinfOm : Normal ↥(FinfPlus p) Om := IsAlgClosure.normal ↥(FinfPlus p) Om

/-- `M∞⁺/F∞⁺` is normal (each `F∞⁺`-auto of `Ω` stabilises the `F⁺ₙ`-Galois layers `M⁺ₙ`). -/
instance instNormalMinfPlusOverFinf : Normal (FinfPlus p) (MinfPlus p) := by
  refine (IntermediateField.normal_iff_forall_map_le).mpr fun σ => ?_
  rw [IntermediateField.map_le_iff_le_comap]
  nth_rewrite 1 [MinfPlus]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro w hw
  obtain ⟨n, hwn⟩ := Set.mem_iUnion.mp hw
  show σ w ∈ MinfPlus p
  have hle : FPlus p n ≤ FinfPlus p := by rw [FinfPlus]; exact le_iSup (FPlus p) n
  letI : Algebra ↥(FPlus p n) ↥(FinfPlus p) := (IntermediateField.inclusion hle).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hσn : σ w ∈ MPlusN p n :=
    (IntermediateField.normal_iff_forall_map_le.mp (instNormalMPlusN p n)
      (σ.restrictScalars ↥(FPlus p n))) ⟨w, hwn, rfl⟩
  rw [MinfPlus]
  exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, hσn⟩)

/-- `L∞⁺/F∞⁺` is normal (same argument over the unramified tower). -/
instance instNormalLinfPlusOverFinf : Normal (FinfPlus p) (LinfPlus p) := by
  refine (IntermediateField.normal_iff_forall_map_le).mpr fun σ => ?_
  rw [IntermediateField.map_le_iff_le_comap]
  nth_rewrite 1 [LinfPlus]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro w hw
  obtain ⟨n, hwn⟩ := Set.mem_iUnion.mp hw
  show σ w ∈ LinfPlus p
  have hle : FPlus p n ≤ FinfPlus p := by rw [FinfPlus]; exact le_iSup (FPlus p) n
  letI : Algebra ↥(FPlus p n) ↥(FinfPlus p) := (IntermediateField.inclusion hle).toAlgebra
  letI : IsScalarTower ↥(FPlus p n) ↥(FinfPlus p) Om := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hσn : σ w ∈ LPlusN p n :=
    (IntermediateField.normal_iff_forall_map_le.mp (instNormalLPlusN p n)
      (σ.restrictScalars ↥(FPlus p n))) ⟨w, hwn, rfl⟩
  rw [LinfPlus]
  exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.mpr ⟨n, hσn⟩)

/-- `L∞⁺` realized as an `F∞⁺`-subfield of `M∞⁺` (the kernel-target of `X∞⁺ ↠ Y∞⁺`), via mathlib's
`IntermediateField.restrict` of the containment `L∞⁺ ≤ M∞⁺`. -/
def LinfPlusInMinf : IntermediateField (FinfPlus p) ↥(MinfPlus p) :=
  IntermediateField.restrict (LinfPlus_le_MinfPlus p)

/-- The carrier iso `L∞⁺-in-M∞⁺ ≃ₐ[F∞⁺] L∞⁺` (mathlib's `restrict_algEquiv`). -/
noncomputable def LinfPlusInMinfEquiv : ↥(LinfPlusInMinf p) ≃ₐ[FinfPlus p] ↥(LinfPlus p) :=
  (IntermediateField.restrict_algEquiv (LinfPlus_le_MinfPlus p)).symm

/-- `L∞⁺-in-M∞⁺` is normal over `F∞⁺`. -/
instance normal_LinfPlusInMinf : Normal (FinfPlus p) ↥(LinfPlusInMinf p) := by
  haveI := instNormalLinfPlusOverFinf p
  exact Normal.of_algEquiv (LinfPlusInMinfEquiv p).symm

/-- **The Galois SES map** `X∞⁺ = Gal(M∞⁺/F∞⁺) →* Y∞⁺ = Gal(L∞⁺/F∞⁺)` (restriction to `L∞⁺`). -/
noncomputable def restrXtoY : XinfPlus p →* YinfPlus p :=
  (AlgEquiv.autCongr (LinfPlusInMinfEquiv p)).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (LinfPlusInMinf p))

/-- `X∞⁺ ↠ Y∞⁺` is surjective (`M∞⁺/F∞⁺` normal). -/
theorem restrXtoY_surjective : Function.Surjective (restrXtoY p) := by
  refine (AlgEquiv.autCongr (LinfPlusInMinfEquiv p)).surjective.comp ?_
  exact AlgEquiv.restrictNormalHom_surjective (F := ↥(FinfPlus p)) ↥(MinfPlus p)

/-- **Kernel of the SES**: `ker(X∞⁺ ↠ Y∞⁺) = Gal(M∞⁺/L∞⁺)` (the `L∞⁺`-fixing subgroup). -/
theorem ker_restrXtoY :
    (restrXtoY p).ker = (LinfPlusInMinf p).fixingSubgroup := by
  rw [← @IntermediateField.restrictNormalHom_ker ↥(FinfPlus p) ↥(MinfPlus p) _ _ _
    (LinfPlusInMinf p) (normal_LinfPlusInMinf p)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact map_eq_one_iff _ (AlgEquiv.autCongr (LinfPlusInMinfEquiv p)).injective

/-! ### Toward the `Λ(Γ⁺)`-module structure (TG2)

The `Λ(Γ⁺)`-module structure on `X⁺_∞` begins with the **`ℤ[Γ⁺]`-module**: since `X∞⁺` is abelian
(`isMulCommutative_XinfPlus`), `Additive X∞⁺` is an additive abelian group, and the conjugation
action of Remark 13.7 (`instMulDistribMulActionGammaPlusXinfPlus`) distributes over it. Both facts
are derived automatically by instance synthesis — recorded here as the first half of TG2. The
remaining half (completion to `Λ(Γ⁺) = ℤp[[Γ⁺]]` and the identification `Γ⁺ ≅ ℤp` linking to §12's
`IwasawaAlgebra`/`Gamma`) is ticket **TG2-Lambda**. -/

/-- `X⁺_∞` is a commutative group (abelian — `isMulCommutative_XinfPlus`). This upgrades `Additive
X∞⁺` to an additive **abelian** group, the carrier of the `Λ(Γ⁺)`-module of Theorem 13.11. -/
instance instCommGroupXinfPlus : CommGroup (XinfPlus p) :=
  { (inferInstance : Group (XinfPlus p)) with
    mul_comm := fun a b => isMulCommutative_iff.mp (isMulCommutative_XinfPlus p) a b }

/-- `Additive X⁺_∞` is an additive abelian group — together with the `Γ⁺`-action
(`instMulDistribMulActionGammaPlusXinfPlus`) this is the `ℤ[Γ⁺]`-module starting the `Λ(Γ⁺)`-module
structure of Theorem 13.11 (completion to `ℤp[[Γ⁺]]` + `Γ⁺ ≅ ℤp` is ticket TG2-Lambda). -/
example : AddCommGroup (Additive (XinfPlus p)) := inferInstance

end Iwasawa.GaloisFoundation
