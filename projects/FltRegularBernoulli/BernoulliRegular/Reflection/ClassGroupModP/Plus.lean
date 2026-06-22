import BernoulliRegular.Reflection.ClassGroupModP.Module
import BernoulliRegular.TotallyRealSubfield.ClassGroup
import BernoulliRegular.TotallyRealSubfield.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Plus-side descent of ClassGroupModP

Defines the natural map `Cl(𝓞 K⁺)/p → Cl(𝓞 K)/p` induced by
`classGroupMap : Cl(𝓞 K⁺) → Cl(𝓞 K)` via the quotient.

This is part of SP-2a infrastructure (the descent to `ClassGroupModP`
of the K⁺ → K class-group embedding).

## Open: injectivity (SP-2a proper)

The injectivity claim `Function.Injective classGroupMap_modP` requires
more than just `classGroupMap_injective` — it needs p-saturation of
the image (equivalently, the cokernel having order coprime to p).
For irregular primes with p ∣ h⁻(K), this can fail without additional
hypotheses. Tracked as SP-2a in the ticket board.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **`classGroupMap_modP`**: the natural map `Cl(𝓞 K⁺)/p → Cl(𝓞 K)/p`
induced by `classGroupMap` via the quotient.

Well-defined because `classGroupMap` sends p-th powers to p-th powers:
if `g = h^p` then `classGroupMap g = (classGroupMap h)^p`. -/
noncomputable def classGroupMap_modP :
    ClassGroupModP K⁺ p →* ClassGroupModP K p :=
  @QuotientGroup.map (ClassGroup (𝓞 K⁺)) (ClassGroup (𝓞 K)) _ _
    ((powMonoidHom p : ClassGroup (𝓞 K⁺) →* _).range) _
    ((powMonoidHom p : ClassGroup (𝓞 K) →* _).range) _
    (classGroupMap K)
    (by
      intro x ⟨y, hy⟩
      refine ⟨classGroupMap K y, ?_⟩
      change (classGroupMap K y) ^ p = classGroupMap K x
      have : y ^ p = x := hy
      rw [← this, map_pow])

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Under p ∤ h⁺, the powMonoidHom range on Cl(K⁺) is the whole group.** -/
theorem powMonoidHom_range_Kplus_eq_top_of_not_dvd_hPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    (powMonoidHom p : ClassGroup (𝓞 K⁺) →* _).range = ⊤ := by
  haveI : Fact (Nat.Prime p) := hp
  have h_coprime : (Nat.card (ClassGroup (𝓞 K⁺))).Coprime p := by
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_
    intro hdvd
    apply h_not_dvd
    change p ∣ Fintype.card (ClassGroup (𝓞 K⁺))
    rwa [Nat.card_eq_fintype_card] at hdvd
  rw [MonoidHom.range_eq_top]
  exact (powCoprime (G := ClassGroup (𝓞 K⁺)) h_coprime).surjective

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Under p ∤ h⁺, `ClassGroupModP K⁺ p` is trivial.** -/
theorem classGroupModP_Kplus_subsingleton_of_not_dvd_hPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    Subsingleton (ClassGroup (𝓞 K⁺) ⧸
      (powMonoidHom p : ClassGroup (𝓞 K⁺) →* _).range) := by
  rw [powMonoidHom_range_Kplus_eq_top_of_not_dvd_hPlus p K h_not_dvd]
  exact QuotientGroup.subsingleton_quotient_top

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **SP-2a (under p ∤ h⁺): `classGroupMap_modP` is injective.**

Under the Vandiver-style hypothesis `p ∤ h⁺`, the source `Cl(K⁺)/p` is
trivial (above), so any map out of it is trivially injective. -/
theorem classGroupMap_modP_injective_of_not_dvd_hPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    Function.Injective (classGroupMap_modP p K) := by
  haveI := classGroupModP_Kplus_subsingleton_of_not_dvd_hPlus p K h_not_dvd
  exact Function.injective_of_subsingleton _

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **SP-2b (under p ∤ h⁺): the range of `classGroupMap_modP` is trivial.**

Under `p ∤ h⁺`, the source `Cl(K⁺)/p` is trivial, hence the range is
trivial (i.e., equals `⊥`). This is the LHS-direction of SP-2b under
the Vandiver hypothesis. -/
theorem classGroupMap_modP_range_eq_bot_of_not_dvd_hPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    (classGroupMap_modP p K).range = ⊥ := by
  haveI := classGroupModP_Kplus_subsingleton_of_not_dvd_hPlus p K h_not_dvd
  rw [Subgroup.eq_bot_iff_forall]
  rintro a ⟨b, rfl⟩
  rw [show b = 1 from Subsingleton.elim _ _, map_one]

/-! ## Unconditional SP-2a via the norm trick

The reviewer's clean argument (2026-05-22): the relative norm map
`N : Cl(K) → Cl(K⁺)` satisfies `N ∘ j = [K : K⁺] = 2` on `Cl(K⁺)`,
where `j = classGroupMap`. Suppose `j(x) = py` for some `y ∈ Cl(K)`.
Apply `N`: `2x = p · N(y)`. Since `p` is odd, `gcd(2, p) = 1`, so by
Bezout `x = z^p` for some `z ∈ Cl(K⁺)`. Hence `x` is in the
p-th-power range, so injectivity on the mod-p quotient holds.

The norm is realised at the ideal level by `Ideal.relNorm (𝓞 K⁺)`,
which is a `MonoidWithZeroHom : Ideal (𝓞 K) →*₀ Ideal (𝓞 K⁺)`. The
key composition identity `relNorm (I.map (algebraMap (𝓞 K⁺) (𝓞 K))) =
I ^ [K : K⁺]` is the shipped mathlib `Ideal.relNorm_algebraMap`. -/

omit [IsCMField K] in
attribute [local instance] FractionRing.liftAlgebra in
/-- **`finrank` of the fraction-ring extension `FracRing(𝓞 K⁺) → FracRing(𝓞 K)`
equals `[K : K⁺] = 2`.** -/
private theorem finrank_fractionRing_ringOfIntegers_K_over_Kplus
    [NumberField.IsCMField K] :
    Module.finrank
      (FractionRing (𝓞 (NumberField.maximalRealSubfield K)))
      (FractionRing (𝓞 K)) = 2 := by
  rw [Algebra.finrank_eq_of_equiv_equiv
    (FractionRing.algEquiv (𝓞 (NumberField.maximalRealSubfield K))
      (NumberField.maximalRealSubfield K)).toRingEquiv
    (FractionRing.algEquiv (𝓞 K) K).toRingEquiv]
  · exact finrank_K_over_Kplus K
  · ext z
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv (𝓞 (NumberField.maximalRealSubfield K))
        (NumberField.maximalRealSubfield K))
      (FractionRing.algEquiv (𝓞 K) K) z

omit [IsCMField K] in
/-- **`Ideal.relNorm` of a non-zero ideal is non-zero.** Wrapper for
`relNorm_eq_bot_iff` mapping `(Ideal (𝓞 K))⁰` to `(Ideal (𝓞 K⁺))⁰`. -/
private theorem relNorm_mem_nonZeroDivisors
    (J : (Ideal (𝓞 K))⁰) :
    Ideal.relNorm (𝓞 (NumberField.maximalRealSubfield K)) J.1 ∈
      nonZeroDivisors (Ideal (𝓞 (NumberField.maximalRealSubfield K))) := by
  rw [mem_nonZeroDivisors_iff_ne_zero, ← bot_eq_zero, ne_eq, Ideal.relNorm_eq_bot_iff]
  exact mem_nonZeroDivisors_iff_ne_zero.mp J.2

omit [IsCMField K] in
attribute [local instance] FractionRing.liftAlgebra in
/-- **The relNorm of an algebraMap'd ideal is its square in 𝓞 K⁺**: direct
`Ideal`-level form of the composition identity, using `[K : K⁺] = 2`. -/
private theorem relNorm_algebraMap_eq_sq
    [NumberField.IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    Ideal.relNorm (𝓞 (NumberField.maximalRealSubfield K))
        (I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) =
      I ^ 2 := by
  rw [Ideal.relNorm_algebraMap]
  congr 1
  exact finrank_fractionRing_ringOfIntegers_K_over_Kplus K

omit [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **SP-2a UNCONDITIONAL via the norm trick** (Reviewer guidance 2026-05-22).

For any odd prime `p`, the natural map
`Cl(K⁺)/p → Cl(K)/p` is injective.

The proof goes through the relative-norm composition identity
`N ∘ j = 2`. Given `j(x) = py`, applying `N` yields `2x = p · N(y)`,
and since `gcd(2, p) = 1` (`p` odd), Bezout gives `x = z^p`. -/
theorem classGroupMap_modP_injective_unconditional [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) :
    Function.Injective (classGroupMap_modP p K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  -- c ∈ ClassGroup (𝓞 K⁺) ⧸ (powMonoidHom p).range; pick representative.
  obtain ⟨cI, rfl⟩ := QuotientGroup.mk_surjective c
  -- hc : classGroupMap_modP p K (mk cI) = 1
  -- Unfold classGroupMap_modP through QuotientGroup.map_mk.
  have h_in : classGroupMap K cI ∈
      (powMonoidHom p : ClassGroup (𝓞 K) →* _).range := by
    rwa [classGroupMap_modP, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hc
  -- Extract a p-th-power witness for classGroupMap cI.
  obtain ⟨d, hd⟩ : ∃ d : ClassGroup (𝓞 K), d ^ p = classGroupMap K cI := h_in
  -- Goal: mk cI = 1, equivalent to cI ∈ (powMonoidHom p).range.
  rw [QuotientGroup.eq_one_iff]
  -- Pick ideal representatives.
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective cI
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective d
  -- hd : (mk0 J) ^ p = classGroupMap K (mk0 I) = mk0 (I.map alg).
  rw [ClassGroup.extensionMap_mk0] at hd
  -- Apply the norm relation: (mk0 I)^2 = (mk0 (relNorm J))^p.
  have h_sq_eq_p_pow :
      (ClassGroup.mk0 I) ^ 2 =
        (ClassGroup.mk0 ⟨Ideal.relNorm
          (𝓞 (NumberField.maximalRealSubfield K)) J.1,
          relNorm_mem_nonZeroDivisors K J⟩) ^ p := by
    -- From hd: mk0 (J^p) = mk0 (I.map alg).
    -- Apply relNorm to both sides via mk0_eq_mk0_iff.
    have hd_mk0 : ClassGroup.mk0 (J ^ p) =
        ClassGroup.mk0 ⟨I.1.map
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            ((Ideal.map_eq_bot_iff_of_injective
              (FaithfulSMul.algebraMap_injective _ _)).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩ := by
      rw [map_pow]
      exact hd
    rw [ClassGroup.mk0_eq_mk0_iff] at hd_mk0
    obtain ⟨x, y, hx_nz, hy_nz, h_eq⟩ := hd_mk0
    -- h_eq : Ideal.span {x} * ↑(J^p) = Ideal.span {y} * ↑(I.map alg ...)
    -- Note: ↑(J^p) in (Ideal _)⁰ unfolds to (↑J)^p; let's normalise the coercion.
    have h_eq' : Ideal.span {x} * (J.1 : Ideal (𝓞 K)) ^ p =
        Ideal.span {y} *
          (I.1.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) := by
      simpa only [SubmonoidClass.coe_pow] using h_eq
    -- Apply relNorm to both sides.
    have h_relNorm_eq :
        Ideal.relNorm (𝓞 (NumberField.maximalRealSubfield K))
          (Ideal.span {x} * (J.1 : Ideal (𝓞 K)) ^ p) =
        Ideal.relNorm (𝓞 (NumberField.maximalRealSubfield K))
          (Ideal.span {y} *
            (I.1.map (algebraMap _ (𝓞 K)))) := by
      rw [h_eq']
    -- Expand via multiplicativity: relNorm (A*B) = relNorm A * relNorm B.
    simp only [map_mul, map_pow, Ideal.relNorm_singleton,
      Ideal.relNorm_algebraMap] at h_relNorm_eq
    -- Now h_relNorm_eq : span {intNorm x} * (relNorm J)^p =
    --                    span {intNorm y} * I^(finrank (FracRing _) (FracRing _))
    -- Use finrank = 2 to convert.
    rw [finrank_fractionRing_ringOfIntegers_K_over_Kplus K] at h_relNorm_eq
    -- Convert mk0 I ^ 2 and mk0 ⟨...⟩ ^ p into mk0 of powers using MonoidHom.map_pow.
    rw [← map_pow ClassGroup.mk0 I 2,
        ← map_pow ClassGroup.mk0
          (⟨Ideal.relNorm _ J.1, relNorm_mem_nonZeroDivisors K J⟩ : (Ideal _)⁰) p]
    -- Now goal: mk0 (I^2) = mk0 (⟨...⟩^p). Apply mk0_eq_mk0_iff.
    apply (ClassGroup.mk0_eq_mk0_iff (R := 𝓞 (NumberField.maximalRealSubfield K))).mpr
    refine ⟨Algebra.intNorm (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y,
            Algebra.intNorm (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x,
            ?_, ?_, ?_⟩
    · -- intNorm y ≠ 0 since y ≠ 0 (and 𝓞 K is integral domain).
      intro h_zero
      exact hy_nz (Algebra.intNorm_eq_zero.mp h_zero)
    · intro h_zero
      exact hx_nz (Algebra.intNorm_eq_zero.mp h_zero)
    · -- Goal (after the symbol):
      --   span {intNorm y} * ↑(I^2) = span {intNorm x} * ↑(⟨relNorm J, _⟩ ^ p)
      -- where the coercion goes (Ideal R)⁰ → Ideal R.
      -- After SubmonoidClass.coe_pow rewrites, this reduces to:
      --   span {intNorm y} * (I.1)^2 = span {intNorm x} * (relNorm J)^p
      -- which is h_relNorm_eq.symm.
      simp only [SubmonoidClass.coe_pow]
      exact h_relNorm_eq.symm
  -- Now from (mk0 I)^2 = w^p with w := mk0 (relNorm J), Bezout gives mk0 I = z^p.
  -- Use the abstract group-theoretic lemma: in a (finite) commutative group,
  -- a^2 = b^p with gcd(2,p)=1 implies ∃ z, a = z^p.
  set w : ClassGroup (𝓞 (NumberField.maximalRealSubfield K)) :=
    ClassGroup.mk0 ⟨Ideal.relNorm _ J.1, relNorm_mem_nonZeroDivisors K J⟩
  -- gcd(2, p) = 1 since p is odd prime.
  have hp_coprime : Nat.Coprime 2 p :=
    Nat.coprime_two_left.mpr ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd)
  -- Bezout in ℤ: ∃ u v, 2*u + p*v = 1.
  have h_bezout : (2 : ℤ) * (2 : ℕ).gcdA p + (p : ℤ) * (2 : ℕ).gcdB p = 1 := by
    have := Nat.gcd_eq_gcd_ab 2 p
    rw [hp_coprime] at this
    exact_mod_cast this.symm
  set u : ℤ := (2 : ℕ).gcdA p
  set v : ℤ := (2 : ℕ).gcdB p
  -- a := mk0 I; we have a^2 = w^p. Want z with z^p = a.
  -- z := w^u * a^v works since z^p = w^(p*u) * a^(p*v) = w^(p*u) * (a^p)^v.
  -- Hmm, but Bezout gives a = a^1 = a^(2u+pv) = (a^2)^u * a^(pv) = (w^p)^u * a^(pv)
  --     = (w^u)^p * (a^v)^p = (w^u * a^v)^p.
  set a : ClassGroup (𝓞 (NumberField.maximalRealSubfield K)) :=
    ClassGroup.mk0 I with ha_def
  set z : ClassGroup (𝓞 (NumberField.maximalRealSubfield K)) :=
    w ^ u * a ^ v
  refine ⟨z, ?_⟩
  -- Want: z^p = a (where a = mk0 I). Use Bezout 2*u + p*v = 1 in ℤ.
  -- z^p = w^(p*u) * a^(p*v) = (w^p)^u * a^(p*v) = (a^2)^u * a^(p*v)
  --     = a^(2*u + p*v) = a^1 = a.
  -- Work in ℤ exponents throughout.
  -- Key fact (from h_sq_eq_p_pow): w^p = a^2 in zpow form too.
  have h_sq_eq_p_pow' : w ^ (p : ℤ) = a ^ (2 : ℤ) := by
    exact_mod_cast h_sq_eq_p_pow.symm
  -- Compute z^p step by step.
  change z ^ p = a
  calc z ^ p
      = z ^ (p : ℤ) := by rw [zpow_natCast]
    _ = (w ^ u * a ^ v) ^ (p : ℤ) := by rfl
    _ = (w ^ u) ^ (p : ℤ) * (a ^ v) ^ (p : ℤ) := mul_zpow _ _ _
    _ = w ^ (u * (p : ℤ)) * a ^ (v * (p : ℤ)) := by rw [← zpow_mul, ← zpow_mul]
    _ = w ^ ((p : ℤ) * u) * a ^ ((p : ℤ) * v) := by rw [mul_comm u, mul_comm v]
    _ = (w ^ (p : ℤ)) ^ u * a ^ ((p : ℤ) * v) := by rw [zpow_mul]
    _ = (a ^ (2 : ℤ)) ^ u * a ^ ((p : ℤ) * v) := by rw [h_sq_eq_p_pow']
    _ = a ^ ((2 : ℤ) * u) * a ^ ((p : ℤ) * v) := by rw [← zpow_mul]
    _ = a ^ ((2 : ℤ) * u + (p : ℤ) * v) := by rw [← zpow_add]
    _ = a ^ (1 : ℤ) := by rw [h_bezout]
    _ = a := zpow_one a

omit [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **SP-2a UNCONDITIONAL: ClassGroupModP descent is injective.**

Top-level wrapper for the unconditional form. The Vandiver-conditional
form `classGroupMap_modP_injective_of_not_dvd_hPlus` is now subsumed by
this (the Vandiver case is just the special instance where the source
is trivial).

Reviewer guidance 2026-05-22 (Q5 / norm trick). -/
theorem classGroupMap_modP_injective [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) :
    Function.Injective (classGroupMap_modP p K) :=
  classGroupMap_modP_injective_unconditional p K hp_odd

end FLT37

end BernoulliRegular

end
