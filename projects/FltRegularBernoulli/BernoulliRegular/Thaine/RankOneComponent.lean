module

public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# T-Q1-RANK-ONE: Rank-one component lemma

Per the 2026-05-07 reviewer followup, the atomic lemma underlying the
`UnitQuotientComponentTrivial ↔ (E⁺/C_S)(ω^i)[p] = 0` equivalence is the
abstract rank-one statement: for a free rank-one Λ-module inclusion
`C ⊂ E` with generator `c`,
   `c ∉ p • E   ⟺   (E/C)[p] = 0`.

After fixing isomorphisms `E ≃ Λ` and `C ≃ Λ` (via the chosen generators),
this reduces to a pure ring-theoretic statement about `Λ`: if the
inclusion `C → E` corresponds to multiplication by `a ∈ Λ`, then
   `¬ p ∣ a   ⟺   (Λ/(a))[p] = 0`.

For our application Λ = ℤ_p (the p-adic integers) is a PID, p is the
defining prime, and the iff specialises to the multiplicative-units
side via the standard `e_i (E⁺ ⊗ ℤ_p) ≃ ℤ_p` Dirichlet identifications.

This module proves the abstract atomic lemma. The substantive
multiplicative-units specialisation (involving Sinnott circular units,
the Pollaczek generator, and the eigencomponent identifications) is
deferred to a follow-up ticket once `e_i (C_S ⊗ ℤ_p) ≃ ℤ_p` and
`e_i (E⁺ ⊗ ℤ_p) ≃ ℤ_p` are formalised.

## References

* Washington, *Introduction to Cyclotomic Fields*, §8.1 (Sinnott),
  §8.3 (cyclotomic units eigencomponents).
* Sinnott, "On the Stickelberger ideal and the circular units of an
  abelian field" (1980), Inv. Math. 62, 181–234.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.Thaine

/-- A class in `R ⧸ (a)` vanishes exactly when `a` divides the representative. -/
private theorem quotient_mk_eq_zero_iff {R : Type*} [CommRing R] (a y : R) :
    (Submodule.Quotient.mk y : R ⧸ Submodule.span R ({a} : Set R)) = 0 ↔ a ∣ y := by
  rw [Submodule.Quotient.mk_eq_zero, Ideal.submodule_span_eq, Ideal.mem_span_singleton]

/-- Being `p`-torsion-free transfers across a `Λ`-linear isomorphism. -/
private theorem forall_smul_eq_zero_congr {Λ M N : Type*} [CommRing Λ]
    [AddCommGroup M] [Module Λ M] [AddCommGroup N] [Module Λ N]
    (p : Λ) (q : M ≃ₗ[Λ] N) :
    (∀ x : M, p • x = 0 → x = 0) ↔ (∀ y : N, p • y = 0 → y = 0) := by
  constructor
  · intro h y hpy
    have : q.symm y = 0 := h _ (by rw [← q.symm.map_smul, hpy, q.symm.map_zero])
    simpa [this] using (q.apply_symm_apply y).symm
  · intro h x hpx
    have : q x = 0 := h _ (by rw [← q.map_smul, hpx, q.map_zero])
    simpa [this] using (q.symm_apply_apply x).symm

/-- The rank-one identification `φ : E ≃ₗ[Λ] Λ` carries `E ⧸ Λ·c` to `Λ ⧸ (φ c)`. -/
private def quotientSpanEquiv {Λ E : Type*} [CommRing Λ] [AddCommGroup E] [Module Λ E]
    (φ : E ≃ₗ[Λ] Λ) (c : E) :
    (E ⧸ Submodule.span Λ ({c} : Set E)) ≃ₗ[Λ]
      (Λ ⧸ Submodule.span Λ ({φ c} : Set Λ)) :=
  Submodule.Quotient.equiv (Submodule.span Λ ({c} : Set E))
    (Submodule.span Λ ({φ c} : Set Λ)) φ (by rw [Submodule.map_span]; simp)

/-- **Abstract rank-one quotient is `p`-torsion-free under coprimeness**
(forward direction, general rings).

For any commutative ring `R`, `p, a ∈ R` with `IsCoprime p a`: the
quotient `R/(a)` has trivial `p`-torsion. This is the most general
form of the forward direction, requiring neither domain structure nor
PID/principal ideal — only the coprimeness hypothesis.

The reverse direction (torsion-free ⟹ coprime) requires more structure
(see `rankOne_quotient_no_p_torsion_iff_generator_not_divisible` below
for the iff in the PID case). -/
theorem rankOne_quotient_p_torsion_free_of_isCoprime
    {R : Type*} [CommRing R]
    {p a : R} (h : IsCoprime p a) :
    ∀ x : R ⧸ Submodule.span R ({a} : Set R), p • x = 0 → x = 0 := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    intro hpy
    have hpy' : a ∣ p * y := (quotient_mk_eq_zero_iff a (p * y)).mp hpy
    exact (quotient_mk_eq_zero_iff a y).mpr (h.symm.dvd_of_dvd_mul_left hpy')

/-- **Abstract atomic rank-one lemma.** For a PID `R`, prime `p ∈ R`,
nonzero `a ∈ R`: the quotient `R/(a)` has trivial `p`-torsion if and only
if `p` does not divide `a`.

**Module-theoretic interpretation**: this is the rank-one component
statement after fixing isomorphisms `E ≃ Λ` and `C ≃ Λ` (via generators).
The inclusion `C → E` becomes multiplication by `a`, and
`(E/C)[p] = 0 ⟺ ¬ p ∣ a` is the assertion that the generator of `C`
maps into `E` as an element not divisible by `p`. -/
theorem rankOne_quotient_no_p_torsion_iff_generator_not_divisible
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {p : R} (hp : Prime p) {a : R} (ha : a ≠ 0) :
    (¬ p ∣ a) ↔
    ∀ x : R ⧸ Submodule.span R ({a} : Set R), p • x = 0 → x = 0 := by
  refine ⟨fun hp_not_dvd ↦
    rankOne_quotient_p_torsion_free_of_isCoprime (hp.coprime_iff_not_dvd.mpr hp_not_dvd), ?_⟩
  rintro h_tf ⟨a', rfl⟩
  have ha' : a' ≠ 0 := fun h ↦ ha (by rw [h, mul_zero])
  have hpx_zero : (p • (Submodule.Quotient.mk a' :
      R ⧸ Submodule.span R ({p * a'} : Set R))) = 0 :=
    (quotient_mk_eq_zero_iff (p * a') (p * a')).mpr dvd_rfl
  obtain ⟨k, hk⟩ := (quotient_mk_eq_zero_iff (p * a') a').mp (h_tf _ hpx_zero)
  -- `a' = p * a' * k` forces `p * k = 1`, contradicting primality of `p`.
  have hzero : a' * (1 - p * k) = 0 := by
    have hexpand : a' * (1 - p * k) = a' - p * a' * k := by ring
    rw [hexpand, ← hk, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact ha' h
  · exact hp.not_unit (IsUnit.of_mul_eq_one k (sub_eq_zero.mp h).symm)

/-- **Module-theoretic rank-one component lemma.** For a PID `Λ`, prime
`p ∈ Λ`, and a free rank-one Λ-module `E` (specified via a Λ-linear
isomorphism `φ : E ≃ₗ[Λ] Λ`), and a nonzero `c ∈ E`:
   `c ∉ p • E   ⟺   (E ⧸ Λ·c)[p] = 0`.

This is the direct module-theoretic specialisation of
`rankOne_quotient_no_p_torsion_iff_generator_not_divisible`,
parametrised by the iso `φ` (the "rank-1 identification"). It is the
form directly applicable to the eigenspace specialisation
`e_i (E⁺ ⊗ ℤ_p) ≃ₗ[ℤ_p] ℤ_p` once that decomposition is in place. -/
theorem rankOne_module_quotient_no_p_torsion_iff_generator_not_p_divisible
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ]
    {p : Λ} (hp : Prime p)
    {E : Type*} [AddCommGroup E] [Module Λ E]
    (φ : E ≃ₗ[Λ] Λ)
    {c : E} (hc : c ≠ 0) :
    (¬ ∃ y : E, c = p • y) ↔
    ∀ x : E ⧸ Submodule.span Λ ({c} : Set E),
      p • x = 0 → x = 0 := by
  have ha_ne : φ c ≠ 0 := fun h ↦ hc (φ.injective (by rw [φ.map_zero]; exact h))
  have h_dvd_iff : (∃ y : E, c = p • y) ↔ p ∣ φ c := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨φ y, by rw [hy, map_smul]; rfl⟩
    · rintro ⟨b, hb⟩
      refine ⟨φ.symm b, ?_⟩
      rw [(φ.symm_apply_apply c).symm, hb, ← smul_eq_mul, map_smul]
  rw [forall_smul_eq_zero_congr p (quotientSpanEquiv φ c),
    ← rankOne_quotient_no_p_torsion_iff_generator_not_divisible hp ha_ne,
    not_iff_not, h_dvd_iff]

/-- **Module-theoretic rank-one is `p`-torsion-free under coprimeness**
(forward direction, general rings).

Module-theoretic generalisation of `rankOne_quotient_p_torsion_free_of_isCoprime`:
for any commutative ring `Λ`, free rank-one Λ-module `E` (specified via
the iso `φ : E ≃ₗ[Λ] Λ`), and `p : Λ` with `IsCoprime p (φ c)`,
   `(E ⧸ Λ·c)[p] = 0`.

This is the most general forward direction at the module level —
no domain or PID assumption needed. -/
theorem rankOne_module_quotient_p_torsion_free_of_isCoprime
    {Λ : Type*} [CommRing Λ]
    {p : Λ}
    {E : Type*} [AddCommGroup E] [Module Λ E]
    (φ : E ≃ₗ[Λ] Λ) {c : E} (h_cop : IsCoprime p (φ c)) :
    ∀ x : E ⧸ Submodule.span Λ ({c} : Set E), p • x = 0 → x = 0 :=
  (forall_smul_eq_zero_congr p (quotientSpanEquiv φ c)).mpr
    (rankOne_quotient_p_torsion_free_of_isCoprime h_cop)

end BernoulliRegular.Thaine

end
