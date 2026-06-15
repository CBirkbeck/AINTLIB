import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

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
  set I : Submodule R R := Submodule.span R ({a} : Set R) with hI_def
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    intro hpy
    have hpy' : a ∣ p * y := by
      have hk : (Submodule.Quotient.mk (p * y) : R ⧸ I) = 0 := hpy
      rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
          Ideal.mem_span_singleton] at hk
      exact hk
    -- IsCoprime a p (by symmetry), applied to a ∣ p * y, gives a ∣ y.
    have hcop_ap : IsCoprime a p := h.symm
    have hady : a ∣ y := hcop_ap.dvd_of_dvd_mul_left hpy'
    rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
        Ideal.mem_span_singleton]
    exact hady

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
  set I : Submodule R R := Submodule.span R ({a} : Set R) with hI_def
  refine ⟨?_, ?_⟩
  · -- Forward: ¬ p ∣ a → R/(a) is p-torsion-free.
    intro hp_not_dvd x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      intro hpy
      -- hpy : p • Submodule.Quotient.mk y = 0, i.e., a ∣ p * y.
      have hpy' : a ∣ p * y := by
        have hk : (Submodule.Quotient.mk (p * y) : R ⧸ I) = 0 := hpy
        rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
            Ideal.mem_span_singleton] at hk
        exact hk
      -- IsCoprime a p, applied to a ∣ p * y, gives a ∣ y.
      have hcop_ap : IsCoprime a p := (hp.coprime_iff_not_dvd.mpr hp_not_dvd).symm
      have hady : a ∣ y := hcop_ap.dvd_of_dvd_mul_left hpy'
      rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
          Ideal.mem_span_singleton]
      exact hady
  · -- Reverse: R/(a) p-torsion-free → ¬ p ∣ a (contrapositive).
    rintro h_tf ⟨a', rfl⟩
    -- a = p * a'; need contradiction.
    have ha' : a' ≠ 0 := fun h => ha (by rw [h, mul_zero])
    -- Take x = ⟦a'⟧ ∈ R ⧸ (p * a').
    have hpx_zero :
        (p • (Submodule.Quotient.mk a' : R ⧸ I) : R ⧸ I) = 0 := by
      change (Submodule.Quotient.mk (p * a') : R ⧸ I) = 0
      rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
          Ideal.mem_span_singleton]
    have hx_zero : (Submodule.Quotient.mk a' : R ⧸ I) = 0 := h_tf _ hpx_zero
    rw [Submodule.Quotient.mk_eq_zero, hI_def, Ideal.submodule_span_eq,
        Ideal.mem_span_singleton] at hx_zero
    -- hx_zero : p * a' ∣ a'.
    obtain ⟨k, hk⟩ := hx_zero
    -- a' = p * a' * k, so a' * (1 - p * k) = 0.
    have hzero : a' * (1 - p * k) = 0 := by
      have hexpand : a' * (1 - p * k) = a' - p * a' * k := by ring
      rw [hexpand, ← hk, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact ha' h
    · -- 1 - p * k = 0, so p * k = 1, so p is a unit; contradicts hp.not_unit.
      have hpk : p * k = 1 := (sub_eq_zero.mp h).symm
      exact hp.not_unit (IsUnit.of_mul_eq_one k hpk)

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
  set a : Λ := φ c with ha_def
  have ha_ne : a ≠ 0 := by
    intro h
    apply hc
    apply φ.injective
    rw [φ.map_zero]
    exact h
  -- Step 1: relate ∃ y, c = p • y with p ∣ a (via φ).
  have h_dvd_iff : (∃ y : E, c = p • y) ↔ p ∣ a := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      refine ⟨φ y, ?_⟩
      rw [ha_def, hy, map_smul]
      rfl
    · rintro ⟨b, hb⟩
      refine ⟨φ.symm b, ?_⟩
      have hc_eq : c = φ.symm a := (φ.symm_apply_apply c).symm
      rw [hc_eq, hb, ← smul_eq_mul, map_smul]
  -- Step 2: build the quotient iso E ⧸ span {c} ≃ₗ[Λ] Λ ⧸ span {a}.
  have h_map :
      Submodule.map (φ : E →ₗ[Λ] Λ) (Submodule.span Λ ({c} : Set E)) =
        Submodule.span Λ ({a} : Set Λ) := by
    rw [Submodule.map_span]
    simp [ha_def]
  set q : (E ⧸ Submodule.span Λ ({c} : Set E)) ≃ₗ[Λ]
            (Λ ⧸ Submodule.span Λ ({a} : Set Λ)) :=
    Submodule.Quotient.equiv (Submodule.span Λ ({c} : Set E))
      (Submodule.span Λ ({a} : Set Λ)) φ h_map with hq_def
  -- Step 3: transfer the torsion-vanishing predicate via q.
  have h_torsion_iff :
      (∀ x : E ⧸ Submodule.span Λ ({c} : Set E), p • x = 0 → x = 0) ↔
      (∀ y : Λ ⧸ Submodule.span Λ ({a} : Set Λ), p • y = 0 → y = 0) := by
    refine ⟨?_, ?_⟩
    · intro h y hpy
      have h1 : p • q.symm y = 0 := by
        rw [← q.symm.map_smul, hpy, q.symm.map_zero]
      have h2 : q.symm y = 0 := h _ h1
      calc y = q (q.symm y) := (q.apply_symm_apply y).symm
        _ = q 0 := by rw [h2]
        _ = 0 := q.map_zero
    · intro h x hpx
      have h1 : p • q x = 0 := by
        rw [← q.map_smul, hpx, q.map_zero]
      have h2 : q x = 0 := h _ h1
      calc x = q.symm (q x) := (q.symm_apply_apply x).symm
        _ = q.symm 0 := by rw [h2]
        _ = 0 := q.symm.map_zero
  -- Step 4: combine via the abstract atomic lemma.
  rw [h_torsion_iff,
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
    ∀ x : E ⧸ Submodule.span Λ ({c} : Set E), p • x = 0 → x = 0 := by
  set a : Λ := φ c
  have h_map :
      Submodule.map (φ : E →ₗ[Λ] Λ) (Submodule.span Λ ({c} : Set E)) =
        Submodule.span Λ ({a} : Set Λ) := by
    rw [Submodule.map_span]; simp [a]
  set q : (E ⧸ Submodule.span Λ ({c} : Set E)) ≃ₗ[Λ]
            (Λ ⧸ Submodule.span Λ ({a} : Set Λ)) :=
    Submodule.Quotient.equiv (Submodule.span Λ ({c} : Set E))
      (Submodule.span Λ ({a} : Set Λ)) φ h_map
  intro x hpx
  have h1 : p • q x = 0 := by rw [← q.map_smul, hpx, q.map_zero]
  have h2 : q x = 0 :=
    rankOne_quotient_p_torsion_free_of_isCoprime h_cop _ h1
  calc x = q.symm (q x) := (q.symm_apply_apply x).symm
    _ = q.symm 0 := by rw [h2]
    _ = 0 := q.symm.map_zero

end BernoulliRegular.Thaine

end
