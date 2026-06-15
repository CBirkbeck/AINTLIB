/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Topology.LocallyConstant.Basic
import PadicLFunctions.Coefficients
import PadicLFunctions.Measure.Basic

/-!
# Dirichlet characters as functions on `ℤ_p`, and Gauss sums (RJW §5.1)

A Dirichlet character `χ` of conductor `p^n` is "seen as a locally constant
character of `ℤ_p^×`" (RJW Thm 5.1, TeX 1620) — concretely, the function
`x ↦ χ (toZModPow n x)`, which vanishes on `pℤ_p` for `n ≥ 1`. Gauss sums
(RJW Def 5.2, TeX 1647–1651) are mathlib's `gaussSum χ e` at the additive
character attached to a primitive `p^n`-th root of unity; Rem 5.3(ii) is
mathlib's `gaussSum_mulShift_of_isPrimitive`, and Rem 5.3(i) at non-prime
level is `gaussSum_mul_gaussSum_inv` below (L5.1.5, a mathlib gap).
-/

namespace PadicLFunctions

variable {p : ℕ} [hp : Fact p.Prime]

section toContinuousMap

variable {R : Type*} [NormedCommRing R] {n : ℕ}

open Classical in
/-- L5.1.1: a Dirichlet character mod `p^n` as a continuous (indeed locally
constant) function `ℤ_[p] → R`, via reduction mod `p^n`. For `n ≥ 1` it
vanishes on `pℤ_[p]` (the character kills non-units).

Source (TeX 1620): "(seen as a locally constant character of `ℤ_p^×`, cf.
§`sec:dirichlet ideles`)". -/
noncomputable def _root_.DirichletCharacter.toContinuousMapZp
    (χ : DirichletCharacter R (p ^ n)) : C(ℤ_[p], R) :=
  ⟨fun x => χ (PadicInt.toZModPow n x), by
    refine IsLocallyConstant.continuous (fun s => ?_)
    have : (fun x => χ (PadicInt.toZModPow n x)) ⁻¹' s
        = ⋃ b ∈ (Finset.univ.filter fun b : ZMod (p ^ n) => χ b ∈ s),
            {x : ℤ_[p] | PadicInt.toZModPow n x = b} := by
      ext x
      simp [Set.mem_iUnion]
    rw [this]
    exact isOpen_biUnion fun b _ => PadicMeasure.isOpen_toZModPow_fiber p n b⟩

@[simp]
lemma DirichletCharacter.toContinuousMapZp_apply
    (χ : DirichletCharacter R (p ^ n)) (x : ℤ_[p]) :
    χ.toContinuousMapZp x = χ (PadicInt.toZModPow n x) := rfl

/-- For `n ≥ 1`, the function vanishes on `pℤ_[p]` (non-units reduce to
non-units mod `p^n`). Source: TeX 1752 "Since `χ` is 0 on `pℤ_p`". -/
lemma DirichletCharacter.toContinuousMapZp_eq_zero
    (χ : DirichletCharacter R (p ^ n)) (hn : 1 ≤ n) {x : ℤ_[p]}
    (hx : ¬IsUnit x) : χ.toContinuousMapZp x = 0 := by
  rw [DirichletCharacter.toContinuousMapZp_apply]
  refine χ.map_nonunit fun hu => hx ?_
  rw [PadicInt.isUnit_iff]
  by_contra hnorm
  have hdvd : (p : ℤ_[p]) ∣ x := by
    rw [← PadicInt.norm_lt_one_iff_dvd]
    exact lt_of_le_of_ne (PadicInt.norm_le_one x) hnorm
  obtain ⟨y, rfl⟩ := hdvd
  have hpu : IsUnit ((p : ZMod (p ^ n))) :=
    isUnit_of_mul_isUnit_left (y := PadicInt.toZModPow n y) (by simpa [map_mul] using hu)
  rw [ZMod.isUnit_iff_coprime] at hpu
  rw [Nat.coprime_pow_right_iff (by omega)] at hpu
  simp only [Nat.Coprime, Nat.gcd_self] at hpu
  exact absurd hpu hp.out.ne_one

/-- At a unit, the tilde-function only depends on the primitive core: the
level-raise `changeLevel` is invisible through `toZModPow`-compatibility. -/
lemma DirichletCharacter.toContinuousMapZp_changeLevel {m : ℕ} (hmn : m ≤ n)
    (hdvd : p ^ m ∣ p ^ n) (χ₀ : DirichletCharacter R (p ^ m)) {x : ℤ_[p]}
    (hx : IsUnit x) :
    (DirichletCharacter.changeLevel hdvd χ₀).toContinuousMapZp x
      = χ₀.toContinuousMapZp x := by
  have hu : IsUnit (PadicInt.toZModPow n x) := hx.map _
  rw [DirichletCharacter.toContinuousMapZp_apply,
    DirichletCharacter.toContinuousMapZp_apply, ← hu.unit_spec,
    DirichletCharacter.changeLevel_eq_cast_of_dvd χ₀ _ hu.unit, hu.unit_spec,
    PadicInt.cast_toZModPow m n hmn]

/-- Multiplicativity (`MulChar`s are unconditionally multiplicative; the
skeleton's `1 ≤ n` hypothesis was unnecessary and is dropped). -/
lemma DirichletCharacter.toContinuousMapZp_mul
    (χ : DirichletCharacter R (p ^ n)) (x y : ℤ_[p]) :
    χ.toContinuousMapZp (x * y)
      = χ.toContinuousMapZp x * χ.toContinuousMapZp y := by
  simp [map_mul]

lemma DirichletCharacter.isLocallyConstant_toContinuousMapZp
    (χ : DirichletCharacter R (p ^ n)) :
    IsLocallyConstant (χ.toContinuousMapZp : ℤ_[p] → R) := by
  classical
  refine fun s => ?_
  have : (χ.toContinuousMapZp : ℤ_[p] → R) ⁻¹' s
      = ⋃ b ∈ (Finset.univ.filter fun b : ZMod (p ^ n) => χ b ∈ s),
          {x : ℤ_[p] | PadicInt.toZModPow n x = b} := by
    ext x
    simp [Set.mem_iUnion]
  rw [this]
  exact isOpen_biUnion fun b _ => PadicMeasure.isOpen_toZModPow_fiber p n b

/-- The values of a ball-valued Dirichlet character have norm at most one
(immediate from ball-valuedness; the skeleton's general-`R` form was
vacuous — replan note in T502). -/
lemma DirichletCharacter.norm_toContinuousMapZp_le
    {K : Type*} [NormedField K] [IsUltrametricDist K]
    (χ : DirichletCharacter (integerRing K) (p ^ n)) (x : ℤ_[p]) :
    ‖χ.toContinuousMapZp x‖ ≤ 1 :=
  (χ.toContinuousMapZp x).2

end toContinuousMap

section gaussSum

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [IsDomain R]

/-- L5.1.5 (Rem 5.3(i) at general level; mathlib has the prime/field case
only): for `χ` a primitive Dirichlet character mod `N` and `e` a primitive
additive character of `ZMod N` into a domain,
`G(χ, e) · G(χ⁻¹, e⁻¹) = N`.

Source (TeX 1656, Rem 5.3(i)): "G(χ) G(χ⁻¹) = χ(−1) p^n" — the displayed
form equals this one after `e⁻¹ = e.mulShift (−1)` and Rem 5.3(ii) absorb
`χ(−1)`. Route (DS05 §4.3-style, 4 finite sums): expand `G(χ⁻¹, e⁻¹)`,
rewrite each summand by `gaussSum_mulShift_of_isPrimitive`, swap sums, and
collapse with primitive-character orthogonality `∑_b e(b·c) = N·δ_{c,0}`. -/
theorem gaussSum_mul_gaussSum_inv {χ : DirichletCharacter R N}
    (hχ : χ.IsPrimitive) {e : AddChar (ZMod N) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (N : R) := by
  classical
  rw [mul_comm, gaussSum, Finset.sum_mul]
  calc ∑ b, χ⁻¹ b * e⁻¹ b * gaussSum χ e
      = ∑ b, e⁻¹ b * gaussSum χ (e.mulShift b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum_mulShift_of_isPrimitive e hχ b]
        ring
    _ = ∑ b, ∑ a, χ a * (e (b * a) * e (-b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.mulShift_apply, AddChar.inv_apply]
        ring
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← AddChar.map_add_eq_mul]
        ring_nf
    _ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod N) : R) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.sum_mulShift _ he]
        simp [apply_ite (Nat.cast : ℕ → R)]
    _ = (N : R) := by
        simp only [sub_eq_zero, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (1 : ZMod N)]
        simp [ZMod.card]

end gaussSum

section gaussSumNorm

variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
  [IsUltrametricDist L] [CompleteSpace L]

omit [hp : Fact p.Prime] in
omit [IsUltrametricDist L] [CompleteSpace L] in
/-- Roots of unity in a normed field have norm one (the `ℂ`-version is
mathlib's `Complex.norm_eq_one_of_pow_eq_one`). -/
lemma norm_eq_one_of_pow_eq_one {x : L} {m : ℕ} (h : x ^ m = 1) (hm : m ≠ 0) :
    ‖x‖ = 1 := by
  have h1 : ‖x‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  refine le_antisymm ?_ ?_
  · by_contra hc
    push Not at hc
    exact absurd h1 (one_lt_pow₀ hc hm).ne'
  · by_contra hc
    push Not at hc
    exact absurd h1 (pow_lt_one₀ (norm_nonneg x) hc hm).ne

omit [CompleteSpace L] in
/-- For `η` primitive of conductor `D` coprime to `p` (and a primitive `D`-th
root of unity `ζ` in `L`), the Gauss sum has norm one — in particular it is a
unit of the integer ring.

Source (TeX 1798): "the Gauss sum is a `p`-adic unit (indeed, we have
`G(η)G(η⁻¹) = η(−1)D` and `D` is coprime to `p`)". Route: `‖G‖ ≤ 1` by the
ultrametric triangle inequality (root-of-unity values), and
`gaussSum_mul_gaussSum_inv` with `‖D‖ = 1` forces equality. -/
theorem norm_gaussSum_eq_one {D : ℕ} [NeZero D] {η : DirichletCharacter L D}
    (hη : η.IsPrimitive) (hD : ¬ (p : ℕ) ∣ D) {ζ : L}
    (hζ : IsPrimitiveRoot ζ D) :
    ‖gaussSum η (AddChar.zmodChar D (hζ.pow_eq_one))‖ = 1 := by
  classical
  set e : AddChar (ZMod D) L := AddChar.zmodChar D (hζ.pow_eq_one) with he
  have htot : Nat.totient D ≠ 0 := (Nat.totient_pos.2 (NeZero.pos D)).ne'
  -- any Gauss sum of a `D`-torsion pair has norm at most one
  have hval : ∀ (ψ : DirichletCharacter L D) (e' : AddChar (ZMod D) L),
      (∀ b, e' b ^ D = 1) → ‖gaussSum ψ e'‖ ≤ 1 := by
    intro ψ e' hroots
    obtain ⟨a, -, ha⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      (t := (Finset.univ : Finset (ZMod D))) Finset.univ_nonempty
      (fun a => ψ a * e' a)
    refine ha.trans ?_
    rw [norm_mul]
    have he' : ‖e' a‖ = 1 := norm_eq_one_of_pow_eq_one (L := L) (hroots a) (NeZero.ne D)
    rcases eq_or_ne (ψ a) 0 with h0 | h0
    · rw [h0, norm_zero, zero_mul]
      norm_num
    · have hu : IsUnit (a : ZMod D) := by
        by_contra hu
        exact h0 (ψ.map_nonunit hu)
      have hpow : ψ a ^ Nat.totient D = 1 := by
        rw [← map_pow]
        obtain ⟨u, rfl⟩ := hu
        rw [show ((u : ZMod D)) ^ Nat.totient D = ((u ^ Nat.totient D : (ZMod D)ˣ) : ZMod D)
            from (Units.val_pow_eq_pow_val u (Nat.totient D)).symm,
          ZMod.pow_totient, Units.val_one, map_one]
      have hψa : ‖ψ a‖ = 1 := norm_eq_one_of_pow_eq_one (L := L) hpow htot
      rw [hψa, he', mul_one]
  -- the value-torsion hypotheses for `e` and `e⁻¹`
  have hroote : ∀ b, e b ^ D = 1 := fun b => by
    rw [← AddChar.map_nsmul_eq_pow]
    have hb : (D : ℕ) • b = 0 := by
      simp [nsmul_eq_mul]
    rw [hb, AddChar.map_zero_eq_one]
  have hrootei : ∀ b, e⁻¹ b ^ D = 1 := fun b => by
    rw [AddChar.inv_apply, ← AddChar.map_nsmul_eq_pow]
    have hb : (D : ℕ) • (-b) = 0 := by
      simp [nsmul_eq_mul]
    rw [hb, AddChar.map_zero_eq_one]
  -- product formula + norm-1 of `D` force equality
  have hprod : ‖gaussSum η e‖ * ‖gaussSum η⁻¹ e⁻¹‖ = 1 := by
    rw [← norm_mul, gaussSum_mul_gaussSum_inv hη]
    · rw [show ((D : ℕ) : L) = algebraMap ℚ_[p] L ((D : ℕ) : ℚ_[p]) by
        simp [map_natCast], norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hD
    · exact AddChar.zmodChar_primitive_of_primitive_root D hζ
  have h1 := hval η e hroote
  have h2 := hval η⁻¹ e⁻¹ hrootei
  nlinarith [norm_nonneg (gaussSum η e), norm_nonneg (gaussSum η⁻¹ e⁻¹)]

end gaussSumNorm

section primitivityTransport

/-- Composing with an injective ring homomorphism preserves the factor-levels
of a Dirichlet character (via the kernel criterion
`factorsThrough_iff_ker_unitsMap`). -/
lemma _root_.DirichletCharacter.factorsThrough_ringHomComp_iff
    {R S : Type*} [CommRing R] [CommRing S] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) {f : R →+* S} (hf : Function.Injective f)
    {d : ℕ} : DirichletCharacter.FactorsThrough (χ.ringHomComp f) d
      ↔ χ.FactorsThrough d := by
  by_cases hd : d ∣ N
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    have hker : ∀ x : (ZMod N)ˣ,
        MulChar.toUnitHom (χ.ringHomComp f) x = 1 ↔ χ.toUnitHom x = 1 := by
      intro x
      rw [← Units.val_eq_one, ← Units.val_eq_one, MulChar.coe_toUnitHom,
        MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, ← map_one f]
      exact ⟨fun h => hf h, fun h => congrArg f h⟩
    constructor
    · intro h x hx
      exact MonoidHom.mem_ker.mpr ((hker x).mp (MonoidHom.mem_ker.mp (h hx)))
    · intro h x hx
      exact MonoidHom.mem_ker.mpr ((hker x).mpr (MonoidHom.mem_ker.mp (h hx)))
  · exact ⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩

/-- Primitivity of a Dirichlet character transports along injective
coefficient homomorphisms. -/
lemma _root_.DirichletCharacter.isPrimitive_ringHomComp_iff
    {R S : Type*} [CommRing R] [CommRing S] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) {f : R →+* S} (hf : Function.Injective f) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp f) ↔ χ.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive DirichletCharacter.conductor
  rw [show DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet from
    Set.ext fun d => DirichletCharacter.factorsThrough_ringHomComp_iff χ hf]

end primitivityTransport

end PadicLFunctions
