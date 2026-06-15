/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Differentials
import HasseWeil.Curves.InseparableDegree
import HasseWeil.EC.IsogenyKernel
import HasseWeil.Frobenius
import HasseWeil.InvariantDifferentialPullback
import HasseWeil.PullbackCoeff
import HasseWeil.RouteBGeneral

/-!
# Witness-parametric Silverman III.5.5 and V.1.2

Silverman III.5.5: for an elliptic curve `E/F_q` with `q`-power Frobenius `π` and
integers `m, n`, the isogeny `m + n·π` is separable iff `p ∤ m`.

The (unconditional) Silverman proof chains:
1. III.5.2 additivity  `(φ+ψ)*ω = φ*ω + ψ*ω`
2. III.5.3 scalar      `[m]*ω = m·ω`
3. II.2.14 + II.4.4    `π* ω = 0`  (Frobenius is purely inseparable)
4. II.4.4              separability ⇔ pullback of `ω` nonzero

Steps 1–3 give `(m + n·π)* ω = m · ω`, i.e. the ω-pullback coefficient is
`(m : F_q)`. Step 4 then gives separability ⇔ `m ≠ 0` in `F_q` ⇔ `¬ p ∣ m`.

Those steps are currently blocked (T-III-5-002 OPEN, T-III-5-003 PARTIAL,
T-II-4-004 OPEN), so this file provides *witness-parametric* closures:

* `isSeparable_iff_of_coeff_witness` — given the ω-pullback coefficient of `β`
  as `algebraMap F _ c` and the T-II-4-004 criterion for `β`, concludes
  `β.IsSeparable ↔ c ≠ 0`.
* `m_plus_n_frob_isSeparable_iff_of_witness` — specialization with coefficient
  `(m : K)` (mirrors Silverman III.5.5 for `m + n·π`).
* `oneSubFrobeniusIsog_isSeparable_of_witness` — specialization with `m = 1,
  n = -1` (T-V-1-002, `1 − π` separable).

Each uses the same design as existing `_of_witness` theorems
(`pointCount_eq_of_witness`, `degree_quadratic_nonneg_of_witness`): the caller
supplies the key external fact; this file chains it to the separability
conclusion by pure rewriting.

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], III.5.5, V.1.2.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Witness-parametric Silverman III.5.5 (coefficient form)**.

Given `β : Isogeny E E` and `c : F`, suppose:
* the ω-pullback coefficient of `β` is `algebraMap F _ c`;
* separability of `β` is equivalent to the ω-pullback coefficient being nonzero
  (this is T-II-4-004 specialized to `β`).

Then `β.IsSeparable ↔ c ≠ 0` in `F`.

Reference: Silverman III.5.5. -/
theorem isSeparable_iff_of_coeff_witness
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (β : Isogeny W.toAffine W.toAffine) (c : F)
    (h_coeff : omegaPullbackCoeff W β =
      algebraMap F W.toAffine.FunctionField c)
    (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) :
    β.IsSeparable ↔ c ≠ 0 := by
  rw [h_sep_iff, h_coeff,
    map_ne_zero_iff _ (algebraMap F W.toAffine.FunctionField).injective]

/-- **Witness-parametric Silverman III.5.5 for `m + n·π`**.

Given an endomorphism isogeny `β` whose ω-pullback coefficient is `(m : K)` (in
the algebra-map sense), and given the T-II-4-004 criterion for `β`,
`β.IsSeparable ↔ (m : K) ≠ 0`. When `K` has characteristic `p`, the right-hand
side is equivalent to `¬ (p : ℤ) ∣ m` via `CharP.intCast_eq_zero_iff`.

Callers are expected to produce `h_coeff` from the additivity + scalar + Frobenius-
inseparable chain; a natural witness is `β = isogSmulSub π (-m) (-n)` once the
genuine pullback of `m·id + n·π` is available.

Reference: Silverman III.5.5. -/
theorem m_plus_n_frob_isSeparable_iff_of_witness
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (m : ℤ)
    (β : Isogeny W.toAffine W.toAffine)
    (h_coeff : omegaPullbackCoeff W β =
      algebraMap K W.toAffine.FunctionField m)
    (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) :
    β.IsSeparable ↔ (m : K) ≠ 0 :=
  isSeparable_iff_of_coeff_witness W β (m : K) h_coeff h_sep_iff

/-- **Witness-parametric Silverman V.1.2 (`1 − π` separable)**.

Given a witness isogeny `β` (the "true" `1 − π`) whose ω-pullback coefficient is
`1` in `K(E)` and satisfies the T-II-4-004 separability criterion, `β` is
separable. The hypothesis `h_coeff : omegaPullbackCoeff W β = 1` is the
Silverman III.5.3 result at `m = 1` (combined with III.5.2 additivity applied
to the decomposition `1 + (-1)·π`, using `π* ω = 0`).

Reference: Silverman V.1.2 (uses III.5.5 with `m = 1, n = -1`). -/
theorem oneSubFrobenius_isSeparable_of_witness
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (β : Isogeny W.toAffine W.toAffine)
    (h_coeff : omegaPullbackCoeff W β = 1)
    (h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0) :
    β.IsSeparable := by
  have h_coeff' : omegaPullbackCoeff W β =
      algebraMap K W.toAffine.FunctionField (1 : K) := by
    rw [h_coeff, map_one]
  exact (isSeparable_iff_of_coeff_witness W β 1 h_coeff' h_sep_iff).mpr one_ne_zero

/-- **Witness-parametric pullback of ω**: if `omegaPullbackCoeff W α =
    algebraMap F _ c`, then `α* ω = c • ω` in `Ω[K(E)/F]`. Instantiating at
    `c = (m : F)` gives Silverman III.5.3 (`[m]* ω = m · ω`) and at `c = 1`
    gives III.5.1 (translation invariance `τ_Q* ω = ω`). -/
theorem pullbackKaehler_invariantDifferential_of_coeff_witness
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine) (c : F)
    (h_coeff : omegaPullbackCoeff W α =
      algebraMap F W.toAffine.FunctionField c) :
    α.pullbackKaehler (invariantDifferential W.toAffine) =
      c • invariantDifferential W.toAffine := by
  rw [Isogeny.pullbackKaehler_invariantDifferential, h_coeff, algebraMap_smul]

/-- **Witness-parametric Silverman III.5.3**: `[m]*ω = m·ω`.
    Direct instantiation of `pullbackKaehler_invariantDifferential_of_coeff_witness`
    with `c = (m : F)`. -/
theorem mulByInt_pullbackKaehler_invariantDifferential_of_witness
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (m : ℤ)
    (h_coeff : omegaPullbackCoeff W (mulByInt W.toAffine m) =
      algebraMap F W.toAffine.FunctionField m) :
    (mulByInt W.toAffine m).pullbackKaehler (invariantDifferential W.toAffine) =
      (m : F) • invariantDifferential W.toAffine :=
  pullbackKaehler_invariantDifferential_of_coeff_witness W (mulByInt W.toAffine m)
    (m : F) h_coeff

/-- **Witness-parametric Silverman III.5.1** (translation invariance): if
    `omegaPullbackCoeff W τ_Q = 1` (the characterizing property of translations
    preserving ω), then `τ_Q* ω = ω`. Direct instantiation of
    `pullbackKaehler_invariantDifferential_of_coeff_witness` with `c = 1`. -/
theorem translation_pullbackKaehler_invariantDifferential_of_witness
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (τ : Isogeny W.toAffine W.toAffine)
    (h_coeff : omegaPullbackCoeff W τ = 1) :
    τ.pullbackKaehler (invariantDifferential W.toAffine) =
      invariantDifferential W.toAffine := by
  have h_coeff' : omegaPullbackCoeff W τ =
      algebraMap F W.toAffine.FunctionField (1 : F) := by
    rw [h_coeff, map_one]
  rw [pullbackKaehler_invariantDifferential_of_coeff_witness W τ 1 h_coeff',
      one_smul]

/-- **Witness-parametric Silverman III.5.4 (`[m]` separable when `m ≠ 0` in K)**.

For `m : ℤ` nonzero in `K`, the multiplication-by-`m` isogeny `[m]` is separable,
given its ω-pullback coefficient `= algebraMap K _ m` (T-III-5-003 for the
`[m]` case) and the T-II-4-004 separability criterion.

The coefficient hypothesis is discharged by the axiom-clean field-general
Route-B chain `omegaCoeff_mulByInt` (`RouteBGeneral.lean`, for `m ≠ 0 : ℤ`);
passing it as a hypothesis here keeps the present theorem parametric.

Reference: Silverman III.5.4. -/
theorem mulByInt_isSeparable_of_witness
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (m : ℤ) (hm : (m : K) ≠ 0)
    (h_coeff : omegaPullbackCoeff W (mulByInt W.toAffine m) =
      algebraMap K W.toAffine.FunctionField m)
    (h_sep_iff : (mulByInt W.toAffine m).IsSeparable ↔
      omegaPullbackCoeff W (mulByInt W.toAffine m) ≠ 0) :
    (mulByInt W.toAffine m).IsSeparable :=
  (m_plus_n_frob_isSeparable_iff_of_witness W m _ h_coeff h_sep_iff).mpr hm

/-- **T-FROB-OMEGA-ZERO**: in characteristic `p`, the ω-pullback coefficient of
    `[p]` vanishes. One-line corollary of the axiom-clean `omegaCoeff_mulByInt`
    (`RouteBGeneral.lean`) and `CharP.cast_eq_zero`. -/
theorem omegaPullbackCoeff_mulByNat_p_eq_zero
    {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [CharP k p] [Fact (Nat.Prime p)]
    (E : WeierstrassCurve k) [E.toAffine.IsElliptic] :
    omegaPullbackCoeff E (mulByInt E.toAffine (p : ℤ)) = 0 := by
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (p : ℕ).Prime).pos.ne'
  rw [omegaCoeff_mulByInt E (p : ℤ) hp_ne,
    show ((p : ℤ) : k) = 0 by rw [Int.cast_natCast]; exact CharP.cast_eq_zero k p]
  exact map_zero _

/-- In characteristic `p`, the ω-pullback coefficient of `[p]` vanishes (alias of
`omegaPullbackCoeff_mulByNat_p_eq_zero`). -/
theorem mulByInt_p_omega_pullback_eq_zero
    {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [CharP k p] [Fact p.Prime]
    (E : WeierstrassCurve k) [E.toAffine.IsElliptic] :
    omegaPullbackCoeff E (mulByInt E.toAffine (p : ℤ)) = 0 :=
  omegaPullbackCoeff_mulByNat_p_eq_zero p E

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The **inseparable degree** of an isogeny, `deg_i φ = deg φ / deg_s φ`.
Silverman II.2.10. -/
noncomputable def inseparableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  φ.degree / φ.sepDegree

/-- `IsSeparable ↔ inseparableDegree = 1`: under `FiniteDimensional`, this is
`Field.finSepDegree_eq_finrank_iff` plus the multiplicativity of the
separable/inseparable decomposition. -/
theorem inseparableDegree_eq_one_iff_isSeparable (φ : Isogeny W₁ W₂)
    (hfin : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _
      φ.toAlgebra.toModule) :
    φ.inseparableDegree = 1 ↔ φ.IsSeparable := by
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.toAlgebra
  rw [show φ.IsSeparable ↔ φ.sepDegree = φ.degree from
    isSeparable_iff_sepDegree_eq_degree φ hfin]
  have h_mul : φ.sepDegree * Field.finInsepDegree W₂.FunctionField W₁.FunctionField =
      φ.degree := by
    change @Field.finSepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra *
        @Field.finInsepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra =
        @Module.finrank W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra.toModule
    exact Field.finSepDegree_mul_finInsepDegree _ _
  have h_sep_pos : 0 < φ.sepDegree := by
    change 0 < @Field.finSepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra
    exact Nat.pos_of_ne_zero (@NeZero.ne _ _ _
      (@Field.instNeZeroFinSepDegree _ _ _ _ φ.toAlgebra hfin))
  constructor
  · intro h_insep_one
    show φ.sepDegree = φ.degree
    change φ.degree / φ.sepDegree = 1 at h_insep_one
    have h_sep_dvd : φ.sepDegree ∣ φ.degree := by
      rw [← h_mul]; exact Dvd.intro _ rfl
    obtain ⟨k, hk⟩ := h_sep_dvd
    rw [hk, Nat.mul_div_cancel_left _ h_sep_pos] at h_insep_one
    rw [hk, h_insep_one, mul_one]
  · intro h_eq
    change φ.degree / φ.sepDegree = 1
    rw [← h_eq, Nat.div_self h_sep_pos]

/-- **`HasseWeil.Isogeny.inseparableDegree_isPow_of_charP`** (parallel of P0-A):
in characteristic `p`, the inseparable degree of any nonzero-degree isogeny
is `p^e` for some `e ≥ 0`. Uses mathlib's `Field.finInsepDegree_eq_pow`. -/
theorem inseparableDegree_isPow_of_charP
    {K : Type*} [Field K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W : WeierstrassCurve K} [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine)
    (h_deg_pos : 0 < α.degree) :
    ∃ e : ℕ, α.inseparableDegree = p ^ e := by
  letI alg : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  haveI : CharP W.toAffine.FunctionField p :=
    charP_of_injective_algebraMap
      (algebraMap K W.toAffine.FunctionField).injective p
  haveI : ExpChar W.toAffine.FunctionField p := ExpChar.prime Fact.out
  haveI hfin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ alg.toModule :=
    @FiniteDimensional.of_finrank_pos _ _ _ _ alg.toModule h_deg_pos
  obtain ⟨e, he⟩ : ∃ n, @Field.finInsepDegree W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ alg = p ^ n := by
    exact finInsepDegree_eq_pow (F := W.toAffine.FunctionField)
      (E := W.toAffine.FunctionField) p
  have h_sep_pos : 0 < α.sepDegree := by
    change 0 < @Field.finSepDegree W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ alg
    exact Nat.pos_of_ne_zero
      (@NeZero.ne _ _ _ (@Field.instNeZeroFinSepDegree _ _ _ _ alg hfin))
  refine ⟨e, ?_⟩
  change α.degree / α.sepDegree = p ^ e
  have h_mul : α.sepDegree * Field.finInsepDegree
      W.toAffine.FunctionField W.toAffine.FunctionField = α.degree := by
    change @Field.finSepDegree W.toAffine.FunctionField W.toAffine.FunctionField
        _ _ alg * @Field.finInsepDegree W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ alg =
        @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
          alg.toModule
    exact Field.finSepDegree_mul_finInsepDegree _ _
  rw [← h_mul, Nat.mul_div_cancel_left _ h_sep_pos]
  exact he

end Isogeny

/-- In characteristic `p`, multiplication-by-`p` is inseparable (Silverman
III.5.6(b)): `[p]` lies in the kernel of `φ ↦ a_φ` since its ω-pullback
coefficient vanishes. -/
theorem mulByInt_p_not_isSeparable
    {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [CharP k p] [Fact p.Prime]
    (E : WeierstrassCurve k) [E.toAffine.IsElliptic] :
    ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable := by
  intro h_sep
  exact isogeny_omegaCoeff_ne_zero_of_isSeparable E (mulByInt E.toAffine (p : ℤ)) h_sep
    (mulByInt_p_omega_pullback_eq_zero p E)

/-- In characteristic `p`, the inseparable degree of `[p]` is a non-trivial power
of `p` (i.e. `p^e` with `1 ≤ e`); Silverman III.4.2(a) + II.2.11, with the
exponent positive because `[p]` is inseparable. -/
theorem mulByInt_p_inseparableDegree_eq_pow
    {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [CharP k p] [Fact p.Prime]
    (E : WeierstrassCurve k) [E.toAffine.IsElliptic] :
    ∃ e : ℕ, 1 ≤ e ∧ (mulByInt E.toAffine (p : ℤ)).inseparableDegree = p ^ e := by
  have hp_prime : p.Prime := Fact.out
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp_prime.pos.ne'
  have h_deg_pos : 0 < (mulByInt E.toAffine (p : ℤ)).degree :=
    mulByInt_degree_pos E.toAffine hp_ne
  obtain ⟨e, he⟩ := Isogeny.inseparableDegree_isPow_of_charP
    p (mulByInt E.toAffine (p : ℤ)) h_deg_pos
  have hfin : @FiniteDimensional E.toAffine.FunctionField E.toAffine.FunctionField
      _ _ (mulByInt E.toAffine (p : ℤ)).toAlgebra.toModule :=
    @FiniteDimensional.of_finrank_pos _ _ _ _
      (mulByInt E.toAffine (p : ℤ)).toAlgebra.toModule h_deg_pos
  have h_not_sep : ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable :=
    mulByInt_p_not_isSeparable p E
  have h_not_one : (mulByInt E.toAffine (p : ℤ)).inseparableDegree ≠ 1 := fun h ↦
    h_not_sep ((Isogeny.inseparableDegree_eq_one_iff_isSeparable _ hfin).mp h)
  refine ⟨e, ?_, he⟩
  by_contra! h_lt
  interval_cases e
  rw [pow_zero] at he
  exact h_not_one he

namespace Conditional

/-- **T-FROB-INSEP (witness-parametric on algebra-Kähler iff)**: in
    characteristic `p`, `[p]` is inseparable, given the algebra-Kähler bridge
    witness `IsSeparable [p] ↔ pullbackKaehler [p] injective`. The substantive
    input is Silverman II.4.2(c) (the differentials proposition; Silverman's
    III.6.1 Case 2 cites it as "III.4.2c", a second-edition typo). -/
theorem mulByNat_p_not_isSeparable_of_algKaehler_witness
    {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [CharP k p] [Fact (Nat.Prime p)]
    (E : WeierstrassCurve k) [E.toAffine.IsElliptic]
    (h_alg : (mulByInt E.toAffine (p : ℤ)).IsSeparable ↔
      Function.Injective (mulByInt E.toAffine (p : ℤ)).pullbackKaehler) :
    ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable := by
  intro h_sep
  have h_iff := isSeparable_iff_omegaPullbackCoeff_ne_zero_of_algKaehler E
    (mulByInt E.toAffine (p : ℤ)) h_alg
  exact (h_iff.mp h_sep) (omegaPullbackCoeff_mulByNat_p_eq_zero p E)

end Conditional

end HasseWeil
