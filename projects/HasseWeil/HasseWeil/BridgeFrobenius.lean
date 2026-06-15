import HasseWeil.FormalIsogenySeries
import HasseWeil.Frobenius
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.Separability
import HasseWeil.LocalExpansion

/-!
# T-IV-BRIDGE-004: Frobenius pulled back to formal group is `T^q`

For an elliptic curve `E/F_q` with Frobenius `π : E → E`, the formal isogeny
series satisfies `formalIsogenySeries W π = PowerSeries.X^q`.

## Key result

`formalIsogenySeries_frobenius` (Silverman IV.4 / III.5.5):
The local expansion of `π.pullback(t)` at the identity is `t^q` (no higher
terms), where `t = -x/y` is the local parameter.

Proof outline:
1. `frobeniusIsog W` has `pullback f = f^q` (from `frobeniusIsog_pullback_apply`).
2. So `π.pullback (localParam W) = (localParam W)^q`.
3. Apply `localExpand` (a ring hom):
   `localExpand((localParam W)^q) = (localExpand (localParam W))^q
     = (HahnSeries.single 1 1)^q = HahnSeries.single q 1`.
4. Therefore the `n`-th formal coefficient is `1 if n = q, else 0`,
   matching `PowerSeries.X^q`.

## References
* Silverman, *The Arithmetic of Elliptic Curves*, IV.4, III.5.5
-/

open WeierstrassCurve PowerSeries LaurentSeries

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

omit [Fintype K] in
/-- `(localParam W) ^ q` pulled back through `localExpand` equals
    `HahnSeries.single q 1` (the formal `T^q`). -/
theorem localExpand_localParam_pow (q : ℕ) :
    localExpand W ((localParam W) ^ q) =
      HahnSeries.single (q : ℤ) (1 : K) := by
  rw [map_pow, localExpand_localParam]
  rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

/-- `frobeniusIsog W`'s pullback of `localParam W` is `(localParam W)^q`. -/
theorem frobeniusIsog_pullback_localParam :
    (frobeniusIsog W).pullback (localParam W) =
      (localParam W) ^ Fintype.card K :=
  frobeniusIsog_pullback_apply W (localParam W)

/-- **T-IV-BRIDGE-004** (Silverman IV.4 / III.5.5): the formal isogeny series
    of the Frobenius isogeny is `T^q`.

    The Frobenius `π : (x, y) ↦ (x^q, y^q)` translates in the local parameter
    `t = −x/y` to `t^q` (since both `x` and `y` get raised to the `q`-th power
    and the ratio becomes the ratio of powers). The `q`-th formal coefficient
    is `1`, all others are `0`. -/
@[simp] theorem formalIsogenySeries_frobenius :
    formalIsogenySeries W (frobeniusIsog W) =
      (PowerSeries.X : PowerSeries K) ^ Fintype.card K := by
  ext n
  rw [formalIsogenySeries_coeff, PowerSeries.coeff_X_pow,
      frobeniusIsog_pullback_localParam, localExpand_localParam_pow]
  by_cases h : n = Fintype.card K
  · subst h
    rw [if_pos rfl, HahnSeries.coeff_single_same]
  · rw [if_neg h, HahnSeries.coeff_single_of_ne (by exact_mod_cast h)]

/-- **Corollary**: the linear coefficient of the Frobenius formal series is
    `0` (since `q ≥ 2` for any `Fintype K`-power Frobenius on an elliptic curve
    over a finite field — but more weakly, just `q ≠ 1`). For `q = 1` the
    Frobenius is the identity which has linear coeff `1`. -/
theorem coeff_one_formalIsogenySeries_frobenius_of_card_ne_one
    (h : Fintype.card K ≠ 1) :
    PowerSeries.coeff 1 (formalIsogenySeries W (frobeniusIsog W)) = 0 := by
  rw [formalIsogenySeries_frobenius, PowerSeries.coeff_X_pow]
  exact if_neg fun heq => h heq.symm

/-! ### `omegaPullbackCoeff(π) = 0` (Frobenius is purely inseparable)

For a finite field `K` of characteristic `p`, the Frobenius map raises functions
to the `q`-th power where `q = #K = p^k`. The pullback of `D(x)` becomes
`D(x^q) = q · x^(q-1) · D(x) = 0` since `q ≡ 0 (mod p)` in `K`. By
`omegaPullbackCoeff_unique`, the omega coefficient must be `0`.

This is the direct (non-formal-series) proof of Silverman III.5.5's "Frobenius
is purely inseparable" — independent of T-IV-BRIDGE-001. -/

/-- **Frobenius pullback coefficient is `0`**: Silverman III.5.5 +
    II.4.4 in characteristic `p`. The pullback of the invariant differential
    under Frobenius vanishes because `D(x^q) = q · x^(q-1) · D(x) = 0`
    in characteristic `p` with `q = p^k`. -/
theorem omegaPullbackCoeff_frobenius :
    omegaPullbackCoeff W (frobeniusIsog W) = 0 := by
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, zero_smul]
  -- Goal: αu⁻¹ • D(α.pullback x_gen) = 0
  -- α.pullback x_gen = x_gen^(card K) by frobeniusIsog_pullback_apply
  rw [frobeniusIsog_pullback_apply W _]
  -- D(x^q) = q • x^(q-1) • D(x) (by Derivation.leibniz_pow)
  rw [Derivation.leibniz_pow]
  -- Cast q-smul to K-scalar action: q • m = (q : K) • m via Nat.cast_smul_eq_nsmul
  rw [← Nat.cast_smul_eq_nsmul (R := K) _ _]
  -- (q : K) = 0 in finite field K
  rw [FiniteField.cast_card_eq_zero, zero_smul, smul_zero]

/-- **Frobenius pulled back to invariant differential is `0`** (Silverman III.5.5).

    Direct consequence of `omegaPullbackCoeff_frobenius = 0` plus the
    witness-parametric pullbackKaehler identity. -/
theorem frobenius_pullbackKaehler_invariantDifferential :
    (frobeniusIsog W).pullbackKaehler (invariantDifferential W.toAffine) = 0 := by
  have h := pullbackKaehler_invariantDifferential_of_coeff_witness W
    (frobeniusIsog W) 0
    (by rw [omegaPullbackCoeff_frobenius]; exact (map_zero _).symm)
  rw [h, zero_smul]

/-- **Frobenius is purely inseparable** (Silverman III.5.5 + II.4.4): the
    pullback coefficient vanishes, so by T-II-4-004 (separability iff coeff ≠ 0),
    `frobeniusIsog W` is *not* separable.

    Witness-parametric: takes T-II-4-004's separability ↔ coeff ≠ 0 criterion
    as input. With this, the contrapositive gives `¬ IsSeparable π`. -/
theorem not_isSeparable_frobenius_of_witness
    (h_sep_iff : (frobeniusIsog W).IsSeparable ↔
      omegaPullbackCoeff W (frobeniusIsog W) ≠ 0) :
    ¬ (frobeniusIsog W).IsSeparable := by
  rw [h_sep_iff, omegaPullbackCoeff_frobenius]
  exact fun h => h rfl

/-! ### `m + n·π` chain witness closer (Silverman III.5.5)

Given an isogeny `β` whose ω-pullback coefficient is the additive sum
`m · a_id + n · a_π`, the new fact `omegaPullbackCoeff_frobenius = 0`
collapses this to `m · 1 = m`. This closes T-III-5-005's coefficient
formula assuming additivity for the specific `(m·id + n·π)` family. -/

/-- **Witness closer for `omegaPullbackCoeff (m·id + n·π) = m`**: takes
    additivity of `omegaPullbackCoeff` for the specific isogeny `β` and
    `id, π` summands as input, plus the witness identification of `β` with
    the formal sum, and produces the closed-form coefficient identity `= m`.

    Combines `omegaPullbackCoeff_of_pullback_eq_id` (for `a_id = 1`),
    `omegaPullbackCoeff_frobenius` (for `a_π = 0`), and the additivity
    hypothesis. -/
theorem omegaPullbackCoeff_m_plus_n_frob_of_witness
    (β : Isogeny W.toAffine W.toAffine)
    (m n : ℤ)
    (h_sum_coeff : omegaPullbackCoeff W β =
      (m : W.toAffine.FunctionField) * omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        (n : W.toAffine.FunctionField) * omegaPullbackCoeff W (frobeniusIsog W)) :
    omegaPullbackCoeff W β = (m : W.toAffine.FunctionField) := by
  rw [h_sum_coeff]
  have h_id : omegaPullbackCoeff W (Isogeny.id W.toAffine) = 1 :=
    omegaPullbackCoeff_of_pullback_eq_id W (Isogeny.id W.toAffine) rfl
  rw [h_id, omegaPullbackCoeff_frobenius, mul_one, mul_zero, add_zero]

/-- **BRIDGE-001 for Frobenius (axiom-clean)**: the bridge identity holds for
the Frobenius isogeny — both sides equal `0` (when `Fintype.card K ≠ 1`,
which holds in particular for `Fintype.card K ≥ 2`).

Direct from `omegaPullbackCoeff_frobenius = 0` +
`coeff_one_formalIsogenySeries_frobenius_of_card_ne_one`. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius
    (h : Fintype.card K ≠ 1) :
    omegaPullbackCoeff W (frobeniusIsog W) =
      algebraMap K W.toAffine.FunctionField
        (PowerSeries.coeff 1 (formalIsogenySeries W (frobeniusIsog W))) := by
  rw [coeff_one_formalIsogenySeries_frobenius_of_card_ne_one W h, map_zero]
  exact omegaPullbackCoeff_frobenius W

end HasseWeil
