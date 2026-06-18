# Inventory: ./HasseWeil/FormalIsogenySeries.lean

**File**: `HasseWeil/FormalIsogenySeries.lean`
**Lines**: 1905
**Total declarations**: 51 (1 noncomputable def + 50 theorems)
**Sorries**: `omegaPullbackCoeff_eq_formalIsogenyLeading`, `formalIsogenySeries_add`
**set_option maxHeartbeats**: none

---

## Section: Definition

### `noncomputable def formalIsogenySeries`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) : PowerSeries F`
- **What**: Defines the formal isogeny series of an isogeny `α`: the power series whose `n`-th coefficient is the `n`-th Laurent-series coefficient of `localExpand W (α.pullback (localParam W))`, i.e. the local `t`-adic expansion of the pullback of the local parameter `t = -x/y` at `O`.
- **How**: Direct `PowerSeries.mk` wrapping `HahnSeries.coeff` at integer index `(n : ℤ)`. No mathematical argument; it truncates away any negative-order terms (for pathological isogenies).
- **Hypotheses**: `W : WeierstrassCurve F`, `F` a field with `DecidableEq`, `W.toAffine.IsElliptic`.
- **Uses from project**: `localExpand`, `localParam`
- **Used by**: `formalIsogenySeries_coeff`, `constantCoeff_formalIsogenySeries_of_orderTop_pos`, `order_formalIsogenySeries_pos_of_orderTop_pos`, `omegaPullbackCoeff_eq_formalIsogenyLeading`, `formalIsogenySeries_add`, and many others throughout the file.
- **Visibility**: public
- **Lines**: 63–66 (4 lines of body)
- **Notes**: none

---

### `@[simp] theorem formalIsogenySeries_coeff`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) (n : ℕ) : PowerSeries.coeff n (formalIsogenySeries W α) = (localExpand W (α.pullback (localParam W))).coeff (n : ℤ)`
- **What**: The `n`-th coefficient of `formalIsogenySeries W α` is the `n`-th Laurent-series coefficient of the local expansion of `α.pullback t`.
- **How**: Unfolds `formalIsogenySeries` and applies `PowerSeries.coeff_mk`.
- **Hypotheses**: Same as `formalIsogenySeries`.
- **Uses from project**: `formalIsogenySeries`
- **Used by**: `constantCoeff_formalIsogenySeries_of_orderTop_pos`, `formalIsogenySeries_id`, `formalIsogenySeries_mulByInt_one`, `formalIsogenySeries_coeff_one_via_bridge_003`
- **Visibility**: public (`@[simp]`)
- **Lines**: 70–75 (6 lines including type)
- **Notes**: none

---

## Section: Constant coefficient / positive order

### `theorem constantCoeff_formalIsogenySeries_of_orderTop_pos`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) (h_orderTop : 0 < (localExpand W (α.pullback (localParam W))).orderTop) : PowerSeries.constantCoeff (formalIsogenySeries W α) = 0`
- **What**: For a genuine isogeny (pullback of `t` vanishes at `O`, i.e. `orderTop > 0`), the formal isogeny series has zero constant term.
- **How**: Rewrites via `formalIsogenySeries_coeff` at `n = 0`, then applies `HahnSeries.coeff_eq_zero_of_lt_orderTop` to derive that the 0-th Laurent coefficient vanishes.
- **Hypotheses**: Positive `orderTop` of the local expansion (the genuine-isogeny / `α(O) = O` condition).
- **Uses from project**: `formalIsogenySeries_coeff`
- **Used by**: `order_formalIsogenySeries_pos_of_orderTop_pos`
- **Visibility**: public
- **Lines**: 98–107 (10 lines)
- **Notes**: none

---

### `theorem order_formalIsogenySeries_pos_of_orderTop_pos`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) (h_orderTop : 0 < (localExpand W (α.pullback (localParam W))).orderTop) : 0 < (formalIsogenySeries W α).order`
- **What**: For a genuine isogeny, the formal isogeny series has positive `PowerSeries.order` (equivalently, zero constant term).
- **How**: Converts via `PowerSeries.order_ne_zero_iff_constCoeff_eq_zero` and delegates to `constantCoeff_formalIsogenySeries_of_orderTop_pos`.
- **Hypotheses**: Positive `orderTop` hypothesis.
- **Uses from project**: `constantCoeff_formalIsogenySeries_of_orderTop_pos`
- **Used by**: `order_formalIsogenySeries_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 114–120 (7 lines)
- **Notes**: none

---

## Section: Formal group law coefficient lemmas

### `theorem formalGroupLaw_coeff_single_zero_one`
- **Type**: `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (formalGroupLaw W).toMvPowerSeries = 1`
- **What**: The `(1,0)` coefficient (coefficient of `X₀^1 · X₁^0`) of the formal group law is `1`.
- **How**: Reduces to `formalGroupLaw_coeff` evaluation using `simp` after computing the `Finsupp` values.
- **Hypotheses**: Only `W : WeierstrassCurve F` (no `DecidableEq` or `IsElliptic` needed; `omit`-ted).
- **Uses from project**: `formalGroupLaw_coeff`
- **Used by**: `coeff_one_subst_bivariate`, `formalIsogenySeries_add_coeff_one_via_FGL`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`
- **Visibility**: public
- **Lines**: 129–137 (9 lines with `omit`)
- **Notes**: none

---

### `theorem formalGroupLaw_coeff_single_one_one`
- **Type**: `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (formalGroupLaw W).toMvPowerSeries = 1`
- **What**: The `(0,1)` coefficient of the formal group law is `1`.
- **How**: Same as `formalGroupLaw_coeff_single_zero_one` by symmetry.
- **Hypotheses**: Only `W` (no `DecidableEq` or `IsElliptic`).
- **Uses from project**: `formalGroupLaw_coeff`
- **Used by**: `coeff_one_subst_bivariate`, `formalIsogenySeries_add_coeff_one_via_FGL`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`
- **Visibility**: public
- **Lines**: 139–147 (9 lines with `omit`)
- **Notes**: none

---

### `theorem constantCoeff_formalGroupLaw`
- **Type**: `MvPowerSeries.constantCoeff (σ := Fin 2) (R := F) (formalGroupLaw W).toMvPowerSeries = 0`
- **What**: The constant coefficient of the formal group law is `0` (formal group law has no constant term).
- **How**: Evaluates `formalGroupLaw_coeff` at the zero multi-index via `simp`.
- **Hypotheses**: Only `W` (no `DecidableEq` or `IsElliptic`).
- **Uses from project**: `formalGroupLaw_coeff`
- **Used by**: `constantCoeff_subst_bivariate_eq_zero`, `order_formalGroupLaw_subst_pos`, `coeff_one_subst_bivariate`, `formalIsogenySeries_add_coeff_zero_via_genuine`, `formalIsogenySeries_add_coeff_one_via_FGL`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`, `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
- **Visibility**: public
- **Lines**: 149–157 (9 lines with `omit`)
- **Notes**: keyApi (used by 8+ declarations in this file)

---

## Section: Generic coefficient-1 substitution lemma

### `theorem coeff_one_subst_bivariate`
- **Type**: `(S : MvPowerSeries (Fin 2) F) (hS10 : coeff (Finsupp.single 0 1) S = 1) (hS01 : coeff (Finsupp.single 1 1) S = 1) (hS00 : constantCoeff S = 0) (f g : PowerSeries F) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : coeff 1 (MvPowerSeries.subst (![f, g]) S) = coeff 1 f + coeff 1 g`
- **What**: For a bivariate series `S` with `S(1,0) = S(0,1) = 1` and `S(0,0) = 0`, and `f, g` with zero constant coefficient, the coefficient of `T^1` in `S(f(T), g(T))` equals `coeff 1 f + coeff 1 g`. This is the formal-group-law linearity at degree 1.
- **How**: Uses `MvPowerSeries.coeff_subst` to expand, then reduces the sum over multi-indices by showing that all monomials of total degree `≥ 2` contribute zero to the degree-1 coefficient (via `PowerSeries.X_pow_dvd_iff`), and multi-index 0 contributes zero (via `hS00`), leaving only the two degree-1 terms. Uses `finsum_eq_finset_sum_of_support_subset` and `Finset.sum_pair`.
- **Hypotheses**: Purely algebraic coefficient identities on `S`; zero constant coefficients on `f, g`.
- **Uses from project**: none (purely mathlib)
- **Used by**: `formalIsogenySeries_add_coeff_one_via_FGL`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
- **Visibility**: public
- **Lines**: 176–248 (73 lines of proof)
- **Notes**: Proof > 30 lines (97 lines total span). Self-contained; replaces the `coeff_one_fAdd` from `FormalGroup/Definition.lean` without requiring a `FormalGroup F` structure.

---

## Section: Formal group law preserves positive order

### `theorem constantCoeff_subst_bivariate_eq_zero`
- **Type**: `(S : MvPowerSeries (Fin 2) F) (hS00 : constantCoeff S = 0) (f g : PowerSeries F) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) : constantCoeff (MvPowerSeries.subst (![f, g]) S) = 0`
- **What**: Substituting two power series with zero constant coefficient into a bivariate series with zero constant term yields zero constant term. A thin specialization of `MvPowerSeries.constantCoeff_subst_eq_zero`.
- **How**: Constructs `MvPowerSeries.HasSubst` via `hasSubst_of_constantCoeff_zero`, then applies `MvPowerSeries.constantCoeff_subst_eq_zero`.
- **Hypotheses**: Zero constant terms on all three series.
- **Uses from project**: none (purely mathlib)
- **Used by**: `order_subst_bivariate_pos`, `formalIsogenySeries_add_coeff_zero_via_genuine`, `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`
- **Visibility**: public
- **Lines**: 267–287 (21 lines, with `omit`)
- **Notes**: none

---

### `theorem order_subst_bivariate_pos`
- **Type**: `(S : MvPowerSeries (Fin 2) F) (hS00 : constantCoeff S = 0) (f g : PowerSeries F) (hf : 0 < order f) (hg : 0 < order g) : 0 < order (MvPowerSeries.subst (![f, g]) S)`
- **What**: Substituting two positive-order power series into a bivariate series with zero constant term yields positive order. This is the formal-power-series form of the formal group subgroup property.
- **How**: Converts `0 < order` to `constantCoeff = 0` (via `PowerSeries.one_le_order_iff_constCoeff_eq_zero`), applies `constantCoeff_subst_bivariate_eq_zero`, then converts back.
- **Hypotheses**: Zero constant term on `S`; positive order on `f, g`.
- **Uses from project**: `constantCoeff_subst_bivariate_eq_zero`
- **Used by**: `order_formalGroupLaw_subst_pos`
- **Visibility**: public
- **Lines**: 289–314 (26 lines, with `omit`)
- **Notes**: none

---

### `theorem order_formalGroupLaw_subst_pos`
- **Type**: `(f g : PowerSeries F) (hf : 0 < order f) (hg : 0 < order g) : 0 < order (MvPowerSeries.subst (![f, g]) (formalGroupLaw W).toMvPowerSeries)`
- **What**: Substituting two positive-order power series into the elliptic curve's formal group law yields positive order. The concrete specialization of `order_subst_bivariate_pos` to `formalGroupLaw W`.
- **How**: Delegates to `order_subst_bivariate_pos` using `constantCoeff_formalGroupLaw`.
- **Hypotheses**: Positive order on `f, g`.
- **Uses from project**: `constantCoeff_formalGroupLaw`
- **Used by**: `orderTop_localExpand_z_sum_pos_of_iv14_identity`
- **Visibility**: public
- **Lines**: 316–327 (12 lines, with `omit`)
- **Notes**: none

---

## Section: T-IV-BRIDGE-001

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) : omegaPullbackCoeff W α = algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W α))`
- **What**: The omega pullback coefficient of `α` equals (the image of) the linear coefficient of its formal isogeny series. This is Silverman IV.4.3: the invariant differential scales by the same factor as the leading term of the formal series.
- **How**: **SORRY** — the mathematical content (identifying the Kähler-module coefficient with the Laurent-series coefficient) is not yet proved.
- **Hypotheses**: Any isogeny `α`.
- **Uses from project**: `omegaPullbackCoeff`, `formalIsogenySeries`
- **Used by**: `omegaPullbackCoeff_add_via_bridge_of_constCoeff` (uses this sorry-carrying result)
- **Visibility**: public
- **Lines**: 351–355 (5 lines; proof = `sorry`)
- **Notes**: **SORRY.** Key bridge lemma (T-IV-BRIDGE-001). Its sorry propagates to `omegaPullbackCoeff_add_via_bridge_of_constCoeff`.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_of_witness`
- **Type**: Takes `c : F`, `h_const : omegaPullbackCoeff W α = algebraMap F KE c`, `h_match : c = coeff 1 (formalIsogenySeries W α)` and concludes `omegaPullbackCoeff W α = algebraMap F KE (coeff 1 (formalIsogenySeries W α))`.
- **What**: A witness-parametric form of BRIDGE-001: given both III.1.5 (omega coefficient lies in `algebraMap F`) and IV.4.3 (it matches the formal series coefficient), the BRIDGE-001 identity follows by substitution.
- **How**: `rw [h_const, h_match]` — purely a composition.
- **Hypotheses**: A witness `c : F` with both identification hypotheses.
- **Uses from project**: `omegaPullbackCoeff`, `formalIsogenySeries`
- **Used by**: unused in file (intended for downstream callers)
- **Visibility**: public
- **Lines**: 380–386 (7 lines)
- **Notes**: Intended API helper; dead code within this file.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_of_constant_witness`
- **Type**: Takes `c : F`, `h_omega_const : omegaPullbackCoeff W α = algebraMap F KE c`, `h_formal_const : coeff 1 (formalIsogenySeries W α) = c` and concludes BRIDGE-001.
- **What**: Equivalent to `omegaPullbackCoeff_eq_formalIsogenyLeading_of_witness` with swapped direction of `h_formal_const`.
- **How**: `rw [h_omega_const, h_formal_const]`.
- **Hypotheses**: Same as previous witness form.
- **Uses from project**: `omegaPullbackCoeff`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 408–414 (7 lines)
- **Notes**: Slight variant of the previous; both are dead code within the file.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_add_witness`
- **Type**: Takes `α β γ`, witnesses `c_α c_β : F`, hypotheses `h_α`, `h_β` (BRIDGE-001 for α, β), `h_omega_add` (omega coefficient additivity), `h_formal_add` (formal series leading coefficient additivity), `h_α_match`, `h_β_match` and concludes BRIDGE-001 for γ.
- **What**: Chains BRIDGE-001 for summands to BRIDGE-001 for the sum, given additivity witnesses on both sides.
- **How**: `rw [h_omega_add, h_α, h_β, h_formal_add, map_add, h_α_match, h_β_match]`.
- **Hypotheses**: BRIDGE-001 for α, β plus additivity of both omega coefficient and formal series leading coefficient.
- **Uses from project**: `omegaPullbackCoeff`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 426–440 (15 lines)
- **Notes**: Dead code within the file (API for downstream callers).

---

## Section: T-IV-BRIDGE-003

### `theorem formalIsogenySeries_add`
- **Type**: `(α β γ : Isogeny W.toAffine W.toAffine) (_h_add : γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom) : formalIsogenySeries W γ = MvPowerSeries.subst (![formalIsogenySeries W α, formalIsogenySeries W β]) (formalGroupLaw W).toMvPowerSeries`
- **What**: If `γ = α + β` as additive homomorphisms, then the formal series of `γ` equals the formal group law applied to the formal series of `α` and `β`. This is Silverman IV.1 + III.5.2.
- **How**: **SORRY** — the mathematical content (identifying the chord-tangent addition in local coordinates with the formal group law substitution) is not yet proved.
- **Hypotheses**: `γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom`.
- **Uses from project**: `formalIsogenySeries`, `formalGroupLaw`
- **Used by**: `omegaPullbackCoeff_add_via_bridge_of_constCoeff`
- **Visibility**: public
- **Lines**: 464–472 (9 lines; proof = `sorry`)
- **Notes**: **SORRY.** Key bridge lemma (T-IV-BRIDGE-003). Its sorry propagates to `omegaPullbackCoeff_add_via_bridge_of_constCoeff`.

---

### `theorem formalIsogenySeries_add_of_coeff_witness`
- **Type**: Takes `h_coeff : ∀ n, coeff n (formalIsogenySeries W γ) = coeff n (MvPowerSeries.subst ...)` and concludes `formalIsogenySeries W γ = MvPowerSeries.subst ...`.
- **What**: BRIDGE-003 from a pointwise coefficient witness. If all coefficients agree, the power series are equal.
- **How**: `PowerSeries.ext h_coeff`.
- **Hypotheses**: Coefficient-by-coefficient equality.
- **Uses from project**: `formalIsogenySeries`
- **Used by**: `formalIsogenySeries_add_of_split_coeff_witness`
- **Visibility**: public
- **Lines**: 501–514 (14 lines)
- **Notes**: none

---

### `theorem formalIsogenySeries_add_of_split_coeff_witness`
- **Type**: Takes separate `h_zero`, `h_one`, `h_higher` hypotheses for coefficients 0, 1, and `n ≥ 2`, and concludes BRIDGE-003.
- **What**: Splits the coefficient-ladder proof into three pieces: n=0 (constant term), n=1 (linear term), n≥2 (higher terms), then reassembles via `formalIsogenySeries_add_of_coeff_witness`.
- **How**: `match` on natural number cases; delegates to `formalIsogenySeries_add_of_coeff_witness`.
- **Hypotheses**: Three separate coefficient hypotheses.
- **Uses from project**: `formalIsogenySeries_add_of_coeff_witness`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 537–567 (31 lines)
- **Notes**: Proof > 30 lines; dead code within this file.

---

### `theorem formalIsogenySeries_add_coeff_zero_via_genuine`
- **Type**: Takes `h_γ_const`, `h_α_const`, `h_β_const` (zero constant coefficients for all three) and proves `coeff 0 (formalIsogenySeries W γ) = coeff 0 (MvPowerSeries.subst ...)`.
- **What**: The `n=0` case of BRIDGE-003: both sides have constant coefficient 0 when all three formal series are "genuine" (zero constant term).
- **How**: Constructs `HasSubst`, applies `MvPowerSeries.constantCoeff_subst_eq_zero` with `constantCoeff_formalGroupLaw`, and converts both sides via `coeff_zero_eq_constantCoeff_apply`.
- **Hypotheses**: Zero constant coefficients for `α`, `β`, `γ`.
- **Uses from project**: `constantCoeff_formalGroupLaw`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 576–610 (35 lines)
- **Notes**: Proof > 30 lines; dead code within this file.

---

### `theorem formalIsogenySeries_add_coeff_one_via_FGL`
- **Type**: Takes `h_lhs_linearity` (Silverman III.5.2 leading-term linearity) and `h_α_const`, `h_β_const` (zero constant coefficients), and proves the `n=1` BRIDGE-003 case.
- **What**: The `n=1` case of BRIDGE-003: given that the LHS leading coefficient is `coeff 1 fα + coeff 1 fβ`, this matches the formal-group-law substitution's coefficient via `coeff_one_subst_bivariate`.
- **How**: Rewrites via `h_lhs_linearity`, then applies `coeff_one_subst_bivariate` with the coefficient facts `formalGroupLaw_coeff_single_zero_one`, `formalGroupLaw_coeff_single_one_one`, `constantCoeff_formalGroupLaw`.
- **Hypotheses**: Silverman III.5.2 additivity of leading coefficient; zero constant coefficients.
- **Uses from project**: `coeff_one_subst_bivariate`, `formalGroupLaw_coeff_single_zero_one`, `formalGroupLaw_coeff_single_one_one`, `constantCoeff_formalGroupLaw`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 620–639 (20 lines)
- **Notes**: Dead code within this file.

---

## Section: Additivity of omegaPullbackCoeff via the bridge

### `theorem omegaPullbackCoeff_add_of_bridge_witnesses`
- **Type**: Takes `f_α f_β f_γ : PowerSeries F`, BRIDGE-001 instances `h_bridge_α`, `h_bridge_β`, `h_bridge_γ`, and coefficient additivity `h_coeff1_add`, and proves `omegaPullbackCoeff W γ = omegaPullbackCoeff W α + omegaPullbackCoeff W β`.
- **What**: Additivity of `omegaPullbackCoeff` given three BRIDGE-001 instances and coefficient-1 additivity of the formal series. Witness-parametric and axiom-clean.
- **How**: Rewrites via the three bridge hypotheses and `h_coeff1_add`, then uses `map_add` and `congrArg`.
- **Hypotheses**: Three BRIDGE-001 instances plus coeff-1 additivity.
- **Uses from project**: `omegaPullbackCoeff`
- **Used by**: `omegaPullbackCoeff_add_of_leading_witness`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`
- **Visibility**: public
- **Lines**: 666–680 (15 lines)
- **Notes**: none

---

### `theorem omegaPullbackCoeff_add_of_leading_witness`
- **Type**: Takes BRIDGE-001 for all three isogenies and `h_leading_add` (coeff-1 additivity for `formalIsogenySeries`), and proves omega-pullback-coefficient additivity.
- **What**: Specializes `omegaPullbackCoeff_add_of_bridge_witnesses` to the canonical `formalIsogenySeries` formal series.
- **How**: Direct delegation to `omegaPullbackCoeff_add_of_bridge_witnesses`.
- **Hypotheses**: Three BRIDGE-001 instances plus leading coefficient additivity.
- **Uses from project**: `omegaPullbackCoeff_add_of_bridge_witnesses`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 687–702 (16 lines)
- **Notes**: Dead code within this file.

---

### `theorem omegaPullbackCoeff_add_via_bridge_of_constCoeff`
- **Type**: `(α β γ : Isogeny ...) (h_add : γ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom) (hα_const hβ_const : constantCoeff (formalIsogenySeries W _) = 0) : omegaPullbackCoeff W γ = omegaPullbackCoeff W α + omegaPullbackCoeff W β`
- **What**: T-III-5-002: omega pullback coefficient is additive for genuine isogenies summing to `γ`. Chains BRIDGE-001 (thrice) + BRIDGE-003 + the formal-group-law linearity at degree 1.
- **How**: Applies `omegaPullbackCoeff_add_of_bridge_witnesses` with the three sorry-carrying BRIDGE-001 instances, then `formalIsogenySeries_add` (also sorry) and `coeff_one_subst_bivariate`.
- **Hypotheses**: Additive-hom equality for `γ = α + β`; zero constant coefficients for `α, β`.
- **Uses from project**: `omegaPullbackCoeff_add_of_bridge_witnesses`, `omegaPullbackCoeff_eq_formalIsogenyLeading` (sorry), `formalIsogenySeries_add` (sorry), `coeff_one_subst_bivariate`, `formalGroupLaw_coeff_single_zero_one`, `formalGroupLaw_coeff_single_one_one`, `constantCoeff_formalGroupLaw`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 723–741 (19 lines)
- **Notes**: Carries sorry via `omegaPullbackCoeff_eq_formalIsogenyLeading` and `formalIsogenySeries_add`.

---

## Section: Identity isogeny formal series

### `theorem formalIsogenySeries_id`
- **Type**: `formalIsogenySeries W (Isogeny.id W.toAffine) = PowerSeries.X`
- **What**: The formal isogeny series of the identity isogeny is the formal variable `X` (the local expansion of `localParam W` is `PowerSeries.X`).
- **How**: Unfolds via `formalIsogenySeries_coeff`, uses `AlgHom.id_apply`, then `localExpand_localParam` (to get `HahnSeries.single 1 1`), and case splits on `n = 1` to match against `PowerSeries.coeff_X`.
- **Hypotheses**: none beyond context
- **Uses from project**: `formalIsogenySeries_coeff`, `localExpand_localParam`
- **Used by**: `coeff_one_formalIsogenySeries_id`, `omegaPullbackCoeff_eq_formalIsogenyLeading_id`
- **Visibility**: public
- **Lines**: 752–765 (14 lines)
- **Notes**: none

---

### `@[simp] theorem coeff_one_formalIsogenySeries_id`
- **Type**: `PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) = 1`
- **What**: The leading coefficient of the identity isogeny's formal series is 1.
- **How**: Rewrites via `formalIsogenySeries_id` to `coeff_X`, then `if_pos rfl`.
- **Hypotheses**: none
- **Uses from project**: `formalIsogenySeries_id`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 771–773 (3 lines)
- **Notes**: Dead code within this file.

---

### `theorem omegaPullbackCoeff_id`
- **Type**: `omegaPullbackCoeff W (Isogeny.id W.toAffine) = 1`
- **What**: The omega pullback coefficient of the identity isogeny is 1. Inlined version of `omegaPullbackCoeff_of_pullback_eq_id` (not imported).
- **How**: Applies `omegaPullbackCoeff_unique`, then `omegaPullbackCoeff_spec`, `alpha_star_u_eq`, uses `Isogeny.id_pullback`, `AlgHom.id_apply`, `one_smul`, and `rfl`.
- **Hypotheses**: none
- **Uses from project**: `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `alpha_star_u_eq`
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_id`
- **Visibility**: public
- **Lines**: 778–782 (5 lines)
- **Notes**: The docstring notes this mirrors `omegaPullbackCoeff_of_pullback_eq_id` but is inlined to avoid a forward import.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_id`
- **Type**: `omegaPullbackCoeff W (Isogeny.id W.toAffine) = algebraMap F KE (PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)))`
- **What**: BRIDGE-001 for the identity isogeny: both sides equal 1.
- **How**: Rewrites via `formalIsogenySeries_id`, `coeff_X`, `if_pos rfl`, `map_one`, and `omegaPullbackCoeff_id`.
- **Hypotheses**: none
- **Uses from project**: `formalIsogenySeries_id`, `omegaPullbackCoeff_id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 789–794 (6 lines)
- **Notes**: Dead code within this file (computed instance of BRIDGE-001 for id).

---

### `theorem formalIsogenySeries_mulByInt_one`
- **Type**: `formalIsogenySeries W (mulByInt W.toAffine 1) = PowerSeries.X`
- **What**: The formal isogeny series of `[1]` is `X`. Same conclusion as `formalIsogenySeries_id` but for `mulByInt 1`.
- **How**: Unfolds via `formalIsogenySeries_coeff`, uses `mulByInt_one_pullback_eq_id` to get `h_pb`, then `localExpand_localParam`, and the same `n = 1` case split as in `formalIsogenySeries_id`.
- **Hypotheses**: none
- **Uses from project**: `formalIsogenySeries_coeff`, `mulByInt_one_pullback_eq_id`, `localExpand_localParam`
- **Used by**: `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
- **Visibility**: public
- **Lines**: 800–814 (15 lines)
- **Notes**: Proof > 30 lines when counted from span start (42 lines). Duplicates `formalIsogenySeries_id` modulo `mulByInt_one = id` identification.

---

## Section: BRIDGE-003 inductive path for mulByInt

### `theorem constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`
- **Type**: Takes `h_bridge_003` (BRIDGE-003 specialized to `[k+1] = [k] + [1]`) and proves `∀ n ≥ 1, constantCoeff (formalIsogenySeries W (mulByInt W.toAffine n)) = 0`.
- **What**: Given BRIDGE-003 in its specialized `[k+1] = [k] + [1]` form, derives that all `[n]` for `n ≥ 1` have zero constant coefficient in their formal series (genuine isogeny property by induction).
- **How**: Induction on `n`. Base: `formalIsogenySeries_mulByInt_one` gives `constantCoeff X = 0`. Step: BRIDGE-003 gives `formalIsogenySeries [k+1] = subst (formalGroupLaw W)`, then `MvPowerSeries.constantCoeff_subst_eq_zero` with `constantCoeff_formalGroupLaw` closes it.
- **Hypotheses**: BRIDGE-003 hypothesis `h_bridge_003` for the successor case.
- **Uses from project**: `formalIsogenySeries_mulByInt_one`, `constantCoeff_formalGroupLaw`
- **Used by**: `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
- **Visibility**: public
- **Lines**: 842–879 (38 lines)
- **Notes**: Proof > 30 lines. Gated on `h_bridge_003` hypothesis.

---

### `theorem coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`
- **Type**: Takes `h_bridge_003` and proves `∀ n ≥ 1, coeff 1 (formalIsogenySeries W (mulByInt W.toAffine n)) = (n : F)`.
- **What**: Given BRIDGE-003 for `[k+1] = [k] + [1]`, the leading coefficient of the formal series of `[n]` is `n`. Alternative to the Wronskian-derived path in `BridgeMulByInt.lean`.
- **How**: Induction on `n`. Base via `formalIsogenySeries_mulByInt_one` + `coeff_one_X`. Step via `h_bridge_003`, `coeff_one_subst_bivariate`, `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`, and arithmetic on `F`.
- **Hypotheses**: BRIDGE-003 hypothesis for `[k+1] = [k] + [1]`.
- **Uses from project**: `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003`, `formalIsogenySeries_mulByInt_one`, `coeff_one_subst_bivariate`, `formalGroupLaw_coeff_single_zero_one`, `formalGroupLaw_coeff_single_one_one`, `constantCoeff_formalGroupLaw`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 892–928 (37 lines)
- **Notes**: Proof > 30 lines (105-line span). Dead code within this file (alternative path to `BridgeMulByInt.lean`'s result).

---

## Section: R5a and valuation infrastructure

### `theorem pullback_equation_inl`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) : (W_KE W).toAffine.Equation (α.pullback (x_gen W)) (α.pullback (y_gen W))`
- **What**: The pullback of the generic point `(x_gen, y_gen)` under `α` satisfies the Weierstrass equation. Inlined version of `pullback_equation` from `AdditionPullback.lean`.
- **How**: Uses `Affine.Equation.map` on the `generic_equation W`, then rewrites `(W_KE W).map α.pullback = W_KE W` using `WeierstrassCurve.map_map` and `α.pullback.commutes`.
- **Hypotheses**: none beyond context
- **Uses from project**: `generic_equation`, `W_KE`
- **Used by**: `ord_pullback_x_neg_of_localParam_pos`, `ordAtInfty_pullback_localParam_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 997–1003 (7 lines)
- **Notes**: Inlined to avoid circular import from `AdditionPullback.lean`.

---

### `theorem ord_algebraMap_F_nonneg`
- **Type**: `(c : F) : 0 ≤ (W_smooth W).ordAtInfty (algebraMap F KE c)`
- **What**: A constant from the base field `F` has non-negative order at `O` (order 0 if nonzero, `⊤` if zero).
- **How**: Case splits on `c = 0` (using `ordAtInfty_zero`) and `c ≠ 0` (using `ordAtInfty_algebraMap_F_nonzero`).
- **Hypotheses**: none
- **Uses from project**: `W_smooth`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ord_pullback_x_neg_of_localParam_pos`, `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`, `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`, `ordAtInfty_x_neg_of_equation_of_neg_div_pos` — used in every Weierstrass-equation valuation proof (high use)
- **Visibility**: public
- **Lines**: 1007–1011 (5 lines)
- **Notes**: keyApi (used in 4+ long valuation proofs, handling all 5 Weierstrass coefficients each time).

---

### `theorem ord_coeff_mul_ge`
- **Type**: `(c z : KE) (hc : 0 ≤ (W_smooth W).ordAtInfty c) : (W_smooth W).ordAtInfty z ≤ (W_smooth W).ordAtInfty (c * z)`
- **What**: Multiplying by an element `c` of non-negative order cannot decrease the order: `ord z ≤ ord(c * z)`. Used to bound valuation of Weierstrass coefficient terms.
- **How**: Case splits on `z = 0` and `c = 0`, then uses `ordAtInfty_mul` with `gcongr` for the multiplicativity step.
- **Hypotheses**: `0 ≤ ordAtInfty c`.
- **Uses from project**: `W_smooth`
- **Used by**: `ord_pullback_x_neg_of_localParam_pos`, `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`, `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`, `ordAtInfty_x_neg_of_equation_of_neg_div_pos`
- **Visibility**: public
- **Lines**: 1015–1023 (9 lines)
- **Notes**: keyApi (appears in every Weierstrass-equation argument; each proof uses it 5–7 times).

---

### `theorem ord_pullback_x_neg_of_localParam_pos`
- **Type**: `(α : Isogeny W.toAffine W.toAffine) (h_base : ordAtInfty (α.pullback (x_gen W)) ≤ 0) (h_pos : 0 < ordAtInfty (α.pullback (localParam W))) : ordAtInfty (α.pullback (x_gen W)) < 0`
- **What**: If `z = α*t` reduces to `O` (positive order) and `α*x` is not a unit at `O` (basepoint hypothesis `≤ 0`), then `α*x` has a strict pole at `O`. This is the genuine content of R5a with the basepoint hypothesis made explicit.
- **How**: Extracts integer orders `m` for `α*x` and `n` for `α*y`, computes `ord(α*localParam) = m − n` via the chain rule `localParam = -x/y`, derives `n < m` from `h_pos`, then case-splits: `m < 0` (done) vs `m = 0` (contradiction via Weierstrass equation: `Y^2` term has order `2n < 0`, but all RHS terms have order ≥ 0, forcing `0 ≤ 2n`, contradicting `n < 0`). Uses `pullback_equation_inl`, `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `ordAtInfty_add_eq_of_lt`.
- **Hypotheses**: Basepoint hypothesis `ordAtInfty(α*x) ≤ 0`; positive order of `α*localParam`.
- **Uses from project**: `pullback_equation_inl`, `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `W_smooth`, `x_gen_ne_zero`, `y_gen_ne_zero`, `localParam`
- **Used by**: `ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base`
- **Visibility**: public
- **Lines**: 1046–1150 (105 lines)
- **Notes**: Proof > 30 lines (143-line span). Major valuation argument. No substitution lemma used.

---

### `theorem ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`
- **Type**: `{X Y : KE} (hX_ne : X ≠ 0) (h_weier : (W_KE W).toAffine.Equation X Y) (hX_neg : ordAtInfty X < 0) : Y ≠ 0`
- **What**: For `(X, Y)` on the Weierstrass curve with `X ≠ 0` and `ord_∞ X < 0`, we have `Y ≠ 0`. If `Y = 0`, the Weierstrass equation degenerates to `X^3 + ... = 0`, impossible since `X^3` dominates with order `3m < 0`.
- **How**: Assumes `Y = 0`, reduces Weierstrass equation to `X^3 + a₂X^2 + a₄X + a₆ = 0`, shows via non-archimedean valuation (`ordAtInfty_add_eq_of_lt`) that the left side has order `3m`, but is also `0` (order `⊤`), contradiction.
- **Hypotheses**: `X ≠ 0`, Weierstrass equation, `ord_∞ X < 0`.
- **Uses from project**: `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `W_smooth`, `W_KE`
- **Used by**: unused in file (helper for the pattern in `ordAtInfty_y_lt...` is internalized there directly)
- **Visibility**: public
- **Lines**: 1189–1253 (65 lines)
- **Notes**: Proof > 30 lines (69-line span). Dead code within this file; the argument is repeated inline in `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`.

---

### `theorem ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`
- **Type**: `{X Y : KE} (hX_ne : X ≠ 0) (hY_ne : Y ≠ 0) (h_weier : Equation X Y) (hX_neg : ordAtInfty X < 0) : ordAtInfty Y < ordAtInfty X`
- **What**: For `(X, Y)` on the Weierstrass curve with `X, Y ≠ 0` and `ord_∞ X < 0`, the order of `Y` is strictly less than the order of `X`: `ord_∞ Y < ord_∞ X`. The `Y^2` term dominates all cross terms when `m ≤ n` (contradiction) because the RHS has order `3m < 2n ≤ 2m`.
- **How**: By contradiction, assumes `m ≤ n` (where `m = ord X`, `n = ord Y`), computes `ord(RHS) = 3m` by peeling each dominant term, shows all LHS terms have order `> 3m`, contradicting the Weierstrass equation. Uses `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `ordAtInfty_add_eq_of_lt`, `ordAtInfty_add_ge_min`.
- **Hypotheses**: `X, Y ≠ 0`, Weierstrass equation, `ord_∞ X < 0`.
- **Uses from project**: `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `W_smooth`, `W_KE`
- **Used by**: `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 1258–1373 (116 lines)
- **Notes**: Proof > 30 lines (122-line span). Major valuation argument; duplicates pattern from `ord_pullback_x_neg_of_localParam_pos` in the Y-dominance case.

---

### `theorem ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`
- **Type**: `{X Y : KE} (hX_ne : X ≠ 0) (hY_ne : Y ≠ 0) (h_weier : Equation X Y) (hX_neg : ordAtInfty X < 0) : 0 < ordAtInfty (-X / Y)`
- **What**: For `(X, Y)` on the Weierstrass curve with `X ≠ 0`, `Y ≠ 0`, and `ord_∞ X < 0`, the local parameter `z = -X/Y` reduces to `O` (positive order). This is the generic "x-pole ⟹ z reduces" direction.
- **How**: Extracts integer orders `m, n`, applies `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg` to get `n < m`, computes `ord(-X/Y) = m - n > 0` via `ordAtInfty_neg` and `ord_div_concrete`.
- **Hypotheses**: Same as previous plus `Y ≠ 0`.
- **Uses from project**: `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg`, `W_smooth`
- **Used by**: `ordAtInfty_pullback_localParam_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 1380–1401 (22 lines)
- **Notes**: none

---

### `theorem ordAtInfty_x_neg_of_equation_of_neg_div_pos`
- **Type**: `{X Y : KE} (hX_ne hY_ne : _ ≠ 0) (h_weier : Equation X Y) (h_base : ordAtInfty X ≤ 0) (h_pos : 0 < ordAtInfty (-X / Y)) : ordAtInfty X < 0`
- **What**: Generic converse: if `z = -X/Y` reduces to `O` and `X` is not a unit at `O` (basepoint hypothesis), then `X` has a strict pole. The back-conversion step 4 in the formal-group route.
- **How**: Expresses `ord(-X/Y) = m - n` via `ord_div_concrete`, derives `n < m`, then case splits: `m < 0` (done) or `m = 0` forces a Weierstrass equation contradiction (same Y²-dominance argument as `ord_pullback_x_neg_of_localParam_pos`).
- **Hypotheses**: `X, Y ≠ 0`, Weierstrass equation, basepoint `ord X ≤ 0`, positive `ord(-X/Y)`.
- **Uses from project**: `ord_algebraMap_F_nonneg`, `ord_coeff_mul_ge`, `W_smooth`, `W_KE`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1416–1509 (94 lines)
- **Notes**: Proof > 30 lines (126-line span). Dead code within this file. Contains the same Weierstrass-equation valuation argument as `ord_pullback_x_neg_of_localParam_pos` (significant duplication).

---

## Section: R5b — formal valuation equals ordAtInfty

### `theorem orderTop_localExpand_algebraMap_fracPolyX`
- **Type**: `{r₀ : FractionRing (Polynomial F)} (hr₀ : r₀ ≠ 0) : (localExpand W (algebraMap (FractionRing (Polynomial F)) KE r₀)).orderTop = ((-2 * (RatFunc.ofFractionRing r₀).intDegree : ℤ) : WithTop ℤ)`
- **What**: The formal order of the local expansion of an `F(X)`-image `r₀` is `-2 · intDegree(r₀)`. This matches `ordAtInfty` on the subfield `F(X)`.
- **How**: Lifts `r₀ = p/d` via `IsLocalization.surj`, maps into `KE` and applies `localExpand`, uses multiplicativity of `HahnSeries.orderTop_mul`, and the polynomial case `orderTop_localExpand_algebraMap_polynomial` for both `p` and `d`. Computes `intDegree = natDeg p - natDeg d` via `RatFunc.intDegree_mul`, `RatFunc.intDegree_inv`, `RatFunc.intDegree_polynomial`.
- **Hypotheses**: `r₀ ≠ 0`.
- **Uses from project**: `localExpand`, `orderTop_localExpand_algebraMap_polynomial`
- **Used by**: `orderTop_localExpand_basis_eq_min`, `orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty`
- **Visibility**: public
- **Lines**: 1542–1616 (75 lines)
- **Notes**: Proof > 30 lines (79-line span). Core of R5b.

---

### `theorem y_gen_eq_coordYInFunctionField`
- **Type**: `y_gen W = (W_smooth W).coordYInFunctionField`
- **What**: The two expressions for the `y`-generator in the function field are definitionally equal: `y_gen W` and `(W_smooth W).coordYInFunctionField` are the same element.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `y_gen`, `W_smooth`
- **Used by**: `orderTop_localExpand_basis_eq_min`, `orderTop_localExpand_eq_ordAtInfty`
- **Visibility**: public
- **Lines**: 1621–1622 (2 lines)
- **Notes**: none

---

### `theorem orderTop_localExpand_y_gen`
- **Type**: `(localExpand W (y_gen W)).orderTop = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The formal order of the local expansion of `y_gen W` is `-3`.
- **How**: Rewrites via `localExpand_y_gen` and applies `formalY_orderTop`.
- **Hypotheses**: none
- **Uses from project**: `localExpand_y_gen`, `formalY_orderTop`
- **Used by**: `orderTop_localExpand_basis_eq_min`, `orderTop_localExpand_eq_ordAtInfty`
- **Visibility**: public
- **Lines**: 1625–1627 (3 lines)
- **Notes**: none

---

### `theorem orderTop_localExpand_basis_eq_min`
- **Type**: `(r₁ r₂ : FractionRing (Polynomial F)) : orderTop (localExpand W (algebraMap r₁ + algebraMap r₂ * y_gen W)) = min (orderTop (localExpand W (algebraMap r₁))) (orderTop (localExpand W (algebraMap r₂)) + orderTop (localExpand W (y_gen W)))`
- **What**: The formal order of the local expansion of a basis element `r₁ + r₂ · y` equals the min of the two summand orders. The exact analogue of `ordAtInfty_basis_eq_min` in the formal-series world.
- **How**: Reduces to `HahnSeries.orderTop_add_eq_left/right` using the parity argument: the `r₁` part has even formal order (`-2 · intDeg r₁`) while `r₂ · y` has odd order (`-2 · intDeg r₂ - 3`), so they can never coincide, and the min picks the correct branch.
- **Hypotheses**: `r₁, r₂ : FractionRing (Polynomial F)`.
- **Uses from project**: `orderTop_localExpand_algebraMap_fracPolyX`, `orderTop_localExpand_y_gen`, `localExpand`
- **Used by**: `orderTop_localExpand_eq_ordAtInfty`
- **Visibility**: public
- **Lines**: 1639–1681 (43 lines)
- **Notes**: Proof > 30 lines (47-line span). Core of R5b parity argument.

---

### `theorem orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty`
- **Type**: `(r : FractionRing (Polynomial F)) : orderTop (localExpand W (algebraMap r)) = (W_smooth W).ordAtInfty (algebraMap r)`
- **What**: The two valuations agree on `F(X)`-images (including `r = 0`).
- **How**: Case splits on `r = 0` (both sides `⊤`) and `r ≠ 0` (uses `orderTop_localExpand_algebraMap_fracPolyX` and `ordAtInfty_algebraMap_fracPolyX_of_ne_zero`).
- **Hypotheses**: `r : FractionRing (Polynomial F)`.
- **Uses from project**: `orderTop_localExpand_algebraMap_fracPolyX`, `W_smooth`
- **Used by**: `orderTop_localExpand_eq_ordAtInfty`
- **Visibility**: public
- **Lines**: 1686–1695 (10 lines)
- **Notes**: none

---

### `theorem orderTop_localExpand_eq_ordAtInfty`
- **Type**: `(f : KE) : (localExpand W f).orderTop = (W_smooth W).ordAtInfty f`
- **What**: The formal `t`-adic valuation `orderTop ∘ localExpand` equals the norm-based `ordAtInfty` on all of `K(E)`. This is the full R5b identity.
- **How**: Decomposes `f = algebraMap r₁ + algebraMap r₂ · y_gen` via `exists_decomp`, applies `orderTop_localExpand_basis_eq_min` and `ordAtInfty_basis_eq_min`, then matches componentwise using `orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty` and `orderTop_localExpand_y_gen`.
- **Hypotheses**: none
- **Uses from project**: `y_gen_eq_coordYInFunctionField`, `orderTop_localExpand_basis_eq_min`, `orderTop_localExpand_algebraMap_fracPolyX_eq_ordAtInfty`, `orderTop_localExpand_y_gen`, `W_smooth`, `localExpand`
- **Used by**: `ordAtInfty_neg_of_orderTop_localExpand_neg`, `ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base`, `ordAtInfty_pullback_localParam_pos_of_ord_x_neg` (via chain), `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 1702–1730 (29 lines)
- **Notes**: keyApi (used by 4+ declarations in this file, and the R5b milestone result).

---

### `theorem ordAtInfty_neg_of_orderTop_localExpand_neg`
- **Type**: `{f : KE} (h : orderTop (localExpand W f) < 0) : (W_smooth W).ordAtInfty f < 0`
- **What**: The `< 0` direction of R5b: formal pole implies valuation pole.
- **How**: `rwa [orderTop_localExpand_eq_ordAtInfty W f] at h`.
- **Hypotheses**: Formal pole `orderTop (localExpand f) < 0`.
- **Uses from project**: `orderTop_localExpand_eq_ordAtInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1737–1740 (4 lines)
- **Notes**: Dead code within this file (immediate corollary).

---

### `theorem ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base`
- **Type**: `(α : Isogeny ...) (h_base : ordAtInfty (α.pullback (x_gen W)) ≤ 0) (h_orderTop : 0 < orderTop (localExpand W (α.pullback (localParam W)))) : ordAtInfty (α.pullback (x_gen W)) < 0`
- **What**: QF Layer-1 brick 5 with basepoint hypothesis: if `α*t` has positive formal order and `α*x` is not a unit at `O`, then `α*x` has a pole. The TRUE version of R5a.
- **How**: Converts `h_orderTop` to `ordAtInfty` form via `orderTop_localExpand_eq_ordAtInfty`, then delegates to `ord_pullback_x_neg_of_localParam_pos`.
- **Hypotheses**: Basepoint hypothesis + positive formal order.
- **Uses from project**: `orderTop_localExpand_eq_ordAtInfty`, `ord_pullback_x_neg_of_localParam_pos`, `x_gen`
- **Used by**: unused in file (available to external callers)
- **Visibility**: public
- **Lines**: 1753–1760 (8 lines)
- **Notes**: Dead code within this file.

---

## Section: x-pole ⟹ z reduces (summand form)

### `theorem ordAtInfty_pullback_localParam_pos_of_ord_x_neg`
- **Type**: `(α : Isogeny ...) (h_x_neg : ordAtInfty (α.pullback (x_gen W)) < 0) : 0 < ordAtInfty (α.pullback (localParam W))`
- **What**: If `α*x` has a pole at `O`, then `α*localParam = -α(x)/α(y)` reduces to `O` (positive order). Uses the generic `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`.
- **How**: Shows `α*(x) ≠ 0` and `α*(y) ≠ 0` via `pullback_injective`, unfolds `localParam = -x/y`, rewrites to `-α(x)/α(y)`, and applies `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg` with `pullback_equation_inl`.
- **Hypotheses**: `ordAtInfty (α.pullback (x_gen W)) < 0`.
- **Uses from project**: `pullback_equation_inl`, `ordAtInfty_neg_div_pos_of_equation_of_ord_x_neg`, `x_gen_ne_zero`, `y_gen_ne_zero`, `localParam`
- **Used by**: `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 1783–1796 (14 lines)
- **Notes**: none

---

### `theorem orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`
- **Type**: `(α : Isogeny ...) (h_x_neg : ordAtInfty (α.pullback (x_gen W)) < 0) : 0 < (localExpand W (α.pullback (localParam W))).orderTop`
- **What**: Formal version: if `α*x` has a pole, the formal expansion of `α*localParam` has positive `orderTop`. Bridges back to the Laurent-series world.
- **How**: Applies `orderTop_localExpand_eq_ordAtInfty`, then `ordAtInfty_pullback_localParam_pos_of_ord_x_neg`.
- **Hypotheses**: `ordAtInfty (α.pullback (x_gen W)) < 0`.
- **Uses from project**: `orderTop_localExpand_eq_ordAtInfty`, `ordAtInfty_pullback_localParam_pos_of_ord_x_neg`
- **Used by**: `order_formalIsogenySeries_pos_of_ord_x_neg`
- **Visibility**: public
- **Lines**: 1807–1812 (6 lines)
- **Notes**: none

---

### `theorem order_formalIsogenySeries_pos_of_ord_x_neg`
- **Type**: `(α : Isogeny ...) (h_x_neg : ordAtInfty (α.pullback (x_gen W)) < 0) : 0 < (formalIsogenySeries W α).order`
- **What**: If `α*x` has a pole at `O`, the formal isogeny series of `α` has positive `PowerSeries.order`. Exact `hf`/`hg` input form for `order_formalGroupLaw_subst_pos`.
- **How**: Delegates to `order_formalIsogenySeries_pos_of_orderTop_pos` with the result of `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`.
- **Hypotheses**: `ordAtInfty (α.pullback (x_gen W)) < 0`.
- **Uses from project**: `order_formalIsogenySeries_pos_of_orderTop_pos`, `orderTop_localExpand_pullback_localParam_pos_of_ord_x_neg`
- **Used by**: `orderTop_localExpand_z_sum_pos_of_iv14_identity`
- **Visibility**: public
- **Lines**: 1818–1823 (6 lines)
- **Notes**: none

---

### `theorem orderTop_ofPowerSeries_pos_of_order_pos`
- **Type**: `{P : PowerSeries F} (hP : 0 < P.order) : (0 : WithTop ℤ) < (HahnSeries.ofPowerSeries ℤ F P).orderTop`
- **What**: A power series with positive `order` (zero constant term) maps to a `LaurentSeries` with positive `orderTop`. Bridge from the `PowerSeries.order` world to the `HahnSeries.orderTop` world.
- **How**: Converts `0 < order` to `constantCoeff = 0`, then uses `HahnSeries.le_orderTop_iff_forall` to show all coefficients at `j < 1` vanish: negative `j` are outside the image of `ℕ` in `ℤ` (`embDomain_notin_range`), and `j = 0` uses `constantCoeff = 0`.
- **Hypotheses**: `0 < P.order` (no `W` or curve structure needed; `omit`-ted).
- **Uses from project**: none
- **Used by**: `orderTop_localExpand_z_sum_pos_of_iv14_identity`
- **Visibility**: public
- **Lines**: 1825–1852 (28 lines, with `omit`)
- **Notes**: Proof > 30 lines (53-line span). Generic power-series/Laurent-series bridge.

---

### `theorem orderTop_localExpand_z_sum_pos_of_iv14_identity`
- **Type**: `(α₁ α₂ : Isogeny ...) (z_sum : KE) (h_α₁ h_α₂ : ordAtInfty (αᵢ.pullback (x_gen W)) < 0) (h_iv14 : localExpand W z_sum = ofPowerSeries ℤ F (subst ...)) : 0 < (localExpand W z_sum).orderTop`
- **What**: IV.1.4 order output from the formal-group identity (witness-parametric, axiom-clean): given the IV.1.4 identity `h_iv14` and that both summand x-pullbacks have poles, the sum's local expansion has positive `orderTop`.
- **How**: Rewrites via `h_iv14`, applies `orderTop_ofPowerSeries_pos_of_order_pos` with `order_formalGroupLaw_subst_pos` (using `order_formalIsogenySeries_pos_of_ord_x_neg` for each summand).
- **Hypotheses**: IV.1.4 identity hypothesis; `ord_∞(αᵢ*x) < 0` for both summands.
- **Uses from project**: `order_formalGroupLaw_subst_pos`, `order_formalIsogenySeries_pos_of_ord_x_neg`, `orderTop_ofPowerSeries_pos_of_order_pos`, `formalIsogenySeries`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1887–1902 (16 lines)
- **Notes**: Dead code within this file (terminal brick for IV.1.4 route; to be called by upstream orchestration).

---

## Summary

- **Total declarations**: 51 (1 `noncomputable def` + 50 `theorem`)
- **Sorries**: `omegaPullbackCoeff_eq_formalIsogenyLeading` (BRIDGE-001, T-IV-BRIDGE-001), `formalIsogenySeries_add` (BRIDGE-003, T-IV-BRIDGE-003)
- **No `set_option maxHeartbeats`**
- **Long proofs (>30 lines)**: `coeff_one_subst_bivariate` (73 lines), `ord_pullback_x_neg_of_localParam_pos` (105 lines), `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg` (65 lines), `ordAtInfty_y_lt_ordAtInfty_x_of_equation_of_ord_x_neg` (116 lines), `ordAtInfty_x_neg_of_equation_of_neg_div_pos` (94 lines), `orderTop_localExpand_algebraMap_fracPolyX` (75 lines), `orderTop_localExpand_basis_eq_min` (43 lines), `constantCoeff_formalIsogenySeries_mulByInt_via_bridge_003` (38 lines), `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003` (37 lines), `formalIsogenySeries_add_of_split_coeff_witness` (31 lines), `formalIsogenySeries_add_coeff_zero_via_genuine` (35 lines), `orderTop_ofPowerSeries_pos_of_order_pos` (28 lines), `omegaPullbackCoeff_add_via_bridge_of_constCoeff` (varies), `formalIsogenySeries_mulByInt_one` (42-line span)
- **keyApi**: `constantCoeff_formalGroupLaw` (used by 8+ declarations), `ord_algebraMap_F_nonneg` (used in 4 major valuation proofs, each calling it 5 times), `ord_coeff_mul_ge` (used in 4 major proofs, each calling it multiple times), `coeff_one_subst_bivariate` (used by 3+), `orderTop_localExpand_eq_ordAtInfty` (used by 4+)
- **Unused in file**: `omegaPullbackCoeff_eq_formalIsogenyLeading_of_witness`, `omegaPullbackCoeff_eq_formalIsogenyLeading_of_constant_witness`, `omegaPullbackCoeff_eq_formalIsogenyLeading_add_witness`, `formalIsogenySeries_add_of_split_coeff_witness`, `formalIsogenySeries_add_coeff_zero_via_genuine`, `formalIsogenySeries_add_coeff_one_via_FGL`, `omegaPullbackCoeff_add_of_leading_witness`, `omegaPullbackCoeff_add_via_bridge_of_constCoeff`, `coeff_one_formalIsogenySeries_id`, `omegaPullbackCoeff_eq_formalIsogenyLeading_id`, `coeff_one_formalIsogenySeries_mulByInt_via_bridge_003`, `ordAtInfty_y_ne_zero_of_equation_of_ord_x_neg`, `ordAtInfty_x_neg_of_equation_of_neg_div_pos`, `ordAtInfty_neg_of_orderTop_localExpand_neg`, `ordAtInfty_pullback_x_gen_neg_of_orderTop_pos_of_base`, `orderTop_localExpand_z_sum_pos_of_iv14_identity`
