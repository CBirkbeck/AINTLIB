import HasseWeil.AdditionPullback.SilvermanIV14
import HasseWeil.Hasse.OpenLemmaPrimitives
import HasseWeil.EC.MulByIntAddRecurrence

/-!
# Silverman III.5.3: `a_{[m]} = m` via curve-side additivity (Route B assembly)

Builds on **RB-ω4** (`kaehler_D_addPullback_x_eq_one_add_smul_omega`, the Silverman III.5.2
collapse) to assemble `omegaPullbackCoeff (mulByInt m) = m` WITHOUT the EDS Wronskian and WITHOUT
the formal-group correspondence.

* **RB-ADD** (`omegaPullbackCoeff_addIsog_id`): `omegaPullbackCoeff (id ⊞ α) = 1 + omegaPullbackCoeff α`.
* **RB-ID/SUM/IND**: `id ⊞ [m] = [m+1]`, induction → `omegaPullbackCoeff (mulByInt m) = m`.

This is Silverman III.5.2 `(φ+ψ)*ω = φ*ω + ψ*ω` specialised to `φ = id`, then III.5.3's induction.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

/-- **RB-ADD** (Silverman III.5.2, `φ = id` case): for the genuine sum isogeny `σ = id ⊞ α`
(built via `addIsog` on the pair `(id, α)`), the omega-pullback coefficient is `1 + a_α`.

Proof: by uniqueness in the 1-dimensional Kähler module. `omegaPullbackCoeff_spec` gives
`a_σ • ω = (α*u of σ)⁻¹ • D(σ*x)`. Now `σ*x = addPullback_x α` and `α*u of σ = u₃ :=
2·addPullback_y + a₁·addPullback_x + a₃`, while RB-ω4 says `D(addPullback_x α) = u₃ · (1+a_α) · ω`.
So `a_σ • ω = u₃⁻¹ · u₃ · (1+a_α) · ω = (1+a_α) · ω`, hence `a_σ = 1 + a_α`. -/
theorem omegaPullbackCoeff_addIsog_id
    (α : Isogeny W.toAffine W.toAffine)
    (hxy : AddNonInversePair (Isogeny.id W.toAffine) α)
    (hinj : Function.Injective (addCoordAlgHomPair hxy))
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    omegaPullbackCoeff W (addIsog hxy hinj) = 1 + omegaPullbackCoeff W α := by
  -- Pullback of the generators under `σ = id ⊞ α` are the addition-formula outputs.
  have hpx : (addIsog hxy hinj).pullback
        (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X)) = addPullback_x W α := by
    show (addIsog hxy hinj).pullback (x_gen W) = addPullback_x W α
    rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq,
      addPullback_x_pair_id]
  have hpy : (addIsog hxy hinj).pullback (y_gen W) = addPullback_y W α := by
    rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq,
      addPullback_y_pair_id]
  -- `α*u of σ = u₃ = 2·addPullback_y + a₁·addPullback_x + a₃`.
  have hu : alpha_star_u W (addIsog hxy hinj)
      = 2 * addPullback_y W α + algebraMap K KE W.a₁ * addPullback_x W α + algebraMap K KE W.a₃ := by
    rw [show alpha_star_u W (addIsog hxy hinj)
        = 2 * (addIsog hxy hinj).pullback (y_gen W)
          + algebraMap K KE W.a₁ * (addIsog hxy hinj).pullback (x_gen W)
          + algebraMap K KE W.a₃ from rfl, hpy]
    rw [show (addIsog hxy hinj).pullback (x_gen W)
        = (addIsog hxy hinj).pullback (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X))
        from rfl, hpx]
  have hu_ne : alpha_star_u W (addIsog hxy hinj) ≠ 0 := by
    rw [alpha_star_u_eq]
    exact fun h ↦ u_gen_ne_zero W
      ((addIsog hxy hinj).pullback_injective (h.trans (map_zero _).symm))
  have hu3_ne : 2 * addPullback_y W α + algebraMap K KE W.a₁ * addPullback_x W α
      + algebraMap K KE W.a₃ ≠ 0 := hu ▸ hu_ne
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx, hu,
    kaehler_D_addPullback_x_eq_one_add_smul_omega W α h_ne, smul_smul,
    inv_mul_cancel₀ hu3_ne, one_smul]

/-- **General-pair Silverman III.5.2 additivity** (`a_{α₁+α₂} = a_{α₁} + a_{α₂}`): for a genuine
sum isogeny `σ = addIsog α₁ α₂` (`α₁*x ≠ α₂*x`), the omega-pullback coefficient is additive. This
is the full bilinear III.5.2 statement; `omegaPullbackCoeff_addIsog_id` is the `α₁ = id` case
(`a_id = 1`).  Needed for the genuine `r·π − s = addIsog (r·π) (−s)` isogeny, a sum of two
non-identity isogenies.

Proof: by uniqueness in the 1-dimensional Kähler module.  `omegaPullbackCoeff_spec` gives
`a_σ • ω = (α*u of σ)⁻¹ • D(σ*x)`; here `σ*x = addPullback_x_pair α₁ α₂` (via
`addPullbackAlgHomPair_x_gen_eq`) and `α*u of σ = u₃`, while the general-pair collapse
`kaehler_D_addPullback_x_pair_eq_smul_omega` gives `D(σ*x) = u₃ • ((a_{α₁}+a_{α₂}) • ω)`.  So
`a_σ • ω = u₃⁻¹ · u₃ · (a_{α₁}+a_{α₂}) • ω = (a_{α₁}+a_{α₂}) • ω`. -/
theorem omegaPullbackCoeff_addIsog_pair
    {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hxy : AddNonInversePair α₁ α₂)
    (hinj : Function.Injective (addCoordAlgHomPair hxy))
    (h_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W)) :
    omegaPullbackCoeff W (addIsog hxy hinj) =
      omegaPullbackCoeff W α₁ + omegaPullbackCoeff W α₂ := by
  -- `σ*x = addPullback_x_pair α₁ α₂`, `σ*y = addPullback_y_pair α₁ α₂`.
  have hpx : (addIsog hxy hinj).pullback
        (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X)) = addPullback_x_pair α₁ α₂ := by
    show (addIsog hxy hinj).pullback (x_gen W) = addPullback_x_pair α₁ α₂
    rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq]
  have hpy : (addIsog hxy hinj).pullback (y_gen W) = addPullback_y_pair α₁ α₂ := by
    rw [addIsog_pullback, OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq]
  -- `α*u of σ = u₃ = 2·addPullback_y_pair + a₁·addPullback_x_pair + a₃`.
  have hu : alpha_star_u W (addIsog hxy hinj)
      = 2 * addPullback_y_pair α₁ α₂ + algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
        + algebraMap K KE W.a₃ := by
    rw [show alpha_star_u W (addIsog hxy hinj)
        = 2 * (addIsog hxy hinj).pullback (y_gen W)
          + algebraMap K KE W.a₁ * (addIsog hxy hinj).pullback (x_gen W)
          + algebraMap K KE W.a₃ from rfl, hpy]
    rw [show (addIsog hxy hinj).pullback (x_gen W)
        = (addIsog hxy hinj).pullback (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X))
        from rfl, hpx]
  have hu_ne : alpha_star_u W (addIsog hxy hinj) ≠ 0 := by
    rw [alpha_star_u_eq]
    exact fun h ↦ u_gen_ne_zero W
      ((addIsog hxy hinj).pullback_injective (h.trans (map_zero _).symm))
  have hu3_ne : 2 * addPullback_y_pair α₁ α₂ + algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂
      + algebraMap K KE W.a₃ ≠ 0 := hu ▸ hu_ne
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx, hu,
    kaehler_D_addPullback_x_pair_eq_smul_omega W α₁ α₂ h_ne, smul_smul,
    inv_mul_cancel₀ hu3_ne, one_smul]

-- **RB-ID core** (`addPullback_xy_mulByInt_eq_succ`, the Silverman III.5.3 addition recurrence
-- `P ⊞ [m]P = [m+1]P`) lives in `HasseWeil.EC.MulByIntAddRecurrence` (minimal imports, to skirt the
-- `(W_KE W).toAffine.Point` ℤ-smul instance diamond — see `SK-ROUTEB-SMUL-DIAMOND` there). It is
-- imported above and consumed by RB-IND below.

/-- **RB chord step** (Silverman III.5.3 recurrence at the differential level): for `k ≥ 2`,
`a_{[k+1]} = 1 + a_{[k]}`.

Proof. By uniqueness in the 1-dimensional Kähler module. `omegaPullbackCoeff_spec` gives
`a_{[k+1]} • ω = (α*u of [k+1])⁻¹ • D([k+1]*x)`. Now:
* `[k+1]*x = mulByInt_x (k+1) = addPullback_x [k]` (RB-ID), so `D([k+1]*x) = D(addPullback_x [k])`.
* RB-ω4 (α = `[k]`, with `x_gen ≠ [k]*x` since `k ≥ 2`): `D(addPullback_x [k]) = u₃ • ((1 + a_{[k]}) • ω)`
  where `u₃ = 2·addPullback_y [k] + a₁·addPullback_x [k] + a₃`.
* RB-ID rewrites `addPullback_x/y [k] = mulByInt_x/y (k+1)`, so `u₃ = α*u of [k+1]` (definitionally,
  via `alpha_star_u_mulByInt`).

Hence `a_{[k+1]} • ω = u₃⁻¹ • (u₃ • (1 + a_{[k]}) • ω) = (1 + a_{[k]}) • ω`. -/
theorem omegaPullbackCoeff_mulByInt_succ (k : ℤ) (hk2 : 2 ≤ k) :
    omegaPullbackCoeff W (mulByInt W.toAffine (k + 1))
      = 1 + omegaPullbackCoeff W (mulByInt W.toAffine k) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k + 1 ≠ 0 := by omega
  -- `x_gen ≠ mulByInt_x k` (k ≥ 2 ⟹ k ≠ ±1, and `x_gen = mulByInt_x 1`).
  have hx_ne : x_gen W ≠ mulByInt_x W k := by
    rw [← mulByInt_x_one W]
    exact mulByInt_x_ne_mulByInt_x W 1 k one_ne_zero hk0 (by omega) (by omega)
  -- `[k]*x = mulByInt_x k`, so RB-ω4's hypothesis `x_gen ≠ [k]*x` is `hx_ne`.
  have hkx : (mulByInt W.toAffine k).pullback (x_gen W) = mulByInt_x W k :=
    mulByInt_pullback_x W k hk0
  have hx_ne_pb : x_gen W ≠ (mulByInt W.toAffine k).pullback (x_gen W) := by
    rw [hkx]; exact hx_ne
  -- RB-ID: `addPullback_x/y [k] = mulByInt_x/y (k+1)`.
  obtain ⟨hAx, hAy⟩ := addPullback_xy_mulByInt_eq_succ W k hk0 hk1 hx_ne
  -- `α*u of [k+1] = u₃ := 2·addPullback_y [k] + a₁·addPullback_x [k] + a₃`
  -- (def + RB-ID + alpha_star_u_mulByInt).
  have hu : alpha_star_u W (mulByInt W.toAffine (k + 1))
      = 2 * addPullback_y W (mulByInt W.toAffine k)
        + algebraMap K KE W.a₁ * addPullback_x W (mulByInt W.toAffine k) + algebraMap K KE W.a₃ := by
    rw [alpha_star_u_mulByInt W (k + 1) hk1, ← hAx, ← hAy]
  have hu_ne : alpha_star_u W (mulByInt W.toAffine (k + 1)) ≠ 0 := by
    rw [alpha_star_u_eq]
    exact fun h ↦ u_gen_ne_zero W
      ((mulByInt W.toAffine (k + 1)).pullback_injective (h.trans (map_zero _).symm))
  have hu3_ne : 2 * addPullback_y W (mulByInt W.toAffine k)
      + algebraMap K KE W.a₁ * addPullback_x W (mulByInt W.toAffine k) + algebraMap K KE W.a₃ ≠ 0 :=
    hu ▸ hu_ne
  -- `[k+1]*x = addPullback_x [k]` (mulByInt_pullback_x + RB-ID).
  have hpx : (mulByInt W.toAffine (k + 1)).pullback
        (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X))
      = addPullback_x W (mulByInt W.toAffine k) := by
    rw [mulByInt_pullback_x W (k + 1) hk1, ← hAx]
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx, hu,
    kaehler_D_addPullback_x_eq_one_add_smul_omega W (mulByInt W.toAffine k) hx_ne_pb, smul_smul,
    inv_mul_cancel₀ hu3_ne, one_smul]

/-- `a_{[n]} = n` for all `n ≥ 2`, by `Int.leInduction` from the axiom-clean base case `n = 2`
(`omegaPullbackCoeff_mulByInt_two`), with step `k ≥ 2 ⟹ k+1` via the chord step
`omegaPullbackCoeff_mulByInt_succ`. -/
theorem omegaPullbackCoeff_mulByInt_ge_two (n : ℤ) (hn : 2 ≤ n) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n := by
  induction n, hn using Int.leInduction with
  | base => exact omegaPullbackCoeff_mulByInt_two W
  | succ k hk2 ih =>
    rw [omegaPullbackCoeff_mulByInt_succ W k hk2, ih, Int.cast_add, Int.cast_one, map_add,
      map_one, add_comm]

/-- **RB-IND** (Silverman III.5.3, positive case): `a_{[n]} = n` for all `n ≥ 1`. Combines the
`n = 1` case (`[1] = id`, `a_id = 1`) with `omegaPullbackCoeff_mulByInt_ge_two`. -/
theorem omegaPullbackCoeff_mulByInt_pos (n : ℤ) (hn : 1 ≤ n) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1; rw [mulByInt_one_eq_id, omegaPullbackCoeff_id, Int.cast_one, map_one]
  · exact omegaPullbackCoeff_mulByInt_ge_two W n (by omega)

/-- **RB negation**: `a_{[-n]} = -a_{[n]}` for `n ≠ 0`. The `[-n]`-pullback of `x_gen`
agrees with the `[n]`-pullback (`mulByInt_x_neg`), while `α*u` flips sign
(`negY`-symmetry of `mulByInt_y`), so the spec equation flips sign and uniqueness
gives the result. -/
theorem omegaPullbackCoeff_mulByInt_neg (n : ℤ) (hn : n ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine (-n))
      = -omegaPullbackCoeff W (mulByInt W.toAffine n) := by
  have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
  -- `[-n]*x = mulByInt_x (-n) = mulByInt_x n = [n]*x` (mulByInt_x_neg).
  have hpx_eq : (mulByInt W.toAffine (-n)).pullback
        (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X))
      = (mulByInt W.toAffine n).pullback
        (algebraMap R KE (algebraMap (Polynomial K) R Polynomial.X)) := by
    rw [mulByInt_pullback_x W (-n) hneg, mulByInt_pullback_x W n hn, mulByInt_x_neg]
  -- `α*u of [-n] = -(α*u of [n])` via `mulByInt_y_neg` and `negY`.
  have hu_neg : alpha_star_u W (mulByInt W.toAffine (-n))
      = -alpha_star_u W (mulByInt W.toAffine n) := by
    rw [alpha_star_u_mulByInt W (-n) hneg, alpha_star_u_mulByInt W n hn,
      mulByInt_x_neg, mulByInt_y_neg W n hn]
    show 2 * (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n)
        + algebraMap K KE W.a₁ * mulByInt_x W n + algebraMap K KE W.a₃ = _
    rw [WeierstrassCurve.Affine.negY,
      show (W_KE W).a₁ = algebraMap K KE W.a₁ from rfl,
      show (W_KE W).a₃ = algebraMap K KE W.a₃ from rfl]
    ring
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx_eq, hu_neg, inv_neg, neg_smul, neg_smul]
  congr 1
  exact (omegaPullbackCoeff_spec W (mulByInt W.toAffine n)).symm

/-- **RB-IND (Silverman III.5.3)**, integer form: `a_{[n]} = n` for all `n ≠ 0`, by the chord-step
induction (positive `n`) and the negation symmetry (negative `n`). Reroutes
`omegaPullbackCoeff_mulByInt` off the (still partial) EDS Wronskian. -/
theorem omegaPullbackCoeff_mulByInt_routeB (n : ℤ) (hn : n ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · -- n < 0: a_{[n]} = a_{[-(-n)]} = -a_{[-n]} = -(-n) = n, with -n ≥ 1.
    rw [show n = -(-n) from (neg_neg n).symm,
      omegaPullbackCoeff_mulByInt_neg W (-n) (by omega),
      omegaPullbackCoeff_mulByInt_pos W (-n) (by omega), ← map_neg]
    norm_cast
  · -- n > 0: direct from the positive induction.
    exact omegaPullbackCoeff_mulByInt_pos W n (by omega)

/-- **Pillar B endpoint (wronskian-free, formal-group-free)**: in characteristic `p`, `[p]*ω = 0`,
i.e. `a_{[p]} = (p : K) = 0`. The axiom-clean Route B replacement for the formal-group
`omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup` and the wronskian
`omegaPullbackCoeff_mulByInt`. Direct from `omegaPullbackCoeff_mulByInt_routeB` + `CharP.cast_eq_zero`. -/
theorem omegaPullbackCoeff_mulByInt_p_eq_zero_routeB (p : ℕ) [CharP K p] (hp : p ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine (p : ℤ)) = 0 := by
  rw [omegaPullbackCoeff_mulByInt_routeB W (p : ℤ) (by exact_mod_cast hp),
    show ((p : ℤ) : K) = 0 from by rw [Int.cast_natCast]; exact CharP.cast_eq_zero K p, map_zero]

/-- **Pillar B endpoint at `q = #K`** (`[q]*ω = 0`): over the finite field `K`, the ω-pullback
coefficient of `[q]` vanishes, since `a_{[q]} = (q : K) = 0` (`#K = char^n`). Axiom-clean via
`omegaPullbackCoeff_mulByInt_routeB`; this is the `q`-th-root input to the Verschiebung
factorisation `[q] = V ∘ Frob`. -/
theorem omegaPullbackCoeff_mulByInt_card_eq_zero :
    omegaPullbackCoeff W (mulByInt W.toAffine (Fintype.card K : ℤ)) = 0 := by
  rw [omegaPullbackCoeff_mulByInt_routeB W (Fintype.card K : ℤ)
      (by exact_mod_cast Fintype.card_ne_zero),
    show ((Fintype.card K : ℤ) : K) = 0 from by
      rw [Int.cast_natCast]; exact FiniteField.cast_card_eq_zero K, map_zero]

end HasseWeil
