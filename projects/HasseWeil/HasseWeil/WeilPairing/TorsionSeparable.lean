import HasseWeil.Hasse.Separability
import HasseWeil.Hasse.TorsionCard
import HasseWeil.OmegaCoeffMulByIntFiniteField
import HasseWeil.AdditionPullback.Differential
import HasseWeil.Curves.Differentials

/-!
# Route 2A — separability of `[ℓ]` (the torsion-structure entry point)

The residual `hscale` (see `Assembly.qf_nonneg_of_pairing_scaling`) needs, per auxiliary prime
`ℓ ≠ p`, the Frobenius matrix on `E[ℓ] ≅ (ZMod ℓ)²`. That torsion structure rests on `#E[ℓ] = ℓ²`,
which rests on `[ℓ]` being **separable** (so `#ker[ℓ] = deg[ℓ] = ℓ²`).

This file records that `[ℓ]` separable is **not** blocked by the EDS-Wronskian `sorry` in
`OmegaPullbackCoeff` (the `m ≥ 5` case of `wronskian_Φ_ΨSq_nat`). The separability witness
`[ℓ]*ω = ℓ·ω` (`omegaPullbackCoeff (mulByInt ℓ) = ℓ`) is supplied **axiom-clean** by the
formal-group route `omegaPullbackCoeff_mulByInt_routeB` (`RouteBInduction`, via `id ⊞ [m] = [m+1]`
induction — no division polynomials), and the differential criterion
`isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim` (Silverman II.4.10c, T-II-4-004) is
likewise axiom-clean.

So `[ℓ]` separable reduces to the single clean hypothesis `FiniteDimensional` of `K(E)` over
`[ℓ]^* K(E)` — the function-field extension cut out by `[ℓ]`. This isolates the torsion-side gap
precisely (no EDS dependence).

Reference: Silverman III.5.4 (`[m]` separable for `m ≠ 0` in `K`), III.6.4(a) (`#E[m] = m²`).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

variable {K : Type*} [Field K] [DecidableEq K] [Finite K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- **`[ℓ]` is separable when `ℓ ≠ 0` in `K`** (Silverman III.5.4), reduced to the single
finite-dimensionality hypothesis on the `[ℓ]`-extension of function fields.

The `ω`-pullback coefficient witness `[ℓ]*ω = ℓ·ω` is discharged **axiom-clean** by the
formal-group route `omegaPullbackCoeff_mulByInt_routeB` (no EDS-Wronskian dependence); the
differential separability criterion is `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`. -/
theorem mulByInt_isSeparable_of_finiteDim
    (ℓ : ℤ) (hℓ : (ℓ : K) ≠ 0)
    (hfindim : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine ℓ).toAlgebra.toModule) :
    (mulByInt W.toAffine ℓ).IsSeparable := by
  haveI : Fintype K := Fintype.ofFinite K
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  have hcoeff := omegaPullbackCoeff_mulByInt_routeB W ℓ hℓ0
  rw [isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim W (mulByInt W.toAffine ℓ) hfindim,
    hcoeff]
  exact fun h ↦ hℓ ((map_eq_zero _).mp h)

/-- **`#E[ℓ] = ℓ²`** (Silverman III.6.4(a)) reduced to the torsion-side witnesses, with separability
discharged axiom-clean via the formal-group route. Given `ℓ ≠ 0` in `K`, finiteness of the
`[ℓ]`-kernel, finite-dimensionality of the `[ℓ]`-extension, and the generic-fibre witness
(`#fibre = deg_s[ℓ]`), the `ℓ`-torsion has cardinality `ℓ²`. -/
theorem torsionSubgroup_card_of_finiteDim
    (ℓ : ℤ) (hℓ : (ℓ : K) ≠ 0)
    [Finite (mulByInt W.toAffine ℓ).kernel]
    (hfindim : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine ℓ).toAlgebra.toModule)
    (h_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (mulByInt W.toAffine ℓ).toAddMonoidHom P =
            (mulByInt W.toAffine ℓ).toAddMonoidHom P₀} =
        (mulByInt W.toAffine ℓ).sepDegree) :
    (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  exact torsionSubgroup_card_of_separable_witness W ℓ hℓ0
    (mulByInt_isSeparable_of_finiteDim W ℓ hℓ hfindim) hfindim h_fiber_witness

/-! ### Unconditional separability (the `FiniteDimensional` gap is closed)

The finite-dimensionality hypothesis above is **not** an open gap:
`HasseWeil.isogeny_finiteDimensional` discharges it axiom-clean for **every** isogeny (via the
transcendence-degree additivity `trdeg F (K(E)_α) + trdeg (K(E)_α) K(E) = trdeg F K(E) = 1`, forcing
`K(E)/K(E)_α` algebraic, hence finite with `EssFiniteType`). So `[ℓ]` separable holds with **no**
hypothesis beyond `ℓ ≠ 0` in `K`. -/

/-- **`[ℓ]` is separable when `ℓ ≠ 0` in `K`** (Silverman III.5.4) — fully unconditional,
axiom-clean. The `ω`-coefficient witness is the formal-group `routeB` (no EDS-Wronskian), and the
finite-dimensionality is the general `isogeny_finiteDimensional`. -/
theorem mulByInt_isSeparable (ℓ : ℤ) (hℓ : (ℓ : K) ≠ 0) :
    (mulByInt W.toAffine ℓ).IsSeparable :=
  mulByInt_isSeparable_of_finiteDim W ℓ hℓ
    (HasseWeil.isogeny_finiteDimensional W (mulByInt W.toAffine ℓ))

/-- **`#E[ℓ] = ℓ²`** (Silverman III.6.4(a)) with the finite-dimensionality gap closed: only the
`[ℓ]`-kernel finiteness and the generic-fibre witness (`#fibre = deg_s[ℓ]`) remain as hypotheses;
separability and finite-dimensionality are both discharged axiom-clean. -/
theorem torsionSubgroup_card (ℓ : ℤ) (hℓ : (ℓ : K) ≠ 0)
    [Finite (mulByInt W.toAffine ℓ).kernel]
    (h_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (mulByInt W.toAffine ℓ).toAddMonoidHom P =
            (mulByInt W.toAffine ℓ).toAddMonoidHom P₀} =
        (mulByInt W.toAffine ℓ).sepDegree) :
    (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2 :=
  torsionSubgroup_card_of_finiteDim W ℓ hℓ
    (HasseWeil.isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)) h_fiber_witness

end HasseWeil.WeilPairing
