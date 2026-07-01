module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# Kummer's lemma on units of cyclotomic fields (FLT37)

For an odd prime `p > 2` and `K = ℚ(ζ_p)`, every unit `u : (𝓞 K)ˣ` has the
form `u = ζ^m · v` where `v` is a real unit (i.e., the image of some
`v⁺ : (𝓞 K⁺)ˣ` under `algebraMap`). This is the unit-decomposition step
underpinning the FLT case-I argument.

The proof builds on `flt-regular`'s `unit_inv_conj_is_root_of_unity`:
`u · σu⁻¹ = ζ^{2m}` for some `m`. Setting `v := u · ζ^{-m}`, one checks
`σv = v`, hence `v ∈ realUnits K = image of (𝓞 K⁺)ˣ`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Kummer's lemma (units form).** For an odd cyclotomic CM field
`K = ℚ(ζ_p)` (with `p > 2`), every unit `u : (𝓞 K)ˣ` decomposes as
`u = ζ^m · algebraMap v⁺` where `v⁺ : (𝓞 K⁺)ˣ`. -/
theorem exists_zeta_pow_mul_real_eq_unit (hp_two : 2 < p) (u : (𝓞 K)ˣ) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ (m : ℕ) (v : (𝓞 (K⁺))ˣ),
      u = ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ m *
        Units.map (algebraMap (𝓞 (K⁺)) (𝓞 K)).toMonoidHom v := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity (zeta_spec p ℚ K) u hp_two
  set ζU : (𝓞 K)ˣ := ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit
  set v : (𝓞 K)ˣ := u * (ζU ^ m)⁻¹ with hv_def
  have hζ_torsion : ζU ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos,
        ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hp.1.ne_zero).pow_eq_one⟩)
  have h_conj_zeta : unitsComplexConj K ζU = ζU⁻¹ :=
    unitsComplexConj_torsion (K := K) ⟨ζU, hζ_torsion⟩
  have h_conj_zeta_pow_inv : unitsComplexConj K ((ζU ^ m)⁻¹) = ζU ^ m := by
    rw [map_inv, map_pow, h_conj_zeta, inv_pow, inv_inv]
  have h_v_real : unitsComplexConj K v = v := by
    have h_conj_v : unitsComplexConj K v =
        unitsComplexConj K u * ζU ^ m := by
      rw [hv_def, map_mul, h_conj_zeta_pow_inv]
    have h_target : unitsComplexConj K u * ((ζU ^ m) * (ζU ^ m)) = u := by
      rw [pow_two] at hm
      rw [← hm, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    rw [h_conj_v, hv_def, eq_mul_inv_iff_mul_eq, mul_assoc]
    exact h_target
  have h_real : v ∈ realUnits K :=
    (unitsComplexConj_eq_self_iff (K := K) v).mp h_v_real
  obtain ⟨v_plus, h_v_plus⟩ := (mem_realUnits_iff (K := K) v).mp h_real
  refine ⟨m, v_plus, ?_⟩
  have h_eq : Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom v_plus = v :=
    Units.ext h_v_plus
  rw [h_eq, hv_def, mul_comm u ((ζU ^ m)⁻¹), ← mul_assoc, mul_inv_cancel,
    one_mul]

end FLT37

end BernoulliRegular

end
