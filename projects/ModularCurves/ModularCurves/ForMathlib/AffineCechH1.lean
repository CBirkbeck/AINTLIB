/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib

/-!
# Affine Čech `H¹` vanishing for a two-element cover (Mayer–Vietoris splitting)

For a commutative ring `R` and an `R`-module `M`, the affine scheme `Spec R` covered by the two
basic opens `D(f)`, `D(g)` (with `f, g` coprime, i.e. `Ideal.span {f, g} = ⊤`) has vanishing
first Čech cohomology with values in the quasi-coherent sheaf `M~`.  In elementary terms this is
the *Mayer–Vietoris splitting*: the difference of restriction maps

  `M[1/f] × M[1/g] → M[1/(fg)]`,  `(a, b) ↦ a|_{fg} - b|_{fg}`

is **surjective**.  Equivalently, every value `c` on the overlap `D(fg)` is an additive
`1`-coboundary: `c = a|_{fg} - b|_{fg}` for some `a` on `D(f)` and `b` on `D(g)`.  This is the
additive `1`-cocycle-splits statement for a two-chart cover — the "`H¹`(affine) = 0" fact in the
form consumed by chart-gluing arguments.

The proof is the standard partition-of-unity argument: from `IsCoprime f g` one gets, after
raising to the powers `f ^ a`, `g ^ b` appearing as the denominator of `c`, a relation
`p * f ^ a + q * g ^ b = 1`; multiplying `c` by `f ^ a` clears the `f`-denominator (landing the
result in `M[1/g]`) and by `g ^ b` clears the `g`-denominator (landing in `M[1/f]`), and the two
pieces reassemble to `c`.

## Main results

* `IsLocalizedModule.exists_sub_liftOfLE_eq_of_isCoprime` — the abstract form: for arbitrary
  localized modules `lf : M →ₗ M_f`, `lg : M →ₗ M_g`, `lfg : M →ₗ M_{fg}` (with `M_{fg}` the
  localization at the join `Submonoid.powers f ⊔ Submonoid.powers g`), every `c : M_{fg}` splits
  as `c = ρ_f a - ρ_g b` with `ρ_f`, `ρ_g` the canonical restriction (`liftOfLE`) maps.
* `IsLocalizedModule.mvDifference_surjective` — the same statement packaged as surjectivity of the
  Mayer–Vietoris difference `LinearMap`.
* `LocalizedModule.exists_sub_liftOfLE_eq_of_isCoprime` — the concrete `LocalizedModule` corollary.

## Implementation notes

The overlap `M_{fg}` is localized at the **join** submonoid `Submonoid.powers f ⊔ Submonoid.powers g`
rather than `Submonoid.powers (f * g)`; the two are the same localization, but the join makes the
restriction maps literal `IsLocalizedModule.liftOfLE` maps (`Submonoid.powers f ≤ …`), which keeps
the fraction bookkeeping clean.  The bridge
`IsLocalizedModule.isLocalizedModule_sup_of_powers_mul` re-expresses a `Submonoid.powers (f * g)`
localization as a join localization, so a consumer holding `M[1/(fg)]` in the `powers (f*g)` form
can still apply the theorem.

The **general finite cover** version (an arbitrary family generating the unit ideal, with the full
`c i j + c j k = c i k` cocycle condition on triple overlaps) is a genuinely homological statement
— the naive partition-of-unity sum does not verify by a direct fraction computation for `≥ 3`
charts — and is deliberately **not** proved here.
-/

namespace IsLocalizedModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {Mf Mg Mfg : Type*}
  [AddCommGroup Mf] [Module R Mf] [AddCommGroup Mg] [Module R Mg]
  [AddCommGroup Mfg] [Module R Mfg]
  (lf : M →ₗ[R] Mf) (lg : M →ₗ[R] Mg) (lfg : M →ₗ[R] Mfg)
  {f g : R}
  [IsLocalizedModule (Submonoid.powers f) lf]
  [IsLocalizedModule (Submonoid.powers g) lg]
  [IsLocalizedModule (Submonoid.powers f ⊔ Submonoid.powers g) lfg]

/-- **Affine Čech `H¹` vanishing for a two-element cover (Mayer–Vietoris splitting).**

Let `M` be a module over a commutative ring `R`, and let `f g : R` be coprime.  Writing
`M_f`, `M_g`, `M_{fg}` for the localizations of `M` at `f`, `g`, and the join
`Submonoid.powers f ⊔ Submonoid.powers g` respectively (so `M_{fg} = M[1/f, 1/g]`), every value
`c : M_{fg}` on the overlap `D(fg)` is an additive `1`-coboundary for the two-chart cover
`{D(f), D(g)}`: there exist `a : M_f` and `b : M_g` with
`c = (a restricted to M_{fg}) - (b restricted to M_{fg})`, the restrictions being the canonical
`IsLocalizedModule.liftOfLE` maps. -/
theorem exists_sub_liftOfLE_eq_of_isCoprime (hfg : IsCoprime f g) (c : Mfg) :
    ∃ (a : Mf) (b : Mg),
      c = liftOfLE (Submonoid.powers f) (Submonoid.powers f ⊔ Submonoid.powers g)
            le_sup_left lf lfg a
        - liftOfLE (Submonoid.powers g) (Submonoid.powers f ⊔ Submonoid.powers g)
            le_sup_right lg lfg b := by
  classical
  -- Write `c = m / s` with `s` in the join submonoid, and split `s = f ^ a * g ^ b`.
  obtain ⟨m, s, rfl⟩ :
      ∃ (m : M) (s : ↥(Submonoid.powers f ⊔ Submonoid.powers g)), mk' lfg m s = c := by
    obtain ⟨⟨m, s⟩, h⟩ := mk'_surjective (Submonoid.powers f ⊔ Submonoid.powers g) lfg c
    exact ⟨m, s, h⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Submonoid.mem_sup.mp s.2
  obtain ⟨a, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hx
  obtain ⟨b, rfl⟩ := (Submonoid.mem_powers_iff y g).mp hy
  -- `hxy : f ^ a * g ^ b = ↑s`.
  obtain ⟨p, q, hpq⟩ : IsCoprime (f ^ a) (g ^ b) := hfg.pow
  have hpf : f ^ a ∈ Submonoid.powers f := pow_mem (Submonoid.mem_powers f) a
  have hpg : g ^ b ∈ Submonoid.powers g := pow_mem (Submonoid.mem_powers g) b
  -- Clearing the `f`-denominator lands `f^a`-restriction of `c` in `M_g`, and dually.
  have eq_f : liftOfLE (Submonoid.powers f) (Submonoid.powers f ⊔ Submonoid.powers g)
        le_sup_left lf lfg (mk' lf m ⟨f ^ a, hpf⟩) = (g ^ b : R) • mk' lfg m s := by
    rw [liftOfLE_mk', ← mk'_smul, mk'_eq_mk'_iff]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    rw [← hxy]
  have eq_g : liftOfLE (Submonoid.powers g) (Submonoid.powers f ⊔ Submonoid.powers g)
        le_sup_right lg lfg (mk' lg m ⟨g ^ b, hpg⟩) = (f ^ a : R) • mk' lfg m s := by
    rw [liftOfLE_mk', ← mk'_smul, mk'_eq_mk'_iff]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    rw [← hxy, mul_comm (f ^ a) (g ^ b)]
  refine ⟨q • mk' lf m ⟨f ^ a, hpf⟩, -(p • mk' lg m ⟨g ^ b, hpg⟩), ?_⟩
  rw [map_smul, map_neg, map_smul, sub_neg_eq_add, eq_f, eq_g, smul_smul, smul_smul, ← add_smul,
    show q * g ^ b + p * f ^ a = 1 by linear_combination hpq, one_smul]

/-- **Affine Čech `H¹` vanishing, packaged as surjectivity.**  For coprime `f g`, the
Mayer–Vietoris difference map `M_f × M_g → M_{fg}`, `(a, b) ↦ a|_{fg} - b|_{fg}`, is surjective. -/
theorem sub_liftOfLE_surjective (hfg : IsCoprime f g) :
    Function.Surjective fun ab : Mf × Mg =>
      liftOfLE (Submonoid.powers f) (Submonoid.powers f ⊔ Submonoid.powers g)
          le_sup_left lf lfg ab.1
        - liftOfLE (Submonoid.powers g) (Submonoid.powers f ⊔ Submonoid.powers g)
            le_sup_right lg lfg ab.2 := by
  intro c
  obtain ⟨a, b, hc⟩ := exists_sub_liftOfLE_eq_of_isCoprime lf lg lfg hfg c
  exact ⟨(a, b), hc.symm⟩

/-- Bridge: a localization of `M` at `Submonoid.powers (f * g)` is also a localization at the join
`Submonoid.powers f ⊔ Submonoid.powers g`.  This lets a consumer holding the overlap module in the
`powers (f * g)` form feed it to `exists_sub_liftOfLE_eq_of_isCoprime`. -/
theorem isLocalizedModule_sup_of_powers_mul {N : Type*} [AddCommGroup N] [Module R N]
    (l : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers (f * g)) l] :
    IsLocalizedModule (Submonoid.powers f ⊔ Submonoid.powers g) l := by
  refine IsLocalizedModule.of_exists_mul_mem (Submonoid.powers (f * g))
    (Submonoid.powers f ⊔ Submonoid.powers g) ?_ ?_ l
  · rw [Submonoid.powers_le]
    exact mul_mem (Submonoid.mem_sup_left (Submonoid.mem_powers f))
      (Submonoid.mem_sup_right (Submonoid.mem_powers g))
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submonoid.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hx
    obtain ⟨b, rfl⟩ := (Submonoid.mem_powers_iff y g).mp hy
    exact ⟨f ^ b * g ^ a, ⟨a + b, by ring⟩⟩

end IsLocalizedModule

namespace LocalizedModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {f g : R}

/-- **Affine Čech `H¹` vanishing for a two-element cover — concrete `LocalizedModule` form.**

For coprime `f g : R` and an `R`-module `M`, every element `c` of the overlap localization
`LocalizedModule (Submonoid.powers f ⊔ Submonoid.powers g) M` is an additive `1`-coboundary for
the cover `{D(f), D(g)}`:
`c = a|_{overlap} - b|_{overlap}` for some `a : M[1/f]` and `b : M[1/g]`, the restrictions being
`LocalizedModule.liftOfLE`. -/
theorem exists_sub_liftOfLE_eq_of_isCoprime (hfg : IsCoprime f g)
    (c : LocalizedModule (Submonoid.powers f ⊔ Submonoid.powers g) M) :
    ∃ (a : LocalizedModule (Submonoid.powers f) M) (b : LocalizedModule (Submonoid.powers g) M),
      c = LocalizedModule.liftOfLE (Submonoid.powers f)
            (Submonoid.powers f ⊔ Submonoid.powers g) le_sup_left a
        - LocalizedModule.liftOfLE (Submonoid.powers g)
            (Submonoid.powers f ⊔ Submonoid.powers g) le_sup_right b :=
  IsLocalizedModule.exists_sub_liftOfLE_eq_of_isCoprime
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f ⊔ Submonoid.powers g) M) hfg c

end LocalizedModule
