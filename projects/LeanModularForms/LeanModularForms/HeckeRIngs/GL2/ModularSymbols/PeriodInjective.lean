/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodInvariant
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeterssonStokes
import LeanModularForms.Modularforms.PeterssonLevelN

/-!
# Injectivity of the period map (ES-4)

This file proves that the unconditional period map `periodMap'` of `PeriodInvariant.lean`,

```
periodMap' N k : S_k(Γ₁(N)) →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ),
```

is **injective** for weight `k ≥ 2`.

## Strategy (Shimura §8.2, Theorem 8.4)

`periodMap' f = 0` says that *every* period of `f` vanishes:
`∫_β^α f(z)·P(z,1) dz = 0` for every cusp pair `{α,β}` and every `P ∈ Sym^{k-2}`.  Shimura's
cohomological pairing argument (Theorem 8.4, p.235) deduces `f = 0` from this via the
**non-degeneracy** of the real bilinear period pairing `A(f,g)` on `S_{n+2}` (`n = k-2`,
Shimura (8.2.17)).

We isolate the analytic content as a single classical input and assemble injectivity around it
sorry-free:

* **The period pairing** `A f g := (f,g) + (-1)ⁿ·(g,f)` (`periodPairingA`) — the Shimura pairing
  (8.2.18a), written on the Petersson side.  Its **Green identity** (Shimura (8.2.18c)) in the
  twisted-diagonal form `A(f, iⁿ·f) = 2·iⁿ·(f,f)` (`periodPairingA_twist_self`) is a clean
  consequence of Hermitian symmetry of the Petersson product — **proven here**.
* **The Stokes/coboundary input** (Shimura (8.2.22)): if all periods of `f` vanish
  (`periodMap' f = 0`), then `A f g = 0` for every `g`
  (`periodPairingA_eq_zero_of_periodMap'_zero`).  This is the integral Eichler–Shimura
  period↔Petersson pairing — a Green's-theorem computation over
  a `Γ₁(N)`-fundamental domain whose boundary edges are paired by `Γ₁(N)` — and is the lone deep
  analytic fact of ES-4, isolated as one named lemma.

Combining them: `periodMap' f = 0` gives `0 = A(f, iⁿ·f) = 2·iⁿ·(f,f)`, hence `(f,f) = 0`, hence
`f = 0` by positive-definiteness `petN_definite` (`Modularforms/PeterssonLevelN.lean`).  Injectivity
of the `ℂ`-linear `periodMap'` reduces to exactly `periodMap' f = 0 → f = 0`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2,
  Theorem 8.4 and (8.2.17)–(8.2.22); the non-degeneracy is (8.2.18c).
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise TensorProduct
open UpperHalfPlane Complex MeasureTheory Filter CongruenceSubgroup
  Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## The bilinear period pairing `A` (Shimura (8.2.17)/(8.2.18a)) -/

/-- **The Shimura period pairing `A(f,g)`** (§8.2, (8.2.17)), written on the Petersson side via
(8.2.18a): `A f g = (f,g) + (-1)ⁿ·(g,f)` with `n = k-2` and `(·,·) = petN` the level-`N`
Petersson inner product.  (Shimura's `A` carries an extra fixed nonzero scalar `(2i)^{n+1}` which
is irrelevant to its non-degeneracy, so we drop it.)  This is the `ℝ`-bilinear cohomological
period pairing whose
non-degeneracy drives the injectivity of the period map. -/
def periodPairingA (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℂ :=
  petN f g + ((-1 : ℂ) ^ (k - 2).toNat) • petN g f

/-- **The Green identity (Shimura (8.2.18c)), twisted-diagonal form.**  For the `iⁿ`-twist
(`n = k-2`), `A(f, iⁿ·f) = 2·iⁿ·(f,f)`.  This is Shimura's `A(f, iⁿg) = 2ⁿ·Re((f,g))` specialized to
`g = f` (where `Re((f,f)) = (f,f)` as `(f,f)` is a non-negative real), repackaged with the harmless
`iⁿ` factor; here it is an immediate consequence of the Hermitian symmetry of `petN`
(`petN_conj_smul_left`, `petN_smul_right`).  It is the algebraic non-degeneracy witness: the right
side is a nonzero multiple of the Petersson norm. -/
theorem periodPairingA_twist_self (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    periodPairingA f ((Complex.I ^ (k - 2).toNat) • f) =
      (2 * Complex.I ^ (k - 2).toNat) * petN f f := by
  rw [periodPairingA, petN_smul_right, petN_conj_smul_left, smul_eq_mul, map_pow, Complex.conj_I,
    show ((-1 : ℂ) ^ (k - 2).toNat) * ((-Complex.I) ^ (k - 2).toNat * petN f f)
      = (((-1 : ℂ) * (-Complex.I)) ^ (k - 2).toNat) * petN f f by rw [mul_pow]; ring,
    show (-1 : ℂ) * (-Complex.I) = Complex.I by ring]
  ring

/-! ## The Stokes/coboundary input (Shimura (8.2.22)) — the isolated analytic core -/

/-- **`periodMap' f = 0` is equivalent to the vanishing of the pre-descent pairing `rawPairing f`.**
Since `periodMap' N k f` is, by construction, the descent of `rawPairing f` along the surjection
`𝕄.mk` (`periodMap'_apply_mk`), the functional `periodMap' N k f` is zero on all of `𝕄 N k` iff the
raw period pairing `rawPairing f` is zero on the whole tensor module `Div⁰ ⊗ Sym`.  This is the
purely formal restatement of "all periods of `f` vanish". -/
theorem rawPairing_eq_zero_of_periodMap'_zero (hk : 2 ≤ k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : periodMap' N k hk f = 0)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) : rawPairing f x = 0 := by
  have h := periodMap'_apply_mk hk f x
  rw [hf] at h
  simpa using h.symm

/-- **The Stokes/Green boundary-period decomposition (Shimura (8.2.22)), the isolated analytic
core.**  The Shimura period pairing `A(f, g)` is a finite `ℂ`-linear combination of *periods of
`f`* — values `rawPairing f (yᵢ)` of the pre-descent period pairing on integral modular symbols
`yᵢ ∈ Div⁰ ⊗ Sym^{k-2}`, with complex coefficients `cᵢ` built from `g` (and the boundary
automorphy data).

This is the Green's-theorem identity `A(f, g) = ∫_F d(F̄ · W · dg) = ∫_{∂F} F̄ · W · dg`: the
Petersson side `A(f, g) = (f, g) + (-1)ⁿ (g, f)` (by (8.2.18a)) is an area integral over a
`Γ₁(N)`-fundamental domain `F` of the exact period 2-form (`F` a holomorphic primitive of the
period form `periodForm f`, from `Complex.isExactOn_upperHalf`); Stokes turns it into a boundary
integral over `∂F`, whose `Γ₁(N)`-paired geodesic edges telescope into the periods of `f` against
boundary symbols, weighted by the corresponding values of `g` (Shimura's
`Σ_α ⟨u_f(α⁻¹), W·∫_{S_α} dg⟩`).  The `period-of-f` factors are exactly the `rawPairing f (yᵢ)`.

This boundary-period reduction is the lone deep analytic input of ES-4; everything else in the
period↔Petersson non-degeneracy is assembled around it (`periodPairingA_eq_zero_of_periodMap'_zero`,
which collapses this sum to `0` once `rawPairing f = 0`). -/
theorem periodPairingA_eq_boundary_period (hk : 2 ≤ k)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ (n : ℕ) (coeff : Fin n → ℂ) (y : Fin n → Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat),
      periodPairingA f g = ∑ i, coeff i * rawPairing f (y i) := by
  -- The Petersson combination `A(f,g) = (f,g) + (-1)ⁿ (g,f)` *is* the left-hand side of the
  -- concrete fundamental-domain identification `exists_pairedBoundary_periodPairingA_eq`, which
  -- exhibits it as `c · rawPairing f (B.boundaryDivisor ⊗ P)` for a `Γ₁(N)`-paired boundary `B`.
  obtain ⟨B, P, c, hBP⟩ := exists_pairedBoundary_periodPairingA_eq hk f g
  -- Package the single boundary period as a one-term sum `∑_{i : Fin 1} coeffᵢ · rawPairing f (yᵢ)`
  -- with `coeff₀ = c` the genuine Green's-identity scalar and `y₀ = B.boundaryDivisor ⊗ P` the
  -- genuine boundary 1-cycle.  (`two_smul_rawPairing_boundaryDivisor` further expands the boundary
  -- divisor into per-edge symbols, but the existential here only needs *a* finite combination, and
  -- the boundary period is already such a value `rawPairing f y₀`.)
  exact ⟨1, fun _ => c, fun _ => B.boundaryDivisor ⊗ₜ P, by
    rw [periodPairingA, hBP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]⟩

theorem periodPairingA_eq_zero_of_periodMap'_zero (hk : 2 ≤ k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : periodMap' N k hk f = 0)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : periodPairingA f g = 0 := by
  obtain ⟨n, coeff, y, hsum⟩ := periodPairingA_eq_boundary_period hk f g
  rw [hsum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [rawPairing_eq_zero_of_periodMap'_zero hk f hf (y i), mul_zero]

/-! ## Injectivity -/

/-- **Period–Petersson non-degeneracy.**  If all periods of `f` vanish (`periodMap' f = 0`) then the
Petersson norm `petN f f` vanishes.  Combines the Stokes/coboundary input
`periodPairingA_eq_zero_of_periodMap'_zero` (the period pairing vanishes, Shimura (8.2.22)) with the
Green identity `periodPairingA_twist_self` (Shimura (8.2.18c)): taking the `iⁿ`-twisted diagonal,
`0 = A(f, iⁿ·f) = 2·iⁿ·(f,f)`, and `2·iⁿ ≠ 0`. -/
theorem periodMap'_petN_self (hk : 2 ≤ k) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : periodMap' N k hk f = 0) : petN f f = 0 := by
  have hA : periodPairingA f ((Complex.I ^ (k - 2).toNat) • f) = 0 :=
    periodPairingA_eq_zero_of_periodMap'_zero hk f hf _
  rw [periodPairingA_twist_self] at hA
  have hne : (2 * Complex.I ^ (k - 2).toNat) ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
  exact (mul_eq_zero.mp hA).resolve_left hne

/-- **Injectivity of the period map (ES-4), `k ≥ 2`.**  The unconditional period map
`periodMap' N k : S_k(Γ₁(N)) →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ)` is injective for weight `k ≥ 2`.

A `ℂ`-linear map is injective iff `periodMap' f = 0 → f = 0`.  The vanishing of all periods of `f`
forces the Petersson norm to vanish (`periodMap'_petN_self`), and positive-definiteness of the
level-`N` Petersson inner product (`petN_definite`) then yields `f = 0`. -/
theorem periodMap'_injective (hk : 2 ≤ k) :
    Function.Injective (periodMap' (N := N) (k := k) hk) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  exact petN_definite f (periodMap'_petN_self hk f hf)

end HeckeRing.GL2.ModularSymbols
